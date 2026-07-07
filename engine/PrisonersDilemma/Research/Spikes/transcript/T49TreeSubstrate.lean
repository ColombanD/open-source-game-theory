import PrisonersDilemma.Decidability.T42ProvableB
import PrisonersDilemma.Decidability.T44BoundedDecider
import PrisonersDilemma.Research.Spikes.transcript.T48CutRelevance

/-!
# T4.9 spike — the TREE SUBSTRATE for cut relevance (fork (A), milestone D0).

`Research/Notes/CUT_RELEVANCE.md` §5e: the three kernel-checked refutations (T48 §9–§11)
closed the judgment-local program — the information CutRelevance needs lives in
DERIVATION TREES of provable roots, not in judgments. But `Provable` is `Prop`-valued:
inside Lean we cannot measure a derivation, count its cuts, or rewrite it with a
terminating measure. This file supplies the missing object:

  * **`PlaysT`/`AtomT`/`ProvT`** — a `Type`-valued mirror of the
    `PlaysProof`/`AtomProvable`/`Provable` mutual triple, constructor for constructor
    (`struct` carries its `Derivation` witness explicitly instead of behind `∃`);
  * **`sound`** — trees map back to the `Prop` triple (structural recursion, verbatim);
  * **`complete`** — `Provable k φ → Nonempty (ProvT k φ)` (mutual `Prop` induction;
    `Nonempty` is all the excision analysis needs, and all `Prop` elimination allows);
  * **`GateOK G t`** — the gate residue of a tree: every formula at one of T42's six
    gated positions (`implTrans`'s `ψ`, `app`'s `φ`, `impS2`'s `ψ`, `axK`'s boxed
    premise, `diagF`/`diagB`'s Löb premise) satisfies `G`, recursively through the whole
    tree — including the `Provable` cites inside the atom layer (`search_t`/`search_f`
    guards), which the judgment-local analyses could never reach;
  * **`toG`** — a tree whose gate residue holds maps into `ProvableG G` — so
    **`TreeCutRelevance`** (every provable root has SOME tree with a modest, bounded cut
    diet) implies `CutRelevance` (`tree_cutRelevance`). The conjecture's battleground is
    now official: build tame trees by EXCISION (milestone D2), tree-by-tree, with the
    tree itself as the termination measure — no judgment-local invariant required.
-/

namespace PD.T49

open PD PD.T42 PD.T44

/-! ## 1. The mirror triple. -/

mutual
  /-- `Type`-valued mirror of `PlaysProof`. -/
  inductive PlaysT : (me opponent body : Prog) → Action → Nat → Type where
    | const :
        PlaysT me opponent (.const a) a c_leaf
    | self :
        PlaysT me opponent me a n →
        PlaysT me opponent .self a (n + c_node)
    | opp :
        PlaysT me opponent opponent a n →
        PlaysT me opponent .opp a (n + c_node)
    | bot :
        PlaysT me opponent p a n →
        PlaysT me opponent (.bot p) a (n + c_node)
    | sim :
        PlaysT (p.subst me opponent) (q.subst me opponent) (p.subst me opponent) a n →
        PlaysT me opponent (.sim p q) a (n + c_node)
    | ite_t :
        PlaysT me opponent b r m → (r == a') = true →
        PlaysT me opponent p a n →
        PlaysT me opponent (.ite b a' p q) a (m + n + c_node)
    | ite_f :
        PlaysT me opponent b r m → (r == a') = false →
        PlaysT me opponent q a n →
        PlaysT me opponent (.ite b a' p q) a (m + n + c_node)
    | search_t :
        ProvT k (φ.subst me opponent) →
        PlaysT me opponent p a n →
        PlaysT me opponent (.search k φ p q) a (n + c_guard k + c_node)
    | search_f :
        ProvT m (.neg (φ.subst me opponent)) →
        PlaysT me opponent q a n →
        PlaysT me opponent (.search k φ p q) a (n + m + k + c_node)

  /-- `Type`-valued mirror of `AtomProvable`. -/
  inductive AtomT : Nat → Formula → Type where
    | mk : PlaysT me opponent me a n → n ≤ k → AtomT k (.plays me opponent a)

  /-- `Type`-valued mirror of `Provable`; `struct` carries its `Derivation` witness. -/
  inductive ProvT : Nat → Formula → Type where
    | struct (d : Derivation φ) :
        d.size ≤ k → ProvT k φ
    | atom : AtomT k φ → ProvT k φ
    | weakenImpl (φ ψ : Formula) (m : Nat) :
        ProvT m ψ → m + (Formula.impl φ ψ).size ≤ k → ProvT k (.impl φ ψ)
    | searchThenSearch_t (k₁ k₂ m : Nat) (ψ₁ ψ₂ : Formula) (c0 c1 : Action)
        (q me opponent : Prog)
        (hme : me = .search k₁ ψ₁ (.search k₂ ψ₂ (.const c0) (.const c1)) q) :
        ProvT m (ψ₂.subst me opponent) → m ≤ k₂ →
        c_guard k₂ +
          (Formula.impl (.box k₁ (ψ₁.subst me opponent)) (.plays me opponent c0)).size ≤ k →
        ProvT k (.impl (.box k₁ (ψ₁.subst me opponent)) (.plays me opponent c0))
    | implTrans (φ ψ χ : Formula) (a b : Nat) :
        ProvT a (.impl φ ψ) → ProvT b (.impl ψ χ) →
        a + b + (Formula.impl φ χ).size ≤ k → ProvT k (.impl φ χ)
    | atomBoxImpl (kBox : Nat) (p q : Prog) (a : Action) :
        AtomT kBox (.plays p q a) →
        kBox + (Formula.impl (.plays p q a) (.box kBox (.plays p q a))).size ≤ k →
        ProvT k (.impl (.plays p q a) (.box kBox (.plays p q a)))
    | boxIntro (kIn K : Nat) (φ : Formula) :
        ProvT kIn φ →
        kIn + (Formula.box kIn φ).size ≤ K →
        ProvT K (.box kIn φ)
    | app (k m₁ m₂ : Nat) (φ α : Formula) :
        ProvT m₁ (.impl φ α) → ProvT m₂ φ → m₁ + m₂ + α.size ≤ k → ProvT k α
    | axK (a b c m K : Nat) (φ α : Formula) :
        ProvT m (.box a (.impl φ α)) →
        a + b + α.size ≤ c →
        m + (Formula.impl (.box b φ) (.box c α)).size ≤ K →
        ProvT K (.impl (.box b φ) (.box c α))
    | box4 (a b K : Nat) (φ : Formula) :
        a + (Formula.box a φ).size ≤ b →
        (Formula.impl (.box a φ) (.box b (.box a φ))).size ≤ K →
        ProvT K (.impl (.box a φ) (.box b (.box a φ)))
    | diagF (pm fb g K : Nat) (tgt : Formula) :
        ProvT pm (.impl (.box fb tgt) tgt) →
        pm + (Formula.impl (.diag g tgt) (.impl (.box g (.diag g tgt)) tgt)).size ≤ K →
        ProvT K (.impl (.diag g tgt) (.impl (.box g (.diag g tgt)) tgt))
    | diagB (pm fb g K : Nat) (tgt : Formula) :
        ProvT pm (.impl (.box fb tgt) tgt) →
        pm + (Formula.impl (.impl (.box g (.diag g tgt)) tgt) (.diag g tgt)).size ≤ K →
        ProvT K (.impl (.impl (.box g (.diag g tgt)) tgt) (.diag g tgt))
    | axKf (a b c K : Nat) (φ α : Formula) :
        a + b + α.size ≤ c →
        (Formula.impl (.box a (.impl φ α)) (.impl (.box b φ) (.box c α))).size ≤ K →
        ProvT K (.impl (.box a (.impl φ α)) (.impl (.box b φ) (.box c α)))
    | impS2 (φ ψ χ : Formula) (m₁ m₂ K : Nat) :
        ProvT m₁ (.impl φ (.impl ψ χ)) → ProvT m₂ (.impl φ ψ) →
        m₁ + m₂ + (Formula.impl φ χ).size ≤ K → ProvT K (.impl φ χ)
    | boxMono (a b K : Nat) (φ : Formula) :
        a ≤ b →
        (Formula.impl (.box a φ) (.box b φ)).size ≤ K →
        ProvT K (.impl (.box a φ) (.box b φ))
    | atomNeg (p q : Prog) (b aN : Action) (m : Nat) :
        AtomT m (.plays p q b) → b ≠ aN →
        m + (Formula.neg (.plays p q aN)).size ≤ k →
        ProvT k (.neg (.plays p q aN))
end

/-! ## 2. Soundness: trees map back to the `Prop` triple, verbatim. -/

mutual
  theorem PlaysT.sound {me o b : Prog} {a : Action} {n : Nat} :
      PlaysT me o b a n → PlaysProof me o b a n
    | .const => .const
    | .self t => .self t.sound
    | .opp t => .opp t.sound
    | .bot t => .bot t.sound
    | .sim t => .sim t.sound
    | .ite_t tb hr tp => .ite_t tb.sound hr tp.sound
    | .ite_f tb hr tq => .ite_f tb.sound hr tq.sound
    | .search_t tg tp => .search_t tg.sound tp.sound
    | .search_f tr tq => .search_f tr.sound tq.sound

  theorem AtomT.sound {k : Nat} {φ : Formula} : AtomT k φ → AtomProvable k φ
    | .mk t hn => .mk t.sound hn

  theorem ProvT.sound {k : Nat} {φ : Formula} : ProvT k φ → Provable k φ
    | .struct d hd => .struct ⟨d, hd⟩
    | .atom t => .atom t.sound
    | .weakenImpl φ ψ m t hle => .weakenImpl φ ψ m t.sound hle
    | .searchThenSearch_t k₁ k₂ m ψ₁ ψ₂ c0 c1 q me opp hme t hm hsz =>
        .searchThenSearch_t k₁ k₂ m ψ₁ ψ₂ c0 c1 q me opp hme t.sound hm hsz
    | .implTrans φ ψ χ a b t1 t2 hle => .implTrans φ ψ χ a b t1.sound t2.sound hle
    | .atomBoxImpl kBox p q a t hle => .atomBoxImpl kBox p q a t.sound hle
    | .boxIntro kIn K φ t hle => .boxIntro kIn K φ t.sound hle
    | .app k m₁ m₂ φ α t1 t2 hle => .app k m₁ m₂ φ α t1.sound t2.sound hle
    | .axK a b c m K φ α t hg1 hg2 => .axK a b c m K φ α t.sound hg1 hg2
    | .box4 a b K φ hg1 hg2 => .box4 a b K φ hg1 hg2
    | .diagF pm fb g K tgt t hle => .diagF pm fb g K tgt t.sound hle
    | .diagB pm fb g K tgt t hle => .diagB pm fb g K tgt t.sound hle
    | .axKf a b c K φ α hg1 hg2 => .axKf a b c K φ α hg1 hg2
    | .impS2 φ ψ χ m₁ m₂ K t1 t2 hle => .impS2 φ ψ χ m₁ m₂ K t1.sound t2.sound hle
    | .boxMono a b K φ hab hle => .boxMono a b K φ hab hle
    | .atomNeg p q b aN m t hne hle => .atomNeg p q b aN m t.sound hne hle
end

/-! ## 3. Completeness: every `Provable` has a tree (at the `Nonempty` level — all that
`Prop` elimination permits, and all that excision needs). -/

mutual
  theorem PlaysT.complete {me o b : Prog} {a : Action} {n : Nat} :
      PlaysProof me o b a n → Nonempty (PlaysT me o b a n)
    | .const => ⟨.const⟩
    | .self h => (PlaysT.complete h).elim fun t => ⟨.self t⟩
    | .opp h => (PlaysT.complete h).elim fun t => ⟨.opp t⟩
    | .bot h => (PlaysT.complete h).elim fun t => ⟨.bot t⟩
    | .sim h => (PlaysT.complete h).elim fun t => ⟨.sim t⟩
    | .ite_t hb hr hp =>
        (PlaysT.complete hb).elim fun tb =>
          (PlaysT.complete hp).elim fun tp => ⟨.ite_t tb hr tp⟩
    | .ite_f hb hr hq =>
        (PlaysT.complete hb).elim fun tb =>
          (PlaysT.complete hq).elim fun tq => ⟨.ite_f tb hr tq⟩
    | .search_t hg hp =>
        (ProvT.complete hg).elim fun tg =>
          (PlaysT.complete hp).elim fun tp => ⟨.search_t tg tp⟩
    | .search_f hr hq =>
        (ProvT.complete hr).elim fun tr =>
          (PlaysT.complete hq).elim fun tq => ⟨.search_f tr tq⟩

  theorem AtomT.complete {k : Nat} {φ : Formula} :
      AtomProvable k φ → Nonempty (AtomT k φ)
    | .mk h hn => (PlaysT.complete h).elim fun t => ⟨.mk t hn⟩

  theorem ProvT.complete {k : Nat} {φ : Formula} :
      Provable k φ → Nonempty (ProvT k φ)
    | .struct h => h.elim fun d hd => ⟨.struct d hd⟩
    | .atom h => (AtomT.complete h).elim fun t => ⟨.atom t⟩
    | .weakenImpl φ ψ m h hle =>
        (ProvT.complete h).elim fun t => ⟨.weakenImpl φ ψ m t hle⟩
    | .searchThenSearch_t k₁ k₂ m ψ₁ ψ₂ c0 c1 q me opp hme h hm hsz =>
        (ProvT.complete h).elim fun t =>
          ⟨.searchThenSearch_t k₁ k₂ m ψ₁ ψ₂ c0 c1 q me opp hme t hm hsz⟩
    | .implTrans φ ψ χ a b h1 h2 hle =>
        (ProvT.complete h1).elim fun t1 =>
          (ProvT.complete h2).elim fun t2 => ⟨.implTrans φ ψ χ a b t1 t2 hle⟩
    | .atomBoxImpl kBox p q a h hle =>
        (AtomT.complete h).elim fun t => ⟨.atomBoxImpl kBox p q a t hle⟩
    | .boxIntro kIn K φ h hle =>
        (ProvT.complete h).elim fun t => ⟨.boxIntro kIn K φ t hle⟩
    | .app k m₁ m₂ φ α h1 h2 hle =>
        (ProvT.complete h1).elim fun t1 =>
          (ProvT.complete h2).elim fun t2 => ⟨.app k m₁ m₂ φ α t1 t2 hle⟩
    | .axK a b c m K φ α h hg1 hg2 =>
        (ProvT.complete h).elim fun t => ⟨.axK a b c m K φ α t hg1 hg2⟩
    | .box4 a b K φ hg1 hg2 => ⟨.box4 a b K φ hg1 hg2⟩
    | .diagF pm fb g K tgt h hle =>
        (ProvT.complete h).elim fun t => ⟨.diagF pm fb g K tgt t hle⟩
    | .diagB pm fb g K tgt h hle =>
        (ProvT.complete h).elim fun t => ⟨.diagB pm fb g K tgt t hle⟩
    | .axKf a b c K φ α hg1 hg2 => ⟨.axKf a b c K φ α hg1 hg2⟩
    | .impS2 φ ψ χ m₁ m₂ K h1 h2 hle =>
        (ProvT.complete h1).elim fun t1 =>
          (ProvT.complete h2).elim fun t2 => ⟨.impS2 φ ψ χ m₁ m₂ K t1 t2 hle⟩
    | .boxMono a b K φ hab hle => ⟨.boxMono a b K φ hab hle⟩
    | .atomNeg p q b aN m h hne hle =>
        (AtomT.complete h).elim fun t => ⟨.atomNeg p q b aN m t hne hle⟩
end

/-- The substrate is exact: provability = tree existence. -/
theorem Provable_iff_nonempty_ProvT {k : Nat} {φ : Formula} :
    Provable k φ ↔ Nonempty (ProvT k φ) :=
  ⟨ProvT.complete, fun ⟨t⟩ => t.sound⟩

/-! ## 4. The gate residue: which cuts a tree actually uses (D1).

`gateOK G t` holds when every formula at one of T42's six gated positions — throughout
the tree, INCLUDING the `Provable` cites inside the atom layer's `search_t`/`search_f`
guards — satisfies `G`. This is the tree-level object the judgment-local program could
never see: the cut DIET of one specific derivation, not of all derivations at once. -/

mutual
  def PlaysT.gateOK (G : Formula → Prop) :
      {me o b : Prog} → {a : Action} → {n : Nat} → PlaysT me o b a n → Prop
    | _, _, _, _, _, .const => True
    | _, _, _, _, _, .self t => t.gateOK G
    | _, _, _, _, _, .opp t => t.gateOK G
    | _, _, _, _, _, .bot t => t.gateOK G
    | _, _, _, _, _, .sim t => t.gateOK G
    | _, _, _, _, _, .ite_t tb _ tp => tb.gateOK G ∧ tp.gateOK G
    | _, _, _, _, _, .ite_f tb _ tq => tb.gateOK G ∧ tq.gateOK G
    | _, _, _, _, _, .search_t tg tp => tg.gateOK G ∧ tp.gateOK G
    | _, _, _, _, _, .search_f tr tq => tr.gateOK G ∧ tq.gateOK G

  def AtomT.gateOK (G : Formula → Prop) : {k : Nat} → {φ : Formula} → AtomT k φ → Prop
    | _, _, .mk t _ => t.gateOK G

  def ProvT.gateOK (G : Formula → Prop) : {k : Nat} → {φ : Formula} → ProvT k φ → Prop
    | _, _, .struct _ _ => True
    | _, _, .atom t => t.gateOK G
    | _, _, .weakenImpl _ _ _ t _ => t.gateOK G
    | _, _, .searchThenSearch_t _ _ _ _ _ _ _ _ _ _ _ t _ _ => t.gateOK G
    | _, _, .implTrans _ ψ _ _ _ t1 t2 _ => G ψ ∧ t1.gateOK G ∧ t2.gateOK G
    | _, _, .atomBoxImpl _ _ _ _ t _ => t.gateOK G
    | _, _, .boxIntro _ _ _ t _ => t.gateOK G
    | _, _, .app _ _ _ φ _ t1 t2 _ => G φ ∧ t1.gateOK G ∧ t2.gateOK G
    | _, _, .axK a _ _ _ _ φ α t _ _ => G (.box a (.impl φ α)) ∧ t.gateOK G
    | _, _, .box4 _ _ _ _ _ _ => True
    | _, _, .diagF _ fb _ _ tgt t _ => G (.impl (.box fb tgt) tgt) ∧ t.gateOK G
    | _, _, .diagB _ fb _ _ tgt t _ => G (.impl (.box fb tgt) tgt) ∧ t.gateOK G
    | _, _, .axKf _ _ _ _ _ _ _ _ => True
    | _, _, .impS2 _ ψ _ _ _ _ t1 t2 _ => G ψ ∧ t1.gateOK G ∧ t2.gateOK G
    | _, _, .boxMono _ _ _ _ _ _ => True
    | _, _, .atomNeg _ _ _ _ _ t _ _ => t.gateOK G
end

/-! ## 5. The transfer: a tree with a passing gate residue lands in `ProvableG G`. -/

mutual
  theorem PlaysT.toG {G : Formula → Prop} {me o b : Prog} {a : Action} {n : Nat} :
      (t : PlaysT me o b a n) → t.gateOK G → PlaysProofG G me o b a n
    | .const, _ => .const
    | .self t, h => .self (t.toG h)
    | .opp t, h => .opp (t.toG h)
    | .bot t, h => .bot (t.toG h)
    | .sim t, h => .sim (t.toG h)
    | .ite_t tb hr tp, h => .ite_t (tb.toG h.1) hr (tp.toG h.2)
    | .ite_f tb hr tq, h => .ite_f (tb.toG h.1) hr (tq.toG h.2)
    | .search_t tg tp, h => .search_t (tg.toG h.1) (tp.toG h.2)
    | .search_f tr tq, h => .search_f (tr.toG h.1) (tq.toG h.2)

  theorem AtomT.toG {G : Formula → Prop} {k : Nat} {φ : Formula} :
      (t : AtomT k φ) → t.gateOK G → AtomProvableG G k φ
    | .mk t hn, h => .mk (t.toG h) hn

  theorem ProvT.toG {G : Formula → Prop} {k : Nat} {φ : Formula} :
      (t : ProvT k φ) → t.gateOK G → ProvableG G k φ
    | .struct d hd, _ => .struct ⟨d, hd⟩
    | .atom t, h => .atom (t.toG h)
    | .weakenImpl φ ψ m t hle, h => .weakenImpl φ ψ m (t.toG h) hle
    | .searchThenSearch_t k₁ k₂ m ψ₁ ψ₂ c0 c1 q me opp hme t hm hsz, h =>
        .searchThenSearch_t k₁ k₂ m ψ₁ ψ₂ c0 c1 q me opp hme (t.toG h) hm hsz
    | .implTrans φ ψ χ a b t1 t2 hle, h =>
        .implTrans φ ψ χ a b (t1.toG h.2.1) (t2.toG h.2.2) hle h.1
    | .atomBoxImpl kBox p q a t hle, h => .atomBoxImpl kBox p q a (t.toG h) hle
    | .boxIntro kIn K φ t hle, h => .boxIntro kIn K φ (t.toG h) hle
    | .app k m₁ m₂ φ α t1 t2 hle, h =>
        .app k m₁ m₂ φ α (t1.toG h.2.1) (t2.toG h.2.2) hle h.1
    | .axK a b c m K φ α t hg1 hg2, h => .axK a b c m K φ α (t.toG h.2) hg1 hg2 h.1
    | .box4 a b K φ hg1 hg2, _ => .box4 a b K φ hg1 hg2
    | .diagF pm fb g K tgt t hle, h => .diagF pm fb g K tgt (t.toG h.2) hle h.1
    | .diagB pm fb g K tgt t hle, h => .diagB pm fb g K tgt (t.toG h.2) hle h.1
    | .axKf a b c K φ α hg1 hg2, _ => .axKf a b c K φ α hg1 hg2
    | .impS2 φ ψ χ m₁ m₂ K t1 t2 hle, h =>
        .impS2 φ ψ χ m₁ m₂ K (t1.toG h.2.1) (t2.toG h.2.2) hle h.1
    | .boxMono a b K φ hab hle, _ => .boxMono a b K φ hab hle
    | .atomNeg p q b aN m t hne hle, h => .atomNeg p q b aN m (t.toG h) hne hle
end

/-! ## 6. The official reduction: CutRelevance is now a statement about trees. -/

/-- **Tree-level cut relevance**: every provable root has SOME tree whose cut diet is
    `N₀`-literal-bounded. This is what excision (milestone D2) must produce — and unlike
    every judgment-local formulation, it is not refuted by dead implications: excision is
    free to REPLACE the tree, not just describe it. -/
def TreeCutRelevance (N₀ : Nat → Formula → Nat) : Prop :=
  ∀ k φ, Provable k φ → ∃ t : ProvT k φ, t.gateOK (T42.litGate (N₀ k φ))

/-- The reduction: tree-level cut relevance implies the T4.1b conjecture. -/
theorem tree_cutRelevance {N₀ : Nat → Formula → Nat} (h : TreeCutRelevance N₀) :
    T42.CutRelevance N₀ :=
  fun k φ hp => (h k φ hp).elim fun t hg => t.toG hg

/-- The modest variant — the form T44's decider actually consumes. -/
def TreeModestRelevance (N₀ : Nat → Formula → Nat) : Prop :=
  ∀ k φ, Provable k φ → ∃ t : ProvT k φ, t.gateOK (T44.modestGate (N₀ k φ))

theorem tree_modestRelevance {N₀ : Nat → Formula → Nat} (h : TreeModestRelevance N₀)
    (k : Nat) (φ : Formula) (hp : Provable k φ) :
    ProvableG (T44.modestGate (N₀ k φ)) k φ :=
  (h k φ hp).elim fun t hg => t.toG hg

/-! ## 7. D2a — the excision toolkit's first layer.

Three foundations the rewrite system needs everywhere, plus the first excision:

  * `ProvT.mono` — budget monotonicity by ROOT re-gating only (every constructor's
    conclusion budget appears in exactly one relaxable `≤`-gate; the subtree is reused,
    so the rewrite system may lift budgets freely without touching structure);
  * `ProvT.mono_gateOK` — re-gating does not change the cut diet;
  * `ProvT.impl_size_le` — every implication-concluding rule PAYS its conclusion's size
    (`struct` via `Derivation.concl_size_le`; atoms cannot conclude implications), the
    arithmetic backbone of the crossing analysis;
  * `cross_weaken` — the first excision: an `app` whose function node is
    `weakenImpl`-headed never needed its argument; the consequent's own subtree serves,
    within budget, with the SAME cut diet (`cross_weaken_gateOK`). This is the entry
    point through which every §5e counterexample dies. -/

/-- Budget monotonicity: relax the root gate, reuse the tree. -/
def ProvT.mono {k k' : Nat} {φ : Formula} (h : k ≤ k') : ProvT k φ → ProvT k' φ
  | .struct d hd => .struct d (le_trans hd h)
  | .atom (.mk t hn) => .atom (.mk t (le_trans hn h))
  | .weakenImpl φ ψ m t hle => .weakenImpl φ ψ m t (le_trans hle h)
  | .searchThenSearch_t k₁ k₂ m ψ₁ ψ₂ c0 c1 q me opp hme t hm hsz =>
      .searchThenSearch_t k₁ k₂ m ψ₁ ψ₂ c0 c1 q me opp hme t hm (le_trans hsz h)
  | .implTrans φ ψ χ a b t1 t2 hle => .implTrans φ ψ χ a b t1 t2 (le_trans hle h)
  | .atomBoxImpl kBox p q a t hle => .atomBoxImpl kBox p q a t (le_trans hle h)
  | .boxIntro kIn K φ t hle => .boxIntro kIn _ φ t (le_trans hle h)
  | .app k m₁ m₂ φ α t1 t2 hle => .app _ m₁ m₂ φ α t1 t2 (le_trans hle h)
  | .axK a b c m K φ α t hg1 hg2 => .axK a b c m _ φ α t hg1 (le_trans hg2 h)
  | .box4 a b K φ hg1 hg2 => .box4 a b _ φ hg1 (le_trans hg2 h)
  | .diagF pm fb g K tgt t hle => .diagF pm fb g _ tgt t (le_trans hle h)
  | .diagB pm fb g K tgt t hle => .diagB pm fb g _ tgt t (le_trans hle h)
  | .axKf a b c K φ α hg1 hg2 => .axKf a b c _ φ α hg1 (le_trans hg2 h)
  | .impS2 φ ψ χ m₁ m₂ K t1 t2 hle => .impS2 φ ψ χ m₁ m₂ _ t1 t2 (le_trans hle h)
  | .boxMono a b K φ hab hle => .boxMono a b _ φ hab (le_trans hle h)
  | .atomNeg p q b aN m t hne hle => .atomNeg p q b aN m t hne (le_trans hle h)

/-- Re-gating does not change the cut diet. -/
theorem ProvT.mono_gateOK {G : Formula → Prop} {k k' : Nat} {φ : Formula}
    (h : k ≤ k') : (t : ProvT k φ) → ((t.mono h).gateOK G ↔ t.gateOK G)
  | .struct _ _ => Iff.rfl
  | .atom (.mk _ _) => Iff.rfl
  | .weakenImpl _ _ _ _ _ => Iff.rfl
  | .searchThenSearch_t _ _ _ _ _ _ _ _ _ _ _ _ _ _ => Iff.rfl
  | .implTrans _ _ _ _ _ _ _ _ => Iff.rfl
  | .atomBoxImpl _ _ _ _ _ _ => Iff.rfl
  | .boxIntro _ _ _ _ _ => Iff.rfl
  | .app _ _ _ _ _ _ _ _ => Iff.rfl
  | .axK _ _ _ _ _ _ _ _ _ _ => Iff.rfl
  | .box4 _ _ _ _ _ _ => Iff.rfl
  | .diagF _ _ _ _ _ _ _ => Iff.rfl
  | .diagB _ _ _ _ _ _ _ => Iff.rfl
  | .axKf _ _ _ _ _ _ _ _ => Iff.rfl
  | .impS2 _ _ _ _ _ _ _ _ _ => Iff.rfl
  | .boxMono _ _ _ _ _ _ => Iff.rfl
  | .atomNeg _ _ _ _ _ _ _ _ => Iff.rfl

/-- Every implication-concluding node pays its conclusion's size into its budget.
    (Atoms conclude only `.plays`, so the `atom` arm is uninhabited.) -/
theorem ProvT.impl_size_le {k : Nat} {A B : Formula} :
    ProvT k (.impl A B) → (Formula.impl A B).size ≤ k
  | .struct d hd => le_trans d.concl_size_le hd
  | .atom t => nomatch t
  | .weakenImpl _ _ _ _ hle => by omega
  | .searchThenSearch_t _ _ _ _ _ _ _ _ _ _ _ _ _ hsz => by omega
  | .implTrans _ _ _ _ _ _ _ hle => by omega
  | .atomBoxImpl _ _ _ _ _ hle => by omega
  | .app _ _ _ _ _ _ _ hle => by omega
  | .axK _ _ _ _ _ _ _ _ _ hg2 => by omega
  | .box4 _ _ _ _ _ hg2 => by omega
  | .diagF _ _ _ _ _ _ hle => by omega
  | .diagB _ _ _ _ _ _ hle => by omega
  | .axKf _ _ _ _ _ _ _ hg2 => by omega
  | .impS2 _ _ _ _ _ _ _ _ hle => by omega
  | .boxMono _ _ _ _ _ hle => by omega

/-- **The first excision**: `app (weakenImpl tw) targ` never needed `targ` — the
    consequent's subtree `tw` serves within the app node's budget. The wild argument
    (any of §5e's dead implications' discharges) is simply dropped. -/
def cross_weaken {k m₁ m₂ m : Nat} {B α : Formula}
    (tw : ProvT m α) (h1 : m + (Formula.impl B α).size ≤ m₁)
    (h2 : m₁ + m₂ + α.size ≤ k) : ProvT k α :=
  tw.mono (by simp only [Formula.size] at h1; omega)

/-- The excised tree's cut diet is `tw`'s own — in particular, the dropped argument's
    cuts (and the gate obligation `G B` the `app` node carried) vanish with it. -/
theorem cross_weaken_gateOK {G : Formula → Prop} {k m₁ m₂ m : Nat} {B α : Formula}
    (tw : ProvT m α) (h1 : m + (Formula.impl B α).size ≤ m₁)
    (h2 : m₁ + m₂ + α.size ≤ k) (hg : tw.gateOK G) :
    (cross_weaken tw h1 h2).gateOK G :=
  (tw.mono_gateOK _).mpr hg

/-! ## 8. D2b probe results — the compression ceiling (see note §5g for the full record).

Designing the `spineCross` master induction arm-by-arm surfaced (a) the GENTZEN WALL —
`impS2`'s crossing arm DUPLICATES one discharge, breaking every total-size termination
measure and strict-budget preservation at once (the classic contraction problem; the fix
is rank-lexicographic measures or shared-discharge environments — a Gentzen-scale
formalization, recorded in the note) — and (b) a major REDUCTION: with C0's local
literal bound and the backward-tameness observations, the conjecture's literal half is
free, and everything rests on the ATOM-MODESTY of some minimal tree. The lemma anchoring
the reduction is the compression ceiling: box subscripts reachable at budget `k` are
`< 2^k`, because every box-concluding node PAYS its conclusion — `boxIntro` and `app` by
their gates, `struct` never (the Type layer concludes no box), atoms never. So
budget-compression is bounded by the budget's own exponential, and the tower of
cite-budget escalations is fueled ONLY by cut atoms' fresh programs — the exact frontier
the modest gate polices. -/

/-- Every box-concluding node pays its conclusion's size (only `boxIntro` and `app` can
    conclude a box; the Type layer cannot — `derivation_no_box`). -/
theorem ProvT.box_size_le {k c : Nat} {ψ : Formula} :
    ProvT k (.box c ψ) → (Formula.box c ψ).size ≤ k
  | .struct d _ => (PD.T48.derivation_no_box d).elim
  | .atom t => nomatch t
  | .boxIntro _ _ _ _ hle => by omega
  | .app _ _ _ _ _ _ _ hle => by omega

/-- **The compression ceiling**: a box judgment reachable at budget `k` has subscript
    `< 2^k` — the numeral pays its logarithm into the size, which the node pays into the
    budget. Budget compression exists (§5e) but is exponentially bounded. -/
theorem ProvT.box_subscript_lt {k c : Nat} {ψ : Formula} (t : ProvT k (.box c ψ)) :
    c < 2 ^ k := by
  have h := t.box_size_le
  simp only [Formula.size] at h
  rcases Nat.eq_zero_or_pos c with hc | hc
  · exact hc ▸ Nat.two_pow_pos k
  · have hlog : Nat.log2 c < k := by omega
    exact (Nat.log2_lt (by omega)).mp hlog

/-! ## 9. D2c — `boxInvGo`: fueled box-content extraction, correct by construction.

The §5g plan called for `box_inv` + `spineCross`; designing them surfaced two collapses:

  * the spine machinery is a STACK MACHINE — hold the pending discharges as a dependent
    stack (`DStack ξ core`: discharge trees for `ξ`'s implication spine down to `core`),
    PUSH at `app`, DROP at `weakenImpl` (excision!), TRANSFORM at the chain rules
    (`implTrans` composes onto the head; `impS2` duplicates it — the Gentzen
    contraction, which FUEL absorbs), CONSUME at the modal leaves;
  * each modal leaf's own gate PAYS the extraction: `axK`/`axKf` return an `app` of the
    dived contents at `≤ a + b + |α| ≤ c` (the gate, verbatim — Observation 1 is
    literally the budget proof); `box4` re-boxes the lifted content at `a + |□aφ| ≤ b`;
    `boxMono` passes `a ≤ b`; `boxIntro`'s subscript IS its content budget.

Making the machine FUEL-indexed sidesteps the termination question entirely (the
`decFull` pattern), and computing the result type from the core
(`BoxContent : Formula → Type`) makes every `some` CORRECT BY CONSTRUCTION: whenever
extraction halts, **a box's content is derivable within the box's own subscript** — box
honesty, the load-bearing dive of the excision plan. Shape-excluded arms (`struct`,
atoms, `searchThenSearch_t`/`diagB` tails) return `none`; their unreachability for box
cores is part of `BoxInvTotal`, the isolated remaining obligation, where the modest-pool
rank argument lives. (Cut-diet bookkeeping for extracted trees is D2d.) -/

/-- Discharge stack: trees for each antecedent of `ξ`'s implication spine, down to
    `core`. -/
inductive DStack : Formula → Formula → Type where
  | nil : DStack core core
  | cons {B rest core : Formula} (m : Nat) (t : ProvT m B) (s : DStack rest core) :
      DStack (.impl B rest) core

/-- What extraction owes for a given core: for a box, its content within the
    subscript; for a diag, the implication it abbreviates (budget-free — the leaf
    gates downstream re-pay). -/
def CoreContent : Formula → Type
  | .box c ψ => Σ' m', (ProvT m' ψ) ×' (m' ≤ c)
  | .diag g tgt => Σ' m', ProvT m' (.impl (.box g (.diag g tgt)) tgt)
  | _ => PEmpty

/-- The fueled extractor. `none` = out of fuel (or a shape-excluded arm); every `some`
    is a genuine content tree within the subscript budget, by type. The tree is matched
    first, the stack in small nested matches per arm — one dependent match per
    constructor keeps the equational theorems generable (a combined deep match defeats
    the equation compiler). -/
def boxInvGo : (fuel : Nat) → {m : Nat} → {ξ core : Formula} →
    (t : ProvT m ξ) → DStack ξ core → Option (CoreContent core)
  | 0, _, _, _, _, _ => none
  | fuel + 1, _, _, _, t, stack =>
    match t with
    -- the box itself
    | .boxIntro kIn _ φ tc _ =>
        match stack with
        | .nil => some ⟨kIn, tc, Nat.le_refl _⟩
    -- spine navigation
    | .app _ m₁ m₂ φ' α f x _ => boxInvGo fuel f (.cons m₂ x stack)
    | .weakenImpl _ _ _ tw _ =>
        (match stack with
         | .cons _ _ s' => boxInvGo fuel tw s'
         | .nil => none)
    | .implTrans φ' ψmid χ' a b tA tB _ =>
        (match stack with
         | .cons mD dB s' =>
             boxInvGo fuel tB (.cons (a + mD + ψmid.size)
               (.app (a + mD + ψmid.size) a mD φ' ψmid tA dB (Nat.le_refl _)) s')
         | .nil => none)
    | .impS2 φ' ψ' χ' m₁' m₂' _ tf tx _ =>
        (match stack with
         | .cons mD dB s' =>
             boxInvGo fuel tf (.cons mD dB (.cons (m₂' + mD + ψ'.size)
               (.app (m₂' + mD + ψ'.size) m₂' mD φ' ψ' tx dB (Nat.le_refl _)) s'))
         | .nil => none)
    -- the Löb pair: diag is a second core; diagB is its base, diagF consumes one
    | .diagB _ _ _ _ _ _ _ =>
        (match stack with
         | .cons mD d s' => (match s' with | .nil => some ⟨mD, d⟩)
         | .nil => none)
    | .diagF _ _ g _ tgt _ _ =>
        (match stack with
         | .cons _ d1 s' =>
             (match s' with
              | .cons mD2 d2 s'' =>
                  (match boxInvGo fuel d1 (.nil : DStack (.diag g tgt) (.diag g tgt)) with
                   | some ⟨mx, x⟩ => boxInvGo fuel x (.cons mD2 d2 s'')
                   | none => none)
              | .nil => none)
         | .nil => none)
    -- modal leaves: the gates pay the extraction
    | .atomBoxImpl kBox p q a cert _ =>
        (match stack with
         | .cons _ _ s' =>
             (match s' with | .nil => some ⟨kBox, .atom cert, Nat.le_refl _⟩)
         | .nil => none)
    | .boxMono a' b' _ φ' hab _ =>
        (match stack with
         | .cons mD dB s' =>
             (match s' with
              | .nil =>
                  match boxInvGo fuel dB .nil with
                  | some ⟨mc, tc, hc⟩ => some ⟨mc, tc, by omega⟩
                  | none => none)
         | .nil => none)
    | .box4 a' b' _ φ' hg1 _ =>
        (match stack with
         | .cons mD dB s' =>
             (match s' with
              | .nil =>
                  match boxInvGo fuel dB .nil with
                  | some ⟨mc, tc, hc⟩ =>
                      some ⟨a' + (Formula.box a' φ').size,
                        .boxIntro a' _ φ' (tc.mono hc) (Nat.le_refl _), hg1⟩
                  | none => none)
         | .nil => none)
    | .axK a'' b'' c'' m'' _ φ' α' tP hg1 _ =>
        (match stack with
         | .cons mD dB s' =>
             (match s' with
              | .nil =>
                  match boxInvGo fuel tP .nil, boxInvGo fuel dB .nil with
                  | some ⟨mP, tPc, hP⟩, some ⟨mx, txc, hx⟩ =>
                      some ⟨mP + mx + α'.size,
                        .app (mP + mx + α'.size) mP mx φ' α' tPc txc (Nat.le_refl _),
                        by omega⟩
                  | _, _ => none)
         | .nil => none)
    | .axKf a'' b'' c'' _ φ' α' hg1 _ =>
        (match stack with
         | .cons _ d1 s' =>
             (match s' with
              | .cons _ d2 s'' =>
                  (match s'' with
                   | .nil =>
                       match boxInvGo fuel d1 .nil, boxInvGo fuel d2 .nil with
                       | some ⟨mP, tPc, hP⟩, some ⟨mx, txc, hx⟩ =>
                           some ⟨mP + mx + α'.size,
                             .app (mP + mx + α'.size) mP mx φ' α' tPc txc
                               (Nat.le_refl _), by omega⟩
                       | _, _ => none)
              | .nil => none)
         | .nil => none)
    -- shape-excluded or blocked: sound to give up (unreachability = totality's job)
    | .struct _ _ => none
    | .atom _ => none
    | .searchThenSearch_t _ _ _ _ _ _ _ _ _ _ _ _ _ _ => none
    | .atomNeg _ _ _ _ _ _ _ _ => none

/-- Box-content extraction: any box judgment, content within the subscript — given
    fuel. -/
def boxInv (fuel : Nat) {m c : Nat} {ψ : Formula} (t : ProvT m (.box c ψ)) :
    Option (CoreContent (.box c ψ)) :=
  boxInvGo fuel t .nil

/-- The isolated remaining obligation (the modest-pool rank argument's target): the
    extractor halts on enough fuel. -/
def BoxInvTotal : Prop :=
  ∀ {m c : Nat} {ψ : Formula} (t : ProvT m (.box c ψ)), ∃ fuel, (boxInv fuel t).isSome

/-! ## 10. The extractor RUNS — `#eval` demos on real trees.

`deadJ`'s wild box (T48 §11) rebuilt as a tree, then hidden behind an `app`/`weakenImpl`
detour: the machine navigates the spine, drops the never-needed discharge, and returns
the content at exactly the subscript's budget. -/

private def demoA : ProvT 100 PD.T48.wildA :=
  .struct (.eqRefl PD.T48.wildQ) (by decide)

private def demoImpl : ProvT 200 (.impl PD.T48.psi0 PD.T48.wildA) :=
  .weakenImpl PD.T48.psi0 PD.T48.wildA 100 demoA (by decide)

private def demoBox : ProvT 500 (.box 200 (.impl PD.T48.psi0 PD.T48.wildA)) :=
  .boxIntro 200 500 _ demoImpl (by decide)

/-- The same box behind a detour: `app (weakenImpl demoBox) demoA`. -/
private def demoDetour : ProvT 900 (.box 200 (.impl PD.T48.psi0 PD.T48.wildA)) :=
  .app 900 700 100 PD.T48.wildA _
    (.weakenImpl PD.T48.wildA _ 500 demoBox (by decide)) demoA (by decide)

-- Extracted content budget: the box's own subscript.
#eval match boxInv 10 demoBox with
  | some ⟨m', _, _⟩ => s!"direct: extracted at budget {m'}"
  | none => "direct: out of fuel"

#eval match boxInv 10 demoDetour with
  | some ⟨m', _, _⟩ => s!"detour: extracted at budget {m'}"
  | none => "detour: out of fuel"

/-! The Löb path: a `diagF` node whose diag discharge routes through `diagB`, ending at
`demoBox` — the machine unfolds the fixpoint pair and extracts the inner box's content. -/

private def demoTgt : Formula := .box 200 (.impl PD.T48.psi0 PD.T48.wildA)

private def demoLob : ProvT 600 (.impl (.box 44 demoTgt) demoTgt) :=
  .weakenImpl _ demoTgt 500 demoBox (by decide)

private def demoXz : ProvT 700 (.impl (.box 5000 (.diag 5000 demoTgt)) demoTgt) :=
  .weakenImpl _ demoTgt 500 demoBox (by decide)

private def demoD1 : ProvT 2000 (.diag 5000 demoTgt) :=
  .app 2000 1000 700 _ _ (.diagB 600 44 5000 1000 demoTgt demoLob (by decide))
    demoXz (by decide)

private def demoD2 : ProvT 6000 (.box 5000 (.diag 5000 demoTgt)) :=
  .boxIntro 5000 6000 _ (ProvT.mono (by omega) demoD1) (by decide)

private def demoDiagF :
    ProvT 1000 (.impl (.diag 5000 demoTgt)
      (.impl (.box 5000 (.diag 5000 demoTgt)) demoTgt)) :=
  .diagF 600 44 5000 1000 demoTgt demoLob (by decide)

#eval match boxInvGo 20 demoDiagF (.cons 2000 demoD1 (.cons 6000 demoD2 .nil)) with
  | some ⟨m', _, _⟩ => s!"löb: extracted at budget {m'}"
  | none => "löb: out of fuel"

/-! ## 11. D2e part 1 — the totality toolkit: weight, contraction-freedom, and the
result-size bound.

The master totality theorem (next) runs by strong induction on the lex measure
`(wt t + wt s, wt t)` — the D2d ledger showed every arm decreases it strictly except
`implTrans` (second component) and `impS2` (excluded here: the Gentzen contraction).
The `diagF` arm's decrease needs one substantive fact proven here: **extraction never
manufactures weight** — `boxInvGo`'s result weighs no more than the state it consumed
(`boxInvGo_wt_le`). The bound genuinely FAILS on `impS2` (the duplicated discharge adds
its weight), so the lemma carries the contraction-freedom hypothesis — the free
fragment is exactly where extraction is weight-non-increasing. -/

/-- Walkable weight: the machine only ever walks the `ProvT` layer (atom certificates
    and `Derivation`s are terminal), so those count 1. -/
def ProvT.wt : {m : Nat} → {φ : Formula} → ProvT m φ → Nat
  | _, _, .struct _ _ => 1
  | _, _, .atom _ => 1
  | _, _, .weakenImpl _ _ _ t _ => t.wt + 1
  | _, _, .searchThenSearch_t _ _ _ _ _ _ _ _ _ _ _ _ _ _ => 1
  | _, _, .implTrans _ _ _ _ _ t1 t2 _ => t1.wt + t2.wt + 1
  | _, _, .atomBoxImpl _ _ _ _ _ _ => 1
  | _, _, .boxIntro _ _ _ t _ => t.wt + 1
  | _, _, .app _ _ _ _ _ t1 t2 _ => t1.wt + t2.wt + 1
  | _, _, .axK _ _ _ _ _ _ _ t _ _ => t.wt + 1
  | _, _, .box4 _ _ _ _ _ _ => 1
  | _, _, .diagF _ _ _ _ _ t _ => t.wt + 1
  | _, _, .diagB _ _ _ _ _ t _ => t.wt + 1
  | _, _, .axKf _ _ _ _ _ _ _ _ => 1
  | _, _, .impS2 _ _ _ _ _ _ t1 t2 _ => t1.wt + t2.wt + 1
  | _, _, .boxMono _ _ _ _ _ _ => 1
  | _, _, .atomNeg _ _ _ _ _ _ _ _ => 1

theorem ProvT.wt_pos {m : Nat} {φ : Formula} : (t : ProvT m φ) → 1 ≤ t.wt
  | .struct _ _ | .atom _ | .atomBoxImpl _ _ _ _ _ _ | .box4 _ _ _ _ _ _
  | .axKf _ _ _ _ _ _ _ _ | .boxMono _ _ _ _ _ _ | .atomNeg _ _ _ _ _ _ _ _
  | .searchThenSearch_t _ _ _ _ _ _ _ _ _ _ _ _ _ _ => Nat.le_refl _
  | .weakenImpl _ _ _ _ _
  | .implTrans _ _ _ _ _ _ _ _ | .boxIntro _ _ _ _ _ | .app _ _ _ _ _ _ _ _
  | .axK _ _ _ _ _ _ _ _ _ _ | .diagF _ _ _ _ _ _ _ | .diagB _ _ _ _ _ _ _
  | .impS2 _ _ _ _ _ _ _ _ _ => by simp [ProvT.wt]

def DStack.wt : {ξ core : Formula} → DStack ξ core → Nat
  | _, _, .nil => 0
  | _, _, .cons _ t s => t.wt + s.wt

/-- Contraction-freedom: no `impS2` node anywhere in the walkable layer. -/
def ProvT.freeS2 : {m : Nat} → {φ : Formula} → ProvT m φ → Prop
  | _, _, .impS2 _ _ _ _ _ _ _ _ _ => False
  | _, _, .weakenImpl _ _ _ t _ => t.freeS2
  | _, _, .searchThenSearch_t _ _ _ _ _ _ _ _ _ _ _ t _ _ => t.freeS2
  | _, _, .implTrans _ _ _ _ _ t1 t2 _ => t1.freeS2 ∧ t2.freeS2
  | _, _, .boxIntro _ _ _ t _ => t.freeS2
  | _, _, .app _ _ _ _ _ t1 t2 _ => t1.freeS2 ∧ t2.freeS2
  | _, _, .axK _ _ _ _ _ _ _ t _ _ => t.freeS2
  | _, _, .diagF _ _ _ _ _ t _ => t.freeS2
  | _, _, .diagB _ _ _ _ _ t _ => t.freeS2
  | _, _, _ => True

def DStack.freeS2 : {ξ core : Formula} → DStack ξ core → Prop
  | _, _, .nil => True
  | _, _, .cons _ t s => t.freeS2 ∧ s.freeS2

/-- Re-gating preserves contraction-freedom. -/
theorem ProvT.mono_freeS2 {k k' : Nat} {φ : Formula}
    (h : k ≤ k') : (t : ProvT k φ) → ((t.mono h).freeS2 ↔ t.freeS2)
  | .struct _ _ => Iff.rfl
  | .atom (.mk _ _) => Iff.rfl
  | .weakenImpl _ _ _ _ _ => Iff.rfl
  | .searchThenSearch_t _ _ _ _ _ _ _ _ _ _ _ _ _ _ => Iff.rfl
  | .implTrans _ _ _ _ _ _ _ _ => Iff.rfl
  | .atomBoxImpl _ _ _ _ _ _ => Iff.rfl
  | .boxIntro _ _ _ _ _ => Iff.rfl
  | .app _ _ _ _ _ _ _ _ => Iff.rfl
  | .axK _ _ _ _ _ _ _ _ _ _ => Iff.rfl
  | .box4 _ _ _ _ _ _ => Iff.rfl
  | .diagF _ _ _ _ _ _ _ => Iff.rfl
  | .diagB _ _ _ _ _ _ _ => Iff.rfl
  | .axKf _ _ _ _ _ _ _ _ => Iff.rfl
  | .impS2 _ _ _ _ _ _ _ _ _ => Iff.rfl
  | .boxMono _ _ _ _ _ _ => Iff.rfl
  | .atomNeg _ _ _ _ _ _ _ _ => Iff.rfl

/-- Re-gating preserves weight. -/
theorem ProvT.mono_wt {k k' : Nat} {φ : Formula}
    (h : k ≤ k') : (t : ProvT k φ) → (t.mono h).wt = t.wt
  | .struct _ _ => rfl
  | .atom (.mk _ _) => rfl
  | .weakenImpl _ _ _ _ _ => rfl
  | .searchThenSearch_t _ _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl
  | .implTrans _ _ _ _ _ _ _ _ => rfl
  | .atomBoxImpl _ _ _ _ _ _ => rfl
  | .boxIntro _ _ _ _ _ => rfl
  | .app _ _ _ _ _ _ _ _ => rfl
  | .axK _ _ _ _ _ _ _ _ _ _ => rfl
  | .box4 _ _ _ _ _ _ => rfl
  | .diagF _ _ _ _ _ _ _ => rfl
  | .diagB _ _ _ _ _ _ _ => rfl
  | .axKf _ _ _ _ _ _ _ _ => rfl
  | .impS2 _ _ _ _ _ _ _ _ _ => rfl
  | .boxMono _ _ _ _ _ _ => rfl
  | .atomNeg _ _ _ _ _ _ _ _ => rfl

/-- The weight of what extraction returns. -/
def CoreContent.wt : {core : Formula} → CoreContent core → Nat := fun {core} =>
  match core with
  | .box _ _ => fun r => r.2.1.wt
  | .diag _ _ => fun r => r.2.wt
  | .plays _ _ _ | .impl _ _ | .neg _ | .eq _ _ => fun r => nomatch r

/-- Contraction-freedom of what extraction returns. -/
def CoreContent.freeS2 : {core : Formula} → CoreContent core → Prop := fun {core} =>
  match core with
  | .box _ _ => fun r => r.2.1.freeS2
  | .diag _ _ => fun r => r.2.freeS2
  | .plays _ _ _ | .impl _ _ | .neg _ | .eq _ _ => fun r => nomatch r

/-- **Extraction never manufactures weight, and preserves contraction-freedom** (on the
    contraction-free fragment). The weight half is the substantive input to the `diagF`
    case of the totality measure; the freedom half is what lets the induction recurse
    through extracted trees. Both genuinely FAIL on `impS2` (the duplicated discharge),
    hence the freedom hypotheses. -/
theorem boxInvGo_wt_le : ∀ (F : Nat) {m : Nat} {ξ core : Formula}
    (t : ProvT m ξ) (s : DStack ξ core), t.freeS2 → s.freeS2 →
    ∀ {r : CoreContent core}, boxInvGo F t s = some r →
    r.wt ≤ t.wt + s.wt ∧ r.freeS2 := by
  intro F
  induction F with
  | zero => intro _ _ _ t s _ _ r h; simp [boxInvGo] at h
  | succ F ih =>
    intro m ξ core t s hf hs r h
    cases t with
    | boxIntro kIn K φ tc hle =>
        cases s with
        | nil =>
            simp only [boxInvGo] at h
            cases h
            exact ⟨by simp [CoreContent.wt, ProvT.wt, DStack.wt], hf⟩
    | app k m₁ m₂ φ' α f x hle =>
        simp only [boxInvGo] at h
        have := ih f (.cons m₂ x s) hf.1 ⟨hf.2, hs⟩ h
        simp only [ProvT.wt, DStack.wt] at *
        exact ⟨by omega, this.2⟩
    | weakenImpl φ' ψ' m' tw hle =>
        cases s with
        | nil => simp [boxInvGo] at h
        | cons mD d s' =>
            simp only [boxInvGo] at h
            have := ih tw s' hf hs.2 h
            simp only [ProvT.wt, DStack.wt] at *
            exact ⟨by omega, this.2⟩
    | implTrans φ' ψmid χ' a b tA tB hle =>
        cases s with
        | nil => simp [boxInvGo] at h
        | cons mD dB s' =>
            simp only [boxInvGo] at h
            have := ih tB (.cons _ (.app _ a mD φ' ψmid tA dB (Nat.le_refl _)) s')
              hf.2 ⟨⟨hf.1, hs.1⟩, hs.2⟩ h
            simp only [ProvT.wt, DStack.wt] at *
            exact ⟨by omega, this.2⟩
    | diagB pm fb g K tgt tP hle =>
        cases s with
        | nil => simp [boxInvGo] at h
        | cons mD d s' =>
            cases s' with
            | nil =>
                simp only [boxInvGo] at h
                cases h
                refine ⟨?_, hs.1⟩
                simp only [CoreContent.wt, ProvT.wt, DStack.wt]
                omega
    | diagF pm fb g K tgt tP hle =>
        cases s with
        | nil => simp [boxInvGo] at h
        | cons mD1 d1 s' =>
            cases s' with
            | nil => simp [boxInvGo] at h
            | cons mD2 d2 s'' =>
                simp only [boxInvGo] at h
                cases hd : boxInvGo F d1 (.nil : DStack (.diag g tgt) (.diag g tgt)) with
                | none => rw [hd] at h; exact absurd h (by simp)
                | some rx =>
                    rw [hd] at h
                    obtain ⟨mx, x⟩ := rx
                    have hx := ih d1 .nil hs.1 trivial hd
                    simp only [CoreContent.wt, CoreContent.freeS2, DStack.wt] at hx
                    have := ih x (.cons mD2 d2 s'') hx.2 ⟨hs.2.1, hs.2.2⟩ h
                    simp only [ProvT.wt, DStack.wt] at *
                    exact ⟨by omega, this.2⟩
    | atomBoxImpl kBox p q a cert hle =>
        cases s with
        | nil => simp [boxInvGo] at h
        | cons mD d s' =>
            cases s' with
            | nil =>
                simp only [boxInvGo] at h
                cases h
                refine ⟨?_, trivial⟩
                simp only [CoreContent.wt, ProvT.wt, DStack.wt]
                omega
    | boxMono a' b' K φ' hab hle =>
        cases s with
        | nil => simp [boxInvGo] at h
        | cons mD dB s' =>
            cases s' with
            | nil =>
                simp only [boxInvGo] at h
                cases hd : boxInvGo F dB (.nil : DStack (.box a' φ') (.box a' φ')) with
                | none => rw [hd] at h; exact absurd h (by simp)
                | some rc =>
                    rw [hd] at h
                    obtain ⟨mc, tc, hc⟩ := rc
                    cases h
                    have := ih dB .nil hs.1 trivial hd
                    simp only [CoreContent.wt, CoreContent.freeS2, ProvT.wt,
                      DStack.wt] at *
                    exact ⟨by omega, this.2⟩
    | box4 a' b' K φ' hg1 hle =>
        cases s with
        | nil => simp [boxInvGo] at h
        | cons mD dB s' =>
            cases s' with
            | nil =>
                simp only [boxInvGo] at h
                cases hd : boxInvGo F dB (.nil : DStack (.box a' φ') (.box a' φ')) with
                | none => rw [hd] at h; exact absurd h (by simp)
                | some rc =>
                    rw [hd] at h
                    obtain ⟨mc, tc, hc⟩ := rc
                    cases h
                    have := ih dB .nil hs.1 trivial hd
                    have hw := ProvT.mono_wt hc tc
                    simp only [CoreContent.wt, CoreContent.freeS2, ProvT.wt,
                      DStack.wt] at *
                    constructor
                    · omega
                    · exact (ProvT.mono_freeS2 hc tc).mpr this.2
    | axK a'' b'' c'' m'' K φ' α' tP hg1 hle =>
        cases s with
        | nil => simp [boxInvGo] at h
        | cons mD dB s' =>
            cases s' with
            | nil =>
                simp only [boxInvGo] at h
                cases hP : boxInvGo F tP
                    (.nil : DStack (.box a'' (.impl φ' α')) _) with
                | none => rw [hP] at h; exact absurd h (by simp)
                | some rP =>
                    cases hx : boxInvGo F dB (.nil : DStack (.box b'' φ') _) with
                    | none => rw [hP, hx] at h; exact absurd h (by simp)
                    | some rx =>
                        rw [hP, hx] at h
                        obtain ⟨mP, tPc, hPle⟩ := rP
                        obtain ⟨mx, txc, hxle⟩ := rx
                        cases h
                        have h1 := ih tP .nil hf trivial hP
                        have h2 := ih dB .nil hs.1 trivial hx
                        simp only [CoreContent.wt, CoreContent.freeS2, ProvT.wt,
                          DStack.wt] at *
                        exact ⟨by omega, h1.2, h2.2⟩
    | axKf a'' b'' c'' K φ' α' hg1 hle =>
        cases s with
        | nil => simp [boxInvGo] at h
        | cons mD1 d1 s' =>
            cases s' with
            | nil => simp [boxInvGo] at h
            | cons mD2 d2 s'' =>
                cases s'' with
                | nil =>
                    simp only [boxInvGo] at h
                    cases hP : boxInvGo F d1
                        (.nil : DStack (.box a'' (.impl φ' α')) _) with
                    | none => rw [hP] at h; exact absurd h (by simp)
                    | some rP =>
                        cases hx : boxInvGo F d2 (.nil : DStack (.box b'' φ') _) with
                        | none => rw [hP, hx] at h; exact absurd h (by simp)
                        | some rx =>
                            rw [hP, hx] at h
                            obtain ⟨mP, tPc, hPle⟩ := rP
                            obtain ⟨mx, txc, hxle⟩ := rx
                            cases h
                            have h1 := ih d1 .nil hs.1 trivial hP
                            have h2 := ih d2 .nil hs.2.1 trivial hx
                            simp only [CoreContent.wt, CoreContent.freeS2, ProvT.wt,
                              DStack.wt] at *
                            exact ⟨by omega, h1.2, h2.2⟩
    | impS2 φ' ψ' χ' m₁' m₂' K tf tx hle => exact absurd hf (by simp [ProvT.freeS2])
    | struct d hd => simp [boxInvGo] at h
    | atom t => simp [boxInvGo] at h
    | searchThenSearch_t k₁ k₂ m' ψ₁ ψ₂ c0 c1 q me opnt hme t hm hsz =>
        simp [boxInvGo] at h
    | atomNeg p q b aN m' t hne hle => simp [boxInvGo] at h

/-! ## 12. D2e-2 — THE MASTER TOTALITY THEOREM (contraction-free fragment).

`boxInvGo_total`: on contraction-free states with a box/diag core, the machine ALWAYS
halts with `some`, at fuel `(P+1)² + wt t + 1` for any potential bound
`P ≥ wt t + wt s`. The induction is on FUEL alone — every recursive call burns one unit,
and the D2d ledger's lex measure `(potential, wt t)` lives inside the threshold
arithmetic (`thr_step` for potential-dropping calls, `thr_same` for `implTrans`'s
same-potential/smaller-tree call; omega cannot see products, so `(P+1)²` is handled as
an atom with `Nat.mul_le_mul` and one expansion identity). The impossible arms close by
`IsCore` reduction, `DStack` index chasing, and `derivation_shape` (a plays-ended spine
never reaches a box/diag core). Corollary: **`boxInv_total_of_freeS2`** — box honesty is
TOTAL on the contraction-free fragment, with closed-form fuel. -/

/-- The cores the machine extracts. -/
def IsCore : Formula → Prop
  | .box _ _ => True
  | .diag _ _ => True
  | _ => False

/-- A plays-ended spine never reaches a box/diag core. -/
theorem EndsInPlays.no_core_stack {ξ core : Formula}
    (h : PD.T48.EndsInPlays ξ) (s : DStack ξ core) (hc : IsCore core) : False := by
  induction h with
  | plays => cases s; exact hc
  | impl _ ih =>
      cases s with
      | nil => exact hc
      | cons _ _ s' => exact ih s'

private theorem thr_step {P P' T T' F : Nat}
    (hF : (P+1)*(P+1) + T + 1 ≤ F) (h2 : P' + 1 ≤ P) (h3 : T' ≤ P') :
    (P'+1)*(P'+1) + T' + 1 + 1 ≤ F := by
  have e : (P+1)*(P+1) = P*P + 2*P + 1 := by
    rw [Nat.succ_mul, Nat.mul_succ]; omega
  have h4 : (P'+1)*(P'+1) ≤ P*P := Nat.mul_le_mul h2 h2
  omega

private theorem thr_same {P T T' F : Nat}
    (hF : (P+1)*(P+1) + T + 1 ≤ F) (h : T' + 1 ≤ T) :
    (P+1)*(P+1) + T' + 1 + 1 ≤ F := by omega

/-- **Master totality** (contraction-free fragment): the machine halts with `some`. -/
theorem boxInvGo_total : ∀ (F P : Nat) {m : Nat} {ξ core : Formula}
    (t : ProvT m ξ) (s : DStack ξ core), t.freeS2 → s.freeS2 → IsCore core →
    t.wt + s.wt ≤ P → (P+1)*(P+1) + t.wt + 1 ≤ F →
    (boxInvGo F t s).isSome := by
  intro F
  induction F with
  | zero =>
      intro P _ _ _ t s _ _ _ _ hF
      have := Nat.mul_pos (Nat.succ_pos P) (Nat.succ_pos P)
      omega
  | succ F ih =>
    intro P m ξ core t s hf hs hc hP hF
    cases t with
    | boxIntro kIn K φ tc hle =>
        cases s with
        | nil => simp [boxInvGo]
    | app k m₁ m₂ φ' α f x hle =>
        simp only [boxInvGo]
        have hx1 := x.wt_pos
        refine ih P f (.cons m₂ x s) hf.1 ⟨hf.2, hs⟩ hc ?_ ?_
        · simp only [ProvT.wt, DStack.wt] at *; omega
        · have := thr_same (T' := f.wt) hF (by simp only [ProvT.wt] at *; omega)
          omega
    | weakenImpl φ' ψ' m' tw hle =>
        cases s with
        | nil => exact hc.elim
        | cons mD d s' =>
            simp only [boxInvGo]
            refine ih P tw s' hf hs.2 hc ?_ ?_
            · simp only [ProvT.wt, DStack.wt] at *; omega
            · have := thr_same (T' := tw.wt) hF (by simp only [ProvT.wt] at *; omega)
              omega
    | implTrans φ' ψmid χ' a b tA tB hle =>
        cases s with
        | nil => exact hc.elim
        | cons mD dB s' =>
            simp only [boxInvGo]
            have h1 := tA.wt_pos
            refine ih P tB (.cons _ (.app _ a mD φ' ψmid tA dB (Nat.le_refl _)) s')
              hf.2 ⟨⟨hf.1, hs.1⟩, hs.2⟩ hc ?_ ?_
            · simp only [ProvT.wt, DStack.wt] at *; omega
            · have := thr_same (T' := tB.wt) hF (by simp only [ProvT.wt] at *; omega)
              omega
    | diagB pm fb g K tgt tP hle =>
        cases s with
        | nil => exact hc.elim
        | cons mD d s' =>
            cases s' with
            | nil => simp [boxInvGo]
    | diagF pm fb g K tgt tP hle =>
        cases s with
        | nil => exact hc.elim
        | cons mD1 d1 s' =>
            cases s' with
            | nil => exact hc.elim
            | cons mD2 d2 s'' =>
                simp only [boxInvGo]
                have htP := tP.wt_pos
                have hd2 := d2.wt_pos
                have hd1w := d1.wt_pos
                simp only [ProvT.wt, DStack.wt] at hP
                have hdive := ih d1.wt d1
                  (.nil : DStack (.diag g tgt) (.diag g tgt)) hs.1 trivial trivial
                  (by simp [DStack.wt])
                  (Nat.le_of_succ_le_succ
                    (thr_step (P' := d1.wt) hF (by omega) (Nat.le_refl _)))
                obtain ⟨rx, hd⟩ := Option.isSome_iff_exists.mp hdive
                rw [hd]
                have hxw := boxInvGo_wt_le F d1 .nil hs.1 trivial hd
                obtain ⟨mx, x⟩ := rx
                simp only [CoreContent.wt, CoreContent.freeS2, DStack.wt] at hxw
                obtain ⟨hxw1, hxf⟩ := hxw
                exact ih (P - 1) x (.cons mD2 d2 s'') hxf ⟨hs.2.1, hs.2.2⟩ hc
                  (by simp only [DStack.wt]; omega)
                  (by
                    have := thr_step (P' := P - 1) (T' := x.wt) hF
                      (by omega) (by omega)
                    omega)
    | atomBoxImpl kBox p q a cert hle =>
        cases s with
        | nil => exact hc.elim
        | cons mD d s' =>
            cases s' with
            | nil => simp [boxInvGo]
    | boxMono a' b' K φ' hab hle =>
        cases s with
        | nil => exact hc.elim
        | cons mD dB s' =>
            cases s' with
            | nil =>
                simp only [boxInvGo]
                have hdive := ih dB.wt dB
                  (.nil : DStack (.box a' φ') (.box a' φ')) hs.1 trivial trivial
                  (by simp [DStack.wt])
                  (Nat.le_of_succ_le_succ (thr_step (P' := dB.wt) hF
                    (by simp only [ProvT.wt, DStack.wt] at hP; omega)
                    (Nat.le_refl _)))
                obtain ⟨rc, hd⟩ := Option.isSome_iff_exists.mp hdive
                rw [hd]
                obtain ⟨mc, tc, hcc⟩ := rc
                simp
    | box4 a' b' K φ' hg1 hle =>
        cases s with
        | nil => exact hc.elim
        | cons mD dB s' =>
            cases s' with
            | nil =>
                simp only [boxInvGo]
                have hdive := ih dB.wt dB
                  (.nil : DStack (.box a' φ') (.box a' φ')) hs.1 trivial trivial
                  (by simp [DStack.wt])
                  (Nat.le_of_succ_le_succ (thr_step (P' := dB.wt) hF
                    (by simp only [ProvT.wt, DStack.wt] at hP; omega)
                    (Nat.le_refl _)))
                obtain ⟨rc, hd⟩ := Option.isSome_iff_exists.mp hdive
                rw [hd]
                obtain ⟨mc, tc, hcc⟩ := rc
                simp
    | axK a'' b'' c'' m'' K φ' α' tP hg1 hle =>
        cases s with
        | nil => exact hc.elim
        | cons mD dB s' =>
            cases s' with
            | nil =>
                simp only [boxInvGo]
                have h1 := dB.wt_pos
                have h2 := tP.wt_pos
                have hdP := ih tP.wt tP
                  (.nil : DStack (.box a'' (.impl φ' α')) _) hf trivial trivial
                  (by simp [DStack.wt])
                  (Nat.le_of_succ_le_succ (thr_step (P' := tP.wt) hF
                    (by simp only [ProvT.wt, DStack.wt] at hP; omega)
                    (Nat.le_refl _)))
                have hdx := ih dB.wt dB (.nil : DStack (.box b'' φ') _) hs.1
                  trivial trivial (by simp [DStack.wt])
                  (Nat.le_of_succ_le_succ (thr_step (P' := dB.wt) hF
                    (by simp only [ProvT.wt, DStack.wt] at hP; omega)
                    (Nat.le_refl _)))
                obtain ⟨rP, hp⟩ := Option.isSome_iff_exists.mp hdP
                obtain ⟨rx, hx⟩ := Option.isSome_iff_exists.mp hdx
                rw [hp, hx]
                obtain ⟨mP, tPc, hPle⟩ := rP
                obtain ⟨mx, txc, hxle⟩ := rx
                simp
    | axKf a'' b'' c'' K φ' α' hg1 hle =>
        cases s with
        | nil => exact hc.elim
        | cons mD1 d1 s' =>
            cases s' with
            | nil => exact hc.elim
            | cons mD2 d2 s'' =>
                cases s'' with
                | nil =>
                    simp only [boxInvGo]
                    have h1 := d1.wt_pos
                    have h2 := d2.wt_pos
                    have hdP := ih d1.wt d1
                      (.nil : DStack (.box a'' (.impl φ' α')) _) hs.1 trivial
                      trivial (by simp [DStack.wt])
                      (Nat.le_of_succ_le_succ (thr_step (P' := d1.wt) hF
                        (by simp only [ProvT.wt, DStack.wt] at hP; omega)
                        (Nat.le_refl _)))
                    have hdx := ih d2.wt d2 (.nil : DStack (.box b'' φ') _) hs.2.1
                      trivial trivial (by simp [DStack.wt])
                      (Nat.le_of_succ_le_succ (thr_step (P' := d2.wt) hF
                        (by simp only [ProvT.wt, DStack.wt] at hP; omega)
                        (Nat.le_refl _)))
                    obtain ⟨rP, hp⟩ := Option.isSome_iff_exists.mp hdP
                    obtain ⟨rx, hx⟩ := Option.isSome_iff_exists.mp hdx
                    rw [hp, hx]
                    obtain ⟨mP, tPc, hPle⟩ := rP
                    obtain ⟨mx, txc, hxle⟩ := rx
                    simp
    | impS2 φ' ψ' χ' m₁' m₂' K tf tx hle => exact absurd hf (by simp [ProvT.freeS2])
    | struct d hd =>
        rcases PD.T48.derivation_shape d with h | ⟨p, hp⟩ | ⟨p, q, hp⟩
        · exact (EndsInPlays.no_core_stack h s hc).elim
        · subst hp; cases s; exact hc.elim
        · subst hp; cases s; exact hc.elim
    | atom t => cases t with | mk _ _ => cases s; exact hc.elim
    | searchThenSearch_t k₁ k₂ m' ψ₁ ψ₂ c0 c1 q me opnt hme t hm hsz =>
        cases s with
        | nil => exact hc.elim
        | cons _ _ s' => cases s'; exact hc.elim
    | atomNeg p q b aN m' t hne hle => cases s; exact hc.elim

/-- **Box honesty is TOTAL on the contraction-free fragment**, with closed-form fuel. -/
theorem boxInv_total_of_freeS2 {m c : Nat} {ψ : Formula}
    (t : ProvT m (.box c ψ)) (hf : t.freeS2) :
    (boxInv ((t.wt+1)*(t.wt+1) + t.wt + 1) t).isSome :=
  boxInvGo_total _ t.wt t .nil hf trivial trivial (by simp [DStack.wt]) (Nat.le_refl _)

/-! ## 13. D2f-a — the cut-diet bookkeeping: extraction PRESERVES the gate.

Where do the extracted trees' cuts come from? The machine only materializes `app` and
`boxIntro` nodes. Working the arms: every materialized `app`'s gated argument formula is
either a STACK SEGMENT — whose `G`-obligation is supplied by the very node that pushed
it (`app`'s own `G φ`, `implTrans`'s `G ψ`, `impS2`'s `G ψ` — the gates align exactly) —
or a BOX CONTENT at the `axK`/`axKf` leaves, needing the single closure hypothesis
`G (.box b ψ) → G ψ` (true of `litGate` — `maxLitF` includes the content — and of the
modest gate). So: if the input trees and stack pass the gate and the stack's segment
formulas do too, the extracted tree passes it. This is the excision pipeline's
bookkeeping lemma: dives never leak exotic cuts. -/

/-- All stack trees pass the gate. -/
def DStack.gateOK (G : Formula → Prop) : {ξ core : Formula} → DStack ξ core → Prop
  | _, _, .nil => True
  | _, _, .cons _ t s => t.gateOK G ∧ s.gateOK G

/-- All stack SEGMENT formulas pass the gate. -/
def DStack.segsOK (G : Formula → Prop) : {ξ core : Formula} → DStack ξ core → Prop
  | _, _, .nil => True
  | _, _, .cons (B := B) _ _ s => G B ∧ s.segsOK G

/-- The extracted tree's diet. -/
def CoreContent.gateOK (G : Formula → Prop) : {core : Formula} → CoreContent core → Prop :=
  fun {core} =>
    match core with
    | .box _ _ => fun r => r.2.1.gateOK G
    | .diag _ _ => fun r => r.2.gateOK G
    | .plays _ _ _ | .impl _ _ | .neg _ | .eq _ _ => fun r => nomatch r

/-- **Extraction preserves the cut diet**, given box-content closure of the gate. -/
theorem boxInvGo_gateOK {G : Formula → Prop}
    (Gbox : ∀ b ψ, G (.box b ψ) → G ψ) :
    ∀ (F : Nat) {m : Nat} {ξ core : Formula}
    (t : ProvT m ξ) (s : DStack ξ core), t.gateOK G → s.gateOK G → s.segsOK G →
    ∀ {r : CoreContent core}, boxInvGo F t s = some r →
    r.gateOK G := by
  intro F
  induction F with
  | zero => intro _ _ _ t s _ _ _ r h; simp [boxInvGo] at h
  | succ F ih =>
    intro m ξ core t s hf hs hsg r h
    cases t with
    | boxIntro kIn K φ tc hle =>
        cases s with
        | nil => simp only [boxInvGo] at h; cases h; exact hf
    | app k m₁ m₂ φ' α f x hle =>
        simp only [boxInvGo] at h
        exact ih f (.cons m₂ x s) hf.2.1 ⟨hf.2.2, hs⟩ ⟨hf.1, hsg⟩ h
    | weakenImpl φ' ψ' m' tw hle =>
        cases s with
        | nil => simp [boxInvGo] at h
        | cons mD d s' =>
            simp only [boxInvGo] at h
            exact ih tw s' hf hs.2 hsg.2 h
    | implTrans φ' ψmid χ' a b tA tB hle =>
        cases s with
        | nil => simp [boxInvGo] at h
        | cons mD dB s' =>
            simp only [boxInvGo] at h
            exact ih tB (.cons _ (.app _ a mD φ' ψmid tA dB (Nat.le_refl _)) s')
              hf.2.2 ⟨⟨hsg.1, hf.2.1, hs.1⟩, hs.2⟩ ⟨hf.1, hsg.2⟩ h
    | diagB pm fb g K tgt tP hle =>
        cases s with
        | nil => simp [boxInvGo] at h
        | cons mD d s' =>
            cases s' with
            | nil => simp only [boxInvGo] at h; cases h; exact hs.1
    | diagF pm fb g K tgt tP hle =>
        cases s with
        | nil => simp [boxInvGo] at h
        | cons mD1 d1 s' =>
            cases s' with
            | nil => simp [boxInvGo] at h
            | cons mD2 d2 s'' =>
                simp only [boxInvGo] at h
                cases hd : boxInvGo F d1
                    (.nil : DStack (.diag g tgt) (.diag g tgt)) with
                | none => rw [hd] at h; exact absurd h (by simp)
                | some rx =>
                    rw [hd] at h
                    have hxg := ih d1 .nil hs.1 trivial trivial hd
                    obtain ⟨mx, x⟩ := rx
                    simp only [CoreContent.gateOK] at hxg
                    exact ih x (.cons mD2 d2 s'') hxg ⟨hs.2.1, hs.2.2⟩
                      ⟨hsg.2.1, hsg.2.2⟩ h
    | atomBoxImpl kBox p q a cert hle =>
        cases s with
        | nil => simp [boxInvGo] at h
        | cons mD d s' =>
            cases s' with
            | nil => simp only [boxInvGo] at h; cases h; exact hf
    | boxMono a' b' K φ' hab hle =>
        cases s with
        | nil => simp [boxInvGo] at h
        | cons mD dB s' =>
            cases s' with
            | nil =>
                simp only [boxInvGo] at h
                cases hd : boxInvGo F dB
                    (.nil : DStack (.box a' φ') (.box a' φ')) with
                | none => rw [hd] at h; exact absurd h (by simp)
                | some rc =>
                    rw [hd] at h
                    obtain ⟨mc, tc, hcc⟩ := rc
                    cases h
                    have := ih dB .nil hs.1 trivial trivial hd
                    simpa [CoreContent.gateOK] using this
    | box4 a' b' K φ' hg1 hle =>
        cases s with
        | nil => simp [boxInvGo] at h
        | cons mD dB s' =>
            cases s' with
            | nil =>
                simp only [boxInvGo] at h
                cases hd : boxInvGo F dB
                    (.nil : DStack (.box a' φ') (.box a' φ')) with
                | none => rw [hd] at h; exact absurd h (by simp)
                | some rc =>
                    rw [hd] at h
                    obtain ⟨mc, tc, hcc⟩ := rc
                    cases h
                    have := ih dB .nil hs.1 trivial trivial hd
                    simp only [CoreContent.gateOK] at *
                    exact (ProvT.mono_gateOK hcc tc).mpr this
    | axK a'' b'' c'' m'' K φ' α' tP hg1 hle =>
        cases s with
        | nil => simp [boxInvGo] at h
        | cons mD dB s' =>
            cases s' with
            | nil =>
                simp only [boxInvGo] at h
                cases hp : boxInvGo F tP
                    (.nil : DStack (.box a'' (.impl φ' α')) _) with
                | none => rw [hp] at h; exact absurd h (by simp)
                | some rP =>
                    cases hx : boxInvGo F dB
                        (.nil : DStack (.box b'' φ') _) with
                    | none => rw [hp, hx] at h; exact absurd h (by simp)
                    | some rx =>
                        rw [hp, hx] at h
                        obtain ⟨mP, tPc, hPle⟩ := rP
                        obtain ⟨mx, txc, hxle⟩ := rx
                        cases h
                        have h1 := ih tP .nil hf.2 trivial trivial hp
                        have h2 := ih dB .nil hs.1 trivial trivial hx
                        simp only [CoreContent.gateOK] at *
                        exact ⟨Gbox _ _ hsg.1, h1, h2⟩
    | axKf a'' b'' c'' K φ' α' hg1 hle =>
        cases s with
        | nil => simp [boxInvGo] at h
        | cons mD1 d1 s' =>
            cases s' with
            | nil => simp [boxInvGo] at h
            | cons mD2 d2 s'' =>
                cases s'' with
                | nil =>
                    simp only [boxInvGo] at h
                    cases hp : boxInvGo F d1
                        (.nil : DStack (.box a'' (.impl φ' α')) _) with
                    | none => rw [hp] at h; exact absurd h (by simp)
                    | some rP =>
                        cases hx : boxInvGo F d2
                            (.nil : DStack (.box b'' φ') _) with
                        | none => rw [hp, hx] at h; exact absurd h (by simp)
                        | some rx =>
                            rw [hp, hx] at h
                            obtain ⟨mP, tPc, hPle⟩ := rP
                            obtain ⟨mx, txc, hxle⟩ := rx
                            cases h
                            have h1 := ih d1 .nil hs.1 trivial trivial hp
                            have h2 := ih d2 .nil hs.2.1 trivial trivial hx
                            simp only [CoreContent.gateOK] at *
                            exact ⟨Gbox _ _ hsg.2.1, h1, h2⟩
    | impS2 φ' ψ' χ' m₁' m₂' K tf tx hle =>
        cases s with
        | nil => simp [boxInvGo] at h
        | cons mD dB s' =>
            simp only [boxInvGo] at h
            exact ih tf (.cons mD dB (.cons _
                (.app _ m₂' mD φ' ψ' tx dB (Nat.le_refl _)) s'))
              hf.2.1 ⟨hs.1, ⟨hsg.1, hf.2.2, hs.1⟩, hs.2⟩
              ⟨hsg.1, hf.1, hsg.2⟩ h
    | struct d hd => simp [boxInvGo] at h
    | atom t => simp [boxInvGo] at h
    | searchThenSearch_t k₁ k₂ m' ψ₁ ψ₂ c0 c1 q me opnt hme t hm hsz =>
        simp [boxInvGo] at h
    | atomNeg p q b aN m' t hne hle => simp [boxInvGo] at h

/-! ## 14. The gate instances and the fuel bound, validated.

Both gates of interest are box-content-closed, so §13 applies to them; and the
closed-form fuel of §12 is checked live against the demos. -/

/-- The literal gate is box-content-closed (`maxLitF (.box n φ) = max n (maxLitF φ)`). -/
theorem litGate_box_closed (N : Nat) : ∀ b ψ, litGate N (.box b ψ) → litGate N ψ := by
  intro b ψ h
  simp only [litGate, maxLitF] at *
  omega

/-- The modest gate is box-content-closed (`modestF` ignores box subscripts). -/
theorem modestGate_box_closed (N : Nat) :
    ∀ b ψ, modestGate N (.box b ψ) → modestGate N ψ := by
  intro b ψ ⟨hlit, hmod⟩
  refine ⟨?_, ?_⟩
  · simp only [maxLitF] at hlit; omega
  · simpa [T43.modestF] using hmod

-- The §12 closed-form fuel, validated live: `demoBox.wt = 3`, so 20 units suffice.
#eval (boxInv ((ProvT.wt demoBox + 1) * (ProvT.wt demoBox + 1)
  + ProvT.wt demoBox + 1) demoBox).isSome

/-! ## 15. D2f-b groundwork — extraction never increases contraction depth.

The stratified measure (note §5b, D2f-b) will induct on the state's `impS2`-nesting
depth; its viability rests on depth being CONSERVED by the machine: navigation moves
subtrees (depth ≤ parent's), and extraction assembles only `app`/`boxIntro` nodes over
extracted pieces — it never builds an `impS2`. Proven here as `boxInvGo_s2d_le`,
unconditionally (like the diet lemma): the result's depth is bounded by the state's. -/

/-- `impS2`-nesting depth of the walkable layer. -/
def ProvT.s2d : {m : Nat} → {φ : Formula} → ProvT m φ → Nat
  | _, _, .impS2 _ _ _ _ _ _ t1 t2 _ => max t1.s2d t2.s2d + 1
  | _, _, .weakenImpl _ _ _ t _ => t.s2d
  | _, _, .searchThenSearch_t _ _ _ _ _ _ _ _ _ _ _ t _ _ => t.s2d
  | _, _, .implTrans _ _ _ _ _ t1 t2 _ => max t1.s2d t2.s2d
  | _, _, .boxIntro _ _ _ t _ => t.s2d
  | _, _, .app _ _ _ _ _ t1 t2 _ => max t1.s2d t2.s2d
  | _, _, .axK _ _ _ _ _ _ _ t _ _ => t.s2d
  | _, _, .diagF _ _ _ _ _ t _ => t.s2d
  | _, _, .diagB _ _ _ _ _ t _ => t.s2d
  | _, _, _ => 0

def DStack.s2d : {ξ core : Formula} → DStack ξ core → Nat
  | _, _, .nil => 0
  | _, _, .cons _ t s => max t.s2d s.s2d

/-- Re-gating preserves depth. -/
theorem ProvT.mono_s2d {k k' : Nat} {φ : Formula}
    (h : k ≤ k') : (t : ProvT k φ) → (t.mono h).s2d = t.s2d
  | .struct _ _ => rfl
  | .atom (.mk _ _) => rfl
  | .weakenImpl _ _ _ _ _ => rfl
  | .searchThenSearch_t _ _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl
  | .implTrans _ _ _ _ _ _ _ _ => rfl
  | .atomBoxImpl _ _ _ _ _ _ => rfl
  | .boxIntro _ _ _ _ _ => rfl
  | .app _ _ _ _ _ _ _ _ => rfl
  | .axK _ _ _ _ _ _ _ _ _ _ => rfl
  | .box4 _ _ _ _ _ _ => rfl
  | .diagF _ _ _ _ _ _ _ => rfl
  | .diagB _ _ _ _ _ _ _ => rfl
  | .axKf _ _ _ _ _ _ _ _ => rfl
  | .impS2 _ _ _ _ _ _ _ _ _ => rfl
  | .boxMono _ _ _ _ _ _ => rfl
  | .atomNeg _ _ _ _ _ _ _ _ => rfl

/-- Depth of what extraction returns. -/
def CoreContent.s2d : {core : Formula} → CoreContent core → Nat := fun {core} =>
  match core with
  | .box _ _ => fun r => r.2.1.s2d
  | .diag _ _ => fun r => r.2.s2d
  | .plays _ _ _ | .impl _ _ | .neg _ | .eq _ _ => fun r => nomatch r

/-- **Extraction never increases contraction depth** (unconditionally). -/
theorem boxInvGo_s2d_le : ∀ (F : Nat) {m : Nat} {ξ core : Formula}
    (t : ProvT m ξ) (s : DStack ξ core),
    ∀ {r : CoreContent core}, boxInvGo F t s = some r →
    r.s2d ≤ max t.s2d s.s2d := by
  intro F
  induction F with
  | zero => intro _ _ _ t s r h; simp [boxInvGo] at h
  | succ F ih =>
    intro m ξ core t s r h
    cases t with
    | boxIntro kIn K φ tc hle =>
        cases s with
        | nil =>
            simp only [boxInvGo] at h
            cases h
            simp [CoreContent.s2d, ProvT.s2d, DStack.s2d]
    | app k m₁ m₂ φ' α f x hle =>
        simp only [boxInvGo] at h
        have := ih f (.cons m₂ x s) h
        simp only [ProvT.s2d, DStack.s2d] at *
        omega
    | weakenImpl φ' ψ' m' tw hle =>
        cases s with
        | nil => simp [boxInvGo] at h
        | cons mD d s' =>
            simp only [boxInvGo] at h
            have := ih tw s' h
            simp only [ProvT.s2d, DStack.s2d] at *
            omega
    | implTrans φ' ψmid χ' a b tA tB hle =>
        cases s with
        | nil => simp [boxInvGo] at h
        | cons mD dB s' =>
            simp only [boxInvGo] at h
            have := ih tB (.cons _ (.app _ a mD φ' ψmid tA dB (Nat.le_refl _)) s') h
            simp only [ProvT.s2d, DStack.s2d] at *
            omega
    | diagB pm fb g K tgt tP hle =>
        cases s with
        | nil => simp [boxInvGo] at h
        | cons mD d s' =>
            cases s' with
            | nil =>
                simp only [boxInvGo] at h
                cases h
                simp only [CoreContent.s2d, ProvT.s2d, DStack.s2d]
                omega
    | diagF pm fb g K tgt tP hle =>
        cases s with
        | nil => simp [boxInvGo] at h
        | cons mD1 d1 s' =>
            cases s' with
            | nil => simp [boxInvGo] at h
            | cons mD2 d2 s'' =>
                simp only [boxInvGo] at h
                cases hd : boxInvGo F d1
                    (.nil : DStack (.diag g tgt) (.diag g tgt)) with
                | none => rw [hd] at h; exact absurd h (by simp)
                | some rx =>
                    rw [hd] at h
                    have hx := ih d1 .nil hd
                    obtain ⟨mx, x⟩ := rx
                    simp only [CoreContent.s2d, DStack.s2d] at hx
                    have := ih x (.cons mD2 d2 s'') h
                    simp only [ProvT.s2d, DStack.s2d] at *
                    omega
    | atomBoxImpl kBox p q a cert hle =>
        cases s with
        | nil => simp [boxInvGo] at h
        | cons mD d s' =>
            cases s' with
            | nil =>
                simp only [boxInvGo] at h
                cases h
                simp [CoreContent.s2d, ProvT.s2d, DStack.s2d]
    | boxMono a' b' K φ' hab hle =>
        cases s with
        | nil => simp [boxInvGo] at h
        | cons mD dB s' =>
            cases s' with
            | nil =>
                simp only [boxInvGo] at h
                cases hd : boxInvGo F dB
                    (.nil : DStack (.box a' φ') (.box a' φ')) with
                | none => rw [hd] at h; exact absurd h (by simp)
                | some rc =>
                    rw [hd] at h
                    obtain ⟨mc, tc, hcc⟩ := rc
                    cases h
                    have := ih dB .nil hd
                    simp only [CoreContent.s2d, ProvT.s2d, DStack.s2d] at *
                    omega
    | box4 a' b' K φ' hg1 hle =>
        cases s with
        | nil => simp [boxInvGo] at h
        | cons mD dB s' =>
            cases s' with
            | nil =>
                simp only [boxInvGo] at h
                cases hd : boxInvGo F dB
                    (.nil : DStack (.box a' φ') (.box a' φ')) with
                | none => rw [hd] at h; exact absurd h (by simp)
                | some rc =>
                    rw [hd] at h
                    obtain ⟨mc, tc, hcc⟩ := rc
                    cases h
                    have h1 := ih dB .nil hd
                    have h2 := ProvT.mono_s2d hcc tc
                    simp only [CoreContent.s2d, ProvT.s2d, DStack.s2d] at *
                    omega
    | axK a'' b'' c'' m'' K φ' α' tP hg1 hle =>
        cases s with
        | nil => simp [boxInvGo] at h
        | cons mD dB s' =>
            cases s' with
            | nil =>
                simp only [boxInvGo] at h
                cases hp : boxInvGo F tP
                    (.nil : DStack (.box a'' (.impl φ' α')) _) with
                | none => rw [hp] at h; exact absurd h (by simp)
                | some rP =>
                    cases hx : boxInvGo F dB
                        (.nil : DStack (.box b'' φ') _) with
                    | none => rw [hp, hx] at h; exact absurd h (by simp)
                    | some rx =>
                        rw [hp, hx] at h
                        obtain ⟨mP, tPc, hPle⟩ := rP
                        obtain ⟨mx, txc, hxle⟩ := rx
                        cases h
                        have h1 := ih tP .nil hp
                        have h2 := ih dB .nil hx
                        simp only [CoreContent.s2d, ProvT.s2d, DStack.s2d] at *
                        omega
    | axKf a'' b'' c'' K φ' α' hg1 hle =>
        cases s with
        | nil => simp [boxInvGo] at h
        | cons mD1 d1 s' =>
            cases s' with
            | nil => simp [boxInvGo] at h
            | cons mD2 d2 s'' =>
                cases s'' with
                | nil =>
                    simp only [boxInvGo] at h
                    cases hp : boxInvGo F d1
                        (.nil : DStack (.box a'' (.impl φ' α')) _) with
                    | none => rw [hp] at h; exact absurd h (by simp)
                    | some rP =>
                        cases hx : boxInvGo F d2
                            (.nil : DStack (.box b'' φ') _) with
                        | none => rw [hp, hx] at h; exact absurd h (by simp)
                        | some rx =>
                            rw [hp, hx] at h
                            obtain ⟨mP, tPc, hPle⟩ := rP
                            obtain ⟨mx, txc, hxle⟩ := rx
                            cases h
                            have h1 := ih d1 .nil hp
                            have h2 := ih d2 .nil hx
                            simp only [CoreContent.s2d, ProvT.s2d, DStack.s2d] at *
                            omega
    | impS2 φ' ψ' χ' m₁' m₂' K tf tx hle =>
        cases s with
        | nil => simp [boxInvGo] at h
        | cons mD dB s' =>
            simp only [boxInvGo] at h
            have := ih tf (.cons mD dB (.cons _
                (.app _ m₂' mD φ' ψ' tx dB (Nat.le_refl _)) s')) h
            simp only [ProvT.s2d, DStack.s2d] at *
            omega
    | struct d hd => simp [boxInvGo] at h
    | atom t => simp [boxInvGo] at h
    | searchThenSearch_t k₁ k₂ m' ψ₁ ψ₂ c0 c1 q me opnt hme t hm hsz =>
        simp [boxInvGo] at h
    | atomNeg p q b aN m' t hne hle => simp [boxInvGo] at h

/-! ## 16. Executable diet certificates — `gateOKb`.

`gateOK` is `Prop`-valued, so neither `#eval` nor `decide` can touch it; per-instance
certificates (route (iii) of the D2f-b verdict) need a Boolean mirror. `gateOKb Gb t`
computes the diet check for a Boolean gate `Gb`; `gateOKb_sound` bridges to any `G`
that `Gb` underapproximates — instantiated with `cutOKb N` (whose `cutOKb_iff` gives
exactly `modestGate N`), a `true` from the checker plus `toG` lands a concrete tree in
`ProvableG (modestGate N)`. The `#eval` below runs the full pipeline on the demo:
extract a box content, CHECK its diet, certify. -/

mutual
  def PlaysT.gateOKb (Gb : Formula → Bool) :
      {me o b : Prog} → {a : Action} → {n : Nat} → PlaysT me o b a n → Bool
    | _, _, _, _, _, .const => true
    | _, _, _, _, _, .self t => t.gateOKb Gb
    | _, _, _, _, _, .opp t => t.gateOKb Gb
    | _, _, _, _, _, .bot t => t.gateOKb Gb
    | _, _, _, _, _, .sim t => t.gateOKb Gb
    | _, _, _, _, _, .ite_t tb _ tp => tb.gateOKb Gb && tp.gateOKb Gb
    | _, _, _, _, _, .ite_f tb _ tq => tb.gateOKb Gb && tq.gateOKb Gb
    | _, _, _, _, _, .search_t tg tp => tg.gateOKb Gb && tp.gateOKb Gb
    | _, _, _, _, _, .search_f tr tq => tr.gateOKb Gb && tq.gateOKb Gb

  def AtomT.gateOKb (Gb : Formula → Bool) :
      {k : Nat} → {φ : Formula} → AtomT k φ → Bool
    | _, _, .mk t _ => t.gateOKb Gb

  def ProvT.gateOKb (Gb : Formula → Bool) :
      {k : Nat} → {φ : Formula} → ProvT k φ → Bool
    | _, _, .struct _ _ => true
    | _, _, .atom t => t.gateOKb Gb
    | _, _, .weakenImpl _ _ _ t _ => t.gateOKb Gb
    | _, _, .searchThenSearch_t _ _ _ _ _ _ _ _ _ _ _ t _ _ => t.gateOKb Gb
    | _, _, .implTrans _ ψ _ _ _ t1 t2 _ => Gb ψ && t1.gateOKb Gb && t2.gateOKb Gb
    | _, _, .atomBoxImpl _ _ _ _ t _ => t.gateOKb Gb
    | _, _, .boxIntro _ _ _ t _ => t.gateOKb Gb
    | _, _, .app _ _ _ φ _ t1 t2 _ => Gb φ && t1.gateOKb Gb && t2.gateOKb Gb
    | _, _, .axK a _ _ _ _ φ α t _ _ =>
        Gb (.box a (.impl φ α)) && t.gateOKb Gb
    | _, _, .box4 _ _ _ _ _ _ => true
    | _, _, .diagF _ fb _ _ tgt t _ =>
        Gb (.impl (.box fb tgt) tgt) && t.gateOKb Gb
    | _, _, .diagB _ fb _ _ tgt t _ =>
        Gb (.impl (.box fb tgt) tgt) && t.gateOKb Gb
    | _, _, .axKf _ _ _ _ _ _ _ _ => true
    | _, _, .impS2 _ ψ _ _ _ _ t1 t2 _ => Gb ψ && t1.gateOKb Gb && t2.gateOKb Gb
    | _, _, .boxMono _ _ _ _ _ _ => true
    | _, _, .atomNeg _ _ _ _ _ t _ _ => t.gateOKb Gb
end

mutual
  theorem PlaysT.gateOKb_sound {Gb : Formula → Bool} {G : Formula → Prop}
      (hGb : ∀ B, Gb B = true → G B) {me o b : Prog} {a : Action} {n : Nat} :
      (t : PlaysT me o b a n) → t.gateOKb Gb = true → t.gateOK G
    | .const, _ => trivial
    | .self t, h => t.gateOKb_sound hGb h
    | .opp t, h => t.gateOKb_sound hGb h
    | .bot t, h => t.gateOKb_sound hGb h
    | .sim t, h => t.gateOKb_sound hGb h
    | .ite_t tb _ tp, h => by
        simp only [PlaysT.gateOKb, Bool.and_eq_true] at h
        exact ⟨tb.gateOKb_sound hGb h.1, tp.gateOKb_sound hGb h.2⟩
    | .ite_f tb _ tq, h => by
        simp only [PlaysT.gateOKb, Bool.and_eq_true] at h
        exact ⟨tb.gateOKb_sound hGb h.1, tq.gateOKb_sound hGb h.2⟩
    | .search_t tg tp, h => by
        simp only [PlaysT.gateOKb, Bool.and_eq_true] at h
        exact ⟨tg.gateOKb_sound hGb h.1, tp.gateOKb_sound hGb h.2⟩
    | .search_f tr tq, h => by
        simp only [PlaysT.gateOKb, Bool.and_eq_true] at h
        exact ⟨tr.gateOKb_sound hGb h.1, tq.gateOKb_sound hGb h.2⟩

  theorem AtomT.gateOKb_sound {Gb : Formula → Bool} {G : Formula → Prop}
      (hGb : ∀ B, Gb B = true → G B) {k : Nat} {φ : Formula} :
      (t : AtomT k φ) → t.gateOKb Gb = true → t.gateOK G
    | .mk t _, h => t.gateOKb_sound hGb h

  theorem ProvT.gateOKb_sound {Gb : Formula → Bool} {G : Formula → Prop}
      (hGb : ∀ B, Gb B = true → G B) {k : Nat} {φ : Formula} :
      (t : ProvT k φ) → t.gateOKb Gb = true → t.gateOK G
    | .struct _ _, _ => trivial
    | .atom t, h => t.gateOKb_sound hGb h
    | .weakenImpl _ _ _ t _, h => t.gateOKb_sound hGb h
    | .searchThenSearch_t _ _ _ _ _ _ _ _ _ _ _ t _ _, h => t.gateOKb_sound hGb h
    | .implTrans _ _ _ _ _ t1 t2 _, h => by
        simp only [ProvT.gateOKb, Bool.and_eq_true] at h
        exact ⟨hGb _ h.1.1, t1.gateOKb_sound hGb h.1.2, t2.gateOKb_sound hGb h.2⟩
    | .atomBoxImpl _ _ _ _ t _, h => t.gateOKb_sound hGb h
    | .boxIntro _ _ _ t _, h => t.gateOKb_sound hGb h
    | .app _ _ _ _ _ t1 t2 _, h => by
        simp only [ProvT.gateOKb, Bool.and_eq_true] at h
        exact ⟨hGb _ h.1.1, t1.gateOKb_sound hGb h.1.2, t2.gateOKb_sound hGb h.2⟩
    | .axK _ _ _ _ _ _ _ t _ _, h => by
        simp only [ProvT.gateOKb, Bool.and_eq_true] at h
        exact ⟨hGb _ h.1, t.gateOKb_sound hGb h.2⟩
    | .box4 _ _ _ _ _ _, _ => trivial
    | .diagF _ _ _ _ _ t _, h => by
        simp only [ProvT.gateOKb, Bool.and_eq_true] at h
        exact ⟨hGb _ h.1, t.gateOKb_sound hGb h.2⟩
    | .diagB _ _ _ _ _ t _, h => by
        simp only [ProvT.gateOKb, Bool.and_eq_true] at h
        exact ⟨hGb _ h.1, t.gateOKb_sound hGb h.2⟩
    | .axKf _ _ _ _ _ _ _ _, _ => trivial
    | .impS2 _ _ _ _ _ _ t1 t2 _, h => by
        simp only [ProvT.gateOKb, Bool.and_eq_true] at h
        exact ⟨hGb _ h.1.1, t1.gateOKb_sound hGb h.1.2, t2.gateOKb_sound hGb h.2⟩
    | .boxMono _ _ _ _ _ _, _ => trivial
    | .atomNeg _ _ _ _ _ t _ _, h => t.gateOKb_sound hGb h
end

/-- A checked tree lands in the modest stratum: the certificate pipeline's exit. -/
theorem certify {N k : Nat} {φ : Formula} (t : ProvT k φ)
    (h : t.gateOKb (T44.cutOKb N) = true) :
    ProvableG (T44.modestGate N) k φ :=
  t.toG (t.gateOKb_sound (fun _ hb => T44.cutOKb_iff.mp hb) h)

-- The full pipeline, live: extract a box content from the Löb demo, CHECK its diet.
#eval match boxInv 10 demoBox with
  | some ⟨_, tc, _⟩ => s!"extracted content passes modestGate 2: {tc.gateOKb (T44.cutOKb 2)}"
  | none => "out of fuel"

/-! ## 17. D2f-b ingredient — the QUANTITATIVE LÖB CAP.

The route-map's fact 5 (the diag formula pins its unfolding budget) becomes quantitative:
walkable weight is bounded by the judgment BUDGET (`wt_le_budget` — each gate pays at
least one character per walkable node; `searchThenSearch_t`'s premise is cite-jumped and
never walked, hence its weight is 1), and extraction certifies content budgets `≤ c`;
composing, **box contents weigh at most their own subscript**
(`content_wt_le_subscript`). This is the well-foundedness leg the future Tait proof's
diag case stands on: every `□g(diag g tgt)`-unfolding along a run produces material of
weight `≤ g` — the SAME `g`, fixed by the formula — so unfold-chains at a fixed diag
formula are weight-capped even though the formula itself recurs. -/

theorem Formula.size_pos : (φ : Formula) → 1 ≤ φ.size := by
  intro φ
  cases φ <;> simp [Formula.size] <;> omega

theorem PlaysT.cost_pos {me o b : Prog} {a : Action} {n : Nat} :
    PlaysT me o b a n → 1 ≤ n
  | .const => Nat.le_refl _
  | .self _ | .opp _ | .bot _ | .sim _ => by simp [c_node]
  | .ite_t _ _ _ | .ite_f _ _ _ | .search_t _ _ | .search_f _ _ => by
      simp [c_node]

/-- **Weight is budget-bounded**: every walkable node is paid for by its gate. -/
theorem ProvT.wt_le_budget : {m : Nat} → {φ : Formula} → (t : ProvT m φ) → t.wt ≤ m
  | _, _, .struct d hd =>
      le_trans (le_trans (Formula.size_pos _) d.concl_size_le) hd
  | _, _, .atom (.mk c hn) => le_trans c.cost_pos hn
  | _, _, .weakenImpl φ' ψ' m' t hle => by
      have h1 := t.wt_le_budget
      have h2 := Formula.size_pos (Formula.impl φ' ψ')
      simp only [ProvT.wt]; omega
  | _, _, .searchThenSearch_t k₁ k₂ m' ψ₁ ψ₂ c0 c1 q me opnt hme t hm hsz => by
      have h2 := Formula.size_pos
        (Formula.impl (.box k₁ (ψ₁.subst me opnt)) (.plays me opnt c0))
      simp only [ProvT.wt]; omega
  | _, _, .implTrans φ' ψ' χ' a b t1 t2 hle => by
      have h1 := t1.wt_le_budget
      have h2 := t2.wt_le_budget
      have h3 := Formula.size_pos (Formula.impl φ' χ')
      simp only [ProvT.wt]; omega
  | _, _, .atomBoxImpl kBox p q a _ hle => by
      have h2 := Formula.size_pos
        (Formula.impl (.plays p q a) (.box kBox (.plays p q a)))
      simp only [ProvT.wt]; omega
  | _, _, .boxIntro kIn K φ' t hle => by
      have h1 := t.wt_le_budget
      have h2 := Formula.size_pos (Formula.box kIn φ')
      simp only [ProvT.wt]; omega
  | _, _, .app _ _ _ φ' α t1 t2 hle => by
      have h1 := t1.wt_le_budget
      have h2 := t2.wt_le_budget
      have h3 := Formula.size_pos α
      simp only [ProvT.wt]; omega
  | _, _, .axK a b c m' K φ' α t _ hg2 => by
      have h1 := t.wt_le_budget
      have h2 := Formula.size_pos (Formula.impl (.box b φ') (.box c α))
      simp only [ProvT.wt]; omega
  | _, _, .box4 a b K φ' _ hg2 => by
      have h2 := Formula.size_pos (Formula.impl (.box a φ') (.box b (.box a φ')))
      simp only [ProvT.wt]; omega
  | _, _, .diagF pm fb g K tgt t hle => by
      have h1 := t.wt_le_budget
      have h2 := Formula.size_pos
        (Formula.impl (.diag g tgt) (.impl (.box g (.diag g tgt)) tgt))
      simp only [ProvT.wt]; omega
  | _, _, .diagB pm fb g K tgt t hle => by
      have h1 := t.wt_le_budget
      have h2 := Formula.size_pos
        (Formula.impl (.impl (.box g (.diag g tgt)) tgt) (.diag g tgt))
      simp only [ProvT.wt]; omega
  | _, _, .axKf a b c K φ' α _ hg2 => by
      have h2 := Formula.size_pos
        (Formula.impl (.box a (.impl φ' α)) (.impl (.box b φ') (.box c α)))
      simp only [ProvT.wt]; omega
  | _, _, .impS2 φ' ψ' χ' m₁ m₂ K t1 t2 hle => by
      have h1 := t1.wt_le_budget
      have h2 := t2.wt_le_budget
      have h3 := Formula.size_pos (Formula.impl φ' χ')
      simp only [ProvT.wt]; omega
  | _, _, .boxMono a b K φ' _ hle => by
      have h2 := Formula.size_pos (Formula.impl (.box a φ') (.box b φ'))
      simp only [ProvT.wt]; omega
  | _, _, .atomNeg p q b aN m' _ _ hle => by
      have h2 := Formula.size_pos (Formula.neg (.plays p q aN))
      simp only [ProvT.wt]; omega

/-- **The quantitative Löb cap**: an extracted box content weighs at most the box's own
    subscript — the weight-well-foundedness of diag unfolding at a fixed formula. -/
theorem content_wt_le_subscript {F m c : Nat} {ψ : Formula} {t : ProvT m (.box c ψ)}
    {r : CoreContent (.box c ψ)} (h : boxInv F t = some r) :
    r.2.1.wt ≤ c :=
  le_trans r.2.1.wt_le_budget r.2.2

/-! ## 18. D2f-b — STRICT consumption: extraction loses at least one node.

The deepest finding of the Lemma-C design attack (see `BOUNDED_LOB_NORMALIZATION.md`
§7): `.diag` is a NEGATIVE recursive type (`D ≅ (□g D) → tgt`, `D` in antecedent
position) — the Curry/Y-combinator recipe, under which normalization is FALSE for
unbounded reduction. The bounded calculus escapes because dynamic self-regeneration is
impossible: trees are finite (no literal self-reference), and extraction returns
STRICTLY lighter material than it consumes — so any Löb unfold-chain strictly descends
in weight and the Y-loop cannot sustain itself. This section proves the strictness
(`boxInvGo_wt_lt`, contraction-free — the hypotheses are exact as in `wt_le`). -/

/-- **Extraction strictly consumes**: the result is strictly lighter than the state
    (contraction-free fragment). The anti-Y lemma. -/
theorem boxInvGo_wt_lt : ∀ (F : Nat) {m : Nat} {ξ core : Formula}
    (t : ProvT m ξ) (s : DStack ξ core), t.freeS2 → s.freeS2 →
    ∀ {r : CoreContent core}, boxInvGo F t s = some r →
    r.wt + 1 ≤ t.wt + s.wt := by
  intro F
  induction F with
  | zero => intro _ _ _ t s _ _ r h; simp [boxInvGo] at h
  | succ F ih =>
    intro m ξ core t s hf hs r h
    cases t with
    | boxIntro kIn K φ tc hle =>
        cases s with
        | nil =>
            simp only [boxInvGo] at h
            cases h
            simp [CoreContent.wt, ProvT.wt, DStack.wt]
    | app k m₁ m₂ φ' α f x hle =>
        simp only [boxInvGo] at h
        have := ih f (.cons m₂ x s) hf.1 ⟨hf.2, hs⟩ h
        simp only [ProvT.wt, DStack.wt] at *
        omega
    | weakenImpl φ' ψ' m' tw hle =>
        cases s with
        | nil => simp [boxInvGo] at h
        | cons mD d s' =>
            simp only [boxInvGo] at h
            have := ih tw s' hf hs.2 h
            have hd := d.wt_pos
            simp only [ProvT.wt, DStack.wt] at *
            omega
    | implTrans φ' ψmid χ' a b tA tB hle =>
        cases s with
        | nil => simp [boxInvGo] at h
        | cons mD dB s' =>
            simp only [boxInvGo] at h
            have := ih tB (.cons _ (.app _ a mD φ' ψmid tA dB (Nat.le_refl _)) s')
              hf.2 ⟨⟨hf.1, hs.1⟩, hs.2⟩ h
            simp only [ProvT.wt, DStack.wt] at *
            omega
    | diagB pm fb g K tgt tP hle =>
        cases s with
        | nil => simp [boxInvGo] at h
        | cons mD d s' =>
            cases s' with
            | nil =>
                simp only [boxInvGo] at h
                cases h
                have := tP.wt_pos
                simp only [CoreContent.wt, ProvT.wt, DStack.wt]
                omega
    | diagF pm fb g K tgt tP hle =>
        cases s with
        | nil => simp [boxInvGo] at h
        | cons mD1 d1 s' =>
            cases s' with
            | nil => simp [boxInvGo] at h
            | cons mD2 d2 s'' =>
                simp only [boxInvGo] at h
                cases hd : boxInvGo F d1
                    (.nil : DStack (.diag g tgt) (.diag g tgt)) with
                | none => rw [hd] at h; exact absurd h (by simp)
                | some rx =>
                    rw [hd] at h
                    have hx := ih d1 .nil hs.1 trivial hd
                    have hxf := boxInvGo_wt_le F d1 .nil hs.1 trivial hd
                    obtain ⟨mx, x⟩ := rx
                    simp only [CoreContent.wt, CoreContent.freeS2, DStack.wt]
                      at hx hxf
                    have := ih x (.cons mD2 d2 s'') hxf.2 ⟨hs.2.1, hs.2.2⟩ h
                    have := tP.wt_pos
                    simp only [ProvT.wt, DStack.wt] at *
                    omega
    | atomBoxImpl kBox p q a cert hle =>
        cases s with
        | nil => simp [boxInvGo] at h
        | cons mD d s' =>
            cases s' with
            | nil =>
                simp only [boxInvGo] at h
                cases h
                have := d.wt_pos
                simp only [CoreContent.wt, ProvT.wt, DStack.wt]
                omega
    | boxMono a' b' K φ' hab hle =>
        cases s with
        | nil => simp [boxInvGo] at h
        | cons mD dB s' =>
            cases s' with
            | nil =>
                simp only [boxInvGo] at h
                cases hd : boxInvGo F dB
                    (.nil : DStack (.box a' φ') (.box a' φ')) with
                | none => rw [hd] at h; exact absurd h (by simp)
                | some rc =>
                    rw [hd] at h
                    obtain ⟨mc, tc, hcc⟩ := rc
                    cases h
                    have := ih dB .nil hs.1 trivial hd
                    simp only [CoreContent.wt, ProvT.wt, DStack.wt] at *
                    omega
    | box4 a' b' K φ' hg1 hle =>
        cases s with
        | nil => simp [boxInvGo] at h
        | cons mD dB s' =>
            cases s' with
            | nil =>
                simp only [boxInvGo] at h
                cases hd : boxInvGo F dB
                    (.nil : DStack (.box a' φ') (.box a' φ')) with
                | none => rw [hd] at h; exact absurd h (by simp)
                | some rc =>
                    rw [hd] at h
                    obtain ⟨mc, tc, hcc⟩ := rc
                    cases h
                    have h1 := ih dB .nil hs.1 trivial hd
                    have h2 := ProvT.mono_wt hcc tc
                    simp only [CoreContent.wt, ProvT.wt, DStack.wt] at *
                    omega
    | axK a'' b'' c'' m'' K φ' α' tP hg1 hle =>
        cases s with
        | nil => simp [boxInvGo] at h
        | cons mD dB s' =>
            cases s' with
            | nil =>
                simp only [boxInvGo] at h
                cases hp : boxInvGo F tP
                    (.nil : DStack (.box a'' (.impl φ' α')) _) with
                | none => rw [hp] at h; exact absurd h (by simp)
                | some rP =>
                    cases hx : boxInvGo F dB
                        (.nil : DStack (.box b'' φ') _) with
                    | none => rw [hp, hx] at h; exact absurd h (by simp)
                    | some rx =>
                        rw [hp, hx] at h
                        obtain ⟨mP, tPc, hPle⟩ := rP
                        obtain ⟨mx, txc, hxle⟩ := rx
                        cases h
                        have h1 := ih tP .nil hf trivial hp
                        have h2 := ih dB .nil hs.1 trivial hx
                        simp only [CoreContent.wt, ProvT.wt, DStack.wt] at *
                        omega
    | axKf a'' b'' c'' K φ' α' hg1 hle =>
        cases s with
        | nil => simp [boxInvGo] at h
        | cons mD1 d1 s' =>
            cases s' with
            | nil => simp [boxInvGo] at h
            | cons mD2 d2 s'' =>
                cases s'' with
                | nil =>
                    simp only [boxInvGo] at h
                    cases hp : boxInvGo F d1
                        (.nil : DStack (.box a'' (.impl φ' α')) _) with
                    | none => rw [hp] at h; exact absurd h (by simp)
                    | some rP =>
                        cases hx : boxInvGo F d2
                            (.nil : DStack (.box b'' φ') _) with
                        | none => rw [hp, hx] at h; exact absurd h (by simp)
                        | some rx =>
                            rw [hp, hx] at h
                            obtain ⟨mP, tPc, hPle⟩ := rP
                            obtain ⟨mx, txc, hxle⟩ := rx
                            cases h
                            have h1 := ih d1 .nil hs.1 trivial hp
                            have h2 := ih d2 .nil hs.2.1 trivial hx
                            simp only [CoreContent.wt, ProvT.wt, DStack.wt] at *
                            omega
    | impS2 φ' ψ' χ' m₁' m₂' K tf tx hle => exact absurd hf (by simp [ProvT.freeS2])
    | struct d hd => simp [boxInvGo] at h
    | atom t => simp [boxInvGo] at h
    | searchThenSearch_t k₁ k₂ m' ψ₁ ψ₂ c0 c1 q me opnt hme t hm hsz =>
        simp [boxInvGo] at h
    | atomNeg p q b aN m' t hne hle => simp [boxInvGo] at h

end PD.T49
