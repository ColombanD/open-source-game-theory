import PrisonersDilemma.Decidability.T42ProvableB
import PrisonersDilemma.Decidability.T44BoundedDecider

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

end PD.T49
