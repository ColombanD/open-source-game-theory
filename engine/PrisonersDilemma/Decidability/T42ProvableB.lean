import PrisonersDilemma.BaseTheorems

/-!
# T4.2 spike — `ProvableG`: gate-parametric proof search, the literal-bounded strata, and
# the CUT-RELEVANCE conjecture.

`DECIDABILITY_ROADMAP.md` T4.1b/T4.2. The engine's residual to full decidability is the
budget TOWER, and T4.1a (`T4QueryBound.lean`) proved its complement: budget-jumping systems
over a BOUNDED vocabulary are decidable by least-fixpoint stabilization. This spike builds
the engine-side object that separates the two: the mutual triple `PlaysProofG /
AtomProvableG / ProvableG G`, mirroring the engine's `PlaysProof / AtomProvable / Provable`
EXACTLY except that the six rules whose premises carry a formula ABSENT from their
conclusions gate that formula by an arbitrary predicate `G : Formula → Prop`:

  * `implTrans` — the cut formula `ψ`:                         gate `G ψ`
  * `app`       — the cut formula `φ`:                         gate `G φ`
  * `impS2`     — the middle formula `ψ`:                      gate `G ψ`
  * `axK`       — the whole premise `.box a (.impl φ α)`
                  (its subscript `a` is enumerated):           gate `G (…)`
  * `diagF`/`diagB` — the whole premise `.impl (.box fb t) t`
                  (its Löb budget `fb` is enumerated):         gate `G (…)`

Everything else already draws its premises from the conclusion's own syntax (subformulas,
substitution instances, source literals), so it needs no gate. (`struct` stays ungated: a
`Derivation` tree is size-paid — `d.size ≤ k` — so every formula in it has size `≤ k` and
literals `< 2^k`.)

Two instances matter:
  * `ProvableB N := ProvableG (litGate N)` with `litGate N B := maxLitF B ≤ N` — the
    LITERAL-BOUNDED strata. Shipped: `Provable_iff_exists_ProvableB` —
    **`Provable k φ ↔ ∃ N, ProvableB N k φ`** (every derivation is finitely-cut, so it
    lives at SOME stratum — max over its own cut diet).
  * `modestGate N B := maxLitF B ≤ N ∧ modestF B = true` (T4.4, next spike) — the
    DECIDABLE fragment: the modest gate additionally keeps cut ATOMS inside the T4.3
    finite cert universe (a non-modest cut atom would spawn evaluation queries about
    substitution-growing programs, re-opening the infinite space).

`CutRelevance` states the T4.1b conjecture: a COMPUTABLE `N₀` with
`Provable k φ → ProvableB (N₀ k φ) k φ`. Given it (and its modest refinement), the T4.1a
stabilization template over the finite query space decides `Provable` outright.

All transfer theorems on `[propext, Quot.sound]` (not even choice).
-/

namespace PD.T42
open PD

/-! ## 1. The literal vocabulary of a program / formula. -/

mutual
  /-- The largest `.search` budget literal in a program (0 if none). -/
  def maxLitP : Prog → Nat
    | .const _ => 0
    | .self => 0
    | .opp => 0
    | .bot p => maxLitP p
    | .sim p q => max (maxLitP p) (maxLitP q)
    | .ite b _ p q => max (maxLitP b) (max (maxLitP p) (maxLitP q))
    | .search k φ p q => max k (max (maxLitF φ) (max (maxLitP p) (maxLitP q)))

  /-- The largest budget literal in a formula: `.search` budgets in mentioned programs,
      `.box` and `.diag` subscripts. -/
  def maxLitF : Formula → Nat
    | .plays p q _ => max (maxLitP p) (maxLitP q)
    | .impl φ ψ => max (maxLitF φ) (maxLitF ψ)
    | .neg φ => maxLitF φ
    | .box n φ => max n (maxLitF φ)
    | .eq p q => max (maxLitP p) (maxLitP q)
    | .diag g φ => max g (maxLitF φ)
end

/-! ## 2. The gate-parametric system — the engine triple verbatim, plus the six gates. -/

mutual
  /-- `PlaysProof` with the gate threaded through its `Provable` premises. -/
  inductive PlaysProofG (G : Formula → Prop) : (me opponent body : Prog) → Action → Nat → Prop where
    | const :
        PlaysProofG G me opponent (.const a) a c_leaf
    | self :
        PlaysProofG G me opponent me a n →
        PlaysProofG G me opponent .self a (n + c_node)
    | opp :
        PlaysProofG G me opponent opponent a n →
        PlaysProofG G me opponent .opp a (n + c_node)
    | bot :
        PlaysProofG G me opponent p a n →
        PlaysProofG G me opponent (.bot p) a (n + c_node)
    | sim :
        PlaysProofG G (p.subst me opponent) (q.subst me opponent) (p.subst me opponent) a n →
        PlaysProofG G me opponent (.sim p q) a (n + c_node)
    | ite_t :
        PlaysProofG G me opponent b r m → (r == a') = true →
        PlaysProofG G me opponent p a n →
        PlaysProofG G me opponent (.ite b a' p q) a (m + n + c_node)
    | ite_f :
        PlaysProofG G me opponent b r m → (r == a') = false →
        PlaysProofG G me opponent q a n →
        PlaysProofG G me opponent (.ite b a' p q) a (m + n + c_node)
    | search_t :
        ProvableG G k (φ.subst me opponent) →
        PlaysProofG G me opponent p a n →
        PlaysProofG G me opponent (.search k φ p q) a (n + c_guard k + c_node)
    | search_f :
        ProvableG G m (.neg (φ.subst me opponent)) →
        PlaysProofG G me opponent q a n →
        PlaysProofG G me opponent (.search k φ p q) a (n + m + k + c_node)

  inductive AtomProvableG (G : Formula → Prop) : Nat → Formula → Prop where
    | mk : PlaysProofG G me opponent me a n → n ≤ k → AtomProvableG G k (.plays me opponent a)

  /-- `Provable` with the six gates (see the header). All other rules are verbatim. -/
  inductive ProvableG (G : Formula → Prop) : Nat → Formula → Prop where
    | struct : (∃ d : Derivation φ, d.size ≤ k) → ProvableG G k φ
    | atom : AtomProvableG G k φ → ProvableG G k φ
    | weakenImpl (φ ψ : Formula) (m : Nat) :
        ProvableG G m ψ → m + (Formula.impl φ ψ).size ≤ k → ProvableG G k (.impl φ ψ)
    | searchThenSearch_t (k₁ k₂ m : Nat) (ψ₁ ψ₂ : Formula) (c0 c1 : Action)
        (q me opponent : Prog)
        (hme : me = .search k₁ ψ₁ (.search k₂ ψ₂ (.const c0) (.const c1)) q) :
        ProvableG G m (ψ₂.subst me opponent) → m ≤ k₂ →
        c_guard k₂ +
          (Formula.impl (.box k₁ (ψ₁.subst me opponent)) (.plays me opponent c0)).size ≤ k →
        ProvableG G k (.impl (.box k₁ (ψ₁.subst me opponent)) (.plays me opponent c0))
    | implTrans (φ ψ χ : Formula) (a b : Nat) :
        ProvableG G a (.impl φ ψ) → ProvableG G b (.impl ψ χ) →
        a + b + (Formula.impl φ χ).size ≤ k →
        G ψ →
        ProvableG G k (.impl φ χ)
    | atomBoxImpl (kBox : Nat) (p q : Prog) (a : Action) :
        AtomProvableG G kBox (.plays p q a) →
        kBox + (Formula.impl (.plays p q a) (.box kBox (.plays p q a))).size ≤ k →
        ProvableG G k (.impl (.plays p q a) (.box kBox (.plays p q a)))
    | boxIntro (kIn K : Nat) (φ : Formula) :
        ProvableG G kIn φ →
        kIn + (Formula.box kIn φ).size ≤ K →
        ProvableG G K (.box kIn φ)
    | app (k m₁ m₂ : Nat) (φ α : Formula) :
        ProvableG G m₁ (.impl φ α) → ProvableG G m₂ φ → m₁ + m₂ + α.size ≤ k →
        G φ →
        ProvableG G k α
    | axK (a b c m K : Nat) (φ α : Formula) :
        ProvableG G m (.box a (.impl φ α)) →
        a + b + α.size ≤ c →
        m + (Formula.impl (.box b φ) (.box c α)).size ≤ K →
        G (.box a (.impl φ α)) →
        ProvableG G K (.impl (.box b φ) (.box c α))
    | box4 (a b K : Nat) (φ : Formula) :
        a + (Formula.box a φ).size ≤ b →
        (Formula.impl (.box a φ) (.box b (.box a φ))).size ≤ K →
        ProvableG G K (.impl (.box a φ) (.box b (.box a φ)))
    | diagF (pm fb g K : Nat) (tgt : Formula) :
        ProvableG G pm (.impl (.box fb tgt) tgt) →
        pm + (Formula.impl (.diag g tgt) (.impl (.box g (.diag g tgt)) tgt)).size ≤ K →
        G (.impl (.box fb tgt) tgt) →
        ProvableG G K (.impl (.diag g tgt) (.impl (.box g (.diag g tgt)) tgt))
    | diagB (pm fb g K : Nat) (tgt : Formula) :
        ProvableG G pm (.impl (.box fb tgt) tgt) →
        pm + (Formula.impl (.impl (.box g (.diag g tgt)) tgt) (.diag g tgt)).size ≤ K →
        G (.impl (.box fb tgt) tgt) →
        ProvableG G K (.impl (.impl (.box g (.diag g tgt)) tgt) (.diag g tgt))
    | axKf (a b c K : Nat) (φ α : Formula) :
        a + b + α.size ≤ c →
        (Formula.impl (.box a (.impl φ α)) (.impl (.box b φ) (.box c α))).size ≤ K →
        ProvableG G K (.impl (.box a (.impl φ α)) (.impl (.box b φ) (.box c α)))
    | impS2 (φ ψ χ : Formula) (m₁ m₂ K : Nat) :
        ProvableG G m₁ (.impl φ (.impl ψ χ)) → ProvableG G m₂ (.impl φ ψ) →
        m₁ + m₂ + (Formula.impl φ χ).size ≤ K →
        G ψ →
        ProvableG G K (.impl φ χ)
    | boxMono (a b K : Nat) (φ : Formula) :
        a ≤ b →
        (Formula.impl (.box a φ) (.box b φ)).size ≤ K →
        ProvableG G K (.impl (.box a φ) (.box b φ))
    | atomNeg (p q : Prog) (b aN : Action) (m : Nat) :
        AtomProvableG G m (.plays p q b) → b ≠ aN →
        m + (Formula.neg (.plays p q aN)).size ≤ k →
        ProvableG G k (.neg (.plays p q aN))
end

/-- The literal-bound gate — the T4.2 strata. -/
@[reducible] def litGate (N : Nat) : Formula → Prop := fun B => maxLitF B ≤ N

@[reducible] def PlaysProofB (N : Nat) := PlaysProofG (litGate N)
@[reducible] def AtomProvableB (N : Nat) := AtomProvableG (litGate N)
@[reducible] def ProvableB (N : Nat) := ProvableG (litGate N)

/-! ## 3. Soundness of the restriction — erase the gates. -/

theorem ProvableG_sound {G : Formula → Prop} : ∀ {k : Nat} {φ : Formula},
    ProvableG G k φ → Provable k φ := by
  intro k φ h
  refine ProvableG.rec (motive_1 := fun me oppo body a n _ => PlaysProof me oppo body a n)
    (motive_2 := fun k φ _ => AtomProvable k φ)
    (motive_3 := fun k φ _ => Provable k φ)
    ?const ?self ?opp ?bot ?sim ?ite_t ?ite_f ?search_t ?search_f ?atomMk
    ?struct ?atom ?weaken ?sts ?itrans ?atomBox ?boxIntro ?app ?axK ?box4
    ?diagF ?diagB ?axKf ?impS2 ?boxMono ?atomNeg h
  case const => intro me oppo a; exact .const
  case self => intro me oppo a n _ ih; exact .self ih
  case opp => intro me oppo a n _ ih; exact .opp ih
  case bot => intro me oppo p a n _ ih; exact .bot ih
  case sim => intro a n me oppo p q _ ih; exact .sim ih
  case ite_t => intro me oppo g r m a' p a n q _ hr _ ihg ihp; exact .ite_t ihg hr ihp
  case ite_f => intro me oppo g r m a' q a n p _ hr _ ihg ihq; exact .ite_f ihg hr ihq
  case search_t => intro kg me oppo p a n g q _ _ ihg ihp; exact .search_t ihg ihp
  case search_f => intro m me oppo q a n kg g p _ _ ihn ihq; exact .search_f ihn ihq
  case atomMk => intro me oppo a n k _ hle ih; exact .mk ih hle
  case struct => intro φ0 k0 hd; exact .struct hd
  case atom => intro k0 φ0 _ ih; exact .atom ih
  case weaken => intro k A B m _ hle ih; exact .weakenImpl A B m ih hle
  case sts =>
      intro k k₁ k₂ m ψ₁ ψ₂ c0 c1 q me opnt hme _ hmk hle ih
      exact .searchThenSearch_t k₁ k₂ m ψ₁ ψ₂ c0 c1 q me opnt hme ih hmk hle
  case itrans =>
      intro k A B C a b _ _ hle hg ih1 ih2
      exact .implTrans A B C a b ih1 ih2 hle
  case atomBox => intro k kBox p q a _ hle ih; exact .atomBoxImpl kBox p q a ih hle
  case boxIntro => intro kIn K A _ hle ih; exact .boxIntro kIn K A ih hle
  case app =>
      intro k m₁ m₂ A B _ _ hle hg ih1 ih2
      exact .app k m₁ m₂ A B ih1 ih2 hle
  case axK =>
      intro a b c m K A B _ hgate hle hg ih
      exact .axK a b c m K A B ih hgate hle
  case box4 => intro a b K A hgate hle; exact .box4 a b K A hgate hle
  case diagF => intro pm fb g K tgt _ hle hg ih; exact .diagF pm fb g K tgt ih hle
  case diagB => intro pm fb g K tgt _ hle hg ih; exact .diagB pm fb g K tgt ih hle
  case axKf => intro a b c K A B hgate hle; exact .axKf a b c K A B hgate hle
  case impS2 =>
      intro A B C m₁ m₂ K _ _ hle hg ih1 ih2
      exact .impS2 A B C m₁ m₂ K ih1 ih2 hle
  case boxMono => intro a b K A hab hle; exact .boxMono a b K A hab hle
  case atomNeg =>
      intro k p q b aN m _ hne hle ih
      exact .atomNeg p q b aN m ih hne hle

theorem ProvableB_sound {N : Nat} {k : Nat} {φ : Formula} :
    ProvableB N k φ → Provable k φ := ProvableG_sound

/-! ## 4. Monotonicity in the gate. -/

theorem PlaysProofG_monoG {G G' : Formula → Prop} (hGG : ∀ B, G B → G' B) :
    ∀ {me oppo body : Prog} {a : Action} {n : Nat},
    PlaysProofG G me oppo body a n → PlaysProofG G' me oppo body a n := by
  intro me oppo body a n h
  refine PlaysProofG.rec
    (motive_1 := fun me oppo body a n _ => PlaysProofG G' me oppo body a n)
    (motive_2 := fun k φ _ => AtomProvableG G' k φ)
    (motive_3 := fun k φ _ => ProvableG G' k φ)
    ?const ?self ?opp ?bot ?sim ?ite_t ?ite_f ?search_t ?search_f ?atomMk
    ?struct ?atom ?weaken ?sts ?itrans ?atomBox ?boxIntro ?app ?axK ?box4
    ?diagF ?diagB ?axKf ?impS2 ?boxMono ?atomNeg h
  case const => intro me oppo a; exact .const
  case self => intro me oppo a n _ ih; exact .self ih
  case opp => intro me oppo a n _ ih; exact .opp ih
  case bot => intro me oppo p a n _ ih; exact .bot ih
  case sim => intro a n me oppo p q _ ih; exact .sim ih
  case ite_t => intro me oppo g r m a' p a n q _ hr _ ihg ihp; exact .ite_t ihg hr ihp
  case ite_f => intro me oppo g r m a' q a n p _ hr _ ihg ihq; exact .ite_f ihg hr ihq
  case search_t => intro kg me oppo p a n g q _ _ ihg ihp; exact .search_t ihg ihp
  case search_f => intro m me oppo q a n kg g p _ _ ihn ihq; exact .search_f ihn ihq
  case atomMk => intro me oppo a n k _ hle ih; exact .mk ih hle
  case struct => intro φ0 k0 hd; exact .struct hd
  case atom => intro k0 φ0 _ ih; exact .atom ih
  case weaken => intro k A B m _ hle ih; exact .weakenImpl A B m ih hle
  case sts =>
      intro k k₁ k₂ m ψ₁ ψ₂ c0 c1 q me opnt hme _ hmk hle ih
      exact .searchThenSearch_t k₁ k₂ m ψ₁ ψ₂ c0 c1 q me opnt hme ih hmk hle
  case itrans =>
      intro k A B C a b _ _ hle hg ih1 ih2
      exact .implTrans A B C a b ih1 ih2 hle (hGG _ hg)
  case atomBox => intro k kBox p q a _ hle ih; exact .atomBoxImpl kBox p q a ih hle
  case boxIntro => intro kIn K A _ hle ih; exact .boxIntro kIn K A ih hle
  case app =>
      intro k m₁ m₂ A B _ _ hle hg ih1 ih2
      exact .app k m₁ m₂ A B ih1 ih2 hle (hGG _ hg)
  case axK =>
      intro a b c m K A B _ hgate hle hg ih
      exact .axK a b c m K A B ih hgate hle (hGG _ hg)
  case box4 => intro a b K A hgate hle; exact .box4 a b K A hgate hle
  case diagF =>
      intro pm fb g K tgt _ hle hg ih
      exact .diagF pm fb g K tgt ih hle (hGG _ hg)
  case diagB =>
      intro pm fb g K tgt _ hle hg ih
      exact .diagB pm fb g K tgt ih hle (hGG _ hg)
  case axKf => intro a b c K A B hgate hle; exact .axKf a b c K A B hgate hle
  case impS2 =>
      intro A B C m₁ m₂ K _ _ hle hg ih1 ih2
      exact .impS2 A B C m₁ m₂ K ih1 ih2 hle (hGG _ hg)
  case boxMono => intro a b K A hab hle; exact .boxMono a b K A hab hle
  case atomNeg =>
      intro k p q b aN m _ hne hle ih
      exact .atomNeg p q b aN m ih hne hle

theorem ProvableG_monoG {G G' : Formula → Prop} (hGG : ∀ B, G B → G' B) :
    ∀ {k : Nat} {φ : Formula},
    ProvableG G k φ → ProvableG G' k φ := by
  intro k φ h
  refine ProvableG.rec
    (motive_1 := fun me oppo body a n _ => PlaysProofG G' me oppo body a n)
    (motive_2 := fun k φ _ => AtomProvableG G' k φ)
    (motive_3 := fun k φ _ => ProvableG G' k φ)
    ?const ?self ?opp ?bot ?sim ?ite_t ?ite_f ?search_t ?search_f ?atomMk
    ?struct ?atom ?weaken ?sts ?itrans ?atomBox ?boxIntro ?app ?axK ?box4
    ?diagF ?diagB ?axKf ?impS2 ?boxMono ?atomNeg h
  case const => intro me oppo a; exact .const
  case self => intro me oppo a n _ ih; exact .self ih
  case opp => intro me oppo a n _ ih; exact .opp ih
  case bot => intro me oppo p a n _ ih; exact .bot ih
  case sim => intro a n me oppo p q _ ih; exact .sim ih
  case ite_t => intro me oppo g r m a' p a n q _ hr _ ihg ihp; exact .ite_t ihg hr ihp
  case ite_f => intro me oppo g r m a' q a n p _ hr _ ihg ihq; exact .ite_f ihg hr ihq
  case search_t => intro kg me oppo p a n g q _ _ ihg ihp; exact .search_t ihg ihp
  case search_f => intro m me oppo q a n kg g p _ _ ihn ihq; exact .search_f ihn ihq
  case atomMk => intro me oppo a n k _ hle ih; exact .mk ih hle
  case struct => intro φ0 k0 hd; exact .struct hd
  case atom => intro k0 φ0 _ ih; exact .atom ih
  case weaken => intro k A B m _ hle ih; exact .weakenImpl A B m ih hle
  case sts =>
      intro k k₁ k₂ m ψ₁ ψ₂ c0 c1 q me opnt hme _ hmk hle ih
      exact .searchThenSearch_t k₁ k₂ m ψ₁ ψ₂ c0 c1 q me opnt hme ih hmk hle
  case itrans =>
      intro k A B C a b _ _ hle hg ih1 ih2
      exact .implTrans A B C a b ih1 ih2 hle (hGG _ hg)
  case atomBox => intro k kBox p q a _ hle ih; exact .atomBoxImpl kBox p q a ih hle
  case boxIntro => intro kIn K A _ hle ih; exact .boxIntro kIn K A ih hle
  case app =>
      intro k m₁ m₂ A B _ _ hle hg ih1 ih2
      exact .app k m₁ m₂ A B ih1 ih2 hle (hGG _ hg)
  case axK =>
      intro a b c m K A B _ hgate hle hg ih
      exact .axK a b c m K A B ih hgate hle (hGG _ hg)
  case box4 => intro a b K A hgate hle; exact .box4 a b K A hgate hle
  case diagF =>
      intro pm fb g K tgt _ hle hg ih
      exact .diagF pm fb g K tgt ih hle (hGG _ hg)
  case diagB =>
      intro pm fb g K tgt _ hle hg ih
      exact .diagB pm fb g K tgt ih hle (hGG _ hg)
  case axKf => intro a b c K A B hgate hle; exact .axKf a b c K A B hgate hle
  case impS2 =>
      intro A B C m₁ m₂ K _ _ hle hg ih1 ih2
      exact .impS2 A B C m₁ m₂ K ih1 ih2 hle (hGG _ hg)
  case boxMono => intro a b K A hab hle; exact .boxMono a b K A hab hle
  case atomNeg =>
      intro k p q b aN m _ hne hle ih
      exact .atomNeg p q b aN m ih hne hle

theorem PlaysProofB_monoN {N N' : Nat} (hNN : N ≤ N') {me oppo body : Prog} {a : Action}
    {n : Nat} : PlaysProofB N me oppo body a n → PlaysProofB N' me oppo body a n :=
  PlaysProofG_monoG (fun _ h => Nat.le_trans h hNN)

theorem ProvableB_monoN {N N' : Nat} (hNN : N ≤ N') {k : Nat} {φ : Formula} :
    ProvableB N k φ → ProvableB N' k φ :=
  ProvableG_monoG (fun _ h => Nat.le_trans h hNN)

/-! ## 5. Every derivation is finitely-cut: `Provable = ⋃_N ProvableB N`. -/

theorem Provable_exists_ProvableB : ∀ {k : Nat} {φ : Formula},
    Provable k φ → ∃ N, ProvableB N k φ := by
  intro k φ h
  refine Provable.rec
    (motive_1 := fun me oppo body a n _ => ∃ N, PlaysProofB N me oppo body a n)
    (motive_2 := fun k φ _ => ∃ N, AtomProvableB N k φ)
    (motive_3 := fun k φ _ => ∃ N, ProvableB N k φ)
    ?pConst ?pSelf ?pOpp ?pBot ?pSim ?pIte_t ?pIte_f ?pSearch_t ?pSearch_f ?pMk
    ?cStruct ?cAtom ?cWeaken ?cSTS ?cITrans ?cAtomBox ?cBoxIntro ?cApp ?cAxK ?cBox4
    ?cDiagF ?cDiagB ?cAxKf ?cImpS2 ?cBoxMono ?cAtomNeg h
  case pConst => intro me oppo a; exact ⟨0, .const⟩
  case pSelf => intro me oppo a n _ ih; obtain ⟨N, e⟩ := ih; exact ⟨N, .self e⟩
  case pOpp => intro me oppo a n _ ih; obtain ⟨N, e⟩ := ih; exact ⟨N, .opp e⟩
  case pBot => intro me oppo p a n _ ih; obtain ⟨N, e⟩ := ih; exact ⟨N, .bot e⟩
  case pSim => intro a n me oppo p q _ ih; obtain ⟨N, e⟩ := ih; exact ⟨N, .sim e⟩
  case pIte_t =>
      intro me oppo g r m a' p a n q _ hr _ ihg ihp
      obtain ⟨N₁, e₁⟩ := ihg
      obtain ⟨N₂, e₂⟩ := ihp
      exact ⟨max N₁ N₂, .ite_t (PlaysProofB_monoN (Nat.le_max_left _ _) e₁) hr
        (PlaysProofB_monoN (Nat.le_max_right _ _) e₂)⟩
  case pIte_f =>
      intro me oppo g r m a' q a n p _ hr _ ihg ihq
      obtain ⟨N₁, e₁⟩ := ihg
      obtain ⟨N₂, e₂⟩ := ihq
      exact ⟨max N₁ N₂, .ite_f (PlaysProofB_monoN (Nat.le_max_left _ _) e₁) hr
        (PlaysProofB_monoN (Nat.le_max_right _ _) e₂)⟩
  case pSearch_t =>
      intro kg me oppo p a n g q _ _ ihg ihp
      obtain ⟨N₁, e₁⟩ := ihg
      obtain ⟨N₂, e₂⟩ := ihp
      exact ⟨max N₁ N₂, .search_t (ProvableB_monoN (Nat.le_max_left _ _) e₁)
        (PlaysProofB_monoN (Nat.le_max_right _ _) e₂)⟩
  case pSearch_f =>
      intro m me oppo q a n kg g p _ _ ihn ihq
      obtain ⟨N₁, e₁⟩ := ihn
      obtain ⟨N₂, e₂⟩ := ihq
      exact ⟨max N₁ N₂, .search_f (ProvableB_monoN (Nat.le_max_left _ _) e₁)
        (PlaysProofB_monoN (Nat.le_max_right _ _) e₂)⟩
  case pMk => intro me oppo a n k _ hle ih; obtain ⟨N, e⟩ := ih; exact ⟨N, .mk e hle⟩
  case cStruct => intro φ0 k0 hd; exact ⟨0, .struct hd⟩
  case cAtom => intro k0 φ0 _ ih; obtain ⟨N, e⟩ := ih; exact ⟨N, .atom e⟩
  case cWeaken =>
      intro k A B m _ hle ih
      obtain ⟨N, e⟩ := ih
      exact ⟨N, .weakenImpl A B m e hle⟩
  case cSTS =>
      intro k k₁ k₂ m ψ₁ ψ₂ c0 c1 q me opnt hme _ hmk hle ih
      obtain ⟨N, e⟩ := ih
      exact ⟨N, .searchThenSearch_t k₁ k₂ m ψ₁ ψ₂ c0 c1 q me opnt hme e hmk hle⟩
  case cITrans =>
      intro k A B C a b _ _ hle ih1 ih2
      obtain ⟨N₁, e₁⟩ := ih1
      obtain ⟨N₂, e₂⟩ := ih2
      refine ⟨max (max N₁ N₂) (maxLitF B), .implTrans A B C a b ?_ ?_ hle ?_⟩
      · exact ProvableB_monoN (by omega) e₁
      · exact ProvableB_monoN (by omega) e₂
      · exact Nat.le_max_right _ _
  case cAtomBox =>
      intro k kBox p q a _ hle ih
      obtain ⟨N, e⟩ := ih
      exact ⟨N, .atomBoxImpl kBox p q a e hle⟩
  case cBoxIntro =>
      intro kIn K A _ hle ih
      obtain ⟨N, e⟩ := ih
      exact ⟨N, .boxIntro kIn K A e hle⟩
  case cApp =>
      intro k m₁ m₂ A B _ _ hle ih1 ih2
      obtain ⟨N₁, e₁⟩ := ih1
      obtain ⟨N₂, e₂⟩ := ih2
      refine ⟨max (max N₁ N₂) (maxLitF A), .app k m₁ m₂ A B ?_ ?_ hle ?_⟩
      · exact ProvableB_monoN (by omega) e₁
      · exact ProvableB_monoN (by omega) e₂
      · exact Nat.le_max_right _ _
  case cAxK =>
      intro a b c m K A B _ hgate hle ih
      obtain ⟨N, e⟩ := ih
      exact ⟨max N (maxLitF (.box a (.impl A B))),
        .axK a b c m K A B (ProvableB_monoN (Nat.le_max_left _ _) e)
          hgate hle (Nat.le_max_right _ _)⟩
  case cBox4 => intro a b K A hgate hle; exact ⟨0, .box4 a b K A hgate hle⟩
  case cDiagF =>
      intro pm fb g K tgt _ hle ih
      obtain ⟨N, e⟩ := ih
      exact ⟨max N (maxLitF (.impl (.box fb tgt) tgt)),
        .diagF pm fb g K tgt (ProvableB_monoN (Nat.le_max_left _ _) e)
          hle (Nat.le_max_right _ _)⟩
  case cDiagB =>
      intro pm fb g K tgt _ hle ih
      obtain ⟨N, e⟩ := ih
      exact ⟨max N (maxLitF (.impl (.box fb tgt) tgt)),
        .diagB pm fb g K tgt (ProvableB_monoN (Nat.le_max_left _ _) e)
          hle (Nat.le_max_right _ _)⟩
  case cAxKf => intro a b c K A B hgate hle; exact ⟨0, .axKf a b c K A B hgate hle⟩
  case cImpS2 =>
      intro A B C m₁ m₂ K _ _ hle ih1 ih2
      obtain ⟨N₁, e₁⟩ := ih1
      obtain ⟨N₂, e₂⟩ := ih2
      refine ⟨max (max N₁ N₂) (maxLitF B), .impS2 A B C m₁ m₂ K ?_ ?_ hle ?_⟩
      · exact ProvableB_monoN (by omega) e₁
      · exact ProvableB_monoN (by omega) e₂
      · exact Nat.le_max_right _ _
  case cBoxMono => intro a b K A hab hle; exact ⟨0, .boxMono a b K A hab hle⟩
  case cAtomNeg =>
      intro k p q b aN m _ hne hle ih
      obtain ⟨N, e⟩ := ih
      exact ⟨N, .atomNeg p q b aN m e hne hle⟩

/-- **`Provable` is exactly the union of its literal-bounded strata.** -/
theorem Provable_iff_exists_ProvableB (k : Nat) (φ : Formula) :
    Provable k φ ↔ ∃ N, ProvableB N k φ :=
  ⟨Provable_exists_ProvableB, fun ⟨_, h⟩ => ProvableG_sound h⟩

/-! ## 6. THE T4.1b CONJECTURE, stated. -/

/-- **CUT RELEVANCE**: the stratum is computable from the query — minimal derivations never
    need cut formulas (or `axK`/`diag` premises) beyond a bound `N₀ k φ` readable off the
    query. Evidence FOR: `bloeb_engine`'s entire cut/diag diet is `O(k)`-literal (every
    library theorem lives in `ProvableB (2^(k+2))`); the exotic material an unrestricted cut
    can smuggle in is logically inert (no reflection rule eliminates boxes; implications with
    atom antecedents trace back to `weakenImpl`/`atomBoxImpl` only). Evidence AGAINST: no
    descent measure survives the guard hops (budgets jump to source literals of the cut's own
    programs, and levels exponentiate: literals `≤ 2^K` per level).

    Given `CutRelevance N₀` for computable `N₀` (with its modest refinement, T4.4), the
    T4.1a stabilization template over the finite query space decides `Provable`:
    `proofSearch := D`, `eval` computable, outcomes `by decide`. If it FAILS, `Provable` is
    a candidate undecidable bounded-provability predicate. -/
def CutRelevance (N₀ : Nat → Formula → Nat) : Prop :=
  ∀ k φ, Provable k φ → ProvableB (N₀ k φ) k φ

/-- Under the conjecture, deciding the stratum decides `Provable`. -/
theorem Provable_iff_ProvableB_of_cutRelevance {N₀ : Nat → Formula → Nat}
    (hcr : CutRelevance N₀) (k : Nat) (φ : Formula) :
    Provable k φ ↔ ProvableB (N₀ k φ) k φ :=
  ⟨hcr k φ, ProvableG_sound⟩

end PD.T42
