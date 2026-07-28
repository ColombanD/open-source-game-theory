import PrisonersDilemma.BaseTheorems

/-!
# T4.2 — `PfG`: gate-parametric proof search, the literal-bounded strata, and the
# CUT-RELEVANCE conjecture

`DECIDABILITY_ROADMAP.md` T4.1b/T4.2, **Pf-only since the migration** (`PF_ONLY_ROADMAP.md`
Phase 4.1). The mirror triple `PlaysProofG / AtomProvableG / PfG G` copies the engine's
unified `PlaysProof / AtomProvable / Pf` EXACTLY except that the six rules whose premises
carry a formula ABSENT from their conclusions gate that formula by an arbitrary predicate
`G : Formula → Prop`:

  * `implTrans` — the cut formula `ψ`:                         gate `G ψ`
  * `mp`        — the cut formula `φ`:                         gate `G φ`
  * `impS2`     — the middle formula `ψ`:                      gate `G ψ`
  * `axK`       — the whole premise `.box a (.impl φ α)`
                  (its subscript `a` is enumerated):           gate `G (…)`
  * `diagF`/`diagB` — the whole premise `.impl (.box fb t) t`
                  (its Löb budget `fb` is enumerated):         gate `G (…)`

Everything else draws its premises from the conclusion's own syntax (subformulas,
substitution instances, source literals — the seven ex-`Derivation` transparency leaves have
NO recursive premises at all), so it needs no gate.

**The D2 decision (uniform gating), executed here.** Pre-migration, `ProvableG.struct`
wrapped the UNGATED `Derivation`: its internal `modusPonens`/`hypSyll` cuts passed no gate,
justified by `d.size ≤ k` bounding every formula in the tree. Post-merge those cuts flow
through the gated `mp`/`implTrans` like everyone else's — ONE rule set, one census. The
stratification theorem below absorbs the change: ex-`Derivation` cuts now contribute their
cut formula's literals to the stratum witness (previously `struct` landed at stratum 0),
which is invisible to the ∃-statement. The certified zoo (T54) is the acceptance test that
real zoo trees still pass the instance gate under uniform gating.

Two instances matter:
  * `PfB N := PfG (litGate N)` with `litGate N B := maxLitF B ≤ N` — the LITERAL-BOUNDED
    strata. Shipped: **`Pf k φ ↔ ∃ N, PfB N k φ`** (every proof is finitely-cut, so it
    lives at SOME stratum — max over its own cut diet).
  * `modestGate N B := maxLitF B ≤ N ∧ modestF B = true` (T4.4) — the DECIDABLE fragment.

`CutRelevance` states the T4.1b conjecture: a COMPUTABLE `N₀` with
`Pf k φ → PfB (N₀ k φ) k φ`. Given it (and its modest refinement), the T4.1a stabilization
template over the finite query space decides `Pf` outright.

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
  /-- `PlaysProof` with the gate threaded through its `Pf` premises. -/
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
        PfG G k (φ.subst me opponent) →
        PlaysProofG G me opponent p a n →
        PlaysProofG G me opponent (.search k φ p q) a (n + c_guard k + c_node)
    | search_f :
        PfG G m (.neg (φ.subst me opponent)) →
        PlaysProofG G me opponent q a n →
        PlaysProofG G me opponent (.search k φ p q) a (n + m + k + c_node)

  inductive AtomProvableG (G : Formula → Prop) : Nat → Formula → Prop where
    | mk : PlaysProofG G me opponent me a n → n ≤ k → AtomProvableG G k (.plays me opponent a)

  /-- `Pf` with the six gates (see the header). Same constructor SET as `Pf` (order differs:
      the 2026-07-28 Family-B leaves `implRefl`/`implK` are appended last here); the
      transparency leaves and the premise-free implication leaves are UNGATED. -/
  inductive PfG (G : Formula → Prop) : Nat → Formula → Prop where
    | atom : AtomProvableG G k φ → PfG G k φ
    | searchBranch (g : Nat) (ψ : Formula) (a b : Action) (me opponent : Prog)
        (hme : me = .search g ψ (.const a) (.const b)) :
        (Formula.impl (.box g (ψ.subst me opponent)) (.plays me opponent a)).size ≤ k →
        PfG G k (.impl (.box g (ψ.subst me opponent)) (.plays me opponent a))
    | simStep (me p q opponent : Prog) (a : Action) (hme : me = .sim p q) :
        (Formula.impl (.plays (p.subst me opponent) (q.subst me opponent) a)
                      (.plays me opponent a)).size ≤ k →
        PfG G k (.impl (.plays (p.subst me opponent) (q.subst me opponent) a)
                       (.plays me opponent a))
    | botSimStep (me p q opponent : Prog) (a : Action) (hme : me = .bot (.sim p q)) :
        (Formula.impl (.plays (p.subst me opponent) (q.subst me opponent) a)
                      (.plays me opponent a)).size ≤ k →
        PfG G k (.impl (.plays (p.subst me opponent) (q.subst me opponent) a)
                       (.plays me opponent a))
    | botSearchStep (g : Nat) (ψ : Formula) (a b : Action) (me opponent : Prog)
        (hme : me = .bot (.search g ψ (.const a) (.const b))) :
        (Formula.impl (.box g (ψ.subst me opponent)) (.plays me opponent a)).size ≤ k →
        PfG G k (.impl (.box g (ψ.subst me opponent)) (.plays me opponent a))
    | iteBranchSearch_t (g : Nat) (z : Prog) (a' c0 c1 : Action) (ψ : Formula)
        (q me opponent : Prog)
        (hme : me = .ite (.sim .opp (.bot z)) a'
                         (.search g ψ (.const c0) (.const c1)) q) :
        (Formula.impl (.plays opponent (.bot z) a')
                      (.impl (.box g (ψ.subst me opponent))
                             (.plays me opponent c0))).size ≤ k →
        PfG G k (.impl (.plays opponent (.bot z) a')
                       (.impl (.box g (ψ.subst me opponent))
                              (.plays me opponent c0)))
    | eqRefl (p : Prog) :
        (Formula.eq p p).size ≤ k → PfG G k (.eq p p)
    | eqNeg (p q : Prog) (hne : p ≠ q) :
        (Formula.neg (.eq p q)).size ≤ k → PfG G k (.neg (.eq p q))
    | mp (m₁ m₂ : Nat) (φ α : Formula) :
        PfG G m₁ (.impl φ α) → PfG G m₂ φ → m₁ + m₂ + α.size ≤ k →
        G φ →
        PfG G k α
    | implTrans (φ ψ χ : Formula) (a b : Nat) :
        PfG G a (.impl φ ψ) → PfG G b (.impl ψ χ) →
        a + b + (Formula.impl φ χ).size ≤ k →
        G ψ →
        PfG G k (.impl φ χ)
    | weakenImpl (φ ψ : Formula) (m : Nat) :
        PfG G m ψ → m + (Formula.impl φ ψ).size ≤ k → PfG G k (.impl φ ψ)
    | searchThenSearch_t (k₁ k₂ m : Nat) (ψ₁ ψ₂ : Formula) (c0 c1 : Action)
        (q me opponent : Prog)
        (hme : me = .search k₁ ψ₁ (.search k₂ ψ₂ (.const c0) (.const c1)) q) :
        PfG G m (ψ₂.subst me opponent) → m ≤ k₂ →
        c_guard k₂ +
          (Formula.impl (.box k₁ (ψ₁.subst me opponent)) (.plays me opponent c0)).size ≤ k →
        PfG G k (.impl (.box k₁ (ψ₁.subst me opponent)) (.plays me opponent c0))
    | atomBoxImpl (kBox : Nat) (p q : Prog) (a : Action) :
        AtomProvableG G kBox (.plays p q a) →
        kBox + (Formula.impl (.plays p q a) (.box kBox (.plays p q a))).size ≤ k →
        PfG G k (.impl (.plays p q a) (.box kBox (.plays p q a)))
    | boxIntro (kIn K : Nat) (φ : Formula) :
        PfG G kIn φ →
        kIn + (Formula.box kIn φ).size ≤ K →
        PfG G K (.box kIn φ)
    | axK (a b c m K : Nat) (φ α : Formula) :
        PfG G m (.box a (.impl φ α)) →
        a + b + α.size ≤ c →
        m + (Formula.impl (.box b φ) (.box c α)).size ≤ K →
        G (.box a (.impl φ α)) →
        PfG G K (.impl (.box b φ) (.box c α))
    | box4 (a b K : Nat) (φ : Formula) :
        a + (Formula.box a φ).size ≤ b →
        (Formula.impl (.box a φ) (.box b (.box a φ))).size ≤ K →
        PfG G K (.impl (.box a φ) (.box b (.box a φ)))
    | diagF (pm fb g K : Nat) (tgt : Formula) :
        PfG G pm (.impl (.box fb tgt) tgt) →
        pm + (Formula.impl (.diag g tgt) (.impl (.box g (.diag g tgt)) tgt)).size ≤ K →
        G (.impl (.box fb tgt) tgt) →
        PfG G K (.impl (.diag g tgt) (.impl (.box g (.diag g tgt)) tgt))
    | diagB (pm fb g K : Nat) (tgt : Formula) :
        PfG G pm (.impl (.box fb tgt) tgt) →
        pm + (Formula.impl (.impl (.box g (.diag g tgt)) tgt) (.diag g tgt)).size ≤ K →
        G (.impl (.box fb tgt) tgt) →
        PfG G K (.impl (.impl (.box g (.diag g tgt)) tgt) (.diag g tgt))
    | axKf (a b c K : Nat) (φ α : Formula) :
        a + b + α.size ≤ c →
        (Formula.impl (.box a (.impl φ α)) (.impl (.box b φ) (.box c α))).size ≤ K →
        PfG G K (.impl (.box a (.impl φ α)) (.impl (.box b φ) (.box c α)))
    | impS2 (φ ψ χ : Formula) (m₁ m₂ K : Nat) :
        PfG G m₁ (.impl φ (.impl ψ χ)) → PfG G m₂ (.impl φ ψ) →
        m₁ + m₂ + (Formula.impl φ χ).size ≤ K →
        G ψ →
        PfG G K (.impl φ χ)
    | boxMono (a b K : Nat) (φ : Formula) :
        a ≤ b →
        (Formula.impl (.box a φ) (.box b φ)).size ≤ K →
        PfG G K (.impl (.box a φ) (.box b φ))
    | atomNeg (p q : Prog) (b aN : Action) (m : Nat) :
        AtomProvableG G m (.plays p q b) → b ≠ aN →
        m + (Formula.neg (.plays p q aN)).size ≤ k →
        PfG G k (.neg (.plays p q aN))
    -- the Family-B completion leaves (2026-07-28): premise-free, hence UNGATED
    | implRefl (φ : Formula) :
        (Formula.impl φ φ).size ≤ k → PfG G k (.impl φ φ)
    | implK (φ ψ : Formula) :
        (Formula.impl φ (.impl ψ φ)).size ≤ k → PfG G k (.impl φ (.impl ψ φ))
    -- Family-B `.neg`-consumer (2026-07-28): the premise formula is reconstructible
    -- from the conclusion, hence UNGATED (like `weakenImpl`). `negElim` has NO mirror:
    -- it is vacuous in the consistent `S` (its premises cannot coexist, by soundness),
    -- so `Pf_exists_PfB` discharges its arm by contradiction.
    | contrapose (φ ψ : Formula) (m : Nat) :
        PfG G m (.impl φ ψ) →
        m + (Formula.impl (.neg ψ) (.neg φ)).size ≤ k →
        PfG G k (.impl (.neg ψ) (.neg φ))
    -- the depth-general search telescope (2026-07-28): a premise-free reading leaf,
    -- hence UNGATED
    | searchChain (g₁ : Nat) (ψ₁ : Formula) (e₁ : Prog)
        (L : List (Nat × Formula × Prog)) (a : Action) (me opponent : Prog)
        (hme : me = .search g₁ ψ₁ (searchPlug L (.const a)) e₁) :
        (Formula.impl (.box g₁ (ψ₁.subst me opponent))
          (implChain (searchGuards me opponent L) (.plays me opponent a))).size ≤ k →
        PfG G k (.impl (.box g₁ (ψ₁.subst me opponent))
          (implChain (searchGuards me opponent L) (.plays me opponent a)))
    -- the MIXED telescope (the ite frontier, 2026-07-28): premise-free leaf, UNGATED
    | ctxChain (hd : CtxLayer) (L : List CtxLayer) (a : Action) (me opponent : Prog)
        (hme : me = ctxPlug (hd :: L) (.const a)) :
        (Formula.impl (ctxGuard me opponent hd)
          (implChain (ctxGuards me opponent L) (.plays me opponent a))).size ≤ k →
        PfG G k (.impl (ctxGuard me opponent hd)
          (implChain (ctxGuards me opponent L) (.plays me opponent a)))
    -- Family-B completeness axioms (2026-07-28): premise-free leaves, UNGATED
    | implS (φ ψ χ : Formula) :
        (Formula.impl (.impl φ (.impl ψ χ))
          (.impl (.impl φ ψ) (.impl φ χ))).size ≤ k →
        PfG G k (.impl (.impl φ (.impl ψ χ)) (.impl (.impl φ ψ) (.impl φ χ)))
end

/-- The literal-bound gate — the T4.2 strata. -/
@[reducible] def litGate (N : Nat) : Formula → Prop := fun B => maxLitF B ≤ N

@[reducible] def PlaysProofB (N : Nat) := PlaysProofG (litGate N)
@[reducible] def AtomProvableB (N : Nat) := AtomProvableG (litGate N)
@[reducible] def PfB (N : Nat) := PfG (litGate N)

/-! ## 3. Soundness of the restriction — erase the gates. -/

theorem PfG_sound {G : Formula → Prop} : ∀ {k : Nat} {φ : Formula},
    PfG G k φ → Pf k φ := by
  intro k φ h
  refine PfG.rec (motive_1 := fun me oppo body a n _ => PlaysProof me oppo body a n)
    (motive_2 := fun k φ _ => AtomProvable k φ)
    (motive_3 := fun k φ _ => Pf k φ)
    ?const ?self ?opp ?bot ?sim ?ite_t ?ite_f ?search_t ?search_f ?atomMk
    ?atom ?sb ?ss ?bss ?bsearch ?iteB ?eqR ?eqN ?mp ?itrans ?weaken ?sts
    ?atomBox ?boxIntro ?axK ?box4 ?diagF ?diagB ?axKf ?impS2 ?boxMono ?atomNeg
    ?implRefl ?implK ?contrapose ?searchChain ?ctxChain ?implS h
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
  case atom => intro k0 φ0 _ ih; exact .atom ih
  case sb => intro k0 g ψ a b me oppo hme hle; exact .searchBranch g ψ a b me oppo hme hle
  case ss => intro k0 me p q oppo a hme hle; exact .simStep me p q oppo a hme hle
  case bss => intro k0 me p q oppo a hme hle; exact .botSimStep me p q oppo a hme hle
  case bsearch => intro k0 g ψ a b me oppo hme hle; exact .botSearchStep g ψ a b me oppo hme hle
  case iteB =>
      intro k0 g z a' c0 c1 ψ q me oppo hme hle
      exact .iteBranchSearch_t g z a' c0 c1 ψ q me oppo hme hle
  case eqR => intro k0 p hle; exact .eqRefl p hle
  case eqN => intro k0 p q hne hle; exact .eqNeg p q hne hle
  case mp => intro k0 m₁ m₂ A B _ _ hle hg ih1 ih2; exact .mp m₁ m₂ A B ih1 ih2 hle
  case itrans =>
      intro k0 A B C a b _ _ hle hg ih1 ih2
      exact .implTrans A B C a b ih1 ih2 hle
  case weaken => intro k0 A B m _ hle ih; exact .weakenImpl A B m ih hle
  case sts =>
      intro k0 k₁ k₂ m ψ₁ ψ₂ c0 c1 q me opnt hme _ hmk hle ih
      exact .searchThenSearch_t k₁ k₂ m ψ₁ ψ₂ c0 c1 q me opnt hme ih hmk hle
  case atomBox => intro k0 kBox p q a _ hle ih; exact .atomBoxImpl kBox p q a ih hle
  case boxIntro => intro kIn K A _ hle ih; exact .boxIntro kIn K A ih hle
  case axK => intro a b c m K A B _ hgate hle hg ih; exact .axK a b c m K A B ih hgate hle
  case box4 => intro a b K A hgate hle; exact .box4 a b K A hgate hle
  case diagF => intro pm fb g K tgt _ hle hg ih; exact .diagF pm fb g K tgt ih hle
  case diagB => intro pm fb g K tgt _ hle hg ih; exact .diagB pm fb g K tgt ih hle
  case axKf => intro a b c K A B hgate hle; exact .axKf a b c K A B hgate hle
  case impS2 =>
      intro A B C m₁ m₂ K _ _ hle hg ih1 ih2
      exact .impS2 A B C m₁ m₂ K ih1 ih2 hle
  case boxMono => intro a b K A hab hle; exact .boxMono a b K A hab hle
  case atomNeg => intro k0 p q b aN m _ hne hle ih; exact .atomNeg p q b aN m ih hne hle
  case implRefl => intro k0 A hle; exact .implRefl A hle
  case implK => intro k0 A B hle; exact .implK A B hle
  case contrapose => intro k0 A B m0 _ hle ih; exact .contrapose A B m0 ih hle
  case searchChain =>
      intro k0 g₁ ψ₁ e₁ L a me opnt hme hle
      exact .searchChain g₁ ψ₁ e₁ L a me opnt hme hle
  case ctxChain =>
      intro k0 hd L a me opnt hme hle
      exact .ctxChain hd L a me opnt hme hle
  case implS => intro k0 A B C hle; exact .implS A B C hle

theorem PfB_sound {N : Nat} {k : Nat} {φ : Formula} :
    PfB N k φ → Pf k φ := PfG_sound

/-! ## 4. Monotonicity in the gate. -/

theorem PlaysProofG_monoG {G G' : Formula → Prop} (hGG : ∀ B, G B → G' B) :
    ∀ {me oppo body : Prog} {a : Action} {n : Nat},
    PlaysProofG G me oppo body a n → PlaysProofG G' me oppo body a n := by
  intro me oppo body a n h
  refine PlaysProofG.rec
    (motive_1 := fun me oppo body a n _ => PlaysProofG G' me oppo body a n)
    (motive_2 := fun k φ _ => AtomProvableG G' k φ)
    (motive_3 := fun k φ _ => PfG G' k φ)
    ?const ?self ?opp ?bot ?sim ?ite_t ?ite_f ?search_t ?search_f ?atomMk
    ?atom ?sb ?ss ?bss ?bsearch ?iteB ?eqR ?eqN ?mp ?itrans ?weaken ?sts
    ?atomBox ?boxIntro ?axK ?box4 ?diagF ?diagB ?axKf ?impS2 ?boxMono ?atomNeg
    ?implRefl ?implK ?contrapose ?searchChain ?ctxChain ?implS h
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
  case atom => intro k0 φ0 _ ih; exact .atom ih
  case sb => intro k0 g ψ a b me oppo hme hle; exact .searchBranch g ψ a b me oppo hme hle
  case ss => intro k0 me p q oppo a hme hle; exact .simStep me p q oppo a hme hle
  case bss => intro k0 me p q oppo a hme hle; exact .botSimStep me p q oppo a hme hle
  case bsearch => intro k0 g ψ a b me oppo hme hle; exact .botSearchStep g ψ a b me oppo hme hle
  case iteB =>
      intro k0 g z a' c0 c1 ψ q me oppo hme hle
      exact .iteBranchSearch_t g z a' c0 c1 ψ q me oppo hme hle
  case eqR => intro k0 p hle; exact .eqRefl p hle
  case eqN => intro k0 p q hne hle; exact .eqNeg p q hne hle
  case mp => intro k0 m₁ m₂ A B _ _ hle hg ih1 ih2; exact .mp m₁ m₂ A B ih1 ih2 hle (hGG _ hg)
  case itrans =>
      intro k0 A B C a b _ _ hle hg ih1 ih2
      exact .implTrans A B C a b ih1 ih2 hle (hGG _ hg)
  case weaken => intro k0 A B m _ hle ih; exact .weakenImpl A B m ih hle
  case sts =>
      intro k0 k₁ k₂ m ψ₁ ψ₂ c0 c1 q me opnt hme _ hmk hle ih
      exact .searchThenSearch_t k₁ k₂ m ψ₁ ψ₂ c0 c1 q me opnt hme ih hmk hle
  case atomBox => intro k0 kBox p q a _ hle ih; exact .atomBoxImpl kBox p q a ih hle
  case boxIntro => intro kIn K A _ hle ih; exact .boxIntro kIn K A ih hle
  case axK => intro a b c m K A B _ hgate hle hg ih; exact .axK a b c m K A B ih hgate hle (hGG _ hg)
  case box4 => intro a b K A hgate hle; exact .box4 a b K A hgate hle
  case diagF => intro pm fb g K tgt _ hle hg ih; exact .diagF pm fb g K tgt ih hle (hGG _ hg)
  case diagB => intro pm fb g K tgt _ hle hg ih; exact .diagB pm fb g K tgt ih hle (hGG _ hg)
  case axKf => intro a b c K A B hgate hle; exact .axKf a b c K A B hgate hle
  case impS2 =>
      intro A B C m₁ m₂ K _ _ hle hg ih1 ih2
      exact .impS2 A B C m₁ m₂ K ih1 ih2 hle (hGG _ hg)
  case boxMono => intro a b K A hab hle; exact .boxMono a b K A hab hle
  case atomNeg => intro k0 p q b aN m _ hne hle ih; exact .atomNeg p q b aN m ih hne hle
  case implRefl => intro k0 A hle; exact .implRefl A hle
  case implK => intro k0 A B hle; exact .implK A B hle
  case contrapose => intro k0 A B m0 _ hle ih; exact .contrapose A B m0 ih hle
  case searchChain =>
      intro k0 g₁ ψ₁ e₁ L a me opnt hme hle
      exact .searchChain g₁ ψ₁ e₁ L a me opnt hme hle
  case ctxChain =>
      intro k0 hd L a me opnt hme hle
      exact .ctxChain hd L a me opnt hme hle
  case implS => intro k0 A B C hle; exact .implS A B C hle

theorem PfG_monoG {G G' : Formula → Prop} (hGG : ∀ B, G B → G' B) :
    ∀ {k : Nat} {φ : Formula},
    PfG G k φ → PfG G' k φ := by
  intro k φ h
  refine PfG.rec
    (motive_1 := fun me oppo body a n _ => PlaysProofG G' me oppo body a n)
    (motive_2 := fun k φ _ => AtomProvableG G' k φ)
    (motive_3 := fun k φ _ => PfG G' k φ)
    ?const ?self ?opp ?bot ?sim ?ite_t ?ite_f ?search_t ?search_f ?atomMk
    ?atom ?sb ?ss ?bss ?bsearch ?iteB ?eqR ?eqN ?mp ?itrans ?weaken ?sts
    ?atomBox ?boxIntro ?axK ?box4 ?diagF ?diagB ?axKf ?impS2 ?boxMono ?atomNeg
    ?implRefl ?implK ?contrapose ?searchChain ?ctxChain ?implS h
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
  case atom => intro k0 φ0 _ ih; exact .atom ih
  case sb => intro k0 g ψ a b me oppo hme hle; exact .searchBranch g ψ a b me oppo hme hle
  case ss => intro k0 me p q oppo a hme hle; exact .simStep me p q oppo a hme hle
  case bss => intro k0 me p q oppo a hme hle; exact .botSimStep me p q oppo a hme hle
  case bsearch => intro k0 g ψ a b me oppo hme hle; exact .botSearchStep g ψ a b me oppo hme hle
  case iteB =>
      intro k0 g z a' c0 c1 ψ q me oppo hme hle
      exact .iteBranchSearch_t g z a' c0 c1 ψ q me oppo hme hle
  case eqR => intro k0 p hle; exact .eqRefl p hle
  case eqN => intro k0 p q hne hle; exact .eqNeg p q hne hle
  case mp => intro k0 m₁ m₂ A B _ _ hle hg ih1 ih2; exact .mp m₁ m₂ A B ih1 ih2 hle (hGG _ hg)
  case itrans =>
      intro k0 A B C a b _ _ hle hg ih1 ih2
      exact .implTrans A B C a b ih1 ih2 hle (hGG _ hg)
  case weaken => intro k0 A B m _ hle ih; exact .weakenImpl A B m ih hle
  case sts =>
      intro k0 k₁ k₂ m ψ₁ ψ₂ c0 c1 q me opnt hme _ hmk hle ih
      exact .searchThenSearch_t k₁ k₂ m ψ₁ ψ₂ c0 c1 q me opnt hme ih hmk hle
  case atomBox => intro k0 kBox p q a _ hle ih; exact .atomBoxImpl kBox p q a ih hle
  case boxIntro => intro kIn K A _ hle ih; exact .boxIntro kIn K A ih hle
  case axK => intro a b c m K A B _ hgate hle hg ih; exact .axK a b c m K A B ih hgate hle (hGG _ hg)
  case box4 => intro a b K A hgate hle; exact .box4 a b K A hgate hle
  case diagF => intro pm fb g K tgt _ hle hg ih; exact .diagF pm fb g K tgt ih hle (hGG _ hg)
  case diagB => intro pm fb g K tgt _ hle hg ih; exact .diagB pm fb g K tgt ih hle (hGG _ hg)
  case axKf => intro a b c K A B hgate hle; exact .axKf a b c K A B hgate hle
  case impS2 =>
      intro A B C m₁ m₂ K _ _ hle hg ih1 ih2
      exact .impS2 A B C m₁ m₂ K ih1 ih2 hle (hGG _ hg)
  case boxMono => intro a b K A hab hle; exact .boxMono a b K A hab hle
  case atomNeg => intro k0 p q b aN m _ hne hle ih; exact .atomNeg p q b aN m ih hne hle
  case implRefl => intro k0 A hle; exact .implRefl A hle
  case implK => intro k0 A B hle; exact .implK A B hle
  case contrapose => intro k0 A B m0 _ hle ih; exact .contrapose A B m0 ih hle
  case searchChain =>
      intro k0 g₁ ψ₁ e₁ L a me opnt hme hle
      exact .searchChain g₁ ψ₁ e₁ L a me opnt hme hle
  case ctxChain =>
      intro k0 hd L a me opnt hme hle
      exact .ctxChain hd L a me opnt hme hle
  case implS => intro k0 A B C hle; exact .implS A B C hle

theorem PlaysProofB_monoN {N N' : Nat} (hNN : N ≤ N') {me oppo body : Prog} {a : Action}
    {n : Nat} : PlaysProofB N me oppo body a n → PlaysProofB N' me oppo body a n :=
  PlaysProofG_monoG (fun _ h => Nat.le_trans h hNN)

theorem PfB_monoN {N N' : Nat} (hNN : N ≤ N') {k : Nat} {φ : Formula} :
    PfB N k φ → PfB N' k φ :=
  PfG_monoG (fun _ h => Nat.le_trans h hNN)

/-! ## 5. Every proof is finitely-cut: `Pf = ⋃_N PfB N`.

**D2 note**: pre-migration, the `struct` arm landed at stratum 0 (a `Derivation`'s cuts were
size-paid, not gated). Under uniform gating the ex-`Derivation` cuts flow through `mp`/
`implTrans` and contribute `maxLitF` of their cut formula to the stratum witness — the seven
transparency LEAF arms still land at stratum 0 (no premises). -/

theorem Pf_exists_PfB : ∀ {k : Nat} {φ : Formula},
    Pf k φ → ∃ N, PfB N k φ := by
  intro k φ h
  refine Pf.rec
    (motive_1 := fun me oppo body a n _ => ∃ N, PlaysProofB N me oppo body a n)
    (motive_2 := fun k φ _ => ∃ N, AtomProvableB N k φ)
    (motive_3 := fun k φ _ => ∃ N, PfB N k φ)
    ?const ?self ?opp ?bot ?sim ?ite_t ?ite_f ?search_t ?search_f ?atomMk
    ?atom ?atomNeg ?sb ?ss ?bss ?bsearch ?iteB ?sts ?searchChain ?ctxChain ?eqR ?eqN ?mp ?itrans
    ?weaken ?impS2 ?implRefl ?implK ?implS ?contrapose ?negElim
    ?boxIntro ?atomBox ?axK ?axKf ?box4 ?boxMono ?diagF ?diagB h
  case const => intro me oppo a; exact ⟨0, .const⟩
  case self => intro me oppo a n _ ih; obtain ⟨N, e⟩ := ih; exact ⟨N, .self e⟩
  case opp => intro me oppo a n _ ih; obtain ⟨N, e⟩ := ih; exact ⟨N, .opp e⟩
  case bot => intro me oppo p a n _ ih; obtain ⟨N, e⟩ := ih; exact ⟨N, .bot e⟩
  case sim => intro a n me oppo p q _ ih; obtain ⟨N, e⟩ := ih; exact ⟨N, .sim e⟩
  case ite_t =>
      intro me oppo g r m a' p a n q _ hr _ ihg ihp
      obtain ⟨N₁, e₁⟩ := ihg
      obtain ⟨N₂, e₂⟩ := ihp
      exact ⟨max N₁ N₂, .ite_t (PlaysProofB_monoN (Nat.le_max_left _ _) e₁) hr
        (PlaysProofB_monoN (Nat.le_max_right _ _) e₂)⟩
  case ite_f =>
      intro me oppo g r m a' q a n p _ hr _ ihg ihq
      obtain ⟨N₁, e₁⟩ := ihg
      obtain ⟨N₂, e₂⟩ := ihq
      exact ⟨max N₁ N₂, .ite_f (PlaysProofB_monoN (Nat.le_max_left _ _) e₁) hr
        (PlaysProofB_monoN (Nat.le_max_right _ _) e₂)⟩
  case search_t =>
      intro kg me oppo p a n g q _ _ ihg ihp
      obtain ⟨N₁, e₁⟩ := ihg
      obtain ⟨N₂, e₂⟩ := ihp
      exact ⟨max N₁ N₂, .search_t (PfB_monoN (Nat.le_max_left _ _) e₁)
        (PlaysProofB_monoN (Nat.le_max_right _ _) e₂)⟩
  case search_f =>
      intro m me oppo q a n kg g p _ _ ihn ihq
      obtain ⟨N₁, e₁⟩ := ihn
      obtain ⟨N₂, e₂⟩ := ihq
      exact ⟨max N₁ N₂, .search_f (PfB_monoN (Nat.le_max_left _ _) e₁)
        (PlaysProofB_monoN (Nat.le_max_right _ _) e₂)⟩
  case atomMk => intro me oppo a n k _ hle ih; obtain ⟨N, e⟩ := ih; exact ⟨N, .mk e hle⟩
  case atom => intro k0 φ0 _ ih; obtain ⟨N, e⟩ := ih; exact ⟨N, .atom e⟩
  case sb =>
      intro k0 g ψ a b me oppo hme hle
      exact ⟨0, .searchBranch g ψ a b me oppo hme hle⟩
  case ss => intro k0 me p q oppo a hme hle; exact ⟨0, .simStep me p q oppo a hme hle⟩
  case bss => intro k0 me p q oppo a hme hle; exact ⟨0, .botSimStep me p q oppo a hme hle⟩
  case bsearch =>
      intro k0 g ψ a b me oppo hme hle
      exact ⟨0, .botSearchStep g ψ a b me oppo hme hle⟩
  case iteB =>
      intro k0 g z a' c0 c1 ψ q me oppo hme hle
      exact ⟨0, .iteBranchSearch_t g z a' c0 c1 ψ q me oppo hme hle⟩
  case eqR => intro k0 p hle; exact ⟨0, .eqRefl p hle⟩
  case eqN => intro k0 p q hne hle; exact ⟨0, .eqNeg p q hne hle⟩
  case searchChain =>
      intro k0 g₁ ψ₁ e₁ L a me opnt hme hle
      exact ⟨0, .searchChain g₁ ψ₁ e₁ L a me opnt hme hle⟩
  case ctxChain =>
      intro k0 hd L a me opnt hme hle
      exact ⟨0, .ctxChain hd L a me opnt hme hle⟩
  case implS => intro k0 A B C hle; exact ⟨0, .implS A B C hle⟩
  case mp =>
      intro k0 m₁ m₂ A B _ _ hle ih1 ih2
      obtain ⟨N₁, e₁⟩ := ih1
      obtain ⟨N₂, e₂⟩ := ih2
      refine ⟨max (max N₁ N₂) (maxLitF A), .mp m₁ m₂ A B ?_ ?_ hle ?_⟩
      · exact PfB_monoN (by omega) e₁
      · exact PfB_monoN (by omega) e₂
      · exact Nat.le_max_right _ _
  case itrans =>
      intro k0 A B C a b _ _ hle ih1 ih2
      obtain ⟨N₁, e₁⟩ := ih1
      obtain ⟨N₂, e₂⟩ := ih2
      refine ⟨max (max N₁ N₂) (maxLitF B), .implTrans A B C a b ?_ ?_ hle ?_⟩
      · exact PfB_monoN (by omega) e₁
      · exact PfB_monoN (by omega) e₂
      · exact Nat.le_max_right _ _
  case weaken =>
      intro k0 A B m _ hle ih
      obtain ⟨N, e⟩ := ih
      exact ⟨N, .weakenImpl A B m e hle⟩
  case sts =>
      intro k0 k₁ k₂ m ψ₁ ψ₂ c0 c1 q me opnt hme _ hmk hle ih
      obtain ⟨N, e⟩ := ih
      exact ⟨N, .searchThenSearch_t k₁ k₂ m ψ₁ ψ₂ c0 c1 q me opnt hme e hmk hle⟩
  case atomBox =>
      intro k0 kBox p q a _ hle ih
      obtain ⟨N, e⟩ := ih
      exact ⟨N, .atomBoxImpl kBox p q a e hle⟩
  case boxIntro =>
      intro kIn K A _ hle ih
      obtain ⟨N, e⟩ := ih
      exact ⟨N, .boxIntro kIn K A e hle⟩
  case axK =>
      intro a b c m K A B _ hgate hle ih
      obtain ⟨N, e⟩ := ih
      exact ⟨max N (maxLitF (.box a (.impl A B))),
        .axK a b c m K A B (PfB_monoN (Nat.le_max_left _ _) e)
          hgate hle (Nat.le_max_right _ _)⟩
  case box4 => intro a b K A hgate hle; exact ⟨0, .box4 a b K A hgate hle⟩
  case diagF =>
      intro pm fb g K tgt _ hle ih
      obtain ⟨N, e⟩ := ih
      exact ⟨max N (maxLitF (.impl (.box fb tgt) tgt)),
        .diagF pm fb g K tgt (PfB_monoN (Nat.le_max_left _ _) e)
          hle (Nat.le_max_right _ _)⟩
  case diagB =>
      intro pm fb g K tgt _ hle ih
      obtain ⟨N, e⟩ := ih
      exact ⟨max N (maxLitF (.impl (.box fb tgt) tgt)),
        .diagB pm fb g K tgt (PfB_monoN (Nat.le_max_left _ _) e)
          hle (Nat.le_max_right _ _)⟩
  case axKf => intro a b c K A B hgate hle; exact ⟨0, .axKf a b c K A B hgate hle⟩
  case impS2 =>
      intro A B C m₁ m₂ K _ _ hle ih1 ih2
      obtain ⟨N₁, e₁⟩ := ih1
      obtain ⟨N₂, e₂⟩ := ih2
      refine ⟨max (max N₁ N₂) (maxLitF B), .impS2 A B C m₁ m₂ K ?_ ?_ hle ?_⟩
      · exact PfB_monoN (by omega) e₁
      · exact PfB_monoN (by omega) e₂
      · exact Nat.le_max_right _ _
  case boxMono => intro a b K A hab hle; exact ⟨0, .boxMono a b K A hab hle⟩
  case implRefl => intro k0 A hle; exact ⟨0, .implRefl A hle⟩
  case implK => intro k0 A B hle; exact ⟨0, .implK A B hle⟩
  case contrapose =>
      intro k0 A B m0 _h hle ih
      obtain ⟨N, e⟩ := ih
      exact ⟨N, .contrapose A B m0 e hle⟩
  case negElim =>
      -- vacuous: the premises are contradictory by soundness
      intro k0 A B m₁ m₂ h1 h2 hle _ih1 _ih2
      exact absurd (PD.BaseTheorems.Pf_sound _ _ h2) (PD.BaseTheorems.Pf_sound _ _ h1)
  case atomNeg =>
      intro k0 p q b aN m _ hne hle ih
      obtain ⟨N, e⟩ := ih
      exact ⟨N, .atomNeg p q b aN m e hne hle⟩

/-- **`Pf` is exactly the union of its literal-bounded strata.** -/
theorem Pf_iff_exists_PfB (k : Nat) (φ : Formula) :
    Pf k φ ↔ ∃ N, PfB N k φ :=
  ⟨Pf_exists_PfB, fun ⟨_, h⟩ => PfG_sound h⟩

/-! ## 6. THE T4.1b CONJECTURE, stated. -/

/-- **CUT RELEVANCE**: the stratum is computable from the query — minimal proofs never need
    cut formulas (or `axK`/`diag` premises) beyond a bound `N₀ k φ` readable off the query.
    See `Research/Notes/CUT_RELEVANCE.md` for the falsification of the ORIGINAL (modest-gate)
    form and the instance-gate repair; this stratum form is the raw statement.

    Given `CutRelevance N₀` for computable `N₀` (with its modest refinement, T4.4), the
    T4.1a stabilization template over the finite query space decides `Pf`: `proofSearch := D`,
    `eval` computable, outcomes `by decide`. If it FAILS, `Pf` is a candidate undecidable
    bounded-provability predicate. -/
def CutRelevance (N₀ : Nat → Formula → Nat) : Prop :=
  ∀ k φ, Pf k φ → PfB (N₀ k φ) k φ

/-- Under the conjecture, deciding the stratum decides `Pf`. -/
theorem Pf_iff_PfB_of_cutRelevance {N₀ : Nat → Formula → Nat}
    (hcr : CutRelevance N₀) (k : Nat) (φ : Formula) :
    Pf k φ ↔ PfB (N₀ k φ) k φ :=
  ⟨hcr k φ, PfG_sound⟩

end PD.T42
