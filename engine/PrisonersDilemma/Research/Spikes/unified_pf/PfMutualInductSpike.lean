import PrisonersDilemma.Pf

/-!
# Spike — replacement-world `Pf`: the mutualization regression, and its cure

De-risks **§0 of `Research/Notes/PF_REPLACEMENT_ASSESSMENT.md`**: under FULL replacement
(retire `Derivation`/`Provable`, point the oracle and `PlaysProof.search_t` at `Pf`), `Pf`
must enter the mutual block with the execution layer — and the coexistence layer's headline
ergonomic win (named `induction … with`) is a property of `Pf` being STANDALONE. Two claims
to machine-check, at FULL scale (the real 9 + 1 + 22 mutual block over the real
`Formula`/`Prog`, transcript costs and all):

1. **The regression is real**: the `induction` tactic REJECTS the mutualized `PfM`
   (checked below with `fail_if_success` — if a future Lean version learns mutual
   induction, that guard breaks and this spike happily retires).
2. **The mitigation works and is bounded**: `PfM.induct` — a named-hypothesis
   `@[elab_as_elim]` eliminator hand-derived ONCE from the raw 32-minor-premise mutual
   recursor (PlaysProof/AtomProvable motives discharged to `True`) — restores
   `induction h using PfM.induct with | atom … | mp …` with named arms. Demonstrated on a
   real exclusion-style theorem (`no_pfM_endsIn_falseEq`, fully syntactic).

This file is the **day-one artifact** a replacement would need: if the merge ever happens,
`PfM.induct` (or its generated twin) ships in the same commit as the merged type.

The full replacement EQUIVALENCE (`PfM`+`PlaysProofM` ↔ the engine triple) is out of scope
here — it is part of the ~23k-line port the assessment prices, not of the ergonomics
question this spike answers.

NOT root-imported. Check:
  `lake env lean PrisonersDilemma/Research/Spikes/unified_pf/PfMutualInductSpike.lean`
-/

namespace PD.PfMutualSpike

open PD

/-! ## 1. The replacement-world mutual block

`PlaysProofM` is the engine's `PlaysProof` with its `Provable` premises re-pointed at `PfM`
(the back-edge that forces mutuality — compare `PlaysProofG` in `Decidability/T42`, which
threads `ProvableG` the same way). `AtomProvableM` is the certificate bridge. `PfM` is the
promoted `Pf` verbatim, with `AtomProvable` premises re-pointed at `AtomProvableM`. -/

mutual
  inductive PlaysProofM : (me opponent body : Prog) → Action → Nat → Prop where
    | const :
        PlaysProofM me opponent (.const a) a c_leaf
    | self :
        PlaysProofM me opponent me a n →
        PlaysProofM me opponent .self a (n + c_node)
    | opp :
        PlaysProofM me opponent opponent a n →
        PlaysProofM me opponent .opp a (n + c_node)
    | bot :
        PlaysProofM me opponent p a n →
        PlaysProofM me opponent (.bot p) a (n + c_node)
    | sim :
        PlaysProofM (p.subst me opponent) (q.subst me opponent) (p.subst me opponent) a n →
        PlaysProofM me opponent (.sim p q) a (n + c_node)
    | ite_t :
        PlaysProofM me opponent b r m → (r == a') = true →
        PlaysProofM me opponent p a n →
        PlaysProofM me opponent (.ite b a' p q) a (m + n + c_node)
    | ite_f :
        PlaysProofM me opponent b r m → (r == a') = false →
        PlaysProofM me opponent q a n →
        PlaysProofM me opponent (.ite b a' p q) a (m + n + c_node)
    -- THE BACK-EDGE: the guard consults the unified system — this is what mutualizes `PfM`.
    | search_t :
        PfM k (φ.subst me opponent) →
        PlaysProofM me opponent p a n →
        PlaysProofM me opponent (.search k φ p q) a (n + c_guard k + c_node)
    | search_f :
        PfM m (.neg (φ.subst me opponent)) →
        PlaysProofM me opponent q a n →
        PlaysProofM me opponent (.search k φ p q) a (n + m + k + c_node)

  inductive AtomProvableM : Nat → Formula → Prop where
    | mk : PlaysProofM me opponent me a n → n ≤ k → AtomProvableM k (.plays me opponent a)

  /-- The unified type, mutualized — `PrisonersDilemma/Pf.lean`'s `Pf` with
      `AtomProvable ↦ AtomProvableM`. -/
  inductive PfM : Nat → Formula → Prop where
    | atom : AtomProvableM k φ → PfM k φ
    | searchBranch (g : Nat) (ψ : Formula) (a b : Action) (me opponent : Prog)
        (hme : me = .search g ψ (.const a) (.const b)) :
        (Formula.impl (.box g (ψ.subst me opponent)) (.plays me opponent a)).size ≤ k →
        PfM k (.impl (.box g (ψ.subst me opponent)) (.plays me opponent a))
    | simStep (me p q opponent : Prog) (a : Action) (hme : me = .sim p q) :
        (Formula.impl (.plays (p.subst me opponent) (q.subst me opponent) a)
                      (.plays me opponent a)).size ≤ k →
        PfM k (.impl (.plays (p.subst me opponent) (q.subst me opponent) a)
                     (.plays me opponent a))
    | botSimStep (me p q opponent : Prog) (a : Action) (hme : me = .bot (.sim p q)) :
        (Formula.impl (.plays (p.subst me opponent) (q.subst me opponent) a)
                      (.plays me opponent a)).size ≤ k →
        PfM k (.impl (.plays (p.subst me opponent) (q.subst me opponent) a)
                     (.plays me opponent a))
    | botSearchStep (g : Nat) (ψ : Formula) (a b : Action) (me opponent : Prog)
        (hme : me = .bot (.search g ψ (.const a) (.const b))) :
        (Formula.impl (.box g (ψ.subst me opponent)) (.plays me opponent a)).size ≤ k →
        PfM k (.impl (.box g (ψ.subst me opponent)) (.plays me opponent a))
    | iteBranchSearch_t (g : Nat) (z : Prog) (a' c0 c1 : Action) (ψ : Formula)
        (q me opponent : Prog)
        (hme : me = .ite (.sim .opp (.bot z)) a'
                         (.search g ψ (.const c0) (.const c1)) q) :
        (Formula.impl (.plays opponent (.bot z) a')
                      (.impl (.box g (ψ.subst me opponent))
                             (.plays me opponent c0))).size ≤ k →
        PfM k (.impl (.plays opponent (.bot z) a')
                     (.impl (.box g (ψ.subst me opponent))
                            (.plays me opponent c0)))
    | eqRefl (p : Prog) :
        (Formula.eq p p).size ≤ k → PfM k (.eq p p)
    | eqNeg (p q : Prog) (hne : p ≠ q) :
        (Formula.neg (.eq p q)).size ≤ k → PfM k (.neg (.eq p q))
    | mp (m₁ m₂ : Nat) (φ α : Formula) :
        PfM m₁ (.impl φ α) → PfM m₂ φ → m₁ + m₂ + α.size ≤ k → PfM k α
    | implTrans (φ ψ χ : Formula) (a b : Nat) :
        PfM a (.impl φ ψ) → PfM b (.impl ψ χ) →
        a + b + (Formula.impl φ χ).size ≤ k → PfM k (.impl φ χ)
    | weakenImpl (φ ψ : Formula) (m : Nat) :
        PfM m ψ → m + (Formula.impl φ ψ).size ≤ k → PfM k (.impl φ ψ)
    | searchThenSearch_t (k₁ k₂ m : Nat) (ψ₁ ψ₂ : Formula) (c0 c1 : Action)
        (q me opponent : Prog)
        (hme : me = .search k₁ ψ₁ (.search k₂ ψ₂ (.const c0) (.const c1)) q) :
        PfM m (ψ₂.subst me opponent) → m ≤ k₂ →
        c_guard k₂ +
          (Formula.impl (.box k₁ (ψ₁.subst me opponent)) (.plays me opponent c0)).size ≤ k →
        PfM k (.impl (.box k₁ (ψ₁.subst me opponent)) (.plays me opponent c0))
    | atomBoxImpl (kBox : Nat) (p q : Prog) (a : Action) :
        AtomProvableM kBox (.plays p q a) →
        kBox + (Formula.impl (.plays p q a) (.box kBox (.plays p q a))).size ≤ k →
        PfM k (.impl (.plays p q a) (.box kBox (.plays p q a)))
    | boxIntro (kIn K : Nat) (φ : Formula) :
        PfM kIn φ →
        kIn + (Formula.box kIn φ).size ≤ K →
        PfM K (.box kIn φ)
    | axK (a b c m K : Nat) (φ α : Formula) :
        PfM m (.box a (.impl φ α)) →
        a + b + α.size ≤ c →
        m + (Formula.impl (.box b φ) (.box c α)).size ≤ K →
        PfM K (.impl (.box b φ) (.box c α))
    | box4 (a b K : Nat) (φ : Formula) :
        a + (Formula.box a φ).size ≤ b →
        (Formula.impl (.box a φ) (.box b (.box a φ))).size ≤ K →
        PfM K (.impl (.box a φ) (.box b (.box a φ)))
    | diagF (pm fb g K : Nat) (tgt : Formula) :
        PfM pm (.impl (.box fb tgt) tgt) →
        pm + (Formula.impl (.diag g tgt) (.impl (.box g (.diag g tgt)) tgt)).size ≤ K →
        PfM K (.impl (.diag g tgt) (.impl (.box g (.diag g tgt)) tgt))
    | diagB (pm fb g K : Nat) (tgt : Formula) :
        PfM pm (.impl (.box fb tgt) tgt) →
        pm + (Formula.impl (.impl (.box g (.diag g tgt)) tgt) (.diag g tgt)).size ≤ K →
        PfM K (.impl (.impl (.box g (.diag g tgt)) tgt) (.diag g tgt))
    | axKf (a b c K : Nat) (φ α : Formula) :
        a + b + α.size ≤ c →
        (Formula.impl (.box a (.impl φ α)) (.impl (.box b φ) (.box c α))).size ≤ K →
        PfM K (.impl (.box a (.impl φ α)) (.impl (.box b φ) (.box c α)))
    | impS2 (φ ψ χ : Formula) (m₁ m₂ K : Nat) :
        PfM m₁ (.impl φ (.impl ψ χ)) → PfM m₂ (.impl φ ψ) →
        m₁ + m₂ + (Formula.impl φ χ).size ≤ K → PfM K (.impl φ χ)
    | boxMono (a b K : Nat) (φ : Formula) :
        a ≤ b →
        (Formula.impl (.box a φ) (.box b φ)).size ≤ K →
        PfM K (.impl (.box a φ) (.box b φ))
    | atomNeg (p q : Prog) (b aN : Action) (m : Nat) :
        AtomProvableM m (.plays p q b) → b ≠ aN →
        m + (Formula.neg (.plays p q aN)).size ≤ k →
        PfM k (.neg (.plays p q aN))
end

/-! ## 2. Claim 1 — the regression is REAL (machine-checked)

The `induction` tactic rejects the mutual `PfM`. If a future toolchain learns mutual
structural induction, `fail_if_success` fails, this example breaks, and the spike (and
assessment §0) should be revisited — the guard is deliberate. -/

set_option linter.unusedVariables false in
example {k : Nat} {φ : Formula} (h : PfM k φ) : True := by
  fail_if_success induction h
  trivial

/-! ## 3. Claim 2 — the cure: `PfM.induct`, the named eliminator derived ONCE

One theorem, proved by ONE application of the raw 32-minor-premise mutual recursor
(`PlaysProofM`/`AtomProvableM` motives discharged to `True` — their ten arms are the
`trivial` lambdas). Every `PfM` rule becomes a NAMED hypothesis whose binder name is the
case label; all binders are explicit so `with`-patterns bind predictably. The motive takes
the proof term (the shape `induction … using` requires: its conclusion is
`motive k φ h` with `h` the major premise); proof-irrelevant motives instantiate it as
`fun k φ _ => …`, which is what bot-facing inductions do. -/

@[elab_as_elim]
theorem PfM.induct (motive : (k : Nat) → (φ : Formula) → PfM k φ → Prop)
    (atom : ∀ (k : Nat) (φ : Formula) (h : AtomProvableM k φ), motive k φ (.atom h))
    (searchBranch : ∀ (k g : Nat) (ψ : Formula) (a b : Action) (me opponent : Prog)
        (hme : me = .search g ψ (.const a) (.const b))
        (hle : (Formula.impl (.box g (ψ.subst me opponent)) (.plays me opponent a)).size ≤ k),
        motive k _ (.searchBranch g ψ a b me opponent hme hle))
    (simStep : ∀ (k : Nat) (me p q opponent : Prog) (a : Action)
        (hme : me = .sim p q)
        (hle : (Formula.impl (.plays (p.subst me opponent) (q.subst me opponent) a)
                             (.plays me opponent a)).size ≤ k),
        motive k _ (.simStep me p q opponent a hme hle))
    (botSimStep : ∀ (k : Nat) (me p q opponent : Prog) (a : Action)
        (hme : me = .bot (.sim p q))
        (hle : (Formula.impl (.plays (p.subst me opponent) (q.subst me opponent) a)
                             (.plays me opponent a)).size ≤ k),
        motive k _ (.botSimStep me p q opponent a hme hle))
    (botSearchStep : ∀ (k g : Nat) (ψ : Formula) (a b : Action) (me opponent : Prog)
        (hme : me = .bot (.search g ψ (.const a) (.const b)))
        (hle : (Formula.impl (.box g (ψ.subst me opponent)) (.plays me opponent a)).size ≤ k),
        motive k _ (.botSearchStep g ψ a b me opponent hme hle))
    (iteBranchSearch_t : ∀ (k g : Nat) (z : Prog) (a' c0 c1 : Action) (ψ : Formula)
        (q me opponent : Prog)
        (hme : me = .ite (.sim .opp (.bot z)) a' (.search g ψ (.const c0) (.const c1)) q)
        (hle : (Formula.impl (.plays opponent (.bot z) a')
                             (.impl (.box g (ψ.subst me opponent))
                                    (.plays me opponent c0))).size ≤ k),
        motive k _ (.iteBranchSearch_t g z a' c0 c1 ψ q me opponent hme hle))
    (eqRefl : ∀ (k : Nat) (p : Prog) (hle : (Formula.eq p p).size ≤ k),
        motive k _ (.eqRefl p hle))
    (eqNeg : ∀ (k : Nat) (p q : Prog) (hne : p ≠ q)
        (hle : (Formula.neg (.eq p q)).size ≤ k),
        motive k _ (.eqNeg p q hne hle))
    (mp : ∀ (k m₁ m₂ : Nat) (φ α : Formula)
        (h1 : PfM m₁ (.impl φ α)) (h2 : PfM m₂ φ) (hle : m₁ + m₂ + α.size ≤ k),
        motive m₁ (.impl φ α) h1 → motive m₂ φ h2 →
        motive k α (.mp m₁ m₂ φ α h1 h2 hle))
    (implTrans : ∀ (k : Nat) (φ ψ χ : Formula) (a b : Nat)
        (h1 : PfM a (.impl φ ψ)) (h2 : PfM b (.impl ψ χ))
        (hle : a + b + (Formula.impl φ χ).size ≤ k),
        motive a (.impl φ ψ) h1 → motive b (.impl ψ χ) h2 →
        motive k _ (.implTrans φ ψ χ a b h1 h2 hle))
    (weakenImpl : ∀ (k : Nat) (φ ψ : Formula) (m : Nat)
        (hψ : PfM m ψ) (hle : m + (Formula.impl φ ψ).size ≤ k),
        motive m ψ hψ → motive k _ (.weakenImpl φ ψ m hψ hle))
    (searchThenSearch_t : ∀ (k k₁ k₂ m : Nat) (ψ₁ ψ₂ : Formula) (c0 c1 : Action)
        (q me opponent : Prog)
        (hme : me = .search k₁ ψ₁ (.search k₂ ψ₂ (.const c0) (.const c1)) q)
        (hprud : PfM m (ψ₂.subst me opponent)) (hmk : m ≤ k₂)
        (hle : c_guard k₂ +
          (Formula.impl (.box k₁ (ψ₁.subst me opponent)) (.plays me opponent c0)).size ≤ k),
        motive m (ψ₂.subst me opponent) hprud →
        motive k _ (.searchThenSearch_t k₁ k₂ m ψ₁ ψ₂ c0 c1 q me opponent hme hprud hmk hle))
    (atomBoxImpl : ∀ (k kBox : Nat) (p q : Prog) (a : Action)
        (hatom : AtomProvableM kBox (.plays p q a))
        (hle : kBox + (Formula.impl (.plays p q a) (.box kBox (.plays p q a))).size ≤ k),
        motive k _ (.atomBoxImpl kBox p q a hatom hle))
    (boxIntro : ∀ (kIn K : Nat) (φ : Formula)
        (hprem : PfM kIn φ) (hle : kIn + (Formula.box kIn φ).size ≤ K),
        motive kIn φ hprem → motive K _ (.boxIntro kIn K φ hprem hle))
    (axK : ∀ (a b c m K : Nat) (φ α : Formula)
        (hprem : PfM m (.box a (.impl φ α))) (hgate : a + b + α.size ≤ c)
        (hle : m + (Formula.impl (.box b φ) (.box c α)).size ≤ K),
        motive m (.box a (.impl φ α)) hprem →
        motive K _ (.axK a b c m K φ α hprem hgate hle))
    (box4 : ∀ (a b K : Nat) (φ : Formula)
        (hgate : a + (Formula.box a φ).size ≤ b)
        (hsz : (Formula.impl (.box a φ) (.box b (.box a φ))).size ≤ K),
        motive K _ (.box4 a b K φ hgate hsz))
    (diagF : ∀ (pm fb g K : Nat) (tgt : Formula)
        (hgate : PfM pm (.impl (.box fb tgt) tgt))
        (hle : pm + (Formula.impl (.diag g tgt) (.impl (.box g (.diag g tgt)) tgt)).size ≤ K),
        motive pm (.impl (.box fb tgt) tgt) hgate →
        motive K _ (.diagF pm fb g K tgt hgate hle))
    (diagB : ∀ (pm fb g K : Nat) (tgt : Formula)
        (hgate : PfM pm (.impl (.box fb tgt) tgt))
        (hle : pm + (Formula.impl (.impl (.box g (.diag g tgt)) tgt) (.diag g tgt)).size ≤ K),
        motive pm (.impl (.box fb tgt) tgt) hgate →
        motive K _ (.diagB pm fb g K tgt hgate hle))
    (axKf : ∀ (a b c K : Nat) (φ α : Formula)
        (hgate : a + b + α.size ≤ c)
        (hsz : (Formula.impl (.box a (.impl φ α)) (.impl (.box b φ) (.box c α))).size ≤ K),
        motive K _ (.axKf a b c K φ α hgate hsz))
    (impS2 : ∀ (φ ψ χ : Formula) (m₁ m₂ K : Nat)
        (h1 : PfM m₁ (.impl φ (.impl ψ χ))) (h2 : PfM m₂ (.impl φ ψ))
        (hle : m₁ + m₂ + (Formula.impl φ χ).size ≤ K),
        motive m₁ (.impl φ (.impl ψ χ)) h1 → motive m₂ (.impl φ ψ) h2 →
        motive K _ (.impS2 φ ψ χ m₁ m₂ K h1 h2 hle))
    (boxMono : ∀ (a b K : Nat) (φ : Formula)
        (hab : a ≤ b) (hsz : (Formula.impl (.box a φ) (.box b φ)).size ≤ K),
        motive K _ (.boxMono a b K φ hab hsz))
    (atomNeg : ∀ (k : Nat) (p q : Prog) (b aN : Action) (m : Nat)
        (hatom : AtomProvableM m (.plays p q b)) (hne : b ≠ aN)
        (hle : m + (Formula.neg (.plays p q aN)).size ≤ k),
        motive k _ (.atomNeg p q b aN m hatom hne hle))
    {k : Nat} {φ : Formula} (h : PfM k φ) : motive k φ h :=
  PfM.rec
    (motive_1 := fun _ _ _ _ _ _ => True)
    (motive_2 := fun _ _ _ => True)
    (motive_3 := motive)
    -- PlaysProofM arms (9) + AtomProvableM.mk (1): motive is `True`.
    trivial (fun _ _ => trivial) (fun _ _ => trivial) (fun _ _ => trivial) (fun _ _ => trivial)
    (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ => trivial) (fun _ _ _ _ => trivial)
    (fun _ _ _ _ => trivial)
    (fun _ _ _ => trivial)
    -- PfM arms (22): route each to its named hypothesis.
    (fun {k} {φ} hatom _ => atom k φ hatom)
    (fun {k} g ψ a b me opponent hme hle => searchBranch k g ψ a b me opponent hme hle)
    (fun {k} me p q opponent a hme hle => simStep k me p q opponent a hme hle)
    (fun {k} me p q opponent a hme hle => botSimStep k me p q opponent a hme hle)
    (fun {k} g ψ a b me opponent hme hle => botSearchStep k g ψ a b me opponent hme hle)
    (fun {k} g z a' c0 c1 ψ q me opponent hme hle =>
      iteBranchSearch_t k g z a' c0 c1 ψ q me opponent hme hle)
    (fun {k} p hle => eqRefl k p hle)
    (fun {k} p q hne hle => eqNeg k p q hne hle)
    (fun {k} m₁ m₂ φ α h1 h2 hle ih1 ih2 => mp k m₁ m₂ φ α h1 h2 hle ih1 ih2)
    (fun {k} φ ψ χ a b h1 h2 hle ih1 ih2 => implTrans k φ ψ χ a b h1 h2 hle ih1 ih2)
    (fun {k} φ ψ m hψ hle ih => weakenImpl k φ ψ m hψ hle ih)
    (fun {k} k₁ k₂ m ψ₁ ψ₂ c0 c1 q me opponent hme hprud hmk hle ih =>
      searchThenSearch_t k k₁ k₂ m ψ₁ ψ₂ c0 c1 q me opponent hme hprud hmk hle ih)
    (fun {k} kBox p q a hatom hle _ => atomBoxImpl k kBox p q a hatom hle)
    (fun kIn K φ hprem hle ih => boxIntro kIn K φ hprem hle ih)
    (fun a b c m K φ α hprem hgate hle ih => axK a b c m K φ α hprem hgate hle ih)
    (fun a b K φ hgate hsz => box4 a b K φ hgate hsz)
    (fun pm fb g K tgt hgate hle ih => diagF pm fb g K tgt hgate hle ih)
    (fun pm fb g K tgt hgate hle ih => diagB pm fb g K tgt hgate hle ih)
    (fun a b c K φ α hgate hsz => axKf a b c K φ α hgate hsz)
    (fun φ ψ χ m₁ m₂ K h1 h2 hle ih1 ih2 => impS2 φ ψ χ m₁ m₂ K h1 h2 hle ih1 ih2)
    (fun a b K φ hab hsz => boxMono a b K φ hab hsz)
    (fun {k} p q b aN m hatom hne hle _ => atomNeg k p q b aN m hatom hne hle)
    h

/-! ## 4. The demo — a real exclusion theorem, NAMED induction in the mutual world

`EndsInFalseEq φ`: φ is (or is an `.impl`-chain ending in) a structural identity `.eq p q`
of DISTINCT programs. The theorem: **`PfM` never proves such a formula** — i.e. even in
the replacement world, `S` cannot certify a false structural identity. Fully SYNTACTIC
(the only `.eq`-producing rule is `eqRefl`, whose programs are equal), so the spike needs
no semantics — and every arm is a one-liner in a single NAMED induction via `PfM.induct`.
Compare: without `PfM.induct` this proof is a 32-lambda positional `PfM.rec`. -/

/-- The forbidden motive: an `.impl`-chain ending in a false structural identity. -/
def EndsInFalseEq : Formula → Prop
  | .eq p q => p ≠ q
  | .impl _ ψ => EndsInFalseEq ψ
  | _ => False

theorem no_pfM_endsIn_falseEq : ∀ {k : Nat} {φ : Formula}, PfM k φ → ¬ EndsInFalseEq φ := by
  intro k φ h
  induction h using PfM.induct with
  -- the certificate bridge concludes a `.plays` atom — not an `.eq`
  | atom k' φ' hatom =>
      cases hatom with
      | mk cert hle => simp [EndsInFalseEq]
  -- source-transparency leaves conclude `.plays`-ended implications
  | searchBranch k' g ψ a b me opponent hme hle => simp [EndsInFalseEq]
  | simStep k' me p q opponent a hme hle => simp [EndsInFalseEq]
  | botSimStep k' me p q opponent a hme hle => simp [EndsInFalseEq]
  | botSearchStep k' g ψ a b me opponent hme hle => simp [EndsInFalseEq]
  | iteBranchSearch_t k' g z a' c0 c1 ψ q me opponent hme hle => simp [EndsInFalseEq]
  | searchThenSearch_t k' k₁ k₂ m ψ₁ ψ₂ c0 c1 q me opponent hme hprud hmk hle _ih =>
      simp [EndsInFalseEq]
  -- the ONLY `.eq`-producer: its programs are EQUAL — the motive's `p ≠ p` is absurd
  | eqRefl k' p hle => intro hF; exact absurd rfl hF
  -- `.neg`/`.box`-ended conclusions: the motive is `False` there
  | eqNeg k' p q hne hle => simp [EndsInFalseEq]
  | atomNeg k' p q b aN m hatom hne hle => simp [EndsInFalseEq]
  | atomBoxImpl k' kBox p q a hatom hle => simp [EndsInFalseEq]
  | boxIntro kIn K φ' hprem hle _ih => simp [EndsInFalseEq]
  | axK a b c m K φ' α hprem hgate hle _ih => simp [EndsInFalseEq]
  | box4 a b K φ' hgate hsz => simp [EndsInFalseEq]
  | diagB pm fb g K tgt hgate hle _ih => simp [EndsInFalseEq]
  | axKf a b c K φ' α hgate hsz => simp [EndsInFalseEq]
  | boxMono a b K φ' hab hsz => simp [EndsInFalseEq]
  -- implication-formers: the motive peels the `.impl`; recurse on the carrying premise
  | mp k' m₁ m₂ φ' α h1 h2 hle ih1 _ih2 => intro hF; exact ih1 hF
  | implTrans k' φ' ψ χ a b h1 h2 hle _ih1 ih2 => intro hF; exact ih2 hF
  | weakenImpl k' φ' ψ m hψ hle ih => intro hF; exact ih hF
  | impS2 φ' ψ χ m₁ m₂ K h1 h2 hle ih1 _ih2 => intro hF; exact ih1 hF
  | diagF pm fb g K tgt hgate hle ih => intro hF; exact ih hF

/-! ## VERDICT

* **Claim 1 CONFIRMED**: `induction h` fails on the mutualized `PfM`
  (`fail_if_success`, §2) — full replacement really does forfeit the coexistence layer's
  named induction, exactly as `PF_REPLACEMENT_ASSESSMENT.md` §0 states.
* **Claim 2 CONFIRMED**: the cure is real and bounded — `PfM.induct` is ONE theorem
  (one raw mutual-recursor application, the ten execution arms discharged by `trivial`),
  and `induction … using PfM.induct with` restores fully NAMED arms
  (`no_pfM_endsIn_falseEq`: 22 named one-liner arms, zero positional lambdas at the
  use-site).
* Bonus: the demo is a real (small) theorem of the replacement world — `S` mutualized
  still never proves a false structural identity — established syntactically.
* Corollary for the CURRENT engine: the same recipe applied to the existing
  `PlaysProof`/`AtomProvable`/`Provable` block (a `Provable.induct`) would fix today's
  positional-`Provable.rec` pain WITHOUT any replacement — the cheapest route to the
  ergonomics, as the assessment's §3 recommends.

If replacement ever happens: this file's `PfM.induct` pattern ships in the same commit as
the merged type — it is the difference between the merge improving and regressing the
proof-writing experience. -/

#check @PfM.induct
#check @no_pfM_endsIn_falseEq
#print axioms no_pfM_endsIn_falseEq

end PD.PfMutualSpike
