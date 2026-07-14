import PrisonersDilemma.Base.AtomCerts

/-!
# Base/Soundness — every provable formula is true

The soundness spine: `eval_mono` (fuel monotonicity), the joint budget-strong-induction
`sound_upto` (the 2026-07-02 `search_f` repair), and the consumer faces `Pf_sound`,
`proofSearch_sound`, `box_provable`.

**Pf-only (Phase 2, 2026-07-14).** The former `Derivation.sound` — a separate structural
induction over the `Type`-valued half of `S` — is GONE as a standalone theorem: its arms
(searchBranch / simStep / bot*Step / iteBranchSearch_t / eqRefl / eqNeg, and the
modusPonens/hypSyll function-application arms) are now arms of `sound_upto`'s single `Pf`
induction. The old `pStruct` hop (which reached through the `struct` glue into a SECOND
induction) has no counterpart — that is the merge paying off. `atom_monotone`/`Pf_mono` moved
to the core (`Derivation.lean`); they are re-exported below for callers.

The raw `Pf.rec` is used HERE deliberately (not `Pf.induct`): soundness is the one place where
the certificate half and the reasoning half must be proved in the SAME induction, since
`Pf.atom` consumes a `PlaysProof` and `PlaysProof.search_t` consumes a `Pf`. Every other
consumer should use the named eliminators.
-/

open Classical

open PD
namespace PD.BaseTheorems

/-! ## Transcript facts and the source-transparency faces

`Derivation.concl_size_le` (a transcript contains its conclusion) is now definitional: every
`Pf` leaf's side-condition IS `conclusion.size ≤ k`, and the combining rules add their premises
on top. The old `K_provable` (lift `modusPonens` to the budgeted level) is likewise subsumed —
`Pf.mp` IS the budgeted rule. -/

/-- S can read source code: if an agent `me` is literally `.search g ψ (.const a) (.const b)`,
    then S proves `□_g ψ' → me plays a against opponent` (`ψ' = ψ.subst me opponent`).
    Was an axiom; now witnessed by the `Pf.searchBranch` constructor. -/
theorem proof_system_verifies_search_branch :
    ∀ (g : Nat) (ψ : Formula) (a b : Action) (me opponent : Prog),
      me = .search g ψ (.const a) (.const b) →
      ∃ m, proofSearch m
        (.impl (.box g (ψ.subst me opponent)) (.plays me opponent a)) = true :=
  fun g ψ a b me opponent hme =>
    ⟨_, (proofSearch_spec _ _).2 (Pf.searchBranch g ψ a b me opponent hme (Nat.le_refl _))⟩

/-- S can read `.sim` nodes: if `me = .sim p q`, then S proves
    `(p' plays a vs q') → (me plays a vs opponent)`. Witnessed by `Pf.simStep`. -/
theorem proof_system_verifies_sim :
    ∀ (me p q opponent : Prog) (a : Action),
      me = .sim p q →
      ∃ m, proofSearch m
        (.impl (.plays (p.subst me opponent) (q.subst me opponent) a)
               (.plays me opponent a)) = true :=
  fun me p q opponent a hme =>
    ⟨_, (proofSearch_spec _ _).2 (Pf.simStep me p q opponent a hme (Nat.le_refl _))⟩


/-! ## Atom certificate soundness (`PlaysProof` → real play)

The atom-side axioms `atom_monotone` and `AtomProvable_sound` are now THEOREMS:
`AtomProvable` is the constructive `PlaysProof` certificate, so monotonicity is
just relaxing its cost bound, and soundness is "a certificate yields a real
play." (Only `atom_complete`'s false-guard *completeness* stays axiomatic — see
`Axioms.lean`.) -/

/-- Fuel monotonicity of `eval`: a successful run survives more fuel. Standard;
    by strong induction on the fuel, generalized over all of `me`/`opp`/`body`
    (the `.sim` case swaps players). -/
theorem eval_mono :
    ∀ (N : Nat) (me opponent body : Prog) (a : Action),
      eval N me opponent body = some a → eval (N+1) me opponent body = some a := by
  intro N
  induction N with
  | zero => intro me opponent body a h; simp [eval] at h
  | succ n ih =>
    intro me opponent body a h
    cases body with
    | const c => simpa [eval] using h
    | self => rw [eval] at h ⊢; exact ih _ _ _ _ h
    | opp => rw [eval] at h ⊢; exact ih _ _ _ _ h
    | bot p => rw [eval] at h ⊢; exact ih _ _ _ _ h
    | sim p q => rw [eval] at h ⊢; exact ih _ _ _ _ h
    | ite b a' p q =>
        rw [eval] at h ⊢
        cases hb : eval n me opponent b with
        | none => simp [hb] at h
        | some r =>
            rw [hb] at h; rw [ih me opponent b r hb]
            simp only [bind, Option.bind] at h ⊢
            by_cases hr : (r == a') = true
            · rw [if_pos hr] at h ⊢; exact ih _ _ _ _ h
            · rw [if_neg hr] at h ⊢; exact ih _ _ _ _ h
    | search k φ p q =>
        rw [eval] at h ⊢
        by_cases hg : proofSearch k (φ.subst me opponent) = true
        · rw [if_pos hg] at h ⊢; exact ih _ _ _ _ h
        · rw [if_neg hg] at h ⊢; exact ih _ _ _ _ h

/-- `≤`-form of fuel monotonicity. -/
theorem eval_mono_le {me opponent body : Prog} {a : Action} {N : Nat}
    (h : eval N me opponent body = some a) : ∀ M, N ≤ M → eval M me opponent body = some a := by
  intro M hM
  induction hM with
  | refl => exact h
  | step _ ih => exact eval_mono _ _ _ _ _ ih

/-! ### Budget monotonicity — now in the core (`Derivation.lean`)

`atom_monotone` and `Pf_mono` are constructors-level facts (every rule's side-condition is
`… ≤ k` with `k` the output budget, so each re-applies with the bound relaxed) and moved to
`Derivation.lean` with the type. Re-exported here under the names callers use. -/

export PD (atom_monotone Pf_mono)

/-! ## Joint soundness by STRONG INDUCTION ON THE BUDGET (the `search_f` repair, 2026-07-02).

With the sound false-guard rule `search_f`, soundness cannot be a plain structural induction:
its arm must rule out a HYPOTHETICAL guard proof `Pf k guard` that is not a sub-derivation. The
budget floor in `search_f`'s cost (it pays the full failed budget `k`) is exactly what repairs
this: the hypothetical proof has transcript ≤ k, STRICTLY below the certificate's own cost, so a
strong induction on the budget/cost supplies its soundness. Within one budget `B`, certificates
come first (their `atomNeg`-style premises are smaller-cost certificates), then `Pf` (its `atom`
entry consumes the certificate half at the same `B`). The public `playsProof_sound` /
`AtomProvable_sound` / `Pf_sound` keep their statements as corollaries.

**Pf-only**: the second half now carries the ex-`Derivation` soundness arms directly
(searchBranch/simStep/bot*Step/iteBranchSearch_t/eqRefl/eqNeg + the mp/implTrans
function-application arms) — the old `struct` arm, which recursed into a separate
`Derivation.sound` induction, is gone. The raw `Pf.rec` is deliberate here: this is the one
proof where both motives must ride together (`Pf.atom` consumes a certificate; `search_t`
consumes a `Pf`). Everywhere else, use `Pf.induct`. -/

set_option maxHeartbeats 1000000 in
theorem sound_upto : ∀ B : Nat,
    (∀ me opponent body a n, PlaysProof me opponent body a n → n ≤ B →
      ∃ N, eval N me opponent body = some a)
    ∧ (∀ k φ, Pf k φ → k ≤ B → φ.interp) := by
  intro B
  induction B using Nat.strong_induction_on with
  | _ B IH =>
    have hplays : ∀ me opponent body a n, PlaysProof me opponent body a n → n ≤ B →
        ∃ N, eval N me opponent body = some a := by
      intro me opponent body a n h
      refine PlaysProof.rec
        (motive_1 := fun me opponent body a n _ =>
          n ≤ B → ∃ N, eval N me opponent body = some a)
        (motive_2 := fun _ _ _ => True)
        (motive_3 := fun _ _ _ => True)
        ?const ?self ?opp ?bot ?sim ?ite_t ?ite_f ?search_t ?search_f ?atomMk
        ?pfAtom ?pfSearchBranch ?pfSimStep ?pfBotSimStep ?pfBotSearchStep ?pfIteBranchSearch
        ?pfEqRefl ?pfEqNeg ?pfMp ?pfImplTrans ?pfWeaken ?pfSTS ?pfAtomBoxImpl ?pfBoxIntro
        ?pfAxK ?pfBox4 ?pfDiagF ?pfDiagB ?pfAxKf ?pfImpS2 ?pfBoxMono ?pfAtomNeg h
      case const => exact fun _ => ⟨1, rfl⟩
      case self =>
        intro me opponent a n _ ih hB
        obtain ⟨N, hN⟩ := ih (by omega)
        exact ⟨N+1, by rw [eval]; exact hN⟩
      case opp =>
        intro me opponent a n _ ih hB
        obtain ⟨N, hN⟩ := ih (by omega)
        exact ⟨N+1, by rw [eval]; exact hN⟩
      case bot =>
        intro me opponent p a n _ ih hB
        obtain ⟨N, hN⟩ := ih (by omega)
        exact ⟨N+1, by rw [eval]; exact hN⟩
      case sim =>
        intro a n me opponent p q _ ih hB
        obtain ⟨N, hN⟩ := ih (by omega)
        exact ⟨N+1, by rw [eval]; exact hN⟩
      case ite_t =>
        intro me opponent b r m a' p a n q _ hr _ ihb ihp hB
        obtain ⟨Nb, hNb⟩ := ihb (by omega)
        obtain ⟨Np, hNp⟩ := ihp (by omega)
        refine ⟨max Nb Np + 1, ?_⟩
        rw [eval, eval_mono_le hNb _ (Nat.le_max_left Nb Np)]
        simp only [bind, Option.bind]; rw [if_pos hr]
        exact eval_mono_le hNp _ (Nat.le_max_right Nb Np)
      case ite_f =>
        intro me opponent b r m a' q a n p _ hr _ ihb ihq hB
        obtain ⟨Nb, hNb⟩ := ihb (by omega)
        obtain ⟨Nq, hNq⟩ := ihq (by omega)
        refine ⟨max Nb Nq + 1, ?_⟩
        rw [eval, eval_mono_le hNb _ (Nat.le_max_left Nb Nq)]
        simp only [bind, Option.bind]; rw [if_neg (by simp [hr])]
        exact eval_mono_le hNq _ (Nat.le_max_right Nb Nq)
      case search_t =>
        intro k me opponent p a n φ q hguard _ _ ihp hB
        obtain ⟨Np, hNp⟩ := ihp (by omega)
        exact ⟨Np+1, by
          rw [eval, if_pos ((proofSearch_spec k (φ.subst me opponent)).2 hguard)]
          exact hNp⟩
      case search_f =>
        intro m me opponent q a n k φ p hneg _ _ ihq hB
        have hcn : c_node = 1 := rfl
        -- the refutation's interp, via the strong IH strictly below B
        have hnegI : ¬ (φ.subst me opponent).interp :=
          (IH m (by omega)).2 m (.neg (φ.subst me opponent)) hneg le_rfl
        -- the guard is unprovable at its own budget k (< the certificate's cost — the FLOOR)
        have hps : proofSearch k (φ.subst me opponent) = false := by
          cases hcase : proofSearch k (φ.subst me opponent) with
          | false => rfl
          | true =>
              exact absurd
                ((IH k (by omega)).2 k _ ((proofSearch_spec _ _).1 hcase) le_rfl) hnegI
        obtain ⟨N, hN⟩ := ihq (by omega)
        exact ⟨N+1, by rw [eval, if_neg (by simp [hps])]; exact hN⟩
      -- the `Pf` half's motive is `True` in THIS recursor (it is proved in `hprov` below)
      all_goals (intros; trivial)
    have hprov : ∀ k φ, Pf k φ → k ≤ B → φ.interp := by
      intro k φ h
      refine Pf.rec
        (motive_1 := fun _ _ _ _ _ _ => True)
        (motive_2 := fun k φ _ => k ≤ B → φ.interp)
        (motive_3 := fun k φ _ => k ≤ B → φ.interp)
        ?pConst ?pSelf ?pOpp ?pBot ?pSim ?pIte_t ?pIte_f ?pSearch_t ?pSearch_f ?pAtomMk
        ?pAtom ?pSearchBranch ?pSimStep ?pBotSimStep ?pBotSearchStep ?pIteBranchSearch
        ?pEqRefl ?pEqNeg ?pMp ?pImplTrans ?pWeaken ?pSTS ?pAtomBoxImpl ?pBoxIntro
        ?pAxK ?pBox4 ?pDiagF ?pDiagB ?pAxKf ?pImpS2 ?pBoxMono ?pAtomNeg h
      -- the certificate half's motive is `True` in THIS recursor (proved in `hplays` above)
      case pConst => intros; trivial
      case pSelf => intros; trivial
      case pOpp => intros; trivial
      case pBot => intros; trivial
      case pSim => intros; trivial
      case pIte_t => intros; trivial
      case pIte_f => intros; trivial
      case pSearch_t => intros; trivial
      case pSearch_f => intros; trivial
      case pAtomMk =>
        -- a budgeted certificate yields the real play, via the certificate half at this B
        intro me opponent a n k cert hle _ih _hB
        exact hplays me opponent me a n cert (by omega)
      case pAtom =>
        intro k0 φ0 _hatom ih hB
        exact ih hB
      -- ── the ex-`Derivation` soundness arms (formerly a SECOND induction, `Derivation.sound`) ──
      case pSearchBranch =>
        -- `me` is a `.search` node; a provable guard makes `eval` take the `.const a` branch.
        intro k0 g ψ a b me opponent hme _hle _hB
        subst hme
        intro hguard
        have hps : proofSearch g (ψ.subst (.search g ψ (.const a) (.const b)) opponent) = true :=
          (proofSearch_spec _ _).2 hguard
        exact ⟨2, by simp only [play, eval, hps, if_true]⟩
      case pSimStep =>
        -- `.sim` eval rule: `me` plays `a` iff its closed body does.
        intro k0 me p q opponent a hme _hle _hB
        subst hme
        rintro ⟨n, hn⟩
        exact ⟨n + 1, by show eval (n+1) (.sim p q) opponent (.sim p q) = some a
                         simp only [eval]; exact hn⟩
      case pBotSimStep =>
        -- `.bot` unwrap (one step, `me` stays the player), then the `.sim`.
        intro k0 me p q opponent a hme _hle _hB
        subst hme
        rintro ⟨n, hn⟩
        exact ⟨n + 2, by
          show eval (n+2) (.bot (.sim p q)) opponent (.bot (.sim p q)) = some a
          simp only [eval]; exact hn⟩
      case pBotSearchStep =>
        -- `.bot` unwrap, then the `.search`; a provable guard lands on `.const a`.
        intro k0 g ψ a b me opponent hme _hle _hB
        subst hme
        intro hguard
        have hps : proofSearch g
            (ψ.subst (.bot (.search g ψ (.const a) (.const b))) opponent) = true :=
          (proofSearch_spec _ _).2 hguard
        exact ⟨3, by simp only [play, eval, hps, if_true]⟩
      case pIteBranchSearch =>
        -- `me = .ite (.sim .opp (.bot z)) a' (.search g ψ (.const c0) (.const c1)) q`.
        -- The guard `.sim .opp (.bot z)` is frame-independent (it is `opponent` vs `.bot z`);
        -- once it fires, the inner `.search` runs IN-FRAME and consults
        -- `proofSearch g (ψ.subst me opponent)`, which the box premise reflects to `true`.
        intro k0 g z a' c0 c1 ψ q me opponent hme _hle _hB
        subst hme
        rintro ⟨nb, hb⟩ hbox
        have hps : proofSearch g (ψ.subst
            (.ite (.sim .opp (.bot z)) a' (.search g ψ (.const c0) (.const c1)) q)
            opponent) = true := (proofSearch_spec _ _).2 hbox
        -- `nb ≥ 1`: a fuel-`0` play is `none ≠ some a'`.
        obtain ⟨m, rfl⟩ : ∃ m, nb = m + 1 := by
          cases nb with
          | zero => simp [play, eval] at hb
          | succ m => exact ⟨m, rfl⟩
        have hguard : eval (m + 1) opponent (.bot z) opponent = some a' := hb
        have hrefl : (a' == a') = true := by cases a' <;> rfl
        refine ⟨m + 1 + 1 + 1, ?_⟩
        show eval (m + 1 + 1 + 1) _ opponent _ = some c0
        rw [eval]
        simp only [bind, Option.bind]
        rw [show eval (m + 1 + 1) ((Prog.opp.sim z.bot).ite a'
                (.search g ψ (.const c0) (.const c1)) q) opponent (.sim .opp (.bot z))
              = eval (m + 1) opponent (.bot z) opponent from rfl, hguard]
        simp only [hrefl, hps, if_pos, eval]
      case pEqRefl =>
        -- `.eq p p` interprets as `p = p`.
        intro k0 p _hle _hB
        rfl
      case pEqNeg =>
        -- `.neg (.eq p q)` interprets as `¬(p = q)` — the syntactic distinctness.
        intro k0 p q hne _hle _hB
        exact hne
      -- ── logical core: `.impl`'s interp is Lean implication, so these are applications ──
      case pMp =>
        intro k0 m₁ m₂ A B0 _himp _hante hle ihimp ihante hB
        exact ihimp (by omega) (ihante (by omega))
      case pImplTrans =>
        intro k0 A B0 C a b _hab _hbc hle ihab ihbc hB
        exact fun h => ihbc (by omega) (ihab (by omega) h)
      case pWeaken =>
        intro k0 A B0 m0 _hψ hle ih hB
        exact fun _ => ih (by omega)
      case pSTS =>
        intro k0 k₁ k₂ m0 ψ₁ ψ₂ c0 c1 q me opponent hme hprud hmk _hle _ih _hB
        subst hme
        intro hbox
        have hps₁ : proofSearch k₁ (ψ₁.subst
            (.search k₁ ψ₁ (.search k₂ ψ₂ (.const c0) (.const c1)) q) opponent) = true :=
          (proofSearch_spec _ _).2 hbox
        have hps₂ : proofSearch k₂ (ψ₂.subst
            (.search k₁ ψ₁ (.search k₂ ψ₂ (.const c0) (.const c1)) q) opponent) = true :=
          (proofSearch_spec _ _).2 (Pf_mono hprud hmk)
        exact ⟨3, by simp only [play, eval, hps₁, hps₂, if_true]⟩
      -- ── modal / HBL tier ──
      case pAtomBoxImpl =>
        intro k0 kBox p q a hatom _hle _ih _hB
        exact fun _ => Pf.atom hatom
      case pBoxIntro =>
        intro kIn K0 A hprem _hle _ih _hB
        exact hprem
      case pAxK =>
        intro a b c m0 K0 A B0 _hprem hgate hle ih hB
        exact fun hφ => Pf.mp a b A B0 (ih (by omega)) hφ hgate
      case pBox4 =>
        intro a b K0 A hgate _hle _hB
        exact fun hφ => Pf.boxIntro a b A hφ hgate
      case pDiagF =>
        intro pm fb g K0 tgt _hgate _hle _ih _hB
        exact fun h => h
      case pDiagB =>
        intro pm fb g K0 tgt _hgate _hle _ih _hB
        exact fun h => h
      case pAxKf =>
        intro a b c K0 A B0 hgate _hle _hB
        exact fun hab ha => Pf.mp a b A B0 hab ha hgate
      case pImpS2 =>
        intro A B0 C m₁ m₂ K0 _h1 _h2 hle ih1 ih2 hB
        exact fun hφ => (ih1 (by omega) hφ) (ih2 (by omega) hφ)
      case pBoxMono =>
        intro a b K0 A hab _hle _hB
        exact fun hpa => Pf_mono hpa hab
      case pAtomNeg =>
        -- a certificate of the ACTUAL play refutes any other action, by eval determinism
        intro k0 p q b aN m0 hatom hne hle _ih hB hEx
        obtain ⟨n', hn'⟩ := hEx
        obtain ⟨cert, hcle⟩ := hatom
        have hszpos : 1 ≤ (Formula.neg (.plays p q aN)).size := by
          simp only [Formula.size]; omega
        obtain ⟨N, hN⟩ := hplays p q p b _ cert (by omega)
        have h1 : eval (max N n') p q p = some b := eval_mono_le hN _ (Nat.le_max_left _ _)
        have h2 : eval (max N n') p q p = some aN :=
          eval_mono_le (show eval n' p q p = some aN from hn') _ (Nat.le_max_right _ _)
        rw [h1] at h2
        injection h2 with h3
        exact hne h3
    exact ⟨hplays, hprov⟩

/-- **Soundness of the play certificate.** A `PlaysProof` yields an actual play (at some
    fuel). Corollary of `sound_upto` at `B := n`. -/
theorem playsProof_sound {me opponent body a n} (h : PlaysProof me opponent body a n) :
    ∃ N, eval N me opponent body = some a :=
  (sound_upto n).1 me opponent body a n h le_rfl

/-- **`AtomProvable_sound` (was an axiom).** A bounded certificate yields a real
    play, hence the atom's `interp` (`∃ n, play n me opponent = some a`). -/
theorem AtomProvable_sound (k : Nat) (φ : Formula) : AtomProvable k φ → φ.interp := by
  rintro ⟨cert, hle⟩
  obtain ⟨N, hN⟩ := playsProof_sound cert
  exact ⟨N, hN⟩

/-- **Soundness of bounded provability: anything provable within a budget is true.**
    Corollary of `sound_upto` at `B := k` (which see for the budget-strong-induction
    structure the `search_f` repair requires). -/
theorem Pf_sound : ∀ k φ, Pf k φ → φ.interp :=
  fun k φ h => (sound_upto k).2 k φ h le_rfl

/-
HOW TO DISCHARGE A `proofSearch k φ = b` GOAL.

The two boolean directions are proved by *opposite* bridges — this asymmetry is
fundamental (Σ₁ vs Π₁), not a stylistic choice:

• `proofSearch k φ = true`  — COMPLETENESS / Σ₁ side. Exhibit a witness.
    For a plays-atom `φ = .plays p q a`: produce a real `play n p q = some a`,
    feed it to `atom_complete` (→ `AtomProvable (atom_cost n) φ`), then flip with
    `(proofSearch_spec _ _).2 (Pf.atom …)`. `proofSearch_complete_plays`
    below packages exactly this. For a structural `φ` (e.g. `.eq p p`), build the
    `Derivation` and use `Pf.struct-GONE`. You are *constructing* a proof object.

• `proofSearch k φ = false` — SOUNDNESS side, by refutation. You CANNOT exhibit
    "a proof that no proof exists" (that is Π₁); instead rule out `true` via its
    semantic consequence. Canonical pattern:
      cases h : proofSearch k φ with
      | true  => exact absurd (proofSearch_sound _ _ h) (interp_…_false …)
      | false => rfl
    i.e. if it were `true`, `proofSearch_sound` would force `φ.interp` (the bot
    would actually play that), which a computed fact (`interp_…_false`) refutes.

Mnemonic: `= true` builds a proof (atom_complete / Derivation); `= false`
destroys a hypothetical one (proofSearch_sound + contradiction). The single place
these collide is `atom_complete`'s false-guard branch — see `atom_complete_false_guard`
in Axioms.lean.
-/

-- Soundness of the proof-search oracle: the `Bool` reflection of `Pf_sound`.
theorem proofSearch_sound :
  ∀ k φ, proofSearch k φ = true → φ.interp :=
  fun k φ hk => Pf_sound k φ ((proofSearch_spec k φ).1 hk)

/-- Completeness of bounded proof search for SEARCH-FREE plays-atoms (the constructive
    fragment; the unrestricted form fell with the inconsistent axiom — a failed-search
    else-play is provable only above its floor, an anti-diagonal one not at all). -/
theorem proofSearch_complete_plays :
    ∀ p q a, p.hasSearch = false → q.hasSearch = false →
      (∃ n, play n p q = some a) → ∃ k, proofSearch k (.plays p q a) = true := by
  intro p q a hp hq ⟨n, hn⟩
  exact ⟨3 ^ n, (proofSearch_spec _ (.plays p q a)).2
    (Pf.atom (atom_complete_searchfree p q a n hp hq hn))⟩

-- Monotonicity in proof-search budget: the Bool reflection of `Pf_mono`
-- (which see — every rule self-weakens in its output budget under transcript cost).
theorem proofSearch_monotone :
    ∀ k₁ k₂ φ, k₁ ≤ k₂ → proofSearch k₁ φ = true → proofSearch k₂ φ = true :=
  fun _k₁ _k₂ φ hk h1 =>
    (proofSearch_spec _ φ).2 (Pf_mono ((proofSearch_spec _ φ).1 h1) hk)


/-- **Bounded GL axiom 4 / necessitation** (`□_k φ → □_K □_k φ`), HBL D2 — NOW A THEOREM
    (was the axiom `box_provable`). If `φ` is provable within budget `k`, then that fact
    `□_k φ` is itself provable, at the output budget `K = (.box k φ).size` (≤ that bound).
    Discharged constructively by the `Pf.boxIntro` constructor (Derivation.lean): the
    conclusion `□_k φ` is built directly from the premise `Pf k φ`, with the size bound
    `(.box k φ).size ≤ K` met by `Nat.le_refl`. Sound + safe — see the `boxIntro` doc. -/
theorem box_provable (k : Nat) (φ : Formula) (h : Pf k φ) :
    ∃ K, K ≤ k + (Formula.box k φ).size ∧ Pf K (.box k φ) :=
  ⟨k + (Formula.box k φ).size, Nat.le_refl _, Pf.boxIntro k _ φ h (Nat.le_refl _)⟩

/-- **Object-level bounded Σ₁-completeness for play-atoms** (the conditional, kernel-checked
    THEOREM). When the play actually happens within `fuel` steps AND the budget `k` fits a
    certificate (`atom_cost fuel ≤ k`), the object implication `(p plays a vs q) → □_k (p plays a vs q)`
    is provable at `K`. Built from the certificate (→ `Pf k atom`),
    `boxIntro` (→ the box), and `weakenImpl` (→ the implication). The CERTIFICATE premise
    keeps it on the sound Σ₁ side: bounded Σ₁-completeness, NOT the GL-excluded
    converse-necessitation `φ → □φ`. (Historical note: the witness-free form was once the
    axiom `atom_box_provable_impl`, removed as unsound; this conditional theorem and the
    `atomBoxImpl` constructor are its sound content.) -/
theorem atom_box_provable_impl_sound (k K : Nat) (p q : Prog) (a : Action)
    (hatom : AtomProvable k (.plays p q a))
    (hK : k + (Formula.box k (.plays p q a)).size
          + (Formula.impl (.plays p q a) (.box k (.plays p q a))).size ≤ K) :
    Pf K (.impl (.plays p q a) (.box k (.plays p q a))) := by
  -- Under transcript cost the conclusion can no longer live at the box's own budget `k`
  -- (the implication's proof CONTAINS the box proof, which contains the `k`-certificate);
  -- the output budget `K` pays certificate + box + conclusion.
  have hbox : Pf (k + (Formula.box k (.plays p q a)).size) (.box k (.plays p q a)) :=
    Pf.boxIntro k _ _ (Pf.atom hatom) (Nat.le_refl _)
  exact Pf.weakenImpl (.plays p q a) (.box k (.plays p q a)) _ hbox hK

end PD.BaseTheorems
