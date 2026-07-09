import PrisonersDilemma.Base.AtomCerts

/-!
# Base/Soundness — every provable formula is true

The soundness spine: `Derivation.sound` (structural rules), `eval_mono` /
`atom_monotone` / `Provable_mono` (budget monotonicity), the joint
budget-strong-induction `sound_upto` (the 2026-07-02 `search_f` repair), and the
consumer faces `Provable_sound`, `proofSearch_sound`, `box_provable`.
-/

open Classical

open PD
namespace PD.BaseTheorems

-- Soundness of the structural rules. Each `Derivation` yields a true
-- formula. The interesting cases (`searchBranch`, `simStep`) are exactly the
-- semantic content the old transparency axioms asserted for free.
--
-- Declared as `_root_.PD.Derivation.sound` (absolute name) so it lands in
-- the `PD.Derivation` namespace and dot notation `d.sound` on a
-- `d : PD.Derivation φ` resolves it — rather than being prefixed by the
-- ambient `PD.BaseTheorems` namespace.
theorem _root_.PD.Derivation.sound : ∀ {φ}, Derivation φ → φ.interp := by
  intro φ d
  induction d with
  | modusPonens φ ψ _ _ ih1 ih2 =>
      -- `.impl`'s interp is Lean implication, so this is just function application.
      exact ih1 ih2
  | searchBranch k ψ a b me opponent hme =>
      -- `me` is a `.search` node; a provable guard makes `eval` take the
      -- `.const a` branch, so `me` plays `a` against `opponent`.
      subst hme
      intro hguard
      have hps : proofSearch k (ψ.subst (.search k ψ (.const a) (.const b)) opponent) = true :=
        (proofSearch_spec _ _).2 hguard
      exact ⟨2, by simp only [play, eval, hps, if_true]⟩
  | simStep me p q opponent a hme =>
      -- `me` is a `.sim` node; by the `.sim` eval rule, `me` plays `a` iff its
      -- closed body `p'` plays `a` against `q'`.
      subst hme
      intro h
      obtain ⟨n, hn⟩ := h
      exact ⟨n + 1, by show eval (n+1) (.sim p q) opponent (.sim p q) = some a
                       simp only [eval]; exact hn⟩
  | botSimStep me p q opponent a hme =>
      -- `me = .bot (.sim p q)`: `eval` unwraps the `.bot` (one step, `me` stays the
      -- player), then runs the `.sim`. So `me` plays `a` iff its substituted body
      -- plays `a`. Witness fuel `n + 2`: one `.bot` unwrap, one `.sim` step.
      subst hme
      intro h
      obtain ⟨n, hn⟩ := h
      exact ⟨n + 2, by
        show eval (n+2) (.bot (.sim p q)) opponent (.bot (.sim p q)) = some a
        simp only [eval]; exact hn⟩
  | botSearchStep k ψ a b me opponent hme =>
      -- `me = .bot (.search k ψ (.const a) (.const b))`: `eval` unwraps the `.bot`
      -- (one step, `me` stays the player), then runs the `.search`. A provable
      -- guard makes `eval` take the `.const a` branch, so `me` plays `a`. Witness
      -- fuel `3`: one `.bot` unwrap, one `.search` step, one `.const a` step.
      subst hme
      intro hguard
      have hps : proofSearch k
          (ψ.subst (.bot (.search k ψ (.const a) (.const b))) opponent) = true :=
        (proofSearch_spec _ _).2 hguard
      exact ⟨3, by simp only [play, eval, hps, if_true]⟩
  | hypSyll φ ψ χ _ _ ih1 ih2 =>
      exact fun h => ih2 (ih1 h)
  | iteBranchSearch_t k z a' c0 c1 ψ q me opponent hme =>
      -- `me = .ite (.sim .opp (.bot z)) a' (.search k ψ (.const c0) (.const c1)) q`.
      -- Guard `.sim .opp (.bot z)` is frame-independent: it equals `opponent` vs
      -- `.bot z` (`eval_sim_opp_bot_of_play`). Once the guard fires (`hb` gives it
      -- plays `a'`, so `a' == a'` selects the then-branch), the inner `.search`
      -- runs in-frame and consults `proofSearch k (ψ.subst me opponent)`, which the
      -- box premise reflects to `true` (`proofSearch_spec`), landing on `.const c0`.
      subst hme
      rintro ⟨nb, hb⟩ hbox
      have hps : proofSearch k (ψ.subst
          (.ite (.sim .opp (.bot z)) a' (.search k ψ (.const c0) (.const c1)) q)
          opponent) = true := (proofSearch_spec _ _).2 hbox
      -- `nb ≥ 1`: a fuel-`0` play is `none ≠ some a'`, so write `nb = m + 1`. The
      -- extra step lets the inner `.search`'s `.const c0` branch evaluate.
      obtain ⟨m, rfl⟩ : ∃ m, nb = m + 1 := by
        cases nb with
        | zero => simp [play, eval] at hb
        | succ m => exact ⟨m, rfl⟩
      -- `.sim .opp (.bot z)` guard reduces (one fuel step; `subst` sends `.opp`↦
      -- opponent, leaves `.bot z` closed) to `eval (m+1) opponent z.bot opponent`,
      -- which is `play (m+1) opponent z.bot = some a'` (`hb`), frame-independent of
      -- `me`. Same reduction `eval_sim_opp_bot_of_play` performs, inlined since
      -- that helper lives downstream of this file.
      have hguard : eval (m + 1) opponent (.bot z) opponent = some a' := hb
      have hrefl : (a' == a') = true := by cases a' <;> rfl
      -- Witness fuel `m + 3`: `.ite` step (→ m+2) evaluates the guard `.sim`
      -- (→ m+1, matching `hguard`); the then-branch `.search` and its `.const c0`
      -- run at `m+1 ≥ 1`.
      refine ⟨m + 1 + 1 + 1, ?_⟩
      show eval (m + 1 + 1 + 1) _ opponent _ = some c0
      -- `.ite` step then `.sim` guard step, exposing `hguard`'s LHS exactly.
      rw [eval]
      simp only [bind, Option.bind]
      rw [show eval (m + 1 + 1) ((Prog.opp.sim z.bot).ite a'
              (.search k ψ (.const c0) (.const c1)) q) opponent (.sim .opp (.bot z))
            = eval (m + 1) opponent (.bot z) opponent from rfl, hguard]
      -- guard fired; `a' == a'` (`hrefl`) selects the `.search`, `hps` makes it
      -- take `.const c0`.
      simp only [hrefl, hps, if_pos, eval]
  | eqRefl p =>
      -- `.eq p p` interprets as `p = p`, which is `rfl`.
      rfl
  | eqNeg p q hne =>
      -- `.neg (.eq p q)` interprets as `¬(p = q)` — exactly the syntactic distinctness.
      exact hne

/-- A derivation of size `m` witnesses `proofSearch m φ = true` (structural
    disjunct of `Provable`). -/
theorem derives {φ : Formula} (d : Derivation φ) : ∃ m, proofSearch m φ = true :=
  ⟨d.size, (proofSearch_spec _ _).2 (Provable.struct ⟨d, Nat.le_refl _⟩)⟩

/-- Every derivation's transcript contains (at least) its conclusion. Base fact of the
    transcript cost model: leaves cost exactly their conclusion; the combining rules pay
    their subtrees ON TOP of the conclusion. -/
theorem _root_.PD.Derivation.concl_size_le : ∀ {φ : Formula} (d : Derivation φ), φ.size ≤ d.size := by
  intro φ d
  cases d with
  | modusPonens φ ψ d1 d2 => simp only [Derivation.size]; omega
  | hypSyll φ ψ χ d1 d2 => simp only [Derivation.size]; omega
  | _ => simp only [Derivation.size]; exact Nat.le_refl _

/-- The **K axiom** of GL, budget-respecting: from a derivation of `φ → ψ` of transcript
    `≤ n` and one of `φ` of transcript `≤ m`, `ψ` is provable within `n + m + n` (the
    combined transcript pays both subtrees plus the conclusion `ψ`, and
    `ψ.size < (φ → ψ).size ≤ n` via `concl_size_le`). Lifts the `modusPonens`
    constructor to the budgeted `Provable` level. -/
theorem K_provable (n m : Nat) (φ ψ : Formula)
    (dImp : Derivation (.impl φ ψ)) (hI : dImp.size ≤ n)
    (dφ : Derivation φ) (hF : dφ.size ≤ m) :
    Provable (n + m + n) ψ := by
  have hψ : ψ.size ≤ n := by
    have h := dImp.concl_size_le
    simp only [Formula.size] at h
    omega
  exact Provable.struct ⟨.modusPonens φ ψ dImp dφ, by
    simp only [Derivation.size]; omega⟩

/--
S can read source code: if an agent `me` is literally
`.search k ψ (.const a) (.const b)`, then S proves
`□_k ψ' → me plays a against opponent`, where `ψ' = ψ.subst me opponent`.

Was an axiom; now a theorem, witnessed by `Derivation.searchBranch`.
-/
theorem proof_system_verifies_search_branch :
    ∀ (k : Nat) (ψ : Formula) (a b : Action) (me opponent : Prog),
      me = .search k ψ (.const a) (.const b) →
      ∃ m, proofSearch m
        (.impl (.box k (ψ.subst me opponent)) (.plays me opponent a)) = true :=
  fun k ψ a b me opponent hme => derives (.searchBranch k ψ a b me opponent hme)

/--
S can read `.sim` nodes: if `me = .sim p q`, then S proves
`(p' plays a vs q') → (me plays a vs opponent)`.

Was an axiom; now a theorem, witnessed by `Derivation.simStep`.
-/
theorem proof_system_verifies_sim :
    ∀ (me p q opponent : Prog) (a : Action),
      me = .sim p q →
      ∃ m, proofSearch m
        (.impl (.plays (p.subst me opponent) (q.subst me opponent) a)
               (.plays me opponent a)) = true :=
  fun me p q opponent a hme => derives (.simStep me p q opponent a hme)


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

/-- **`atom_monotone` (was an axiom).** Relaxing the certificate's cost bound. -/
theorem atom_monotone (k₁ k₂ : Nat) (φ : Formula) (hk : k₁ ≤ k₂) :
    AtomProvable k₁ φ → AtomProvable k₂ φ := by
  rintro ⟨cert, hle⟩; exact .mk cert (Nat.le_trans hle hk)

/-- **Budget monotonicity of `Provable`** — a ≤k₁-transcript proof is a ≤k₂-transcript proof
    (k₁ ≤ k₂). Genuine and structural under the transcript cost model: EVERY rule's final
    side-condition is `… ≤ k` with `k` the output budget, so each constructor re-applies with
    the bound relaxed — plain `cases`, no recursion. (Replaces the per-rule reasoning that
    `proofSearch_monotone` used to inline; that theorem is now a one-line corollary.) -/
theorem Provable_mono : ∀ {k₁ : Nat} {φ : Formula}, Provable k₁ φ →
    ∀ {k₂ : Nat}, k₁ ≤ k₂ → Provable k₂ φ := by
  intro k₁ φ h k₂ hk
  cases h with
  | struct hd => obtain ⟨d, hsz⟩ := hd; exact .struct ⟨d, Nat.le_trans hsz hk⟩
  | atom hatom => exact .atom (atom_monotone k₁ k₂ φ hk hatom)
  | weakenImpl φ ψ m hψ hle => exact .weakenImpl φ ψ m hψ (Nat.le_trans hle hk)
  | searchThenSearch_t k₁' k₂' m ψ₁ ψ₂ c0 c1 q me opponent hme hprud hmk hle =>
      exact .searchThenSearch_t k₁' k₂' m ψ₁ ψ₂ c0 c1 q me opponent hme hprud hmk
        (Nat.le_trans hle hk)
  | implTrans φ ψ χ a b h1 h2 hle => exact .implTrans φ ψ χ a b h1 h2 (Nat.le_trans hle hk)
  | atomBoxImpl kBox p q a hatom hle => exact .atomBoxImpl kBox p q a hatom (Nat.le_trans hle hk)
  | boxIntro kIn K φ hprem hle => exact .boxIntro kIn k₂ φ hprem (Nat.le_trans hle hk)
  | app =>
      rename_i m₁ m₂ φ' h1 h2 hle
      exact .app k₂ m₁ m₂ φ' _ h2 h1 (Nat.le_trans hle hk)
  | axK a b c m K φ α hprem hgate hle =>
      exact .axK a b c m k₂ φ α hprem hgate (Nat.le_trans hle hk)
  | box4 a b K φ hgate hle => exact .box4 a b k₂ φ hgate (Nat.le_trans hle hk)
  | diagF pm fb g K tgt hgate hle => exact .diagF pm fb g k₂ tgt hgate (Nat.le_trans hle hk)
  | diagB pm fb g K tgt hgate hle => exact .diagB pm fb g k₂ tgt hgate (Nat.le_trans hle hk)
  | axKf a b c K φ α hgate hle => exact .axKf a b c k₂ φ α hgate (Nat.le_trans hle hk)
  | impS2 φ ψ χ m₁ m₂ K h1 h2 hle => exact .impS2 φ ψ χ m₁ m₂ k₂ h1 h2 (Nat.le_trans hle hk)
  | boxMono a b K φ hab hle => exact .boxMono a b k₂ φ hab (Nat.le_trans hle hk)
  | atomNeg p q b aN m hatom hne hle =>
      exact .atomNeg p q b aN m hatom hne (Nat.le_trans hle hk)

/-! ## Joint soundness by STRONG INDUCTION ON THE BUDGET (the `search_f` repair, 2026-07-02).

With the sound false-guard rule `search_f`, soundness can no longer be a plain structural
induction: its arm must rule out a HYPOTHETICAL guard proof `Provable k guard` that is not a
sub-derivation. The budget floor in `search_f`'s cost (it pays the full failed budget `k`) is
exactly what repairs this: the hypothetical proof has transcript ≤ k, STRICTLY below the
certificate's own cost, so a strong induction on the budget/cost supplies its soundness.
Within one budget `B`, certificates come first (their `atomNeg`-style premises are
smaller-cost certificates), then `Provable` (its `atom` entry consumes the certificate half at
the same `B`). The public `playsProof_sound` / `AtomProvable_sound` / `Provable_sound` keep
their statements as corollaries. -/

set_option maxHeartbeats 1000000 in
theorem sound_upto : ∀ B : Nat,
    (∀ me opponent body a n, PlaysProof me opponent body a n → n ≤ B →
      ∃ N, eval N me opponent body = some a)
    ∧ (∀ k φ, Provable k φ → k ≤ B → φ.interp) := by
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
        ?const ?self ?opp ?bot ?sim ?ite_t ?ite_f ?search_t ?search_f ?atomMk ?provStruct
        ?provAtom ?provWeaken ?provSearchThenSearch ?provImplTrans ?provAtomBoxImpl
        ?provBoxIntro ?provApp ?provAxK ?provBox4 ?provDiagF ?provDiagB ?provAxKf ?provImpS2
        ?provBoxMono ?provAtomNeg h
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
      case atomMk => intros; trivial
      case provStruct => intros; trivial
      case provAtom => intros; trivial
      case provWeaken => intros; trivial
      case provSearchThenSearch => intros; trivial
      case provImplTrans => intros; trivial
      case provAtomBoxImpl => intros; trivial
      case provBoxIntro => intros; trivial
      case provApp => intros; trivial
      case provAxK => intros; trivial
      case provBox4 => intros; trivial
      case provDiagF => intros; trivial
      case provDiagB => intros; trivial
      case provAxKf => intros; trivial
      case provImpS2 => intros; trivial
      case provBoxMono => intros; trivial
      case provAtomNeg => intros; trivial
    have hprov : ∀ k φ, Provable k φ → k ≤ B → φ.interp := by
      intro k φ h
      refine Provable.rec
        (motive_1 := fun _ _ _ _ _ _ => True)
        (motive_2 := fun k φ _ => k ≤ B → φ.interp)
        (motive_3 := fun k φ _ => k ≤ B → φ.interp)
        ?pConst ?pSelf ?pOpp ?pBot ?pSim ?pIte_t ?pIte_f ?pSearch_t ?pSearch_f ?pAtomMk
        ?pStruct ?pAtom ?pWeaken ?pSTS ?pImplTrans ?pAtomBoxImpl ?pBoxIntro ?pApp ?pAxK
        ?pBox4 ?pDiagF ?pDiagB ?pAxKf ?pImpS2 ?pBoxMono ?pAtomNeg h
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
      case pStruct =>
        intro φ0 k0 hd _hB
        obtain ⟨d, _⟩ := hd
        exact d.sound
      case pAtom =>
        intro k0 φ0 _hatom ih hB
        exact ih hB
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
          (proofSearch_spec _ _).2 (Provable_mono hprud hmk)
        exact ⟨3, by simp only [play, eval, hps₁, hps₂, if_true]⟩
      case pImplTrans =>
        intro k0 A B0 C a b _hab _hbc hle ihab ihbc hB
        exact fun h => ihbc (by omega) (ihab (by omega) h)
      case pAtomBoxImpl =>
        intro k0 kBox p q a hatom _hle _ih _hB
        exact fun _ => Provable.atom hatom
      case pBoxIntro =>
        intro kIn K0 A hprem _hle _ih _hB
        exact hprem
      case pApp =>
        intro k0 m₁ m₂ A B0 _himp _hante hle ihimp ihante hB
        exact ihimp (by omega) (ihante (by omega))
      case pAxK =>
        intro a b c m0 K0 A B0 _hprem hgate hle ih hB
        exact fun hφ => Provable.app c a b A B0 (ih (by omega)) hφ hgate
      case pBox4 =>
        intro a b K0 A hgate _hle _hB
        exact fun hφ => Provable.boxIntro a b A hφ hgate
      case pDiagF =>
        intro pm fb g K0 tgt _hgate _hle _ih _hB
        exact fun h => h
      case pDiagB =>
        intro pm fb g K0 tgt _hgate _hle _ih _hB
        exact fun h => h
      case pAxKf =>
        intro a b c K0 A B0 hgate _hle _hB
        exact fun hab ha => Provable.app c a b A B0 hab ha hgate
      case pImpS2 =>
        intro A B0 C m₁ m₂ K0 _h1 _h2 hle ih1 ih2 hB
        exact fun hφ => (ih1 (by omega) hφ) (ih2 (by omega) hφ)
      case pBoxMono =>
        intro a b K0 A hab _hle _hB
        exact fun hpa => Provable_mono hpa hab
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
theorem Provable_sound : ∀ k φ, Provable k φ → φ.interp :=
  fun k φ h => (sound_upto k).2 k φ h le_rfl

/-
HOW TO DISCHARGE A `proofSearch k φ = b` GOAL.

The two boolean directions are proved by *opposite* bridges — this asymmetry is
fundamental (Σ₁ vs Π₁), not a stylistic choice:

• `proofSearch k φ = true`  — COMPLETENESS / Σ₁ side. Exhibit a witness.
    For a plays-atom `φ = .plays p q a`: produce a real `play n p q = some a`,
    feed it to `atom_complete` (→ `AtomProvable (atom_cost n) φ`), then flip with
    `(proofSearch_spec _ _).2 (Provable.atom …)`. `proofSearch_complete_plays`
    below packages exactly this. For a structural `φ` (e.g. `.eq p p`), build the
    `Derivation` and use `Provable.struct`. You are *constructing* a proof object.

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

-- Soundness of the proof-search oracle: the `Bool` reflection of `Provable_sound`.
theorem proofSearch_sound :
  ∀ k φ, proofSearch k φ = true → φ.interp :=
  fun k φ hk => Provable_sound k φ ((proofSearch_spec k φ).1 hk)

/-- Completeness of bounded proof search for SEARCH-FREE plays-atoms (the constructive
    fragment; the unrestricted form fell with the inconsistent axiom — a failed-search
    else-play is provable only above its floor, an anti-diagonal one not at all). -/
theorem proofSearch_complete_plays :
    ∀ p q a, p.hasSearch = false → q.hasSearch = false →
      (∃ n, play n p q = some a) → ∃ k, proofSearch k (.plays p q a) = true := by
  intro p q a hp hq ⟨n, hn⟩
  exact ⟨3 ^ n, (proofSearch_spec _ (.plays p q a)).2
    (Provable.atom (atom_complete_searchfree p q a n hp hq hn))⟩

-- Monotonicity in proof-search budget: the Bool reflection of `Provable_mono`
-- (which see — every rule self-weakens in its output budget under transcript cost).
theorem proofSearch_monotone :
    ∀ k₁ k₂ φ, k₁ ≤ k₂ → proofSearch k₁ φ = true → proofSearch k₂ φ = true :=
  fun _k₁ _k₂ φ hk h1 =>
    (proofSearch_spec _ φ).2 (Provable_mono ((proofSearch_spec _ φ).1 h1) hk)


/-- **Bounded GL axiom 4 / necessitation** (`□_k φ → □_K □_k φ`), HBL D2 — NOW A THEOREM
    (was the axiom `box_provable`). If `φ` is provable within budget `k`, then that fact
    `□_k φ` is itself provable, at the output budget `K = (.box k φ).size` (≤ that bound).
    Discharged constructively by the `Provable.boxIntro` constructor (Derivation.lean): the
    conclusion `□_k φ` is built directly from the premise `Provable k φ`, with the size bound
    `(.box k φ).size ≤ K` met by `Nat.le_refl`. Sound + safe — see the `boxIntro` doc. -/
theorem box_provable (k : Nat) (φ : Formula) (h : Provable k φ) :
    ∃ K, K ≤ k + (Formula.box k φ).size ∧ Provable K (.box k φ) :=
  ⟨k + (Formula.box k φ).size, Nat.le_refl _, Provable.boxIntro k _ φ h (Nat.le_refl _)⟩

/-- **Object-level bounded Σ₁-completeness for play-atoms** (the conditional, kernel-checked
    THEOREM). When the play actually happens within `fuel` steps AND the budget `k` fits a
    certificate (`atom_cost fuel ≤ k`), the object implication `(p plays a vs q) → □_k (p plays a vs q)`
    is provable at `K`. Built from the certificate (→ `Provable k atom`),
    `boxIntro` (→ the box), and `weakenImpl` (→ the implication). The CERTIFICATE premise
    keeps it on the sound Σ₁ side: bounded Σ₁-completeness, NOT the GL-excluded
    converse-necessitation `φ → □φ`. (Historical note: the witness-free form was once the
    axiom `atom_box_provable_impl`, removed as unsound; this conditional theorem and the
    `atomBoxImpl` constructor are its sound content.) -/
theorem atom_box_provable_impl_sound (k K : Nat) (p q : Prog) (a : Action)
    (hatom : AtomProvable k (.plays p q a))
    (hK : k + (Formula.box k (.plays p q a)).size
          + (Formula.impl (.plays p q a) (.box k (.plays p q a))).size ≤ K) :
    Provable K (.impl (.plays p q a) (.box k (.plays p q a))) := by
  -- Under transcript cost the conclusion can no longer live at the box's own budget `k`
  -- (the implication's proof CONTAINS the box proof, which contains the `k`-certificate);
  -- the output budget `K` pays certificate + box + conclusion.
  have hbox : Provable (k + (Formula.box k (.plays p q a)).size) (.box k (.plays p q a)) :=
    Provable.boxIntro k _ _ (Provable.atom hatom) (Nat.le_refl _)
  exact Provable.weakenImpl (.plays p q a) (.box k (.plays p q a)) _ hbox hK

end PD.BaseTheorems
