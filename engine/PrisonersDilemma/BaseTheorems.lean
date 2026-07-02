import PrisonersDilemma.Dynamics
import PrisonersDilemma.Axioms
import PrisonersDilemma.SizeLemmas


open Classical

open PD
open PD.Axioms
namespace PD.BaseTheorems

/-- `c_guard` (the cost of writing the budget numeral `k` in a proof transcript)
    is monotone: a larger `k` takes at least as many characters to write.
    Needed for `atom_cost_mono`. Now a *theorem* (was an axiom): with the concrete
    `c_guard k = Nat.log2 k + 1` (Derivation.lean), monotonicity is `Nat.log2`'s. -/
theorem c_guard_mono : ∀ {a b : Nat}, a ≤ b → c_guard a ≤ c_guard b := by
  intro a b h
  simp only [c_guard, Nat.log2_eq_log_two]
  exact Nat.add_le_add_right (Nat.log_mono_right h) 1

/-- `atom_cost` is monotone in fuel, so bot proofs can lift a small-fuel atom to a
    larger working budget via `proofSearch_monotone`. -/
theorem atom_cost_mono {a b : Nat} (h : a ≤ b) : atom_cost a ≤ atom_cost b := by
  unfold atom_cost
  exact Nat.add_le_add_left
    (Nat.mul_le_mul (Nat.add_le_add_left (c_guard_mono h) _) h) _

/-- σ₁-completeness for atoms: every `fuel`-step play has an `AtomProvable`
    certificate at budget `atom_cost fuel`. Constructive when a `PlaysProof`
    exists; falls back to `atom_complete_false_guard` otherwise.
    This means that if p plays a against q within fuel steps,
    then S can prove that fact within the budget -/
theorem atom_complete :
    ∀ p q a fuel, play fuel p q = some a →
      AtomProvable (atom_cost fuel) (.plays p q a) := by
  intro p q a fuel h
  by_cases hc : ∃ _ : PlaysProof p q p a (atom_cost fuel), True
  · obtain ⟨cert, _⟩ := hc; exact .mk cert (Nat.le_refl _)
  · exact atom_complete_false_guard p q a fuel h hc

/-- The bridge `proofSearch ↔ Provable` is now a theorem, not an axiom. -/
theorem proofSearch_spec (k : Nat) (φ : Formula) :
    proofSearch k φ = true ↔ Provable k φ := by
  unfold proofSearch; exact decide_eq_true_iff

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

/-- **Soundness of the play certificate.** A `PlaysProof` yields an actual play
    (at some fuel). Via `PlaysProof.rec` (`induction` can't handle the mutual
    block); `.ite`/`.search` unify the two child fuels with `eval_mono_le` to
    `max … + 1`. The `.search_t` case reflects its `Provable` guard premise into
    the `proofSearch` the evaluator consults, via `(proofSearch_spec).2`. -/
theorem playsProof_sound {me opponent body a n} (h : PlaysProof me opponent body a n) :
    ∃ N, eval N me opponent body = some a := by
  refine PlaysProof.rec
    (motive_1 := fun me opponent body a _ _ => ∃ N, eval N me opponent body = some a)
    (motive_2 := fun _ _ _ => True)
    (motive_3 := fun _ _ _ => True)
    ?const ?self ?opp ?bot ?sim ?ite_t ?ite_f ?search_t ?atomMk ?provStruct ?provAtom ?provWeaken
    ?provSearchThenSearch ?provImplTrans ?provAtomBoxImpl ?provBoxIntro ?provApp ?provAxK ?provBox4
    ?provDiagF ?provDiagB ?provAxKf ?provImpS2 ?provBoxMono h
  case const => exact ⟨1, rfl⟩
  case self => intro me opponent a n _ ih; obtain ⟨N, hN⟩ := ih; exact ⟨N+1, by rw [eval]; exact hN⟩
  case opp => intro me opponent a n _ ih; obtain ⟨N, hN⟩ := ih; exact ⟨N+1, by rw [eval]; exact hN⟩
  case bot => intro me opponent p a n _ ih; obtain ⟨N, hN⟩ := ih; exact ⟨N+1, by rw [eval]; exact hN⟩
  case sim => intro a n me opponent p q _ ih; obtain ⟨N, hN⟩ := ih; exact ⟨N+1, by rw [eval]; exact hN⟩
  case ite_t =>
    intro me opponent b r m a' p a n q _ hr _ ihb ihp
    obtain ⟨Nb, hNb⟩ := ihb; obtain ⟨Np, hNp⟩ := ihp
    refine ⟨max Nb Np + 1, ?_⟩
    rw [eval, eval_mono_le hNb _ (Nat.le_max_left Nb Np)]
    simp only [bind, Option.bind]; rw [if_pos hr]
    exact eval_mono_le hNp _ (Nat.le_max_right Nb Np)
  case ite_f =>
    intro me opponent b r m a' q a n p _ hr _ ihb ihq
    obtain ⟨Nb, hNb⟩ := ihb; obtain ⟨Nq, hNq⟩ := ihq
    refine ⟨max Nb Nq + 1, ?_⟩
    rw [eval, eval_mono_le hNb _ (Nat.le_max_left Nb Nq)]
    simp only [bind, Option.bind]; rw [if_neg (by simp [hr])]
    exact eval_mono_le hNq _ (Nat.le_max_right Nb Nq)
  case search_t =>
    intro k me opponent p a n φ q hguard _ _ ihp
    obtain ⟨Np, hNp⟩ := ihp
    exact ⟨Np+1, by rw [eval, if_pos ((proofSearch_spec k (φ.subst me opponent)).2 hguard)]; exact hNp⟩
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

/-- **`atom_monotone` (was an axiom).** Relaxing the certificate's cost bound. -/
theorem atom_monotone (k₁ k₂ : Nat) (φ : Formula) (hk : k₁ ≤ k₂) :
    AtomProvable k₁ φ → AtomProvable k₂ φ := by
  rintro ⟨cert, hle⟩; exact .mk cert (Nat.le_trans hle hk)

/-- **`AtomProvable_sound` (was an axiom).** A bounded certificate yields a real
    play, hence the atom's `interp` (`∃ n, play n me opponent = some a`). -/
theorem AtomProvable_sound (k : Nat) (φ : Formula) : AtomProvable k φ → φ.interp := by
  rintro ⟨cert, _⟩
  obtain ⟨N, hN⟩ := playsProof_sound cert
  exact ⟨N, hN⟩

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

-- **Soundness of bounded provability: anything provable within a budget is true.**
-- One arm per `Provable` constructor (grouped as in `Derivation.lean`):
--   • entry points: `struct` (→ `Derivation.sound`), `atom` (→ `AtomProvable_sound`);
--   • implication reasoning: `weakenImpl`/`searchThenSearch_t`/`implTrans` (interp is Lean
--     implication, so these are function composition / the IH on the consequent);
--   • modal/box rules: `atomBoxImpl`/`boxIntro`/`app`/`axK`/`box4` — each interp is `Provable …`
--     (the box clause), discharged from the premise's provability (`app` runs the implication).
-- `induction`/`cases` can't recurse through the mutual block, so we drive it with `Provable.rec`
-- (mirroring `playsProof_sound`); the minor premises are POSITIONAL — all `PlaysProof`/`AtomProvable`
-- arms have motive `True`, then one arm per `Provable` constructor in declaration order.
theorem Provable_sound : ∀ k φ, Provable k φ → φ.interp := by
  intro k φ h
  exact Provable.rec
    (motive_1 := fun _ _ _ _ _ _ => True)
    (motive_2 := fun _ _ _ => True)
    (motive_3 := fun _ φ _ => φ.interp)
    trivial                                   -- const
    (fun _ _ => trivial)                      -- self
    (fun _ _ => trivial)                      -- opp
    (fun _ _ => trivial)                      -- bot
    (fun _ _ => trivial)                      -- sim
    (fun _ _ _ _ _ => trivial)                -- ite_t
    (fun _ _ _ _ _ => trivial)                -- ite_f
    (fun _ _ _ _ => trivial)                  -- search_t
    (fun _ _ _ => trivial)                    -- mk (AtomProvable)
    (fun {k} {φ} hd => by obtain ⟨d, _⟩ := hd; exact d.sound)   -- struct
    (fun {k} {φ} hatom _ => AtomProvable_sound k φ hatom)       -- atom
    -- weakenImpl: `(.impl φ ψ).interp` is `φ.interp → ψ.interp`; the IH
    -- `ih : ψ.interp` (from `Provable m ψ`) discharges it via `fun _ => ih`.
    (fun _φ _ψ _m _hpsi _hle ih => fun _ => ih)                 -- weakenImpl
    -- searchThenSearch_t: conclusion `(□_{k₁} ψ₁' → me plays c0).interp`, i.e.
    -- `Provable k₁ ψ₁' → ∃ n, play n me opponent = some c0`. Given the box
    -- antecedent (`hbox : Provable k₁ ψ₁'`) and the prudence premise
    -- (`hprud : Provable k₂ ψ₂'`), both reflect to `proofSearch … = true`, so
    -- `eval` runs outer `.search` → inner `.search` → `.const c0`. Witness fuel 3.
    (fun {_k} k₁ k₂ m ψ₁ ψ₂ c0 c1 q me opponent hme hprud hmk _hle _ih => by
        subst hme
        intro hbox
        have hps₁ : proofSearch k₁ (ψ₁.subst
            (.search k₁ ψ₁ (.search k₂ ψ₂ (.const c0) (.const c1)) q) opponent) = true :=
          (proofSearch_spec _ _).2 hbox
        -- the inner premise is at its own transcript `m ≤ k₂`; budget-monotonicity lifts it
        have hps₂ : proofSearch k₂ (ψ₂.subst
            (.search k₁ ψ₁ (.search k₂ ψ₂ (.const c0) (.const c1)) q) opponent) = true :=
          (proofSearch_spec _ _).2 (Provable_mono hprud hmk)
        exact ⟨3, by simp only [play, eval, hps₁, hps₂, if_true]⟩)
    -- implTrans: compose the two implications' interps (function composition).
    (fun _φ _ψ _χ _a _b _hab _hbc _hle ihab ihbc => fun h => ihbc (ihab h))  -- implTrans
    -- atomBoxImpl: conclusion `(φ → □_k φ).interp`, i.e. `φ.interp → Provable k φ`.
    -- The certificate `hatom : AtomProvable k φ` discharges the consequent directly
    -- (`Provable.atom`), independent of the antecedent — no axiom.
    (fun {_k} _kBox _p _q _a hatom _hle _ih => fun _ => Provable.atom hatom)  -- atomBoxImpl
    -- boxIntro: conclusion `(□_{kIn} φ).interp` is *definitionally* `Provable kIn φ`,
    -- which is exactly the premise `hprem`. The arm is the identity (`ih : φ.interp`
    -- is unused — we return the stronger provability the premise already carries).
    (fun _kIn _K _φ hprem _hle _ih => hprem)                                  -- boxIntro
    -- app: conclusion `α.interp`. ihimp : `(φ→α).interp = (φ.interp → α.interp)`;
    -- ihφ : `φ.interp`. Pure function application. (binders: k m₁ m₂ φ α impl ante gate)
    (fun _k _m₁ _m₂ _φ _α _himp _hante _hle ihimp ihante => ihimp ihante)      -- app
    -- axK: conclusion `(□_b φ → □_c α).interp = (Provable b φ → Provable c α)`. The IH on the
    -- premise `Provable m (□_a(φ→α))` is its interp `Provable a (φ→α)`; apply it to the
    -- hypothetical `Provable b φ` via OBJECT modus ponens `Provable.app` at output `c` — the
    -- additive gate `a + b + α.size ≤ c` is EXACTLY `app`'s side condition (transcript-honest K).
    (fun a b c _m _K φ α _hprem hgate _hle ih =>
      (fun hφ => Provable.app c a b φ α ih hφ hgate))                          -- axK
    -- box4: conclusion `(□_a φ → □_b (□_a φ)).interp = (Provable a φ → Provable b (□_a φ))`:
    -- `boxIntro` with the additive gate `a + (□_a φ).size ≤ b` (the premise transcript ≤ a).
    (fun a b _K φ hgate _hsz =>
      (show Provable a φ → Provable b (.box a φ) from
        fun hφ => Provable.boxIntro a b φ hφ hgate))                           -- box4
    -- diagF: conclusion `(ψ → (□_g ψ → tgt)).interp` where `ψ := .diag g tgt` and
    -- `ψ.interp = (Provable g ψ → tgt.interp)` BY DEFINITION (Dynamics.lean) — the identity.
    (fun _pm _fb _g _K _tgt _hgate _hle _ih => fun h => h)                     -- diagF
    -- diagB: `((□_g ψ → tgt) → ψ).interp` — the same identity, other direction.
    (fun _pm _fb _g _K _tgt _hgate _hle _ih => fun h => h)                     -- diagB
    -- axKf: `(□_a(φ→α) → (□_bφ → □_cα)).interp = Provable a (φ→α) → Provable b φ → Provable c α`:
    -- object modus ponens (`Provable.app`) at output `c`; the gate is `app`'s condition.
    (fun a b c _K φ α hgate _hsz =>
      fun hab ha => Provable.app c a b φ α hab ha hgate)                       -- axKf
    -- impS2: `(φ→χ).interp` from ih₁ : `(φ→(ψ→χ)).interp` and ih₂ : `(φ→ψ).interp` — the
    -- S-combinator, plain function application.
    (fun _φ _ψ _χ _m₁ _m₂ _K _h1 _h2 _hle ih1 ih2 => fun hφ => (ih1 hφ) (ih2 hφ))  -- impS2
    -- boxMono: `(□_a φ → □_b φ).interp = (Provable a φ → Provable b φ)` with `a ≤ b` —
    -- budget monotonicity (`Provable_mono`), the semantic fact the rule internalizes.
    (fun _a _b _K _φ hab _hsz => fun hpa => Provable_mono hpa hab)             -- boxMono
    h

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

/-- Completeness of bounded proof search for atomic plays-formulas: a play within
    `fuel` steps is provable within budget `atom_cost fuel`. -/
theorem proofSearch_complete_plays :
∀ p q a, (∃ n, play n p q = some a) → ∃ k, proofSearch k (.plays p q a) = true := by
  intro p q a ⟨n, hn⟩
  exact ⟨atom_cost n,
    (proofSearch_spec _ (.plays p q a)).2 (Provable.atom (atom_complete p q a n hn))⟩

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
    is provable at `k`. Built from `atom_complete` + `atom_monotone` (→ `Provable k atom`),
    `box_provable` (→ `Provable K (□_k atom)`), and `weakenImpl` (→ the implication).

    The threshold `atom_cost fuel ≤ k` keeps it on the sound Σ₁ side: bounded Σ₁-completeness, NOT the
    GL-excluded converse-necessitation `φ → □φ`. (Historical note: the witness-free form was once the
    axiom `atom_box_provable_impl`, removed as unsound; this conditional theorem and the `atomBoxImpl`
    constructor are its sound content.) -/
theorem atom_box_provable_impl_sound (k fuel K : Nat) (p q : Prog) (a : Action)
    (hplay : play fuel p q = some a) (hk : atom_cost fuel ≤ k)
    (hK : k + (Formula.box k (.plays p q a)).size
          + (Formula.impl (.plays p q a) (.box k (.plays p q a))).size ≤ K) :
    Provable K (.impl (.plays p q a) (.box k (.plays p q a))) := by
  -- Under transcript cost the conclusion can no longer live at the box's own budget `k`
  -- (the implication's proof CONTAINS the box proof, which contains the `k`-certificate);
  -- the output budget `K` pays certificate + box + conclusion.
  have hatom : Provable k (.plays p q a) :=
    Provable.atom (atom_monotone (atom_cost fuel) k _ hk (atom_complete p q a fuel hplay))
  have hbox : Provable (k + (Formula.box k (.plays p q a)).size) (.box k (.plays p q a)) :=
    Provable.boxIntro k _ _ hatom (Nat.le_refl _)
  exact Provable.weakenImpl (.plays p q a) (.box k (.plays p q a)) _ hbox hK

/-- `Nat.log2` is monotone (companion to `c_guard_mono`; used by the `pblt_engine`
    instantiations to bound the chain's box-subscript numerals by `log2 k`). -/
theorem log2_mono {a b : Nat} (h : a ≤ b) : Nat.log2 a ≤ Nat.log2 b := by
  simp only [Nat.log2_eq_log_two]; exact Nat.log_mono_right h

/-! ### The mutual-Löb corollary — closes the cross-bot cooperation fixpoints

`mutual_loeb` derives a closed Löb premise from the two object transparency legs
(`legPD : □_kP A → B`, `legDP : □_kD B → A`). TRANSCRIPT-COST SHAPE (T0 §6,
`Research/Spikes/transcript/T0Transcript.lean`): the conclusion lives at a LOWERED box
subscript `fb` (strictly below the legs' source literals) — `□_fb A → □_kP A` feeds leg 1
via upward `boxMono`, the K-distribution lands at `c ≤ kD` which mono-UPs onto leg 2's box,
yielding `□_fb A → A` with an O(log k) transcript. `bloeb_engine`/`pblt_engine` then consume
the premise at `fb`. (The former same-subscript factoring `□_k φP → φP` is UNDERIVABLE under
transcript cost: K-distribution pushes the intermediate subscript above `k`, and downward
box-mono is unsound.) -/

/-- **Mutual / simultaneous bounded Löb premise** (object form) — ALL CONSTRUCTORS, no axiom.
    From `legPD : □_kP A → B` and `legDP : □_kD B → A`, build `□_fb A → A` at the lowered
    subscript `fb`. Free choices: `fb n m c` and the step transcripts `d₁…d₉`; the H-side
    conditions are what the consumers' omega blocks discharge (all O(log k)-shaped when the
    legs are transparency leaves). -/
theorem mutual_loeb (A B : Formula) (kP kD fb n m c pA pB : Nat)
    (d₁ d₂ d₃ d₄ d₅ d₆ d₇ d₈ d₉ K : Nat)
    (legPD : Provable pA (.impl (.box kP A) B))
    (legDP : Provable pB (.impl (.box kD B) A))
    (H1 : fb ≤ kP)
    (H2 : (Formula.impl (.box fb A) (.box kP A)).size ≤ d₁)
    (H3 : d₁ + pA + (Formula.impl (.box fb A) B).size ≤ d₂)
    (H4 : d₂ ≤ n)
    (H5 : n + (Formula.box n (.impl (.box fb A) B)).size ≤ d₃)
    (H6 : n + m + B.size ≤ c)
    (H7 : (Formula.impl (.box n (.impl (.box fb A) B))
            (.impl (.box m (.box fb A)) (.box c B))).size ≤ d₄)
    (H8 : d₄ + d₃ + (Formula.impl (.box m (.box fb A)) (.box c B)).size ≤ d₅)
    (H9 : fb + (Formula.box fb A).size ≤ m)
    (H10 : (Formula.impl (.box fb A) (.box m (.box fb A))).size ≤ d₆)
    (H11 : d₆ + d₅ + (Formula.impl (.box fb A) (.box c B)).size ≤ d₇)
    (H12 : c ≤ kD)
    (H13 : (Formula.impl (.box c B) (.box kD B)).size ≤ d₈)
    (H14 : d₇ + d₈ + (Formula.impl (.box fb A) (.box kD B)).size ≤ d₉)
    (H15 : d₉ + pB + (Formula.impl (.box fb A) A).size ≤ K) :
    Provable K (.impl (.box fb A) A) := by
  -- s1 : □_fb A → □_kP A   (mono-UP onto leg 1's antecedent)
  have s1 : Provable d₁ (.impl (.box fb A) (.box kP A)) := Provable.boxMono fb kP d₁ A H1 H2
  -- s2 : □_fb A → B
  have s2 : Provable d₂ (.impl (.box fb A) B) :=
    Provable.implTrans _ _ _ d₁ pA s1 legPD H3
  -- s3 : □_n (□_fb A → B)
  have s3 : Provable d₃ (.box n (.impl (.box fb A) B)) :=
    Provable.boxIntro n d₃ _ (Provable_mono s2 H4) H5
  -- s4 : K-distribution landing at c ≤ kD (THE fix)
  have s4 : Provable d₄ (.impl (.box n (.impl (.box fb A) B))
      (.impl (.box m (.box fb A)) (.box c B))) :=
    Provable.axKf n m c d₄ (.box fb A) B H6 H7
  have s5 : Provable d₅ (.impl (.box m (.box fb A)) (.box c B)) :=
    Provable.app d₅ d₄ d₃ _ _ s4 s3 H8
  -- s6 : □_fb A → □_m □_fb A   (four)
  have s6 : Provable d₆ (.impl (.box fb A) (.box m (.box fb A))) :=
    Provable.box4 fb m d₆ A H9 H10
  have s7 : Provable d₇ (.impl (.box fb A) (.box c B)) :=
    Provable.implTrans _ _ _ d₆ d₅ s6 s5 H11
  -- s8 : □_c B → □_kD B   (mono-UP onto leg 2's antecedent)
  have s8 : Provable d₈ (.impl (.box c B) (.box kD B)) := Provable.boxMono c kD d₈ B H12 H13
  have s9 : Provable d₉ (.impl (.box fb A) (.box kD B)) :=
    Provable.implTrans _ _ _ d₇ d₈ s7 s8 H14
  -- s10 : □_fb A → A — the tight Löb premise at the LOWERED subscript
  exact Provable.implTrans _ _ _ d₉ pB s9 legDP H15

/-! ## Bounded Löb INSIDE `Provable` — the internalized chain, TRANSCRIPT-COST (T0).

`bloeb_engine` runs Löb's derivation entirely in `Provable` from the TIGHT premise
`Provable pm (□_fb φ → φ)` — `pm` is the premise's honest transcript (O(log k) for the
consumers' single-leaf `searchBranch` / `mutual_loeb` premises; do NOT weaken it up to `k`,
the chain needs `pm ≪ fb`). The fixpoint sentence `ψ := .diag g φ` lives at the FREE subscript
`g ≺ fb`: under transcript cost ψ's proof CONTAINS the premise's proof, so `□`-ing ψ needs
`g` to absorb ψ's whole transcript (`H19 : c₁₃ ≤ g`) — Critch's `g ≺ f` dance, validated in
`Research/Spikes/transcript/T0Transcript.lean` (`bloeb_transcript`, axiom-free). The step
transcripts `c₁…c₁₄` and the box stages `n₁ n₃ n₄ n₅` are explicit; `pblt_engine` instantiates
everything as multiples of ONE O(log k) unit and discharges the 21 side-conditions by omega. -/

theorem bloeb_engine (φ : Formula) (pm fb g n₁ n₃ n₄ n₅ : Nat)
    (c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ c₁₁ c₁₂ c₁₃ c₁₄ K : Nat)
    (hLoeb : Provable pm (.impl (.box fb φ) φ))
    (H1 : pm + (Formula.impl (.diag g φ) (.impl (.box g (.diag g φ)) φ)).size ≤ c₁)
    (H2 : pm + (Formula.impl (.impl (.box g (.diag g φ)) φ) (.diag g φ)).size ≤ c₂)
    (H3 : c₁ ≤ n₁)
    (H4 : n₁ + (Formula.box n₁ (.impl (.diag g φ) (.impl (.box g (.diag g φ)) φ))).size ≤ c₃)
    (H5 : n₁ + g + (Formula.impl (.box g (.diag g φ)) φ).size ≤ n₃)
    (H6 : (Formula.impl (.box n₁ (.impl (.diag g φ) (.impl (.box g (.diag g φ)) φ)))
            (.impl (.box g (.diag g φ)) (.box n₃ (.impl (.box g (.diag g φ)) φ)))).size ≤ c₄)
    (H7 : c₄ + c₃ + (Formula.impl (.box g (.diag g φ))
            (.box n₃ (.impl (.box g (.diag g φ)) φ))).size ≤ c₅)
    (H8 : n₃ + n₄ + φ.size ≤ n₅)
    (H9 : (Formula.impl (.box n₃ (.impl (.box g (.diag g φ)) φ))
            (.impl (.box n₄ (.box g (.diag g φ))) (.box n₅ φ))).size ≤ c₆)
    (H10 : g + (Formula.box g (.diag g φ)).size ≤ n₄)
    (H11 : (Formula.impl (.box g (.diag g φ)) (.box n₄ (.box g (.diag g φ)))).size ≤ c₇)
    (H12 : c₅ + c₆ + (Formula.impl (.box g (.diag g φ))
            (.impl (.box n₄ (.box g (.diag g φ))) (.box n₅ φ))).size ≤ c₈)
    (H13 : c₈ + c₇ + (Formula.impl (.box g (.diag g φ)) (.box n₅ φ)).size ≤ c₉)
    (H14 : n₅ ≤ fb)
    (H15 : (Formula.impl (.box n₅ φ) (.box fb φ)).size ≤ c₁₀)
    (H16 : c₉ + c₁₀ + (Formula.impl (.box g (.diag g φ)) (.box fb φ)).size ≤ c₁₁)
    (H17 : c₁₁ + pm + (Formula.impl (.box g (.diag g φ)) φ).size ≤ c₁₂)
    (H18 : c₂ + c₁₂ + (Formula.diag g φ).size ≤ c₁₃)
    (H19 : c₁₃ ≤ g)
    (H20 : g + (Formula.box g (.diag g φ)).size ≤ c₁₄)
    (H21 : c₁₂ + c₁₄ + φ.size ≤ K) :
    Provable K φ := by
  -- the two fixpoint legs (gated on hLoeb, charging its transcript)
  have legF : Provable c₁ (.impl (.diag g φ) (.impl (.box g (.diag g φ)) φ)) :=
    Provable.diagF pm fb g c₁ φ hLoeb H1
  have legB : Provable c₂ (.impl (.impl (.box g (.diag g φ)) φ) (.diag g φ)) :=
    Provable.diagB pm fb g c₂ φ hLoeb H2
  -- hnec : □_{n₁}(ψ → (□_gψ→φ))
  have hnec : Provable c₃ (.box n₁ (.impl (.diag g φ) (.impl (.box g (.diag g φ)) φ))) :=
    Provable.boxIntro n₁ c₃ _ (Provable_mono legF H3) H4
  -- hK1 : □_{n₁}(ψ→ctx) → (□_g ψ → □_{n₃} ctx)   [axKf stage 1]
  have hK1 : Provable c₄ (.impl (.box n₁ (.impl (.diag g φ) (.impl (.box g (.diag g φ)) φ)))
      (.impl (.box g (.diag g φ)) (.box n₃ (.impl (.box g (.diag g φ)) φ)))) :=
    Provable.axKf n₁ g n₃ c₄ (.diag g φ) (.impl (.box g (.diag g φ)) φ) H5 H6
  -- h2 : □_g ψ → □_{n₃} ctx
  have h2 : Provable c₅ (.impl (.box g (.diag g φ)) (.box n₃ (.impl (.box g (.diag g φ)) φ))) :=
    Provable.app c₅ c₄ c₃ _ _ hK1 hnec H7
  -- hK2 : □_{n₃}(□_gψ→φ) → (□_{n₄}□_gψ → □_{n₅} φ)   [axKf stage 2]
  have hK2 : Provable c₆ (.impl (.box n₃ (.impl (.box g (.diag g φ)) φ))
      (.impl (.box n₄ (.box g (.diag g φ))) (.box n₅ φ))) :=
    Provable.axKf n₃ n₄ n₅ c₆ (.box g (.diag g φ)) φ H8 H9
  -- hfour : □_g ψ → □_{n₄} □_g ψ
  have hfour : Provable c₇ (.impl (.box g (.diag g φ)) (.box n₄ (.box g (.diag g φ)))) :=
    Provable.box4 g n₄ c₇ (.diag g φ) H10 H11
  -- h4 : □_g ψ → (□_{n₄}□_gψ → □_{n₅} φ)
  have h4 : Provable c₈ (.impl (.box g (.diag g φ))
      (.impl (.box n₄ (.box g (.diag g φ))) (.box n₅ φ))) :=
    Provable.implTrans _ _ _ c₅ c₆ h2 hK2 H12
  -- h6 : □_g ψ → □_{n₅} φ   [impS2 — S-composition]
  have h6 : Provable c₉ (.impl (.box g (.diag g φ)) (.box n₅ φ)) :=
    Provable.impS2 _ _ _ c₈ c₇ c₉ h4 hfour H13
  -- hmono : □_{n₅} φ → □_{fb} φ   [upward boxMono — new with the transcript model]
  have hmono : Provable c₁₀ (.impl (.box n₅ φ) (.box fb φ)) :=
    Provable.boxMono n₅ fb c₁₀ φ H14 H15
  -- h6' : □_g ψ → □_{fb} φ
  have h6' : Provable c₁₁ (.impl (.box g (.diag g φ)) (.box fb φ)) :=
    Provable.implTrans _ _ _ c₉ c₁₀ h6 hmono H16
  -- hE : □_g ψ → φ
  have hE : Provable c₁₂ (.impl (.box g (.diag g φ)) φ) :=
    Provable.implTrans _ _ _ c₁₁ pm h6' hLoeb H17
  -- hF : ψ  (contains legB + hE — hence the premise's transcript; H19 : c₁₃ ≤ g absorbs it)
  have hF : Provable c₁₃ (.diag g φ) := Provable.app c₁₃ c₂ c₁₂ _ _ legB hE H18
  have hG : Provable c₁₄ (.box g (.diag g φ)) :=
    Provable.boxIntro g c₁₄ _ (Provable_mono hF H19) H20
  exact Provable.app K c₁₂ c₁₄ _ _ hE hG H21

/-- **Parametric bounded Löb, INTERNAL** — the `PBLT` conclusion as a THEOREM, transcript-cost.
    Premise at its HONEST transcript `pm k` (O(log k) for all consumers — do not weaken to `f k`);
    ONE master headroom bound `8192·(pm k + (φ k).size + log2 (f k) + 8) ≤ f k` instantiates the
    whole chain as multiples of the unit `W := pm + |φ| + log2 (f k) + 8` (T0's assignment:
    `g = 1024·W` absorbs the fixpoint's proof, the largest stage is `n₅ = 8192·W ≤ f k`). -/
theorem pblt_engine (φ : Nat → Formula) (f pm : Nat → Nat) (k₁ : Nat)
    (hLoeb : ∀ k, k > k₁ → Provable (pm k) (.impl (.box (f k) (φ k)) (φ k)))
    (hsz : ∀ k, k > k₁ → 8192 * (pm k + (φ k).size + Nat.log2 (f k) + 8) ≤ f k) :
    ∃ k₂, ∀ k, k > k₂ → ∃ m, Provable m (φ k) := by
  refine ⟨k₁, fun k hk => ?_⟩
  obtain ⟨W, hW⟩ : ∃ W, W = pm k + (φ k).size + Nat.log2 (f k) + 8 := ⟨_, rfl⟩
  have hWk : 8192 * W ≤ f k := hW ▸ hsz k hk
  -- every chosen subscript is ≤ f k, so its numeral's log2 is ≤ log2 (f k)
  have hlg : Nat.log2 (1024 * W) ≤ Nat.log2 (f k) := log2_mono (by omega)
  have hl₁ : Nat.log2 (32 * W) ≤ Nat.log2 (f k) := log2_mono (by omega)
  have hl₃ : Nat.log2 (2048 * W) ≤ Nat.log2 (f k) := log2_mono (by omega)
  have hl₅ : Nat.log2 (8192 * W) ≤ Nat.log2 (f k) := log2_mono (by omega)
  refine ⟨4096 * W, bloeb_engine (φ k) (pm k) (f k)
    (1024 * W) (32 * W) (2048 * W) (2048 * W) (8192 * W)
    (16 * W) (16 * W) (64 * W) (32 * W) (128 * W) (32 * W) (16 * W)
    (256 * W) (512 * W) (16 * W) (640 * W) (704 * W) (768 * W) (2048 * W) (4096 * W)
    (hLoeb k hk)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_⟩ <;>
  · (try simp only [Formula.size]); omega

/-- **Consumer-facing PBLT** (`f = id`, the shape every bot theorem uses): tight Löb premise at
    its honest transcript `pm k` (what the `*_loeb_premise` lemmas produce — a single
    transparency leaf, `O(log k)` characters) + generous uniform `10·log2 k + 100` bounds on
    both the play-atom family and the premise transcript (covers every bot in the zoo).
    Replaces the former `PBLT` axiom at all call sites. -/
theorem pblt_engine_id (φ : Nat → Formula) (pm : Nat → Nat) (k₁ : Nat)
    (hφ : ∀ k, (φ k).size ≤ 100 * Nat.log2 k + 1000)
    (hpm : ∀ k, pm k ≤ 100 * Nat.log2 k + 1000)
    (hLoeb : ∀ k, k > k₁ → Provable (pm k) (.impl (.box k (φ k)) (φ k))) :
    ∃ k₂, ∀ k, k > k₂ → ∃ m, Provable m (φ k) := by
  -- master bound: 8192·((100L+1000) + (100L+1000) + L + 8) = 1646592·L + 16449536 ≤ k, eventually.
  obtain ⟨Ksz, hKsz⟩ := linear_log2_add_le 1646592 16449536
  obtain ⟨k₂, hk₂⟩ := pblt_engine φ id pm (max k₁ Ksz)
    (fun k hk => hLoeb k (lt_of_le_of_lt (Nat.le_max_left _ _) hk))
    (by
      intro k hk
      have h1 := hKsz k (Nat.le_of_lt (lt_of_le_of_lt (Nat.le_max_right _ _) hk))
      have h2 := hφ k
      have h3 := hpm k
      show 8192 * (pm k + (φ k).size + Nat.log2 (id k) + 8) ≤ id k
      simp only [id]
      omega)
  exact ⟨k₂, hk₂⟩

/-- **Consumer-facing MUTUAL PBLT** (`f = id`): the cross-bot cooperation closer
    (PrudentBot↔DupocBot, JustBot legs, …). Takes the two transparency legs at their honest
    O(log k) transcripts and SAME-`k` source literals, derives the lowered premise via
    `mutual_loeb` (`fb = k − 64·V`), and runs `bloeb_engine` at `fb`. Validated in
    `T0Transcript.lean` §6 (`mutual_pblt_transcript`). -/
theorem mutual_pblt_engine_id (Af Bf : Nat → Formula) (p₁ p₂ : Nat → Nat) (k₁ : Nat)
    (hsA : ∀ k, (Af k).size ≤ 100 * Nat.log2 k + 1000)
    (hsB : ∀ k, (Bf k).size ≤ 100 * Nat.log2 k + 1000)
    (hp1 : ∀ k, p₁ k ≤ 100 * Nat.log2 k + 1000)
    (hp2 : ∀ k, p₂ k ≤ 100 * Nat.log2 k + 1000)
    (hL1 : ∀ k, k > k₁ → Provable (p₁ k) (.impl (.box k (Af k)) (Bf k)))
    (hL2 : ∀ k, k > k₁ → Provable (p₂ k) (.impl (.box k (Bf k)) (Af k))) :
    ∃ k₂, ∀ k, k > k₂ → ∃ m, Provable m (Af k) := by
  -- master headroom: 131072·V ≤ k with V ≤ 401·log2 k + 4016.
  obtain ⟨Ksz, hKsz⟩ := linear_log2_add_le (131072 * 401) (131072 * 4016)
  refine ⟨max k₁ Ksz, fun k hk => ?_⟩
  obtain ⟨V, hV⟩ : ∃ V,
      V = p₁ k + p₂ k + (Af k).size + (Bf k).size + Nat.log2 k + 16 := ⟨_, rfl⟩
  have hp1k := hp1 k; have hp2k := hp2 k; have hsAk := hsA k; have hsBk := hsB k
  have hVk : 131072 * V ≤ k := by
    have h := hKsz k (Nat.le_of_lt (lt_of_le_of_lt (Nat.le_max_right _ _) hk))
    have hVle : V ≤ 401 * Nat.log2 k + 4016 := by omega
    calc 131072 * V ≤ 131072 * (401 * Nat.log2 k + 4016) := Nat.mul_le_mul_left _ hVle
      _ = 131072 * 401 * Nat.log2 k + 131072 * 4016 := by ring
      _ ≤ k := h
  have hkk₁ : k > k₁ := lt_of_le_of_lt (Nat.le_max_left _ _) hk
  -- the lowered premise subscript: fb + 64V = k
  obtain ⟨fb, hfb⟩ : ∃ fb, 64 * V + fb = k := Nat.le.dest (by omega)
  have hLfb : Nat.log2 fb ≤ Nat.log2 k := log2_mono (by omega)
  have hLm : Nat.log2 (fb + 8*V) ≤ Nat.log2 k := log2_mono (by omega)
  have hLc : Nat.log2 (fb + 32*V) ≤ Nat.log2 k := log2_mono (by omega)
  have hLn : Nat.log2 (16*V) ≤ Nat.log2 k := log2_mono (by omega)
  have hLn₁ : Nat.log2 (512*V) ≤ Nat.log2 k := log2_mono (by omega)
  have hLg : Nat.log2 (8192*V) ≤ Nat.log2 k := log2_mono (by omega)
  have hLn₃ : Nat.log2 (16384*V) ≤ Nat.log2 k := log2_mono (by omega)
  have hLn₅ : Nat.log2 (65536*V) ≤ Nat.log2 k := log2_mono (by omega)
  -- the lowered Löb premise (mutual_loeb): Provable (160V) (□_fb Af → Af)
  have s10 : Provable (160*V) (.impl (.box fb (Af k)) (Af k)) := by
    refine mutual_loeb (Af k) (Bf k) k k fb (16*V) (fb + 8*V) (fb + 32*V) (p₁ k) (p₂ k)
      (8*V) (16*V) (32*V) (16*V) (64*V) (16*V) (96*V) (8*V) (128*V) (160*V)
      (hL1 k hkk₁) (hL2 k hkk₁)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    · (try simp only [Formula.size]); omega
  -- single-leg bloeb at fb
  refine ⟨32768*V, bloeb_engine (Af k) (160*V) fb
    (8192*V) (512*V) (16384*V) (16384*V) (65536*V)
    (256*V) (256*V) (1024*V) (512*V) (2048*V) (512*V) (512*V)
    (3072*V) (4096*V) (256*V) (5120*V) (6144*V) (7168*V) (16384*V) (32768*V)
    s10 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_⟩ <;>
  · (try simp only [Formula.size]); omega
