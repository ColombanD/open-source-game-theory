import PrisonersDilemma.Dynamics
import PrisonersDilemma.Axioms


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

/-- The **K axiom** of GL, budget-respecting: from a derivation of `φ → ψ` of
    size `≤ n` and one of `φ` of size `≤ m`, `ψ` is provable within `n + m + 1`.
    With the character-faithful `Derivation.size = conclusion.size`, the combined
    derivation's size is `ψ.size ≤ (φ → ψ).size ≤ n ≤ n + m + 1`. Lifts the
    `modusPonens` constructor to the budgeted `Provable` level. -/
theorem K_provable (n m : Nat) (φ ψ : Formula)
    (dImp : Derivation (.impl φ ψ)) (hI : dImp.size ≤ n)
    (dφ : Derivation φ) (_hF : dφ.size ≤ m) :
    Provable (n + m + 1) ψ := by
  -- dImp.size = (φ → ψ).size = φ.size + ψ.size + 1, so ψ.size ≤ n ≤ n+m+1.
  exact Provable.struct ⟨.modusPonens φ ψ dImp dφ, by
    simp only [Derivation.size] at *; simp [Formula.size] at hI; omega⟩

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
    ?provSearchThenSearch ?provImplTrans ?provAtomBoxImpl h
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

-- Soundness of bounded provability: anything provable within a budget is true.
-- Three disjuncts now:
--   • structural `Derivation` rules (→ `Derivation.sound`);
--   • an atomic σ₁ fact (→ `AtomProvable_sound`);
--   • a `weakenImpl` true-consequent implication (recursive on the consequent's
--     provability — `Provable m ψ` is a structural subterm, so via `Provable.rec`).
-- `induction`/`cases` can't recurse through the mutual block, so we drive it with
-- `Provable.rec` (mirroring `playsProof_sound`).
theorem Provable_sound : ∀ k φ, Provable k φ → φ.interp := by
  intro k φ h
  -- The minor premises of `Provable.rec` are positional (anonymous binders), so
  -- we supply all twelve in order: the eight `PlaysProof` cases and the
  -- `AtomProvable` (`mk`) case all have motive `True`; then `struct`, `atom`, and
  -- the new `weakenImpl`.
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
    (fun _φ _ψ _m _hpsi _hmk _hsz ih => fun _ => ih)            -- weakenImpl
    -- searchThenSearch_t: conclusion `(□_{k₁} ψ₁' → me plays c0).interp`, i.e.
    -- `Provable k₁ ψ₁' → ∃ n, play n me opponent = some c0`. Given the box
    -- antecedent (`hbox : Provable k₁ ψ₁'`) and the prudence premise
    -- (`hprud : Provable k₂ ψ₂'`), both reflect to `proofSearch … = true`, so
    -- `eval` runs outer `.search` → inner `.search` → `.const c0`. Witness fuel 3.
    (fun {_k} k₁ k₂ ψ₁ ψ₂ c0 c1 q me opponent hme hprud _hk2 _hsz _ih => by
        subst hme
        intro hbox
        have hps₁ : proofSearch k₁ (ψ₁.subst
            (.search k₁ ψ₁ (.search k₂ ψ₂ (.const c0) (.const c1)) q) opponent) = true :=
          (proofSearch_spec _ _).2 hbox
        have hps₂ : proofSearch k₂ (ψ₂.subst
            (.search k₁ ψ₁ (.search k₂ ψ₂ (.const c0) (.const c1)) q) opponent) = true :=
          (proofSearch_spec _ _).2 hprud
        exact ⟨3, by simp only [play, eval, hps₁, hps₂, if_true]⟩)
    -- implTrans: compose the two implications' interps (function composition).
    (fun _φ _ψ _χ _a _b _hab _hbc _hak _hbk _hpsisz _hsz ihab ihbc => fun h => ihbc (ihab h))  -- implTrans
    -- atomBoxImpl: conclusion `(φ → □_k φ).interp`, i.e. `φ.interp → Provable k φ`.
    -- The certificate `hatom : AtomProvable k φ` discharges the consequent directly
    -- (`Provable.atom`), independent of the antecedent — no axiom.
    (fun {_k} _kBox _p _q _a hatom _hsz _ih => fun _ => Provable.atom hatom)  -- atomBoxImpl
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

-- Monotonicity in proof-search budget: the structural disjunct relaxes its size
-- bound; the `AtomProvable` disjunct carries over by `atom_monotone`.
theorem proofSearch_monotone :
  ∀ k₁ k₂ φ, k₁ ≤ k₂ → proofSearch k₁ φ = true → proofSearch k₂ φ = true := by
  intro k₁ k₂ φ hk h1
  cases (proofSearch_spec k₁ φ).1 h1 with
  | struct hd => obtain ⟨d, hsz⟩ := hd
                 -- the derivation carries over; only its size bound relaxes `k₁ → k₂`.
                 exact (proofSearch_spec k₂ φ).2
                   (Provable.struct ⟨d, Nat.le_trans hsz hk⟩)
  | atom hatom => exact (proofSearch_spec k₂ φ).2 (Provable.atom (atom_monotone k₁ k₂ φ hk hatom))
  | weakenImpl ψ' χ' m hpsi hmk hsz =>
      -- the conclusion's size bound relaxes from `k₁` to `k₂`; the consequent's
      -- proof and budget bound carry over (transitivity through `k₁ ≤ k₂`).
      exact (proofSearch_spec k₂ _).2
        (Provable.weakenImpl ψ' χ' m hpsi (Nat.le_trans hmk hk) (Nat.le_trans hsz hk))
  | searchThenSearch_t a₁ a₂ ψ₁ ψ₂ c0 c1 q me opponent hme hprud hk2 hsz =>
      -- same as `weakenImpl`: relax the conclusion's size and `k₂` bounds `k₁ → k₂`;
      -- the inner (prudence) proof and `hme` carry over unchanged.
      exact (proofSearch_spec k₂ _).2
        (Provable.searchThenSearch_t a₁ a₂ ψ₁ ψ₂ c0 c1 q me opponent hme hprud
          (Nat.le_trans hk2 hk) (Nat.le_trans hsz hk))
  | implTrans φ ψ χ a b hab hbc hak hbk hpsisz hsz =>
      -- relax the conclusion's size, both leg budgets, and the cut-formula size
      -- bound `k₁ → k₂` (all via transitivity through `k₁ ≤ k₂`).
      exact (proofSearch_spec k₂ _).2
        (Provable.implTrans φ ψ χ a b hab hbc (Nat.le_trans hak hk) (Nat.le_trans hbk hk)
          (Nat.le_trans hpsisz hk) (Nat.le_trans hsz hk))
  | atomBoxImpl kBox p q a hatom hsz =>
      -- the box certificate stays at its own budget `kBox` (untouched by `k₁ → k₂`);
      -- only the conclusion's size bound relaxes from `k₁` to `k₂`.
      exact (proofSearch_spec k₂ _).2
        (Provable.atomBoxImpl kBox p q a hatom (Nat.le_trans hsz hk))

/-- **Soundness witness for the `atom_box_provable_impl` axiom (Axioms.lean).**
    Object-level bounded Σ₁-completeness for play-atoms, in the *conditional* form
    that is a kernel-checked THEOREM: when the play actually happens within `fuel`
    steps AND the budget `k` fits a certificate (`atom_cost fuel ≤ k`), the object
    implication `(p plays a vs q) → □_k (p plays a vs q)` is provable at `k`. Built
    from `atom_complete` + `atom_monotone` (→ `Provable k atom`), `box_provable`
    (→ `Provable K (□_k atom)`), and `weakenImpl` (→ the implication).

    This certifies the principle the axiom asserts is SOUND under the budget
    threshold; the axiom drops the `play`/`atom_cost ≤ k` hypotheses so it can be used
    *witness-free* (the matchup builds its Löb premise before the cooperative play is
    in hand — see the false-case analysis in `PrudentDupoc.lean`), which is the part
    that genuinely needs to be axiomatic (Π₁/`box_provable`-style reflection). The
    threshold `atom_cost fuel ≤ k` is what keeps it on the sound Σ₁ side: it is bounded
    Σ₁-completeness, NOT the GL-excluded converse-necessitation `φ → □φ`. -/
theorem atom_box_provable_impl_sound (k fuel : Nat) (p q : Prog) (a : Action)
    (hplay : play fuel p q = some a) (hk : atom_cost fuel ≤ k)
    (hsz : (Formula.impl (.plays p q a) (.box k (.plays p q a))).size ≤ k) :
    Provable k (.impl (.plays p q a) (.box k (.plays p q a))) := by
  have hatom : Provable k (.plays p q a) :=
    Provable.atom (atom_monotone (atom_cost fuel) k _ hk (atom_complete p q a fuel hplay))
  obtain ⟨K, hKle, hbox⟩ := box_provable k (.plays p q a) hatom
  -- `hKle : K ≤ (□_k atom).size`, and `hsz` forces `(□_k atom).size < (atom → □_k atom).size ≤ k`,
  -- so `K ≤ k` — exactly the budget bound the now-bounded `weakenImpl` requires.
  have hszbox : (Formula.box k (.plays p q a)).size < (Formula.impl (.plays p q a) (.box k (.plays p q a))).size := by
    simp only [Formula.size]; omega
  have hKk : K ≤ k := Nat.le_trans hKle (Nat.le_trans (Nat.le_of_lt hszbox) hsz)
  exact Provable.weakenImpl (.plays p q a) (.box k (.plays p q a)) K hbox hKk hsz

/-! ### Soundness of `boxInternalize`; the mutual-Löb corollary

`boxInternalize` (Axioms.lean) internalizes a budget-`k` proof transformer as an object box
implication at budget `k`, between play-atoms (it is NOT GL axiom K — see its doc). Its
soundness is `boxInternalize_sound`. `mutual_loeb` derives the closed Löb premise `□_k φP → φP`
from `boxInternalize` + the two transparency legs, by `implTrans`. -/

/-- **`boxInternalize` soundness.** `interp (□_k φ → □_k α)` is, definitionally,
    `Provable k φ → Provable k α` — which is *exactly* the proof-transformer premise `hfitD`.
    So the object implication denotes precisely its own hypothesis: the proof is `:= hfitD`,
    tautological, no new semantic content. (This is why the axiom is sound, not false.) -/
theorem boxInternalize_sound (k : Nat) (φ : Formula) (p q : Prog) (c : Action)
    (hfitD : Provable k φ → Provable k (.plays p q c)) :
    (Formula.impl (.box k φ) (.box k (.plays p q c))).interp :=
  hfitD

/-- **Soundness content of `mutual_loeb`.** The interp of `□_k φP → φP` holds, given the
    opponent leg `legDP` and the budget-fit transparency `hfitD`. Pure `Provable_sound`
    (no box axiom): under the hypothetical `Provable k φP`, `hfitD` gives `Provable k φD`,
    `legDP` makes `φP` play. Non-collapsible: needs `legDP` + `hfitD`, which only a genuine
    two-bot fixpoint supplies. -/
theorem mutual_loeb_sound (k : Nat) (pP qP pD qD : Prog) (bP bD : Action)
    (legDP : Provable k (.impl (.box k (.plays pD qD bD)) (.plays pP qP bP)))
    (hfitD : Provable k (.plays pP qP bP) → Provable k (.plays pD qD bD)) :
    (Formula.impl (.box k (.plays pP qP bP)) (.plays pP qP bP)).interp := by
  have hDP : (Formula.impl (.box k (.plays pD qD bD)) (.plays pP qP bP)).interp :=
    Provable_sound k _ legDP
  intro hboxP
  exact hDP (hfitD hboxP)

/-- **Mutual / simultaneous bounded Löb** (object form), derived via `boxInternalize`.
    From the opponent leg `legDP : □_k φD → φP` and the budget-`k` proof transformer
    `hfitD : Provable k φP → Provable k φD`, build `□_k φP → φP` as a `Provable` object:

      `boxInternalize` ⊳ hfitD : □_k φP → □_k φD   (internalize the transformer)
      `implTrans` with legDP : □_k φD → φP         ⇒  □_k φP → φP.

    All boxes stay at the single budget `k`, so the only side-conditions are the formula-size
    bounds. The single-fixed-`k` form is what lets the cut `□_k φD` meet `legDP`; the faithful
    object-antecedent GL-K route inflates the budget and does NOT compose (`Research/Spikes/
    HonestKSpike.lean`, `MutualLobSpike.lean`). -/
theorem mutual_loeb (k : Nat) (pP qP pD qD : Prog) (bP bD : Action)
    (legDP : Provable k (.impl (.box k (.plays pD qD bD)) (.plays pP qP bP)))
    (hfitD : Provable k (.plays pP qP bP) → Provable k (.plays pD qD bD))
    (hszK : (Formula.impl (.box k (.plays pP qP bP)) (.box k (.plays pD qD bD))).size ≤ k)
    (hszBoxD : (Formula.box k (.plays pD qD bD)).size ≤ k)
    (hsz : (Formula.impl (.box k (.plays pP qP bP)) (.plays pP qP bP)).size ≤ k) :
    Provable k (.impl (.box k (.plays pP qP bP)) (.plays pP qP bP)) := by
  -- boxInternalize : □_k φP → □_k φD
  have hKstep : Provable k (.impl (.box k (.plays pP qP bP)) (.box k (.plays pD qD bD))) :=
    boxInternalize k (.plays pP qP bP) pD qD bD hfitD hszK
  -- implTrans through the cut formula □_k φD : □_k φP → φP
  exact Provable.implTrans (.box k (.plays pP qP bP)) (.box k (.plays pD qD bD))
    (.plays pP qP bP) k k hKstep legDP (le_refl k) (le_refl k) hszBoxD hsz
