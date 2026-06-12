import PrisonersDilemma.Dynamics
import PrisonersDilemma.Axioms


open Classical

open PD
open PD.Axioms
namespace PD.BaseTheorems

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
  | hypSyll φ ψ χ _ _ ih1 ih2 =>
      exact fun h => ih2 (ih1 h)
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
  -- dImp.size = (φ → ψ).size = φ.size + ψ.size + 1, so ψ.size ≤ n ≤ n+m+1
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
    ?const ?self ?opp ?bot ?sim ?ite_t ?ite_f ?search_t ?atomMk ?provStruct ?provAtom ?provWeaken h
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
    (fun _φ _ψ _m _hpsi _hsz ih => fun _ => ih)                 -- weakenImpl
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
                 exact (proofSearch_spec k₂ φ).2 (Provable.struct ⟨d, Nat.le_trans hsz hk⟩)
  | atom hatom => exact (proofSearch_spec k₂ φ).2 (Provable.atom (atom_monotone k₁ k₂ φ hk hatom))
  | weakenImpl ψ' χ' m hpsi hsz =>
      -- the conclusion's size bound relaxes from `k₁` to `k₂`; the consequent's
      -- proof carries over unchanged.
      exact (proofSearch_spec k₂ _).2
        (Provable.weakenImpl ψ' χ' m hpsi (Nat.le_trans hsz hk))

end PD.BaseTheorems
