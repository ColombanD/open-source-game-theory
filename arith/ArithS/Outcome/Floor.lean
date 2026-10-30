import ArithS.Outcome.Spec

/-!
# ArithS.Outcome.Floor — the floor template: the engine-side half of a dichotomy

`Cells/FloorDichotomy.lean` states each GENUINE floor of the ledger as a hypothesis-free dichotomy
`dich_<L>_vs_<R>`: with `A_k` the cell's HINGE (`□[k]` of the floor side's outermost guard at its own budget —
bounded consistency of `TAct` at `k` up to an additive constant, Pudlák's linear-regime question, open both
ways), `¬A_k →` the engine's value and `A_k →` the found-branch value. Nothing will "prove" a floor; the app
carries it as a cell with provenance `floor_dichotomy` and an explicit policy
(`docs/notes/SPRIME_SOURCE_OF_TRUTH.md` §0.2).

`FloorSpecA L R hinge r` is the half the app reads under the `engine_side` policy, on the `OutcomeSpecA`
vocabulary: for all large `k`, if the hinge fails then the outcome is `r`. The hinge is written INLINE in each
statement (`Outcome/Floors.lean`), any `Prop` in `k`; for the nested cells it is the boolean combination of the
outer hinges under which the engine's value is forced. The full dichotomy stays where it is.
-/

namespace ArithS

/-- **The floor statement of PA-`S'`**: `r` is the outcome of `L k` facing `R k` for all large `k` at which
the hinge FAILS — the engine-side half of `dich_<L>_vs_<R>`. -/
def FloorSpecA (L R : ℕ → ℕ) (hinge : ℕ → Prop) (r : Option PD.Outcome) : Prop :=
  ∃ k₀, ∀ k, k₀ < k → ¬ hinge k → OutcomeAtA (L k) (R k) r

/-- From a dichotomy-shaped fact whose FIRST conjunct is the `¬hinge` branch (the order of
`Cells/FloorDichotomy.lean` §2–3); the found-branch conjunct `Q k` is not consulted. -/
theorem FloorSpecA.of_dich {L R : ℕ → ℕ} {hinge Q : ℕ → Prop} {a b : PD.Action} {n m : ℕ}
    (h : ∃ k₀, ∀ k, k₀ < k →
      (¬ hinge k → EvalGraph n (L k) (R k) (L k) (actCode a) ∧ EvalGraph m (R k) (L k) (R k) (actCode b)) ∧
      (hinge k → Q k)) :
    FloorSpecA L R hinge (some (a, b)) := by
  obtain ⟨k₀, h⟩ := h
  exact ⟨k₀, fun k hk hn ↦ OutcomeAtA.of_evalGraph ((h k hk).1 hn)⟩

/-- The general constructor: any eventual `¬hinge → plays` pair. -/
theorem FloorSpecA.of {L R : ℕ → ℕ} {hinge : ℕ → Prop} {a b : PD.Action} {n m : ℕ}
    (h : ∃ k₀, ∀ k, k₀ < k → ¬ hinge k →
      EvalGraph n (L k) (R k) (L k) (actCode a) ∧ EvalGraph m (R k) (L k) (R k) (actCode b)) :
    FloorSpecA L R hinge (some (a, b)) := by
  obtain ⟨k₀, h⟩ := h
  exact ⟨k₀, fun k hk hn ↦ OutcomeAtA.of_evalGraph (h k hk hn)⟩

/-- A floor whose hinge never fails beyond `k₀` says nothing; one whose hinge always fails is an eventual cell. -/
theorem FloorSpecA.eventual_of_not_hinge {L R : ℕ → ℕ} {hinge : ℕ → Prop} {r : Option PD.Outcome}
    (h : FloorSpecA L R hinge r) (hn : ∃ k₁, ∀ k, k₁ < k → ¬ hinge k) : OutcomeSpecA .eventual L R r := by
  obtain ⟨k₀, h⟩ := h; obtain ⟨k₁, hn⟩ := hn
  exact ⟨k₀ + k₁, fun k hk ↦ h k (by omega) (hn k (by omega))⟩

end ArithS
