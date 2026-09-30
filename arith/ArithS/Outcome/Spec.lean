import ArithS.Eval.EvalN
import ArithS.Agents.Code
import PrisonersDilemma.Outcome.Spec
import ArithS.Notation

/-!
# ArithS.Outcome.Spec — the outcome statement of PA-`S'`, in the engine's vocabulary

The engine states every matrix cell as `OutcomeSpec regime pad L R (some (a, b))`
(`PrisonersDilemma/Outcome/Spec.lean`). This module is the same statement for the arithmetized
system, so that a cell of `S'` reads the way a cell of `S` does:

    theorem outcome_DupocBot_vs_CupodBot :
        OutcomeSpecA .universal (bot DupocBot) (bot CupodBot) (some (.D, .C))

* `plays me opp a`: the arithmetized evaluator, given enough fuel, returns the action `a` for
  `me` facing `opp` — the engine's `play`, on program CODES (`ℕ`).
* `diverges me opp`: no fuel returns anything (the engine's `none`; Mirror facing Mirror).
* `OutcomeAtA L R r`: the pair, both sides.
* `OutcomeSpecA regime L R r`: quantified over the budget like the engine's `OutcomeSpec` —
  `nobudget` (closed bots), `universal` (every `k`), `eventual` (`∃ k₀, ∀ k > k₀`). The regime
  type IS the engine's `PD.BudgetRegime`. Fuel is existential here (`∃ n`), which by fuel
  monotonicity (`EvalGraph.mono_le`) is the same as the engine's cofinite pad.
* `bot P` / `const P`: the engine's bots as budget-indexed codes, through `progCode`.
* `□[k] φ`: the box, `LenBox TAct k φ` — the notation `□_k σ` of the notes (`ArithS.Notation`).

The per-left-bot files `Outcome/Matrix/<L>.lean` state every cell of the ledger
(`Research/Notes/ROUTE_B_CENSUS.md`, "S' status per cell") in this form, each proved from the
method-named theorem of `Cells/` (`snd_…`, `pos_…`, `loeb_…`, `khat_…`, `sf_…`) that carries
the mathematics. Nothing here proves anything new; it is the reading layer.
-/

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus
open LAct

/-! ### Plays and outcomes on codes -/

/-- `me` facing `opp` plays the action `a`: some fuel returns it. -/
def plays (me opp : ℕ) (a : PD.Action) : Prop := ∃ n, EvalGraph n me opp me (actCode a)

/-- `me` facing `opp` returns nothing at any fuel (the engine's `none`). -/
def diverges (me opp : ℕ) : Prop := ∀ n a, ¬ EvalGraph n me opp me a

/-- A play is unique: two fuels agree (`EvalGraph.unique'`). -/
theorem plays_unique {me opp : ℕ} {a b : PD.Action} (ha : plays me opp a) (hb : plays me opp b) : a = b := by
  obtain ⟨n, hn⟩ := ha; obtain ⟨m, hm⟩ := hb
  have := EvalGraph.unique' hn hm
  cases a <;> cases b <;> simp [actCode] at this ⊢

theorem plays_of_evalGraph {n me opp : ℕ} {a : PD.Action} (h : EvalGraph n me opp me (actCode a)) :
    plays me opp a := ⟨n, h⟩

/-- The pair: `L` facing `R` plays `a`, `R` facing `L` plays `b`; or both diverge. -/
def OutcomeAtA (L R : ℕ) : Option PD.Outcome → Prop
  | some (a, b) => plays L R a ∧ plays R L b
  | none => diverges L R ∧ diverges R L

/-- **The canonical outcome statement of PA-`S'`** — the engine's `OutcomeSpec`, on codes. -/
def OutcomeSpecA (b : PD.BudgetRegime) (L R : ℕ → ℕ) (r : Option PD.Outcome) : Prop :=
  match b with
  | .nobudget => OutcomeAtA (L 0) (R 0) r
  | .universal => ∀ k, OutcomeAtA (L k) (R k) r
  | .eventual => ∃ k₀, ∀ k, k₀ < k → OutcomeAtA (L k) (R k) r

/-- An engine bot with a budget, as a budget-indexed code. -/
noncomputable abbrev bot (P : ℕ → PD.Prog) : ℕ → ℕ := fun k ↦ progCode (P k)

/-- A closed engine bot, as a (constant) budget-indexed code. -/
noncomputable abbrev const (P : PD.Prog) : ℕ → ℕ := fun _ ↦ progCode P

/-! ### Constructors, from the shapes the cell theorems have -/

theorem OutcomeAtA.of_evalGraph {n m L R : ℕ} {a b : PD.Action}
    (h : EvalGraph n L R L (actCode a) ∧ EvalGraph m R L R (actCode b)) :
    OutcomeAtA L R (some (a, b)) := ⟨⟨n, h.1⟩, ⟨m, h.2⟩⟩

theorem OutcomeAtA.of_evalGraph₂ {n m L R : ℕ} {a b : PD.Action}
    (h₁ : EvalGraph n L R L (actCode a)) (h₂ : EvalGraph m R L R (actCode b)) :
    OutcomeAtA L R (some (a, b)) := ⟨⟨n, h₁⟩, ⟨m, h₂⟩⟩

theorem OutcomeSpecA.nobudget_of {L R : ℕ → ℕ} {r : Option PD.Outcome} (h : OutcomeAtA (L 0) (R 0) r) :
    OutcomeSpecA .nobudget L R r := h

theorem OutcomeSpecA.universal_of {L R : ℕ → ℕ} {r : Option PD.Outcome} (h : ∀ k, OutcomeAtA (L k) (R k) r) :
    OutcomeSpecA .universal L R r := h

theorem OutcomeSpecA.eventual_of {L R : ℕ → ℕ} {r : Option PD.Outcome}
    (h : ∃ k₀, ∀ k, k₀ < k → OutcomeAtA (L k) (R k) r) : OutcomeSpecA .eventual L R r := h

/-- A universal statement is in particular eventual. -/
theorem OutcomeSpecA.eventual_of_universal {L R : ℕ → ℕ} {r : Option PD.Outcome}
    (h : OutcomeSpecA .universal L R r) : OutcomeSpecA .eventual L R r := ⟨0, fun k _ ↦ h k⟩

/-- Two eventual one-sided facts make an eventual cell. -/
theorem OutcomeSpecA.eventual_of₂ {L R : ℕ → ℕ} {a b : PD.Action} {n m : ℕ}
    (h₁ : ∃ k₀, ∀ k, k₀ < k → EvalGraph n (L k) (R k) (L k) (actCode a))
    (h₂ : ∃ k₀, ∀ k, k₀ < k → EvalGraph m (R k) (L k) (R k) (actCode b)) :
    OutcomeSpecA .eventual L R (some (a, b)) := by
  obtain ⟨k₁, e₁⟩ := h₁; obtain ⟨k₂, e₂⟩ := h₂
  exact ⟨k₁ + k₂, fun k hk ↦ ⟨⟨n, e₁ k (by omega)⟩, ⟨m, e₂ k (by omega)⟩⟩⟩

/-- Two universal one-sided facts make a universal cell. -/
theorem OutcomeSpecA.universal_of₂ {L R : ℕ → ℕ} {a b : PD.Action} {n m : ℕ}
    (h₁ : ∀ k, EvalGraph n (L k) (R k) (L k) (actCode a))
    (h₂ : ∀ k, EvalGraph m (R k) (L k) (R k) (actCode b)) :
    OutcomeSpecA .universal L R (some (a, b)) :=
  fun k ↦ ⟨⟨n, h₁ k⟩, ⟨m, h₂ k⟩⟩

/-- The action literals the older cell theorems use. -/
@[simp] lemma actCode_C : actCode .C = 0 := rfl
@[simp] lemma actCode_D : actCode .D = 1 := rfl

end ArithS
