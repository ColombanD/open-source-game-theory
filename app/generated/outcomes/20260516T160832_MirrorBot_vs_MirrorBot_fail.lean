import PrisonersDilemma.Bots.MirrorBot

open PDNew
open PDNew.Bots
namespace PDNew.Theorems

/-- MirrorBot vs MirrorBot never terminates: both sides try to simulate the
    opponent against itself, recursing into the same configuration with one
    less unit of fuel. Hence `play` always returns `none`, and so does
    `outcome`. -/
theorem outcome_MirrorBot_MirrorBot_none (n : Nat) :
    outcome n MirrorBot MirrorBot = none := by
  have h : ∀ k, play k MirrorBot MirrorBot = none := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
        show eval (k+1) MirrorBot MirrorBot MirrorBot = none
        unfold MirrorBot
        simp [eval, Prog.subst]
        exact ih
  simp [outcome, h]

/-- Corollary: the requested theorem template
    `∀ n, outcome (n+FUEL) MirrorBot MirrorBot = some (L, R)`
    is unsatisfiable for every choice of FUEL, L, R. -/
example (FUEL : Nat) (L R : Action) :
    ¬ ∀ n, outcome (n + FUEL) MirrorBot MirrorBot = some (L, R) := by
  intro h
  have := h 0
  rw [outcome_MirrorBot_MirrorBot_none] at this
  cases this

end PDNew.Theorems
