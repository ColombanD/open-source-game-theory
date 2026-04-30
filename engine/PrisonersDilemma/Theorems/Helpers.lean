import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics

open PDNew

namespace PDNew.Theorems

theorem play_from_eval (fuel : Nat) (me opponent : Prog) (a : Action)
    (hEval : eval fuel me opponent me = some a) :
    play fuel me opponent = some a := by
  simpa [play] using hEval

/--
Generic one-step helper for `ite` programs: if `me` is an `ite` and you know
the guard value at fuel `fuel + n`, this theorem rewrites
`play (fuel + n + 1) me opponent` to the corresponding branch evaluation.
If guardAct == test, then use p as body, else use q
-/
theorem play_ite_from_guard
    (fuel n : Nat)
    (me opponent guard p q : Prog)
    (test guardAct : Action)
    (hMe : me = .ite guard test p q)
    (hGuard : eval (fuel + n) me opponent guard = some guardAct) :
    play (fuel + n + 1) me opponent =
      (if guardAct == test
        then eval (fuel + n) me opponent p
        else eval (fuel + n) me opponent q) := by
  have hGuard' :
      eval (fuel + n) (.ite guard test p q) opponent guard = some guardAct := by
    simpa [hMe] using hGuard
  rw [hMe]
  unfold play
  rw [show eval (fuel + n + 1)
          (.ite guard test p q)
          opponent
          (.ite guard test p q)
        =
          (do
            let r ← eval (fuel + n) (.ite guard test p q) opponent guard
            if r == test then
              eval (fuel + n) (.ite guard test p q) opponent p
            else
              eval (fuel + n) (.ite guard test p q) opponent q) by
        rfl]
  rw [hGuard']
  simp

/--
`eval`-level twin of `play_ite_from_guard`: given the guard's value, peel off
one layer of an `ite` body without requiring the body to equal `me`. Useful
for tracing nested `ite` chains (EBot's three-guard structure, etc.).
-/
theorem eval_ite_from_guard
    (fuel : Nat) (me opponent guard p q : Prog)
    (test guardAct : Action)
    (hGuard : eval fuel me opponent guard = some guardAct) :
    eval (fuel + 1) me opponent (.ite guard test p q) =
      (if guardAct == test
        then eval fuel me opponent p
        else eval fuel me opponent q) := by
  rw [show eval (fuel + 1) me opponent (.ite guard test p q)
        = (do let r ← eval fuel me opponent guard
              if r == test then eval fuel me opponent p
              else eval fuel me opponent q)
        by rfl]
  rw [hGuard]
  simp

/--
A `(.sim .opp (.bot z))` guard reduces to `play fuel opp (.bot z)`: the outer
`subst` sends `.opp` to `opp` and leaves `.bot z` untouched, so the simulation
is exactly opp running against `.bot z`. Hypothesis at `fuel`, conclusion at
`fuel + 1`.
-/
theorem eval_sim_opp_bot_of_play
    (fuel : Nat) (me opponent z : Prog) (a : Action)
    (h : play fuel opponent (.bot z) = some a) :
    eval (fuel + 1) me opponent (.sim .opp (.bot z)) = some a := by
  show eval fuel opponent (.bot z) opponent = some a
  exact h

/-- Package two `play` results into an `outcome`. -/
theorem outcome_of_plays
    (fuel : Nat) (p q : Prog) (a b : Action)
    (hA : play fuel p q = some a) (hB : play fuel q p = some b) :
    outcome fuel p q = some (a, b) := by
  simp [outcome, hA, hB]

end PDNew.Theorems
