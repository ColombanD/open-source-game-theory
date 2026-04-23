import PrisonersDilemmaNew.Program
import PrisonersDilemmaNew.Dynamics

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

end PDNew.Theorems
