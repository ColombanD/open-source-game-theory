import PrisonersDilemmaNew.Program
import PrisonersDilemmaNew.Dynamics
import PrisonersDilemmaNew.Bots.DefectBot

open PDNew
open PDNew.Bots

namespace PDNew.Theorems

-- DefectBot always defects (with any fuel ≥ 1).
theorem play_DefectBot (n : Nat) (opponent : Prog) :
      play (n+1) DefectBot opponent = some .D := by
    unfold play eval DefectBot
    simp

-- The interpretation "DB plays C against q" is false.
-- This is the semantic content the soundness axiom will consume.
theorem interp_DefectBot_plays_C_false (q : Prog) :
    ¬ (Formula.plays DefectBot q .C).interp := by
  rintro ⟨n, hn⟩
  cases n with
  | zero   => simp [play, eval] at hn
  | succ m =>
      rw [play_DefectBot] at hn
      cases hn                -- some .D = some .C : impossible

-- DefectBot vs itself: mutual defection, (D, D).
theorem outcome_DefectBot_vs_DefectBot (n : Nat) :
    outcome (n+1) DefectBot DefectBot = some (.D, .D) := by
  unfold outcome
  rw [play_DefectBot]
  rfl

end PDNew.Theorems
