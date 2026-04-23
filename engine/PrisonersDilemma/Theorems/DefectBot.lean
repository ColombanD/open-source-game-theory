import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Bots.DefectBot

open PDNew
open PDNew.Bots

namespace PDNew.Theorems

-- DefectBot always defects (with any fuel ≥ 1).
theorem play_DefectBot (n : Nat) (opponent : Prog) :
      play (n+1) DefectBot opponent = some .D := by
    unfold play eval DefectBot
    simp

-- The interpretation "DB plays D against q" is true.
-- This is the semantic content the completeness axiom will consume.
theorem interp_DefectBot_plays_D_true (q : Prog) :
    (Formula.plays DefectBot q .D).interp := by
  unfold Formula.interp
  exists 1

-- DefectBot vs itself: mutual defection, (D, D).
theorem outcome_DefectBot_vs_DefectBot (n : Nat) :
    outcome (n+1) DefectBot DefectBot = some (.D, .D) := by
  unfold outcome
  rw [play_DefectBot]
  rfl

end PDNew.Theorems
