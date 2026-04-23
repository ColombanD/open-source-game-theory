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

-- The interpretation "DB plays D against q" is true.
-- This is the semantic content the completeness axiom will consume.
theorem interp_DefectBot_plays_D_true (q : Prog) :
    (Formula.plays DefectBot q .D).interp := by
  unfold Formula.interp
  exists 1

end PDNew.Theorems
