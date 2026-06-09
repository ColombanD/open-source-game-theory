import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Bots.DBot
import PrisonersDilemma.Bots.TitForTatBot
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Theorems.Helpers

open PD
open PD.Bots
namespace PD.Theorems

theorem llm_outcome_DBot_vs_TitForTatBot (n : Nat) :
    outcome (n+7) DBot TitForTatBot = some (.C, .D) := by
  -- DBot's guard: probe TitForTatBot against DefectBot → TitForTatBot plays D
  have hGuard1 : eval (n + 6) DBot TitForTatBot (.sim .opp (.bot DefectBot)) = some .D := by
    simp [eval, Prog.subst, TitForTatBot, DefectBot, CooperateBot]; decide
  have hA : play (n + 7) DBot TitForTatBot = some .C := by
    have hPlay := play_ite_from_guard
      n 6 DBot TitForTatBot (.sim .opp (.bot DefectBot))
      (.const Action.D) (.const Action.C)
      Action.C Action.D
      (by rfl) hGuard1
    simpa [eval] using hPlay
  -- TitForTatBot's guard: probe DBot against CooperateBot → DBot plays D
  have hGuard2 : eval (n + 6) TitForTatBot DBot (.sim .opp (.bot CooperateBot)) = some .D := by
    simp [eval, Prog.subst, DBot, DefectBot, CooperateBot]; decide
  have hB : play (n + 7) TitForTatBot DBot = some .D := by
    have hPlay := play_ite_from_guard
      n 6 TitForTatBot DBot (.sim .opp (.bot CooperateBot))
      (.const Action.C) (.const Action.D)
      Action.C Action.D
      (by rfl) hGuard2
    simpa [eval] using hPlay
  exact outcome_of_plays _ _ _ _ _ hA hB

end PD.Theorems
