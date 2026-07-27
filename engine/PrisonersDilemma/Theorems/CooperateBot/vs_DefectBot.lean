import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Theorems.DefectBot
import PrisonersDilemma.Theorems.CooperateBot.Helpers

open PD
open PD.Bots

namespace PD.Theorems
-- CooperateBot vs DefectBot: the cooperator is exploited, (C, D).
theorem outcome_CooperateBot_vs_DefectBot (n : Nat) :
    outcome (n+1) CooperateBot DefectBot = some (.C, .D) := by
  unfold outcome
  rw [play_CooperateBot, play_DefectBot]
  rfl

end PD.Theorems
