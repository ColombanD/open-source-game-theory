import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Theorems.CooperateBot.Helpers

open PD
open PD.Bots

namespace PD.Theorems
-- CooperateBot vs itself: mutual cooperation, (C, C).
theorem outcome_CooperateBot_vs_CooperateBot (n : Nat) :
    outcome (n+1) CooperateBot CooperateBot = some (.C, .C) := by
  unfold outcome
  rw [play_CooperateBot]
  rfl

end PD.Theorems
