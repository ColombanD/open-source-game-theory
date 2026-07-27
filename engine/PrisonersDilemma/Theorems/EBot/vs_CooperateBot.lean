import PrisonersDilemma.Bots.EBot
import PrisonersDilemma.Bots.OBot
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Bots.DBot
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.Theorems.DBot.Helpers
import PrisonersDilemma.Theorems.DBot.vs_CooperateBot
import PrisonersDilemma.Theorems.DBot.vs_DBot
import PrisonersDilemma.Theorems.DBot.vs_DefectBot
import PrisonersDilemma.Theorems.OBot.Helpers
import PrisonersDilemma.Theorems.OBot.vs_CooperateBot
import PrisonersDilemma.Theorems.OBot.vs_DBot
import PrisonersDilemma.Theorems.OBot.vs_DefectBot
import PrisonersDilemma.Theorems.OBot.vs_OBot
import PrisonersDilemma.Theorems.OBot.vs_TitForTatBot
import PrisonersDilemma.Theorems.TitForTatBot.Helpers
import PrisonersDilemma.Theorems.TitForTatBot.vs_CooperateBot
import PrisonersDilemma.Theorems.TitForTatBot.vs_DBot
import PrisonersDilemma.Theorems.TitForTatBot.vs_DefectBot
import PrisonersDilemma.Theorems.TitForTatBot.vs_TitForTatBot
import PrisonersDilemma.Theorems.MirrorBot.Helpers
import PrisonersDilemma.Theorems.MirrorBot.vs_CooperateBot
import PrisonersDilemma.Theorems.MirrorBot.vs_DBot
import PrisonersDilemma.Theorems.MirrorBot.vs_DefectBot
import PrisonersDilemma.Theorems.MirrorBot.vs_MirrorBot
import PrisonersDilemma.Theorems.MirrorBot.vs_OBot
import PrisonersDilemma.Theorems.MirrorBot.vs_TitForTatBot
import PrisonersDilemma.Theorems.EBot.Helpers


open PD.Bots
namespace PD.Theorems
theorem outcome_EBot_vs_CooperateBot (fuel : Nat):
    outcome (fuel + 3) EBot CooperateBot = some (.D, .C) := by
    have hA : play (fuel + 3) EBot CooperateBot = some .D := EBot_plays_D_against_CooperateBot (fuel)
    have hB : play (fuel + 3) CooperateBot EBot = some .C := rfl
    exact outcome_of_plays _ _ _ _ _ hA hB

end PD.Theorems
