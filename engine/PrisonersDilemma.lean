-- This module serves as the root of the `PrisonersDilemma` library:
-- the agent language, the proof system, the zoo, and the outcome theorems.
-- The decidability metatheory (T31…T54) is a separate lake target,
-- `Metatheory`, rooted at `PrisonersDilemma.Decidability`.
import PrisonersDilemma.Theorems.CupodBot
import PrisonersDilemma.Theorems.CooperateBot
import PrisonersDilemma.Theorems.DefectBot
import PrisonersDilemma.Theorems.DupocBot
import PrisonersDilemma.Theorems.EBot
import PrisonersDilemma.Theorems.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Theorems.TitForTatBot
import PrisonersDilemma.Theorems.OBot
import PrisonersDilemma.Theorems.MirrorBot
import PrisonersDilemma.Theorems.DBot
import PrisonersDilemma.Theorems.CupodTrollBot
import PrisonersDilemma.Theorems.LlmGenerations
