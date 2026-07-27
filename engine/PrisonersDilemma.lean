-- This module serves as the root of the `PrisonersDilemma` library:
-- the agent language, the proof system, the zoo, and the outcome theorems.
-- The decidability metatheory (T31…T54) is a separate lake target,
-- `Metatheory`, rooted at `PrisonersDilemma.Decidability`.
import PrisonersDilemma.Theorems.CooperateBot.Helpers
import PrisonersDilemma.Theorems.CooperateBot.vs_DefectBot
import PrisonersDilemma.Theorems.CooperateBot.vs_CooperateBot

import PrisonersDilemma.Theorems.CupodBot.Helpers
import PrisonersDilemma.Theorems.CupodBot.vs_CooperateBot
import PrisonersDilemma.Theorems.CupodBot.vs_DefectBot
import PrisonersDilemma.Theorems.CupodBot.vs_CupodBot
import PrisonersDilemma.Theorems.CupodBot.vs_TitForTatBot
import PrisonersDilemma.Theorems.CupodBot.vs_DBot
import PrisonersDilemma.Theorems.CupodBot.vs_OBot
import PrisonersDilemma.Theorems.CupodBot.vs_EBot
import PrisonersDilemma.Theorems.CupodBot.vs_MirrorBot

import PrisonersDilemma.Theorems.CupodTrollBot.Helpers
import PrisonersDilemma.Theorems.CupodTrollBot.vs_CupodBot
import PrisonersDilemma.Theorems.CupodTrollBot.vs_CupodTrollBot
import PrisonersDilemma.Theorems.CupodTrollBot.vs_CooperateBot
import PrisonersDilemma.Theorems.CupodTrollBot.vs_DefectBot
import PrisonersDilemma.Theorems.CupodTrollBot.vs_TitForTatBot
import PrisonersDilemma.Theorems.CupodTrollBot.vs_DBot
import PrisonersDilemma.Theorems.CupodTrollBot.vs_OBot
import PrisonersDilemma.Theorems.CupodTrollBot.vs_MirrorBot
import PrisonersDilemma.Theorems.CupodTrollBot.vs_EBot
import PrisonersDilemma.Theorems.CupodTrollBot.vs_DupocBot

import PrisonersDilemma.Theorems.DBot.Helpers
import PrisonersDilemma.Theorems.DBot.vs_CooperateBot
import PrisonersDilemma.Theorems.DBot.vs_DefectBot
import PrisonersDilemma.Theorems.DBot.vs_DBot

import PrisonersDilemma.Theorems.DefectBot.Helpers
import PrisonersDilemma.Theorems.DefectBot.vs_DefectBot

import PrisonersDilemma.Theorems.DupocBot.Helpers
import PrisonersDilemma.Theorems.DupocBot.vs_DefectBot
import PrisonersDilemma.Theorems.DupocBot.vs_CooperateBot
import PrisonersDilemma.Theorems.DupocBot.vs_DBot
import PrisonersDilemma.Theorems.DupocBot.vs_OBot
import PrisonersDilemma.Theorems.DupocBot.vs_TitForTatBot
import PrisonersDilemma.Theorems.DupocBot.vs_EBot
import PrisonersDilemma.Theorems.DupocBot.vs_DupocBot
import PrisonersDilemma.Theorems.DupocBot.vs_MirrorBot

import PrisonersDilemma.Theorems.EBot.Helpers
import PrisonersDilemma.Theorems.EBot.vs_CooperateBot
import PrisonersDilemma.Theorems.EBot.vs_DefectBot
import PrisonersDilemma.Theorems.EBot.vs_DBot
import PrisonersDilemma.Theorems.EBot.vs_TitForTatBot
import PrisonersDilemma.Theorems.EBot.vs_OBot
import PrisonersDilemma.Theorems.EBot.vs_MirrorBot
import PrisonersDilemma.Theorems.EBot.vs_EBot

import PrisonersDilemma.Theorems.MirrorBot.Helpers
import PrisonersDilemma.Theorems.MirrorBot.vs_CooperateBot
import PrisonersDilemma.Theorems.MirrorBot.vs_DefectBot
import PrisonersDilemma.Theorems.MirrorBot.vs_DBot
import PrisonersDilemma.Theorems.MirrorBot.vs_OBot
import PrisonersDilemma.Theorems.MirrorBot.vs_TitForTatBot
import PrisonersDilemma.Theorems.MirrorBot.vs_MirrorBot

import PrisonersDilemma.Theorems.OBot.Helpers
import PrisonersDilemma.Theorems.OBot.vs_CooperateBot
import PrisonersDilemma.Theorems.OBot.vs_DefectBot
import PrisonersDilemma.Theorems.OBot.vs_TitForTatBot
import PrisonersDilemma.Theorems.OBot.vs_DBot
import PrisonersDilemma.Theorems.OBot.vs_OBot

import PrisonersDilemma.Theorems.TitForTatBot.Helpers
import PrisonersDilemma.Theorems.TitForTatBot.vs_CooperateBot
import PrisonersDilemma.Theorems.TitForTatBot.vs_DefectBot
import PrisonersDilemma.Theorems.TitForTatBot.vs_TitForTatBot
import PrisonersDilemma.Theorems.TitForTatBot.vs_DBot

import PrisonersDilemma.Theorems.CIMCIC.vs_CooperateBot
import PrisonersDilemma.Theorems.CIMCIC.vs_DBot
import PrisonersDilemma.Theorems.CIMCIC.vs_DefectBot
import PrisonersDilemma.Theorems.CIMCIC.vs_EBot
import PrisonersDilemma.Theorems.CIMCIC.vs_TitForTatBot

import PrisonersDilemma.Theorems.DIMCID.vs_CooperateBot
import PrisonersDilemma.Theorems.DIMCID.vs_DefectBot

import PrisonersDilemma.Theorems.JustBot.Helpers
import PrisonersDilemma.Theorems.JustBot.vs_CooperateBot
import PrisonersDilemma.Theorems.JustBot.vs_CupodTrollBot
import PrisonersDilemma.Theorems.JustBot.vs_DBot
import PrisonersDilemma.Theorems.JustBot.vs_DefectBot
import PrisonersDilemma.Theorems.JustBot.vs_DupocBot
import PrisonersDilemma.Theorems.JustBot.vs_EBot
import PrisonersDilemma.Theorems.JustBot.vs_JustBot
import PrisonersDilemma.Theorems.JustBot.vs_OBot
import PrisonersDilemma.Theorems.JustBot.vs_PrudentBot
import PrisonersDilemma.Theorems.JustBot.vs_TitForTatBot

import PrisonersDilemma.Theorems.PrudentBot.Helpers
import PrisonersDilemma.Theorems.PrudentBot.vs_CooperateBot
import PrisonersDilemma.Theorems.PrudentBot.vs_CupodTrollBot
import PrisonersDilemma.Theorems.PrudentBot.vs_DBot
import PrisonersDilemma.Theorems.PrudentBot.vs_DefectBot
import PrisonersDilemma.Theorems.PrudentBot.vs_DupocBot
import PrisonersDilemma.Theorems.PrudentBot.vs_EBot
import PrisonersDilemma.Theorems.PrudentBot.vs_MirrorBot
import PrisonersDilemma.Theorems.PrudentBot.vs_OBot
import PrisonersDilemma.Theorems.PrudentBot.vs_PrudentBot
import PrisonersDilemma.Theorems.PrudentBot.vs_TitForTatBot

import PrisonersDilemma.Theorems.LlmGenerations.LlmLemmas
