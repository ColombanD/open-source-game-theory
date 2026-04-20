-- This module serves as the root of the `PrisonersDilemmaNew` library.
-- Import modules here that should be built as part of the library.
import PrisonersDilemmaNew.Game

-- Core models
import PrisonersDilemmaNew.Models.Bot

-- Strategies
import PrisonersDilemmaNew.Models.Bots.CooperateBot
import PrisonersDilemmaNew.Models.Bots.DBot

-- Predicates and proofs
import PrisonersDilemmaNew.Predicates.OpponentBehavior
import PrisonersDilemmaNew.Proofs.DBotBehavior
