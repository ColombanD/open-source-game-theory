import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Bots.CupodTrollBot
import PrisonersDilemma.Bots.DBot
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Bots.EBot
import PrisonersDilemma.Bots.LlmGenerations.CIMCIC
import PrisonersDilemma.Bots.LlmGenerations.DIMCID
import PrisonersDilemma.Bots.LlmGenerations.LegibleBot
import PrisonersDilemma.Bots.MirrorBot
import PrisonersDilemma.Bots.OBot
import PrisonersDilemma.Bots.TitForTatBot
import PrisonersDilemma.Decidability.T31EngineDecider

open PD PD.Bots PD.T31

/-! # Tier-0 certified outcomes — LegibleBot

Machine-generated from the deterministic pre-pass (prepass2.jsonl, 2026-07-29).
Each statement is the strict concrete-fuel outcome template; each proof lifts a
computable `outcomeG (guardFastN k)` verdict to the classical `outcome` via
`outcomeG_sound` — the `by decide` re-runs the evaluation inside the kernel.
NOT yet wired into any lake target (Metatheory-side: imports T31EngineDecider). -/

set_option maxHeartbeats 1000000

namespace PD.T31.CertifiedOutcomes

theorem outcome_LegibleBot_vs_CIMCIC_k2 :
    outcome 64 (LegibleBot 2 2) (CIMCIC 2) = some (.D, .D) :=
  outcomeG_sound (guardFastN 2) (guardFastN_sound 2) 64 _ _ _ (by decide)

theorem outcome_LegibleBot_vs_CooperateBot_k2 :
    outcome 64 (LegibleBot 2 2) (CooperateBot) = some (.D, .C) :=
  outcomeG_sound (guardFastN 2) (guardFastN_sound 2) 64 _ _ _ (by decide)

theorem outcome_LegibleBot_vs_CupodTrollBot_k2 :
    outcome 64 (LegibleBot 2 2) (CupodTrollBot 2) = some (.D, .C) :=
  outcomeG_sound (guardFastN 2) (guardFastN_sound 2) 64 _ _ _ (by decide)

theorem outcome_LegibleBot_vs_DBot_k2 :
    outcome 64 (LegibleBot 2 2) (DBot) = some (.D, .C) :=
  outcomeG_sound (guardFastN 2) (guardFastN_sound 2) 64 _ _ _ (by decide)

theorem outcome_LegibleBot_vs_DIMCID_k2 :
    outcome 64 (LegibleBot 2 2) (DIMCID 2) = some (.D, .C) :=
  outcomeG_sound (guardFastN 2) (guardFastN_sound 2) 64 _ _ _ (by decide)

theorem outcome_LegibleBot_vs_DefectBot_k2 :
    outcome 64 (LegibleBot 2 2) (DefectBot) = some (.D, .D) :=
  outcomeG_sound (guardFastN 2) (guardFastN_sound 2) 64 _ _ _ (by decide)

theorem outcome_LegibleBot_vs_EBot_k2 :
    outcome 64 (LegibleBot 2 2) (EBot) = some (.D, .D) :=
  outcomeG_sound (guardFastN 2) (guardFastN_sound 2) 64 _ _ _ (by decide)

theorem outcome_LegibleBot_vs_LegibleBot_k2 :
    outcome 64 (LegibleBot 2 2) (LegibleBot 2 2) = some (.D, .D) :=
  outcomeG_sound (guardFastN 2) (guardFastN_sound 2) 64 _ _ _ (by decide)

theorem outcome_LegibleBot_vs_MirrorBot_k2 :
    outcome 64 (LegibleBot 2 2) (MirrorBot) = some (.D, .D) :=
  outcomeG_sound (guardFastN 2) (guardFastN_sound 2) 64 _ _ _ (by decide)

theorem outcome_LegibleBot_vs_OBot_k2 :
    outcome 64 (LegibleBot 2 2) (OBot) = some (.D, .D) :=
  outcomeG_sound (guardFastN 2) (guardFastN_sound 2) 64 _ _ _ (by decide)

theorem outcome_LegibleBot_vs_TitForTatBot_k2 :
    outcome 64 (LegibleBot 2 2) (TitForTatBot) = some (.D, .D) :=
  outcomeG_sound (guardFastN 2) (guardFastN_sound 2) 64 _ _ _ (by decide)

end PD.T31.CertifiedOutcomes
