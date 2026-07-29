import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Bots.LlmGenerations.GuardianBot
import PrisonersDilemma.Bots.MirrorBot
import PrisonersDilemma.Decidability.T31EngineDecider

open PD PD.Bots PD.T31

/-! # Tier-0 certified outcomes — GuardianBot

Machine-generated from the deterministic pre-pass (prepass2.jsonl, 2026-07-29).
Each statement is the strict concrete-fuel outcome template; each proof lifts a
computable `outcomeG (guardFastN k)` verdict to the classical `outcome` via
`outcomeG_sound` — the `by decide` re-runs the evaluation inside the kernel.
NOT yet wired into any lake target (Metatheory-side: imports T31EngineDecider). -/

set_option maxHeartbeats 1000000

namespace PD.T31.CertifiedOutcomes

theorem outcome_GuardianBot_vs_CooperateBot_k2 :
    outcome 64 (GuardianBot 2) (CooperateBot) = some (.C, .C) :=
  outcomeG_sound (guardFastN 2) (guardFastN_sound 2) 64 _ _ _ (by decide)

theorem outcome_GuardianBot_vs_DefectBot_k2 :
    outcome 64 (GuardianBot 2) (DefectBot) = some (.D, .D) :=
  outcomeG_sound (guardFastN 2) (guardFastN_sound 2) 64 _ _ _ (by decide)

theorem outcome_GuardianBot_vs_MirrorBot_k4 :
    outcome 64 (GuardianBot 4) (MirrorBot) = some (.C, .C) :=
  outcomeG_sound (guardFastN 4) (guardFastN_sound 4) 64 _ _ _ (by decide)

end PD.T31.CertifiedOutcomes
