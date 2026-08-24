import PrisonersDilemma.Tau.Roster

/-!
# TauGuardian — the norm enforcer, lifted

Base GuardianBot: "search for a proof that the opponent DEFECTS against
CooperateBot; if found, punish (D); else trust (C)" — third-party norm enforcement
from a default of trust, the inversion of JustBot's reward-based probe. One `prove`
stage with `test = .D` (the zoo's first prover of DEFECTION).

The consequence that makes it the most interesting addition: **Guardian's own
cooperation is NEVER provable within budget** — its C sits behind a FAILED search
(the punish-probe that found nothing), so every certificate pays the `search_f`
floor. Its bits in every prover's column are 0 while its TRUE plays are
cooperative: with Guardian in the zoo, the behavioral and prover TFT variants
finally separate ON THE α-AXIS (TauTFTSim counts `w .guardian` in its mass,
TauTFTPf does not) — the prover/behavioral split stops being budget-only.
-/

namespace PD.Tau

/-- τ(GuardianBot): "provably defects vs Coop? → D; else C." -/
def tauGuardianSpec : Spec Tmpl :=
  .search .prove (.name .coop) .D (.const .D) (.const .C)

end PD.Tau
