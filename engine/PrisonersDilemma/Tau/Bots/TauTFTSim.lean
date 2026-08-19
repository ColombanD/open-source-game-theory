import PrisonersDilemma.Tau.Roster

/-!
# TauTFTSim — tit-for-tat, the BEHAVIORAL lift

One `run` stage: SIMULATE the hypothesis against the cooperator and copy what it
does. Base TitForTatBot's `.sim .opp (.bot CooperateBot)` guard, lifted verbatim.
Because the read is behavioral it sees TRUE plays and is blind to provability
floors; its α-boundary coincides with the prover variant's (`TauTFTPf`) at large k —
the prover/behavioral split is a BUDGET gap, not an α gap — but it reaches that
boundary at a far smaller budget (no proof search anywhere in its instances).
-/

namespace PD.Tau

/-- τ(TitForTatBot), behavioral: "run them against a cooperator; if they cooperate,
    C; else D." -/
def tauTFTSimSpec : Spec Tmpl := ⟨[⟨.run, .name .coop, .C⟩], .D⟩

end PD.Tau
