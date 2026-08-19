import PrisonersDilemma.Tau.Roster

/-!
# TauTFTPf — tit-for-tat, the PROVER lift

One `prove` stage: search (within the budget) for a PROOF that the hypothesis
cooperates with the cooperator. One word away from `TauTFTSim` — `run` became
`prove` — which is the entire prover/behavioral distinction, visible as a one-field
diff in the spec. The prover read is floor-aware: a hypothesis whose cooperation is
true but priced above the budget reads 0 here while the behavioral twin reads 1
(no such cell exists on the δ_C column this bot consults, which is why the two TFTs
share their bit row at large k).
-/

namespace PD.Tau

/-- τ(TitForTatBot), prover: "prove they'd cooperate with a cooperator; then C;
    else D." -/
def tauTFTPfSpec : Spec Tmpl := ⟨[⟨.prove, .name .coop, .C, .C⟩], .D⟩

end PD.Tau
