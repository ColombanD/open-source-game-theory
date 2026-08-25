import PrisonersDilemma.Tau.Roster

/-!
# τ(TitForTatBot), the BEHAVIORAL lift

Base `TitForTatBot = .ite (.sim .opp (.bot CooperateBot)) C (const C) (const D)`:
simulate the opponent against the cooperator and copy what it does. The lift keeps
the `.sim` modality: it sees TRUE plays and is blind to provability floors. Its
prover twin is `TauTFTPf` — the two differ by one node, `ite (sim …)` vs
`search .prove …`.
-/

namespace PD.Tau

/-- τ(TitForTatBot), behavioral: cooperates with the cooperator? then C, else D. -/
def tauTFTSimSpec : Spec Tmpl :=
  .ite (.sim (.name .coop)) .C (.const .C) (.const .D)

end PD.Tau
