import PrisonersDilemma.Tau.Roster

/-!
# τ(TitForTatBot), the PROVER lift

Same question as `TauTFTSim` — does the hypothesis cooperate with the cooperator?
— asked by proof search instead of simulation. A true but floor-priced cooperation
reads C behaviorally and D here; those cells are the prover-modality divergences
recorded in `app`'s whitelist.
-/

namespace PD.Tau

/-- τ(TitForTatBot), prover: provably cooperates with the cooperator? then C, else D. -/
def tauTFTPfSpec : Spec Tmpl :=
  .search .prove (.name .coop) .C (.const .C) (.const .D)

end PD.Tau
