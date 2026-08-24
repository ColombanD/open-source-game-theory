import PrisonersDilemma.Tau.Roster

/-!
# TauJust — the third-party prover, lifted

Base JustBot: "search for a proof that the opponent cooperates with DUPOC; then C,
else D" — norm-based reciprocity, judged against a fixed third party rather than
against me. One `prove` stage with a NAME target (the frozen `.bot DupocBot` of the
base code becomes `.name .dupoc`), so JustBot lifts with no quine and no new column:
it consults exactly the δ_L column TauDupoc already reads ("does T, seeing Dupoc,
cooperate?"). Two cells inherited from that column are the interesting ones: its
DUPOC bit is the Löb quine's (so its phase theorem is Löb-GATED like TauDupoc's),
and its EBot/Guardian bits are floors.
-/

namespace PD.Tau

/-- τ(JustBot): "prove they'd cooperate with Dupoc; then C; else D." -/
def tauJustSpec : Spec Tmpl :=
  .search .prove (.name .dupoc) .C (.const .C) (.const .D)

end PD.Tau
