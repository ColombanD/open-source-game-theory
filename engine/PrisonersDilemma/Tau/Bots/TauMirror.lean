import PrisonersDilemma.Tau.Roster

/-!
# τ(MirrorBot), the forwarder

Base `MirrorBot = .sim .opp .self`: play whatever the opponent plays against me.
The lift is the bare `.sim .self` — no test, no branches. Its diagonal compiles
to `.sim .self .self`, base MirrorBot's self-play, which does not terminate; that
is the one zoo cell with no play, and why τ(Mirror)'s phase has a `none` regime.
-/

namespace PD.Tau

/-- τ(MirrorBot): copy the hypothesis's play against me. -/
def tauMirrorSpec : Spec Tmpl := .sim .self

end PD.Tau
