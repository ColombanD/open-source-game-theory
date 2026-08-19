import PrisonersDilemma.Tau.Roster

/-!
# TauEBot — the exploiter, lifted

TWO `prove` stages — base EBot's cascade, and the bot the 2026-08-13 retraction was
about:

1. exploit check: "would they cooperate even with a DEFECTOR? then I defect" (fire D
   — the only D-firing stage in the zoo);
2. reciprocity check: "would they cooperate with a COOPERATOR? then C"; else D.

The vote never sees the stages separately: the whole cascade runs per hypothesis and
only its final action is counted — which is exactly the corrected reading (the
retracted "crowd-exploiter" put a θ-threshold inside each stage instead, and was a
different agent). Consequences, all theorems: its boundary is ONE-SIDED,
`θ ≤ wTs + wTp + wL` (no window; it excludes `w .coop` — the weight it exploits);
every one of its cooperations is FLOOR-priced (reached behind the failed exploit
probe), which is what TauDupoc's probe honestly reads as 0; and its SELF-bit is 0 —
base EBot's Mirror-branch escape is not `.opp`-free-liftable, the one recorded lift
divergence from Def 3 (the whitelisted cell of the Python coincidence
certification).
-/

namespace PD.Tau

/-- τ(EBot): "exploitable? then D; else reciprocates? then C; else D." -/
def tauEBotSpec : Spec Tmpl :=
  ⟨[⟨.prove, .name .defect, .D⟩, ⟨.prove, .name .coop, .C⟩], .D⟩

end PD.Tau
