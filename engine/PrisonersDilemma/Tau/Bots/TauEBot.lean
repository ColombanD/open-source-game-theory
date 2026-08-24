import PrisonersDilemma.Tau.Roster

/-!
# TauEBot — the exploiter, lifted

TWO `run` stages — the faithful modality of base EBot's cascade, whose branches are
`.sim` WATCHES (`.sim .opp (.bot DefectBot)` / `.sim .opp (.bot CooperateBot)`),
not proof searches:

1. exploit check: "would they cooperate even with a DEFECTOR? then I defect" (fire D
   — the only D-firing stage in the zoo);
2. reciprocity check: "would they cooperate with a COOPERATOR? then C"; else D.

**Modality corrected 2026-08-19.** The stages were `prove` from the original tau
layer (2026-08-11) through the Def-4 rebuild — a silent sim→search infidelity that
no zoo cell could see until GuardianBot arrived: Guardian's floor-priced cooperation
is visible to a sim and invisible to a prover, and the 9-zoo coincidence
certification flagged `(TauEBot, TauGuardian)` as `D` where base
`EBot vs GuardianBot` is `C`. With `run` stages the lift is behaviorally faithful
to base EBot's first two branches; the remaining recorded divergence is the
MIRROR-BRANCH TRUNCATION (base EBot's third branch sims MirrorBot, which is not
`.opp`-free-liftable), which keeps its SELF-bit 0 — the whitelisted cell of the
Python coincidence certification.

Consequences, all theorems: its boundary is ONE-SIDED, `θ ≤ eMass` (now INCLUDING
`w .guardian` — the behavioral read sees Guardian's true cooperation; still
excluding `w .coop`, the weight it exploits); and its cooperation with DUPOC is
floor-priced ONE LEVEL DOWN (stage 1 watches `inst .dupoc .defect`, whose D-play
certificate pays the embedded `search_f` floor), which is what TauDupoc's probe
honestly reads as 0 — the embedded-floor census in `Theorems/TauEBot/Helpers.lean`.
-/

namespace PD.Tau

/-- τ(EBot): "exploitable? then D; else reciprocates? then C; else D" — read by
    SIMULATION, base EBot's own modality. -/
def tauEBotSpec : Spec Tmpl :=
  ⟨[⟨.run, .name .defect, .C, .D⟩, ⟨.run, .name .coop, .C, .C⟩,
    -- the THIRD stage, restored 2026-08-24 once `.mirror` entered the roster:
    -- base EBot's last branch sims MirrorBot, and until then this stage could
    -- not be written at all — the sole content of the former
    -- `(TauEBot, TauEBot)` whitelist entry.
    ⟨.run, .name .mirror, .C, .C⟩], .D⟩

end PD.Tau
