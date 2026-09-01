import PrisonersDilemma.Tau.Bots.TauMaxConfidence

/-!
# MinConfidenceBot — the worst-case Löbian cooperator (native, 2026-09-01)

MaxConfidenceBot's C/D-transposition dual, the second native tau player. Same
per-hypothesis TEST (Dupoc's Löbian probe), the **MIN / worst-case aggregator**:

    MinConfidenceBot(w, θ) = C   iff   ∀ T, θ ≤ w T → (the T-instance, facing me, provably cooperates)

— it cooperates only when NO credible hypothesis fails the test: a single hypothesis
carrying at least θ of the signal on its own and provably defecting flips it to D.
Where MaxConfidenceBot is the ambiguity-averse OPTIMIST (one credible cooperator
suffices), this is the Gilboa–Schmeidler PESSIMIST (one credible defector vetoes).
Together with the lifts' `sum` these are the {expectation, best case, worst case}
aggregator family over one and the same test — the paper's aggregator ablation.

**Why it cannot be a lift** (`minconfidence_not_linear`,
`Tau/Theorems/TauMinConfidence/Phase.lean`): a lift's play thresholds the C-MASS,
linear in the signal; a max over the D-slots is not. Two defect-hypotheses split
vs concentrated separate it from every threshold-of-mass player: it plays D, C, D
on `2·δ_defect`, `δ_defect + δ_dbot`, `2·δ_dbot` at θ = 2, and the middle signal is
the average of the outer two.

**Its test is Dupoc's**, so `tauMinConfidenceSpec = tauDupocSpec` and in the
hypothesis role it is Dupoc (`Zoo.lean`'s `inst_minconfidence_eq_dupoc` bridges, all
`rfl`). Its entangled pairs — with `.dupoc` and with `.maxconfidence` — compile to the
SAME symmetric `.sys` term `cfdSys` the maxconfidence × dupoc pair produced (`sysGo`
never reads the template name for this spec), so the mutual-Löb closure is
`TauMaxConfidence/Helpers.lean`'s, consumed by `rfl`, and this bot adds NO new proof
obligations at the instance level. Its player is `MinConfidenceBotZ` (`Zoo.lean`),
the `minPlayer` chain over the same decision vector.

The boundary convention: an entry is credible at weight ≥ θ, and a weightless entry
never blocks (`Tau/Vote.lean`'s credibility gate) — the app's `play.min_mass` maps
its α dial by `θ_credible ↔ 1 − α`, with `≥` on the mass exactly as every player.
-/

namespace PD.Tau

/-- MinConfidenceBot's per-hypothesis TEST — Dupoc's: provably cooperates with me?
    then C, else D. (Definitionally `tauDupocSpec`; spelled out so the file reads
    alone.) -/
def tauMinConfidenceSpec : Spec Tmpl :=
  .search .prove .self .C (.const .C) (.const .D)

theorem tauMinConfidenceSpec_eq_dupoc : tauMinConfidenceSpec = tauDupocSpec := rfl

theorem tauMinConfidenceSpec_eq_maxconfidence :
    tauMinConfidenceSpec = tauMaxConfidenceSpec := rfl

end PD.Tau
