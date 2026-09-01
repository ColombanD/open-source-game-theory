import PrisonersDilemma.Tau.Bots.TauDupoc

/-!
# MaxConfidenceBot — the ambiguity-averse Löbian cooperator (native, 2026-08-27)

The first tau player that is NOT the lift of a base bot. A tau player is a pair
(per-hypothesis TEST, AGGREGATOR): the test is a `Spec` — what the player decides at
point mass on each hypothesis — and the aggregator turns the weighted per-hypothesis
decisions into one play. Every lift `TauBotZ` aggregates by `sum ≥ θ` (the C-mass of
the signal reaches the threshold). MaxConfidenceBot aggregates by **`max ≥ θ`**:

    MaxConfidenceBot(w, θ) = C   iff   ∃ T, θ ≤ w T ∧ (the T-instance, facing me, provably cooperates)

— it cooperates only when it is CONFIDENT who it is facing: some single hypothesis
must carry at least θ of the signal on its own AND pass Dupoc's Löbian test. The
lifts are risk-neutral in expectation; this bot is ambiguity-averse. It makes the
headline question — how much transparency does Löbian cooperation need? — literal:
its cooperation with τ(Dupoc) switches off exactly when the channel's confidence on a
Löb-cooperating hypothesis drops below θ, however high the expected cooperation.

**Why it cannot be a lift** (`maxconfidence_not_linear`, `Tau/Theorems/TauMaxConfidence/
Phase.lean`): a lift's play is a function of the C-MASS `Σ w T · [row T = C]`, LINEAR
in the signal; the max is not. Three signals separate it from every threshold-of-mass
player on every row.

**Its test is Dupoc's**, so `tauMaxConfidenceSpec = tauDupocSpec` and in the hypothesis
role it is Dupoc (`Zoo.lean`'s `inst_maxconfidence_eq_dupoc` bridges, all `rfl`). The
one new cell is `maxconfidence × dupoc`: two Dupoc-spec self-probers, a symmetric `.sys`
system closed by mutual Löb (`TauMaxConfidence/Helpers.lean`). Its player is
`MaxConfidenceBotZ` (`Zoo.lean`), the `maxPlayer` chain over the same decision vector
`TauBotZ k .maxconfidence` would sum.

The circular reading "cooperate iff there is a heavy hypothesis I'd cooperate with"
is NOT this bot: at point mass the weight condition is vacuous and "I'd cooperate"
would be a fixpoint with no grounding. The test must be a concrete probe of the
hypothesis — here Dupoc's — and that choice is what fixes the point-mass collapse.
-/

namespace PD.Tau

/-- MaxConfidenceBot's per-hypothesis TEST — Dupoc's: provably cooperates with me? then C,
    else D. (Definitionally `tauDupocSpec`; spelled out so the file reads alone.) -/
def tauMaxConfidenceSpec : Spec Tmpl :=
  .search .prove .self .C (.const .C) (.const .D)

theorem tauMaxConfidenceSpec_eq_dupoc : tauMaxConfidenceSpec = tauDupocSpec := rfl

end PD.Tau
