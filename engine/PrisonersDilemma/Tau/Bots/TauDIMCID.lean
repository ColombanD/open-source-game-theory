import PrisonersDilemma.Tau.Roster

/-!
# τ(DIMCID) — the conditional DEFECTOR, CIMCIC's polarity twin

Base `DIMCID k = .search k (.impl (.plays .self .opp C) (.plays .opp .self D))
(.const D) (.const C)`: "if I can prove that my cooperating would be met with
DEFECTION, defect; otherwise cooperate." The suspicious mirror of CIMCIC's
conditional cooperation — same implication guard, ASYMMETRIC consequent, which is
what `Mode.proveImplD` exists to express (`Tau/Spec.lean`).

**The FOURTH self-prober.** Its guard mentions both `.self` and `.opp`, so it
entangles with `dupoc`, `cupod` AND `cimcic` — four 2-cycles in the zoo, each a
2-member `.sys` system.

**Its diagonal is a real Löb fixpoint**, unlike CIMCIC's. After substitution the
guard reads "if I cooperate with myself, I defect against myself" — the two sides
name the SAME player at OPPOSITE actions, so `implRefl` does not apply. Bounded
Löb closes it on DEFECTION (the tau image of base `llm_outcome_DIMCID_vs_DIMCID
= (D, D)`): provable self-defection makes the guard true by `weakenImpl`, the
search fires, and the fire-action IS `D`. Self-fulfilling suspicion.
-/

open PD

namespace PD.Tau

/-- τ(DIMCID)'s spec: one `proveImplD` stage on the self-target, fire `D`,
    default `C`. -/
def tauDIMCIDSpec : Spec Tmpl :=
  .search .proveImplD .self .C (.const .D) (.const .C)

end PD.Tau
