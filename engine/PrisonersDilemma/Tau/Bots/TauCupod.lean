import PrisonersDilemma.Tau.Roster

/-!
# τ(CupodBot), the suspicious cooperator

Base `CupodBot k = .search k (.plays .opp .self D) (const D) (const C)`: punish iff
the opponent provably defects against me; trust otherwise. τ(Dupoc) with the
polarity flipped — same self-probe, proving DEFECTION and firing D.
-/

namespace PD.Tau

/-- τ(CupodBot): provably defects against me? then D, else C. -/
def tauCupodSpec : Spec Tmpl :=
  .search .prove .self .D (.const .D) (.const .C)

end PD.Tau
