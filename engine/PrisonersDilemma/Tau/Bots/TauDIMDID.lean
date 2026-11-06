import PrisonersDilemma.Tau.Roster

/-!
# τ(DIMDID), the C/D transposition of τ(CIMCIC)

Base `DIMDID k = .search k (.impl (.plays .self .opp D) (.plays .opp .self D)) (const D) (const C)`
(`Bots/DIMDID.lean`, 2026-10-13): "defect iff I can prove that my defection implies yours" —
`(CIMCIC k).transpose` by `rfl`. The lift is CIMCIC's spec with the test and the branches
transposed, so `inst (tauZoo k) .dimdid T = (inst (tauZoo k) .cimcic τT).transpose` whenever
the roster contains the transposed hypothesis `τT` (`Tau/Theorems/TauDIMDID/Helpers.lean`).

Added 2026-10-19 so that the paper's ladder zoo `body8+trolls+provers` has kernel rows in
PA-`S'`; the engine row is the twin the roster census demands.
-/

namespace PD.Tau

/-- τ(DIMDID): provably (I defect ⇒ you defect)? then D, else C. -/
def tauDIMDIDSpec : Spec Tmpl :=
  .search .proveImpl .self .D (.const .D) (.const .C)

end PD.Tau
