import PrisonersDilemma.Tau.Theorems.Columns

/-!
# τ(CupodBot)'s phase — the suspicious cooperator, and the zoo's first OPEN cell.

Cupod trusts by default and punishes only what it can convict. On this zoo it
convicts the defector, OBot (which truly defects on it) and itself (the Löbian
self-defection, `ps_probeD_inst_cupod_quine`) — and its cell at **Dupoc is
genuinely OPEN**: the two are an entangled pair whose 2-cycle is not Löbian
(`TauCupod/Helpers`, "the 2-cycle is not Löbian"). That bit enters as a hypothesis,
so this phase theorem is stated for either resolution.
-/

open PD PD.BaseTheorems

namespace PD.Tau

/-- τ(Cupod)'s bit ROW. The `.dupoc` slot is supplied by hypothesis — it is the
    entangled cell, open at the object level. -/
def cupodRow (bDupoc : Action) : Tmpl → Action
  | .coop       => .C
  | .defect     => .D
  | .tftSim     => .C
  | .tftPf      => .C
  | .dupoc      => bDupoc
  | .ebot       => .C
  | .just       => .C
  | .obot       => .C
  | .guardian   => .C
  | .dbot       => .C
  | .cupodTroll => .C
  | .cupod      => .D

end PD.Tau
