import ArithS.Tau.Columns
import ArithS.Tau.Attr

/-!
# ArithS.Tau.Rows.Defect — τ(DefectBot)'s row in PA-`S'`: all D

Every instance is the compiled constant `pConst 1` (`instCode_defect`). Engine twin:
`Tau/Theorems/TauDefect/Phase.lean` (`defectRowSpec`). No floor bits.
-/

namespace ArithS.Tau

open PD PD.Tau

/-- τ(DefectBot)'s bit row: D everywhere. -/
def defectRowA : Tmpl → Action := fun _ => .D

theorem defect_bit (k : ℕ) (T : Tmpl) : bitPlays k .defect T .D :=
  bitPlays_of_eq (instCode_defect k T) ⟨_, const_play 0 _ _ _⟩

/-- **τ(Defect)'s row in `S'`** — all 14 paper slots, at every budget. -/
@[tau_rowA]
theorem defectRowSpecA : RowSpecA .defect
    [.coop, .defect, .tftSim, .dupoc, .ebot, .obot, .dbot, .cupodTroll, .cupod, .dimcid, .cimcic,
     .prudent, .maxconfidence, .minconfidence] defectRowA :=
  ⟨0, fun k _ T _ ↦ defect_bit k T⟩

end ArithS.Tau
