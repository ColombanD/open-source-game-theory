import ArithS.Tau.Columns
import ArithS.Tau.Attr

/-!
# ArithS.Tau.Rows.Coop — τ(CooperateBot)'s row in PA-`S'`: all C

Every instance is the compiled constant `pConst 0` (`instCode_coop`); the row is signal-blind cooperation at
every budget. Engine twin: `Tau/Theorems/TauCooperate/Phase.lean` (`coopRowSpec`). No floor bits.
-/

namespace ArithS.Tau

open PD PD.Tau

/-- τ(CooperateBot)'s bit row: C everywhere. -/
def coopRowA : Tmpl → Action := fun _ => .C

theorem coop_bit (k : ℕ) (T : Tmpl) : bitPlays k .coop T .C :=
  bitPlays_of_eq (instCode_coop k T) ⟨_, const_play 0 _ _ _⟩

/-- **τ(Cooperate)'s row in `S'`** — all 16 paper slots, at every budget. -/
@[tau_rowA]
theorem coopRowSpecA : RowSpecA .coop
    [.coop, .defect, .tftSim, .dupoc, .ebot, .obot, .dbot, .cupodTroll, .dupocTroll, .cupod, .dimcid, .cimcic, .dimdid,
     .prudent, .maxconfidence, .minconfidence] coopRowA :=
  ⟨0, fun k _ T _ ↦ coop_bit k T⟩

end ArithS.Tau
