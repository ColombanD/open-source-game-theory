import ArithS.Tau.Entangled.Base

/-!
# ArithS.Tau.Entangled.CimcicPrudent — the `cimcic × prudent` systems: two floor bits (‡)

`inst cimcic prudent = .sys [cim 1, pm 0 cimcic] 0`, `inst prudent cimcic = .sys [pm 1 cimcic, cim 0] 0` (base
`dich_CIMCIC_vs_PrudentBot`). The CIMCIC member plays `D` when its implication guard about the Prudent member is not
found; the Prudent member plays `D` when its outer probe of the CIMCIC member is not found. No theorem bit: the
Prudent member's inner guard freezes `inst cimcic .defect` (`k` inside) — the §7 obstacle (`DupocPrudent.lean`).
-/

namespace ArithS.Tau

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open LAct
open PD PD.Tau

/-- `cimcic × prudent` ‡ : D when the CIMCIC member's guard about the Prudent member is not found. -/
theorem entFloor_cimcic_prudent : FloorBitA .cimcic .prudent
    (fun k ↦ □[k] (guardCodeB (templateCode (.impl (.plays .self (.bot (.sys (sys2 (cim 1 k) (pm 0 k .cimcic)) 1)) .C)
      (.plays (.bot (.sys (sys2 (cim 1 k) (pm 0 k .cimcic)) 1)) .self .C)))
      (pBot (instCode k .cimcic .prudent)) (pBot (instCode k .cimcic .prudent)) k)) .D :=
  FloorBitA.of_not_hinge ⟨0, fun k _ hn ↦
    bit_D_of_cim_else (inst_cimcic_prudent k) (not_found_of_not_hinge (inst_cimcic_prudent k) _ hn)⟩

/-- `prudent × cimcic` ‡ : D when the Prudent member's outer probe of the CIMCIC member is not found. -/
theorem entFloor_prudent_cimcic : FloorBitA .prudent .cimcic
    (fun k ↦ □[k] (guardCodeB (templateCode (.plays (.bot (.sys (sys2 (pm 1 k .cimcic) (cim 0 k)) 1))
      (.bot (.sys (sys2 (pm 1 k .cimcic) (cim 0 k)) 1)) .C))
      (pBot (instCode k .prudent .cimcic)) (pBot (instCode k .prudent .cimcic)) k)) .D :=
  FloorBitA.of_not_hinge ⟨0, fun k _ hn ↦
    bit_D_of_pm_else (inst_prudent_cimcic k) (not_found_of_not_hinge (inst_prudent_cimcic k) _ hn)⟩

end ArithS.Tau
