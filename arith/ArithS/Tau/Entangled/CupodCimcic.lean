import ArithS.Tau.Entangled.Base

/-!
# ArithS.Tau.Entangled.CupodCimcic — the `cupod × cimcic` systems: two floor bits (‡)

`inst cupod cimcic = .sys [cm 1, cim 0] 0`, `inst cimcic cupod = .sys [cim 1, cm 0] 0` (base `dich_CIMCIC_vs_CupodBot`,
the floor on Cupod's else-play). The Cupod member plays `C` when its punish-probe of the CIMCIC member is not found;
the CIMCIC member plays `D` when its implication guard about the Cupod member is not found. A Löb family for the
CIMCIC member would need the Cupod member NOT to find a FALSE guard in every model — soundness inside `V`, the
genuine floor.
-/

namespace ArithS.Tau

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open LAct
open PD PD.Tau

/-- `cupod × cimcic` ‡ : C when the Cupod member's punish-probe of the CIMCIC member is not found. -/
theorem entFloor_cupod_cimcic : FloorBitA .cupod .cimcic
    (fun k ↦ □[k] (guardCodeB (templateCode (.plays (.bot (.sys (sys2 (cm 1 k) (cim 0 k)) 1))
      (.bot (.sys (sys2 (cm 1 k) (cim 0 k)) 1)) .D))
      (pBot (instCode k .cupod .cimcic)) (pBot (instCode k .cupod .cimcic)) k)) .C :=
  FloorBitA.of_not_hinge ⟨0, fun k _ hn ↦
    bit_C_of_cm_else (inst_cupod_cimcic k) (not_found_of_not_hinge (inst_cupod_cimcic k) _ hn)⟩

/-- `cimcic × cupod` ‡ : D when the CIMCIC member's guard about the Cupod member is not found. -/
theorem entFloor_cimcic_cupod : FloorBitA .cimcic .cupod
    (fun k ↦ □[k] (guardCodeB (templateCode (.impl (.plays .self (.bot (.sys (sys2 (cim 1 k) (cm 0 k)) 1)) .C)
      (.plays (.bot (.sys (sys2 (cim 1 k) (cm 0 k)) 1)) .self .C)))
      (pBot (instCode k .cimcic .cupod)) (pBot (instCode k .cimcic .cupod)) k)) .D :=
  FloorBitA.of_not_hinge ⟨0, fun k _ hn ↦
    bit_D_of_cim_else (inst_cimcic_cupod k) (not_found_of_not_hinge (inst_cimcic_cupod k) _ hn)⟩

end ArithS.Tau
