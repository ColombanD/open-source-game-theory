import ArithS.Tau.Entangled.Base

/-!
# ArithS.Tau.Entangled.CupodPrudent — the `cupod × prudent` systems: two floor bits (‡)

`inst cupod prudent = .sys [cm 1, pm 0 cupod] 0`, `inst prudent cupod = .sys [pm 1 cupod, cm 0] 0` (base
`dich_CupodBot_vs_PrudentBot` / `dich_PrudentBot_vs_CupodBot`). The Cupod member plays `C` when its punish-probe of
the Prudent member is not found; the Prudent member plays `D` when its outer probe of the Cupod member is not found.
No theorem bit: the Prudent member's inner guard freezes `inst cupod .defect` (`k` inside) — the §7 obstacle
(`DupocPrudent.lean`).
-/

namespace ArithS.Tau

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open LAct
open PD PD.Tau

/-- `cupod × prudent` ‡ : C when the Cupod member's punish-probe of the Prudent member is not found. -/
theorem entFloor_cupod_prudent : FloorBitA .cupod .prudent
    (fun k ↦ □[k] (guardCodeB (templateCode (.plays (.bot (.sys (sys2 (cm 1 k) (pm 0 k .cupod)) 1))
      (.bot (.sys (sys2 (cm 1 k) (pm 0 k .cupod)) 1)) .D))
      (pBot (instCode k .cupod .prudent)) (pBot (instCode k .cupod .prudent)) k)) .C :=
  FloorBitA.of_not_hinge ⟨0, fun k _ hn ↦
    bit_C_of_cm_else (inst_cupod_prudent k) (not_found_of_not_hinge (inst_cupod_prudent k) _ hn)⟩

/-- `prudent × cupod` ‡ : D when the Prudent member's outer probe of the Cupod member is not found. -/
theorem entFloor_prudent_cupod : FloorBitA .prudent .cupod
    (fun k ↦ □[k] (guardCodeB (templateCode (.plays (.bot (.sys (sys2 (pm 1 k .cupod) (cm 0 k)) 1))
      (.bot (.sys (sys2 (pm 1 k .cupod) (cm 0 k)) 1)) .C))
      (pBot (instCode k .prudent .cupod)) (pBot (instCode k .prudent .cupod)) k)) .D :=
  FloorBitA.of_not_hinge ⟨0, fun k _ hn ↦
    bit_D_of_pm_else (inst_prudent_cupod k) (not_found_of_not_hinge (inst_prudent_cupod k) _ hn)⟩

end ArithS.Tau
