import ArithS.Tau.Entangled.Base

/-!
# ArithS.Tau.Entangled.DupocPrudent — the `dupoc × prudent` systems: six floor bits (‡)

`inst dupoc prudent = .sys [dm 1, pm 0 dupoc] 0` and `inst prudent dupoc = .sys [pm 1 dupoc, dm 0] 0`; the natives
(`maxconfidence`, `minconfidence`) are Dupoc's spec and their prudence probes are Dupoc's
(`inst_*_prudent`, `inst_prudent_*`, `pm_maxconfidence`, `pm_minconfidence`), so the six bits are two systems.

Both are floors in the table (base `dich_PrudentBot_vs_DupocBot`): the Dupoc member plays `D` when its probe of the
Prudent member is not found, the Prudent member plays `D` when its OUTER probe of the Dupoc member is not found.
The hinge of each bit is the box the bit's own search consults, in the bit's frame — on the member codes, as
`Tau/Rows/*.lean` write theirs on the instance codes.

**Why no theorem bit here (the §7 obstacle).** The Prudent member's INNER guard freezes `inst dupoc .defect`, a
third party whose code carries `k` (`instCode_dupoc_defect`); the system's description is therefore the
`binNumeral k`-instance of no fixed term (`ROUTE_B_SCOPE.md` §7), and no Löb family can be stated for either
member. The dichotomy halves below are what `S'` settles.
-/

namespace ArithS.Tau

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open LAct
open PD PD.Tau

/-- `dupoc × prudent` ‡ : D when the Dupoc member's probe of the Prudent member is not found. -/
theorem entFloor_dupoc_prudent : FloorBitA .dupoc .prudent
    (fun k ↦ □[k] (guardCodeB (templateCode (.plays (.bot (.sys (sys2 (dm 1 k) (pm 0 k .dupoc)) 1))
      (.bot (.sys (sys2 (dm 1 k) (pm 0 k .dupoc)) 1)) .C))
      (pBot (instCode k .dupoc .prudent)) (pBot (instCode k .dupoc .prudent)) k)) .D :=
  FloorBitA.of_not_hinge ⟨0, fun k _ hn ↦
    bit_D_of_dm_else (inst_dupoc_prudent k) (not_found_of_not_hinge (inst_dupoc_prudent k) _ hn)⟩

theorem entFloor_maxconfidence_prudent : FloorBitA .maxconfidence .prudent
    (fun k ↦ □[k] (guardCodeB (templateCode (.plays (.bot (.sys (sys2 (dm 1 k) (pm 0 k .maxconfidence)) 1))
      (.bot (.sys (sys2 (dm 1 k) (pm 0 k .maxconfidence)) 1)) .C))
      (pBot (instCode k .maxconfidence .prudent)) (pBot (instCode k .maxconfidence .prudent)) k)) .D :=
  FloorBitA.of_not_hinge ⟨0, fun k _ hn ↦
    bit_D_of_dm_else (inst_maxconfidence_prudent k) (not_found_of_not_hinge (inst_maxconfidence_prudent k) _ hn)⟩

theorem entFloor_minconfidence_prudent : FloorBitA .minconfidence .prudent
    (fun k ↦ □[k] (guardCodeB (templateCode (.plays (.bot (.sys (sys2 (dm 1 k) (pm 0 k .minconfidence)) 1))
      (.bot (.sys (sys2 (dm 1 k) (pm 0 k .minconfidence)) 1)) .C))
      (pBot (instCode k .minconfidence .prudent)) (pBot (instCode k .minconfidence .prudent)) k)) .D :=
  FloorBitA.of_not_hinge ⟨0, fun k _ hn ↦
    bit_D_of_dm_else (inst_minconfidence_prudent k) (not_found_of_not_hinge (inst_minconfidence_prudent k) _ hn)⟩

/-- `prudent × dupoc` ‡ : D when the Prudent member's outer probe of the Dupoc member is not found. -/
theorem entFloor_prudent_dupoc : FloorBitA .prudent .dupoc
    (fun k ↦ □[k] (guardCodeB (templateCode (.plays (.bot (.sys (sys2 (pm 1 k .dupoc) (dm 0 k)) 1))
      (.bot (.sys (sys2 (pm 1 k .dupoc) (dm 0 k)) 1)) .C))
      (pBot (instCode k .prudent .dupoc)) (pBot (instCode k .prudent .dupoc)) k)) .D :=
  FloorBitA.of_not_hinge ⟨0, fun k _ hn ↦
    bit_D_of_pm_else (inst_prudent_dupoc k) (not_found_of_not_hinge (inst_prudent_dupoc k) _ hn)⟩

theorem entFloor_prudent_maxconfidence : FloorBitA .prudent .maxconfidence
    (fun k ↦ □[k] (guardCodeB (templateCode (.plays (.bot (.sys (sys2 (pm 1 k .maxconfidence) (dm 0 k)) 1))
      (.bot (.sys (sys2 (pm 1 k .maxconfidence) (dm 0 k)) 1)) .C))
      (pBot (instCode k .prudent .maxconfidence)) (pBot (instCode k .prudent .maxconfidence)) k)) .D :=
  FloorBitA.of_not_hinge ⟨0, fun k _ hn ↦
    bit_D_of_pm_else (inst_prudent_maxconfidence k) (not_found_of_not_hinge (inst_prudent_maxconfidence k) _ hn)⟩

theorem entFloor_prudent_minconfidence : FloorBitA .prudent .minconfidence
    (fun k ↦ □[k] (guardCodeB (templateCode (.plays (.bot (.sys (sys2 (pm 1 k .minconfidence) (dm 0 k)) 1))
      (.bot (.sys (sys2 (pm 1 k .minconfidence) (dm 0 k)) 1)) .C))
      (pBot (instCode k .prudent .minconfidence)) (pBot (instCode k .prudent .minconfidence)) k)) .D :=
  FloorBitA.of_not_hinge ⟨0, fun k _ hn ↦
    bit_D_of_pm_else (inst_prudent_minconfidence k) (not_found_of_not_hinge (inst_prudent_minconfidence k) _ hn)⟩

end ArithS.Tau
