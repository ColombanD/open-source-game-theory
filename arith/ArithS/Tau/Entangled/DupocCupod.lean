import ArithS.Tau.Entangled.Base

/-!
# ArithS.Tau.Entangled.DupocCupod — the `dupoc × cupod` systems: the tau image of the red cell is a FLOOR in `S'`

`inst dupoc cupod = .sys [dm 1, cm 0] 0` (member 0 Dupoc probing the Cupod member for C) and
`inst cupod dupoc = .sys [cm 1, dm 0] 0` (member 0 Cupod probing the Dupoc member for D); the natives are the same
two systems (`inst_maxconfidence_cupod`, `inst_cupod_maxconfidence`, …).

**The finding.** The table (`SPRIME_SOURCE_OF_TRUTH.md` §3) lists these six bits as THEOREM bits (`D` / `C`),
derived from the base red cell `outcome_DupocBot_vs_CupodBot = (D, C)`, which `Cells/RedCell.lean` proves in
`S'` by τ-SYMMETRY: Cupod `k` IS `transposeCode (Dupoc k)`, so Dupoc's guard about Cupod and Cupod's guard about
Dupoc are τ-images of each other and are provable together or not at all; provable together contradicts
determinism. The compiled tau pair has no such symmetry: τ maps the system `[dm 1, cm 0]` to the OTHER
orientation's system `[cm 1, dm 0]`, so the τ-image of the Dupoc member's guard is a guard of the other system,
not the partner's guard in the same system. Inside one system the three scenarios "Dupoc's guard found /
Cupod's guard found / neither" are all consistent with soundness and determinism, and `S'` picks one only
through a bounded-consistency question: Dupoc's guard "the Cupod member cooperates with itself" is
equivalent to "the Cupod member does not find its own guard", a `¬□_k` statement (the engine's own proof of
these bits, `Tau/Theorems/TauCupod/Helpers.lean`, is explicit that "the 2-cycle bounded Löb cannot close …
the floor DECIDES"). In `S'` the six bits are therefore floor bits with the hinge the member's own search
consults — stated here as `FloorBitA` (untagged), the engine-side value under `¬ hinge`; they are NOT
theorem bits, and the table should be updated (a theorem that became a floor).
-/

namespace ArithS.Tau

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open LAct
open PD PD.Tau

/-- `dupoc × cupod`: D when the Dupoc member's probe of the Cupod member is not found (a FLOOR in `S'`). -/
theorem entFloor_dupoc_cupod : FloorBitA .dupoc .cupod
    (fun k ↦ □[k] (guardCodeB (templateCode (.plays (.bot (.sys (sys2 (dm 1 k) (cm 0 k)) 1))
      (.bot (.sys (sys2 (dm 1 k) (cm 0 k)) 1)) .C))
      (pBot (instCode k .dupoc .cupod)) (pBot (instCode k .dupoc .cupod)) k)) .D :=
  FloorBitA.of_not_hinge ⟨0, fun k _ hn ↦
    bit_D_of_dm_else (inst_dupoc_cupod k) (not_found_of_not_hinge (inst_dupoc_cupod k) _ hn)⟩

theorem entFloor_maxconfidence_cupod : FloorBitA .maxconfidence .cupod
    (fun k ↦ □[k] (guardCodeB (templateCode (.plays (.bot (.sys (sys2 (dm 1 k) (cm 0 k)) 1))
      (.bot (.sys (sys2 (dm 1 k) (cm 0 k)) 1)) .C))
      (pBot (instCode k .maxconfidence .cupod)) (pBot (instCode k .maxconfidence .cupod)) k)) .D :=
  FloorBitA.of_not_hinge ⟨0, fun k _ hn ↦
    bit_D_of_dm_else (inst_maxconfidence_cupod k) (not_found_of_not_hinge (inst_maxconfidence_cupod k) _ hn)⟩

theorem entFloor_minconfidence_cupod : FloorBitA .minconfidence .cupod
    (fun k ↦ □[k] (guardCodeB (templateCode (.plays (.bot (.sys (sys2 (dm 1 k) (cm 0 k)) 1))
      (.bot (.sys (sys2 (dm 1 k) (cm 0 k)) 1)) .C))
      (pBot (instCode k .minconfidence .cupod)) (pBot (instCode k .minconfidence .cupod)) k)) .D :=
  FloorBitA.of_not_hinge ⟨0, fun k _ hn ↦
    bit_D_of_dm_else (inst_minconfidence_cupod k) (not_found_of_not_hinge (inst_minconfidence_cupod k) _ hn)⟩

/-- `cupod × dupoc`: C when the Cupod member's punish-probe of the Dupoc member is not found (a FLOOR in `S'`). -/
theorem entFloor_cupod_dupoc : FloorBitA .cupod .dupoc
    (fun k ↦ □[k] (guardCodeB (templateCode (.plays (.bot (.sys (sys2 (cm 1 k) (dm 0 k)) 1))
      (.bot (.sys (sys2 (cm 1 k) (dm 0 k)) 1)) .D))
      (pBot (instCode k .cupod .dupoc)) (pBot (instCode k .cupod .dupoc)) k)) .C :=
  FloorBitA.of_not_hinge ⟨0, fun k _ hn ↦
    bit_C_of_cm_else (inst_cupod_dupoc k) (not_found_of_not_hinge (inst_cupod_dupoc k) _ hn)⟩

theorem entFloor_cupod_maxconfidence : FloorBitA .cupod .maxconfidence
    (fun k ↦ □[k] (guardCodeB (templateCode (.plays (.bot (.sys (sys2 (cm 1 k) (dm 0 k)) 1))
      (.bot (.sys (sys2 (cm 1 k) (dm 0 k)) 1)) .D))
      (pBot (instCode k .cupod .maxconfidence)) (pBot (instCode k .cupod .maxconfidence)) k)) .C :=
  FloorBitA.of_not_hinge ⟨0, fun k _ hn ↦
    bit_C_of_cm_else (inst_cupod_maxconfidence k) (not_found_of_not_hinge (inst_cupod_maxconfidence k) _ hn)⟩

theorem entFloor_cupod_minconfidence : FloorBitA .cupod .minconfidence
    (fun k ↦ □[k] (guardCodeB (templateCode (.plays (.bot (.sys (sys2 (cm 1 k) (dm 0 k)) 1))
      (.bot (.sys (sys2 (cm 1 k) (dm 0 k)) 1)) .D))
      (pBot (instCode k .cupod .minconfidence)) (pBot (instCode k .cupod .minconfidence)) k)) .C :=
  FloorBitA.of_not_hinge ⟨0, fun k _ hn ↦
    bit_C_of_cm_else (inst_cupod_minconfidence k) (not_found_of_not_hinge (inst_cupod_minconfidence k) _ hn)⟩

end ArithS.Tau
