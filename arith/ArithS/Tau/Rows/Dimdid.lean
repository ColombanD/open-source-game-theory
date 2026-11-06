import ArithS.Tau.Dimdid
import ArithS.Tau.ClosedWatchDd
import ArithS.Tau.Entangled.DimdidSys
import ArithS.Tau.Rows.CIMCIC
import ArithS.Tau.Attr

/-!
# ArithS.Tau.Rows.Dimdid — τ(DIMDID)'s row in PA-`S'` (2026-10-19)

τ(DIMDID) is the C/D transposition of τ(CIMCIC) template by template (`Tau/Bots/TauDIMDID.lean`; `inst dimdid T
= (inst cimcic τT).transpose` by `rfl` wherever `τT` is a roster template): the guard "if I defect against `T`'s
instance seeing DIMDID, it defects against me", then `D`, else `C`. Engine twin: `Tau/Theorems/TauDIMDID/Phase.lean`
(`dimdidRowSpec`); the row agrees with the engine's at every slot but `obot` (the `S'` FLIP, see below).

Slots stated here (eleven theorem slots):
* `coop` C and `defect` D — the transpositions of CIMCIC's `defect` (self-refuting ⇒ self-defeating) and `coop` (POS),
  `Tau/Dimdid.col_dimdid_coop/defect`; the diagonal D — the transposition of CIMCIC's tautology (`dimdid_quine_D`);
* `tftSim`, `dbot`, `cupodTroll`, `dupocTroll` C — the SELF-DEFEATING guard (`Tau/Dimdid.dimdid_not_found_of_C`):
  the hypothesis's instance cooperates with DIMDID's in every frame, so a proof of the guard would make DIMDID defect
  and, by soundness, the partner defect — against the fact; `ebot` C the same argument fragment-free
  (`Tau/ClosedWatchDd.dimdid_ebot_C`: τ(EBot)'s instance contains the system `inst dimdid mirror`);
* `obot` D — **the `S'` FLIP of the engine's C**: τ(OBot)'s instance at DIMDID defects in EVERY model above a
  standard threshold (its second watch sees DIMDID's found defection against the defector; its first is total),
  so the guard's consequent is a conditional `TAct`-theorem and the guard is found — POS, no Löb
  (`Tau/ClosedWatchDd.dimdid_obot_D`; the engine's census `dimdid_obot_plays_C` rests on `S` not reading OBot's
  source). The base cell `outcome_DIMDID_vs_OBot = (D, D)` is the same flip (`Cells/Dimdid.loeb_DIMDID_vs_OBot`);
* `cupod` D and `dimcid` D — the entangled systems, mutual Löb aligned on defection
  (`Tau/Entangled/DimdidSys.ent_dimdid_cupod`, `ent_dimdid_dimcid`).

**Floor bits** (`‡`, five, floor SIDE): `dupoc`, `maxconfidence`, `minconfidence` (base `dich_DIMDID_vs_DupocBot`),
`cimcic` (base `dich_DIMDID_vs_CIMCIC`, the self-dual pair), `prudent` (base `dich_DIMDID_vs_PrudentBot`): C when
the DIMDID member's guard is not found — the hinge is DIMDID's own guard about the partner member.
-/

namespace ArithS.Tau

open PD PD.Tau

/-- τ(DIMDID)'s bit row: D at the defector, OBot (the flip), Cupod, DIMCID and itself; C elsewhere. -/
def dimdidRowA : Tmpl → Action
  | .defect | .obot | .cupod | .dimcid | .dimdid => .D
  | _ => .C

/-- **The diagonal: D** — the transposition of CIMCIC's tautology (`cimcic_quine_C`). -/
theorem dimdid_quine_D : bitEventually .dimdid .dimdid .D := by
  refine bitEventually.mono (fun k h ↦ ?_) cimcic_quine_C
  -- elaborated without the expected type (`Tau/Dimdid.col_dimdid_coop`'s trap)
  have h' := bitPlays_transpose (inst_dimdid_dimdid_tr k) (by rw [inst_cimcic_quine]; rfl) h
  exact h'

/-- **τ(DIMDID)'s row in `S'`** — eleven theorem slots (the five floor bits are below). -/
@[tau_rowA]
theorem dimdidRowSpecA : RowSpecA .dimdid
    [.coop, .defect, .tftSim, .ebot, .obot, .dbot, .cupodTroll, .dupocTroll, .cupod, .dimcid, .dimdid] dimdidRowA :=
  RowSpecA.cons (bitEventually.of_forall col_dimdid_coop) <|
  RowSpecA.cons col_dimdid_defect <|
  RowSpecA.cons (bitEventually.of_forall dimdid_tftSim_C) <|
  RowSpecA.cons dimdid_ebot_C <|
  RowSpecA.cons dimdid_obot_D <|
  RowSpecA.cons dimdid_dbot_C <|
  RowSpecA.cons (bitEventually.of_forall dimdid_cupodTroll_C) <|
  RowSpecA.cons (bitEventually.of_forall dimdid_dupocTroll_C) <|
  RowSpecA.cons ent_dimdid_cupod <|
  RowSpecA.cons ent_dimdid_dimcid <|
  RowSpecA.cons dimdid_quine_D <|
  RowSpecA.nil _ _

/-! ### The floor bits — DIMDID's own guard about the partner member is the hinge (floor SIDE) -/

/-- `dimdid × dupoc` ‡ (base `dich_DIMDID_vs_DupocBot`): C when the DIMDID member's guard is not found. -/
@[tau_floor_bitA]
theorem dimdidRowSpecA_dupoc_floor : FloorBitA .dimdid .dupoc
    (fun k ↦ □[k] (guardCodeB (templateCode (.impl (.plays .self (.bot (.sys (sys2 (ddm 1 k) (dm 0 k)) 1)) .D)
      (.plays (.bot (.sys (sys2 (ddm 1 k) (dm 0 k)) 1)) .self .D)))
      (pBot (instCode k .dimdid .dupoc)) (pBot (instCode k .dimdid .dupoc)) k)) .C :=
  entFloor_dimdid_dupoc

/-- `dimdid × maxconfidence` ‡ (Dupoc's spec on the native; base `dich_DIMDID_vs_DupocBot`). -/
@[tau_floor_bitA]
theorem dimdidRowSpecA_maxconfidence_floor : FloorBitA .dimdid .maxconfidence
    (fun k ↦ □[k] (guardCodeB (templateCode (.impl (.plays .self (.bot (.sys (sys2 (ddm 1 k) (dm 0 k)) 1)) .D)
      (.plays (.bot (.sys (sys2 (ddm 1 k) (dm 0 k)) 1)) .self .D)))
      (pBot (instCode k .dimdid .maxconfidence)) (pBot (instCode k .dimdid .maxconfidence)) k)) .C :=
  entFloor_dimdid_maxconfidence

/-- `dimdid × minconfidence` ‡ (Dupoc's spec on the native; base `dich_DIMDID_vs_DupocBot`). -/
@[tau_floor_bitA]
theorem dimdidRowSpecA_minconfidence_floor : FloorBitA .dimdid .minconfidence
    (fun k ↦ □[k] (guardCodeB (templateCode (.impl (.plays .self (.bot (.sys (sys2 (ddm 1 k) (dm 0 k)) 1)) .D)
      (.plays (.bot (.sys (sys2 (ddm 1 k) (dm 0 k)) 1)) .self .D)))
      (pBot (instCode k .dimdid .minconfidence)) (pBot (instCode k .dimdid .minconfidence)) k)) .C :=
  entFloor_dimdid_minconfidence

/-- `dimdid × cimcic` ‡ (base `dich_DIMDID_vs_CIMCIC`): C when the DIMDID member's guard is not found. -/
@[tau_floor_bitA]
theorem dimdidRowSpecA_cimcic_floor : FloorBitA .dimdid .cimcic
    (fun k ↦ □[k] (guardCodeB (templateCode (.impl (.plays .self (.bot (.sys (sys2 (ddm 1 k) (cim 0 k)) 1)) .D)
      (.plays (.bot (.sys (sys2 (ddm 1 k) (cim 0 k)) 1)) .self .D)))
      (pBot (instCode k .dimdid .cimcic)) (pBot (instCode k .dimdid .cimcic)) k)) .C :=
  entFloor_dimdid_cimcic

/-- `dimdid × prudent` ‡ (base `dich_DIMDID_vs_PrudentBot`): C when the DIMDID member's guard is not found. -/
@[tau_floor_bitA]
theorem dimdidRowSpecA_prudent_floor : FloorBitA .dimdid .prudent
    (fun k ↦ □[k] (guardCodeB (templateCode (.impl (.plays .self (.bot (.sys (sys2 (ddm 1 k) (pm 0 k .dimdid)) 1)) .D)
      (.plays (.bot (.sys (sys2 (ddm 1 k) (pm 0 k .dimdid)) 1)) .self .D)))
      (pBot (instCode k .dimdid .prudent)) (pBot (instCode k .dimdid .prudent)) k)) .C :=
  entFloor_dimdid_prudent

end ArithS.Tau
