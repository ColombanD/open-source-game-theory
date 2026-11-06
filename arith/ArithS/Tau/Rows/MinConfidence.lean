import ArithS.Tau.Rows.Dupoc

/-!
# ArithS.Tau.Rows.MinConfidence — the native MinConfidenceBot's row in PA-`S'`

MinConfidenceBot is a NATIVE tau player — Dupoc's per-hypothesis TEST under the `min / worst-case` aggregator (`Tau/Zoo.lean`,
`MaxConfidenceBotZ`/`MinConfidenceBotZ`) — whose spec IS Dupoc's spec, so its compiled instances are Dupoc's
by `rfl` off the two system slots, the diagonal and the `.just` slot (`inst_minconfidence_eq_dupoc`), and its diagonal is
the SAME quine term as Dupoc's (`inst_minconfidence_quine`). Its row is therefore Dupoc's row, restated under its own name
(the census requires one row per template); every proof is the Dupoc proof on the instance unfolded at the
`.minconfidence` slot. Engine twin: `Tau/Theorems/TauMinConfidence/Phase.lean`.

Slots stated here (`[coop, defect, dupoc, obot, dimcid, cimcic, maxconfidence, minconfidence]`): `coop` C, `defect` D
(`Tau/Columns.col_minconfidence_*`, by the bridge), `obot` D (SND), the diagonal C (Löb, the quine), and the ENTANGLED slots
(`Tau/Entangled/`, Dupoc's systems on the native's slot): `dupoc`/`maxconfidence` C (the symmetric system of two
Dupoc-spec self-probers, `ent_minconfidence_dupoc`/`ent_minconfidence_maxconfidence`), `dimcid` D (`ent_minconfidence_dimcid`),
`cimcic` C (`ent_minconfidence_cimcic`). **Floor bits** (`‡`, five, floor SIDE): `ebot`, `dbot`, `cupodTroll` — the hinge
is the native's own probe of the hypothesis's instance seeing it, not found ⇒ D — and the system floors `cupod` (the
red cell's tau image, a floor in `S'`: `Tau/Entangled/DupocCupod.lean`) and `prudent` (base `dich_PrudentBot_vs_DupocBot`).

`tftSim` C is Dupoc's `dupoc_tftSim_C` through the bridge (`Tau/ClosedWatch.minconfidence_tftSim_C`, Phase 3e).
-/

namespace ArithS.Tau

open PD PD.Tau

/-- MinConfidenceBot's bit row: Dupoc's. -/
def minconfidenceRowA : Tmpl → Action := dupocRowA

/-! ### The compiled instances (Dupoc's shape, at the `.minconfidence` slot) -/

theorem instCode_minconfidence_ebot (k : ℕ) : instCode k .minconfidence .ebot =
    pSearch k (templateCodeAt (probe (inst (tauZoo k) .ebot .minconfidence)) k) (pConst 0) (pConst 1) := by
  unfold instCode
  rw [show inst (tauZoo k) .minconfidence .ebot = .search k (probe (inst (tauZoo k) .ebot .minconfidence)) (.const .C) (.const .D)
    from rfl]
  simp [actCode]

theorem instCode_minconfidence_obot (k : ℕ) : instCode k .minconfidence .obot =
    pSearch k (templateCodeAt (probe (inst (tauZoo k) .obot .minconfidence)) k) (pConst 0) (pConst 1) := by
  unfold instCode
  rw [show inst (tauZoo k) .minconfidence .obot = .search k (probe (inst (tauZoo k) .obot .minconfidence)) (.const .C) (.const .D)
    from rfl]
  simp [actCode]

theorem instCode_minconfidence_dbot (k : ℕ) : instCode k .minconfidence .dbot =
    pSearch k (templateCodeAt (probe (inst (tauZoo k) .dbot .minconfidence)) k) (pConst 0) (pConst 1) := by
  unfold instCode
  rw [show inst (tauZoo k) .minconfidence .dbot = .search k (probe (inst (tauZoo k) .dbot .minconfidence)) (.const .C) (.const .D)
    from rfl]
  simp [actCode]

theorem instCode_minconfidence_cupodTroll (k : ℕ) : instCode k .minconfidence .cupodTroll =
    pSearch k (templateCodeAt (probe (inst (tauZoo k) .cupodTroll .minconfidence)) k) (pConst 0) (pConst 1) := by
  unfold instCode
  rw [show inst (tauZoo k) .minconfidence .cupodTroll =
    .search k (probe (inst (tauZoo k) .cupodTroll .minconfidence)) (.const .C) (.const .D) from rfl]
  simp [actCode]

/-- The diagonal is Dupoc's quine term. -/
theorem instCode_minconfidence_minconfidence (k : ℕ) : instCode k .minconfidence .minconfidence = instCode k .dupoc .dupoc := by
  unfold instCode; rw [inst_minconfidence_quine]

/-! ### The slots -/

theorem minconfidence_quine_C : bitEventually .minconfidence .minconfidence .C :=
  bitEventually.mono (fun k h ↦ (bitPlays_congr (instCode_minconfidence_minconfidence k) _).mpr h) dupoc_quine_C

theorem col_obot_minconfidence : bitEventually .obot .minconfidence .D := obotRowSpecA.slot (by simp)

theorem minconfidence_obot_D : bitEventually .minconfidence .obot .D :=
  bitEventually.mono (fun k h ↦ dupocLike_D_of_probe_false_at (instCode_minconfidence_obot k) rfl h) col_obot_minconfidence

/-- `minconfidence × dupocTroll` (2026-10-19): Dupoc's theorem slot through the bridge — the troll recognises the native's
SOURCE as Dupoc's and defects, so the native's probe is false (SND, D). -/
theorem minconfidence_dupocTroll_D : bitEventually .minconfidence .dupocTroll .D :=
  bitEventually.mono (fun k h ↦ (bitPlays_congr (instCode_minconfidence_eq k .dupocTroll (by decide) (by decide) (by decide) (by decide)) _).mpr h)
    dupoc_dupocTroll_D

/-- **MinConfidenceBot's row in `S'`** — the ten theorem slots (Dupoc's: six non-entangled, four entangled). -/
@[tau_rowA]
theorem minconfidenceRowSpecA : RowSpecA .minconfidence
    [.coop, .defect, .tftSim, .dupoc, .obot, .dupocTroll, .dimcid, .cimcic, .maxconfidence, .minconfidence] minconfidenceRowA :=
  RowSpecA.cons col_minconfidence_coop <|
  RowSpecA.cons (bitEventually.of_forall col_minconfidence_defect) <|
  RowSpecA.cons minconfidence_tftSim_C <|
  RowSpecA.cons ent_minconfidence_dupoc <|
  RowSpecA.cons minconfidence_obot_D <|
  RowSpecA.cons minconfidence_dupocTroll_D <|
  RowSpecA.cons ent_minconfidence_dimcid <|
  RowSpecA.cons ent_minconfidence_cimcic <|
  RowSpecA.cons ent_minconfidence_maxconfidence <|
  RowSpecA.cons minconfidence_quine_C <|
  RowSpecA.nil _ _

/-! ### The floor bits — the native's own probe is the hinge (floor SIDE) -/

/-- `minconfidence × ebot` ‡ (Dupoc's row by the bridge; base `dich_DupocBot_vs_EBot`). -/
@[tau_floor_bitA]
theorem minconfidenceRowSpecA_ebot_floor : FloorBitA .minconfidence .ebot
    (fun k ↦ □[k] (guardCodeB (templateCode (probe (inst (tauZoo k) .ebot .minconfidence)))
      (pBot (instCode k .minconfidence .ebot)) (pBot (instCode k .minconfidence .ebot)) k)) .D :=
  FloorBitA.of_not_hinge ⟨0, fun k _ hn ↦ dupocLike_floor_D_at (instCode_minconfidence_ebot k) rfl hn⟩

/-- `minconfidence × dbot` ‡ (base `dich_DupocBot_vs_DBot`). -/
@[tau_floor_bitA]
theorem minconfidenceRowSpecA_dbot_floor : FloorBitA .minconfidence .dbot
    (fun k ↦ □[k] (guardCodeB (templateCode (probe (inst (tauZoo k) .dbot .minconfidence)))
      (pBot (instCode k .minconfidence .dbot)) (pBot (instCode k .minconfidence .dbot)) k)) .D :=
  FloorBitA.of_not_hinge ⟨0, fun k _ hn ↦ dupocLike_floor_D_at (instCode_minconfidence_dbot k) rfl hn⟩

/-- `minconfidence × cupodTroll` ‡ (base `dich_DupocBot_vs_CupodTrollBot`). -/
@[tau_floor_bitA]
theorem minconfidenceRowSpecA_cupodTroll_floor : FloorBitA .minconfidence .cupodTroll
    (fun k ↦ □[k] (guardCodeB (templateCode (probe (inst (tauZoo k) .cupodTroll .minconfidence)))
      (pBot (instCode k .minconfidence .cupodTroll)) (pBot (instCode k .minconfidence .cupodTroll)) k)) .D :=
  FloorBitA.of_not_hinge ⟨0, fun k _ hn ↦ dupocLike_floor_D_at (instCode_minconfidence_cupodTroll k) rfl hn⟩

/-! ### The system floor bits — the Dupoc member's own probe is the hinge (`Tau/Entangled/`) -/

/-- `minconfidence × cupod` ‡ — the red cell's tau image on the native (the same system as Dupoc's), a FLOOR in `S'`
(`Tau/Entangled/DupocCupod.lean`): D when the Dupoc member's probe of the Cupod member is not found. -/
@[tau_floor_bitA]
theorem minconfidenceRowSpecA_cupod_floor : FloorBitA .minconfidence .cupod
    (fun k ↦ □[k] (guardCodeB (templateCode (.plays (.bot (.sys (sys2 (dm 1 k) (cm 0 k)) 1))
      (.bot (.sys (sys2 (dm 1 k) (cm 0 k)) 1)) .C))
      (pBot (instCode k .minconfidence .cupod)) (pBot (instCode k .minconfidence .cupod)) k)) .D :=
  entFloor_minconfidence_cupod

/-- `minconfidence × dimdid` ‡ (Dupoc's row by the bridge; base `dich_DIMDID_vs_DupocBot`). -/
@[tau_floor_bitA]
theorem minconfidenceRowSpecA_dimdid_floor : FloorBitA .minconfidence .dimdid
    (fun k ↦ □[k] (guardCodeB (templateCode (.plays (.bot (.sys (sys2 (dm 1 k) (ddm 0 k)) 1))
      (.bot (.sys (sys2 (dm 1 k) (ddm 0 k)) 1)) .C))
      (pBot (instCode k .minconfidence .dimdid)) (pBot (instCode k .minconfidence .dimdid)) k)) .D :=
  entFloor_minconfidence_dimdid

/-- `minconfidence × prudent` ‡ (base `dich_PrudentBot_vs_DupocBot`): D when the Dupoc member's probe of the Prudent member is
not found (`Tau/Entangled/DupocPrudent.lean`). -/

@[tau_floor_bitA]
theorem minconfidenceRowSpecA_prudent_floor : FloorBitA .minconfidence .prudent
    (fun k ↦ □[k] (guardCodeB (templateCode (.plays (.bot (.sys (sys2 (dm 1 k) (pm 0 k .minconfidence)) 1))
      (.bot (.sys (sys2 (dm 1 k) (pm 0 k .minconfidence)) 1)) .C))
      (pBot (instCode k .minconfidence .prudent)) (pBot (instCode k .minconfidence .prudent)) k)) .D :=
  entFloor_minconfidence_prudent

end ArithS.Tau
