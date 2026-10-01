import ArithS.Tau.Rows.Dupoc

/-!
# ArithS.Tau.Rows.MaxConfidence — the native MaxConfidenceBot's row in PA-`S'`

MaxConfidenceBot is a NATIVE tau player — Dupoc's per-hypothesis TEST under the `max ≥ θ` aggregator (`Tau/Zoo.lean`,
`MaxConfidenceBotZ`/`MinConfidenceBotZ`) — whose spec IS Dupoc's spec, so its compiled instances are Dupoc's
by `rfl` off the two system slots, the diagonal and the `.just` slot (`inst_maxconfidence_eq_dupoc`), and its diagonal is
the SAME quine term as Dupoc's (`inst_maxconfidence_quine`). Its row is therefore Dupoc's row, restated under its own name
(the census requires one row per template); every proof is the Dupoc proof on the instance unfolded at the
`.maxconfidence` slot. Engine twin: `Tau/Theorems/TauMaxConfidence/Phase.lean`.

Slots stated here (`[coop, defect, dupoc, obot, dimcid, cimcic, maxconfidence, minconfidence]`): `coop` C, `defect` D
(`Tau/Columns.col_maxconfidence_*`, by the bridge), `obot` D (SND), the diagonal C (Löb, the quine), and the ENTANGLED slots
(`Tau/Entangled/`, Dupoc's systems on the native's slot): `dupoc`/`minconfidence` C (the symmetric system of two
Dupoc-spec self-probers, `ent_maxconfidence_dupoc`/`ent_maxconfidence_minconfidence`), `dimcid` D (`ent_maxconfidence_dimcid`),
`cimcic` C (`ent_maxconfidence_cimcic`). **Floor bits** (`‡`, five, floor SIDE): `ebot`, `dbot`, `cupodTroll` — the hinge
is the native's own probe of the hypothesis's instance seeing it, not found ⇒ D — and the system floors `cupod` (the
red cell's tau image, a floor in `S'`: `Tau/Entangled/DupocCupod.lean`) and `prudent` (base `dich_PrudentBot_vs_DupocBot`).

`tftSim` C is Dupoc's `dupoc_tftSim_C` through the bridge (`Tau/ClosedWatch.maxconfidence_tftSim_C`, Phase 3e).
-/

namespace ArithS.Tau

open PD PD.Tau

/-- MaxConfidenceBot's bit row: Dupoc's. -/
def maxconfidenceRowA : Tmpl → Action := dupocRowA

/-! ### The compiled instances (Dupoc's shape, at the `.maxconfidence` slot) -/

theorem instCode_maxconfidence_ebot (k : ℕ) : instCode k .maxconfidence .ebot =
    pSearch k (templateCodeAt (probe (inst (tauZoo k) .ebot .maxconfidence)) k) (pConst 0) (pConst 1) := by
  unfold instCode
  rw [show inst (tauZoo k) .maxconfidence .ebot = .search k (probe (inst (tauZoo k) .ebot .maxconfidence)) (.const .C) (.const .D)
    from rfl]
  simp [actCode]

theorem instCode_maxconfidence_obot (k : ℕ) : instCode k .maxconfidence .obot =
    pSearch k (templateCodeAt (probe (inst (tauZoo k) .obot .maxconfidence)) k) (pConst 0) (pConst 1) := by
  unfold instCode
  rw [show inst (tauZoo k) .maxconfidence .obot = .search k (probe (inst (tauZoo k) .obot .maxconfidence)) (.const .C) (.const .D)
    from rfl]
  simp [actCode]

theorem instCode_maxconfidence_dbot (k : ℕ) : instCode k .maxconfidence .dbot =
    pSearch k (templateCodeAt (probe (inst (tauZoo k) .dbot .maxconfidence)) k) (pConst 0) (pConst 1) := by
  unfold instCode
  rw [show inst (tauZoo k) .maxconfidence .dbot = .search k (probe (inst (tauZoo k) .dbot .maxconfidence)) (.const .C) (.const .D)
    from rfl]
  simp [actCode]

theorem instCode_maxconfidence_cupodTroll (k : ℕ) : instCode k .maxconfidence .cupodTroll =
    pSearch k (templateCodeAt (probe (inst (tauZoo k) .cupodTroll .maxconfidence)) k) (pConst 0) (pConst 1) := by
  unfold instCode
  rw [show inst (tauZoo k) .maxconfidence .cupodTroll =
    .search k (probe (inst (tauZoo k) .cupodTroll .maxconfidence)) (.const .C) (.const .D) from rfl]
  simp [actCode]

/-- The diagonal is Dupoc's quine term. -/
theorem instCode_maxconfidence_maxconfidence (k : ℕ) : instCode k .maxconfidence .maxconfidence = instCode k .dupoc .dupoc := by
  unfold instCode; rw [inst_maxconfidence_quine]

/-! ### The slots -/

theorem maxconfidence_quine_C : bitEventually .maxconfidence .maxconfidence .C :=
  bitEventually.mono (fun k h ↦ (bitPlays_congr (instCode_maxconfidence_maxconfidence k) _).mpr h) dupoc_quine_C

theorem col_obot_maxconfidence : bitEventually .obot .maxconfidence .D := obotRowSpecA.slot (by simp)

theorem maxconfidence_obot_D : bitEventually .maxconfidence .obot .D :=
  bitEventually.mono (fun k h ↦ dupocLike_D_of_probe_false_at (instCode_maxconfidence_obot k) rfl h) col_obot_maxconfidence

/-- **MaxConfidenceBot's row in `S'`** — the nine theorem slots (Dupoc's: five non-entangled, four entangled). -/
@[tau_rowA]
theorem maxconfidenceRowSpecA : RowSpecA .maxconfidence
    [.coop, .defect, .tftSim, .dupoc, .obot, .dimcid, .cimcic, .maxconfidence, .minconfidence] maxconfidenceRowA :=
  RowSpecA.cons col_maxconfidence_coop <|
  RowSpecA.cons (bitEventually.of_forall col_maxconfidence_defect) <|
  RowSpecA.cons maxconfidence_tftSim_C <|
  RowSpecA.cons ent_maxconfidence_dupoc <|
  RowSpecA.cons maxconfidence_obot_D <|
  RowSpecA.cons ent_maxconfidence_dimcid <|
  RowSpecA.cons ent_maxconfidence_cimcic <|
  RowSpecA.cons maxconfidence_quine_C <|
  RowSpecA.cons ent_maxconfidence_minconfidence <|
  RowSpecA.nil _ _

/-! ### The floor bits — the native's own probe is the hinge (floor SIDE) -/

/-- `maxconfidence × ebot` ‡ (Dupoc's row by the bridge; base `dich_DupocBot_vs_EBot`). -/
@[tau_floor_bitA]
theorem maxconfidenceRowSpecA_ebot_floor : FloorBitA .maxconfidence .ebot
    (fun k ↦ □[k] (guardCodeB (templateCode (probe (inst (tauZoo k) .ebot .maxconfidence)))
      (pBot (instCode k .maxconfidence .ebot)) (pBot (instCode k .maxconfidence .ebot)) k)) .D :=
  FloorBitA.of_not_hinge ⟨0, fun k _ hn ↦ dupocLike_floor_D_at (instCode_maxconfidence_ebot k) rfl hn⟩

/-- `maxconfidence × dbot` ‡ (base `dich_DupocBot_vs_DBot`). -/
@[tau_floor_bitA]
theorem maxconfidenceRowSpecA_dbot_floor : FloorBitA .maxconfidence .dbot
    (fun k ↦ □[k] (guardCodeB (templateCode (probe (inst (tauZoo k) .dbot .maxconfidence)))
      (pBot (instCode k .maxconfidence .dbot)) (pBot (instCode k .maxconfidence .dbot)) k)) .D :=
  FloorBitA.of_not_hinge ⟨0, fun k _ hn ↦ dupocLike_floor_D_at (instCode_maxconfidence_dbot k) rfl hn⟩

/-- `maxconfidence × cupodTroll` ‡ (base `dich_DupocBot_vs_CupodTrollBot`). -/
@[tau_floor_bitA]
theorem maxconfidenceRowSpecA_cupodTroll_floor : FloorBitA .maxconfidence .cupodTroll
    (fun k ↦ □[k] (guardCodeB (templateCode (probe (inst (tauZoo k) .cupodTroll .maxconfidence)))
      (pBot (instCode k .maxconfidence .cupodTroll)) (pBot (instCode k .maxconfidence .cupodTroll)) k)) .D :=
  FloorBitA.of_not_hinge ⟨0, fun k _ hn ↦ dupocLike_floor_D_at (instCode_maxconfidence_cupodTroll k) rfl hn⟩

/-! ### The system floor bits — the Dupoc member's own probe is the hinge (`Tau/Entangled/`) -/

/-- `maxconfidence × cupod` ‡ — the red cell's tau image on the native (the same system as Dupoc's), a FLOOR in `S'`
(`Tau/Entangled/DupocCupod.lean`): D when the Dupoc member's probe of the Cupod member is not found. -/
@[tau_floor_bitA]
theorem maxconfidenceRowSpecA_cupod_floor : FloorBitA .maxconfidence .cupod
    (fun k ↦ □[k] (guardCodeB (templateCode (.plays (.bot (.sys (sys2 (dm 1 k) (cm 0 k)) 1))
      (.bot (.sys (sys2 (dm 1 k) (cm 0 k)) 1)) .C))
      (pBot (instCode k .maxconfidence .cupod)) (pBot (instCode k .maxconfidence .cupod)) k)) .D :=
  entFloor_maxconfidence_cupod

/-- `maxconfidence × prudent` ‡ (base `dich_PrudentBot_vs_DupocBot`): D when the Dupoc member's probe of the Prudent member is
not found (`Tau/Entangled/DupocPrudent.lean`). -/
@[tau_floor_bitA]
theorem maxconfidenceRowSpecA_prudent_floor : FloorBitA .maxconfidence .prudent
    (fun k ↦ □[k] (guardCodeB (templateCode (.plays (.bot (.sys (sys2 (dm 1 k) (pm 0 k .maxconfidence)) 1))
      (.bot (.sys (sys2 (dm 1 k) (pm 0 k .maxconfidence)) 1)) .C))
      (pBot (instCode k .maxconfidence .prudent)) (pBot (instCode k .maxconfidence .prudent)) k)) .D :=
  entFloor_maxconfidence_prudent

end ArithS.Tau
