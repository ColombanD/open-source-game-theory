import ArithS.Tau.Rows.Dupoc

/-!
# ArithS.Tau.Rows.MinConfidence — the native MinConfidenceBot's row in PA-`S'` (the NON-entangled slots)

MinConfidenceBot is a NATIVE tau player — Dupoc's per-hypothesis TEST under the `min / worst-case` aggregator (`Tau/Zoo.lean`,
`MaxConfidenceBotZ`/`MinConfidenceBotZ`) — whose spec IS Dupoc's spec, so its compiled instances are Dupoc's
by `rfl` off the two system slots, the diagonal and the `.just` slot (`inst_minconfidence_eq_dupoc`), and its diagonal is
the SAME quine term as Dupoc's (`inst_minconfidence_quine`). Its row is therefore Dupoc's row, restated under its own name
(the census requires one row per template); every proof is the Dupoc proof on the instance unfolded at the
`.minconfidence` slot. Engine twin: `Tau/Theorems/TauMinConfidence/Phase.lean`.

Slots stated here (`[coop, defect, obot, minconfidence]`): `coop` C, `defect` D (`Tau/Columns.col_minconfidence_*`, by the bridge),
`obot` D (SND), the diagonal C (Löb, the quine). **Floor bits** (`‡`, three, floor SIDE): `ebot`, `dbot`,
`cupodTroll` — the hinge is the native's own probe of the hypothesis's instance seeing it, not found ⇒ D.

-- Phase 3c: entangled — `dupoc cupod dimcid cimcic prudent maxconfidence` (the symmetric system `cfdSys` with the
--   other two Dupoc-spec self-probers, and the four `.sys` pairs).
-- TODO Phase 3d: slot `.tftSim` (C) — as `Rows/Dupoc.lean`'s (the same probed instance shape).
-/

namespace ArithS.Tau

open PD PD.Tau

/-- MinConfidenceBot's bit row: Dupoc's. -/
def minconfidenceRowA : Tmpl → Action := dupocRowA

/-! ### The compiled instances (Dupoc's shape, at the `.minconfidence` slot) -/

theorem instCode_minconfidence_ebot (k : ℕ) : instCode k .minconfidence .ebot =
    pSearch k (templateCode (probe (inst (tauZoo k) .ebot .minconfidence))) (pConst 0) (pConst 1) := by
  unfold instCode
  rw [show inst (tauZoo k) .minconfidence .ebot = .search k (probe (inst (tauZoo k) .ebot .minconfidence)) (.const .C) (.const .D)
    from rfl]
  simp [actCode]

theorem instCode_minconfidence_obot (k : ℕ) : instCode k .minconfidence .obot =
    pSearch k (templateCode (probe (inst (tauZoo k) .obot .minconfidence))) (pConst 0) (pConst 1) := by
  unfold instCode
  rw [show inst (tauZoo k) .minconfidence .obot = .search k (probe (inst (tauZoo k) .obot .minconfidence)) (.const .C) (.const .D)
    from rfl]
  simp [actCode]

theorem instCode_minconfidence_dbot (k : ℕ) : instCode k .minconfidence .dbot =
    pSearch k (templateCode (probe (inst (tauZoo k) .dbot .minconfidence))) (pConst 0) (pConst 1) := by
  unfold instCode
  rw [show inst (tauZoo k) .minconfidence .dbot = .search k (probe (inst (tauZoo k) .dbot .minconfidence)) (.const .C) (.const .D)
    from rfl]
  simp [actCode]

theorem instCode_minconfidence_cupodTroll (k : ℕ) : instCode k .minconfidence .cupodTroll =
    pSearch k (templateCode (probe (inst (tauZoo k) .cupodTroll .minconfidence))) (pConst 0) (pConst 1) := by
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
  bitEventually.mono (fun k h ↦ dupocLike_D_of_probe_false (instCode_minconfidence_obot k) rfl h) col_obot_minconfidence

/-- **MinConfidenceBot's row in `S'`** — the four non-entangled theorem slots (Dupoc's). -/
@[tau_rowA]
theorem minconfidenceRowSpecA : RowSpecA .minconfidence [.coop, .defect, .obot, .minconfidence] minconfidenceRowA :=
  RowSpecA.cons col_minconfidence_coop <|
  RowSpecA.cons (bitEventually.of_forall col_minconfidence_defect) <|
  RowSpecA.cons minconfidence_obot_D <|
  RowSpecA.cons minconfidence_quine_C <|
  RowSpecA.nil _ _

/-! ### The floor bits — the native's own probe is the hinge (floor SIDE) -/

/-- `minconfidence × ebot` ‡ (Dupoc's row by the bridge; base `dich_DupocBot_vs_EBot`). -/
@[tau_floor_bitA]
theorem minconfidenceRowSpecA_ebot_floor : FloorBitA .minconfidence .ebot
    (fun k ↦ □[k] (guardCodeB (templateCode (probe (inst (tauZoo k) .ebot .minconfidence)))
      (pBot (instCode k .minconfidence .ebot)) (pBot (instCode k .minconfidence .ebot)) k)) .D :=
  FloorBitA.of_not_hinge ⟨0, fun k _ hn ↦ dupocLike_floor_D (instCode_minconfidence_ebot k) rfl hn⟩

/-- `minconfidence × dbot` ‡ (base `dich_DupocBot_vs_DBot`). -/
@[tau_floor_bitA]
theorem minconfidenceRowSpecA_dbot_floor : FloorBitA .minconfidence .dbot
    (fun k ↦ □[k] (guardCodeB (templateCode (probe (inst (tauZoo k) .dbot .minconfidence)))
      (pBot (instCode k .minconfidence .dbot)) (pBot (instCode k .minconfidence .dbot)) k)) .D :=
  FloorBitA.of_not_hinge ⟨0, fun k _ hn ↦ dupocLike_floor_D (instCode_minconfidence_dbot k) rfl hn⟩

/-- `minconfidence × cupodTroll` ‡ (base `dich_DupocBot_vs_CupodTrollBot`). -/
@[tau_floor_bitA]
theorem minconfidenceRowSpecA_cupodTroll_floor : FloorBitA .minconfidence .cupodTroll
    (fun k ↦ □[k] (guardCodeB (templateCode (probe (inst (tauZoo k) .cupodTroll .minconfidence)))
      (pBot (instCode k .minconfidence .cupodTroll)) (pBot (instCode k .minconfidence .cupodTroll)) k)) .D :=
  FloorBitA.of_not_hinge ⟨0, fun k _ hn ↦ dupocLike_floor_D (instCode_minconfidence_cupodTroll k) rfl hn⟩

end ArithS.Tau
