import ArithS.Tau.Quine
import ArithS.Tau.Attr

/-!
# ArithS.Tau.Rows.Dupoc — τ(DupocBot)'s row in PA-`S'` (the NON-entangled slots)

τ(Dupoc)'s instance at a hypothesis `T` that does not self-probe is one prove-stage on `T`'s instance seeing
Dupoc: `.search k (probe (inst T .dupoc)) C D` (`Tau/Zoo.inst_dupoc_peel_*`). Its DIAGONAL is the quine
`.search k (.plays .self .self C) C D` (`inst_dupoc_quine`), closed by bounded Löb on the bot-wrapped instance
(`Tau/Quine.quine_found`). Engine twin: `Tau/Theorems/TauDupoc/Phase.lean` (`dupocRowSpec`).

Slots stated here (`[coop, defect, dupoc, obot]`): `coop` C (POS on the frozen cooperator, `col_dupoc_coop`),
`defect` D (SND, `col_dupoc_defect`), the diagonal C (Löb), `obot` D (SND: τ(OBot)'s instance at Dupoc defects —
its second defection watch sees Dupoc's instance defect against the defector — so the probe is false).

**Floor bits** (`‡`, three, all on THIS side — the first floor-SIDE bits of the tau layer): `ebot`, `dbot`,
`cupodTroll`. The hinge is Dupoc's OWN probe of the hypothesis's instance (true in ℕ: the partner's C runs
through Dupoc's else-play; base `dich_DupocBot_vs_EBot/DBot/CupodTrollBot`); when it is not found, the
else-branch D (`FloorBitA.of_not_hinge` + `search_else`).

-- Phase 3c: entangled — `cupod dimcid cimcic prudent maxconfidence minconfidence` (`.sys` systems, the
--   member-slot families; `Tau/Entangled/`).
-- TODO Phase 3d: slot `.tftSim` (C): τ(TFTSim)'s instance at Dupoc is `ite (sim (bot (inst dupoc coop)) …)`,
--   which cooperates (POS), so the probe is TRUE and must be FOUND; the probed program carries the budget
--   `k` (the `.search k` leaf of `inst dupoc coop`), so the box needs a `binNumeral k`-tower for the ite/sim
--   watch over `pBot (SV g 0 k)` (the `botT1`/`searchT1` builders plus NEW `iteT1`/`simT1`, with the
--   canonical-code comparison of the watch against its transposition above a threshold, the
--   `nested_search_lt` pattern of `Cells/PrudentMirror.lean`) and the `k̂`-chain `found_of_all_above`
--   (truth needs the inner guard found, i.e. `k ≥ L`). Not built in this phase.
-/

namespace ArithS.Tau

open PD PD.Tau

/-- τ(Dupoc)'s bit row (the table of `SPRIME_SOURCE_OF_TRUTH.md` §3, floor bits at their engine-side value). -/
def dupocRowA : Tmpl → Action
  | .coop => .C | .defect => .D | .tftSim => .C | .dupoc => .C | .ebot => .D | .obot => .D | .dbot => .D
  | .cupodTroll => .D | .cupod => .D | .dimcid => .D | .cimcic => .C | .prudent => .D
  | .maxconfidence => .C | .minconfidence => .C
  | _ => .D

/-! ### The compiled instances -/

theorem instCode_dupoc_tftSim (k : ℕ) : instCode k .dupoc .tftSim =
    pSearch k (templateCode (probe (inst (tauZoo k) .tftSim .dupoc))) (pConst 0) (pConst 1) := by
  unfold instCode; rw [inst_dupoc_peel_tftSim]; simp [actCode]

theorem instCode_dupoc_ebot (k : ℕ) : instCode k .dupoc .ebot =
    pSearch k (templateCode (probe (inst (tauZoo k) .ebot .dupoc))) (pConst 0) (pConst 1) := by
  unfold instCode; rw [inst_dupoc_peel_ebot]; simp [actCode]

theorem instCode_dupoc_obot (k : ℕ) : instCode k .dupoc .obot =
    pSearch k (templateCode (probe (inst (tauZoo k) .obot .dupoc))) (pConst 0) (pConst 1) := by
  unfold instCode
  rw [show inst (tauZoo k) .dupoc .obot = .search k (probe (inst (tauZoo k) .obot .dupoc)) (.const .C) (.const .D)
    from rfl]
  simp [actCode]

theorem instCode_dupoc_dbot (k : ℕ) : instCode k .dupoc .dbot =
    pSearch k (templateCode (probe (inst (tauZoo k) .dbot .dupoc))) (pConst 0) (pConst 1) := by
  unfold instCode
  rw [show inst (tauZoo k) .dupoc .dbot = .search k (probe (inst (tauZoo k) .dbot .dupoc)) (.const .C) (.const .D)
    from rfl]
  simp [actCode]

theorem instCode_dupoc_cupodTroll (k : ℕ) : instCode k .dupoc .cupodTroll =
    pSearch k (templateCode (probe (inst (tauZoo k) .cupodTroll .dupoc))) (pConst 0) (pConst 1) := by
  unfold instCode
  rw [show inst (tauZoo k) .dupoc .cupodTroll =
    .search k (probe (inst (tauZoo k) .cupodTroll .dupoc)) (.const .C) (.const .D) from rfl]
  simp [actCode]

/-- The diagonal: the quine. -/
theorem instCode_dupoc_dupoc (k : ℕ) : instCode k .dupoc .dupoc =
    pSearch k (templateCode (quineF .C)) (pConst 0) (pConst 1) := by
  unfold instCode; rw [inst_dupoc_quine]; simp [actCode]

/-! ### The slots -/

/-- **The diagonal: C by bounded Löb on the bot-wrapped quine** (`quine_found .C`). -/
theorem dupoc_quine_C : bitEventually .dupoc .dupoc .C := by
  obtain ⟨k₀, h⟩ := quine_found .C
  refine ⟨k₀, fun k hk ↦ bitPlays_of_eq (instCode_dupoc_dupoc k) ?_⟩
  exact ⟨_, search_then (quineF .C) (h k hk) (const_play 0 _ _ _)⟩

/-- τ(OBot)'s instance at Dupoc defects (a row slot of `obotRowSpecA`). -/
theorem col_obot_dupoc : bitEventually .obot .dupoc .D := obotRowSpecA.slot (by simp)

/-- `dupoc × obot`: the probe of a defecting instance is false — SND, D. -/
theorem dupoc_obot_D : bitEventually .dupoc .obot .D :=
  bitEventually.mono (fun k h ↦ dupocLike_D_of_probe_false (instCode_dupoc_obot k) rfl h) col_obot_dupoc

/-- **τ(Dupoc)'s row in `S'`** — the four non-entangled theorem slots. -/
@[tau_rowA]
theorem dupocRowSpecA : RowSpecA .dupoc [.coop, .defect, .dupoc, .obot] dupocRowA :=
  RowSpecA.cons col_dupoc_coop <|
  RowSpecA.cons (bitEventually.of_forall col_dupoc_defect) <|
  RowSpecA.cons dupoc_quine_C <|
  RowSpecA.cons dupoc_obot_D <|
  RowSpecA.nil _ _

/-! ### The floor bits — Dupoc's own probe is the hinge (floor SIDE) -/

/-- `dupoc × ebot` ‡ (base `dich_DupocBot_vs_EBot`): hinge = Dupoc's probe of τ(EBot)'s instance seeing Dupoc,
in the bit's frame; not found ⇒ D. -/
@[tau_floor_bitA]
theorem dupocRowSpecA_ebot_floor : FloorBitA .dupoc .ebot
    (fun k ↦ □[k] (guardCodeB (templateCode (probe (inst (tauZoo k) .ebot .dupoc)))
      (pBot (instCode k .dupoc .ebot)) (pBot (instCode k .dupoc .ebot)) k)) .D :=
  FloorBitA.of_not_hinge ⟨0, fun k _ hn ↦ dupocLike_floor_D (instCode_dupoc_ebot k) rfl hn⟩

/-- `dupoc × dbot` ‡ (base `dich_DupocBot_vs_DBot`). -/
@[tau_floor_bitA]
theorem dupocRowSpecA_dbot_floor : FloorBitA .dupoc .dbot
    (fun k ↦ □[k] (guardCodeB (templateCode (probe (inst (tauZoo k) .dbot .dupoc)))
      (pBot (instCode k .dupoc .dbot)) (pBot (instCode k .dupoc .dbot)) k)) .D :=
  FloorBitA.of_not_hinge ⟨0, fun k _ hn ↦ dupocLike_floor_D (instCode_dupoc_dbot k) rfl hn⟩

/-- `dupoc × cupodTroll` ‡ (base `dich_DupocBot_vs_CupodTrollBot`). -/
@[tau_floor_bitA]
theorem dupocRowSpecA_cupodTroll_floor : FloorBitA .dupoc .cupodTroll
    (fun k ↦ □[k] (guardCodeB (templateCode (probe (inst (tauZoo k) .cupodTroll .dupoc)))
      (pBot (instCode k .dupoc .cupodTroll)) (pBot (instCode k .dupoc .cupodTroll)) k)) .D :=
  FloorBitA.of_not_hinge ⟨0, fun k _ hn ↦ dupocLike_floor_D (instCode_dupoc_cupodTroll k) rfl hn⟩

end ArithS.Tau
