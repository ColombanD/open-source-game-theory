import ArithS.Tau.Quine
import ArithS.Tau.ClosedWatch
import ArithS.Tau.Entangled.DupocDupoc
import ArithS.Tau.Entangled.DimcidDupoc
import ArithS.Tau.Entangled.DupocCimcic
import ArithS.Tau.Entangled.DupocCupod
import ArithS.Tau.Entangled.DupocPrudent
import ArithS.Tau.Entangled.DimdidSys
import ArithS.Tau.Attr

/-!
# ArithS.Tau.Rows.Dupoc — τ(DupocBot)'s row in PA-`S'`

τ(Dupoc)'s instance at a hypothesis `T` that does not self-probe is one prove-stage on `T`'s instance seeing
Dupoc: `.search k (probe (inst T .dupoc)) C D` (`Tau/Zoo.inst_dupoc_peel_*`). Its DIAGONAL is the quine
`.search k (.plays .self .self C) C D` (`inst_dupoc_quine`), closed by bounded Löb on the bot-wrapped instance
(`Tau/Quine.quine_found`). Engine twin: `Tau/Theorems/TauDupoc/Phase.lean` (`dupocRowSpec`).

Slots stated here (`[coop, defect, tftSim, dupoc, obot, dimcid, cimcic, maxconfidence, minconfidence]`): `coop` C (POS on
the frozen cooperator, `col_dupoc_coop`), `defect` D (SND, `col_dupoc_defect`), `tftSim` C (Phase 3e: Dupoc's probe of
τ(TFTSim)'s instance — a run-stage watch over Dupoc's own instance at the cooperator — is a TRUE closed probe of a
budget-carrying watch; under budget abstraction the stored template is a constant and the watch is a `k̂`-tower, so
the probe is a conditional `TAct`-theorem found by the `k̂`-chain, `Tau/ClosedWatch.dupoc_tftSim_C`), the diagonal C (Löb), `obot` D (SND:
τ(OBot)'s instance at Dupoc defects — its second defection watch sees Dupoc's instance defect against the defector —
so the probe is false); and the ENTANGLED slots (`.sys` systems on the member slots, `Tau/Entangled/`, Phase 3c):
`dimcid` D (the DIMCID member defects by its self-fulfilling family, so Dupoc's probe is false — `ent_dupoc_dimcid`),
`cimcic` C (mutual Löb on the member slots, `ent_dupoc_cimcic`), `maxconfidence`/`minconfidence` C (the symmetric
system of two Dupoc-spec self-probers, `ent_dupoc_maxconfidence`/`ent_dupoc_minconfidence`).

**Floor bits** (`‡`, five, all on THIS side): `ebot`, `dbot`, `cupodTroll` — the hinge is Dupoc's OWN probe of the
hypothesis's instance (true in ℕ: the partner's C runs through Dupoc's else-play; base
`dich_DupocBot_vs_EBot/DBot/CupodTrollBot`); when it is not found, the else-branch D (`FloorBitA.of_not_hinge` +
`search_else`) — and the two system floors `cupod` (the tau image of the RED CELL, a floor in `S'` although the base
cell is a theorem: `Tau/Entangled/DupocCupod.lean`) and `prudent` (base `dich_PrudentBot_vs_DupocBot`), whose hinge
is the Dupoc member's own probe in the bit's frame.

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
    pSearch k (templateCodeAt (probe (inst (tauZoo k) .tftSim .dupoc)) k) (pConst 0) (pConst 1) := by
  unfold instCode; rw [inst_dupoc_peel_tftSim]; simp [actCode]

theorem instCode_dupoc_ebot (k : ℕ) : instCode k .dupoc .ebot =
    pSearch k (templateCodeAt (probe (inst (tauZoo k) .ebot .dupoc)) k) (pConst 0) (pConst 1) := by
  unfold instCode; rw [inst_dupoc_peel_ebot]; simp [actCode]

theorem instCode_dupoc_obot (k : ℕ) : instCode k .dupoc .obot =
    pSearch k (templateCodeAt (probe (inst (tauZoo k) .obot .dupoc)) k) (pConst 0) (pConst 1) := by
  unfold instCode
  rw [show inst (tauZoo k) .dupoc .obot = .search k (probe (inst (tauZoo k) .obot .dupoc)) (.const .C) (.const .D)
    from rfl]
  simp [actCode]

theorem instCode_dupoc_dbot (k : ℕ) : instCode k .dupoc .dbot =
    pSearch k (templateCodeAt (probe (inst (tauZoo k) .dbot .dupoc)) k) (pConst 0) (pConst 1) := by
  unfold instCode
  rw [show inst (tauZoo k) .dupoc .dbot = .search k (probe (inst (tauZoo k) .dbot .dupoc)) (.const .C) (.const .D)
    from rfl]
  simp [actCode]

theorem instCode_dupoc_cupodTroll (k : ℕ) : instCode k .dupoc .cupodTroll =
    pSearch k (templateCodeAt (probe (inst (tauZoo k) .cupodTroll .dupoc)) k) (pConst 0) (pConst 1) := by
  unfold instCode
  rw [show inst (tauZoo k) .dupoc .cupodTroll =
    .search k (probe (inst (tauZoo k) .cupodTroll .dupoc)) (.const .C) (.const .D) from rfl]
  simp [actCode]

theorem instCode_dupoc_dupocTroll (k : ℕ) : instCode k .dupoc .dupocTroll =
    pSearch k (templateCodeAt (probe (inst (tauZoo k) .dupocTroll .dupoc)) k) (pConst 0) (pConst 1) := by
  unfold instCode
  rw [show inst (tauZoo k) .dupoc .dupocTroll =
    .search k (probe (inst (tauZoo k) .dupocTroll .dupoc)) (.const .C) (.const .D) from rfl]
  simp [actCode]

/-- The diagonal: the quine. -/
theorem instCode_dupoc_dupoc (k : ℕ) : instCode k .dupoc .dupoc =
    pSearch k (templateCode (quineF .C)) (pConst 0) (pConst 1) := by
  unfold instCode; rw [inst_dupoc_quine]; rw [progCode_search_noSnap _ _ _ _ rfl]; simp [actCode]

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
  bitEventually.mono (fun k h ↦ dupocLike_D_of_probe_false_at (instCode_dupoc_obot k) rfl h) col_obot_dupoc

/-- `dupoc × dupocTroll` (2026-10-19): the troll DEFECTS on Dupoc, so Dupoc's probe of its instance is false — SND, D.
A theorem slot where `dupoc × cupodTroll` is a floor bit: the troll it hunts cannot be fooled by its own else-play. -/
theorem dupoc_dupocTroll_D : bitEventually .dupoc .dupocTroll .D :=
  bitEventually.mono (fun k h ↦ dupocLike_D_of_probe_false_at (instCode_dupoc_dupocTroll k) rfl h) (dupocTroll_rec_D .dupoc rfl)

/-- **τ(Dupoc)'s row in `S'`** — the ten theorem slots (six non-entangled, four entangled). -/
@[tau_rowA]
theorem dupocRowSpecA : RowSpecA .dupoc
    [.coop, .defect, .tftSim, .dupoc, .obot, .dupocTroll, .dimcid, .cimcic, .maxconfidence, .minconfidence] dupocRowA :=
  RowSpecA.cons col_dupoc_coop <|
  RowSpecA.cons (bitEventually.of_forall col_dupoc_defect) <|
  RowSpecA.cons dupoc_tftSim_C <|
  RowSpecA.cons dupoc_quine_C <|
  RowSpecA.cons dupoc_obot_D <|
  RowSpecA.cons dupoc_dupocTroll_D <|
  RowSpecA.cons ent_dupoc_dimcid <|
  RowSpecA.cons ent_dupoc_cimcic <|
  RowSpecA.cons ent_dupoc_maxconfidence <|
  RowSpecA.cons ent_dupoc_minconfidence <|
  RowSpecA.nil _ _

/-! ### The floor bits — Dupoc's own probe is the hinge (floor SIDE) -/

/-- `dupoc × ebot` ‡ (base `dich_DupocBot_vs_EBot`): hinge = Dupoc's probe of τ(EBot)'s instance seeing Dupoc,
in the bit's frame; not found ⇒ D. -/
@[tau_floor_bitA]
theorem dupocRowSpecA_ebot_floor : FloorBitA .dupoc .ebot
    (fun k ↦ □[k] (guardCodeB (templateCode (probe (inst (tauZoo k) .ebot .dupoc)))
      (pBot (instCode k .dupoc .ebot)) (pBot (instCode k .dupoc .ebot)) k)) .D :=
  FloorBitA.of_not_hinge ⟨0, fun k _ hn ↦ dupocLike_floor_D_at (instCode_dupoc_ebot k) rfl hn⟩

/-- `dupoc × dbot` ‡ (base `dich_DupocBot_vs_DBot`). -/
@[tau_floor_bitA]
theorem dupocRowSpecA_dbot_floor : FloorBitA .dupoc .dbot
    (fun k ↦ □[k] (guardCodeB (templateCode (probe (inst (tauZoo k) .dbot .dupoc)))
      (pBot (instCode k .dupoc .dbot)) (pBot (instCode k .dupoc .dbot)) k)) .D :=
  FloorBitA.of_not_hinge ⟨0, fun k _ hn ↦ dupocLike_floor_D_at (instCode_dupoc_dbot k) rfl hn⟩

/-- `dupoc × cupodTroll` ‡ (base `dich_DupocBot_vs_CupodTrollBot`). -/
@[tau_floor_bitA]
theorem dupocRowSpecA_cupodTroll_floor : FloorBitA .dupoc .cupodTroll
    (fun k ↦ □[k] (guardCodeB (templateCode (probe (inst (tauZoo k) .cupodTroll .dupoc)))
      (pBot (instCode k .dupoc .cupodTroll)) (pBot (instCode k .dupoc .cupodTroll)) k)) .D :=
  FloorBitA.of_not_hinge ⟨0, fun k _ hn ↦ dupocLike_floor_D_at (instCode_dupoc_cupodTroll k) rfl hn⟩

/-! ### The system floor bits — the Dupoc member's own probe is the hinge (`Tau/Entangled/`) -/

/-- `dupoc × cupod` ‡ — the tau image of the red cell `outcome_DupocBot_vs_CupodBot = (D, C)`, a FLOOR in `S'`
(no τ-symmetry inside one system; `Tau/Entangled/DupocCupod.lean`): D when the Dupoc member's probe of the Cupod
member is not found. -/
@[tau_floor_bitA]
theorem dupocRowSpecA_cupod_floor : FloorBitA .dupoc .cupod
    (fun k ↦ □[k] (guardCodeB (templateCode (.plays (.bot (.sys (sys2 (dm 1 k) (cm 0 k)) 1))
      (.bot (.sys (sys2 (dm 1 k) (cm 0 k)) 1)) .C))
      (pBot (instCode k .dupoc .cupod)) (pBot (instCode k .dupoc .cupod)) k)) .D :=
  entFloor_dupoc_cupod

/-- `dupoc × dimdid` ‡ (base `dich_DIMDID_vs_DupocBot`, 2026-10-19): D when the Dupoc member's probe of the DIMDID
member is not found — DIMDID's cooperation is an else-play (`Tau/Entangled/DimdidSys.lean`). -/
@[tau_floor_bitA]
theorem dupocRowSpecA_dimdid_floor : FloorBitA .dupoc .dimdid
    (fun k ↦ □[k] (guardCodeB (templateCode (.plays (.bot (.sys (sys2 (dm 1 k) (ddm 0 k)) 1))
      (.bot (.sys (sys2 (dm 1 k) (ddm 0 k)) 1)) .C))
      (pBot (instCode k .dupoc .dimdid)) (pBot (instCode k .dupoc .dimdid)) k)) .D :=
  entFloor_dupoc_dimdid

/-- `dupoc × prudent` ‡ (base `dich_PrudentBot_vs_DupocBot`): D when the Dupoc member's probe of the Prudent member
is not found (`Tau/Entangled/DupocPrudent.lean`). -/

@[tau_floor_bitA]
theorem dupocRowSpecA_prudent_floor : FloorBitA .dupoc .prudent
    (fun k ↦ □[k] (guardCodeB (templateCode (.plays (.bot (.sys (sys2 (dm 1 k) (pm 0 k .dupoc)) 1))
      (.bot (.sys (sys2 (dm 1 k) (pm 0 k .dupoc)) 1)) .C))
      (pBot (instCode k .dupoc .prudent)) (pBot (instCode k .dupoc .prudent)) k)) .D :=
  entFloor_dupoc_prudent

end ArithS.Tau
