import ArithS.Tau.Quine
import ArithS.Tau.ClosedProbe
import ArithS.Tau.Entangled.DimcidCupod
import ArithS.Tau.Entangled.DupocCupod
import ArithS.Tau.Entangled.CupodCimcic
import ArithS.Tau.Entangled.CupodPrudent
import ArithS.Tau.Attr

/-!
# ArithS.Tau.Rows.Cupod — τ(CupodBot)'s row in PA-`S'`

τ(Cupod)'s instance at a hypothesis `T` that does not self-probe is one DEFECTION prove-stage on `T`'s instance
seeing Cupod: `.search k (probeD (inst T .cupod)) D C` (`Tau/Zoo.inst_cupod_peel_*`); its diagonal is the quine
`.search k (.plays .self .self D) D C` (`inst_cupod_quine`), closed by bounded Löb on the bot-wrapped instance
(`Tau/Quine.quine_found .D` — Dupoc's argument with the polarity flipped: Cupod provably DEFECTS against
itself, Critch's twin cell). Engine twin: `Tau/Theorems/TauCupod/Phase.lean` (`cupodRowSpec`).

Slots stated here (`[coop, defect, tftSim, ebot, dbot, cupodTroll, cupod, dimcid]`): `coop` C (SND), `defect` D (POS),
`tftSim`/`ebot`/`dbot` C (SND: the hypothesis's instance at Cupod COOPERATES — τ(TFTSim) copies Cupod's C at the
cooperator, τ(EBot)'s reciprocity watch fires, τ(DBot) trusts Cupod's D at the defector — so the defection probe is
false), `cupodTroll` D (POS-above: τ(CupodTroll)'s instance at Cupod is the `.eq`-searcher `.search k (.eq C C) D C`,
which DEFECTS for large `k`, so Cupod's defection probe is a TRUE closed probe of a budget-carrying searcher — found
by the `k̂`-chain on the bot tower, `Tau/ClosedProbe.cupod_cupodTroll_found`), the diagonal D (Löb), and the
entangled `dimcid` D (the DIMCID member defects by its self-fulfilling family, so Cupod's punish-probe is a box
consequence of it — `Tau/Entangled/DimcidCupod.ent_cupod_dimcid`).

**Floor bits** (`‡`, six, floor SIDE): `obot` — hinge = Cupod's own defection probe of τ(OBot)'s instance seeing
Cupod (true in ℕ: OBot's second watch fires; base `dich_CupodBot_vs_OBot`); not found ⇒ else-branch C — and the five
system floors (`Tau/Entangled/`, the hinge the Cupod member's own punish-probe in the bit's frame): `dupoc`,
`maxconfidence`, `minconfidence` (the tau images of the RED CELL, floors in `S'` although the base cell is a theorem:
`DupocCupod.lean`), `cimcic` (base `dich_CIMCIC_vs_CupodBot`) and `prudent` (base `dich_CupodBot_vs_PrudentBot`).
-/

namespace ArithS.Tau

open PD PD.Tau

/-- τ(Cupod)'s bit row (floor bit at its engine-side value). -/
def cupodRowA : Tmpl → Action
  | .coop => .C | .defect => .D | .tftSim => .C | .dupoc => .C | .ebot => .C | .obot => .C | .dbot => .C
  | .cupodTroll => .D | .cupod => .D | .dimcid => .D | .cimcic => .C | .prudent => .C
  | .maxconfidence => .C | .minconfidence => .C
  | _ => .C

/-! ### The compiled instances -/

theorem instCode_cupod_tftSim (k : ℕ) : instCode k .cupod .tftSim =
    pSearch k (templateCodeAt (probeD (inst (tauZoo k) .tftSim .cupod)) k) (pConst 1) (pConst 0) := by
  unfold instCode; rw [inst_cupod_peel_tftSim]; simp [actCode]

theorem instCode_cupod_ebot (k : ℕ) : instCode k .cupod .ebot =
    pSearch k (templateCodeAt (probeD (inst (tauZoo k) .ebot .cupod)) k) (pConst 1) (pConst 0) := by
  unfold instCode; rw [inst_cupod_peel_ebot]; simp [actCode]

theorem instCode_cupod_obot (k : ℕ) : instCode k .cupod .obot =
    pSearch k (templateCodeAt (probeD (inst (tauZoo k) .obot .cupod)) k) (pConst 1) (pConst 0) := by
  unfold instCode; rw [inst_cupod_peel_obot]; simp [actCode]

theorem instCode_cupod_dbot (k : ℕ) : instCode k .cupod .dbot =
    pSearch k (templateCodeAt (probeD (inst (tauZoo k) .dbot .cupod)) k) (pConst 1) (pConst 0) := by
  unfold instCode; rw [inst_cupod_peel_dbot]; simp [actCode]

theorem instCode_cupod_cupodTroll (k : ℕ) : instCode k .cupod .cupodTroll =
    pSearch k (templateCodeAt (probeD (inst (tauZoo k) .cupodTroll .cupod)) k) (pConst 1) (pConst 0) := by
  unfold instCode; rw [inst_cupod_peel_cupodTroll]; simp [actCode]

/-- The diagonal: the quine, fire D. -/
theorem instCode_cupod_cupod (k : ℕ) : instCode k .cupod .cupod =
    pSearch k (templateCode (quineF .D)) (pConst 1) (pConst 0) := by
  unfold instCode; rw [inst_cupod_quine]; rw [progCode_search_noSnap _ _ _ _ rfl]; simp [actCode]

/-! ### The slots -/

/-- **The diagonal: D by bounded Löb on the bot-wrapped quine** (`quine_found .D`). -/
theorem cupod_quine_D : bitEventually .cupod .cupod .D := by
  obtain ⟨k₀, h⟩ := quine_found .D
  refine ⟨k₀, fun k hk ↦ bitPlays_of_eq (instCode_cupod_cupod k) ?_⟩
  exact ⟨_, search_then (quineF .D) (h k hk) (const_play 0 _ _ _)⟩

/-- The hypotheses' instances at Cupod that cooperate (row slots of the Phase-3a rows). -/
theorem col_tftSim_cupod : bitEventually .tftSim .cupod .C := tftSimRowSpecA.slot (by simp)
theorem col_ebot_cupod : bitEventually .ebot .cupod .C := ebotRowSpecA.slot (by simp)
theorem col_dbot_cupod : bitEventually .dbot .cupod .C := dbotRowSpecA.slot (by simp)

theorem cupod_tftSim_C : bitEventually .cupod .tftSim .C :=
  bitEventually.mono (fun k h ↦ cupod_C_of_probeD_false_at (instCode_cupod_tftSim k) rfl h) col_tftSim_cupod
theorem cupod_ebot_C : bitEventually .cupod .ebot .C :=
  bitEventually.mono (fun k h ↦ cupod_C_of_probeD_false_at (instCode_cupod_ebot k) rfl h) col_ebot_cupod
theorem cupod_dbot_C : bitEventually .cupod .dbot .C :=
  bitEventually.mono (fun k h ↦ cupod_C_of_probeD_false_at (instCode_cupod_dbot k) rfl h) col_dbot_cupod

/-- `cupod × cupodTroll`: the defection probe of the `.eq`-searcher is found — D (`cupod_cupodTroll_found`). -/
theorem cupod_cupodTroll_D : bitEventually .cupod .cupodTroll .D := by
  obtain ⟨k₀, h⟩ := cupod_cupodTroll_found
  refine ⟨k₀, fun k hk ↦ bitPlays_of_eq (instCode_cupod_cupodTroll k) ?_⟩
  have hf := h k hk
  rw [instCode_cupod_cupodTroll] at hf
  exact ⟨_, search_then_at _ hf (const_play 0 _ _ _) rfl⟩

/-- **τ(Cupod)'s row in `S'`** — the eight theorem slots (seven non-entangled, `dimcid` entangled). -/
@[tau_rowA]
theorem cupodRowSpecA : RowSpecA .cupod [.coop, .defect, .tftSim, .ebot, .dbot, .cupodTroll, .cupod, .dimcid] cupodRowA :=
  RowSpecA.cons (bitEventually.of_forall col_cupod_coop) <|
  RowSpecA.cons col_cupod_defect <|
  RowSpecA.cons cupod_tftSim_C <|
  RowSpecA.cons cupod_ebot_C <|
  RowSpecA.cons cupod_dbot_C <|
  RowSpecA.cons cupod_cupodTroll_D <|
  RowSpecA.cons cupod_quine_D <|
  RowSpecA.cons ent_cupod_dimcid <|
  RowSpecA.nil _ _

/-! ### The floor bit — Cupod's own defection probe is the hinge (floor SIDE) -/

/-- `cupod × obot` ‡ (base `dich_CupodBot_vs_OBot`): hinge = Cupod's defection probe of τ(OBot)'s instance seeing
Cupod, in the bit's frame; not found ⇒ C. -/
@[tau_floor_bitA]
theorem cupodRowSpecA_obot_floor : FloorBitA .cupod .obot
    (fun k ↦ □[k] (guardCodeB (templateCode (probeD (inst (tauZoo k) .obot .cupod)))
      (pBot (instCode k .cupod .obot)) (pBot (instCode k .cupod .obot)) k)) .C :=
  FloorBitA.of_not_hinge ⟨0, fun k _ hn ↦ cupod_floor_C_at (instCode_cupod_obot k) rfl hn⟩

/-! ### The system floor bits — the Cupod member's own punish-probe is the hinge (`Tau/Entangled/`) -/

/-- `cupod × dupoc` ‡ — the tau image of the red cell `outcome_DupocBot_vs_CupodBot = (D, C)`, a FLOOR in `S'`
(`Tau/Entangled/DupocCupod.lean`): C when the Cupod member's punish-probe of the Dupoc member is not found. -/
@[tau_floor_bitA]
theorem cupodRowSpecA_dupoc_floor : FloorBitA .cupod .dupoc
    (fun k ↦ □[k] (guardCodeB (templateCode (.plays (.bot (.sys (sys2 (cm 1 k) (dm 0 k)) 1))
      (.bot (.sys (sys2 (cm 1 k) (dm 0 k)) 1)) .D))
      (pBot (instCode k .cupod .dupoc)) (pBot (instCode k .cupod .dupoc)) k)) .C :=
  entFloor_cupod_dupoc

/-- `cupod × maxconfidence` ‡ (the red cell's image on the native; the same system). -/
@[tau_floor_bitA]
theorem cupodRowSpecA_maxconfidence_floor : FloorBitA .cupod .maxconfidence
    (fun k ↦ □[k] (guardCodeB (templateCode (.plays (.bot (.sys (sys2 (cm 1 k) (dm 0 k)) 1))
      (.bot (.sys (sys2 (cm 1 k) (dm 0 k)) 1)) .D))
      (pBot (instCode k .cupod .maxconfidence)) (pBot (instCode k .cupod .maxconfidence)) k)) .C :=
  entFloor_cupod_maxconfidence

/-- `cupod × minconfidence` ‡ (the red cell's image on the native; the same system). -/
@[tau_floor_bitA]
theorem cupodRowSpecA_minconfidence_floor : FloorBitA .cupod .minconfidence
    (fun k ↦ □[k] (guardCodeB (templateCode (.plays (.bot (.sys (sys2 (cm 1 k) (dm 0 k)) 1))
      (.bot (.sys (sys2 (cm 1 k) (dm 0 k)) 1)) .D))
      (pBot (instCode k .cupod .minconfidence)) (pBot (instCode k .cupod .minconfidence)) k)) .C :=
  entFloor_cupod_minconfidence

/-- `cupod × cimcic` ‡ (base `dich_CIMCIC_vs_CupodBot`): C when the Cupod member's punish-probe of the CIMCIC member
is not found (`Tau/Entangled/CupodCimcic.lean`). -/
@[tau_floor_bitA]
theorem cupodRowSpecA_cimcic_floor : FloorBitA .cupod .cimcic
    (fun k ↦ □[k] (guardCodeB (templateCode (.plays (.bot (.sys (sys2 (cm 1 k) (cim 0 k)) 1))
      (.bot (.sys (sys2 (cm 1 k) (cim 0 k)) 1)) .D))
      (pBot (instCode k .cupod .cimcic)) (pBot (instCode k .cupod .cimcic)) k)) .C :=
  entFloor_cupod_cimcic

/-- `cupod × prudent` ‡ (base `dich_CupodBot_vs_PrudentBot`): C when the Cupod member's punish-probe of the Prudent
member is not found (`Tau/Entangled/CupodPrudent.lean`). -/
@[tau_floor_bitA]
theorem cupodRowSpecA_prudent_floor : FloorBitA .cupod .prudent
    (fun k ↦ □[k] (guardCodeB (templateCode (.plays (.bot (.sys (sys2 (cm 1 k) (pm 0 k .cupod)) 1))
      (.bot (.sys (sys2 (cm 1 k) (pm 0 k .cupod)) 1)) .D))
      (pBot (instCode k .cupod .prudent)) (pBot (instCode k .cupod .prudent)) k)) .C :=
  entFloor_cupod_prudent

end ArithS.Tau
