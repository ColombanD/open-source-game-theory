import ArithS.Tau.Quine
import ArithS.Tau.ClosedProbe
import ArithS.Tau.Attr

/-!
# ArithS.Tau.Rows.Cupod — τ(CupodBot)'s row in PA-`S'` (the NON-entangled slots)

τ(Cupod)'s instance at a hypothesis `T` that does not self-probe is one DEFECTION prove-stage on `T`'s instance
seeing Cupod: `.search k (probeD (inst T .cupod)) D C` (`Tau/Zoo.inst_cupod_peel_*`); its diagonal is the quine
`.search k (.plays .self .self D) D C` (`inst_cupod_quine`), closed by bounded Löb on the bot-wrapped instance
(`Tau/Quine.quine_found .D` — Dupoc's argument with the polarity flipped: Cupod provably DEFECTS against
itself, Critch's twin cell). Engine twin: `Tau/Theorems/TauCupod/Phase.lean` (`cupodRowSpec`).

Slots stated here (`[coop, defect, tftSim, ebot, dbot, cupodTroll, cupod]`): `coop` C (SND), `defect` D (POS),
`tftSim`/`ebot`/`dbot` C (SND: the hypothesis's instance at Cupod COOPERATES — τ(TFTSim) copies Cupod's C at the
cooperator, τ(EBot)'s reciprocity watch fires, τ(DBot) trusts Cupod's D at the defector — so the defection probe is
false), `cupodTroll` D (POS-above: τ(CupodTroll)'s instance at Cupod is the `.eq`-searcher `.search k (.eq C C) D C`,
which DEFECTS for large `k`, so Cupod's defection probe is a TRUE closed probe of a budget-carrying searcher — found
by the `k̂`-chain on the bot tower, `Tau/ClosedProbe.cupod_cupodTroll_found`), the diagonal D (Löb).

**Floor bit** (`‡`, one, floor SIDE): `obot` — hinge = Cupod's own defection probe of τ(OBot)'s instance seeing
Cupod (true in ℕ: OBot's second watch fires; base `dich_CupodBot_vs_OBot`); not found ⇒ else-branch C.

-- Phase 3c: entangled — `dupoc dimcid cimcic prudent maxconfidence minconfidence`.
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
    pSearch k (templateCode (probeD (inst (tauZoo k) .tftSim .cupod))) (pConst 1) (pConst 0) := by
  unfold instCode; rw [inst_cupod_peel_tftSim]; simp [actCode]

theorem instCode_cupod_ebot (k : ℕ) : instCode k .cupod .ebot =
    pSearch k (templateCode (probeD (inst (tauZoo k) .ebot .cupod))) (pConst 1) (pConst 0) := by
  unfold instCode; rw [inst_cupod_peel_ebot]; simp [actCode]

theorem instCode_cupod_obot (k : ℕ) : instCode k .cupod .obot =
    pSearch k (templateCode (probeD (inst (tauZoo k) .obot .cupod))) (pConst 1) (pConst 0) := by
  unfold instCode; rw [inst_cupod_peel_obot]; simp [actCode]

theorem instCode_cupod_dbot (k : ℕ) : instCode k .cupod .dbot =
    pSearch k (templateCode (probeD (inst (tauZoo k) .dbot .cupod))) (pConst 1) (pConst 0) := by
  unfold instCode; rw [inst_cupod_peel_dbot]; simp [actCode]

theorem instCode_cupod_cupodTroll (k : ℕ) : instCode k .cupod .cupodTroll =
    pSearch k (templateCode (probeD (inst (tauZoo k) .cupodTroll .cupod))) (pConst 1) (pConst 0) := by
  unfold instCode; rw [inst_cupod_peel_cupodTroll]; simp [actCode]

/-- The diagonal: the quine, fire D. -/
theorem instCode_cupod_cupod (k : ℕ) : instCode k .cupod .cupod =
    pSearch k (templateCode (quineF .D)) (pConst 1) (pConst 0) := by
  unfold instCode; rw [inst_cupod_quine]; simp [actCode]

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
  bitEventually.mono (fun k h ↦ cupod_C_of_probeD_false (instCode_cupod_tftSim k) rfl h) col_tftSim_cupod
theorem cupod_ebot_C : bitEventually .cupod .ebot .C :=
  bitEventually.mono (fun k h ↦ cupod_C_of_probeD_false (instCode_cupod_ebot k) rfl h) col_ebot_cupod
theorem cupod_dbot_C : bitEventually .cupod .dbot .C :=
  bitEventually.mono (fun k h ↦ cupod_C_of_probeD_false (instCode_cupod_dbot k) rfl h) col_dbot_cupod

/-- `cupod × cupodTroll`: the defection probe of the `.eq`-searcher is found — D (`cupod_cupodTroll_found`). -/
theorem cupod_cupodTroll_D : bitEventually .cupod .cupodTroll .D := by
  obtain ⟨k₀, h⟩ := cupod_cupodTroll_found
  refine ⟨k₀, fun k hk ↦ bitPlays_of_eq (instCode_cupod_cupodTroll k) ?_⟩
  have hf := h k hk
  rw [instCode_cupod_cupodTroll] at hf
  exact ⟨_, search_then _ hf (const_play 0 _ _ _) rfl⟩

/-- **τ(Cupod)'s row in `S'`** — the seven non-entangled theorem slots. -/
@[tau_rowA]
theorem cupodRowSpecA : RowSpecA .cupod [.coop, .defect, .tftSim, .ebot, .dbot, .cupodTroll, .cupod] cupodRowA :=
  RowSpecA.cons (bitEventually.of_forall col_cupod_coop) <|
  RowSpecA.cons col_cupod_defect <|
  RowSpecA.cons cupod_tftSim_C <|
  RowSpecA.cons cupod_ebot_C <|
  RowSpecA.cons cupod_dbot_C <|
  RowSpecA.cons cupod_cupodTroll_D <|
  RowSpecA.cons cupod_quine_D <|
  RowSpecA.nil _ _

/-! ### The floor bit — Cupod's own defection probe is the hinge (floor SIDE) -/

/-- `cupod × obot` ‡ (base `dich_CupodBot_vs_OBot`): hinge = Cupod's defection probe of τ(OBot)'s instance seeing
Cupod, in the bit's frame; not found ⇒ C. -/
@[tau_floor_bitA]
theorem cupodRowSpecA_obot_floor : FloorBitA .cupod .obot
    (fun k ↦ □[k] (guardCodeB (templateCode (probeD (inst (tauZoo k) .obot .cupod)))
      (pBot (instCode k .cupod .obot)) (pBot (instCode k .cupod .obot)) k)) .C :=
  FloorBitA.of_not_hinge ⟨0, fun k _ hn ↦ cupod_floor_C (instCode_cupod_obot k) rfl hn⟩

end ArithS.Tau
