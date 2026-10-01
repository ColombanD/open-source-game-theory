import ArithS.Tau.Quine
import ArithS.Tau.Attr

/-!
# ArithS.Tau.Rows.Prudent — τ(PrudentBot)'s row in PA-`S'` (the NON-entangled slots)

τ(Prudent)'s instance at a hypothesis `T` that does not self-probe is the nested shape of the base source:
the OUTER probe of `T`'s instance seeing Prudent, and in its then-branch the INNER prudence check "`T`'s instance at
the defector defects against itself"; D on either failure (`Tau/Zoo.inst_prudent_peel_*`). The diagonal is the
outer quine `.plays .self .self C` with the inner check on its own `defect` cell (`inst_prudent_quine`). Engine
twin: `Tau/Theorems/TauPrudent/Phase.lean` (`prudentRowSpec`, D everywhere but the mirror).

Slots stated here (`[coop, defect, tftSim, obot, dbot, cupodTroll]`), all D:
* `coop`, `defect` (`col_prudent_coop/defect`: the inner check fails at the cooperator, the outer at the defector);
* `tftSim`, `obot`: the OUTER probe is false — τ(TFTSim)'s and τ(OBot)'s instances at Prudent defect (they copy /
  watch Prudent's D at the cooperator) — SND, D;
* `dbot`, `cupodTroll`: the INNER check is false — τ(DBot)'s instance at the defector trusts (C), τ(CupodTroll)'s
  cooperates (its identity is false) — so the then-branch plays D too: D whatever the outer verdict
  (`search_either`).

**Floor bits** (`‡`, two, floor SIDE): `ebot` — hinge = Prudent's OUTER probe of τ(EBot)'s instance seeing
Prudent (base `dich_PrudentBot_vs_EBot`; the inner check against EBot is found there) — and the DIAGONAL
`prudent` — hinge = the outer quine `.plays .self .self C` in the bit's frame (base
`dich_PrudentBot_vs_PrudentBot`: single-tier prudence is self-defeating; the found world needs the inner probe
of its own `defect` cell, a budget-carrying closed probe — the `tftSim`-class box of `Rows/Dupoc.lean`'s TODO).
Not found ⇒ D.

-- Phase 3c: entangled — `dupoc cupod dimcid cimcic maxconfidence minconfidence` (`‡` at dupoc/cupod/cimcic/
--   maxconfidence/minconfidence in the table, all `.sys` systems).
-/

namespace ArithS.Tau

open PD PD.Tau

/-- τ(Prudent)'s bit row: D everywhere in the paper table. -/
def prudentRowA : Tmpl → Action
  | _ => .D

/-! ### The compiled instances -/

theorem instCode_prudent_tftSim (k : ℕ) : instCode k .prudent .tftSim =
    pSearch k (templateCode (probe (inst (tauZoo k) .tftSim .prudent)))
      (pSearch k (templateCode (probeD (inst (tauZoo k) .tftSim .defect))) (pConst 0) (pConst 1)) (pConst 1) := by
  unfold instCode; rw [inst_prudent_peel_tftSim]; simp [actCode]

theorem instCode_prudent_ebot (k : ℕ) : instCode k .prudent .ebot =
    pSearch k (templateCode (probe (inst (tauZoo k) .ebot .prudent)))
      (pSearch k (templateCode (probeD (inst (tauZoo k) .ebot .defect))) (pConst 0) (pConst 1)) (pConst 1) := by
  unfold instCode; rw [inst_prudent_peel_ebot]; simp [actCode]

theorem instCode_prudent_obot (k : ℕ) : instCode k .prudent .obot =
    pSearch k (templateCode (probe (inst (tauZoo k) .obot .prudent)))
      (pSearch k (templateCode (probeD (inst (tauZoo k) .obot .defect))) (pConst 0) (pConst 1)) (pConst 1) := by
  unfold instCode; rw [inst_prudent_peel_obot]; simp [actCode]

theorem instCode_prudent_dbot (k : ℕ) : instCode k .prudent .dbot =
    pSearch k (templateCode (probe (inst (tauZoo k) .dbot .prudent)))
      (pSearch k (templateCode (probeD (inst (tauZoo k) .dbot .defect))) (pConst 0) (pConst 1)) (pConst 1) := by
  unfold instCode; rw [inst_prudent_peel_dbot]; simp [actCode]

theorem instCode_prudent_cupodTroll (k : ℕ) : instCode k .prudent .cupodTroll =
    pSearch k (templateCode (probe (inst (tauZoo k) .cupodTroll .prudent)))
      (pSearch k (templateCode (probeD (inst (tauZoo k) .cupodTroll .defect))) (pConst 0) (pConst 1)) (pConst 1) := by
  unfold instCode; rw [inst_prudent_peel_cupodTroll]; simp [actCode]

/-- The diagonal: the outer quine, the inner check on its own `defect` cell. -/
theorem instCode_prudent_prudent (k : ℕ) : instCode k .prudent .prudent =
    pSearch k (templateCode (quineF .C))
      (pSearch k (templateCode (probeD (inst (tauZoo k) .prudent .defect))) (pConst 0) (pConst 1)) (pConst 1) := by
  unfold instCode; rw [inst_prudent_quine]; simp [actCode]

/-! ### The slots -/

/-- The hypotheses' instances at Prudent that defect (row slots of the Phase-3a rows). -/
theorem col_tftSim_prudent : bitEventually .tftSim .prudent .D := tftSimRowSpecA.slot (by simp)
theorem col_obot_prudent : bitEventually .obot .prudent .D := obotRowSpecA.slot (by simp)

theorem prudent_tftSim_D : bitEventually .prudent .tftSim .D :=
  bitEventually.mono (fun k h ↦ prudent_D_of_outer_false (instCode_prudent_tftSim k) rfl h) col_tftSim_prudent
theorem prudent_obot_D : bitEventually .prudent .obot .D :=
  bitEventually.mono (fun k h ↦ prudent_D_of_outer_false (instCode_prudent_obot k) rfl h) col_obot_prudent
theorem prudent_dbot_D (k : ℕ) : bitPlays k .prudent .dbot .D :=
  prudent_D_of_inner_false (instCode_prudent_dbot k) rfl rfl (col_dbot_defect k)
theorem prudent_cupodTroll_D (k : ℕ) : bitPlays k .prudent .cupodTroll .D :=
  prudent_D_of_inner_false (instCode_prudent_cupodTroll k) rfl rfl (col_cupodTroll_defect k)

/-- **τ(Prudent)'s row in `S'`** — the six non-entangled theorem slots. -/
@[tau_rowA]
theorem prudentRowSpecA : RowSpecA .prudent [.coop, .defect, .tftSim, .obot, .dbot, .cupodTroll] prudentRowA :=
  RowSpecA.cons (bitEventually.of_forall col_prudent_coop) <|
  RowSpecA.cons (bitEventually.of_forall col_prudent_defect) <|
  RowSpecA.cons prudent_tftSim_D <|
  RowSpecA.cons prudent_obot_D <|
  RowSpecA.cons (bitEventually.of_forall prudent_dbot_D) <|
  RowSpecA.cons (bitEventually.of_forall prudent_cupodTroll_D) <|
  RowSpecA.nil _ _

/-! ### The floor bits — Prudent's own OUTER probe is the hinge (floor SIDE) -/

/-- `prudent × ebot` ‡ (base `dich_PrudentBot_vs_EBot`): hinge = Prudent's outer probe of τ(EBot)'s instance seeing
Prudent, in the bit's frame; not found ⇒ D. -/
@[tau_floor_bitA]
theorem prudentRowSpecA_ebot_floor : FloorBitA .prudent .ebot
    (fun k ↦ □[k] (guardCodeB (templateCode (probe (inst (tauZoo k) .ebot .prudent)))
      (pBot (instCode k .prudent .ebot)) (pBot (instCode k .prudent .ebot)) k)) .D :=
  FloorBitA.of_not_hinge ⟨0, fun k _ hn ↦ prudent_floor_D (instCode_prudent_ebot k) rfl hn⟩

/-- `prudent × prudent` ‡ (base `dich_PrudentBot_vs_PrudentBot`): hinge = the outer quine "I cooperate with
myself", in the bit's frame; not found ⇒ D. -/
@[tau_floor_bitA]
theorem prudentRowSpecA_prudent_floor : FloorBitA .prudent .prudent
    (fun k ↦ □[k] (guardCodeB (templateCode (.plays .self .self .C))
      (pBot (instCode k .prudent .prudent)) (pBot (instCode k .prudent .prudent)) k)) .D :=
  FloorBitA.of_not_hinge ⟨0, fun k _ hn ↦ prudent_floor_D (instCode_prudent_prudent k) rfl hn⟩

end ArithS.Tau
