import ArithS.Tau.Quine
import ArithS.Tau.Entangled.DupocPrudent
import ArithS.Tau.Entangled.CupodPrudent
import ArithS.Tau.Entangled.CimcicPrudent
import ArithS.Tau.Attr

/-!
# ArithS.Tau.Rows.Prudent — τ(PrudentBot)'s row in PA-`S'`

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

**Floor bits** (`‡`, seven, floor SIDE): `ebot` — hinge = Prudent's OUTER probe of τ(EBot)'s instance seeing
Prudent (base `dich_PrudentBot_vs_EBot`; the inner check against EBot is found there) — and the DIAGONAL
`prudent` — hinge = the outer quine `.plays .self .self C` in the bit's frame (base
`dich_PrudentBot_vs_PrudentBot`: single-tier prudence is self-defeating; the found world needs the inner probe
of its own `defect` cell, a budget-carrying closed probe — the `tftSim`-class box of `Rows/Dupoc.lean`'s TODO).
Not found ⇒ D. And the five SYSTEM floors `dupoc`, `maxconfidence`, `minconfidence` (base
`dich_PrudentBot_vs_DupocBot`), `cupod` (base `dich_PrudentBot_vs_CupodBot`), `cimcic` (base
`dich_CIMCIC_vs_PrudentBot`) — hinge = the Prudent member's OUTER probe of the partner member, in the bit's frame
(`Tau/Entangled/DupocPrudent.lean`, `CupodPrudent.lean`, `CimcicPrudent.lean`: the Prudent member's inner guard
freezes a budget-carrying third party, so no Löb family can be stated — the §7 obstacle; the dichotomy halves are
what `S'` settles).

-- UNSTATED (decision pending — `SPRIME_SOURCE_OF_TRUTH.md` §3, the budget-snapshot obstruction): slot `.dimcid`
--   (`inst prudent dimcid = .sys [pm 1 dimcid, dim 0] 0`, the same obstacle on the Prudent member).
-/

namespace ArithS.Tau

open PD PD.Tau

/-- τ(Prudent)'s bit row: D everywhere in the paper table. -/
def prudentRowA : Tmpl → Action
  | _ => .D

/-! ### The compiled instances -/

theorem instCode_prudent_tftSim (k : ℕ) : instCode k .prudent .tftSim =
    pSearch k (templateCodeAt (probe (inst (tauZoo k) .tftSim .prudent)) k)
      (pSearch k (templateCode (probeD (inst (tauZoo k) .tftSim .defect))) (pConst 0) (pConst 1)) (pConst 1) := by
  unfold instCode; rw [inst_prudent_peel_tftSim]; rw [progCode_search, progCode_search_noSnap k (probeD (inst (tauZoo k) .tftSim .defect)) _ _ rfl]; simp [actCode]

theorem instCode_prudent_ebot (k : ℕ) : instCode k .prudent .ebot =
    pSearch k (templateCodeAt (probe (inst (tauZoo k) .ebot .prudent)) k)
      (pSearch k (templateCode (probeD (inst (tauZoo k) .ebot .defect))) (pConst 0) (pConst 1)) (pConst 1) := by
  unfold instCode; rw [inst_prudent_peel_ebot]; rw [progCode_search, progCode_search_noSnap k (probeD (inst (tauZoo k) .ebot .defect)) _ _ rfl]; simp [actCode]

theorem instCode_prudent_obot (k : ℕ) : instCode k .prudent .obot =
    pSearch k (templateCodeAt (probe (inst (tauZoo k) .obot .prudent)) k)
      (pSearch k (templateCode (probeD (inst (tauZoo k) .obot .defect))) (pConst 0) (pConst 1)) (pConst 1) := by
  unfold instCode; rw [inst_prudent_peel_obot]; rw [progCode_search, progCode_search_noSnap k (probeD (inst (tauZoo k) .obot .defect)) _ _ rfl]; simp [actCode]

theorem instCode_prudent_dbot (k : ℕ) : instCode k .prudent .dbot =
    pSearch k (templateCodeAt (probe (inst (tauZoo k) .dbot .prudent)) k)
      (pSearch k (templateCode (probeD (inst (tauZoo k) .dbot .defect))) (pConst 0) (pConst 1)) (pConst 1) := by
  unfold instCode; rw [inst_prudent_peel_dbot]; rw [progCode_search, progCode_search_noSnap k (probeD (inst (tauZoo k) .dbot .defect)) _ _ rfl]; simp [actCode]

theorem instCode_prudent_cupodTroll (k : ℕ) : instCode k .prudent .cupodTroll =
    pSearch k (templateCodeAt (probe (inst (tauZoo k) .cupodTroll .prudent)) k)
      (pSearch k (templateCodeAt (probeD (inst (tauZoo k) .cupodTroll .defect)) k) (pConst 0) (pConst 1)) (pConst 1) := by
  unfold instCode; rw [inst_prudent_peel_cupodTroll]; simp [actCode]

/-- The diagonal: the outer quine, the inner check on its own `defect` cell. -/
theorem instCode_prudent_prudent (k : ℕ) : instCode k .prudent .prudent =
    pSearch k (templateCode (quineF .C))
      (pSearch k (templateCodeAt (probeD (inst (tauZoo k) .prudent .defect)) k) (pConst 0) (pConst 1)) (pConst 1) := by
  unfold instCode; rw [inst_prudent_quine]; rw [progCode_search_noSnap k (quineF .C) _ _ rfl]; simp [actCode]

/-! ### The slots -/

/-- The hypotheses' instances at Prudent that defect (row slots of the Phase-3a rows). -/
theorem col_tftSim_prudent : bitEventually .tftSim .prudent .D := tftSimRowSpecA.slot (by simp)
theorem col_obot_prudent : bitEventually .obot .prudent .D := obotRowSpecA.slot (by simp)

theorem prudent_tftSim_D : bitEventually .prudent .tftSim .D :=
  bitEventually.mono (fun k h ↦ prudent_D_of_outer_false_at (instCode_prudent_tftSim k) rfl h) col_tftSim_prudent
theorem prudent_obot_D : bitEventually .prudent .obot .D :=
  bitEventually.mono (fun k h ↦ prudent_D_of_outer_false_at (instCode_prudent_obot k) rfl h) col_obot_prudent
theorem prudent_dbot_D (k : ℕ) : bitPlays k .prudent .dbot .D :=
  prudent_D_of_inner_false_at (instCode_prudent_dbot k) rfl rfl (col_dbot_defect k)
theorem prudent_cupodTroll_D (k : ℕ) : bitPlays k .prudent .cupodTroll .D :=
  prudent_D_of_inner_false_at₂ (instCode_prudent_cupodTroll k) rfl rfl (col_cupodTroll_defect k)

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
  FloorBitA.of_not_hinge ⟨0, fun k _ hn ↦ prudent_floor_D_at (instCode_prudent_ebot k) rfl hn⟩

/-- `prudent × prudent` ‡ (base `dich_PrudentBot_vs_PrudentBot`): hinge = the outer quine "I cooperate with
myself", in the bit's frame; not found ⇒ D. -/
@[tau_floor_bitA]
theorem prudentRowSpecA_prudent_floor : FloorBitA .prudent .prudent
    (fun k ↦ □[k] (guardCodeB (templateCode (.plays .self .self .C))
      (pBot (instCode k .prudent .prudent)) (pBot (instCode k .prudent .prudent)) k)) .D :=
  FloorBitA.of_not_hinge ⟨0, fun k _ hn ↦ prudent_floor_D (instCode_prudent_prudent k) rfl hn⟩

/-! ### The system floor bits — the Prudent member's OUTER probe is the hinge (`Tau/Entangled/`) -/

/-- `prudent × dupoc` ‡ (base `dich_PrudentBot_vs_DupocBot`): D when the Prudent member's outer probe of the Dupoc
member is not found (`Tau/Entangled/DupocPrudent.lean`). -/
@[tau_floor_bitA]
theorem prudentRowSpecA_dupoc_floor : FloorBitA .prudent .dupoc
    (fun k ↦ □[k] (guardCodeB (templateCode (.plays (.bot (.sys (sys2 (pm 1 k .dupoc) (dm 0 k)) 1))
      (.bot (.sys (sys2 (pm 1 k .dupoc) (dm 0 k)) 1)) .C))
      (pBot (instCode k .prudent .dupoc)) (pBot (instCode k .prudent .dupoc)) k)) .D :=
  entFloor_prudent_dupoc

/-- `prudent × maxconfidence` ‡ (Dupoc's spec on the native; base `dich_PrudentBot_vs_DupocBot`). -/
@[tau_floor_bitA]
theorem prudentRowSpecA_maxconfidence_floor : FloorBitA .prudent .maxconfidence
    (fun k ↦ □[k] (guardCodeB (templateCode (.plays (.bot (.sys (sys2 (pm 1 k .maxconfidence) (dm 0 k)) 1))
      (.bot (.sys (sys2 (pm 1 k .maxconfidence) (dm 0 k)) 1)) .C))
      (pBot (instCode k .prudent .maxconfidence)) (pBot (instCode k .prudent .maxconfidence)) k)) .D :=
  entFloor_prudent_maxconfidence

/-- `prudent × minconfidence` ‡ (Dupoc's spec on the native; base `dich_PrudentBot_vs_DupocBot`). -/
@[tau_floor_bitA]
theorem prudentRowSpecA_minconfidence_floor : FloorBitA .prudent .minconfidence
    (fun k ↦ □[k] (guardCodeB (templateCode (.plays (.bot (.sys (sys2 (pm 1 k .minconfidence) (dm 0 k)) 1))
      (.bot (.sys (sys2 (pm 1 k .minconfidence) (dm 0 k)) 1)) .C))
      (pBot (instCode k .prudent .minconfidence)) (pBot (instCode k .prudent .minconfidence)) k)) .D :=
  entFloor_prudent_minconfidence

/-- `prudent × cupod` ‡ (base `dich_PrudentBot_vs_CupodBot`): D when the Prudent member's outer probe of the Cupod
member is not found (`Tau/Entangled/CupodPrudent.lean`). -/
@[tau_floor_bitA]
theorem prudentRowSpecA_cupod_floor : FloorBitA .prudent .cupod
    (fun k ↦ □[k] (guardCodeB (templateCode (.plays (.bot (.sys (sys2 (pm 1 k .cupod) (cm 0 k)) 1))
      (.bot (.sys (sys2 (pm 1 k .cupod) (cm 0 k)) 1)) .C))
      (pBot (instCode k .prudent .cupod)) (pBot (instCode k .prudent .cupod)) k)) .D :=
  entFloor_prudent_cupod

/-- `prudent × cimcic` ‡ (base `dich_CIMCIC_vs_PrudentBot`): D when the Prudent member's outer probe of the CIMCIC
member is not found (`Tau/Entangled/CimcicPrudent.lean`). -/
@[tau_floor_bitA]
theorem prudentRowSpecA_cimcic_floor : FloorBitA .prudent .cimcic
    (fun k ↦ □[k] (guardCodeB (templateCode (.plays (.bot (.sys (sys2 (pm 1 k .cimcic) (cim 0 k)) 1))
      (.bot (.sys (sys2 (pm 1 k .cimcic) (cim 0 k)) 1)) .C))
      (pBot (instCode k .prudent .cimcic)) (pBot (instCode k .prudent .cimcic)) k)) .D :=
  entFloor_prudent_cimcic

end ArithS.Tau
