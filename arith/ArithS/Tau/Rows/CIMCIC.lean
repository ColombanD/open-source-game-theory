import ArithS.Tau.Quine
import ArithS.Tau.ClosedWatch
import ArithS.Tau.Entangled.DupocCimcic
import ArithS.Tau.Entangled.DimcidCimcic
import ArithS.Tau.Entangled.CupodCimcic
import ArithS.Tau.Entangled.CimcicPrudent
import ArithS.Tau.Entangled.DimdidSys
import ArithS.Tau.Attr

/-!
# ArithS.Tau.Rows.CIMCIC — τ(CIMCIC)'s row in PA-`S'`

τ(CIMCIC)'s instance at a hypothesis `T` that does not self-probe is one `proveImpl` stage: the guard
`cimG X := .impl (.plays .self (.bot X) C) (.plays (.bot X) .self C)` — "if I cooperate with `T`'s instance seeing
CIMCIC, it cooperates with me" — with the antecedent's subject the `.self` PRONOUN (`Tau/Zoo.inst_cimcic_peel_*`);
its diagonal is `.impl (self plays self C) (self plays self C)`, a tautology (`inst_cimcic_quine`), found Löb-free
(`Tau/Quine.cimcic_quine_found`, the `S'` twin of `Pf.implRefl`). Engine twin: `Tau/Theorems/TauCIMCIC/Phase.lean`.

Slots stated here (`[coop, defect, tftSim, dupoc, obot, dimcid, cimcic, maxconfidence, minconfidence]`): `coop` C (POS on the instance's own description,
`Tau/Described.col_cimcic_coop`), `defect` D (self-refuting, `col_cimcic_defect`), `tftSim` C (Phase 3e,
`Tau/ClosedWatch.cimcic_tftSim_C`: under budget abstraction the stored template is a constant, τ(TFTSim)'s instance
at CIMCIC is a `k̂`-tower that copies CIMCIC's C at the cooperator, and the guard is a conditional `TAct`-theorem
found by the `k̂`-chain; the D of the pre-abstraction coding, `Tau/NeverFits.cimcic_selfBot_D`, was an artefact of the
stored template carrying the hypothesis's budget numeral); `obot` D — self-refuting on the instance: τ(OBot)'s instance at
CIMCIC defects (its second watch sees CIMCIC's instance defect against the defector), so a proof of the guard would
make the instance cooperate with it (antecedent true) while the consequent is false — the guard would be false,
against soundness (`cimcic_obot_not_found`, `cimcic_defect_not_found`'s argument with a frame-generic play of the
probed instance in place of the constant's); the diagonal C; and the ENTANGLED slots (`Tau/Entangled/`, Phase 3c):
`dupoc`/`maxconfidence`/`minconfidence` C (mutual Löb on the member slots with the Dupoc-spec self-probers,
`ent_cimcic_dupoc` …), `dimcid` D (the guard about the DIMCID member is self-refuting, `ent_cimcic_dimcid`).

**Floor bits** (`‡`, five, floor SIDE): `ebot`, `dbot`, `cupodTroll` — hinge = CIMCIC's own implication guard
about the hypothesis's instance seeing CIMCIC (base `dich_CIMCIC_vs_EBot/DBot/CupodTrollBot`); not found ⇒ D.
In `S'` these three hinges are in fact FALSE at every `k` (the same obstruction — the probed instances carry the
budget), so the bits are theorems (D) rather than floors; they are stated as floor bits because the table (and
`expectedFloorBits`) keeps them `‡` for parity with the base cells, whose partners (`DBot`, `EBot`,
`CupodTrollBot k`) carry no second budget. Updating the table moves them to row slots with the same value. The two system floors `cupod` (base
`dich_CIMCIC_vs_CupodBot`) and `prudent` (base `dich_CIMCIC_vs_PrudentBot`) have the CIMCIC member's own guard as
hinge (`Tau/Entangled/CupodCimcic.lean`, `CimcicPrudent.lean`).
-/

namespace ArithS.Tau

open PD PD.Tau

/-- τ(CIMCIC)'s bit row — the table's values (`tftSim` C: the never-fits reading of 2026-10-01 morning was an
artefact of the pre-abstraction coding; re-proved as C in Phase 3e, `Tau/ClosedWatch.lean`). -/
def cimcicRowA : Tmpl → Action
  | .coop => .C | .defect => .D | .tftSim => .C | .dupoc => .C | .ebot => .D | .obot => .D | .dbot => .D
  | .cupodTroll => .D | .cupod => .D | .dimcid => .D | .cimcic => .C | .prudent => .D
  | .maxconfidence => .C | .minconfidence => .C
  | _ => .D

/-- CIMCIC's off-diagonal guard at the probed instance `X`. -/
abbrev cimG (X : PD.Prog) : PD.Formula := .impl (.plays .self (.bot X) .C) (.plays (.bot X) .self .C)

/-! ### The compiled instances -/

theorem instCode_cimcic_tftSim (k : ℕ) : instCode k .cimcic .tftSim =
    pSearch k (templateCodeAt (cimG (inst (tauZoo k) .tftSim .cimcic)) k) (pConst 0) (pConst 1) := by
  unfold instCode; rw [inst_cimcic_peel_tftSim]; simp [actCode]

theorem instCode_cimcic_ebot (k : ℕ) : instCode k .cimcic .ebot =
    pSearch k (templateCodeAt (cimG (inst (tauZoo k) .ebot .cimcic)) k) (pConst 0) (pConst 1) := by
  unfold instCode; rw [inst_cimcic_peel_ebot]; simp [actCode]

theorem instCode_cimcic_obot (k : ℕ) : instCode k .cimcic .obot =
    pSearch k (templateCodeAt (cimG (inst (tauZoo k) .obot .cimcic)) k) (pConst 0) (pConst 1) := by
  unfold instCode; rw [inst_cimcic_peel_obot]; simp [actCode]

theorem instCode_cimcic_dbot (k : ℕ) : instCode k .cimcic .dbot =
    pSearch k (templateCodeAt (cimG (inst (tauZoo k) .dbot .cimcic)) k) (pConst 0) (pConst 1) := by
  unfold instCode; rw [inst_cimcic_peel_dbot]; simp [actCode]

theorem instCode_cimcic_cupodTroll (k : ℕ) : instCode k .cimcic .cupodTroll =
    pSearch k (templateCodeAt (cimG (inst (tauZoo k) .cupodTroll .cimcic)) k) (pConst 0) (pConst 1) := by
  unfold instCode; rw [inst_cimcic_peel_cupodTroll]; simp [actCode]
theorem instCode_cimcic_dupocTroll (k : ℕ) : instCode k .cimcic .dupocTroll =
    pSearch k (templateCodeAt (cimG (inst (tauZoo k) .dupocTroll .cimcic)) k) (pConst 0) (pConst 1) := by
  unfold instCode; rw [inst_cimcic_peel_dupocTroll]; simp [actCode]

/-- The diagonal: the tautology. -/
theorem instCode_cimcic_cimcic (k : ℕ) : instCode k .cimcic .cimcic =
    pSearch k (templateCode cimQ) (pConst 0) (pConst 1) := by
  unfold instCode; rw [inst_cimcic_quine]; rw [progCode_search_noSnap _ _ _ _ rfl]; simp [actCode]

/-! ### The slots -/

/-- **The diagonal: C, Löb-free** (`cimcic_quine_found`). -/
theorem cimcic_quine_C : bitEventually .cimcic .cimcic .C := by
  obtain ⟨k₀, h⟩ := cimcic_quine_found
  refine ⟨k₀, fun k hk ↦ bitPlays_of_eq (instCode_cimcic_cimcic k) ?_⟩
  exact ⟨_, search_then cimQ (h k hk) (const_play 0 _ _ _)⟩

/-- τ(OBot)'s instance at CIMCIC defects in EVERY frame (its watches set their own frames): the first watch sees
CIMCIC's instance cooperate with the cooperator (not D), the second sees it defect against the defector. -/
theorem obot_cimcic_D_frame {k : ℕ} (hco : bitPlays k .cimcic .coop .C) :
    ∃ n, ∀ me opp : ℕ, EvalGraph n me opp (instCode k .obot .cimcic) 1 := by
  obtain ⟨n₁, h₁⟩ := hco
  obtain ⟨n₂, h₂⟩ := col_cimcic_defect k
  refine ⟨n₁ + (n₂ + (0 + 1) + 3) + 3, fun me opp ↦ ?_⟩
  rw [instCode_obot]
  exact watch_falls' h₁ (by decide) (watch_fires' h₂ (const_play 0 _ _ _))

/-- **`cimcic × obot` is SELF-REFUTING**: a proof of "if I cooperate with τ(OBot)'s instance, it cooperates with
me" would make the instance cooperate with it, so by soundness that instance would cooperate — but it defects.
Never found. -/
theorem cimcic_obot_not_found {k : ℕ} (hco : bitPlays k .cimcic .coop .C) :
    ¬ LenBox TAct k (guardOf (cimG (inst (tauZoo k) .obot .cimcic))
      (.bot (inst (tauZoo k) .cimcic .obot)) (.bot (inst (tauZoo k) .cimcic .obot))) := by
  intro hf
  have hfr : fragF (cimG (inst (tauZoo k) .obot .cimcic)) = true := rfl
  have hns : noSelfIdxF (cimG (inst (tauZoo k) .obot .cimcic)) = true := rfl
  have hme : ProperPlayer (PD.Prog.bot (inst (tauZoo k) .cimcic .obot)) := properPlayer_bot _
  have hX : ProperPlayer (PD.Prog.bot (inst (tauZoo k) .obot .cimcic)) := properPlayer_bot _
  have hme' : noSelfIdxP (PD.Prog.bot (inst (tauZoo k) .cimcic .obot)) = true := rfl
  have hX' : noSelfIdxP (PD.Prog.bot (inst (tauZoo k) .obot .cimcic)) = true := rfl
  -- the same verdict in the probe frame `(me, .bot X)`: the template mentions no `.opp`
  have hf' : LenBox TAct k (guardOf (cimG (inst (tauZoo k) .obot .cimcic))
      (.bot (inst (tauZoo k) .cimcic .obot)) (.bot (inst (tauZoo k) .obot .cimcic))) := by
    rw [guardOf_eq_templateCode_subst hme hX _ hfr hme' hX']
    rw [guardOf_eq_templateCode_subst hme hme _ hfr hme' hme'] at hf
    exact hf
  -- so the instance cooperates with `.bot X`
  have hC : EvalGraph 3 (progCode (PD.Prog.bot (inst (tauZoo k) .cimcic .obot)))
      (progCode (PD.Prog.bot (inst (tauZoo k) .obot .cimcic)))
      (progCode (PD.Prog.bot (inst (tauZoo k) .cimcic .obot))) 0 := by
    unfold guardOf at hf'
    rw [progCode_bot_inst, progCode_bot_inst, instCode_cimcic_obot] at hf' ⊢
    show EvalGraph (2 + 1) _ _ _ _
    rw [EvalGraph.bot_iff]
    exact search_then_at _ hf' (const_play 0 _ _ _) hns
  -- by soundness the guard is true in ℕ: `.bot X` cooperates with the instance — against the fact
  have hT := models_sentenceAt_of_lenBox hf hns
  rw [← sentenceAt_subst (.bot (inst (tauZoo k) .cimcic .obot)) (.bot (inst (tauZoo k) .cimcic .obot)) hme hme _ hfr] at hT
  change ℕ↓[LAct] ⊧ sentenceAt (.bot (inst (tauZoo k) .cimcic .obot)) (.bot (inst (tauZoo k) .cimcic .obot))
    (.impl (.plays (.bot (inst (tauZoo k) .cimcic .obot)) (.bot (inst (tauZoo k) .obot .cimcic)) .C)
      (.plays (.bot (inst (tauZoo k) .obot .cimcic)) (.bot (inst (tauZoo k) .cimcic .obot)) .C)) at hT
  rw [models_sentenceAt_impl, models_sentenceAt_plays _ _ _ _ _ hme hX,
    models_sentenceAt_plays _ _ _ _ _ hX hme] at hT
  obtain ⟨N', hN'⟩ := hT ⟨3, hC⟩
  obtain ⟨N'', rfl, _⟩ := EvalGraph.case_iff.mp hN'
  rw [progCode_bot_inst, EvalGraph.bot_iff] at hN'
  obtain ⟨n, hn⟩ := obot_cimcic_D_frame hco
  exact absurd (EvalGraph.unique' hN' (hn _ _)) (by decide)

/-- `cimcic × tftSim`: C (Phase 3e, `Tau/ClosedWatch.cimcic_tftSim_C`) — the consequent "τ(TFTSim)'s instance cooperates
with me" holds in both readings (the watch copies CIMCIC's C at the cooperator), so the guard is a conditional
`TAct`-theorem over the watch's `k̂`-tower, found by the `k̂`-chain. The D of the pre-abstraction coding
(`Tau/NeverFits.cimcic_selfBot_D`) was an artefact of the stored template carrying the hypothesis's budget numeral. -/
theorem cimcic_tftSim_C' : bitEventually .cimcic .tftSim .C := cimcic_tftSim_C

/-- `cimcic × obot`: D (else-branch). -/
theorem cimcic_obot_D : bitEventually .cimcic .obot .D := by
  refine bitEventually.mono (fun k hco ↦ bitPlays_of_eq (instCode_cimcic_obot k) ?_) col_cimcic_coop
  have hn := cimcic_obot_not_found hco
  unfold guardOf at hn
  rw [progCode_bot_inst, instCode_cimcic_obot] at hn
  exact ⟨_, search_else_at _ hn (const_play 0 _ _ _) rfl⟩

/-- **τ(CIMCIC)'s row in `S'`** — nine theorem slots (five non-entangled, four entangled). -/
@[tau_rowA]
theorem cimcicRowSpecA : RowSpecA .cimcic
    [.coop, .defect, .tftSim, .dupoc, .obot, .dimcid, .cimcic, .maxconfidence, .minconfidence] cimcicRowA :=
  RowSpecA.cons col_cimcic_coop <|
  RowSpecA.cons (bitEventually.of_forall col_cimcic_defect) <|
  RowSpecA.cons cimcic_tftSim_C <|
  RowSpecA.cons ent_cimcic_dupoc <|
  RowSpecA.cons cimcic_obot_D <|
  RowSpecA.cons ent_cimcic_dimcid <|
  RowSpecA.cons cimcic_quine_C <|
  RowSpecA.cons ent_cimcic_maxconfidence <|
  RowSpecA.cons ent_cimcic_minconfidence <|
  RowSpecA.nil _ _

/-! ### The floor bits — CIMCIC's own guard is the hinge (floor SIDE) -/

/-- `cimcic × dimdid` ‡ (base `dich_DIMDID_vs_CIMCIC`, the self-dual pair, 2026-10-19): D when the CIMCIC member's
guard about the DIMDID member is not found (`Tau/Entangled/DimdidSys.lean`). -/
@[tau_floor_bitA]
theorem cimcicRowSpecA_dimdid_floor : FloorBitA .cimcic .dimdid
    (fun k ↦ □[k] (guardCodeB (templateCode (.impl (.plays .self (.bot (.sys (sys2 (cim 1 k) (ddm 0 k)) 1)) .C)
      (.plays (.bot (.sys (sys2 (cim 1 k) (ddm 0 k)) 1)) .self .C)))
      (pBot (instCode k .cimcic .dimdid)) (pBot (instCode k .cimcic .dimdid)) k)) .D :=
  entFloor_cimcic_dimdid

/-- CIMCIC's floor-side slot: its own guard not found — else-branch D. -/
theorem cimcic_floor_D {k : ℕ} {T : Tmpl}
    (hc : instCode k .cimcic T = pSearch k (templateCodeAt (cimG (inst (tauZoo k) T .cimcic)) k) (pConst 0) (pConst 1))
    (hns : noSelfIdxF (cimG (inst (tauZoo k) T .cimcic)) = true)
    (hn : ¬ LenBox TAct k (guardCodeB (templateCode (cimG (inst (tauZoo k) T .cimcic)))
      (pBot (instCode k .cimcic T)) (pBot (instCode k .cimcic T)) k)) : bitPlays k .cimcic T .D := by
  rw [hingeB _ _ _ _ hns, hc] at hn
  exact bitPlays_of_eq hc ⟨_, search_else_at _ hn (const_play 0 _ _ _) hns⟩

/-! The three `‡` slots below were, under the pre-2026-10-01 coding, theorems (hinge false at every `k`, the
never-fits obstruction); under budget abstraction they are honest floor bits again (Phase 3e re-derives
`expectedFloorBits`). -/

/-- `cimcic × ebot` ‡ (base `dich_CIMCIC_vs_EBot`): hinge = CIMCIC's implication guard about τ(EBot)'s instance
seeing CIMCIC, in the bit's frame; not found ⇒ D (and in `S'` it is never found: `cimcic_ebot_D`). -/
@[tau_floor_bitA]
theorem cimcicRowSpecA_ebot_floor : FloorBitA .cimcic .ebot
    (fun k ↦ □[k] (guardCodeB (templateCode (.impl (.plays .self (.bot (inst (tauZoo k) .ebot .cimcic)) .C)
      (.plays (.bot (inst (tauZoo k) .ebot .cimcic)) .self .C)))
      (pBot (instCode k .cimcic .ebot)) (pBot (instCode k .cimcic .ebot)) k)) .D :=
  FloorBitA.of_not_hinge ⟨0, fun k _ hn ↦ cimcic_floor_D (instCode_cimcic_ebot k) rfl hn⟩

/-- `cimcic × dbot` ‡ (base `dich_CIMCIC_vs_DBot`). -/
@[tau_floor_bitA]
theorem cimcicRowSpecA_dbot_floor : FloorBitA .cimcic .dbot
    (fun k ↦ □[k] (guardCodeB (templateCode (.impl (.plays .self (.bot (inst (tauZoo k) .dbot .cimcic)) .C)
      (.plays (.bot (inst (tauZoo k) .dbot .cimcic)) .self .C)))
      (pBot (instCode k .cimcic .dbot)) (pBot (instCode k .cimcic .dbot)) k)) .D :=
  FloorBitA.of_not_hinge ⟨0, fun k _ hn ↦ cimcic_floor_D (instCode_cimcic_dbot k) rfl hn⟩

/-- `cimcic × cupodTroll` ‡ (base `dich_CIMCIC_vs_CupodTrollBot`). -/
@[tau_floor_bitA]
theorem cimcicRowSpecA_cupodTroll_floor : FloorBitA .cimcic .cupodTroll
    (fun k ↦ □[k] (guardCodeB (templateCode (.impl (.plays .self (.bot (inst (tauZoo k) .cupodTroll .cimcic)) .C)
      (.plays (.bot (inst (tauZoo k) .cupodTroll .cimcic)) .self .C)))
      (pBot (instCode k .cimcic .cupodTroll)) (pBot (instCode k .cimcic .cupodTroll)) k)) .D :=
  FloorBitA.of_not_hinge ⟨0, fun k _ hn ↦ cimcic_floor_D (instCode_cimcic_cupodTroll k) rfl hn⟩

/-- `cimcic × dupocTroll` ‡ (base `dich_DupocTrollBot_vs_CIMCIC`, 2026-10-19): the same floor as at `cupodTroll`. -/
@[tau_floor_bitA]
theorem cimcicRowSpecA_dupocTroll_floor : FloorBitA .cimcic .dupocTroll
    (fun k ↦ □[k] (guardCodeB (templateCode (.impl (.plays .self (.bot (inst (tauZoo k) .dupocTroll .cimcic)) .C)
      (.plays (.bot (inst (tauZoo k) .dupocTroll .cimcic)) .self .C)))
      (pBot (instCode k .cimcic .dupocTroll)) (pBot (instCode k .cimcic .dupocTroll)) k)) .D :=
  FloorBitA.of_not_hinge ⟨0, fun k _ hn ↦ cimcic_floor_D (instCode_cimcic_dupocTroll k) rfl hn⟩

/-! ### The system floor bits — the CIMCIC member's own guard is the hinge (`Tau/Entangled/`) -/

/-- `cimcic × cupod` ‡ (base `dich_CIMCIC_vs_CupodBot`): D when the CIMCIC member's guard about the Cupod member is
not found (`Tau/Entangled/CupodCimcic.lean`). -/
@[tau_floor_bitA]
theorem cimcicRowSpecA_cupod_floor : FloorBitA .cimcic .cupod
    (fun k ↦ □[k] (guardCodeB (templateCode (.impl (.plays .self (.bot (.sys (sys2 (cim 1 k) (cm 0 k)) 1)) .C)
      (.plays (.bot (.sys (sys2 (cim 1 k) (cm 0 k)) 1)) .self .C)))
      (pBot (instCode k .cimcic .cupod)) (pBot (instCode k .cimcic .cupod)) k)) .D :=
  entFloor_cimcic_cupod

/-- `cimcic × prudent` ‡ (base `dich_CIMCIC_vs_PrudentBot`): D when the CIMCIC member's guard about the Prudent
member is not found (`Tau/Entangled/CimcicPrudent.lean`). -/
@[tau_floor_bitA]
theorem cimcicRowSpecA_prudent_floor : FloorBitA .cimcic .prudent
    (fun k ↦ □[k] (guardCodeB (templateCode (.impl (.plays .self (.bot (.sys (sys2 (cim 1 k) (pm 0 k .cimcic)) 1)) .C)
      (.plays (.bot (.sys (sys2 (cim 1 k) (pm 0 k .cimcic)) 1)) .self .C)))
      (pBot (instCode k .cimcic .prudent)) (pBot (instCode k .cimcic .prudent)) k)) .D :=
  entFloor_cimcic_prudent

end ArithS.Tau
