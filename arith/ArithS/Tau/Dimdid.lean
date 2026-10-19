import ArithS.Tau.Columns
import ArithS.Tau.Described
import ArithS.Cells.Transposition

/-!
# ArithS.Tau.Dimdid — τ(DIMDID)'s instances on codes: the columns, the transposition bridge, the
self-defeating guard (2026-10-19)

τ(DIMDID) (`engine/.../Tau/Bots/TauDIMDID.lean`, the C/D transposition of τ(CIMCIC) template by template) is one
`proveImplD` stage at a hypothesis `T` that does not self-probe: the guard `ddGf X := .impl (.plays .self (.bot X) D)
(.plays (.bot X) .self D)` — "if I defect against `T`'s instance seeing DIMDID, it defects against me" — then `D`,
else `C` (`Tau/Zoo.inst_dimdid_peel_*`). Three facts every row file needs:

* **the two columns** `col_dimdid_coop` (C at EVERY `k`) and `col_dimdid_defect` (D for all large `k`): the
  transpositions of `col_cimcic_defect` and `col_cimcic_coop` through `bitPlays_transpose` — a tau bit is a `plays`
  of the bot-wrapped instance against itself, and `inst dimdid T = (inst cimcic τT).transpose` by `rfl` for the
  constants (`Cells/Transposition.plays_transpose` on the fragment);
* **the self-defeating guard** (`dimdid_not_found_of_C`, the tau twin of `Cells/Dimdid.dimdid_selfref_not_found`):
  against a hypothesis whose instance cooperates with DIMDID's in every frame, a proof of the guard would make the
  instance defect, so by soundness the partner would defect — against the fact; never found, so DIMDID cooperates
  (`dimdid_C_of_not_found`). Stated for a guard on the fragment (`fragF`), which covers τ(TFTSim), τ(DBot) and the
  two trolls; τ(EBot)'s instance contains the system `inst dimdid mirror` and takes the fragment-free route of
  `Tau/ClosedWatchDd.lean`.
-/

set_option linter.constructorNameAsVariable false

namespace ArithS.Tau

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open LAct
open PD PD.Tau

/-- DIMDID's off-diagonal guard at the probed instance `X`. -/
abbrev ddGf (X : PD.Prog) : PD.Formula := .impl (.plays .self (.bot X) .D) (.plays (.bot X) .self .D)

/-- The diagonal guard: "if I defect against myself, I defect against myself" — a tautology. -/
abbrev ddQ : PD.Formula := .impl (.plays .self .self .D) (.plays .self .self .D)

/-! ### 1. The compiled instances -/

/-- At the cooperator: the guard on the frozen constant `C` (`implC .C .D .D`). -/
theorem instCode_dimdid_coop (k : ℕ) : instCode k .dimdid .coop =
    pSearch k (templateCode (implC .C .D .D)) (pConst 1) (pConst 0) := by
  unfold instCode; rw [inst_dimdid_peel_coop, inst_coop_peel]; rw [progCode_search_noSnap _ _ _ _ rfl]; simp [actCode]

/-- At the defector: the guard on the frozen constant `D` (`implC .D .D .D`, a `TAct`-theorem instance). -/
theorem instCode_dimdid_defect (k : ℕ) : instCode k .dimdid .defect =
    pSearch k (templateCode (implC .D .D .D)) (pConst 1) (pConst 0) := by
  unfold instCode; rw [inst_dimdid_peel_defect, inst_defect_peel]; rw [progCode_search_noSnap _ _ _ _ rfl]; simp [actCode]

/-- The diagonal. -/
theorem instCode_dimdid_dimdid (k : ℕ) : instCode k .dimdid .dimdid =
    pSearch k (templateCode ddQ) (pConst 1) (pConst 0) := by
  unfold instCode; rw [inst_dimdid_quine]; rw [progCode_search_noSnap _ _ _ _ rfl]; simp [actCode]

/-- At a budget-carrying hypothesis: the STORED (abstracted) template of the guard at its instance. -/
theorem instCode_dimdid_tftSim' (k : ℕ) : instCode k .dimdid .tftSim =
    pSearch k (templateCodeAt (ddGf (inst (tauZoo k) .tftSim .dimdid)) k) (pConst 1) (pConst 0) := by
  unfold instCode; rw [inst_dimdid_peel_tftSim]; simp [actCode]
theorem instCode_dimdid_ebot' (k : ℕ) : instCode k .dimdid .ebot =
    pSearch k (templateCodeAt (ddGf (inst (tauZoo k) .ebot .dimdid)) k) (pConst 1) (pConst 0) := by
  unfold instCode; rw [inst_dimdid_peel_ebot]; simp [actCode]
theorem instCode_dimdid_obot' (k : ℕ) : instCode k .dimdid .obot =
    pSearch k (templateCodeAt (ddGf (inst (tauZoo k) .obot .dimdid)) k) (pConst 1) (pConst 0) := by
  unfold instCode; rw [inst_dimdid_peel_obot]; simp [actCode]
theorem instCode_dimdid_dbot' (k : ℕ) : instCode k .dimdid .dbot =
    pSearch k (templateCodeAt (ddGf (inst (tauZoo k) .dbot .dimdid)) k) (pConst 1) (pConst 0) := by
  unfold instCode; rw [inst_dimdid_peel_dbot]; simp [actCode]
theorem instCode_dimdid_cupodTroll' (k : ℕ) : instCode k .dimdid .cupodTroll =
    pSearch k (templateCodeAt (ddGf (inst (tauZoo k) .cupodTroll .dimdid)) k) (pConst 1) (pConst 0) := by
  unfold instCode; rw [inst_dimdid_peel_cupodTroll]; simp [actCode]
theorem instCode_dimdid_dupocTroll' (k : ℕ) : instCode k .dimdid .dupocTroll =
    pSearch k (templateCodeAt (ddGf (inst (tauZoo k) .dupocTroll .dimdid)) k) (pConst 1) (pConst 0) := by
  unfold instCode; rw [inst_dimdid_peel_dupocTroll]; simp [actCode]

/-! ### 2. The transposition bridge: a tau bit is a `plays` of the bot-wrapped instance -/

/-- A bit IS `plays` on the bot-wrapped instance (`EvalGraph.bot_iff`, one fuel step). -/
theorem bitPlays_iff_plays (k : ℕ) (A T : Tmpl) (a : Action) :
    bitPlays k A T a ↔ plays (pBot (instCode k A T)) (pBot (instCode k A T)) a := by
  constructor
  · rintro ⟨n, h⟩; exact ⟨n + 1, EvalGraph.bot_iff.mpr h⟩
  · rintro ⟨n, h⟩
    obtain ⟨m, rfl, -⟩ := EvalGraph.case_iff.mp h
    exact ⟨m, EvalGraph.bot_iff.mp h⟩

/-- **Bits transpose**: if `A`'s instance at `T` is the transposition of `A'`'s at `T'` (a fragment program), the
bit at `(A, T)` is the transposed bit at `(A', T')` — `Cells/Transposition.plays_transpose` on the bot-wrapped
instances. -/
theorem bitPlays_transpose {k : ℕ} {A T A' T' : Tmpl} {a : Action}
    (h : inst (tauZoo k) A T = (inst (tauZoo k) A' T').transpose)
    (hf : fragP (inst (tauZoo k) A' T') = true) (hb : bitPlays k A' T' a) : bitPlays k A T a.swap := by
  rw [bitPlays_iff_plays] at hb ⊢
  unfold instCode at hb ⊢
  rw [← progCode_bot] at hb ⊢
  rw [h]
  have hf' : fragP (PD.Prog.bot (inst (tauZoo k) A' T')) = true := hf
  exact (plays_transpose (L := .bot (inst (tauZoo k) A' T')) (R := .bot (inst (tauZoo k) A' T')) hf' hf' a).mp hb

/-- τ(DIMDID) is τ(CIMCIC) transposed, template by template, at the constants and on the diagonal
(the engine's `Tau/Theorems/TauDIMDID/Helpers.inst_dimdid_*_tr`, by `rfl`). -/
theorem inst_dimdid_coop_tr (k : ℕ) : inst (tauZoo k) .dimdid .coop = (inst (tauZoo k) .cimcic .defect).transpose := rfl
theorem inst_dimdid_defect_tr (k : ℕ) : inst (tauZoo k) .dimdid .defect = (inst (tauZoo k) .cimcic .coop).transpose := rfl
theorem inst_dimdid_dimdid_tr (k : ℕ) : inst (tauZoo k) .dimdid .dimdid = (inst (tauZoo k) .cimcic .cimcic).transpose := rfl

/-! ### 3. The two columns -/

/-- CIMCIC's instances at the constants are fragment programs (peel first: `rfl` through the compiler is slow). -/
theorem fragP_inst_cimcic_coop (k : ℕ) : fragP (inst (tauZoo k) .cimcic .coop) = true := by
  rw [inst_cimcic_peel_coop, inst_coop_peel]; rfl
theorem fragP_inst_cimcic_defect (k : ℕ) : fragP (inst (tauZoo k) .cimcic .defect) = true := by
  rw [inst_cimcic_peel_defect, inst_defect_peel]; rfl

/-- **`dimdid × coop` is C at every `k`**: the transposition of `col_cimcic_defect` (CIMCIC's self-refuting guard at
the defector is DIMDID's self-defeating guard at the cooperator). -/
theorem col_dimdid_coop (k : ℕ) : bitPlays k .dimdid .coop .C := by
  -- elaborate without the expected type: unifying `Action.D.swap` with `.C` under `bitPlays` unfolds the instance
  have h := bitPlays_transpose (inst_dimdid_coop_tr k) (fragP_inst_cimcic_defect k) (col_cimcic_defect k)
  exact h

/-- **`dimdid × defect` is D for all large `k`**: the transposition of `col_cimcic_coop` (POS — "if I defect against
the frozen defector, it defects against me" is a `TAct`-theorem instance). -/
theorem col_dimdid_defect : bitEventually .dimdid .defect .D := by
  refine bitEventually.mono (fun k h ↦ ?_) col_cimcic_coop
  have h' := bitPlays_transpose (inst_dimdid_defect_tr k) (fragP_inst_cimcic_coop k) h
  exact h'

/-! ### 4. The self-defeating guard on the fragment -/

/-- **DIMDID's guard against a hypothesis whose instance cooperates with it is never found** (in the bit's frame): a
proof of "I defect against `X` ⇒ `X` defects against me" would make the instance defect against `X` — the same
sentence is consulted in the probe frame, the template mentions no `.opp` — so by soundness `X` would defect
against it, against the fact that `X` cooperates in every frame. The tau twin of `Cells/Dimdid.dimdid_selfref_not_found`
(`Rows/CIMCIC.cimcic_obot_not_found` with the actions exchanged). -/
theorem dimdid_not_found_of_C {k : ℕ} {T : Tmpl}
    (hI : instCode k .dimdid T =
      pSearch k (templateCodeAt (ddGf (inst (tauZoo k) T .dimdid)) k) (pConst 1) (pConst 0))
    (hfr : fragF (ddGf (inst (tauZoo k) T .dimdid)) = true)
    (hns : noSelfIdxF (ddGf (inst (tauZoo k) T .dimdid)) = true)
    (hnsX : noSelfIdxP (.bot (inst (tauZoo k) T .dimdid)) = true)
    (hnsI : noSelfIdxP (.bot (inst (tauZoo k) .dimdid T)) = true)
    (hC : ∀ me opp : PD.Prog, ∃ n, EvalGraph n (progCode me) (progCode opp) (instCode k T .dimdid) 0) :
    ¬ LenBox TAct k (guardOf (ddGf (inst (tauZoo k) T .dimdid))
      (.bot (inst (tauZoo k) .dimdid T)) (.bot (inst (tauZoo k) .dimdid T))) := by
  intro hf
  have hme : ProperPlayer (PD.Prog.bot (inst (tauZoo k) .dimdid T)) := properPlayer_bot _
  have hX : ProperPlayer (PD.Prog.bot (inst (tauZoo k) T .dimdid)) := properPlayer_bot _
  -- the same verdict in the probe frame `(me, .bot X)`: the template mentions no `.opp`
  have hf' : LenBox TAct k (guardOf (ddGf (inst (tauZoo k) T .dimdid))
      (.bot (inst (tauZoo k) .dimdid T)) (.bot (inst (tauZoo k) T .dimdid))) := by
    rw [guardOf_eq_templateCode_subst hme hX _ hfr hnsI hnsX]
    rw [guardOf_eq_templateCode_subst hme hme _ hfr hnsI hnsI] at hf
    exact hf
  -- so the instance defects against `.bot X`
  have hD : EvalGraph 3 (progCode (PD.Prog.bot (inst (tauZoo k) .dimdid T)))
      (progCode (PD.Prog.bot (inst (tauZoo k) T .dimdid)))
      (progCode (PD.Prog.bot (inst (tauZoo k) .dimdid T))) (actCode .D) := by
    unfold guardOf at hf'
    rw [progCode_bot_inst, progCode_bot_inst, hI] at hf' ⊢
    show EvalGraph (2 + 1) _ _ _ _
    rw [EvalGraph.bot_iff]
    exact search_then_at _ hf' (const_play 0 _ _ _) hns
  -- by soundness the guard is true in ℕ: `.bot X` defects against the instance — against the fact
  have hT := models_sentenceAt_of_lenBox hf hns
  rw [← sentenceAt_subst (.bot (inst (tauZoo k) .dimdid T)) (.bot (inst (tauZoo k) .dimdid T)) hme hme _ hfr] at hT
  change ℕ↓[LAct] ⊧ sentenceAt (.bot (inst (tauZoo k) .dimdid T)) (.bot (inst (tauZoo k) .dimdid T))
    (.impl (.plays (.bot (inst (tauZoo k) .dimdid T)) (.bot (inst (tauZoo k) T .dimdid)) .D)
      (.plays (.bot (inst (tauZoo k) T .dimdid)) (.bot (inst (tauZoo k) .dimdid T)) .D)) at hT
  rw [models_sentenceAt_impl, models_sentenceAt_plays _ _ _ _ _ hme hX,
    models_sentenceAt_plays _ _ _ _ _ hX hme] at hT
  obtain ⟨N', hN'⟩ := hT ⟨3, hD⟩
  obtain ⟨N'', rfl, _⟩ := EvalGraph.case_iff.mp hN'
  rw [progCode_bot_inst, EvalGraph.bot_iff] at hN'
  obtain ⟨n, hn⟩ := hC (.bot (inst (tauZoo k) T .dimdid)) (.bot (inst (tauZoo k) .dimdid T))
  rw [progCode_bot_inst] at hn
  exact absurd (EvalGraph.unique' hN' hn) (by decide)

/-- The else-branch: DIMDID cooperates when its guard is not found in the bit's frame. -/
theorem dimdid_C_of_not_found {k : ℕ} {T : Tmpl}
    (hI : instCode k .dimdid T =
      pSearch k (templateCodeAt (ddGf (inst (tauZoo k) T .dimdid)) k) (pConst 1) (pConst 0))
    (hns : noSelfIdxF (ddGf (inst (tauZoo k) T .dimdid)) = true)
    (hn : ¬ LenBox TAct k (guardOf (ddGf (inst (tauZoo k) T .dimdid))
      (.bot (inst (tauZoo k) .dimdid T)) (.bot (inst (tauZoo k) .dimdid T)))) :
    bitPlays k .dimdid T .C := by
  refine bitPlays_of_eq hI ?_
  unfold guardOf at hn
  rw [progCode_bot_inst, hI] at hn
  exact ⟨_, search_else_at _ hn (const_play 0 _ _ _) hns⟩

/-! ### 5. The four fragment slots -/

/-- `dimdid × tftSim`: C at every `k` — τ(TFTSim)'s instance copies DIMDID's C at the cooperator, in every frame. -/
theorem dimdid_tftSim_C (k : ℕ) : bitPlays k .dimdid .tftSim .C := by
  obtain ⟨n, hn⟩ := col_dimdid_coop k
  refine dimdid_C_of_not_found (instCode_dimdid_tftSim' k) rfl
    (dimdid_not_found_of_C (instCode_dimdid_tftSim' k) rfl rfl rfl rfl fun me opp ↦ ?_)
  rw [instCode_tftSim]
  exact ⟨_, watch_fires' hn (const_play 0 _ _ _)⟩

/-- `dimdid × dbot`: C for all large `k` — τ(DBot)'s instance trusts DIMDID's D at the defector, in every frame. -/
theorem dimdid_dbot_C : bitEventually .dimdid .dbot .C := by
  refine bitEventually.mono (fun k h ↦ ?_) col_dimdid_defect
  obtain ⟨n, hn⟩ := h
  refine dimdid_C_of_not_found (instCode_dimdid_dbot' k) rfl
    (dimdid_not_found_of_C (instCode_dimdid_dbot' k) rfl rfl rfl rfl fun me opp ↦ ?_)
  rw [instCode_dbot]
  exact ⟨_, watch_falls' hn (by decide) (const_play 0 _ _ _)⟩

/-- `dimdid × cupodTroll`: C at every `k` — the troll's identity guard is false at DIMDID, it cooperates in every frame. -/
theorem dimdid_cupodTroll_C (k : ℕ) : bitPlays k .dimdid .cupodTroll .C :=
  dimdid_C_of_not_found (instCode_dimdid_cupodTroll' k) rfl
    (dimdid_not_found_of_C (instCode_dimdid_cupodTroll' k) rfl rfl rfl rfl fun me opp ↦ by
      rw [instCode_cupodTroll k .dimdid (by decide)]
      exact ⟨_, search_else _ (eq_const_not_found (by decide) me opp k) (const_play 0 _ _ _)⟩)

/-- `dimdid × dupocTroll`: C at every `k` (DIMDID's source is not Dupoc's). -/
theorem dimdid_dupocTroll_C (k : ℕ) : bitPlays k .dimdid .dupocTroll .C :=
  dimdid_C_of_not_found (instCode_dimdid_dupocTroll' k) rfl
    (dimdid_not_found_of_C (instCode_dimdid_dupocTroll' k) rfl rfl rfl rfl fun me opp ↦ by
      rw [instCode_dupocTroll k .dimdid (by decide)]
      exact ⟨_, search_else _ (eq_const_not_found (by decide) me opp k) (const_play 0 _ _ _)⟩)

end ArithS.Tau
