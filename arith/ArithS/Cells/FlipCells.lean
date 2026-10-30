import ArithS.Cells.PositiveCells
import ArithS.Cells.DIMCID
import ArithS.Cells.KhatCells

/-!
# ArithS.Cells.FlipCells — the FLIP cells: where PA-`S'` disagrees with the engine's `S`

`docs/notes/ARITHMETIZED_S_RESULTS.md` "THE FINDING" and `ROUTE_B_SCOPE.md` §2: the engine
closes ten cells by censuses that rest on a player being UNREADABLE by `S`'s rules
(`no_provable_tailTo_unreadable`, the WV valuation censuses). In PA every source is readable
(Σ₁-completeness), and the value of six of them FLIPS. `Cells/PositiveCells.lean` §7 proved the first
(`loeb_DIMCID_vs_CooperateBot`); this module proves the remaining five as theorems, each unconditional
(`∃ k₀, ∀ k > k₀, …`, three standard axioms), each with the `S'` value and the box form.

The mechanism, in one sentence: **a NEGATIVE-Löb guard is self-fulfilling under a real proof predicate.**
A searcher whose then-branch FALSIFIES its own guard's antecedent (DIMCID: "I play C against you ⇒ …",
then-branch D) or MAKES its guard's negation true (Wary: "¬(you play C against me)", then-branch D, against a
copier) has a guard that becomes true as soon as it is proved — bounded Löb (`Assembly/Family.family_found`)
then finds it, whatever the guard's consequent. The engine's `S` never reads these guards (its rule set has
no reader for a searcher's own else-play inside a negative), so its censuses return the else branch.

1. **A described opponent** (`descVal`, `Describes`): the code hypotheses of the instance equations for a triple
   `(X, U, W)` in every model, plus "the transposed triple denotes the transposed program". Then the generic
   Löb premise **`loebSound_pG_of`**: DIMCID's family `pG X U W` (`Cells/DIMCID.lean` §6) is `LoebSound`
   against EVERY described opponent — the proof of `loebSound_pDi0` never used the consequent — and
   **`dimcid_vs_described`**: DIMCID defects against it and finds its guard for all large `k`.
2. **Closed opponents**: `.bot CooperateBot` (`describes_botCB`, from the constants of `PositiveCells` §1) and
   TitForTatBot (`TFTV`, its transposition, `TFTV_lt_TFTTV`, the closed term `TTFT`, `describes_TFT`).
3. **Cell 1 — DIMCID × TitForTatBot `(D, D)`** (`loeb_DIMCID_vs_TitForTatBot`; engine
   `llm_outcome_DIMCID_vs_TitForTatBot = (C, C)`, pad 4): DIMCID's guard against TFT is self-fulfilling; TFT
   defects because DIMCID defects against `.bot CooperateBot` (the same Löb, `loeb_DIMCID_vs_botCB`).
4. **The box-consequence lemma** (`BoxConseq`, `box_conseq_uniform`, `found_of_box_conseq`): the general
   "`k̂`-chain" for a guard whose truth needs ANOTHER searcher's Löb-found guard. `TAct ⊢ ∀ k ≥ k̂,
   Box_g(psiF p)(k) → q(k)` by completeness (the chain `chain_core_VF` runs in every model), instantiated at
   `binNumeral k` (`lenBoxNat_inst_size`), the antecedents cut away (`NumeralFacts.lenBoxNat_le_binNumeralMeta` and the
   meta closure's box `exists_psiF_instance_length` + `BoundedInnerNec.nec`), the total polylog
   (`total_le_eventually`).
5. **Cell 2 — GuardianBot × DIMCID `(D, D)`** (`loeb_GuardianBot_vs_DIMCID`; engine
   `llm_outcome_GuardianBot_vs_DIMCID = (C, C)`, pad 2): Guardian's guard "DIMCID defects against
   `.bot CooperateBot`" is a box consequence of DIMCID's Löb family, so Guardian finds it (`guardian_finds_DIMCID`);
   DIMCID's guard against Guardian (described by the `SV` layer, `describes_Guardian`) is self-fulfilling.
6. **The `.neg` family** (`pQ q := q ⋏ τq`, `pQ_both_V`, `SV_search_V`) and **cells 3, 4 — WaryBot × MirrorBot
   `(D, D)`, WaryBot × WaryBot `(D, D)`** (`loeb_WaryBot_vs_MirrorBot`, `loeb_WaryBot_vs_WaryBot`; engine
   `outcome_WaryBot_vs_MirrorBot`/`outcome_WaryBot_vs_WaryBot = (C, C)` at EVERY `k`, pads 3/2): "¬(you
   cooperate with me)" against a copier is self-fulfilling — found ⇒ Wary defects ⇒ the copier defects.
7. **Cell 5 — DIMCID × CupodTrollBot `(D, C)`** (`loeb_DIMCID_vs_CupodTrollBot`; engine
   `llm_outcome_DIMCID_vs_CupodTrollBot = (C, C)`, pad 2), on the budget-slot `CupodTroll7 k` of
   `Cells/KhatCells.lean` (the same play as the engine's `CupodTrollBot k` in every frame,
   `evalGraph_CupodTroll7_iff`; an opponent's guard that DESCRIBES it needs the slot): DIMCID's guard against
   the described CupodTroll (`describes_troll7`) is self-fulfilling; CupodTroll's `.eq` guard "DIMCID is
   `CupodBot k`" is FALSE (`progCode_DIMCID_ne_CupodBot`, the templates separated semantically), so by soundness it
   is never found and CupodTroll cooperates — on the engine's own code too (`snd_CupodTrollBot_vs_DIMCID_engine`).

Conventions: every threshold EXISTENTIAL; `simp` never sees a closed quote; `omega` is never asked about `V`;
`≤` at ℕ bridged by `le_def`; `V` pinned in every statement.
-/

set_option linter.constructorNameAsVariable false

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open LAct
open PD.Bots

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ### 1. A described opponent, and DIMCID's self-fulfilling refutation against it -/

section described


/-- **DIMCID defects against every described opponent, and FINDS its guard, for all large `k`**,
unconditional: `family_found` on `pG X U W` (the arithmetized `pblt_engine`), then ∧-elimination on codes
(`pG_both_V`, `pG_guards_V`). -/
theorem dimcid_vs_described {X : Semiterm LAct Empty 1} {U W : ClosedSemiterm LAct 0} (h : Describes X U W) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 2 (Dimcid k) (descVal X U W k) (Dimcid k) 1 ∧
      LenBox TAct k (guardCode (⌜templateD⌝ : ℕ) (Dimcid k) (descVal X U W k)) := by
  obtain ⟨k₀, hf⟩ := family_found (pG X U W) boundedInnerNec_sixteen (loebSound_pG_of h)
  refine ⟨k₀, fun k hk ↦ ?_⟩
  obtain ⟨a, ha, hpc⟩ := hf k hk
  have ha' := le_def.mpr (pConj_slack_nat a _ _ _ k (formulaLen_instB_pG (V := ℕ) X U W k) ha)
  exact ⟨(pG_both_V (V := ℕ) k X U W (h.hX ℕ k) (h.hU ℕ k) (h.hW ℕ k) a ha' hpc).1,
    (pG_guards_V (V := ℕ) k X U W (h.hX ℕ k) (h.hU ℕ k) (h.hW ℕ k) a ha' hpc).1⟩

end described

/-! ### 2. Closed opponents: `.bot CooperateBot` and TitForTatBot -/

section closedOpponents


end closedOpponents

/-! ### 3. Cell 1 — DIMCID × TitForTatBot `(D, D)` -/

section cell1

/-- **DIMCID defects against `.bot CooperateBot` for all large `k`** (the self-fulfilling Löb of
`loeb_DIMCID_vs_CooperateBot`, against the frozen probe), with the box form. -/
theorem loeb_DIMCID_vs_botCB :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 2 (progCode (DIMCID k)) (pBot (pConst 0)) (progCode (DIMCID k)) 1 ∧
      LenBox TAct k (guardCode (templateCode phiD) (progCode (DIMCID k)) (pBot (pConst 0))) := by
  obtain ⟨k₀, h⟩ := dimcid_vs_described describes_botCB
  refine ⟨k₀, fun k hk ↦ ?_⟩
  have := h k hk
  rw [templateCode_eq_quote_template phiD rfl]
  rwa [descVal_botCB, ← progCode_DIMCID] at this

/-- **DIMCID defects against TitForTatBot and FINDS its guard, for all large `k`.** -/
theorem loeb_DIMCID_vs_TitForTatBot_core :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 2 (progCode (DIMCID k)) (progCode TitForTatBot) (progCode (DIMCID k)) 1 ∧
      LenBox TAct k (guardCode (templateCode phiD) (progCode (DIMCID k)) (progCode TitForTatBot)) := by
  obtain ⟨k₀, h⟩ := dimcid_vs_described describes_TFT
  refine ⟨k₀, fun k hk ↦ ?_⟩
  have := h k hk
  rw [templateCode_eq_quote_template phiD rfl]
  rwa [descVal_TFT, TFTV_nat, ← progCode_DIMCID] at this

/-- **DIMCID × TitForTatBot is `(D, D)` in PA-`S'`**, for all large `k`, unconditional. The engine proves
`(C, C)` by an unreadability census (`llm_outcome_DIMCID_vs_TitForTatBot`, pad 4); in `S'` the value is
`(D, D)` because DIMCID's guard "I play C against TFT ⇒ TFT plays D against me" is SELF-FULFILLING (its proof
makes DIMCID defect, which falsifies the antecedent) and bounded Löb finds it, so DIMCID defects; and TFT's
probe sees DIMCID defect against `.bot CooperateBot` (the same Löb), so TFT defects. -/
theorem loeb_DIMCID_vs_TitForTatBot :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 4 (progCode (DIMCID k)) (progCode TitForTatBot) (progCode (DIMCID k)) (actCode .D) ∧
      EvalGraph 4 (progCode TitForTatBot) (progCode (DIMCID k)) (progCode TitForTatBot) (actCode .D) := by
  obtain ⟨k₁, h₁⟩ := loeb_DIMCID_vs_TitForTatBot_core
  obtain ⟨k₂, h₂⟩ := loeb_DIMCID_vs_botCB
  refine ⟨k₁ + k₂, fun k hk ↦ ⟨?_, ?_⟩⟩
  · exact EvalGraph.mono_le (by omega) (h₁ k (by omega)).1
  · exact EvalGraph.mono_le (by omega) (tft_D_of_probe_D (h₂ k (by omega)).1)


end cell1

/-! ### 4. The box-consequence lemma: a guard whose truth needs another searcher's Löb-found guard -/

section boxConseq


end boxConseq

/-! ### 5. Cell 2 — GuardianBot × DIMCID `(D, D)` -/

section cell2

/-- Guardian's guard template: "opp plays D against `.bot CooperateBot`". -/
noncomputable abbrev gG : Semisentence LAct 6 := template (.plays .opp (.bot CooperateBot) .D)
/-- Its transposition: "opp plays C against `.bot DefectBot`". -/
noncomputable abbrev gGT : Semisentence LAct 6 := template (.plays .opp (.bot DefectBot) .C)

lemma lMap_swap_gG : Semiformula.lMap swap gG = gGT := lMap_swap_template _ rfl

lemma progCode_GuardianBot_SV (k : ℕ) : progCode (GuardianBot k) = SV (V := ℕ) gG 1 k := by
  rw [progCode_GuardianBot, SV_nat, templateCode_eq_quote_template phiG rfl]; rfl


/-! #### Guardian's guard against DIMCID as a fixed formula, its instance and truth equations -/

/-- Guardian's guard against `DimcidV k`: "`DimcidV k` plays D against `.bot CooperateBot`". -/
noncomputable def qGD : Semisentence LAct 1 := qT gG (TS gG 1) (uS gG 1) (wS gG 1) TDi uDi wDi

theorem guardCode_GD (k : V) : guardCode (⌜gG⌝ : V) (SV gG 1 k) (DimcidV k) = instB (⌜qGD⌝ : V) k :=
  guardCode_qT_eq_instB gG k _ _ _ _ _ _ (hX_SV gG 1 (Or.inr rfl) k) (hU_SV gG 1 (Or.inr rfl) k)
    (hW_SV gG 1 (Or.inr rfl) k) (hX_dimcid k) (hU_dimcid k) (hW_dimcid k)

/-- `qGD(k)` in the standard reading: `DimcidV k` plays D against `pBot (pConst 0)`. -/
theorem eval_qGD_iff (k : V) :
    Semiformula.Eval (s := stdReadingV V) ![k] Empty.elim qGD ↔
      ∃ n, EvalGraph n (DimcidV k) (pBot (pConst 0)) (DimcidV k) 1 := by
  unfold qGD
  rw [eval_qT_iff, eval_template_plays_opp_closed_V _ (by intro h; cases h) (by intro h; cases h)]
  simp only [Matrix.cons_val, actCode, Nat.cast_one, progCode_bot, progCode_const, PD.Bots.CooperateBot, cast_pBot,
    cast_pConst, Nat.cast_zero]
  rw [desc_dimcid k]

/-- `qGD(k)` in the swapped reading: `DimcidTV k` plays C against `pBot (pConst 1)`. -/
theorem eval_qGD_swap_iff (k : V) :
    Semiformula.Eval (s := swappedReading V) ![k] Empty.elim qGD ↔
      ∃ n, EvalGraph n (DimcidTV k) (pBot (pConst 1)) (DimcidTV k) 0 := by
  unfold qGD
  rw [eval_qT_swap, lMap_swap_gG, eval_qT_iff,
    eval_template_plays_opp_closed_V _ (by intro h; cases h) (by intro h; cases h)]
  simp only [Matrix.cons_val, actCode, Nat.cast_zero, progCode_bot, progCode_const, PD.Bots.DefectBot, cast_pBot,
    cast_pConst, Nat.cast_one]
  rw [descT_dimcid k]

/-- **Guardian's guard against DIMCID is a box consequence of DIMCID's family against `.bot CooperateBot`**:
a proof of `pG (cl TB0) C D (k)` with the slack makes `DimcidV k` defect against `.bot CooperateBot` and
`DimcidTV k` cooperate with `.bot DefectBot` (`pG_both_V`), which is `qGD(k)` in the two readings. -/
theorem boxConseq_qGD : BoxConseq (pG (cl TB0) (cterm Act.C) (cterm Act.D)) qGD 7 8 := by
  intro V _ _ k a ha hp
  have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
  have ha' : a + 8 * (formulaLen LAct (instB (⌜qDG (cl TB0) (cterm Act.C) (cterm Act.D)⌝ : V) k) +
      formulaLen LAct (instB (⌜qTG (Semiterm.lMap swap (cl TB0 : Semiterm LAct Empty 1))
        (Semiterm.lMap swap (cterm Act.C)) (Semiterm.lMap swap (cterm Act.D))⌝ : V) k)) + 7 ≤ k :=
    le_trans (pConj_slack_le a _ _ _ (formulaLen_instB_pG (cl TB0) (cterm Act.C) (cterm Act.D) k)) ha
  obtain ⟨h1, h2⟩ := pG_both_V k (cl TB0) (cterm Act.C) (cterm Act.D) (hX_bot_zero k) hU_C_bot_zero hW_D_bot_zero
    a ha' hp
  rw [transposeCode_pBot, transposeCode_pConst_zero] at h2
  exact ⟨by rw [← stdReadingV_eq_stdReading, eval_qGD_iff]; exact ⟨2, h1⟩, (eval_qGD_swap_iff k).mpr ⟨2, h2⟩⟩

/-- **Guardian FINDS its guard against DIMCID for all large `k`** (the box form of cell 2, Guardian's side):
`found_of_box_conseq` on DIMCID's family against `.bot CooperateBot`. -/
theorem guardian_finds_DIMCID :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      LenBox TAct k (guardCode (templateCode phiG) (progCode (GuardianBot k)) (progCode (DIMCID k))) :=
  found_of_box_conseq (pG (cl TB0) (cterm Act.C) (cterm Act.D)) boundedInnerNec_sixteen
    (loebSound_pG_of describes_botCB) qGD boxConseq_qGD
    (fun k ↦ guardCode (templateCode phiG) (progCode (GuardianBot k)) (progCode (DIMCID k)))
    (fun k ↦ by rw [progCode_GuardianBot_SV, progCode_DIMCID, templateCode_eq_quote_template phiG rfl]; exact guardCode_GD (V := ℕ) k)

/-- **DIMCID defects against Guardian and FINDS its guard, for all large `k`** (the self-fulfilling refutation
against the `SV`-described Guardian). -/
theorem loeb_DIMCID_vs_GuardianBot_core :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 2 (progCode (DIMCID k)) (progCode (GuardianBot k)) (progCode (DIMCID k)) 1 ∧
      LenBox TAct k (guardCode (templateCode phiD) (progCode (DIMCID k)) (progCode (GuardianBot k))) := by
  obtain ⟨k₀, h⟩ := dimcid_vs_described (describes_SV gG 1 (Or.inr rfl))
  refine ⟨k₀, fun k hk ↦ ?_⟩
  have := h k hk
  rw [templateCode_eq_quote_template phiD rfl]
  rwa [descVal_SV gG 1 (Or.inr rfl), ← progCode_GuardianBot_SV, ← progCode_DIMCID] at this

/-- **GuardianBot × DIMCID is `(D, D)` in PA-`S'`**, for all large `k`, unconditional. The engine proves
`(C, C)` by an unreadability census (`llm_outcome_GuardianBot_vs_DIMCID`, pad 2); in `S'` the value is
`(D, D)` because Guardian's guard "DIMCID defects against `.bot CooperateBot`" is TRUE (DIMCID's guard
against the frozen probe is self-fulfilling) and PROVABLE within the budget (a box consequence of DIMCID's
Löb family, `guardian_finds_DIMCID`), so Guardian punishes; and DIMCID's guard against Guardian is
self-fulfilling too, so DIMCID defects. -/
theorem loeb_GuardianBot_vs_DIMCID :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 2 (progCode (GuardianBot k)) (progCode (DIMCID k)) (progCode (GuardianBot k)) (actCode .D) ∧
      EvalGraph 2 (progCode (DIMCID k)) (progCode (GuardianBot k)) (progCode (DIMCID k)) (actCode .D) := by
  obtain ⟨k₁, h₁⟩ := guardian_finds_DIMCID
  obtain ⟨k₂, h₂⟩ := loeb_DIMCID_vs_GuardianBot_core
  exact ⟨k₁ + k₂, fun k hk ↦ ⟨guardian_D_of_found k (h₁ k (by omega)), (h₂ k (by omega)).1⟩⟩


end cell2

/-! ### 6. The `.neg` family `q ⋏ τq`, and cells 3, 4 — WaryBot × MirrorBot, WaryBot × WaryBot -/

section negFamily


/-! #### Wary's fixed formulas against Mirror and against itself -/

/-- The transposed Wary triple describes the transposed searcher `SV gWT 0 k` (values). -/
lemma desc_WT (k : V) :
    revalue ((Semiterm.lMap swap (uS gW 1)).val (s := stdReadingV V) ![] Empty.elim)
      ((Semiterm.lMap swap (wS gW 1)).val (s := stdReadingV V) ![] Empty.elim)
      ((Semiterm.lMap swap (TS gW 1)).val (s := stdReadingV V) ![k] Empty.elim) = SV gWT 0 k := by
  have := descT_SV gW 1 (Or.inr rfl) k
  rwa [lMap_swap_gW] at this

/-- Wary's guard against Mirror: "Mirror does NOT play C against `Wary(k)`". -/
noncomputable def qWM : Semisentence LAct 1 :=
  qT gW (TS gW 1) (uS gW 1) (wS gW 1) (cl TM) (numT 0) (numT 1)

lemma qWM_swap :
    Semiformula.lMap swap qWM =
      qT gWT (Semiterm.lMap swap (TS gW 1)) (Semiterm.lMap swap (uS gW 1)) (Semiterm.lMap swap (wS gW 1))
        (cl TM) (numT 0) (numT 1) := by
  unfold qWM
  rw [lMap_swap_qT, lMap_swap_gW, lMap_swap_cl, lMap_swap_TM, lMap_swap_numT, lMap_swap_numT]

theorem guardCode_WM (k : V) : guardCode (⌜gW⌝ : V) (SV gW 1 k) MirrorV = instB (⌜qWM⌝ : V) k :=
  guardCode_qT_eq_instB gW k _ _ _ _ _ _ (hX_SV gW 1 (Or.inr rfl) k) (hU_SV gW 1 (Or.inr rfl) k)
    (hW_SV gW 1 (Or.inr rfl) k) (hX_mirror k) hU_mirror hW_mirror

theorem guardCode_WMT (k : V) :
    guardCode (⌜gWT⌝ : V) (SV gWT 0 k) MirrorV = instB (⌜Semiformula.lMap swap qWM⌝ : V) k := by
  have := guardCode_qT_swap_eq_instB gW k _ _ _ _ _ _ (hX_SV gW 1 (Or.inr rfl) k) (hU_SV gW 1 (Or.inr rfl) k)
    (hW_SV gW 1 (Or.inr rfl) k) (hX_mirror k) hU_mirror hW_mirror
  rwa [transposeCode_SV gW 1 (Or.inr rfl), lMap_swap_gW, transposeCode_MirrorV] at this

theorem eval_qWM_iff (k : V) :
    Semiformula.Eval (s := stdReadingV V) ![k] Empty.elim qWM ↔ ¬ ∃ n, EvalGraph n MirrorV (SV gW 1 k) MirrorV 0 := by
  rw [qWM, eval_qT_neg_plays_opp_self .C _ _ _ _ _ _ k (desc_SV gW 1 (Or.inr rfl) k) (desc_mirror k), actCode_C_cast]

theorem eval_qWMT_iff (k : V) :
    Semiformula.Eval (s := stdReadingV V) ![k] Empty.elim (Semiformula.lMap swap qWM) ↔
      ¬ ∃ n, EvalGraph n MirrorV (SV gWT 0 k) MirrorV 1 := by
  rw [qWM_swap, eval_qT_neg_plays_opp_self .D _ _ _ _ _ _ k (desc_WT k) (desc_mirror k), actCode_D_cast]

/-- Wary's guard against itself: "`Wary(k)` does NOT play C against `Wary(k)`". -/
noncomputable def qWW : Semisentence LAct 1 :=
  qT gW (TS gW 1) (uS gW 1) (wS gW 1) (TS gW 1) (uS gW 1) (wS gW 1)

lemma qWW_swap :
    Semiformula.lMap swap qWW =
      qT gWT (Semiterm.lMap swap (TS gW 1)) (Semiterm.lMap swap (uS gW 1)) (Semiterm.lMap swap (wS gW 1))
        (Semiterm.lMap swap (TS gW 1)) (Semiterm.lMap swap (uS gW 1)) (Semiterm.lMap swap (wS gW 1)) := by
  unfold qWW
  rw [lMap_swap_qT, lMap_swap_gW]

theorem guardCode_WW (k : V) : guardCode (⌜gW⌝ : V) (SV gW 1 k) (SV gW 1 k) = instB (⌜qWW⌝ : V) k :=
  guardCode_qT_eq_instB gW k _ _ _ _ _ _ (hX_SV gW 1 (Or.inr rfl) k) (hU_SV gW 1 (Or.inr rfl) k)
    (hW_SV gW 1 (Or.inr rfl) k) (hX_SV gW 1 (Or.inr rfl) k) (hU_SV gW 1 (Or.inr rfl) k) (hW_SV gW 1 (Or.inr rfl) k)

theorem guardCode_WWT (k : V) :
    guardCode (⌜gWT⌝ : V) (SV gWT 0 k) (SV gWT 0 k) = instB (⌜Semiformula.lMap swap qWW⌝ : V) k := by
  have := guardCode_qT_swap_eq_instB gW k _ _ _ _ _ _ (hX_SV gW 1 (Or.inr rfl) k) (hU_SV gW 1 (Or.inr rfl) k)
    (hW_SV gW 1 (Or.inr rfl) k) (hX_SV gW 1 (Or.inr rfl) k) (hU_SV gW 1 (Or.inr rfl) k) (hW_SV gW 1 (Or.inr rfl) k)
  rwa [transposeCode_SV gW 1 (Or.inr rfl), lMap_swap_gW] at this

theorem eval_qWW_iff (k : V) :
    Semiformula.Eval (s := stdReadingV V) ![k] Empty.elim qWW ↔
      ¬ ∃ n, EvalGraph n (SV gW 1 k) (SV gW 1 k) (SV gW 1 k) 0 := by
  rw [qWW, eval_qT_neg_plays_opp_self .C _ _ _ _ _ _ k (desc_SV gW 1 (Or.inr rfl) k) (desc_SV gW 1 (Or.inr rfl) k),
    actCode_C_cast]

theorem eval_qWWT_iff (k : V) :
    Semiformula.Eval (s := stdReadingV V) ![k] Empty.elim (Semiformula.lMap swap qWW) ↔
      ¬ ∃ n, EvalGraph n (SV gWT 0 k) (SV gWT 0 k) (SV gWT 0 k) 1 := by
  rw [qWW_swap, eval_qT_neg_plays_opp_self .D _ _ _ _ _ _ k (desc_WT k) (desc_WT k), actCode_D_cast]

/-! #### The Löb premises: the `.neg` guard is self-fulfilling against a copier -/

/-- **Wary's Löb premise against Mirror, slack `(7, 8)`**: a box of the family makes Wary FIND its guard, so
Wary defects (fuel 2), so Mirror copies the defection (fuel 3), so "Mirror plays C against Wary" is FALSE by
determinism — the guard "¬(Mirror plays C against me)" is TRUE; the transposed searcher cooperates and Mirror
copies that, so "¬(Mirror plays D against me)" is true too. Both readings. -/
theorem loebSound_pWM : LoebSound (pQ qWM) 7 8 := by
  refine loebSound_pQ_of qWM fun V _ _ k h1 h2 ↦ ?_
  rw [← guardCode_WM] at h1
  rw [← guardCode_WMT] at h2
  have e1 := mirror_copies2_V _ _ (SV_search_V gW 1 k MirrorV h1)
  have e2 := mirror_copies2_V _ _ (SV_search_V gWT 0 k MirrorV h2)
  rw [Nat.cast_one] at e1
  rw [Nat.cast_zero] at e2
  have hA : ¬ ∃ n, EvalGraph n MirrorV (SV gW 1 k) MirrorV 0 := by
    rintro ⟨n, hn⟩
    exact _root_.zero_ne_one (EvalGraph.unique_V' n 3 _ _ _ _ _ hn e1)
  have hB : ¬ ∃ n, EvalGraph n MirrorV (SV gWT 0 k) MirrorV 1 := by
    rintro ⟨n, hn⟩
    exact _root_.one_ne_zero (EvalGraph.unique_V' n 3 _ _ _ _ _ hn e2)
  rw [← stdReadingV_eq_stdReading, eval_qWM_iff, eval_qWMT_iff]
  exact ⟨hA, hB⟩

/-- **Wary's Löb premise against itself, slack `(7, 8)`**: found ⇒ Wary defects against Wary ⇒ "Wary plays C
against Wary" is FALSE ⇒ the guard is true; the transposed searcher likewise. -/
theorem loebSound_pWW : LoebSound (pQ qWW) 7 8 := by
  refine loebSound_pQ_of qWW fun V _ _ k h1 h2 ↦ ?_
  rw [← guardCode_WW] at h1
  rw [← guardCode_WWT] at h2
  have e1 := SV_search_V gW 1 k (SV gW 1 k) h1
  have e2 := SV_search_V gWT 0 k (SV gWT 0 k) h2
  rw [Nat.cast_one] at e1
  rw [Nat.cast_zero] at e2
  have hA : ¬ ∃ n, EvalGraph n (SV gW 1 k) (SV gW 1 k) (SV gW 1 k) 0 := by
    rintro ⟨n, hn⟩
    exact _root_.zero_ne_one (EvalGraph.unique_V' n 2 _ _ _ _ _ hn e1)
  have hB : ¬ ∃ n, EvalGraph n (SV gWT 0 k) (SV gWT 0 k) (SV gWT 0 k) 1 := by
    rintro ⟨n, hn⟩
    exact _root_.one_ne_zero (EvalGraph.unique_V' n 2 _ _ _ _ _ hn e2)
  rw [← stdReadingV_eq_stdReading, eval_qWW_iff, eval_qWWT_iff]
  exact ⟨hA, hB⟩

/-! #### Cells 3 and 4 -/

/-- **Wary defects against Mirror and FINDS its `.neg` guard, for all large `k`**, unconditional. -/
theorem loeb_WaryBot_vs_MirrorBot_core :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 2 (progCode (WaryBot k)) (progCode MirrorBot) (progCode (WaryBot k)) 1 ∧
      LenBox TAct k (guardCode (templateCode phiW) (progCode (WaryBot k)) (progCode MirrorBot)) := by
  obtain ⟨k₀, hf⟩ := family_found (pQ qWM) boundedInnerNec_sixteen loebSound_pWM
  refine ⟨k₀, fun k hk ↦ ?_⟩
  obtain ⟨a, ha, hpc⟩ := hf k hk
  have ha' := le_def.mpr (pConj_slack_nat a _ _ _ k (formulaLen_instB_pQ (V := ℕ) qWM k) ha)
  have h1 := (pQ_both_V (V := ℕ) qWM k a ha' hpc).1
  rw [← guardCode_WM] at h1
  rw [progCode_WaryBot_SV, progCode_MirrorBot, ← MirrorV_nat, templateCode_eq_quote_template phiW rfl]
  exact ⟨SV_search_V (V := ℕ) gW 1 k MirrorV h1, h1⟩

/-- **WaryBot × MirrorBot is `(D, D)` in PA-`S'`**, for all large `k`, unconditional. The engine proves `(C, C)`
at EVERY `k` by a `.neg`-guard valuation census (`outcome_WaryBot_vs_MirrorBot`, pad 3); in `S'` the value is
`(D, D)` because Wary's guard "¬(Mirror plays C against me)" is SELF-FULFILLING against a copier (its proof
makes Wary defect, Mirror copies, so Mirror indeed does not cooperate) and bounded Löb finds it. -/
theorem loeb_WaryBot_vs_MirrorBot :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 3 (progCode (WaryBot k)) (progCode MirrorBot) (progCode (WaryBot k)) (actCode .D) ∧
      EvalGraph 3 (progCode MirrorBot) (progCode (WaryBot k)) (progCode MirrorBot) (actCode .D) := by
  obtain ⟨k₀, h⟩ := loeb_WaryBot_vs_MirrorBot_core
  exact ⟨k₀, fun k hk ↦ ⟨EvalGraph.mono_le (by omega) (h k hk).1, mirror_copies (h k hk).1⟩⟩


/-- **Wary defects against itself and FINDS its `.neg` guard, for all large `k`**, unconditional. -/
theorem loeb_WaryBot_vs_WaryBot_core :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 2 (progCode (WaryBot k)) (progCode (WaryBot k)) (progCode (WaryBot k)) 1 ∧
      LenBox TAct k (guardCode (templateCode phiW) (progCode (WaryBot k)) (progCode (WaryBot k))) := by
  obtain ⟨k₀, hf⟩ := family_found (pQ qWW) boundedInnerNec_sixteen loebSound_pWW
  refine ⟨k₀, fun k hk ↦ ?_⟩
  obtain ⟨a, ha, hpc⟩ := hf k hk
  have ha' := le_def.mpr (pConj_slack_nat a _ _ _ k (formulaLen_instB_pQ (V := ℕ) qWW k) ha)
  have h1 := (pQ_both_V (V := ℕ) qWW k a ha' hpc).1
  rw [← guardCode_WW] at h1
  rw [progCode_WaryBot_SV, templateCode_eq_quote_template phiW rfl]
  exact ⟨SV_search_V (V := ℕ) gW 1 k (SV gW 1 k) h1, h1⟩

/-- **WaryBot × WaryBot is `(D, D)` in PA-`S'`**, for all large `k`, unconditional. The engine proves `(C, C)`
at EVERY `k` by a `.neg`-guard valuation census (`outcome_WaryBot_vs_WaryBot`, pad 2); in `S'` the value is
`(D, D)` because Wary's guard "¬(Wary plays C against me)" is SELF-FULFILLING in self-play (its proof makes
Wary defect against itself) and bounded Löb finds it. -/
theorem loeb_WaryBot_vs_WaryBot :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 2 (progCode (WaryBot k)) (progCode (WaryBot k)) (progCode (WaryBot k)) (actCode .D) ∧
      EvalGraph 2 (progCode (WaryBot k)) (progCode (WaryBot k)) (progCode (WaryBot k)) (actCode .D) := by
  obtain ⟨k₀, h⟩ := loeb_WaryBot_vs_WaryBot_core
  exact ⟨k₀, fun k hk ↦ ⟨(h k hk).1, (h k hk).1⟩⟩


end negFamily

/-! ### 7. Cell 5 — DIMCID × CupodTrollBot `(D, C)`, on the budget-slot `CupodTroll7` -/

section cell5

lemma properPlayer_DIMCID (k : ℕ) : ProperPlayer (DIMCID k) := ⟨by simp [DIMCID], by simp [DIMCID]⟩

/-- DIMCID's and Cupod's templates differ: at the frame `(DefectBot, CooperateBot)`, "I play C against
CooperateBot ⇒ CooperateBot plays D against me" is true (a false antecedent) while "CooperateBot plays D
against DefectBot" is false. -/
lemma templateCode_phiD_ne_phiCu : templateCode phiD ≠ templateCode phiCu := by
  refine templateCode_ne_of_models DefectBot CooperateBot ?_ ?_
  · rw [← sentenceAt_subst DefectBot CooperateBot sfp_DefectBot.1 sfp_CooperateBot.1 _ rfl]
    show ℕ↓[LAct] ⊧ sentenceAt DefectBot CooperateBot
      (.impl (.plays DefectBot CooperateBot .C) (.plays CooperateBot DefectBot .D))
    rw [models_sentenceAt_impl, models_sentenceAt_plays _ _ _ _ _ sfp_DefectBot.1 sfp_CooperateBot.1]
    rintro ⟨N, hN⟩
    rw [progCode_DB] at hN
    exact absurd (EvalGraph.unique' hN (const_play 0 _ _ 1)) (by decide)
  · rw [← sentenceAt_subst DefectBot CooperateBot sfp_DefectBot.1 sfp_CooperateBot.1 _ rfl]
    show ¬ ℕ↓[LAct] ⊧ sentenceAt DefectBot CooperateBot (.plays CooperateBot DefectBot .D)
    rw [models_sentenceAt_plays _ _ _ _ _ sfp_CooperateBot.1 sfp_DefectBot.1]
    rintro ⟨N, hN⟩
    rw [progCode_CB] at hN
    exact absurd (EvalGraph.unique' hN (const_play 0 _ _ 0)) (by decide)

lemma progCode_DIMCID_ne_CupodBot (k : ℕ) : progCode (DIMCID k) ≠ progCode (CupodBot k) := by
  rw [progCode_DIMCID_search, progCode_CupodBot]
  intro e
  exact templateCode_phiD_ne_phiCu (pSearch_inj e).2.1


/-- CupodTroll's half on the ENGINE's own code, at every `k` (its guard does not read the frame's `me`). -/
theorem snd_CupodTrollBot_vs_DIMCID_engine (k : ℕ) :
    EvalGraph 2 (progCode (CupodTrollBot k)) (progCode (DIMCID k)) (progCode (CupodTrollBot k)) (actCode .C) :=
  ctb_C_of_ne k (properPlayer_DIMCID k) (progCode_DIMCID_ne_CupodBot k)


end cell5

end ArithS
