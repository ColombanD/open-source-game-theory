import ArithS.Cells.PositiveCells
import ArithS.Cells.DIMCID

/-!
# ArithS.Cells.FlipCells — the FLIP cells: where PA-`S'` disagrees with the engine's `S`

`Research/Notes/ARITHMETIZED_S_RESULTS.md` "THE FINDING" and `ROUTE_B_SCOPE.md` §2 (2026-09-23): the engine
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
   defects because DIMCID defects against `.bot CooperateBot` (the same Löb, `dimcid_vs_botCB_defects`).
4. **The box-consequence lemma** (`BoxConseq`, `box_conseq_uniform`, `found_of_box_conseq`): the general
   "`k̂`-chain" for a guard whose truth needs ANOTHER searcher's Löb-found guard. `TAct ⊢ ∀ k ≥ k̂,
   Box_g(psiF p)(k) → q(k)` by completeness (the chain `chain_core_VF` runs in every model), instantiated at
   `bnum k` (`lenProvable_inst_size`), the antecedents cut away (`NumeralFacts.lenProvable_le_bnumT` and the
   meta closure's box `exists_psiF_instance_length` + `BoundedInnerNec.nec`), the total polylog
   (`total_le_eventually`).
5. **Cell 2 — GuardianBot × DIMCID `(D, D)`** (`loeb_GuardianBot_vs_DIMCID`; engine
   `llm_outcome_GuardianBot_vs_DIMCID = (C, C)`, pad 2): Guardian's guard "DIMCID defects against
   `.bot CooperateBot`" is a box consequence of DIMCID's Löb family, so Guardian finds it (`guardian_finds_DIMCID`);
   DIMCID's guard against Guardian (described by the `SV` layer, `describes_Guardian`) is self-fulfilling.
6. **The `.neg` family** (`pQ q := q ⋏ τq`, `pQ_guards_V`, `SV_search_V`) and **cells 3, 4 — WaryBot × MirrorBot
   `(D, D)`, WaryBot × WaryBot `(D, D)`** (`loeb_WaryBot_vs_MirrorBot`, `loeb_WaryBot_vs_WaryBot`; engine
   `outcome_WaryBot_vs_MirrorBot`/`outcome_WaryBot_vs_WaryBot = (C, C)` at EVERY `k`, pads 3/2): "¬(you
   cooperate with me)" against a copier is self-fulfilling — found ⇒ Wary defects ⇒ the copier defects.

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

/-- **The program a description triple denotes at the budget `k`** (`X` the one-variable structural term,
`U W` the two closed re-valuation terms). -/
noncomputable def descVal (X : Semiterm LAct Empty 1) (U W : ClosedSemiterm LAct 0) (k : V) : V :=
  relabel (U.val (s := stdActV V) ![] Empty.elim) (W.val (s := stdActV V) ![] Empty.elim)
    (X.val (s := stdActV V) ![k] Empty.elim)

lemma descVal_def (X : Semiterm LAct Empty 1) (U W : ClosedSemiterm LAct 0) (k : V) :
    descVal X U W k =
      relabel (U.val (s := stdActV V) ![] Empty.elim) (W.val (s := stdActV V) ![] Empty.elim)
        (X.val (s := stdActV V) ![k] Empty.elim) := rfl

/-- **A triple describes its value in every model**: the three code hypotheses of the instance equations
(`guardCode_qT_eq_instB`, `guardCode_DimcidV_eq_instB`) and "the transposed triple denotes the transposed
program". Every zoo opponent's triple is one (`describes_botCB`, `describes_TFT`, `describes_Guardian`). -/
structure Describes (X : Semiterm LAct Empty 1) (U W : ClosedSemiterm LAct 0) : Prop where
  hX : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (k : V),
    termSubst LAct (bnum k ∷ (0 : V)) (⌜(Rew.emb X : SyntacticSemiterm LAct 1)⌝ : V) =
      progT (dnum (descVal X U W k))
  hU : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (k : V), (⌜U⌝ : V) = dU (descVal X U W k)
  hW : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (k : V), (⌜W⌝ : V) = dW (descVal X U W k)
  hT : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (k : V),
    descVal (Semiterm.lMap swap X) (Semiterm.lMap swap U) (Semiterm.lMap swap W) k = swapcode (descVal X U W k)

/-- **DIMCID's Löb premise against ANY described opponent, slack `(7, 8)`** (`loebSound_pDi0`, made
generic): a box of the family makes `DimcidV k` defect against the opponent and the transposed searcher
cooperate with the transposed opponent, so the antecedents "I play C" / "I play D" are FALSE and both
implications hold in both readings — whatever the consequents say. This is the self-fulfilling refutation:
the guard "I cooperate ⇒ …" is made true by the defection its own proof triggers. -/
theorem loebSound_pG_of {X : Semiterm LAct Empty 1} {U W : ClosedSemiterm LAct 0} (h : Describes X U W) :
    LoebSound (pG X U W) 7 8 := by
  intro V _ _ k a ha hp
  have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
  have ha' : a + 8 * (formulaLen LAct (instB (⌜qDG X U W⌝ : V) k) +
      formulaLen LAct (instB (⌜qTG (Semiterm.lMap swap X) (Semiterm.lMap swap U) (Semiterm.lMap swap W)⌝ : V) k))
      + 7 ≤ k :=
    le_trans (pConj_slack_le a _ _ _ (formulaLen_instB_pG X U W k)) ha
  obtain ⟨h1, h2⟩ := pG_both_V k X U W (h.hX V k) (h.hU V k) (h.hW V k) a ha' hp
  have hA : ¬ ∃ n, EvalGraph n (DimcidV k) (descVal X U W k) (DimcidV k) 0 := by
    rintro ⟨n, hn⟩
    exact _root_.zero_ne_one (EvalGraph.unique_V' n 2 _ _ _ _ _ hn h1)
  have hB : ¬ ∃ n, EvalGraph n (DimcidTV k) (swapcode (descVal X U W k)) (DimcidTV k) 1 := by
    rintro ⟨n, hn⟩
    exact _root_.one_ne_zero (EvalGraph.unique_V' n 2 _ _ _ _ _ hn h2)
  exact ⟨(eval_pG_iff_stdActS k X U W rfl (h.hT V k)).mpr ⟨fun h ↦ absurd h hA, fun h ↦ absurd h hB⟩,
    (eval_pG_iff_swap k X U W rfl (h.hT V k)).mpr ⟨fun h ↦ absurd h hA, fun h ↦ absurd h hB⟩⟩

/-- **DIMCID defects against every described opponent, and FINDS its guard, for all large `k`**,
unconditional: `family_found` on `pG X U W` (the arithmetized `pblt_engine`), then ∧-elimination on codes
(`pG_both_V`, `pG_guards_V`). -/
theorem dimcid_vs_described {X : Semiterm LAct Empty 1} {U W : ClosedSemiterm LAct 0} (h : Describes X U W) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 2 (Dimcid k) (descVal X U W k) (Dimcid k) 1 ∧
      LenProvableV TAct k (guardCode (⌜tmplD⌝ : ℕ) (Dimcid k) (descVal X U W k)) := by
  obtain ⟨k₀, hf⟩ := family_found (pG X U W) boundedInnerNec_sixteen (loebSound_pG_of h)
  refine ⟨k₀, fun k hk ↦ ?_⟩
  obtain ⟨a, ha, hpc⟩ := hf k hk
  have ha' := le_def.mpr (pConj_slack_nat a _ _ _ k (formulaLen_instB_pG (V := ℕ) X U W k) ha)
  exact ⟨(pG_both_V (V := ℕ) k X U W (h.hX ℕ k) (h.hU ℕ k) (h.hW ℕ k) a ha' hpc).1,
    (pG_guards_V (V := ℕ) k X U W (h.hX ℕ k) (h.hU ℕ k) (h.hW ℕ k) a ha' hpc).1⟩

end described

/-! ### 2. Closed opponents: `.bot CooperateBot` and TitForTatBot -/

section closedOpponents

/-! #### `.bot CooperateBot` -/

lemma descVal_botCB (k : V) : descVal (cl TB0) (cterm Act.C) (cterm Act.D) k = pBot (pConst 0) :=
  val_desc_bot_zero k

lemma descVal_botCB_T (k : V) :
    descVal (Semiterm.lMap swap (cl TB0)) (Semiterm.lMap swap (cterm Act.C)) (Semiterm.lMap swap (cterm Act.D)) k =
      pBot (pConst 1) := by
  rw [descVal_def, lMap_swap_cl, lMap_swap_TB0, lMap_swap_cterm_C, lMap_swap_cterm_D]
  exact val_desc_bot_one k

/-- The triple `(cl TB0, C, D)` describes `.bot CooperateBot` in every model. -/
theorem describes_botCB : Describes (cl TB0) (cterm Act.C) (cterm Act.D) where
  hX := by intro V _ _ k; rw [descVal_botCB]; exact hX_bot_zero k
  hU := by intro V _ _ k; rw [descVal_botCB]; exact hU_C_bot_zero
  hW := by intro V _ _ k; rw [descVal_botCB]; exact hW_D_bot_zero
  hT := by intro V _ _ k; rw [descVal_botCB_T, descVal_botCB, swapcode_pBot, swapcode_pConst_zero]

/-! #### TitForTatBot -/

/-- TitForTatBot in every model: "if `opp` plays C against `.bot CooperateBot` then C else D". -/
noncomputable def TFTV : V := pIte (pSim pOpp (pBot (pConst 0))) 0 (pConst 0) (pConst 1)
/-- Its transposition: "if `opp` plays D against `.bot DefectBot` then D else C". -/
noncomputable def TFTTV : V := pIte (pSim pOpp (pBot (pConst 1))) 1 (pConst 1) (pConst 0)

lemma cast_TFT : ((pcode TitForTatBot : ℕ) : V) = TFTV := by
  simp only [TitForTatBot, CooperateBot, pcode_ite, pcode_sim, pcode_opp, pcode_bot, pcode_const, actCode]
  rw [cast_pIte, cast_pSim, cast_pOpp, cast_pBot, cast_pConst, cast_pConst]
  simp [TFTV]

lemma TFTV_nat : TFTV (V := ℕ) = pcode TitForTatBot := by
  rw [← cast_TFT, natCast_nat]

theorem swapcode_TFTV : swapcode (TFTV : V) = TFTTV := by
  unfold TFTV TFTTV swapcode
  simp [relabelAct]

/-- The code of TFT is below the code of its transposition (the probe `.bot CooperateBot` is the smaller). -/
theorem TFTV_lt_TFTTV : (TFTV : V) < TFTTV := by
  unfold TFTV TFTTV pIte pSim pBot pConst pOpp ppair
  norm_num

lemma dnum_TFTV : dnum (TFTV : V) = TFTV := dnum_of_lt (by rw [swapcode_TFTV]; exact TFTV_lt_TFTTV)

lemma dU_TFTV : dU (TFTV : V) = csym 0 := by
  unfold dU; rw [swapcode_TFTV, if_pos TFTV_lt_TFTTV]

lemma dW_TFTV : dW (TFTV : V) = csym 1 := by
  unfold dW; rw [swapcode_TFTV, if_pos TFTV_lt_TFTTV]

/-- The closed structural term of TitForTatBot's code. -/
noncomputable def TTFT : ClosedSemiterm LAct 0 := Semiterm.lMap emb (progTT (pcode TitForTatBot))

lemma lMap_swap_TTFT : Semiterm.lMap swap TTFT = TTFT := term_lMap_swap_emb _

theorem val_TTFT_V : TTFT.val (s := stdActV V) ![] Empty.elim = TFTV := by
  unfold TTFT
  rw [Semiterm.val_lMap, stdActV_lMap_emb, val_progTT_V, cast_TFT]

theorem quote_emb_TTFT : (⌜(Rew.emb TTFT : SyntacticSemiterm LAct 0)⌝ : V) = progT TFTV := by
  unfold TTFT
  rw [term_emb_lMap_emb, quote_term_lMap_emb, ← Semiterm.empty_quote_def, quote_progTT, cast_TFT]

lemma descVal_TFT (k : V) : descVal (cl TTFT) (cterm Act.C) (cterm Act.D) k = TFTV := by
  rw [descVal_def, val_cl_V, val_TTFT_V, val_cterm_C_V, val_cterm_D_V, relabel_zero_one]

lemma descVal_TFT_T (k : V) :
    descVal (Semiterm.lMap swap (cl TTFT)) (Semiterm.lMap swap (cterm Act.C)) (Semiterm.lMap swap (cterm Act.D)) k =
      TFTTV := by
  rw [descVal_def, lMap_swap_cl, lMap_swap_TTFT, lMap_swap_cterm_C, lMap_swap_cterm_D, val_cl_V, val_TTFT_V,
    val_cterm_C_V, val_cterm_D_V]
  exact swapcode_TFTV

/-- The triple `(cl TTFT, C, D)` describes TitForTatBot in every model. -/
theorem describes_TFT : Describes (cl TTFT) (cterm Act.C) (cterm Act.D) where
  hX := by
    intro V _ _ k
    rw [descVal_TFT, quote_emb_cl_V, termSubst_closed _ (semiterm_quote_emb₀ _), quote_emb_TTFT, dnum_TFTV]
  hU := by intro V _ _ k; rw [descVal_TFT, quote_cterm_C, dU_TFTV]
  hW := by intro V _ _ k; rw [descVal_TFT, quote_cterm_D, dW_TFTV]
  hT := by intro V _ _ k; rw [descVal_TFT_T, descVal_TFT, swapcode_TFTV]

end closedOpponents

/-! ### 3. Cell 1 — DIMCID × TitForTatBot `(D, D)` -/

section cell1

/-- **DIMCID defects against `.bot CooperateBot` for all large `k`** (the self-fulfilling Löb of
`loeb_DIMCID_vs_CooperateBot`, against the frozen probe), with the box form. -/
theorem dimcid_vs_botCB_defects :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 2 (pcode (DIMCID k)) (pBot (pConst 0)) (pcode (DIMCID k)) 1 ∧
      LenProvableV TAct k (guardCode (tcode phiD) (pcode (DIMCID k)) (pBot (pConst 0))) := by
  obtain ⟨k₀, h⟩ := dimcid_vs_described describes_botCB
  refine ⟨k₀, fun k hk ↦ ?_⟩
  have := h k hk
  rwa [descVal_botCB, ← pcode_DIMCID] at this

/-- **DIMCID defects against TitForTatBot and FINDS its guard, for all large `k`.** -/
theorem dimcid_vs_TFT_defects :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 2 (pcode (DIMCID k)) (pcode TitForTatBot) (pcode (DIMCID k)) 1 ∧
      LenProvableV TAct k (guardCode (tcode phiD) (pcode (DIMCID k)) (pcode TitForTatBot)) := by
  obtain ⟨k₀, h⟩ := dimcid_vs_described describes_TFT
  refine ⟨k₀, fun k hk ↦ ?_⟩
  have := h k hk
  rwa [descVal_TFT, TFTV_nat, ← pcode_DIMCID] at this

/-- **DIMCID × TitForTatBot is `(D, D)` in PA-`S'`**, for all large `k`, unconditional. The engine proves
`(C, C)` by an unreadability census (`llm_outcome_DIMCID_vs_TitForTatBot`, pad 4); in `S'` the value is
`(D, D)` because DIMCID's guard "I play C against TFT ⇒ TFT plays D against me" is SELF-FULFILLING (its proof
makes DIMCID defect, which falsifies the antecedent) and bounded Löb finds it, so DIMCID defects; and TFT's
probe sees DIMCID defect against `.bot CooperateBot` (the same Löb), so TFT defects. -/
theorem loeb_DIMCID_vs_TitForTatBot :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 4 (pcode (DIMCID k)) (pcode TitForTatBot) (pcode (DIMCID k)) (actCode .D) ∧
      EvalGraph 4 (pcode TitForTatBot) (pcode (DIMCID k)) (pcode TitForTatBot) (actCode .D) := by
  obtain ⟨k₁, h₁⟩ := dimcid_vs_TFT_defects
  obtain ⟨k₂, h₂⟩ := dimcid_vs_botCB_defects
  refine ⟨k₁ + k₂, fun k hk ↦ ⟨?_, ?_⟩⟩
  · exact EvalGraph.mono_le (by omega) (h₁ k (by omega)).1
  · exact EvalGraph.mono_le (by omega) (tft_D_of_probe_D (h₂ k (by omega)).1)

/-- **The box form of cell 1**: DIMCID FINDS its guard against TitForTatBot within its budget, for all large `k`. -/
theorem dimcid_finds_guard_vs_TFT :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      LenProvableV TAct k (guardCode (tcode phiD) (pcode (DIMCID k)) (pcode TitForTatBot)) := by
  obtain ⟨k₀, h⟩ := dimcid_vs_TFT_defects
  exact ⟨k₀, fun k hk ↦ (h k hk).2⟩

end cell1

end ArithS
