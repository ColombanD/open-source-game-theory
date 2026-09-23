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

/-! ### 4. The box-consequence lemma: a guard whose truth needs another searcher's Löb-found guard -/

section boxConseq

/-- **A consequence of the family's box**: `q(k)` holds in both readings whenever the `k`-instance of `p`
has a `TAct`-proof with the slack to spare — the shape of `LoebSound`, with the conclusion `q` in place of
`p` (`LoebSound p S₀ S₁ = BoxConseq p p S₀ S₁`). For a guard `q` that describes ANOTHER searcher's play,
`q(k)` is true once that searcher's guard is found, i.e. once its family `p` has such a proof. -/
def BoxConseq (p q : Semisentence LAct 1) (S₀ S₁ : ℕ) : Prop :=
  ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔] (k a : V),
    a + (S₀ : V) + (S₁ : V) * formulaLen LAct (instB (⌜p⌝ : V) k) ≤ k →
    LenDerivable TAct a (instB (⌜p⌝ : V) k) →
    Semiformula.Eval (s := stdActS V) ![k] Empty.elim q ∧ Semiformula.Eval (s := swapActS V) ![k] Empty.elim q

lemma loebSound_iff_boxConseq (p : Semisentence LAct 1) (S₀ S₁ : ℕ) :
    LoebSound p S₀ S₁ ↔ BoxConseq p p S₀ S₁ := Iff.rfl

/-- **The uniform theorem of a box consequence** (`pblt_uniformF`'s shape, with `q` in the conclusion and the
box `Box_g (psiF p)` as an explicit antecedent): `TAct ⊢ ∀ k, (k̂ ≤ k → (Box_g (psiF p) (k) → q(k)))` — by
completeness, since in every model the chain (`chain_core_VF`) turns the box into a proof of `p(k)` with the
slack to spare, and `hq` turns that into `q(k)`. Needs NO Löb premise: the box is assumed, not derived. -/
theorem box_conseq_uniform (p : Semisentence LAct 1) {S₀ S₁ d : ℕ} (hE : BoundedInnerNec d)
    (q : Semisentence LAct 1) (hq : BoxConseq p q S₀ S₁) :
    ∃ kHat : ℕ, TAct ⊢ ∀¹ ((leF (↑kHat) #0 : Semisentence LAct 1) 🡒 (Box_g (psiF p) 🡒 q)) := by
  obtain ⟨N₁, hN₁⟩ := exists_forward_lengthF p
  obtain ⟨Cψ, hCψ⟩ := hE.nec (psiF p)
  obtain ⟨C, hC⟩ := chainBoundF_poly p S₀ S₁ N₁ d Cψ
  obtain ⟨kHat₀, hkHat₀⟩ := poly_size_le_eventually C (3 * d + 3)
  refine ⟨kHat₀ + 1, tact_complete' _ fun M _ _ ↦ ?_⟩
  have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
  have key : ∀ k : M, ((kHat₀ + 1 : ℕ) : M) ≤ k → LenDerivable TAct (gBudget k) (instB (⌜psiF p⌝ : M) k) →
      Semiformula.Eval (s := stdActS M) ![k] Empty.elim q ∧
      Semiformula.Eval (s := swapActS M) ![k] Empty.elim q := by
    intro k hk hbox
    have hk₀ : (kHat₀ : M) ≤ k := le_trans (by push_cast; exact le_self_add) hk
    have hs1 : 1 ≤ ‖k‖ := by
      have h1 : (1 : M) ≤ k := le_trans (by push_cast; exact le_add_self) hk
      have := length_monotone h1
      rwa [length_one] at this
    have hbound : chainBoundF p S₀ S₁ N₁ d Cψ k ≤ k := le_trans (hC M k hs1) (hkHat₀ M k hk₀)
    have hnec : NecAtF p d Cψ M := fun k ↦ hCψ M k
    obtain ⟨a, ha, hp⟩ := chain_core_VF p hnec (hN₁ M) k hbound hbox
    exact hq M k a ha hp
  constructor
  · simp only [Semiformula.eval_all, LogicalConnective.HomClass.map_imply, LogicalConnective.Prop.arrow_eq]
    intro x hx hbox
    rw [eval_Box_g_iff_std] at hbox
    exact (key x ((eval_leF_numeral_bvar _ stdActS_lMap_emb _ x).mp hx) hbox).1
  · simp only [Semiformula.eval_all, LogicalConnective.HomClass.map_imply, LogicalConnective.Prop.arrow_eq]
    intro x hx hbox
    rw [eval_Box_g_iff_swap] at hbox
    exact (key x ((eval_leF_numeral_bvar _ swapActS_lMap_emb _ x).mp hx) hbox).2

/-- Foundation's `≤` at ℕ (`le_def`) read as `Nat.le`, with the sides inferred (never restate a term that
carries `‖k‖ ^ d`: the pow instance at ℕ is `instCommSemiring_foundation`'s, not `Nat.instMonoid`'s). -/
lemma nat_le_of_le_def {a b : ℕ} (h : a = b ∨ a < b) : a ≤ b := by omega

/-- Substitution distributes over the implication. -/
lemma substs_imp (φ ψ : Semisentence LAct 1) (t : ClosedSemiterm LAct 0) :
    ((φ 🡒 ψ : Semisentence LAct 1) ⇜ ![t] : Sentence LAct) =
      ((φ ⇜ ![t] : Sentence LAct) 🡒 (ψ ⇜ ![t] : Sentence LAct)) := by
  simp

/-- **The total cost of the instantiated chain is polylog**: `A + B‖k‖ + C₁‖k‖² + Cψ(gBudget k ^ d + 1) ≤ k` for
all large `k`, in every model (the `PLE` bookkeeping of `Assembly/Family.lean` §6). -/
theorem total_le_eventually (A B C₁ Cψ d : ℕ) :
    ∃ kHat : ℕ, ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (k : V), (kHat : V) ≤ k →
      (A : V) + (B : V) * ‖k‖ + (C₁ : V) * ‖k‖ * ‖k‖ + (Cψ : V) * (gBudget k ^ d + 1) ≤ k := by
  obtain ⟨kHat, h⟩ := poly_size_le_eventually (A + B + C₁ + Cψ * 2) (3 * d + 2)
  refine ⟨kHat + 1, fun V _ _ k hk ↦ ?_⟩
  have hk₀ : (kHat : V) ≤ k := le_trans (by push_cast; exact le_self_add) hk
  have hs1 : 1 ≤ ‖k‖ := by
    have h1 : (1 : V) ≤ k := le_trans (by push_cast; exact le_add_self) hk
    have := length_monotone h1
    rwa [length_one] at this
  refine le_trans ?_ (h V k hk₀)
  have hA : PLE ‖k‖ (A : V) A (3 * d + 2) := PLE.mono hs1 (PLE.const A) le_rfl (Nat.zero_le _)
  have hB : PLE ‖k‖ ((B : V) * ‖k‖) B (3 * d + 2) :=
    PLE.mono hs1 (PLE.mul (PLE.const B) PLE.var) (by omega) (by omega)
  have hC : PLE ‖k‖ ((C₁ : V) * ‖k‖ * ‖k‖) C₁ (3 * d + 2) :=
    PLE.mono hs1 (PLE.mul (PLE.mul (PLE.const C₁) PLE.var) PLE.var) (by omega) (by omega)
  have hg : PLE ‖k‖ (gBudget k ^ d + 1) (1 + 1) (3 * d) :=
    PLE.add (PLE.mono hs1 (PLE.pow (PLE_gBudget hs1) d) (by simp) le_rfl)
      (PLE.mono hs1 PLE.one le_rfl (Nat.zero_le _))
  have hD : PLE ‖k‖ ((Cψ : V) * (gBudget k ^ d + 1)) (Cψ * 2) (3 * d + 2) :=
    PLE.mono hs1 (PLE.mul (PLE.const Cψ) hg) (by omega) (by omega)
  exact PLE.add (PLE.add (PLE.add hA hB) hC) hD

/-- **A box consequence is FOUND within the budget for all large `k`** (the general "`k̂`-chain"): given
bounded inner necessitation, the family's Löb premise (for the meta closure, i.e. the box at ℕ) and
`BoxConseq p q`, the guard-code family `G k = instB ⌜q⌝ k` has a `TAct`-proof within `k` for all large
`k`. The proof: the uniform theorem `∀ k, (k̂ ≤ k → (Box_g (psiF p) (k) → q(k)))` (`box_conseq_uniform`)
instantiated at `bnum k` (`lenProvable_inst_size`), the numeral antecedent cut away
(`NumeralFacts.lenProvable_le_bnumT`), the box antecedent cut away with the necessitated meta closure
(`exists_psiF_instance_length` + `BoundedInnerNec.nec` at ℕ), the total `A + B·size k + C₁·size k² +
Cψ·(gBudget k ^ d + 1)` polylog (`total_le_eventually`). -/
theorem found_of_box_conseq (p : Semisentence LAct 1) {S₀ S₁ d : ℕ} (hE : BoundedInnerNec d)
    (hs : LoebSound p S₀ S₁) (q : Semisentence LAct 1) (hq : BoxConseq p q S₀ S₁) (G : ℕ → ℕ)
    (hG : ∀ k, G k = instB (⌜q⌝ : ℕ) k) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k → LenProvableV TAct k (G k) := by
  obtain ⟨kHat, hprov⟩ := box_conseq_uniform p hE q hq
  obtain ⟨N₃, hN₃⟩ := lenProvable_of_provable hprov
  obtain ⟨C₀, C₁, hle⟩ := lenProvable_le_bnumT kHat
  obtain ⟨kHat', K₀, K₁, K₂, hmeta⟩ := exists_psiF_instance_length p hE hs
  obtain ⟨Cψ, hCψ⟩ := hE.nec (psiF p)
  set fr := flen (((leF (↑kHat) #0 : Semisentence LAct 1) 🡒 (Box_g (psiF p) 🡒 q) : Semisentence LAct 1) :
    Semiproposition LAct 1) with hfr
  set fB := flen (Box_g (psiF p) : Semiproposition LAct 1) with hfB
  set fq := flen (q : Semiproposition LAct 1) with hfq
  set c := tlen (Rew.emb (↑kHat : ClosedSemiterm LAct 0) : SyntacticSemiterm LAct 0) with hc
  obtain ⟨kHat₂, hkHat₂⟩ := total_le_eventually (N₃ + 13 * fr + C₀ + 20 * c + 40 * fB + 40 * fq + 86)
    (30 * fr + 120 * fB + 120 * fq + 126) C₁ Cψ d
  refine ⟨kHat + kHat' + 2 ^ (K₀ + K₁ + K₂ + 1) + kHat₂ + 1, fun k hk ↦ ?_⟩
  have h2pow : 2 ≤ 2 ^ (K₀ + K₁ + K₂ + 1) := Nat.le_self_pow (Nat.succ_ne_zero _) 2
  -- the meta closure, as the box on codes, below the budget `gBudget k` (as in `family_found`)
  have hbox : LenDerivable TAct (gBudget k) (instB (⌜psiF p⌝ : ℕ) k) := by
    have h := hmeta k (by omega)
    rw [← lenProvableV_nat, ← lenDerivable_iff_lenProvableV] at h
    have hq : instB (⌜psiF p⌝ : ℕ) k = ⌜(psiF p ⇜ ![Semiterm.lMap emb (bnumT k)] : Sentence LAct)⌝ := by
      have := quote_instB (V := ℕ) (psiF p) k
      rwa [natCast_nat] at this
    rw [← hq] at h
    refine lenDerivable_mono_V ?_ h
    have hsize : K₀ + K₁ + K₂ + 1 ≤ Nat.size k := Nat.lt_size.mpr (by omega)
    have hcube := quadratic_le_cube K₀ K₁ K₂ (Nat.size k) hsize
    unfold gBudget
    rw [← size_eq_length]
    exact le_def.mpr (Nat.eq_or_lt_of_le hcube)
  -- the necessitated box: `TAct ⊢ Box_g (psiF p) (k)` at polylog length
  obtain ⟨e, he, hBx⟩ := hCψ ℕ k hbox
  -- step 1: instantiate the uniform theorem at `bnumT k`; step 2: the numeral antecedent; the budget
  have h1 := lenProvable_inst_size ((leF (↑kHat) #0 : Semisentence LAct 1) 🡒 (Box_g (psiF p) 🡒 q)) k hN₃
  have h2 := hle k (by omega)
  have hpoly := hkHat₂ ℕ k (le_def.mpr (Or.inr (by rw [natCast_nat]; omega)))
  simp only [natCast_nat] at hpoly he
  rw [← size_eq_length] at hpoly
  -- abbreviations, introduced AFTER the facts so that they fold everywhere
  set t : ClosedSemiterm LAct 0 := Semiterm.lMap emb (bnumT k) with ht
  set s := Nat.size k with hs
  have hBx' : LenProvable (fbound : ℕ → ℕ) e TAct (⌜(Box_g (psiF p) ⇜ ![t] : Sentence LAct)⌝ : ℕ) := by
    have hqB : instB (⌜Box_g (psiF p)⌝ : ℕ) k = ⌜(Box_g (psiF p) ⇜ ![t] : Sentence LAct)⌝ := by
      have := quote_instB (V := ℕ) (Box_g (psiF p)) k
      rwa [natCast_nat] at this
    rw [lenDerivable_iff_lenProvableV, lenProvableV_nat, hqB] at hBx
    exact hBx
  have hrt : flen ((((leF (↑kHat) #0 : Semisentence LAct 1) 🡒 (Box_g (psiF p) 🡒 q)) ⇜ ![t] : Sentence LAct) :
      Proposition LAct) ≤ fr * (6 * s + 2) := flen_subst_bnumT_le _ k
  have h1' : LenProvable (fbound : ℕ → ℕ) (N₃ + 5 * (fr * (6 * s + 2)) + 3 * fr + 6 * s + 8) TAct
      (⌜(((leF (↑kHat) #0 : Semisentence LAct 1) 🡒 (Box_g (psiF p) 🡒 q)) ⇜ ![t] : Sentence LAct)⌝ : ℕ) :=
    lenProvable_fbound_mono (by omega) h1
  rw [substs_leF_imp, substs_imp] at h1'
  -- step 3: the two cuts
  have h3 := lenProvable_mp h1' h2
  have h4 := lenProvable_mp h3 hBx'
  -- the bookkeeping
  have hBt : flen ((Box_g (psiF p) ⇜ ![t] : Sentence LAct) : Proposition LAct) ≤ fB * (6 * s + 2) :=
    flen_subst_bnumT_le _ k
  have hqt : flen ((q ⇜ ![t] : Sentence LAct) : Proposition LAct) ≤ fq * (6 * s + 2) := flen_subst_bnumT_le _ k
  have hleF : flen ((leF (↑kHat) t : Sentence LAct) : Proposition LAct) ≤ 2 * c + 2 * (6 * s + 1) + 3 := by
    rw [flen_leF_sentence, ht, tlen_emb_lMap_bnumT]
    have : tlen (Rew.emb (bnumT k) : SyntacticSemiterm ℒₒᵣ 0) ≤ 6 * s + 1 := tlen_bnumT k
    omega
  have hBqt := flen_imply_sentence (Box_g (psiF p) ⇜ ![t] : Sentence LAct) (q ⇜ ![t] : Sentence LAct)
  have hpoly' := nat_le_of_le_def (le_def.mp hpoly)
  have he' := nat_le_of_le_def (le_def.mp he)
  have hq' : instB (⌜q⌝ : ℕ) k = ⌜(q ⇜ ![t] : Sentence LAct)⌝ := by
    have := quote_instB (V := ℕ) q k
    rwa [natCast_nat] at this
  rw [hG, hq', lenProvableV_nat]
  refine lenProvable_fbound_mono (le_trans ?_ hpoly') h4
  calc _ ≤ N₃ + 5 * (fr * (6 * s + 2)) + 3 * fr + 6 * s + 8 + (C₀ + C₁ * s * s)
        + 10 * ((2 * c + 2 * (6 * s + 1) + 3) + (fB * (6 * s + 2) + fq * (6 * s + 2) + 1)) + 9 + e
        + 10 * (fB * (6 * s + 2) + fq * (6 * s + 2)) + 9 := by
          rw [hBqt]; gcongr
    _ = N₃ + 13 * fr + C₀ + 20 * c + 40 * fB + 40 * fq + 86 + (30 * fr + 120 * fB + 120 * fq + 126) * s
        + C₁ * s * s + e := by ring
    _ ≤ _ := Nat.add_le_add_left he' _

end boxConseq

/-! ### 5. Cell 2 — GuardianBot × DIMCID `(D, D)` -/

section cell2

/-- Guardian's guard template: "opp plays D against `.bot CooperateBot`". -/
noncomputable abbrev gG : Semisentence LAct 6 := tmpl (.plays .opp (.bot CooperateBot) .D)
/-- Its transposition: "opp plays C against `.bot DefectBot`". -/
noncomputable abbrev gGT : Semisentence LAct 6 := tmpl (.plays .opp (.bot DefectBot) .C)

lemma lMap_swap_gG : Semiformula.lMap swap gG = gGT := lMap_swap_tmpl _ rfl

lemma pcode_GuardianBot_SV (k : ℕ) : pcode (GuardianBot k) = SV (V := ℕ) gG 1 k := by
  rw [pcode_GuardianBot, SV_nat]; rfl

/-! #### The `SV` layer describes the engine searchers -/

lemma descVal_SV (g : Semisentence LAct 6) (a : ℕ) (ha : a = 0 ∨ a = 1) (k : V) :
    descVal (TS g a) (uS g a) (wS g a) k = SV g a k := hme_SV g a ha k

lemma descVal_SV_T (g : Semisentence LAct 6) (a : ℕ) (ha : a = 0 ∨ a = 1) (k : V) :
    descVal (Semiterm.lMap swap (TS g a)) (Semiterm.lMap swap (uS g a)) (Semiterm.lMap swap (wS g a)) k =
      SV (Semiformula.lMap swap g) (1 - a) k := hme_SVT g a ha k

/-- **The canonical triple of an engine searcher describes it in every model** (`PositiveCells` §2, packaged). -/
theorem describes_SV (g : Semisentence LAct 6) (a : ℕ) (ha : a = 0 ∨ a = 1) : Describes (TS g a) (uS g a) (wS g a) where
  hX := by intro V _ _ k; rw [descVal_SV g a ha]; exact hX_SV g a ha k
  hU := by intro V _ _ k; rw [descVal_SV g a ha]; exact hU_SV g a ha k
  hW := by intro V _ _ k; rw [descVal_SV g a ha]; exact hW_SV g a ha k
  hT := by intro V _ _ k; rw [descVal_SV_T g a ha, descVal_SV g a ha, swapcode_SV g a ha]

/-! #### Guardian's guard against DIMCID as a fixed formula, its instance and truth equations -/

/-- Guardian's guard against `DimcidV k`: "`DimcidV k` plays D against `.bot CooperateBot`". -/
noncomputable def qGD : Semisentence LAct 1 := qT gG (TS gG 1) (uS gG 1) (wS gG 1) TDi uDi wDi

theorem guardCode_GD (k : V) : guardCode (⌜gG⌝ : V) (SV gG 1 k) (DimcidV k) = instB (⌜qGD⌝ : V) k :=
  guardCode_qT_eq_instB gG k _ _ _ _ _ _ (hX_SV gG 1 (Or.inr rfl) k) (hU_SV gG 1 (Or.inr rfl) k)
    (hW_SV gG 1 (Or.inr rfl) k) (hX_self k) (hU_self k) (hW_self k)

/-- `qGD(k)` in the standard reading: `DimcidV k` plays D against `pBot (pConst 0)`. -/
theorem eval_qGD_iff (k : V) :
    Semiformula.Eval (s := stdActV V) ![k] Empty.elim qGD ↔
      ∃ n, EvalGraph n (DimcidV k) (pBot (pConst 0)) (DimcidV k) 1 := by
  unfold qGD
  rw [eval_qT_iff, eval_tmpl_plays_opp_closed_V _ (by intro h; cases h) (by intro h; cases h)]
  simp only [Matrix.cons_val, actCode, Nat.cast_one, pcode_bot, pcode_const, PD.Bots.CooperateBot, cast_pBot,
    cast_pConst, Nat.cast_zero]
  rw [hopp_self k]

/-- `qGD(k)` in the swapped reading: `DimcidTV k` plays C against `pBot (pConst 1)`. -/
theorem eval_qGD_swap_iff (k : V) :
    Semiformula.Eval (s := swapActS V) ![k] Empty.elim qGD ↔
      ∃ n, EvalGraph n (DimcidTV k) (pBot (pConst 1)) (DimcidTV k) 0 := by
  unfold qGD
  rw [eval_qT_swap, lMap_swap_gG, eval_qT_iff,
    eval_tmpl_plays_opp_closed_V _ (by intro h; cases h) (by intro h; cases h)]
  simp only [Matrix.cons_val, actCode, Nat.cast_zero, pcode_bot, pcode_const, PD.Bots.DefectBot, cast_pBot,
    cast_pConst, Nat.cast_one]
  rw [hopp'_self k]

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
  rw [swapcode_pBot, swapcode_pConst_zero] at h2
  exact ⟨by rw [← stdActV_eq_stdActS, eval_qGD_iff]; exact ⟨2, h1⟩, (eval_qGD_swap_iff k).mpr ⟨2, h2⟩⟩

/-- **Guardian FINDS its guard against DIMCID for all large `k`** (the box form of cell 2, Guardian's side):
`found_of_box_conseq` on DIMCID's family against `.bot CooperateBot`. -/
theorem guardian_finds_DIMCID :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      LenProvableV TAct k (guardCode (tcode phiG) (pcode (GuardianBot k)) (pcode (DIMCID k))) :=
  found_of_box_conseq (pG (cl TB0) (cterm Act.C) (cterm Act.D)) boundedInnerNec_sixteen
    (loebSound_pG_of describes_botCB) qGD boxConseq_qGD
    (fun k ↦ guardCode (tcode phiG) (pcode (GuardianBot k)) (pcode (DIMCID k)))
    (fun k ↦ by rw [pcode_GuardianBot_SV, pcode_DIMCID]; exact guardCode_GD (V := ℕ) k)

/-- **DIMCID defects against Guardian and FINDS its guard, for all large `k`** (the self-fulfilling refutation
against the `SV`-described Guardian). -/
theorem dimcid_vs_Guardian_defects :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 2 (pcode (DIMCID k)) (pcode (GuardianBot k)) (pcode (DIMCID k)) 1 ∧
      LenProvableV TAct k (guardCode (tcode phiD) (pcode (DIMCID k)) (pcode (GuardianBot k))) := by
  obtain ⟨k₀, h⟩ := dimcid_vs_described (describes_SV gG 1 (Or.inr rfl))
  refine ⟨k₀, fun k hk ↦ ?_⟩
  have := h k hk
  rwa [descVal_SV gG 1 (Or.inr rfl), ← pcode_GuardianBot_SV, ← pcode_DIMCID] at this

/-- **GuardianBot × DIMCID is `(D, D)` in PA-`S'`**, for all large `k`, unconditional. The engine proves
`(C, C)` by an unreadability census (`llm_outcome_GuardianBot_vs_DIMCID`, pad 2); in `S'` the value is
`(D, D)` because Guardian's guard "DIMCID defects against `.bot CooperateBot`" is TRUE (DIMCID's guard
against the frozen probe is self-fulfilling) and PROVABLE within the budget (a box consequence of DIMCID's
Löb family, `guardian_finds_DIMCID`), so Guardian punishes; and DIMCID's guard against Guardian is
self-fulfilling too, so DIMCID defects. -/
theorem loeb_GuardianBot_vs_DIMCID :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 2 (pcode (GuardianBot k)) (pcode (DIMCID k)) (pcode (GuardianBot k)) (actCode .D) ∧
      EvalGraph 2 (pcode (DIMCID k)) (pcode (GuardianBot k)) (pcode (DIMCID k)) (actCode .D) := by
  obtain ⟨k₁, h₁⟩ := guardian_finds_DIMCID
  obtain ⟨k₂, h₂⟩ := dimcid_vs_Guardian_defects
  exact ⟨k₁ + k₂, fun k hk ↦ ⟨guardian_D_of_found k (h₁ k (by omega)), (h₂ k (by omega)).1⟩⟩

/-- **The box form of cell 2, DIMCID's side**: DIMCID FINDS its guard against Guardian within its budget. -/
theorem dimcid_finds_guard_vs_Guardian :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      LenProvableV TAct k (guardCode (tcode phiD) (pcode (DIMCID k)) (pcode (GuardianBot k))) := by
  obtain ⟨k₀, h⟩ := dimcid_vs_Guardian_defects
  exact ⟨k₀, fun k hk ↦ (h k hk).2⟩

end cell2

end ArithS
