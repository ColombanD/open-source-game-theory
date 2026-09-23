import ArithS.Cells.PositiveCells
import ArithS.Cells.DIMCID
import ArithS.Cells.KhatCells

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
6. **The `.neg` family** (`pQ q := q ⋏ τq`, `pQ_both_V`, `SV_search_V`) and **cells 3, 4 — WaryBot × MirrorBot
   `(D, D)`, WaryBot × WaryBot `(D, D)`** (`loeb_WaryBot_vs_MirrorBot`, `loeb_WaryBot_vs_WaryBot`; engine
   `outcome_WaryBot_vs_MirrorBot`/`outcome_WaryBot_vs_WaryBot = (C, C)` at EVERY `k`, pads 3/2): "¬(you
   cooperate with me)" against a copier is self-fulfilling — found ⇒ Wary defects ⇒ the copier defects.
7. **Cell 5 — DIMCID × CupodTrollBot `(D, C)`** (`loeb_DIMCID_vs_CupodTrollBot`; engine
   `llm_outcome_DIMCID_vs_CupodTrollBot = (C, C)`, pad 2), on the budget-slot `CupodTroll7 k` of
   `Cells/KhatCells.lean` (the same play as the engine's `CupodTrollBot k` in every frame,
   `evalGraph_CupodTroll7_iff`; an opponent's guard that DESCRIBES it needs the slot): DIMCID's guard against
   the described CupodTroll (`describes_troll7`) is self-fulfilling; CupodTroll's `.eq` guard "DIMCID is
   `CupodBot k`" is FALSE (`pcode_DIMCID_ne_CupodBot`, the templates separated semantically), so by soundness it
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

/-! ### 6. The `.neg` family `q ⋏ τq`, and cells 3, 4 — WaryBot × MirrorBot, WaryBot × WaryBot -/

section negFamily

/-- **The two-guard family of a single searcher's cell**: its guard's fixed formula `q` AND the transposed
searcher's `τq` — one box, ∧-elimination on codes, the same slack `(7, 8)` as `pConj`. -/
noncomputable def pQ (q : Semisentence LAct 1) : Semisentence LAct 1 := q ⋏ Semiformula.lMap swap q

lemma pQ_def (q : Semisentence LAct 1) : pQ q = q ⋏ Semiformula.lMap swap q := rfl

lemma lMap_swap_pQ (q : Semisentence LAct 1) :
    Semiformula.lMap swap (pQ q) = Semiformula.lMap swap q ⋏ q := by
  rw [pQ_def, LogicalConnective.HomClass.map_and, lMap_swap_swap]

theorem instB_quote_pQ (q : Semisentence LAct 1) (k : V) :
    instB (⌜pQ q⌝ : V) k = instB (⌜q⌝ : V) k ^⋏ instB (⌜Semiformula.lMap swap q⌝ : V) k :=
  instB_quote_and _ _ k

lemma formulaLen_instB_pQ (q : Semisentence LAct 1) (k : V) :
    formulaLen LAct (instB (⌜pQ q⌝ : V) k) =
      formulaLen LAct (instB (⌜q⌝ : V) k) + formulaLen LAct (instB (⌜Semiformula.lMap swap q⌝ : V) k) + 1 := by
  rw [instB_quote_pQ,
    formulaLen_and (isFormula_instB_quote _ k).isUFormula (isFormula_instB_quote _ k).isUFormula]

/-- **Both instances are provable within `k` from a box of the family with the slack** (∧-elimination on
codes, `pG_guards_V`'s shape for an arbitrary `q`). -/
theorem pQ_both_V (q : Semisentence LAct 1) (k a : V)
    (ha : a + 8 * (formulaLen LAct (instB (⌜q⌝ : V) k) + formulaLen LAct (instB (⌜Semiformula.lMap swap q⌝ : V) k))
      + 7 ≤ k)
    (h : LenDerivable TAct a (instB (⌜pQ q⌝ : V) k)) :
    LenProvableV TAct k (instB (⌜q⌝ : V) k) ∧ LenProvableV TAct k (instB (⌜Semiformula.lMap swap q⌝ : V) k) := by
  rw [instB_quote_pQ] at h
  have hx := isFormula_instB_quote q k
  have hy := isFormula_instB_quote (Semiformula.lMap swap q) k
  exact ⟨(lenDerivable_iff_lenProvableV _ _).mp (lenDerivable_mono_V ha (lenDerivable_andL_V hx hy h)),
    (lenDerivable_iff_lenProvableV _ _).mp (lenDerivable_mono_V ha (lenDerivable_andR_V hx hy h))⟩

omit [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
/-- `pQ q (k)` in the standard reading: both conjuncts. -/
theorem eval_pQ_std (q : Semisentence LAct 1) (k : V) :
    Semiformula.Eval (s := stdActS V) ![k] Empty.elim (pQ q) ↔
      Semiformula.Eval (s := stdActS V) ![k] Empty.elim q ∧
      Semiformula.Eval (s := stdActS V) ![k] Empty.elim (Semiformula.lMap swap q) := by
  rw [pQ_def]
  simp only [LogicalConnective.HomClass.map_and, LogicalConnective.Prop.and_eq]

omit [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
/-- `pQ q (k)` in the swapped reading: the conjuncts exchange roles. -/
theorem eval_pQ_swap (q : Semisentence LAct 1) (k : V) :
    Semiformula.Eval (s := swapActS V) ![k] Empty.elim (pQ q) ↔
      Semiformula.Eval (s := stdActS V) ![k] Empty.elim (Semiformula.lMap swap q) ∧
      Semiformula.Eval (s := stdActS V) ![k] Empty.elim q := by
  rw [eval_swapActS, lMap_swap_pQ]
  simp only [LogicalConnective.HomClass.map_and, LogicalConnective.Prop.and_eq]

/-- **The search clause of the generic engine searcher in every model** (fuel 2): found ⇒ the then-branch. -/
theorem SV_search_V (g : Semisentence LAct 6) (a : ℕ) (k opp : V)
    (h : LenProvableV TAct k (guardCode (⌜g⌝ : V) (SV g a k) opp)) :
    EvalGraph 2 (SV g a k) opp (SV g a k) (a : V) := by
  rw [show (2 : V) = 1 + 1 from one_add_one_eq_two.symm]
  show EvalGraph (1 + 1) (SV g a k) opp (pSearch k (⌜g⌝ : V) (pConst (a : V)) (pConst ((1 - a : ℕ) : V))) (a : V)
  rw [EvalGraph.search_iff₆ (isSemiformula_quote₆ g)]
  left
  refine ⟨h, ?_⟩
  have e : EvalGraph (0 + 1) (SV g a k) opp (pConst (a : V)) (a : V) := EvalGraph.const_iff.mpr rfl
  rwa [zero_add] at e

/-! #### Wary's fixed formulas against Mirror and against itself -/

/-- The transposed Wary triple describes the transposed searcher `SV gWT 0 k` (values). -/
lemma hme_WT (k : V) :
    relabel ((Semiterm.lMap swap (uS gW 1)).val (s := stdActV V) ![] Empty.elim)
      ((Semiterm.lMap swap (wS gW 1)).val (s := stdActV V) ![] Empty.elim)
      ((Semiterm.lMap swap (TS gW 1)).val (s := stdActV V) ![k] Empty.elim) = SV gWT 0 k := by
  have := hme_SVT gW 1 (Or.inr rfl) k
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
  rwa [swapcode_SV gW 1 (Or.inr rfl), lMap_swap_gW, swapcode_MirrorV] at this

theorem eval_qWM_iff (k : V) :
    Semiformula.Eval (s := stdActV V) ![k] Empty.elim qWM ↔ ¬ ∃ n, EvalGraph n MirrorV (SV gW 1 k) MirrorV 0 := by
  rw [qWM, eval_qT_neg_plays_opp_self .C _ _ _ _ _ _ k (hme_SV gW 1 (Or.inr rfl) k) (hopp_mirror k), actCode_C_cast]

theorem eval_qWMT_iff (k : V) :
    Semiformula.Eval (s := stdActV V) ![k] Empty.elim (Semiformula.lMap swap qWM) ↔
      ¬ ∃ n, EvalGraph n MirrorV (SV gWT 0 k) MirrorV 1 := by
  rw [qWM_swap, eval_qT_neg_plays_opp_self .D _ _ _ _ _ _ k (hme_WT k) (hopp_mirror k), actCode_D_cast]

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
  rwa [swapcode_SV gW 1 (Or.inr rfl), lMap_swap_gW] at this

theorem eval_qWW_iff (k : V) :
    Semiformula.Eval (s := stdActV V) ![k] Empty.elim qWW ↔
      ¬ ∃ n, EvalGraph n (SV gW 1 k) (SV gW 1 k) (SV gW 1 k) 0 := by
  rw [qWW, eval_qT_neg_plays_opp_self .C _ _ _ _ _ _ k (hme_SV gW 1 (Or.inr rfl) k) (hme_SV gW 1 (Or.inr rfl) k),
    actCode_C_cast]

theorem eval_qWWT_iff (k : V) :
    Semiformula.Eval (s := stdActV V) ![k] Empty.elim (Semiformula.lMap swap qWW) ↔
      ¬ ∃ n, EvalGraph n (SV gWT 0 k) (SV gWT 0 k) (SV gWT 0 k) 1 := by
  rw [qWW_swap, eval_qT_neg_plays_opp_self .D _ _ _ _ _ _ k (hme_WT k) (hme_WT k), actCode_D_cast]

/-! #### The Löb premises: the `.neg` guard is self-fulfilling against a copier -/

/-- **Wary's Löb premise against Mirror, slack `(7, 8)`**: a box of the family makes Wary FIND its guard, so
Wary defects (fuel 2), so Mirror copies the defection (fuel 3), so "Mirror plays C against Wary" is FALSE by
determinism — the guard "¬(Mirror plays C against me)" is TRUE; the transposed searcher cooperates and Mirror
copies that, so "¬(Mirror plays D against me)" is true too. Both readings. -/
theorem loebSound_pWM : LoebSound (pQ qWM) 7 8 := by
  intro V _ _ k a ha hp
  have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
  have ha' : a + 8 * (formulaLen LAct (instB (⌜qWM⌝ : V) k) +
      formulaLen LAct (instB (⌜Semiformula.lMap swap qWM⌝ : V) k)) + 7 ≤ k :=
    le_trans (pConj_slack_le a _ _ _ (formulaLen_instB_pQ qWM k)) ha
  obtain ⟨h1, h2⟩ := pQ_both_V qWM k a ha' hp
  rw [← guardCode_WM] at h1
  rw [← guardCode_WMT] at h2
  have e1 := mirror_copies_V _ _ (SV_search_V gW 1 k MirrorV h1)
  have e2 := mirror_copies_V _ _ (SV_search_V gWT 0 k MirrorV h2)
  rw [Nat.cast_one] at e1
  rw [Nat.cast_zero] at e2
  have hA : ¬ ∃ n, EvalGraph n MirrorV (SV gW 1 k) MirrorV 0 := by
    rintro ⟨n, hn⟩
    exact _root_.zero_ne_one (EvalGraph.unique_V' n 3 _ _ _ _ _ hn e1)
  have hB : ¬ ∃ n, EvalGraph n MirrorV (SV gWT 0 k) MirrorV 1 := by
    rintro ⟨n, hn⟩
    exact _root_.one_ne_zero (EvalGraph.unique_V' n 3 _ _ _ _ _ hn e2)
  refine ⟨?_, ?_⟩
  · rw [eval_pQ_std, ← stdActV_eq_stdActS, eval_qWM_iff, eval_qWMT_iff]
    exact ⟨hA, hB⟩
  · rw [eval_pQ_swap, ← stdActV_eq_stdActS, eval_qWMT_iff, eval_qWM_iff]
    exact ⟨hB, hA⟩

/-- **Wary's Löb premise against itself, slack `(7, 8)`**: found ⇒ Wary defects against Wary ⇒ "Wary plays C
against Wary" is FALSE ⇒ the guard is true; the transposed searcher likewise. -/
theorem loebSound_pWW : LoebSound (pQ qWW) 7 8 := by
  intro V _ _ k a ha hp
  have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
  have ha' : a + 8 * (formulaLen LAct (instB (⌜qWW⌝ : V) k) +
      formulaLen LAct (instB (⌜Semiformula.lMap swap qWW⌝ : V) k)) + 7 ≤ k :=
    le_trans (pConj_slack_le a _ _ _ (formulaLen_instB_pQ qWW k)) ha
  obtain ⟨h1, h2⟩ := pQ_both_V qWW k a ha' hp
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
  refine ⟨?_, ?_⟩
  · rw [eval_pQ_std, ← stdActV_eq_stdActS, eval_qWW_iff, eval_qWWT_iff]
    exact ⟨hA, hB⟩
  · rw [eval_pQ_swap, ← stdActV_eq_stdActS, eval_qWWT_iff, eval_qWW_iff]
    exact ⟨hB, hA⟩

/-! #### Cells 3 and 4 -/

/-- **Wary defects against Mirror and FINDS its `.neg` guard, for all large `k`**, unconditional. -/
theorem wary_vs_mirror_core :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 2 (pcode (WaryBot k)) (pcode MirrorBot) (pcode (WaryBot k)) 1 ∧
      LenProvableV TAct k (guardCode (tcode phiW) (pcode (WaryBot k)) (pcode MirrorBot)) := by
  obtain ⟨k₀, hf⟩ := family_found (pQ qWM) boundedInnerNec_sixteen loebSound_pWM
  refine ⟨k₀, fun k hk ↦ ?_⟩
  obtain ⟨a, ha, hpc⟩ := hf k hk
  have ha' := le_def.mpr (pConj_slack_nat a _ _ _ k (formulaLen_instB_pQ (V := ℕ) qWM k) ha)
  have h1 := (pQ_both_V (V := ℕ) qWM k a ha' hpc).1
  rw [← guardCode_WM] at h1
  rw [pcode_WaryBot_SV, pcode_MirrorBot, ← MirrorV_nat]
  exact ⟨SV_search_V (V := ℕ) gW 1 k MirrorV h1, h1⟩

/-- **WaryBot × MirrorBot is `(D, D)` in PA-`S'`**, for all large `k`, unconditional. The engine proves `(C, C)`
at EVERY `k` by a `.neg`-guard valuation census (`outcome_WaryBot_vs_MirrorBot`, pad 3); in `S'` the value is
`(D, D)` because Wary's guard "¬(Mirror plays C against me)" is SELF-FULFILLING against a copier (its proof
makes Wary defect, Mirror copies, so Mirror indeed does not cooperate) and bounded Löb finds it. -/
theorem loeb_WaryBot_vs_MirrorBot :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 3 (pcode (WaryBot k)) (pcode MirrorBot) (pcode (WaryBot k)) (actCode .D) ∧
      EvalGraph 3 (pcode MirrorBot) (pcode (WaryBot k)) (pcode MirrorBot) (actCode .D) := by
  obtain ⟨k₀, h⟩ := wary_vs_mirror_core
  exact ⟨k₀, fun k hk ↦ ⟨EvalGraph.mono_le (by omega) (h k hk).1, mirror_copies (h k hk).1⟩⟩

/-- **The box form of cell 3**: Wary FINDS its `.neg` guard against Mirror within its budget. -/
theorem wary_finds_guard_vs_Mirror :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      LenProvableV TAct k (guardCode (tcode phiW) (pcode (WaryBot k)) (pcode MirrorBot)) := by
  obtain ⟨k₀, h⟩ := wary_vs_mirror_core
  exact ⟨k₀, fun k hk ↦ (h k hk).2⟩

/-- **Wary defects against itself and FINDS its `.neg` guard, for all large `k`**, unconditional. -/
theorem wary_vs_wary_core :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 2 (pcode (WaryBot k)) (pcode (WaryBot k)) (pcode (WaryBot k)) 1 ∧
      LenProvableV TAct k (guardCode (tcode phiW) (pcode (WaryBot k)) (pcode (WaryBot k))) := by
  obtain ⟨k₀, hf⟩ := family_found (pQ qWW) boundedInnerNec_sixteen loebSound_pWW
  refine ⟨k₀, fun k hk ↦ ?_⟩
  obtain ⟨a, ha, hpc⟩ := hf k hk
  have ha' := le_def.mpr (pConj_slack_nat a _ _ _ k (formulaLen_instB_pQ (V := ℕ) qWW k) ha)
  have h1 := (pQ_both_V (V := ℕ) qWW k a ha' hpc).1
  rw [← guardCode_WW] at h1
  rw [pcode_WaryBot_SV]
  exact ⟨SV_search_V (V := ℕ) gW 1 k (SV gW 1 k) h1, h1⟩

/-- **WaryBot × WaryBot is `(D, D)` in PA-`S'`**, for all large `k`, unconditional. The engine proves `(C, C)`
at EVERY `k` by a `.neg`-guard valuation census (`outcome_WaryBot_vs_WaryBot`, pad 2); in `S'` the value is
`(D, D)` because Wary's guard "¬(Wary plays C against me)" is SELF-FULFILLING in self-play (its proof makes
Wary defect against itself) and bounded Löb finds it. -/
theorem loeb_WaryBot_vs_WaryBot :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 2 (pcode (WaryBot k)) (pcode (WaryBot k)) (pcode (WaryBot k)) (actCode .D) ∧
      EvalGraph 2 (pcode (WaryBot k)) (pcode (WaryBot k)) (pcode (WaryBot k)) (actCode .D) := by
  obtain ⟨k₀, h⟩ := wary_vs_wary_core
  exact ⟨k₀, fun k hk ↦ ⟨(h k hk).1, (h k hk).1⟩⟩

/-- **The box form of cell 4**: Wary FINDS its `.neg` guard against itself within its budget. -/
theorem wary_finds_guard_vs_self :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      LenProvableV TAct k (guardCode (tcode phiW) (pcode (WaryBot k)) (pcode (WaryBot k))) := by
  obtain ⟨k₀, h⟩ := wary_vs_wary_core
  exact ⟨k₀, fun k hk ↦ (h k hk).2⟩

end negFamily

/-! ### 7. Cell 5 — DIMCID × CupodTrollBot `(D, C)`, on the budget-slot `CupodTroll7` -/

section cell5

lemma proper_DIMCID (k : ℕ) : Proper (DIMCID k) := ⟨by simp [DIMCID], by simp [DIMCID]⟩

/-- DIMCID's and Cupod's templates differ: at the frame `(DefectBot, CooperateBot)`, "I play C against
CooperateBot ⇒ CooperateBot plays D against me" is true (a false antecedent) while "CooperateBot plays D
against DefectBot" is false. -/
lemma tcode_phiD_ne_phiCu : tcode phiD ≠ tcode phiCu := by
  refine tcode_ne_of_models DefectBot CooperateBot ?_ ?_
  · rw [← trAt_subst DefectBot CooperateBot sfp_DefectBot.1 sfp_CooperateBot.1 _ rfl]
    show ℕ↓[LAct] ⊧ trAt DefectBot CooperateBot
      (.impl (.plays DefectBot CooperateBot .C) (.plays CooperateBot DefectBot .D))
    rw [models_trAt_impl, models_trAt_plays _ _ _ _ _ sfp_DefectBot.1 sfp_CooperateBot.1]
    rintro ⟨N, hN⟩
    rw [pcode_DB] at hN
    exact absurd (EvalGraph.unique' hN (const_play 0 _ _ 1)) (by decide)
  · rw [← trAt_subst DefectBot CooperateBot sfp_DefectBot.1 sfp_CooperateBot.1 _ rfl]
    show ¬ ℕ↓[LAct] ⊧ trAt DefectBot CooperateBot (.plays CooperateBot DefectBot .D)
    rw [models_trAt_plays _ _ _ _ _ sfp_CooperateBot.1 sfp_DefectBot.1]
    rintro ⟨N, hN⟩
    rw [pcode_CB] at hN
    exact absurd (EvalGraph.unique' hN (const_play 0 _ _ 0)) (by decide)

lemma pcode_DIMCID_ne_CupodBot (k : ℕ) : pcode (DIMCID k) ≠ pcode (CupodBot k) := by
  rw [pcode_DIMCID', pcode_CupodBot]
  intro e
  exact tcode_phiD_ne_phiCu (pSearch_inj e).2.1

/-- **CupodTroll's `.eq` guard against DIMCID is FALSE, hence never found (soundness): `CupodTroll7 k`
cooperates with `DIMCID k` at EVERY `k`** (the SND mechanism on the budget-slot code). -/
theorem troll7_vs_DIMCID (k : ℕ) : EvalGraph 2 (CupodTroll7 k) (pcode (DIMCID k)) (CupodTroll7 k) 0 := by
  have hn := not_found_eq_opp (proper_CupodTrollBot k) (proper_DIMCID k) (Q := CupodBot k) rfl
    (pcode_DIMCID_ne_CupodBot k) k
  rw [← guardCode_eqTmpl_eq_tcode (CupodBot k) (pcode (CupodTrollBot k)) (pcode (DIMCID k)), pcode_CupodBot_SV] at hn
  exact troll7_else_V k _ _ hn

/-- CupodTroll's half on the ENGINE's own code, at every `k` (its guard does not read the frame's `me`). -/
theorem snd_CupodTrollBot_vs_DIMCID_engine (k : ℕ) :
    EvalGraph 2 (pcode (CupodTrollBot k)) (pcode (DIMCID k)) (pcode (CupodTrollBot k)) (actCode .C) :=
  ctb_C_of_ne k (proper_DIMCID k) (pcode_DIMCID_ne_CupodBot k)

lemma descVal_troll7 (k : V) : descVal TT uT wT k = CupodTrollV7 k := hopp_troll7 k

lemma descVal_troll7_T (k : V) :
    descVal (Semiterm.lMap swap TT) (Semiterm.lMap swap uT) (Semiterm.lMap swap wT) k = CupodTrollTV7 k :=
  hopp'_troll7 k

/-- The canonical triple of the budget-slot CupodTroll describes it in every model (`KhatCells` §7). -/
theorem describes_troll7 : Describes TT uT wT where
  hX := by intro V _ _ k; rw [descVal_troll7]; exact hX_troll7 k
  hU := by intro V _ _ k; rw [descVal_troll7]; exact hU_troll7 k
  hW := by intro V _ _ k; rw [descVal_troll7]; exact hW_troll7 k
  hT := by intro V _ _ k; rw [descVal_troll7_T, descVal_troll7, swapcode_CupodTrollV7]

/-- **DIMCID defects against `CupodTroll7 k` and FINDS its guard, for all large `k`** (the self-fulfilling
refutation against the described CupodTroll). -/
theorem dimcid_vs_troll7_defects :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 2 (pcode (DIMCID k)) (CupodTroll7 k) (pcode (DIMCID k)) 1 ∧
      LenProvableV TAct k (guardCode (tcode phiD) (pcode (DIMCID k)) (CupodTroll7 k)) := by
  obtain ⟨k₀, h⟩ := dimcid_vs_described describes_troll7
  refine ⟨k₀, fun k hk ↦ ?_⟩
  have := h k hk
  rwa [descVal_troll7, CupodTrollV7_nat, ← pcode_DIMCID] at this

/-- **DIMCID × CupodTrollBot is `(D, C)` in PA-`S'`**, for all large `k`, unconditional, on the budget-slot
`CupodTroll7 k` (which plays as the engine's `CupodTrollBot k` in every frame, `evalGraph_CupodTroll7_iff`).
The engine proves `(C, C)` by an unreadability census (`llm_outcome_DIMCID_vs_CupodTrollBot`, pad 2); in `S'`
the value is `(D, C)` because DIMCID's guard "I play C against CupodTroll ⇒ CupodTroll plays D against me" is
SELF-FULFILLING (its proof makes DIMCID defect, which falsifies the antecedent — the consequent, false here,
never enters) and bounded Löb finds it, so DIMCID defects; while CupodTroll's `.eq` guard "DIMCID is
`CupodBot k`" is false, so by soundness it is never found and CupodTroll cooperates. -/
theorem loeb_DIMCID_vs_CupodTrollBot :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 2 (pcode (DIMCID k)) (CupodTroll7 k) (pcode (DIMCID k)) (actCode .D) ∧
      EvalGraph 2 (CupodTroll7 k) (pcode (DIMCID k)) (CupodTroll7 k) (actCode .C) := by
  obtain ⟨k₀, h⟩ := dimcid_vs_troll7_defects
  exact ⟨k₀, fun k hk ↦ ⟨(h k hk).1, troll7_vs_DIMCID k⟩⟩

/-- **The box form of cell 5**: DIMCID FINDS its guard against `CupodTroll7 k` within its budget. -/
theorem dimcid_finds_guard_vs_troll7 :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      LenProvableV TAct k (guardCode (tcode phiD) (pcode (DIMCID k)) (CupodTroll7 k)) := by
  obtain ⟨k₀, h⟩ := dimcid_vs_troll7_defects
  exact ⟨k₀, fun k hk ↦ (h k hk).2⟩

end cell5

end ArithS
