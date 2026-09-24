import ArithS.Cells.Common.Syntax
import ArithS.Assembly.Prep
import ArithS.SimTest
import PrisonersDilemma.Bots.TitForTatBot

/-!
# ArithS.Cells.Common.Bots — the bot codes and description towers shared by the cell files

Consolidation stage 2 (`Research/Notes/ROUTE_B_CELLS_MAP.md`, 2026-09-24). Everything here was MOVED
unchanged (names, statements, definition bodies) out of `Cells/DupocMirror`, `Cells/KhatCells`,
`Cells/PositiveCells` and `Cells/FlipCells`:

1. **Mirror in every model** (`MirrorV`, `cast_Mirror`, `swapcode/dnum/dU/dW_MirrorV`) and its closed
   description term `TM` (`val_TM_V`, `quote_emb_TM`). The sim step and the copy lemmas stay with the
   probers (`Cells/DupocMirror` until stage 4).
2. **TitForTatBot in every model**: the `Tft` block (`TftV`/`TftTV`, `TTft`, the canonical-code facts,
   the description hypotheses `hX/hU/hW_tft`, the values `val_desc_tft(_swap)`) and, right after it,
   `Cells/FlipCells`' EXACT DUPLICATES `TFTV`/`TFTTV`/`TTFT` — kept as definitions with their original
   bodies (the gate: no definition body changes), with the bridges `TFTV_eq_TftV`/`TFTTV_eq_TftTV`/
   `TTFT_eq_TTft` (all `rfl`) and their lemmas now one-liners over the `Tft` ones.
3. **The constant opponents** `pConst 0/1`, `pBot (pConst 0/1)`: the closed terms `T0`/`TB0`, the
   description hypotheses and values.
4. **The generic engine searcher** `SV g a k := pSearch k ⌜g⌝ (pConst a) (pConst (1 - a))` with its
   `variable (g) (a)` block kept verbatim (binder names and order — the `rfl`-bridges downstream depend
   on it): `innerS`, `swapcode_SV`, the canonical triple `gS/pS/qS/uS/wS`, `dnum/dU/dW_SV`, the tower
   `TS`, `hX/hU/hW_SV`, the value reconstructions; then `hme_SV`/`hme_SVT`.
5. **The explicit engine templates** `gDu/gCu/gW/gWT` and the bot-wrapped searcher's tower `TBS`
   (`termSubst_TBS`, `hU/hW_botSV`, `hme_botSV`/`hme_botSVT`). The engine-code bridges
   `pcode_DupocBot_SV`/`pcode_CupodBot_SV`/`pcode_WaryBot_SV` stay in `Cells/PositiveCells` (they need
   the ℕ-branch's `pcode_*` lemmas). The bridges `DimcidV_eq_SV`/`CimcicV_eq_SV` live next to
   `DimcidV`/`CimcicV` (`Cells/DIMCID`, `Cells/CIMCIC`); `DupocV`/`CupodV` are NOT `SV` instances
   (hand template `GtmplA a` vs `tmpl (.plays .opp .self _)`, `Code.lean`) — never merge them.
-/

set_option linter.constructorNameAsVariable false

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open LAct
open PD.Bots

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ### 1. Mirror in every model, and its closed description term -/

section mirror

/-- `Mirror` in an arbitrary model (`SimTest.Mirror` is `MirrorV` at `V = ℕ`). -/
noncomputable def MirrorV : V := pSim pOpp pSelf

lemma MirrorV_nat : MirrorV (V := ℕ) = Mirror := rfl

lemma cast_Mirror : ((Mirror : ℕ) : V) = MirrorV := by
  unfold Mirror MirrorV
  rw [cast_pSim, cast_pOpp, cast_pSelf]

theorem swapcode_MirrorV : swapcode (MirrorV : V) = MirrorV := by
  unfold MirrorV swapcode; simp

lemma dnum_MirrorV : dnum (MirrorV : V) = MirrorV := dnum_of_eq swapcode_MirrorV.symm

lemma dU_MirrorV : dU (MirrorV : V) = numeral 0 := by
  unfold dU
  rw [swapcode_MirrorV, if_neg (_root_.lt_irrefl _), if_neg (_root_.lt_irrefl _)]

lemma dW_MirrorV : dW (MirrorV : V) = numeral 1 := by
  unfold dW
  rw [swapcode_MirrorV, if_neg (_root_.lt_irrefl _), if_neg (_root_.lt_irrefl _)]


/-- **Mirror's closed description term** (over `LAct`): the structural term of its code. -/
noncomputable def TM : ClosedSemiterm LAct 0 := Semiterm.lMap emb (progTT Mirror)

lemma lMap_swap_TM : Semiterm.lMap swap TM = TM := term_lMap_swap_emb _

/-- `TM` denotes `MirrorV` in every model. -/
theorem val_TM_V : TM.val (s := stdActV V) ![] Empty.elim = MirrorV := by
  unfold TM
  rw [Semiterm.val_lMap, stdActV_lMap_emb, val_progTT_V, cast_Mirror]

/-- The code of `TM` is the structural term code of `MirrorV`. -/
theorem quote_emb_TM : (⌜(Rew.emb TM : SyntacticSemiterm LAct 0)⌝ : V) = progT MirrorV := by
  unfold TM
  rw [term_emb_lMap_emb, quote_term_lMap_emb, ← Semiterm.empty_quote_def, quote_progTT, cast_Mirror]

end mirror

/-! ### 2. TitForTatBot in every model -/

section tft

/-- **TitForTatBot's code, in every model**: `ite (sim opp (bot CooperateBot)) C (const C) (const D)`. -/
noncomputable def TftV : V := pIte (pSim pOpp (pBot (pConst 0))) 0 (pConst 0) (pConst 1)

/-- The transposed TitForTatBot: `ite (sim opp (bot DefectBot)) D (const D) (const C)`. -/
noncomputable def TftTV : V := pIte (pSim pOpp (pBot (pConst 1))) 1 (pConst 1) (pConst 0)

lemma pcode_TFT : pcode TitForTatBot = pIte (pSim pOpp (pBot (pConst 0))) 0 (pConst 0) (pConst 1) := by
  simp [TitForTatBot, CooperateBot, actCode]

lemma TftV_nat : TftV (V := ℕ) = pcode TitForTatBot := by rw [pcode_TFT]; rfl

lemma cast_Tft : ((pcode TitForTatBot : ℕ) : V) = TftV := by
  rw [pcode_TFT, cast_pIte, cast_pSim, cast_pOpp, cast_pBot, cast_pConst, cast_pConst]
  simp [TftV]

theorem swapcode_TftV : swapcode (TftV : V) = TftTV := by
  unfold TftV TftTV swapcode
  simp [relabelAct]

theorem swapcode_TftTV : swapcode (TftTV : V) = TftV := by
  rw [← swapcode_TftV, swapcode_swapcode]

/-- TFT is CANONICAL: its code is below its transposition's (the probe's constant decides). -/
theorem TftV_lt_TftTV : (TftV : V) < TftTV := by
  unfold TftV TftTV pIte pSim pBot pConst pOpp ppair
  norm_num

lemma dnum_TftV : dnum (TftV : V) = TftV :=
  dnum_of_lt (by rw [swapcode_TftV]; exact TftV_lt_TftTV)

lemma dU_TftV : dU (TftV : V) = csym 0 := by
  unfold dU; rw [swapcode_TftV, if_pos TftV_lt_TftTV]

lemma dW_TftV : dW (TftV : V) = csym 1 := by
  unfold dW; rw [swapcode_TftV, if_pos TftV_lt_TftTV]

/-- TFT's closed description term: the structural term of its code. -/
noncomputable def TTft : ClosedSemiterm LAct 0 := Semiterm.lMap emb (progTT (pcode TitForTatBot))

lemma lMap_swap_TTft : Semiterm.lMap swap TTft = TTft := term_lMap_swap_emb _

theorem val_TTft_V : TTft.val (s := stdActV V) ![] Empty.elim = TftV := by
  unfold TTft
  rw [Semiterm.val_lMap, stdActV_lMap_emb, val_progTT_V, cast_Tft]

theorem quote_emb_TTft : (⌜(Rew.emb TTft : SyntacticSemiterm LAct 0)⌝ : V) = progT TftV := by
  unfold TTft
  rw [term_emb_lMap_emb, quote_term_lMap_emb, ← Semiterm.empty_quote_def, quote_progTT, cast_Tft]

/-- The description hypotheses of the triple `(cl TTft, cterm C, cterm D)`. -/
lemma hX_tft (k : V) :
    termSubst LAct (bnum k ∷ (0 : V)) (⌜(Rew.emb (cl TTft : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝ : V) =
      progT (dnum TftV) := by
  rw [quote_emb_cl_V, termSubst_closed _ (semiterm_quote_emb₀ _), quote_emb_TTft, dnum_TftV]
lemma hU_tft : (⌜(cterm Act.C : ClosedSemiterm LAct 0)⌝ : V) = dU TftV := by rw [quote_cterm_C, dU_TftV]
lemma hW_tft : (⌜(cterm Act.D : ClosedSemiterm LAct 0)⌝ : V) = dW TftV := by rw [quote_cterm_D, dW_TftV]

/-- The values: the triple reconstructs TFT; the swapped triple its transposition. -/
lemma val_desc_tft (k : V) :
    relabel ((cterm Act.C : ClosedSemiterm LAct 0).val (s := stdActV V) ![] Empty.elim)
      ((cterm Act.D : ClosedSemiterm LAct 0).val (s := stdActV V) ![] Empty.elim)
      ((cl TTft : Semiterm LAct Empty 1).val (s := stdActV V) ![k] Empty.elim) = TftV := by
  rw [val_cl_V, val_TTft_V, val_cterm_C_V, val_cterm_D_V, relabel_zero_one]
lemma val_desc_tft_swap (k : V) :
    relabel ((cterm Act.D : ClosedSemiterm LAct 0).val (s := stdActV V) ![] Empty.elim)
      ((cterm Act.C : ClosedSemiterm LAct 0).val (s := stdActV V) ![] Empty.elim)
      ((cl TTft : Semiterm LAct Empty 1).val (s := stdActV V) ![k] Empty.elim) = TftTV := by
  rw [val_cl_V, val_TTft_V, val_cterm_C_V, val_cterm_D_V]
  exact swapcode_TftV

/-! #### `Cells/FlipCells`' twins of the block above (same definitions; the lemmas are one-liners) -/

/-- TitForTatBot in every model: "if `opp` plays C against `.bot CooperateBot` then C else D". -/
noncomputable def TFTV : V := pIte (pSim pOpp (pBot (pConst 0))) 0 (pConst 0) (pConst 1)
/-- Its transposition: "if `opp` plays D against `.bot DefectBot` then D else C". -/
noncomputable def TFTTV : V := pIte (pSim pOpp (pBot (pConst 1))) 1 (pConst 1) (pConst 0)

/-- `TFTV` and `TftV` are the same term. -/
lemma TFTV_eq_TftV : (TFTV : V) = TftV := rfl
lemma TFTTV_eq_TftTV : (TFTTV : V) = TftTV := rfl

lemma cast_TFT : ((pcode TitForTatBot : ℕ) : V) = TFTV := by
  rw [TFTV_eq_TftV]; exact cast_Tft

lemma TFTV_nat : TFTV (V := ℕ) = pcode TitForTatBot := by
  rw [TFTV_eq_TftV]; exact TftV_nat

theorem swapcode_TFTV : swapcode (TFTV : V) = TFTTV := by
  rw [TFTV_eq_TftV, TFTTV_eq_TftTV]; exact swapcode_TftV

/-- The code of TFT is below the code of its transposition (the probe `.bot CooperateBot` is the smaller). -/
theorem TFTV_lt_TFTTV : (TFTV : V) < TFTTV := by
  rw [TFTV_eq_TftV, TFTTV_eq_TftTV]; exact TftV_lt_TftTV

lemma dnum_TFTV : dnum (TFTV : V) = TFTV := by
  rw [TFTV_eq_TftV]; exact dnum_TftV

lemma dU_TFTV : dU (TFTV : V) = csym 0 := by
  rw [TFTV_eq_TftV]; exact dU_TftV

lemma dW_TFTV : dW (TFTV : V) = csym 1 := by
  rw [TFTV_eq_TftV]; exact dW_TftV

/-- The closed structural term of TitForTatBot's code. -/
noncomputable def TTFT : ClosedSemiterm LAct 0 := Semiterm.lMap emb (progTT (pcode TitForTatBot))

lemma TTFT_eq_TTft : TTFT = TTft := rfl

lemma lMap_swap_TTFT : Semiterm.lMap swap TTFT = TTFT := term_lMap_swap_emb _

theorem val_TTFT_V : TTFT.val (s := stdActV V) ![] Empty.elim = TFTV := by
  rw [TTFT_eq_TTft, TFTV_eq_TftV]; exact val_TTft_V

theorem quote_emb_TTFT : (⌜(Rew.emb TTFT : SyntacticSemiterm LAct 0)⌝ : V) = progT TFTV := by
  rw [TTFT_eq_TTft, TFTV_eq_TftV]; exact quote_emb_TTft

end tft

/-! ### 3. The constant opponents: `pConst 0`, `pConst 1`, `pBot (pConst 0)`, `pBot (pConst 1)` -/

section constants

/-- The closed structural term of the code `pConst 0` (the canonical code of both constants). -/
noncomputable def T0 : ClosedSemiterm LAct 0 := Semiterm.lMap emb (progTT (pConst 0))

lemma lMap_swap_T0 : Semiterm.lMap swap T0 = T0 := term_lMap_swap_emb _

theorem val_T0_V : T0.val (s := stdActV V) ![] Empty.elim = pConst 0 := by
  unfold T0
  rw [Semiterm.val_lMap, stdActV_lMap_emb, val_progTT_V, cast_pConst, Nat.cast_zero]

theorem quote_emb_T0 : (⌜(Rew.emb T0 : SyntacticSemiterm LAct 0)⌝ : V) = progT (pConst 0) := by
  unfold T0
  rw [term_emb_lMap_emb, quote_term_lMap_emb, ← Semiterm.empty_quote_def, quote_progTT, cast_pConst, Nat.cast_zero]

/-- The closed structural term of the code `pBot (pConst 0)`. -/
noncomputable def TB0 : ClosedSemiterm LAct 0 := Semiterm.lMap emb (progTT (pBot (pConst 0)))

lemma lMap_swap_TB0 : Semiterm.lMap swap TB0 = TB0 := term_lMap_swap_emb _

theorem val_TB0_V : TB0.val (s := stdActV V) ![] Empty.elim = pBot (pConst 0) := by
  unfold TB0
  rw [Semiterm.val_lMap, stdActV_lMap_emb, val_progTT_V, cast_pBot, cast_pConst, Nat.cast_zero]

theorem quote_emb_TB0 : (⌜(Rew.emb TB0 : SyntacticSemiterm LAct 0)⌝ : V) = progT (pBot (pConst 0)) := by
  unfold TB0
  rw [term_emb_lMap_emb, quote_term_lMap_emb, ← Semiterm.empty_quote_def, quote_progTT, cast_pBot, cast_pConst,
    Nat.cast_zero]

/-- The `X'`-hypothesis of `guardCode_qT_eq_instB` for the four constant opponents. -/
lemma hX_const_zero (k : V) :
    termSubst LAct (bnum k ∷ (0 : V)) (⌜(Rew.emb (cl T0 : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝ : V) =
      progT (dnum (pConst 0)) := by
  rw [quote_emb_cl_V, termSubst_closed _ (semiterm_quote_emb₀ _), quote_emb_T0, dnum_pConst_zero]
lemma hX_const_one (k : V) :
    termSubst LAct (bnum k ∷ (0 : V)) (⌜(Rew.emb (cl T0 : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝ : V) =
      progT (dnum (pConst 1)) := by
  rw [quote_emb_cl_V, termSubst_closed _ (semiterm_quote_emb₀ _), quote_emb_T0, dnum_pConst_one]
lemma hX_bot_zero (k : V) :
    termSubst LAct (bnum k ∷ (0 : V)) (⌜(Rew.emb (cl TB0 : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝ : V) =
      progT (dnum (pBot (pConst 0))) := by
  rw [quote_emb_cl_V, termSubst_closed _ (semiterm_quote_emb₀ _), quote_emb_TB0, dnum_pBot, dnum_pConst_zero]
lemma hX_bot_one (k : V) :
    termSubst LAct (bnum k ∷ (0 : V)) (⌜(Rew.emb (cl TB0 : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝ : V) =
      progT (dnum (pBot (pConst 1))) := by
  rw [quote_emb_cl_V, termSubst_closed _ (semiterm_quote_emb₀ _), quote_emb_TB0, dnum_pBot, dnum_pConst_one]

lemma hU_C_zero : (⌜(cterm Act.C : ClosedSemiterm LAct 0)⌝ : V) = dU (pConst 0) := by
  rw [quote_cterm_C, dU_pConst_zero]
lemma hW_D_zero : (⌜(cterm Act.D : ClosedSemiterm LAct 0)⌝ : V) = dW (pConst 0) := by
  rw [quote_cterm_D, dW_pConst_zero]
lemma hU_D_one : (⌜(cterm Act.D : ClosedSemiterm LAct 0)⌝ : V) = dU (pConst 1) := by
  rw [quote_cterm_D, dU_pConst_one]
lemma hW_C_one : (⌜(cterm Act.C : ClosedSemiterm LAct 0)⌝ : V) = dW (pConst 1) := by
  rw [quote_cterm_C, dW_pConst_one]
lemma hU_C_bot_zero : (⌜(cterm Act.C : ClosedSemiterm LAct 0)⌝ : V) = dU (pBot (pConst 0)) := by
  rw [quote_cterm_C, dU_pBot, dU_pConst_zero]
lemma hW_D_bot_zero : (⌜(cterm Act.D : ClosedSemiterm LAct 0)⌝ : V) = dW (pBot (pConst 0)) := by
  rw [quote_cterm_D, dW_pBot, dW_pConst_zero]
lemma hU_D_bot_one : (⌜(cterm Act.D : ClosedSemiterm LAct 0)⌝ : V) = dU (pBot (pConst 1)) := by
  rw [quote_cterm_D, dU_pBot, dU_pConst_one]
lemma hW_C_bot_one : (⌜(cterm Act.C : ClosedSemiterm LAct 0)⌝ : V) = dW (pBot (pConst 1)) := by
  rw [quote_cterm_C, dW_pBot, dW_pConst_one]

/-- The values: the four constant triples reconstruct their programs. -/
lemma val_desc_const_zero (k : V) :
    relabel ((cterm Act.C : ClosedSemiterm LAct 0).val (s := stdActV V) ![] Empty.elim)
      ((cterm Act.D : ClosedSemiterm LAct 0).val (s := stdActV V) ![] Empty.elim)
      ((cl T0 : Semiterm LAct Empty 1).val (s := stdActV V) ![k] Empty.elim) = pConst 0 := by
  rw [val_cl_V, val_T0_V, val_cterm_C_V, val_cterm_D_V, relabel_zero_one]
lemma val_desc_const_one (k : V) :
    relabel ((cterm Act.D : ClosedSemiterm LAct 0).val (s := stdActV V) ![] Empty.elim)
      ((cterm Act.C : ClosedSemiterm LAct 0).val (s := stdActV V) ![] Empty.elim)
      ((cl T0 : Semiterm LAct Empty 1).val (s := stdActV V) ![k] Empty.elim) = pConst 1 := by
  rw [val_cl_V, val_T0_V, val_cterm_C_V, val_cterm_D_V, relabel_const]; simp [relabelAct]
lemma val_desc_bot_zero (k : V) :
    relabel ((cterm Act.C : ClosedSemiterm LAct 0).val (s := stdActV V) ![] Empty.elim)
      ((cterm Act.D : ClosedSemiterm LAct 0).val (s := stdActV V) ![] Empty.elim)
      ((cl TB0 : Semiterm LAct Empty 1).val (s := stdActV V) ![k] Empty.elim) = pBot (pConst 0) := by
  rw [val_cl_V, val_TB0_V, val_cterm_C_V, val_cterm_D_V, relabel_zero_one]
lemma val_desc_bot_one (k : V) :
    relabel ((cterm Act.D : ClosedSemiterm LAct 0).val (s := stdActV V) ![] Empty.elim)
      ((cterm Act.C : ClosedSemiterm LAct 0).val (s := stdActV V) ![] Empty.elim)
      ((cl TB0 : Semiterm LAct Empty 1).val (s := stdActV V) ![k] Empty.elim) = pBot (pConst 1) := by
  rw [val_cl_V, val_TB0_V, val_cterm_C_V, val_cterm_D_V, relabel_bot, relabel_const]; simp [relabelAct]

end constants

/-! ### 4. The generic engine searcher `pSearch k ⌜g⌝ (pConst a) (pConst (1 - a))` and its description -/

section searcher

variable (g : Semisentence LAct 6) (a : ℕ)

/-- The searcher on the stored template `g` with then-branch `a ∈ {0, 1}`, in every model. -/
noncomputable def SV (k : V) : V := pSearch k (⌜g⌝ : V) (pConst (a : V)) (pConst ((1 - a : ℕ) : V))

lemma SV_nat (k : ℕ) : SV (V := ℕ) g a k = pSearch k (⌜g⌝ : ℕ) (pConst a) (pConst (1 - a)) := by
  simp [SV]

/-- The budget-independent inner part of the searcher's code. -/
noncomputable def innerS : ℕ := ppair (⌜g⌝ : ℕ) (ppair (pConst a) (pConst (1 - a)))

lemma innerS_def : innerS g a = ppair (⌜g⌝ : ℕ) (ppair (pConst a) (pConst (1 - a))) := rfl

attribute [irreducible] innerS

lemma cast_innerS : ((innerS g a : ℕ) : V) = ppair (⌜g⌝ : V) (ppair (pConst (a : V)) (pConst ((1 - a : ℕ) : V))) := by
  rw [innerS_def, cast_ppair, cast_ppair, cast_pConst, cast_pConst, coe_quote_sentence₆]

lemma SV_eq_inner (k : V) : SV g a k = ppair 6 (ppair k (innerS g a : V)) + 1 := by
  rw [cast_innerS]; rfl

variable (ha : a = 0 ∨ a = 1)
include ha

lemma swapAct_cast : swapAct (a : V) = ((1 - a : ℕ) : V) := by
  rcases ha with rfl | rfl <;> simp [relabelAct]

lemma swapAct_cast' : swapAct ((1 - a : ℕ) : V) = (a : V) := by
  rcases ha with rfl | rfl <;> simp [relabelAct]

lemma one_sub_one_sub : 1 - (1 - a) = a := by rcases ha with rfl | rfl <;> rfl

/-- τ on the searcher: the transposed template, the branches exchanged. -/
theorem swapcode_SV (k : V) : swapcode (SV g a k) = SV (Semiformula.lMap swap g) (1 - a) k := by
  unfold SV swapcode
  rw [relabel_search, relabel_const, relabel_const, relabelTemplate_quote_sentence₆_V]
  show pSearch k _ (pConst (swapAct _)) (pConst (swapAct _)) = _
  rw [swapAct_cast a ha, swapAct_cast' a ha, one_sub_one_sub a ha]

lemma SV_lt_SVT_iff (k : V) :
    SV g a k < SV (Semiformula.lMap swap g) (1 - a) k ↔ innerS g a < innerS (Semiformula.lMap swap g) (1 - a) := by
  rw [SV_eq_inner, SV_eq_inner, pSearchInner_lt_iff, Nat.cast_lt]

lemma SVT_lt_SV_iff (k : V) :
    SV (Semiformula.lMap swap g) (1 - a) k < SV g a k ↔ innerS (Semiformula.lMap swap g) (1 - a) < innerS g a := by
  rw [SV_eq_inner, SV_eq_inner, pSearchInner_lt_iff, Nat.cast_lt]

omit ha

/-- The stored template of the canonical searcher. -/
noncomputable def gS : ℕ :=
  if innerS g a ≤ innerS (Semiformula.lMap swap g) (1 - a) then (⌜g⌝ : ℕ) else (⌜Semiformula.lMap swap g⌝ : ℕ)
/-- Its then-branch. -/
noncomputable def pS : ℕ :=
  if innerS g a ≤ innerS (Semiformula.lMap swap g) (1 - a) then pConst a else pConst (1 - a)
/-- Its else-branch. -/
noncomputable def qS : ℕ :=
  if innerS g a ≤ innerS (Semiformula.lMap swap g) (1 - a) then pConst (1 - a) else pConst a
/-- The first re-valuation term. -/
noncomputable def uS : ClosedSemiterm LAct 0 :=
  if innerS g a < innerS (Semiformula.lMap swap g) (1 - a) then cterm Act.C
  else if innerS (Semiformula.lMap swap g) (1 - a) < innerS g a then cterm Act.D else numT 0
/-- The second re-valuation term. -/
noncomputable def wS : ClosedSemiterm LAct 0 :=
  if innerS g a < innerS (Semiformula.lMap swap g) (1 - a) then cterm Act.D
  else if innerS (Semiformula.lMap swap g) (1 - a) < innerS g a then cterm Act.C else numT 1

lemma SV_eq_cast (k : V) :
    SV g a k = pSearch k ((⌜g⌝ : ℕ) : V) ((pConst a : ℕ) : V) ((pConst (1 - a) : ℕ) : V) := by
  unfold SV; rw [coe_quote_sentence₆, cast_pConst, cast_pConst]

include ha

lemma SVT_eq_cast (k : V) :
    SV (Semiformula.lMap swap g) (1 - a) k =
      pSearch k ((⌜Semiformula.lMap swap g⌝ : ℕ) : V) ((pConst (1 - a) : ℕ) : V) ((pConst a : ℕ) : V) := by
  unfold SV; rw [coe_quote_sentence₆, cast_pConst, cast_pConst, one_sub_one_sub a ha]

/-- **The canonical code of the searcher is a searcher with the (cast) `k`-independent inner triple.** -/
theorem dnum_SV (k : V) : dnum (SV g a k) = pSearch k (gS g a : V) (pS g a : V) (qS g a : V) := by
  by_cases h : innerS g a ≤ innerS (Semiformula.lMap swap g) (1 - a)
  · simp only [gS, pS, qS, if_pos h]
    rcases Nat.lt_or_eq_of_le h with h' | h'
    · rw [dnum_of_lt (by rw [swapcode_SV g a ha]; exact (SV_lt_SVT_iff g a ha k).mpr h')]
      exact SV_eq_cast g a k
    · rw [dnum_of_eq (by rw [swapcode_SV g a ha, SV_eq_inner, SV_eq_inner, h'])]
      exact SV_eq_cast g a k
  · simp only [gS, pS, qS, if_neg h]
    rw [dnum_of_gt (by rw [swapcode_SV g a ha]; exact (SVT_lt_SV_iff g a ha k).mpr (Nat.lt_of_not_le h)),
      swapcode_SV g a ha]
    exact SVT_eq_cast g a ha k

theorem dU_SV (k : V) : dU (SV g a k) = (⌜uS g a⌝ : V) := by
  unfold dU uS
  rw [swapcode_SV g a ha]
  by_cases h1 : innerS g a < innerS (Semiformula.lMap swap g) (1 - a)
  · rw [if_pos ((SV_lt_SVT_iff g a ha k).mpr h1), if_pos h1, quote_cterm_C]
  · rw [if_neg (fun h ↦ h1 ((SV_lt_SVT_iff g a ha k).mp h)), if_neg h1]
    by_cases h2 : innerS (Semiformula.lMap swap g) (1 - a) < innerS g a
    · rw [if_pos ((SVT_lt_SV_iff g a ha k).mpr h2), if_pos h2, quote_cterm_D]
    · rw [if_neg (fun h ↦ h2 ((SVT_lt_SV_iff g a ha k).mp h)), if_neg h2, quote_numT]
      simp

theorem dW_SV (k : V) : dW (SV g a k) = (⌜wS g a⌝ : V) := by
  unfold dW wS
  rw [swapcode_SV g a ha]
  by_cases h1 : innerS g a < innerS (Semiformula.lMap swap g) (1 - a)
  · rw [if_pos ((SV_lt_SVT_iff g a ha k).mpr h1), if_pos h1, quote_cterm_D]
  · rw [if_neg (fun h ↦ h1 ((SV_lt_SVT_iff g a ha k).mp h)), if_neg h1]
    by_cases h2 : innerS (Semiformula.lMap swap g) (1 - a) < innerS g a
    · rw [if_pos ((SVT_lt_SV_iff g a ha k).mpr h2), if_pos h2, quote_cterm_C]
    · rw [if_neg (fun h ↦ h2 ((SVT_lt_SV_iff g a ha k).mp h)), if_neg h2, quote_numT]
      simp

omit ha

/-- The one-variable description term of the searcher, over `LAct`. -/
noncomputable def TS : Semiterm LAct Empty 1 := Semiterm.lMap emb (searchT1 (gS g a) (pS g a) (qS g a))

lemma lMap_swap_TS : Semiterm.lMap swap (TS g a) = TS g a := term_lMap_swap_emb _

theorem quote_emb_TS :
    (⌜(Rew.emb (TS g a) : SyntacticSemiterm LAct 1)⌝ : V) =
    ppairT (bnum 6) (ppairT (^#0) (ppairT (bnum (gS g a : V)) (ppairT (progT (pS g a : V)) (progT (qS g a : V))))) ^+ 𝟏 := by
  unfold TS
  rw [term_emb_lMap_emb_n, quote_term_lMap_emb, quote_emb_searchT1]

include ha

/-- `TS` at the budget `k` denotes the canonical code of the searcher. -/
theorem val_TS_V (k : V) : (TS g a).val (s := stdActV V) ![k] Empty.elim = dnum (SV g a k) := by
  unfold TS
  rw [Semiterm.val_lMap, stdActV_lMap_emb, val_searchT1_V, dnum_SV g a ha]

/-- The `X`-hypothesis of the instance equations: the tower describes the searcher on codes. -/
theorem hX_SV (k : V) :
    termSubst LAct (bnum k ∷ (0 : V)) (⌜(Rew.emb (TS g a) : SyntacticSemiterm LAct 1)⌝ : V) =
      progT (dnum (SV g a k)) := by
  rw [quote_emb_TS, termSubst_tower, dnum_SV g a ha]

lemma hU_SV (k : V) : (⌜uS g a⌝ : V) = dU (SV g a k) := (dU_SV g a ha k).symm
lemma hW_SV (k : V) : (⌜wS g a⌝ : V) = dW (SV g a k) := (dW_SV g a ha k).symm

/-- The re-valuation terms reconstruct the searcher from its canonical code. -/
theorem relabel_val_uS_wS_V (k : V) :
    relabel ((uS g a).val (s := stdActV V) ![] Empty.elim) ((wS g a).val (s := stdActV V) ![] Empty.elim)
      (dnum (SV g a k)) = SV g a k := by
  unfold uS wS
  by_cases h1 : innerS g a < innerS (Semiformula.lMap swap g) (1 - a)
  · rw [if_pos h1, if_pos h1, val_cterm_C_V, val_cterm_D_V,
      dnum_of_lt (by rw [swapcode_SV g a ha]; exact (SV_lt_SVT_iff g a ha k).mpr h1), relabel_zero_one]
  · rw [if_neg h1, if_neg h1]
    by_cases h2 : innerS (Semiformula.lMap swap g) (1 - a) < innerS g a
    · rw [if_pos h2, if_pos h2, val_cterm_D_V, val_cterm_C_V,
        dnum_of_gt (by rw [swapcode_SV g a ha]; exact (SVT_lt_SV_iff g a ha k).mpr h2)]
      exact swapcode_swapcode _
    · have h' : innerS g a = innerS (Semiformula.lMap swap g) (1 - a) := le_antisymm (not_lt.mp h2) (not_lt.mp h1)
      rw [if_neg h2, if_neg h2, val_numT_V, val_numT_V, Nat.cast_zero, Nat.cast_one,
        dnum_of_eq (by rw [swapcode_SV g a ha, SV_eq_inner, SV_eq_inner, h']), relabel_zero_one]

/-- The transposed re-valuation terms reconstruct the TRANSPOSED searcher from the canonical code. -/
theorem relabel_val_uST_wST_V (k : V) :
    relabel ((Semiterm.lMap swap (uS g a)).val (s := stdActV V) ![] Empty.elim)
      ((Semiterm.lMap swap (wS g a)).val (s := stdActV V) ![] Empty.elim)
      (dnum (SV g a k)) = SV (Semiformula.lMap swap g) (1 - a) k := by
  unfold uS wS
  by_cases h1 : innerS g a < innerS (Semiformula.lMap swap g) (1 - a)
  · rw [if_pos h1, if_pos h1, lMap_swap_cterm_C, lMap_swap_cterm_D, val_cterm_D_V, val_cterm_C_V,
      dnum_of_lt (by rw [swapcode_SV g a ha]; exact (SV_lt_SVT_iff g a ha k).mpr h1)]
    exact swapcode_SV g a ha k
  · rw [if_neg h1, if_neg h1]
    by_cases h2 : innerS (Semiformula.lMap swap g) (1 - a) < innerS g a
    · rw [if_pos h2, if_pos h2, lMap_swap_cterm_D, lMap_swap_cterm_C, val_cterm_C_V, val_cterm_D_V,
        dnum_of_gt (by rw [swapcode_SV g a ha]; exact (SVT_lt_SV_iff g a ha k).mpr h2), swapcode_SV g a ha,
        relabel_zero_one]
    · have h' : innerS g a = innerS (Semiformula.lMap swap g) (1 - a) := le_antisymm (not_lt.mp h2) (not_lt.mp h1)
      have hST : SV g a k = SV (Semiformula.lMap swap g) (1 - a) k := by rw [SV_eq_inner, SV_eq_inner, h']
      rw [if_neg h2, if_neg h2, lMap_swap_numT, lMap_swap_numT, val_numT_V, val_numT_V, Nat.cast_zero,
        Nat.cast_one, dnum_of_eq (by rw [swapcode_SV g a ha, hST]), relabel_zero_one, hST]

end searcher

section values

/-- The searcher's triple describes it (values). -/
theorem hme_SV (g : Semisentence LAct 6) (a : ℕ) (ha : a = 0 ∨ a = 1) (k : V) :
    relabel ((uS g a).val (s := stdActV V) ![] Empty.elim) ((wS g a).val (s := stdActV V) ![] Empty.elim)
      ((TS g a).val (s := stdActV V) ![k] Empty.elim) = SV g a k := by
  rw [val_TS_V g a ha, relabel_val_uS_wS_V g a ha]

/-- The transposed triple describes the transposed searcher (values). -/
theorem hme_SVT (g : Semisentence LAct 6) (a : ℕ) (ha : a = 0 ∨ a = 1) (k : V) :
    relabel ((Semiterm.lMap swap (uS g a)).val (s := stdActV V) ![] Empty.elim)
      ((Semiterm.lMap swap (wS g a)).val (s := stdActV V) ![] Empty.elim)
      ((Semiterm.lMap swap (TS g a)).val (s := stdActV V) ![k] Empty.elim) = SV (Semiformula.lMap swap g) (1 - a) k := by
  rw [lMap_swap_TS, val_TS_V g a ha, relabel_val_uST_wST_V g a ha]

end values

/-! ### 5. The bot tower, the explicit engine templates and the bot-wrapped searcher's tower -/

section instances

/-- The one-variable structural term of a bot-wrapped program. -/
noncomputable def botT1 (t : Semiterm ℒₒᵣ Empty 1) : Semiterm ℒₒᵣ Empty 1 :=
  succT1 (ppairT1 (Rew.bShift (bnumT 3)) t)

lemma val_botT1_V (t : Semiterm ℒₒᵣ Empty 1) (k : V) :
    (botT1 t).val (s := standardModel V) ![k] Empty.elim = pBot (t.val (s := standardModel V) ![k] Empty.elim) := by
  rw [botT1, val_succT1_V, val_ppairT1_V, val_bShift₁_V, val_bnumT_V]
  unfold pBot
  push_cast
  rfl

lemma quote_emb_botT1 (t : Semiterm ℒₒᵣ Empty 1) :
    (⌜(Rew.emb (botT1 t) : SyntacticSemiterm ℒₒᵣ 1)⌝ : V) =
    ppairT (bnum 3) (⌜(Rew.emb t : SyntacticSemiterm ℒₒᵣ 1)⌝ : V) ^+ 𝟏 := by
  rw [botT1, quote_emb_succT1, quote_emb_ppairT1, quote_emb_bShift, ← Semiterm.empty_quote_def, quote_bnumT]
  push_cast
  rfl

/-- Dupoc's guard template, explicitly. -/
noncomputable abbrev gDu : Semisentence LAct 6 := tmpl (.plays .opp .self .C)
/-- Cupod's guard template, explicitly. -/
noncomputable abbrev gCu : Semisentence LAct 6 := tmpl (.plays .opp .self .D)
/-- Wary's guard template, explicitly. -/
noncomputable abbrev gW : Semisentence LAct 6 := tmpl (.neg (.plays .opp .self .C))
/-- The transposed Wary template. -/
noncomputable abbrev gWT : Semisentence LAct 6 := tmpl (.neg (.plays .opp .self .D))

lemma lMap_swap_gDu : Semiformula.lMap swap gDu = gCu := lMap_swap_tmpl _ rfl
lemma lMap_swap_gCu : Semiformula.lMap swap gCu = gDu := lMap_swap_tmpl _ rfl
lemma lMap_swap_gW : Semiformula.lMap swap gW = gWT := lMap_swap_tmpl _ rfl

/-- The one-variable description term of the bot-wrapped searcher `pBot (SV g a k)`. -/
noncomputable def TBS (g : Semisentence LAct 6) (a : ℕ) : Semiterm LAct Empty 1 :=
  Semiterm.lMap emb (botT1 (searchT1 (gS g a) (pS g a) (qS g a)))

lemma lMap_swap_TBS (g : Semisentence LAct 6) (a : ℕ) : Semiterm.lMap swap (TBS g a) = TBS g a :=
  term_lMap_swap_emb _

theorem val_TBS_V (g : Semisentence LAct 6) (a : ℕ) (ha : a = 0 ∨ a = 1) (k : V) :
    (TBS g a).val (s := stdActV V) ![k] Empty.elim = dnum (pBot (SV g a k)) := by
  unfold TBS
  rw [Semiterm.val_lMap, stdActV_lMap_emb, val_botT1_V, val_searchT1_V, dnum_pBot, dnum_SV g a ha]

theorem quote_emb_TBS (g : Semisentence LAct 6) (a : ℕ) :
    (⌜(Rew.emb (TBS g a) : SyntacticSemiterm LAct 1)⌝ : V) =
    ppairT (bnum 3)
      (ppairT (bnum 6) (ppairT (^#0) (ppairT (bnum (gS g a : V)) (ppairT (progT (pS g a : V)) (progT (qS g a : V))))) ^+ 𝟏)
      ^+ 𝟏 := by
  unfold TBS
  rw [term_emb_lMap_emb_n, quote_term_lMap_emb, quote_emb_botT1, quote_emb_searchT1]

/-- Filling the budget slot of the bot tower (`termSubst_TBD`, generic in the inner triple). -/
theorem termSubst_TBS (g : Semisentence LAct 6) (a : ℕ) (ha : a = 0 ∨ a = 1) (k : V) :
    termSubst LAct (bnum k ∷ (0 : V)) (⌜(Rew.emb (TBS g a) : SyntacticSemiterm LAct 1)⌝ : V) =
      progT (dnum (pBot (SV g a k))) := by
  have hb3 : IsUTerm LAct (bnum (3 : V)) := (bnum_semiterm_LAct 0 _).isUTerm
  have hb6 : IsUTerm LAct (bnum (6 : V)) := (bnum_semiterm_LAct 0 _).isUTerm
  have hbg : IsUTerm LAct (bnum (gS g a : V)) := (bnum_semiterm_LAct 0 _).isUTerm
  have hp : IsUTerm LAct (progT (pS g a : V)) := (progT_semiterm_LAct 0 _).isUTerm
  have hq : IsUTerm LAct (progT (qS g a : V)) := (progT_semiterm_LAct 0 _).isUTerm
  have hone : IsUTerm LAct (𝟏 : V) := (IsSemiterm.LAct_of_LOR (one_semiterm (n := 0))).isUTerm
  have h1 : IsUTerm LAct (ppairT (progT (pS g a : V)) (progT (qS g a : V))) := ppairT_uterm_LAct hp hq
  have h2 : IsUTerm LAct (ppairT (bnum (gS g a : V)) (ppairT (progT (pS g a : V)) (progT (qS g a : V)))) :=
    ppairT_uterm_LAct hbg h1
  have h3 : IsUTerm LAct (ppairT (^#0) (ppairT (bnum (gS g a : V)) (ppairT (progT (pS g a : V)) (progT (qS g a : V))))) :=
    ppairT_uterm_LAct bvar_zero_uterm h2
  have h4 : IsUTerm LAct (ppairT (bnum 6)
      (ppairT (^#0) (ppairT (bnum (gS g a : V)) (ppairT (progT (pS g a : V)) (progT (qS g a : V)))))) :=
    ppairT_uterm_LAct hb6 h3
  have h5 : IsUTerm LAct (ppairT (bnum 6)
      (ppairT (^#0) (ppairT (bnum (gS g a : V)) (ppairT (progT (pS g a : V)) (progT (qS g a : V))))) ^+ 𝟏) :=
    qqAdd_uterm_LAct h4 hone
  have h6 : IsUTerm LAct (ppairT (bnum 3)
      (ppairT (bnum 6) (ppairT (^#0) (ppairT (bnum (gS g a : V)) (ppairT (progT (pS g a : V)) (progT (qS g a : V))))) ^+ 𝟏)) :=
    ppairT_uterm_LAct hb3 h5
  rw [quote_emb_TBS, termSubst_qqAdd _ h6 hone, termSubst_ppairT _ hb3 h5,
    termSubst_closed _ (bnum_semiterm_LAct 0 _), termSubst_closed _ (IsSemiterm.LAct_of_LOR one_semiterm),
    termSubst_tower, dnum_pBot, dnum_SV g a ha, progT_bot]

lemma hU_botSV (g : Semisentence LAct 6) (a : ℕ) (ha : a = 0 ∨ a = 1) (k : V) :
    (⌜uS g a⌝ : V) = dU (pBot (SV g a k)) := by rw [dU_pBot]; exact hU_SV g a ha k
lemma hW_botSV (g : Semisentence LAct 6) (a : ℕ) (ha : a = 0 ∨ a = 1) (k : V) :
    (⌜wS g a⌝ : V) = dW (pBot (SV g a k)) := by rw [dW_pBot]; exact hW_SV g a ha k

theorem hme_botSV (g : Semisentence LAct 6) (a : ℕ) (ha : a = 0 ∨ a = 1) (k : V) :
    relabel ((uS g a).val (s := stdActV V) ![] Empty.elim) ((wS g a).val (s := stdActV V) ![] Empty.elim)
      ((TBS g a).val (s := stdActV V) ![k] Empty.elim) = pBot (SV g a k) := by
  rw [val_TBS_V g a ha, dnum_pBot, relabel_bot, relabel_val_uS_wS_V g a ha]

theorem hme_botSVT (g : Semisentence LAct 6) (a : ℕ) (ha : a = 0 ∨ a = 1) (k : V) :
    relabel ((Semiterm.lMap swap (uS g a)).val (s := stdActV V) ![] Empty.elim)
      ((Semiterm.lMap swap (wS g a)).val (s := stdActV V) ![] Empty.elim)
      ((Semiterm.lMap swap (TBS g a)).val (s := stdActV V) ![k] Empty.elim) =
      pBot (SV (Semiformula.lMap swap g) (1 - a) k) := by
  rw [lMap_swap_TBS, val_TBS_V g a ha, dnum_pBot, relabel_bot, relabel_val_uST_wST_V g a ha]

end instances

end ArithS
