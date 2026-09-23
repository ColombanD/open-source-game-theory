import ArithS.Cells.SoundnessCells
import ArithS.Cells.CIMCIC
import ArithS.Cells.JustBot
import ArithS.Cells.PrudentMirror

/-!
# ArithS.Cells.PositiveCells — the POS class of the census in PA-`S'`, and the unreadability cells re-evaluated

`Research/Notes/ROUTE_B_SCOPE.md` §3 Phase 4, class **POS** of `ROUTE_B_CENSUS.md` (2026-09-23): cells whose
searcher FINDS its guard without Löb (the engine's `search_t` on a search-free atom, `weakenImpl`, `atomNeg`),
unconditional in `S'` (no `BoundedInnerNec`), for all large `k`. The mechanism is `cimcic_self_coop`'s, made
generic: the guard is the `bnum k`-instance of a FIXED one-variable formula `q` (`guardCode_qT_eq_instB` with
the searcher's description triple), `q(k)` is true in BOTH standard readings of every model, so `TAct ⊢ ∀¹ q`
by completeness (`tact_all_of_both`), and the instance at `bnum k` costs `K₀ + K₁·size k ≤ k` (`found_of_all`).

1. **The constant opponents** `pConst 0`, `pConst 1`, `pBot (pConst 0)`, `pBot (pConst 1)`: canonical codes,
   re-valuation terms, closed structural terms `T0`/`TB0`, the code hypotheses `hX_const_*`/`hU_*`/`hW_*` and the
   value equations `val_desc_*`.
2. **The generic engine-searcher description layer**: `SV g a k := pSearch k ⌜g⌝ (pConst a) (pConst (1 - a))`,
   `swapcode_SV`, the canonical triple `dnum_SV`/`dU_SV`/`dW_SV` (`Cells/CIMCIC.lean` §2 with the template and
   branch as parameters), the tower `TS`, `hX_SV`, and the reconstructions `relabel_val_uS_wS_V`/`_uST_wST_V`.
   It puts the ENGINE codes `pcode (DupocBot k)`, `pcode (CupodBot k)`, `pcode (WaryBot k)` on the same footing as
   `Cimcic k`/`Dimcid k`; the bot tower `TBS` describes the frozen snapshot `pBot (pcode (DupocBot k))`, and
   `guardCode_JustBot_eq` shows Just's consulted guard IS Dupoc's engine guard in the snapshot's frame.
3. **The closure**: `tact_all_of_both`, `found_of_all`; the generic truth of a play-atom template instance in
   both triples (`eval_qT_plays_opp_self`, `eval_qT_neg_plays_opp_self`, `eval_qT_swap`), the plays of constants
   in every model and their negations by determinism (`const_play_V`, `bot_const_play_V`, `const_not_play_V`).
4. **The cells**: `pos_DupocBot_vs_CooperateBot` `(C, C)`, `pos_CupodBot_vs_DefectBot` `(D, D)`,
   `pos_CIMCIC_vs_CooperateBot` `(C, C)`, `pos_DIMCID_vs_DefectBot` `(D, D)`, `pos_JustBot_vs_CooperateBot` `(C, C)`
   (on the engine's own code), `pos_WaryBot_vs_DefectBot` `(D, D)` (the `.neg` guard is a Π₁ truth by
   determinism — the `S'` twin of `Pf.atomNeg`), and the SND cells whose positive sub-fact is the searcher finding
   its guard against `.bot DefectBot`: `snd_CupodBot_vs_DBot`/`_EBot` and `snd_WaryBot_vs_DBot`/`_EBot`, all `(C, C)`.
5. **The unreadability cells re-evaluated** (census classes FLOOR(cenU)/OTHER, where PA reads every source):
   * CIMCIC's guard against an opponent that defects against it is SELF-REFUTING (found ⇒ CIMCIC cooperates ⇒ by
     soundness the opponent cooperates — against the fact): `cimcic_selfref_not_found`, so
     `snd_CIMCIC_vs_DefectBot` `(D, D)` at EVERY `k` and `snd_CIMCIC_vs_OBot` `(D, D)` for large `k` keep the
     engine's values by soundness instead of the unreadability census.
   * **DIMCID × CooperateBot FLIPS**: the engine's `(C, C)` becomes `(D, C)` — DIMCID's guard "I play C against
     CooperateBot ⇒ CooperateBot plays D against me" has a false consequent, so it says "I do not cooperate"; a
     proof of it makes DIMCID defect, which makes it TRUE, and bounded Löb (`family_found` on the family
     `pG (cl T0) (cterm C) (cterm D)`, `loebSound_pDi0`) finds it: `loeb_DIMCID_vs_CooperateBot`.

Conventions: every threshold EXISTENTIAL; `simp` never sees a closed quote (`innerS` is irreducible); `omega` is
never asked about `V`; `≤` at ℕ bridged by `le_def`.
-/

set_option linter.constructorNameAsVariable false

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open LAct
open PD.Bots

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ### 1. The constant opponents: `pConst 0`, `pConst 1`, `pBot (pConst 0)`, `pBot (pConst 1)` -/

section constants

lemma pConst_zero_lt_one : pConst (0 : V) < pConst 1 := by
  unfold pConst ppair; norm_num

lemma swapcode_pConst_zero : swapcode (pConst (0 : V)) = pConst 1 := by
  unfold swapcode; rw [relabel_const]; simp [relabelAct]

lemma swapcode_pConst_one : swapcode (pConst (1 : V)) = pConst 0 := by
  unfold swapcode; rw [relabel_const]; simp [relabelAct]

lemma dnum_pConst_zero : dnum (pConst (0 : V)) = pConst 0 :=
  dnum_of_lt (by rw [swapcode_pConst_zero]; exact pConst_zero_lt_one)

lemma dnum_pConst_one : dnum (pConst (1 : V)) = pConst 0 := by
  rw [dnum_of_gt (by rw [swapcode_pConst_one]; exact pConst_zero_lt_one), swapcode_pConst_one]

lemma dU_pConst_zero : dU (pConst (0 : V)) = csym 0 := by
  unfold dU; rw [swapcode_pConst_zero, if_pos pConst_zero_lt_one]

lemma dW_pConst_zero : dW (pConst (0 : V)) = csym 1 := by
  unfold dW; rw [swapcode_pConst_zero, if_pos pConst_zero_lt_one]

lemma dU_pConst_one : dU (pConst (1 : V)) = csym 1 := by
  unfold dU; rw [swapcode_pConst_one, if_neg (lt_asymm pConst_zero_lt_one), if_pos pConst_zero_lt_one]

lemma dW_pConst_one : dW (pConst (1 : V)) = csym 0 := by
  unfold dW; rw [swapcode_pConst_one, if_neg (lt_asymm pConst_zero_lt_one), if_pos pConst_zero_lt_one]

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

/-! ### 2. The generic engine searcher `pSearch k ⌜g⌝ (pConst a) (pConst (1 - a))` and its description -/

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

/-! ### 3. From `TAct ⊢ ∀¹ q` to "found at every large `k`" -/

section closure

/-- **A `TAct`-theorem `∀¹ q` true in both readings, by completeness** (`tact_proves_qCC`'s shape). -/
theorem tact_all_of_both (q : Semisentence LAct 1)
    (hstd : ∀ (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (x : M),
      Semiformula.Eval (s := stdActV M) ![x] Empty.elim q)
    (hswap : ∀ (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (x : M),
      Semiformula.Eval (s := swapActS M) ![x] Empty.elim q) :
    TAct ⊢ ∀¹ q := by
  refine tact_complete' _ fun M _ _ ↦ ?_
  have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
  constructor
  · simp only [Semiformula.eval_all]
    intro x
    rw [← stdActV_eq_stdActS]
    exact hstd M x
  · simp only [Semiformula.eval_all]
    intro x
    exact hswap M x

/-- **The instance of a `TAct`-theorem `∀¹ q` at `bnum k` fits the budget `k` for all large `k`**
(`cimcic_self_finds_guard`'s body, generic in `q` and in the guard-code family `G`): the instance
costs `K₀ + K₁·size k` (`lenProvable_inst_size` + `flen_subst_bnumT_le`), below `k` eventually
(`linear_size_le_eventually`). -/
theorem found_of_all {q : Semisentence LAct 1} (hq : TAct ⊢ ∀¹ q) (G : ℕ → ℕ)
    (hG : ∀ k, G k = instB (⌜q⌝ : ℕ) k) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k → LenProvableV TAct k (G k) := by
  obtain ⟨N₃, hN₃⟩ := lenProvable_of_provable hq
  obtain ⟨kHat, hkHat⟩ :=
    linear_size_le_eventually (N₃ + 13 * flen (q : Semiproposition LAct 1) + 8 + 30 * flen (q : Semiproposition LAct 1) + 6)
  refine ⟨kHat + 1, fun k hk ↦ ?_⟩
  have h1 := lenProvable_inst_size q k hN₃
  have hqt := flen_subst_bnumT_le q k
  set fq := flen (q : Semiproposition LAct 1) with hfq
  set s := Nat.size k with hs
  have hs1 : 0 < s := Nat.lt_size.mpr (by rw [pow_zero]; omega)
  have hpoly := hkHat ℕ k (le_def.mpr (Or.inr (by rw [natCast_nat]; omega)))
  rw [natCast_nat, ← size_eq_length] at hpoly
  have hpoly' : (N₃ + 13 * fq + 8 + 30 * fq + 6) * s ≤ k := by
    rcases le_def.mp hpoly with h | h
    · exact Nat.le_of_eq h
    · exact Nat.le_of_lt h
  have hle : N₃ + 5 * flen ((q ⇜ ![Semiterm.lMap emb (bnumT k)] : Sentence LAct) : Proposition LAct)
      + 3 * fq + 6 * s + 8 ≤ k := by
    calc N₃ + 5 * flen ((q ⇜ ![Semiterm.lMap emb (bnumT k)] : Sentence LAct) : Proposition LAct)
          + 3 * fq + 6 * s + 8
        ≤ N₃ + 5 * (fq * (6 * s + 2)) + 3 * fq + 6 * s + 8 := by gcongr
      _ = (N₃ + 13 * fq + 8) + (30 * fq + 6) * s := by ring
      _ ≤ (N₃ + 13 * fq + 8) * s + (30 * fq + 6) * s := by
          gcongr; exact Nat.le_mul_of_pos_right _ hs1
      _ = (N₃ + 13 * fq + 8 + 30 * fq + 6) * s := by ring
      _ ≤ k := hpoly'
  have h2 := lenProvable_fbound_mono hle h1
  rw [← lenProvableV_nat] at h2
  have hq' : instB (⌜q⌝ : ℕ) k = ⌜(q ⇜ ![Semiterm.lMap emb (bnumT k)] : Sentence LAct)⌝ := by
    have := quote_instB (V := ℕ) q k
    rwa [natCast_nat] at this
  rw [hG, hq']
  exact h2

end closure

/-! ### 4. The truth of a play-atom template instance, generic in both triples -/

section truth

/-- **`qT (tmpl (.plays .opp .self a')) X U W X' U' W'` at `k`**: "the program the opp-triple
describes plays `a'` against the one the me-triple describes". -/
theorem eval_qT_plays_opp_self (a' : PD.Action) (X : Semiterm LAct Empty 1) (U W : ClosedSemiterm LAct 0)
    (X' : Semiterm LAct Empty 1) (U' W' : ClosedSemiterm LAct 0) (k : V) {me opp : V}
    (hme : relabel (U.val (s := stdActV V) ![] Empty.elim) (W.val (s := stdActV V) ![] Empty.elim)
      (X.val (s := stdActV V) ![k] Empty.elim) = me)
    (hopp : relabel (U'.val (s := stdActV V) ![] Empty.elim) (W'.val (s := stdActV V) ![] Empty.elim)
      (X'.val (s := stdActV V) ![k] Empty.elim) = opp) :
    Semiformula.Eval (s := stdActV V) ![k] Empty.elim (qT (tmpl (.plays .opp .self a')) X U W X' U' W') ↔
      ∃ n, EvalGraph n opp me opp (actCode a' : V) := by
  rw [eval_qT_iff, eval_tmpl_plays_opp_self_V]
  simp only [Matrix.cons_val]
  rw [hme, hopp]

/-- The negated atom: "the opp-program does NOT play `a'` against the me-program". -/
theorem eval_qT_neg_plays_opp_self (a' : PD.Action) (X : Semiterm LAct Empty 1) (U W : ClosedSemiterm LAct 0)
    (X' : Semiterm LAct Empty 1) (U' W' : ClosedSemiterm LAct 0) (k : V) {me opp : V}
    (hme : relabel (U.val (s := stdActV V) ![] Empty.elim) (W.val (s := stdActV V) ![] Empty.elim)
      (X.val (s := stdActV V) ![k] Empty.elim) = me)
    (hopp : relabel (U'.val (s := stdActV V) ![] Empty.elim) (W'.val (s := stdActV V) ![] Empty.elim)
      (X'.val (s := stdActV V) ![k] Empty.elim) = opp) :
    Semiformula.Eval (s := stdActV V) ![k] Empty.elim (qT (tmpl (.neg (.plays .opp .self a'))) X U W X' U' W') ↔
      ¬ ∃ n, EvalGraph n opp me opp (actCode a' : V) := by
  rw [eval_qT_iff, tmpl_neg]
  simp only [LogicalConnective.HomClass.map_neg, LogicalConnective.Prop.neg_eq]
  rw [eval_tmpl_plays_opp_self_V]
  simp only [Matrix.cons_val]
  rw [hme, hopp]

/-- The swapped reading of a `qT` instance is the standard reading of the transposed instance. -/
theorem eval_qT_swap (g : Semisentence LAct 6) (X : Semiterm LAct Empty 1) (U W : ClosedSemiterm LAct 0)
    (X' : Semiterm LAct Empty 1) (U' W' : ClosedSemiterm LAct 0) (k : V) :
    Semiformula.Eval (s := swapActS V) ![k] Empty.elim (qT g X U W X' U' W') ↔
      Semiformula.Eval (s := stdActV V) ![k] Empty.elim
        (qT (Semiformula.lMap swap g) (Semiterm.lMap swap X) (Semiterm.lMap swap U) (Semiterm.lMap swap W)
          (Semiterm.lMap swap X') (Semiterm.lMap swap U') (Semiterm.lMap swap W')) := by
  rw [eval_swapActS, lMap_swap_qT, ← stdActV_eq_stdActS]

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

/-- A constant plays itself against anything, in every model (fuel 1). -/
lemma const_play_V (me opp a : V) : ∃ n : V, EvalGraph n me opp (pConst a) a :=
  ⟨0 + 1, EvalGraph.const_iff.mpr rfl⟩

/-- A frozen constant plays itself against anything, in every model (fuel 2). -/
lemma bot_const_play_V (me opp a : V) : ∃ n : V, EvalGraph n me opp (pBot (pConst a)) a :=
  ⟨0 + 1 + 1, EvalGraph.bot_iff.mpr (EvalGraph.const_iff.mpr rfl)⟩

/-- A constant never plays the other value, in every model (determinism). -/
lemma const_not_play_V (me opp : V) {a b : V} (hab : a ≠ b) : ¬ ∃ n : V, EvalGraph n me opp (pConst a) b := by
  rintro ⟨n, hn⟩
  obtain ⟨m, hm⟩ := const_play_V me opp a
  exact hab (EvalGraph.unique_V' m n _ _ _ _ _ hm hn)

lemma bot_const_not_play_V (me opp : V) {a b : V} (hab : a ≠ b) : ¬ ∃ n : V, EvalGraph n me opp (pBot (pConst a)) b := by
  rintro ⟨n, hn⟩
  obtain ⟨m, hm⟩ := bot_const_play_V me opp a
  exact hab (EvalGraph.unique_V' m n _ _ _ _ _ hm hn)

end truth

/-! ### 5. The engine searchers as `SV` instances, and the bot-wrapped snapshot -/

section instances

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

lemma pcode_DupocBot_SV (k : ℕ) : pcode (DupocBot k) = SV (V := ℕ) gDu 0 k := by
  rw [pcode_DupocBot', SV_nat]; rfl
lemma pcode_CupodBot_SV (k : ℕ) : pcode (CupodBot k) = SV (V := ℕ) gCu 1 k := by
  rw [pcode_CupodBot, SV_nat]; rfl
lemma pcode_WaryBot_SV (k : ℕ) : pcode (WaryBot k) = SV (V := ℕ) gW 1 k := by
  rw [pcode_WaryBot, SV_nat]; rfl

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

/-- Just's consulted guard against `opp` is Dupoc's engine guard in the frame `(.bot (DupocBot k), opp)`
(both are the template code of "`opp` plays C against `.bot (DupocBot k)`"). -/
lemma guardCode_JustBot_eq (k : ℕ) {opp : PD.Prog} (hopp : Proper opp) :
    guardCode (tcode (phiJ k)) (pcode (JustBot k)) (pcode opp) =
      guardCode (tcode phiDu) (pBot (pcode (DupocBot k))) (pcode opp) := by
  rw [← pcode_bot]
  change guardOf (phiJ k) (JustBot k) opp = guardOf phiDu (.bot (DupocBot k)) opp
  rw [guardOf_eq_tcode_subst (proper_JustBot k) hopp _ rfl, guardOf_eq_tcode_subst (proper_bot _) hopp _ rfl]
  rfl

end instances

/-! ### 6. The cells -/

section cells

lemma actCode_C_cast : ((actCode .C : ℕ) : V) = 0 := by simp [actCode]
lemma actCode_D_cast : ((actCode .D : ℕ) : V) = 1 := by simp [actCode]

/-! #### DupocBot × CooperateBot `(C, C)` -/

/-- Dupoc's guard against CooperateBot as a fixed formula: "CooperateBot plays C against Dupoc(k)". -/
noncomputable def qDu0 : Semisentence LAct 1 :=
  qT gDu (TS gDu 0) (uS gDu 0) (wS gDu 0) (cl T0) (cterm Act.C) (cterm Act.D)

theorem guardCode_Du0 (k : V) : guardCode (⌜gDu⌝ : V) (SV gDu 0 k) (pConst 0) = instB (⌜qDu0⌝ : V) k :=
  guardCode_qT_eq_instB gDu k _ _ _ _ _ _ (hX_SV gDu 0 (Or.inl rfl) k) (hU_SV gDu 0 (Or.inl rfl) k)
    (hW_SV gDu 0 (Or.inl rfl) k) (hX_const_zero k) hU_C_zero hW_D_zero

theorem tact_qDu0 : TAct ⊢ ∀¹ qDu0 := by
  refine tact_all_of_both _ (fun M _ _ x ↦ ?_) (fun M _ _ x ↦ ?_)
  · have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    rw [qDu0, eval_qT_plays_opp_self .C _ _ _ _ _ _ x (hme_SV gDu 0 (Or.inl rfl) x) (val_desc_const_zero x),
      actCode_C_cast]
    exact const_play_V _ _ _
  · have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    rw [qDu0, eval_qT_swap, lMap_swap_gDu, lMap_swap_cl, lMap_swap_T0, lMap_swap_cterm_C, lMap_swap_cterm_D,
      eval_qT_plays_opp_self .D _ _ _ _ _ _ x (hme_SVT gDu 0 (Or.inl rfl) x) (val_desc_const_one x),
      actCode_D_cast]
    exact const_play_V _ _ _

/-- `DupocBot × CooperateBot = (C, C)` (engine `outcome_DupocBot_vs_CooperateBot`, pad 2), for all large `k`:
the guard "CooperateBot plays C against me" is a `TAct`-theorem in `k` (`tact_qDu0`), found within the
budget for all large `k` (`found_of_all`). -/
theorem pos_DupocBot_vs_CooperateBot :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 2 (pcode (DupocBot k)) (pcode CooperateBot) (pcode (DupocBot k)) (actCode .C) ∧
      EvalGraph 2 (pcode CooperateBot) (pcode (DupocBot k)) (pcode CooperateBot) (actCode .C) := by
  obtain ⟨k₀, h⟩ := found_of_all tact_qDu0
    (fun k ↦ guardCode (tcode phiDu) (pcode (DupocBot k)) (pcode CooperateBot))
    (fun k ↦ by rw [pcode_CB, pcode_DupocBot_SV]; exact guardCode_Du0 (V := ℕ) k)
  refine ⟨k₀, fun k hk ↦ ⟨?_, by rw [pcode_CB]; exact const_play 1 _ _ _⟩⟩
  have hg := h k hk
  rw [pcode_DupocBot'] at hg ⊢
  exact search_then phiDu hg (const_play _ _ _ _)

/-! #### CupodBot × DefectBot `(D, D)`, and Cupod's positive guard against `.bot DefectBot` -/

/-- Cupod's guard against DefectBot: "DefectBot plays D against Cupod(k)". -/
noncomputable def qCu1 : Semisentence LAct 1 :=
  qT gCu (TS gCu 1) (uS gCu 1) (wS gCu 1) (cl T0) (cterm Act.D) (cterm Act.C)

theorem guardCode_Cu1 (k : V) : guardCode (⌜gCu⌝ : V) (SV gCu 1 k) (pConst 1) = instB (⌜qCu1⌝ : V) k :=
  guardCode_qT_eq_instB gCu k _ _ _ _ _ _ (hX_SV gCu 1 (Or.inr rfl) k) (hU_SV gCu 1 (Or.inr rfl) k)
    (hW_SV gCu 1 (Or.inr rfl) k) (hX_const_one k) hU_D_one hW_C_one

theorem tact_qCu1 : TAct ⊢ ∀¹ qCu1 := by
  refine tact_all_of_both _ (fun M _ _ x ↦ ?_) (fun M _ _ x ↦ ?_)
  · have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    rw [qCu1, eval_qT_plays_opp_self .D _ _ _ _ _ _ x (hme_SV gCu 1 (Or.inr rfl) x) (val_desc_const_one x),
      actCode_D_cast]
    exact const_play_V _ _ _
  · have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    rw [qCu1, eval_qT_swap, lMap_swap_gCu, lMap_swap_cl, lMap_swap_T0, lMap_swap_cterm_C, lMap_swap_cterm_D,
      eval_qT_plays_opp_self .C _ _ _ _ _ _ x (hme_SVT gCu 1 (Or.inr rfl) x) (val_desc_const_zero x),
      actCode_C_cast]
    exact const_play_V _ _ _

/-- `CupodBot × DefectBot = (D, D)` (engine `outcome_CupodBot_vs_DefectBot`, pad 2), for all large `k`. -/
theorem pos_CupodBot_vs_DefectBot :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 2 (pcode (CupodBot k)) (pcode DefectBot) (pcode (CupodBot k)) (actCode .D) ∧
      EvalGraph 2 (pcode DefectBot) (pcode (CupodBot k)) (pcode DefectBot) (actCode .D) := by
  obtain ⟨k₀, h⟩ := found_of_all tact_qCu1
    (fun k ↦ guardCode (tcode phiCu) (pcode (CupodBot k)) (pcode DefectBot))
    (fun k ↦ by rw [pcode_DB, pcode_CupodBot_SV]; exact guardCode_Cu1 (V := ℕ) k)
  refine ⟨k₀, fun k hk ↦ ⟨?_, by rw [pcode_DB]; exact const_play 1 _ _ _⟩⟩
  have hg := h k hk
  rw [pcode_CupodBot] at hg ⊢
  exact search_then phiCu hg (const_play _ _ _ _)

/-- Cupod's guard against `.bot DefectBot`: "`.bot DefectBot` plays D against Cupod(k)". -/
noncomputable def qCuB1 : Semisentence LAct 1 :=
  qT gCu (TS gCu 1) (uS gCu 1) (wS gCu 1) (cl TB0) (cterm Act.D) (cterm Act.C)

theorem guardCode_CuB1 (k : V) :
    guardCode (⌜gCu⌝ : V) (SV gCu 1 k) (pBot (pConst 1)) = instB (⌜qCuB1⌝ : V) k :=
  guardCode_qT_eq_instB gCu k _ _ _ _ _ _ (hX_SV gCu 1 (Or.inr rfl) k) (hU_SV gCu 1 (Or.inr rfl) k)
    (hW_SV gCu 1 (Or.inr rfl) k) (hX_bot_one k) hU_D_bot_one hW_C_bot_one

theorem tact_qCuB1 : TAct ⊢ ∀¹ qCuB1 := by
  refine tact_all_of_both _ (fun M _ _ x ↦ ?_) (fun M _ _ x ↦ ?_)
  · have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    rw [qCuB1, eval_qT_plays_opp_self .D _ _ _ _ _ _ x (hme_SV gCu 1 (Or.inr rfl) x) (val_desc_bot_one x),
      actCode_D_cast]
    exact bot_const_play_V _ _ _
  · have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    rw [qCuB1, eval_qT_swap, lMap_swap_gCu, lMap_swap_cl, lMap_swap_TB0, lMap_swap_cterm_C, lMap_swap_cterm_D,
      eval_qT_plays_opp_self .C _ _ _ _ _ _ x (hme_SVT gCu 1 (Or.inr rfl) x) (val_desc_bot_zero x),
      actCode_C_cast]
    exact bot_const_play_V _ _ _

/-- Cupod defects against `.bot DefectBot` for all large `k` (its guard is found). -/
theorem cupod_vs_botDB_found :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k → EvalGraph 2 (pcode (CupodBot k)) (pBot (pConst 1)) (pcode (CupodBot k)) 1 := by
  obtain ⟨k₀, h⟩ := found_of_all tact_qCuB1
    (fun k ↦ guardCode (tcode phiCu) (pcode (CupodBot k)) (pBot (pConst 1)))
    (fun k ↦ by rw [pcode_CupodBot_SV]; exact guardCode_CuB1 (V := ℕ) k)
  refine ⟨k₀, fun k hk ↦ ?_⟩
  have hg := h k hk
  rw [pcode_CupodBot] at hg ⊢
  exact search_then phiCu hg (const_play _ _ _ _)

/-- `CupodBot × DBot = (C, C)` (engine `outcome_CupodBot_vs_DBot`, pad 4), for all large `k`: DBot sees Cupod
defect against `.bot DefectBot` (found) and cooperates; Cupod's guard against DBot is then false. -/
theorem snd_CupodBot_vs_DBot :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 4 (pcode (CupodBot k)) (pcode DBot) (pcode (CupodBot k)) (actCode .C) ∧
      EvalGraph 4 (pcode DBot) (pcode (CupodBot k)) (pcode DBot) (actCode .C) := by
  obtain ⟨k₀, h⟩ := cupod_vs_botDB_found
  refine ⟨k₀, fun k hk ↦ ?_⟩
  have hD := dbot_C_of_probe_D (h k hk)
  exact ⟨EvalGraph.mono_le (by omega) (cupod_C_of_probe k sfp_DBot.1 hD), hD⟩

/-- `CupodBot × EBot = (C, C)` (engine `outcome_CupodBot_vs_EBot`, pad 5), for all large `k`. -/
theorem snd_CupodBot_vs_EBot :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 5 (pcode (CupodBot k)) (pcode EBot) (pcode (CupodBot k)) (actCode .C) ∧
      EvalGraph 5 (pcode EBot) (pcode (CupodBot k)) (pcode EBot) (actCode .C) := by
  obtain ⟨k₀, h⟩ := cupod_vs_botDB_found
  refine ⟨k₀, fun k hk ↦ ?_⟩
  have hE := ebot_C_of_probes (h k hk) (cupod_vs_botCB k)
  exact ⟨EvalGraph.mono_le (by omega) (cupod_C_of_probe k sfp_EBot.1 hE), hE⟩

/-! #### CIMCIC × CooperateBot `(C, C)` -/

/-- CIMCIC's guard against CooperateBot: "I play C against CooperateBot ⇒ CooperateBot plays C against me". -/
noncomputable def qCi0 : Semisentence LAct 1 := qCG (cl T0) (cterm Act.C) (cterm Act.D)

theorem guardCode_Ci0 (k : V) : guardCode (⌜tmplC⌝ : V) (CimcicV k) (pConst 0) = instB (⌜qCi0⌝ : V) k :=
  guardCode_CimcicV_eq_instB k (cl T0) _ _ (hX_const_zero k) hU_C_zero hW_D_zero

theorem tact_qCi0 : TAct ⊢ ∀¹ qCi0 := by
  refine tact_all_of_both _ (fun M _ _ x ↦ ?_) (fun M _ _ x ↦ ?_)
  · have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    rw [qCi0, eval_qCG_iff_V x _ _ _ (val_desc_const_zero x)]
    exact fun _ ↦ const_play_V _ _ _
  · have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    rw [qCi0, eval_qCG_swap_iff_V, lMap_swap_cl, lMap_swap_T0, lMap_swap_cterm_C, lMap_swap_cterm_D,
      eval_qCTG_iff_V x _ _ _ (val_desc_const_one x)]
    exact fun _ ↦ const_play_V _ _ _

/-- `CIMCIC × CooperateBot = (C, C)` (engine `outcome_CIMCIC_vs_CooperateBot`, pad 2), for all large `k`
(the engine's `weakenImpl`: the consequent is a closed true atom). -/
theorem pos_CIMCIC_vs_CooperateBot :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 2 (pcode (CIMCIC k)) (pcode CooperateBot) (pcode (CIMCIC k)) (actCode .C) ∧
      EvalGraph 2 (pcode CooperateBot) (pcode (CIMCIC k)) (pcode CooperateBot) (actCode .C) := by
  obtain ⟨k₀, h⟩ := found_of_all tact_qCi0
    (fun k ↦ guardCode (⌜tmplC⌝ : ℕ) (Cimcic k) (pConst 0)) (fun k ↦ guardCode_Ci0 (V := ℕ) k)
  refine ⟨k₀, fun k hk ↦ ⟨?_, by rw [pcode_CB]; exact const_play 1 _ _ _⟩⟩
  rw [pcode_CIMCIC, pcode_CB]
  exact cimcic_search_V (V := ℕ) k (pConst 0) (h k hk)

/-! #### DIMCID × DefectBot `(D, D)` -/

/-- DIMCID's guard against DefectBot: "I play C against DefectBot ⇒ DefectBot plays D against me". -/
noncomputable def qDi1 : Semisentence LAct 1 := qDG (cl T0) (cterm Act.D) (cterm Act.C)

theorem guardCode_Di1 (k : V) : guardCode (⌜tmplD⌝ : V) (DimcidV k) (pConst 1) = instB (⌜qDi1⌝ : V) k :=
  guardCode_DimcidV_eq_instB k (cl T0) _ _ (hX_const_one k) hU_D_one hW_C_one

theorem tact_qDi1 : TAct ⊢ ∀¹ qDi1 := by
  refine tact_all_of_both _ (fun M _ _ x ↦ ?_) (fun M _ _ x ↦ ?_)
  · have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    rw [qDi1, eval_qDG_iff_V x _ _ _ (val_desc_const_one x)]
    exact fun _ ↦ const_play_V _ _ _
  · have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    rw [qDi1, eval_qDG_swap_iff_V, lMap_swap_cl, lMap_swap_T0, lMap_swap_cterm_C, lMap_swap_cterm_D,
      eval_qTG_iff_V x _ _ _ (val_desc_const_zero x)]
    exact fun _ ↦ const_play_V _ _ _

/-- `DIMCID × DefectBot = (D, D)` (engine `outcome_DIMCID_vs_DefectBot`, pad 2), for all large `k`. -/
theorem pos_DIMCID_vs_DefectBot :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 2 (pcode (DIMCID k)) (pcode DefectBot) (pcode (DIMCID k)) (actCode .D) ∧
      EvalGraph 2 (pcode DefectBot) (pcode (DIMCID k)) (pcode DefectBot) (actCode .D) := by
  obtain ⟨k₀, h⟩ := found_of_all tact_qDi1
    (fun k ↦ guardCode (⌜tmplD⌝ : ℕ) (Dimcid k) (pConst 1)) (fun k ↦ guardCode_Di1 (V := ℕ) k)
  refine ⟨k₀, fun k hk ↦ ⟨?_, by rw [pcode_DB]; exact const_play 1 _ _ _⟩⟩
  rw [pcode_DIMCID, pcode_DB]
  exact dimcid_search_V (V := ℕ) k (pConst 1) (h k hk)

/-! #### JustBot × CooperateBot `(C, C)`, on the engine's own code -/

/-- Just's guard against CooperateBot: "CooperateBot plays C against the frozen `.bot (DupocBot k)`". -/
noncomputable def qJ0 : Semisentence LAct 1 :=
  qT gDu (TBS gDu 0) (uS gDu 0) (wS gDu 0) (cl T0) (cterm Act.C) (cterm Act.D)

theorem guardCode_J0 (k : V) : guardCode (⌜gDu⌝ : V) (pBot (SV gDu 0 k)) (pConst 0) = instB (⌜qJ0⌝ : V) k :=
  guardCode_qT_eq_instB gDu k _ _ _ _ _ _ (termSubst_TBS gDu 0 (Or.inl rfl) k) (hU_botSV gDu 0 (Or.inl rfl) k)
    (hW_botSV gDu 0 (Or.inl rfl) k) (hX_const_zero k) hU_C_zero hW_D_zero

theorem tact_qJ0 : TAct ⊢ ∀¹ qJ0 := by
  refine tact_all_of_both _ (fun M _ _ x ↦ ?_) (fun M _ _ x ↦ ?_)
  · have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    rw [qJ0, eval_qT_plays_opp_self .C _ _ _ _ _ _ x (hme_botSV gDu 0 (Or.inl rfl) x) (val_desc_const_zero x),
      actCode_C_cast]
    exact const_play_V _ _ _
  · have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    rw [qJ0, eval_qT_swap, lMap_swap_gDu, lMap_swap_cl, lMap_swap_T0, lMap_swap_cterm_C, lMap_swap_cterm_D,
      eval_qT_plays_opp_self .D _ _ _ _ _ _ x (hme_botSVT gDu 0 (Or.inl rfl) x) (val_desc_const_one x),
      actCode_D_cast]
    exact const_play_V _ _ _

/-- `JustBot × CooperateBot = (C, C)` (engine `outcome_JustBot_vs_CooperateBot`, pad 2), for all large `k`, on the
engine's own code `pcode (JustBot k)`: the consulted guard is Dupoc's engine guard in the frame of the frozen
snapshot (`guardCode_JustBot_eq`), the `bnum k`-instance of `qJ0` through the bot tower `TBS`. -/
theorem pos_JustBot_vs_CooperateBot :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 2 (pcode (JustBot k)) (pcode CooperateBot) (pcode (JustBot k)) (actCode .C) ∧
      EvalGraph 2 (pcode CooperateBot) (pcode (JustBot k)) (pcode CooperateBot) (actCode .C) := by
  obtain ⟨k₀, h⟩ := found_of_all tact_qJ0
    (fun k ↦ guardCode (tcode (phiJ k)) (pcode (JustBot k)) (pcode CooperateBot))
    (fun k ↦ by
      rw [guardCode_JustBot_eq k sfp_CooperateBot.1, pcode_CB, pcode_DupocBot_SV]
      exact guardCode_J0 (V := ℕ) k)
  refine ⟨k₀, fun k hk ↦ ⟨?_, by rw [pcode_CB]; exact const_play 1 _ _ _⟩⟩
  have hg := h k hk
  rw [pcode_JustBot] at hg ⊢
  exact search_then (phiJ k) hg (const_play _ _ _ _)

/-! #### WaryBot × DefectBot `(D, D)`, and Wary's positive `.neg` guard against `.bot DefectBot` -/

/-- Wary's guard against DefectBot: "DefectBot does NOT play C against Wary(k)". -/
noncomputable def qW1 : Semisentence LAct 1 :=
  qT gW (TS gW 1) (uS gW 1) (wS gW 1) (cl T0) (cterm Act.D) (cterm Act.C)

theorem guardCode_W1 (k : V) : guardCode (⌜gW⌝ : V) (SV gW 1 k) (pConst 1) = instB (⌜qW1⌝ : V) k :=
  guardCode_qT_eq_instB gW k _ _ _ _ _ _ (hX_SV gW 1 (Or.inr rfl) k) (hU_SV gW 1 (Or.inr rfl) k)
    (hW_SV gW 1 (Or.inr rfl) k) (hX_const_one k) hU_D_one hW_C_one

theorem tact_qW1 : TAct ⊢ ∀¹ qW1 := by
  refine tact_all_of_both _ (fun M _ _ x ↦ ?_) (fun M _ _ x ↦ ?_)
  · have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    rw [qW1, eval_qT_neg_plays_opp_self .C _ _ _ _ _ _ x (hme_SV gW 1 (Or.inr rfl) x) (val_desc_const_one x),
      actCode_C_cast]
    exact const_not_play_V _ _ _root_.one_ne_zero
  · have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    rw [qW1, eval_qT_swap, lMap_swap_gW, lMap_swap_cl, lMap_swap_T0, lMap_swap_cterm_C, lMap_swap_cterm_D,
      eval_qT_neg_plays_opp_self .D _ _ _ _ _ _ x (hme_SVT gW 1 (Or.inr rfl) x) (val_desc_const_zero x),
      actCode_D_cast]
    exact const_not_play_V _ _ _root_.zero_ne_one

/-- `WaryBot × DefectBot = (D, D)` (engine `outcome_WaryBot_vs_DefectBot`, pad 2), for all large `k`: the `.neg`
guard "DefectBot does not cooperate with me" is a Π₁ truth in every model (determinism), a `TAct`-theorem
in `k`, found within the budget (the `S'` twin of the engine's `Pf.atomNeg`). -/
theorem pos_WaryBot_vs_DefectBot :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 2 (pcode (WaryBot k)) (pcode DefectBot) (pcode (WaryBot k)) (actCode .D) ∧
      EvalGraph 2 (pcode DefectBot) (pcode (WaryBot k)) (pcode DefectBot) (actCode .D) := by
  obtain ⟨k₀, h⟩ := found_of_all tact_qW1
    (fun k ↦ guardCode (tcode phiW) (pcode (WaryBot k)) (pcode DefectBot))
    (fun k ↦ by rw [pcode_DB, pcode_WaryBot_SV]; exact guardCode_W1 (V := ℕ) k)
  refine ⟨k₀, fun k hk ↦ ⟨?_, by rw [pcode_DB]; exact const_play 1 _ _ _⟩⟩
  have hg := h k hk
  rw [pcode_WaryBot] at hg ⊢
  exact search_then phiW hg (const_play _ _ _ _)

/-- Wary's guard against `.bot DefectBot`: "`.bot DefectBot` does NOT play C against Wary(k)". -/
noncomputable def qWB1 : Semisentence LAct 1 :=
  qT gW (TS gW 1) (uS gW 1) (wS gW 1) (cl TB0) (cterm Act.D) (cterm Act.C)

theorem guardCode_WB1 (k : V) : guardCode (⌜gW⌝ : V) (SV gW 1 k) (pBot (pConst 1)) = instB (⌜qWB1⌝ : V) k :=
  guardCode_qT_eq_instB gW k _ _ _ _ _ _ (hX_SV gW 1 (Or.inr rfl) k) (hU_SV gW 1 (Or.inr rfl) k)
    (hW_SV gW 1 (Or.inr rfl) k) (hX_bot_one k) hU_D_bot_one hW_C_bot_one

theorem tact_qWB1 : TAct ⊢ ∀¹ qWB1 := by
  refine tact_all_of_both _ (fun M _ _ x ↦ ?_) (fun M _ _ x ↦ ?_)
  · have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    rw [qWB1, eval_qT_neg_plays_opp_self .C _ _ _ _ _ _ x (hme_SV gW 1 (Or.inr rfl) x) (val_desc_bot_one x),
      actCode_C_cast]
    exact bot_const_not_play_V _ _ _root_.one_ne_zero
  · have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    rw [qWB1, eval_qT_swap, lMap_swap_gW, lMap_swap_cl, lMap_swap_TB0, lMap_swap_cterm_C, lMap_swap_cterm_D,
      eval_qT_neg_plays_opp_self .D _ _ _ _ _ _ x (hme_SVT gW 1 (Or.inr rfl) x) (val_desc_bot_zero x),
      actCode_D_cast]
    exact bot_const_not_play_V _ _ _root_.zero_ne_one

/-- Wary defects against `.bot DefectBot` for all large `k` (its `.neg` guard is found). -/
theorem wary_vs_botDB_found :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k → EvalGraph 2 (pcode (WaryBot k)) (pBot (pConst 1)) (pcode (WaryBot k)) 1 := by
  obtain ⟨k₀, h⟩ := found_of_all tact_qWB1
    (fun k ↦ guardCode (tcode phiW) (pcode (WaryBot k)) (pBot (pConst 1)))
    (fun k ↦ by rw [pcode_WaryBot_SV]; exact guardCode_WB1 (V := ℕ) k)
  refine ⟨k₀, fun k hk ↦ ?_⟩
  have hg := h k hk
  rw [pcode_WaryBot] at hg ⊢
  exact search_then phiW hg (const_play _ _ _ _)

/-- `WaryBot × DBot = (C, C)` (engine `outcome_WaryBot_vs_DBot`, pad 4), for all large `k`. -/
theorem snd_WaryBot_vs_DBot :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 4 (pcode (WaryBot k)) (pcode DBot) (pcode (WaryBot k)) (actCode .C) ∧
      EvalGraph 4 (pcode DBot) (pcode (WaryBot k)) (pcode DBot) (actCode .C) := by
  obtain ⟨k₀, h⟩ := wary_vs_botDB_found
  refine ⟨k₀, fun k hk ↦ ?_⟩
  have hD := dbot_C_of_probe_D (h k hk)
  exact ⟨EvalGraph.mono_le (by omega) (wary_C_of_probe k sfp_DBot.1 hD), hD⟩

/-- `WaryBot × EBot = (C, C)` (engine `outcome_WaryBot_vs_EBot`, pad 5), for all large `k`. -/
theorem snd_WaryBot_vs_EBot :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 5 (pcode (WaryBot k)) (pcode EBot) (pcode (WaryBot k)) (actCode .C) ∧
      EvalGraph 5 (pcode EBot) (pcode (WaryBot k)) (pcode EBot) (actCode .C) := by
  obtain ⟨k₀, h⟩ := wary_vs_botDB_found
  refine ⟨k₀, fun k hk ↦ ?_⟩
  have hE := ebot_C_of_probes (h k hk) (wary_vs_botCB k)
  exact ⟨EvalGraph.mono_le (by omega) (wary_C_of_probe k sfp_EBot.1 hE), hE⟩

end cells

/-! ### 7. The UNREADABILITY cells re-evaluated in `S'` (census class FLOOR(cenU)/OTHER) -/

section unreadability

lemma pcode_CIMCIC' (k : ℕ) : pcode (CIMCIC k) = pSearch k (tcode phiC) (pConst 0) (pConst 1) := by
  simp [CIMCIC, phiC, actCode]
lemma proper_CIMCIC (k : ℕ) : Proper (CIMCIC k) := ⟨by simp [CIMCIC], by simp [CIMCIC]⟩

/-- **CIMCIC's guard against an opponent that defects against it is SELF-REFUTING**: a proof of
"I play C against `opp` ⇒ `opp` plays C against me" makes CIMCIC cooperate, so by soundness `opp`
cooperates — against the fact. So it is never found (the red cell's argument, one level up). -/
theorem cimcic_selfref_not_found (k : ℕ) {opp : PD.Prog} (hopp : Proper opp) {N : ℕ}
    (h : EvalGraph N (pcode opp) (pcode (CIMCIC k)) (pcode opp) 1) :
    ¬ LenProvableV TAct k (guardCode (tcode phiC) (pcode (CIMCIC k)) (pcode opp)) := by
  intro hf
  have hC : EvalGraph 2 (pcode (CIMCIC k)) (pcode opp) (pcode (CIMCIC k)) 0 := by
    rw [pcode_CIMCIC'] at hf ⊢
    exact search_then phiC hf (const_play _ _ _ _)
  have hT : ℕ↓[LAct] ⊧ trAt (CIMCIC k) opp phiC :=
    models_trAt_of_lenProvableV (φ := phiC) (me := CIMCIC k) (opp := opp) hf
  rw [← trAt_subst (CIMCIC k) opp (proper_CIMCIC k) hopp phiC rfl] at hT
  change ℕ↓[LAct] ⊧ trAt (CIMCIC k) opp (.impl (.plays (CIMCIC k) opp .C) (.plays opp (CIMCIC k) .C)) at hT
  rw [models_trAt_impl, models_trAt_plays _ _ _ _ _ (proper_CIMCIC k) hopp,
    models_trAt_plays _ _ _ _ _ hopp (proper_CIMCIC k)] at hT
  obtain ⟨N', hN'⟩ := hT ⟨2, hC⟩
  exact absurd (EvalGraph.unique' hN' h) (by decide)

/-- `CIMCIC × DefectBot = (D, D)` (engine `outcome_CIMCIC_vs_DefectBot`, pad 2) at EVERY `k`: in `S'` the
guard is true but self-refuting, hence never found — the census's unreadability argument replaced by
soundness. -/
theorem snd_CIMCIC_vs_DefectBot (k : ℕ) :
    EvalGraph 2 (pcode (CIMCIC k)) (pcode DefectBot) (pcode (CIMCIC k)) (actCode .D) ∧
    EvalGraph 2 (pcode DefectBot) (pcode (CIMCIC k)) (pcode DefectBot) (actCode .D) := by
  have hn := cimcic_selfref_not_found k sfp_DefectBot.1 (N := 1) (by rw [pcode_DB]; exact const_play 0 _ _ _)
  rw [pcode_CIMCIC'] at hn ⊢
  exact ⟨search_else phiC hn (const_play _ _ _ _), by rw [pcode_DB]; exact const_play 1 _ _ _⟩

/-- CIMCIC defects against `.bot DefectBot` at every `k` (self-refuting guard). -/
theorem cimcic_vs_botDB (k : ℕ) :
    EvalGraph 2 (pcode (CIMCIC k)) (pBot (pConst 1)) (pcode (CIMCIC k)) 1 := by
  have hn := cimcic_selfref_not_found k (opp := .bot DefectBot) proper_botDB (N := 2)
    (by rw [pcode_botDB]; exact bot_const_play 0 _ _ _)
  rw [pcode_botDB] at hn
  rw [pcode_CIMCIC'] at hn ⊢
  exact search_else phiC hn (const_play _ _ _ _)

/-- CIMCIC's guard against `.bot CooperateBot`: the consequent "`.bot CooperateBot` plays C against me" is
a closed truth, so the implication is a `TAct`-theorem in `k`. -/
noncomputable def qCiB0 : Semisentence LAct 1 := qCG (cl TB0) (cterm Act.C) (cterm Act.D)

theorem guardCode_CiB0 (k : V) :
    guardCode (⌜tmplC⌝ : V) (CimcicV k) (pBot (pConst 0)) = instB (⌜qCiB0⌝ : V) k :=
  guardCode_CimcicV_eq_instB k (cl TB0) _ _ (hX_bot_zero k) hU_C_bot_zero hW_D_bot_zero

theorem tact_qCiB0 : TAct ⊢ ∀¹ qCiB0 := by
  refine tact_all_of_both _ (fun M _ _ x ↦ ?_) (fun M _ _ x ↦ ?_)
  · have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    rw [qCiB0, eval_qCG_iff_V x _ _ _ (val_desc_bot_zero x)]
    exact fun _ ↦ bot_const_play_V _ _ _
  · have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    rw [qCiB0, eval_qCG_swap_iff_V, lMap_swap_cl, lMap_swap_TB0, lMap_swap_cterm_C, lMap_swap_cterm_D,
      eval_qCTG_iff_V x _ _ _ (val_desc_bot_one x)]
    exact fun _ ↦ bot_const_play_V _ _ _

/-- CIMCIC cooperates with `.bot CooperateBot` for all large `k` (its guard is found). -/
theorem cimcic_vs_botCB_found :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k → EvalGraph 2 (pcode (CIMCIC k)) (pBot (pConst 0)) (pcode (CIMCIC k)) 0 := by
  obtain ⟨k₀, h⟩ := found_of_all tact_qCiB0
    (fun k ↦ guardCode (⌜tmplC⌝ : ℕ) (Cimcic k) (pBot (pConst 0))) (fun k ↦ guardCode_CiB0 (V := ℕ) k)
  refine ⟨k₀, fun k hk ↦ ?_⟩
  rw [pcode_CIMCIC]
  exact cimcic_search_V (V := ℕ) k (pBot (pConst 0)) (h k hk)

/-- `CIMCIC × OBot = (D, D)` (engine `outcome_CIMCIC_vs_OBot`, pad 5) for all large `k`: OBot sees CIMCIC
cooperate with `.bot CooperateBot` (found) but defect against `.bot DefectBot` (self-refuting), and defects;
CIMCIC's guard against OBot is then self-refuting too. -/
theorem snd_CIMCIC_vs_OBot :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 5 (pcode (CIMCIC k)) (pcode OBot) (pcode (CIMCIC k)) (actCode .D) ∧
      EvalGraph 5 (pcode OBot) (pcode (CIMCIC k)) (pcode OBot) (actCode .D) := by
  obtain ⟨k₀, h⟩ := cimcic_vs_botCB_found
  refine ⟨k₀, fun k hk ↦ ?_⟩
  have hO := obot_D_of_probes (h k hk) (cimcic_vs_botDB k)
  have hn := cimcic_selfref_not_found k sfp_OBot.1 hO
  refine ⟨?_, hO⟩
  rw [pcode_CIMCIC'] at hn ⊢
  exact search_else phiC hn (const_play 3 _ _ _)

/-! #### DIMCID × CooperateBot: the value FLIPS in `S'` — a self-fulfilling refutation is Löb-provable -/

lemma pcode_DIMCID' (k : ℕ) : pcode (DIMCID k) = pSearch k (tcode phiD) (pConst 1) (pConst 0) := by
  simp [DIMCID, phiD, actCode]

/-- **The bounded Löb premise of DIMCID against CooperateBot, slack `(7, 8)`**: a box of the family makes
DIMCID defect against CooperateBot and the transposed searcher cooperate with DefectBot, so the
antecedents "I play C against CooperateBot" / "I play D against DefectBot" are false and both
implications hold, in both readings. -/
theorem loebSound_pDi0 : LoebSound (pG (cl T0) (cterm Act.C) (cterm Act.D)) 7 8 := by
  intro V _ _ k a ha h
  have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
  have ha' : a + 8 * (formulaLen LAct (instB (⌜qDG (cl T0) (cterm Act.C) (cterm Act.D)⌝ : V) k) +
      formulaLen LAct (instB (⌜qTG (Semiterm.lMap swap (cl T0 : Semiterm LAct Empty 1))
        (Semiterm.lMap swap (cterm Act.C)) (Semiterm.lMap swap (cterm Act.D))⌝ : V) k)) + 7 ≤ k :=
    le_trans (pConj_slack_le a _ _ _ (formulaLen_instB_pG (cl T0) (cterm Act.C) (cterm Act.D) k)) ha
  obtain ⟨h1, h2⟩ := pG_both_V k (cl T0) (cterm Act.C) (cterm Act.D) (hX_const_zero k) hU_C_zero hW_D_zero a ha' h
  rw [swapcode_pConst_zero] at h2
  have hopp' : relabel ((Semiterm.lMap swap (cterm Act.C : ClosedSemiterm LAct 0)).val (s := stdActV V) ![] Empty.elim)
      ((Semiterm.lMap swap (cterm Act.D : ClosedSemiterm LAct 0)).val (s := stdActV V) ![] Empty.elim)
      ((Semiterm.lMap swap (cl T0 : Semiterm LAct Empty 1)).val (s := stdActV V) ![k] Empty.elim) = pConst 1 := by
    rw [lMap_swap_cl, lMap_swap_T0, lMap_swap_cterm_C, lMap_swap_cterm_D]
    exact val_desc_const_one k
  have hA : ¬ ∃ n, EvalGraph n (DimcidV k) (pConst 0) (DimcidV k) 0 := by
    rintro ⟨n, hn⟩
    exact _root_.zero_ne_one (EvalGraph.unique_V' n 2 _ _ _ _ _ hn h1)
  have hB : ¬ ∃ n, EvalGraph n (DimcidTV k) (pConst 1) (DimcidTV k) 1 := by
    rintro ⟨n, hn⟩
    exact _root_.one_ne_zero (EvalGraph.unique_V' n 2 _ _ _ _ _ hn h2)
  exact ⟨(eval_pG_iff_stdActS k (cl T0) (cterm Act.C) (cterm Act.D) (val_desc_const_zero k) hopp').mpr
      ⟨fun h ↦ absurd h hA, fun h ↦ absurd h hB⟩,
    (eval_pG_iff_swap k (cl T0) (cterm Act.C) (cterm Act.D) (val_desc_const_zero k) hopp').mpr
      ⟨fun h ↦ absurd h hA, fun h ↦ absurd h hB⟩⟩

/-- **DIMCID × CooperateBot is `(D, C)` in PA-`S'`**, for all large `k`, unconditional — the engine's cell is
`(C, C)` (`outcome_DIMCID_vs_CooperateBot`, an unreadability census). In `S'` the guard "I play C against
CooperateBot ⇒ CooperateBot plays D against me" has a false consequent, so it says "I do not cooperate":
a proof of it makes DIMCID defect, which makes it TRUE — bounded Löb (`family_found`) then finds it. -/
theorem loeb_DIMCID_vs_CooperateBot :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 2 (pcode (DIMCID k)) (pcode CooperateBot) (pcode (DIMCID k)) (actCode .D) ∧
      EvalGraph 2 (pcode CooperateBot) (pcode (DIMCID k)) (pcode CooperateBot) (actCode .C) := by
  obtain ⟨k₀, h⟩ := family_found (pG (cl T0) (cterm Act.C) (cterm Act.D)) boundedInnerNec_sixteen loebSound_pDi0
  refine ⟨k₀, fun k hk ↦ ⟨?_, by rw [pcode_CB]; exact const_play 1 _ _ _⟩⟩
  obtain ⟨a, ha, hpc⟩ := h k hk
  have ha' := le_def.mpr (pConj_slack_nat a _ _ _ k
    (formulaLen_instB_pG (V := ℕ) (cl T0) (cterm Act.C) (cterm Act.D) k) ha)
  have h1 := pG_both_V (V := ℕ) k (cl T0) (cterm Act.C) (cterm Act.D) (hX_const_zero k) hU_C_zero hW_D_zero a ha' hpc
  rw [pcode_DIMCID, pcode_CB]
  exact h1.1

end unreadability

end ArithS
