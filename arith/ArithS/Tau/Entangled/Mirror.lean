import ArithS.Tau.Entangled.Dimcid
import ArithS.Tau.Described

/-!
# ArithS.Tau.Entangled.Mirror — a self-prober entangled with τ(Mirror): the closed, τ-fixed partner

τ(EBot)'s third watch sims the hypothesis's instance at the MIRROR; at a self-probing hypothesis `T` that
instance is the system `.sys [sysGo 1 T mirror (spec T), mm 0] 0` whose second member `mm 0 = .sim (.bot
(.selfIdx 0)) (.bot (.selfIdx 0))` is a CLOSED, `k`-free, τ-FIXED program (no action constant). This module is
the `Sys2` kit (`Tower`/`Loeb`/`Congr`/`Dimcid`) for such a system, `Sys2c`: a simple member `0` and a closed
τ-fixed member `1`. Everything simplifies: the τ-order is decided by member `0` alone, with NO threshold
(`sys2_lt_of_member0`), and only member `0` has a guard. It is instantiated on `inst dimcid mirror =
.sys [dim 1, mm 0] 0`: the DIMCID member defects (its self-fulfilling family, `found_Di_c`), so the mirror
watch of τ(EBot) at DIMCID falls and `ebot × dimcid` is `D` — the FLIP of the engine's `C`.
-/

set_option linter.constructorNameAsVariable false

namespace ArithS.Tau

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open LAct
open PD PD.Tau

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- A system of a simple member `0` and a closed τ-fixed member `1` (code `P`). -/
structure Sys2c where
  m₀ : SM
  P : ℕ
  hP : transposeCode P = P

namespace Sys2c

/-! ### 1. Codes, transposition, the canonical choice -/

noncomputable def D (S : Sys2c) (k : V) : V := pCons (S.m₀.code k) (pCons (S.P : V) pNil)
noncomputable def code (S : Sys2c) (j : ℕ) (k : V) : V := pSys (S.D k) (j : V)
noncomputable def tr (S : Sys2c) : Sys2c := ⟨S.m₀.tr, S.P, S.hP⟩

lemma tr_m₀ (S : Sys2c) : S.tr.m₀ = S.m₀.tr := rfl

lemma transposeCode_P (S : Sys2c) : transposeCode (S.P : V) = (S.P : V) := by
  rw [← cast_transposeCode, S.hP]

theorem transposeCode_D (S : Sys2c) (k : V) : transposeCode (S.D k) = S.tr.D k := by
  unfold D transposeCode
  rw [revalue_cons, revalue_cons, revalue_nil]
  show pCons (transposeCode _) (pCons (transposeCode _) pNil) = _
  rw [SM.transposeCode_code, transposeCode_P]; rfl

theorem transposeCode_code (S : Sys2c) (j : ℕ) (k : V) : transposeCode (S.code j k) = S.tr.code j k := by
  unfold code transposeCode
  rw [revalue_sys]
  show pSys (transposeCode _) _ = _
  rw [transposeCode_D]

/-- The decision: member `0`'s inner part below its transposed one (no threshold). -/
def orig (S : Sys2c) : Prop := S.m₀.inner < S.m₀.tr.inner

theorem code_lt_tr {S : Sys2c} (h : S.orig) (j : ℕ) (k : V) : S.code j k < S.tr.code j k := by
  unfold code D
  exact sys2_lt_of_member0 ((SM.code_lt_iff _ _ k).mpr h)

theorem tr_lt_code {S : Sys2c} (h : ¬ S.orig) (j : ℕ) (k : V) : S.tr.code j k < S.code j k := by
  have h' : S.m₀.tr.inner < S.m₀.inner := lt_of_le_of_ne (not_lt.mp h) (Ne.symm (SM.inner_ne_tr _))
  unfold code D
  exact sys2_lt_of_member0 ((SM.code_lt_iff _ _ k).mpr h')

open scoped Classical in
noncomputable def can (S : Sys2c) : Sys2c := if S.orig then S else S.tr
open scoped Classical in
noncomputable def uT (S : Sys2c) : ClosedSemiterm LAct 0 := if S.orig then cterm Act.C else cterm Act.D
open scoped Classical in
noncomputable def wT (S : Sys2c) : ClosedSemiterm LAct 0 := if S.orig then cterm Act.D else cterm Act.C

theorem canonical_code (S : Sys2c) (j : ℕ) (k : V) : canonical (S.code j k) = S.can.code j k := by
  unfold can
  by_cases h : S.orig
  · rw [if_pos h, canonical_of_lt (by rw [transposeCode_code]; exact code_lt_tr h j k)]
  · rw [if_neg h, canonical_of_gt (by rw [transposeCode_code]; exact tr_lt_code h j k), transposeCode_code]

theorem revalueU_code (S : Sys2c) (j : ℕ) (k : V) : revalueU (S.code j k) = (⌜S.uT⌝ : V) := by
  unfold revalueU uT
  rw [transposeCode_code]
  by_cases h : S.orig
  · rw [if_pos (code_lt_tr h j k), if_pos h, quote_cterm_C]
  · rw [if_neg (lt_asymm (tr_lt_code h j k)), if_pos (tr_lt_code h j k), if_neg h, quote_cterm_D]

theorem revalueW_code (S : Sys2c) (j : ℕ) (k : V) : revalueW (S.code j k) = (⌜S.wT⌝ : V) := by
  unfold revalueW wT
  rw [transposeCode_code]
  by_cases h : S.orig
  · rw [if_pos (code_lt_tr h j k), if_pos h, quote_cterm_D]
  · rw [if_neg (lt_asymm (tr_lt_code h j k)), if_pos (tr_lt_code h j k), if_neg h, quote_cterm_C]

theorem revalue_val_uT_wT (S : Sys2c) (k : V) (j : ℕ) :
    revalue (S.uT.val (s := stdReadingV V) ![] Empty.elim) (S.wT.val (s := stdReadingV V) ![] Empty.elim)
      (S.can.code j k) = S.code j k := by
  unfold uT wT can
  by_cases h : S.orig
  · rw [if_pos h, if_pos h, if_pos h, val_cterm_C_V, val_cterm_D_V, revalue_zero_one]
  · rw [if_neg h, if_neg h, if_neg h, val_cterm_D_V, val_cterm_C_V]
    show transposeCode (S.tr.code j k) = _
    rw [← transposeCode_code S j k, transposeCode_transposeCode]

theorem revalue_val_uT_wT_swap (S : Sys2c) (k : V) (j : ℕ) :
    revalue ((Semiterm.lMap swap S.uT).val (s := stdReadingV V) ![] Empty.elim)
      ((Semiterm.lMap swap S.wT).val (s := stdReadingV V) ![] Empty.elim) (S.can.code j k) = S.tr.code j k := by
  unfold uT wT can
  by_cases h : S.orig
  · rw [if_pos h, if_pos h, if_pos h, lMap_swap_cterm_C, lMap_swap_cterm_D, val_cterm_D_V, val_cterm_C_V]
    show transposeCode (S.code j k) = _
    rw [transposeCode_code]
  · rw [if_neg h, if_neg h, if_neg h, lMap_swap_cterm_D, lMap_swap_cterm_C, val_cterm_C_V, val_cterm_D_V,
      revalue_zero_one]

/-! ### 2. The towers -/

/-- The closed member's one-variable term: its structural term, shifted. -/
noncomputable def PT1 (S : Sys2c) : Semiterm ℒₒᵣ Empty 1 := Rew.bShift (codeTermMeta S.P)

lemma val_PT1_V (S : Sys2c) (k : V) : S.PT1.val (s := standardModel V) ![k] Empty.elim = (S.P : V) := by
  rw [PT1, val_bShift₁_V, val_codeTermMeta_V]

lemma termSubst_PT1 (S : Sys2c) (w : V) :
    termSubst LAct w (⌜(Rew.emb S.PT1 : SyntacticSemiterm ℒₒᵣ 1)⌝ : V) = codeTerm (S.P : V) := by
  rw [PT1, quote_emb_bShift, ← Semiterm.empty_quote_def, quote_codeTermMeta, termSubst_closed _ (codeTerm_semiterm_LAct 0 _)]

noncomputable def T1 (S : Sys2c) (j : ℕ) : Semiterm ℒₒᵣ Empty 1 := sysT1 (consT1 S.m₀.T1 (consT1 S.PT1 nilT1)) j

lemma val_T1_V (S : Sys2c) (j : ℕ) (k : V) : (S.T1 j).val (s := standardModel V) ![k] Empty.elim = S.code j k := by
  rw [T1, val_sysT1_V, val_consT1_V, val_consT1_V, val_nilT1_V, SM.val_T1_V, val_PT1_V]; rfl

lemma termSubst_T1 (S : Sys2c) (j : ℕ) (k : V) :
    termSubst LAct (binNumeral k ∷ (0 : V)) (⌜(Rew.emb (S.T1 j) : SyntacticSemiterm ℒₒᵣ 1)⌝ : V) = codeTerm (S.code j k) := by
  rw [T1]
  exact termSubst_sysT1 _ (termSubst_consT1 _ (SM.termSubst_T1 _ _) (termSubst_consT1 _ (termSubst_PT1 _ _) (termSubst_nilT1 _))) j

noncomputable def TM (S : Sys2c) (j : ℕ) : Semiterm LAct Empty 1 := Semiterm.lMap emb (S.can.T1 j)
noncomputable def TX (S : Sys2c) (j : ℕ) : Semiterm LAct Empty 1 := Semiterm.lMap emb (botT1 (S.can.T1 j))

lemma lMap_swap_TM (S : Sys2c) (j : ℕ) : Semiterm.lMap swap (S.TM j) = S.TM j := term_lMap_swap_emb _
lemma lMap_swap_TX (S : Sys2c) (j : ℕ) : Semiterm.lMap swap (S.TX j) = S.TX j := term_lMap_swap_emb _

theorem val_TM_V (S : Sys2c) (j : ℕ) (k : V) : (S.TM j).val (s := stdReadingV V) ![k] Empty.elim = canonical (S.code j k) := by
  unfold TM; rw [Semiterm.val_lMap, stdReadingV_lMap_emb, val_T1_V, canonical_code]

theorem val_TX_V (S : Sys2c) (j : ℕ) (k : V) :
    (S.TX j).val (s := stdReadingV V) ![k] Empty.elim = canonical (pBot (S.code j k)) := by
  unfold TX; rw [Semiterm.val_lMap, stdReadingV_lMap_emb, val_botT1_V, val_T1_V, canonical_pBot, canonical_code]

theorem hX_TM (S : Sys2c) (j : ℕ) (k : V) :
    termSubst LAct (binNumeral k ∷ (0 : V)) (⌜(Rew.emb (S.TM j) : SyntacticSemiterm LAct 1)⌝ : V) =
      codeTerm (canonical (S.code j k)) := by
  unfold TM; rw [term_emb_lMap_emb_n, quote_term_lMap_emb, termSubst_T1, canonical_code]

theorem hX_TX (S : Sys2c) (j : ℕ) (k : V) :
    termSubst LAct (binNumeral k ∷ (0 : V)) (⌜(Rew.emb (S.TX j) : SyntacticSemiterm LAct 1)⌝ : V) =
      codeTerm (canonical (pBot (S.code j k))) := by
  unfold TX
  rw [term_emb_lMap_emb_n, quote_term_lMap_emb, termSubst_botT1 _ (termSubst_T1 _ _ _), canonical_pBot, canonical_code]

theorem descVal_TM (S : Sys2c) (j : ℕ) (k : V) : descVal (S.TM j) S.uT S.wT k = S.code j k := by
  rw [descVal_def, val_TM_V, canonical_code, revalue_val_uT_wT]
theorem descVal_TM_T (S : Sys2c) (j : ℕ) (k : V) :
    descVal (Semiterm.lMap swap (S.TM j)) (Semiterm.lMap swap S.uT) (Semiterm.lMap swap S.wT) k = S.tr.code j k := by
  rw [descVal_def, lMap_swap_TM, val_TM_V, canonical_code, revalue_val_uT_wT_swap]
theorem descVal_TX (S : Sys2c) (j : ℕ) (k : V) : descVal (S.TX j) S.uT S.wT k = pBot (S.code j k) := by
  rw [descVal_def, val_TX_V, canonical_pBot, revalue_bot, canonical_code, revalue_val_uT_wT]
theorem descVal_TX_T (S : Sys2c) (j : ℕ) (k : V) :
    descVal (Semiterm.lMap swap (S.TX j)) (Semiterm.lMap swap S.uT) (Semiterm.lMap swap S.wT) k = pBot (S.tr.code j k) := by
  rw [descVal_def, lMap_swap_TX, val_TX_V, canonical_pBot, revalue_bot, canonical_code, revalue_val_uT_wT_swap]

/-! ### 3. Member `0`'s guard: the instance equation and the search clauses -/

lemma code_zero (S : Sys2c) (k : V) : S.code 0 k = pSys (S.D k) 0 := by unfold code; rw [Nat.cast_zero]
lemma code_one (S : Sys2c) (k : V) : S.code 1 k = pSys (S.D k) 1 := by unfold code; rw [Nat.cast_one]

/-- Member `0`'s guard, consulted in the frame of the bot-wrapped members `(i, i')`. -/
noncomputable def q (S : Sys2c) (i i' : ℕ) : Semisentence LAct 1 :=
  qT13 S.m₀.g (S.TX i) S.uT S.wT (S.TX i') S.uT S.wT (S.TM 0) S.uT S.wT (S.TM 1) S.uT S.wT

theorem guard_eq_instB (S : Sys2c) (k : V) (i i' : ℕ) :
    guardCodeB (sysCloseTemplate (S.D k) ((⌜S.m₀.g⌝ : ℕ) : V)) (pBot (S.code i k)) (pBot (S.code i' k)) k =
      instB (⌜S.q i i'⌝ : V) k := by
  rw [coe_quote_sentence₁₃]
  unfold q
  refine guardCodeB_sysClose_eq_instB _ k (S.D k) _ _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact hX_TX S i k
  · rw [revalueU_pBot, revalueU_code]
  · rw [revalueW_pBot, revalueW_code]
  · exact hX_TX S i' k
  · rw [revalueU_pBot, revalueU_code]
  · rw [revalueW_pBot, revalueW_code]
  · rw [← code_zero]; exact hX_TM S 0 k
  · rw [← code_zero, revalueU_code]
  · rw [← code_zero, revalueW_code]
  · rw [← code_one]; exact hX_TM S 1 k
  · rw [← code_one, revalueU_code]
  · rw [← code_one, revalueW_code]

lemma listGet_D_zero (S : Sys2c) (k : V) : listGet (S.D k) 0 = S.m₀.code k + 1 := by
  unfold D; rw [listGet_cons_zero]

lemma sysCloseCode_m₀ (S : Sys2c) (k : V) :
    sysCloseCode (S.D k) (S.m₀.code k) =
      pSearch k (sysCloseTemplate (S.D k) ((⌜S.m₀.g⌝ : ℕ) : V)) (pConst (S.m₀.a : V)) (pConst ((1 - S.m₀.a : ℕ) : V)) := by
  unfold SM.code; rw [sysCloseCode_search, sysCloseCode_const, sysCloseCode_const]

theorem member_then_V (S : Sys2c) (k me opp : V)
    (h : LenBox TAct k (guardCodeB (sysCloseTemplate (S.D k) ((⌜S.m₀.g⌝ : ℕ) : V)) me opp k)) :
    EvalGraph 4 me opp (pBot (S.code 0 k)) (S.m₀.a : V) := by
  rw [show (4 : V) = 3 + 1 from three_add_one_eq_four.symm, EvalGraph.bot_iff,
    show (3 : V) = 2 + 1 from two_add_one_eq_three.symm, code_zero, EvalGraph.sys_iff]
  refine ⟨_, listGet_D_zero S k, ?_⟩
  rw [sysCloseCode_m₀, show (2 : V) = 1 + 1 from one_add_one_eq_two.symm, EvalGraph.search_iff]
  exact Or.inl ⟨h, by rw [show (1 : V) = 0 + 1 by simp, EvalGraph.const_iff]⟩

theorem plays_of_box (S : Sys2c) (k : V) (i i' : ℕ) (h : LenBox TAct k (instB (⌜S.q i i'⌝ : V) k)) :
    EvalGraph 4 (pBot (S.code i k)) (pBot (S.code i' k)) (pBot (S.code 0 k)) (S.m₀.a : V) := by
  rw [← guard_eq_instB] at h
  exact member_then_V S k _ _ h

/-! #### The transposed system -/

theorem canonical_tr_code (S : Sys2c) (j : ℕ) (k : V) : canonical (S.tr.code j k) = S.can.code j k := by
  rw [← transposeCode_code, canonical_transposeCode, canonical_code]

theorem revalueU_tr_code (S : Sys2c) (j : ℕ) (k : V) : revalueU (S.tr.code j k) = (⌜Semiterm.lMap swap S.uT⌝ : V) := by
  have e : transposeCode (S.tr.code j k) = S.code j k := by rw [← transposeCode_code, transposeCode_transposeCode]
  unfold revalueU uT
  rw [e]
  by_cases h : S.orig
  · rw [if_neg (lt_asymm (code_lt_tr h j k)), if_pos (code_lt_tr h j k), if_pos h, lMap_swap_cterm_C, quote_cterm_D]
  · rw [if_pos (tr_lt_code h j k), if_neg h, lMap_swap_cterm_D, quote_cterm_C]

theorem revalueW_tr_code (S : Sys2c) (j : ℕ) (k : V) : revalueW (S.tr.code j k) = (⌜Semiterm.lMap swap S.wT⌝ : V) := by
  have e : transposeCode (S.tr.code j k) = S.code j k := by rw [← transposeCode_code, transposeCode_transposeCode]
  unfold revalueW wT
  rw [e]
  by_cases h : S.orig
  · rw [if_neg (lt_asymm (code_lt_tr h j k)), if_pos (code_lt_tr h j k), if_pos h, lMap_swap_cterm_D, quote_cterm_C]
  · rw [if_pos (tr_lt_code h j k), if_neg h, lMap_swap_cterm_C, quote_cterm_D]

lemma lMap_swap_q (S : Sys2c) (i i' : ℕ) :
    Semiformula.lMap swap (S.q i i') =
      qT13 (Semiformula.lMap swap S.m₀.g) (S.TX i) (Semiterm.lMap swap S.uT) (Semiterm.lMap swap S.wT)
        (S.TX i') (Semiterm.lMap swap S.uT) (Semiterm.lMap swap S.wT)
        (S.TM 0) (Semiterm.lMap swap S.uT) (Semiterm.lMap swap S.wT)
        (S.TM 1) (Semiterm.lMap swap S.uT) (Semiterm.lMap swap S.wT) := by
  unfold q
  rw [lMap_swap_qT13, lMap_swap_TX, lMap_swap_TX, lMap_swap_TM, lMap_swap_TM]

theorem tr_guard_eq_instB (S : Sys2c) (k : V) (i i' : ℕ) :
    guardCodeB (sysCloseTemplate (S.tr.D k) ((⌜S.tr.m₀.g⌝ : ℕ) : V)) (pBot (S.tr.code i k)) (pBot (S.tr.code i' k)) k =
      instB (⌜Semiformula.lMap swap (S.q i i')⌝ : V) k := by
  rw [tr_m₀, SM.tr_g, coe_quote_sentence₁₃, lMap_swap_q]
  refine guardCodeB_sysClose_eq_instB _ k (S.tr.D k) _ _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hX_TX, canonical_pBot, canonical_pBot, canonical_tr_code, canonical_code]
  · rw [revalueU_pBot, revalueU_tr_code]
  · rw [revalueW_pBot, revalueW_tr_code]
  · rw [hX_TX, canonical_pBot, canonical_pBot, canonical_tr_code, canonical_code]
  · rw [revalueU_pBot, revalueU_tr_code]
  · rw [revalueW_pBot, revalueW_tr_code]
  · rw [hX_TM, ← code_zero, canonical_tr_code, canonical_code]
  · rw [← code_zero]; exact (revalueU_tr_code S 0 k).symm
  · rw [← code_zero]; exact (revalueW_tr_code S 0 k).symm
  · rw [hX_TM, ← code_one, canonical_tr_code, canonical_code]
  · rw [← code_one]; exact (revalueU_tr_code S 1 k).symm
  · rw [← code_one]; exact (revalueW_tr_code S 1 k).symm

theorem tr_plays_of_box (S : Sys2c) (k : V) (i i' : ℕ)
    (h : LenBox TAct k (instB (⌜Semiformula.lMap swap (S.q i i')⌝ : V) k)) :
    EvalGraph 4 (pBot (S.tr.code i k)) (pBot (S.tr.code i' k)) (pBot (S.tr.code 0 k)) (S.tr.m₀.a : V) := by
  rw [← tr_guard_eq_instB] at h
  exact member_then_V S.tr k _ _ h

/-! #### The truth equations (the `.impl` guard of member `0` probing member `1`) -/

noncomputable def vals (S : Sys2c) (i i' : ℕ) (k : V) : Fin 13 → V :=
  ![(S.TX i).val (s := stdReadingV V) ![k] Empty.elim, S.uT.val (s := stdReadingV V) ![] Empty.elim,
    S.wT.val (s := stdReadingV V) ![] Empty.elim, (S.TX i').val (s := stdReadingV V) ![k] Empty.elim,
    S.uT.val (s := stdReadingV V) ![] Empty.elim, S.wT.val (s := stdReadingV V) ![] Empty.elim, k,
    (S.TM 0).val (s := stdReadingV V) ![k] Empty.elim, S.uT.val (s := stdReadingV V) ![] Empty.elim,
    S.wT.val (s := stdReadingV V) ![] Empty.elim, (S.TM 1).val (s := stdReadingV V) ![k] Empty.elim,
    S.uT.val (s := stdReadingV V) ![] Empty.elim, S.wT.val (s := stdReadingV V) ![] Empty.elim]

omit [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
lemma eval_q_iff_vals (S : Sys2c) (i i' : ℕ) (k : V) :
    Semiformula.Eval (s := stdReadingV V) ![k] Empty.elim (S.q i i') ↔
      Semiformula.Eval (s := stdReadingV V) (S.vals i i' k) Empty.elim S.m₀.g := by
  unfold q vals; exact eval_qT13_iff _ _ _ _ _ _ _ _ _ _ _ _ _ k

lemma vals_me (S : Sys2c) (i i' : ℕ) (k : V) :
    revalue (S.vals i i' k 1) (S.vals i i' k 2) (S.vals i i' k 0) = pBot (S.code i k) := by
  have := descVal_TX S i k; rw [descVal_def] at this; exact this

lemma vals_mem1 (S : Sys2c) (i i' : ℕ) (k : V) : memVal (S.vals i i' k) 1 = S.code 1 k := by
  rw [memVal_one]; have := descVal_TM S 1 k; rw [descVal_def] at this; exact this

theorem eval_q_impl (S : Sys2c) {a a' : PD.Action}
    (hg : S.m₀.g = template13 (.impl (.plays .self (.bot (.selfIdx 1)) a) (.plays (.bot (.selfIdx 1)) .self a'))) (i i' : ℕ) (k : V) :
    Semiformula.Eval (s := stdReadingV V) ![k] Empty.elim (S.q i i') ↔
      ((∃ n, EvalGraph n (pBot (S.code i k)) (pBot (S.code 1 k)) (pBot (S.code i k)) (actCode a : V)) →
        (∃ n, EvalGraph n (pBot (S.code 1 k)) (pBot (S.code i k)) (pBot (S.code 1 k)) (actCode a' : V))) := by
  rw [eval_q_iff_vals, hg, template13_impl]
  simp only [LogicalConnective.HomClass.map_imply, LogicalConnective.Prop.arrow_eq]
  rw [eval_template13_self_partner 1 (by decide), eval_template13_partner_self 1 (by decide), vals_mem1, vals_me]

noncomputable def valsT (S : Sys2c) (i i' : ℕ) (k : V) : Fin 13 → V :=
  ![(S.TX i).val (s := stdReadingV V) ![k] Empty.elim, (Semiterm.lMap swap S.uT).val (s := stdReadingV V) ![] Empty.elim,
    (Semiterm.lMap swap S.wT).val (s := stdReadingV V) ![] Empty.elim, (S.TX i').val (s := stdReadingV V) ![k] Empty.elim,
    (Semiterm.lMap swap S.uT).val (s := stdReadingV V) ![] Empty.elim, (Semiterm.lMap swap S.wT).val (s := stdReadingV V) ![] Empty.elim, k,
    (S.TM 0).val (s := stdReadingV V) ![k] Empty.elim, (Semiterm.lMap swap S.uT).val (s := stdReadingV V) ![] Empty.elim,
    (Semiterm.lMap swap S.wT).val (s := stdReadingV V) ![] Empty.elim, (S.TM 1).val (s := stdReadingV V) ![k] Empty.elim,
    (Semiterm.lMap swap S.uT).val (s := stdReadingV V) ![] Empty.elim, (Semiterm.lMap swap S.wT).val (s := stdReadingV V) ![] Empty.elim]

omit [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
lemma eval_swap_q_iff_valsT (S : Sys2c) (i i' : ℕ) (k : V) :
    Semiformula.Eval (s := stdReadingV V) ![k] Empty.elim (Semiformula.lMap swap (S.q i i')) ↔
      Semiformula.Eval (s := stdReadingV V) (S.valsT i i' k) Empty.elim (Semiformula.lMap swap S.m₀.g) := by
  rw [lMap_swap_q]; unfold valsT; exact eval_qT13_iff _ _ _ _ _ _ _ _ _ _ _ _ _ k

lemma valsT_me (S : Sys2c) (i i' : ℕ) (k : V) :
    revalue (S.valsT i i' k 1) (S.valsT i i' k 2) (S.valsT i i' k 0) = pBot (S.tr.code i k) := by
  have := descVal_TX_T S i k; rw [descVal_def, lMap_swap_TX] at this; exact this

lemma valsT_mem1 (S : Sys2c) (i i' : ℕ) (k : V) : memVal (S.valsT i i' k) 1 = S.tr.code 1 k := by
  rw [memVal_one]; have := descVal_TM_T S 1 k; rw [descVal_def, lMap_swap_TM] at this; exact this

theorem eval_q_impl_swap (S : Sys2c) {a a' : PD.Action}
    (hg : S.m₀.g = template13 (.impl (.plays .self (.bot (.selfIdx 1)) a) (.plays (.bot (.selfIdx 1)) .self a'))) (i i' : ℕ) (k : V) :
    Semiformula.Eval (s := stdReadingV V) ![k] Empty.elim (Semiformula.lMap swap (S.q i i')) ↔
      ((∃ n, EvalGraph n (pBot (S.tr.code i k)) (pBot (S.tr.code 1 k)) (pBot (S.tr.code i k)) (actCode a.swap : V)) →
        (∃ n, EvalGraph n (pBot (S.tr.code 1 k)) (pBot (S.tr.code i k)) (pBot (S.tr.code 1 k)) (actCode a'.swap : V))) := by
  rw [eval_swap_q_iff_valsT, hg, lMap_swap_template13_impl, lMap_swap_template13_self_partner 1 (by decide),
    lMap_swap_template13_partner_self 1 (by decide)]
  simp only [LogicalConnective.HomClass.map_imply, LogicalConnective.Prop.arrow_eq]
  rw [eval_template13_self_partner 1 (by decide), eval_template13_partner_self 1 (by decide), valsT_mem1, valsT_me]

/-! ### 4. DIMCID's self-fulfilling family on the mirror system -/

/-- DIMCID at the head of a mirror system: boxes in the frames `(0, 0)` and `(0, 1)` make it defect in both. -/
theorem loebSound_Di (S : Sys2c) (hg : S.m₀.g = template13 (entDimG 1)) (ha : S.m₀.a = 1) :
    LoebSound (pQ (S.q 0 0 ⋏ S.q 0 1)) 14 16 := by
  have h := loebSound_pQ₂_above (S.q 0 0) (S.q 0 1) 0 fun V _ _ k _ b₁ b₂ b₃ b₄ ↦ by
    have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    rw [← stdReadingV_eq_stdReading]
    have hD := S.plays_of_box k 0 1 b₂
    have hDT := S.tr_plays_of_box k 0 1 b₄
    rw [ha, Nat.cast_one] at hD
    rw [tr_m₀, SM.tr_a, ha] at hDT
    simp only [Nat.sub_self, Nat.cast_zero] at hDT
    have hA : ¬ ∃ n, EvalGraph n (pBot (S.code 0 k)) (pBot (S.code 1 k)) (pBot (S.code 0 k)) (actCode .C : V) := by
      rintro ⟨n, hn⟩
      have := EvalGraph.unique_V' n 4 _ _ _ _ _ hn hD
      rw [actCode_C_cast] at this
      exact _root_.zero_ne_one this
    have hAT : ¬ ∃ n, EvalGraph n (pBot (S.tr.code 0 k)) (pBot (S.tr.code 1 k)) (pBot (S.tr.code 0 k)) (actCode Action.C.swap : V) := by
      rintro ⟨n, hn⟩
      have := EvalGraph.unique_V' n 4 _ _ _ _ _ hn hDT
      rw [show Action.C.swap = .D from rfl, actCode_D_cast] at this
      exact _root_.one_ne_zero this
    exact ⟨(S.eval_q_impl hg 0 0 k).mpr fun h ↦ absurd h hA, (S.eval_q_impl hg 0 1 k).mpr fun h ↦ absurd h hA,
      (S.eval_q_impl_swap hg 0 0 k).mpr fun h ↦ absurd h hAT, (S.eval_q_impl_swap hg 0 1 k).mpr fun h ↦ absurd h hAT⟩
  simpa using h

/-- DIMCID finds its guard in the bit's frame for all large `k`. -/
theorem found_Di (S : Sys2c) (hg : S.m₀.g = template13 (entDimG 1)) (ha : S.m₀.a = 1) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k → LenBox TAct k (instB (⌜S.q 0 0⌝ : ℕ) k) := by
  obtain ⟨k₀, h⟩ := family_found (pQ (S.q 0 0 ⋏ S.q 0 1)) boundedInnerNec_sixteen (loebSound_Di S hg ha)
  refine ⟨k₀, fun k hk ↦ ?_⟩
  obtain ⟨a, ha', hbox⟩ := h k hk
  obtain ⟨b₁, -, -, -⟩ := boxes_pQ₂_nat _ _ 0 k a (by simpa using ha') hbox
  exact b₁

/-! ### 5. The bridge to the engine's codes at ℕ -/

theorem D_nat (φ₀ : PD.Formula) (a₀ : PD.Action) (m₁ : Prog) (hP : transposeCode (progCode m₁) = progCode m₁) (k : ℕ) :
    (Sys2c.mk (SM.ofSearch φ₀ a₀) (progCode m₁) hP).D k =
      progListCode (sys2 (.search k φ₀ (.const a₀) (.const a₀.swap)) m₁) := by
  unfold D; rw [SM.code_nat, natCast_nat]; rfl

theorem code_nat (φ₀ : PD.Formula) (a₀ : PD.Action) (m₁ : Prog) (hP : transposeCode (progCode m₁) = progCode m₁) (j k : ℕ) :
    (Sys2c.mk (SM.ofSearch φ₀ a₀) (progCode m₁) hP).code j k =
      progCode (.sys (sys2 (.search k φ₀ (.const a₀) (.const a₀.swap)) m₁) j) := by
  unfold code; rw [D_nat, progCode_sys, natCast_nat]

theorem guardCodeB_sysClose_nat (φ₀ : PD.Formula) (a₀ : PD.Action) (m₁ : Prog) (hP : transposeCode (progCode m₁) = progCode m₁)
    (k : ℕ) (φ : PD.Formula) (hφ : memberGuardF φ = true)
    (hns : noSelfIdxF (φ.sysClose (sys2 (.search k φ₀ (.const a₀) (.const a₀.swap)) m₁)) = true) (x y : ℕ) :
    guardCodeB (sysCloseTemplate ((Sys2c.mk (SM.ofSearch φ₀ a₀) (progCode m₁) hP).D k) ((⌜template13 φ⌝ : ℕ) : ℕ)) x y k =
      guardCode (templateCode (φ.sysClose (sys2 (.search k φ₀ (.const a₀) (.const a₀.swap)) m₁))) x y := by
  rw [D_nat]
  show guardCodeB (sysCloseTemplate _ (templateCode φ)) x y k = _
  rw [templateCode_sysClose _ φ hφ, guardCodeB_of_template (isSemiformula_templateCode _ hns)]

end Sys2c

/-! ### 6. `ebot × dimcid`: DIMCID at the mirror defects, the mirror watch falls -/

/-- The mirror member is τ-fixed (no action constant). -/
lemma transposeCode_mm0 : transposeCode (progCode (mm 0)) = progCode (mm 0) := by
  simp [mm, transposeCode]

/-- `inst dimcid mirror = .sys [dim 1, mm 0] 0`, as a mirror system. -/
noncomputable def SDiM : Sys2c := ⟨SM.ofSearch (entDimG 1) .D, progCode (mm 0), transposeCode_mm0⟩

theorem found_DiM_engine : ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
    LenBox TAct k (guardCode (templateCode (.impl (.plays .self (.bot (.sys (sys2 (dim 1 k) (mm 0)) 1)) .C)
      (.plays (.bot (.sys (sys2 (dim 1 k) (mm 0)) 1)) .self .D)))
      (progCode (sysFrame (dim 1 k) (mm 0))) (progCode (sysFrame (dim 1 k) (mm 0)))) := by
  obtain ⟨k₀, h⟩ := Sys2c.found_Di SDiM rfl rfl
  refine ⟨k₀, fun k hk ↦ ?_⟩
  have e := Sys2c.guard_eq_instB (V := ℕ) SDiM k 0 0
  rw [natCast_nat] at e
  have := h k hk
  rw [← e, show (⌜SDiM.m₀.g⌝ : ℕ) = ⌜template13 (entDimG 1)⌝ from rfl,
    show SDiM = Sys2c.mk (SM.ofSearch (entDimG 1) .D) (progCode (mm 0)) transposeCode_mm0 from rfl,
    Sys2c.guardCodeB_sysClose_nat (entDimG 1) .D (mm 0) transposeCode_mm0 k (entDimG 1) rfl rfl, Sys2c.code_nat] at this
  exact this

/-- **τ(DIMCID) at the mirror defects against itself** (the `mirror` column at DIMCID). -/
theorem col_dimcid_mirror_D : bitEventually .dimcid .mirror .D := by
  obtain ⟨k₀, h⟩ := found_DiM_engine
  exact ⟨k₀, fun k hk ↦ bit_D_of_dim_then (inst_dimcid_mirror k) (h k hk)⟩

/-- `ebot × dimcid`: D — the FLIP of the engine's `C`. τ(EBot)'s three watches on DIMCID's instances all fall:
at the defector (`col_dimcid_defect`, POS on its own description: D), at the cooperator (`col_dimcid_coop`, the
base FLIP: D) and at the mirror (`col_dimcid_mirror_D`). -/
theorem ent_ebot_dimcid : bitEventually .ebot .dimcid .D := by
  obtain ⟨k₁, h₁⟩ := col_dimcid_defect
  obtain ⟨k₂, h₂⟩ := col_dimcid_coop
  obtain ⟨k₃, h₃⟩ := col_dimcid_mirror_D
  refine ⟨k₁ + k₂ + k₃, fun k hk ↦ ?_⟩
  apply bitPlays_of_eq (instCode_ebot k _)
  obtain ⟨n₁, e₁⟩ := h₁ k (by omega)
  obtain ⟨n₂, e₂⟩ := h₂ k (by omega)
  obtain ⟨n₃, e₃⟩ := h₃ k (by omega)
  exact ⟨_, watch_falls' e₁ (by decide) (watch_falls' e₂ (by decide) (watch_falls' e₃ (by decide) (const_play 0 _ _ _)))⟩

end ArithS.Tau
