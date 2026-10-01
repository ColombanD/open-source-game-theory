import ArithS.Tau.Entangled.Mirror
import ArithS.Cells.PrudentMirror

/-!
# ArithS.Tau.Entangled.EBotPrudent — τ(Prudent) at the mirror cooperates: `ebot × prudent` is C (‡)

τ(EBot)'s third watch at the hypothesis `prudent` sims `inst prudent mirror = .sys [pm 1 mirror, mm 0] 0`: the
Prudent member probes "the mirror member cooperates with itself" and then runs the prudence check on the mirror's
instance at the defector — `inst mirror defect = .sim (.bot DefectBot) (.bot DefectBot)`, a CLOSED, `k`-FREE
program (unlike at every other hypothesis, where the frozen third party carries `k`: the §7 obstacle). So the
system's description is a fixed tower in `binNumeral k` and the engine's `prudent_mirror_plays_C` transfers: a box
of the outer probe AND of the prudence guard makes the Prudent member cooperate, the mirror member copies it,
and the prudence guard is a closed truth — the family `pQ (q_out ⋏ q_in)` (`loebSound_PMi`), the base
`Cells/PrudentMirror.lean`'s `pPM` on the member slots. The nested member needs its own kit (`NM`, `Sys2n`): the
two-level tower (`searchT1'`), the τ-order decided by the member itself above the threshold `⌜g⌝ + ⌜g^τ⌝ ≤ k`
(`nested_search_lt`), and the two-box search clause.
-/

set_option linter.constructorNameAsVariable false

namespace ArithS.Tau

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open LAct
open PD PD.Tau

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ### 0. Closed atoms in the thirteen-variable template -/

lemma eval_closedDesc13_V (c : ℕ) (b : Fin 14 → V) :
    Semiformula.Eval (s := stdReadingV V) b Empty.elim (closedDesc13 c) ↔ b 0 = (c : V) := by
  unfold closedDesc13 descF
  simp only [Semiformula.eval_ex, LogicalConnective.HomClass.map_and, LogicalConnective.Prop.and_eq,
    Semiformula.eval_rel, Semiformula.eval_substs, eval_relDesc_V, stdReadingV_rel_eq, Function.comp_def,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_succ, Matrix.vecHead, Matrix.vecTail, Semiterm.val_bvar, val_cl_V, val_canonicalMeta_V]
  constructor
  · rintro ⟨x, rfl, h⟩
    rwa [revalue_val_desc_V] at h
  · intro h
    exact ⟨_, rfl, by rw [revalue_val_desc_V]; exact h⟩

/-- The template of a probe over a closed, pronoun-free program `P`, at any thirteen-slot valuation. -/
theorem eval_template13_closed (P : PD.Prog) (hP : ProperPlayer P) (hns : noSelfIdxP P = true) (a : PD.Action) (b : Fin 13 → V) :
    Semiformula.Eval (s := stdReadingV V) b Empty.elim (template13 (.plays P P a)) ↔
      ∃ n, EvalGraph n ((progCode P : ℕ) : V) ((progCode P : ℕ) : V) ((progCode P : ℕ) : V) (actCode a : V) := by
  rw [template13_plays]
  unfold progGraph13
  rw [progAux13_of_ne hP.1 hP.2 (pronounP_eq_false_of_noSelfIdxP hns)]
  simp only [Semiformula.eval_substs, Semiformula.eval_ex, LogicalConnective.HomClass.map_and,
    LogicalConnective.Prop.and_eq, eval_closedDesc13_V, eval_evalG_V, Function.comp_def, Matrix.cons_val,
    Semiterm.val_bvar, val_cl_V, val_actT_V]
  constructor
  · rintro ⟨x, y, N, rfl, rfl, h⟩
    exact ⟨N, h⟩
  · rintro ⟨N, h⟩
    exact ⟨_, _, N, rfl, rfl, h⟩

lemma lMap_swap_closedDesc13 (c : ℕ) : Semiformula.lMap swap (closedDesc13 c) = closedDesc13 (transposeCode c) := by
  unfold closedDesc13
  rw [lMap_swap_descF, lMap_swap_cl, lMap_swap_cl, lMap_swap_cl, lMap_swap_canonicalMeta, lMap_swap_revalueUMeta, lMap_swap_revalueWMeta]
  rfl

/-- τ on the template of a closed probe over a fragment program. -/
theorem lMap_swap_template13_closed (P : PD.Prog) (hP : ProperPlayer P) (hns : noSelfIdxP P = true) (hf : fragP P = true)
    (hPt : ProperPlayer P.transpose) (hnst : noSelfIdxP P.transpose = true) (a : PD.Action) :
    Semiformula.lMap swap (template13 (.plays P P a)) = template13 (.plays P.transpose P.transpose a.swap) := by
  rw [template13_plays, template13_plays]
  unfold progGraph13
  rw [progAux13_of_ne hP.1 hP.2 (pronounP_eq_false_of_noSelfIdxP hns),
    progAux13_of_ne hPt.1 hPt.2 (pronounP_eq_false_of_noSelfIdxP hnst)]
  simp only [Semiformula.lMap_exs, LogicalConnective.HomClass.map_and, Semiformula.lMap_subst, lMap_swap_evalG,
    lMap_swap_closedDesc13, transposeCode_progCode P hf]
  congr 4
  · congr 1; funext i; fin_cases i <;> rfl
  · congr 1
    · congr 1; funext i; fin_cases i <;> rfl
    · congr 1
      funext i
      fin_cases i
      · rfl
      · rfl
      · rfl
      · rfl
      · show Semiterm.lMap swap (cl (actT (actCode a))) = cl (actT (actCode a.swap))
        rw [lMap_swap_cl, lMap_swap_actT, actCode_swap]

/-! ### 1. The nested member -/

/-- A nested member: `pSearch k ⌜g⌝ (pSearch k ⌜g'⌝ (pConst a) (pConst (1 - a))) (pConst (1 - a))` — Prudent's
shape (`a = 0`) and its transposition (`a = 1`). -/
structure NM where
  g : Semisentence LAct 13
  g' : Semisentence LAct 13
  a : ℕ
  ha : a = 0 ∨ a = 1

namespace NM

/-- The inner searcher as a simple member. -/
def inn (m : NM) : SM := ⟨m.g', m.a, m.ha⟩

noncomputable def code (m : NM) (k : V) : V :=
  pSearch k ((⌜m.g⌝ : ℕ) : V) (m.inn.code k) (pConst ((1 - m.a : ℕ) : V))

noncomputable def tr (m : NM) : NM := ⟨Semiformula.lMap swap m.g, Semiformula.lMap swap m.g', 1 - m.a, by rcases m.ha with h | h <;> simp [h]⟩

lemma tr_inn (m : NM) : m.tr.inn = m.inn.tr := rfl

theorem transposeCode_code (m : NM) (k : V) : transposeCode (m.code k) = m.tr.code k := by
  unfold code transposeCode
  rw [revalue_search, revalue_const, revalueTemplate_cast_quote]
  show pSearch k _ (revalue 1 0 (m.inn.code k)) (pConst (swapAction _)) = _
  rw [show revalue 1 0 (m.inn.code k) = transposeCode (m.inn.code k) from rfl, SM.transposeCode_code,
    swapAction_cast' m.a m.ha]
  show pSearch k _ (m.inn.tr.code k) (pConst (m.a : V)) = pSearch k _ (m.tr.inn.code k) (pConst ((1 - m.tr.a : ℕ) : V))
  rw [tr_inn, show (1 - m.tr.a : ℕ) = m.a from by rcases m.ha with h | h <;> simp [tr, h]]
  rfl

/-- `m.code k` with the inner part exposed, for `nested_search_lt`. -/
lemma code_eq_inner (m : NM) (k : V) :
    m.code k = ppair 6 (ppair k (ppair ((⌜m.g⌝ : ℕ) : V) (ppair (ppair 6 (ppair k (m.inn.inner : V)) + 1) (pConst ((1 - m.a : ℕ) : V))))) + 1 := by
  unfold code
  rw [SM.code_eq_inner]; rfl

/-- The threshold above which the τ-order of the nested member is uniform: the two outer template codes. -/
noncomputable def K (m : NM) : ℕ := (⌜m.g⌝ : ℕ) + (⌜Semiformula.lMap swap m.g⌝ : ℕ)

lemma K_def (m : NM) : m.K = (⌜m.g⌝ : ℕ) + (⌜Semiformula.lMap swap m.g⌝ : ℕ) := rfl

attribute [irreducible] K

lemma quote_g_le_of_K {m : NM} {k : V} (hk : (m.K : V) ≤ k) : ((⌜m.g⌝ : ℕ) : V) ≤ k := by
  rw [K_def] at hk; push_cast at hk; exact le_trans le_self_add hk
lemma quote_gT_le_of_K {m : NM} {k : V} (hk : (m.K : V) ≤ k) : ((⌜Semiformula.lMap swap m.g⌝ : ℕ) : V) ≤ k := by
  rw [K_def] at hk; push_cast at hk; exact le_trans le_add_self hk

lemma pConst_sub_succ_le (m : NM) : pConst ((1 - m.a : ℕ) : V) + 1 ≤ (14 : V) := by
  rcases m.ha with h | h
  · simp only [h, Nat.sub_zero, Nat.cast_one]; exact pConst_one_succ_le
  · simp only [h, Nat.sub_self, Nat.cast_zero]; exact pConst_zero_succ_le

/-- The decision: the inner searcher's inner part below its transposed one. -/
def orig (m : NM) : Prop := m.inn.inner < m.inn.tr.inner

theorem code_lt_tr {m : NM} {k : V} (hk : (m.K : V) ≤ k) (h : m.orig) : m.code k < m.tr.code k := by
  rw [code_eq_inner, code_eq_inner, tr_inn]
  exact nested_search_lt (lt_iff_succ_le.mp (Nat.cast_lt.mpr h)) (quote_g_le_of_K hk) (pConst_sub_succ_le m)

theorem tr_lt_code {m : NM} {k : V} (hk : (m.K : V) ≤ k) (h : ¬ m.orig) : m.tr.code k < m.code k := by
  have h' : m.inn.tr.inner < m.inn.inner := lt_of_le_of_ne (not_lt.mp h) (Ne.symm (SM.inner_ne_tr _))
  rw [code_eq_inner, code_eq_inner, tr_inn]
  exact nested_search_lt (lt_iff_succ_le.mp (Nat.cast_lt.mpr h')) (quote_gT_le_of_K hk) (pConst_sub_succ_le m.tr)

/-- The one-variable term of the nested member. -/
noncomputable def T1 (m : NM) : Semiterm ℒₒᵣ Empty 1 := searchT1' (⌜m.g⌝ : ℕ) m.inn.T1 (pConst (1 - m.a))

lemma val_T1_V (m : NM) (k : V) : (m.T1).val (s := standardModel V) ![k] Empty.elim = m.code k := by
  rw [T1, val_searchT1'_V, SM.val_T1_V, cast_pConst]; rfl

lemma termSubst_T1 (m : NM) (k : V) :
    termSubst LAct (binNumeral k ∷ (0 : V)) (⌜(Rew.emb m.T1 : SyntacticSemiterm ℒₒᵣ 1)⌝ : V) = codeTerm (m.code k) := by
  rw [T1, quote_emb_searchT1', SM.T1, quote_emb_searchT1]
  have h5 : IsUTerm LAct (ppairTerm (binNumeral 6) (ppairTerm (^#0) (ppairTerm (binNumeral ((⌜m.inn.g⌝ : ℕ) : V))
      (ppairTerm (codeTerm ((pConst m.inn.a : ℕ) : V)) (codeTerm ((pConst (1 - m.inn.a) : ℕ) : V))))) ^+ 𝟏) :=
    qqAdd_uterm_LAct (ppairTerm_uterm_LAct (uterm_binNumeral _) (ppairTerm_uterm_LAct bvar_zero_uterm
      (ppairTerm_uterm_LAct (uterm_binNumeral _) (ppairTerm_uterm_LAct (codeTerm_semiterm_LAct 0 _).isUTerm
        (codeTerm_semiterm_LAct 0 _).isUTerm)))) uterm_one
  rw [termSubst_tower' k _ _ h5 (termSubst_tower k _ _ _), cast_pConst, cast_pConst, cast_pConst]
  rfl

end NM

/-! ### 2. The nested system: a nested member `0`, a closed τ-fixed member `1` -/

structure Sys2n where
  m₀ : NM
  P : ℕ
  hP : transposeCode P = P

namespace Sys2n

noncomputable def D (S : Sys2n) (k : V) : V := pCons (S.m₀.code k) (pCons (S.P : V) pNil)
noncomputable def code (S : Sys2n) (j : ℕ) (k : V) : V := pSys (S.D k) (j : V)
noncomputable def tr (S : Sys2n) : Sys2n := ⟨S.m₀.tr, S.P, S.hP⟩
lemma tr_m₀ (S : Sys2n) : S.tr.m₀ = S.m₀.tr := rfl

lemma transposeCode_P (S : Sys2n) : transposeCode (S.P : V) = (S.P : V) := by rw [← cast_transposeCode, S.hP]

theorem transposeCode_D (S : Sys2n) (k : V) : transposeCode (S.D k) = S.tr.D k := by
  unfold D transposeCode
  rw [revalue_cons, revalue_cons, revalue_nil]
  show pCons (transposeCode _) (pCons (transposeCode _) pNil) = _
  rw [NM.transposeCode_code, transposeCode_P]; rfl

theorem transposeCode_code (S : Sys2n) (j : ℕ) (k : V) : transposeCode (S.code j k) = S.tr.code j k := by
  unfold code transposeCode
  rw [revalue_sys]
  show pSys (transposeCode _) _ = _
  rw [transposeCode_D]

def orig (S : Sys2n) : Prop := S.m₀.orig
noncomputable def K (S : Sys2n) : ℕ := S.m₀.K

theorem code_lt_tr {S : Sys2n} {k : V} (hk : (S.K : V) ≤ k) (h : S.orig) (j : ℕ) : S.code j k < S.tr.code j k := by
  unfold code D
  exact sys2_lt_of_member0 (NM.code_lt_tr hk h)

theorem tr_lt_code {S : Sys2n} {k : V} (hk : (S.K : V) ≤ k) (h : ¬ S.orig) (j : ℕ) : S.tr.code j k < S.code j k := by
  unfold code D
  exact sys2_lt_of_member0 (NM.tr_lt_code hk h)

open scoped Classical in
noncomputable def can (S : Sys2n) : Sys2n := if S.orig then S else S.tr
open scoped Classical in
noncomputable def uT (S : Sys2n) : ClosedSemiterm LAct 0 := if S.orig then cterm Act.C else cterm Act.D
open scoped Classical in
noncomputable def wT (S : Sys2n) : ClosedSemiterm LAct 0 := if S.orig then cterm Act.D else cterm Act.C

theorem canonical_code {S : Sys2n} {k : V} (hk : (S.K : V) ≤ k) (j : ℕ) : canonical (S.code j k) = S.can.code j k := by
  unfold can
  by_cases h : S.orig
  · rw [if_pos h, canonical_of_lt (by rw [transposeCode_code]; exact code_lt_tr hk h j)]
  · rw [if_neg h, canonical_of_gt (by rw [transposeCode_code]; exact tr_lt_code hk h j), transposeCode_code]

theorem revalueU_code {S : Sys2n} {k : V} (hk : (S.K : V) ≤ k) (j : ℕ) : revalueU (S.code j k) = (⌜S.uT⌝ : V) := by
  unfold revalueU uT
  rw [transposeCode_code]
  by_cases h : S.orig
  · rw [if_pos (code_lt_tr hk h j), if_pos h, quote_cterm_C]
  · rw [if_neg (lt_asymm (tr_lt_code hk h j)), if_pos (tr_lt_code hk h j), if_neg h, quote_cterm_D]

theorem revalueW_code {S : Sys2n} {k : V} (hk : (S.K : V) ≤ k) (j : ℕ) : revalueW (S.code j k) = (⌜S.wT⌝ : V) := by
  unfold revalueW wT
  rw [transposeCode_code]
  by_cases h : S.orig
  · rw [if_pos (code_lt_tr hk h j), if_pos h, quote_cterm_D]
  · rw [if_neg (lt_asymm (tr_lt_code hk h j)), if_pos (tr_lt_code hk h j), if_neg h, quote_cterm_C]

theorem revalue_val_uT_wT (S : Sys2n) (k : V) (j : ℕ) :
    revalue (S.uT.val (s := stdReadingV V) ![] Empty.elim) (S.wT.val (s := stdReadingV V) ![] Empty.elim)
      (S.can.code j k) = S.code j k := by
  unfold uT wT can
  by_cases h : S.orig
  · rw [if_pos h, if_pos h, if_pos h, val_cterm_C_V, val_cterm_D_V, revalue_zero_one]
  · rw [if_neg h, if_neg h, if_neg h, val_cterm_D_V, val_cterm_C_V]
    show transposeCode (S.tr.code j k) = _
    rw [← transposeCode_code S j k, transposeCode_transposeCode]

theorem revalue_val_uT_wT_swap (S : Sys2n) (k : V) (j : ℕ) :
    revalue ((Semiterm.lMap swap S.uT).val (s := stdReadingV V) ![] Empty.elim)
      ((Semiterm.lMap swap S.wT).val (s := stdReadingV V) ![] Empty.elim) (S.can.code j k) = S.tr.code j k := by
  unfold uT wT can
  by_cases h : S.orig
  · rw [if_pos h, if_pos h, if_pos h, lMap_swap_cterm_C, lMap_swap_cterm_D, val_cterm_D_V, val_cterm_C_V]
    show transposeCode (S.code j k) = _
    rw [transposeCode_code]
  · rw [if_neg h, if_neg h, if_neg h, lMap_swap_cterm_D, lMap_swap_cterm_C, val_cterm_C_V, val_cterm_D_V,
      revalue_zero_one]

/-! #### The towers -/

noncomputable def PT1 (S : Sys2n) : Semiterm ℒₒᵣ Empty 1 := Rew.bShift (codeTermMeta S.P)
lemma val_PT1_V (S : Sys2n) (k : V) : S.PT1.val (s := standardModel V) ![k] Empty.elim = (S.P : V) := by
  rw [PT1, val_bShift₁_V, val_codeTermMeta_V]
lemma termSubst_PT1 (S : Sys2n) (w : V) :
    termSubst LAct w (⌜(Rew.emb S.PT1 : SyntacticSemiterm ℒₒᵣ 1)⌝ : V) = codeTerm (S.P : V) := by
  rw [PT1, quote_emb_bShift, ← Semiterm.empty_quote_def, quote_codeTermMeta, termSubst_closed _ (codeTerm_semiterm_LAct 0 _)]

noncomputable def T1 (S : Sys2n) (j : ℕ) : Semiterm ℒₒᵣ Empty 1 := sysT1 (consT1 S.m₀.T1 (consT1 S.PT1 nilT1)) j

lemma val_T1_V (S : Sys2n) (j : ℕ) (k : V) : (S.T1 j).val (s := standardModel V) ![k] Empty.elim = S.code j k := by
  rw [T1, val_sysT1_V, val_consT1_V, val_consT1_V, val_nilT1_V, NM.val_T1_V, val_PT1_V]; rfl

lemma termSubst_T1 (S : Sys2n) (j : ℕ) (k : V) :
    termSubst LAct (binNumeral k ∷ (0 : V)) (⌜(Rew.emb (S.T1 j) : SyntacticSemiterm ℒₒᵣ 1)⌝ : V) = codeTerm (S.code j k) := by
  rw [T1]
  exact termSubst_sysT1 _ (termSubst_consT1 _ (NM.termSubst_T1 _ _) (termSubst_consT1 _ (termSubst_PT1 _ _) (termSubst_nilT1 _))) j

noncomputable def TM (S : Sys2n) (j : ℕ) : Semiterm LAct Empty 1 := Semiterm.lMap emb (S.can.T1 j)
noncomputable def TX (S : Sys2n) (j : ℕ) : Semiterm LAct Empty 1 := Semiterm.lMap emb (botT1 (S.can.T1 j))
lemma lMap_swap_TM (S : Sys2n) (j : ℕ) : Semiterm.lMap swap (S.TM j) = S.TM j := term_lMap_swap_emb _
lemma lMap_swap_TX (S : Sys2n) (j : ℕ) : Semiterm.lMap swap (S.TX j) = S.TX j := term_lMap_swap_emb _

theorem val_TM_V {S : Sys2n} {k : V} (hk : (S.K : V) ≤ k) (j : ℕ) :
    (S.TM j).val (s := stdReadingV V) ![k] Empty.elim = canonical (S.code j k) := by
  unfold TM; rw [Semiterm.val_lMap, stdReadingV_lMap_emb, val_T1_V, canonical_code hk]
theorem val_TX_V {S : Sys2n} {k : V} (hk : (S.K : V) ≤ k) (j : ℕ) :
    (S.TX j).val (s := stdReadingV V) ![k] Empty.elim = canonical (pBot (S.code j k)) := by
  unfold TX; rw [Semiterm.val_lMap, stdReadingV_lMap_emb, val_botT1_V, val_T1_V, canonical_pBot, canonical_code hk]
theorem hX_TM {S : Sys2n} {k : V} (hk : (S.K : V) ≤ k) (j : ℕ) :
    termSubst LAct (binNumeral k ∷ (0 : V)) (⌜(Rew.emb (S.TM j) : SyntacticSemiterm LAct 1)⌝ : V) =
      codeTerm (canonical (S.code j k)) := by
  unfold TM; rw [term_emb_lMap_emb_n, quote_term_lMap_emb, termSubst_T1, canonical_code hk]
theorem hX_TX {S : Sys2n} {k : V} (hk : (S.K : V) ≤ k) (j : ℕ) :
    termSubst LAct (binNumeral k ∷ (0 : V)) (⌜(Rew.emb (S.TX j) : SyntacticSemiterm LAct 1)⌝ : V) =
      codeTerm (canonical (pBot (S.code j k))) := by
  unfold TX
  rw [term_emb_lMap_emb_n, quote_term_lMap_emb, termSubst_botT1 _ (termSubst_T1 _ _ _), canonical_pBot, canonical_code hk]

theorem descVal_TM {S : Sys2n} {k : V} (hk : (S.K : V) ≤ k) (j : ℕ) : descVal (S.TM j) S.uT S.wT k = S.code j k := by
  rw [descVal_def, val_TM_V hk, canonical_code hk, revalue_val_uT_wT]
theorem descVal_TM_T {S : Sys2n} {k : V} (hk : (S.K : V) ≤ k) (j : ℕ) :
    descVal (Semiterm.lMap swap (S.TM j)) (Semiterm.lMap swap S.uT) (Semiterm.lMap swap S.wT) k = S.tr.code j k := by
  rw [descVal_def, lMap_swap_TM, val_TM_V hk, canonical_code hk, revalue_val_uT_wT_swap]
theorem descVal_TX {S : Sys2n} {k : V} (hk : (S.K : V) ≤ k) (j : ℕ) : descVal (S.TX j) S.uT S.wT k = pBot (S.code j k) := by
  rw [descVal_def, val_TX_V hk, canonical_pBot, revalue_bot, canonical_code hk, revalue_val_uT_wT]
theorem descVal_TX_T {S : Sys2n} {k : V} (hk : (S.K : V) ≤ k) (j : ℕ) :
    descVal (Semiterm.lMap swap (S.TX j)) (Semiterm.lMap swap S.uT) (Semiterm.lMap swap S.wT) k = pBot (S.tr.code j k) := by
  rw [descVal_def, lMap_swap_TX, val_TX_V hk, canonical_pBot, revalue_bot, canonical_code hk, revalue_val_uT_wT_swap]

/-! #### The two guards of the nested member, their instance equations and the two-box search clause -/

lemma code_zero (S : Sys2n) (k : V) : S.code 0 k = pSys (S.D k) 0 := by unfold code; rw [Nat.cast_zero]
lemma code_one (S : Sys2n) (k : V) : S.code 1 k = pSys (S.D k) 1 := by unfold code; rw [Nat.cast_one]

/-- The outer guard, consulted in the frame `(i, i')`. -/
noncomputable def qo (S : Sys2n) (i i' : ℕ) : Semisentence LAct 1 :=
  qT13 S.m₀.g (S.TX i) S.uT S.wT (S.TX i') S.uT S.wT (S.TM 0) S.uT S.wT (S.TM 1) S.uT S.wT
/-- The inner (prudence) guard, consulted in the frame `(i, i')`. -/
noncomputable def qi (S : Sys2n) (i i' : ℕ) : Semisentence LAct 1 :=
  qT13 S.m₀.g' (S.TX i) S.uT S.wT (S.TX i') S.uT S.wT (S.TM 0) S.uT S.wT (S.TM 1) S.uT S.wT

/-- The generic instance equation of the system, for any thirteen-variable template `g`. -/
theorem guard_eq_instB_of {S : Sys2n} {k : V} (hk : (S.K : V) ≤ k) (g : Semisentence LAct 13) (i i' : ℕ) :
    guardCodeB (sysCloseTemplate (S.D k) ((⌜g⌝ : ℕ) : V)) (pBot (S.code i k)) (pBot (S.code i' k)) k =
      instB (⌜qT13 g (S.TX i) S.uT S.wT (S.TX i') S.uT S.wT (S.TM 0) S.uT S.wT (S.TM 1) S.uT S.wT⌝ : V) k := by
  rw [coe_quote_sentence₁₃]
  refine guardCodeB_sysClose_eq_instB _ k (S.D k) _ _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact hX_TX hk i
  · rw [revalueU_pBot, revalueU_code hk]
  · rw [revalueW_pBot, revalueW_code hk]
  · exact hX_TX hk i'
  · rw [revalueU_pBot, revalueU_code hk]
  · rw [revalueW_pBot, revalueW_code hk]
  · rw [← code_zero]; exact hX_TM hk 0
  · rw [← code_zero, revalueU_code hk]
  · rw [← code_zero, revalueW_code hk]
  · rw [← code_one]; exact hX_TM hk 1
  · rw [← code_one, revalueU_code hk]
  · rw [← code_one, revalueW_code hk]

theorem qo_eq_instB {S : Sys2n} {k : V} (hk : (S.K : V) ≤ k) (i i' : ℕ) :
    guardCodeB (sysCloseTemplate (S.D k) ((⌜S.m₀.g⌝ : ℕ) : V)) (pBot (S.code i k)) (pBot (S.code i' k)) k =
      instB (⌜S.qo i i'⌝ : V) k := guard_eq_instB_of hk _ i i'
theorem qi_eq_instB {S : Sys2n} {k : V} (hk : (S.K : V) ≤ k) (i i' : ℕ) :
    guardCodeB (sysCloseTemplate (S.D k) ((⌜S.m₀.g'⌝ : ℕ) : V)) (pBot (S.code i k)) (pBot (S.code i' k)) k =
      instB (⌜S.qi i i'⌝ : V) k := guard_eq_instB_of hk _ i i'

lemma listGet_D_zero (S : Sys2n) (k : V) : listGet (S.D k) 0 = S.m₀.code k + 1 := by unfold D; rw [listGet_cons_zero]
lemma listGet_D_one (S : Sys2n) (k : V) : listGet (S.D k) 1 = (S.P : V) + 1 := by
  unfold D
  conv_lhs => rw [show (1 : V) = 0 + 1 by simp]
  rw [listGet_cons_succ, listGet_cons_zero]

lemma sysCloseCode_m₀ (S : Sys2n) (k : V) :
    sysCloseCode (S.D k) (S.m₀.code k) =
      pSearch k (sysCloseTemplate (S.D k) ((⌜S.m₀.g⌝ : ℕ) : V))
        (pSearch k (sysCloseTemplate (S.D k) ((⌜S.m₀.g'⌝ : ℕ) : V)) (pConst (S.m₀.a : V)) (pConst ((1 - S.m₀.a : ℕ) : V)))
        (pConst ((1 - S.m₀.a : ℕ) : V)) := by
  unfold NM.code SM.code
  rw [sysCloseCode_search, sysCloseCode_search, sysCloseCode_const, sysCloseCode_const, sysCloseCode_const]; rfl

/-- **The two-box search clause**: both guards found in the frame `(me, opp)` make the bot-wrapped nested member
play its inner then-action (fuel `5`). -/
theorem member_then2_V (S : Sys2n) (k me opp : V)
    (ho : LenBox TAct k (guardCodeB (sysCloseTemplate (S.D k) ((⌜S.m₀.g⌝ : ℕ) : V)) me opp k))
    (hi : LenBox TAct k (guardCodeB (sysCloseTemplate (S.D k) ((⌜S.m₀.g'⌝ : ℕ) : V)) me opp k)) :
    EvalGraph 5 me opp (pBot (S.code 0 k)) (S.m₀.a : V) := by
  rw [show (5 : V) = 4 + 1 by norm_num, EvalGraph.bot_iff,
    show (4 : V) = 3 + 1 from three_add_one_eq_four.symm, code_zero, EvalGraph.sys_iff]
  refine ⟨_, listGet_D_zero S k, ?_⟩
  rw [sysCloseCode_m₀, show (3 : V) = 2 + 1 from two_add_one_eq_three.symm, EvalGraph.search_iff]
  refine Or.inl ⟨ho, ?_⟩
  rw [show (2 : V) = 1 + 1 from one_add_one_eq_two.symm, EvalGraph.search_iff]
  exact Or.inl ⟨hi, by rw [show (1 : V) = 0 + 1 by simp, EvalGraph.const_iff]⟩

theorem plays_of_boxes {S : Sys2n} {k : V} (hk : (S.K : V) ≤ k) (i i' : ℕ)
    (ho : LenBox TAct k (instB (⌜S.qo i i'⌝ : V) k)) (hi : LenBox TAct k (instB (⌜S.qi i i'⌝ : V) k)) :
    EvalGraph 5 (pBot (S.code i k)) (pBot (S.code i' k)) (pBot (S.code 0 k)) (S.m₀.a : V) := by
  rw [← qo_eq_instB hk] at ho
  rw [← qi_eq_instB hk] at hi
  exact member_then2_V S k _ _ ho hi

/-- **The mirror member copies the nested member's self-play**: the closed member `1` is `sim B₀ B₀`. -/
theorem mirror_copies_V (S : Sys2n) (hP : S.P = progCode (mm 0)) (n me opp a : V)
    (h : EvalGraph n (pBot (S.code 0 k)) (pBot (S.code 0 k)) (pBot (S.code 0 k)) a) :
    EvalGraph (n + 1 + 1 + 1) me opp (pBot (S.code 1 k)) a := by
  rw [EvalGraph.bot_iff, code_one, EvalGraph.sys_iff]
  refine ⟨_, listGet_D_one S k, ?_⟩
  have hPc : (S.P : V) = pSim (pBot (pSelfIdx 0)) (pBot (pSelfIdx 0)) := by
    rw [hP, show progCode (mm 0) = pSim (pBot (pSelfIdx 0)) (pBot (pSelfIdx 0)) by simp [mm], cast_pSim, cast_pBot,
      cast_pSelfIdx, Nat.cast_zero]
  rw [hPc, sysCloseCode_sim, sysCloseCode_bot, sysCloseCode_selfIdx, EvalGraph.sim_iff, substCode_bot, ← code_zero]
  exact h

/-! #### The transposed system -/

theorem canonical_tr_code {S : Sys2n} {k : V} (hk : (S.K : V) ≤ k) (j : ℕ) : canonical (S.tr.code j k) = S.can.code j k := by
  rw [← transposeCode_code, canonical_transposeCode, canonical_code hk]

theorem revalueU_tr_code {S : Sys2n} {k : V} (hk : (S.K : V) ≤ k) (j : ℕ) :
    revalueU (S.tr.code j k) = (⌜Semiterm.lMap swap S.uT⌝ : V) := by
  have e : transposeCode (S.tr.code j k) = S.code j k := by rw [← transposeCode_code, transposeCode_transposeCode]
  unfold revalueU uT
  rw [e]
  by_cases h : S.orig
  · rw [if_neg (lt_asymm (code_lt_tr hk h j)), if_pos (code_lt_tr hk h j), if_pos h, lMap_swap_cterm_C, quote_cterm_D]
  · rw [if_pos (tr_lt_code hk h j), if_neg h, lMap_swap_cterm_D, quote_cterm_C]

theorem revalueW_tr_code {S : Sys2n} {k : V} (hk : (S.K : V) ≤ k) (j : ℕ) :
    revalueW (S.tr.code j k) = (⌜Semiterm.lMap swap S.wT⌝ : V) := by
  have e : transposeCode (S.tr.code j k) = S.code j k := by rw [← transposeCode_code, transposeCode_transposeCode]
  unfold revalueW wT
  rw [e]
  by_cases h : S.orig
  · rw [if_neg (lt_asymm (code_lt_tr hk h j)), if_pos (code_lt_tr hk h j), if_pos h, lMap_swap_cterm_D, quote_cterm_C]
  · rw [if_pos (tr_lt_code hk h j), if_neg h, lMap_swap_cterm_C, quote_cterm_D]

/-- The transposed instance equation, for any template `g` (used with `lMap swap S.m₀.g` and `lMap swap S.m₀.g'`). -/
theorem tr_guard_eq_instB_of {S : Sys2n} {k : V} (hk : (S.K : V) ≤ k) (g : Semisentence LAct 13) (i i' : ℕ) :
    guardCodeB (sysCloseTemplate (S.tr.D k) ((⌜Semiformula.lMap swap g⌝ : ℕ) : V)) (pBot (S.tr.code i k)) (pBot (S.tr.code i' k)) k =
      instB (⌜Semiformula.lMap swap (qT13 g (S.TX i) S.uT S.wT (S.TX i') S.uT S.wT (S.TM 0) S.uT S.wT (S.TM 1) S.uT S.wT)⌝ : V) k := by
  rw [coe_quote_sentence₁₃, lMap_swap_qT13, lMap_swap_TX, lMap_swap_TX, lMap_swap_TM, lMap_swap_TM]
  refine guardCodeB_sysClose_eq_instB _ k (S.tr.D k) _ _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hX_TX hk, canonical_pBot, canonical_pBot, canonical_tr_code hk, canonical_code hk]
  · rw [revalueU_pBot, revalueU_tr_code hk]
  · rw [revalueW_pBot, revalueW_tr_code hk]
  · rw [hX_TX hk, canonical_pBot, canonical_pBot, canonical_tr_code hk, canonical_code hk]
  · rw [revalueU_pBot, revalueU_tr_code hk]
  · rw [revalueW_pBot, revalueW_tr_code hk]
  · rw [hX_TM hk, ← code_zero, canonical_tr_code hk, canonical_code hk]
  · rw [← code_zero]; exact (revalueU_tr_code hk 0).symm
  · rw [← code_zero]; exact (revalueW_tr_code hk 0).symm
  · rw [hX_TM hk, ← code_one, canonical_tr_code hk, canonical_code hk]
  · rw [← code_one]; exact (revalueU_tr_code hk 1).symm
  · rw [← code_one]; exact (revalueW_tr_code hk 1).symm

theorem tr_plays_of_boxes {S : Sys2n} {k : V} (hk : (S.K : V) ≤ k) (i i' : ℕ)
    (ho : LenBox TAct k (instB (⌜Semiformula.lMap swap (S.qo i i')⌝ : V) k))
    (hi : LenBox TAct k (instB (⌜Semiformula.lMap swap (S.qi i i')⌝ : V) k)) :
    EvalGraph 5 (pBot (S.tr.code i k)) (pBot (S.tr.code i' k)) (pBot (S.tr.code 0 k)) (S.tr.m₀.a : V) := by
  unfold qo at ho
  unfold qi at hi
  rw [← tr_guard_eq_instB_of hk] at ho hi
  exact member_then2_V S.tr k _ _ ho hi

/-! #### The truth equations -/

noncomputable def vals (S : Sys2n) (i i' : ℕ) (k : V) : Fin 13 → V :=
  ![(S.TX i).val (s := stdReadingV V) ![k] Empty.elim, S.uT.val (s := stdReadingV V) ![] Empty.elim,
    S.wT.val (s := stdReadingV V) ![] Empty.elim, (S.TX i').val (s := stdReadingV V) ![k] Empty.elim,
    S.uT.val (s := stdReadingV V) ![] Empty.elim, S.wT.val (s := stdReadingV V) ![] Empty.elim, k,
    (S.TM 0).val (s := stdReadingV V) ![k] Empty.elim, S.uT.val (s := stdReadingV V) ![] Empty.elim,
    S.wT.val (s := stdReadingV V) ![] Empty.elim, (S.TM 1).val (s := stdReadingV V) ![k] Empty.elim,
    S.uT.val (s := stdReadingV V) ![] Empty.elim, S.wT.val (s := stdReadingV V) ![] Empty.elim]

noncomputable def valsT (S : Sys2n) (i i' : ℕ) (k : V) : Fin 13 → V :=
  ![(S.TX i).val (s := stdReadingV V) ![k] Empty.elim, (Semiterm.lMap swap S.uT).val (s := stdReadingV V) ![] Empty.elim,
    (Semiterm.lMap swap S.wT).val (s := stdReadingV V) ![] Empty.elim, (S.TX i').val (s := stdReadingV V) ![k] Empty.elim,
    (Semiterm.lMap swap S.uT).val (s := stdReadingV V) ![] Empty.elim, (Semiterm.lMap swap S.wT).val (s := stdReadingV V) ![] Empty.elim, k,
    (S.TM 0).val (s := stdReadingV V) ![k] Empty.elim, (Semiterm.lMap swap S.uT).val (s := stdReadingV V) ![] Empty.elim,
    (Semiterm.lMap swap S.wT).val (s := stdReadingV V) ![] Empty.elim, (S.TM 1).val (s := stdReadingV V) ![k] Empty.elim,
    (Semiterm.lMap swap S.uT).val (s := stdReadingV V) ![] Empty.elim, (Semiterm.lMap swap S.wT).val (s := stdReadingV V) ![] Empty.elim]

omit [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
lemma eval_qT_iff_vals (S : Sys2n) (g : Semisentence LAct 13) (i i' : ℕ) (k : V) :
    Semiformula.Eval (s := stdReadingV V) ![k] Empty.elim
      (qT13 g (S.TX i) S.uT S.wT (S.TX i') S.uT S.wT (S.TM 0) S.uT S.wT (S.TM 1) S.uT S.wT) ↔
      Semiformula.Eval (s := stdReadingV V) (S.vals i i' k) Empty.elim g := by
  unfold vals; exact eval_qT13_iff _ _ _ _ _ _ _ _ _ _ _ _ _ k

omit [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
lemma eval_swap_qT_iff_valsT (S : Sys2n) (g : Semisentence LAct 13) (i i' : ℕ) (k : V) :
    Semiformula.Eval (s := stdReadingV V) ![k] Empty.elim
      (Semiformula.lMap swap (qT13 g (S.TX i) S.uT S.wT (S.TX i') S.uT S.wT (S.TM 0) S.uT S.wT (S.TM 1) S.uT S.wT)) ↔
      Semiformula.Eval (s := stdReadingV V) (S.valsT i i' k) Empty.elim (Semiformula.lMap swap g) := by
  rw [lMap_swap_qT13, lMap_swap_TX, lMap_swap_TX, lMap_swap_TM, lMap_swap_TM]
  unfold valsT; exact eval_qT13_iff _ _ _ _ _ _ _ _ _ _ _ _ _ k

lemma vals_mem1 {S : Sys2n} {k : V} (hk : (S.K : V) ≤ k) (i i' : ℕ) : memVal (S.vals i i' k) 1 = S.code 1 k := by
  rw [memVal_one]; have := descVal_TM hk (S := S) (k := k) 1; rw [descVal_def] at this; exact this
lemma valsT_mem1 {S : Sys2n} {k : V} (hk : (S.K : V) ≤ k) (i i' : ℕ) : memVal (S.valsT i i' k) 1 = S.tr.code 1 k := by
  rw [memVal_one]; have := descVal_TM_T hk (S := S) (k := k) 1; rw [descVal_def, lMap_swap_TM] at this; exact this

/-- The outer guard (the mirror member's self-cooperation) in the standard reading. -/
theorem eval_qo {S : Sys2n} {k : V} (hk : (S.K : V) ≤ k) (hg : S.m₀.g = template13 (entDmG 1)) (i i' : ℕ) :
    Semiformula.Eval (s := stdReadingV V) ![k] Empty.elim (S.qo i i') ↔
      ∃ n, EvalGraph n (pBot (S.code 1 k)) (pBot (S.code 1 k)) (pBot (S.code 1 k)) (actCode .C : V) := by
  unfold qo
  rw [eval_qT_iff_vals, hg, eval_template13_partner 1 (by decide), vals_mem1 hk]

theorem eval_qo_swap {S : Sys2n} {k : V} (hk : (S.K : V) ≤ k) (hg : S.m₀.g = template13 (entDmG 1)) (i i' : ℕ) :
    Semiformula.Eval (s := stdReadingV V) ![k] Empty.elim (Semiformula.lMap swap (S.qo i i')) ↔
      ∃ n, EvalGraph n (pBot (S.tr.code 1 k)) (pBot (S.tr.code 1 k)) (pBot (S.tr.code 1 k)) (actCode Action.C.swap : V) := by
  unfold qo
  rw [eval_swap_qT_iff_valsT, hg, lMap_swap_template13_partner 1 (by decide), eval_template13_partner 1 (by decide), valsT_mem1 hk]

/-- The inner guard, a closed probe, in the standard reading: its own play. -/
theorem eval_qi {S : Sys2n} {P : PD.Prog} (hP : ProperPlayer P) (hns : noSelfIdxP P = true)
    (hg : S.m₀.g' = template13 (.plays P P .D)) (i i' : ℕ) (k : V) :
    Semiformula.Eval (s := stdReadingV V) ![k] Empty.elim (S.qi i i') ↔
      ∃ n, EvalGraph n ((progCode P : ℕ) : V) ((progCode P : ℕ) : V) ((progCode P : ℕ) : V) (actCode .D : V) := by
  unfold qi
  rw [eval_qT_iff_vals, hg, eval_template13_closed P hP hns]

theorem eval_qi_swap {S : Sys2n} {P : PD.Prog} (hP : ProperPlayer P) (hns : noSelfIdxP P = true) (hf : fragP P = true)
    (hPt : ProperPlayer P.transpose) (hnst : noSelfIdxP P.transpose = true)
    (hg : S.m₀.g' = template13 (.plays P P .D)) (i i' : ℕ) (k : V) :
    Semiformula.Eval (s := stdReadingV V) ![k] Empty.elim (Semiformula.lMap swap (S.qi i i')) ↔
      ∃ n, EvalGraph n ((progCode P.transpose : ℕ) : V) ((progCode P.transpose : ℕ) : V) ((progCode P.transpose : ℕ) : V)
        (actCode Action.D.swap : V) := by
  unfold qi
  rw [eval_swap_qT_iff_valsT, hg, lMap_swap_template13_closed P hP hns hf hPt hnst, eval_template13_closed _ hPt hnst]

end Sys2n

/-! ### 3. The system `inst prudent mirror = .sys [pm 1 mirror, mm 0] 0` -/

/-- The mirror's instance at the defector: the bare forwarder of the frozen defector (`k`-free). -/
abbrev mirrorDef : Prog := .sim (.bot (.const .D)) (.bot (.const .D))

lemma inst_mirror_defect_eq (k : ℕ) : inst (tauZoo k) .mirror .defect = mirrorDef := rfl

/-- The prudence probe at the mirror. -/
abbrev prudG : Formula := .plays (.bot mirrorDef) (.bot mirrorDef) .D

/-- The Prudent member at the mirror, as a nested member. -/
noncomputable def PMm : NM := ⟨template13 (entDmG 1), template13 prudG, 0, Or.inl rfl⟩

noncomputable def SPM : Sys2n := ⟨PMm, progCode (mm 0), transposeCode_mm0⟩

lemma SPM_P : SPM.P = progCode (mm 0) := rfl

/-- The frozen forwarder of the defector defects against itself, in every model (fuel 4). -/
lemma botMirrorDef_plays_D : EvalGraph (0 + 1 + 1 + 1 + 1) ((progCode (.bot mirrorDef) : ℕ) : V) ((progCode (.bot mirrorDef) : ℕ) : V)
    ((progCode (.bot mirrorDef) : ℕ) : V) (actCode .D : V) := by
  have e : ((progCode (.bot mirrorDef) : ℕ) : V) = pBot (pSim (pBot (pConst 1)) (pBot (pConst 1))) := by
    simp only [mirrorDef, progCode_bot, progCode_sim, progCode_const, actCode_D, cast_pBot, cast_pSim, cast_pConst, Nat.cast_one]
  rw [e, actCode_D_cast, EvalGraph.bot_iff, EvalGraph.sim_iff, substCode_bot, EvalGraph.bot_iff, EvalGraph.const_iff]

lemma botMirrorDef_transpose : (PD.Prog.bot mirrorDef).transpose = .bot (.sim (.bot (.const .C)) (.bot (.const .C))) := rfl

lemma botMirrorDefT_plays_C : EvalGraph (0 + 1 + 1 + 1 + 1) ((progCode (PD.Prog.bot mirrorDef).transpose : ℕ) : V)
    ((progCode (PD.Prog.bot mirrorDef).transpose : ℕ) : V) ((progCode (PD.Prog.bot mirrorDef).transpose : ℕ) : V)
    (actCode Action.D.swap : V) := by
  have e : ((progCode (PD.Prog.bot mirrorDef).transpose : ℕ) : V) = pBot (pSim (pBot (pConst 0)) (pBot (pConst 0))) := by
    rw [botMirrorDef_transpose]
    simp only [progCode_bot, progCode_sim, progCode_const, actCode_C, cast_pBot, cast_pSim, cast_pConst, Nat.cast_zero]
  rw [e, show Action.D.swap = .C from rfl, actCode_C_cast, EvalGraph.bot_iff, EvalGraph.sim_iff, substCode_bot,
    EvalGraph.bot_iff, EvalGraph.const_iff]

/-- **The Löb premise of τ(Prudent) at the mirror**: boxes of the outer probe and of the prudence guard make the
Prudent member cooperate, the mirror member copies it (the outer probe holds), and the prudence guard is a closed
truth; in the transposed system the transposed member defects and the mirror copies that. -/
theorem loebSound_PMi : LoebSound (pQ (SPM.qo 0 0 ⋏ SPM.qi 0 0)) (14 + SPM.K) 16 := by
  refine loebSound_pQ₂_above _ _ SPM.K fun V _ _ k hk b₁ b₂ b₃ b₄ ↦ ?_
  have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
  rw [← stdReadingV_eq_stdReading]
  have hC := Sys2n.plays_of_boxes hk 0 0 b₁ b₂
  have hCT := Sys2n.tr_plays_of_boxes hk 0 0 b₃ b₄
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine (Sys2n.eval_qo hk rfl 0 0).mpr ⟨5 + 1 + 1 + 1, ?_⟩
    rw [show (actCode .C : V) = ((PMm.a : ℕ) : V) by rfl]
    exact Sys2n.mirror_copies_V SPM SPM_P 5 _ _ _ hC
  · exact (Sys2n.eval_qi (properPlayer_bot _) rfl rfl 0 0 k).mpr ⟨_, botMirrorDef_plays_D⟩
  · refine (Sys2n.eval_qo_swap hk rfl 0 0).mpr ⟨5 + 1 + 1 + 1, ?_⟩
    rw [show (actCode Action.C.swap : V) = ((SPM.tr.m₀.a : ℕ) : V) by rfl]
    exact Sys2n.mirror_copies_V SPM.tr SPM_P 5 _ _ _ hCT
  · exact (Sys2n.eval_qi_swap (properPlayer_bot _) rfl rfl (properPlayer_bot _) rfl rfl 0 0 k).mpr ⟨_, botMirrorDefT_plays_C⟩

/-- Both guards of the Prudent member are found in the bit's frame for all large `k`. -/
theorem found_PMi : ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k → SPM.K ≤ k ∧
    LenBox TAct k (instB (⌜SPM.qo 0 0⌝ : ℕ) k) ∧ LenBox TAct k (instB (⌜SPM.qi 0 0⌝ : ℕ) k) := by
  obtain ⟨k₀, h⟩ := family_found (pQ (SPM.qo 0 0 ⋏ SPM.qi 0 0)) boundedInnerNec_sixteen loebSound_PMi
  refine ⟨k₀ + SPM.K, fun k hk ↦ ?_⟩
  obtain ⟨a, ha', hbox⟩ := h k (by omega)
  obtain ⟨b₁, b₂, -, -⟩ := boxes_pQ₂_nat _ _ SPM.K k a ha' hbox
  exact ⟨by omega, b₁, b₂⟩

/-! #### The bridge to the engine, at ℕ -/

lemma SPM_D_nat (k : ℕ) : SPM.D k = progListCode (sys2 (pm 1 k .mirror) (mm 0)) := by
  unfold Sys2n.D NM.code SM.code
  simp only [SPM, PMm, NM.inn, natCast_nat]
  rfl

lemma SPM_code_nat (j k : ℕ) : SPM.code j k = progCode (.sys (sys2 (pm 1 k .mirror) (mm 0)) j) := by
  unfold Sys2n.code; rw [SPM_D_nat, progCode_sys, natCast_nat]

/-- **τ(Prudent) at the mirror cooperates with itself** (the `mirror` column at Prudent). -/
theorem col_prudent_mirror_C : bitEventually .prudent .mirror .C := by
  obtain ⟨k₀, h⟩ := found_PMi
  refine ⟨k₀, fun k hk ↦ ?_⟩
  obtain ⟨hK, bo, bi⟩ := h k hk
  have eo := Sys2n.qo_eq_instB (V := ℕ) (S := SPM) (k := k) (le_def.mpr (Nat.eq_or_lt_of_le (by rw [natCast_nat]; exact hK))) 0 0
  have ei := Sys2n.qi_eq_instB (V := ℕ) (S := SPM) (k := k) (le_def.mpr (Nat.eq_or_lt_of_le (by rw [natCast_nat]; exact hK))) 0 0
  rw [natCast_nat] at eo ei
  rw [← eo] at bo
  rw [← ei] at bi
  -- the consulted codes are the engine's guard codes of the closed guards
  rw [SPM_D_nat, SPM_code_nat] at bo bi
  rw [show (⌜SPM.m₀.g⌝ : ℕ) = templateCode (entDmG 1) from rfl, templateCode_sysClose _ _ rfl,
    guardCodeB_of_template (isSemiformula_templateCode _ rfl)] at bo
  rw [show (⌜SPM.m₀.g'⌝ : ℕ) = templateCode prudG from rfl, templateCode_sysClose _ _ rfl,
    guardCodeB_of_template (isSemiformula_templateCode _ rfl)] at bi
  exact bitPlays_of_member (inst_prudent_mirror k) (memberP_pm 1 k (by decide) .mirror) (N := 0 + 1 + 1 + 1)
    (by rw [pm_sysClose]; exact member_then _ bo (member_then _ bi (const_play 0 _ _ _)))

/-- `ebot × prudent`: C — τ(EBot)'s exploit and reciprocity watches fall on Prudent's instances at the defector and
the cooperator (`col_prudent_defect`, `col_prudent_coop`: both D) and the mirror watch fires. -/
theorem ent_ebot_prudent : bitEventually .ebot .prudent .C := by
  obtain ⟨k₃, h₃⟩ := col_prudent_mirror_C
  refine ⟨k₃, fun k hk ↦ ?_⟩
  apply bitPlays_of_eq (instCode_ebot k _)
  obtain ⟨n₁, e₁⟩ := col_prudent_defect k
  obtain ⟨n₂, e₂⟩ := col_prudent_coop k
  obtain ⟨n₃, e₃⟩ := h₃ k hk
  exact ⟨_, watch_falls' e₁ (by decide) (watch_falls' e₂ (by decide) (watch_fires' e₃ (const_play 0 _ _ _)))⟩

/-- `ebot × prudent` ‡ (base `dich_PrudentBot_vs_EBot`): settled C on this side; the hinge is Prudent's outer
probe of EBot's instance, in Prudent's own frame (the convention of `Tau/Rows/EBot.lean`). -/
theorem entFloor_ebot_prudent : FloorBitA .ebot .prudent
    (fun k ↦ □[k] (guardCodeB (templateCode (probe (inst (tauZoo k) .ebot .prudent)))
      (pBot (instCode k .prudent .ebot)) (pBot (instCode k .prudent .ebot)) k)) .C :=
  FloorBitA.of _ ent_ebot_prudent

end ArithS.Tau
