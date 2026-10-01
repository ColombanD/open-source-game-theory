import ArithS.Tau.Entangled.Tower
import ArithS.Cells.Common.Families

/-!
# ArithS.Tau.Entangled.Family — the thirteen-slot instance equation and the member guards in every model

The closed member `pSearch k (sysCloseTemplate d ⌜g⌝) p q` consults, in the frame `(me, opp)` at its budget `k`,
the code `guardCodeB (sysCloseTemplate d ⌜g⌝) me opp k` = the thirteen-variable template `g` with the frame
descriptions in `#0..#5`, `binNumeral k` in `#6` and the two members' descriptions in `#7..#12`
(`descriptionsSys`). This module:

* **`qT13`** — `g` filled with six description triples and `#0` in the budget slot, the thirteen-slot twin of
  `qT` (`Cells/Common/Templates.lean`), and **`guardCodeB_sysClose_eq_instB`**: the consulted code is the
  `binNumeral k`-instance of `⌜qT13 g …⌝` whenever the four triples describe the frame players and the two
  members on codes (`substs_substs` twice, the two thirteen-entry `termSubstVec` computations);
* **`eval_qT13_iff`** and the truth of the three atom shapes a member guard carries, at any thirteen-slot
  valuation: the partner's self-play `.plays (.bot (.selfIdx j)) (.bot (.selfIdx j)) a`, and the two `.self`
  atoms `.plays .self (.bot (.selfIdx j)) a` / `.plays (.bot (.selfIdx j)) .self a` (the pronoun clause
  `progAux13_botSelfIdx` reads member `j` as `pBotTerm` of its slot: `val_pBotTerm_V`);
* **τ on the thirteen-variable templates** of those shapes (`lMap_swap_template13_*`): the transposed template
  is the template of the transposed formula, as `lMap_swap_template` on the fragment;
* **the search clauses on a closed member in every model** (`Sys2.member_then_V`/`member_else_V`): a box of the
  consulted code makes the bot-wrapped member play its then-action at fuel `3`, no box its else-action.
-/

set_option linter.constructorNameAsVariable false

namespace ArithS.Tau

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open LAct

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ### 1. `qT13` and its quote -/

/-- A thirteen-variable template filled with the frame triples (me, opp), `#0` in the budget slot, and the two
member triples. -/
noncomputable def qT13 (g : Semisentence LAct 13) (X : Semiterm LAct Empty 1) (U W : ClosedSemiterm LAct 0)
    (X' : Semiterm LAct Empty 1) (U' W' : ClosedSemiterm LAct 0)
    (Y₀ : Semiterm LAct Empty 1) (U₀ W₀ : ClosedSemiterm LAct 0)
    (Y₁ : Semiterm LAct Empty 1) (U₁ W₁ : ClosedSemiterm LAct 0) : Semisentence LAct 1 :=
  g ⇜ ![X, cl U, cl W, X', cl U', cl W', #0, Y₀, cl U₀, cl W₀, Y₁, cl U₁, cl W₁]

lemma lMap_swap_qT13 (g : Semisentence LAct 13) (X : Semiterm LAct Empty 1) (U W : ClosedSemiterm LAct 0)
    (X' : Semiterm LAct Empty 1) (U' W' : ClosedSemiterm LAct 0)
    (Y₀ : Semiterm LAct Empty 1) (U₀ W₀ : ClosedSemiterm LAct 0)
    (Y₁ : Semiterm LAct Empty 1) (U₁ W₁ : ClosedSemiterm LAct 0) :
    Semiformula.lMap swap (qT13 g X U W X' U' W' Y₀ U₀ W₀ Y₁ U₁ W₁) =
      qT13 (Semiformula.lMap swap g) (Semiterm.lMap swap X) (Semiterm.lMap swap U) (Semiterm.lMap swap W)
        (Semiterm.lMap swap X') (Semiterm.lMap swap U') (Semiterm.lMap swap W')
        (Semiterm.lMap swap Y₀) (Semiterm.lMap swap U₀) (Semiterm.lMap swap W₀)
        (Semiterm.lMap swap Y₁) (Semiterm.lMap swap U₁) (Semiterm.lMap swap W₁) := by
  unfold qT13
  rw [Semiformula.lMap_subst]
  congr 1
  funext i
  fin_cases i <;> simp [lMap_swap_cl]

lemma isSemiformula_quote₁₃ (φ : Semisentence LAct 13) : IsSemiformula LAct 13 (⌜φ⌝ : V) := by
  simpa using Sentence.quote_isSemiformula (V := V) φ

/-- The thirteen codes of the substituted terms of `qT13`, as an internal vector. -/
noncomputable def gVec13 (X : Semiterm LAct Empty 1) (U W : ClosedSemiterm LAct 0)
    (X' : Semiterm LAct Empty 1) (U' W' : ClosedSemiterm LAct 0)
    (Y₀ : Semiterm LAct Empty 1) (U₀ W₀ : ClosedSemiterm LAct 0)
    (Y₁ : Semiterm LAct Empty 1) (U₁ W₁ : ClosedSemiterm LAct 0) : V :=
  (⌜(Rew.emb X : SyntacticSemiterm LAct 1)⌝ : V) ∷
    ⌜(Rew.emb (cl U : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝ ∷
    ⌜(Rew.emb (cl W : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝ ∷
    ⌜(Rew.emb X' : SyntacticSemiterm LAct 1)⌝ ∷
    ⌜(Rew.emb (cl U' : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝ ∷
    ⌜(Rew.emb (cl W' : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝ ∷
    ⌜(Rew.emb (#0 : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝ ∷
    ⌜(Rew.emb Y₀ : SyntacticSemiterm LAct 1)⌝ ∷
    ⌜(Rew.emb (cl U₀ : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝ ∷
    ⌜(Rew.emb (cl W₀ : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝ ∷
    ⌜(Rew.emb Y₁ : SyntacticSemiterm LAct 1)⌝ ∷
    ⌜(Rew.emb (cl U₁ : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝ ∷
    ⌜(Rew.emb (cl W₁ : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝ ∷ 0

theorem quote_qT13 (g : Semisentence LAct 13) (X : Semiterm LAct Empty 1) (U W : ClosedSemiterm LAct 0)
    (X' : Semiterm LAct Empty 1) (U' W' : ClosedSemiterm LAct 0)
    (Y₀ : Semiterm LAct Empty 1) (U₀ W₀ : ClosedSemiterm LAct 0)
    (Y₁ : Semiterm LAct Empty 1) (U₁ W₁ : ClosedSemiterm LAct 0) :
    (⌜qT13 g X U W X' U' W' Y₀ U₀ W₀ Y₁ U₁ W₁⌝ : V) = subst LAct (gVec13 X U W X' U' W' Y₀ U₀ W₀ Y₁ U₁ W₁) (⌜g⌝ : V) := by
  unfold qT13
  rw [Sentence.quote_def, Semiformula.coe_subst_eq_subst_coe, Semiformula.quote_def,
    Semiformula.typed_quote_substs, Bootstrapping.Semiformula.val_substs, ← Semiformula.quote_def,
    ← Sentence.quote_def]
  congr 1

lemma gVec13_semitermVec (X : Semiterm LAct Empty 1) (U W : ClosedSemiterm LAct 0)
    (X' : Semiterm LAct Empty 1) (U' W' : ClosedSemiterm LAct 0)
    (Y₀ : Semiterm LAct Empty 1) (U₀ W₀ : ClosedSemiterm LAct 0)
    (Y₁ : Semiterm LAct Empty 1) (U₁ W₁ : ClosedSemiterm LAct 0) :
    IsSemitermVec LAct 13 1 (gVec13 X U W X' U' W' Y₀ U₀ W₀ Y₁ U₁ W₁ : V) := by
  rw [thirteen_eq, gVec13]
  exact (((((((((((((IsSemitermVec.nil 1).adjoin (semiterm_quote_emb₁ _)).adjoin (semiterm_quote_emb₁ _)).adjoin
    (semiterm_quote_emb₁ _)).adjoin (semiterm_quote_emb₁ _)).adjoin (semiterm_quote_emb₁ _)).adjoin
    (semiterm_quote_emb₁ _)).adjoin (semiterm_quote_emb₁ _)).adjoin (semiterm_quote_emb₁ _)).adjoin
    (semiterm_quote_emb₁ _)).adjoin (semiterm_quote_emb₁ _)).adjoin (semiterm_quote_emb₁ _)).adjoin
    (semiterm_quote_emb₁ _)).adjoin (semiterm_quote_emb₁ _)

/-- The full description vector a closed member's guard is filled with: the frame, the budget, the members. -/
noncomputable def fullVec (me opp k s₀ s₁ : V) : V :=
  codeTerm (canonical me) ∷ revalueU me ∷ revalueW me ∷ codeTerm (canonical opp) ∷ revalueU opp ∷ revalueW opp ∷
    binNumeral k ∷ codeTerm (canonical s₀) ∷ revalueU s₀ ∷ revalueW s₀ ∷
    codeTerm (canonical s₁) ∷ revalueU s₁ ∷ revalueW s₁ ∷ 0

lemma quote_emb_bvar_zero_LAct : (⌜(Rew.emb (#0 : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝ : V) = ^#0 := by
  simp [Rew.emb]

/-- The code of a closed term, cast to one variable, is fixed by the budget substitution. -/
lemma termSubst_quote_cl (w : V) (U : ClosedSemiterm LAct 0) :
    termSubst LAct w (⌜(Rew.emb (cl U : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝ : V) = ⌜U⌝ := by
  rw [quote_emb_cl_V, termSubst_closed _ (semiterm_quote_emb₀ _), ← Semiterm.empty_quote_def]

/-- **Substituting the budget into the thirteen codes gives the full description vector**, given the twelve
entry equations. -/
theorem termSubstVec_gVec13 (k : V) (X : Semiterm LAct Empty 1) (U W : ClosedSemiterm LAct 0)
    (X' : Semiterm LAct Empty 1) (U' W' : ClosedSemiterm LAct 0)
    (Y₀ : Semiterm LAct Empty 1) (U₀ W₀ : ClosedSemiterm LAct 0)
    (Y₁ : Semiterm LAct Empty 1) (U₁ W₁ : ClosedSemiterm LAct 0) {me opp s₀ s₁ : V}
    (hX : termSubst LAct (binNumeral k ∷ (0 : V)) (⌜(Rew.emb X : SyntacticSemiterm LAct 1)⌝ : V) = codeTerm (canonical me))
    (hU : (⌜U⌝ : V) = revalueU me) (hW : (⌜W⌝ : V) = revalueW me)
    (hX' : termSubst LAct (binNumeral k ∷ (0 : V)) (⌜(Rew.emb X' : SyntacticSemiterm LAct 1)⌝ : V) = codeTerm (canonical opp))
    (hU' : (⌜U'⌝ : V) = revalueU opp) (hW' : (⌜W'⌝ : V) = revalueW opp)
    (hY₀ : termSubst LAct (binNumeral k ∷ (0 : V)) (⌜(Rew.emb Y₀ : SyntacticSemiterm LAct 1)⌝ : V) = codeTerm (canonical s₀))
    (hU₀ : (⌜U₀⌝ : V) = revalueU s₀) (hW₀ : (⌜W₀⌝ : V) = revalueW s₀)
    (hY₁ : termSubst LAct (binNumeral k ∷ (0 : V)) (⌜(Rew.emb Y₁ : SyntacticSemiterm LAct 1)⌝ : V) = codeTerm (canonical s₁))
    (hU₁ : (⌜U₁⌝ : V) = revalueU s₁) (hW₁ : (⌜W₁⌝ : V) = revalueW s₁) :
    termSubstVec LAct 13 (binNumeral k ∷ (0 : V)) (gVec13 X U W X' U' W' Y₀ U₀ W₀ Y₁ U₁ W₁) = fullVec me opp k s₀ s₁ := by
  have u : ∀ t : Semiterm LAct Empty 1, IsUTerm LAct (⌜(Rew.emb t : SyntacticSemiterm LAct 1)⌝ : V) :=
    fun t ↦ (semiterm_quote_emb₁ t).isUTerm
  have e0 : IsUTermVec LAct 0 (0 : V) := IsUTermVec.empty
  have e1 := e0.adjoin (u (cl W₁))
  have e2 := e1.adjoin (u (cl U₁))
  have e3 := e2.adjoin (u Y₁)
  have e4 := e3.adjoin (u (cl W₀))
  have e5 := e4.adjoin (u (cl U₀))
  have e6 := e5.adjoin (u Y₀)
  have e7 := e6.adjoin (u #0)
  have e8 := e7.adjoin (u (cl W'))
  have e9 := e8.adjoin (u (cl U'))
  have e10 := e9.adjoin (u X')
  have e11 := e10.adjoin (u (cl W))
  have e12 := e11.adjoin (u (cl U))
  unfold gVec13 fullVec
  rw [thirteen_eq, termSubstVec_cons (u X) e12, termSubstVec_cons (u (cl U)) e11, termSubstVec_cons (u (cl W)) e10,
    termSubstVec_cons (u X') e9, termSubstVec_cons (u (cl U')) e8, termSubstVec_cons (u (cl W')) e7,
    termSubstVec_cons (u #0) e6, termSubstVec_cons (u Y₀) e5, termSubstVec_cons (u (cl U₀)) e4,
    termSubstVec_cons (u (cl W₀)) e3, termSubstVec_cons (u Y₁) e2, termSubstVec_cons (u (cl U₁)) e1,
    termSubstVec_cons (u (cl W₁)) e0, termSubstVec_nil,
    hX, termSubst_quote_cl, termSubst_quote_cl, hX', termSubst_quote_cl, termSubst_quote_cl,
    quote_emb_bvar_zero_LAct, termSubst_bvar, nth_adjoin_zero,
    hY₀, termSubst_quote_cl, termSubst_quote_cl, hY₁, termSubst_quote_cl, termSubst_quote_cl,
    hU, hW, hU', hW', hU₀, hW₀, hU₁, hW₁]

/-! ### 2. The consulted code of a closed member -/

/-- **Substituting the frame descriptions into the member-slot vector gives the full description vector.** -/
theorem termSubstVec_descriptionsSys (me opp k d : V) :
    termSubstVec LAct 13 (descriptionsB me opp k) (descriptionsSys d) = fullVec me opp k (pSys d 0) (pSys d 1) := by
  have b : ∀ i : V, IsUTerm LAct (^#i : V) := fun i ↦ (IsSemiterm.bvar.mpr (lt_add_one i) : IsSemiterm LAct (i + 1) (^#i)).isUTerm
  have c : ∀ x : V, IsUTerm LAct (codeTerm x) := fun x ↦ (codeTerm_semiterm_LAct 0 x).isUTerm
  have ru : ∀ x : V, IsUTerm LAct (revalueU x) := fun x ↦ (revalueU_semiterm 0 x).isUTerm
  have rw' : ∀ x : V, IsUTerm LAct (revalueW x) := fun x ↦ (revalueW_semiterm 0 x).isUTerm
  have e0 : IsUTermVec LAct 0 (0 : V) := IsUTermVec.empty
  have e1 := e0.adjoin (rw' (pSys d 1))
  have e2 := e1.adjoin (ru (pSys d 1))
  have e3 := e2.adjoin (c (canonical (pSys d 1)))
  have e4 := e3.adjoin (rw' (pSys d 0))
  have e5 := e4.adjoin (ru (pSys d 0))
  have e6 := e5.adjoin (c (canonical (pSys d 0)))
  have e7 := e6.adjoin (b 6)
  have e8 := e7.adjoin (b 5)
  have e9 := e8.adjoin (b 4)
  have e10 := e9.adjoin (b 3)
  have e11 := e10.adjoin (b 2)
  have e12 := e11.adjoin (b 1)
  unfold descriptionsSys fullVec
  rw [thirteen_eq, termSubstVec_cons (b 0) e12, termSubstVec_cons (b 1) e11, termSubstVec_cons (b 2) e10,
    termSubstVec_cons (b 3) e9, termSubstVec_cons (b 4) e8, termSubstVec_cons (b 5) e7, termSubstVec_cons (b 6) e6,
    termSubstVec_cons (c _) e5, termSubstVec_cons (ru _) e4, termSubstVec_cons (rw' _) e3,
    termSubstVec_cons (c _) e2, termSubstVec_cons (ru _) e1, termSubstVec_cons (rw' _) e0, termSubstVec_nil]
  simp only [termSubst_bvar, nth_descriptionsB_zero, nth_descriptionsB_one, nth_descriptionsB_two,
    nth_descriptionsB_three, nth_descriptionsB_four, nth_descriptionsB_five, nth_descriptionsB_six]
  rw [termSubst_closed _ (codeTerm_semiterm_LAct 0 _), termSubst_closed _ (revalueU_semiterm 0 _),
    termSubst_closed _ (revalueW_semiterm 0 _), termSubst_closed _ (codeTerm_semiterm_LAct 0 _),
    termSubst_closed _ (revalueU_semiterm 0 _), termSubst_closed _ (revalueW_semiterm 0 _)]

/-- **The thirteen-slot instance equation**: the code a closed member consults in the frame `(me, opp)` at its
budget `k` is the `binNumeral k`-instance of `⌜qT13 g …⌝`, whenever the triples describe the frame players and the
two members on codes. -/
theorem guardCodeB_sysClose_eq_instB (g : Semisentence LAct 13) (k d : V) (X : Semiterm LAct Empty 1) (U W : ClosedSemiterm LAct 0)
    (X' : Semiterm LAct Empty 1) (U' W' : ClosedSemiterm LAct 0)
    (Y₀ : Semiterm LAct Empty 1) (U₀ W₀ : ClosedSemiterm LAct 0)
    (Y₁ : Semiterm LAct Empty 1) (U₁ W₁ : ClosedSemiterm LAct 0) {me opp : V}
    (hX : termSubst LAct (binNumeral k ∷ (0 : V)) (⌜(Rew.emb X : SyntacticSemiterm LAct 1)⌝ : V) = codeTerm (canonical me))
    (hU : (⌜U⌝ : V) = revalueU me) (hW : (⌜W⌝ : V) = revalueW me)
    (hX' : termSubst LAct (binNumeral k ∷ (0 : V)) (⌜(Rew.emb X' : SyntacticSemiterm LAct 1)⌝ : V) = codeTerm (canonical opp))
    (hU' : (⌜U'⌝ : V) = revalueU opp) (hW' : (⌜W'⌝ : V) = revalueW opp)
    (hY₀ : termSubst LAct (binNumeral k ∷ (0 : V)) (⌜(Rew.emb Y₀ : SyntacticSemiterm LAct 1)⌝ : V) = codeTerm (canonical (pSys d 0)))
    (hU₀ : (⌜U₀⌝ : V) = revalueU (pSys d 0)) (hW₀ : (⌜W₀⌝ : V) = revalueW (pSys d 0))
    (hY₁ : termSubst LAct (binNumeral k ∷ (0 : V)) (⌜(Rew.emb Y₁ : SyntacticSemiterm LAct 1)⌝ : V) = codeTerm (canonical (pSys d 1)))
    (hU₁ : (⌜U₁⌝ : V) = revalueU (pSys d 1)) (hW₁ : (⌜W₁⌝ : V) = revalueW (pSys d 1)) :
    guardCodeB (sysCloseTemplate d (⌜g⌝ : V)) me opp k = instB (⌜qT13 g X U W X' U' W' Y₀ U₀ W₀ Y₁ U₁ W₁⌝ : V) k := by
  rw [sysCloseTemplate_of_template₁₃ (isSemiformula_quote₁₃ g)]
  unfold guardCodeB instB
  rw [substs_substs (isSemiformula_quote₁₃ g) (descriptionsB_semitermVec me opp k) (descriptionsSys_semitermVec₇ d),
    termSubstVec_descriptionsSys, quote_qT13,
    substs_substs (isSemiformula_quote₁₃ g) (binNumeral_cons_semitermVec k) (gVec13_semitermVec X U W X' U' W' Y₀ U₀ W₀ Y₁ U₁ W₁),
    termSubstVec_gVec13 k X U W X' U' W' Y₀ U₀ W₀ Y₁ U₁ W₁ hX hU hW hX' hU' hW' hY₀ hU₀ hW₀ hY₁ hU₁ hW₁]

/-! ### 3. The truth of `qT13` and of the pronoun atoms -/

section truth

/-- The pronoun term denotes `pBot` of its argument. -/
lemma val_pBotTerm_V {n : ℕ} (t : Semiterm LAct Empty n) (b : Fin n → V) :
    (pBotTerm t).val (s := stdReadingV V) b Empty.elim = pBot (t.val (s := stdReadingV V) b Empty.elim) := by
  have h3 : (cl (numTB 3) : Semiterm LAct Empty n).val (s := stdReadingV V) b Empty.elim = 3 := by
    rw [val_cl_V]
    unfold numTB
    rw [Semiterm.val_lMap, stdReadingV_lMap_emb, val_binNumeralMeta_V]
    norm_num
  unfold pBotTerm pBot ppair
  simp [h3]
  rfl

lemma lMap_swap_add {n : ℕ} (s t : Semiterm LAct Empty n) :
    Semiterm.lMap swap (‘!!s + !!t’ : Semiterm LAct Empty n) = ‘!!(Semiterm.lMap swap s) + !!(Semiterm.lMap swap t)’ := by
  simp only [Semiterm.Operator.operator, Semiterm.Operator.Add.term_eq, Rew.func, Semiterm.lMap_func]
  congr 1
  funext i; fin_cases i <;> simp

lemma lMap_swap_mul {n : ℕ} (s t : Semiterm LAct Empty n) :
    Semiterm.lMap swap (‘!!s * !!t’ : Semiterm LAct Empty n) = ‘!!(Semiterm.lMap swap s) * !!(Semiterm.lMap swap t)’ := by
  simp only [Semiterm.Operator.operator, Semiterm.Operator.Mul.term_eq, Rew.func, Semiterm.lMap_func]
  congr 1
  funext i; fin_cases i <;> simp

lemma lMap_swap_natCast_one {n : ℕ} : Semiterm.lMap swap ((1 : ℕ) : Semiterm LAct Empty n) = ((1 : ℕ) : Semiterm LAct Empty n) := by
  show Semiterm.lMap swap (Semiterm.Operator.const (Semiterm.Operator.numeral LAct 1)) =
    Semiterm.Operator.const (Semiterm.Operator.numeral LAct 1)
  rw [Semiterm.Operator.numeral_one]
  simp only [Semiterm.Operator.const, Semiterm.Operator.operator, Semiterm.Operator.One.term_eq, Rew.func,
    Semiterm.lMap_func]
  congr 1
  funext i; exact i.elim0

lemma lMap_swap_pBotTerm {n : ℕ} (t : Semiterm LAct Empty n) :
    Semiterm.lMap swap (pBotTerm t) = pBotTerm (Semiterm.lMap swap t) := by
  have h : Semiterm.lMap swap (cl (numTB 3) : Semiterm LAct Empty n) = cl (numTB 3) := by
    rw [lMap_swap_cl]; unfold numTB; rw [term_lMap_swap_emb]
  unfold pBotTerm
  simp only [lMap_swap_add, lMap_swap_mul, lMap_swap_natCast_one, h]

omit [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
/-- The truth of a `qT13` instance at `k` is the truth of the template at the thirteen values. -/
theorem eval_qT13_iff (g : Semisentence LAct 13) (X : Semiterm LAct Empty 1) (U W : ClosedSemiterm LAct 0)
    (X' : Semiterm LAct Empty 1) (U' W' : ClosedSemiterm LAct 0)
    (Y₀ : Semiterm LAct Empty 1) (U₀ W₀ : ClosedSemiterm LAct 0)
    (Y₁ : Semiterm LAct Empty 1) (U₁ W₁ : ClosedSemiterm LAct 0) (k : V) :
    Semiformula.Eval (s := stdReadingV V) ![k] Empty.elim (qT13 g X U W X' U' W' Y₀ U₀ W₀ Y₁ U₁ W₁) ↔
      Semiformula.Eval (s := stdReadingV V)
        ![X.val (s := stdReadingV V) ![k] Empty.elim, U.val (s := stdReadingV V) ![] Empty.elim,
          W.val (s := stdReadingV V) ![] Empty.elim, X'.val (s := stdReadingV V) ![k] Empty.elim,
          U'.val (s := stdReadingV V) ![] Empty.elim, W'.val (s := stdReadingV V) ![] Empty.elim, k,
          Y₀.val (s := stdReadingV V) ![k] Empty.elim, U₀.val (s := stdReadingV V) ![] Empty.elim,
          W₀.val (s := stdReadingV V) ![] Empty.elim, Y₁.val (s := stdReadingV V) ![k] Empty.elim,
          U₁.val (s := stdReadingV V) ![] Empty.elim, W₁.val (s := stdReadingV V) ![] Empty.elim] Empty.elim g := by
  unfold qT13
  rw [Semiformula.eval_substs]
  have h0 : (Semiterm.val (s := stdReadingV V) ![k] Empty.elim ∘ ![X, cl U, cl W, X', cl U', cl W', #0, Y₀, cl U₀, cl W₀, Y₁, cl U₁, cl W₁]) =
      ![X.val (s := stdReadingV V) ![k] Empty.elim, U.val (s := stdReadingV V) ![] Empty.elim,
          W.val (s := stdReadingV V) ![] Empty.elim, X'.val (s := stdReadingV V) ![k] Empty.elim,
          U'.val (s := stdReadingV V) ![] Empty.elim, W'.val (s := stdReadingV V) ![] Empty.elim, k,
          Y₀.val (s := stdReadingV V) ![k] Empty.elim, U₀.val (s := stdReadingV V) ![] Empty.elim,
          W₀.val (s := stdReadingV V) ![] Empty.elim, Y₁.val (s := stdReadingV V) ![k] Empty.elim,
          U₁.val (s := stdReadingV V) ![] Empty.elim, W₁.val (s := stdReadingV V) ![] Empty.elim] := by
    funext i; fin_cases i <;> simp [val_cl_V]
  rw [h0]

omit [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
/-- The swapped reading of a `qT13` instance is the standard reading of the transposed instance. -/
theorem eval_qT13_swap (g : Semisentence LAct 13) (X : Semiterm LAct Empty 1) (U W : ClosedSemiterm LAct 0)
    (X' : Semiterm LAct Empty 1) (U' W' : ClosedSemiterm LAct 0)
    (Y₀ : Semiterm LAct Empty 1) (U₀ W₀ : ClosedSemiterm LAct 0)
    (Y₁ : Semiterm LAct Empty 1) (U₁ W₁ : ClosedSemiterm LAct 0) (k : V) :
    Semiformula.Eval (s := swappedReading V) ![k] Empty.elim (qT13 g X U W X' U' W' Y₀ U₀ W₀ Y₁ U₁ W₁) ↔
      Semiformula.Eval (s := stdReadingV V) ![k] Empty.elim
        (qT13 (Semiformula.lMap swap g) (Semiterm.lMap swap X) (Semiterm.lMap swap U) (Semiterm.lMap swap W)
          (Semiterm.lMap swap X') (Semiterm.lMap swap U') (Semiterm.lMap swap W')
          (Semiterm.lMap swap Y₀) (Semiterm.lMap swap U₀) (Semiterm.lMap swap W₀)
          (Semiterm.lMap swap Y₁) (Semiterm.lMap swap U₁) (Semiterm.lMap swap W₁)) := by
  rw [eval_swappedReading, lMap_swap_qT13, ← stdReadingV_eq_stdReading]

/-- The member `j` a thirteen-slot valuation describes (`j ∈ {0, 1}`): `revalue u_j w_j x_j`. -/
noncomputable def memVal (b : Fin 13 → V) (j : ℕ) : V :=
  if j = 0 then revalue (b 8) (b 9) (b 7) else revalue (b 11) (b 12) (b 10)

lemma memVal_zero (b : Fin 13 → V) : memVal b 0 = revalue (b 8) (b 9) (b 7) := rfl
lemma memVal_one (b : Fin 13 → V) : memVal b 1 = revalue (b 11) (b 12) (b 10) := rfl

/-- **The partner's self-play atom**, `.plays (.bot (.selfIdx j)) (.bot (.selfIdx j)) a`, in every model: the
bot-wrapped member `j` plays `a` against itself. -/
theorem eval_template13_partner (j : ℕ) (hj : j ≤ 1) (a : PD.Action) (b : Fin 13 → V) :
    Semiformula.Eval (s := stdReadingV V) b Empty.elim (template13 (.plays (.bot (.selfIdx j)) (.bot (.selfIdx j)) a)) ↔
      ∃ n, EvalGraph n (pBot (memVal b j)) (pBot (memVal b j)) (pBot (memVal b j)) (actCode a : V) := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hj with rfl | rfl
  · rw [template13_plays]
    unfold progGraph13
    rw [progAux13_botSelfIdx0, memVal_zero]
    unfold descF
    simp only [Semiformula.eval_substs, Semiformula.eval_ex, LogicalConnective.HomClass.map_and,
      LogicalConnective.Prop.and_eq, Semiformula.eval_rel, eval_relDesc_V, eval_evalG_V, stdReadingV_rel_eq,
      Function.comp_def, Matrix.cons_val, Semiterm.val_bvar, val_cl_V, val_actT_V, val_pBotTerm_V]
    constructor
    · rintro ⟨x, y, N, ⟨d, rfl, rfl⟩, ⟨d', rfl, rfl⟩, h⟩
      rw [revalue_bot] at h
      exact ⟨N, h⟩
    · rintro ⟨N, h⟩
      exact ⟨_, _, N, ⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩, by rw [revalue_bot]; exact h⟩
  · rw [template13_plays]
    unfold progGraph13
    rw [progAux13_botSelfIdx1, memVal_one]
    unfold descF
    simp only [Semiformula.eval_substs, Semiformula.eval_ex, LogicalConnective.HomClass.map_and,
      LogicalConnective.Prop.and_eq, Semiformula.eval_rel, eval_relDesc_V, eval_evalG_V, stdReadingV_rel_eq,
      Function.comp_def, Matrix.cons_val, Semiterm.val_bvar, val_cl_V, val_actT_V, val_pBotTerm_V]
    constructor
    · rintro ⟨x, y, N, ⟨d, rfl, rfl⟩, ⟨d', rfl, rfl⟩, h⟩
      rw [revalue_bot] at h
      exact ⟨N, h⟩
    · rintro ⟨N, h⟩
      exact ⟨_, _, N, ⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩, by rw [revalue_bot]; exact h⟩

/-- **"Me plays `a` against the partner"**, `.plays .self (.bot (.selfIdx j)) a`, in every model. -/
theorem eval_template13_self_partner (j : ℕ) (hj : j ≤ 1) (a : PD.Action) (b : Fin 13 → V) :
    Semiformula.Eval (s := stdReadingV V) b Empty.elim (template13 (.plays .self (.bot (.selfIdx j)) a)) ↔
      ∃ n, EvalGraph n (revalue (b 1) (b 2) (b 0)) (pBot (memVal b j)) (revalue (b 1) (b 2) (b 0)) (actCode a : V) := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hj with rfl | rfl
  · rw [template13_plays]
    unfold progGraph13
    rw [progAux13_self, progAux13_botSelfIdx0, memVal_zero]
    unfold descF
    simp only [Semiformula.eval_substs, Semiformula.eval_ex, LogicalConnective.HomClass.map_and,
      LogicalConnective.Prop.and_eq, Semiformula.eval_rel, eval_relDesc_V, eval_evalG_V, stdReadingV_rel_eq,
      Function.comp_def, Matrix.cons_val, Semiterm.val_bvar, val_cl_V, val_actT_V, val_pBotTerm_V]
    constructor
    · rintro ⟨x, y, N, ⟨d, rfl, rfl⟩, ⟨d', rfl, rfl⟩, h⟩
      rw [revalue_bot] at h
      exact ⟨N, h⟩
    · rintro ⟨N, h⟩
      exact ⟨_, _, N, ⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩, by rw [revalue_bot]; exact h⟩
  · rw [template13_plays]
    unfold progGraph13
    rw [progAux13_self, progAux13_botSelfIdx1, memVal_one]
    unfold descF
    simp only [Semiformula.eval_substs, Semiformula.eval_ex, LogicalConnective.HomClass.map_and,
      LogicalConnective.Prop.and_eq, Semiformula.eval_rel, eval_relDesc_V, eval_evalG_V, stdReadingV_rel_eq,
      Function.comp_def, Matrix.cons_val, Semiterm.val_bvar, val_cl_V, val_actT_V, val_pBotTerm_V]
    constructor
    · rintro ⟨x, y, N, ⟨d, rfl, rfl⟩, ⟨d', rfl, rfl⟩, h⟩
      rw [revalue_bot] at h
      exact ⟨N, h⟩
    · rintro ⟨N, h⟩
      exact ⟨_, _, N, ⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩, by rw [revalue_bot]; exact h⟩

/-- **"The partner plays `a` against me"**, `.plays (.bot (.selfIdx j)) .self a`, in every model. -/
theorem eval_template13_partner_self (j : ℕ) (hj : j ≤ 1) (a : PD.Action) (b : Fin 13 → V) :
    Semiformula.Eval (s := stdReadingV V) b Empty.elim (template13 (.plays (.bot (.selfIdx j)) .self a)) ↔
      ∃ n, EvalGraph n (pBot (memVal b j)) (revalue (b 1) (b 2) (b 0)) (pBot (memVal b j)) (actCode a : V) := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hj with rfl | rfl
  · rw [template13_plays]
    unfold progGraph13
    rw [progAux13_self, progAux13_botSelfIdx0, memVal_zero]
    unfold descF
    simp only [Semiformula.eval_substs, Semiformula.eval_ex, LogicalConnective.HomClass.map_and,
      LogicalConnective.Prop.and_eq, Semiformula.eval_rel, eval_relDesc_V, eval_evalG_V, stdReadingV_rel_eq,
      Function.comp_def, Matrix.cons_val, Semiterm.val_bvar, val_cl_V, val_actT_V, val_pBotTerm_V]
    constructor
    · rintro ⟨x, y, N, ⟨d, rfl, rfl⟩, ⟨d', rfl, rfl⟩, h⟩
      rw [revalue_bot] at h
      exact ⟨N, h⟩
    · rintro ⟨N, h⟩
      exact ⟨_, _, N, ⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩, by rw [revalue_bot]; exact h⟩
  · rw [template13_plays]
    unfold progGraph13
    rw [progAux13_self, progAux13_botSelfIdx1, memVal_one]
    unfold descF
    simp only [Semiformula.eval_substs, Semiformula.eval_ex, LogicalConnective.HomClass.map_and,
      LogicalConnective.Prop.and_eq, Semiformula.eval_rel, eval_relDesc_V, eval_evalG_V, stdReadingV_rel_eq,
      Function.comp_def, Matrix.cons_val, Semiterm.val_bvar, val_cl_V, val_actT_V, val_pBotTerm_V]
    constructor
    · rintro ⟨x, y, N, ⟨d, rfl, rfl⟩, ⟨d', rfl, rfl⟩, h⟩
      rw [revalue_bot] at h
      exact ⟨N, h⟩
    · rintro ⟨N, h⟩
      exact ⟨_, _, N, ⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩, by rw [revalue_bot]; exact h⟩

end truth

/-! ### 4. τ on the thirteen-variable templates of the member guards -/

section swap

lemma lMap_swap_progAux13_botSelfIdx (j : ℕ) (hj : j ≤ 1) (c : ℕ) :
    Semiformula.lMap swap (progAux13 (.bot (.selfIdx j)) c) = progAux13 (.bot (.selfIdx j)) c := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hj with rfl | rfl
  · rw [progAux13_botSelfIdx0, lMap_swap_descF, lMap_swap_pBotTerm]; rfl
  · rw [progAux13_botSelfIdx1, lMap_swap_descF, lMap_swap_pBotTerm]; rfl

lemma lMap_swap_progAux13_self (c : ℕ) : Semiformula.lMap swap (progAux13 .self c) = progAux13 .self c := by
  rw [progAux13_self, lMap_swap_descF]; rfl

/-- τ on a `.plays` template whose arguments are pronouns (`.self` or `.bot (.selfIdx j)`): the arguments are
fixed, the action swaps. -/
theorem lMap_swap_template13_plays {p q : PD.Prog}
    (hp : Semiformula.lMap swap (progAux13 p (progCode p)) = progAux13 p (progCode p))
    (hq : Semiformula.lMap swap (progAux13 q (progCode q)) = progAux13 q (progCode q)) (a : PD.Action) :
    Semiformula.lMap swap (template13 (.plays p q a)) = template13 (.plays p q a.swap) := by
  rw [template13_plays, template13_plays]
  unfold progGraph13
  simp only [Semiformula.lMap_exs, LogicalConnective.HomClass.map_and, Semiformula.lMap_subst, lMap_swap_evalG, hp, hq]
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

theorem lMap_swap_template13_partner (j : ℕ) (hj : j ≤ 1) (a : PD.Action) :
    Semiformula.lMap swap (template13 (.plays (.bot (.selfIdx j)) (.bot (.selfIdx j)) a)) =
      template13 (.plays (.bot (.selfIdx j)) (.bot (.selfIdx j)) a.swap) :=
  lMap_swap_template13_plays (lMap_swap_progAux13_botSelfIdx j hj _) (lMap_swap_progAux13_botSelfIdx j hj _) a

theorem lMap_swap_template13_self_partner (j : ℕ) (hj : j ≤ 1) (a : PD.Action) :
    Semiformula.lMap swap (template13 (.plays .self (.bot (.selfIdx j)) a)) =
      template13 (.plays .self (.bot (.selfIdx j)) a.swap) :=
  lMap_swap_template13_plays (lMap_swap_progAux13_self _) (lMap_swap_progAux13_botSelfIdx j hj _) a

theorem lMap_swap_template13_partner_self (j : ℕ) (hj : j ≤ 1) (a : PD.Action) :
    Semiformula.lMap swap (template13 (.plays (.bot (.selfIdx j)) .self a)) =
      template13 (.plays (.bot (.selfIdx j)) .self a.swap) :=
  lMap_swap_template13_plays (lMap_swap_progAux13_botSelfIdx j hj _) (lMap_swap_progAux13_self _) a

theorem lMap_swap_template13_impl (φ ψ : PD.Formula) :
    Semiformula.lMap swap (template13 (.impl φ ψ)) = Semiformula.lMap swap (template13 φ) 🡒 Semiformula.lMap swap (template13 ψ) := by
  rw [template13_impl, LogicalConnective.HomClass.map_imply]

end swap

/-! ### 5. The search clauses on a closed member, in every model -/

namespace Sys2

/-- Member `j` of the system (`j ∈ {0, 1}`). -/
def mem (S : Sys2) (j : ℕ) : SM := if j = 0 then S.m₀ else S.m₁

lemma mem_zero (S : Sys2) : S.mem 0 = S.m₀ := rfl
lemma mem_one (S : Sys2) : S.mem 1 = S.m₁ := rfl

/-- Member lookup on the list code. -/
lemma listGet_D (S : Sys2) (j : ℕ) (hj : j ≤ 1) (k : V) : listGet (S.D k) (j : V) = (S.mem j).code k + 1 := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hj with rfl | rfl
  · unfold D; rw [Nat.cast_zero, listGet_cons_zero]; rfl
  · unfold D
    rw [Nat.cast_one]
    conv_lhs => rw [show (1 : V) = 0 + 1 by simp]
    rw [listGet_cons_succ, listGet_cons_zero]; rfl

/-- The closed member `j`: its stored template closed by the member slots AT ITS OWN BUDGET (`sysCloseTemplateAt`,
Phase 2d — the members described with the budget in the slot `#6`), its branches the constants. The sentence it
consults is the verbatim closer's (`guardCodeB_sysCloseTemplateAt`), which is what `member_then_V`/`member_else_V`
and every instance equation of this folder are stated on. -/
lemma sysCloseCode_mem (S : Sys2) (j : ℕ) (k : V) :
    sysCloseCode (S.D k) ((S.mem j).code k) =
      pSearch k (sysCloseTemplateAt (S.D k) k ((⌜(S.mem j).g⌝ : ℕ) : V)) (pConst ((S.mem j).a : V)) (pConst ((1 - (S.mem j).a : ℕ) : V)) := by
  unfold SM.code
  rw [sysCloseCode_search, sysCloseCode_const, sysCloseCode_const]

/-- **The then-clause of a closed member in every model**: a box of the consulted code at the frame `(me, opp)`
makes the bot-wrapped member play its then-action at fuel `4`. -/
theorem member_then_V (S : Sys2) (j : ℕ) (hj : j ≤ 1) (k me opp : V)
    (h : LenBox TAct k (guardCodeB (sysCloseTemplate (S.D k) ((⌜(S.mem j).g⌝ : ℕ) : V)) me opp k)) :
    EvalGraph 4 me opp (pBot (S.code j k)) ((S.mem j).a : V) := by
  rw [show (4 : V) = 3 + 1 from three_add_one_eq_four.symm, EvalGraph.bot_iff,
    show (3 : V) = 2 + 1 from two_add_one_eq_three.symm]
  unfold code
  rw [EvalGraph.sys_iff]
  refine ⟨_, listGet_D S j hj k, ?_⟩
  rw [sysCloseCode_mem, show (2 : V) = 1 + 1 from one_add_one_eq_two.symm, EvalGraph.search_iff,
    guardCodeB_sysCloseTemplateAt]
  exact Or.inl ⟨h, by rw [show (1 : V) = 0 + 1 by simp, EvalGraph.const_iff]⟩

/-- **The else-clause**: no box, the else-action. -/
theorem member_else_V (S : Sys2) (j : ℕ) (hj : j ≤ 1) (k me opp : V)
    (h : ¬ LenBox TAct k (guardCodeB (sysCloseTemplate (S.D k) ((⌜(S.mem j).g⌝ : ℕ) : V)) me opp k)) :
    EvalGraph 4 me opp (pBot (S.code j k)) ((1 - (S.mem j).a : ℕ) : V) := by
  rw [show (4 : V) = 3 + 1 from three_add_one_eq_four.symm, EvalGraph.bot_iff,
    show (3 : V) = 2 + 1 from two_add_one_eq_three.symm]
  unfold code
  rw [EvalGraph.sys_iff]
  refine ⟨_, listGet_D S j hj k, ?_⟩
  rw [sysCloseCode_mem, show (2 : V) = 1 + 1 from one_add_one_eq_two.symm, EvalGraph.search_iff,
    guardCodeB_sysCloseTemplateAt]
  exact Or.inr ⟨h, by rw [show (1 : V) = 0 + 1 by simp, EvalGraph.const_iff]⟩

end Sys2

end ArithS.Tau
