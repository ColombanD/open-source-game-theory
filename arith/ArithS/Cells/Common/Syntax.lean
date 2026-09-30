import ArithS.Assembly.Prep
import ArithS.Agents.InstanceV
import ArithS.Eval.SimTest
import ArithS.Agents.Template
import ArithS.Eval.EvalN

/-!
# ArithS.Cells.Common.Syntax — the arity-generic syntax lemmas shared by every `Cells/*` file

Consolidation stage 1 (`Research/Notes/ROUTE_B_CELLS_MAP.md`): the declarations below were
written once per cell file (JustSlot, DIMCID, JustBot, PrudentMirror, DimcidFlips, DupocMirror,
PositiveCells) and MOVED here unchanged — same names, same statements, same proofs. Nothing in this
module depends on a bot: it sits directly on `Assembly/Prep`, `InstanceV`, `SimTest`, `Template` and
`EvalN` (option B of the map: `Prep`'s one-variable `₁` lemmas stay where they are).

* Quotes and the code-level τ at arities four, six and seven: `quote_emb_castLE_V`,
  `semiterm_quote_emb_n/₄/₇`, `isSemiformula_quote₄/₇`, `coe_quote_sentence₆/₇`,
  `revalueTemplate_quote_sentence₆_V/₇_V`, `four_eq`.
* The entries of the description vectors: `nth_descriptions_three/four/five`, `nth_descriptionsB_zero…six`; the
  τ-equivariance of `guardCodeB`: `termRelabelVec_descriptionsB`, `revalueTemplate_guardCodeB`.
* Tower substitution: `termSubst_tower_of` (any vector whose head is `binNumeral k`), `termSubst_tower'`
  (the then-slot holds a term code whose own instance is a program).
* Absoluteness of the canonical code: `cast_transposeCode`, `cast_canonical`; `quote_emb_numT`.
* The `pBot` algebra (`pBot_le_pBot_iff`, `transposeCode_pBot`, `canonical/revalueU/revalueW_pBot`, `transposeCode_pBot_DupocV`)
  and the `pConst` facts (`pConst_zero_lt_one`, `transposeCode/canonical/revalueU/revalueW_pConst_zero/one`).
-/

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open LAct

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ### 1. Quotes, casts and the code-level τ at arities four, six and seven -/

section quotes

/-- The code of a term cast into more bound variables is the code of the term. -/
lemma quote_emb_castLE_V {n m : ℕ} (h : n ≤ m) :
    ∀ t : Semiterm LAct Empty n,
      (⌜(Rew.emb (Rew.castLE h t) : SyntacticSemiterm LAct m)⌝ : V) = ⌜(Rew.emb t : SyntacticSemiterm LAct n)⌝
  | #x => by simp [Rew.emb]
  | &x => x.elim
  | .func f v => by
    rw [Rew.func, Rew.func, Rew.func, Semiterm.quote_func, Semiterm.quote_func]
    congr 1
    unfold SemitermVec.val
    exact matrixToVec_congr (fun i ↦ quote_emb_castLE_V h (v i))

/-- The code of an embedded `n`-variable term is an `n`-variable term code. -/
lemma semiterm_quote_emb_n {n : ℕ} (t : Semiterm LAct Empty n) :
    IsSemiterm LAct ((n : ℕ) : V) (⌜(Rew.emb t : SyntacticSemiterm LAct n)⌝ : V) := by
  rw [Semiterm.quote_def]
  exact (⌜(Rew.emb t : SyntacticSemiterm LAct n)⌝ : Bootstrapping.Semiterm V LAct n).isSemiterm

lemma semiterm_quote_emb₄ (t : Semiterm LAct Empty 4) :
    IsSemiterm LAct 4 (⌜(Rew.emb t : SyntacticSemiterm LAct 4)⌝ : V) := by
  simpa using semiterm_quote_emb_n (V := V) t

lemma semiterm_quote_emb₇ (t : Semiterm LAct Empty 7) :
    IsSemiterm LAct 7 (⌜(Rew.emb t : SyntacticSemiterm LAct 7)⌝ : V) := by
  simpa using semiterm_quote_emb_n (V := V) t

/-- The code of a closed four- or seven-variable semisentence is a template of that arity. -/
lemma isSemiformula_quote₄ (φ : Semisentence LAct 4) : IsSemiformula LAct 4 (⌜φ⌝ : V) := by
  simpa using Sentence.quote_isSemiformula (V := V) φ

lemma isSemiformula_quote₇ (φ : Semisentence LAct 7) : IsSemiformula LAct 7 (⌜φ⌝ : V) := by
  simpa using Sentence.quote_isSemiformula (V := V) φ

lemma four_eq : (4 : V) = 0 + 1 + 1 + 1 + 1 := by norm_num

lemma coe_quote_sentence₆ (σ : Semisentence LAct 6) : ((⌜σ⌝ : ℕ) : V) = ⌜σ⌝ := by
  rw [Sentence.quote_def, Sentence.quote_def, Semiformula.coe_quote_eq_quote]

/-- The code-level τ of a six-variable template code, in every model (as
`Prep.revalueTemplate_quote_sentence_V`). -/
lemma revalueTemplate_quote_sentence₆_V (σ : Semisentence LAct 6) :
    revalueTemplate 1 0 (⌜σ⌝ : V) = ⌜Semiformula.lMap swap σ⌝ := by
  have h := DefinedFunction.shigmaOne_absolute_func V (revalueTemplate.defined (V := ℕ))
    (revalueTemplate.defined (V := V)) ![1, 0, (⌜σ⌝ : ℕ)]
  simp only [Function.comp_def, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_succ, Matrix.vecHead, Matrix.vecTail, Nat.cast_one, Nat.cast_zero] at h
  rw [revalueTemplate_quote_sentence, coe_quote_sentence₆, coe_quote_sentence₆] at h
  exact h.symm

end quotes

/-! ### 2. Description vectors and the τ-equivariance of `guardCodeB` -/

section descriptions

lemma nth_descriptions_three (me opp : V) : (descriptions me opp).[3] = codeTerm (canonical opp) := by
  unfold descriptions
  rw [show (3 : V) = 2 + 1 by norm_num, nth_adjoin_succ, nth_adjoin_two, nth_adjoin_one, nth_adjoin_zero]

lemma nth_descriptions_four (me opp : V) : (descriptions me opp).[4] = revalueU opp := by
  unfold descriptions
  rw [show (4 : V) = 3 + 1 by norm_num, nth_adjoin_succ, show (3 : V) = 2 + 1 by norm_num, nth_adjoin_succ,
    nth_adjoin_two, nth_adjoin_one, nth_adjoin_zero]

lemma nth_descriptions_five (me opp : V) : (descriptions me opp).[5] = revalueW opp := by
  unfold descriptions
  rw [show (5 : V) = 4 + 1 by norm_num, nth_adjoin_succ, show (4 : V) = 3 + 1 by norm_num, nth_adjoin_succ,
    show (3 : V) = 2 + 1 by norm_num, nth_adjoin_succ, nth_adjoin_two, nth_adjoin_one, nth_adjoin_zero]

/-! #### The entries of `descriptionsB` -/

lemma nth_descriptionsB_zero (me opp k : V) : (descriptionsB me opp k).[0] = codeTerm (canonical me) := by
  unfold descriptionsB; rw [nth_adjoin_zero]

lemma nth_descriptionsB_one (me opp k : V) : (descriptionsB me opp k).[1] = revalueU me := by
  unfold descriptionsB; simp only [nth_adjoin_zero, nth_adjoin_one]

lemma nth_descriptionsB_two (me opp k : V) : (descriptionsB me opp k).[2] = revalueW me := by
  unfold descriptionsB; simp only [nth_adjoin_zero, nth_adjoin_one, nth_adjoin_two]

lemma nth_descriptionsB_three (me opp k : V) : (descriptionsB me opp k).[3] = codeTerm (canonical opp) := by
  unfold descriptionsB
  rw [show (3 : V) = 2 + 1 by norm_num, nth_adjoin_succ]
  simp only [nth_adjoin_zero, nth_adjoin_one, nth_adjoin_two]

lemma nth_descriptionsB_four (me opp k : V) : (descriptionsB me opp k).[4] = revalueU opp := by
  unfold descriptionsB
  rw [show (4 : V) = 2 + 1 + 1 by norm_num, nth_adjoin_succ, nth_adjoin_succ]
  simp only [nth_adjoin_zero, nth_adjoin_one, nth_adjoin_two]

lemma nth_descriptionsB_five (me opp k : V) : (descriptionsB me opp k).[5] = revalueW opp := by
  unfold descriptionsB
  rw [show (5 : V) = 2 + 1 + 1 + 1 by norm_num, nth_adjoin_succ, nth_adjoin_succ, nth_adjoin_succ]
  simp only [nth_adjoin_zero, nth_adjoin_one, nth_adjoin_two]

lemma nth_descriptionsB_six (me opp k : V) : (descriptionsB me opp k).[6] = binNumeral k := by
  unfold descriptionsB
  rw [show (6 : V) = 2 + 1 + 1 + 1 + 1 by norm_num, nth_adjoin_succ, nth_adjoin_succ, nth_adjoin_succ,
    nth_adjoin_succ]
  simp only [nth_adjoin_zero, nth_adjoin_one, nth_adjoin_two]

/-! #### τ-equivariance of `guardCodeB` -/

/-- The code-level τ maps `descriptionsB me opp k` entrywise to `descriptionsB (transposeCode me) (transposeCode opp) k`. -/
theorem termRelabelVec_descriptionsB (me opp k : V) :
    termRelabelVec 1 0 7 (descriptionsB me opp k) = descriptionsB (transposeCode me) (transposeCode opp) k := by
  have e0 : IsUTermVec LAct 0 (0 : V) := IsUTermVec.empty
  have h0 : IsUTermVec LAct (0 + 1) (binNumeral k ∷ (0 : V)) := e0.adjoin (binNumeral_semiterm_LAct 0 k).isUTerm
  have h1 : IsUTermVec LAct (0 + 1 + 1) (revalueW opp ∷ binNumeral k ∷ (0 : V)) := h0.adjoin (revalueW_semiterm 0 opp).isUTerm
  have h2 : IsUTermVec LAct (0 + 1 + 1 + 1) (revalueU opp ∷ revalueW opp ∷ binNumeral k ∷ (0 : V)) :=
    h1.adjoin (revalueU_semiterm 0 opp).isUTerm
  have h3 : IsUTermVec LAct (0 + 1 + 1 + 1 + 1) (codeTerm (canonical opp) ∷ revalueU opp ∷ revalueW opp ∷ binNumeral k ∷ (0 : V)) :=
    h2.adjoin (codeTerm_semiterm_LAct 0 (canonical opp)).isUTerm
  have h4 : IsUTermVec LAct (0 + 1 + 1 + 1 + 1 + 1)
      (revalueW me ∷ codeTerm (canonical opp) ∷ revalueU opp ∷ revalueW opp ∷ binNumeral k ∷ (0 : V)) :=
    h3.adjoin (revalueW_semiterm 0 me).isUTerm
  have h5 : IsUTermVec LAct (0 + 1 + 1 + 1 + 1 + 1 + 1)
      (revalueU me ∷ revalueW me ∷ codeTerm (canonical opp) ∷ revalueU opp ∷ revalueW opp ∷ binNumeral k ∷ (0 : V)) :=
    h4.adjoin (revalueU_semiterm 0 me).isUTerm
  unfold descriptionsB
  rw [seven_eq, termRelabelVec_cons (codeTerm_semiterm_LAct 0 (canonical me)).isUTerm h5,
    termRelabelVec_cons (revalueU_semiterm 0 me).isUTerm h4, termRelabelVec_cons (revalueW_semiterm 0 me).isUTerm h3,
    termRelabelVec_cons (codeTerm_semiterm_LAct 0 (canonical opp)).isUTerm h2,
    termRelabelVec_cons (revalueU_semiterm 0 opp).isUTerm h1,
    termRelabelVec_cons (revalueW_semiterm 0 opp).isUTerm h0,
    termRelabelVec_cons (binNumeral_semiterm_LAct 0 k).isUTerm e0, termRelabelVec_nil,
    termRelabel_codeTerm, termRelabel_codeTerm, termRelabel_revalueU, termRelabel_revalueU, termRelabel_revalueW, termRelabel_revalueW,
    termRelabel_binNumeral, canonical_transposeCode, canonical_transposeCode]

/-- **The swap equation for `guardCodeB`** on seven-variable templates. -/
theorem revalueTemplate_guardCodeB {g : V} (hg : IsSemiformula LAct 7 g) (me opp k : V) :
    revalueTemplate 1 0 (guardCodeB g me opp k) =
      guardCodeB (revalueTemplate 1 0 g) (transposeCode me) (transposeCode opp) k := by
  unfold guardCodeB
  rw [revalueTemplate_subst isAct_one isAct_zero hg (descriptionsB_semitermVec me opp k), termRelabelVec_descriptionsB]

lemma coe_quote_sentence₇ (σ : Semisentence LAct 7) : ((⌜σ⌝ : ℕ) : V) = ⌜σ⌝ := by
  rw [Sentence.quote_def, Sentence.quote_def, Semiformula.coe_quote_eq_quote]

/-- The code-level τ of a seven-variable template code, in every model. -/
lemma revalueTemplate_quote_sentence₇_V (σ : Semisentence LAct 7) :
    revalueTemplate 1 0 (⌜σ⌝ : V) = ⌜Semiformula.lMap swap σ⌝ := by
  have h := DefinedFunction.shigmaOne_absolute_func V (revalueTemplate.defined (V := ℕ))
    (revalueTemplate.defined (V := V)) ![1, 0, (⌜σ⌝ : ℕ)]
  simp only [Function.comp_def, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_succ, Matrix.vecHead, Matrix.vecTail, Nat.cast_one, Nat.cast_zero] at h
  rw [revalueTemplate_quote_sentence, coe_quote_sentence₇, coe_quote_sentence₇] at h
  exact h.symm

end descriptions

/-! ### 3. Tower substitution -/

section tower

/-- The searcher tower under ANY substitution vector whose head is `binNumeral k`. -/
theorem termSubst_tower_of (w k g p q : V) (h0 : w.[0] = binNumeral k) :
    termSubst LAct w
      (ppairTerm (binNumeral 6) (ppairTerm (^#0) (ppairTerm (binNumeral g) (ppairTerm (codeTerm p) (codeTerm q)))) ^+ 𝟏) =
    codeTerm (pSearch k g p q) := by
  have hb6 : IsUTerm LAct (binNumeral (6 : V)) := (binNumeral_semiterm_LAct 0 _).isUTerm
  have hbg : IsUTerm LAct (binNumeral g) := (binNumeral_semiterm_LAct 0 _).isUTerm
  have hp : IsUTerm LAct (codeTerm p) := (codeTerm_semiterm_LAct 0 _).isUTerm
  have hq : IsUTerm LAct (codeTerm q) := (codeTerm_semiterm_LAct 0 _).isUTerm
  have h1 : IsUTerm LAct (ppairTerm (codeTerm p) (codeTerm q)) := ppairTerm_uterm_LAct hp hq
  have h2 : IsUTerm LAct (ppairTerm (binNumeral g) (ppairTerm (codeTerm p) (codeTerm q))) := ppairTerm_uterm_LAct hbg h1
  have h3 : IsUTerm LAct (ppairTerm (^#0) (ppairTerm (binNumeral g) (ppairTerm (codeTerm p) (codeTerm q)))) :=
    ppairTerm_uterm_LAct bvar_zero_uterm h2
  have h4 : IsUTerm LAct (ppairTerm (binNumeral 6) (ppairTerm (^#0) (ppairTerm (binNumeral g) (ppairTerm (codeTerm p) (codeTerm q))))) :=
    ppairTerm_uterm_LAct hb6 h3
  have hone : IsUTerm LAct (𝟏 : V) := (IsSemiterm.LAct_of_LOR (one_semiterm (n := 0))).isUTerm
  rw [termSubst_qqAdd _ h4 hone, termSubst_ppairTerm _ hb6 h3, termSubst_ppairTerm _ bvar_zero_uterm h2,
    termSubst_ppairTerm _ hbg h1, termSubst_ppairTerm _ hp hq, termSubst_bvar, h0,
    termSubst_closed _ (binNumeral_semiterm_LAct 0 _), termSubst_closed _ (binNumeral_semiterm_LAct 0 _),
    termSubst_closed _ (codeTerm_semiterm_LAct 0 _), termSubst_closed _ (codeTerm_semiterm_LAct 0 _),
    termSubst_closed _ (IsSemiterm.LAct_of_LOR one_semiterm), codeTerm_search]

/-- **Filling the budget slot of a two-level tower**: the then-slot holds a term code `P` whose own
`binNumeral k`-instance is the structural term of `p`. -/
theorem termSubst_tower' (k g q : V) {P p : V} (hP : IsUTerm LAct P)
    (hPs : termSubst LAct (binNumeral k ∷ (0 : V)) P = codeTerm p) :
    termSubst LAct (binNumeral k ∷ (0 : V))
      (ppairTerm (binNumeral 6) (ppairTerm (^#0) (ppairTerm (binNumeral g) (ppairTerm P (codeTerm q)))) ^+ 𝟏) =
    codeTerm (pSearch k g p q) := by
  have hb6 : IsUTerm LAct (binNumeral (6 : V)) := (binNumeral_semiterm_LAct 0 _).isUTerm
  have hbg : IsUTerm LAct (binNumeral g) := (binNumeral_semiterm_LAct 0 _).isUTerm
  have hq : IsUTerm LAct (codeTerm q) := (codeTerm_semiterm_LAct 0 _).isUTerm
  have h1 : IsUTerm LAct (ppairTerm P (codeTerm q)) := ppairTerm_uterm_LAct hP hq
  have h2 : IsUTerm LAct (ppairTerm (binNumeral g) (ppairTerm P (codeTerm q))) := ppairTerm_uterm_LAct hbg h1
  have h3 : IsUTerm LAct (ppairTerm (^#0) (ppairTerm (binNumeral g) (ppairTerm P (codeTerm q)))) :=
    ppairTerm_uterm_LAct bvar_zero_uterm h2
  have h4 : IsUTerm LAct (ppairTerm (binNumeral 6) (ppairTerm (^#0) (ppairTerm (binNumeral g) (ppairTerm P (codeTerm q))))) :=
    ppairTerm_uterm_LAct hb6 h3
  have hone : IsUTerm LAct (𝟏 : V) := (IsSemiterm.LAct_of_LOR (one_semiterm (n := 0))).isUTerm
  rw [termSubst_qqAdd _ h4 hone, termSubst_ppairTerm _ hb6 h3, termSubst_ppairTerm _ bvar_zero_uterm h2,
    termSubst_ppairTerm _ hbg h1, termSubst_ppairTerm _ hP hq, termSubst_bvar, nth_adjoin_zero,
    termSubst_closed _ (binNumeral_semiterm_LAct 0 _), termSubst_closed _ (binNumeral_semiterm_LAct 0 _),
    termSubst_closed _ (codeTerm_semiterm_LAct 0 _),
    termSubst_closed _ (IsSemiterm.LAct_of_LOR one_semiterm), hPs, codeTerm_search]

end tower

/-! ### 4. Absoluteness of the canonical code; numerals -/

section casts

/-- `transposeCode` is absolute (it is `revalue 1 0`, a Σ₁-definable function: `cast_revalue`). -/
lemma cast_transposeCode (x : ℕ) : ((transposeCode x : ℕ) : V) = transposeCode (x : V) := by
  have := cast_revalue (V := V) 1 0 x
  rwa [Nat.cast_one, Nat.cast_zero] at this

/-- `canonical` is absolute (a Σ₁-definable function). -/
lemma cast_canonical (x : ℕ) : ((canonical x : ℕ) : V) = canonical (x : V) := by
  have := DefinedFunction.shigmaOne_absolute_func V (canonical.defined (V := ℕ)) (canonical.defined (V := V)) ![x]
  simpa [Function.comp_def] using this

lemma quote_emb_numT (a : ℕ) : (⌜(Rew.emb (numT a) : SyntacticSemiterm LAct 0)⌝ : V) = numeral (a : V) := by
  rw [← Semiterm.empty_quote_def, quote_numT]

end casts

/-! ### 5. The `pBot` algebra and the `pConst` facts -/

section codes

lemma pBot_le_pBot_iff {p q : V} : pBot p ≤ pBot q ↔ p ≤ q := by
  unfold pBot
  rw [add_le_add_iff_right, ppair_le_ppair_right_iff]

lemma pBot_lt_pBot_iff {p q : V} : pBot p < pBot q ↔ p < q := by
  rw [← not_le, ← not_le, pBot_le_pBot_iff]

lemma transposeCode_pBot (p : V) : transposeCode (pBot p) = pBot (transposeCode p) := by
  unfold transposeCode; simp

/-- The canonical numeral commutes with bot-wrapping (`pBot` is strictly monotone). -/
lemma canonical_pBot (p : V) : canonical (pBot p) = pBot (canonical p) := by
  unfold canonical
  rw [transposeCode_pBot]
  simp only [pBot_le_pBot_iff, apply_ite pBot]

lemma revalueU_pBot (p : V) : revalueU (pBot p) = revalueU p := by
  unfold revalueU
  rw [transposeCode_pBot]
  simp only [pBot_lt_pBot_iff]

lemma revalueW_pBot (p : V) : revalueW (pBot p) = revalueW p := by
  unfold revalueW
  rw [transposeCode_pBot]
  simp only [pBot_lt_pBot_iff]

lemma transposeCode_pBot_DupocV (k : V) : transposeCode (pBot (DupocV k)) = pBot (CupodV k) := by
  rw [transposeCode_pBot, transposeCode_DupocV]

lemma pConst_zero_lt_one : pConst (0 : V) < pConst 1 := by
  unfold pConst ppair; norm_num

lemma transposeCode_pConst_zero : transposeCode (pConst (0 : V)) = pConst 1 := by
  unfold transposeCode; rw [revalue_const]; simp [revalueAction]

lemma transposeCode_pConst_one : transposeCode (pConst (1 : V)) = pConst 0 := by
  unfold transposeCode; rw [revalue_const]; simp [revalueAction]

lemma canonical_pConst_zero : canonical (pConst (0 : V)) = pConst 0 :=
  canonical_of_lt (by rw [transposeCode_pConst_zero]; exact pConst_zero_lt_one)

lemma canonical_pConst_one : canonical (pConst (1 : V)) = pConst 0 := by
  rw [canonical_of_gt (by rw [transposeCode_pConst_one]; exact pConst_zero_lt_one), transposeCode_pConst_one]

lemma revalueU_pConst_zero : revalueU (pConst (0 : V)) = csym 0 := by
  unfold revalueU; rw [transposeCode_pConst_zero, if_pos pConst_zero_lt_one]

lemma revalueW_pConst_zero : revalueW (pConst (0 : V)) = csym 1 := by
  unfold revalueW; rw [transposeCode_pConst_zero, if_pos pConst_zero_lt_one]

lemma revalueU_pConst_one : revalueU (pConst (1 : V)) = csym 1 := by
  unfold revalueU; rw [transposeCode_pConst_one, if_neg (lt_asymm pConst_zero_lt_one), if_pos pConst_zero_lt_one]

lemma revalueW_pConst_one : revalueW (pConst (1 : V)) = csym 0 := by
  unfold revalueW; rw [transposeCode_pConst_one, if_neg (lt_asymm pConst_zero_lt_one), if_pos pConst_zero_lt_one]

end codes

end ArithS
