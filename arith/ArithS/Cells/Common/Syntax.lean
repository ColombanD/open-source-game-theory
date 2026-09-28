import ArithS.Assembly.Prep
import ArithS.Agents.InstanceV
import ArithS.Eval.SimTest
import ArithS.Agents.Template
import ArithS.Eval.EvalN

/-!
# ArithS.Cells.Common.Syntax — the arity-generic syntax lemmas shared by every `Cells/*` file

Consolidation stage 1 (`Research/Notes/ROUTE_B_CELLS_MAP.md`, 2026-09-24): the declarations below were
written once per cell file (JustSlot, DIMCID, JustBot, PrudentMirror, DimcidFlips, DupocMirror,
PositiveCells) and MOVED here unchanged — same names, same statements, same proofs. Nothing in this
module depends on a bot: it sits directly on `Assembly/Prep`, `InstanceV`, `SimTest`, `Template` and
`EvalN` (option B of the map: `Prep`'s one-variable `₁` lemmas stay where they are).

* Quotes and the code-level τ at arities four, six and seven: `quote_emb_castLE_V`,
  `semiterm_quote_emb_n/₄/₇`, `isSemiformula_quote₄/₇`, `coe_quote_sentence₆/₇`,
  `relabelTemplate_quote_sentence₆_V/₇_V`, `four_eq`.
* The entries of the description vectors: `nth_descVec_three/four/five`, `nth_descVecB_zero…six`; the
  τ-equivariance of `guardCodeB`: `termRelabelVec_descVecB`, `relabelTemplate_guardCodeB`.
* Tower substitution: `termSubst_tower_of` (any vector whose head is `bnum k`), `termSubst_tower'`
  (the then-slot holds a term code whose own instance is a program).
* Absoluteness of the canonical code: `cast_swapcode`, `cast_dnum`; `quote_emb_numT`.
* The `pBot` algebra (`pBot_le_pBot_iff`, `swapcode_pBot`, `dnum/dU/dW_pBot`, `swapcode_pBot_DupocV`)
  and the `pConst` facts (`pConst_zero_lt_one`, `swapcode/dnum/dU/dW_pConst_zero/one`).
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
`Prep.relabelTemplate_quote_sentence_V`). -/
lemma relabelTemplate_quote_sentence₆_V (σ : Semisentence LAct 6) :
    relabelTemplate 1 0 (⌜σ⌝ : V) = ⌜Semiformula.lMap swap σ⌝ := by
  have h := DefinedFunction.shigmaOne_absolute_func V (relabelTemplate.defined (V := ℕ))
    (relabelTemplate.defined (V := V)) ![1, 0, (⌜σ⌝ : ℕ)]
  simp only [Function.comp_def, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_succ, Matrix.vecHead, Matrix.vecTail, Nat.cast_one, Nat.cast_zero] at h
  rw [relabelTemplate_quote_sentence, coe_quote_sentence₆, coe_quote_sentence₆] at h
  exact h.symm

end quotes

/-! ### 2. Description vectors and the τ-equivariance of `guardCodeB` -/

section descVec

lemma nth_descVec_three (me opp : V) : (descVec me opp).[3] = progT (dnum opp) := by
  unfold descVec
  rw [show (3 : V) = 2 + 1 by norm_num, nth_adjoin_succ, nth_adjoin_two, nth_adjoin_one, nth_adjoin_zero]

lemma nth_descVec_four (me opp : V) : (descVec me opp).[4] = dU opp := by
  unfold descVec
  rw [show (4 : V) = 3 + 1 by norm_num, nth_adjoin_succ, show (3 : V) = 2 + 1 by norm_num, nth_adjoin_succ,
    nth_adjoin_two, nth_adjoin_one, nth_adjoin_zero]

lemma nth_descVec_five (me opp : V) : (descVec me opp).[5] = dW opp := by
  unfold descVec
  rw [show (5 : V) = 4 + 1 by norm_num, nth_adjoin_succ, show (4 : V) = 3 + 1 by norm_num, nth_adjoin_succ,
    show (3 : V) = 2 + 1 by norm_num, nth_adjoin_succ, nth_adjoin_two, nth_adjoin_one, nth_adjoin_zero]

/-! #### The entries of `descVecB` -/

lemma nth_descVecB_zero (me opp k : V) : (descVecB me opp k).[0] = progT (dnum me) := by
  unfold descVecB; rw [nth_adjoin_zero]

lemma nth_descVecB_one (me opp k : V) : (descVecB me opp k).[1] = dU me := by
  unfold descVecB; simp only [nth_adjoin_zero, nth_adjoin_one]

lemma nth_descVecB_two (me opp k : V) : (descVecB me opp k).[2] = dW me := by
  unfold descVecB; simp only [nth_adjoin_zero, nth_adjoin_one, nth_adjoin_two]

lemma nth_descVecB_three (me opp k : V) : (descVecB me opp k).[3] = progT (dnum opp) := by
  unfold descVecB
  rw [show (3 : V) = 2 + 1 by norm_num, nth_adjoin_succ]
  simp only [nth_adjoin_zero, nth_adjoin_one, nth_adjoin_two]

lemma nth_descVecB_four (me opp k : V) : (descVecB me opp k).[4] = dU opp := by
  unfold descVecB
  rw [show (4 : V) = 2 + 1 + 1 by norm_num, nth_adjoin_succ, nth_adjoin_succ]
  simp only [nth_adjoin_zero, nth_adjoin_one, nth_adjoin_two]

lemma nth_descVecB_five (me opp k : V) : (descVecB me opp k).[5] = dW opp := by
  unfold descVecB
  rw [show (5 : V) = 2 + 1 + 1 + 1 by norm_num, nth_adjoin_succ, nth_adjoin_succ, nth_adjoin_succ]
  simp only [nth_adjoin_zero, nth_adjoin_one, nth_adjoin_two]

lemma nth_descVecB_six (me opp k : V) : (descVecB me opp k).[6] = bnum k := by
  unfold descVecB
  rw [show (6 : V) = 2 + 1 + 1 + 1 + 1 by norm_num, nth_adjoin_succ, nth_adjoin_succ, nth_adjoin_succ,
    nth_adjoin_succ]
  simp only [nth_adjoin_zero, nth_adjoin_one, nth_adjoin_two]

/-! #### τ-equivariance of `guardCodeB` -/

/-- The code-level τ maps `descVecB me opp k` entrywise to `descVecB (swapcode me) (swapcode opp) k`. -/
theorem termRelabelVec_descVecB (me opp k : V) :
    termRelabelVec 1 0 7 (descVecB me opp k) = descVecB (swapcode me) (swapcode opp) k := by
  have e0 : IsUTermVec LAct 0 (0 : V) := IsUTermVec.empty
  have h0 : IsUTermVec LAct (0 + 1) (bnum k ∷ (0 : V)) := e0.adjoin (bnum_semiterm_LAct 0 k).isUTerm
  have h1 : IsUTermVec LAct (0 + 1 + 1) (dW opp ∷ bnum k ∷ (0 : V)) := h0.adjoin (dW_semiterm 0 opp).isUTerm
  have h2 : IsUTermVec LAct (0 + 1 + 1 + 1) (dU opp ∷ dW opp ∷ bnum k ∷ (0 : V)) :=
    h1.adjoin (dU_semiterm 0 opp).isUTerm
  have h3 : IsUTermVec LAct (0 + 1 + 1 + 1 + 1) (progT (dnum opp) ∷ dU opp ∷ dW opp ∷ bnum k ∷ (0 : V)) :=
    h2.adjoin (progT_semiterm_LAct 0 (dnum opp)).isUTerm
  have h4 : IsUTermVec LAct (0 + 1 + 1 + 1 + 1 + 1)
      (dW me ∷ progT (dnum opp) ∷ dU opp ∷ dW opp ∷ bnum k ∷ (0 : V)) :=
    h3.adjoin (dW_semiterm 0 me).isUTerm
  have h5 : IsUTermVec LAct (0 + 1 + 1 + 1 + 1 + 1 + 1)
      (dU me ∷ dW me ∷ progT (dnum opp) ∷ dU opp ∷ dW opp ∷ bnum k ∷ (0 : V)) :=
    h4.adjoin (dU_semiterm 0 me).isUTerm
  unfold descVecB
  rw [seven_eq, termRelabelVec_cons (progT_semiterm_LAct 0 (dnum me)).isUTerm h5,
    termRelabelVec_cons (dU_semiterm 0 me).isUTerm h4, termRelabelVec_cons (dW_semiterm 0 me).isUTerm h3,
    termRelabelVec_cons (progT_semiterm_LAct 0 (dnum opp)).isUTerm h2,
    termRelabelVec_cons (dU_semiterm 0 opp).isUTerm h1,
    termRelabelVec_cons (dW_semiterm 0 opp).isUTerm h0,
    termRelabelVec_cons (bnum_semiterm_LAct 0 k).isUTerm e0, termRelabelVec_nil,
    termRelabel_progT, termRelabel_progT, termRelabel_dU, termRelabel_dU, termRelabel_dW, termRelabel_dW,
    termRelabel_bnum, dnum_swapcode, dnum_swapcode]

/-- **The swap equation for `guardCodeB`** on seven-variable templates. -/
theorem relabelTemplate_guardCodeB {g : V} (hg : IsSemiformula LAct 7 g) (me opp k : V) :
    relabelTemplate 1 0 (guardCodeB g me opp k) =
      guardCodeB (relabelTemplate 1 0 g) (swapcode me) (swapcode opp) k := by
  unfold guardCodeB
  rw [relabelTemplate_subst isAct_one isAct_zero hg (descVecB_semitermVec me opp k), termRelabelVec_descVecB]

lemma coe_quote_sentence₇ (σ : Semisentence LAct 7) : ((⌜σ⌝ : ℕ) : V) = ⌜σ⌝ := by
  rw [Sentence.quote_def, Sentence.quote_def, Semiformula.coe_quote_eq_quote]

/-- The code-level τ of a seven-variable template code, in every model. -/
lemma relabelTemplate_quote_sentence₇_V (σ : Semisentence LAct 7) :
    relabelTemplate 1 0 (⌜σ⌝ : V) = ⌜Semiformula.lMap swap σ⌝ := by
  have h := DefinedFunction.shigmaOne_absolute_func V (relabelTemplate.defined (V := ℕ))
    (relabelTemplate.defined (V := V)) ![1, 0, (⌜σ⌝ : ℕ)]
  simp only [Function.comp_def, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_succ, Matrix.vecHead, Matrix.vecTail, Nat.cast_one, Nat.cast_zero] at h
  rw [relabelTemplate_quote_sentence, coe_quote_sentence₇, coe_quote_sentence₇] at h
  exact h.symm

end descVec

/-! ### 3. Tower substitution -/

section tower

/-- The searcher tower under ANY substitution vector whose head is `bnum k`. -/
theorem termSubst_tower_of (w k g p q : V) (h0 : w.[0] = bnum k) :
    termSubst LAct w
      (ppairT (bnum 6) (ppairT (^#0) (ppairT (bnum g) (ppairT (progT p) (progT q)))) ^+ 𝟏) =
    progT (pSearch k g p q) := by
  have hb6 : IsUTerm LAct (bnum (6 : V)) := (bnum_semiterm_LAct 0 _).isUTerm
  have hbg : IsUTerm LAct (bnum g) := (bnum_semiterm_LAct 0 _).isUTerm
  have hp : IsUTerm LAct (progT p) := (progT_semiterm_LAct 0 _).isUTerm
  have hq : IsUTerm LAct (progT q) := (progT_semiterm_LAct 0 _).isUTerm
  have h1 : IsUTerm LAct (ppairT (progT p) (progT q)) := ppairT_uterm_LAct hp hq
  have h2 : IsUTerm LAct (ppairT (bnum g) (ppairT (progT p) (progT q))) := ppairT_uterm_LAct hbg h1
  have h3 : IsUTerm LAct (ppairT (^#0) (ppairT (bnum g) (ppairT (progT p) (progT q)))) :=
    ppairT_uterm_LAct bvar_zero_uterm h2
  have h4 : IsUTerm LAct (ppairT (bnum 6) (ppairT (^#0) (ppairT (bnum g) (ppairT (progT p) (progT q))))) :=
    ppairT_uterm_LAct hb6 h3
  have hone : IsUTerm LAct (𝟏 : V) := (IsSemiterm.LAct_of_LOR (one_semiterm (n := 0))).isUTerm
  rw [termSubst_qqAdd _ h4 hone, termSubst_ppairT _ hb6 h3, termSubst_ppairT _ bvar_zero_uterm h2,
    termSubst_ppairT _ hbg h1, termSubst_ppairT _ hp hq, termSubst_bvar, h0,
    termSubst_closed _ (bnum_semiterm_LAct 0 _), termSubst_closed _ (bnum_semiterm_LAct 0 _),
    termSubst_closed _ (progT_semiterm_LAct 0 _), termSubst_closed _ (progT_semiterm_LAct 0 _),
    termSubst_closed _ (IsSemiterm.LAct_of_LOR one_semiterm), progT_search]

/-- **Filling the budget slot of a two-level tower**: the then-slot holds a term code `P` whose own
`bnum k`-instance is the structural term of `p`. -/
theorem termSubst_tower' (k g q : V) {P p : V} (hP : IsUTerm LAct P)
    (hPs : termSubst LAct (bnum k ∷ (0 : V)) P = progT p) :
    termSubst LAct (bnum k ∷ (0 : V))
      (ppairT (bnum 6) (ppairT (^#0) (ppairT (bnum g) (ppairT P (progT q)))) ^+ 𝟏) =
    progT (pSearch k g p q) := by
  have hb6 : IsUTerm LAct (bnum (6 : V)) := (bnum_semiterm_LAct 0 _).isUTerm
  have hbg : IsUTerm LAct (bnum g) := (bnum_semiterm_LAct 0 _).isUTerm
  have hq : IsUTerm LAct (progT q) := (progT_semiterm_LAct 0 _).isUTerm
  have h1 : IsUTerm LAct (ppairT P (progT q)) := ppairT_uterm_LAct hP hq
  have h2 : IsUTerm LAct (ppairT (bnum g) (ppairT P (progT q))) := ppairT_uterm_LAct hbg h1
  have h3 : IsUTerm LAct (ppairT (^#0) (ppairT (bnum g) (ppairT P (progT q)))) :=
    ppairT_uterm_LAct bvar_zero_uterm h2
  have h4 : IsUTerm LAct (ppairT (bnum 6) (ppairT (^#0) (ppairT (bnum g) (ppairT P (progT q))))) :=
    ppairT_uterm_LAct hb6 h3
  have hone : IsUTerm LAct (𝟏 : V) := (IsSemiterm.LAct_of_LOR (one_semiterm (n := 0))).isUTerm
  rw [termSubst_qqAdd _ h4 hone, termSubst_ppairT _ hb6 h3, termSubst_ppairT _ bvar_zero_uterm h2,
    termSubst_ppairT _ hbg h1, termSubst_ppairT _ hP hq, termSubst_bvar, nth_adjoin_zero,
    termSubst_closed _ (bnum_semiterm_LAct 0 _), termSubst_closed _ (bnum_semiterm_LAct 0 _),
    termSubst_closed _ (progT_semiterm_LAct 0 _),
    termSubst_closed _ (IsSemiterm.LAct_of_LOR one_semiterm), hPs, progT_search]

end tower

/-! ### 4. Absoluteness of the canonical code; numerals -/

section casts

/-- `swapcode` is absolute (it is `relabel 1 0`, a Σ₁-definable function: `cast_relabel`). -/
lemma cast_swapcode (x : ℕ) : ((swapcode x : ℕ) : V) = swapcode (x : V) := by
  have := cast_relabel (V := V) 1 0 x
  rwa [Nat.cast_one, Nat.cast_zero] at this

/-- `dnum` is absolute (a Σ₁-definable function). -/
lemma cast_dnum (x : ℕ) : ((dnum x : ℕ) : V) = dnum (x : V) := by
  have := DefinedFunction.shigmaOne_absolute_func V (dnum.defined (V := ℕ)) (dnum.defined (V := V)) ![x]
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

lemma swapcode_pBot (p : V) : swapcode (pBot p) = pBot (swapcode p) := by
  unfold swapcode; simp

/-- The canonical numeral commutes with bot-wrapping (`pBot` is strictly monotone). -/
lemma dnum_pBot (p : V) : dnum (pBot p) = pBot (dnum p) := by
  unfold dnum
  rw [swapcode_pBot]
  simp only [pBot_le_pBot_iff, apply_ite pBot]

lemma dU_pBot (p : V) : dU (pBot p) = dU p := by
  unfold dU
  rw [swapcode_pBot]
  simp only [pBot_lt_pBot_iff]

lemma dW_pBot (p : V) : dW (pBot p) = dW p := by
  unfold dW
  rw [swapcode_pBot]
  simp only [pBot_lt_pBot_iff]

lemma swapcode_pBot_DupocV (k : V) : swapcode (pBot (DupocV k)) = pBot (CupodV k) := by
  rw [swapcode_pBot, swapcode_DupocV]

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

end codes

end ArithS
