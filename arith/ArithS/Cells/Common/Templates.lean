import ArithS.Cells.Common.Bots

/-!
# ArithS.Cells.Common.Templates — template instances, instance/truth equations, the `Describes` layer

Consolidation stage 3 (`Research/Notes/ROUTE_B_CELLS_MAP.md`, 2026-09-24). Everything here was MOVED
unchanged (names, statements, definition bodies) out of `Cells/DIMCID`, `Cells/PrudentMirror`,
`Cells/JustBot`, `Cells/JustSlot`, `Cells/PositiveCells`, `Cells/FlipCells` and `Cells/DimcidFlips`:

1. **The hand-written template filled with two triples**: `qG a X U W X' U' W'`, the substitution
   vector `gVec`, `quote_qG`, `guardCode_GtmplA_eq_instB`/`_swap_eq_instB`, `eval_qG_iff_V`.
2. **An arbitrary six-variable template filled with two triples**: `qT g …`, `quote_qT`,
   `guardCode_qT_eq_instB`/`_swap_eq_instB`, `eval_qT_iff`, the closed-opponent atom
   `eval_template_plays_opp_closed_V`.
3. **JustBot's earlier form of the same equation** on `guardTemplate a ⇜ ![T₁, cl u₁, cl w₁, T₂, cl u₂, cl w₂]`:
   `templateVec` (kept as a definition with its original body; `templateVec_eq_gVec` is `rfl` — the two vectors
   are the same term, the arguments in a different order), `quote_GtmplA_subst`, `guardCode_eq_instB_of`,
   `eval_GtmplA_subst_iff`.
4. **The atom truths**: `eval_template_plays_self_opp_V`/`_opp_self_V` and the `qT`-level
   `eval_qT_plays_opp_self`/`eval_qT_neg_plays_opp_self`/`eval_qT_swap`.
5. **The Dupoc towers**: Cupod's description on the `TD` tower (`transposeCode_CupodV`, `revalueU/revalueW_CupodV`,
   `hX/hU/hW_cupod`, `hopp/descT_cupod`, `hX/hU/hW_dupoc`) and the bot tower `TBD` of `pBot (DupocV k)`
   (`val_TBD_V`, `quote_emb_TBD`, `termSubst_TBD`, `quote_emb_uD/wD_botDupocV`, `hX/hU/hW_botDupoc`,
   `hme/descT_botDupoc`).
6. **The `Describes` layer**: `descVal`, `Describes`, `DescribesAbove`, `Describes.above`; every closed
   code is described (`describes_closed`); the instances `describes_botCB`, `describes_TFT`,
   `describes_SV`, `describes_botSV`, `describes_dupocV`, `describes_botDupoc`. The tower-specific
   `describes_just7`/`describesAbove_prudent` stay with their towers; `loebSound_pG_of`/`_of_above`
   and the DIMCID row theorems stay downstream (they need `pG`).
-/

set_option linter.constructorNameAsVariable false

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open LAct
open PD.Bots

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ### 1. The hand-written template `guardTemplate a`, filled with two arbitrary description triples -/

section qG

/-- The template instance `guardTemplate a` filled with the triples `(X, U, W)` (me) and `(X', U', W')` (opp). -/
noncomputable def qG (a : ℕ) (X : Semiterm LAct Empty 1) (U W : ClosedSemiterm LAct 0)
    (X' : Semiterm LAct Empty 1) (U' W' : ClosedSemiterm LAct 0) : Semisentence LAct 1 :=
  guardTemplate a ⇜ ![X, cl U, cl W, X', cl U', cl W']

lemma lMap_swap_qG (a : ℕ) (X : Semiterm LAct Empty 1) (U W : ClosedSemiterm LAct 0)
    (X' : Semiterm LAct Empty 1) (U' W' : ClosedSemiterm LAct 0) :
    Semiformula.lMap swap (qG a X U W X' U' W') =
      qG (swapAction a) (Semiterm.lMap swap X) (Semiterm.lMap swap U) (Semiterm.lMap swap W)
        (Semiterm.lMap swap X') (Semiterm.lMap swap U') (Semiterm.lMap swap W') := by
  unfold qG
  rw [Semiformula.lMap_subst, lMap_swap_GtmplA]
  congr 1
  funext i
  fin_cases i <;> simp [lMap_swap_cl]

/-- The six codes of the substituted terms of `qG`, as an internal vector. -/
noncomputable def gVec (X : Semiterm LAct Empty 1) (U W : ClosedSemiterm LAct 0)
    (X' : Semiterm LAct Empty 1) (U' W' : ClosedSemiterm LAct 0) : V :=
  (⌜(Rew.emb X : SyntacticSemiterm LAct 1)⌝ : V) ∷
    ⌜(Rew.emb (cl U : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝ ∷
    ⌜(Rew.emb (cl W : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝ ∷
    ⌜(Rew.emb X' : SyntacticSemiterm LAct 1)⌝ ∷
    ⌜(Rew.emb (cl U' : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝ ∷
    ⌜(Rew.emb (cl W' : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝ ∷ 0

lemma semitermVec_val_gVec (X : Semiterm LAct Empty 1) (U W : ClosedSemiterm LAct 0)
    (X' : Semiterm LAct Empty 1) (U' W' : ClosedSemiterm LAct 0) :
    SemitermVec.val (fun i ↦ (⌜(Rew.emb ((![X, cl U, cl W, X', cl U', cl W'] :
      Fin 6 → Semiterm LAct Empty 1) i) : SyntacticSemiterm LAct 1)⌝ : Bootstrapping.Semiterm V LAct 1)) =
      gVec X U W X' U' W' := by
  have hv : (fun i ↦ (⌜(Rew.emb ((![X, cl U, cl W, X', cl U', cl W'] :
      Fin 6 → Semiterm LAct Empty 1) i) : SyntacticSemiterm LAct 1)⌝ : Bootstrapping.Semiterm V LAct 1)) =
      ![⌜(Rew.emb X : SyntacticSemiterm LAct 1)⌝,
        ⌜(Rew.emb (cl U : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝,
        ⌜(Rew.emb (cl W : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝,
        ⌜(Rew.emb X' : SyntacticSemiterm LAct 1)⌝,
        ⌜(Rew.emb (cl U' : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝,
        ⌜(Rew.emb (cl W' : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝] := by
    funext i; fin_cases i <;> rfl
  rw [hv]
  simp only [SemitermVec.val_cons, SemitermVec.val_nil]
  rfl

theorem quote_qG (a : ℕ) (X : Semiterm LAct Empty 1) (U W : ClosedSemiterm LAct 0)
    (X' : Semiterm LAct Empty 1) (U' W' : ClosedSemiterm LAct 0) :
    (⌜qG a X U W X' U' W'⌝ : V) = subst LAct (gVec X U W X' U' W') (⌜guardTemplate a⌝ : V) := by
  unfold qG
  rw [Sentence.quote_def, Semiformula.coe_subst_eq_subst_coe, Semiformula.quote_def,
    Semiformula.typed_quote_substs, Bootstrapping.Semiformula.val_substs, ← Semiformula.quote_def,
    ← Sentence.quote_def]
  congr 1

lemma gVec_semitermVec (X : Semiterm LAct Empty 1) (U W : ClosedSemiterm LAct 0)
    (X' : Semiterm LAct Empty 1) (U' W' : ClosedSemiterm LAct 0) :
    IsSemitermVec LAct 6 1 (gVec X U W X' U' W' : V) := by
  rw [six_eq, gVec]
  exact ((((((IsSemitermVec.nil 1).adjoin (semiterm_quote_emb₁ _)).adjoin (semiterm_quote_emb₁ _)).adjoin
    (semiterm_quote_emb₁ _)).adjoin (semiterm_quote_emb₁ _)).adjoin (semiterm_quote_emb₁ _)).adjoin
    (semiterm_quote_emb₁ _)

/-- Substituting `binNumeral k` into the six codes gives the description vector of `(me, opp)`, given that
the two triples describe `me` and `opp` on codes. -/
theorem termSubstVec_gVec (k : V) (X : Semiterm LAct Empty 1) (U W : ClosedSemiterm LAct 0)
    (X' : Semiterm LAct Empty 1) (U' W' : ClosedSemiterm LAct 0) {me opp : V}
    (hX : termSubst LAct (binNumeral k ∷ (0 : V)) (⌜(Rew.emb X : SyntacticSemiterm LAct 1)⌝ : V) = codeTerm (canonical me))
    (hU : (⌜U⌝ : V) = revalueU me) (hW : (⌜W⌝ : V) = revalueW me)
    (hX' : termSubst LAct (binNumeral k ∷ (0 : V)) (⌜(Rew.emb X' : SyntacticSemiterm LAct 1)⌝ : V) = codeTerm (canonical opp))
    (hU' : (⌜U'⌝ : V) = revalueU opp) (hW' : (⌜W'⌝ : V) = revalueW opp) :
    termSubstVec LAct 6 (binNumeral k ∷ (0 : V)) (gVec X U W X' U' W') = descriptions me opp := by
  have h1 : IsUTerm LAct (⌜(Rew.emb X : SyntacticSemiterm LAct 1)⌝ : V) := (semiterm_quote_emb₁ _).isUTerm
  have h2 : IsUTerm LAct (⌜(Rew.emb (cl U : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝ : V) :=
    (semiterm_quote_emb₁ _).isUTerm
  have h3 : IsUTerm LAct (⌜(Rew.emb (cl W : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝ : V) :=
    (semiterm_quote_emb₁ _).isUTerm
  have h4 : IsUTerm LAct (⌜(Rew.emb X' : SyntacticSemiterm LAct 1)⌝ : V) := (semiterm_quote_emb₁ _).isUTerm
  have h5 : IsUTerm LAct (⌜(Rew.emb (cl U' : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝ : V) :=
    (semiterm_quote_emb₁ _).isUTerm
  have h6 : IsUTerm LAct (⌜(Rew.emb (cl W' : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝ : V) :=
    (semiterm_quote_emb₁ _).isUTerm
  have e0 : IsUTermVec LAct 0 (0 : V) := IsUTermVec.empty
  have e1 := e0.adjoin h6
  have e2 := e1.adjoin h5
  have e3 := e2.adjoin h4
  have e4 := e3.adjoin h3
  have e5 := e4.adjoin h2
  have sU : termSubst LAct (binNumeral k ∷ 0) (⌜(Rew.emb (cl U : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝ : V) =
      revalueU me := by
    rw [quote_emb_cl_V, termSubst_closed _ (semiterm_quote_emb₀ _), ← Semiterm.empty_quote_def, hU]
  have sW : termSubst LAct (binNumeral k ∷ 0) (⌜(Rew.emb (cl W : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝ : V) =
      revalueW me := by
    rw [quote_emb_cl_V, termSubst_closed _ (semiterm_quote_emb₀ _), ← Semiterm.empty_quote_def, hW]
  have sU' : termSubst LAct (binNumeral k ∷ 0) (⌜(Rew.emb (cl U' : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝ : V) =
      revalueU opp := by
    rw [quote_emb_cl_V, termSubst_closed _ (semiterm_quote_emb₀ _), ← Semiterm.empty_quote_def, hU']
  have sW' : termSubst LAct (binNumeral k ∷ 0) (⌜(Rew.emb (cl W' : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝ : V) =
      revalueW opp := by
    rw [quote_emb_cl_V, termSubst_closed _ (semiterm_quote_emb₀ _), ← Semiterm.empty_quote_def, hW']
  unfold gVec descriptions
  rw [six_eq, termSubstVec_cons h1 e5, termSubstVec_cons h2 e4, termSubstVec_cons h3 e3,
    termSubstVec_cons h4 e2, termSubstVec_cons h5 e1, termSubstVec_cons h6 e0, termSubstVec_nil,
    hX, sU, sW, hX', sU', sW']

/-- **The instance equation on codes for the hand-written template, in every model**: the guard code
of `me` against `opp` on `guardTemplate a` is the `binNumeral k`-instance of `⌜qG a …⌝` whenever the two triples
describe `me` and `opp` on codes. -/
theorem guardCode_GtmplA_eq_instB (a : ℕ) (k : V) (X : Semiterm LAct Empty 1) (U W : ClosedSemiterm LAct 0)
    (X' : Semiterm LAct Empty 1) (U' W' : ClosedSemiterm LAct 0) {me opp : V}
    (hX : termSubst LAct (binNumeral k ∷ (0 : V)) (⌜(Rew.emb X : SyntacticSemiterm LAct 1)⌝ : V) = codeTerm (canonical me))
    (hU : (⌜U⌝ : V) = revalueU me) (hW : (⌜W⌝ : V) = revalueW me)
    (hX' : termSubst LAct (binNumeral k ∷ (0 : V)) (⌜(Rew.emb X' : SyntacticSemiterm LAct 1)⌝ : V) = codeTerm (canonical opp))
    (hU' : (⌜U'⌝ : V) = revalueU opp) (hW' : (⌜W'⌝ : V) = revalueW opp) :
    guardCode (⌜guardTemplate a⌝ : V) me opp = instB (⌜qG a X U W X' U' W'⌝ : V) k := by
  show guardCode (⌜guardTemplate a⌝ : V) me opp = subst LAct (binNumeral k ∷ (0 : V)) (⌜qG a X U W X' U' W'⌝ : V)
  rw [quote_qG, substs_substs (p := (⌜guardTemplate a⌝ : V)) (l := 6)
    (by simpa using Sentence.quote_isSemiformula (V := V) (guardTemplate a))
    (binNumeral_cons_semitermVec k) (gVec_semitermVec X U W X' U' W'),
    termSubstVec_gVec k X U W X' U' W' hX hU hW hX' hU' hW']
  rfl

/-- The transposed instance equation: the guard code of `transposeCode me` against `transposeCode opp` on
`guardTemplate (swapAction a)` is the `binNumeral k`-instance of `⌜lMap swap (qG a …)⌝`. -/
theorem guardCode_GtmplA_swap_eq_instB (a : ℕ) (k : V) (X : Semiterm LAct Empty 1) (U W : ClosedSemiterm LAct 0)
    (X' : Semiterm LAct Empty 1) (U' W' : ClosedSemiterm LAct 0) {me opp : V}
    (hX : termSubst LAct (binNumeral k ∷ (0 : V)) (⌜(Rew.emb X : SyntacticSemiterm LAct 1)⌝ : V) = codeTerm (canonical me))
    (hU : (⌜U⌝ : V) = revalueU me) (hW : (⌜W⌝ : V) = revalueW me)
    (hX' : termSubst LAct (binNumeral k ∷ (0 : V)) (⌜(Rew.emb X' : SyntacticSemiterm LAct 1)⌝ : V) = codeTerm (canonical opp))
    (hU' : (⌜U'⌝ : V) = revalueU opp) (hW' : (⌜W'⌝ : V) = revalueW opp) :
    guardCode (⌜guardTemplate (swapAction a)⌝ : V) (transposeCode me) (transposeCode opp) =
      instB (⌜Semiformula.lMap swap (qG a X U W X' U' W')⌝ : V) k := by
  have hg0 : IsSemiformula LAct 6 (⌜guardTemplate a⌝ : V) := by
    simpa using Sentence.quote_isSemiformula (V := V) (guardTemplate a)
  have hg1 : IsSemiformula LAct 6 (⌜guardTemplate (swapAction a)⌝ : V) := by
    simpa using Sentence.quote_isSemiformula (V := V) (guardTemplate (swapAction a))
  rw [← substTemplate_of_template hg1, ← revalueTemplate_quote_GtmplA_V, ← revalueTemplate_substTemplate, substTemplate_of_template hg0,
    guardCode_GtmplA_eq_instB a k X U W X' U' W' hX hU hW hX' hU' hW']
  unfold instB
  rw [revalueTemplate_subst isAct_one isAct_zero (Sentence.quote_isSemiformul₁ (qG a X U W X' U' W'))
    (binNumeral_cons_semitermVec k), revalueTemplate_quote_sentence_V]
  congr 1
  rw [show (1 : V) = 0 + 1 by simp, termRelabelVec_cons (binNumeral_term_LAct k).isUTerm IsUTermVec.empty,
    termRelabelVec_nil, termRelabel_binNumeral]

/-- **The truth equation of `qG a …` in every model** (standard reading), given that the triples
describe `me` and `opp`: "`opp` plays `a` against `me`". -/
theorem eval_qG_iff_V (a : ℕ) (k : V) (X : Semiterm LAct Empty 1) (U W : ClosedSemiterm LAct 0)
    (X' : Semiterm LAct Empty 1) (U' W' : ClosedSemiterm LAct 0) {me opp : V}
    (hme : revalue (U.val (s := stdReadingV V) ![] Empty.elim) (W.val (s := stdReadingV V) ![] Empty.elim)
      (X.val (s := stdReadingV V) ![k] Empty.elim) = me)
    (hopp : revalue (U'.val (s := stdReadingV V) ![] Empty.elim) (W'.val (s := stdReadingV V) ![] Empty.elim)
      (X'.val (s := stdReadingV V) ![k] Empty.elim) = opp) :
    Semiformula.Eval (s := stdReadingV V) ![k] Empty.elim (qG a X U W X' U' W') ↔
      ∃ n, EvalGraph n opp me opp (a : V) := by
  unfold qG guardTemplate guardTemplate7
  rw [Semiformula.eval_substs, Semiformula.eval_substs, Semiformula.eval_lMap, stdReadingV_lMap_emb]
  have h0 : (Semiterm.val (s := stdReadingV V) ![k] Empty.elim ∘ ![X, cl U, cl W, X', cl U', cl W']) =
      ![X.val (s := stdReadingV V) ![k] Empty.elim, U.val (s := stdReadingV V) ![] Empty.elim,
        W.val (s := stdReadingV V) ![] Empty.elim, X'.val (s := stdReadingV V) ![k] Empty.elim,
        U'.val (s := stdReadingV V) ![] Empty.elim, W'.val (s := stdReadingV V) ![] Empty.elim] := by
    funext i; fin_cases i <;> simp [val_cl_V]
  rw [h0]
  have h1 : (Semiterm.val (s := stdReadingV V)
      ![X.val (s := stdReadingV V) ![k] Empty.elim, U.val (s := stdReadingV V) ![] Empty.elim,
        W.val (s := stdReadingV V) ![] Empty.elim, X'.val (s := stdReadingV V) ![k] Empty.elim,
        U'.val (s := stdReadingV V) ![] Empty.elim, W'.val (s := stdReadingV V) ![] Empty.elim]
      Empty.elim ∘ ![#0, #1, #2, #3, #4, #5, actT6 a]) =
      ![X.val (s := stdReadingV V) ![k] Empty.elim, U.val (s := stdReadingV V) ![] Empty.elim,
        W.val (s := stdReadingV V) ![] Empty.elim, X'.val (s := stdReadingV V) ![k] Empty.elim,
        U'.val (s := stdReadingV V) ![] Empty.elim, W'.val (s := stdReadingV V) ![] Empty.elim, (a : V)] := by
    funext i; fin_cases i <;> simp [val_actT6_V]
  rw [h1]
  refine (eval_guardTemplateRaw (V := V) _).trans ?_
  simp only [Matrix.cons_val]
  rw [hme, hopp]

end qG

/-! ### 2. An arbitrary template filled with two triples, and the atom over a closed program -/

section qT

/-- An arbitrary six-variable template filled with the triples `(X, U, W)` (me) and `(X', U', W')` (opp). -/
noncomputable def qT (g : Semisentence LAct 6) (X : Semiterm LAct Empty 1) (U W : ClosedSemiterm LAct 0)
    (X' : Semiterm LAct Empty 1) (U' W' : ClosedSemiterm LAct 0) : Semisentence LAct 1 :=
  g ⇜ ![X, cl U, cl W, X', cl U', cl W']

lemma lMap_swap_qT (g : Semisentence LAct 6) (X : Semiterm LAct Empty 1) (U W : ClosedSemiterm LAct 0)
    (X' : Semiterm LAct Empty 1) (U' W' : ClosedSemiterm LAct 0) :
    Semiformula.lMap swap (qT g X U W X' U' W') =
      qT (Semiformula.lMap swap g) (Semiterm.lMap swap X) (Semiterm.lMap swap U) (Semiterm.lMap swap W)
        (Semiterm.lMap swap X') (Semiterm.lMap swap U') (Semiterm.lMap swap W') := by
  unfold qT
  rw [Semiformula.lMap_subst]
  congr 1
  funext i
  fin_cases i <;> simp [lMap_swap_cl]

theorem quote_qT (g : Semisentence LAct 6) (X : Semiterm LAct Empty 1) (U W : ClosedSemiterm LAct 0)
    (X' : Semiterm LAct Empty 1) (U' W' : ClosedSemiterm LAct 0) :
    (⌜qT g X U W X' U' W'⌝ : V) = subst LAct (gVec X U W X' U' W') (⌜g⌝ : V) := by
  unfold qT
  rw [Sentence.quote_def, Semiformula.coe_subst_eq_subst_coe, Semiformula.quote_def,
    Semiformula.typed_quote_substs, Bootstrapping.Semiformula.val_substs, ← Semiformula.quote_def,
    ← Sentence.quote_def]
  congr 1

/-- **The generic instance equation on codes, for an arbitrary template**: the guard code of `me`
against `opp` on `g` is the `binNumeral k`-instance of `⌜qT g …⌝` whenever the triples describe `me` and
`opp` on codes. -/
theorem guardCode_qT_eq_instB (g : Semisentence LAct 6) (k : V) (X : Semiterm LAct Empty 1)
    (U W : ClosedSemiterm LAct 0) (X' : Semiterm LAct Empty 1) (U' W' : ClosedSemiterm LAct 0) {me opp : V}
    (hX : termSubst LAct (binNumeral k ∷ (0 : V)) (⌜(Rew.emb X : SyntacticSemiterm LAct 1)⌝ : V) = codeTerm (canonical me))
    (hU : (⌜U⌝ : V) = revalueU me) (hW : (⌜W⌝ : V) = revalueW me)
    (hX' : termSubst LAct (binNumeral k ∷ (0 : V)) (⌜(Rew.emb X' : SyntacticSemiterm LAct 1)⌝ : V) = codeTerm (canonical opp))
    (hU' : (⌜U'⌝ : V) = revalueU opp) (hW' : (⌜W'⌝ : V) = revalueW opp) :
    guardCode (⌜g⌝ : V) me opp = instB (⌜qT g X U W X' U' W'⌝ : V) k := by
  show guardCode (⌜g⌝ : V) me opp = subst LAct (binNumeral k ∷ (0 : V)) (⌜qT g X U W X' U' W'⌝ : V)
  rw [quote_qT, substs_substs (p := (⌜g⌝ : V)) (l := 6)
    (by simpa using Sentence.quote_isSemiformula (V := V) g)
    (binNumeral_cons_semitermVec k) (gVec_semitermVec X U W X' U' W'),
    termSubstVec_gVec k X U W X' U' W' hX hU hW hX' hU' hW']
  rfl

/-- The transposed instance equation: the guard code of `transposeCode me` against `transposeCode opp` on
`lMap swap g` is the `binNumeral k`-instance of `⌜lMap swap (qT g …)⌝`. -/
theorem guardCode_qT_swap_eq_instB (g : Semisentence LAct 6) (k : V) (X : Semiterm LAct Empty 1)
    (U W : ClosedSemiterm LAct 0) (X' : Semiterm LAct Empty 1) (U' W' : ClosedSemiterm LAct 0) {me opp : V}
    (hX : termSubst LAct (binNumeral k ∷ (0 : V)) (⌜(Rew.emb X : SyntacticSemiterm LAct 1)⌝ : V) = codeTerm (canonical me))
    (hU : (⌜U⌝ : V) = revalueU me) (hW : (⌜W⌝ : V) = revalueW me)
    (hX' : termSubst LAct (binNumeral k ∷ (0 : V)) (⌜(Rew.emb X' : SyntacticSemiterm LAct 1)⌝ : V) = codeTerm (canonical opp))
    (hU' : (⌜U'⌝ : V) = revalueU opp) (hW' : (⌜W'⌝ : V) = revalueW opp) :
    guardCode (⌜Semiformula.lMap swap g⌝ : V) (transposeCode me) (transposeCode opp) =
      instB (⌜Semiformula.lMap swap (qT g X U W X' U' W')⌝ : V) k := by
  have hg0 : IsSemiformula LAct 6 (⌜g⌝ : V) := by
    simpa using Sentence.quote_isSemiformula (V := V) g
  have hg1 : IsSemiformula LAct 6 (⌜Semiformula.lMap swap g⌝ : V) := by
    simpa using Sentence.quote_isSemiformula (V := V) (Semiformula.lMap swap g)
  rw [← substTemplate_of_template hg1, ← revalueTemplate_quote_sentence₆_V, ← revalueTemplate_substTemplate, substTemplate_of_template hg0,
    guardCode_qT_eq_instB g k X U W X' U' W' hX hU hW hX' hU' hW']
  unfold instB
  rw [revalueTemplate_subst isAct_one isAct_zero (Sentence.quote_isSemiformul₁ (qT g X U W X' U' W'))
    (binNumeral_cons_semitermVec k), revalueTemplate_quote_sentence_V]
  congr 1
  rw [show (1 : V) = 0 + 1 by simp, termRelabelVec_cons (binNumeral_term_LAct k).isUTerm IsUTermVec.empty,
    termRelabelVec_nil, termRelabel_binNumeral]

omit [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
/-- The truth of a template instance at `k` is the truth of the template at the six values. -/
theorem eval_qT_iff (g : Semisentence LAct 6) (X : Semiterm LAct Empty 1) (U W : ClosedSemiterm LAct 0)
    (X' : Semiterm LAct Empty 1) (U' W' : ClosedSemiterm LAct 0) (k : V) :
    Semiformula.Eval (s := stdReadingV V) ![k] Empty.elim (qT g X U W X' U' W') ↔
      Semiformula.Eval (s := stdReadingV V)
        ![X.val (s := stdReadingV V) ![k] Empty.elim, U.val (s := stdReadingV V) ![] Empty.elim,
          W.val (s := stdReadingV V) ![] Empty.elim, X'.val (s := stdReadingV V) ![k] Empty.elim,
          U'.val (s := stdReadingV V) ![] Empty.elim, W'.val (s := stdReadingV V) ![] Empty.elim] Empty.elim g := by
  unfold qT
  rw [Semiformula.eval_substs]
  have h0 : (Semiterm.val (s := stdReadingV V) ![k] Empty.elim ∘ ![X, cl U, cl W, X', cl U', cl W']) =
      ![X.val (s := stdReadingV V) ![k] Empty.elim, U.val (s := stdReadingV V) ![] Empty.elim,
        W.val (s := stdReadingV V) ![] Empty.elim, X'.val (s := stdReadingV V) ![k] Empty.elim,
        U'.val (s := stdReadingV V) ![] Empty.elim, W'.val (s := stdReadingV V) ![] Empty.elim] := by
    funext i; fin_cases i <;> simp [val_cl_V]
  rw [h0]

/-- **The `.plays .opp q a` atom of `template` for a CLOSED `q`, in every model**: "opp plays `a` against
the (cast) code of `q`" — the me-slots are inert. -/
lemma eval_template_plays_opp_closed_V (q : PD.Prog) (hq1 : q ≠ .self) (hq2 : q ≠ .opp) (a : PD.Action)
    (b : Fin 6 → V) :
    Semiformula.Eval (s := stdReadingV V) b Empty.elim (template (.plays .opp q a)) ↔
      ∃ n, EvalGraph n (revalue (b 4) (b 5) (b 3)) ((progCode q : ℕ) : V) (revalue (b 4) (b 5) (b 3)) (actCode a : V) := by
  rw [template_plays]
  unfold progGraph
  rw [progAux_opp, progAux_of_ne hq1 hq2]
  unfold descF
  simp only [Semiformula.eval_substs, Semiformula.eval_ex, LogicalConnective.HomClass.map_and,
    LogicalConnective.Prop.and_eq, Semiformula.eval_rel, eval_relDesc_V, eval_evalG_V, eval_closedDesc_V,
    stdReadingV_rel_eq, Function.comp_def, Matrix.cons_val, Semiterm.val_bvar, val_cl_V, val_actT_V]
  constructor
  · rintro ⟨x, y, N, ⟨d, rfl, rfl⟩, rfl, h⟩
    exact ⟨N, h⟩
  · rintro ⟨N, h⟩
    exact ⟨_, _, N, ⟨_, rfl, rfl⟩, rfl, h⟩


end qT

/-! ### 3. The generic instance equation and truth equation of a template instance (JustBot's form) -/

section templateVec

/-- The six codes of the substituted terms of `guardTemplate a ⇜ ![T₁, cl u₁, cl w₁, T₂, cl u₂, cl w₂]`,
as an internal vector. -/
noncomputable def templateVec (T₁ T₂ : Semiterm LAct Empty 1) (u₁ w₁ u₂ w₂ : ClosedSemiterm LAct 0) : V :=
  (⌜(Rew.emb T₁ : SyntacticSemiterm LAct 1)⌝ : V) ∷
    ⌜(Rew.emb (cl u₁ : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝ ∷
    ⌜(Rew.emb (cl w₁ : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝ ∷
    ⌜(Rew.emb T₂ : SyntacticSemiterm LAct 1)⌝ ∷
    ⌜(Rew.emb (cl u₂ : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝ ∷
    ⌜(Rew.emb (cl w₂ : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝ ∷ 0

/-- The code of a template instance is the internal substitution of `templateVec` into the template code. -/
theorem quote_GtmplA_subst (a : ℕ) (T₁ T₂ : Semiterm LAct Empty 1) (u₁ w₁ u₂ w₂ : ClosedSemiterm LAct 0) :
    (⌜(guardTemplate a ⇜ ![T₁, cl u₁, cl w₁, T₂, cl u₂, cl w₂] : Semisentence LAct 1)⌝ : V) =
      subst LAct (templateVec T₁ T₂ u₁ w₁ u₂ w₂) (⌜guardTemplate a⌝ : V) := by
  rw [Sentence.quote_def, Semiformula.coe_subst_eq_subst_coe, Semiformula.quote_def,
    Semiformula.typed_quote_substs, Bootstrapping.Semiformula.val_substs, ← Semiformula.quote_def,
    ← Sentence.quote_def]
  congr 1

lemma templateVec_semitermVec (T₁ T₂ : Semiterm LAct Empty 1) (u₁ w₁ u₂ w₂ : ClosedSemiterm LAct 0) :
    IsSemitermVec LAct 6 1 (templateVec T₁ T₂ u₁ w₁ u₂ w₂ : V) := by
  rw [six_eq, templateVec]
  exact ((((((IsSemitermVec.nil 1).adjoin (semiterm_quote_emb₁ _)).adjoin (semiterm_quote_emb₁ _)).adjoin
    (semiterm_quote_emb₁ _)).adjoin (semiterm_quote_emb₁ _)).adjoin (semiterm_quote_emb₁ _)).adjoin
    (semiterm_quote_emb₁ _)

/-- Substituting `binNumeral k` into the six codes gives the description vector of `(me, opp)`, given
the six entry equations. -/
theorem termSubstVec_templateVec {T₁ T₂ : Semiterm LAct Empty 1} {u₁ w₁ u₂ w₂ : ClosedSemiterm LAct 0}
    {k me opp : V}
    (h₁ : termSubst LAct (binNumeral k ∷ (0 : V)) (⌜(Rew.emb T₁ : SyntacticSemiterm LAct 1)⌝ : V) = codeTerm (canonical me))
    (hu₁ : (⌜(Rew.emb u₁ : SyntacticSemiterm LAct 0)⌝ : V) = revalueU me)
    (hw₁ : (⌜(Rew.emb w₁ : SyntacticSemiterm LAct 0)⌝ : V) = revalueW me)
    (h₂ : termSubst LAct (binNumeral k ∷ (0 : V)) (⌜(Rew.emb T₂ : SyntacticSemiterm LAct 1)⌝ : V) = codeTerm (canonical opp))
    (hu₂ : (⌜(Rew.emb u₂ : SyntacticSemiterm LAct 0)⌝ : V) = revalueU opp)
    (hw₂ : (⌜(Rew.emb w₂ : SyntacticSemiterm LAct 0)⌝ : V) = revalueW opp) :
    termSubstVec LAct 6 (binNumeral k ∷ (0 : V)) (templateVec T₁ T₂ u₁ w₁ u₂ w₂) = descriptions me opp := by
  have hT₁ : IsUTerm LAct (⌜(Rew.emb T₁ : SyntacticSemiterm LAct 1)⌝ : V) := (semiterm_quote_emb₁ _).isUTerm
  have hU₁ : IsUTerm LAct (⌜(Rew.emb (cl u₁ : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝ : V) :=
    (semiterm_quote_emb₁ _).isUTerm
  have hW₁ : IsUTerm LAct (⌜(Rew.emb (cl w₁ : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝ : V) :=
    (semiterm_quote_emb₁ _).isUTerm
  have hT₂ : IsUTerm LAct (⌜(Rew.emb T₂ : SyntacticSemiterm LAct 1)⌝ : V) := (semiterm_quote_emb₁ _).isUTerm
  have hU₂ : IsUTerm LAct (⌜(Rew.emb (cl u₂ : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝ : V) :=
    (semiterm_quote_emb₁ _).isUTerm
  have hW₂ : IsUTerm LAct (⌜(Rew.emb (cl w₂ : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝ : V) :=
    (semiterm_quote_emb₁ _).isUTerm
  have e0 : IsUTermVec LAct 0 (0 : V) := IsUTermVec.empty
  have e1 := e0.adjoin hW₂
  have e2 := e1.adjoin hU₂
  have e3 := e2.adjoin hT₂
  have e4 := e3.adjoin hW₁
  have e5 := e4.adjoin hU₁
  have sU₁ : termSubst LAct (binNumeral k ∷ 0) (⌜(Rew.emb (cl u₁ : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝ : V) =
      revalueU me := by
    rw [quote_emb_cl_V, termSubst_closed _ (semiterm_quote_emb₀ _), hu₁]
  have sW₁ : termSubst LAct (binNumeral k ∷ 0) (⌜(Rew.emb (cl w₁ : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝ : V) =
      revalueW me := by
    rw [quote_emb_cl_V, termSubst_closed _ (semiterm_quote_emb₀ _), hw₁]
  have sU₂ : termSubst LAct (binNumeral k ∷ 0) (⌜(Rew.emb (cl u₂ : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝ : V) =
      revalueU opp := by
    rw [quote_emb_cl_V, termSubst_closed _ (semiterm_quote_emb₀ _), hu₂]
  have sW₂ : termSubst LAct (binNumeral k ∷ 0) (⌜(Rew.emb (cl w₂ : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝ : V) =
      revalueW opp := by
    rw [quote_emb_cl_V, termSubst_closed _ (semiterm_quote_emb₀ _), hw₂]
  unfold templateVec descriptions
  rw [six_eq, termSubstVec_cons hT₁ e5, termSubstVec_cons hU₁ e4, termSubstVec_cons hW₁ e3,
    termSubstVec_cons hT₂ e2, termSubstVec_cons hU₂ e1, termSubstVec_cons hW₂ e0, termSubstVec_nil,
    h₁, sU₁, sW₁, h₂, sU₂, sW₂]

/-- **The generic instance equation on codes**: the guard code of `(me, opp)` on the template
`guardTemplate a` is the `binNumeral k`-instance of the code of the template instance, given the six entry
equations. -/
theorem guardCode_eq_instB_of (a : ℕ) {T₁ T₂ : Semiterm LAct Empty 1} {u₁ w₁ u₂ w₂ : ClosedSemiterm LAct 0}
    {k me opp : V}
    (h₁ : termSubst LAct (binNumeral k ∷ (0 : V)) (⌜(Rew.emb T₁ : SyntacticSemiterm LAct 1)⌝ : V) = codeTerm (canonical me))
    (hu₁ : (⌜(Rew.emb u₁ : SyntacticSemiterm LAct 0)⌝ : V) = revalueU me)
    (hw₁ : (⌜(Rew.emb w₁ : SyntacticSemiterm LAct 0)⌝ : V) = revalueW me)
    (h₂ : termSubst LAct (binNumeral k ∷ (0 : V)) (⌜(Rew.emb T₂ : SyntacticSemiterm LAct 1)⌝ : V) = codeTerm (canonical opp))
    (hu₂ : (⌜(Rew.emb u₂ : SyntacticSemiterm LAct 0)⌝ : V) = revalueU opp)
    (hw₂ : (⌜(Rew.emb w₂ : SyntacticSemiterm LAct 0)⌝ : V) = revalueW opp) :
    guardCode (⌜guardTemplate a⌝ : V) me opp =
      instB (⌜(guardTemplate a ⇜ ![T₁, cl u₁, cl w₁, T₂, cl u₂, cl w₂] : Semisentence LAct 1)⌝ : V) k := by
  show guardCode (⌜guardTemplate a⌝ : V) me opp =
    subst LAct (binNumeral k ∷ (0 : V)) (⌜(guardTemplate a ⇜ ![T₁, cl u₁, cl w₁, T₂, cl u₂, cl w₂] : Semisentence LAct 1)⌝ : V)
  rw [quote_GtmplA_subst, substs_substs (p := (⌜guardTemplate a⌝ : V)) (l := 6)
    (by simpa using Sentence.quote_isSemiformula (V := V) (guardTemplate a))
    (binNumeral_cons_semitermVec k) (templateVec_semitermVec T₁ T₂ u₁ w₁ u₂ w₂),
    termSubstVec_templateVec h₁ hu₁ hw₁ h₂ hu₂ hw₂]
  rfl

/-- **The generic truth equation** (standard reading): a template instance at the budget `k` says
"the program reconstructed from the opp-triple plays `a` against the one reconstructed from the
me-triple". -/
theorem eval_GtmplA_subst_iff (a : ℕ) (T₁ T₂ : Semiterm LAct Empty 1) (u₁ w₁ u₂ w₂ : ClosedSemiterm LAct 0)
    (k : V) :
    Semiformula.Eval (s := stdReadingV V) ![k] Empty.elim (guardTemplate a ⇜ ![T₁, cl u₁, cl w₁, T₂, cl u₂, cl w₂]) ↔
      ∃ n, EvalGraph n
        (revalue (u₂.val (s := stdReadingV V) ![] Empty.elim) (w₂.val (s := stdReadingV V) ![] Empty.elim)
          (T₂.val (s := stdReadingV V) ![k] Empty.elim))
        (revalue (u₁.val (s := stdReadingV V) ![] Empty.elim) (w₁.val (s := stdReadingV V) ![] Empty.elim)
          (T₁.val (s := stdReadingV V) ![k] Empty.elim))
        (revalue (u₂.val (s := stdReadingV V) ![] Empty.elim) (w₂.val (s := stdReadingV V) ![] Empty.elim)
          (T₂.val (s := stdReadingV V) ![k] Empty.elim))
        (a : V) := by
  unfold guardTemplate guardTemplate7
  rw [Semiformula.eval_substs, Semiformula.eval_substs, Semiformula.eval_lMap, stdReadingV_lMap_emb]
  have h0 : (Semiterm.val (s := stdReadingV V) ![k] Empty.elim ∘ ![T₁, cl u₁, cl w₁, T₂, cl u₂, cl w₂]) =
      ![T₁.val (s := stdReadingV V) ![k] Empty.elim, u₁.val (s := stdReadingV V) ![] Empty.elim,
        w₁.val (s := stdReadingV V) ![] Empty.elim, T₂.val (s := stdReadingV V) ![k] Empty.elim,
        u₂.val (s := stdReadingV V) ![] Empty.elim, w₂.val (s := stdReadingV V) ![] Empty.elim] := by
    funext i; fin_cases i <;> simp [val_cl_V]
  rw [h0]
  have h1 : (Semiterm.val (s := stdReadingV V)
      ![T₁.val (s := stdReadingV V) ![k] Empty.elim, u₁.val (s := stdReadingV V) ![] Empty.elim,
        w₁.val (s := stdReadingV V) ![] Empty.elim, T₂.val (s := stdReadingV V) ![k] Empty.elim,
        u₂.val (s := stdReadingV V) ![] Empty.elim, w₂.val (s := stdReadingV V) ![] Empty.elim]
      Empty.elim ∘ ![#0, #1, #2, #3, #4, #5, actT6 a]) =
      ![T₁.val (s := stdReadingV V) ![k] Empty.elim, u₁.val (s := stdReadingV V) ![] Empty.elim,
        w₁.val (s := stdReadingV V) ![] Empty.elim, T₂.val (s := stdReadingV V) ![k] Empty.elim,
        u₂.val (s := stdReadingV V) ![] Empty.elim, w₂.val (s := stdReadingV V) ![] Empty.elim, (a : V)] := by
    funext i; fin_cases i <;> simp [val_actT6_V]
  rw [h1]
  exact eval_guardTemplateRaw (V := V) _


/-- `templateVec` IS `gVec` (the same six-code vector, the arguments in a different order). -/
lemma templateVec_eq_gVec (T₁ T₂ : Semiterm LAct Empty 1) (u₁ w₁ u₂ w₂ : ClosedSemiterm LAct 0) :
    (templateVec T₁ T₂ u₁ w₁ u₂ w₂ : V) = gVec T₁ u₁ w₁ T₂ u₂ w₂ := rfl

end templateVec

/-! ### 4. The truth of the play atoms of `template`, and of a `qT` instance -/

section atoms

/-- **The `.plays .self .opp a` atom of `template` in every model**: at the frame
`b = (x₁, u₁, w₁, x₂, u₂, w₂)`, "me (`revalue u₁ w₁ x₁`) plays `a` against opp
(`revalue u₂ w₂ x₂`)". -/
lemma eval_template_plays_self_opp_V (a : PD.Action) (b : Fin 6 → V) :
    Semiformula.Eval (s := stdReadingV V) b Empty.elim (template (.plays .self .opp a)) ↔
      ∃ n, EvalGraph n (revalue (b 1) (b 2) (b 0)) (revalue (b 4) (b 5) (b 3))
        (revalue (b 1) (b 2) (b 0)) (actCode a : V) := by
  rw [template_plays]
  unfold progGraph
  rw [progAux_self, progAux_opp]
  unfold descF
  simp only [Semiformula.eval_substs, Semiformula.eval_ex, LogicalConnective.HomClass.map_and,
    LogicalConnective.Prop.and_eq, Semiformula.eval_rel, eval_relDesc_V, eval_evalG_V, stdReadingV_rel_eq,
    Function.comp_def, Matrix.cons_val, Semiterm.val_bvar, val_cl_V, val_actT_V]
  constructor
  · rintro ⟨x, y, N, ⟨d, rfl, rfl⟩, ⟨d', rfl, rfl⟩, h⟩
    exact ⟨N, h⟩
  · rintro ⟨N, h⟩
    exact ⟨_, _, N, ⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩, h⟩

/-- **The `.plays .opp .self a` atom of `template` in every model**: "opp plays `a` against me". -/
lemma eval_template_plays_opp_self_V (a : PD.Action) (b : Fin 6 → V) :
    Semiformula.Eval (s := stdReadingV V) b Empty.elim (template (.plays .opp .self a)) ↔
      ∃ n, EvalGraph n (revalue (b 4) (b 5) (b 3)) (revalue (b 1) (b 2) (b 0))
        (revalue (b 4) (b 5) (b 3)) (actCode a : V) := by
  rw [template_plays]
  unfold progGraph
  rw [progAux_self, progAux_opp]
  unfold descF
  simp only [Semiformula.eval_substs, Semiformula.eval_ex, LogicalConnective.HomClass.map_and,
    LogicalConnective.Prop.and_eq, Semiformula.eval_rel, eval_relDesc_V, eval_evalG_V, stdReadingV_rel_eq,
    Function.comp_def, Matrix.cons_val, Semiterm.val_bvar, val_cl_V, val_actT_V]
  constructor
  · rintro ⟨x, y, N, ⟨d, rfl, rfl⟩, ⟨d', rfl, rfl⟩, h⟩
    exact ⟨N, h⟩
  · rintro ⟨N, h⟩
    exact ⟨_, _, N, ⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩, h⟩

/-- **`qT (template (.plays .opp .self a')) X U W X' U' W'` at `k`**: "the program the opp-triple
describes plays `a'` against the one the me-triple describes". -/
theorem eval_qT_plays_opp_self (a' : PD.Action) (X : Semiterm LAct Empty 1) (U W : ClosedSemiterm LAct 0)
    (X' : Semiterm LAct Empty 1) (U' W' : ClosedSemiterm LAct 0) (k : V) {me opp : V}
    (hme : revalue (U.val (s := stdReadingV V) ![] Empty.elim) (W.val (s := stdReadingV V) ![] Empty.elim)
      (X.val (s := stdReadingV V) ![k] Empty.elim) = me)
    (hopp : revalue (U'.val (s := stdReadingV V) ![] Empty.elim) (W'.val (s := stdReadingV V) ![] Empty.elim)
      (X'.val (s := stdReadingV V) ![k] Empty.elim) = opp) :
    Semiformula.Eval (s := stdReadingV V) ![k] Empty.elim (qT (template (.plays .opp .self a')) X U W X' U' W') ↔
      ∃ n, EvalGraph n opp me opp (actCode a' : V) := by
  rw [eval_qT_iff, eval_template_plays_opp_self_V]
  simp only [Matrix.cons_val]
  rw [hme, hopp]

/-- The negated atom: "the opp-program does NOT play `a'` against the me-program". -/
theorem eval_qT_neg_plays_opp_self (a' : PD.Action) (X : Semiterm LAct Empty 1) (U W : ClosedSemiterm LAct 0)
    (X' : Semiterm LAct Empty 1) (U' W' : ClosedSemiterm LAct 0) (k : V) {me opp : V}
    (hme : revalue (U.val (s := stdReadingV V) ![] Empty.elim) (W.val (s := stdReadingV V) ![] Empty.elim)
      (X.val (s := stdReadingV V) ![k] Empty.elim) = me)
    (hopp : revalue (U'.val (s := stdReadingV V) ![] Empty.elim) (W'.val (s := stdReadingV V) ![] Empty.elim)
      (X'.val (s := stdReadingV V) ![k] Empty.elim) = opp) :
    Semiformula.Eval (s := stdReadingV V) ![k] Empty.elim (qT (template (.neg (.plays .opp .self a'))) X U W X' U' W') ↔
      ¬ ∃ n, EvalGraph n opp me opp (actCode a' : V) := by
  rw [eval_qT_iff, template_neg]
  simp only [LogicalConnective.HomClass.map_neg, LogicalConnective.Prop.neg_eq]
  rw [eval_template_plays_opp_self_V]
  simp only [Matrix.cons_val]
  rw [hme, hopp]

/-- The swapped reading of a `qT` instance is the standard reading of the transposed instance. -/
theorem eval_qT_swap (g : Semisentence LAct 6) (X : Semiterm LAct Empty 1) (U W : ClosedSemiterm LAct 0)
    (X' : Semiterm LAct Empty 1) (U' W' : ClosedSemiterm LAct 0) (k : V) :
    Semiformula.Eval (s := swappedReading V) ![k] Empty.elim (qT g X U W X' U' W') ↔
      Semiformula.Eval (s := stdReadingV V) ![k] Empty.elim
        (qT (Semiformula.lMap swap g) (Semiterm.lMap swap X) (Semiterm.lMap swap U) (Semiterm.lMap swap W)
          (Semiterm.lMap swap X') (Semiterm.lMap swap U') (Semiterm.lMap swap W')) := by
  rw [eval_swappedReading, lMap_swap_qT, ← stdReadingV_eq_stdReading]

end atoms

/-! ### 5. The Dupoc towers: Cupod's description on `TD`, and the bot tower `TBD` -/

section towers

theorem transposeCode_CupodV (k : V) : transposeCode (CupodV k) = DupocV k := by
  rw [← transposeCode_DupocV, transposeCode_transposeCode]

theorem canonical_CupodV_eq (k : V) : canonical (CupodV k) = canonical (DupocV k) := by
  rw [← transposeCode_DupocV, canonical_transposeCode]

theorem revalueU_CupodV (k : V) : revalueU (CupodV k) = (⌜uC⌝ : V) := by
  unfold revalueU uC uD
  rw [transposeCode_CupodV]
  by_cases h1 : innerD < innerC
  · rw [if_neg (fun h ↦ lt_asymm ((DupocV_lt_CupodV_iff k).mpr h1) h), if_pos ((DupocV_lt_CupodV_iff k).mpr h1),
      if_pos h1, lMap_swap_cterm_C, quote_cterm_D]
  · rw [if_neg h1]
    by_cases h2 : innerC < innerD
    · rw [if_pos ((CupodV_lt_DupocV_iff k).mpr h2), if_pos h2, lMap_swap_cterm_D, quote_cterm_C]
    · rw [if_neg (fun h ↦ h2 ((CupodV_lt_DupocV_iff k).mp h)), if_neg (fun h ↦ h1 ((DupocV_lt_CupodV_iff k).mp h)),
        if_neg h2, lMap_swap_numT, quote_numT]
      simp

theorem revalueW_CupodV (k : V) : revalueW (CupodV k) = (⌜wC⌝ : V) := by
  unfold revalueW wC wD
  rw [transposeCode_CupodV]
  by_cases h1 : innerD < innerC
  · rw [if_neg (fun h ↦ lt_asymm ((DupocV_lt_CupodV_iff k).mpr h1) h), if_pos ((DupocV_lt_CupodV_iff k).mpr h1),
      if_pos h1, lMap_swap_cterm_D, quote_cterm_C]
  · rw [if_neg h1]
    by_cases h2 : innerC < innerD
    · rw [if_pos ((CupodV_lt_DupocV_iff k).mpr h2), if_pos h2, lMap_swap_cterm_C, quote_cterm_D]
    · rw [if_neg (fun h ↦ h2 ((CupodV_lt_DupocV_iff k).mp h)), if_neg (fun h ↦ h1 ((DupocV_lt_CupodV_iff k).mp h)),
        if_neg h2, lMap_swap_numT, quote_numT]
      simp

/-- Cupod's triple `(TD, uC, wC)` describes `CupodV k` on codes: the `X`-hypothesis. -/
lemma hX_cupod (k : V) :
    termSubst LAct (binNumeral k ∷ (0 : V)) (⌜(Rew.emb TD : SyntacticSemiterm LAct 1)⌝ : V) =
      codeTerm (canonical (CupodV k)) := by
  rw [quote_emb_TD, termSubst_tower, canonical_CupodV_eq, canonical_DupocV]

lemma hU_cupod (k : V) : (⌜uC⌝ : V) = revalueU (CupodV k) := (revalueU_CupodV k).symm
lemma hW_cupod (k : V) : (⌜wC⌝ : V) = revalueW (CupodV k) := (revalueW_CupodV k).symm

/-- Cupod's triple describes `CupodV k` in `stdReadingV V`. -/
lemma desc_cupod (k : V) :
    revalue (uC.val (s := stdReadingV V) ![] Empty.elim) (wC.val (s := stdReadingV V) ![] Empty.elim)
      (TD.val (s := stdReadingV V) ![k] Empty.elim) = CupodV k := by
  rw [val_TD_V]; exact revalue_val_uC_wC_V k

/-- The transposed triple describes `DupocV k` in `stdReadingV V`. -/
lemma descT_cupod (k : V) :
    revalue ((Semiterm.lMap swap uC).val (s := stdReadingV V) ![] Empty.elim)
      ((Semiterm.lMap swap wC).val (s := stdReadingV V) ![] Empty.elim)
      ((Semiterm.lMap swap TD).val (s := stdReadingV V) ![k] Empty.elim) = DupocV k := by
  unfold uC wC
  rw [term_lMap_swap_swap, term_lMap_swap_swap, lMap_swap_TD, val_TD_V]
  exact revalue_val_uD_wD_V k

/-- Dupoc's own triple describes `DupocV k` on codes (as `hX_dimcid`). -/
lemma hX_dupoc (k : V) :
    termSubst LAct (binNumeral k ∷ (0 : V)) (⌜(Rew.emb TD : SyntacticSemiterm LAct 1)⌝ : V) =
      codeTerm (canonical (DupocV k)) := by
  rw [quote_emb_TD, termSubst_tower, canonical_DupocV]

lemma hU_dupoc (k : V) : (⌜uD⌝ : V) = revalueU (DupocV k) := (revalueU_DupocV k).symm
lemma hW_dupoc (k : V) : (⌜wD⌝ : V) = revalueW (DupocV k) := (revalueW_DupocV k).symm

/-- **The one-variable description term of `pBot (Dupoc k)`**, over `LAct`. -/
noncomputable def TBD : Semiterm LAct Empty 1 := Semiterm.lMap emb (botT1 (searchT1 gD pD qD))

lemma lMap_swap_TBD : Semiterm.lMap swap TBD = TBD := term_lMap_swap_emb _

/-- `TBD` at the budget `k` denotes the canonical code of `pBot (DupocV k)`. -/
theorem val_TBD_V (k : V) : TBD.val (s := stdReadingV V) ![k] Empty.elim = canonical (pBot (DupocV k)) := by
  unfold TBD
  rw [Semiterm.val_lMap, stdReadingV_lMap_emb, val_botT1_V, val_searchT1_V, canonical_pBot, canonical_DupocV]

theorem quote_emb_TBD :
    (⌜(Rew.emb TBD : SyntacticSemiterm LAct 1)⌝ : V) =
    ppairTerm (binNumeral 3)
      (ppairTerm (binNumeral 6) (ppairTerm (^#0) (ppairTerm (binNumeral (gD : V)) (ppairTerm (codeTerm (pD : V)) (codeTerm (qD : V))))) ^+ 𝟏) ^+ 𝟏 := by
  unfold TBD
  rw [term_emb_lMap_emb_n, quote_term_lMap_emb, quote_emb_botT1, quote_emb_searchT1]

/-- **Filling the budget slot of the bot tower.** -/
theorem termSubst_TBD (k : V) :
    termSubst LAct (binNumeral k ∷ (0 : V)) (⌜(Rew.emb TBD : SyntacticSemiterm LAct 1)⌝ : V) =
      codeTerm (canonical (pBot (DupocV k))) := by
  have hb3 : IsUTerm LAct (binNumeral (3 : V)) := (binNumeral_semiterm_LAct 0 _).isUTerm
  have hb6 : IsUTerm LAct (binNumeral (6 : V)) := (binNumeral_semiterm_LAct 0 _).isUTerm
  have hbg : IsUTerm LAct (binNumeral (gD : V)) := (binNumeral_semiterm_LAct 0 _).isUTerm
  have hp : IsUTerm LAct (codeTerm (pD : V)) := (codeTerm_semiterm_LAct 0 _).isUTerm
  have hq : IsUTerm LAct (codeTerm (qD : V)) := (codeTerm_semiterm_LAct 0 _).isUTerm
  have hone : IsUTerm LAct (𝟏 : V) := (IsSemiterm.LAct_of_LOR (one_semiterm (n := 0))).isUTerm
  have h1 : IsUTerm LAct (ppairTerm (codeTerm (pD : V)) (codeTerm (qD : V))) := ppairTerm_uterm_LAct hp hq
  have h2 : IsUTerm LAct (ppairTerm (binNumeral (gD : V)) (ppairTerm (codeTerm (pD : V)) (codeTerm (qD : V)))) := ppairTerm_uterm_LAct hbg h1
  have h3 : IsUTerm LAct (ppairTerm (^#0) (ppairTerm (binNumeral (gD : V)) (ppairTerm (codeTerm (pD : V)) (codeTerm (qD : V))))) :=
    ppairTerm_uterm_LAct bvar_zero_uterm h2
  have h4 : IsUTerm LAct (ppairTerm (binNumeral 6) (ppairTerm (^#0) (ppairTerm (binNumeral (gD : V)) (ppairTerm (codeTerm (pD : V)) (codeTerm (qD : V)))))) :=
    ppairTerm_uterm_LAct hb6 h3
  have h5 : IsUTerm LAct (ppairTerm (binNumeral 6) (ppairTerm (^#0) (ppairTerm (binNumeral (gD : V)) (ppairTerm (codeTerm (pD : V)) (codeTerm (qD : V))))) ^+ 𝟏) :=
    qqAdd_uterm_LAct h4 hone
  have h6 : IsUTerm LAct (ppairTerm (binNumeral 3)
      (ppairTerm (binNumeral 6) (ppairTerm (^#0) (ppairTerm (binNumeral (gD : V)) (ppairTerm (codeTerm (pD : V)) (codeTerm (qD : V))))) ^+ 𝟏)) :=
    ppairTerm_uterm_LAct hb3 h5
  rw [quote_emb_TBD, termSubst_qqAdd _ h6 hone, termSubst_ppairTerm _ hb3 h5,
    termSubst_closed _ (binNumeral_semiterm_LAct 0 _), termSubst_closed _ (IsSemiterm.LAct_of_LOR one_semiterm),
    termSubst_tower, canonical_pBot, canonical_DupocV, codeTerm_bot]

lemma quote_emb_uD_botDupocV (k : V) :
    (⌜(Rew.emb uD : SyntacticSemiterm LAct 0)⌝ : V) = revalueU (pBot (DupocV k)) := by
  rw [revalueU_pBot, revalueU_DupocV, Semiterm.empty_quote_def]

lemma quote_emb_wD_botDupocV (k : V) :
    (⌜(Rew.emb wD : SyntacticSemiterm LAct 0)⌝ : V) = revalueW (pBot (DupocV k)) := by
  rw [revalueW_pBot, revalueW_DupocV, Semiterm.empty_quote_def]

/-- The bot tower's triple `(TBD, uD, wD)` describes `pBot (DupocV k)` on codes (`X`-hypothesis). -/
lemma hX_botDupoc (k : V) :
    termSubst LAct (binNumeral k ∷ (0 : V)) (⌜(Rew.emb TBD : SyntacticSemiterm LAct 1)⌝ : V) =
      codeTerm (canonical (pBot (DupocV k))) := termSubst_TBD k

lemma hU_botDupoc (k : V) : (⌜uD⌝ : V) = revalueU (pBot (DupocV k)) := quote_emb_uD_botDupocV k
lemma hW_botDupoc (k : V) : (⌜wD⌝ : V) = revalueW (pBot (DupocV k)) := quote_emb_wD_botDupocV k

/-- The bot tower's triple describes `pBot (DupocV k)` in `stdReadingV V`. -/
lemma desc_botDupoc (k : V) :
    revalue (uD.val (s := stdReadingV V) ![] Empty.elim) (wD.val (s := stdReadingV V) ![] Empty.elim)
      (TBD.val (s := stdReadingV V) ![k] Empty.elim) = pBot (DupocV k) := by
  rw [val_TBD_V, canonical_pBot, revalue_bot, revalue_val_uD_wD_V]

/-- The transposed bot triple describes `pBot (CupodV k)` in `stdReadingV V`. -/
lemma descT_botDupoc (k : V) :
    revalue ((Semiterm.lMap swap uD).val (s := stdReadingV V) ![] Empty.elim)
      ((Semiterm.lMap swap wD).val (s := stdReadingV V) ![] Empty.elim)
      ((Semiterm.lMap swap TBD).val (s := stdReadingV V) ![k] Empty.elim) = pBot (CupodV k) := by
  rw [lMap_swap_TBD, val_TBD_V, canonical_pBot, revalue_bot]
  have h := revalue_val_uC_wC_V (V := V) k
  unfold uC wC at h
  rw [h]

end towers

/-! ### 6. The `Describes` layer -/

section describes

/-- **The program a description triple denotes at the budget `k`** (`X` the one-variable structural term,
`U W` the two closed re-valuation terms). -/
noncomputable def descVal (X : Semiterm LAct Empty 1) (U W : ClosedSemiterm LAct 0) (k : V) : V :=
  revalue (U.val (s := stdReadingV V) ![] Empty.elim) (W.val (s := stdReadingV V) ![] Empty.elim)
    (X.val (s := stdReadingV V) ![k] Empty.elim)

lemma descVal_def (X : Semiterm LAct Empty 1) (U W : ClosedSemiterm LAct 0) (k : V) :
    descVal X U W k =
      revalue (U.val (s := stdReadingV V) ![] Empty.elim) (W.val (s := stdReadingV V) ![] Empty.elim)
        (X.val (s := stdReadingV V) ![k] Empty.elim) := rfl

/-- **A triple describes its value in every model**: the three code hypotheses of the instance equations
(`guardCode_qT_eq_instB`, `guardCode_DimcidV_eq_instB`) and "the transposed triple denotes the transposed
program". Every zoo opponent's triple is one (`describes_botCB`, `describes_TFT`, `describes_Guardian`). -/
structure Describes (X : Semiterm LAct Empty 1) (U W : ClosedSemiterm LAct 0) : Prop where
  hX : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (k : V),
    termSubst LAct (binNumeral k ∷ (0 : V)) (⌜(Rew.emb X : SyntacticSemiterm LAct 1)⌝ : V) =
      codeTerm (canonical (descVal X U W k))
  hU : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (k : V), (⌜U⌝ : V) = revalueU (descVal X U W k)
  hW : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (k : V), (⌜W⌝ : V) = revalueW (descVal X U W k)
  hT : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (k : V),
    descVal (Semiterm.lMap swap X) (Semiterm.lMap swap U) (Semiterm.lMap swap W) k = transposeCode (descVal X U W k)

/-- **A triple describes its value in every model ABOVE a standard threshold `K`** (`Describes` with the
hypothesis `K ≤ k` on every field): PrudentBot's canonical description (`Cells/PrudentMirror.lean` §2,
`KP ≤ k`). -/
structure DescribesAbove (K : ℕ) (X : Semiterm LAct Empty 1) (U W : ClosedSemiterm LAct 0) : Prop where
  hX : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (k : V), (K : V) ≤ k →
    termSubst LAct (binNumeral k ∷ (0 : V)) (⌜(Rew.emb X : SyntacticSemiterm LAct 1)⌝ : V) =
      codeTerm (canonical (descVal X U W k))
  hU : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (k : V), (K : V) ≤ k → (⌜U⌝ : V) = revalueU (descVal X U W k)
  hW : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (k : V), (K : V) ≤ k → (⌜W⌝ : V) = revalueW (descVal X U W k)
  hT : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (k : V), (K : V) ≤ k →
    descVal (Semiterm.lMap swap X) (Semiterm.lMap swap U) (Semiterm.lMap swap W) k = transposeCode (descVal X U W k)

/-- A description everywhere is a description above `0`. -/
theorem Describes.above {X : Semiterm LAct Empty 1} {U W : ClosedSemiterm LAct 0} (h : Describes X U W) :
    DescribesAbove 0 X U W where
  hX := fun V _ _ k _ ↦ h.hX V k
  hU := fun V _ _ k _ ↦ h.hU V k
  hW := fun V _ _ k _ ↦ h.hW V k
  hT := fun V _ _ k _ ↦ h.hT V k

/-! #### Every closed code is described -/

lemma lMap_swap_canonicalMeta' (P : ℕ) : Semiterm.lMap swap (canonicalMeta P) = canonicalMeta P := term_lMap_swap_emb _

/-- The code of the closed structural term of the canonical code of `P`, in every model. -/
theorem quote_emb_canonicalMeta (P : ℕ) :
    (⌜(Rew.emb (canonicalMeta P) : SyntacticSemiterm LAct 0)⌝ : V) = codeTerm (canonical (P : V)) := by
  unfold canonicalMeta
  rw [term_emb_lMap_emb, quote_term_lMap_emb, ← Semiterm.empty_quote_def, quote_codeTermMeta, cast_canonical]

/-- The generic closed triple denotes `P` itself (`revalue_val_desc_V`). -/
lemma descVal_closed (P : ℕ) (k : V) : descVal (cl (canonicalMeta P)) (revalueUMeta P) (revalueWMeta P) k = (P : V) := by
  rw [descVal_def, val_cl_V, val_canonicalMeta_V, revalue_val_desc_V]

/-- The transposed generic triple denotes the transposed program. -/
lemma descVal_closed_T (P : ℕ) (k : V) :
    descVal (Semiterm.lMap swap (cl (canonicalMeta P))) (Semiterm.lMap swap (revalueUMeta P)) (Semiterm.lMap swap (revalueWMeta P)) k =
      transposeCode (P : V) := by
  rw [descVal_def, lMap_swap_cl, lMap_swap_canonicalMeta', val_cl_V, val_canonicalMeta_V]
  unfold revalueUMeta revalueWMeta
  rcases lt_trichotomy P (transposeCode P) with h | h | h
  · rw [if_pos h, if_pos h, lMap_swap_cterm_C, lMap_swap_cterm_D, val_cterm_D_V, val_cterm_C_V, canonical_of_lt h]
  · have hs : transposeCode P = P := h.symm
    rw [hs, if_neg (_root_.lt_irrefl _), if_neg (_root_.lt_irrefl _), if_neg (_root_.lt_irrefl _),
      if_neg (_root_.lt_irrefl _), lMap_swap_numT, lMap_swap_numT, val_numT_V, val_numT_V, Nat.cast_zero,
      Nat.cast_one, canonical_of_eq h, revalue_zero_one, ← cast_transposeCode, hs]
  · rw [if_neg (lt_asymm h), if_pos h, if_neg (lt_asymm h), if_pos h, lMap_swap_cterm_D, lMap_swap_cterm_C,
      val_cterm_C_V, val_cterm_D_V, canonical_of_gt h, revalue_zero_one, cast_transposeCode]

/-- **Every closed code is described in every model**: the generic triple `(cl (canonicalMeta P), revalueUMeta P, revalueWMeta P)`. -/
theorem describes_closed (P : ℕ) : Describes (cl (canonicalMeta P)) (revalueUMeta P) (revalueWMeta P) where
  hX := by
    intro V _ _ k
    rw [descVal_closed, quote_emb_cl_V, termSubst_closed _ (semiterm_quote_emb₀ _), quote_emb_canonicalMeta]
  hU := by
    intro V _ _ k
    rw [descVal_closed]
    unfold revalueUMeta revalueU
    rcases lt_trichotomy P (transposeCode P) with h | h | h
    · have h' : (P : V) < transposeCode (P : V) := by rw [← cast_transposeCode]; exact Nat.cast_lt.mpr h
      rw [if_pos h, if_pos h', quote_cterm_C]
    · have hs : transposeCode P = P := h.symm
      have hs' : transposeCode (P : V) = (P : V) := by rw [← cast_transposeCode, hs]
      rw [hs, hs', if_neg (_root_.lt_irrefl _), if_neg (_root_.lt_irrefl _), if_neg (_root_.lt_irrefl _),
        if_neg (_root_.lt_irrefl _), quote_numT, Nat.cast_zero]
    · have h' : transposeCode (P : V) < (P : V) := by rw [← cast_transposeCode]; exact Nat.cast_lt.mpr h
      rw [if_neg (lt_asymm h), if_pos h, if_neg (lt_asymm h'), if_pos h', quote_cterm_D]
  hW := by
    intro V _ _ k
    rw [descVal_closed]
    unfold revalueWMeta revalueW
    rcases lt_trichotomy P (transposeCode P) with h | h | h
    · have h' : (P : V) < transposeCode (P : V) := by rw [← cast_transposeCode]; exact Nat.cast_lt.mpr h
      rw [if_pos h, if_pos h', quote_cterm_D]
    · have hs : transposeCode P = P := h.symm
      have hs' : transposeCode (P : V) = (P : V) := by rw [← cast_transposeCode, hs]
      rw [hs, hs', if_neg (_root_.lt_irrefl _), if_neg (_root_.lt_irrefl _), if_neg (_root_.lt_irrefl _),
        if_neg (_root_.lt_irrefl _), quote_numT, Nat.cast_one]
    · have h' : transposeCode (P : V) < (P : V) := by rw [← cast_transposeCode]; exact Nat.cast_lt.mpr h
      rw [if_neg (lt_asymm h), if_pos h, if_neg (lt_asymm h'), if_pos h', quote_cterm_C]
  hT := by intro V _ _ k; rw [descVal_closed_T, descVal_closed]

/-! #### The instances: the closed opponents, the engine searchers, the Dupoc towers -/

/-! #### `.bot CooperateBot` -/

lemma descVal_botCB (k : V) : descVal (cl TB0) (cterm Act.C) (cterm Act.D) k = pBot (pConst 0) :=
  val_desc_bot_zero k

lemma descVal_botCB_T (k : V) :
    descVal (Semiterm.lMap swap (cl TB0)) (Semiterm.lMap swap (cterm Act.C)) (Semiterm.lMap swap (cterm Act.D)) k =
      pBot (pConst 1) := by
  rw [descVal_def, lMap_swap_cl, lMap_swap_TB0, lMap_swap_cterm_C, lMap_swap_cterm_D]
  exact val_desc_bot_one k

/-- The triple `(cl T0, C, D)` describes `CooperateBot`'s code `pConst 0` in every model (the `T0` tower,
`val_desc_const_zero/one`; consolidation stage 5 — `loebSound_pDi0` is `loebSound_pG_of` of it). -/
theorem describes_CB : Describes (cl T0) (cterm Act.C) (cterm Act.D) where
  hX := by intro V _ _ k; rw [descVal_def, val_desc_const_zero]; exact hX_const_zero k
  hU := by intro V _ _ k; rw [descVal_def, val_desc_const_zero]; exact hU_C_zero
  hW := by intro V _ _ k; rw [descVal_def, val_desc_const_zero]; exact hW_D_zero
  hT := by
    intro V _ _ k
    rw [descVal_def, descVal_def, lMap_swap_cl, lMap_swap_T0, lMap_swap_cterm_C, lMap_swap_cterm_D,
      val_desc_const_one, val_desc_const_zero, transposeCode_pConst_zero]

/-- The triple `(cl TB0, C, D)` describes `.bot CooperateBot` in every model. -/
theorem describes_botCB : Describes (cl TB0) (cterm Act.C) (cterm Act.D) where
  hX := by intro V _ _ k; rw [descVal_botCB]; exact hX_bot_zero k
  hU := by intro V _ _ k; rw [descVal_botCB]; exact hU_C_bot_zero
  hW := by intro V _ _ k; rw [descVal_botCB]; exact hW_D_bot_zero
  hT := by intro V _ _ k; rw [descVal_botCB_T, descVal_botCB, transposeCode_pBot, transposeCode_pConst_zero]


lemma descVal_TFT (k : V) : descVal (cl TTFT) (cterm Act.C) (cterm Act.D) k = TFTV := by
  rw [descVal_def, val_cl_V, val_TTFT_V, val_cterm_C_V, val_cterm_D_V, revalue_zero_one]

lemma descVal_TFT_T (k : V) :
    descVal (Semiterm.lMap swap (cl TTFT)) (Semiterm.lMap swap (cterm Act.C)) (Semiterm.lMap swap (cterm Act.D)) k =
      TFTTV := by
  rw [descVal_def, lMap_swap_cl, lMap_swap_TTFT, lMap_swap_cterm_C, lMap_swap_cterm_D, val_cl_V, val_TTFT_V,
    val_cterm_C_V, val_cterm_D_V]
  exact transposeCode_TFTV

/-- The triple `(cl TTFT, C, D)` describes TitForTatBot in every model. -/
theorem describes_TFT : Describes (cl TTFT) (cterm Act.C) (cterm Act.D) where
  hX := by
    intro V _ _ k
    rw [descVal_TFT, quote_emb_cl_V, termSubst_closed _ (semiterm_quote_emb₀ _), quote_emb_TTFT, canonical_TFTV]
  hU := by intro V _ _ k; rw [descVal_TFT, quote_cterm_C, revalueU_TFTV]
  hW := by intro V _ _ k; rw [descVal_TFT, quote_cterm_D, revalueW_TFTV]
  hT := by intro V _ _ k; rw [descVal_TFT_T, descVal_TFT, transposeCode_TFTV]

/-! #### The `SV` layer describes the engine searchers -/

lemma descVal_SV (g : Semisentence LAct 6) (a : ℕ) (ha : a = 0 ∨ a = 1) (k : V) :
    descVal (TS g a) (uS g a) (wS g a) k = SV g a k := desc_SV g a ha k

lemma descVal_SV_T (g : Semisentence LAct 6) (a : ℕ) (ha : a = 0 ∨ a = 1) (k : V) :
    descVal (Semiterm.lMap swap (TS g a)) (Semiterm.lMap swap (uS g a)) (Semiterm.lMap swap (wS g a)) k =
      SV (Semiformula.lMap swap g) (1 - a) k := descT_SV g a ha k

/-- **The canonical triple of an engine searcher describes it in every model** (`PositiveCells` §2, packaged). -/
theorem describes_SV (g : Semisentence LAct 6) (a : ℕ) (ha : a = 0 ∨ a = 1) : Describes (TS g a) (uS g a) (wS g a) where
  hX := by intro V _ _ k; rw [descVal_SV g a ha]; exact hX_SV g a ha k
  hU := by intro V _ _ k; rw [descVal_SV g a ha]; exact hU_SV g a ha k
  hW := by intro V _ _ k; rw [descVal_SV g a ha]; exact hW_SV g a ha k
  hT := by intro V _ _ k; rw [descVal_SV_T g a ha, descVal_SV g a ha, transposeCode_SV g a ha]

/-! #### The bot-wrapped engine searcher `pBot (SV g a k)` (`.bot (DupocBot k)`, Just's frozen snapshot) -/

lemma descVal_botSV (g : Semisentence LAct 6) (a : ℕ) (ha : a = 0 ∨ a = 1) (k : V) :
    descVal (TBS g a) (uS g a) (wS g a) k = pBot (SV g a k) := desc_botSV g a ha k

lemma descVal_botSV_T (g : Semisentence LAct 6) (a : ℕ) (ha : a = 0 ∨ a = 1) (k : V) :
    descVal (Semiterm.lMap swap (TBS g a)) (Semiterm.lMap swap (uS g a)) (Semiterm.lMap swap (wS g a)) k =
      pBot (SV (Semiformula.lMap swap g) (1 - a) k) := descT_botSV g a ha k

/-- **The bot tower of an engine searcher describes `pBot (SV g a k)` in every model** (`PositiveCells` §5). -/
theorem describes_botSV (g : Semisentence LAct 6) (a : ℕ) (ha : a = 0 ∨ a = 1) :
    Describes (TBS g a) (uS g a) (wS g a) where
  hX := by intro V _ _ k; rw [descVal_botSV g a ha]; exact termSubst_TBS g a ha k
  hU := by intro V _ _ k; rw [descVal_botSV g a ha]; exact hU_botSV g a ha k
  hW := by intro V _ _ k; rw [descVal_botSV g a ha]; exact hW_botSV g a ha k
  hT := by intro V _ _ k; rw [descVal_botSV_T g a ha, descVal_botSV g a ha, transposeCode_pBot, transposeCode_SV g a ha]

/-! #### The hand-written Dupoc `DupocV k` (the `TD` tower) and its bot-wrapping (the `TBD` tower) -/

lemma descVal_dupocV (k : V) : descVal TD uD wD k = DupocV k := by
  rw [descVal_def, val_TD_V, revalue_val_uD_wD_V]

lemma descVal_dupocV_T (k : V) :
    descVal (Semiterm.lMap swap TD) (Semiterm.lMap swap uD) (Semiterm.lMap swap wD) k = CupodV k := by
  rw [descVal_def, lMap_swap_TD, val_TD_V]
  have h := revalue_val_uC_wC_V (V := V) k
  unfold uC wC at h
  exact h

/-- **The `TD` tower describes `DupocV k` in every model.** -/
theorem describes_dupocV : Describes TD uD wD where
  hX := by intro V _ _ k; rw [descVal_dupocV]; exact hX_dupoc k
  hU := by intro V _ _ k; rw [descVal_dupocV]; exact hU_dupoc k
  hW := by intro V _ _ k; rw [descVal_dupocV]; exact hW_dupoc k
  hT := by intro V _ _ k; rw [descVal_dupocV_T, descVal_dupocV, transposeCode_DupocV]

lemma descVal_botDupoc (k : V) : descVal TBD uD wD k = pBot (DupocV k) := desc_botDupoc k

lemma descVal_botDupoc_T (k : V) :
    descVal (Semiterm.lMap swap TBD) (Semiterm.lMap swap uD) (Semiterm.lMap swap wD) k = pBot (CupodV k) :=
  descT_botDupoc k

/-- **The `TBD` tower describes `pBot (DupocV k)` in every model** (`JustSlot` §3). -/
theorem describes_botDupoc : Describes TBD uD wD where
  hX := by intro V _ _ k; rw [descVal_botDupoc]; exact hX_botDupoc k
  hU := by intro V _ _ k; rw [descVal_botDupoc]; exact hU_botDupoc k
  hW := by intro V _ _ k; rw [descVal_botDupoc]; exact hW_botDupoc k
  hT := by intro V _ _ k; rw [descVal_botDupoc_T, descVal_botDupoc, transposeCode_pBot_DupocV]

end describes

end ArithS
