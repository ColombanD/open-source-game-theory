import ArithS.Cells.Common.Bots

/-!
# ArithS.Cells.Common.Templates — template instances, instance/truth equations, the `Describes` layer

Consolidation stage 3 (`Research/Notes/ROUTE_B_CELLS_MAP.md`). Everything here was MOVED
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


/-- The six codes of the substituted terms of `qG`, as an internal vector. -/
noncomputable def gVec (X : Semiterm LAct Empty 1) (U W : ClosedSemiterm LAct 0)
    (X' : Semiterm LAct Empty 1) (U' W' : ClosedSemiterm LAct 0) : V :=
  (⌜(Rew.emb X : SyntacticSemiterm LAct 1)⌝ : V) ∷
    ⌜(Rew.emb (cl U : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝ ∷
    ⌜(Rew.emb (cl W : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝ ∷
    ⌜(Rew.emb X' : SyntacticSemiterm LAct 1)⌝ ∷
    ⌜(Rew.emb (cl U' : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝ ∷
    ⌜(Rew.emb (cl W' : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝ ∷ 0


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


/-- **The one-variable description term of `pBot (Dupoc k)`**, over `LAct`. -/
noncomputable def TBD : Semiterm LAct Empty 1 := Semiterm.lMap emb (botT1 (searchT1 gD pD qD))


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


end describes

end ArithS
