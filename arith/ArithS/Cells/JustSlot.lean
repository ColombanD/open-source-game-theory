import ArithS.Cells.JustBot
import ArithS.Cells.CIMCIC

/-!
# ArithS.Cells.JustSlot — JustBot on a CONSTANT template with a budget slot (route c): Just × Just,
Just × Dupoc and CIMCIC × Just, all `(C, C)`, in PA-`S'`

`Research/Notes/ROUTE_B_SCOPE.md` §7–§8 (2026-09-23). `Cells/JustBot.lean` arithmetized
`JustBot k := .search k (.plays .opp (.bot (DupocBot k)) C) (.const C) (.const D)` as `JustV k :=
pSearch k (gJ k) …` with a `k`-DEPENDENT stored template `gJ k` (the description of the frozen snapshot
`pBot (Dupoc k)` pre-filled into the me-slots), so `JustV k` was not the `binNumeral k`-instance of any fixed
term and the family assembly (`Assembly/Family.family_found`) could not describe it (§7). Route (c):
the evaluator's search clause now fills a SEVENTH slot `#6` of the stored template with the node's own
budget (`guardCodeB`, `ArithS.Guard`/`ArithS.Eval`; six-variable templates unchanged by the gate lemma
`guardCodeB_of_template`). Just's template becomes the CONSTANT

  `guardTemplateJust7 := (guardTemplate 0 ⇜ ![TBD(#0), cl uD, cl wD, #1, #2, #3]) ⇜ ![#6, #3, #4, #5]`

("the program described by the frame's opp-triple `#3 #4 #5` plays C against the bot-wrapped Dupoc of
budget `#6`"), and `JustV7 k := pSearch k ⌜guardTemplateJust7⌝ (pConst 0) (pConst 1)` IS a `binNumeral k`-instance of a
fixed term, exactly like `DupocV`/`CimcicV` — so its description `TJ` is a one-variable term and every
guard mentioning `JustV7 k` is `instB ⌜q⌝ k` for a fixed `q`.

0. **Generic pieces**: `castLE` is quote-transparent (`quote_emb_castLE_V`); the description tower with
   an arbitrary substitution vector whose head is `binNumeral k` (`termSubst_tower_of`, `termSubst_TBD_of`);
   the τ-equivariance of `guardCodeB` (`revalueTemplate_guardCodeB`, from `termRelabelVec_descriptionsB`).
1. **The template and its instance equation**: `guardCodeB ⌜guardTemplateJust7⌝ me opp k = guardCode ⌜guardTemplate 0⌝
   (pBot (DupocV k)) opp` (`guardCodeB_guardTemplateJust7`) — Just's guard against `opp` IS the guard of the
   bot-wrapped Dupoc against `opp`, the frame's `me` unused (as `guardCode_JustV`); the transposed
   template `guardTemplateJust7A 1 uC wC = lMap swap guardTemplateJust7` gives `guardCode ⌜guardTemplate 1⌝ (pBot (CupodV k)) opp`.
2. **`JustV7` plays exactly as `JustV`** in every frame and at every fuel (`evalGraph_JustV7_iff`), so
   `loeb_Just_vs_Mirror` transfers (`loeb_Just7_vs_Mirror`).
3. **The description layer** of `JustV7 k` (`Cells/CIMCIC.lean` §2 re-run): `canonical (JustV7 k) = pSearch k
   gJd pJd qJd`, `TJ`, `uJ`, `wJ`, and the description hypotheses `hX_just7`/`desc_just7` (+ transposed).
4. **Just × Just `(C, C)`** (`llm_outcome_JustBot_vs_JustBot`): Just's guard against Just is "Just plays C
   against `pBot (Dupoc k)`" (`qJJ`), whose truth needs the box of the bot-wrapped self-play guard
   `qBD` — the family `pJJ := (qJJ ⋏ τqJJ) ⋏ pBD`, slack `(14, 16)`: **`loeb_Just7_vs_Just7`**.
5. **Just × Dupoc `(C, C)`** (`llm_outcome_JustBot_vs_DupocBot`, the engine's mutual Löb): three guards
   chase each other — Just's against Dupoc `qJD` ("Dupoc plays C against `pBot (Dupoc k)`"), whose truth
   needs Dupoc's guard against `pBot (Dupoc k)` `qBDD` ("`pBot (Dupoc k)` plays C against Dupoc"), whose
   truth needs `qJD` again; and Dupoc's guard against Just `qDJ` ("Just plays C against Dupoc"), whose
   truth needs `qJD`. The family `pJD := (qJD ⋏ τ) ⋏ ((qBDD ⋏ τ) ⋏ (qDJ ⋏ τ))`, a THREE-level
   ∧-elimination at slack `(21, 24)`: **`loeb_Just7_vs_Dupoc`** (both cooperate at fuel 2).
6. **CIMCIC × Just `(C, C)`** (`llm_outcome_CIMCIC_vs_JustBot`): CIMCIC's guard against Just `qCG TJ uJ wJ`
   (consequent: Just plays C against CIMCIC), Just's guard against CIMCIC `qJCi` ("CIMCIC plays C against
   `pBot (Dupoc k)`"), and CIMCIC's guard against `pBot (Dupoc k)` `qCG TBD uD wD` (consequent: the
   bot-wrapped Dupoc plays C against CIMCIC, which is Dupoc's guard against CIMCIC = `qJCi`). The family
   `pCJ := pGC TJ uJ wJ ⋏ ((qJCi ⋏ τ) ⋏ pGC TBD uD wD)`, slack `(21, 24)`:
   **`loeb_Cimcic_vs_Just7`**.

`JustBot k = JustBot2 k k`: `Just7 k` is the DIAGONAL — the snapshot's budget equals the searcher's,
read from the slot. Conventions (`HANDOVER_ARITHMETIZED_S.md` §5–6): every threshold EXISTENTIAL; `simp`
never sees a closed quote of `guardTemplateJust7`/`qJJ`/…; `omega` never asked about `V`; at ℕ the thresholds are
STRICT and the V-generic `≤` is bridged by `le_def`.
-/

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open LAct

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ### 0. Generic pieces -/

section generic


/-- The bot tower `TBD` under any substitution vector whose head is `binNumeral k`. -/
theorem termSubst_TBD_of (w k : V) (h0 : w.[0] = binNumeral k) :
    termSubst LAct w (⌜(Rew.emb TBD : SyntacticSemiterm LAct 1)⌝ : V) = codeTerm (canonical (pBot (DupocV k))) := by
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
    termSubst_tower_of w k _ _ _ h0, canonical_pBot, canonical_DupocV, codeTerm_bot]


end generic

/-! ### 1. The constant seven-variable template and its instance equation -/

section template

/-- The bot tower with the budget as `#0`, cast into four variables. -/
noncomputable def TBD4 : Semiterm LAct Empty 4 := Rew.castLE (by norm_num) TBD

/-- "The program described by the opp-triple `(#1, #2, #3)` plays `a` against the bot-wrapped searcher
described by `(TBD(#0), U, W)`": the budget in `#0`. -/
noncomputable def qJ4 (a : ℕ) (U W : ClosedSemiterm LAct 0) : Semisentence LAct 4 :=
  guardTemplate a ⇜ ![TBD4, cl U, cl W, #1, #2, #3]

/-- **The constant seven-variable template**: the frame's opp-triple in `#3 #4 #5`, the node budget in
`#6` (the me-triple `#0 #1 #2` unused, as in `guardTemplateJust`). -/
noncomputable def guardTemplateJust7A (a : ℕ) (U W : ClosedSemiterm LAct 0) : Semisentence LAct 7 :=
  qJ4 a U W ⇜ ![#6, #3, #4, #5]

/-- **Just's template**: "the opponent plays C against `pBot (Dupoc #6)`". -/
noncomputable def guardTemplateJust7 : Semisentence LAct 7 := guardTemplateJust7A 0 uD wD

lemma guardTemplateJust7_def : guardTemplateJust7 = guardTemplateJust7A 0 uD wD := rfl

lemma lMap_swap_TBD4 : Semiterm.lMap swap TBD4 = TBD4 := by
  unfold TBD4
  change Semiterm.lMap swap (Rew.map (Fin.castLE _) id TBD) = Rew.map (Fin.castLE _) id TBD
  rw [Semiterm.lMap_map, lMap_swap_TBD]

lemma lMap_swap_qJ4 (a : ℕ) (U W : ClosedSemiterm LAct 0) :
    Semiformula.lMap swap (qJ4 a U W) = qJ4 (swapAction a) (Semiterm.lMap swap U) (Semiterm.lMap swap W) := by
  unfold qJ4
  rw [Semiformula.lMap_subst, lMap_swap_GtmplA]
  congr 1
  funext i
  fin_cases i <;> simp [lMap_swap_TBD4, lMap_swap_cl]

lemma lMap_swap_guardTemplateJust7A (a : ℕ) (U W : ClosedSemiterm LAct 0) :
    Semiformula.lMap swap (guardTemplateJust7A a U W) =
      guardTemplateJust7A (swapAction a) (Semiterm.lMap swap U) (Semiterm.lMap swap W) := by
  unfold guardTemplateJust7A
  rw [Semiformula.lMap_subst, lMap_swap_qJ4]
  congr 1
  funext i
  fin_cases i <;> simp

/-- The transposition of Just's template is the Cupod-snapshot template with `uC = swap uD`. -/
lemma lMap_swap_guardTemplateJust7 : Semiformula.lMap swap guardTemplateJust7 = guardTemplateJust7A 1 uC wC := by
  rw [guardTemplateJust7_def, lMap_swap_guardTemplateJust7A, swapAction_zero]; rfl

/-! #### The codes -/

/-- The codes of `![#6, #3, #4, #5]`. -/
noncomputable def sVec7 : V :=
  (⌜(Rew.emb (#6 : Semiterm LAct Empty 7) : SyntacticSemiterm LAct 7)⌝ : V) ∷
    ⌜(Rew.emb (#3 : Semiterm LAct Empty 7) : SyntacticSemiterm LAct 7)⌝ ∷
    ⌜(Rew.emb (#4 : Semiterm LAct Empty 7) : SyntacticSemiterm LAct 7)⌝ ∷
    ⌜(Rew.emb (#5 : Semiterm LAct Empty 7) : SyntacticSemiterm LAct 7)⌝ ∷ 0

/-- The codes of `![TBD4, cl U, cl W, #1, #2, #3]`. -/
noncomputable def jVec4 (U W : ClosedSemiterm LAct 0) : V :=
  (⌜(Rew.emb TBD4 : SyntacticSemiterm LAct 4)⌝ : V) ∷
    ⌜(Rew.emb (cl U : Semiterm LAct Empty 4) : SyntacticSemiterm LAct 4)⌝ ∷
    ⌜(Rew.emb (cl W : Semiterm LAct Empty 4) : SyntacticSemiterm LAct 4)⌝ ∷
    ⌜(Rew.emb (#1 : Semiterm LAct Empty 4) : SyntacticSemiterm LAct 4)⌝ ∷
    ⌜(Rew.emb (#2 : Semiterm LAct Empty 4) : SyntacticSemiterm LAct 4)⌝ ∷
    ⌜(Rew.emb (#3 : Semiterm LAct Empty 4) : SyntacticSemiterm LAct 4)⌝ ∷ 0

theorem quote_guardTemplateJust7A (a : ℕ) (U W : ClosedSemiterm LAct 0) :
    (⌜guardTemplateJust7A a U W⌝ : V) = subst LAct sVec7 (⌜qJ4 a U W⌝ : V) := by
  unfold guardTemplateJust7A
  rw [Sentence.quote_def, Semiformula.coe_subst_eq_subst_coe, Semiformula.quote_def,
    Semiformula.typed_quote_substs, Bootstrapping.Semiformula.val_substs, ← Semiformula.quote_def,
    ← Sentence.quote_def]
  congr 1

theorem quote_qJ4 (a : ℕ) (U W : ClosedSemiterm LAct 0) :
    (⌜qJ4 a U W⌝ : V) = subst LAct (jVec4 U W) (⌜guardTemplate a⌝ : V) := by
  unfold qJ4
  rw [Sentence.quote_def, Semiformula.coe_subst_eq_subst_coe, Semiformula.quote_def,
    Semiformula.typed_quote_substs, Bootstrapping.Semiformula.val_substs, ← Semiformula.quote_def,
    ← Sentence.quote_def]
  congr 1

lemma quote_emb_bvar7_6 : (⌜(Rew.emb (#6 : Semiterm LAct Empty 7) : SyntacticSemiterm LAct 7)⌝ : V) = ^#6 := by
  simp [Rew.emb]
lemma quote_emb_bvar7_3 : (⌜(Rew.emb (#3 : Semiterm LAct Empty 7) : SyntacticSemiterm LAct 7)⌝ : V) = ^#3 := by
  simp [Rew.emb]
lemma quote_emb_bvar7_4 : (⌜(Rew.emb (#4 : Semiterm LAct Empty 7) : SyntacticSemiterm LAct 7)⌝ : V) = ^#4 := by
  simp [Rew.emb]
lemma quote_emb_bvar7_5 : (⌜(Rew.emb (#5 : Semiterm LAct Empty 7) : SyntacticSemiterm LAct 7)⌝ : V) = ^#5 := by
  simp [Rew.emb]
lemma quote_emb_bvar4_1 : (⌜(Rew.emb (#1 : Semiterm LAct Empty 4) : SyntacticSemiterm LAct 4)⌝ : V) = ^#1 := by
  simp [Rew.emb]
lemma quote_emb_bvar4_2 : (⌜(Rew.emb (#2 : Semiterm LAct Empty 4) : SyntacticSemiterm LAct 4)⌝ : V) = ^#2 := by
  simp [Rew.emb]
lemma quote_emb_bvar4_3 : (⌜(Rew.emb (#3 : Semiterm LAct Empty 4) : SyntacticSemiterm LAct 4)⌝ : V) = ^#3 := by
  simp [Rew.emb]

lemma sVec7_semitermVec : IsSemitermVec LAct 4 7 (sVec7 : V) := by
  rw [four_eq, sVec7]
  exact ((((IsSemitermVec.nil 7).adjoin (semiterm_quote_emb₇ (#5 : Semiterm LAct Empty 7))).adjoin
    (semiterm_quote_emb₇ (#4 : Semiterm LAct Empty 7))).adjoin
    (semiterm_quote_emb₇ (#3 : Semiterm LAct Empty 7))).adjoin
    (semiterm_quote_emb₇ (#6 : Semiterm LAct Empty 7))

lemma jVec4_semitermVec (U W : ClosedSemiterm LAct 0) : IsSemitermVec LAct 6 4 (jVec4 U W : V) := by
  rw [six_eq, jVec4]
  exact ((((((IsSemitermVec.nil 4).adjoin (semiterm_quote_emb₄ (#3 : Semiterm LAct Empty 4))).adjoin
    (semiterm_quote_emb₄ (#2 : Semiterm LAct Empty 4))).adjoin
    (semiterm_quote_emb₄ (#1 : Semiterm LAct Empty 4))).adjoin
    (semiterm_quote_emb₄ (cl W : Semiterm LAct Empty 4))).adjoin
    (semiterm_quote_emb₄ (cl U : Semiterm LAct Empty 4))).adjoin (semiterm_quote_emb₄ TBD4)

/-- The budget vector of the four-variable intermediate at the frame `opp` and budget `k`. -/
noncomputable def bVec4 (opp k : V) : V := binNumeral k ∷ codeTerm (canonical opp) ∷ revalueU opp ∷ revalueW opp ∷ 0

lemma bVec4_semitermVec (opp k : V) : IsSemitermVec LAct 4 0 (bVec4 opp k) := by
  rw [four_eq, bVec4]
  exact ((((IsSemitermVec.nil 0).adjoin (revalueW_semiterm 0 opp)).adjoin (revalueU_semiterm 0 opp)).adjoin
    (codeTerm_semiterm_LAct 0 (canonical opp))).adjoin (binNumeral_semiterm_LAct 0 k)

/-- Filling `![#6, #3, #4, #5]` with `descriptionsB me opp k` gives the budget vector of `(opp, k)`. -/
theorem termSubstVec_sVec7 (me opp k : V) :
    termSubstVec LAct 4 (descriptionsB me opp k) (sVec7 : V) = bVec4 opp k := by
  have h6 : IsUTerm LAct (^#6 : V) := (IsSemiterm.bvar.mpr (by norm_num : (6 : V) < 7)).isUTerm
  have h3 : IsUTerm LAct (^#3 : V) := (IsSemiterm.bvar.mpr (by norm_num : (3 : V) < 7)).isUTerm
  have h4 : IsUTerm LAct (^#4 : V) := (IsSemiterm.bvar.mpr (by norm_num : (4 : V) < 7)).isUTerm
  have h5 : IsUTerm LAct (^#5 : V) := (IsSemiterm.bvar.mpr (by norm_num : (5 : V) < 7)).isUTerm
  have e0 : IsUTermVec LAct 0 (0 : V) := IsUTermVec.empty
  have e1 := e0.adjoin h5
  have e2 := e1.adjoin h4
  have e3 := e2.adjoin h3
  have h : termSubstVec LAct (0 + 1 + 1 + 1 + 1) (descriptionsB me opp k) (^#6 ∷ ^#3 ∷ ^#4 ∷ ^#5 ∷ (0 : V)) =
      bVec4 opp k := by
    unfold bVec4
    rw [termSubstVec_cons h6 e3, termSubstVec_cons h3 e2, termSubstVec_cons h4 e1, termSubstVec_cons h5 e0,
      termSubstVec_nil, termSubst_bvar, termSubst_bvar, termSubst_bvar, termSubst_bvar, nth_descriptionsB_six,
      nth_descriptionsB_three, nth_descriptionsB_four, nth_descriptionsB_five]
  rw [← four_eq] at h
  unfold sVec7
  rw [quote_emb_bvar7_6, quote_emb_bvar7_3, quote_emb_bvar7_4, quote_emb_bvar7_5]
  exact h

/-- Filling `![TBD4, cl U, cl W, #1, #2, #3]` with the budget vector gives the description vector of
`(pBot (DupocV k), opp)` up to the two closed entries. -/
theorem termSubstVec_jVec4 (U W : ClosedSemiterm LAct 0) (opp k : V) :
    termSubstVec LAct 6 (bVec4 opp k) (jVec4 U W) =
      codeTerm (canonical (pBot (DupocV k))) ∷ (⌜(Rew.emb U : SyntacticSemiterm LAct 0)⌝ : V) ∷
        (⌜(Rew.emb W : SyntacticSemiterm LAct 0)⌝ : V) ∷ codeTerm (canonical opp) ∷ revalueU opp ∷ revalueW opp ∷ 0 := by
  unfold jVec4 TBD4
  rw [quote_emb_castLE_V, show (cl U : Semiterm LAct Empty 4) = Rew.castLE (Nat.zero_le 4) U from rfl,
    show (cl W : Semiterm LAct Empty 4) = Rew.castLE (Nat.zero_le 4) W from rfl,
    quote_emb_castLE_V, quote_emb_castLE_V, quote_emb_bvar4_1, quote_emb_bvar4_2, quote_emb_bvar4_3]
  have hT : IsUTerm LAct (⌜(Rew.emb TBD : SyntacticSemiterm LAct 1)⌝ : V) := (semiterm_quote_emb₁ _).isUTerm
  have hU : IsUTerm LAct (⌜(Rew.emb U : SyntacticSemiterm LAct 0)⌝ : V) := (semiterm_quote_emb₀ _).isUTerm
  have hW : IsUTerm LAct (⌜(Rew.emb W : SyntacticSemiterm LAct 0)⌝ : V) := (semiterm_quote_emb₀ _).isUTerm
  have h1 : IsUTerm LAct (^#1 : V) := (IsSemiterm.bvar.mpr (by norm_num : (1 : V) < 4)).isUTerm
  have h2 : IsUTerm LAct (^#2 : V) := (IsSemiterm.bvar.mpr (by norm_num : (2 : V) < 4)).isUTerm
  have h3 : IsUTerm LAct (^#3 : V) := (IsSemiterm.bvar.mpr (by norm_num : (3 : V) < 4)).isUTerm
  have e0 : IsUTermVec LAct 0 (0 : V) := IsUTermVec.empty
  have e1 := e0.adjoin h3
  have e2 := e1.adjoin h2
  have e3 := e2.adjoin h1
  have e4 := e3.adjoin hW
  have e5 := e4.adjoin hU
  rw [six_eq, termSubstVec_cons hT e5, termSubstVec_cons hU e4, termSubstVec_cons hW e3,
    termSubstVec_cons h1 e2, termSubstVec_cons h2 e1, termSubstVec_cons h3 e0, termSubstVec_nil,
    termSubst_TBD_of _ k (by unfold bVec4; rw [nth_adjoin_zero]),
    termSubst_closed _ (semiterm_quote_emb₀ _), termSubst_closed _ (semiterm_quote_emb₀ _),
    termSubst_bvar, termSubst_bvar, termSubst_bvar]
  unfold bVec4
  rw [show (3 : V) = 2 + 1 by norm_num, nth_adjoin_succ]
  simp only [nth_adjoin_zero, nth_adjoin_one, nth_adjoin_two]

/-- **The generic instance equation of the seven-variable template**: its guard code with the node
budget is `guardTemplate a` filled with the bot tower at `k`, the two closed terms, and `opp`'s description. -/
theorem guardCodeB_guardTemplateJust7A (a : ℕ) (U W : ClosedSemiterm LAct 0) (me opp k : V) :
    guardCodeB (⌜guardTemplateJust7A a U W⌝ : V) me opp k =
      subst LAct (codeTerm (canonical (pBot (DupocV k))) ∷ (⌜(Rew.emb U : SyntacticSemiterm LAct 0)⌝ : V) ∷
        (⌜(Rew.emb W : SyntacticSemiterm LAct 0)⌝ : V) ∷ codeTerm (canonical opp) ∷ revalueU opp ∷ revalueW opp ∷ 0)
        (⌜guardTemplate a⌝ : V) := by
  unfold guardCodeB
  rw [quote_guardTemplateJust7A, substs_substs (isSemiformula_quote₄ (qJ4 a U W)) (descriptionsB_semitermVec me opp k)
    sVec7_semitermVec, termSubstVec_sVec7, quote_qJ4,
    substs_substs (isSemiformula_quote₆ (guardTemplate a)) (bVec4_semitermVec opp k) (jVec4_semitermVec U W),
    termSubstVec_jVec4]

/-- **Just's instance equation**: in the frame `(me, opp)`, the constant template filled with the node
budget `k` IS the guard of the bot-wrapped Dupoc of budget `k` against `opp` — the frame's `me` unused. -/
theorem guardCodeB_guardTemplateJust7 (me opp k : V) :
    guardCodeB (⌜guardTemplateJust7⌝ : V) me opp k = guardCode (⌜guardTemplate 0⌝ : V) (pBot (DupocV k)) opp := by
  rw [guardTemplateJust7_def, guardCodeB_guardTemplateJust7A, quote_emb_uD_botDupocV, quote_emb_wD_botDupocV]
  rfl

/-- **The transposed instance equation**: the Cupod-snapshot template gives the guard of the bot-wrapped
Cupod against `opp`. -/
theorem guardCodeB_guardTemplateJust7T (me opp k : V) :
    guardCodeB (⌜guardTemplateJust7A 1 uC wC⌝ : V) me opp k = guardCode (⌜guardTemplate 1⌝ : V) (pBot (CupodV k)) opp := by
  have h := revalueTemplate_guardCodeB (isSemiformula_quote₇ guardTemplateJust7) (transposeCode me) (transposeCode opp) k
  rw [transposeCode_transposeCode, transposeCode_transposeCode, revalueTemplate_quote_sentence₇_V, lMap_swap_guardTemplateJust7,
    guardCodeB_guardTemplateJust7] at h
  rw [← h]
  have hg0 : IsSemiformula LAct 6 (⌜guardTemplate 0⌝ : V) := isSemiformula_quote₆ (guardTemplate 0)
  have hg1 : IsSemiformula LAct 6 (⌜guardTemplate 1⌝ : V) := isSemiformula_quote₆ (guardTemplate 1)
  rw [← substTemplate_of_template hg0, revalueTemplate_substTemplate, transposeCode_pBot_DupocV, transposeCode_transposeCode,
    revalueTemplate_quote_GtmplA_V, swapAction_zero, substTemplate_of_template hg1]

end template

/-! ### 2. `JustV7`: the searcher on the constant template, and its equivalence with `JustV` -/

section just7

/-- **JustBot on the constant template, in every model**: `pSearch k ⌜guardTemplateJust7⌝ (pConst 0) (pConst 1)`. -/
noncomputable def JustV7 (k : V) : V := pSearch k (⌜guardTemplateJust7⌝ : V) (pConst 0) (pConst 1)

/-- The transposed searcher (found ⇒ `D`). -/
noncomputable def JustTV7 (k : V) : V := pSearch k (⌜guardTemplateJust7A 1 uC wC⌝ : V) (pConst 1) (pConst 0)

/-- **JustBot at ℕ on the constant template.** -/
noncomputable def Just7 (k : ℕ) : ℕ := JustV7 (V := ℕ) k

lemma JustV7_nat (k : ℕ) : JustV7 (V := ℕ) k = Just7 k := rfl

theorem transposeCode_JustV7 (k : V) : transposeCode (JustV7 k) = JustTV7 k := by
  unfold JustV7 JustTV7 transposeCode
  rw [revalue_search, revalue_const, revalue_const, revalueTemplate_quote_sentence₇_V, lMap_swap_guardTemplateJust7]
  simp [revalueAction]

theorem transposeCode_JustTV7 (k : V) : transposeCode (JustTV7 k) = JustV7 k := by
  rw [← transposeCode_JustV7, transposeCode_transposeCode]

/-- **Just's search clause in ANY frame** (fuel 2): a proof within `k` of "`opp` plays C against
`pBot (Dupoc k)`" makes `JustV7 k` cooperate with `opp`. -/
theorem just7_search_V (k me opp : V) :
    LenBox TAct k (guardCode (⌜guardTemplate 0⌝ : V) (pBot (DupocV k)) opp) →
      EvalGraph 2 me opp (JustV7 k) 0 := by
  intro h
  rw [show (2 : V) = 1 + 1 from one_add_one_eq_two.symm]
  show EvalGraph (1 + 1) me opp (pSearch k (⌜guardTemplateJust7⌝ : V) (pConst 0) (pConst 1)) 0
  rw [EvalGraph.search_iff, guardCodeB_guardTemplateJust7]
  left
  refine ⟨h, ?_⟩
  rw [show (1 : V) = 0 + 1 by simp, EvalGraph.const_iff]

/-- **The transposed searcher's search clause in any frame** (fuel 2): found ⇒ `D`. -/
theorem just7T_search_V (k me opp : V) :
    LenBox TAct k (guardCode (⌜guardTemplate 1⌝ : V) (pBot (CupodV k)) opp) →
      EvalGraph 2 me opp (JustTV7 k) 1 := by
  intro h
  rw [show (2 : V) = 1 + 1 from one_add_one_eq_two.symm]
  show EvalGraph (1 + 1) me opp (pSearch k (⌜guardTemplateJust7A 1 uC wC⌝ : V) (pConst 1) (pConst 0)) 1
  rw [EvalGraph.search_iff, guardCodeB_guardTemplateJust7T]
  left
  refine ⟨h, ?_⟩
  have e : EvalGraph (0 + 1) me opp (pConst 1) 1 := EvalGraph.const_iff.mpr rfl
  rwa [zero_add] at e

/-- **`JustV7 k` and `JustV k` play identically**: in every frame, at every fuel, the same results. -/
theorem evalGraph_JustV7_iff (n me opp a k : V) :
    EvalGraph n me opp (JustV7 k) a ↔ EvalGraph n me opp (JustV k) a := by
  rcases zero_or_succ n with rfl | ⟨n, rfl⟩
  · exact ⟨fun h ↦ absurd h EvalGraph.zero_iff, fun h ↦ absurd h EvalGraph.zero_iff⟩
  · have hgJ : IsSemiformula LAct 6 (gJ k) := (isSemiformula_quote₆ (guardTemplate 0)).subst (jVec_semitermVec k)
    unfold JustV7 JustV
    rw [EvalGraph.search_iff, guardCodeB_guardTemplateJust7, EvalGraph.search_iff₆ hgJ, guardCode_JustV]

/-- The same at ℕ, for the ℕ-level constants. -/
theorem evalGraph_Just7_iff (n me opp a k : ℕ) :
    EvalGraph n me opp (Just7 k) a ↔ EvalGraph n me opp (Just k) a := by
  rw [← JustV7_nat, ← JustV_nat]; exact evalGraph_JustV7_iff n me opp a k

/-- **Just × Mirror `(C, C)` transfers to the constant-template Just** (unconditional): fuel 2 for Just,
fuel 3 for Mirror. -/
theorem loeb_Just7_vs_Mirror :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 2 (Just7 k) Mirror (Just7 k) 0 ∧ EvalGraph 3 Mirror (Just7 k) Mirror 0 := by
  obtain ⟨k₀, h⟩ := loeb_Just_vs_Mirror_core_of_nec boundedInnerNec_sixteen
  refine ⟨k₀, fun k hk ↦ ?_⟩
  have hJ : EvalGraph 2 (Just7 k) Mirror (Just7 k) 0 := just7_search_V (V := ℕ) k _ Mirror (h k hk).2.1
  exact ⟨hJ, (mirror_step_V (V := ℕ) 2 (Just7 k) 0).mpr hJ⟩

/-- **The else branch of the budget-slot Just in any frame** (fuel 2): the guard "`opp` plays C against
`pBot (Dupoc k)`" not found ⇒ `D`. -/
theorem just7_else_V (k me opp : V) :
    ¬ LenBox TAct k (guardCode (⌜guardTemplate 0⌝ : V) (pBot (DupocV k)) opp) →
      EvalGraph 2 me opp (JustV7 k) 1 := by
  intro h
  rw [show (2 : V) = 1 + 1 from one_add_one_eq_two.symm]
  show EvalGraph (1 + 1) me opp (pSearch k (⌜guardTemplateJust7⌝ : V) (pConst 0) (pConst 1)) 1
  rw [EvalGraph.search_iff, guardCodeB_guardTemplateJust7]
  right
  refine ⟨h, ?_⟩
  have e : EvalGraph (0 + 1) me opp (pConst 1) 1 := EvalGraph.const_iff.mpr rfl
  rwa [zero_add] at e

/-- **`Just7 k` defects against an opponent that defects against `pBot (Dupoc k)`** (soundness of a found
guard, `evalGraph_of_guard`, against the arithmetized sub-play). -/
theorem just7_D_of_probe (k : ℕ) {opp : ℕ} {N : ℕ} (h : EvalGraph N opp (pBot (Dupoc k)) opp 1) :
    EvalGraph 2 (Just7 k) opp (Just7 k) 1 := by
  refine just7_else_V (V := ℕ) k (Just7 k) opp fun hf ↦ ?_
  obtain ⟨n, hn⟩ := evalGraph_of_guard hf
  exact absurd (EvalGraph.unique' hn h) (by decide)

end just7

/-! ### 3. The description layer of `JustV7 k` (`Cells/CIMCIC.lean` §2 re-run) -/

section canonical

/-- The budget-independent inner part of Just's code. -/
noncomputable def innerJ : ℕ := ppair (⌜guardTemplateJust7⌝ : ℕ) (ppair (pConst 0) (pConst 1))

/-- The budget-independent inner part of the transposed searcher's code. -/
noncomputable def innerJT : ℕ := ppair (⌜guardTemplateJust7A 1 uC wC⌝ : ℕ) (ppair (pConst 1) (pConst 0))

lemma innerJ_def : innerJ = ppair (⌜guardTemplateJust7⌝ : ℕ) (ppair (pConst 0) (pConst 1)) := rfl
lemma innerJT_def : innerJT = ppair (⌜guardTemplateJust7A 1 uC wC⌝ : ℕ) (ppair (pConst 1) (pConst 0)) := rfl

/- Closed constants built from the giant template: never to be evaluated. -/
attribute [irreducible] innerJ innerJT

lemma cast_innerJ : ((innerJ : ℕ) : V) = ppair (⌜guardTemplateJust7⌝ : V) (ppair (pConst 0) (pConst 1)) := by
  rw [innerJ_def, cast_ppair, cast_ppair, cast_pConst, cast_pConst, coe_quote_sentence₇]
  push_cast
  rfl

lemma cast_innerJT : ((innerJT : ℕ) : V) = ppair (⌜guardTemplateJust7A 1 uC wC⌝ : V) (ppair (pConst 1) (pConst 0)) := by
  rw [innerJT_def, cast_ppair, cast_ppair, cast_pConst, cast_pConst, coe_quote_sentence₇]
  push_cast
  rfl

lemma JustV7_eq_inner (k : V) : JustV7 k = ppair 6 (ppair k (innerJ : V)) + 1 := by
  rw [cast_innerJ]; rfl
lemma JustTV7_eq_inner (k : V) : JustTV7 k = ppair 6 (ppair k (innerJT : V)) + 1 := by
  rw [cast_innerJT]; rfl

lemma JustV7_lt_JustTV7_iff (k : V) : JustV7 k < JustTV7 k ↔ innerJ < innerJT := by
  rw [JustV7_eq_inner, JustTV7_eq_inner, pSearchInner_lt_iff, Nat.cast_lt]

lemma JustTV7_lt_JustV7_iff (k : V) : JustTV7 k < JustV7 k ↔ innerJT < innerJ := by
  rw [JustV7_eq_inner, JustTV7_eq_inner, pSearchInner_lt_iff, Nat.cast_lt]

/-- The stored template of the canonical searcher. -/
noncomputable def gJd : ℕ := if innerJ ≤ innerJT then (⌜guardTemplateJust7⌝ : ℕ) else (⌜guardTemplateJust7A 1 uC wC⌝ : ℕ)
/-- Its then-branch. -/
noncomputable def pJd : ℕ := if innerJ ≤ innerJT then pConst 0 else pConst 1
/-- Its else-branch. -/
noncomputable def qJd : ℕ := if innerJ ≤ innerJT then pConst 1 else pConst 0
/-- The first re-valuation term of the description of `JustV7 k`. -/
noncomputable def uJ : ClosedSemiterm LAct 0 :=
  if innerJ < innerJT then cterm Act.C else if innerJT < innerJ then cterm Act.D else numT 0
/-- The second re-valuation term of the description of `JustV7 k`. -/
noncomputable def wJ : ClosedSemiterm LAct 0 :=
  if innerJ < innerJT then cterm Act.D else if innerJT < innerJ then cterm Act.C else numT 1

lemma JustV7_eq_cast (k : V) :
    JustV7 k = pSearch k ((⌜guardTemplateJust7⌝ : ℕ) : V) ((pConst 0 : ℕ) : V) ((pConst 1 : ℕ) : V) := by
  unfold JustV7; rw [coe_quote_sentence₇, cast_pConst, cast_pConst]; push_cast; rfl

lemma JustTV7_eq_cast (k : V) :
    JustTV7 k = pSearch k ((⌜guardTemplateJust7A 1 uC wC⌝ : ℕ) : V) ((pConst 1 : ℕ) : V) ((pConst 0 : ℕ) : V) := by
  unfold JustTV7; rw [coe_quote_sentence₇, cast_pConst, cast_pConst]; push_cast; rfl

/-- **The canonical code of `JustV7 k` is a searcher with the (cast) `k`-independent inner triple.** -/
theorem canonical_JustV7 (k : V) : canonical (JustV7 k) = pSearch k (gJd : V) (pJd : V) (qJd : V) := by
  by_cases h : innerJ ≤ innerJT
  · simp only [gJd, pJd, qJd, if_pos h]
    rcases Nat.lt_or_eq_of_le h with h' | h'
    · rw [canonical_of_lt (by rw [transposeCode_JustV7]; exact (JustV7_lt_JustTV7_iff k).mpr h')]
      exact JustV7_eq_cast k
    · rw [canonical_of_eq (by rw [transposeCode_JustV7, JustV7_eq_inner, JustTV7_eq_inner, h'])]
      exact JustV7_eq_cast k
  · simp only [gJd, pJd, qJd, if_neg h]
    rw [canonical_of_gt (by rw [transposeCode_JustV7]; exact (JustTV7_lt_JustV7_iff k).mpr (Nat.lt_of_not_le h)),
      transposeCode_JustV7]
    exact JustTV7_eq_cast k

theorem revalueU_JustV7 (k : V) : revalueU (JustV7 k) = (⌜uJ⌝ : V) := by
  unfold revalueU uJ
  rw [transposeCode_JustV7]
  by_cases h1 : innerJ < innerJT
  · rw [if_pos ((JustV7_lt_JustTV7_iff k).mpr h1), if_pos h1, quote_cterm_C]
  · rw [if_neg (fun h ↦ h1 ((JustV7_lt_JustTV7_iff k).mp h)), if_neg h1]
    by_cases h2 : innerJT < innerJ
    · rw [if_pos ((JustTV7_lt_JustV7_iff k).mpr h2), if_pos h2, quote_cterm_D]
    · rw [if_neg (fun h ↦ h2 ((JustTV7_lt_JustV7_iff k).mp h)), if_neg h2, quote_numT]
      simp

theorem revalueW_JustV7 (k : V) : revalueW (JustV7 k) = (⌜wJ⌝ : V) := by
  unfold revalueW wJ
  rw [transposeCode_JustV7]
  by_cases h1 : innerJ < innerJT
  · rw [if_pos ((JustV7_lt_JustTV7_iff k).mpr h1), if_pos h1, quote_cterm_D]
  · rw [if_neg (fun h ↦ h1 ((JustV7_lt_JustTV7_iff k).mp h)), if_neg h1]
    by_cases h2 : innerJT < innerJ
    · rw [if_pos ((JustTV7_lt_JustV7_iff k).mpr h2), if_pos h2, quote_cterm_C]
    · rw [if_neg (fun h ↦ h2 ((JustTV7_lt_JustV7_iff k).mp h)), if_neg h2, quote_numT]
      simp

/-- The one-variable description term of Just, over `LAct`. -/
noncomputable def TJ : Semiterm LAct Empty 1 := Semiterm.lMap emb (searchT1 gJd pJd qJd)

lemma lMap_swap_TJ : Semiterm.lMap swap TJ = TJ := term_lMap_swap_emb _

/-- The code of `TJ` (over `LAct`) is the `ℒₒᵣ` tower. -/
theorem quote_emb_TJ :
    (⌜(Rew.emb TJ : SyntacticSemiterm LAct 1)⌝ : V) =
    ppairTerm (binNumeral 6) (ppairTerm (^#0) (ppairTerm (binNumeral (gJd : V)) (ppairTerm (codeTerm (pJd : V)) (codeTerm (qJd : V))))) ^+ 𝟏 := by
  unfold TJ
  rw [term_emb_lMap_emb_n, quote_term_lMap_emb, quote_emb_searchT1]

/-- **`TJ` at the budget `k` denotes the canonical code of `JustV7 k`** (in `stdReadingV V`). -/
theorem val_TJ_V (k : V) : TJ.val (s := stdReadingV V) ![k] Empty.elim = canonical (JustV7 k) := by
  unfold TJ
  rw [Semiterm.val_lMap, stdReadingV_lMap_emb, val_searchT1_V, canonical_JustV7]

/-- The `k`-independent re-valuation terms reconstruct `JustV7 k` from its canonical code. -/
theorem revalue_val_uJ_wJ_V (k : V) :
    revalue (uJ.val (s := stdReadingV V) ![] Empty.elim) (wJ.val (s := stdReadingV V) ![] Empty.elim)
      (canonical (JustV7 k)) = JustV7 k := by
  unfold uJ wJ
  by_cases h1 : innerJ < innerJT
  · rw [if_pos h1, if_pos h1, val_cterm_C_V, val_cterm_D_V,
      canonical_of_lt (by rw [transposeCode_JustV7]; exact (JustV7_lt_JustTV7_iff k).mpr h1), revalue_zero_one]
  · rw [if_neg h1, if_neg h1]
    by_cases h2 : innerJT < innerJ
    · rw [if_pos h2, if_pos h2, val_cterm_D_V, val_cterm_C_V,
        canonical_of_gt (by rw [transposeCode_JustV7]; exact (JustTV7_lt_JustV7_iff k).mpr h2)]
      exact transposeCode_transposeCode _
    · have h' : innerJ = innerJT := le_antisymm (not_lt.mp h2) (not_lt.mp h1)
      rw [if_neg h2, if_neg h2, val_numT_V, val_numT_V, Nat.cast_zero, Nat.cast_one,
        canonical_of_eq (by rw [transposeCode_JustV7, JustV7_eq_inner, JustTV7_eq_inner, h']), revalue_zero_one]

/-- The transposed re-valuation terms. -/
noncomputable def uJT : ClosedSemiterm LAct 0 := Semiterm.lMap swap uJ
noncomputable def wJT : ClosedSemiterm LAct 0 := Semiterm.lMap swap wJ

/-- The transposed descriptions reconstruct `JustTV7 k` from the canonical code of `JustV7 k`. -/
theorem revalue_val_uJT_wJT_V (k : V) :
    revalue (uJT.val (s := stdReadingV V) ![] Empty.elim) (wJT.val (s := stdReadingV V) ![] Empty.elim)
      (canonical (JustV7 k)) = JustTV7 k := by
  unfold uJT wJT uJ wJ
  by_cases h1 : innerJ < innerJT
  · rw [if_pos h1, if_pos h1, lMap_swap_cterm_C, lMap_swap_cterm_D, val_cterm_D_V, val_cterm_C_V,
      canonical_of_lt (by rw [transposeCode_JustV7]; exact (JustV7_lt_JustTV7_iff k).mpr h1)]
    exact transposeCode_JustV7 k
  · rw [if_neg h1, if_neg h1]
    by_cases h2 : innerJT < innerJ
    · rw [if_pos h2, if_pos h2, lMap_swap_cterm_D, lMap_swap_cterm_C, val_cterm_C_V, val_cterm_D_V,
        canonical_of_gt (by rw [transposeCode_JustV7]; exact (JustTV7_lt_JustV7_iff k).mpr h2), transposeCode_JustV7,
        revalue_zero_one]
    · have h' : innerJ = innerJT := le_antisymm (not_lt.mp h2) (not_lt.mp h1)
      rw [if_neg h2, if_neg h2, lMap_swap_numT, lMap_swap_numT, val_numT_V, val_numT_V, Nat.cast_zero,
        Nat.cast_one, canonical_of_eq (by rw [transposeCode_JustV7, JustV7_eq_inner, JustTV7_eq_inner, h']),
        revalue_zero_one]
      have e : JustV7 k = JustTV7 k := by rw [JustV7_eq_inner, JustTV7_eq_inner, h']
      exact e

/-! #### The description hypotheses -/

/-- Just's own triple describes `JustV7 k` on codes. -/
lemma hX_just7 (k : V) :
    termSubst LAct (binNumeral k ∷ (0 : V)) (⌜(Rew.emb TJ : SyntacticSemiterm LAct 1)⌝ : V) =
      codeTerm (canonical (JustV7 k)) := by
  rw [quote_emb_TJ, termSubst_tower, canonical_JustV7]

lemma hU_just7 (k : V) : (⌜uJ⌝ : V) = revalueU (JustV7 k) := (revalueU_JustV7 k).symm
lemma hW_just7 (k : V) : (⌜wJ⌝ : V) = revalueW (JustV7 k) := (revalueW_JustV7 k).symm

/-- Just's own triple describes `JustV7 k` in `stdReadingV V`. -/
lemma desc_just7 (k : V) :
    revalue (uJ.val (s := stdReadingV V) ![] Empty.elim) (wJ.val (s := stdReadingV V) ![] Empty.elim)
      (TJ.val (s := stdReadingV V) ![k] Empty.elim) = JustV7 k := by
  rw [val_TJ_V]; exact revalue_val_uJ_wJ_V k

/-- The transposed triple describes `JustTV7 k` in `stdReadingV V`. -/
lemma descT_just7 (k : V) :
    revalue ((Semiterm.lMap swap uJ).val (s := stdReadingV V) ![] Empty.elim)
      ((Semiterm.lMap swap wJ).val (s := stdReadingV V) ![] Empty.elim)
      ((Semiterm.lMap swap TJ).val (s := stdReadingV V) ![k] Empty.elim) = JustTV7 k := by
  rw [lMap_swap_TJ, val_TJ_V]; exact revalue_val_uJT_wJT_V k


end canonical

/-! ### 4. The slack arithmetic of a THREE-level conjunction family, `(21, 24)` -/

section slack

/-- Two-level elimination under the `(21, 24)` budget (the left conjunct split). -/
lemma slack6_le₁ (a x y u v z : V) (hx : x = u + v + 1) (hz : z = x + y + 1) :
    a + 8 * (x + y) + 7 + 8 * (u + v) + 7 ≤ a + ((21 : ℕ) : V) + ((24 : ℕ) : V) * z := by
  refine le_trans (slack4_le a x y u v z hx hz) ?_
  push_cast
  gcongr <;> norm_num

/-- Three-level elimination: the right conjunct `y = y₁ + y₂ + 1` split, then its LEFT part
`y₁ = s + t + 1`. -/
lemma slack6_le (a x y y₁ y₂ s t z : V) (hy : y = y₁ + y₂ + 1) (hs : y₁ = s + t + 1) (hz : z = x + y + 1) :
    a + 8 * (x + y) + 7 + 8 * (y₁ + y₂) + 7 + 8 * (s + t) + 7 ≤ a + ((21 : ℕ) : V) + ((24 : ℕ) : V) * z := by
  have h1 : y₁ + y₂ ≤ x + y := by subst hy; exact le_trans le_self_add le_add_self
  have h2 : s + t ≤ x + y := by
    subst hy hs
    calc s + t ≤ s + t + 1 := le_self_add
      _ ≤ s + t + 1 + y₂ := le_self_add
      _ ≤ s + t + 1 + y₂ + 1 := le_self_add
      _ ≤ x + (s + t + 1 + y₂ + 1) := le_add_self
  have h := slack_depth_le a z [(x, y), (y₁, y₂), (s, t)] (by
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl
    · subst hz; exact le_self_add
    · subst hz; exact le_trans h1 le_self_add
    · subst hz; exact le_trans h2 le_self_add)
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons, List.length_nil,
    add_zero] at h
  push_cast at h ⊢
  exact le_trans (le_of_eq (by ring)) (le_trans h (le_of_eq (by ring)))

/-- Three-level elimination, the right conjunct's RIGHT part `y₂ = s + t + 1`. -/
lemma slack6_le' (a x y y₁ y₂ s t z : V) (hy : y = y₁ + y₂ + 1) (hs : y₂ = s + t + 1) (hz : z = x + y + 1) :
    a + 8 * (x + y) + 7 + 8 * (y₁ + y₂) + 7 + 8 * (s + t) + 7 ≤ a + ((21 : ℕ) : V) + ((24 : ℕ) : V) * z := by
  have h1 : y₁ + y₂ ≤ x + y := by subst hy; exact le_trans le_self_add le_add_self
  have h2 : s + t ≤ x + y := by
    subst hy hs
    calc s + t ≤ s + t + 1 := le_self_add
      _ ≤ y₁ + (s + t + 1) := le_add_self
      _ ≤ y₁ + (s + t + 1) + 1 := le_self_add
      _ ≤ x + (y₁ + (s + t + 1) + 1) := le_add_self
  have h := slack_depth_le a z [(x, y), (y₁, y₂), (s, t)] (by
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl
    · subst hz; exact le_self_add
    · subst hz; exact le_trans h1 le_self_add
    · subst hz; exact le_trans h2 le_self_add)
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons, List.length_nil,
    add_zero] at h
  push_cast at h ⊢
  exact le_trans (le_of_eq (by ring)) (le_trans h (le_of_eq (by ring)))

lemma slack6_nat₁ (a x y u v z k : ℕ) (hx : x = u + v + 1) (hz : z = x + y + 1) (h : a + 21 + 24 * z ≤ k) :
    a + 8 * (x + y) + 7 + 8 * (u + v) + 7 = k ∨ a + 8 * (x + y) + 7 + 8 * (u + v) + 7 < k := by
  have h1 := le_def.mp (slack6_le₁ (V := ℕ) a x y u v z hx hz)
  simp only [natCast_nat] at h1
  exact le_def_trans h1 (Nat.eq_or_lt_of_le h)

lemma slack6_nat (a x y y₁ y₂ s t z k : ℕ) (hy : y = y₁ + y₂ + 1) (hs : y₁ = s + t + 1) (hz : z = x + y + 1)
    (h : a + 21 + 24 * z ≤ k) :
    a + 8 * (x + y) + 7 + 8 * (y₁ + y₂) + 7 + 8 * (s + t) + 7 = k ∨
      a + 8 * (x + y) + 7 + 8 * (y₁ + y₂) + 7 + 8 * (s + t) + 7 < k := by
  have h1 := le_def.mp (slack6_le (V := ℕ) a x y y₁ y₂ s t z hy hs hz)
  simp only [natCast_nat] at h1
  exact le_def_trans h1 (Nat.eq_or_lt_of_le h)

lemma slack6_nat' (a x y y₁ y₂ s t z k : ℕ) (hy : y = y₁ + y₂ + 1) (hs : y₂ = s + t + 1) (hz : z = x + y + 1)
    (h : a + 21 + 24 * z ≤ k) :
    a + 8 * (x + y) + 7 + 8 * (y₁ + y₂) + 7 + 8 * (s + t) + 7 = k ∨
      a + 8 * (x + y) + 7 + 8 * (y₁ + y₂) + 7 + 8 * (s + t) + 7 < k := by
  have h1 := le_def.mp (slack6_le' (V := ℕ) a x y y₁ y₂ s t z hy hs hz)
  simp only [natCast_nat] at h1
  exact le_def_trans h1 (Nat.eq_or_lt_of_le h)

end slack

/-! ### 5. Cell 1 — Just × Just `(C, C)` -/

section selfCell

/-- **Just's guard against Just**: `qJJ(k)` says "`JustV7 k` plays C against `pBot (Dupoc k)`". -/
noncomputable def qJJ : Semisentence LAct 1 := qG 0 TBD uD wD TJ uJ wJ

lemma qJJ_def : qJJ = qG 0 TBD uD wD TJ uJ wJ := rfl

/-- **The instance equation on codes**: Just's guard code against `JustV7 k`. -/
theorem guardCode_botDupocV_JustV7_eq_instB (k : V) :
    guardCode (⌜guardTemplate 0⌝ : V) (pBot (DupocV k)) (JustV7 k) = instB (⌜qJJ⌝ : V) k :=
  guardCode_GtmplA_eq_instB 0 k TBD uD wD TJ uJ wJ (hX_botDupoc k) (hU_botDupoc k) (hW_botDupoc k) (hX_just7 k) (hU_just7 k)
    (hW_just7 k)

theorem guardCode_botCupodV_JustTV7_eq_instB (k : V) :
    guardCode (⌜guardTemplate 1⌝ : V) (pBot (CupodV k)) (JustTV7 k) = instB (⌜Semiformula.lMap swap qJJ⌝ : V) k := by
  have h := guardCode_GtmplA_swap_eq_instB 0 k TBD uD wD TJ uJ wJ (hX_botDupoc k) (hU_botDupoc k) (hW_botDupoc k) (hX_just7 k)
    (hU_just7 k) (hW_just7 k)
  rwa [swapAction_zero, transposeCode_pBot_DupocV, transposeCode_JustV7] at h

/-- **The truth equation of `qJJ`** (standard reading). -/
theorem eval_qJJ_iff_V (k : V) :
    Semiformula.Eval (s := stdReadingV V) ![k] Empty.elim qJJ ↔
      ∃ n, EvalGraph n (JustV7 k) (pBot (DupocV k)) (JustV7 k) 0 := by
  have h := eval_qG_iff_V 0 k TBD uD wD TJ uJ wJ (desc_botDupoc k) (desc_just7 k)
  rwa [Nat.cast_zero] at h

theorem eval_qJJ_swapped_iff_V (k : V) :
    Semiformula.Eval (s := stdReadingV V) ![k] Empty.elim (Semiformula.lMap swap qJJ) ↔
      ∃ n, EvalGraph n (JustTV7 k) (pBot (CupodV k)) (JustTV7 k) 1 := by
  rw [qJJ_def, lMap_swap_qG, swapAction_zero]
  have h := eval_qG_iff_V 1 k _ _ _ _ _ _ (descT_botDupoc k) (descT_just7 k)
  rwa [Nat.cast_one] at h

/-- The two-sided conjunct: Just's guard against Just and its transposition. -/
noncomputable def pJJ2 : Semisentence LAct 1 := qJJ ⋏ Semiformula.lMap swap qJJ

lemma pJJ2_def : pJJ2 = qJJ ⋏ Semiformula.lMap swap qJJ := rfl

lemma lMap_swap_pJJ2 : Semiformula.lMap swap pJJ2 = Semiformula.lMap swap qJJ ⋏ qJJ := by
  rw [pJJ2_def, LogicalConnective.HomClass.map_and, lMap_swap_swap]

/-- **The Löb family of the Just × Just cell**: Just's guard against Just (both readings) AND the
bot-wrapped self-play family `pBD`, whose boxes the truth of the former needs. -/
noncomputable def pJJ : Semisentence LAct 1 := pJJ2 ⋏ pBD

lemma pJJ_def : pJJ = pJJ2 ⋏ pBD := rfl

theorem instB_quote_pJJ2 (k : V) :
    instB (⌜pJJ2⌝ : V) k = instB (⌜qJJ⌝ : V) k ^⋏ instB (⌜Semiformula.lMap swap qJJ⌝ : V) k :=
  instB_quote_and _ _ k

theorem instB_quote_pJJ (k : V) :
    instB (⌜pJJ⌝ : V) k = instB (⌜pJJ2⌝ : V) k ^⋏ instB (⌜pBD⌝ : V) k :=
  instB_quote_and _ _ k

lemma formulaLen_instB_pJJ2 (k : V) :
    formulaLen LAct (instB (⌜pJJ2⌝ : V) k) =
      formulaLen LAct (instB (⌜qJJ⌝ : V) k) + formulaLen LAct (instB (⌜Semiformula.lMap swap qJJ⌝ : V) k) + 1 := by
  rw [instB_quote_pJJ2,
    formulaLen_and (isFormula_instB_quote _ k).isUFormula (isFormula_instB_quote _ k).isUFormula]

lemma formulaLen_instB_pJJ (k : V) :
    formulaLen LAct (instB (⌜pJJ⌝ : V) k) =
      formulaLen LAct (instB (⌜pJJ2⌝ : V) k) + formulaLen LAct (instB (⌜pBD⌝ : V) k) + 1 := by
  rw [instB_quote_pJJ,
    formulaLen_and (isFormula_instB_quote _ k).isUFormula (isFormula_instB_quote _ k).isUFormula]

/-- **Everything from a box of the family** (two-level ∧-elimination): Just cooperates with Just (and
the transposed searcher defects against itself), Just cooperates with `pBot (Dupoc k)` (the truth of
`qJJ`), and the bot-wrapped self-plays. -/
theorem pJJ_all_V (k a : V)
    (ha₁ : a + 8 * (formulaLen LAct (instB (⌜pJJ2⌝ : V) k) + formulaLen LAct (instB (⌜pBD⌝ : V) k)) + 7 +
      8 * (formulaLen LAct (instB (⌜qJJ⌝ : V) k) + formulaLen LAct (instB (⌜Semiformula.lMap swap qJJ⌝ : V) k))
      + 7 ≤ k)
    (ha₂ : a + 8 * (formulaLen LAct (instB (⌜pJJ2⌝ : V) k) + formulaLen LAct (instB (⌜pBD⌝ : V) k)) + 7 +
      8 * (formulaLen LAct (instB (⌜qBD⌝ : V) k) + formulaLen LAct (instB (⌜qBC⌝ : V) k)) + 7 ≤ k)
    (h : LenBoxUnbounded TAct a (instB (⌜pJJ⌝ : V) k)) :
    (EvalGraph 2 (JustV7 k) (JustV7 k) (JustV7 k) 0 ∧ EvalGraph 2 (JustTV7 k) (JustTV7 k) (JustTV7 k) 1) ∧
    (EvalGraph 2 (JustV7 k) (pBot (DupocV k)) (JustV7 k) 0 ∧ EvalGraph 2 (JustTV7 k) (pBot (CupodV k)) (JustTV7 k) 1) ∧
    (EvalGraph 3 (pBot (DupocV k)) (pBot (DupocV k)) (pBot (DupocV k)) 0 ∧
      EvalGraph 3 (pBot (CupodV k)) (pBot (CupodV k)) (pBot (CupodV k)) 1) := by
  rw [instB_quote_pJJ] at h
  have hx := isFormula_instB_quote pJJ2 k
  have hy := isFormula_instB_quote pBD k
  have h₁ := lenBoxUnbounded_andL_V hx hy h
  have h₂ := lenBoxUnbounded_andR_V hx hy h
  have hx' := isFormula_instB_quote qJJ k
  have hy' := isFormula_instB_quote (Semiformula.lMap swap qJJ) k
  have h₁' : LenBoxUnbounded TAct
      (a + 8 * (formulaLen LAct (instB (⌜pJJ2⌝ : V) k) + formulaLen LAct (instB (⌜pBD⌝ : V) k)) + 7)
      (instB (⌜qJJ⌝ : V) k ^⋏ instB (⌜Semiformula.lMap swap qJJ⌝ : V) k) := by
    rw [← instB_quote_pJJ2]; exact h₁
  have c1 := lenBoxUnbounded_mono_V ha₁ (lenBoxUnbounded_andL_V hx' hy' h₁')
  have c2 := lenBoxUnbounded_mono_V ha₁ (lenBoxUnbounded_andR_V hx' hy' h₁')
  rw [lenBoxUnbounded_iff_lenBox, ← guardCode_botDupocV_JustV7_eq_instB] at c1
  rw [lenBoxUnbounded_iff_lenBox, ← guardCode_botCupodV_JustTV7_eq_instB] at c2
  have hb := pBD_both_V k _ ha₂ h₂
  have hg := pBD_guards_V k _ ha₂ h₂
  exact ⟨⟨just7_search_V k _ _ c1, just7T_search_V k _ _ c2⟩,
    ⟨just7_search_V k _ _ hg.1, just7T_search_V k _ _ hg.2⟩, hb⟩

/-- **The box form**: Just's guard against Just is provable within `k`. -/
theorem pJJ_guards_V (k a : V)
    (ha₁ : a + 8 * (formulaLen LAct (instB (⌜pJJ2⌝ : V) k) + formulaLen LAct (instB (⌜pBD⌝ : V) k)) + 7 +
      8 * (formulaLen LAct (instB (⌜qJJ⌝ : V) k) + formulaLen LAct (instB (⌜Semiformula.lMap swap qJJ⌝ : V) k))
      + 7 ≤ k)
    (h : LenBoxUnbounded TAct a (instB (⌜pJJ⌝ : V) k)) :
    LenBox TAct k (guardCode (⌜guardTemplate 0⌝ : V) (pBot (DupocV k)) (JustV7 k)) := by
  rw [instB_quote_pJJ] at h
  have hx := isFormula_instB_quote pJJ2 k
  have hy := isFormula_instB_quote pBD k
  have h₁ := lenBoxUnbounded_andL_V hx hy h
  have hx' := isFormula_instB_quote qJJ k
  have hy' := isFormula_instB_quote (Semiformula.lMap swap qJJ) k
  have h₁' : LenBoxUnbounded TAct
      (a + 8 * (formulaLen LAct (instB (⌜pJJ2⌝ : V) k) + formulaLen LAct (instB (⌜pBD⌝ : V) k)) + 7)
      (instB (⌜qJJ⌝ : V) k ^⋏ instB (⌜Semiformula.lMap swap qJJ⌝ : V) k) := by
    rw [← instB_quote_pJJ2]; exact h₁
  have c1 := lenBoxUnbounded_mono_V ha₁ (lenBoxUnbounded_andL_V hx' hy' h₁')
  rwa [lenBoxUnbounded_iff_lenBox, ← guardCode_botDupocV_JustV7_eq_instB] at c1

/-! #### `pJJ` in both readings -/

theorem eval_pJJ_iff_std (k : V) :
    Semiformula.Eval (s := stdReadingV V) ![k] Empty.elim pJJ ↔
      ((∃ n, EvalGraph n (JustV7 k) (pBot (DupocV k)) (JustV7 k) 0) ∧
        (∃ n, EvalGraph n (JustTV7 k) (pBot (CupodV k)) (JustTV7 k) 1)) ∧
      ((∃ n, EvalGraph n (pBot (DupocV k)) (pBot (DupocV k)) (pBot (DupocV k)) 0) ∧
        (∃ n, EvalGraph n (pBot (CupodV k)) (pBot (CupodV k)) (pBot (CupodV k)) 1)) := by
  rw [pJJ_def, pJJ2_def, pBD_def]
  simp only [LogicalConnective.HomClass.map_and, LogicalConnective.Prop.and_eq]
  rw [eval_qJJ_iff_V, eval_qJJ_swapped_iff_V, eval_qBD_iff_V, eval_qBC_iff_V]

theorem eval_pJJ_iff_swap (k : V) :
    Semiformula.Eval (s := swappedReading V) ![k] Empty.elim pJJ ↔
      ((∃ n, EvalGraph n (JustV7 k) (pBot (DupocV k)) (JustV7 k) 0) ∧
        (∃ n, EvalGraph n (JustTV7 k) (pBot (CupodV k)) (JustTV7 k) 1)) ∧
      ((∃ n, EvalGraph n (pBot (DupocV k)) (pBot (DupocV k)) (pBot (DupocV k)) 0) ∧
        (∃ n, EvalGraph n (pBot (CupodV k)) (pBot (CupodV k)) (pBot (CupodV k)) 1)) := by
  rw [eval_swappedReading, pJJ_def, LogicalConnective.HomClass.map_and, lMap_swap_pJJ2, lMap_swap_pBD,
    ← stdReadingV_eq_stdReading]
  simp only [LogicalConnective.HomClass.map_and, LogicalConnective.Prop.and_eq]
  rw [eval_qJJ_swapped_iff_V, eval_qJJ_iff_V, eval_qBC_iff_V, eval_qBD_iff_V,
    and_comm (a := ∃ n, EvalGraph n (JustTV7 k) (pBot (CupodV k)) (JustTV7 k) 1),
    and_comm (a := ∃ n, EvalGraph n (pBot (CupodV k)) (pBot (CupodV k)) (pBot (CupodV k)) 1)]

theorem eval_pJJ_iff_stdReading (k : V) :
    Semiformula.Eval (s := stdReading V) ![k] Empty.elim pJJ ↔
      ((∃ n, EvalGraph n (JustV7 k) (pBot (DupocV k)) (JustV7 k) 0) ∧
        (∃ n, EvalGraph n (JustTV7 k) (pBot (CupodV k)) (JustTV7 k) 1)) ∧
      ((∃ n, EvalGraph n (pBot (DupocV k)) (pBot (DupocV k)) (pBot (DupocV k)) 0) ∧
        (∃ n, EvalGraph n (pBot (CupodV k)) (pBot (CupodV k)) (pBot (CupodV k)) 1)) := by
  rw [← stdReadingV_eq_stdReading]; exact eval_pJJ_iff_std k

/-- **The bounded Löb premise of the Just × Just family, slack `(14, 16)`.** -/
theorem loebSound_pJJ : LoebSound pJJ 14 16 := by
  intro V _ _ k a ha h
  have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
  have ha₁ := le_trans (slack4_le a _ _ _ _ _ (formulaLen_instB_pJJ2 k) (formulaLen_instB_pJJ k)) ha
  have ha₂ := le_trans (slack4_le' a _ _ _ _ _ (formulaLen_instB_pBD k) (formulaLen_instB_pJJ k)) ha
  obtain ⟨_, ⟨j1, j2⟩, ⟨b1, b2⟩⟩ := pJJ_all_V k a ha₁ ha₂ h
  exact ⟨(eval_pJJ_iff_stdReading k).mpr ⟨⟨⟨2, j1⟩, ⟨2, j2⟩⟩, ⟨⟨3, b1⟩, ⟨3, b2⟩⟩⟩,
    (eval_pJJ_iff_swap k).mpr ⟨⟨⟨2, j1⟩, ⟨2, j2⟩⟩, ⟨⟨3, b1⟩, ⟨3, b2⟩⟩⟩⟩

/-! #### The cell at ℕ -/

/-- **The Just × Just cell, packaged**: for all large `k`, `Just7 k` cooperates with itself (fuel 2)
and finds its guard against itself. -/
theorem loeb_Just7_vs_Just7_core_of_nec {d : ℕ} (hE : BoundedInnerNec d) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 2 (Just7 k) (Just7 k) (Just7 k) 0 ∧
      LenBox TAct k (guardCode (⌜guardTemplate 0⌝ : ℕ) (pBot (Dupoc k)) (Just7 k)) := by
  obtain ⟨k₀, h⟩ := family_found pJJ hE loebSound_pJJ
  refine ⟨k₀, fun k hk ↦ ?_⟩
  obtain ⟨a, ha, hpc⟩ := h k hk
  have ha₁ := le_def.mpr (slack4_nat a _ _ _ _ _ k (formulaLen_instB_pJJ2 (V := ℕ) k)
    (formulaLen_instB_pJJ (V := ℕ) k) ha)
  have ha₂ := le_def.mpr (slack4_nat' a _ _ _ _ _ k (formulaLen_instB_pBD (V := ℕ) k)
    (formulaLen_instB_pJJ (V := ℕ) k) ha)
  exact ⟨(pJJ_all_V (V := ℕ) k a ha₁ ha₂ hpc).1.1, pJJ_guards_V (V := ℕ) k a ha₁ hpc⟩

/-- **Just × Just is `(C, C)` in PA-`S'`, conditional on bounded inner necessitation** (fuel 2). -/
theorem loeb_Just7_vs_Just7_of_nec {d : ℕ} (hE : BoundedInnerNec d) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k → EvalGraph 2 (Just7 k) (Just7 k) (Just7 k) 0 := by
  obtain ⟨k₀, h⟩ := loeb_Just7_vs_Just7_core_of_nec hE
  exact ⟨k₀, fun k hk ↦ (h k hk).1⟩

/-- **Just × Just `(C, C)` in PA-`S'`, unconditional**: for all large `k`, `Just7 k` cooperates with
itself at fuel 2 — the engine's `outcome_JustBot_vs_JustBot`. -/
theorem loeb_Just7_vs_Just7 :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k → EvalGraph 2 (Just7 k) (Just7 k) (Just7 k) 0 :=
  loeb_Just7_vs_Just7_of_nec boundedInnerNec_sixteen

/-- **The box form, unconditional**: Just FINDS its guard against itself within its budget — stated
with the node-budget guard code of the constant template. -/
theorem loeb_Just7_vs_Just7_guard :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k → LenBox TAct k (guardCodeB (⌜guardTemplateJust7⌝ : ℕ) (Just7 k) (Just7 k) k) := by
  obtain ⟨k₀, h⟩ := loeb_Just7_vs_Just7_core_of_nec boundedInnerNec_sixteen
  refine ⟨k₀, fun k hk ↦ ?_⟩
  rw [guardCodeB_guardTemplateJust7]
  exact (h k hk).2

end selfCell

/-! ### 6. Cell 2 — Just × Dupoc `(C, C)`, the three-guard mutual family -/

section dupocCell

/-- **Just's guard against Dupoc**: "`DupocV k` plays C against `pBot (Dupoc k)`". -/
noncomputable def qJD : Semisentence LAct 1 := qG 0 TBD uD wD TD uD wD
/-- **Dupoc's guard against `pBot (Dupoc k)`**: "`pBot (Dupoc k)` plays C against `DupocV k`". -/
noncomputable def qBDD : Semisentence LAct 1 := qG 0 TD uD wD TBD uD wD
/-- **Dupoc's guard against Just**: "`JustV7 k` plays C against `DupocV k`". -/
noncomputable def qDJ : Semisentence LAct 1 := qG 0 TD uD wD TJ uJ wJ

lemma qJD_def : qJD = qG 0 TBD uD wD TD uD wD := rfl
lemma qBDD_def : qBDD = qG 0 TD uD wD TBD uD wD := rfl
lemma qDJ_def : qDJ = qG 0 TD uD wD TJ uJ wJ := rfl

/-! #### The instance equations on codes -/

theorem guardCode_botDupocV_DupocV_eq_instB (k : V) :
    guardCode (⌜guardTemplate 0⌝ : V) (pBot (DupocV k)) (DupocV k) = instB (⌜qJD⌝ : V) k :=
  guardCode_GtmplA_eq_instB 0 k TBD uD wD TD uD wD (hX_botDupoc k) (hU_botDupoc k) (hW_botDupoc k) (hX_dupoc k) (hU_dupoc k)
    (hW_dupoc k)

theorem guardCode_botCupodV_CupodV_eq_instB (k : V) :
    guardCode (⌜guardTemplate 1⌝ : V) (pBot (CupodV k)) (CupodV k) = instB (⌜Semiformula.lMap swap qJD⌝ : V) k := by
  have h := guardCode_GtmplA_swap_eq_instB 0 k TBD uD wD TD uD wD (hX_botDupoc k) (hU_botDupoc k) (hW_botDupoc k) (hX_dupoc k)
    (hU_dupoc k) (hW_dupoc k)
  rwa [swapAction_zero, transposeCode_pBot_DupocV, transposeCode_DupocV] at h

theorem guardCode_DupocV_botDupocV_eq_instB (k : V) :
    guardCode (⌜guardTemplate 0⌝ : V) (DupocV k) (pBot (DupocV k)) = instB (⌜qBDD⌝ : V) k :=
  guardCode_GtmplA_eq_instB 0 k TD uD wD TBD uD wD (hX_dupoc k) (hU_dupoc k) (hW_dupoc k) (hX_botDupoc k) (hU_botDupoc k)
    (hW_botDupoc k)

theorem guardCode_CupodV_botCupodV_eq_instB (k : V) :
    guardCode (⌜guardTemplate 1⌝ : V) (CupodV k) (pBot (CupodV k)) = instB (⌜Semiformula.lMap swap qBDD⌝ : V) k := by
  have h := guardCode_GtmplA_swap_eq_instB 0 k TD uD wD TBD uD wD (hX_dupoc k) (hU_dupoc k) (hW_dupoc k) (hX_botDupoc k)
    (hU_botDupoc k) (hW_botDupoc k)
  rwa [swapAction_zero, transposeCode_pBot_DupocV, transposeCode_DupocV] at h

theorem guardCode_DupocV_JustV7_eq_instB (k : V) :
    guardCode (⌜guardTemplate 0⌝ : V) (DupocV k) (JustV7 k) = instB (⌜qDJ⌝ : V) k :=
  guardCode_GtmplA_eq_instB 0 k TD uD wD TJ uJ wJ (hX_dupoc k) (hU_dupoc k) (hW_dupoc k) (hX_just7 k) (hU_just7 k)
    (hW_just7 k)

theorem guardCode_CupodV_JustTV7_eq_instB (k : V) :
    guardCode (⌜guardTemplate 1⌝ : V) (CupodV k) (JustTV7 k) = instB (⌜Semiformula.lMap swap qDJ⌝ : V) k := by
  have h := guardCode_GtmplA_swap_eq_instB 0 k TD uD wD TJ uJ wJ (hX_dupoc k) (hU_dupoc k) (hW_dupoc k) (hX_just7 k)
    (hU_just7 k) (hW_just7 k)
  rwa [swapAction_zero, transposeCode_DupocV, transposeCode_JustV7] at h

/-! #### The truth equations -/

theorem eval_qJD_iff_V (k : V) :
    Semiformula.Eval (s := stdReadingV V) ![k] Empty.elim qJD ↔
      ∃ n, EvalGraph n (DupocV k) (pBot (DupocV k)) (DupocV k) 0 := by
  have h := eval_qG_iff_V 0 k TBD uD wD TD uD wD (desc_botDupoc k) (desc_dupoc k)
  rwa [Nat.cast_zero] at h

theorem eval_qJD_swapped_iff_V (k : V) :
    Semiformula.Eval (s := stdReadingV V) ![k] Empty.elim (Semiformula.lMap swap qJD) ↔
      ∃ n, EvalGraph n (CupodV k) (pBot (CupodV k)) (CupodV k) 1 := by
  rw [qJD_def, lMap_swap_qG, swapAction_zero]
  have h := eval_qG_iff_V 1 k _ _ _ _ _ _ (descT_botDupoc k) (descT_dupoc k)
  rwa [Nat.cast_one] at h

theorem eval_qBDD_iff_V (k : V) :
    Semiformula.Eval (s := stdReadingV V) ![k] Empty.elim qBDD ↔
      ∃ n, EvalGraph n (pBot (DupocV k)) (DupocV k) (pBot (DupocV k)) 0 := by
  have h := eval_qG_iff_V 0 k TD uD wD TBD uD wD (desc_dupoc k) (desc_botDupoc k)
  rwa [Nat.cast_zero] at h

theorem eval_qBDD_swapped_iff_V (k : V) :
    Semiformula.Eval (s := stdReadingV V) ![k] Empty.elim (Semiformula.lMap swap qBDD) ↔
      ∃ n, EvalGraph n (pBot (CupodV k)) (CupodV k) (pBot (CupodV k)) 1 := by
  rw [qBDD_def, lMap_swap_qG, swapAction_zero]
  have h := eval_qG_iff_V 1 k _ _ _ _ _ _ (descT_dupoc k) (descT_botDupoc k)
  rwa [Nat.cast_one] at h

theorem eval_qDJ_iff_V (k : V) :
    Semiformula.Eval (s := stdReadingV V) ![k] Empty.elim qDJ ↔
      ∃ n, EvalGraph n (JustV7 k) (DupocV k) (JustV7 k) 0 := by
  have h := eval_qG_iff_V 0 k TD uD wD TJ uJ wJ (desc_dupoc k) (desc_just7 k)
  rwa [Nat.cast_zero] at h

theorem eval_qDJ_swapped_iff_V (k : V) :
    Semiformula.Eval (s := stdReadingV V) ![k] Empty.elim (Semiformula.lMap swap qDJ) ↔
      ∃ n, EvalGraph n (JustTV7 k) (CupodV k) (JustTV7 k) 1 := by
  rw [qDJ_def, lMap_swap_qG, swapAction_zero]
  have h := eval_qG_iff_V 1 k _ _ _ _ _ _ (descT_dupoc k) (descT_just7 k)
  rwa [Nat.cast_one] at h

/-! #### The mutual family -/

/-- The three two-sided conjuncts and the family `pJD := pJD2 ⋏ (pBDD2 ⋏ pDJ2)`. -/
noncomputable def pJD2 : Semisentence LAct 1 := qJD ⋏ Semiformula.lMap swap qJD
noncomputable def pBDD2 : Semisentence LAct 1 := qBDD ⋏ Semiformula.lMap swap qBDD
noncomputable def pDJ2 : Semisentence LAct 1 := qDJ ⋏ Semiformula.lMap swap qDJ
noncomputable def pJDR : Semisentence LAct 1 := pBDD2 ⋏ pDJ2
noncomputable def pJD : Semisentence LAct 1 := pJD2 ⋏ pJDR

lemma pJD2_def : pJD2 = qJD ⋏ Semiformula.lMap swap qJD := rfl
lemma pBDD2_def : pBDD2 = qBDD ⋏ Semiformula.lMap swap qBDD := rfl
lemma pDJ2_def : pDJ2 = qDJ ⋏ Semiformula.lMap swap qDJ := rfl
lemma pJDR_def : pJDR = pBDD2 ⋏ pDJ2 := rfl
lemma pJD_def : pJD = pJD2 ⋏ pJDR := rfl

lemma lMap_swap_pJD2 : Semiformula.lMap swap pJD2 = Semiformula.lMap swap qJD ⋏ qJD := by
  rw [pJD2_def, LogicalConnective.HomClass.map_and, lMap_swap_swap]
lemma lMap_swap_pBDD2 : Semiformula.lMap swap pBDD2 = Semiformula.lMap swap qBDD ⋏ qBDD := by
  rw [pBDD2_def, LogicalConnective.HomClass.map_and, lMap_swap_swap]
lemma lMap_swap_pDJ2 : Semiformula.lMap swap pDJ2 = Semiformula.lMap swap qDJ ⋏ qDJ := by
  rw [pDJ2_def, LogicalConnective.HomClass.map_and, lMap_swap_swap]

theorem instB_quote_pJD2 (k : V) :
    instB (⌜pJD2⌝ : V) k = instB (⌜qJD⌝ : V) k ^⋏ instB (⌜Semiformula.lMap swap qJD⌝ : V) k :=
  instB_quote_and _ _ k
theorem instB_quote_pBDD2 (k : V) :
    instB (⌜pBDD2⌝ : V) k = instB (⌜qBDD⌝ : V) k ^⋏ instB (⌜Semiformula.lMap swap qBDD⌝ : V) k :=
  instB_quote_and _ _ k
theorem instB_quote_pDJ2 (k : V) :
    instB (⌜pDJ2⌝ : V) k = instB (⌜qDJ⌝ : V) k ^⋏ instB (⌜Semiformula.lMap swap qDJ⌝ : V) k :=
  instB_quote_and _ _ k
theorem instB_quote_pJDR (k : V) :
    instB (⌜pJDR⌝ : V) k = instB (⌜pBDD2⌝ : V) k ^⋏ instB (⌜pDJ2⌝ : V) k :=
  instB_quote_and _ _ k
theorem instB_quote_pJD (k : V) :
    instB (⌜pJD⌝ : V) k = instB (⌜pJD2⌝ : V) k ^⋏ instB (⌜pJDR⌝ : V) k :=
  instB_quote_and _ _ k

lemma formulaLen_instB_pJD2 (k : V) :
    formulaLen LAct (instB (⌜pJD2⌝ : V) k) =
      formulaLen LAct (instB (⌜qJD⌝ : V) k) + formulaLen LAct (instB (⌜Semiformula.lMap swap qJD⌝ : V) k) + 1 := by
  rw [instB_quote_pJD2, formulaLen_and (isFormula_instB_quote _ k).isUFormula (isFormula_instB_quote _ k).isUFormula]
lemma formulaLen_instB_pBDD2 (k : V) :
    formulaLen LAct (instB (⌜pBDD2⌝ : V) k) =
      formulaLen LAct (instB (⌜qBDD⌝ : V) k) + formulaLen LAct (instB (⌜Semiformula.lMap swap qBDD⌝ : V) k) + 1 := by
  rw [instB_quote_pBDD2, formulaLen_and (isFormula_instB_quote _ k).isUFormula (isFormula_instB_quote _ k).isUFormula]
lemma formulaLen_instB_pDJ2 (k : V) :
    formulaLen LAct (instB (⌜pDJ2⌝ : V) k) =
      formulaLen LAct (instB (⌜qDJ⌝ : V) k) + formulaLen LAct (instB (⌜Semiformula.lMap swap qDJ⌝ : V) k) + 1 := by
  rw [instB_quote_pDJ2, formulaLen_and (isFormula_instB_quote _ k).isUFormula (isFormula_instB_quote _ k).isUFormula]
lemma formulaLen_instB_pJDR (k : V) :
    formulaLen LAct (instB (⌜pJDR⌝ : V) k) =
      formulaLen LAct (instB (⌜pBDD2⌝ : V) k) + formulaLen LAct (instB (⌜pDJ2⌝ : V) k) + 1 := by
  rw [instB_quote_pJDR, formulaLen_and (isFormula_instB_quote _ k).isUFormula (isFormula_instB_quote _ k).isUFormula]
lemma formulaLen_instB_pJD (k : V) :
    formulaLen LAct (instB (⌜pJD⌝ : V) k) =
      formulaLen LAct (instB (⌜pJD2⌝ : V) k) + formulaLen LAct (instB (⌜pJDR⌝ : V) k) + 1 := by
  rw [instB_quote_pJD, formulaLen_and (isFormula_instB_quote _ k).isUFormula (isFormula_instB_quote _ k).isUFormula]

/-- **The six guard boxes from a box of the family** (three-level ∧-elimination). -/
theorem pJD_guards_V (k a : V)
    (ha₁ : a + 8 * (formulaLen LAct (instB (⌜pJD2⌝ : V) k) + formulaLen LAct (instB (⌜pJDR⌝ : V) k)) + 7 +
      8 * (formulaLen LAct (instB (⌜qJD⌝ : V) k) + formulaLen LAct (instB (⌜Semiformula.lMap swap qJD⌝ : V) k))
      + 7 ≤ k)
    (ha₂ : a + 8 * (formulaLen LAct (instB (⌜pJD2⌝ : V) k) + formulaLen LAct (instB (⌜pJDR⌝ : V) k)) + 7 +
      8 * (formulaLen LAct (instB (⌜pBDD2⌝ : V) k) + formulaLen LAct (instB (⌜pDJ2⌝ : V) k)) + 7 +
      8 * (formulaLen LAct (instB (⌜qBDD⌝ : V) k) + formulaLen LAct (instB (⌜Semiformula.lMap swap qBDD⌝ : V) k))
      + 7 ≤ k)
    (ha₃ : a + 8 * (formulaLen LAct (instB (⌜pJD2⌝ : V) k) + formulaLen LAct (instB (⌜pJDR⌝ : V) k)) + 7 +
      8 * (formulaLen LAct (instB (⌜pBDD2⌝ : V) k) + formulaLen LAct (instB (⌜pDJ2⌝ : V) k)) + 7 +
      8 * (formulaLen LAct (instB (⌜qDJ⌝ : V) k) + formulaLen LAct (instB (⌜Semiformula.lMap swap qDJ⌝ : V) k))
      + 7 ≤ k)
    (h : LenBoxUnbounded TAct a (instB (⌜pJD⌝ : V) k)) :
    (LenBox TAct k (guardCode (⌜guardTemplate 0⌝ : V) (pBot (DupocV k)) (DupocV k)) ∧
      LenBox TAct k (guardCode (⌜guardTemplate 1⌝ : V) (pBot (CupodV k)) (CupodV k))) ∧
    (LenBox TAct k (guardCode (⌜guardTemplate 0⌝ : V) (DupocV k) (pBot (DupocV k))) ∧
      LenBox TAct k (guardCode (⌜guardTemplate 1⌝ : V) (CupodV k) (pBot (CupodV k)))) ∧
    (LenBox TAct k (guardCode (⌜guardTemplate 0⌝ : V) (DupocV k) (JustV7 k)) ∧
      LenBox TAct k (guardCode (⌜guardTemplate 1⌝ : V) (CupodV k) (JustTV7 k))) := by
  rw [instB_quote_pJD] at h
  have hx := isFormula_instB_quote pJD2 k
  have hy := isFormula_instB_quote pJDR k
  have h₁ := lenBoxUnbounded_andL_V hx hy h
  have h₂ := lenBoxUnbounded_andR_V hx hy h
  -- level 2, left
  have hx₁ := isFormula_instB_quote qJD k
  have hy₁ := isFormula_instB_quote (Semiformula.lMap swap qJD) k
  have h₁' : LenBoxUnbounded TAct
      (a + 8 * (formulaLen LAct (instB (⌜pJD2⌝ : V) k) + formulaLen LAct (instB (⌜pJDR⌝ : V) k)) + 7)
      (instB (⌜qJD⌝ : V) k ^⋏ instB (⌜Semiformula.lMap swap qJD⌝ : V) k) := by
    rw [← instB_quote_pJD2]; exact h₁
  have c1 := lenBoxUnbounded_mono_V ha₁ (lenBoxUnbounded_andL_V hx₁ hy₁ h₁')
  have c1' := lenBoxUnbounded_mono_V ha₁ (lenBoxUnbounded_andR_V hx₁ hy₁ h₁')
  -- level 2, right
  have hx₂ := isFormula_instB_quote pBDD2 k
  have hy₂ := isFormula_instB_quote pDJ2 k
  have h₂' : LenBoxUnbounded TAct
      (a + 8 * (formulaLen LAct (instB (⌜pJD2⌝ : V) k) + formulaLen LAct (instB (⌜pJDR⌝ : V) k)) + 7)
      (instB (⌜pBDD2⌝ : V) k ^⋏ instB (⌜pDJ2⌝ : V) k) := by
    rw [← instB_quote_pJDR]; exact h₂
  have h₂₁ := lenBoxUnbounded_andL_V hx₂ hy₂ h₂'
  have h₂₂ := lenBoxUnbounded_andR_V hx₂ hy₂ h₂'
  -- level 3
  have hx₃ := isFormula_instB_quote qBDD k
  have hy₃ := isFormula_instB_quote (Semiformula.lMap swap qBDD) k
  have h₂₁' : LenBoxUnbounded TAct
      (a + 8 * (formulaLen LAct (instB (⌜pJD2⌝ : V) k) + formulaLen LAct (instB (⌜pJDR⌝ : V) k)) + 7 +
        8 * (formulaLen LAct (instB (⌜pBDD2⌝ : V) k) + formulaLen LAct (instB (⌜pDJ2⌝ : V) k)) + 7)
      (instB (⌜qBDD⌝ : V) k ^⋏ instB (⌜Semiformula.lMap swap qBDD⌝ : V) k) := by
    rw [← instB_quote_pBDD2]; exact h₂₁
  have c2 := lenBoxUnbounded_mono_V ha₂ (lenBoxUnbounded_andL_V hx₃ hy₃ h₂₁')
  have c2' := lenBoxUnbounded_mono_V ha₂ (lenBoxUnbounded_andR_V hx₃ hy₃ h₂₁')
  have hx₄ := isFormula_instB_quote qDJ k
  have hy₄ := isFormula_instB_quote (Semiformula.lMap swap qDJ) k
  have h₂₂' : LenBoxUnbounded TAct
      (a + 8 * (formulaLen LAct (instB (⌜pJD2⌝ : V) k) + formulaLen LAct (instB (⌜pJDR⌝ : V) k)) + 7 +
        8 * (formulaLen LAct (instB (⌜pBDD2⌝ : V) k) + formulaLen LAct (instB (⌜pDJ2⌝ : V) k)) + 7)
      (instB (⌜qDJ⌝ : V) k ^⋏ instB (⌜Semiformula.lMap swap qDJ⌝ : V) k) := by
    rw [← instB_quote_pDJ2]; exact h₂₂
  have c3 := lenBoxUnbounded_mono_V ha₃ (lenBoxUnbounded_andL_V hx₄ hy₄ h₂₂')
  have c3' := lenBoxUnbounded_mono_V ha₃ (lenBoxUnbounded_andR_V hx₄ hy₄ h₂₂')
  rw [lenBoxUnbounded_iff_lenBox, ← guardCode_botDupocV_DupocV_eq_instB] at c1
  rw [lenBoxUnbounded_iff_lenBox, ← guardCode_botCupodV_CupodV_eq_instB] at c1'
  rw [lenBoxUnbounded_iff_lenBox, ← guardCode_DupocV_botDupocV_eq_instB] at c2
  rw [lenBoxUnbounded_iff_lenBox, ← guardCode_CupodV_botCupodV_eq_instB] at c2'
  rw [lenBoxUnbounded_iff_lenBox, ← guardCode_DupocV_JustV7_eq_instB] at c3
  rw [lenBoxUnbounded_iff_lenBox, ← guardCode_CupodV_JustTV7_eq_instB] at c3'
  exact ⟨⟨c1, c1'⟩, ⟨c2, c2'⟩, ⟨c3, c3'⟩⟩

/-- **All the plays from the six boxes.** -/
theorem pJD_all_V (k : V)
    (hb : (LenBox TAct k (guardCode (⌜guardTemplate 0⌝ : V) (pBot (DupocV k)) (DupocV k)) ∧
      LenBox TAct k (guardCode (⌜guardTemplate 1⌝ : V) (pBot (CupodV k)) (CupodV k))) ∧
    (LenBox TAct k (guardCode (⌜guardTemplate 0⌝ : V) (DupocV k) (pBot (DupocV k))) ∧
      LenBox TAct k (guardCode (⌜guardTemplate 1⌝ : V) (CupodV k) (pBot (CupodV k)))) ∧
    (LenBox TAct k (guardCode (⌜guardTemplate 0⌝ : V) (DupocV k) (JustV7 k)) ∧
      LenBox TAct k (guardCode (⌜guardTemplate 1⌝ : V) (CupodV k) (JustTV7 k)))) :
    (EvalGraph 2 (JustV7 k) (DupocV k) (JustV7 k) 0 ∧ EvalGraph 2 (JustTV7 k) (CupodV k) (JustTV7 k) 1) ∧
    (EvalGraph 2 (DupocV k) (JustV7 k) (DupocV k) 0 ∧ EvalGraph 2 (CupodV k) (JustTV7 k) (CupodV k) 1) ∧
    (EvalGraph 2 (DupocV k) (pBot (DupocV k)) (DupocV k) 0 ∧ EvalGraph 2 (CupodV k) (pBot (CupodV k)) (CupodV k) 1) ∧
    (EvalGraph 3 (pBot (DupocV k)) (DupocV k) (pBot (DupocV k)) 0 ∧
      EvalGraph 3 (pBot (CupodV k)) (CupodV k) (pBot (CupodV k)) 1) := by
  obtain ⟨⟨c1, c1'⟩, ⟨c2, c2'⟩, ⟨c3, c3'⟩⟩ := hb
  exact ⟨⟨just7_search_V k _ _ c1, just7T_search_V k _ _ c1'⟩,
    ⟨dupoc_search_any_V k _ c3, cupod_search_any_V k _ c3'⟩,
    ⟨dupoc_search_any_V k _ c2, cupod_search_any_V k _ c2'⟩,
    ⟨botDupoc_frame_search_V k _ _ c1, botCupod_frame_search_V k _ _ c1'⟩⟩

/-! #### `pJD` in both readings -/

theorem eval_pJD_iff_std (k : V) :
    Semiformula.Eval (s := stdReadingV V) ![k] Empty.elim pJD ↔
      ((∃ n, EvalGraph n (DupocV k) (pBot (DupocV k)) (DupocV k) 0) ∧
        (∃ n, EvalGraph n (CupodV k) (pBot (CupodV k)) (CupodV k) 1)) ∧
      ((∃ n, EvalGraph n (pBot (DupocV k)) (DupocV k) (pBot (DupocV k)) 0) ∧
        (∃ n, EvalGraph n (pBot (CupodV k)) (CupodV k) (pBot (CupodV k)) 1)) ∧
      ((∃ n, EvalGraph n (JustV7 k) (DupocV k) (JustV7 k) 0) ∧
        (∃ n, EvalGraph n (JustTV7 k) (CupodV k) (JustTV7 k) 1)) := by
  rw [pJD_def, pJDR_def, pJD2_def, pBDD2_def, pDJ2_def]
  simp only [LogicalConnective.HomClass.map_and, LogicalConnective.Prop.and_eq]
  rw [eval_qJD_iff_V, eval_qJD_swapped_iff_V, eval_qBDD_iff_V, eval_qBDD_swapped_iff_V, eval_qDJ_iff_V,
    eval_qDJ_swapped_iff_V]

theorem eval_pJD_iff_swap (k : V) :
    Semiformula.Eval (s := swappedReading V) ![k] Empty.elim pJD ↔
      ((∃ n, EvalGraph n (DupocV k) (pBot (DupocV k)) (DupocV k) 0) ∧
        (∃ n, EvalGraph n (CupodV k) (pBot (CupodV k)) (CupodV k) 1)) ∧
      ((∃ n, EvalGraph n (pBot (DupocV k)) (DupocV k) (pBot (DupocV k)) 0) ∧
        (∃ n, EvalGraph n (pBot (CupodV k)) (CupodV k) (pBot (CupodV k)) 1)) ∧
      ((∃ n, EvalGraph n (JustV7 k) (DupocV k) (JustV7 k) 0) ∧
        (∃ n, EvalGraph n (JustTV7 k) (CupodV k) (JustTV7 k) 1)) := by
  rw [eval_swappedReading, pJD_def, pJDR_def, pJD2_def, pBDD2_def, pDJ2_def, ← stdReadingV_eq_stdReading]
  simp only [LogicalConnective.HomClass.map_and, lMap_swap_swap, LogicalConnective.Prop.and_eq]
  rw [eval_qJD_iff_V, eval_qJD_swapped_iff_V, eval_qBDD_iff_V, eval_qBDD_swapped_iff_V, eval_qDJ_iff_V,
    eval_qDJ_swapped_iff_V]
  constructor
  · rintro ⟨⟨a, b⟩, ⟨c, d⟩, ⟨e, f⟩⟩; exact ⟨⟨b, a⟩, ⟨d, c⟩, ⟨f, e⟩⟩
  · rintro ⟨⟨a, b⟩, ⟨c, d⟩, ⟨e, f⟩⟩; exact ⟨⟨b, a⟩, ⟨d, c⟩, ⟨f, e⟩⟩

theorem eval_pJD_iff_stdReading (k : V) :
    Semiformula.Eval (s := stdReading V) ![k] Empty.elim pJD ↔
      ((∃ n, EvalGraph n (DupocV k) (pBot (DupocV k)) (DupocV k) 0) ∧
        (∃ n, EvalGraph n (CupodV k) (pBot (CupodV k)) (CupodV k) 1)) ∧
      ((∃ n, EvalGraph n (pBot (DupocV k)) (DupocV k) (pBot (DupocV k)) 0) ∧
        (∃ n, EvalGraph n (pBot (CupodV k)) (CupodV k) (pBot (CupodV k)) 1)) ∧
      ((∃ n, EvalGraph n (JustV7 k) (DupocV k) (JustV7 k) 0) ∧
        (∃ n, EvalGraph n (JustTV7 k) (CupodV k) (JustTV7 k) 1)) := by
  rw [← stdReadingV_eq_stdReading]; exact eval_pJD_iff_std k

/-- **The bounded Löb premise of the Just × Dupoc family, slack `(21, 24)`.** -/
theorem loebSound_pJD : LoebSound pJD 21 24 := by
  intro V _ _ k a ha h
  have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
  have ha₁ := le_trans (slack6_le₁ a _ _ _ _ _ (formulaLen_instB_pJD2 k) (formulaLen_instB_pJD k)) ha
  have ha₂ := le_trans (slack6_le a _ _ _ _ _ _ _ (formulaLen_instB_pJDR k) (formulaLen_instB_pBDD2 k)
    (formulaLen_instB_pJD k)) ha
  have ha₃ := le_trans (slack6_le' a _ _ _ _ _ _ _ (formulaLen_instB_pJDR k) (formulaLen_instB_pDJ2 k)
    (formulaLen_instB_pJD k)) ha
  obtain ⟨⟨j1, j2⟩, _, ⟨d1, d2⟩, ⟨b1, b2⟩⟩ := pJD_all_V k (pJD_guards_V k a ha₁ ha₂ ha₃ h)
  exact ⟨(eval_pJD_iff_stdReading k).mpr ⟨⟨⟨2, d1⟩, ⟨2, d2⟩⟩, ⟨⟨3, b1⟩, ⟨3, b2⟩⟩, ⟨⟨2, j1⟩, ⟨2, j2⟩⟩⟩,
    (eval_pJD_iff_swap k).mpr ⟨⟨⟨2, d1⟩, ⟨2, d2⟩⟩, ⟨⟨3, b1⟩, ⟨3, b2⟩⟩, ⟨⟨2, j1⟩, ⟨2, j2⟩⟩⟩⟩

/-! #### The cell at ℕ -/

/-- **The Just × Dupoc cell, packaged**: for all large `k`, Just cooperates with Dupoc and Dupoc
cooperates with Just (fuel 2), and both guard boxes hold. -/
theorem loeb_Just7_vs_Dupoc_core_of_nec {d : ℕ} (hE : BoundedInnerNec d) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      (EvalGraph 2 (Just7 k) (Dupoc k) (Just7 k) 0 ∧ EvalGraph 2 (Dupoc k) (Just7 k) (Dupoc k) 0) ∧
      (LenBox TAct k (guardCode (⌜guardTemplate 0⌝ : ℕ) (pBot (Dupoc k)) (Dupoc k)) ∧
        LenBox TAct k (guardCode (⌜guardTemplate 0⌝ : ℕ) (Dupoc k) (Just7 k))) := by
  obtain ⟨k₀, h⟩ := family_found pJD hE loebSound_pJD
  refine ⟨k₀, fun k hk ↦ ?_⟩
  obtain ⟨a, ha, hpc⟩ := h k hk
  have ha₁ := le_def.mpr (slack6_nat₁ a _ _ _ _ _ k (formulaLen_instB_pJD2 (V := ℕ) k)
    (formulaLen_instB_pJD (V := ℕ) k) ha)
  have ha₂ := le_def.mpr (slack6_nat a _ _ _ _ _ _ _ k (formulaLen_instB_pJDR (V := ℕ) k)
    (formulaLen_instB_pBDD2 (V := ℕ) k) (formulaLen_instB_pJD (V := ℕ) k) ha)
  have ha₃ := le_def.mpr (slack6_nat' a _ _ _ _ _ _ _ k (formulaLen_instB_pJDR (V := ℕ) k)
    (formulaLen_instB_pDJ2 (V := ℕ) k) (formulaLen_instB_pJD (V := ℕ) k) ha)
  have hb := pJD_guards_V (V := ℕ) k a ha₁ ha₂ ha₃ hpc
  obtain ⟨⟨j1, _⟩, ⟨d1, _⟩, _, _⟩ := pJD_all_V (V := ℕ) k hb
  exact ⟨⟨j1, d1⟩, hb.1.1, hb.2.2.1⟩

/-- **Just × Dupoc is `(C, C)` in PA-`S'`, conditional on bounded inner necessitation** (fuel 2). -/
theorem loeb_Just7_vs_Dupoc_of_nec {d : ℕ} (hE : BoundedInnerNec d) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 2 (Just7 k) (Dupoc k) (Just7 k) 0 ∧ EvalGraph 2 (Dupoc k) (Just7 k) (Dupoc k) 0 := by
  obtain ⟨k₀, h⟩ := loeb_Just7_vs_Dupoc_core_of_nec hE
  exact ⟨k₀, fun k hk ↦ (h k hk).1⟩

/-- **Just × Dupoc `(C, C)` in PA-`S'`, unconditional**: for all large `k`, `Just7 k` cooperates with
`Dupoc k` and `Dupoc k` cooperates with `Just7 k` (fuel 2) — the engine's `outcome_JustBot_vs_DupocBot`,
the mutual Löb cell. -/
theorem loeb_Just7_vs_Dupoc :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 2 (Just7 k) (Dupoc k) (Just7 k) 0 ∧ EvalGraph 2 (Dupoc k) (Just7 k) (Dupoc k) 0 :=
  loeb_Just7_vs_Dupoc_of_nec boundedInnerNec_sixteen

/-- **The box forms, unconditional**: Just finds its guard against Dupoc (the node-budget guard code of
the constant template) and Dupoc finds its guard against Just. -/
theorem loeb_Just7_vs_Dupoc_guards :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      LenBox TAct k (guardCodeB (⌜guardTemplateJust7⌝ : ℕ) (Just7 k) (Dupoc k) k) ∧
      LenBox TAct k (guardCode (⌜guardTemplate 0⌝ : ℕ) (Dupoc k) (Just7 k)) := by
  obtain ⟨k₀, h⟩ := loeb_Just7_vs_Dupoc_core_of_nec boundedInnerNec_sixteen
  refine ⟨k₀, fun k hk ↦ ?_⟩
  rw [guardCodeB_guardTemplateJust7]
  exact (h k hk).2

end dupocCell

/-! ### 7. Cell 3 — CIMCIC × Just `(C, C)` -/

section cimcicCell

/-- **Just's guard against CIMCIC** (= Dupoc's guard in the frame `(pBot (Dupoc k), CIMCIC)`):
"`CimcicV k` plays C against `pBot (Dupoc k)`". -/
noncomputable def qJCi : Semisentence LAct 1 := qG 0 TBD uD wD TCi uCi wCi

lemma qJCi_def : qJCi = qG 0 TBD uD wD TCi uCi wCi := rfl

theorem guardCode_botDupocV_CimcicV_eq_instB (k : V) :
    guardCode (⌜guardTemplate 0⌝ : V) (pBot (DupocV k)) (CimcicV k) = instB (⌜qJCi⌝ : V) k :=
  guardCode_GtmplA_eq_instB 0 k TBD uD wD TCi uCi wCi (hX_botDupoc k) (hU_botDupoc k) (hW_botDupoc k) (hX_cimcic k)
    (hU_cimcic k) (hW_cimcic k)

theorem guardCode_botCupodV_CimcicTV_eq_instB (k : V) :
    guardCode (⌜guardTemplate 1⌝ : V) (pBot (CupodV k)) (CimcicTV k) = instB (⌜Semiformula.lMap swap qJCi⌝ : V) k := by
  have h := guardCode_GtmplA_swap_eq_instB 0 k TBD uD wD TCi uCi wCi (hX_botDupoc k) (hU_botDupoc k) (hW_botDupoc k)
    (hX_cimcic k) (hU_cimcic k) (hW_cimcic k)
  rwa [swapAction_zero, transposeCode_pBot_DupocV, transposeCode_CimcicV] at h

theorem eval_qJCi_iff_V (k : V) :
    Semiformula.Eval (s := stdReadingV V) ![k] Empty.elim qJCi ↔
      ∃ n, EvalGraph n (CimcicV k) (pBot (DupocV k)) (CimcicV k) 0 := by
  have h := eval_qG_iff_V 0 k TBD uD wD TCi uCi wCi (desc_botDupoc k) (desc_cimcic k)
  rwa [Nat.cast_zero] at h

theorem eval_qJCi_swapped_iff_V (k : V) :
    Semiformula.Eval (s := stdReadingV V) ![k] Empty.elim (Semiformula.lMap swap qJCi) ↔
      ∃ n, EvalGraph n (CimcicTV k) (pBot (CupodV k)) (CimcicTV k) 1 := by
  rw [qJCi_def, lMap_swap_qG, swapAction_zero]
  have h := eval_qG_iff_V 1 k _ _ _ _ _ _ (descT_botDupoc k) (descT_cimcic k)
  rwa [Nat.cast_one] at h

/-! #### The mutual family -/

/-- The two-sided conjunct of Just's guard against CIMCIC. -/
noncomputable def pJCi2 : Semisentence LAct 1 := qJCi ⋏ Semiformula.lMap swap qJCi
/-- The right part: Just's guard against CIMCIC and CIMCIC's family against `pBot (Dupoc k)`. -/
noncomputable def pCJR : Semisentence LAct 1 := pJCi2 ⋏ pGC TBD uD wD
/-- **The Löb family of the CIMCIC × Just cell**: CIMCIC's family against Just AND the right part. -/
noncomputable def pCJ : Semisentence LAct 1 := pGC TJ uJ wJ ⋏ pCJR

lemma pJCi2_def : pJCi2 = qJCi ⋏ Semiformula.lMap swap qJCi := rfl
lemma pCJR_def : pCJR = pJCi2 ⋏ pGC TBD uD wD := rfl
lemma pCJ_def : pCJ = pGC TJ uJ wJ ⋏ pCJR := rfl

lemma lMap_swap_pJCi2 : Semiformula.lMap swap pJCi2 = Semiformula.lMap swap qJCi ⋏ qJCi := by
  rw [pJCi2_def, LogicalConnective.HomClass.map_and, lMap_swap_swap]

theorem instB_quote_pJCi2 (k : V) :
    instB (⌜pJCi2⌝ : V) k = instB (⌜qJCi⌝ : V) k ^⋏ instB (⌜Semiformula.lMap swap qJCi⌝ : V) k :=
  instB_quote_and _ _ k
theorem instB_quote_pCJR (k : V) :
    instB (⌜pCJR⌝ : V) k = instB (⌜pJCi2⌝ : V) k ^⋏ instB (⌜pGC TBD uD wD⌝ : V) k :=
  instB_quote_and _ _ k
theorem instB_quote_pCJ (k : V) :
    instB (⌜pCJ⌝ : V) k = instB (⌜pGC TJ uJ wJ⌝ : V) k ^⋏ instB (⌜pCJR⌝ : V) k :=
  instB_quote_and _ _ k

lemma formulaLen_instB_pJCi2 (k : V) :
    formulaLen LAct (instB (⌜pJCi2⌝ : V) k) =
      formulaLen LAct (instB (⌜qJCi⌝ : V) k) + formulaLen LAct (instB (⌜Semiformula.lMap swap qJCi⌝ : V) k) + 1 := by
  rw [instB_quote_pJCi2, formulaLen_and (isFormula_instB_quote _ k).isUFormula (isFormula_instB_quote _ k).isUFormula]
lemma formulaLen_instB_pCJR (k : V) :
    formulaLen LAct (instB (⌜pCJR⌝ : V) k) =
      formulaLen LAct (instB (⌜pJCi2⌝ : V) k) + formulaLen LAct (instB (⌜pGC TBD uD wD⌝ : V) k) + 1 := by
  rw [instB_quote_pCJR, formulaLen_and (isFormula_instB_quote _ k).isUFormula (isFormula_instB_quote _ k).isUFormula]
lemma formulaLen_instB_pCJ (k : V) :
    formulaLen LAct (instB (⌜pCJ⌝ : V) k) =
      formulaLen LAct (instB (⌜pGC TJ uJ wJ⌝ : V) k) + formulaLen LAct (instB (⌜pCJR⌝ : V) k) + 1 := by
  rw [instB_quote_pCJ, formulaLen_and (isFormula_instB_quote _ k).isUFormula (isFormula_instB_quote _ k).isUFormula]

/-- **All the plays from a box of the family** (three-level ∧-elimination): CIMCIC cooperates with Just,
Just cooperates with CIMCIC, CIMCIC cooperates with `pBot (Dupoc k)` (the truth of `qJCi`), the
bot-wrapped Dupoc cooperates with CIMCIC (the consequent of CIMCIC's guard against it), and the
transposed plays. -/
theorem pCJ_all_V (k a : V)
    (ha₁ : a + 8 * (formulaLen LAct (instB (⌜pGC TJ uJ wJ⌝ : V) k) + formulaLen LAct (instB (⌜pCJR⌝ : V) k)) + 7 +
      8 * (formulaLen LAct (instB (⌜qCG TJ uJ wJ⌝ : V) k) +
        formulaLen LAct (instB (⌜qCTG (Semiterm.lMap swap TJ) (Semiterm.lMap swap uJ) (Semiterm.lMap swap wJ)⌝ : V) k))
      + 7 ≤ k)
    (ha₂ : a + 8 * (formulaLen LAct (instB (⌜pGC TJ uJ wJ⌝ : V) k) + formulaLen LAct (instB (⌜pCJR⌝ : V) k)) + 7 +
      8 * (formulaLen LAct (instB (⌜pJCi2⌝ : V) k) + formulaLen LAct (instB (⌜pGC TBD uD wD⌝ : V) k)) + 7 +
      8 * (formulaLen LAct (instB (⌜qJCi⌝ : V) k) + formulaLen LAct (instB (⌜Semiformula.lMap swap qJCi⌝ : V) k))
      + 7 ≤ k)
    (ha₃ : a + 8 * (formulaLen LAct (instB (⌜pGC TJ uJ wJ⌝ : V) k) + formulaLen LAct (instB (⌜pCJR⌝ : V) k)) + 7 +
      8 * (formulaLen LAct (instB (⌜pJCi2⌝ : V) k) + formulaLen LAct (instB (⌜pGC TBD uD wD⌝ : V) k)) + 7 +
      8 * (formulaLen LAct (instB (⌜qCG TBD uD wD⌝ : V) k) +
        formulaLen LAct (instB (⌜qCTG (Semiterm.lMap swap TBD) (Semiterm.lMap swap uD) (Semiterm.lMap swap wD)⌝ : V) k))
      + 7 ≤ k)
    (h : LenBoxUnbounded TAct a (instB (⌜pCJ⌝ : V) k)) :
    (EvalGraph 2 (CimcicV k) (JustV7 k) (CimcicV k) 0 ∧ EvalGraph 2 (CimcicTV k) (JustTV7 k) (CimcicTV k) 1) ∧
    (EvalGraph 2 (JustV7 k) (CimcicV k) (JustV7 k) 0 ∧ EvalGraph 2 (JustTV7 k) (CimcicTV k) (JustTV7 k) 1) ∧
    (EvalGraph 2 (CimcicV k) (pBot (DupocV k)) (CimcicV k) 0 ∧
      EvalGraph 2 (CimcicTV k) (pBot (CupodV k)) (CimcicTV k) 1) ∧
    (EvalGraph 3 (pBot (DupocV k)) (CimcicV k) (pBot (DupocV k)) 0 ∧
      EvalGraph 3 (pBot (CupodV k)) (CimcicTV k) (pBot (CupodV k)) 1) ∧
    (LenBox TAct k (guardCode (⌜templateC⌝ : V) (CimcicV k) (JustV7 k)) ∧
      LenBox TAct k (guardCode (⌜guardTemplate 0⌝ : V) (pBot (DupocV k)) (CimcicV k))) := by
  rw [instB_quote_pCJ] at h
  have hx := isFormula_instB_quote (pGC TJ uJ wJ) k
  have hy := isFormula_instB_quote pCJR k
  have h₁ := lenBoxUnbounded_andL_V hx hy h
  have h₂ := lenBoxUnbounded_andR_V hx hy h
  obtain ⟨g1, g2⟩ := pGC_both_V k TJ uJ wJ (hX_just7 k) (hU_just7 k) (hW_just7 k) _ ha₁ h₁
  obtain ⟨gb1, _⟩ := pGC_guards_V k TJ uJ wJ (hX_just7 k) (hU_just7 k) (hW_just7 k) _ ha₁ h₁
  rw [transposeCode_JustV7] at g2
  have hx₂ := isFormula_instB_quote pJCi2 k
  have hy₂ := isFormula_instB_quote (pGC TBD uD wD) k
  have h₂' : LenBoxUnbounded TAct
      (a + 8 * (formulaLen LAct (instB (⌜pGC TJ uJ wJ⌝ : V) k) + formulaLen LAct (instB (⌜pCJR⌝ : V) k)) + 7)
      (instB (⌜pJCi2⌝ : V) k ^⋏ instB (⌜pGC TBD uD wD⌝ : V) k) := by
    rw [← instB_quote_pCJR]; exact h₂
  have h₂₁ := lenBoxUnbounded_andL_V hx₂ hy₂ h₂'
  have h₂₂ := lenBoxUnbounded_andR_V hx₂ hy₂ h₂'
  have hx₃ := isFormula_instB_quote qJCi k
  have hy₃ := isFormula_instB_quote (Semiformula.lMap swap qJCi) k
  have h₂₁' : LenBoxUnbounded TAct
      (a + 8 * (formulaLen LAct (instB (⌜pGC TJ uJ wJ⌝ : V) k) + formulaLen LAct (instB (⌜pCJR⌝ : V) k)) + 7 +
        8 * (formulaLen LAct (instB (⌜pJCi2⌝ : V) k) + formulaLen LAct (instB (⌜pGC TBD uD wD⌝ : V) k)) + 7)
      (instB (⌜qJCi⌝ : V) k ^⋏ instB (⌜Semiformula.lMap swap qJCi⌝ : V) k) := by
    rw [← instB_quote_pJCi2]; exact h₂₁
  have c1 := lenBoxUnbounded_mono_V ha₂ (lenBoxUnbounded_andL_V hx₃ hy₃ h₂₁')
  have c1' := lenBoxUnbounded_mono_V ha₂ (lenBoxUnbounded_andR_V hx₃ hy₃ h₂₁')
  rw [lenBoxUnbounded_iff_lenBox, ← guardCode_botDupocV_CimcicV_eq_instB] at c1
  rw [lenBoxUnbounded_iff_lenBox, ← guardCode_botCupodV_CimcicTV_eq_instB] at c1'
  obtain ⟨b1, b2⟩ := pGC_both_V k TBD uD wD (hX_botDupoc k) (hU_botDupoc k) (hW_botDupoc k) _ ha₃ h₂₂
  rw [transposeCode_pBot_DupocV] at b2
  exact ⟨⟨g1, g2⟩, ⟨just7_search_V k _ _ c1, just7T_search_V k _ _ c1'⟩, ⟨b1, b2⟩,
    ⟨botDupoc_frame_search_V k _ _ c1, botCupod_frame_search_V k _ _ c1'⟩, ⟨gb1, c1⟩⟩

/-! #### `pCJ` in both readings -/

theorem eval_pCJ_iff_std (k : V) :
    Semiformula.Eval (s := stdReadingV V) ![k] Empty.elim pCJ ↔
      (((∃ n, EvalGraph n (CimcicV k) (JustV7 k) (CimcicV k) 0) → (∃ n, EvalGraph n (JustV7 k) (CimcicV k) (JustV7 k) 0)) ∧
       ((∃ n, EvalGraph n (CimcicTV k) (JustTV7 k) (CimcicTV k) 1) → (∃ n, EvalGraph n (JustTV7 k) (CimcicTV k) (JustTV7 k) 1))) ∧
      ((∃ n, EvalGraph n (CimcicV k) (pBot (DupocV k)) (CimcicV k) 0) ∧
        (∃ n, EvalGraph n (CimcicTV k) (pBot (CupodV k)) (CimcicTV k) 1)) ∧
      (((∃ n, EvalGraph n (CimcicV k) (pBot (DupocV k)) (CimcicV k) 0) →
          (∃ n, EvalGraph n (pBot (DupocV k)) (CimcicV k) (pBot (DupocV k)) 0)) ∧
       ((∃ n, EvalGraph n (CimcicTV k) (pBot (CupodV k)) (CimcicTV k) 1) →
          (∃ n, EvalGraph n (pBot (CupodV k)) (CimcicTV k) (pBot (CupodV k)) 1))) := by
  rw [pCJ_def, pCJR_def, pJCi2_def]
  simp only [LogicalConnective.HomClass.map_and, LogicalConnective.Prop.and_eq]
  rw [eval_pGC_iff_std k TJ uJ wJ (desc_just7 k) (descT_just7 k), eval_qJCi_iff_V, eval_qJCi_swapped_iff_V,
    eval_pGC_iff_std k TBD uD wD (desc_botDupoc k) (descT_botDupoc k)]

theorem eval_pCJ_iff_swap (k : V) :
    Semiformula.Eval (s := swappedReading V) ![k] Empty.elim pCJ ↔
      (((∃ n, EvalGraph n (CimcicV k) (JustV7 k) (CimcicV k) 0) → (∃ n, EvalGraph n (JustV7 k) (CimcicV k) (JustV7 k) 0)) ∧
       ((∃ n, EvalGraph n (CimcicTV k) (JustTV7 k) (CimcicTV k) 1) → (∃ n, EvalGraph n (JustTV7 k) (CimcicTV k) (JustTV7 k) 1))) ∧
      ((∃ n, EvalGraph n (CimcicV k) (pBot (DupocV k)) (CimcicV k) 0) ∧
        (∃ n, EvalGraph n (CimcicTV k) (pBot (CupodV k)) (CimcicTV k) 1)) ∧
      (((∃ n, EvalGraph n (CimcicV k) (pBot (DupocV k)) (CimcicV k) 0) →
          (∃ n, EvalGraph n (pBot (DupocV k)) (CimcicV k) (pBot (DupocV k)) 0)) ∧
       ((∃ n, EvalGraph n (CimcicTV k) (pBot (CupodV k)) (CimcicTV k) 1) →
          (∃ n, EvalGraph n (pBot (CupodV k)) (CimcicTV k) (pBot (CupodV k)) 1))) := by
  rw [eval_swappedReading, pCJ_def, pCJR_def, pJCi2_def, ← stdReadingV_eq_stdReading]
  simp only [LogicalConnective.HomClass.map_and, lMap_swap_swap, lMap_swap_pGC, LogicalConnective.Prop.and_eq]
  rw [eval_qCG_iff_V k TJ uJ wJ (desc_just7 k), eval_qCTG_iff_V k _ _ _ (descT_just7 k), eval_qJCi_iff_V,
    eval_qJCi_swapped_iff_V, eval_qCG_iff_V k TBD uD wD (desc_botDupoc k), eval_qCTG_iff_V k _ _ _ (descT_botDupoc k)]
  constructor
  · rintro ⟨⟨a, b⟩, ⟨c, d⟩, ⟨e, f⟩⟩; exact ⟨⟨b, a⟩, ⟨d, c⟩, ⟨f, e⟩⟩
  · rintro ⟨⟨a, b⟩, ⟨c, d⟩, ⟨e, f⟩⟩; exact ⟨⟨b, a⟩, ⟨d, c⟩, ⟨f, e⟩⟩

theorem eval_pCJ_iff_stdReading (k : V) :
    Semiformula.Eval (s := stdReading V) ![k] Empty.elim pCJ ↔
      (((∃ n, EvalGraph n (CimcicV k) (JustV7 k) (CimcicV k) 0) → (∃ n, EvalGraph n (JustV7 k) (CimcicV k) (JustV7 k) 0)) ∧
       ((∃ n, EvalGraph n (CimcicTV k) (JustTV7 k) (CimcicTV k) 1) → (∃ n, EvalGraph n (JustTV7 k) (CimcicTV k) (JustTV7 k) 1))) ∧
      ((∃ n, EvalGraph n (CimcicV k) (pBot (DupocV k)) (CimcicV k) 0) ∧
        (∃ n, EvalGraph n (CimcicTV k) (pBot (CupodV k)) (CimcicTV k) 1)) ∧
      (((∃ n, EvalGraph n (CimcicV k) (pBot (DupocV k)) (CimcicV k) 0) →
          (∃ n, EvalGraph n (pBot (DupocV k)) (CimcicV k) (pBot (DupocV k)) 0)) ∧
       ((∃ n, EvalGraph n (CimcicTV k) (pBot (CupodV k)) (CimcicTV k) 1) →
          (∃ n, EvalGraph n (pBot (CupodV k)) (CimcicTV k) (pBot (CupodV k)) 1))) := by
  rw [← stdReadingV_eq_stdReading]; exact eval_pCJ_iff_std k

/-- **The bounded Löb premise of the CIMCIC × Just family, slack `(21, 24)`.** -/
theorem loebSound_pCJ : LoebSound pCJ 21 24 := by
  intro V _ _ k a ha h
  have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
  have ha₁ := le_trans (slack6_le₁ a _ _ _ _ _ (formulaLen_instB_pGC TJ uJ wJ k) (formulaLen_instB_pCJ k)) ha
  have ha₂ := le_trans (slack6_le a _ _ _ _ _ _ _ (formulaLen_instB_pCJR k) (formulaLen_instB_pJCi2 k)
    (formulaLen_instB_pCJ k)) ha
  have ha₃ := le_trans (slack6_le' a _ _ _ _ _ _ _ (formulaLen_instB_pCJR k) (formulaLen_instB_pGC TBD uD wD k)
    (formulaLen_instB_pCJ k)) ha
  obtain ⟨_, ⟨j1, j2⟩, ⟨c1, c2⟩, ⟨b1, b2⟩, _⟩ := pCJ_all_V k a ha₁ ha₂ ha₃ h
  exact ⟨(eval_pCJ_iff_stdReading k).mpr ⟨⟨fun _ ↦ ⟨2, j1⟩, fun _ ↦ ⟨2, j2⟩⟩, ⟨⟨2, c1⟩, ⟨2, c2⟩⟩,
      ⟨fun _ ↦ ⟨3, b1⟩, fun _ ↦ ⟨3, b2⟩⟩⟩,
    (eval_pCJ_iff_swap k).mpr ⟨⟨fun _ ↦ ⟨2, j1⟩, fun _ ↦ ⟨2, j2⟩⟩, ⟨⟨2, c1⟩, ⟨2, c2⟩⟩,
      ⟨fun _ ↦ ⟨3, b1⟩, fun _ ↦ ⟨3, b2⟩⟩⟩⟩

/-! #### The cell at ℕ -/

/-- **The CIMCIC × Just cell, packaged**: for all large `k`, CIMCIC cooperates with Just and Just
cooperates with CIMCIC (fuel 2), and both guard boxes hold. -/
theorem loeb_Cimcic_vs_Just7_core_of_nec {d : ℕ} (hE : BoundedInnerNec d) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      (EvalGraph 2 (Cimcic k) (Just7 k) (Cimcic k) 0 ∧ EvalGraph 2 (Just7 k) (Cimcic k) (Just7 k) 0) ∧
      (LenBox TAct k (guardCode (⌜templateC⌝ : ℕ) (Cimcic k) (Just7 k)) ∧
        LenBox TAct k (guardCode (⌜guardTemplate 0⌝ : ℕ) (pBot (Dupoc k)) (Cimcic k))) := by
  obtain ⟨k₀, h⟩ := family_found pCJ hE loebSound_pCJ
  refine ⟨k₀, fun k hk ↦ ?_⟩
  obtain ⟨a, ha, hpc⟩ := h k hk
  have ha₁ := le_def.mpr (slack6_nat₁ a _ _ _ _ _ k (formulaLen_instB_pGC (V := ℕ) TJ uJ wJ k)
    (formulaLen_instB_pCJ (V := ℕ) k) ha)
  have ha₂ := le_def.mpr (slack6_nat a _ _ _ _ _ _ _ k (formulaLen_instB_pCJR (V := ℕ) k)
    (formulaLen_instB_pJCi2 (V := ℕ) k) (formulaLen_instB_pCJ (V := ℕ) k) ha)
  have ha₃ := le_def.mpr (slack6_nat' a _ _ _ _ _ _ _ k (formulaLen_instB_pCJR (V := ℕ) k)
    (formulaLen_instB_pGC (V := ℕ) TBD uD wD k) (formulaLen_instB_pCJ (V := ℕ) k) ha)
  obtain ⟨⟨g1, _⟩, ⟨j1, _⟩, _, _, hb⟩ := pCJ_all_V (V := ℕ) k a ha₁ ha₂ ha₃ hpc
  exact ⟨⟨g1, j1⟩, hb⟩

/-- **CIMCIC × Just is `(C, C)` in PA-`S'`, conditional on bounded inner necessitation** (fuel 2). -/
theorem loeb_Cimcic_vs_Just7_of_nec {d : ℕ} (hE : BoundedInnerNec d) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 2 (Cimcic k) (Just7 k) (Cimcic k) 0 ∧ EvalGraph 2 (Just7 k) (Cimcic k) (Just7 k) 0 := by
  obtain ⟨k₀, h⟩ := loeb_Cimcic_vs_Just7_core_of_nec hE
  exact ⟨k₀, fun k hk ↦ (h k hk).1⟩

/-- **CIMCIC × Just `(C, C)` in PA-`S'`, unconditional**: for all large `k`, `Cimcic k` cooperates with
`Just7 k` and `Just7 k` cooperates with `Cimcic k` (fuel 2) — the engine's
`llm_outcome_CIMCIC_vs_JustBot`. -/
theorem loeb_Cimcic_vs_Just7 :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 2 (Cimcic k) (Just7 k) (Cimcic k) 0 ∧ EvalGraph 2 (Just7 k) (Cimcic k) (Just7 k) 0 :=
  loeb_Cimcic_vs_Just7_of_nec boundedInnerNec_sixteen

/-- **The box forms, unconditional**: CIMCIC finds its guard against Just, and Just finds its guard
against CIMCIC (the node-budget guard code of the constant template). -/
theorem loeb_Cimcic_vs_Just7_guards :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      LenBox TAct k (guardCode (⌜templateC⌝ : ℕ) (Cimcic k) (Just7 k)) ∧
      LenBox TAct k (guardCodeB (⌜guardTemplateJust7⌝ : ℕ) (Just7 k) (Cimcic k) k) := by
  obtain ⟨k₀, h⟩ := loeb_Cimcic_vs_Just7_core_of_nec boundedInnerNec_sixteen
  refine ⟨k₀, fun k hk ↦ ?_⟩
  rw [guardCodeB_guardTemplateJust7]
  exact (h k hk).2

end cimcicCell

end ArithS
