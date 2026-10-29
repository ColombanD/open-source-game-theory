import ArithS.Cells.CIMCIC

/-!
# ArithS.Cells.JustSlot — JustBot on a CONSTANT template with a budget slot (route c): Just × Just,
Just × Dupoc and CIMCIC × Just, all `(C, C)`, in PA-`S'`

`Research/Notes/ROUTE_B_SCOPE.md` §7–§8. `Cells/JustBot.lean` arithmetized
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


/-! #### The codes -/

/-- The codes of `![#6, #3, #4, #5]`. -/
noncomputable def sVec7 : V :=
  (⌜(Rew.emb (#6 : Semiterm LAct Empty 7) : SyntacticSemiterm LAct 7)⌝ : V) ∷
    ⌜(Rew.emb (#3 : Semiterm LAct Empty 7) : SyntacticSemiterm LAct 7)⌝ ∷
    ⌜(Rew.emb (#4 : Semiterm LAct Empty 7) : SyntacticSemiterm LAct 7)⌝ ∷
    ⌜(Rew.emb (#5 : Semiterm LAct Empty 7) : SyntacticSemiterm LAct 7)⌝ ∷ 0


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


end template

/-! ### 2. `JustV7`: the searcher on the constant template, and its equivalence with `JustV` -/

section just7


end just7

/-! ### 3. The description layer of `JustV7 k` (`Cells/CIMCIC.lean` §2 re-run) -/

section canonical

/-- The budget-independent inner part of Just's code. -/
noncomputable def innerJ : ℕ := ppair (⌜guardTemplateJust7⌝ : ℕ) (ppair (pConst 0) (pConst 1))

/-- The budget-independent inner part of the transposed searcher's code. -/
noncomputable def innerJT : ℕ := ppair (⌜guardTemplateJust7A 1 uC wC⌝ : ℕ) (ppair (pConst 1) (pConst 0))


/- Closed constants built from the giant template: never to be evaluated. -/
attribute [irreducible] innerJ innerJT


/-! #### The description hypotheses -/


end canonical

/-! ### 4. The slack arithmetic of a THREE-level conjunction family, `(21, 24)` -/

section slack


end slack

/-! ### 5. Cell 1 — Just × Just `(C, C)` -/

section selfCell


/-! #### `pJJ` in both readings -/


/-! #### The cell at ℕ -/


end selfCell

/-! ### 6. Cell 2 — Just × Dupoc `(C, C)`, the three-guard mutual family -/

section dupocCell


/-! #### The instance equations on codes -/


/-! #### The truth equations -/


/-! #### The mutual family -/


/-! #### `pJD` in both readings -/


/-! #### The cell at ℕ -/


end dupocCell

/-! ### 7. Cell 3 — CIMCIC × Just `(C, C)` -/

section cimcicCell


/-! #### The mutual family -/


/-! #### `pCJ` in both readings -/


/-! #### The cell at ℕ -/


end cimcicCell

end ArithS
