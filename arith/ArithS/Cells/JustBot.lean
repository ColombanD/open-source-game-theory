import ArithS.Cells.DupocMirror

/-!
# ArithS.Cells.JustBot — the frozen-`.bot` Löb families in PA-`S'`

`Research/Notes/ROUTE_B_SCOPE.md` §3 Phase 2, the JustBot family. The engine's
`JustBot k := .search k (.plays .opp (.bot (DupocBot k)) C) (.const C) (.const D)` — "cooperate
iff I can prove the opponent cooperates with a FROZEN snapshot of Dupoc k". Every JustBot cell
rests on the bot-wrapped Dupoc self-cooperation (`Theorems/JustBot/Helpers.loeb_botDupoc_vs_botDupoc_of_nec`).
V-generic (every model of `𝗜𝚺₁`, budgets `k : V` possibly nonstandard) unless a statement says `ℕ`.

1. **Bot-wrapping.** `pBot p` runs `p` in the SAME frame (`EvalGraph.bot_iff`) and is FROZEN under
   `substCode`; `pBot` is strictly monotone, so the canonical description commutes with it
   (`canonical_pBot`, `revalueU_pBot`, `revalueW_pBot`; `transposeCode_pBot`). Dupoc's search clause holds in ANY frame
   (`dupoc_frame_search_V`): `pBot (DupocV k)` in the frame `(me, opp)` searches
   `guardCode ⌜guardTemplate 0⌝ me opp` — so the guards below are those of the FRAME players.
2. **The description tower.** `TBD := lMap emb (botT1 (searchT1 gD pD qD))` is the one-variable
   description of `pBot (Dupoc k)` (`botT1 t = succT1 (ppairT1 3̂ t)`, `CodeTerm.codeTerm_bot`);
   `val_TBD_V : TBD(k) = canonical (pBot (DupocV k))`, `termSubst_TBD : (binNumeral k)-instance of ⌜TBD⌝ =
   codeTerm (canonical (pBot (DupocV k)))`.
3. **The generic instance equation and truth equation** for a template instance
   `guardTemplate a ⇜ ![T₁, cl u₁, cl w₁, T₂, cl u₂, cl w₂]` (`guardCode_eq_instB_of`,
   `eval_GtmplA_subst_iff`): the six per-cell substitution computations of `InstanceV`/
   `Cells/DupocMirror` factored once.
4. **Family (1): the bot-wrapped self-play** `pBD := qBD ⋏ qBC` (`qBD = guardTemplate 0 ⇜ ![TBD, cl uD, cl wD,
   TBD, cl uD, cl wD]`, `qBC = lMap swap qBD`): `loeb_botDupoc_vs_botDupoc` — for all large
   `k`, `EvalGraph 3 (pBot (Dupoc k)) (pBot (Dupoc k)) (pBot (Dupoc k)) 0` (fuel 3: bot, search,
   const) — and `loeb_botCupod_vs_botCupod`.
5. **JustV.** `JustV k := pSearch k (gJ k) (pConst 0) (pConst 1)` with the stored template
   `gJ k := subst (jVec k) ⌜guardTemplate 0⌝` — `guardTemplate 0` PRE-FILLED in its me-slots with the closed
   description of `pBot (DupocV k)`, the opp-slots left as the frame variables `^#3 ^#4 ^#5`.
   `guardCode_JustV : guardCode (gJ k) me opp = guardCode ⌜guardTemplate 0⌝ (pBot (DupocV k)) opp` — Just's
   guard against `opp` IS the guard of Dupoc-in-bot against `opp` (the frame's `me` is unused,
   exactly the engine's `Formula.subst` on `.plays .opp (.bot (DupocBot k)) C`). At ℕ, `Just k :=
   pSearch k ⌜guardTemplateJust k⌝ …` with the meta template `guardTemplateJust k` and the bridge `JustV_nat`.
6. **Family (3): Just × Mirror** `pJM := qJM ⋏ qJM'` (`qJM = guardTemplate 0 ⇜ ![TBD, cl uD, cl wD, cl TM,
   cl (numT 0), cl (numT 1)]`, "Mirror plays C against `pBot (Dupoc k)`"): a proof of `qJM(k)` within
   budget makes Dupoc-in-bot cooperate with Mirror (fuel 3), Mirror copies (fuel 4), so it is true;
   `family_found pJM` then fires Just's OUTER search by the same box:
   `loeb_Just_vs_Mirror` — `EvalGraph 2 (Just k) Mirror (Just k) 0 ∧ EvalGraph 3 Mirror
   (Just k) Mirror 0`, the `(C, C)` cell.

**Not here — Just × Just and Just × Dupoc (the engine's `outcome_JustBot_vs_JustBot`,
`outcome_JustBot_vs_DupocBot`).** Both need a box of a sentence in which `Just k` itself is
DESCRIBED (Just's guard against Just is "Just k plays C against `pBot (Dupoc k)`"; Dupoc's guard
against Just is "Just k plays C against Dupoc k"). The description `codeTerm (canonical (JustV k))`
carries the leaf `binNumeral (gJ k)` — the binary numeral of the stored template, whose bits depend on
`k` — so it is NOT the `binNumeral k`-instance of any fixed term, and no fixed one-variable formula has
these guards as its `k`-instances: the family-parametric assembly does not apply. In the engine
those cells are the Löb family (1) plus a `search_t` HAND certificate (cost `O(log k)`); the
`S'` twin of that certificate is the transparency lift — bounded-length Σ₁-evaluation of the
description terms — which the package does not have (the POS class of `ROUTE_B_SCOPE.md` §2).

Conventions (`HANDOVER_ARITHMETIZED_S.md` §5–6): every threshold and constant is EXISTENTIAL;
`simp` never sees a closed quote of a large sentence; `omega` is never asked about `V`; at
`V = ℕ` the thresholds are STRICT and the V-generic `≤` is bridged by `le_def`.
-/

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open LAct

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ### 1. Bot-wrapping in every model -/

section bot


end bot

/-! ### 2. The description tower of `pBot (Dupoc k)` -/

section tower


end tower

/-! ### 3. The generic instance equation and truth equation of a template instance -/

section generic

end generic
/-! ### 4. Family (1): the bot-wrapped self-play -/

section botSelf

/-- **The fixed formula of the bot-wrapped Dupoc self-play**: `guardTemplate 0` filled with the
description of `pBot (Dupoc k)` twice. -/
noncomputable def qBD : Semisentence LAct 1 :=
  guardTemplate 0 ⇜ ![TBD, cl uD, cl wD, TBD, cl uD, cl wD]

lemma qBD_eq : qBD = guardTemplate 0 ⇜ ![TBD, cl uD, cl wD, TBD, cl uD, cl wD] := rfl

/-- The transposition: the bot-wrapped Cupod self-play. -/
noncomputable def qBC : Semisentence LAct 1 := Semiformula.lMap swap qBD

lemma lMap_swap_qBD : Semiformula.lMap swap qBD = qBC := rfl

lemma lMap_swap_qBC : Semiformula.lMap swap qBC = qBD := lMap_swap_swap _


/-- **The instance equation on codes of the bot-wrapped Dupoc self-play, in every model.** -/
theorem guardCode_botDupocV_eq_instB (k : V) :
    guardCode (⌜guardTemplate 0⌝ : V) (pBot (DupocV k)) (pBot (DupocV k)) = instB (⌜qBD⌝ : V) k :=
  guardCode_eq_instB_of 0 (termSubst_TBD k) (quote_emb_uD_botDupocV k) (quote_emb_wD_botDupocV k)
    (termSubst_TBD k) (quote_emb_uD_botDupocV k) (quote_emb_wD_botDupocV k)

lemma revalueTemplate_quote_qBD_V : revalueTemplate 1 0 (⌜qBD⌝ : V) = ⌜qBC⌝ :=
  revalueTemplate_quote_sentence_V qBD

lemma guardCode_botCupodV_eq_revalue (k : V) :
    guardCode (⌜guardTemplate 1⌝ : V) (pBot (CupodV k)) (pBot (CupodV k)) =
      revalueTemplate 1 0 (guardCode (⌜guardTemplate 0⌝ : V) (pBot (DupocV k)) (pBot (DupocV k))) := by
  have hg0 : IsSemiformula LAct 6 (⌜guardTemplate 0⌝ : V) := by
    simpa using Sentence.quote_isSemiformula (V := V) (guardTemplate 0)
  have hg1 : IsSemiformula LAct 6 (⌜guardTemplate 1⌝ : V) := by
    simpa using Sentence.quote_isSemiformula (V := V) (guardTemplate 1)
  rw [← substTemplate_of_template hg0, revalueTemplate_substTemplate, transposeCode_pBot_DupocV,
    revalueTemplate_quote_GtmplA_V, swapAction_zero, substTemplate_of_template hg1]

/-- **The instance equation on codes of the bot-wrapped Cupod self-play, in every model.** -/
theorem guardCode_botCupodV_eq_instB (k : V) :
    guardCode (⌜guardTemplate 1⌝ : V) (pBot (CupodV k)) (pBot (CupodV k)) = instB (⌜qBC⌝ : V) k := by
  rw [guardCode_botCupodV_eq_revalue, guardCode_botDupocV_eq_instB]
  unfold instB
  rw [revalueTemplate_subst isAct_one isAct_zero (Sentence.quote_isSemiformul₁ qBD)
    (binNumeral_cons_semitermVec k), revalueTemplate_quote_qBD_V]
  congr 1
  rw [show (1 : V) = 0 + 1 by simp, termRelabelVec_cons (binNumeral_term_LAct k).isUTerm IsUTermVec.empty,
    termRelabelVec_nil, termRelabel_binNumeral]

/-! #### The truth equations -/

/-- `qBC` is `guardTemplate 1` filled with the bot tower and the transposed re-valuation terms. -/
theorem qBC_eq : qBC = guardTemplate 1 ⇜ ![TBD, cl uC, cl wC, TBD, cl uC, cl wC] := by
  unfold qBC qBD
  rw [Semiformula.lMap_subst, lMap_swap_GtmplA, swapAction_zero]
  congr 1
  funext i
  fin_cases i <;> simp [lMap_swap_TBD, lMap_swap_cl, uC, wC]

/-- **The truth equation** (standard reading): `qBD(k)` holds in `stdReadingV V` iff
`pBot (DupocV k)` plays `C` against itself. -/
theorem eval_qBD_iff_V (k : V) :
    Semiformula.Eval (s := stdReadingV V) ![k] Empty.elim qBD ↔
      ∃ n, EvalGraph n (pBot (DupocV k)) (pBot (DupocV k)) (pBot (DupocV k)) 0 := by
  rw [qBD_eq, eval_GtmplA_subst_iff, val_TBD_V, canonical_pBot, revalue_bot, revalue_val_uD_wD_V, Nat.cast_zero]

/-- `qBC(k)` holds in `stdReadingV V` iff `pBot (CupodV k)` plays `D` against itself. -/
theorem eval_qBC_iff_V (k : V) :
    Semiformula.Eval (s := stdReadingV V) ![k] Empty.elim qBC ↔
      ∃ n, EvalGraph n (pBot (CupodV k)) (pBot (CupodV k)) (pBot (CupodV k)) 1 := by
  rw [qBC_eq, eval_GtmplA_subst_iff, val_TBD_V, canonical_pBot, revalue_bot, revalue_val_uC_wC_V, Nat.cast_one]

theorem eval_qBD_swap_iff_V (k : V) :
    Semiformula.Eval (s := swappedReading V) ![k] Empty.elim qBD ↔
      ∃ n, EvalGraph n (pBot (CupodV k)) (pBot (CupodV k)) (pBot (CupodV k)) 1 := by
  rw [eval_swappedReading, lMap_swap_qBD, ← stdReadingV_eq_stdReading]
  exact eval_qBC_iff_V k

theorem eval_qBC_swap_iff_V (k : V) :
    Semiformula.Eval (s := swappedReading V) ![k] Empty.elim qBC ↔
      ∃ n, EvalGraph n (pBot (DupocV k)) (pBot (DupocV k)) (pBot (DupocV k)) 0 := by
  rw [eval_swappedReading, lMap_swap_qBC, ← stdReadingV_eq_stdReading]
  exact eval_qBD_iff_V k

/-! #### The search clauses -/

/-- **The bot-wrapped Dupoc's search clause against itself** (fuel 3). -/
theorem botDupoc_search_V (k : V) :
    LenBox TAct k (guardCode (⌜guardTemplate 0⌝ : V) (pBot (DupocV k)) (pBot (DupocV k))) →
      EvalGraph 3 (pBot (DupocV k)) (pBot (DupocV k)) (pBot (DupocV k)) 0 :=
  botDupoc_frame_search_V k _ _

theorem botCupod_search_V (k : V) :
    LenBox TAct k (guardCode (⌜guardTemplate 1⌝ : V) (pBot (CupodV k)) (pBot (CupodV k))) →
      EvalGraph 3 (pBot (CupodV k)) (pBot (CupodV k)) (pBot (CupodV k)) 1 :=
  botCupod_frame_search_V k _ _

/-! #### The conjunction family -/

/-- **The Löb family of the bot-wrapped self-play.** -/
noncomputable def pBD : Semisentence LAct 1 := qBD ⋏ qBC

lemma pBD_def : pBD = qBD ⋏ qBC := rfl

lemma lMap_swap_pBD : Semiformula.lMap swap pBD = qBC ⋏ qBD := by
  rw [pBD_def, LogicalConnective.HomClass.map_and, lMap_swap_qBD, lMap_swap_qBC]

theorem instB_quote_pBD (k : V) :
    instB (⌜pBD⌝ : V) k = instB (⌜qBD⌝ : V) k ^⋏ instB (⌜qBC⌝ : V) k :=
  instB_quote_and qBD qBC k

lemma formulaLen_instB_pBD (k : V) :
    formulaLen LAct (instB (⌜pBD⌝ : V) k) =
      formulaLen LAct (instB (⌜qBD⌝ : V) k) + formulaLen LAct (instB (⌜qBC⌝ : V) k) + 1 := by
  rw [instB_quote_pBD,
    formulaLen_and (isFormula_instB_quote qBD k).isUFormula (isFormula_instB_quote qBC k).isUFormula]

/-- **Both bot-wrapped searchers find their guards from a box of the conjunction** (fuel 3). -/
theorem pBD_both_V (k : V) : ∀ a : V,
    a + 8 * (formulaLen LAct (instB (⌜qBD⌝ : V) k) + formulaLen LAct (instB (⌜qBC⌝ : V) k)) + 7 ≤ k →
    LenBoxUnbounded TAct a (instB (⌜pBD⌝ : V) k) →
    EvalGraph 3 (pBot (DupocV k)) (pBot (DupocV k)) (pBot (DupocV k)) 0 ∧
      EvalGraph 3 (pBot (CupodV k)) (pBot (CupodV k)) (pBot (CupodV k)) 1 := by
  intro a ha h
  rw [instB_quote_pBD] at h
  have hx := isFormula_instB_quote qBD k
  have hy := isFormula_instB_quote qBC k
  have h₁ := lenBoxUnbounded_mono_V ha (lenBoxUnbounded_andL_V hx hy h)
  have h₂ := lenBoxUnbounded_mono_V ha (lenBoxUnbounded_andR_V hx hy h)
  rw [lenBoxUnbounded_iff_lenBox, ← guardCode_botDupocV_eq_instB] at h₁
  rw [lenBoxUnbounded_iff_lenBox, ← guardCode_botCupodV_eq_instB] at h₂
  exact ⟨botDupoc_search_V k h₁, botCupod_search_V k h₂⟩

/-- The box form of `pBD_both_V`. -/
theorem pBD_guards_V (k : V) (a : V)
    (ha : a + 8 * (formulaLen LAct (instB (⌜qBD⌝ : V) k) + formulaLen LAct (instB (⌜qBC⌝ : V) k)) + 7 ≤ k)
    (hpc : LenBoxUnbounded TAct a (instB (⌜pBD⌝ : V) k)) :
    LenBox TAct k (guardCode (⌜guardTemplate 0⌝ : V) (pBot (DupocV k)) (pBot (DupocV k))) ∧
    LenBox TAct k (guardCode (⌜guardTemplate 1⌝ : V) (pBot (CupodV k)) (pBot (CupodV k))) := by
  rw [instB_quote_pBD] at hpc
  have hx := isFormula_instB_quote qBD k
  have hy := isFormula_instB_quote qBC k
  have h₁ := lenBoxUnbounded_mono_V ha (lenBoxUnbounded_andL_V hx hy hpc)
  have h₂ := lenBoxUnbounded_mono_V ha (lenBoxUnbounded_andR_V hx hy hpc)
  rw [lenBoxUnbounded_iff_lenBox, ← guardCode_botDupocV_eq_instB] at h₁
  rw [lenBoxUnbounded_iff_lenBox, ← guardCode_botCupodV_eq_instB] at h₂
  exact ⟨h₁, h₂⟩

theorem eval_pBD_iff_std (k : V) :
    Semiformula.Eval (s := stdReadingV V) ![k] Empty.elim pBD ↔
      (∃ n, EvalGraph n (pBot (DupocV k)) (pBot (DupocV k)) (pBot (DupocV k)) 0) ∧
      (∃ n, EvalGraph n (pBot (CupodV k)) (pBot (CupodV k)) (pBot (CupodV k)) 1) := by
  rw [pBD_def]
  simp only [LogicalConnective.HomClass.map_and, LogicalConnective.Prop.and_eq]
  rw [eval_qBD_iff_V, eval_qBC_iff_V]

theorem eval_pBD_iff_swap (k : V) :
    Semiformula.Eval (s := swappedReading V) ![k] Empty.elim pBD ↔
      (∃ n, EvalGraph n (pBot (DupocV k)) (pBot (DupocV k)) (pBot (DupocV k)) 0) ∧
      (∃ n, EvalGraph n (pBot (CupodV k)) (pBot (CupodV k)) (pBot (CupodV k)) 1) := by
  rw [eval_swappedReading, lMap_swap_pBD, ← stdReadingV_eq_stdReading]
  simp only [LogicalConnective.HomClass.map_and, LogicalConnective.Prop.and_eq]
  rw [eval_qBD_iff_V, eval_qBC_iff_V, and_comm]

theorem eval_pBD_iff_stdReading (k : V) :
    Semiformula.Eval (s := stdReading V) ![k] Empty.elim pBD ↔
      (∃ n, EvalGraph n (pBot (DupocV k)) (pBot (DupocV k)) (pBot (DupocV k)) 0) ∧
      (∃ n, EvalGraph n (pBot (CupodV k)) (pBot (CupodV k)) (pBot (CupodV k)) 1) := by
  rw [← stdReadingV_eq_stdReading]; exact eval_pBD_iff_std k

/-- **The bounded Löb premise of the bot-wrapped self-play family, slack `(7, 8)`.** -/
theorem loebSound_pBD : LoebSound pBD 7 8 := by
  intro V _ _ k a ha h
  have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
  have ha' : a + 8 * (formulaLen LAct (instB (⌜qBD⌝ : V) k) + formulaLen LAct (instB (⌜qBC⌝ : V) k)) + 7 ≤ k :=
    le_trans (pConj_slack_le a _ _ _ (formulaLen_instB_pBD k)) ha
  obtain ⟨h1, h2⟩ := pBD_both_V k a ha' h
  exact ⟨(eval_pBD_iff_stdReading k).mpr ⟨⟨3, h1⟩, ⟨3, h2⟩⟩, (eval_pBD_iff_swap k).mpr ⟨⟨3, h1⟩, ⟨3, h2⟩⟩⟩

/-! #### The cells at ℕ -/

/-- **The bot-wrapped self-play cells, packaged**: for all large `k`, both bot-wrapped searchers
find their guards (fuel 3) and both guard boxes hold — `family_found pBD`, the arithmetized
`loeb_botDupoc_vs_botDupoc_of_nec`. -/
theorem loeb_botDupoc_vs_botDupoc_core_of_nec {d : ℕ} (hE : BoundedInnerNec d) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      (EvalGraph 3 (pBot (Dupoc k)) (pBot (Dupoc k)) (pBot (Dupoc k)) 0 ∧
        EvalGraph 3 (pBot (Cupod k)) (pBot (Cupod k)) (pBot (Cupod k)) 1) ∧
      (LenBox TAct k (guardCode (⌜guardTemplate 0⌝ : ℕ) (pBot (Dupoc k)) (pBot (Dupoc k))) ∧
        LenBox TAct k (guardCode (⌜guardTemplate 1⌝ : ℕ) (pBot (Cupod k)) (pBot (Cupod k)))) := by
  obtain ⟨k₀, h⟩ := family_found pBD hE loebSound_pBD
  refine ⟨k₀, fun k hk ↦ ?_⟩
  obtain ⟨a, ha, hpc⟩ := h k hk
  have ha' := le_def.mpr (pConj_slack_nat a _ _ _ k (formulaLen_instB_pBD (V := ℕ) k) ha)
  exact ⟨pBD_both_V k a ha' hpc, pBD_guards_V k a ha' hpc⟩

/-- **The bot-wrapped Dupoc cooperates with itself in PA-`S'`** (the engine's
`loeb_botDupoc_vs_botDupoc_of_nec`), conditional on bounded inner necessitation: fuel 3. -/
theorem loeb_botDupoc_vs_botDupoc_of_nec {d : ℕ} (hE : BoundedInnerNec d) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k → EvalGraph 3 (pBot (Dupoc k)) (pBot (Dupoc k)) (pBot (Dupoc k)) 0 := by
  obtain ⟨k₀, h⟩ := loeb_botDupoc_vs_botDupoc_core_of_nec hE
  exact ⟨k₀, fun k hk ↦ (h k hk).1.1⟩

theorem loeb_botCupod_vs_botCupod_of_nec {d : ℕ} (hE : BoundedInnerNec d) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k → EvalGraph 3 (pBot (Cupod k)) (pBot (Cupod k)) (pBot (Cupod k)) 1 := by
  obtain ⟨k₀, h⟩ := loeb_botDupoc_vs_botDupoc_core_of_nec hE
  exact ⟨k₀, fun k hk ↦ (h k hk).1.2⟩

/-- **The box form**: for all large `k`, the bot-wrapped Dupoc FINDS a proof of its guard against
itself within its budget `k` (conditional). -/
theorem loeb_botDupoc_vs_botDupoc_guard_of_nec {d : ℕ} (hE : BoundedInnerNec d) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      LenBox TAct k (guardCode (⌜guardTemplate 0⌝ : ℕ) (pBot (Dupoc k)) (pBot (Dupoc k))) := by
  obtain ⟨k₀, h⟩ := loeb_botDupoc_vs_botDupoc_core_of_nec hE
  exact ⟨k₀, fun k hk ↦ (h k hk).2.1⟩

/-- **The bot-wrapped Dupoc self-cooperation in PA-`S'`, unconditional**: for all large `k`,
`pBot (Dupoc k)` cooperates with itself at fuel 3 (bot, search, const). -/
theorem loeb_botDupoc_vs_botDupoc :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k → EvalGraph 3 (pBot (Dupoc k)) (pBot (Dupoc k)) (pBot (Dupoc k)) 0 :=
  loeb_botDupoc_vs_botDupoc_of_nec boundedInnerNec_sixteen

/-- **The bot-wrapped Cupod self-defection in PA-`S'`, unconditional.** -/
theorem loeb_botCupod_vs_botCupod :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k → EvalGraph 3 (pBot (Cupod k)) (pBot (Cupod k)) (pBot (Cupod k)) 1 :=
  loeb_botCupod_vs_botCupod_of_nec boundedInnerNec_sixteen

/-- **The bot-wrapped Dupoc finds its guard, unconditional.** -/
theorem loeb_botDupoc_vs_botDupoc_guard :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      LenBox TAct k (guardCode (⌜guardTemplate 0⌝ : ℕ) (pBot (Dupoc k)) (pBot (Dupoc k))) :=
  loeb_botDupoc_vs_botDupoc_guard_of_nec boundedInnerNec_sixteen

end botSelf
/-! ### 5. JustV: the searcher on the pre-filled template -/

section just

/-- The pre-filled substitution vector: the description of `pBot (DupocV k)` in the me-slots,
the frame variables `^#3 ^#4 ^#5` in the opp-slots. -/
noncomputable def jVec (k : V) : V :=
  codeTerm (canonical (pBot (DupocV k))) ∷ revalueU (pBot (DupocV k)) ∷ revalueW (pBot (DupocV k)) ∷ ^#3 ∷ ^#4 ∷ ^#5 ∷ 0

/-- **Just's stored template**: `guardTemplate 0` with its me-slots pre-filled by the closed description
of `pBot (DupocV k)` — "the opponent plays C against `pBot (Dupoc k)`". -/
noncomputable def gJ (k : V) : V := subst LAct (jVec k) (⌜guardTemplate 0⌝ : V)

/-- **JustBot in every model**: `pSearch k (gJ k) (pConst 0) (pConst 1)`. -/
noncomputable def JustV (k : V) : V := pSearch k (gJ k) (pConst 0) (pConst 1)

lemma jVec_semitermVec (k : V) : IsSemitermVec LAct 6 6 (jVec k) := by
  have h3 : IsSemiterm LAct 6 (^#3 : V) := IsSemiterm.bvar.mpr (by norm_num)
  have h4 : IsSemiterm LAct 6 (^#4 : V) := IsSemiterm.bvar.mpr (by norm_num)
  have h5 : IsSemiterm LAct 6 (^#5 : V) := IsSemiterm.bvar.mpr (by norm_num)
  have := ((((((IsSemitermVec.nil 6).adjoin h5).adjoin h4).adjoin h3).adjoin (revalueW_semiterm 6 (pBot (DupocV k)))).adjoin
    (revalueU_semiterm 6 (pBot (DupocV k)))).adjoin (codeTerm_semiterm_LAct 6 (canonical (pBot (DupocV k))))
  rwa [← six_eq] at this


/-- Filling the frame variables of `jVec k` with the descriptions of `(me, opp)` gives the
description vector of `(pBot (DupocV k), opp)`: the frame's `me` is unused. -/
theorem termSubstVec_jVec (k me opp : V) :
    termSubstVec LAct 6 (descriptions me opp) (jVec k) = descriptions (pBot (DupocV k)) opp := by
  have hT : IsUTerm LAct (codeTerm (canonical (pBot (DupocV k)))) := (codeTerm_semiterm_LAct 6 _).isUTerm
  have hU : IsUTerm LAct (revalueU (pBot (DupocV k))) := (revalueU_semiterm 6 _).isUTerm
  have hW : IsUTerm LAct (revalueW (pBot (DupocV k))) := (revalueW_semiterm 6 _).isUTerm
  have h3 : IsUTerm LAct (^#3 : V) := (IsSemiterm.bvar.mpr (by norm_num : (3 : V) < 6)).isUTerm
  have h4 : IsUTerm LAct (^#4 : V) := (IsSemiterm.bvar.mpr (by norm_num : (4 : V) < 6)).isUTerm
  have h5 : IsUTerm LAct (^#5 : V) := (IsSemiterm.bvar.mpr (by norm_num : (5 : V) < 6)).isUTerm
  have e0 : IsUTermVec LAct 0 (0 : V) := IsUTermVec.empty
  have e1 := e0.adjoin h5
  have e2 := e1.adjoin h4
  have e3 := e2.adjoin h3
  have e4 := e3.adjoin hW
  have e5 := e4.adjoin hU
  unfold jVec
  rw [six_eq, termSubstVec_cons hT e5, termSubstVec_cons hU e4, termSubstVec_cons hW e3,
    termSubstVec_cons h3 e2, termSubstVec_cons h4 e1, termSubstVec_cons h5 e0, termSubstVec_nil,
    termSubst_closed _ (codeTerm_semiterm_LAct 0 _), termSubst_closed _ (revalueU_semiterm 0 _),
    termSubst_closed _ (revalueW_semiterm 0 _), termSubst_bvar, termSubst_bvar, termSubst_bvar,
    nth_descriptions_three, nth_descriptions_four, nth_descriptions_five]
  rfl

/-- **Just's guard is Dupoc-in-bot's guard**: in the frame `(me, opp)`, `JustV k` searches exactly
what `pBot (DupocV k)` searches in the frame `(pBot (DupocV k), opp)` — "`opp` plays C against
`pBot (Dupoc k)`", the frame's `me` unused (the engine's `Formula.subst` on
`.plays .opp (.bot (DupocBot k)) C`). -/
theorem guardCode_JustV (k me opp : V) :
    guardCode (gJ k) me opp = guardCode (⌜guardTemplate 0⌝ : V) (pBot (DupocV k)) opp := by
  have hg0 : IsSemiformula LAct 6 (⌜guardTemplate 0⌝ : V) := by
    simpa using Sentence.quote_isSemiformula (V := V) (guardTemplate 0)
  unfold guardCode gJ
  rw [substs_substs hg0 (descriptions_semitermVec me opp) (jVec_semitermVec k), termSubstVec_jVec]

/-- **Just's search clause in every model** (fuel 2): if "`opp` plays C against `pBot (Dupoc k)`"
is provable within `k`, `JustV k` cooperates with `opp`. -/
theorem just_search_V (k opp : V) :
    LenBox TAct k (guardCode (⌜guardTemplate 0⌝ : V) (pBot (DupocV k)) opp) →
      EvalGraph 2 (JustV k) opp (JustV k) 0 := by
  intro h
  rw [show (2 : V) = 1 + 1 from one_add_one_eq_two.symm]
  show EvalGraph (1 + 1) (JustV k) opp (pSearch k (gJ k) (pConst 0) (pConst 1)) 0
  have hgJ : IsSemiformula LAct 6 (gJ k) := (isSemiformula_quote₆ (guardTemplate 0)).subst (jVec_semitermVec k)
  rw [EvalGraph.search_iff₆ hgJ, guardCode_JustV]
  left
  refine ⟨h, ?_⟩
  rw [show (1 : V) = 0 + 1 by simp, EvalGraph.const_iff]

/-! #### The meta template at ℕ -/

/-- **Just's template as a meta sentence** (`ℕ`): `guardTemplate 0` with the me-slots filled by the closed
description terms of `pBot (Dupoc k)` and the opp-slots kept as the frame variables. -/
noncomputable def guardTemplateJust (k : ℕ) : Semisentence LAct 6 :=
  guardTemplate 0 ⇜ ![cl (canonicalMeta (pBot (Dupoc k))), cl (revalueUMeta (pBot (Dupoc k))), cl (revalueWMeta (pBot (Dupoc k))), #3, #4, #5]

/-- **JustBot at ℕ**: the searcher of budget `k` on the template `⌜guardTemplateJust k⌝`. -/
noncomputable def Just (k : ℕ) : ℕ := pSearch k (⌜guardTemplateJust k⌝ : ℕ) (pConst 0) (pConst 1)

lemma quote_emb_cl6_canonicalMeta (x : ℕ) :
    (⌜(Rew.emb (cl (canonicalMeta x) : Semiterm LAct Empty 6) : SyntacticSemiterm LAct 6)⌝ : ℕ) = codeTerm (canonical x) := by
  rw [quote_emb_cl, ← Semiterm.empty_quote_def, quote_canonicalMeta]

lemma quote_emb_cl6_revalueUMeta (x : ℕ) :
    (⌜(Rew.emb (cl (revalueUMeta x) : Semiterm LAct Empty 6) : SyntacticSemiterm LAct 6)⌝ : ℕ) = revalueU x := by
  rw [quote_emb_cl, ← Semiterm.empty_quote_def, quote_revalueUMeta]

lemma quote_emb_cl6_revalueWMeta (x : ℕ) :
    (⌜(Rew.emb (cl (revalueWMeta x) : Semiterm LAct Empty 6) : SyntacticSemiterm LAct 6)⌝ : ℕ) = revalueW x := by
  rw [quote_emb_cl, ← Semiterm.empty_quote_def, quote_revalueWMeta]

lemma quote_emb_bvar6 (i : Fin 6) :
    (⌜(Rew.emb (#i : Semiterm LAct Empty 6) : SyntacticSemiterm LAct 6)⌝ : ℕ) = ^#(i : ℕ) := by
  simp [Rew.emb]

/-- **The code of the meta template is the internal pre-filled template.** -/
theorem quote_guardTemplateJust (k : ℕ) : (⌜guardTemplateJust k⌝ : ℕ) = gJ k := by
  unfold guardTemplateJust gJ
  rw [Sentence.quote_def, Semiformula.coe_subst_eq_subst_coe, Semiformula.quote_def,
    Semiformula.typed_quote_substs, Bootstrapping.Semiformula.val_substs, ← Semiformula.quote_def,
    ← Sentence.quote_def]
  congr 1
  have hv : (fun i ↦ (⌜(Rew.emb ((![cl (canonicalMeta (pBot (Dupoc k))), cl (revalueUMeta (pBot (Dupoc k))), cl (revalueWMeta (pBot (Dupoc k))),
      #3, #4, #5] : Fin 6 → Semiterm LAct Empty 6) i) : SyntacticSemiterm LAct 6)⌝ : Bootstrapping.Semiterm ℕ LAct 6)) =
      ![⌜(Rew.emb (cl (canonicalMeta (pBot (Dupoc k))) : Semiterm LAct Empty 6) : SyntacticSemiterm LAct 6)⌝,
        ⌜(Rew.emb (cl (revalueUMeta (pBot (Dupoc k))) : Semiterm LAct Empty 6) : SyntacticSemiterm LAct 6)⌝,
        ⌜(Rew.emb (cl (revalueWMeta (pBot (Dupoc k))) : Semiterm LAct Empty 6) : SyntacticSemiterm LAct 6)⌝,
        ⌜(Rew.emb (#3 : Semiterm LAct Empty 6) : SyntacticSemiterm LAct 6)⌝,
        ⌜(Rew.emb (#4 : Semiterm LAct Empty 6) : SyntacticSemiterm LAct 6)⌝,
        ⌜(Rew.emb (#5 : Semiterm LAct Empty 6) : SyntacticSemiterm LAct 6)⌝] := by
    funext i; fin_cases i <;> rfl
  rw [hv]
  simp only [SemitermVec.val_cons, SemitermVec.val_nil]
  show (⌜(Rew.emb (cl (canonicalMeta (pBot (Dupoc k))) : Semiterm LAct Empty 6) : SyntacticSemiterm LAct 6)⌝ : ℕ) ∷
    (⌜(Rew.emb (cl (revalueUMeta (pBot (Dupoc k))) : Semiterm LAct Empty 6) : SyntacticSemiterm LAct 6)⌝ : ℕ) ∷
    (⌜(Rew.emb (cl (revalueWMeta (pBot (Dupoc k))) : Semiterm LAct Empty 6) : SyntacticSemiterm LAct 6)⌝ : ℕ) ∷
    (⌜(Rew.emb (#3 : Semiterm LAct Empty 6) : SyntacticSemiterm LAct 6)⌝ : ℕ) ∷
    (⌜(Rew.emb (#4 : Semiterm LAct Empty 6) : SyntacticSemiterm LAct 6)⌝ : ℕ) ∷
    (⌜(Rew.emb (#5 : Semiterm LAct Empty 6) : SyntacticSemiterm LAct 6)⌝ : ℕ) ∷ 0 = jVec k
  rw [quote_emb_cl6_canonicalMeta, quote_emb_cl6_revalueUMeta, quote_emb_cl6_revalueWMeta, quote_emb_bvar6, quote_emb_bvar6, quote_emb_bvar6]
  rfl

/-- **The bridge**: `JustV` at `V = ℕ` is `Just`. -/
theorem JustV_nat (k : ℕ) : JustV (V := ℕ) k = Just k := by
  unfold JustV Just
  rw [quote_guardTemplateJust]

end just
/-! ### 6. Family (3): Just × Mirror -/

section justMirror

/-- **The fixed formula of Just's guard against Mirror**: "Mirror plays C against
`pBot (Dupoc k)`" — `guardTemplate 0` with the bot tower in the me-slots and Mirror's closed description
in the opp-slots. -/
noncomputable def qJM : Semisentence LAct 1 :=
  guardTemplate 0 ⇜ ![TBD, cl uD, cl wD, cl TM, cl (numT 0), cl (numT 1)]

lemma qJM_eq : qJM = guardTemplate 0 ⇜ ![TBD, cl uD, cl wD, cl TM, cl (numT 0), cl (numT 1)] := rfl

/-- The transposition: "Mirror plays D against `pBot (Cupod k)`". -/
noncomputable def qJC : Semisentence LAct 1 := Semiformula.lMap swap qJM

lemma lMap_swap_qJM : Semiformula.lMap swap qJM = qJC := rfl

lemma lMap_swap_qJC : Semiformula.lMap swap qJC = qJM := lMap_swap_swap _

lemma termSubst_cl_TM (k : V) :
    termSubst LAct (binNumeral k ∷ (0 : V)) (⌜(Rew.emb (cl TM : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝ : V) =
      codeTerm (canonical MirrorV) := by
  rw [quote_emb_cl_V, termSubst_closed _ (semiterm_quote_emb₀ _), quote_emb_TM, canonical_MirrorV]

lemma quote_emb_numT_zero_revalueU : (⌜(Rew.emb (numT 0) : SyntacticSemiterm LAct 0)⌝ : V) = revalueU MirrorV := by
  rw [quote_emb_numT, revalueU_MirrorV, Nat.cast_zero]

lemma quote_emb_numT_one_revalueW : (⌜(Rew.emb (numT 1) : SyntacticSemiterm LAct 0)⌝ : V) = revalueW MirrorV := by
  rw [quote_emb_numT, revalueW_MirrorV, Nat.cast_one]

/-- **The instance equation on codes of Dupoc-in-bot's guard against Mirror, in every model.** -/
theorem guardCode_botDupocV_MirrorV_eq_instB (k : V) :
    guardCode (⌜guardTemplate 0⌝ : V) (pBot (DupocV k)) MirrorV = instB (⌜qJM⌝ : V) k :=
  guardCode_eq_instB_of 0 (termSubst_TBD k) (quote_emb_uD_botDupocV k) (quote_emb_wD_botDupocV k)
    (termSubst_cl_TM k) quote_emb_numT_zero_revalueU quote_emb_numT_one_revalueW

lemma revalueTemplate_quote_qJM_V : revalueTemplate 1 0 (⌜qJM⌝ : V) = ⌜qJC⌝ :=
  revalueTemplate_quote_sentence_V qJM

lemma guardCode_botCupodV_MirrorV_eq_revalue (k : V) :
    guardCode (⌜guardTemplate 1⌝ : V) (pBot (CupodV k)) MirrorV =
      revalueTemplate 1 0 (guardCode (⌜guardTemplate 0⌝ : V) (pBot (DupocV k)) MirrorV) := by
  have hg0 : IsSemiformula LAct 6 (⌜guardTemplate 0⌝ : V) := by
    simpa using Sentence.quote_isSemiformula (V := V) (guardTemplate 0)
  have hg1 : IsSemiformula LAct 6 (⌜guardTemplate 1⌝ : V) := by
    simpa using Sentence.quote_isSemiformula (V := V) (guardTemplate 1)
  rw [← substTemplate_of_template hg0, revalueTemplate_substTemplate, transposeCode_pBot_DupocV, transposeCode_MirrorV,
    revalueTemplate_quote_GtmplA_V, swapAction_zero, substTemplate_of_template hg1]

/-- **The instance equation on codes of Cupod-in-bot's guard against Mirror, in every model.** -/
theorem guardCode_botCupodV_MirrorV_eq_instB (k : V) :
    guardCode (⌜guardTemplate 1⌝ : V) (pBot (CupodV k)) MirrorV = instB (⌜qJC⌝ : V) k := by
  rw [guardCode_botCupodV_MirrorV_eq_revalue, guardCode_botDupocV_MirrorV_eq_instB]
  unfold instB
  rw [revalueTemplate_subst isAct_one isAct_zero (Sentence.quote_isSemiformul₁ qJM)
    (binNumeral_cons_semitermVec k), revalueTemplate_quote_qJM_V]
  congr 1
  rw [show (1 : V) = 0 + 1 by simp, termRelabelVec_cons (binNumeral_term_LAct k).isUTerm IsUTermVec.empty,
    termRelabelVec_nil, termRelabel_binNumeral]

/-! #### The truth equations -/

theorem qJC_eq : qJC = guardTemplate 1 ⇜ ![TBD, cl uC, cl wC, cl TM, cl (numT 0), cl (numT 1)] := by
  unfold qJC qJM
  rw [Semiformula.lMap_subst, lMap_swap_GtmplA, swapAction_zero]
  congr 1
  funext i
  fin_cases i <;> simp [lMap_swap_TBD, lMap_swap_cl, uC, wC, lMap_swap_TM, lMap_swap_numT]

/-- **The truth equation of Just's guard against Mirror** (standard reading): `qJM(k)` holds iff
Mirror plays `C` against `pBot (DupocV k)`. -/
theorem eval_qJM_iff_V (k : V) :
    Semiformula.Eval (s := stdReadingV V) ![k] Empty.elim qJM ↔
      ∃ n, EvalGraph n MirrorV (pBot (DupocV k)) MirrorV 0 := by
  rw [qJM_eq, eval_GtmplA_subst_iff]
  simp only [val_TBD_V, val_cl_V, val_TM_V, val_numT_V, Nat.cast_zero, Nat.cast_one, revalue_zero_one,
    canonical_pBot, revalue_bot, revalue_val_uD_wD_V]

/-- `qJC(k)` holds iff Mirror plays `D` against `pBot (CupodV k)`. -/
theorem eval_qJC_iff_V (k : V) :
    Semiformula.Eval (s := stdReadingV V) ![k] Empty.elim qJC ↔
      ∃ n, EvalGraph n MirrorV (pBot (CupodV k)) MirrorV 1 := by
  rw [qJC_eq, eval_GtmplA_subst_iff]
  simp only [val_TBD_V, val_cl_V, val_TM_V, val_numT_V, Nat.cast_zero, Nat.cast_one, revalue_zero_one,
    canonical_pBot, revalue_bot, revalue_val_uC_wC_V]

theorem eval_qJM_swap_iff_V (k : V) :
    Semiformula.Eval (s := swappedReading V) ![k] Empty.elim qJM ↔
      ∃ n, EvalGraph n MirrorV (pBot (CupodV k)) MirrorV 1 := by
  rw [eval_swappedReading, lMap_swap_qJM, ← stdReadingV_eq_stdReading]
  exact eval_qJC_iff_V k

theorem eval_qJC_swap_iff_V (k : V) :
    Semiformula.Eval (s := swappedReading V) ![k] Empty.elim qJC ↔
      ∃ n, EvalGraph n MirrorV (pBot (DupocV k)) MirrorV 0 := by
  rw [eval_swappedReading, lMap_swap_qJC, ← stdReadingV_eq_stdReading]
  exact eval_qJM_iff_V k

/-! #### The search clauses and Mirror's copy -/

/-- **Dupoc-in-bot's search clause against Mirror** (fuel 3). -/
theorem botDupoc_mirror_search_V (k : V) :
    LenBox TAct k (guardCode (⌜guardTemplate 0⌝ : V) (pBot (DupocV k)) MirrorV) →
      EvalGraph 3 (pBot (DupocV k)) MirrorV (pBot (DupocV k)) 0 :=
  botDupoc_frame_search_V k _ _

theorem botCupod_mirror_search_V (k : V) :
    LenBox TAct k (guardCode (⌜guardTemplate 1⌝ : V) (pBot (CupodV k)) MirrorV) →
      EvalGraph 3 (pBot (CupodV k)) MirrorV (pBot (CupodV k)) 1 :=
  botCupod_frame_search_V k _ _

/-- Mirror copies the bot-wrapped Dupoc: C at fuel 3 ⇒ Mirror plays C at fuel 4. -/
theorem mirror_copies_botDupoc_V (k : V) (h : EvalGraph 3 (pBot (DupocV k)) MirrorV (pBot (DupocV k)) 0) :
    EvalGraph 4 MirrorV (pBot (DupocV k)) MirrorV 0 := by
  rw [show (4 : V) = 3 + 1 from three_add_one_eq_four.symm]
  exact (mirror_step_V 3 (pBot (DupocV k)) 0).mpr h

theorem mirror_copies_botCupod_V (k : V) (h : EvalGraph 3 (pBot (CupodV k)) MirrorV (pBot (CupodV k)) 1) :
    EvalGraph 4 MirrorV (pBot (CupodV k)) MirrorV 1 := by
  rw [show (4 : V) = 3 + 1 from three_add_one_eq_four.symm]
  exact (mirror_step_V 3 (pBot (CupodV k)) 1).mpr h

/-! #### The conjunction family -/

/-- **The Löb family of the Just × Mirror cell.** -/
noncomputable def pJM : Semisentence LAct 1 := qJM ⋏ qJC

lemma pJM_def : pJM = qJM ⋏ qJC := rfl

lemma lMap_swap_pJM : Semiformula.lMap swap pJM = qJC ⋏ qJM := by
  rw [pJM_def, LogicalConnective.HomClass.map_and, lMap_swap_qJM, lMap_swap_qJC]

theorem instB_quote_pJM (k : V) :
    instB (⌜pJM⌝ : V) k = instB (⌜qJM⌝ : V) k ^⋏ instB (⌜qJC⌝ : V) k :=
  instB_quote_and qJM qJC k

lemma formulaLen_instB_pJM (k : V) :
    formulaLen LAct (instB (⌜pJM⌝ : V) k) =
      formulaLen LAct (instB (⌜qJM⌝ : V) k) + formulaLen LAct (instB (⌜qJC⌝ : V) k) + 1 := by
  rw [instB_quote_pJM,
    formulaLen_and (isFormula_instB_quote qJM k).isUFormula (isFormula_instB_quote qJC k).isUFormula]

/-- **Both bot-wrapped searchers find their guards against Mirror from a box of the conjunction**
(fuel 3). -/
theorem pJM_both_V (k : V) : ∀ a : V,
    a + 8 * (formulaLen LAct (instB (⌜qJM⌝ : V) k) + formulaLen LAct (instB (⌜qJC⌝ : V) k)) + 7 ≤ k →
    LenBoxUnbounded TAct a (instB (⌜pJM⌝ : V) k) →
    EvalGraph 3 (pBot (DupocV k)) MirrorV (pBot (DupocV k)) 0 ∧
      EvalGraph 3 (pBot (CupodV k)) MirrorV (pBot (CupodV k)) 1 := by
  intro a ha h
  rw [instB_quote_pJM] at h
  have hx := isFormula_instB_quote qJM k
  have hy := isFormula_instB_quote qJC k
  have h₁ := lenBoxUnbounded_mono_V ha (lenBoxUnbounded_andL_V hx hy h)
  have h₂ := lenBoxUnbounded_mono_V ha (lenBoxUnbounded_andR_V hx hy h)
  rw [lenBoxUnbounded_iff_lenBox, ← guardCode_botDupocV_MirrorV_eq_instB] at h₁
  rw [lenBoxUnbounded_iff_lenBox, ← guardCode_botCupodV_MirrorV_eq_instB] at h₂
  exact ⟨botDupoc_mirror_search_V k h₁, botCupod_mirror_search_V k h₂⟩

/-- The box form of `pJM_both_V`. -/
theorem pJM_guards_V (k : V) (a : V)
    (ha : a + 8 * (formulaLen LAct (instB (⌜qJM⌝ : V) k) + formulaLen LAct (instB (⌜qJC⌝ : V) k)) + 7 ≤ k)
    (hpc : LenBoxUnbounded TAct a (instB (⌜pJM⌝ : V) k)) :
    LenBox TAct k (guardCode (⌜guardTemplate 0⌝ : V) (pBot (DupocV k)) MirrorV) ∧
    LenBox TAct k (guardCode (⌜guardTemplate 1⌝ : V) (pBot (CupodV k)) MirrorV) := by
  rw [instB_quote_pJM] at hpc
  have hx := isFormula_instB_quote qJM k
  have hy := isFormula_instB_quote qJC k
  have h₁ := lenBoxUnbounded_mono_V ha (lenBoxUnbounded_andL_V hx hy hpc)
  have h₂ := lenBoxUnbounded_mono_V ha (lenBoxUnbounded_andR_V hx hy hpc)
  rw [lenBoxUnbounded_iff_lenBox, ← guardCode_botDupocV_MirrorV_eq_instB] at h₁
  rw [lenBoxUnbounded_iff_lenBox, ← guardCode_botCupodV_MirrorV_eq_instB] at h₂
  exact ⟨h₁, h₂⟩

theorem eval_pJM_iff_std (k : V) :
    Semiformula.Eval (s := stdReadingV V) ![k] Empty.elim pJM ↔
      (∃ n, EvalGraph n MirrorV (pBot (DupocV k)) MirrorV 0) ∧
      (∃ n, EvalGraph n MirrorV (pBot (CupodV k)) MirrorV 1) := by
  rw [pJM_def]
  simp only [LogicalConnective.HomClass.map_and, LogicalConnective.Prop.and_eq]
  rw [eval_qJM_iff_V, eval_qJC_iff_V]

theorem eval_pJM_iff_swap (k : V) :
    Semiformula.Eval (s := swappedReading V) ![k] Empty.elim pJM ↔
      (∃ n, EvalGraph n MirrorV (pBot (DupocV k)) MirrorV 0) ∧
      (∃ n, EvalGraph n MirrorV (pBot (CupodV k)) MirrorV 1) := by
  rw [eval_swappedReading, lMap_swap_pJM, ← stdReadingV_eq_stdReading]
  simp only [LogicalConnective.HomClass.map_and, LogicalConnective.Prop.and_eq]
  rw [eval_qJM_iff_V, eval_qJC_iff_V, and_comm]

theorem eval_pJM_iff_stdReading (k : V) :
    Semiformula.Eval (s := stdReading V) ![k] Empty.elim pJM ↔
      (∃ n, EvalGraph n MirrorV (pBot (DupocV k)) MirrorV 0) ∧
      (∃ n, EvalGraph n MirrorV (pBot (CupodV k)) MirrorV 1) := by
  rw [← stdReadingV_eq_stdReading]; exact eval_pJM_iff_std k

/-- **The bounded Löb premise of the Just × Mirror family, slack `(7, 8)`**: a proof of `pJM(k)`
within the budget makes both bot-wrapped searchers find their guards against Mirror, Mirror
COPIES at fuel 4, and `pJM(k)` is true in both readings. -/
theorem loebSound_pJM : LoebSound pJM 7 8 := by
  intro V _ _ k a ha h
  have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
  have ha' : a + 8 * (formulaLen LAct (instB (⌜qJM⌝ : V) k) + formulaLen LAct (instB (⌜qJC⌝ : V) k)) + 7 ≤ k :=
    le_trans (pConj_slack_le a _ _ _ (formulaLen_instB_pJM k)) ha
  obtain ⟨h1, h2⟩ := pJM_both_V k a ha' h
  exact ⟨(eval_pJM_iff_stdReading k).mpr ⟨⟨4, mirror_copies_botDupoc_V k h1⟩, ⟨4, mirror_copies_botCupod_V k h2⟩⟩,
    (eval_pJM_iff_swap k).mpr ⟨⟨4, mirror_copies_botDupoc_V k h1⟩, ⟨4, mirror_copies_botCupod_V k h2⟩⟩⟩

/-! #### The cells at ℕ -/

/-- **The Just × Mirror family, packaged**: for all large `k`, both bot-wrapped searchers find
their guards against Mirror (fuel 3) and both guard boxes hold — `family_found pJM`, the
arithmetized `jm_guard_true`. -/
theorem loeb_Just_vs_Mirror_core_of_nec {d : ℕ} (hE : BoundedInnerNec d) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      (EvalGraph 3 (pBot (Dupoc k)) Mirror (pBot (Dupoc k)) 0 ∧
        EvalGraph 3 (pBot (Cupod k)) Mirror (pBot (Cupod k)) 1) ∧
      (LenBox TAct k (guardCode (⌜guardTemplate 0⌝ : ℕ) (pBot (Dupoc k)) Mirror) ∧
        LenBox TAct k (guardCode (⌜guardTemplate 1⌝ : ℕ) (pBot (Cupod k)) Mirror)) := by
  obtain ⟨k₀, h⟩ := family_found pJM hE loebSound_pJM
  refine ⟨k₀, fun k hk ↦ ?_⟩
  obtain ⟨a, ha, hpc⟩ := h k hk
  have ha' := le_def.mpr (pConj_slack_nat a _ _ _ k (formulaLen_instB_pJM (V := ℕ) k) ha)
  exact ⟨pJM_both_V k a ha' hpc, pJM_guards_V k a ha' hpc⟩

/-- **Just × Mirror is `(C, C)` in PA-`S'`, conditional on bounded inner necessitation**: for all
large `k`, `Just k` cooperates with Mirror (fuel 2: Just's OUTER search fires on the box of
"Mirror plays C against `pBot (Dupoc k)`") and Mirror copies (fuel 3). -/
theorem loeb_Just_vs_Mirror_of_nec {d : ℕ} (hE : BoundedInnerNec d) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 2 (Just k) Mirror (Just k) 0 ∧ EvalGraph 3 Mirror (Just k) Mirror 0 := by
  obtain ⟨k₀, h⟩ := loeb_Just_vs_Mirror_core_of_nec hE
  refine ⟨k₀, fun k hk ↦ ?_⟩
  have hJ : EvalGraph 2 (JustV (V := ℕ) k) Mirror (JustV (V := ℕ) k) 0 := just_search_V k Mirror (h k hk).2.1
  rw [JustV_nat] at hJ
  exact ⟨hJ, (mirror_step_V (V := ℕ) 2 (Just k) 0).mpr hJ⟩

/-- **The bot-wrapped Dupoc × Mirror `(C, C)`, conditional**: fuel 3 for `pBot (Dupoc k)`, fuel 4
for Mirror. -/
theorem loeb_botDupoc_vs_Mirror_of_nec {d : ℕ} (hE : BoundedInnerNec d) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 3 (pBot (Dupoc k)) Mirror (pBot (Dupoc k)) 0 ∧ EvalGraph 4 Mirror (pBot (Dupoc k)) Mirror 0 := by
  obtain ⟨k₀, h⟩ := loeb_Just_vs_Mirror_core_of_nec hE
  exact ⟨k₀, fun k hk ↦ ⟨(h k hk).1.1, mirror_copies_botDupoc_V (V := ℕ) k (h k hk).1.1⟩⟩

/-- **The box form**: for all large `k`, Just actually FINDS a proof of its guard against Mirror
within its budget `k` (conditional). -/
theorem loeb_Just_vs_Mirror_guard_of_nec {d : ℕ} (hE : BoundedInnerNec d) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k → LenBox TAct k (guardCode (gJ k) (Just k) Mirror) := by
  obtain ⟨k₀, h⟩ := loeb_Just_vs_Mirror_core_of_nec hE
  refine ⟨k₀, fun k hk ↦ ?_⟩
  rw [guardCode_JustV]
  exact (h k hk).2.1

/-- **Just × Mirror `(C, C)` in PA-`S'`, unconditional**: for all large `k`, `Just k` cooperates
with Mirror (fuel 2) and Mirror copies (fuel 3). -/
theorem loeb_Just_vs_Mirror :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 2 (Just k) Mirror (Just k) 0 ∧ EvalGraph 3 Mirror (Just k) Mirror 0 :=
  loeb_Just_vs_Mirror_of_nec boundedInnerNec_sixteen

/-- **The bot-wrapped Dupoc × Mirror `(C, C)`, unconditional.** -/
theorem loeb_botDupoc_vs_Mirror :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 3 (pBot (Dupoc k)) Mirror (pBot (Dupoc k)) 0 ∧ EvalGraph 4 Mirror (pBot (Dupoc k)) Mirror 0 :=
  loeb_botDupoc_vs_Mirror_of_nec boundedInnerNec_sixteen

/-- **Just finds its guard against Mirror, unconditional.** -/
theorem loeb_Just_vs_Mirror_guard :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k → LenBox TAct k (guardCode (gJ k) (Just k) Mirror) :=
  loeb_Just_vs_Mirror_guard_of_nec boundedInnerNec_sixteen

end justMirror

end ArithS
