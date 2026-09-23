import ArithS.Cells.DupocMirror

/-!
# ArithS.Cells.JustBot — the frozen-`.bot` Löb families in PA-`S'`

`Research/Notes/ROUTE_B_SCOPE.md` §3 Phase 2 (2026-09-23), the JustBot family. The engine's
`JustBot k := .search k (.plays .opp (.bot (DupocBot k)) C) (.const C) (.const D)` — "cooperate
iff I can prove the opponent cooperates with a FROZEN snapshot of Dupoc k". Every JustBot cell
rests on the bot-wrapped Dupoc self-cooperation (`Theorems/JustBot/Helpers.botDupoc_self_coop`).
V-generic (every model of `𝗜𝚺₁`, budgets `k : V` possibly nonstandard) unless a statement says `ℕ`.

1. **Bot-wrapping.** `pBot p` runs `p` in the SAME frame (`EvalGraph.bot_iff`) and is FROZEN under
   `psubst`; `pBot` is strictly monotone, so the canonical description commutes with it
   (`dnum_pBot`, `dU_pBot`, `dW_pBot`; `swapcode_pBot`). Dupoc's search clause holds in ANY frame
   (`dupoc_frame_search_V`): `pBot (DupocV k)` in the frame `(me, opp)` searches
   `guardCode ⌜GtmplA 0⌝ me opp` — so the guards below are those of the FRAME players.
2. **The description tower.** `TBD := lMap emb (botT1 (searchT1 gD pD qD))` is the one-variable
   description of `pBot (Dupoc k)` (`botT1 t = succT1 (ppairT1 3̂ t)`, `ProgT.progT_bot`);
   `val_TBD_V : TBD(k) = dnum (pBot (DupocV k))`, `termSubst_TBD : (bnum k)-instance of ⌜TBD⌝ =
   progT (dnum (pBot (DupocV k)))`.
3. **The generic instance equation and truth equation** for a template instance
   `GtmplA a ⇜ ![T₁, cl u₁, cl w₁, T₂, cl u₂, cl w₂]` (`guardCode_eq_instB_of`,
   `eval_GtmplA_subst_iff`): the six per-cell substitution computations of `InstanceV`/
   `Cells/DupocMirror` factored once.
4. **Family (1): the bot-wrapped self-play** `pBD := qBD ⋏ qBC` (`qBD = GtmplA 0 ⇜ ![TBD, cl uD, cl wD,
   TBD, cl uD, cl wD]`, `qBC = lMap swap qBD`): `botDupoc_self_coop_unconditional` — for all large
   `k`, `EvalGraph 3 (pBot (Dupoc k)) (pBot (Dupoc k)) (pBot (Dupoc k)) 0` (fuel 3: bot, search,
   const) — and `botCupod_self_defect_unconditional`.
5. **JustV.** `JustV k := pSearch k (gJ k) (pConst 0) (pConst 1)` with the stored template
   `gJ k := subst (jVec k) ⌜GtmplA 0⌝` — `GtmplA 0` PRE-FILLED in its me-slots with the closed
   description of `pBot (DupocV k)`, the opp-slots left as the frame variables `^#3 ^#4 ^#5`.
   `guardCode_JustV : guardCode (gJ k) me opp = guardCode ⌜GtmplA 0⌝ (pBot (DupocV k)) opp` — Just's
   guard against `opp` IS the guard of Dupoc-in-bot against `opp` (the frame's `me` is unused,
   exactly the engine's `Formula.subst` on `.plays .opp (.bot (DupocBot k)) C`). At ℕ, `Just k :=
   pSearch k ⌜GtmplJ k⌝ …` with the meta template `GtmplJ k` and the bridge `JustV_nat`.
6. **Family (3): Just × Mirror** `pJM := qJM ⋏ qJM'` (`qJM = GtmplA 0 ⇜ ![TBD, cl uD, cl wD, cl TM,
   cl (numT 0), cl (numT 1)]`, "Mirror plays C against `pBot (Dupoc k)`"): a proof of `qJM(k)` within
   budget makes Dupoc-in-bot cooperate with Mirror (fuel 3), Mirror copies (fuel 4), so it is true;
   `family_found pJM` then fires Just's OUTER search by the same box:
   `just_mirror_coop_unconditional` — `EvalGraph 2 (Just k) Mirror (Just k) 0 ∧ EvalGraph 3 Mirror
   (Just k) Mirror 0`, the `(C, C)` cell.

**Not here — Just × Just and Just × Dupoc (the engine's `outcome_JustBot_vs_JustBot`,
`outcome_JustBot_vs_DupocBot`).** Both need a box of a sentence in which `Just k` itself is
DESCRIBED (Just's guard against Just is "Just k plays C against `pBot (Dupoc k)`"; Dupoc's guard
against Just is "Just k plays C against Dupoc k"). The description `progT (dnum (JustV k))`
carries the leaf `bnum (gJ k)` — the binary numeral of the stored template, whose bits depend on
`k` — so it is NOT the `bnum k`-instance of any fixed term, and no fixed one-variable formula has
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

/-- **Dupoc's search clause in ANY frame** (fuel 2): `DupocV k` run in the frame `(me, opp)` plays
`C` if `guardCode ⌜GtmplA 0⌝ me opp` is provable within `k`. -/
theorem dupoc_frame_search_V (k me opp : V) :
    LenProvableV TAct k (guardCode (⌜GtmplA 0⌝ : V) me opp) → EvalGraph 2 me opp (DupocV k) 0 := by
  intro h
  rw [show (2 : V) = 1 + 1 from one_add_one_eq_two.symm]
  show EvalGraph (1 + 1) me opp (pSearch k (⌜GtmplA 0⌝ : V) (pConst 0) (pConst 1)) 0
  rw [EvalGraph.search_iff]
  left
  refine ⟨h, ?_⟩
  rw [show (1 : V) = 0 + 1 by simp, EvalGraph.const_iff]

/-- **Cupod's search clause in ANY frame** (fuel 2). -/
theorem cupod_frame_search_V (k me opp : V) :
    LenProvableV TAct k (guardCode (⌜GtmplA 1⌝ : V) me opp) → EvalGraph 2 me opp (CupodV k) 1 := by
  intro h
  rw [show (2 : V) = 1 + 1 from one_add_one_eq_two.symm]
  show EvalGraph (1 + 1) me opp (pSearch k (⌜GtmplA 1⌝ : V) (pConst 1) (pConst 0)) 1
  rw [EvalGraph.search_iff]
  left
  refine ⟨h, ?_⟩
  have e : EvalGraph (0 + 1) me opp (pConst 1) 1 := EvalGraph.const_iff.mpr rfl
  rwa [zero_add] at e

/-- **The bot-wrapped Dupoc's search clause in any frame** (fuel 3: the bot step, the search step,
the constant). -/
theorem botDupoc_frame_search_V (k me opp : V) :
    LenProvableV TAct k (guardCode (⌜GtmplA 0⌝ : V) me opp) → EvalGraph 3 me opp (pBot (DupocV k)) 0 := by
  intro h
  rw [show (3 : V) = 2 + 1 from two_add_one_eq_three.symm, EvalGraph.bot_iff]
  exact dupoc_frame_search_V k me opp h

theorem botCupod_frame_search_V (k me opp : V) :
    LenProvableV TAct k (guardCode (⌜GtmplA 1⌝ : V) me opp) → EvalGraph 3 me opp (pBot (CupodV k)) 1 := by
  intro h
  rw [show (3 : V) = 2 + 1 from two_add_one_eq_three.symm, EvalGraph.bot_iff]
  exact cupod_frame_search_V k me opp h

end bot

/-! ### 2. The description tower of `pBot (Dupoc k)` -/

section tower

/-- The one-variable structural term of a bot-wrapped program. -/
noncomputable def botT1 (t : Semiterm ℒₒᵣ Empty 1) : Semiterm ℒₒᵣ Empty 1 :=
  succT1 (ppairT1 (Rew.bShift (bnumT 3)) t)

lemma val_botT1_V (t : Semiterm ℒₒᵣ Empty 1) (k : V) :
    (botT1 t).val (s := standardModel V) ![k] Empty.elim = pBot (t.val (s := standardModel V) ![k] Empty.elim) := by
  rw [botT1, val_succT1_V, val_ppairT1_V, val_bShift₁_V, val_bnumT_V]
  unfold pBot
  push_cast
  rfl

lemma quote_emb_botT1 (t : Semiterm ℒₒᵣ Empty 1) :
    (⌜(Rew.emb (botT1 t) : SyntacticSemiterm ℒₒᵣ 1)⌝ : V) =
    ppairT (bnum 3) (⌜(Rew.emb t : SyntacticSemiterm ℒₒᵣ 1)⌝ : V) ^+ 𝟏 := by
  rw [botT1, quote_emb_succT1, quote_emb_ppairT1, quote_emb_bShift, ← Semiterm.empty_quote_def, quote_bnumT]
  push_cast
  rfl

/-- **The one-variable description term of `pBot (Dupoc k)`**, over `LAct`. -/
noncomputable def TBD : Semiterm LAct Empty 1 := Semiterm.lMap emb (botT1 (searchT1 gD pD qD))

lemma lMap_swap_TBD : Semiterm.lMap swap TBD = TBD := term_lMap_swap_emb _

/-- `TBD` at the budget `k` denotes the canonical code of `pBot (DupocV k)`. -/
theorem val_TBD_V (k : V) : TBD.val (s := stdActV V) ![k] Empty.elim = dnum (pBot (DupocV k)) := by
  unfold TBD
  rw [Semiterm.val_lMap, stdActV_lMap_emb, val_botT1_V, val_searchT1_V, dnum_pBot, dnum_DupocV]

theorem quote_emb_TBD :
    (⌜(Rew.emb TBD : SyntacticSemiterm LAct 1)⌝ : V) =
    ppairT (bnum 3)
      (ppairT (bnum 6) (ppairT (^#0) (ppairT (bnum (gD : V)) (ppairT (progT (pD : V)) (progT (qD : V))))) ^+ 𝟏) ^+ 𝟏 := by
  unfold TBD
  rw [term_emb_lMap_emb_n, quote_term_lMap_emb, quote_emb_botT1, quote_emb_searchT1]

/-- **Filling the budget slot of the bot tower.** -/
theorem termSubst_TBD (k : V) :
    termSubst LAct (bnum k ∷ (0 : V)) (⌜(Rew.emb TBD : SyntacticSemiterm LAct 1)⌝ : V) =
      progT (dnum (pBot (DupocV k))) := by
  have hb3 : IsUTerm LAct (bnum (3 : V)) := (bnum_semiterm_LAct 0 _).isUTerm
  have hb6 : IsUTerm LAct (bnum (6 : V)) := (bnum_semiterm_LAct 0 _).isUTerm
  have hbg : IsUTerm LAct (bnum (gD : V)) := (bnum_semiterm_LAct 0 _).isUTerm
  have hp : IsUTerm LAct (progT (pD : V)) := (progT_semiterm_LAct 0 _).isUTerm
  have hq : IsUTerm LAct (progT (qD : V)) := (progT_semiterm_LAct 0 _).isUTerm
  have hone : IsUTerm LAct (𝟏 : V) := (IsSemiterm.LAct_of_LOR (one_semiterm (n := 0))).isUTerm
  have h1 : IsUTerm LAct (ppairT (progT (pD : V)) (progT (qD : V))) := ppairT_uterm_LAct hp hq
  have h2 : IsUTerm LAct (ppairT (bnum (gD : V)) (ppairT (progT (pD : V)) (progT (qD : V)))) := ppairT_uterm_LAct hbg h1
  have h3 : IsUTerm LAct (ppairT (^#0) (ppairT (bnum (gD : V)) (ppairT (progT (pD : V)) (progT (qD : V))))) :=
    ppairT_uterm_LAct bvar_zero_uterm h2
  have h4 : IsUTerm LAct (ppairT (bnum 6) (ppairT (^#0) (ppairT (bnum (gD : V)) (ppairT (progT (pD : V)) (progT (qD : V)))))) :=
    ppairT_uterm_LAct hb6 h3
  have h5 : IsUTerm LAct (ppairT (bnum 6) (ppairT (^#0) (ppairT (bnum (gD : V)) (ppairT (progT (pD : V)) (progT (qD : V))))) ^+ 𝟏) :=
    qqAdd_uterm_LAct h4 hone
  have h6 : IsUTerm LAct (ppairT (bnum 3)
      (ppairT (bnum 6) (ppairT (^#0) (ppairT (bnum (gD : V)) (ppairT (progT (pD : V)) (progT (qD : V))))) ^+ 𝟏)) :=
    ppairT_uterm_LAct hb3 h5
  rw [quote_emb_TBD, termSubst_qqAdd _ h6 hone, termSubst_ppairT _ hb3 h5,
    termSubst_closed _ (bnum_semiterm_LAct 0 _), termSubst_closed _ (IsSemiterm.LAct_of_LOR one_semiterm),
    termSubst_tower, dnum_pBot, dnum_DupocV, progT_bot]

end tower

/-! ### 3. The generic instance equation and truth equation of a template instance -/

section generic

/-- The six codes of the substituted terms of `GtmplA a ⇜ ![T₁, cl u₁, cl w₁, T₂, cl u₂, cl w₂]`,
as an internal vector. -/
noncomputable def tmplVec (T₁ T₂ : Semiterm LAct Empty 1) (u₁ w₁ u₂ w₂ : ClosedSemiterm LAct 0) : V :=
  (⌜(Rew.emb T₁ : SyntacticSemiterm LAct 1)⌝ : V) ∷
    ⌜(Rew.emb (cl u₁ : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝ ∷
    ⌜(Rew.emb (cl w₁ : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝ ∷
    ⌜(Rew.emb T₂ : SyntacticSemiterm LAct 1)⌝ ∷
    ⌜(Rew.emb (cl u₂ : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝ ∷
    ⌜(Rew.emb (cl w₂ : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝ ∷ 0

/-- The code of a template instance is the internal substitution of `tmplVec` into the template code. -/
theorem quote_GtmplA_subst (a : ℕ) (T₁ T₂ : Semiterm LAct Empty 1) (u₁ w₁ u₂ w₂ : ClosedSemiterm LAct 0) :
    (⌜(GtmplA a ⇜ ![T₁, cl u₁, cl w₁, T₂, cl u₂, cl w₂] : Semisentence LAct 1)⌝ : V) =
      subst LAct (tmplVec T₁ T₂ u₁ w₁ u₂ w₂) (⌜GtmplA a⌝ : V) := by
  rw [Sentence.quote_def, Semiformula.coe_subst_eq_subst_coe, Semiformula.quote_def,
    Semiformula.typed_quote_substs, Bootstrapping.Semiformula.val_substs, ← Semiformula.quote_def,
    ← Sentence.quote_def]
  congr 1

lemma tmplVec_semitermVec (T₁ T₂ : Semiterm LAct Empty 1) (u₁ w₁ u₂ w₂ : ClosedSemiterm LAct 0) :
    IsSemitermVec LAct 6 1 (tmplVec T₁ T₂ u₁ w₁ u₂ w₂ : V) := by
  rw [six_eq, tmplVec]
  exact ((((((IsSemitermVec.nil 1).adjoin (semiterm_quote_emb₁ _)).adjoin (semiterm_quote_emb₁ _)).adjoin
    (semiterm_quote_emb₁ _)).adjoin (semiterm_quote_emb₁ _)).adjoin (semiterm_quote_emb₁ _)).adjoin
    (semiterm_quote_emb₁ _)

/-- Substituting `bnum k` into the six codes gives the description vector of `(me, opp)`, given
the six entry equations. -/
theorem termSubstVec_tmplVec {T₁ T₂ : Semiterm LAct Empty 1} {u₁ w₁ u₂ w₂ : ClosedSemiterm LAct 0}
    {k me opp : V}
    (h₁ : termSubst LAct (bnum k ∷ (0 : V)) (⌜(Rew.emb T₁ : SyntacticSemiterm LAct 1)⌝ : V) = progT (dnum me))
    (hu₁ : (⌜(Rew.emb u₁ : SyntacticSemiterm LAct 0)⌝ : V) = dU me)
    (hw₁ : (⌜(Rew.emb w₁ : SyntacticSemiterm LAct 0)⌝ : V) = dW me)
    (h₂ : termSubst LAct (bnum k ∷ (0 : V)) (⌜(Rew.emb T₂ : SyntacticSemiterm LAct 1)⌝ : V) = progT (dnum opp))
    (hu₂ : (⌜(Rew.emb u₂ : SyntacticSemiterm LAct 0)⌝ : V) = dU opp)
    (hw₂ : (⌜(Rew.emb w₂ : SyntacticSemiterm LAct 0)⌝ : V) = dW opp) :
    termSubstVec LAct 6 (bnum k ∷ (0 : V)) (tmplVec T₁ T₂ u₁ w₁ u₂ w₂) = descVec me opp := by
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
  have sU₁ : termSubst LAct (bnum k ∷ 0) (⌜(Rew.emb (cl u₁ : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝ : V) =
      dU me := by
    rw [quote_emb_cl_V, termSubst_closed _ (semiterm_quote_emb₀ _), hu₁]
  have sW₁ : termSubst LAct (bnum k ∷ 0) (⌜(Rew.emb (cl w₁ : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝ : V) =
      dW me := by
    rw [quote_emb_cl_V, termSubst_closed _ (semiterm_quote_emb₀ _), hw₁]
  have sU₂ : termSubst LAct (bnum k ∷ 0) (⌜(Rew.emb (cl u₂ : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝ : V) =
      dU opp := by
    rw [quote_emb_cl_V, termSubst_closed _ (semiterm_quote_emb₀ _), hu₂]
  have sW₂ : termSubst LAct (bnum k ∷ 0) (⌜(Rew.emb (cl w₂ : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝ : V) =
      dW opp := by
    rw [quote_emb_cl_V, termSubst_closed _ (semiterm_quote_emb₀ _), hw₂]
  unfold tmplVec descVec
  rw [six_eq, termSubstVec_cons hT₁ e5, termSubstVec_cons hU₁ e4, termSubstVec_cons hW₁ e3,
    termSubstVec_cons hT₂ e2, termSubstVec_cons hU₂ e1, termSubstVec_cons hW₂ e0, termSubstVec_nil,
    h₁, sU₁, sW₁, h₂, sU₂, sW₂]

/-- **The generic instance equation on codes**: the guard code of `(me, opp)` on the template
`GtmplA a` is the `bnum k`-instance of the code of the template instance, given the six entry
equations. -/
theorem guardCode_eq_instB_of (a : ℕ) {T₁ T₂ : Semiterm LAct Empty 1} {u₁ w₁ u₂ w₂ : ClosedSemiterm LAct 0}
    {k me opp : V}
    (h₁ : termSubst LAct (bnum k ∷ (0 : V)) (⌜(Rew.emb T₁ : SyntacticSemiterm LAct 1)⌝ : V) = progT (dnum me))
    (hu₁ : (⌜(Rew.emb u₁ : SyntacticSemiterm LAct 0)⌝ : V) = dU me)
    (hw₁ : (⌜(Rew.emb w₁ : SyntacticSemiterm LAct 0)⌝ : V) = dW me)
    (h₂ : termSubst LAct (bnum k ∷ (0 : V)) (⌜(Rew.emb T₂ : SyntacticSemiterm LAct 1)⌝ : V) = progT (dnum opp))
    (hu₂ : (⌜(Rew.emb u₂ : SyntacticSemiterm LAct 0)⌝ : V) = dU opp)
    (hw₂ : (⌜(Rew.emb w₂ : SyntacticSemiterm LAct 0)⌝ : V) = dW opp) :
    guardCode (⌜GtmplA a⌝ : V) me opp =
      instB (⌜(GtmplA a ⇜ ![T₁, cl u₁, cl w₁, T₂, cl u₂, cl w₂] : Semisentence LAct 1)⌝ : V) k := by
  show guardCode (⌜GtmplA a⌝ : V) me opp =
    subst LAct (bnum k ∷ (0 : V)) (⌜(GtmplA a ⇜ ![T₁, cl u₁, cl w₁, T₂, cl u₂, cl w₂] : Semisentence LAct 1)⌝ : V)
  rw [quote_GtmplA_subst, substs_substs (p := (⌜GtmplA a⌝ : V)) (l := 6)
    (by simpa using Sentence.quote_isSemiformula (V := V) (GtmplA a))
    (bnum_cons_semitermVec k) (tmplVec_semitermVec T₁ T₂ u₁ w₁ u₂ w₂),
    termSubstVec_tmplVec h₁ hu₁ hw₁ h₂ hu₂ hw₂]
  rfl

/-- **The generic truth equation** (standard reading): a template instance at the budget `k` says
"the program reconstructed from the opp-triple plays `a` against the one reconstructed from the
me-triple". -/
theorem eval_GtmplA_subst_iff (a : ℕ) (T₁ T₂ : Semiterm LAct Empty 1) (u₁ w₁ u₂ w₂ : ClosedSemiterm LAct 0)
    (k : V) :
    Semiformula.Eval (s := stdActV V) ![k] Empty.elim (GtmplA a ⇜ ![T₁, cl u₁, cl w₁, T₂, cl u₂, cl w₂]) ↔
      ∃ n, EvalGraph n
        (relabel (u₂.val (s := stdActV V) ![] Empty.elim) (w₂.val (s := stdActV V) ![] Empty.elim)
          (T₂.val (s := stdActV V) ![k] Empty.elim))
        (relabel (u₁.val (s := stdActV V) ![] Empty.elim) (w₁.val (s := stdActV V) ![] Empty.elim)
          (T₁.val (s := stdActV V) ![k] Empty.elim))
        (relabel (u₂.val (s := stdActV V) ![] Empty.elim) (w₂.val (s := stdActV V) ![] Empty.elim)
          (T₂.val (s := stdActV V) ![k] Empty.elim))
        (a : V) := by
  unfold GtmplA Gtmpl
  rw [Semiformula.eval_substs, Semiformula.eval_substs, Semiformula.eval_lMap, stdActV_lMap_emb]
  have h0 : (Semiterm.val (s := stdActV V) ![k] Empty.elim ∘ ![T₁, cl u₁, cl w₁, T₂, cl u₂, cl w₂]) =
      ![T₁.val (s := stdActV V) ![k] Empty.elim, u₁.val (s := stdActV V) ![] Empty.elim,
        w₁.val (s := stdActV V) ![] Empty.elim, T₂.val (s := stdActV V) ![k] Empty.elim,
        u₂.val (s := stdActV V) ![] Empty.elim, w₂.val (s := stdActV V) ![] Empty.elim] := by
    funext i; fin_cases i <;> simp [val_cl_V]
  rw [h0]
  have h1 : (Semiterm.val (s := stdActV V)
      ![T₁.val (s := stdActV V) ![k] Empty.elim, u₁.val (s := stdActV V) ![] Empty.elim,
        w₁.val (s := stdActV V) ![] Empty.elim, T₂.val (s := stdActV V) ![k] Empty.elim,
        u₂.val (s := stdActV V) ![] Empty.elim, w₂.val (s := stdActV V) ![] Empty.elim]
      Empty.elim ∘ ![#0, #1, #2, #3, #4, #5, actT6 a]) =
      ![T₁.val (s := stdActV V) ![k] Empty.elim, u₁.val (s := stdActV V) ![] Empty.elim,
        w₁.val (s := stdActV V) ![] Empty.elim, T₂.val (s := stdActV V) ![k] Empty.elim,
        u₂.val (s := stdActV V) ![] Empty.elim, w₂.val (s := stdActV V) ![] Empty.elim, (a : V)] := by
    funext i; fin_cases i <;> simp [val_actT6_V]
  rw [h1]
  exact eval_gtmpl (V := V) _

end generic
/-! ### 4. Family (1): the bot-wrapped self-play -/

section botSelf

/-- **The fixed formula of the bot-wrapped Dupoc self-play**: `GtmplA 0` filled with the
description of `pBot (Dupoc k)` twice. -/
noncomputable def qBD : Semisentence LAct 1 :=
  GtmplA 0 ⇜ ![TBD, cl uD, cl wD, TBD, cl uD, cl wD]

lemma qBD_eq : qBD = GtmplA 0 ⇜ ![TBD, cl uD, cl wD, TBD, cl uD, cl wD] := rfl

/-- The transposition: the bot-wrapped Cupod self-play. -/
noncomputable def qBC : Semisentence LAct 1 := Semiformula.lMap swap qBD

lemma lMap_swap_qBD : Semiformula.lMap swap qBD = qBC := rfl

lemma lMap_swap_qBC : Semiformula.lMap swap qBC = qBD := lMap_swap_swap _

lemma quote_emb_uD_botDupocV (k : V) :
    (⌜(Rew.emb uD : SyntacticSemiterm LAct 0)⌝ : V) = dU (pBot (DupocV k)) := by
  rw [dU_pBot, dU_DupocV, Semiterm.empty_quote_def]

lemma quote_emb_wD_botDupocV (k : V) :
    (⌜(Rew.emb wD : SyntacticSemiterm LAct 0)⌝ : V) = dW (pBot (DupocV k)) := by
  rw [dW_pBot, dW_DupocV, Semiterm.empty_quote_def]

/-- **The instance equation on codes of the bot-wrapped Dupoc self-play, in every model.** -/
theorem guardCode_botDupocV_eq_instB (k : V) :
    guardCode (⌜GtmplA 0⌝ : V) (pBot (DupocV k)) (pBot (DupocV k)) = instB (⌜qBD⌝ : V) k :=
  guardCode_eq_instB_of 0 (termSubst_TBD k) (quote_emb_uD_botDupocV k) (quote_emb_wD_botDupocV k)
    (termSubst_TBD k) (quote_emb_uD_botDupocV k) (quote_emb_wD_botDupocV k)

lemma relabelTemplate_quote_qBD_V : relabelTemplate 1 0 (⌜qBD⌝ : V) = ⌜qBC⌝ :=
  relabelTemplate_quote_sentence_V qBD

lemma guardCode_botCupodV_eq_relabel (k : V) :
    guardCode (⌜GtmplA 1⌝ : V) (pBot (CupodV k)) (pBot (CupodV k)) =
      relabelTemplate 1 0 (guardCode (⌜GtmplA 0⌝ : V) (pBot (DupocV k)) (pBot (DupocV k))) := by
  have hg0 : IsSemiformula LAct 6 (⌜GtmplA 0⌝ : V) := by
    simpa using Sentence.quote_isSemiformula (V := V) (GtmplA 0)
  have hg1 : IsSemiformula LAct 6 (⌜GtmplA 1⌝ : V) := by
    simpa using Sentence.quote_isSemiformula (V := V) (GtmplA 1)
  rw [← gsubst_of_template hg0, relabelTemplate_gsubst, swapcode_pBot_DupocV,
    relabelTemplate_quote_GtmplA_V, swapAct_zero, gsubst_of_template hg1]

/-- **The instance equation on codes of the bot-wrapped Cupod self-play, in every model.** -/
theorem guardCode_botCupodV_eq_instB (k : V) :
    guardCode (⌜GtmplA 1⌝ : V) (pBot (CupodV k)) (pBot (CupodV k)) = instB (⌜qBC⌝ : V) k := by
  rw [guardCode_botCupodV_eq_relabel, guardCode_botDupocV_eq_instB]
  unfold instB
  rw [relabelTemplate_subst isAct_one isAct_zero (Sentence.quote_isSemiformul₁ qBD)
    (bnum_cons_semitermVec k), relabelTemplate_quote_qBD_V]
  congr 1
  rw [show (1 : V) = 0 + 1 by simp, termRelabelVec_cons (bnum_term_LAct k).isUTerm IsUTermVec.empty,
    termRelabelVec_nil, termRelabel_bnum]

/-! #### The truth equations -/

/-- `qBC` is `GtmplA 1` filled with the bot tower and the transposed re-valuation terms. -/
theorem qBC_eq : qBC = GtmplA 1 ⇜ ![TBD, cl uC, cl wC, TBD, cl uC, cl wC] := by
  unfold qBC qBD
  rw [Semiformula.lMap_subst, lMap_swap_GtmplA, swapAct_zero]
  congr 1
  funext i
  fin_cases i <;> simp [lMap_swap_TBD, lMap_swap_cl, uC, wC]

/-- **The truth equation** (standard reading): `qBD(k)` holds in `stdActV V` iff
`pBot (DupocV k)` plays `C` against itself. -/
theorem eval_qBD_iff_V (k : V) :
    Semiformula.Eval (s := stdActV V) ![k] Empty.elim qBD ↔
      ∃ n, EvalGraph n (pBot (DupocV k)) (pBot (DupocV k)) (pBot (DupocV k)) 0 := by
  rw [qBD_eq, eval_GtmplA_subst_iff, val_TBD_V, dnum_pBot, relabel_bot, relabel_val_uD_wD_V, Nat.cast_zero]

/-- `qBC(k)` holds in `stdActV V` iff `pBot (CupodV k)` plays `D` against itself. -/
theorem eval_qBC_iff_V (k : V) :
    Semiformula.Eval (s := stdActV V) ![k] Empty.elim qBC ↔
      ∃ n, EvalGraph n (pBot (CupodV k)) (pBot (CupodV k)) (pBot (CupodV k)) 1 := by
  rw [qBC_eq, eval_GtmplA_subst_iff, val_TBD_V, dnum_pBot, relabel_bot, relabel_val_uC_wC_V, Nat.cast_one]

theorem eval_qBD_swap_iff_V (k : V) :
    Semiformula.Eval (s := swapActS V) ![k] Empty.elim qBD ↔
      ∃ n, EvalGraph n (pBot (CupodV k)) (pBot (CupodV k)) (pBot (CupodV k)) 1 := by
  rw [eval_swapActS, lMap_swap_qBD, ← stdActV_eq_stdActS]
  exact eval_qBC_iff_V k

theorem eval_qBC_swap_iff_V (k : V) :
    Semiformula.Eval (s := swapActS V) ![k] Empty.elim qBC ↔
      ∃ n, EvalGraph n (pBot (DupocV k)) (pBot (DupocV k)) (pBot (DupocV k)) 0 := by
  rw [eval_swapActS, lMap_swap_qBC, ← stdActV_eq_stdActS]
  exact eval_qBD_iff_V k

/-! #### The search clauses -/

/-- **The bot-wrapped Dupoc's search clause against itself** (fuel 3). -/
theorem botDupoc_search_V (k : V) :
    LenProvableV TAct k (guardCode (⌜GtmplA 0⌝ : V) (pBot (DupocV k)) (pBot (DupocV k))) →
      EvalGraph 3 (pBot (DupocV k)) (pBot (DupocV k)) (pBot (DupocV k)) 0 :=
  botDupoc_frame_search_V k _ _

theorem botCupod_search_V (k : V) :
    LenProvableV TAct k (guardCode (⌜GtmplA 1⌝ : V) (pBot (CupodV k)) (pBot (CupodV k))) →
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
    LenDerivable TAct a (instB (⌜pBD⌝ : V) k) →
    EvalGraph 3 (pBot (DupocV k)) (pBot (DupocV k)) (pBot (DupocV k)) 0 ∧
      EvalGraph 3 (pBot (CupodV k)) (pBot (CupodV k)) (pBot (CupodV k)) 1 := by
  intro a ha h
  rw [instB_quote_pBD] at h
  have hx := isFormula_instB_quote qBD k
  have hy := isFormula_instB_quote qBC k
  have h₁ := lenDerivable_mono_V ha (lenDerivable_andL_V hx hy h)
  have h₂ := lenDerivable_mono_V ha (lenDerivable_andR_V hx hy h)
  rw [lenDerivable_iff_lenProvableV, ← guardCode_botDupocV_eq_instB] at h₁
  rw [lenDerivable_iff_lenProvableV, ← guardCode_botCupodV_eq_instB] at h₂
  exact ⟨botDupoc_search_V k h₁, botCupod_search_V k h₂⟩

/-- The box form of `pBD_both_V`. -/
theorem pBD_guards_V (k : V) (a : V)
    (ha : a + 8 * (formulaLen LAct (instB (⌜qBD⌝ : V) k) + formulaLen LAct (instB (⌜qBC⌝ : V) k)) + 7 ≤ k)
    (hpc : LenDerivable TAct a (instB (⌜pBD⌝ : V) k)) :
    LenProvableV TAct k (guardCode (⌜GtmplA 0⌝ : V) (pBot (DupocV k)) (pBot (DupocV k))) ∧
    LenProvableV TAct k (guardCode (⌜GtmplA 1⌝ : V) (pBot (CupodV k)) (pBot (CupodV k))) := by
  rw [instB_quote_pBD] at hpc
  have hx := isFormula_instB_quote qBD k
  have hy := isFormula_instB_quote qBC k
  have h₁ := lenDerivable_mono_V ha (lenDerivable_andL_V hx hy hpc)
  have h₂ := lenDerivable_mono_V ha (lenDerivable_andR_V hx hy hpc)
  rw [lenDerivable_iff_lenProvableV, ← guardCode_botDupocV_eq_instB] at h₁
  rw [lenDerivable_iff_lenProvableV, ← guardCode_botCupodV_eq_instB] at h₂
  exact ⟨h₁, h₂⟩

theorem eval_pBD_iff_std (k : V) :
    Semiformula.Eval (s := stdActV V) ![k] Empty.elim pBD ↔
      (∃ n, EvalGraph n (pBot (DupocV k)) (pBot (DupocV k)) (pBot (DupocV k)) 0) ∧
      (∃ n, EvalGraph n (pBot (CupodV k)) (pBot (CupodV k)) (pBot (CupodV k)) 1) := by
  rw [pBD_def]
  simp only [LogicalConnective.HomClass.map_and, LogicalConnective.Prop.and_eq]
  rw [eval_qBD_iff_V, eval_qBC_iff_V]

theorem eval_pBD_iff_swap (k : V) :
    Semiformula.Eval (s := swapActS V) ![k] Empty.elim pBD ↔
      (∃ n, EvalGraph n (pBot (DupocV k)) (pBot (DupocV k)) (pBot (DupocV k)) 0) ∧
      (∃ n, EvalGraph n (pBot (CupodV k)) (pBot (CupodV k)) (pBot (CupodV k)) 1) := by
  rw [eval_swapActS, lMap_swap_pBD, ← stdActV_eq_stdActS]
  simp only [LogicalConnective.HomClass.map_and, LogicalConnective.Prop.and_eq]
  rw [eval_qBD_iff_V, eval_qBC_iff_V, and_comm]

theorem eval_pBD_iff_stdActS (k : V) :
    Semiformula.Eval (s := stdActS V) ![k] Empty.elim pBD ↔
      (∃ n, EvalGraph n (pBot (DupocV k)) (pBot (DupocV k)) (pBot (DupocV k)) 0) ∧
      (∃ n, EvalGraph n (pBot (CupodV k)) (pBot (CupodV k)) (pBot (CupodV k)) 1) := by
  rw [← stdActV_eq_stdActS]; exact eval_pBD_iff_std k

/-- **The bounded Löb premise of the bot-wrapped self-play family, slack `(7, 8)`.** -/
theorem loebSound_pBD : LoebSound pBD 7 8 := by
  intro V _ _ k a ha h
  have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
  have ha' : a + 8 * (formulaLen LAct (instB (⌜qBD⌝ : V) k) + formulaLen LAct (instB (⌜qBC⌝ : V) k)) + 7 ≤ k :=
    le_trans (pConj_slack_le a _ _ _ (formulaLen_instB_pBD k)) ha
  obtain ⟨h1, h2⟩ := pBD_both_V k a ha' h
  exact ⟨(eval_pBD_iff_stdActS k).mpr ⟨⟨3, h1⟩, ⟨3, h2⟩⟩, (eval_pBD_iff_swap k).mpr ⟨⟨3, h1⟩, ⟨3, h2⟩⟩⟩

/-! #### The cells at ℕ -/

/-- **The bot-wrapped self-play cells, packaged**: for all large `k`, both bot-wrapped searchers
find their guards (fuel 3) and both guard boxes hold — `family_found pBD`, the arithmetized
`botDupoc_self_coop`. -/
theorem botDupoc_cell_core {d : ℕ} (hE : BoundedInnerNec d) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      (EvalGraph 3 (pBot (Dupoc k)) (pBot (Dupoc k)) (pBot (Dupoc k)) 0 ∧
        EvalGraph 3 (pBot (Cupod k)) (pBot (Cupod k)) (pBot (Cupod k)) 1) ∧
      (LenProvableV TAct k (guardCode (⌜GtmplA 0⌝ : ℕ) (pBot (Dupoc k)) (pBot (Dupoc k))) ∧
        LenProvableV TAct k (guardCode (⌜GtmplA 1⌝ : ℕ) (pBot (Cupod k)) (pBot (Cupod k)))) := by
  obtain ⟨k₀, h⟩ := family_found pBD hE loebSound_pBD
  refine ⟨k₀, fun k hk ↦ ?_⟩
  obtain ⟨a, ha, hpc⟩ := h k hk
  have ha' := le_def.mpr (pConj_slack_nat a _ _ _ k (formulaLen_instB_pBD (V := ℕ) k) ha)
  exact ⟨pBD_both_V k a ha' hpc, pBD_guards_V k a ha' hpc⟩

/-- **The bot-wrapped Dupoc cooperates with itself in PA-`S'`** (the engine's
`botDupoc_self_coop`), conditional on bounded inner necessitation: fuel 3. -/
theorem botDupoc_self_coop {d : ℕ} (hE : BoundedInnerNec d) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k → EvalGraph 3 (pBot (Dupoc k)) (pBot (Dupoc k)) (pBot (Dupoc k)) 0 := by
  obtain ⟨k₀, h⟩ := botDupoc_cell_core hE
  exact ⟨k₀, fun k hk ↦ (h k hk).1.1⟩

theorem botCupod_self_defect {d : ℕ} (hE : BoundedInnerNec d) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k → EvalGraph 3 (pBot (Cupod k)) (pBot (Cupod k)) (pBot (Cupod k)) 1 := by
  obtain ⟨k₀, h⟩ := botDupoc_cell_core hE
  exact ⟨k₀, fun k hk ↦ (h k hk).1.2⟩

/-- **The box form**: for all large `k`, the bot-wrapped Dupoc FINDS a proof of its guard against
itself within its budget `k` (conditional). -/
theorem botDupoc_finds_guard {d : ℕ} (hE : BoundedInnerNec d) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      LenProvableV TAct k (guardCode (⌜GtmplA 0⌝ : ℕ) (pBot (Dupoc k)) (pBot (Dupoc k))) := by
  obtain ⟨k₀, h⟩ := botDupoc_cell_core hE
  exact ⟨k₀, fun k hk ↦ (h k hk).2.1⟩

/-- **The bot-wrapped Dupoc self-cooperation in PA-`S'`, unconditional**: for all large `k`,
`pBot (Dupoc k)` cooperates with itself at fuel 3 (bot, search, const). -/
theorem botDupoc_self_coop_unconditional :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k → EvalGraph 3 (pBot (Dupoc k)) (pBot (Dupoc k)) (pBot (Dupoc k)) 0 :=
  botDupoc_self_coop boundedInnerNec_sixteen

/-- **The bot-wrapped Cupod self-defection in PA-`S'`, unconditional.** -/
theorem botCupod_self_defect_unconditional :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k → EvalGraph 3 (pBot (Cupod k)) (pBot (Cupod k)) (pBot (Cupod k)) 1 :=
  botCupod_self_defect boundedInnerNec_sixteen

/-- **The bot-wrapped Dupoc finds its guard, unconditional.** -/
theorem botDupoc_finds_guard_unconditional :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      LenProvableV TAct k (guardCode (⌜GtmplA 0⌝ : ℕ) (pBot (Dupoc k)) (pBot (Dupoc k))) :=
  botDupoc_finds_guard boundedInnerNec_sixteen

end botSelf

end ArithS
