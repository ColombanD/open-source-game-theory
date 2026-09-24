import ArithS.Cells.Common.Templates
import ArithS.Cells.Common.Probers
import ArithS.Cells.Common.Families
import ArithS.Assembly.Cell
import ArithS.SimTest
import ArithS.Necessitation.Package

/-!
# ArithS.Cells.DupocMirror — Dupoc × Mirror `(C, C)` and Cupod × Mirror `(D, D)` in PA-`S'`

`Research/Notes/ROUTE_B_SCOPE.md` §3 Phase 2 (2026-09-23): the first Löb family after the
self-play one — the arithmetized twins of the engine's `outcome_DupocBot_vs_MirrorBot = (C, C)`
and `outcome_CupodBot_vs_MirrorBot = (D, D)` (both `eventual`, both `pblt_engine_id` in the
engine). The pattern is `Assembly/Prep.lean` §1–§3 + `Assembly/Family.lean` + `Assembly/Cell.lean`
with Mirror as the OPPONENT instead of the player itself. V-generic (every model of `𝗜𝚺₁`,
budgets `k : V` possibly nonstandard) unless a statement says `ℕ`.

1. **Mirror in every model.** `MirrorV := pSim pOpp pSelf` (`SimTest.Mirror` at `V = ℕ`, by
   `rfl`; `cast_Mirror`), τ-fixed (`swapcode_MirrorV`), hence its canonical description is
   `k`-free and closed: `dnum MirrorV = MirrorV`, `dU MirrorV = 0`, `dW MirrorV = 1`. Its sim
   step `mirror_step_V : EvalGraph (n+1) MirrorV opp MirrorV a ↔ EvalGraph n opp MirrorV opp a`
   (`EvalGraph.sim_iff` + `psubst_opp/self`): Mirror in the frame `(Mirror, opp)` runs `opp` in
   the frame `(opp, Mirror)`.
2. **The guards as `k`-instances of FIXED one-variable formulas.** `TM := lMap emb (progTT Mirror)`
   is Mirror's CLOSED description term (`val_TM_V : TM = MirrorV`, `quote_emb_TM : ⌜TM⌝ =
   progT MirrorV`), and `qDM := GtmplA 0 ⇜ ![TD, cl uD, cl wD, cl TM, cl (numT 0), cl (numT 1)]`
   — Dupoc's one-variable description in the me-slots (`Instance.TD`, `k` = `#0`), Mirror's
   closed description in the opp-slots. The instance equation on codes
   `guardCode_DupocV_MirrorV_eq_instB : guardCode ⌜GtmplA 0⌝ (DupocV k) MirrorV = instB ⌜qDM⌝ k`
   follows `InstanceV.guardCode_DupocV_eq` (internal `substs_substs` on the code of the fixed
   formula; the me-entries by `termSubst_tower`, the opp-entries closed, `termSubst_closed`).
   `qCM := lMap swap qDM` is Cupod's guard against Mirror (`swapcode MirrorV = MirrorV`):
   `guardCode_CupodV_MirrorV_eq_instB`, via `relabelTemplate_gsubst` exactly as `Prep` §1.
   Nothing in `Instance*.lean`/`Guard.lean`/`Template.lean` was generalized: the opp-slots take a
   closed term through the same `quote_emb_cl_V`/`termSubst_closed` route as `uD`/`wD`.
3. **Truth equations**, standard reading `stdActV V`: `eval_qDM_iff_V : qDM(k) ↔ ∃ n, EvalGraph n
   MirrorV (DupocV k) MirrorV 0` ("Mirror plays C against Dupoc k"), `eval_qCM_iff_V` ("Mirror
   plays D against Cupod k"), and the swap-reading twins (`eval_qDM_swap_iff_V`,
   `eval_qCM_swap_iff_V`: the two formulas exchange roles).
4. **The search clauses** (fuel 2): `dupoc_mirror_search_V`, `cupod_mirror_search_V`.
5. **The conjunction family** `pDM := qDM ⋏ qCM` (the `Prep` §3 move — no evaluator
   τ-equivariance in `V` is needed): `instB_quote_pDM`, `pDM_both_V` (a box of `pDM(k)` at budget
   `a` with `a + 8(|qDM(k)| + |qCM(k)|) + 7 ≤ k` makes BOTH searchers find their guards, by
   ∧-elimination on codes), `pDM_guards_V` (the box form), and `eval_pDM_iff_std/_swap`: Mirror
   COPIES — Dupoc plays C at fuel 2 ⇒ Mirror plays C at fuel 3 (`mirror_copies_dupoc_V`,
   `mirror_step_V`), and in the swap reading the roles exchange, so the content is the same.
6. **The Löb premise and the cells.** `loebSound_pDM : LoebSound pDM 7 8` (as `loebSound_pConj`),
   then the engine `family_found pDM` (the arithmetized `pblt_engine`) at ℕ: the conditional
   forms `dupoc_mirror_coop`/`cupod_mirror_defect`/`dupoc_finds_guard_vs_mirror`/
   `cupod_finds_guard_vs_mirror` (`hE : BoundedInnerNec d`, as `Cell.lean`), and their
   UNCONDITIONAL twins at `boundedInnerNec_sixteen` (`Necessitation/Package.lean`):
   **`dupoc_mirror_coop_unconditional`** — for all large `k`, `Dupoc k` cooperates with Mirror
   (fuel 2) and Mirror copies (fuel 3): the `(C, C)` cell — and
   **`cupod_mirror_defect_unconditional`** — the `(D, D)` cell.

Conventions (`HANDOVER_ARITHMETIZED_S.md` §5–6): every threshold and constant is EXISTENTIAL;
`simp` never sees a closed quote of `qDM`/`pDM`/`psiF pDM` (the quote equations are for
VARIABLE sentences, instantiated; `set`/`rfl`-bridges); `omega` is never asked about `V`; at
`V = ℕ` the thresholds are STRICT (`k₀ < k`) and the V-generic `≤` is bridged by `le_def`
(`Cell.cell_core`'s idiom).
-/

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open LAct

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ### 1. Mirror in every model -/

section mirror


/-- Mirror copies Dupoc: if `DupocV k` plays C against Mirror at fuel 2, Mirror plays C against
`DupocV k` at fuel 3. -/
theorem mirror_copies_dupoc_V (k : V) (h : EvalGraph 2 (DupocV k) MirrorV (DupocV k) 0) :
    EvalGraph 3 MirrorV (DupocV k) MirrorV 0 := by
  rw [show (3 : V) = 2 + 1 from two_add_one_eq_three.symm]
  exact (mirror_step_V 2 (DupocV k) 0).mpr h

/-- Mirror copies Cupod. -/
theorem mirror_copies_cupod_V (k : V) (h : EvalGraph 2 (CupodV k) MirrorV (CupodV k) 1) :
    EvalGraph 3 MirrorV (CupodV k) MirrorV 1 := by
  rw [show (3 : V) = 2 + 1 from two_add_one_eq_three.symm]
  exact (mirror_step_V 2 (CupodV k) 1).mpr h

end mirror

/-! ### 2. The fixed formulas and their instance equations on codes -/

section instanceEq


/-- **The fixed formula of Dupoc vs Mirror**: the template instance `GtmplA 0` filled with
Dupoc's one-variable description (me-slots) and Mirror's closed description (opp-slots). -/
noncomputable def qDM : Semisentence LAct 1 :=
  GtmplA 0 ⇜ ![TD, cl uD, cl wD, cl TM, cl (numT 0), cl (numT 1)]

lemma qDM_eq : qDM = GtmplA 0 ⇜ ![TD, cl uD, cl wD, cl TM, cl (numT 0), cl (numT 1)] := rfl

/-- **The fixed formula of Cupod vs Mirror**: the transposition of `qDM`. -/
noncomputable def qCM : Semisentence LAct 1 := Semiformula.lMap swap qDM

lemma lMap_swap_qDM : Semiformula.lMap swap qDM = qCM := rfl

lemma lMap_swap_qCM : Semiformula.lMap swap qCM = qDM := lMap_swap_swap _

/-- The six codes of the substituted terms of `qDM`, as an internal vector. -/
noncomputable def qDMVec : V :=
  (⌜(Rew.emb TD : SyntacticSemiterm LAct 1)⌝ : V) ∷ ⌜(Rew.emb (cl uD : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝ ∷
    ⌜(Rew.emb (cl wD : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝ ∷
    ⌜(Rew.emb (cl TM : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝ ∷
    ⌜(Rew.emb (cl (numT 0) : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝ ∷
    ⌜(Rew.emb (cl (numT 1) : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝ ∷ 0

lemma semitermVec_val_qDM :
    SemitermVec.val (fun i ↦ (⌜(Rew.emb ((![TD, cl uD, cl wD, cl TM, cl (numT 0), cl (numT 1)] :
      Fin 6 → Semiterm LAct Empty 1) i) : SyntacticSemiterm LAct 1)⌝ : Bootstrapping.Semiterm V LAct 1)) = qDMVec := by
  have hv : (fun i ↦ (⌜(Rew.emb ((![TD, cl uD, cl wD, cl TM, cl (numT 0), cl (numT 1)] :
      Fin 6 → Semiterm LAct Empty 1) i) : SyntacticSemiterm LAct 1)⌝ : Bootstrapping.Semiterm V LAct 1)) =
      ![⌜(Rew.emb TD : SyntacticSemiterm LAct 1)⌝, ⌜(Rew.emb (cl uD : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝,
        ⌜(Rew.emb (cl wD : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝,
        ⌜(Rew.emb (cl TM : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝,
        ⌜(Rew.emb (cl (numT 0) : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝,
        ⌜(Rew.emb (cl (numT 1) : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝] := by
    funext i; fin_cases i <;> rfl
  rw [hv]
  simp only [SemitermVec.val_cons, SemitermVec.val_nil]
  rfl

/-- The code of `qDM` is the internal substitution of `qDMVec` into the template code. -/
theorem quote_qDM : (⌜qDM⌝ : V) = subst LAct qDMVec (⌜GtmplA 0⌝ : V) := by
  unfold qDM
  rw [Sentence.quote_def, Semiformula.coe_subst_eq_subst_coe, Semiformula.quote_def,
    Semiformula.typed_quote_substs, Bootstrapping.Semiformula.val_substs, ← Semiformula.quote_def,
    ← Sentence.quote_def]
  congr 1

lemma qDMVec_semitermVec : IsSemitermVec LAct 6 1 (qDMVec : V) := by
  rw [six_eq, qDMVec]
  exact ((((((IsSemitermVec.nil 1).adjoin (semiterm_quote_emb₁ _)).adjoin (semiterm_quote_emb₁ _)).adjoin
    (semiterm_quote_emb₁ _)).adjoin (semiterm_quote_emb₁ _)).adjoin (semiterm_quote_emb₁ _)).adjoin
    (semiterm_quote_emb₁ _)

/-- Substituting `bnum k` into the six codes gives the description vector of `(DupocV k, MirrorV)`:
the me-entries by `termSubst_tower`/`dU_DupocV`/`dW_DupocV`, the opp-entries CLOSED. -/
theorem termSubstVec_qDMVec (k : V) :
    termSubstVec LAct 6 (bnum k ∷ (0 : V)) qDMVec = descVec (DupocV k) MirrorV := by
  have hT : IsUTerm LAct (⌜(Rew.emb TD : SyntacticSemiterm LAct 1)⌝ : V) := (semiterm_quote_emb₁ _).isUTerm
  have hU : IsUTerm LAct (⌜(Rew.emb (cl uD : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝ : V) :=
    (semiterm_quote_emb₁ _).isUTerm
  have hW : IsUTerm LAct (⌜(Rew.emb (cl wD : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝ : V) :=
    (semiterm_quote_emb₁ _).isUTerm
  have hM : IsUTerm LAct (⌜(Rew.emb (cl TM : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝ : V) :=
    (semiterm_quote_emb₁ _).isUTerm
  have h0 : IsUTerm LAct (⌜(Rew.emb (cl (numT 0) : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝ : V) :=
    (semiterm_quote_emb₁ _).isUTerm
  have h1 : IsUTerm LAct (⌜(Rew.emb (cl (numT 1) : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝ : V) :=
    (semiterm_quote_emb₁ _).isUTerm
  have e0 : IsUTermVec LAct 0 (0 : V) := IsUTermVec.empty
  have e1 := e0.adjoin h1
  have e2 := e1.adjoin h0
  have e3 := e2.adjoin hM
  have e4 := e3.adjoin hW
  have e5 := e4.adjoin hU
  have sT : termSubst LAct (bnum k ∷ 0) (⌜(Rew.emb TD : SyntacticSemiterm LAct 1)⌝ : V) =
      progT (dnum (DupocV k)) := by
    rw [quote_emb_TD, termSubst_tower, dnum_DupocV]
  have sU : termSubst LAct (bnum k ∷ 0) (⌜(Rew.emb (cl uD : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝ : V) =
      dU (DupocV k) := by
    rw [quote_emb_cl_V, termSubst_closed _ (semiterm_quote_emb₀ _), dU_DupocV, Semiterm.empty_quote_def]
  have sW : termSubst LAct (bnum k ∷ 0) (⌜(Rew.emb (cl wD : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝ : V) =
      dW (DupocV k) := by
    rw [quote_emb_cl_V, termSubst_closed _ (semiterm_quote_emb₀ _), dW_DupocV, Semiterm.empty_quote_def]
  have sM : termSubst LAct (bnum k ∷ 0) (⌜(Rew.emb (cl TM : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝ : V) =
      progT (dnum MirrorV) := by
    rw [quote_emb_cl_V, termSubst_closed _ (semiterm_quote_emb₀ _), quote_emb_TM, dnum_MirrorV]
  have s0 : termSubst LAct (bnum k ∷ 0) (⌜(Rew.emb (cl (numT 0) : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝ : V) =
      dU MirrorV := by
    rw [quote_emb_cl_V, termSubst_closed _ (semiterm_quote_emb₀ _), quote_emb_numT, dU_MirrorV, Nat.cast_zero]
  have s1 : termSubst LAct (bnum k ∷ 0) (⌜(Rew.emb (cl (numT 1) : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝ : V) =
      dW MirrorV := by
    rw [quote_emb_cl_V, termSubst_closed _ (semiterm_quote_emb₀ _), quote_emb_numT, dW_MirrorV, Nat.cast_one]
  unfold qDMVec descVec
  rw [six_eq, termSubstVec_cons hT e5, termSubstVec_cons hU e4, termSubstVec_cons hW e3,
    termSubstVec_cons hM e2, termSubstVec_cons h0 e1, termSubstVec_cons h1 e0, termSubstVec_nil,
    sT, sU, sW, sM, s0, s1]

/-- **Dupoc's instance equation on codes against Mirror, in every model**: the guard code of
`DupocV k` against `MirrorV` is the `bnum k`-instance of `⌜qDM⌝`. -/
theorem guardCode_DupocV_MirrorV_eq_instB (k : V) :
    guardCode (⌜GtmplA 0⌝ : V) (DupocV k) MirrorV = instB (⌜qDM⌝ : V) k := by
  show guardCode (⌜GtmplA 0⌝ : V) (DupocV k) MirrorV = subst LAct (bnum k ∷ (0 : V)) (⌜qDM⌝ : V)
  rw [quote_qDM, substs_substs (p := (⌜GtmplA 0⌝ : V)) (l := 6)
    (by simpa using Sentence.quote_isSemiformula (V := V) (GtmplA 0))
    (bnum_cons_semitermVec k) qDMVec_semitermVec, termSubstVec_qDMVec]
  rfl

/-- The code-level τ of `⌜qDM⌝` is `⌜qCM⌝`, in every model. -/
lemma relabelTemplate_quote_qDM_V : relabelTemplate 1 0 (⌜qDM⌝ : V) = ⌜qCM⌝ :=
  relabelTemplate_quote_sentence_V qDM

/-- Cupod's guard code against Mirror is the code-level τ of Dupoc's (Mirror is τ-fixed). -/
lemma guardCode_CupodV_MirrorV_eq_relabel (k : V) :
    guardCode (⌜GtmplA 1⌝ : V) (CupodV k) MirrorV =
      relabelTemplate 1 0 (guardCode (⌜GtmplA 0⌝ : V) (DupocV k) MirrorV) := by
  have hg0 : IsSemiformula LAct 6 (⌜GtmplA 0⌝ : V) := by
    simpa using Sentence.quote_isSemiformula (V := V) (GtmplA 0)
  have hg1 : IsSemiformula LAct 6 (⌜GtmplA 1⌝ : V) := by
    simpa using Sentence.quote_isSemiformula (V := V) (GtmplA 1)
  rw [← gsubst_of_template hg0, relabelTemplate_gsubst, swapcode_DupocV, swapcode_MirrorV,
    relabelTemplate_quote_GtmplA_V, swapAct_zero, gsubst_of_template hg1]

/-- **Cupod's instance equation on codes against Mirror, in every model.** -/
theorem guardCode_CupodV_MirrorV_eq_instB (k : V) :
    guardCode (⌜GtmplA 1⌝ : V) (CupodV k) MirrorV = instB (⌜qCM⌝ : V) k := by
  rw [guardCode_CupodV_MirrorV_eq_relabel, guardCode_DupocV_MirrorV_eq_instB]
  unfold instB
  rw [relabelTemplate_subst isAct_one isAct_zero (Sentence.quote_isSemiformul₁ qDM)
    (bnum_cons_semitermVec k), relabelTemplate_quote_qDM_V]
  congr 1
  rw [show (1 : V) = 0 + 1 by simp, termRelabelVec_cons (bnum_term_LAct k).isUTerm IsUTermVec.empty,
    termRelabelVec_nil, termRelabel_bnum]

/-! #### The search clauses -/

/-- **Dupoc's search clause against Mirror in every model** (fuel `2`). -/
theorem dupoc_mirror_search_V (k : V) :
    LenProvableV TAct k (guardCode (⌜GtmplA 0⌝ : V) (DupocV k) MirrorV) →
      EvalGraph 2 (DupocV k) MirrorV (DupocV k) 0 := by
  intro h
  rw [show (2 : V) = 1 + 1 from one_add_one_eq_two.symm]
  show EvalGraph (1 + 1) (DupocV k) MirrorV (pSearch k (⌜GtmplA 0⌝ : V) (pConst 0) (pConst 1)) 0
  rw [EvalGraph.search_iff₆ (isSemiformula_quote₆ (GtmplA 0))]
  left
  refine ⟨h, ?_⟩
  rw [show (1 : V) = 0 + 1 by simp, EvalGraph.const_iff]

/-- **Cupod's search clause against Mirror in every model** (fuel `2`; the found branch plays
`pConst 1`). -/
theorem cupod_mirror_search_V (k : V) :
    LenProvableV TAct k (guardCode (⌜GtmplA 1⌝ : V) (CupodV k) MirrorV) →
      EvalGraph 2 (CupodV k) MirrorV (CupodV k) 1 := by
  intro h
  rw [show (2 : V) = 1 + 1 from one_add_one_eq_two.symm]
  show EvalGraph (1 + 1) (CupodV k) MirrorV (pSearch k (⌜GtmplA 1⌝ : V) (pConst 1) (pConst 0)) 1
  rw [EvalGraph.search_iff₆ (isSemiformula_quote₆ (GtmplA 1))]
  left
  refine ⟨h, ?_⟩
  have e : EvalGraph (0 + 1) (CupodV k) MirrorV (pConst 1) 1 := EvalGraph.const_iff.mpr rfl
  rwa [zero_add] at e

/-- The search clauses in the `instB` vocabulary. -/
theorem dupoc_mirror_search_instB_V (k : V) :
    LenProvableV TAct k (instB (⌜qDM⌝ : V) k) → EvalGraph 2 (DupocV k) MirrorV (DupocV k) 0 := by
  intro h
  rw [← guardCode_DupocV_MirrorV_eq_instB] at h
  exact dupoc_mirror_search_V k h

theorem cupod_mirror_search_instB_V (k : V) :
    LenProvableV TAct k (instB (⌜qCM⌝ : V) k) → EvalGraph 2 (CupodV k) MirrorV (CupodV k) 1 := by
  intro h
  rw [← guardCode_CupodV_MirrorV_eq_instB] at h
  exact cupod_mirror_search_V k h

end instanceEq

/-! ### 3. The truth equations, in both readings -/

section truth

/-- `qCM` is the template instance `GtmplA 1` filled with Dupoc's description term, the
transposed re-valuation terms, and Mirror's (τ-fixed) closed description. -/
theorem qCM_eq : qCM = GtmplA 1 ⇜ ![TD, cl uC, cl wC, cl TM, cl (numT 0), cl (numT 1)] := by
  unfold qCM qDM
  rw [Semiformula.lMap_subst, lMap_swap_GtmplA, swapAct_zero]
  congr 1
  funext i
  fin_cases i <;> simp [lMap_swap_TD, lMap_swap_cl, uC, wC, lMap_swap_TM, lMap_swap_numT]

/-- **The truth equation of Dupoc's guard against Mirror in every model** (standard reading):
`qDM(k)` holds in `stdActV V` iff Mirror plays `C` against `DupocV k` (at some fuel). -/
theorem eval_qDM_iff_V (k : V) :
    Semiformula.Eval (s := stdActV V) ![k] Empty.elim qDM ↔
      ∃ n, EvalGraph n MirrorV (DupocV k) MirrorV 0 := by
  rw [qDM_eq]
  unfold GtmplA Gtmpl
  rw [Semiformula.eval_substs, Semiformula.eval_substs, Semiformula.eval_lMap, stdActV_lMap_emb]
  have h0 : (Semiterm.val (s := stdActV V) ![k] Empty.elim ∘ ![TD, cl uD, cl wD, cl TM, cl (numT 0), cl (numT 1)]) =
      ![dnum (DupocV k), uD.val (s := stdActV V) ![] Empty.elim, wD.val (s := stdActV V) ![] Empty.elim,
        MirrorV, 0, 1] := by
    funext i; fin_cases i <;> simp [val_TD_V, val_cl_V, val_TM_V, val_numT_V]
  rw [h0]
  have h1 : (Semiterm.val (s := stdActV V)
      ![dnum (DupocV k), uD.val (s := stdActV V) ![] Empty.elim, wD.val (s := stdActV V) ![] Empty.elim,
        MirrorV, 0, 1] Empty.elim ∘ ![#0, #1, #2, #3, #4, #5, actT6 0]) =
      ![dnum (DupocV k), uD.val (s := stdActV V) ![] Empty.elim, wD.val (s := stdActV V) ![] Empty.elim,
        MirrorV, 0, 1, 0] := by
    funext i; fin_cases i <;> simp [val_actT6_V]
  rw [h1]
  refine (eval_gtmpl (V := V) _).trans ?_
  simp [relabel_val_uD_wD_V, relabel_zero_one]

/-- **The truth equation of Cupod's guard against Mirror in every model** (standard reading):
`qCM(k)` holds in `stdActV V` iff Mirror plays `D` against `CupodV k`. -/
theorem eval_qCM_iff_V (k : V) :
    Semiformula.Eval (s := stdActV V) ![k] Empty.elim qCM ↔
      ∃ n, EvalGraph n MirrorV (CupodV k) MirrorV 1 := by
  rw [qCM_eq]
  unfold GtmplA Gtmpl
  rw [Semiformula.eval_substs, Semiformula.eval_substs, Semiformula.eval_lMap, stdActV_lMap_emb]
  have h0 : (Semiterm.val (s := stdActV V) ![k] Empty.elim ∘ ![TD, cl uC, cl wC, cl TM, cl (numT 0), cl (numT 1)]) =
      ![dnum (DupocV k), uC.val (s := stdActV V) ![] Empty.elim, wC.val (s := stdActV V) ![] Empty.elim,
        MirrorV, 0, 1] := by
    funext i; fin_cases i <;> simp [val_TD_V, val_cl_V, val_TM_V, val_numT_V]
  rw [h0]
  have h1 : (Semiterm.val (s := stdActV V)
      ![dnum (DupocV k), uC.val (s := stdActV V) ![] Empty.elim, wC.val (s := stdActV V) ![] Empty.elim,
        MirrorV, 0, 1] Empty.elim ∘ ![#0, #1, #2, #3, #4, #5, actT6 1]) =
      ![dnum (DupocV k), uC.val (s := stdActV V) ![] Empty.elim, wC.val (s := stdActV V) ![] Empty.elim,
        MirrorV, 0, 1, 1] := by
    funext i; fin_cases i <;> simp [val_actT6_V]
  rw [h1]
  refine (eval_gtmpl (V := V) _).trans ?_
  simp [relabel_val_uC_wC_V, relabel_zero_one]

/-- In the swapped reading, `qDM(k)` says "Mirror plays D against Cupod k". -/
theorem eval_qDM_swap_iff_V (k : V) :
    Semiformula.Eval (s := swapActS V) ![k] Empty.elim qDM ↔
      ∃ n, EvalGraph n MirrorV (CupodV k) MirrorV 1 := by
  rw [eval_swapActS, lMap_swap_qDM, ← stdActV_eq_stdActS]
  exact eval_qCM_iff_V k

/-- In the swapped reading, `qCM(k)` says "Mirror plays C against Dupoc k". -/
theorem eval_qCM_swap_iff_V (k : V) :
    Semiformula.Eval (s := swapActS V) ![k] Empty.elim qCM ↔
      ∃ n, EvalGraph n MirrorV (DupocV k) MirrorV 0 := by
  rw [eval_swapActS, lMap_swap_qCM, ← stdActV_eq_stdActS]
  exact eval_qDM_iff_V k

end truth

/-! ### 4. The conjunction family -/

section conj

/-- **The Löb family of the Mirror cells**: the conjunction of the two guards. -/
noncomputable def pDM : Semisentence LAct 1 := qDM ⋏ qCM

lemma pDM_def : pDM = qDM ⋏ qCM := rfl

lemma lMap_swap_pDM : Semiformula.lMap swap pDM = qCM ⋏ qDM := by
  rw [pDM_def, LogicalConnective.HomClass.map_and, lMap_swap_qDM, lMap_swap_qCM]

/-- **`instB ⌜pDM⌝ k` is the conjunction of the two instances.** -/
theorem instB_quote_pDM (k : V) :
    instB (⌜pDM⌝ : V) k = instB (⌜qDM⌝ : V) k ^⋏ instB (⌜qCM⌝ : V) k :=
  instB_quote_and qDM qCM k

lemma formulaLen_instB_pDM (k : V) :
    formulaLen LAct (instB (⌜pDM⌝ : V) k) =
      formulaLen LAct (instB (⌜qDM⌝ : V) k) + formulaLen LAct (instB (⌜qCM⌝ : V) k) + 1 := by
  rw [instB_quote_pDM,
    formulaLen_and (isFormula_instB_quote qDM k).isUFormula (isFormula_instB_quote qCM k).isUFormula]

/-- **Both searchers find their guards against Mirror from a box of the conjunction**: for every
budget `a` with `a + 8(|instB ⌜qDM⌝ k| + |instB ⌜qCM⌝ k|) + 7 ≤ k`, a `TAct`-proof code of the
`k`-instance of `pDM` of length `≤ a` makes `DupocV k` cooperate with Mirror and `CupodV k`
defect against Mirror (fuel 2). -/
theorem pDM_both_V (k : V) : ∀ a : V,
    a + 8 * (formulaLen LAct (instB (⌜qDM⌝ : V) k) + formulaLen LAct (instB (⌜qCM⌝ : V) k)) + 7 ≤ k →
    LenDerivable TAct a (instB (⌜pDM⌝ : V) k) →
    EvalGraph 2 (DupocV k) MirrorV (DupocV k) 0 ∧ EvalGraph 2 (CupodV k) MirrorV (CupodV k) 1 := by
  intro a ha h
  rw [instB_quote_pDM] at h
  have hx := isFormula_instB_quote qDM k
  have hy := isFormula_instB_quote qCM k
  have h₁ := lenDerivable_mono_V ha (lenDerivable_andL_V hx hy h)
  have h₂ := lenDerivable_mono_V ha (lenDerivable_andR_V hx hy h)
  rw [lenDerivable_iff_lenProvableV, ← guardCode_DupocV_MirrorV_eq_instB] at h₁
  rw [lenDerivable_iff_lenProvableV, ← guardCode_CupodV_MirrorV_eq_instB] at h₂
  exact ⟨dupoc_mirror_search_V k h₁, cupod_mirror_search_V k h₂⟩

/-- **Both searchers FIND their guards against Mirror** (the box form of `pDM_both_V`). -/
theorem pDM_guards_V (k : V) (a : V)
    (ha : a + 8 * (formulaLen LAct (instB (⌜qDM⌝ : V) k) + formulaLen LAct (instB (⌜qCM⌝ : V) k)) + 7 ≤ k)
    (hpc : LenDerivable TAct a (instB (⌜pDM⌝ : V) k)) :
    LenProvableV TAct k (guardCode (⌜GtmplA 0⌝ : V) (DupocV k) MirrorV) ∧
    LenProvableV TAct k (guardCode (⌜GtmplA 1⌝ : V) (CupodV k) MirrorV) := by
  rw [instB_quote_pDM] at hpc
  have hx := isFormula_instB_quote qDM k
  have hy := isFormula_instB_quote qCM k
  have h₁ := lenDerivable_mono_V ha (lenDerivable_andL_V hx hy hpc)
  have h₂ := lenDerivable_mono_V ha (lenDerivable_andR_V hx hy hpc)
  rw [lenDerivable_iff_lenProvableV, ← guardCode_DupocV_MirrorV_eq_instB] at h₁
  rw [lenDerivable_iff_lenProvableV, ← guardCode_CupodV_MirrorV_eq_instB] at h₂
  exact ⟨h₁, h₂⟩

/-! #### `pDM` in both readings -/

/-- `pDM(k)` in the standard reading: Mirror plays C against Dupoc AND D against Cupod. -/
theorem eval_pDM_iff_std (k : V) :
    Semiformula.Eval (s := stdActV V) ![k] Empty.elim pDM ↔
      (∃ n, EvalGraph n MirrorV (DupocV k) MirrorV 0) ∧
      (∃ n, EvalGraph n MirrorV (CupodV k) MirrorV 1) := by
  rw [pDM_def]
  simp only [LogicalConnective.HomClass.map_and, LogicalConnective.Prop.and_eq]
  rw [eval_qDM_iff_V, eval_qCM_iff_V]

/-- `pDM(k)` in the swapped reading: the SAME content (the conjuncts exchange roles). -/
theorem eval_pDM_iff_swap (k : V) :
    Semiformula.Eval (s := swapActS V) ![k] Empty.elim pDM ↔
      (∃ n, EvalGraph n MirrorV (DupocV k) MirrorV 0) ∧
      (∃ n, EvalGraph n MirrorV (CupodV k) MirrorV 1) := by
  rw [eval_swapActS, lMap_swap_pDM, ← stdActV_eq_stdActS]
  simp only [LogicalConnective.HomClass.map_and, LogicalConnective.Prop.and_eq]
  rw [eval_qDM_iff_V, eval_qCM_iff_V, and_comm]

/-- `pDM(k)` in the standard reading, `stdActS` form. -/
theorem eval_pDM_iff_stdActS (k : V) :
    Semiformula.Eval (s := stdActS V) ![k] Empty.elim pDM ↔
      (∃ n, EvalGraph n MirrorV (DupocV k) MirrorV 0) ∧
      (∃ n, EvalGraph n MirrorV (CupodV k) MirrorV 1) := by
  rw [← stdActV_eq_stdActS]; exact eval_pDM_iff_std k

end conj

/-! ### 5. The Löb premise, the engine, and the cells at ℕ -/

section cells

/-- **The bounded Löb premise of the Mirror family, slack `(7, 8)`**: a proof code of `pDM(k)` of
length `a` with `a + 7 + 8·|pDM(k)| ≤ k` makes both searchers find their guards (`pDM_both_V`), so
Mirror COPIES at fuel 3 and `pDM(k)` is TRUE in both readings. -/
theorem loebSound_pDM : LoebSound pDM 7 8 := by
  intro V _ _ k a ha h
  have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
  have ha' : a + 8 * (formulaLen LAct (instB (⌜qDM⌝ : V) k) + formulaLen LAct (instB (⌜qCM⌝ : V) k)) + 7 ≤ k :=
    le_trans (pConj_slack_le a _ _ _ (formulaLen_instB_pDM k)) ha
  obtain ⟨h1, h2⟩ := pDM_both_V k a ha' h
  exact ⟨(eval_pDM_iff_stdActS k).mpr ⟨⟨3, mirror_copies_dupoc_V k h1⟩, ⟨3, mirror_copies_cupod_V k h2⟩⟩,
    (eval_pDM_iff_swap k).mpr ⟨⟨3, mirror_copies_dupoc_V k h1⟩, ⟨3, mirror_copies_cupod_V k h2⟩⟩⟩

/-- **The Mirror cells, packaged**: for all large `k`, both searchers find their guards against
Mirror (fuel 2) and both guard boxes hold — `family_found pDM` (the arithmetized `pblt_engine`)
then the ∧-elimination on codes. -/
theorem dupoc_mirror_cell_core {d : ℕ} (hE : BoundedInnerNec d) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      (EvalGraph 2 (Dupoc k) Mirror (Dupoc k) 0 ∧ EvalGraph 2 (Cupod k) Mirror (Cupod k) 1) ∧
      (LenProvableV TAct k (guardCode (⌜GtmplA 0⌝ : ℕ) (Dupoc k) Mirror) ∧
        LenProvableV TAct k (guardCode (⌜GtmplA 1⌝ : ℕ) (Cupod k) Mirror)) := by
  obtain ⟨k₀, h⟩ := family_found pDM hE loebSound_pDM
  refine ⟨k₀, fun k hk ↦ ?_⟩
  obtain ⟨a, ha, hpc⟩ := h k hk
  have ha' := le_def.mpr (pConj_slack_nat a _ _ _ k (formulaLen_instB_pDM (V := ℕ) k) ha)
  exact ⟨pDM_both_V k a ha' hpc, pDM_guards_V k a ha' hpc⟩

/-- **Dupoc × Mirror is `(C, C)` in PA-`S'`, conditional on bounded inner necessitation**: for all
large `k`, `Dupoc k` cooperates with Mirror (fuel 2) and Mirror copies (fuel 3). -/
theorem dupoc_mirror_coop {d : ℕ} (hE : BoundedInnerNec d) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 2 (Dupoc k) Mirror (Dupoc k) 0 ∧ EvalGraph 3 Mirror (Dupoc k) Mirror 0 := by
  obtain ⟨k₀, h⟩ := dupoc_mirror_cell_core hE
  exact ⟨k₀, fun k hk ↦ ⟨(h k hk).1.1, mirror_copies_dupoc_V (V := ℕ) k (h k hk).1.1⟩⟩

/-- **Cupod × Mirror is `(D, D)` in PA-`S'`, conditional on bounded inner necessitation**: for all
large `k`, `Cupod k` defects against Mirror (fuel 2) and Mirror copies (fuel 3). -/
theorem cupod_mirror_defect {d : ℕ} (hE : BoundedInnerNec d) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 2 (Cupod k) Mirror (Cupod k) 1 ∧ EvalGraph 3 Mirror (Cupod k) Mirror 1 := by
  obtain ⟨k₀, h⟩ := dupoc_mirror_cell_core hE
  exact ⟨k₀, fun k hk ↦ ⟨(h k hk).1.2, mirror_copies_cupod_V (V := ℕ) k (h k hk).1.2⟩⟩

/-- **The box form**: for all large `k`, Dupoc actually FINDS a proof of its guard against Mirror
within its budget `k` (conditional). -/
theorem dupoc_finds_guard_vs_mirror {d : ℕ} (hE : BoundedInnerNec d) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k → LenProvableV TAct k (guardCode (⌜GtmplA 0⌝ : ℕ) (Dupoc k) Mirror) := by
  obtain ⟨k₀, h⟩ := dupoc_mirror_cell_core hE
  exact ⟨k₀, fun k hk ↦ (h k hk).2.1⟩

/-- **The box form**: for all large `k`, Cupod FINDS a proof of its guard against Mirror within
its budget `k` (conditional). -/
theorem cupod_finds_guard_vs_mirror {d : ℕ} (hE : BoundedInnerNec d) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k → LenProvableV TAct k (guardCode (⌜GtmplA 1⌝ : ℕ) (Cupod k) Mirror) := by
  obtain ⟨k₀, h⟩ := dupoc_mirror_cell_core hE
  exact ⟨k₀, fun k hk ↦ (h k hk).2.2⟩

/-! #### Unconditional, at `boundedInnerNec_sixteen` -/

/-- **Dupoc × Mirror `(C, C)` in PA-`S'`, unconditional**: for all large `k`, `Dupoc k` cooperates
with Mirror and Mirror copies. -/
theorem dupoc_mirror_coop_unconditional :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 2 (Dupoc k) Mirror (Dupoc k) 0 ∧ EvalGraph 3 Mirror (Dupoc k) Mirror 0 :=
  dupoc_mirror_coop boundedInnerNec_sixteen

/-- **Cupod × Mirror `(D, D)` in PA-`S'`, unconditional**: for all large `k`, `Cupod k` defects
against Mirror and Mirror copies. -/
theorem cupod_mirror_defect_unconditional :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 2 (Cupod k) Mirror (Cupod k) 1 ∧ EvalGraph 3 Mirror (Cupod k) Mirror 1 :=
  cupod_mirror_defect boundedInnerNec_sixteen

/-- **Dupoc finds its guard against Mirror, unconditional.** -/
theorem dupoc_finds_guard_vs_mirror_unconditional :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k → LenProvableV TAct k (guardCode (⌜GtmplA 0⌝ : ℕ) (Dupoc k) Mirror) :=
  dupoc_finds_guard_vs_mirror boundedInnerNec_sixteen

/-- **Cupod finds its guard against Mirror, unconditional.** -/
theorem cupod_finds_guard_vs_mirror_unconditional :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k → LenProvableV TAct k (guardCode (⌜GtmplA 1⌝ : ℕ) (Cupod k) Mirror) :=
  cupod_finds_guard_vs_mirror boundedInnerNec_sixteen

end cells

end ArithS
