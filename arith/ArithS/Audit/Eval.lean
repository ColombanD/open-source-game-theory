import ArithS.Readings
import ArithS.Eval.Fixpoint
import ArithS.Eval.Transparency
import ArithS.Eval.TauCheck

/-!
# ArithS.Audit.Eval — the axiom census of the arithmetized layer: Eval

This file covers the evaluator layer (`Eval/`): Dupoc transparency in every model
(`Transparency`) and determinism (`Det`).

Split out of the former single `ArithS/Audit.lean` on 2026-09-28; every `#print axioms` line and its
comment block are verbatim (the comment blocks are the historical record). `ArithS/Audit.lean` imports
the nine per-layer files; each line must read `[propext, Classical.choice, Quot.sound]`.
-/

namespace ArithS

-- M4 U7 — Dupoc transparency (Critch's step 0) in EVERY model of IΣ₁, at every (possibly
-- nonstandard) budget `k : V`, in the `LAct`-structure `stdReadingV V` (`c_C ↦ 0`, `c_D ↦ 1`): the
-- description term denotes the canonical code, the truth equation of `qDupoc` ("Dupoc plays C
-- against itself"), the search clause at fuel 2, the Löb premise `bewB k ⌜qDupoc⌝ k → qDupoc(k)`
-- under `ProperBound V TAct` (unconditional at ℕ), and the uniform ℒₒᵣ-sentence with the Δ₁ box,
-- provable in IΣ₁/PA (completeness) and in TAct along `emb`.
#print axioms val_TD_V
#print axioms eval_qDupoc_iff_V
#print axioms dupoc_search_V
#print axioms dupoc_search_instB_V
#print axioms dupoc_loeb_premise_V
#print axioms dupoc_loeb_premise_nat
#print axioms dupoc_loeb_premise_guardSentence
#print axioms dupoc_loeb_premise_evalGraph
#print axioms isigma1_proves_dupocPremise
#print axioms pa_proves_dupocPremise
#print axioms tact_proves_dupocPremise

-- Det: determinism in every model of IΣ₁; the negative atom; the atomNeg leaf of T2-CORE.
#print axioms EvalGraph.unique_V'
#print axioms models_sentenceAt_plays_V
#print axioms pa_proves_neg_sentenceAt_inst
#print axioms leaf_atomNeg_sound
#print axioms leaf_atomNeg_sound_searchFree

-- Phase 2 (2026-09-30) — the tau constructors in the evaluator: the inversion lemmas of the three new
-- clauses, determinism and monotonicity across them (`EvalGraph.unique`, `EvalGraph.mono`, at ℕ;
-- `EvalGraph.unique_V'` in every model), the one-step unfolding of the engine's `cfdSys k` system, and the
-- lockstep theorem with the engine's `eval` on the tau-search-free fragment (`Eval/TauCheck.lean`).
#print axioms EvalGraph.tvote_cons_iff
#print axioms EvalGraph.sys_iff
#print axioms EvalGraph.selfIdx_iff
#print axioms EvalGraph.unique
#print axioms EvalGraph.mono
#print axioms evalGraph_cfdSys_unfold
#print axioms sysCloseCode_cfdSys_member
-- Phase 2, the pronoun reading (2026-10-01): the closed member's stored template is the template code of the
-- engine's closed guard (`.bot (.sys (cfdSys k) (1 - i))` plays C against itself).
#print axioms sysCloseTemplate_cfdGuard
#print axioms progCode_cfdSys_ne_zero
#print axioms evalGraph_of_eval_tauSearchFree
#print axioms evalGraph_of_eval_sys_step
#print axioms evalGraph_of_eval_tvote_nil
#print axioms evalGraph_of_eval_tvote_zero

end ArithS
