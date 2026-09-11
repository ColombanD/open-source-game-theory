import ArithS.Agent
import ArithS.AgentConverse
import ArithS.Core.Sound
import ArithS.Cut
import ArithS.CutV
import ArithS.ProperV
import ArithS.InstV
import ArithS.Diag
import ArithS.Det
import ArithS.FitBox
import ArithS.Inst
import ArithS.Instance
import ArithS.InstanceV
import ArithS.Transparency
import ArithS.Assembly.Prep

/-!
# ArithS.Audit — the axiom census of the arithmetized layer

Every headline theorem of tiers T1 and T2, with `#print axioms`. Building this module (it is
the last import of `ArithS.lean`) prints the census; each line must read
`[propext, Classical.choice, Quot.sound]` — Lean's three standard axioms and nothing else.
The `example`s below FAIL TO COMPILE if any of these theorems disappears or changes its name,
so the census is also a freshness check for the paper's claims.
-/

namespace ArithS

-- T1: the red cell, at every shared budget, fuel 2; and its non-vacuity.
example : ∀ k : ℕ, EvalGraph 2 (Dupoc k) (Cupod k) (Dupoc k) 1 ∧ EvalGraph 2 (Cupod k) (Dupoc k) (Cupod k) 0 :=
  red_cell
#print axioms red_cell
#print axioms red_cell_unique
#print axioms guard_fits
#print axioms guard_fits'

-- τ-closure of TAct at every proof length (the engine's `Pf.transpose`, on codes).
#print axioms lenProvable_fbound_swap_iff
#print axioms swapcode_swapcode
#print axioms swapcode_psubst

-- M4, first field — bounded D2 in rule form: PA-S closes under modus ponens at additive
-- cost `k₁ + k₂ + 10(|φ| + |ψ|) + 9` (sharp: `5|φ| + 10|ψ| + 9`); budget monotonicity; verum.
#print axioms lenProvable_mp
#print axioms lenProvable_mp_sharp
#print axioms lenProvableV_mp
#print axioms lenProvable_fbound_mono
#print axioms lenProvable_verum
#print axioms mlen_cutMP

-- M4, bounded D2 INSIDE every model of IΣ₁ (CutV): the cut on codes with dlen accounting —
-- unconditional for `LenDerivable` (no code bound), under `ProperV` for `LenProvableV`
-- (a theorem at ℕ), and as ONE ℒₒᵣ-sentence proved by IΣ₁/PA/TAct via the completeness theorem.
#print axioms lenDerivable_cut_V
#print axioms lenProvableV_cut_V
#print axioms lenProvableV_mono_V
#print axioms properV_nat_TAct
#print axioms pa_proves_cutSentence
#print axioms tact_proves_cutSentence

-- M4, properness INSIDE every model of IΣ₁ (ProperV): the code/length chain of `Proper.lean`
-- redone on internal codes by the internal induction principles (no quotes) — `ProperV V TAct`
-- is a THEOREM, so bounded D2 for `LenProvableV` is unconditional and the Σ₁ box
-- `LenDerivable` (the Löb argument's) coincides with the Δ₁ box `LenProvableV` (the evaluator's).
#print axioms properV_of_small
#print axioms properV_TAct
#print axioms lenProvableV_cut_V'
#print axioms lenDerivable_iff_lenProvableV

-- M4, U1 + U3 (InstV): the bnum-instance operator `instB` (Σ₁ graph, code equation, length
-- `|instB n k| ≤ |n|·|bnum k|`), the parametric box `bewB` (Σ₁), and Quantifier Distribution
-- on codes with dlen accounting (`N + 5|χ[bnum k]| + 3|χ| + |bnum k| + 7`) — V-generic, its
-- meta twin at ℕ (the final PBLT step), and as ONE ℒₒᵣ-sentence proved by IΣ₁/PA/TAct.
#print axioms instB.defined
#print axioms quote_instB
#print axioms formulaLen_instB_le
#print axioms bewB.defined
#print axioms lenDerivable_inst_V
#print axioms lenDerivable_instB_V
#print axioms lenDerivable_instB_V'
#print axioms lenProvable_inst
#print axioms lenProvable_inst_size
#print axioms pa_proves_instSentence
#print axioms tact_proves_instSentence

-- M4, U6 (Diag): the parametric diagonal lemma over TAct for LAct formulas — Foundation's
-- construction transported along the reduct (`substNumeralParamsA` twin of `substNumeralParams`,
-- `tactFixedpoint`), through completeness with equality (`𝗘𝗤 LAct ⪯ TAct`, `tact_complete`);
-- the instances at `bnum k` (∀-elimination), their truth in every model and their internal
-- provability (D1).
#print axioms eqAxiom_weakerThan_TAct
#print axioms tact_complete
#print axioms tact_complete'
#print axioms substNumeralParamsA_app_quote
#print axioms tact_parametric_diagonal₁
#print axioms tact_parametric_diagonal
#print axioms tact_parametric_diagonal_inst
#print axioms models_tact_parametric_diagonal_inst
#print axioms provable_code_parametric_diagonal_inst

-- U0b (TheoryAct, 2026-09-12): the action axiom `axAct : (c_C = 0 ∧ c_D = 1) ∨ (c_C = 1 ∧ c_D = 0)`
-- — TAct proves it, its model class is exactly the two standard readings (`stdActS`/`swapActS`),
-- and ℕ satisfies it. Without it no guard sentence was TAct-provable (a vacuity).
#print axioms tact_proves_axAct
#print axioms models_axAct_iff
#print axioms eval_axAct_iff
#print axioms structure_eq_of_axAct
#print axioms models_axAct
#print axioms lMap_swap_axAct

-- M4 U0 — programs described by TERMS over the polynomial pairing: Dupoc's guard sentence
-- against itself is the `k`-instance `q ⇜ ![k̂]` of ONE fixed one-variable formula (meta), and on
-- codes `subst (bnum k ∷ 0) cq` (Critch's "source with `k` written in binary"); the description
-- of a program denotes its code (`val_progTT`) and codes are what the guard names (`quote_progTT`).
#print axioms exists_dupoc_instance
#print axioms exists_dupoc_instance_code
#print axioms exists_dupoc_instance_code_V
#print axioms quote_progTT
#print axioms val_progTT
#print axioms size_le_tlen_progTT

-- M4 U7 — Dupoc transparency (Critch's step 0) in EVERY model of IΣ₁, at every (possibly
-- nonstandard) budget `k : V`, in the `LAct`-structure `stdActV V` (`c_C ↦ 0`, `c_D ↦ 1`): the
-- description term denotes the canonical code, the truth equation of `qDupoc` ("Dupoc plays C
-- against itself"), the search clause at fuel 2, the Löb premise `bewB k ⌜qDupoc⌝ k → qDupoc(k)`
-- under `ProperV V TAct` (unconditional at ℕ), and the uniform ℒₒᵣ-sentence with the Δ₁ box,
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

-- M4 assembly prep (Assembly/Prep, 2026-09-12): Cupod's instance equation on codes and search
-- clause in every model; the truth equations in BOTH readings (`swapActS` pulled back to
-- `stdActS`); the conjunction family `pConj = qDupoc ⋏ qCupod` with `instB` distributing over
-- the code connectives and ∧-elimination on codes with dlen accounting (`a + 8(|x|+|y|) + 7`),
-- so a box of the `k`-instance of `pConj` makes BOTH searchers find their guards; the box
-- formula `Box_g` (`g k = ‖k‖²`) with its semantics, `θ` (`#0` = code slot, `#1` = budget) and
-- the fixed point `psi` with `TAct ⊢ ∀¹ (psi 🡘 (Box_g psi 🡒 pConj))`; Σ₁ upward transfer of a
-- bounded proof code from ℕ to every model, and a length for every `TAct`-theorem.
#print axioms guardCode_CupodV_eq_instB
#print axioms cupod_search_V
#print axioms eval_qCupod_iff_V
#print axioms eval_swapActS
#print axioms eval_qDupoc_swap_iff_V
#print axioms eval_qCupod_swap_iff_V
#print axioms instB_quote_pConj
#print axioms instB_imp
#print axioms lenDerivable_andL_V_sharp
#print axioms lenDerivable_andR_V_sharp
#print axioms lenDerivable_andL_V
#print axioms lenDerivable_andR_V
#print axioms pconj_both_V
#print axioms eval_pConj_iff_std
#print axioms eval_pConj_iff_swap
#print axioms gBudget.defined
#print axioms eval_Box_g_iff
#print axioms theta_subst_code
#print axioms psi_fixed_point
#print axioms models_psi_fixed_point
#print axioms lenDerivable_of_nat
#print axioms lenDerivable_of_proof
#print axioms exists_lenDerivable_V_of_proof

-- T2-CORE: the modal-propositional core is sound over PA (budget erased).
#print axioms Core.Pf_core_sound

-- T2-NEG: no budget-keeping transfer at any inflation.
#print axioms no_budget_keeping_transfer

-- T2-AGENT: engine certificates are arith evaluator runs, same budgets.
#print axioms playsProof_evalGraph
#print axioms playsProof_evalGraph_searchFree
#print axioms atomProvable_evalGraph
#print axioms models_trAt_plays

-- T2-AGENT converse: eval ↔ EvalGraph on modest programs under the two-sided oracle.
#print axioms eval_of_evalGraph
#print axioms evalGraph_of_eval
#print axioms eval_iff_evalGraph
#print axioms play_iff_evalGraph
#print axioms outcome_iff_evalGraph
#print axioms playsProof_evalGraph_of_guardAgree
#print axioms plays_interp_iff
#print axioms GuardAgree.toF

-- Instantiation `c_C ↦ 0, c_D ↦ 1`: PA proves the atom sentences of modest plays
-- (Σ₁-completeness); the `atom`/`atomBoxImpl` leaves of T2-CORE discharged at `Aι`.
#print axioms LAct.models_inst
#print axioms hierarchy_lMap_inst_trAt_plays
#print axioms pa_proves_trAt_inst
#print axioms pa_proves_trAt_inst_of_atomProvable
#print axioms pa_proves_trAt_inst_searchFree
#print axioms leaf_atom_sound
#print axioms leaf_atom_sound_searchFree
#print axioms leaf_atomBoxImpl_sound
#print axioms transfer_of_leaves

-- Code translation: substitution code equations and τ on the search-bot fragment.
#print axioms pcode_subst
#print axioms tcode_subst
#print axioms swapcode_pcode

-- Det: determinism in every model of IΣ₁; the negative atom; the atomNeg leaf of T2-CORE.
#print axioms EvalGraph.unique_V'
#print axioms models_trAt_plays_V
#print axioms pa_proves_neg_trAt_inst
#print axioms leaf_atomNeg_sound
#print axioms leaf_atomNeg_sound_searchFree

-- FitBox: Critch's (b) for box-carrying guards — the positive budget-linear bound and the
-- obstruction: under Cantor pairing a searcher whose guard names its own budget cannot fit.
#print axioms size_bnum_ge
#print axioms exists_flen_tmpl_const
#print axioms box_guard_never_fits
#print axioms legibleBot_guard_never_fits

end ArithS
