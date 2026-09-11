import ArithS.Agent
import ArithS.AgentConverse
import ArithS.Core.Sound
import ArithS.Cut
import ArithS.CutV
import ArithS.Det
import ArithS.FitBox
import ArithS.Inst

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
