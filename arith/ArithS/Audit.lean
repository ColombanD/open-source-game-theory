import ArithS.Agent
import ArithS.AgentConverse
import ArithS.Core.Sound

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

-- Code translation: substitution code equations and τ on the search-bot fragment.
#print axioms pcode_subst
#print axioms tcode_subst
#print axioms swapcode_pcode

end ArithS
