import ArithS.Bridge.Inst

/-!
# ArithS.Audit.Bridge — the axiom census of the arithmetized layer: Bridge

This file covers the T2 bridge modules (`Bridge/`, frozen): T2-CORE, T2-NEG (retired), T2-AGENT
and its converse, the instantiation.

Split out of the former single `ArithS/Audit.lean` on 2026-09-28; every `#print axioms` line and its
comment block are verbatim (the comment blocks are the historical record). `ArithS/Audit.lean` imports
the nine per-layer files; each line must read `[propext, Classical.choice, Quot.sound]`.
-/

namespace ArithS

-- T2-CORE: the modal-propositional core is sound over PA (budget erased).
#print axioms Core.Pf_core_sound

-- T2-NEG: RETIRED 2026-09-16 by the atom re-cost (`no_budget_keeping_transfer` is no longer
-- statable — its witness is not an engine theorem any more); what remains is the record that
-- the witness now pays for the program it names, and that every engine theorem fits its budget.
#print axioms no_budget_keeping_witness_pays
#print axioms pf_size

-- T2-AGENT: engine certificates are arith evaluator runs, same budgets.
#print axioms playsProof_evalGraph
#print axioms playsProof_evalGraph_searchFree
#print axioms atomProvable_evalGraph
#print axioms models_sentenceAt_plays

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
#print axioms hierarchy_lMap_inst_sentenceAt_plays
#print axioms pa_proves_sentenceAt_inst
#print axioms pa_proves_sentenceAt_inst_of_atomProvable
#print axioms pa_proves_sentenceAt_inst_searchFree
#print axioms leaf_atom_sound
#print axioms leaf_atom_sound_searchFree
#print axioms leaf_atomBoxImpl_sound
#print axioms transfer_of_leaves

end ArithS
