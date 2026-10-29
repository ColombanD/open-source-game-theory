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

-- T2-NEG: RETIRED 2026-09-16 by the atom re-cost (`no_budget_keeping_transfer` is no longer
-- statable — its witness is not an engine theorem any more); what remains is the record that
-- the witness now pays for the program it names, and that every engine theorem fits its budget.

-- T2-AGENT: engine certificates are arith evaluator runs, same budgets.
#print axioms models_sentenceAt_plays

-- T2-AGENT converse: eval ↔ EvalGraph on modest programs under the two-sided oracle.

-- Instantiation `c_C ↦ 0, c_D ↦ 1`: PA proves the atom sentences of modest plays
-- (Σ₁-completeness); the `atom`/`atomBoxImpl` leaves of T2-CORE discharged at `Aι`.
#print axioms LAct.models_inst
#print axioms hierarchy_lMap_inst_sentenceAt_plays

end ArithS
