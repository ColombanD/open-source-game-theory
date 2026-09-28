import ArithS.Agents.Subst

/-!
# ArithS.Audit.Theory — the axiom census of the arithmetized layer: Theory

This file covers the theory layer (`Theory/`): `TAct`'s action axiom and its model class, and
τ-closure of `TAct` at every proof length.

Split out of the former single `ArithS/Audit.lean` on 2026-09-28; every `#print axioms` line and its
comment block are verbatim (the comment blocks are the historical record). `ArithS/Audit.lean` imports
the nine per-layer files; each line must read `[propext, Classical.choice, Quot.sound]`.
-/

namespace ArithS

-- τ-closure of TAct at every proof length (the engine's `Pf.transpose`, on codes).
#print axioms lenProvable_fbound_swap_iff
#print axioms swapcode_swapcode
#print axioms swapcode_psubst

-- U0b (TheoryAct, 2026-09-12): the action axiom `axAct : (c_C = 0 ∧ c_D = 1) ∨ (c_C = 1 ∧ c_D = 0)`
-- — TAct proves it, its model class is exactly the two standard readings (`stdActS`/`swapActS`),
-- and ℕ satisfies it. Without it no guard sentence was TAct-provable (a vacuity).
#print axioms tact_proves_axAct
#print axioms models_axAct_iff
#print axioms eval_axAct_iff
#print axioms structure_eq_of_axAct
#print axioms models_axAct
#print axioms lMap_swap_axAct

end ArithS
