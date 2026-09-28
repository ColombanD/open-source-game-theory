import ArithS.Agents.InstanceV
import ArithS.Agents.FitBox

/-!
# ArithS.Audit.Agents — the axiom census of the arithmetized layer: Agents

This file covers the agents layer (`Agents/`): programs described by terms, the code translation
and τ on the search-bot fragment, and `FitBox`.

Split out of the former single `ArithS/Audit.lean` on 2026-09-28; every `#print axioms` line and its
comment block are verbatim (the comment blocks are the historical record). `ArithS/Audit.lean` imports
the nine per-layer files; each line must read `[propext, Classical.choice, Quot.sound]`.
-/

namespace ArithS

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

-- Code translation: substitution code equations and τ on the search-bot fragment.
#print axioms pcode_subst
#print axioms tcode_subst
#print axioms swapcode_pcode

-- FitBox: Critch's (b) for box-carrying guards — the positive budget-linear bound and the
-- obstruction: under Cantor pairing a searcher whose guard names its own budget cannot fit.
#print axioms size_bnum_ge
#print axioms exists_flen_tmpl_const
#print axioms box_guard_never_fits
#print axioms legibleBot_guard_never_fits

end ArithS
