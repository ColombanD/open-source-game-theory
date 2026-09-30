import ArithS.Agents.SubstTemplate
import ArithS.Agents.SysClose
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
-- codes `subst (binNumeral k ∷ 0) cq` (Critch's "source with `k` written in binary"); the description
-- of a program denotes its code (`val_codeTermMeta`) and codes are what the guard names (`quote_codeTermMeta`).
#print axioms exists_dupoc_instance
#print axioms exists_dupoc_instance_code
#print axioms exists_dupoc_instance_code_V
#print axioms quote_codeTermMeta
#print axioms val_codeTermMeta
#print axioms size_le_termLenMeta_codeTermMeta

-- Code translation: substitution code equations and τ on the search-bot fragment.
#print axioms progCode_subst
#print axioms templateCode_subst
#print axioms transposeCode_progCode

-- FitBox: Critch's (b) for box-carrying guards — the positive budget-linear bound and the
-- obstruction: under Cantor pairing a searcher whose guard names its own budget cannot fit.
#print axioms size_binNumeral_ge
#print axioms exists_formulaLenMeta_template_const
#print axioms box_guard_never_fits
#print axioms legibleBot_guard_never_fits

-- Phase 2 (2026-09-30) — the tau constructors in the trusted base, agents layer: the codes `pTvote`/`pSys`/
-- `pSelfIdx`/`pCons` are shapes with τ, description terms and substitution (`revalue_sys`, `codeTerm_sys`,
-- `substCode_sys`); member lookup and the system closer are total Σ₁ functions (`listGet`, `sysCloseCode`);
-- the member slots `#7..#12` never touch a seven-variable template (`sysCloseTemplate_of_template₇`); every
-- program code is a shape (`isShape_progCode`), so no compiled instance has the code `0`.
#print axioms transposeCode_transposeCode
#print axioms revalue_sys
#print axioms codeTerm_sys
#print axioms termLenMeta_emb_codeTermMeta_sys
#print axioms listGet_cons_succ
#print axioms sysCloseCode_selfIdx
#print axioms sysCloseCode_search
#print axioms sysCloseTemplate_of_template₇
#print axioms isShape_progCode
#print axioms progCode_ne_zero
#print axioms listGet_progListCode_some
#print axioms progCode_subst_tauSearchFree
#print axioms progCode_sysClose_tauSearchFree

end ArithS
