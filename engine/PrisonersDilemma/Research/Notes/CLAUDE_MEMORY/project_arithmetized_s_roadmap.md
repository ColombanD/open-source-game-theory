---
name: project-arithmetized-s-roadmap
description: "Arithmetized S on Foundation (arith/ArithS): T1 red cell proven and non-vacuous; M3 DONE 2026-09-10 on canonical branch colomban-arith-m3 (~/wt/osgt-arith-m3, engine on v4.33.1) — T2 = T2-CORE + T2-NEG + T2-AGENT, all 3-axiom; what is out of scope (box compositionality, tau constructors, LAct Σ₁-completeness) and the traps"
metadata: 
  node_type: memory
  type: project
  originSessionId: 1a734d76-f764-480d-8461-59dedf4d8e0a
  modified: 2026-09-10T13:50:42.554Z
---

Decision 2026-09-09 (Colomban): ARITHMETIZED instance of `S` on Foundation, proof LENGTH
measure, standalone package `arith/` (`ArithS`). Plan + full status log:
`engine/PrisonersDilemma/Research/Notes/ARITHMETIZED_S_ROADMAP.md` (kept in sync on both
branches); design materials `Research/Notes/M3_TRANSFER/`.

**STATE 2026-09-10 (end of the M3 push), canonical branch `colomban-arith-m3` in
`~/wt/osgt-arith-m3` (engine bumped to Lean v4.33.1 + arith merged; `lake build ArithS`
green, ~3200 jobs, incremental ~15 s). OneDrive checkout stays on `colomban-arith-s`
(arith-only, engine v4.28) — develop on `-m3`, sync docs to `-s` by copying the roadmap.**
Proven, all `#print axioms` = the three standard ones:
- T1 `red_cell` (Dupoc, Cupod) = (D, C) every k; non-vacuous: `guard_fits` (binary
  descriptions, Critch's (b)). 6-variable templates `pSearch k g p q`, τ acts on templates
  (`relabelTemplate`), `psubst`/`pSim` semantics with unconditional τ-equivariance.
- T2-CORE `Core.Pf_core_sound`: budget-erased modal-propositional core sound over PA
  (ProvabilityAbstraction D1–D3, kreisel fixpoint), non-core rules as the `Leaf` hypothesis.
- T2-NEG `no_budget_keeping_transfer`: no inflation `e` makes `Pf k φ → PA ⊢_{e k} tr φ`
  true (atoms are charged by evaluation steps: `Pf 1 (plays (const C) (bot^m (const C)) C)`).
- T2-AGENT `playsProof_evalGraph`: engine evaluation certificates are arith evaluator runs
  at the same budgets, given `GuardAgreeT/F` on the consulted guards; unconditional
  `playsProof_evalGraph_searchFree`; truth equation `models_trAt_plays`. Fragment = the
  engine's MODEST programs (`modestP`, all sim arguments placeholder-or-closed — true of
  the whole zoo), players `Proper` (≠ .self/.opp).
- AFTER M3 (same day): `AgentConverse` — `eval_iff_evalGraph`/`play_iff`/`outcome_iff` under ONE
  two-sided `GuardAgree` (restricted to modest proper frames); `GuardAgreeF` derived from engine
  soundness. `Inst` — hom `inst : LAct →ᵥ ℒₒᵣ` (c_C ↦ 0, c_D ↦ 1); `pa_proves_trAt_inst`: PA proves
  the atom sentence of every modest play (Σ₁-completeness), unconditional for search-free
  programs; T2-CORE's atom leaves discharged (`leaf_atom_sound`, `leaf_atomBoxImpl_sound`,
  `transfer_of_leaves`). Still hypotheses: the 12 source-reading leaves (= bounded D1) and
  `atomNeg` (needs PA-internal determinism, ~150 lines of general-model eval lemmas). Audit.lean
  census: 33 theorems, all three standard axioms.
- Code translation `pcode/tmpl/tcode` with substitution code equations + τ on the box-free
  search-bot fragment `fragP/fragF`.

**Boundaries (honest, recorded, not gaps in proofs):** `.box` cannot be translated
compositionally under LENGTH-bounded provability (the box carries its body's code as a
numeral; provable equivalence ≠ identity) — so T2-AGENT's box facts are hypotheses, exactly
bounded D1 (Critch's (d), M4). Truth → `TAct ⊢` for `trAt` sentences needs Σ₁-completeness
over `LAct` with the two constants (Foundation's is ℒₒᵣ-only) — open. tvote/sys/selfIdx
outside (code 0). `GuardAgreeF` from engine soundness needs the converse of T2-AGENT.
Paper sentence: "S is sound relative to PA wherever a character count exists; where the
engine charges steps/cheap citations, no PA proof length can match — proven; bounded
soundness is exactly Critch's (d)". The budget-erased world is Berns/Barász's — novelty
stays the BOUNDED S.

**Traps:** closed constants built from the template (`flen Gtmpl`, `⌜Gtmpl⌝` pairs) must
never enter kernel-compared `Nat` arithmetic — package existentially; `lake env lean` output
is block-buffered when redirected (bisect by truncation with `timeout`); at V = ℕ `<` is
Nat's but `≤` is PeanoMinus's (`le_def`); omega useless on Foundation orders; `Formula`
must be `PD.Formula`; `simp` never rewrites the instance-implicit structure of
`Semiformula.Eval` (use `rw [stdAct_lMap_emb]`); never compile Foundation/mathlib;
LeanInteract has no REPL tag for v4.33.1 yet. See [[project-arith-numeral-vacuity]],
[[project-boundedgl-interface]], [[project-transpose-red-cell]].
