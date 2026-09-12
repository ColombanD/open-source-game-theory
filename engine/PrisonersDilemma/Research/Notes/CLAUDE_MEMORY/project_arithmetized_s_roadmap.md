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

**DECISIONS 2026-09-11 (Colomban, new session):** goal restated = a working S' (PA + length-bounded
□_k) in which PBLT (parametric bounded Löb, Critch Lemma 3.6) is a theorem, Cupod-vs-Dupoc holds
(done, T1) and all zoo programs run; the MERGE onto the rule-based `Pf` (the T2 bridge) is
DEFERRED — do not extend T2-CORE/AGENT/Inst/Det further. Ordering agreed: M4 (bounded D1/D3, parametric
diagonal lemma) → PBLT → Löbian cells re-proved in S'. CORRECTION to an earlier claim: the
`tmpl (.box k ψ)` node-data coding fix (FitBox design fix) is NOT a prerequisite for PBLT — Dupoc's
guard is box-free and fits. What PBLT needs is the PARAMETRIC box: `□_x ψ(x)` written as
"LenProvableV x (subst (bnum x) ⌜ψ⌝)" via internal substitution, never as a numeral of ⌜ψ(k̄)⌝
(that numeral has ≥ k symbols by `size_bnum_ge`, so no proof of it fits). The `tmpl` fix serves only
LegibleBot/OptimBot + the bridge — behind M4. Method: written brief + verbatim reader reports in
`Research/Notes/M4_BOUNDED_HBL/`, then agent-sized proof tasks (≤2 concurrent Lean agents).

**CHECKPOINT 2026-09-11 (evening, user away ~2h).** Design brief `Research/Notes/M4_BOUNDED_HBL/BRIEF.md`
(+ 3 reader reports) committed 05ccd3b; roadmap has the M4-start entry. Design: Critch 2019's UNIFORM
PBLT proof (Properties 1 impl-distribution, 2 quantifier-distribution, 4 bounded INNER necessitation
`□_a ψ → □_{E a} □_a ψ` with E subexponential = THE crux; Property 3 reduces to unbounded
Σ₁-completeness, free); all bounded lemmas V-GENERIC on codes + `complete`; guard mismatch fixed by
re-coding programs on `ppair x y = (x+y)²+y` (term-expressible; Foundation's `pair` has an `if`).
LANDED: a1aa1b9 `ppair` re-pairing of Prog.lean, green, 62 census lines, no statement weakened.
IN FLIGHT (background agents, each commits when green or as `wip`): (1) `ArithS/CutV.lean` — bounded
D2 on codes inside every model of IΣ₁ with dlen accounting (may carry a named `ProperV` hypothesis);
(2) `progT`/`progTT` term descriptions replacing `bnum (dnum x)` in descVec/dnumT, `guard_fits`
re-proved, HEADLINE `exists_dupoc_instance : ∃ q : Semisentence LAct 1, ∀ k, guardSentenceA 0
(Dupoc k) (Dupoc k) = q ⇜ ![bnumT k]` (+ code form, V-generic if time). If a session was closed,
check `git status`/`git log` in ~/wt/osgt-arith-m3 for partial files before assuming loss.
NEXT (brief §3 ladder): U1 parametric box `bewB a n k := ∃ g, g = subst (bnum k ∷ 0) n ∧ L a g`;
U3 instantiation-with-dlen in V; U6 parametric diagonal lemma with bnum instances
(Foundation's `parameterizedFixedpoint` uses unary numerals — re-do with bnum); U7 Dupoc
transparency in V (V twins of the ℕ-only evaluation lemmas listed in READ_arith_for_m4 §4(iv));
U8/U9 pblt_uniform + dupoc_self_coop conditional on `BoundedInnerNec E`; U10 discharge it.
**2026-09-11 later — U2 LANDED (f4a1a0b, `ArithS/CutV.lean`):** bounded D2 on derivation CODES in
every model of IΣ₁: `lenDerivable_cut_V` UNCONDITIONAL for `LenDerivable T k φ := ∃ d, Proof T d φ ∧
dlen T d ≤ k` (Σ₁, no fbound); `lenProvableV_cut_V` under named `ProperV V T` (theorem at ℕ:
`properV_nat_TAct`; OPEN for general V — needs V-internal induction on derivation codes);
`pa_proves_cutSentence`/`tact_proves_cutSentence` via `complete`. LESSON: write the Löb argument
with `LenDerivable` (no fbound); `LenProvableV`/`ProperV` enter only where the evaluator's guard is
consulted. Agents stall silently on long commands — tell them "short tool calls, timeout 600, print
progress". IN FLIGHT: `ProgT.lean`+descriptions+`Instance.lean` (exists_dupoc_instance);
`InstV.lean` (instB, bewB, lenDerivable_inst_V = Property 2 with dlen accounting).
**2026-09-12 — M4 ladder progress (all three axioms, census 104):** U0 done (ppair re-pairing a1aa1b9;
ProgT/Instance/InstanceV: `guardCode_DupocV_eq_instB` — Dupoc's guard IS `instB ⌜qDupoc⌝ k` in every
model); U1+U3 InstV (47fa241; `bewB`, Quantifier Distribution `+5|χ[t]|+3|χ|+|t|+7`); U2 CutV (f4a1a0b);
U6 Diag (669704c; parametric diagonal lemma over TAct; `tact_complete` = completeness on REAL-equality
models, `𝗘𝗤 LAct ⪯ TAct`; TRAP: `simp` on a goal containing `⌜tactDiag θ⌝` overflows the kernel
numeral — prove for a variable sentence); U7 Transparency (54aee07). VACUITY FOUND + being fixed
(U0b): TAct with only `c_C ≠ c_D` has models reading constants as e.g. 5,7 where the guard is FALSE ⇒
`TAct ⊬ guard(k)` ⇒ Dupoc never cooperates; fix = axiom `axAct : (c_C=0 ∧ c_D=1) ∨ (c_C=1 ∧ c_D=0)`
(+ swap image). Brief §6 = exact U5/U8/U9 statements; §7 = the correction. Remaining: ProperV V
(agent), axAct (agent), NumeralFacts (`k̂ ≤ bnumT k` short proofs), U8 assembly, U9 cell; U10 = E.
**2026-09-12 later:** axAct LANDED (7908336; `tact_complete'` over stdActS/swapActS); ProperV LANDED
unconditional (5d9fc0a; `lenDerivable_iff_lenProvableV` in every model); Assembly/Prep LANDED (ec5a8b6,
census 138): conjunction family `pConj = qDupoc ⋏ qCupod` (Critch's PBLT-on-the-conjunction move —
avoids evaluator τ-equivariance in V), `psi_fixed_point`, `BoundedInnerNec (d c c₁ c₀)`. IN FLIGHT:
Assembly/Uniform (U8), Assembly/Cell (U9 `dupoc_self_coop`), NumeralFacts. After U9: only U10
(discharge BoundedInnerNec, polynomial E) remains for the Löbian cell; then mutual-Löb cells.
**U10 design 2026-09-12 (`M4_BOUNDED_HBL/DESIGN_inner_necessitation.md`):** eigenvariable construction
(never write a code as a numeral; ~40 universal lemma-sentences by `complete`; recursion by
`Derivation.induction1`), expected E(a)=O(a³) (O(a²) with binary variable indices in Length.lean),
2.5–4 MONTHS — the user's call. LESSON/TRAP: the first `BoundedInnerNec d c c₁ c₀` was UNSATISFIABLE
(target contains the unary numeral ⌜χ⌝ ⇒ dlen ≥ encode χ, exponential in flen χ): any bound on a
sentence naming a formula by numeral must be per-family (`∀ χ, ∃ C`), never uniform in flen.
Restated `BoundedInnerNec d`. Risk to check first: Foundation's `𝗣𝗔.Δ₁` recognizer for the `axm` leaves.
**MILESTONE 2026-09-12 (4c8ecc9, census 162/3 axioms, tree clean):** `pblt_uniform` and
`dupoc_self_coop`/`dupoc_finds_guard` are THEOREMS conditional on the single hypothesis
`BoundedInnerNec d` (Critch (d)); Cupod-defects-vs-Cupod comes with it (conjunction family). Docs:
roadmap status log, results addendum, handover §4 update, brief rows — all committed. NOT synced to
OneDrive `-s` (outside allowed dirs; user does it by copy). NEXT = USER DECISION: U10 (prove
BoundedInnerNec 3; 2.5–4 months) vs mutual-Löb cells vs paper; cheap independent improvement: binary
variable indices in Length.lean (one factor of a off E).
**U10 STARTED 2026-09-12 on branch `colomban-arith-u10`** (same worktree ~/wt/osgt-arith-m3; `-m3` frozen
at 15b015a). Plan = DESIGN_inner_necessitation.md §5 + brief §9: Necessitation/Primitives (useLemma,
elimExists codes), Lib/{Basic,Sets,Formulas,Lengths} (agents launched), then Lib/Nodes (Intro/Dlen/axm
sentences), describeFormula, per-tag fragments, Derivation.induction1 recursion, top → BoundedInnerNec 3.
**Agent ops (2026-09-12):** the account's session rate limit (resets ~4:10am Berlin) kills background
agents mid-task; their wip commits and untracked files stay on disk. RESUME the same agent by
SendMessage (it keeps its transcript) with the exact on-disk state (`git status`, single-file check
output) — no relaunch needed. Two Lean agents concurrently max. `pgrep -f 'bin/lake build'` (plain
`'lake build'` matches the agent's own polling shell). U10 state: Primitives landed (204c012);
Lib/{Basic,Sets,Formulas,Lengths} wip-committed (e898999, 02e43c6), Nodes.lean drafted; both resumed.
**U10 progress 2026-09-12 (branch colomban-arith-u10):** Primitives 204c012, Lib A f6536fc (145 rows),
Lib/Nodes d95ba66 (Intro/Dlen/axm), Lib/Bridge 637df06 (ℒₒᵣ/LAct), Steps wip 3e4de8e (useHorn/introFact).
ARCHITECTURE (brief §10): CPS recursion is impossible internally (changing continuation; Π₂) → a
flat STEP LIST + a PR chain builder folding from the end with fixed params (`chainCode`), contexts
precomputed (`ctxVec`), `StepOK` Δ₁, proofs by IΣ₁ induction on the index; producers are
list-valued Σ₁ functions (`describeSteps`, fragments, `verifySteps`). Chain agent launched.
**HANDOVER 2026-09-13 (user moving to another account):** U10 landed modules on `colomban-arith-u10`:
Primitives, Lib A (145 rows), Lib/Nodes, Lib/Bridge, Steps, ShiftLen, Lib/Walk+WalkLemmas (census 292);
Chain.lean = partial vector twins (wip), RowInst/describeSteps/fragments/verifySteps/top NOT started.
Handover doc rewritten (HANDOVER_ARITHMETIZED_S.md), CLAUDE_MEMORY/ refreshed from this memory dir.
