# HANDOVER — the arithmetized `S` refactor (rewritten 2026-09-13 for a new assistant/account)

*This document is self-contained: read it first, then the records it points to (§2). Everything
that lived only in the assistants' memory is copied into `CLAUDE_MEMORY/` next to this file
(48 notes; the index is `CLAUDE_MEMORY/MEMORY.md` — the arith note
`project_arithmetized_s_roadmap.md` is the long one). Nothing below depends on a chat history.
Two assistant sessions produced this state: the first (2026-09-09/11) built M1–M3 and this
document's first version; the second (2026-09-11/13, Claude Fable 5.1) executed M4 and started
U10. Adapt the commit attribution line in §5 to the new assistant.*

## 0. Who and what

Colomban Duclaux, ETH master thesis: a Lean 4 mechanization of Open-Source Game Theory
(Critch 2022, bounded-proof-search agents in the Prisoner's Dilemma). The repository has an
ENGINE (`engine/`, namespace `PD`: agent language `Prog`/`Formula`, the rule-based proof
system `Pf` ("`S`", 33 constructors, transcript-cumulative costs), the fuelled evaluator
`eval`, the bot zoo, ~180 outcome theorems), an APP (`app/`, an LLM pipeline that writes
bots and proofs), a tau layer, an EGT layer, and — the subject of this handover — a
STANDALONE package `arith/` (`ArithS`) that builds an ARITHMETIZED instance of `S` on the
Foundation library (FormalizedFormalLogic): Peano Arithmetic with a length-bounded provability
predicate `□_k`. **The user's goal, restated 2026-09-11:** *a working `S'` = PA + the
length-bounded `□_k` in which the parametric bounded Löb theorem (PBLT, Critch 2019 Thm 3 /
2022 Lemma 3.6) is a theorem, Cupod-vs-Dupoc holds, and the zoo programs run; the merge onto
the rule-based `Pf` comes later.*

Decisions the user fixed (do not re-litigate): measure = proof LENGTH, not Gödel-number
magnitude; standalone package pinned to a Foundation commit; work on branches, never on
`main`; tau bots stay OUTSIDE the arithmetized layer; the paper is handled separately by the
user; **the T2 bridge (engine `Pf` ↔ PA-`S`) is DEFERRED — do not extend `Core/`, `Agent`,
`AgentConverse`, `Inst`, `Det`**; **the one remaining obligation of M4 (`BoundedInnerNec`, §4)
is to be pushed for, on its own branch.**

## 1. Where everything is (two folders, one repository, three branches)

| Folder | Branch | Content | Engine toolchain |
|---|---|---|---|
| `~/wt/osgt-arith-m3` (a git WORKTREE, outside OneDrive) | **`colomban-arith-u10` — CANONICAL, checked out** | everything below + the U10 work in `arith/ArithS/Necessitation/` | Lean v4.33.1, mathlib `0df444a360ea` |
| same worktree | `colomban-arith-m3` — FROZEN at `15b015a` (the M4 milestone) | engine bumped + M1–M4 results + notes through the milestone | same |
| the OneDrive checkout (`.../workspace/open-source-game-theory`) | `colomban-arith-s` | arith as of the M3 merge; notes copied by hand up to 2026-09-11 (NOT synced since) | Lean v4.28.0 (old) |

`-u10` contains everything in `-m3`, which contains everything in `-s`; develop ONLY on `-u10`
(create a new branch off it if you prefer). The OneDrive folder exists so the app/IDE keep
working on the old engine toolchain; Lean builds inside OneDrive stall on I/O (see
`CLAUDE_MEMORY/project_onedrive_lake_replay_timeout.md`). `-m3` and `-s` are pushed to `origin`
(GitHub `ColombanD/open-source-game-theory`); **`-u10` has NEVER been pushed** — push it first
thing on the new account if the machine changes (`git push -u origin colomban-arith-u10`).
To collapse to one folder later: merge into `main`, `git checkout main` in OneDrive,
`cd engine && lake exe cache get && lake build`, `git worktree remove ~/wt/osgt-arith-m3`.

Lake layout in the worktree: `arith/.lake -> ~/wt/arith-lake-m3` (its `packages` is a symlink
to `~/wt/arith-lake/packages`, the prebuilt Foundation + mathlib; its own `build/`). NEVER
compile Foundation or mathlib from source: `lake exe cache get` for mathlib; Foundation oleans
are already in `~/wt/arith-lake/packages`.

Build (worktree): `cd ~/wt/osgt-arith-m3/arith && LEAN_NUM_THREADS=4 timeout 3000 lake build ArithS`
(~3230 jobs, ~30 s incremental; builds the engine as a path dependency). This Lake has no
`-j`; parallelism is `LEAN_NUM_THREADS`. ONE lake build at a time on the machine — check with
`pgrep -f 'elan/toolchains.*bin/lake build'` (plain `pgrep -f 'lake build'` matches your own
polling shell; the IDE's `lake serve`/`lean --worker` do not count). Single-file check:
`timeout 600 lake env lean ArithS/<File>.lean 2>&1 | grep -E "error|sorry" -A 12` — and CHECK THE
EXIT CODE of `lake env lean` itself (a `timeout` kill upstream of `grep` looks like success).
Probes/scratch files go in the session scratchpad, never in the package.

The axiom census: building `ArithS` prints `#print axioms` for the headline theorems listed in
`arith/ArithS/Audit.lean` (292 lines as of 45c8844); every line must be
`[propext, Classical.choice, Quot.sound]` (one pre-existing line, `substs_leF_imp`, prints the
SUBSET `[propext, Quot.sound]` — fine). `Audit.lean` has its OWN import list (it does not import
the root): a new module must be imported in BOTH `ArithS.lean` and `Audit.lean`.

## 2. Read next, in this order

1. `ARITHMETIZED_S_RESULTS.md` — what is proved (M1–M4), exact statements, the paper sentences,
   boundaries, the M4 addendum and the status of the hypothesis.
2. `ARITHMETIZED_S_ROADMAP.md` — the plan and the full dated STATUS LOG (§3; the M4/U10 entries
   are the newest, inserted just above the "**M4 — quantitative HBL**" paragraph) and every
   proof-craft trap found, paragraph by paragraph.
3. `M4_BOUNDED_HBL/` — **`BRIEF.md`** (the M4 design: §1 Critch's uniform PBLT, §2 the guard
   mismatch and the `ppair` decision, §3 the U0–U10 ladder with status, §6 the exact assembly,
   §7 the action-axiom correction and the conjunction family, §8 the U10 design summary, **§9 the
   U10 execution status file by file, §10 the step-list architecture**), the three M4 reader
   reports (`READ_*.md`), **`DESIGN_inner_necessitation.md`** (U10: the eigenvariable
   construction, the cost analysis, the task list) and **`DESIGN_describe.md`** (U10: the formula
   walk, step by step, with the index arithmetic).
4. `M3_TRANSFER/` (the M3 design brief and reader reports), `BEW_PRIMER.md` (a study note on
   provability predicates), `PROVABILITY_NOTATION.md`.
5. `CLAUDE_MEMORY/` — the assistants' memory notes (project-wide, not only arith).
6. The code: `arith/ArithS.lean` lists the modules in dependency order; each file has a
   module docstring saying what it proves and why. For U10, `Necessitation/Steps.lean`'s docstring
   §1–10 is the FRAGMENT PROTOCOL every further construction follows.

## 3. What is achieved (all machine-checked, three standard axioms)

**M1 — the predicate.** Structural `len` on Foundation's codes (Δ₁), meta twins, `dlen ⌜d⌝ = mlen d`;
`LenProvable`/`LenProvableV` (`□_k`), Δ₁ via PROPERNESS (`fbound k = exp³(12k)+1`); the
length-restricted Gödel sentence true, provable, with a length lower bound. Files `Length,
SequentLength, DerivationLength, Bew, MetaLength, Proper`.

**M2 — agents and the red cell (T1).** `LAct = ℒₒᵣ + {c_C, c_D}`; `TAct = PA ∪ {c_C ≠ c_D,
c_D ≠ c_C}` **∪ {axAct, axAct'}** (since 2026-09-12: the constants are `0` and `1` in one of the
two orders — without it no guard sentence was `TAct`-provable, a vacuity found by the M4 work);
τ = constant swap, `lenProvable_fbound_swap_iff`. **Program codes on the polynomial pairing
`ppair x y = (x+y)²+y`** (since 2026-09-11; Foundation's `pair` has an `if` and is not a term),
`pConst/…/pSearch k g p q`, `relabel`/`swapcode`, `psubst`; **programs are described by TERMS
`progT`/`progTT` built from `ppair` and binary numerals** (so a searcher's guard is the
`bnum k`-instance of a fixed formula: `guardCode_DupocV_eq_instB`, `exists_dupoc_instance`);
`guardCode`, the Σ₁ fixpoint evaluator `EvalGraph`. `red_cell : (Dupoc k, Cupod k) = (D, C)` at
every `k`, non-vacuous (`guard_fits`). Files `LangAct, TheoryAct, Transpose, Sound, Symmetry,
ProofLength, Cut, Prog, RelabelTemplate, Bnum, ProgT, BewV, Guard, Subst, Eval, EvalN, SimTest,
Template, RedCell, Fit, Instance, InstanceV`.

**M3 — `S` relative to PA (T2), as three theorems (DEFERRED, do not extend).** T2-CORE
`Core.Pf_core_sound`, T2-NEG `no_budget_keeping_transfer`, T2-AGENT `eval_iff_evalGraph` +
`Inst`/`Det` (see the results record). `FitBox`: box-carrying guards never fit under Cantor codes
(the "node data" fix is NOT a PBLT prerequisite; deferred with the bridge).

**M4 — PBLT and the Dupoc cell in PA-`S`, conditional on ONE hypothesis (2026-09-11/12).**
Following Critch 2019's UNIFORM proof (one PA proof with `k` free; the bounded steps are
V-generic lemmas on codes + the completeness theorem): `CutV` (bounded D2 on codes, `LenDerivable
T k φ := ∃ d, Proof T d φ ∧ dlen T d ≤ k`), `ProperV` (properness in every model:
`lenDerivable_iff_lenProvableV`), `InstV` (`instB n k := subst (bnum k ∷ 0) n`, the parametric
box `bewB`, Quantifier Distribution `lenDerivable_instB_V`), `Diag` (parametric diagonal lemma
over `TAct`; `tact_complete'` = completeness on the two standard readings), `NumeralFacts`
(short proofs of `c ≤ bnumT k`), `Transparency` (Dupoc's truth equation and search clause in
every model), `Assembly/Prep` (Cupod's instance, the conjunction family `pConj = qDupoc ⋏
qCupod`, ∧-elimination on codes, `Box_g`, `psi` with `psi_fixed_point`, the hypothesis
structure), `Assembly/Uniform` (`chain_V`, `psi_true_V`, **`pblt_uniform`**), `Assembly/Cell`
(**`dupoc_self_coop`**, `dupoc_finds_guard`). The hypothesis:
`BoundedInnerNec d := ∀ χ, ∃ C, ∀ V k, □_{‖k‖³} χ(k) → ∃ e ≤ C·(‖k‖^{3d}+1), □_e (□_{‖k‖³} χ(k))`
inside every model — Critch's Property 4 / assumption (d), polynomial expansion. (Its first
formulation with a uniform `c₁·flen χ` term was UNSATISFIABLE — the target names `χ` by a unary
numeral — and was restated; brief §8.)

**U10 (started 2026-09-12, branch `-u10`) — discharging `BoundedInnerNec 3`.** The verification
proof: a `TAct`-proof code that follows the tree of a derivation `ρ`, introduces every code it
talks about as an EIGENVARIABLE via ∃-elimination from a finite library of universal lemma-
sentences, never writes a code as a numeral, expected cost `E(a) = O(a³)`. LANDED (all green,
census 292): `Necessitation/Primitives` (`useLemmaCode`, `elimExistsCode`), `Lib/Basic`
(`Lib σ := ∃ N, ∀ V, LenDerivable TAct N ⌜lMap emb σ⌝`, `Lib.univ_code`), `Lib/Sets` (26 rows),
`Lib/Formulas` (84), `Lib/Lengths` (35), `Lib/Nodes` (the ten `Intro_tag`, ten `Dlen_tag`, ten
node-code totalities, the axiom recognizer incl. induction instances), `Lib/Bridge` (ℒₒᵣ/LAct,
49 rows), `Steps` (`useHornCode`, `useHornAndCode`, `introFactCode`, the fragment protocol,
`instOuterAt_subst`), `ShiftLen` (free-variable occurrence counts; `setLen (setShift s) ≤ setLen s
+ fvOccS s` — the additive bound; the doubling bound composes exponentially), `Lib/Walk` +
`WalkLemmas` (`lt` rows, closed symbol rows as chain numerals `cT`, `bvOcc`, `fvOccF_subst_le`,
`instOuterAt_subst_bvList`, `freeIter_subst_listToVec`).

**Infrastructure.** Engine on v4.33.1 (`Metatheory` target broken before, documented tau debt);
one workspace; results record; roadmap status log; the M4 brief and two U10 design notes.

## 4. What is left (with estimates)

**U10, in order (brief §9–§10; DESIGN_inner_necessitation §5; DESIGN_describe):**
1. **`Necessitation/Chain.lean` — the step language and the PR chain builder** (§8 below for
   its exact state): step codes `sIntroFact i j ē`, `sUseHorn`, `sUseHornAnd`, `sElimExs`,
   `sSplit`, `sWkDrop`, `sAxLFact`; `applyStep`, `ctxAfter`, `ctxVec` (PR), `chainCode` (PR from
   the end with fixed parameters), `StepOK` (Δ₁), `stepCost`; `chainCode_proof`,
   `dlen_chainCode_le` by IΣ₁ induction on the index. ~1 week.
2. **`RowInst.lean`** — for every row the walk uses: the row-shape lemma (`⌜lMap emb rowB⌝` read
   off the DSL) and the instantiation lemma at witnesses (canonical fact codes
   `subst (listToVec ws) ⌜lMap emb P⌝`), plus the context-fact definitions (`shapeF`, `piF`, …)
   with `IsFormula`/length/`fvOcc` bounds. ~1 week (never started; an agent was killed at launch).
3. **`describeSteps`** — the formula walk as a `Fixpoint` on `⟪n, r⟫` (DESIGN_describe §4–§7),
   `descCount`, `StepsOK` by `IsSemiformula.pi1_structural_induction`, the final-context facts,
   the cost. Then `negSteps/shiftSteps/substSteps/freeSteps` (§9). ~3 weeks.
4. **The ten per-tag fragments** as step-list emitters (DESIGN_inner_necessitation §3.3) and the
   `dlen` bookkeeping with binary numerals (§4.1–4.2; needs `formulaLenShift`+`fvOcc` rows for
   shifted atoms — flagged). ~4–6 weeks.
5. **`verifySteps ρ`** — a `DlenGraph`-style fixpoint on `⟪ρ, list⟫`, with `StepsOK` and the cost
   sum by `Derivation.induction1`; **the top** (§4.3): closing the target sentence, `gBudget`,
   the numeral `⌜χ⌝`; then `theorem boundedInnerNec_three : BoundedInnerNec 3` and the
   UNCONDITIONAL `dupoc_self_coop`. ~3 weeks.
6. Small: the `Steps.lean` `dlen_introFactCode_le_occ` swap (ShiftLen's report says how);
   `Lib/Nodes` item (iii) is in `Bridge` (`axIsFormula`).
   Total remaining: 2–3 months. Cheap independent improvement: charge variable indices in
   BINARY in `Length.lean` (one factor of `a` off `E`; touches the M1 constants).

**After U10:** the mutual-Löb cells (PrudentBot/JustBot vs Dupoc — same machinery on the
conjunction), the tau constructors, LegibleBot/OptimBot (box guards: the node-data coding fix),
the merge onto `Pf` (T2-NEG: cannot be budget-preserving), the paper (the results record's
sentences), pushing `-u10`, syncing notes to `-s`, re-pinning LeanInteract.

## 5. Conventions the user expects

* Commit early and often, each commit green; message style `feat(arith): …`, `docs(arith): …`,
  `wip(arith): …` (green partial), ending with `Co-Authored-By: Claude Fable 5.1 <noreply@anthropic.com>`
  (adapt to the new assistant's attribution line). Never push without being asked; never
  commit on `main`.
* No `sorry`, no `axiom`, ever; if a statement resists, WEAKEN it and say so. Every threshold
  and constant EXISTENTIAL — never a numeric constant (Cantor coding makes them astronomical).
* Record every landed step and every trap in the roadmap's status log / brief §9 the same day.
* Honesty over reach: "for all large k"; call a hypothesis a hypothesis; a conditional theorem
  is only as good as its hypothesis being TRUE — check satisfiability (the `BoundedInnerNec`
  lesson: bounds on sentences that name a formula by numeral must be per-family).
* Notation (`PROVABILITY_NOTATION.md`): `⊢_k φ` = `Pf k φ`, `⊨ φ` = `φ.interp`, `⊢` never
  means Lean. Python in `app/`: `uv` only.
* **Agent operations (learned 2026-09-12):** two concurrent Lean agents maximum (three
  exhausted the account); each agent gets ONE file set, is told never to touch others', to
  check single files with `lake env lean`, to commit only its files by name (never `git add -A`),
  to re-read `ArithS.lean`/`Audit.lean` before editing them, to keep every tool call under
  `timeout 600` and print progress (a silent 10 minutes trips the watchdog), to poll its own
  background builds (no notification reaches it). The account's session rate limit kills
  agents mid-task (resets at a shown time); their wip commits and untracked files stay on disk —
  RESUME the same agent with the exact on-disk state, or relaunch. Read-only "reader"/"design"
  agents producing verbatim reports precede every design decision (the M3/M4/U10 pattern).

## 6. Proof-craft traps (the roadmap and brief §9 have the full list)

* At `V = ℕ`, `<` is `Nat.lt` but `≤` is PeanoMinus's `le_def`; `omega` is useless on `V`; two
  `Nat.cast` instances at ℕ. `add_le_add_left/right` have swapped sides in this toolchain.
* NEVER `simp` a goal containing a closed quote of a big sentence (`⌜qDupoc⌝`, `⌜tactDiag θ⌝`):
  the kernel builds a numeral over `LEAN_NAT_MAX_SIZE`; prove for a VARIABLE sentence and
  instantiate. Never put a closed numeral inside a Δ₁ fixpoint blueprint (26 GB elaboration).
  In `TermRec`/`UformulaRec1` blueprints, ∃-wrap graph clauses (`∃ s, !listSumDef s v' ∧ y = s`).
* Closed constants built from a giant DSL template (`flen (GtmplA 0)`, `⌜GtmplA 0⌝ ≤ ⌜GtmplA 1⌝`)
  must never be evaluated: package them existentially, case-split with `le_total`.
* Foundation numerals are unary; every budget entering a sentence goes through `bnum`; the code
  of a binary numeral term is exponential under Cantor pairing (`size_bnum_ge`).
* `lake env lean` output is block-buffered when redirected; bisect slow files by truncation.
* `Formula` is ambiguous with Foundation's: write `PD.Formula`. `simp` never rewrites the
  instance-implicit structure argument of `Semiformula.Eval` — `rw [stdAct_lMap_emb]`.
* `k̂`/`lit` are not identifiers; uniform existential constants must be built as pure terms;
  `set` does not fold into later facts; pin `(k := 0)` on `qqTwo_semiterm.isUTerm`.
* U10 specifics: witness lists are the row's DSL variable list read RIGHT-TO-LEFT; Foundation's
  `exsIntro` keeps the principal formula (the `(m+1)²` in `useLemmaCode`'s bound is real);
  `IsUTermVec` hypotheses arrive unfolded after `pi1_succ_induction` (apply lemmas explicitly);
  `derivation TAct` is used only as `!(derivation TAct).sigma`, never unfolded; the `.pi`/`.sigma`
  polarity convention (hypotheses `.pi`, conclusions `.sigma`, bridge rows both ways).

## 7. How the assistants worked

Orchestration with background subagents (§5 agent operations); design decisions after a written
brief plus verbatim reader reports; a judge panel was tried once and not needed. Check
`git status` in the worktree before assuming work was lost.

## 8. Last session state (2026-09-13, 00:50 — both running agents killed by the rate limit)

Tree on `colomban-arith-u10` at the commit that includes this handover. ONE partial file:
`arith/ArithS/Necessitation/Chain.lean` (832 lines, committed as `wip` with this handover; NOT
imported from `ArithS.lean`). It contains Part A of the chain task — V-INTERNAL vector twins of
the `Steps` machinery (`vecOf`, `revV`, `tailIter`, `qVecIterV`, `qqExss`, `impChainV`,
`mapSubst`, `mapNeg`, `sufChains`, `ctxChain`, `ctxL`, `nthFromEnd`, `levelF`,
`instOuterAt_eq_subst`, `exsChainV`, …) but NOT yet the step language (`applyStep`/`ctxAfter`/
`StepOK`/`stepCost`), `ctxVec`, `chainCode`, or their theorems. Its type-check status is UNVERIFIED: a `lake env lean` run had not finished within 15 minutes
when this was committed (the file is heavy) — run the single-file check first, with
`timeout 1800`, before building on it.
`RowInst.lean` was never created. Next actions: finish `Chain.lean` (§4 item 1, with the two
extra tags `sElimExs`/`sSplit` from `DESIGN_describe.md` §6), then `RowInst`, then the walk.
