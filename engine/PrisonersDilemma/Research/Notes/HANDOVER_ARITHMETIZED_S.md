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
(GitHub `ColombanD/open-source-game-theory`); **`-u10` IS pushed and in sync** (verified
2026-09-14: `origin/colomban-arith-u10` at the same commit, 0 ahead / 0 behind) — keep pushing it
after each session (`git push`), it is the only off-machine copy of the U10 work.
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

**U10 progress as of 2026-09-14** (the detail is §8 and `BRIEF.md` §11): on top of the modules
above, `RowInstB`, `Lib/Frag` (196 rows), `Lib/Occ`, `CertRows`, `NumSteps`, `Layout`
(`copySteps`/`chainSteps`/`eqSteps`), `Frag1Rows`+`Frag1` and `Frag2Rows`+`Frag2` (**all ten
per-tag fragments**), `Cert` (the term and formula certification passes with `certNeg`/`certShift`)
and `Verify` (`VerifyGraph` with `StrongFinite`, the ten inversion lemmas, `verifyGraph_exists`).
Build 3247 jobs, census 451 lines, all three standard axioms.

**Infrastructure.** Engine on v4.33.1 (`Metatheory` target broken before, documented tau debt);
one workspace; results record; roadmap status log; the M4 brief and two U10 design notes.

## 4. What is left (with estimates)

**The ladder is §8's "REMAINING, in order"** — that list supersedes the 2026-09-13 plan that stood
here (items 1–3 of it, `Chain`/`RowInst`/`describeSteps`, are DONE; item 4, the ten fragments, is
DONE; item 5 is in progress). In brief: finish `Cert`'s `_ok` theorems and the remaining producers
(deciding the `tvPiFact`/`utvPiFact` question first), apply `Verify` §3.6's clause edit and then
uniqueness/`verifySteps`/`verifySteps_ok`/`dlen_verifySteps_le`, write the prologue producers that
discharge the fragments' layout hypotheses, then the top and `boundedInnerNec_three`, which retires
the hypothesis and makes `dupoc_self_coop` UNCONDITIONAL. Estimate from here: days to a couple of
weeks of agent work, the prologue producers and the top being the bulk; the per-tag layout theorems
(`DESIGN_fragments` §9 risk 1) remain the place where surprises would appear.

**After U10:** the mutual-Löb cells (PrudentBot/JustBot vs Dupoc — same machinery on the
conjunction), the tau constructors, LegibleBot/OptimBot (box guards: the node-data coding fix),
the merge onto `Pf` (T2-NEG: cannot be budget-preserving), the paper (the results record's
sentences), syncing notes to `-s`, re-pinning LeanInteract.

## 5. Conventions the user expects

* Commit early and often, each commit green; message style `feat(arith): …`, `docs(arith): …`,
  `wip(arith): …` (green partial), ending with the CURRENT assistant's attribution line (Fable 5.1 wrote M4 and started U10;
  Opus 5 continued it on 2026-09-14 — adapt to whoever is working). Never push without being asked; never
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

## 8. Last session state (2026-09-14, ~18:30 — Opus 5 session, stopped cleanly by the user)

Branch `colomban-arith-u10`, **pushed and in sync** with `origin`. Tree CLEAN, build GREEN:
**`lake build ArithS` 3247 jobs, census 451 lines, all `[propext, Classical.choice, Quot.sound]`**
(the single `substs_leF_imp` line prints the SUBSET `[propext, Quot.sound]` — pre-existing, fine).
55 commits this session. Full narrative in `M4_BOUNDED_HBL/BRIEF.md` §11 (read its status entries
in order — they are the U10 log, newest last).

**RECOVERED AT TAKEOVER** (the three files the previous session left unverified are all green now):
`Frag1Rows.lean` was green as committed; `Frag1.lean` had 2 errors (the residual goal `2 ≤ 3·M + 11`
— `norm_num` cannot do `V`-arithmetic with a CAST NATURAL; fixed by `le_trans (by norm_num)
le_add_self`); `Cert.lean` HUNG (exit 124 at 30 min, empty log) — bisection by truncation pinned it
to `passGraph_defined`'s blanket `simp` over the five-disjunct `PassT` blueprint; the fix
(`Cert.lean:1679`, now the house pattern) is a targeted `simp only [<theDef>, val_mkSigma,
Semiformula.eval_substs, Matrix.comp_vecCons', cons_val_zero, cons_val_one, head_cons,
constant_eq_singleton]` then `rw [<Construction>.eval_fixpointDef]; rfl` — 30 min → 44 s.

**LANDED THIS SESSION (all green, all wired):** `Frag2.lean` + `Frag2Rows.lean` + `gen_frag2.py`
— **all TEN per-tag fragments now exist** (`Frag1`: axL, verum, and, or, wk, cut; `Frag2`: shift,
all, exs, axm), each `node<Tag>Head` (4 steps, 1 shift) + a shared tail, with `_ok` (`len = 9`,
`shiftsV = 1`, concluding the node's goal fact in `finalCtx`), `sizeOK_` and `costSum_…_le`.
`Cert.lean` (1836 → 3599): the term pass and the FORMULA pass as fixpoints with existence,
uniqueness and functional forms (`passT`, `passV`, `passF`), hence the producers
`certNeg`/`certShift` (one parametric pass, `ν = 1`/`ν = 2`), their shift-freeness and length
bounds, count preservation under shift, and the count bridge `eqCount_eq_descCountF` that
`Layout.lean:53` had left open. `CertRows.lean`: `tsvAdjCert` entered the table at `cIdx = 181`
(APPENDED, so every older index is byte-stable), `cok_` at `M = 9`. `Verify.lean` (NEW, 1166):
`le_appendV_mid`, the Σ₁ definability of the fragments' pieces, `VerifyGraph`'s blueprint +
definability + `StrongFinite`, `case_iff`, the ten inversion lemmas, and **`verifyGraph_exists`
(all ten cases by `Derivation.induction1 𝚺`)**.

**THE ONE HONEST WEAKENING — read `Verify.lean` §3.6 before touching `Verify` or `Cert`.**
`verifyGraph_unique`, the function `verifySteps`, `verifySteps_ok` and `dlen_verifySteps_le` are
NOT stated, and uniqueness is **FALSE as the file currently defines `VerifyGraph`** — not merely
unproved: each clause leaves the prologue `pro` and the index arguments EXISTENTIALLY free
(`∃ pro ≤ L, …`) because the prologue producers do not exist yet, so many lists `L` satisfy
`VerifyGraph W tblN ρ L`. THE FIX, which changes nothing above it: replace each clause's
`∃ pro ≤ L, …`/`∃ is ≤ L, …` by the Σ₁ calls that COMPUTE them (`∃ pro, !proDef pro … ∧ …`), as
`DESIGN_fragments.md` §6.1's last paragraph prescribes; the blueprint, construction,
`StrongFinite`, `case_iff`, the ten inversion lemmas and `verifyGraph_exists` are all stated
against the clause SHAPE and survive unchanged, after which uniqueness goes through by
`Fixpoint.induction` and `verifySteps` by `Classical.choose!` (the `descFw` template).

**REMAINING, in order.** (1) `Cert`: the `ListOK` conjunct and the root-pair fact of
`certShift_ok`/`certNeg_ok` (the dossier-consumption argument reading the `dossF_*` decomposition
lemmas), then `certSubst`/`certFree` (now unblocked — `tsvAdjCert` is in the table; mix caps with
`StepOK.mono`/`ListOK.mono` at `M = 9`), `lenSteps` (state it with **`NoDrop'`**, `Frag1.lean:21`,
which admits tags 6/7 — the "`NoDrop` blocks `lenSteps`" report was a false alarm), and the
DOSSIER bridge `DossF … → DossierAt …` (needs `Layout`'s per-node `dossFacts_*` equations first).
**A REAL DESIGN FINDING from the last agent, not yet acted on:** the vector walk (`descVecAux`)
emits `tvPiFact` (row 16), NOT `utvPiFact` (row 39, which appears only at `func`/`rel`/`nrel`
nodes), so the tail's `utvPiFact` is genuinely absent from a vector dossier — it must be derived
from `tvPiFact` by a new bridge row, or the pass restructured to carry it. Decide this before
finishing `certSubst`. (2) `Verify`: the §3.6 clause edit above, then uniqueness, `verifySteps`,
`verifySteps_ok` (state `Layout` as list-membership of a Σ₁ `layoutFacts`, per `DESIGN_fragments`
§9 risk 1), `dlen_verifySteps_le`. (3) The prologue producers (`memberList`, the per-tag prologues
of §4.5/4.6/4.8/4.10) which discharge the fragments' layout hypotheses — including `nodeAxm`'s
recognizer fact `axchFact`, the one deliberate weakening in `Frag2`. (4) The top (§7) and
`theorem boundedInnerNec_three : BoundedInnerNec 3`; then the UNCONDITIONAL `dupoc_self_coop`.

**PROCESS NOTES EARNED THIS SESSION.** Verify a reported blocker against the tree before believing
it — both blockers reported this session dissolved on inspection (one was already solved by
`NoDrop'`, one needed a one-line cap lift with a worked precedent). Sentinel-test a suspiciously
fast `EXIT 0` on a large generated file (break a lemma deliberately, confirm Lean fails where
expected). Only `exit 124` with an EMPTY log is a stall; a truncation prefix ending mid-declaration
reports `unexpected end of input`, which is an artifact. Never end an agent turn while its own
check is running (a network drop cost a turn that way; the work survived only by luck). Poll with a
pattern that does NOT match the polling shell (`pgrep -f 'bin/lake build ArithS'`). Agents were
killed twice by API/network errors and repeatedly by the session rate limit — every green section
must be its own wip commit, and resume from `git status`.
