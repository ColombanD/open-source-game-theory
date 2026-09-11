# HANDOVER — the arithmetized `S` refactor (written 2026-09-11 for a new assistant/account)

*This document is self-contained: read it first, then the two records it points to. Everything
that lived only in the previous assistant's memory is copied into `CLAUDE_MEMORY/` next to this
file (48 notes; the index is `CLAUDE_MEMORY/MEMORY.md`). Nothing below depends on a chat
history.*

## 0. Who and what

Colomban Duclaux, ETH master thesis: a Lean 4 mechanization of Open-Source Game Theory
(Critch 2022, bounded-proof-search agents in the Prisoner's Dilemma). The repository has an
ENGINE (`engine/`, namespace `PD`: agent language `Prog`/`Formula`, the rule-based proof
system `Pf` ("`S`", 33 constructors, transcript-cumulative costs), the fuelled evaluator
`eval`, the bot zoo, ~180 outcome theorems), an APP (`app/`, an LLM pipeline that writes
bots and proofs), a tau layer, an EGT layer, and — the subject of this handover — a
STANDALONE package `arith/` (`ArithS`) that builds an ARITHMETIZED instance of `S` on the
Foundation library (FormalizedFormalLogic): Peano Arithmetic with a length-bounded provability
predicate `□_k`. The user's stated goal: *"we formalized OSGT, with an `S` that is Lean-checked
and connected to an approved mathematical formalization; we prove Cupod-vs-Dupoc in this
formalization, which cannot be false because `S` is literally like Critch."*

Decisions the user fixed (do not re-litigate): measure = proof LENGTH, not Gödel-number
magnitude; standalone package pinned to a Foundation commit; work on branches, never on
`main`; the restricted guard template first, generalize later; tau bots stay OUTSIDE the
arithmetized layer for now; the paper is handled separately by the user.

## 1. Where everything is (two folders, one repository)

| Folder | Branch | Content | Engine toolchain |
|---|---|---|---|
| `~/wt/osgt-arith-m3` (a git WORKTREE, outside OneDrive) | `colomban-arith-m3` — CANONICAL | engine bumped + all arith results + notes | Lean v4.33.1, mathlib `0df444a360ea` |
| the OneDrive checkout (`.../workspace/open-source-game-theory`) | `colomban-arith-s` | arith package as of the merge; notes copied by hand | Lean v4.28.0 (old) |

`colomban-arith-m3` contains everything in `colomban-arith-s`; develop ONLY on `-m3`. The
OneDrive folder exists so the app/IDE keep working on the old engine toolchain; Lean builds
inside OneDrive stall on I/O (see `CLAUDE_MEMORY/project_onedrive_lake_replay_timeout.md`), which
is why the worktree exists. Both branches are pushed to `origin` (GitHub `ColombanD/open-source-game-theory`).
To collapse to one folder later: merge `-m3` into `main`, `git checkout main` in OneDrive,
`cd engine && lake exe cache get && lake build`, `git worktree remove ~/wt/osgt-arith-m3`.

Lake layout in the worktree: `arith/.lake -> ~/wt/arith-lake-m3` (its `packages` is a symlink
to `~/wt/arith-lake/packages`, the prebuilt Foundation + mathlib; its own `build/`). The
OneDrive `arith/.lake -> ~/wt/arith-lake`. NEVER compile Foundation or mathlib from source:
`lake exe cache get` for mathlib; Foundation oleans are already in `~/wt/arith-lake/packages`.

Build (worktree): `cd ~/wt/osgt-arith-m3/arith && LEAN_NUM_THREADS=4 lake build ArithS`
(~3200 jobs, ~20 s incremental; builds the engine as a path dependency). This Lake has no
`-j`; parallelism is `LEAN_NUM_THREADS`. One lake build at a time on the machine (check
`pgrep -f 'lake build'`; the IDE's `lake serve` does not count). Single-file check:
`timeout 600 lake env lean ArithS/<File>.lean 2>&1 | grep -E "error|sorry" -A 12`.

The axiom census: building `ArithS` prints `#print axioms` for the 48 headline theorems from
`arith/ArithS/Audit.lean`; every line must be `[propext, Classical.choice, Quot.sound]`.

## 2. Read next, in this order

1. `ARITHMETIZED_S_RESULTS.md` — what is proved, exact statements, the paper sentence, boundaries.
2. `ARITHMETIZED_S_ROADMAP.md` — the plan (§0 goal and tiers, §1 Foundation API, §2 objects,
   §3 milestones with the full dated STATUS LOG, §4 what transfers, §5 dangers) and every
   proof-craft trap found, paragraph by paragraph.
3. `M3_TRANSFER/` — the design brief for the transfer theorem, four verbatim reader reports
   (engine `Pf` catalogue, Foundation API, toolchain gap, arith inventory) and the one surviving
   panel proposal; `BEW_PRIMER.md` — a study note on provability predicates.
4. `CLAUDE_MEMORY/` — the previous assistant's memory notes (project-wide, not only arith).
5. The code: `arith/ArithS.lean` lists the modules in dependency order; each file has a
   module docstring saying what it proves and why.

## 3. What is achieved (all machine-checked, three standard axioms)

**M1 — the predicate.** Structural `len` on Foundation's codes (Δ₁), meta twins, `dlen ⌜d⌝ = mlen d`;
`LenProvable`/`LenProvableV` (`□_k`), Δ₁ via PROPERNESS (`fbound k = exp³(12k)+1` bounds the
code of any derivation of length ≤ k); length-restricted Gödel sentence true, provable, with a
length lower bound. Files `Length, SequentLength, DerivationLength, Bew, MetaLength, Proper`.

**M2 — agents and the red cell (T1).** `LAct = ℒₒᵣ + {c_C, c_D}`, `TAct = PA ∪ {c_C ≠ c_D, c_D ≠ c_C}`,
τ = constant swap, `lenProvable_fbound_swap_iff` (τ-closure at every length; replaces the
engine's 47-arm `Pf.transpose`). Program codes `pConst/pSelf/pOpp/pBot/pSim/pIte/pSearch k g p q`
(six-variable templates), `relabel`/`swapcode` (τ acts on templates via `relabelTemplate`),
`psubst` one-shot as in the engine (τ-equivariant), canonical BINARY descriptions
(`bnum (dnum x), dU x, dW x`), `guardCode`, the Σ₁ fixpoint evaluator `EvalGraph` (const/self/
opp/bot/sim/ite/search; deterministic and fuel-monotone in every model of IΣ₁). Restricted
template `GtmplA a` with code/swap/truth equations. `red_cell : (Dupoc k, Cupod k) = (D, C)`
at every `k`, fuel 2, by symmetry + soundness + determinism. Non-vacuity: `guard_fits`.
Files `LangAct, TheoryAct, Transpose, Sound, Symmetry, ProofLength, Prog, RelabelTemplate,
Bnum, BewV, Guard, Subst, Eval, EvalN, SimTest, Template, RedCell, Fit`.

**M3 — `S` relative to PA (T2), as three theorems.** `Core/Tr, Core/Sound`: T2-CORE
`Pf_core_sound` — budget-erased translation, the 16 modal/propositional rules sound over PA
via Foundation's `ProvabilityAbstraction` (D1–D3, kreisel fixpoint), the 17 non-core rules as
a `Leaf` hypothesis. `Code`: `pcode/tmpl/tcode` with substitution code equations and τ on the
box-free search-bot fragment. `Neg`: T2-NEG `no_budget_keeping_transfer` — no inflation `e`
makes `Pf k φ → PA ⊢_{e k} tr φ` true (atoms are charged by evaluation steps; witness
`Pf 1 (plays (const C) (bot^m (const C)) C)`). `Agent, AgentConverse`: T2-AGENT
`eval_iff_evalGraph` — on modest programs (the whole zoo) the arithmetized and the engine
evaluators compute the same plays given ONE two-sided `GuardAgree` on the consulted `□_k`
facts; unconditional for search-free programs. `Inst`: hom `c_C ↦ 0, c_D ↦ 1`; PA proves the
atom sentences of modest plays (Σ₁-completeness); `Det`: determinism in every model,
negative atoms PA-provable (completeness theorem); T2-CORE's `atom/atomNeg/atomBoxImpl/
eqRefl/eqNeg` leaves discharged — only the twelve source-reading leaves remain hypotheses,
each = bounded D1. `FitBox`: Critch's (b) for box guards SPLITS — templates are `O(size k)`
(`exists_flen_tmpl_const`) but the Cantor-pair CODE of a binary numeral is exponential
(`size_bnum_ge`), so a searcher naming its own budget inside a box never fits
(`box_guard_never_fits`). `EngineBridge`, `Audit`.

**Infrastructure.** Engine bumped to v4.33.1 (proof-only repairs, 76 files; `Metatheory`
target was already broken before — documented tau debt); one workspace; results record;
roadmap status log.

## 4. What is left (with estimates from the previous assistant)

1. **Coding fix for boxed guards** (blocks all Löbian work): store box budgets as node DATA
   referenced by a seventh template variable (`lenProvG ⇜ ![#6, #0]` filled by `descVec` from
   the node's `k`) — or balanced numeral terms (`n = a·b + c`, `a, b ≈ √n`, depth O(log log n),
   polylog codes). 3–5 days, low risk.
2. **Bounded HBL (M4)**: D2 (cut with length accounting; days), D1 (Critch's (d): actual PA
   derivations of "d proves σ with len ≤ k" of bounded length — Foundation proves D1
   model-theoretically, no proof object; this is Σ₁-completeness as a proof-producing
   function), D3, bounded diagonal lemma. Decide abbreviations (assumption (c)) first.
   2–4 months, high risk; ask Foundation's Zulip whether proof-object completeness exists.
3. **PBLT and the Löbian cells (M5/T3)**: 3–5 weeks after 2; re-prove, never transfer.
4. **Floors (M6)**: proof-length lower bounds on consistency-like statements; some cells are
   genuinely open in PA; sample, report honestly.
5. Deferred by the user: tau constructors (`tvote/sys/selfIdx`, code 0 in the translation);
   the paper. Housekeeping: merge to `main`, rebuild OneDrive engine on v4.33.1, remove the
   worktree; re-pin LeanInteract when a v4.33.1 REPL tag exists (app fast checker currently
   falls back to `lake env lean`).

Open items that are stated, not gaps: `.box` cannot be translated compositionally under
length-bounded provability (the box carries its body's code; provable equivalence ≠
identity); `GuardAgree`'s direction from PA back to `S` is false in general (PA is stronger)
— the theorems are conditionals and prose must say so; `TAct ⊢` with constants uninterpreted
is not a Σ₁-completeness instance (the instantiated form is what is proved).

## 5. Conventions the user expects

* Commit early and often, each commit green; message style `feat(arith): …`, `docs(arith): …`,
  `chore(arith): …`, ending with `Co-Authored-By: Claude Fable 5.1 <noreply@anthropic.com>`
  (adapt to the new assistant's attribution line). Never push without being asked; never
  commit on `main`.
* Verify before committing with `out=$(… | grep -E "^ArithS.*error")` — an `&&` chain masks
  grep's exit and once committed a broken file.
* No `sorry`, no `axiom`, ever; if a statement resists, WEAKEN it and say so.
* Record every landed step and every trap in the roadmap's status log the same day; sync the
  notes to the OneDrive branch by copying the files and committing there.
* Honesty over reach: state "for all large k", never quote a constant (Cantor coding makes
  constants astronomical); call a hypothesis a hypothesis.
* Notation (`PROVABILITY_NOTATION.md`): `⊢_k φ` = `Pf k φ`, `⊨ φ` = `φ.interp`, `⊢` never
  means Lean.
* Python in `app/`: `uv` only, never pip.

## 6. Proof-craft traps (the ones that cost hours; the roadmap has the full list)

* At `V = ℕ`, `<` is `Nat.lt` but `≤` is PeanoMinus's `x = y ∨ x < y` (`le_def`); `omega` is
  useless on Foundation orders — prove helper lemmas, or bridge with `Nat.le_of_eq/lt`.
* A theorem stated with CLOSED constants built from a template (`10 * cG₀`, `Nat.size cP`)
  makes Lean EVALUATE `flen`/`encode` on the giant DSL term for hours (then a kernel
  "deterministic timeout"); `@[irreducible]` does not stop the kernel. Package such constants
  EXISTENTIALLY and do arithmetic over variables. Related hangs: unification unfolding
  `qqAnd/qqExs` to `pair`; an index mismatch (`9` vs `6+1+1+1`) making `isDefEq` unfold a giant
  quote; `whnf` of closed `Nat` arithmetic on symbol counts.
* `lake env lean` output is block-buffered when redirected: a partial log shows NOTHING.
  Always `timeout`; bisect a slow file by truncation (`sed -n 1,N`); `set_option maxHeartbeats
  N in` goes BEFORE the docstring.
* `Formula` is ambiguous with Foundation's: write `PD.Formula`. `simp` never rewrites the
  instance-implicit structure argument of `Semiformula.Eval` — use `rw [stdAct_lMap_emb]`.
* Foundation numerals are unary (`1+1+…+1`); never put a program code into a sentence as a
  unary numeral (that made every search fail — the retired `Vacuity.lean`); and under Cantor
  pairing even a binary numeral TERM's code is exponential (`size_bnum_ge`).
* `tlen/flen/mlen` are WF-compiled: `simp [tlen]`/`rw`, never `rfl`/`change`.
* Δ₁ blueprints need Σ antecedents in the Π form; `Fin 0 → V` parameters via
  `Subsingleton.elim`; `Defined.of_zero` for Σ₀ cores; `numeral_eq_natCast` for DSL numerals ≥ 5.
* `Semisentence` quotes: `Sentence.quote_def`; code equations via `coe_subst_eq_subst_coe` +
  `typed_quote_substs` + `val_substs`; term values `t.val (s := stdAct) ![] Empty.elim`.
* Lean 4.33 vs 4.28 (engine bump): `simpa … using!` for old transparency; `dsimp +instances`
  for stale `Decidable` instances; `clear_value` for an `omega` recursion-depth regression;
  `simpa [-forall_const]` for typeclass timeouts.

## 7. How the previous assistant worked (so the workflow can be reproduced)

Orchestration with background subagents, each given ONE file set, told never to touch
others', to check single files with `lake env lean`, to commit only when green, and to report
statements verbatim; the orchestrator wired imports/census, built, committed, recorded, synced,
pushed. Design decisions were taken after a written brief (`M3_TRANSFER/BRIEF.md`) plus
verbatim reader reports; a judge panel was started but not needed. Agents run on the
account's rate limit: three concurrent Lean agents once exhausted it mid-task; prefer two.
Agents die at rate limits or watchdogs: their partial files stay on disk — check
`git status` in the worktree before assuming work was lost, and commit partial-but-green
files as `wip`.

## 8. Last session (2026-09-11): bounded D2 in rule form — DONE (finished the same day)

**Status: COMPLETE.** `Cut.lean` type-checks, is imported after `ProofLength`, its six
theorems are in the `Audit.lean` census (three axioms), `lake build ArithS` is green. Landed
statements: `lenProvable_mp` with `(c₁, c₀) = (10, 9)`, `lenProvable_mp_sharp`
(`5|φ| + 10|ψ| + 9`), `lenProvableV_mp` (in `RedCell.lean`), `lenProvable_fbound_mono`,
`lenProvable_verum`, `mlen_cutMP`; reusable bridges `derivation_of_lenProvable` /
`lenProvable_of_derivation`. Recorded in the roadmap's M4 paragraph and the results §3
addendum. The paragraph below is the pre-completion plan, kept for the record.


`arith/ArithS/Cut.lean` (246 lines, no `sorry`, NOT yet type-checked end to end, NOT imported
from `ArithS.lean`, committed as `wip`) is the first M4 field: modus ponens for `LenProvable`
with exact additive length accounting. Intended statement:
`lenProvable_mp : LenProvable fbound k₁ TAct ⌜φ ➝ ψ⌝ → LenProvable fbound k₂ TAct ⌜φ⌝ →
LenProvable fbound (k₁ + k₂ + c₁·(flen φ + flen ψ) + c₀) TAct ⌜ψ⌝`, built at the meta level
(`Proof.sound'` twice, a `Derivation2` cut on `φ ➝ ψ = ∼φ ⋎ ψ` — weaken `d₂` to `{ψ, φ}`,
`closed` leaf `{ψ, ∼ψ}`, `and` to `{ψ, φ ⋏ ∼ψ}`, weaken `d₁`, `cut` — then `derivation_quote`,
properness for the code bound, `dlen_quote` for the length; the pattern is
`lenProvable_fbound_swap` in `Symmetry.lean`), plus `flen_neg`, `fbound_mono`, `lenProvable_verum`.
To finish: `timeout 600 lake env lean ArithS/Cut.lean`, fix, add `import ArithS.Cut` after
`ProofLength` in `ArithS.lean`, add the theorems to `Audit.lean`, build, record in the
roadmap's M4 paragraph and in the results record ("first M4 field"). Note for the paper:
PA-S pays `|φ| + |ψ|` at a cut where the engine's `mp` charges only `|ψ|` — a constant-factor
departure; T2-NEG shows the real obstruction is the atoms, not this.
