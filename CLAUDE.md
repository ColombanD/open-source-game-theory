# Project Guidelines

**What this project is.** A mechanization of **open-source game theory (OSGT)** — Critch 2022's
bounded-proof-search agents — in **Lean 4**, its extension to **partial transparency** (τ-bots),
and the **evolutionary** analysis of the resulting populations. Companion code of the paper
*Partial Transparency in OSGT* (`latex/paper_status.tex`). Four parts, in dependency order
(each depends only on the ones above it):

1. **`engine/`** — the HOST: the agent language `Prog`, the fuelled evaluator, the bot zoo, the
   τ-bot DSL, the typed outcome-theorem template with its linter and census. Also the rule-based
   proof system `S` and its outcome matrix — the COMPARISON system, not the paper's.
2. **`arith/`** — **PA-`S'`, THE PAPER'S PROOF SYSTEM**: Peano Arithmetic with a provability
   predicate bounded by proof length, on Foundation; Critch's PBLT proved unconditionally; the
   matrix and the tau rows re-proved cell by cell. Imports the engine's GAME, not its proof system:
   the language, the evaluator, the bots, the τ-roster, the syntactic transposition and 27 search-free
   cells (246 constants, measured 2026-10-29); no theorem of `S` is used — `Pf` is in the transitive
   closure only because `Dynamics.eval`'s search guard is `decide (Pf k φ)`. The engine never imports it.
3. **`app/`** — the Python CORE (`pd_runner`): the matrices read from the two Lean exports, the tau
   layer, the EGT stages. The paper's experiments and `latex/scripts/` run on it.
4. **`pipeline/`** — the LLM PIPELINE (`pd_pipeline`): bots from natural language, outcome proofs
   by an agent judged by the kernel, the faithfulness reviewer, the web UI. OUT OF THE PAPER'S SCOPE;
   split off from `app/` on 2026-10-29; depends on `app/`.

Other top-level: `latex/` (the paper, figure/table generators in `latex/scripts/`, earlier notes
and talks — the user curates it, do not delete there), `llm-distillation/` (a separate experiment,
kept for later), `README.md`. The design notes and results records of the WHOLE project live in
`engine/PrisonersDilemma/Research/Notes/` (both Lean packages, the Python layer, the paper).

**Removed for the submission (2026-10-29, in git history before `3f99464`):** the engine's
decidability metatheory (`Decidability/`, T31–T54, lake target `Metatheory`), the research spikes
(`Research/Spikes/`), the memory copy `Research/Notes/CLAUDE_MEMORY/`, the root `PBLT_proof.tex` /
`critch22.pdf` / `Pipeline Figure.jpeg`. Docstrings that cite a spike by path refer to that history.
The pipeline's Tier A2 reviewer (`outcome_prepass`) ran `Decidability.T31EngineDecider` and is
BROKEN until it is restored.

---

# Part I — PA-`S'`, the arithmetized proof system (`arith/ArithS`)

**Read first:** `arith/ArithS/Tour.lean` (the nine trusted definitions at ℕ by `rfl`, the red cell
step by step, the headline `#check`s, the census), then `arith/ArithS/README.md` (the four tiers,
the nine definitions in reading order, the engine↔ArithS↔paper dictionary), then
`Research/Notes/SPRIME_DESIGN_RATIONALE.md` (what a reader accepts by eye), `ARITHMETIZED_S_RESULTS.md`
(what is proved), `ROUTE_B_SCOPE.md` + `ROUTE_B_CENSUS.md` (the cell programme and its ledger),
`ARITH_TRAPS.md` (read before writing a line of `ArithS`), `arith/PATHS.md` (the 2026-09-28 layer
reorganization and the deep rename — older notes cite old paths; read them through its table).

Build: `cd arith && lake build --try-cache` (~3500 jobs; Foundation pinned; the engine is a PATH
dependency `../engine`). Default targets: `ArithS`, `ArithSOutcomeCheck` (cell + floor census, paper-zoo
coverage), `ArithSTauCheck` (row/floor-bit validator). Tier targets `ArithSCore/Frozen/Loeb/Matrix/Audit`
rooted at `ArithS/{Core,Frozen,PBLT,Matrix,Audit}.lean`; `scripts/check_tiers.py` enforces the import
direction core < frozen < Löb < results < audit and that each root imports exactly its tier — RUN IT
after adding a module (Lake cannot). Three standard axioms end to end: `ArithS/Audit/<Layer>.lean` is
every `#print axioms` the build runs. `lake exe export_sprime_outcomes` writes
`app/generated/sprime_outcome_theorems.json` and `sprime_tau_rows.json`.

| Layer | Files | What it defines |
|---|---|---|
| **Theory** | `Theory/{LangAct,TheoryAct,Transpose,Sound,Symmetry}` | `LAct = ℒₒᵣ + {c_C, c_D}`; `TAct = PA ∪ {c_C ≠ c_D, c_D ≠ c_C, actionAxiom}` (the constants are `0/1` in one of two orders); τ = the constant swap, a language automorphism; the two standard readings `stdReading`/`swappedReading` and `TAct_complete_of_readings` — the whole positive method; soundness in ℕ — the whole negative method. |
| **Length** | `Length/{Length,SequentLength,DerivationLength,MetaLength,Proper,ProofLength}` | `proofLen`: the structural symbol count of a coded derivation (symbol-blind, so τ preserves it exactly; PROPER: `codeBound k = exp³(12k)+1`); `proofLen ⌜d⌝ = proofLenMeta d`. |
| **The box** | `Box/{Bew,BewV,Cut,CutV,ProperBound}` | `□_k σ := ∃ d < codeBound k, Proof TAct d ⌜σ⌝ ∧ proofLen d ≤ k` (`LenBox`, Δ₁, the evaluator's box) and `LenBoxUnbounded` (Σ₁, the Löb argument's box), equal in every model. Bounded D2 with length accounting. Notation `□[k] φ` (`ArithS/Notation.lean`). |
| **Agents** | `Agents/{Prog,CodeTerm,CodeTermAbs,CodeTermSlot,RevalueTemplate,BinNumeral,Template,Guard,SubstTemplate,Subst,Code,Instance,InstanceV,Fit,FitBox,SysClose,SysTemplate}` | Program codes on the polynomial pairing `ppair`; descriptions are TERMS in binary numerals (`codeTerm`); the six-variable `guardTemplate` and the general `template : PD.Formula → Semisentence LAct 6`; `substCode` = the engine's one-shot `Prog.subst`; **route (c)**: a seventh slot `#6` filled with the node's own budget at guard time (`guardCodeB`), GENERIC — a closed program inside a guard is described with its budget abstracted to the slot, through systems too (`guardCodeB_templateCodeAt`, `guardCodeB_sysCloseTemplateAt`); the thirteen-variable `templateAt` with member pronoun slots for `.sys`. |
| **Evaluator** | `Eval/{Fixpoint,Eval,EvalN,SimTest,Transparency,Det,TauCheck}` | `EvalGraph n me opp p a`: a Σ₁ fixpoint mirroring the engine's `eval` clause by clause (incl. `.tvote/.sys/.selfIdx`); `search` consults `LenBox TAct k (guardCodeB g me opp k)`; deterministic, fuel-monotone, in LOCKSTEP with the engine on search-free constructors. |
| **PBLT** | `Loeb/{Diag,InstV,NumeralFacts}`, `Assembly/{Prep,Family,Cell,Uniform}`, `Necessitation/*` | The parametric diagonal lemma over `TAct`; Critch 2019's uniform proof of the parametric bounded Löb theorem, family-parametric (`LoebSound`, `family_found`); its one hypothesis, bounded inner necessitation, is a THEOREM: `boundedInnerNec_sixteen` (U10, degree 16, ~96k generated lines — do not open; `Necessitation/Package.lean` is the statement) and `closedInnerNec_sixteen`. |
| **Outcome** | `Outcome/{Spec,Attr,Floor,Floors,Lint,Check,Export}`, `Outcome/Matrix/<L>.lean` | The engine's vocabulary on codes: `OutcomeSpecA regime L R (some (a, b))`, `bot P`/`const P` = `progCode` of the engine's bots; ONE `@[outcomeA] theorem outcome_<L>_vs_<R>` per ledger cell, `@[floorA] … _floor` per floor. |
| **Cells** | `Cells/*` (uniform methods by method, Löb by bot; `Cells/Common/` shared kits) | `RedCell`/`RedCellEngine` (every `k`, τ-symmetry + soundness, no Löb); `SearchFree` (transfer at the engine's fuel); `SoundnessCells` (guard false ⇒ else branch); `PositiveCells` (`TAct ⊢ ∀¹ q` by completeness); the Löb families (`DupocMirror`, `JustBot`, `DIMCID`, `CIMCIC`, `PrudentMirror`, `JustSlot`, `KhatCells`, `*Engine`, `DupocTrollBot`, `Dimdid`, `DimdidTroll`, `DupocTrollPrudent`); `FlipCells`/`DimcidFlips` (the disagreements with the engine); `FloorDichotomy`/`FloorVerdicts` (the floors); `Transposition` (`outcomeSpecA_transpose`, the general C/D transposition theorem on `fragP`). |
| **Tau** | `Tau/{Spec,Attr,Lint,Check,Columns,Described,Quine,ClosedProbe,…}`, `Tau/Rows/*`, `Tau/Entangled/*` | The 16 paper templates as `RowSpecA` rows + `FloorBitA` floor bits; `.sys` only for ENTANGLED pairs (both self-probe); `#check_tau_rowsA strict`. |
| **Frozen / estimates** | `Bridge/{Agent,AgentConverse,Inst,Neg}`, `Eval/Det`, `Agents/Fit*`, `Length/Proper`, `Box/ProperBound` | `Bridge/` is what remains of the T2 rule bridge `S → S'` (shown IMPOSSIBLE at polynomial budgets, `MERGE_CROSSROAD.md`; the bridge proper was deleted 2026-10-29, `ARITH_DEAD_CODE_AUDIT.md` §9): the evaluation-certificate kit the cells use (`properPlayer_*`, `inst` and its simp set, `outcome_eq_some_iff`, the size arithmetic of `FitBox`/`NeverFits`). Plus the numeric estimates. |

**The ledger (export of 2026-10-19): 132 cells, 30 genuine floors, 0 companions.** Of the engine's 155
census rows: 107 have an `S'` statement (94 agree, 13 FLIP — 11 DIMCID's, 2 WaryBot's), 26 are genuine
floors, 22 are excluded (LegibleBot: a box inside a guard; OptimBot; WaryBot's floor cells). Plus the
`S'`-ONLY cells of `DupocTrollBot k` ("defect iff the opponent IS `DupocBot k`", separates the engine-side
twins CIMCIC/DupocBot) and `DIMDID k` (the C/D transposition of CIMCIC, `(CIMCIC k).transpose = DIMDID k`
by `rfl`; the SELF-DEFEATING guard argument), and the PrudentBot × DupocTrollBot pair. `S'`-only bots have
an engine DEFINITION but no engine theorem; `outcome_matrix.roster_bots` adds them to the roster. Tau:
16 rows, 197 row slots + 59 floor bits = 256/256 strict; 13 tau flips, all DIMCID's; one `S'` tau flip
`dimdid × obot = D`; 6 RECORDED provenance divergences (the red-cell cross bits `dupoc/natives × cupod`
are FLOOR bits in `S'` though the base cell is a theorem — no τ-symmetry inside one `.sys`).

**The disagreements are theorems, not gaps.** The engine closes them by censuses resting on a player
being UNREADABLE by `S`'s rules; PA reads every source. `dimcid_vs_closed`: in `S'` DIMCID defects
against every closed program (its guard "my cooperating implies X" is self-fulfilling), contradicting
the engine's universal `outcome_DIMCID_vs_DupocBot = (C, D)` — and Critch's own Example 5.3(a); DIMCID
is DefectBot's payoff-exact twin under `S'`. Sentence for the paper: *the engine's `S` is PA plus free
citation and MINUS the reading of sources its rules do not cover; the second departure changes outcomes.*

**Floors.** Every remaining floor is GENUINE: the floor guard is a true Σ₁ sentence whose only
evaluation witness runs through the ELSE branch of a search on a guard FALSE in ℕ, so its provability
within budget is inter-derivable with bounded consistency `Con_TAct(k ± c)` — ONE proof-complexity
question (Pudlák: lower bound `k^ε`, linear regime open). Each floor is a hypothesis-free DICHOTOMY
`dich_<L>_vs_<R>` (`Cells/FloorDichotomy.lean`; `S'`-only bots keep theirs beside their cells): `¬A_k →`
the engine's value, `A_k →` the other, hinge `A_k = LenBox TAct k (the outer guard)` inline. NEVER admit
the hinge as an axiom: the two answers give DIFFERENT cell values; the engine's `+k` stipulates the
negative side.

**Working conventions (binding):** all results "for all large `k`" with EXISTENTIAL thresholds (Cantor
coding makes every constant astronomical — never quote one); `simp` must never see a closed Gödel quote
(state for a variable sentence, bridge by `rfl`); `omega` is useless on `V` (`le_self_add`/`gcongr` under
`open PeanoMinus`); at `V = ℕ` `<` is Nat's but `≤` is `le_def`; `const` inside `namespace ArithS` is
`Outcome/Spec`'s — write `LAct.const`; never compile Foundation or mathlib (`lake build --try-cache`;
`arith/.lake` is a symlink outside OneDrive); ONE lake build on the machine at a time; single-file checks
with `timeout 900 lake env lean` and CHECK THE EXIT CODE (`${pipestatus[1]}` in zsh); a full rebuild after
touching the trusted base is ~35 min; every new module is imported in `ArithS.lean`, its tier root, and
the relevant `Audit/<Layer>.lean`; the nine generated row tables (`Necessitation/*Rows.lean`, `RowInst*`,
`Lib/Frag`) are NEVER edited by hand — edit the generator, `scripts/regen_all.sh`
(`scripts/README.md`); they are PRUNED at generation time by `scripts/prune.py` over
`scripts/pruned/<module>.txt` (`ARITH_DEAD_CODE_AUDIT.md`; `rfl` lemmas and simp-set names are invisible
to the closure — never delete on the audit alone, the build is the judge). The hand codes
`DupocV`/`CupodV` (`Agents/InstanceV`) are the vehicles of the engine-code cells and LIVE; the retired
twin cells (`Just7`/`CupodTroll7`/`JustV`, `Cells/{JustBot,DupocMirror,SimSlot,TauMember,Names}`) were
deleted on 2026-10-29 by the claims-mode reachability audit (`scripts/DeadCode.lean`,
`ARITH_DEAD_CODE_AUDIT.md` §8); the matrix is stated on the engine's own `progCode`s only.

**Notation** (`Research/Notes/PROVABILITY_NOTATION.md`): `⊢_k φ` = derivable at budget `k`
(the engine's `Pf k φ`, the paper's `□_k`), `⊨ φ` = truth; a turnstile never means Lean; `¬ ⊢_k φ` (a
Lean fact) ≠ `⊢_k ¬φ`.

---

# Part II — The engine (`engine/PrisonersDilemma/`), the host

Build: `cd engine && lake build` (default targets `PrisonersDilemma` + `OutcomeCheck` — the linter and
the census run inside the build). Namespace `PD`. Toolchain `v4.33.1`, mathlib pinned. ZERO project
axioms, no `sorry`. `lake exe export_outcomes` writes `app/generated/outcome_theorems.json` (155 cells,
4 staggered companions) and `tau_rows.json` (20 rows). Layered bottom-up:

| Layer | File(s) | What it defines |
|---|---|---|
| **Language** | `Program.lean` | `Action` (C/D), `Outcome`; the mutually recursive `Prog` (`.const/.self/.opp/.bot/.sim/.ite/.search`, plus the τ constructors `.tvote/.sys/.selfIdx`) and `Formula` (`.plays/.impl/.neg/.box/.eq`); `subst`, `size`. Pure syntax. |
| **Proof system `S`** | `ProofSystem.lean` | The ONE unified proof-term type `Pf k φ` (33 constructors; eliminators `Pf.induct`/`PlaysProof.induct` — NEVER the raw mutual recursors outside `ProofSystem.lean` §4 and `Base/ValuationSoundness.lean`). Costs are transcript-cumulative (`k` = characters of proof transcript, Critch's literal model). `AtomProvable.mk` requires `n + (plays me opp a).size ≤ k` (the atom re-cost of 2026-09-16). |
| **Dynamics** | `Dynamics.lean` | The fuelled evaluator `eval` (its `.search` guard is `proofSearch k φ := decide (Pf k φ)`, noncomputable — the engine's `eval` is a definition, not a program); `play`, `outcome`; `Formula.interp` (`.box` = `Pf`). |
| **Meta-theorems** | `Base/{Asymptotics,AtomCerts,Soundness,ValuationSoundness,Exclusion,Loeb,Transpose,BoundedGL,Closure,Helpers,TowerCensus,EvalTranspose,RedCellFramework}`; `BaseTheorems.lean` re-exports | Soundness (`sound_upto`, instances of the parametric `wv_sound_upto`); monotonicity; the internalized bounded Löb (`bloeb_engine`/`pblt_engine` via the fixpoint sentence `Formula.diag`, mutual variants); the NEGATIVE direction (`Exclusion`: the transparency census `tail_plays_readable`, the floor bounds `no_provable_probeFirst_tail`, `no_provable_searcherPlay_tail`, `no_provable_searcherElse_tail` — the cost FLOOR forced by consistency: an else-play certificate pays the full failed budget); `Transpose` (τ̂: `S` closed under C/D transposition at the SAME budget, 47-arm raw `Pf.rec` — resolved Critch's open red cell `outcome_DupocBot_vs_CupodBot = (D, C)` at every same `k`); `EvalTranspose` (`eval` commutes with τ̂); `BoundedGL` (the abstract bounded-GL interface, `Pf` a model by `rfl`, Löb/PBLT generic). |
| **Bots** | `Bots/*.lean`, `Bots/LlmGenerations/*.lean` | The zoo. `DupocTrollBot` and `DIMDID` have no engine theorems (their rows are `S'`-only). |
| **Outcome theorems** | `Theorems/<Left>/vs_<Right>.lean`; dir-local lemmas in `Theorems/<Bot>/Helpers.lean`; reusable rules in `Theorems/LlmGenerations/LlmLemmas.lean` | One file per ordered matchup. NO umbrellas: the ROOT `PrisonersDilemma.lean` imports every theorem module directly. LLM-written theorems keep the `llm_outcome_` prefix. |
| **Template, linter, census, export** | `Outcome/{Spec,Lint,Check,Export}` | See below. |
| **τ-bots** | `Tau/{Spec,Vote,Zoo,RowSpec,Lint,…}`, `Tau/Bots/*`, `Tau/Theorems/<T>/Phase.lean` | See Part III. |

**The strict outcome-theorem template is the linchpin.** Every matrix theorem is
`@[outcome] theorem (llm_)outcome_<L>_vs_<R> : OutcomeSpec <regime> <pad> L R (some (.X, .Y))`
(`Outcome/Spec.lean`; regimes `nobudget | universal | eventual`; `L R : Nat → Prog`, so staggering is a
property of the lambda; no guarded and no existential-fuel template — `Base/Helpers.outcome_at_of_ex`
lifts a `Pf_sound` witness to a literal pad). `Outcome/Lint.lean` validates every tagged theorem against
its own name; `Outcome/Check.lean` runs the census: every declaration named like a cell is tagged, no
allowlist; regime variants take a suffix (`_floor`, `_samek`) and are not cells. A pair's result under a
budget STAGGER is a `@[outcome_companion]` theorem `…_staggered` (must be staggered, must have a cell); the
matrix renders a disagreeing companion as BUDGET-SENSITIVE `(D, D) ⇄ (C, C)`; `†` = no shared-budget
theorem (the LegibleBot/OptimBot two-tier cells). Cells are SHARED-budget values (the staggered
cross-bot cooperations `PrudentBot (2k+64)` vs `DupocBot k`, JustBot × PrudentBot, JustBot ×
CupodTrollBot, CupodTrollBot × DupocBot are non-cell companions). Because the statement is fully
concrete, **compilation == correctness** (modulo the NL→Lean translation of a bot).

**Foundational status.** `PBLT` is a theorem (bounded Löb derived IN `S` via `Formula.diag`,
2026-07-01); costs transcript-cumulative (2026-07-02); the last axiom, `atom_complete_false_guard`, was
machine-checked INCONSISTENT (the anti-diagonal bot) and replaced by the sound `search_f`/`atomNeg`/`eqNeg`
machinery with the cost FLOOR (2026-07-03). Consequences, all Critch-faithful: same-budget results that
consumed a partner's else-play are honestly FALSE (tombstones in the theorem files); the seven floor
tombstones are honest outcomes (`outcome_DupocBot_vs_DBot = (D, C)`, `… PrudentBot_vs_PrudentBot = (D, D)`,
`… CupodBot_vs_OBot = (C, D)`, …); cross-bot cooperation returns at STAGGERED budgets; self-play needs the
two-tier `PrudentBot2`. Meaning-preservation vs the pre-merge `S` was a theorem (`legacy_iff_live`, in the
removed spikes). The engine's `eval` is noncomputable; uniform computability rested on the universal
closure of the instance gate (`CUT_RELEVANCE.md`, `DECIDABILITY_ROADMAP.md`) — the decidability chain
that pursued it is removed.

**Dead ends (do not retry):** deciding `Provable` by structural recursion on the program; a separate-gas
checker; proof-term enumeration under CONCLUSION cost (dissolved by transcript costs); model/realizability
witness extraction; unprovability-premised `search_f` (non-monotone fixpoint — the anti-diagonal bot is its
paradox); charging `searchThenSearch_t`'s inner premise (sinks the staggered Löb chains); uniform size bounds
for a decider's query space; a rule bridge `S → S'` (citation composes doubly-exponentially through nested
boxes, `MERGE_CROSSROAD.md`).

**Proof-craft traps:** OneDrive makes `lake build` print "Replaying X… time expired (60)" — I/O, not code;
build the target directly then the full build; never wait on `pgrep -x lake` (matches the IDE's `lake
serve`) — use `pgrep -f 'lake build'`. `simpa` needs `-forall_const` on quantified rows; set `maxHeartbeats`
BEFORE the docstring; peel before `rfl` on `fragP (inst …)`; elaborate transposed bits without an expected
type; `omega` case-splits every `max` in a threshold tower (2ⁿ) — thresholds are SUMS.

---

# Part III — The Python core (`app/`, package `pd_runner`)

**Package management — ALWAYS `uv`, never `pip`:** `uv sync --extra dev`, `uv add`, `uv run pytest`,
`uv run python -m pd_runner.…` (inside `app/`). Lint: `uv run ruff check src tests` (config in
`pyproject.toml`, rule set `E4/E7/E9/F`, `E741` ignored; keep it green). 442 tests + 6 skipped.

**Source of truth (`Research/Notes/SPRIME_SOURCE_OF_TRUTH.md`).** PA-`S'`
(`app/generated/sprime_outcome_theorems.json`) is the app's source of truth; the engine's export stays
loadable as the COMPARISON. `settings.CELL_SOURCE` (`PD_CELL_SOURCE`, default `sprime`) and
`FLOOR_POLICY` (`PD_FLOOR_POLICY`, default `engine_side`) are threaded through every loader
(`scan_outcome_theorems`/`build_outcome_matrix`, `load_tau_matrix`/`NamedZoo.load`, the EGT `sweep`).
A `S'` GENUINE FLOOR is carried as a labelled cell (`provenance="floor_dichotomy"`, `‡`, the engine-side
value), as a hole (`restrict_zoo`: totality fails naming the pairs), or — **the ROBUSTNESS CHECK,
`hinge_side`** — as the OTHER branch of its dichotomy (every box hypothesis TRUE; `eval/sprime_floors.
HINGE_SIDE_PAIRS`, re-derived from the `dich_` statements by `tests/test_floor_hinge_side.py`; floors are
never `≠` flips; the `S'` kernel floor bits are unstated under it). A `≠` cell FLIPS the engine (all
in-paper flips are DIMCID's). Kernel tau rows load PER SOURCE (`tau_rows.json` on `engine`,
`sprime_tau_rows.json` on `sprime`), each VERIFIED against its own cells at load (a floor bit must sit on
a floor cell with the same engine-side value; a provenance swap raises) and never crossed.
`python -m pd_runner.tau.compare --zoo paper --source sprime` certifies Def 3 ≡ Def 4 on `S'`
(agree / floor-agree / mismatch / uncovered: 149 / 41 / 0 / 0 on the 14-bot paper zoo, plus the 6
recorded divergences `def4_theorems.SPRIME_RECORDED_DIVERGENCES`; a recorded divergence that no longer
fires raises `StaleDivergenceWarning`). `python -m pd_runner.eval.source_diff` → `generated/source_diff.md`.
Test stand-ins `tests/fixtures/sprime_*.sample.json` are used by `conftest.py` only while a real export is
absent. A stipulation can never shadow a proven cell (`NamedZoo.contradictions` is the separate,
loud override channel of the `superficial-standalone` validation zoo — never cite a number from it).

**The tau layer (`tau/`; authoritative design note `Research/Notes/TAUBOTS.md`).** Partial
transparency as a type space over the zoo: a bot receives a SIGNAL — candidates with weights (blur in
the weights, never in the programs); the σ-families (temperature `t` = transparency, behavioral and
syntactic distances, `epsilon`) interpolate Critch's OSGT (`t=0`… point mass) and the opaque PD. **Def 3**
(self probe, base hypotheses): `TauA(α)(sig) = C iff Σ{pᵢ : A's action in outcome(A, Bᵢ) = C} ≥ α`;
**Def 4** = the uniform SOURCE lift: τ-bots are Spec-DSL rows compiled to real `Prog`s (`.tvote`
action votes, `.sys` for entangled pairs), their rows proved as `@[tau_row] RowSpec` theorems in
`engine/…/Tau/Theorems/<T>/Phase.lean` (20 templates) and as `RowSpecA` rows in `arith/` (16 paper
templates); the Python layer CERTIFIES Def 3 ≡ Def 4 instance-wise. Two dials, never conflated: `t`
(signal) and `α` (caution). NATIVE players (`tau/matrix.py::NATIVE_PLAYERS`): MaxConfidenceBot /
MinConfidenceBot = (Dupoc's test, `max`/`min ≥ θ`) — as hypotheses they are Dupoc twins (a ceiling
below 1 for the distance families, by design); `maxconfidence_not_linear`. A τ-bot ALWAYS terminates:
a swept matrix never contains the `none` state. `proveEq` decides identity by SOURCE.

**Paper zoos (`ZOOS` in `tau/matrix.py`; `--zoo` everywhere).** **The paper's base zoo is `body8`**
(CooperateBot, CupodBot, DBot, DefectBot, DupocBot, EBot, OBot, TitForTatBot — twin-free on the engine
side, 3 hinge pairs, 0 flips); the ladder `nonprovers+dupoc` (7), `body8+trolls` (10),
`body8+trolls+provers` (12), `body8+natives` (10, the aggregator comparison, ε-family only). Only these
have runs on disk; `body`/`body+twins`/`body+twins+natives` (thesis era) stay registered, runless;
`critch8` reproduces the standalone repo's eight types (fully proven since the red cell). WaryBot can be
in no total `S'` roster; no floor-free roster contains DupocBot. Caution grid α ∈ {0.2, 0.4, 0.5, 0.6,
0.8, 1} (re-chosen 2026-10-19).

**EGT (`egt/`; records `Research/Notes/EGT_FINDINGS_SPRIME.md`, thesis-era `EGT_FINDINGS.md`).** Stages:
`static_analysis/` (pure ESS), `invasion/` (`G>`/`G≥` graphs, SCCs), `faces/` (face equilibria), `nash/`
(extreme NE, exact `Fraction`), `replicator/` (basins — grouped by SUPPORT, not proximity; non-convergence
is a finding), `moran/` (fixation, stochastic stability; log-space); `pipeline.py` runs a `(t, α)` sweep
(`--resume` reuses complete run dirs by fingerprint), `report.py` renders. PD convention `(D,C)=b,
(C,C)=b−c, (D,D)=0, (C,D)=−c`. Headline: on `body8` DupocBot is uniquely stochastically stable at full
transparency, its share rising with selection intensity (85.9% at (M, β) = (100, 1); 71.2% on the hinge
side); partial transparency: critical transparency U-shaped in caution, static = dynamic collapse,
same thresholds on the syntactic channel (`EGT_FINDINGS_SPRIME.md` §10, `latex/scripts/gen_tau_*.py`).
**Traps:** `--alphas phases` is exact but ~|zoo|² phases per `t` (hours of Nash) — use the α list; the
unit of work is the DISTINCT MATRIX (runs keyed by a cell hash; `grid_points` maps points to runs);
`lrsnash` is optional and usually absent (recorded as `cross_check_performed: false`, never as passed);
a truncated face enumeration carries a TRUNCATED marker; sweep artefacts are gitignored
(`generated/egt/.gitignore`); share ≠ cooperation rate; α = 0 is degenerate. The standalone repo's
hand-transcribed CSV disagrees with the kernel on 6 of 62 cells (`CRITCH8_TRANSCRIPTION_DIFFS`).

---

# Part IV — The LLM pipeline (`pipeline/`, package `pd_pipeline`)

Out of the paper's scope; `pipeline/README.md` and `pipeline/docs/BOT_REVIEWER.md` are the
references. `cd pipeline && uv sync --extra dev` (installs `pd-runner` from `../app` editable; `anthropic
< 1` pinned — the 1.x SDK rejects the calibrated client's `httpx.Timeout`); `uv run pd-serve --reload`;
`uv run run-matchup`; 255 tests. Keys in `pipeline/.env` (loaded on import; never exported from a shell
rc). Its `generated/` holds the agents' artefacts: `constructor_proposals/`, `prepass/`,
`lemma_attempts/` tracked; `outcomes/` (the proof-episode transcripts, longitudinal thesis data),
`reviews/`, `integrations/`, `lean/`, `logs/` gitignored.

**Architecture.** Proof agent = Proposer → Compiler → Reviewer → Memory (AxProverBase-style):
`services/proof_episodes.py::run_proof_search`, up to 3 fresh-context episodes × 10 turns, only the lab
notebook, the best compiling source, the last compiler feedback and a prior open verdict cross episodes;
the first `open_*` verdict buys ONE retry episode. Fast compile through a persistent LeanInteract REPL
(`lean/interact.py`, `PD_LEAN_INTERACT=0` to disable; the verdict gate and the library writer ALWAYS
file-compile). Verdicts via `submit_verdict` (`proved | open_bistable | open_blocked |
constructor_proposed`), never prose. A `proved` submission is RE-COMPILED with `#validate_outcome` plus
textual checks (exact `llm_outcome_<L>_vs_<R>` name, `@[outcome]`, template head, no `proofSearch`
premises, no sorry/axiom, no hand-rolled `Pf.induct` census, no name collisions) — the same checks
`library_writer` enforces, which then builds `PrisonersDilemma` + `OutcomeCheck` in a transaction
(byte-identical rollback) and refreshes the export. Prompt caching with 4 breakpoints
(`llm/prompts.py::build_system_prompt_blocks`); `ProofSystem.lean` and `Base/Exclusion.lean` embedded as
signature digests. Multi-provider: `claude-*` → the calibrated `AnthropicClient`; other names →
`settings.OPENAI_COMPAT_PROVIDERS` (`leanstral-1-5`) or `PD_OPENAI_BASE_URL` → `OpenAICompatClient`
(mirrored 1:1 — change both). Config: `pd_pipeline.settings` (`DEFAULT_MODEL`, `RetryPolicy`,
`RetrievalConfig`, `EvalGuard` = `hidden_bots` vs `allow_library_growth`).

**Bot synthesis and the faithfulness reviewer** (`docs/BOT_REVIEWER.md`): bot writer
(`services/bot_service.py`, full `Prog`, `run_lean_build` tool); **Tier A1** blind expectation extractor
(`bot_expectation.py` — takes the description string, never the Lean; `unspecified` is a first-class
answer; `explicit` vs `inferred` decides hard-fail vs warn; UNANIMITY OVERRIDES CONFIDENCE); **Tier A2**
certified behavioral profile (`bot_profile.py` over `eval/outcome_prepass.py`, `k ∈ {2,4,6,16}` — THE
BUDGET SWEEP IS LOAD-BEARING; `jobs × memory_mb` is what the machine sees, the 3072 MB per-cell cap is
MEASURED; **requires the removed `Decidability` chain**); **Tier B** judge on the residual only
(advisory; NO ground truth; never a verification result in the paper). Comparison is deterministic code
(`faithful | mismatch | underdetermined`); the rewriter loop (`bot_rewriter.py`) triggers only on
`should_rewrite`. Nothing auto-accepts: human gates at bots and proof (`run_bot_pipeline`, the API).

**Growth ladder:** `add_base_lemma` (Tier 1, derived rules in `LlmLemmas.lean`, sound by construction,
transactional) and `propose_pf_constructor` (Tier 2, human-gated evidence bundle with a soundness
certificate compiled against the engine; integration by an agent in a git WORKTREE, `git diff` reviewed
by a human; `/proposals/{name}/integrate`, `/integration/{job}/accept-diff`). Both registered only when
`hidden_bots` is empty — the eval harness never mutates the library. Bare `OUTCOME OPEN` is reserved for
BISTABLE matchups; no base cell is currently certified bistable.

**Eval:** `eval/common.py` (14 harness cases) shared by `harness.py` and `run_bot_matrix.py`; every run
persists to `generated/outcomes/`. Prover-model comparison (E4): `Research/Notes/PROVER_MODEL_COMPARISON.md`.
SOTA provers (DeepSeek/Goedel/Kimina) are NOT swapped in: out of distribution for the custom inductive
types; E4 numbers justify the bespoke pipeline.

---

# Cross-cutting conventions

* The two JSON exports are the ONLY interface between Lean and Python; no regex over Lean source.
* Commit by file name; one lake build at a time; `arith/` and `engine/` share the toolchain and the
  mathlib commit. CI (`.github/workflows/lean_action_ci.yml`) builds both Lean packages.
* `latex/` is the user's: `paper_status.tex` and `figures and tables/` are edited by the user; the
  generators `latex/scripts/gen_*.py` read `app/generated/` and the EGT runs.
* Never quote a Cantor-coding constant; state every `S'` result "for all large `k`".
* Memory of past sessions: the notes under `Research/Notes/` are the record; dated narratives there
  supersede any summary here.
