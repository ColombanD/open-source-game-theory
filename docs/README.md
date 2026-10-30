# `docs/` — the design record

The notes behind the formalization and the experiments: why the proof system is built the way it is,
what is proved, what was tried and abandoned, and the traps that cost a session each. The paper
(`latex/`) is the public account; these are the working record, kept because the code alone does not
say *why*. Names are stable; older notes cite each other by name.

## Live — about the code as it is

| Note | What it holds |
|---|---|
| [`SPRIME_DESIGN_RATIONALE.md`](notes/SPRIME_DESIGN_RATIONALE.md) | The trusted base of PA-`S'`: the nine definitions a reader accepts by eye, and the one design choice behind each. Read first. |
| [`ARITHMETIZED_S_RESULTS.md`](notes/ARITHMETIZED_S_RESULTS.md) | What `arith/` proves: PBLT, bounded inner necessitation, the matrix, the floors, the flips. |
| [`ROUTE_B_SCOPE.md`](notes/ROUTE_B_SCOPE.md) | The cell-by-cell programme (route B): methods per cell class, route (c) for budget-carrying snapshots, what is deliberately out of scope (LegibleBot, OptimBot, WaryBot's floors). |
| [`ROUTE_B_CENSUS.md`](notes/ROUTE_B_CENSUS.md) | The ledger over the engine's census rows: stated / agree / flip / floor / excluded, cell by cell. |
| [`ROUTE_B_CELLS_MAP.md`](notes/ROUTE_B_CELLS_MAP.md) | Where each cell's proof lives in `arith/ArithS/Cells/`, and the naming scheme. |
| [`ARITH_TRAPS.md`](notes/ARITH_TRAPS.md) | The consolidated trap list for writing `ArithS` (coding, `simp` and Gödel quotes, `omega` on `V`, builds). Read before writing a line. |
| [`SPRIME_SOURCE_OF_TRUTH.md`](notes/SPRIME_SOURCE_OF_TRUTH.md) | How the Python layer reads the two exports: `CellSource`, `FloorPolicy`, the kernel-backed tau rows, the recorded divergences. |
| [`TAUBOTS.md`](notes/TAUBOTS.md) | Partial transparency: Defs 1–4, the σ-families, the Spec DSL, the roster and its exclusions, the native players, remaining debt. |
| [`EGT_FINDINGS_SPRIME.md`](notes/EGT_FINDINGS_SPRIME.md) | The evolutionary results on the `S'` matrices: the base zoo `body8`, the ladder, the hinge side, partial transparency. |
| [`PROVABILITY_NOTATION.md`](notes/PROVABILITY_NOTATION.md) | `⊢_k`, `⊨`, meta: the three levels and the three negations, fixed for the paper. |
| [`ARITH_DEAD_CODE_AUDIT.md`](notes/ARITH_DEAD_CODE_AUDIT.md) | The reachability audits of `arith/` (September and October 2026): method, the tool, what was pruned and why. |
| [`MERGE_CROSSROAD.md`](notes/MERGE_CROSSROAD.md) | Why a rule bridge `S → S'` is impossible at polynomial budgets, and why cells are re-proved instead. |

## Archive — decisions that still shape the code

| Note | What it holds |
|---|---|
| [`DESIGN_CHOICES.md`](notes/archive/DESIGN_CHOICES.md) | The engine's design decisions, in the order they were made. |
| [`UNIFIED_PF_SKETCH.md`](notes/archive/UNIFIED_PF_SKETCH.md), [`PF_REPLACEMENT_ASSESSMENT.md`](notes/archive/PF_REPLACEMENT_ASSESSMENT.md), [`PF_ONLY_ROADMAP.md`](notes/archive/PF_ONLY_ROADMAP.md) | The unification of the engine's proof terms into one `Pf` type (July 2026): design, cost model, the executed plan and its gates. |
| [`FAMILY_COMPLETION_DESIGN.md`](notes/archive/FAMILY_COMPLETION_DESIGN.md) | The closure of `S`'s rule families (implication, search telescopes). |
| [`ARITHMETIZED_S_ROADMAP.md`](notes/archive/ARITHMETIZED_S_ROADMAP.md), [`HANDOVER_ARITHMETIZED_S.md`](notes/archive/HANDOVER_ARITHMETIZED_S.md) | The milestones M1–M6 of `arith/` and the hand-over note (build recipe, the first trap list). |
| [`BEW_PRIMER.md`](notes/archive/BEW_PRIMER.md), [`BOXCOST_SPIKE.md`](notes/archive/BOXCOST_SPIKE.md) | A primer on Foundation's provability predicate, and the measurement that fixed the cost of a box. |
| [`RED_CELL_AUDIT.md`](notes/archive/RED_CELL_AUDIT.md) | The audit of the red cell (CupodBot vs DupocBot) before it was promoted. |
| [`EGT_FINDINGS.md`](notes/archive/EGT_FINDINGS.md) | The thesis-era evolutionary results on the engine's matrices (superseded by the `S'` findings). |
| [`PROVER_MODEL_COMPARISON.md`](notes/archive/PROVER_MODEL_COMPARISON.md) | The LLM pipeline's prover-model case study (out of the paper's scope). |
| [`UnderstandingTheLayers.md`](notes/archive/UnderstandingTheLayers.md) | An early tutorial walk through the engine's layers. |
| [`DeadEnds/`](notes/archive/DeadEnds/) | Constructive bounded Löb, a constructed `Bew`, a normalization road map: tried and abandoned, with the reasons. |
| [`M3_TRANSFER/`](notes/archive/M3_TRANSFER/), [`M4_BOUNDED_HBL/`](notes/archive/M4_BOUNDED_HBL/) | The agent briefs and reading notes of the transfer theorem and of bounded inner necessitation (U10): the working documents behind `arith/ArithS/Necessitation/`. |

## Archive — about code removed on 2026-10-29

| Note | What it holds |
|---|---|
| [`DECIDABILITY_ROADMAP.md`](notes/archive/DECIDABILITY_ROADMAP.md) | The engine's decidability chain T31–T54: the verified enumerator, the computable evaluator, the modest and instance strata. |
| [`CUT_RELEVANCE.md`](notes/archive/CUT_RELEVANCE.md) | CutRelevance: falsified as stated, repaired by the instance gate, decidability at that gate. |
| [`T49_BOUNDED_LOB_NORMALIZATION.md`](notes/archive/T49_BOUNDED_LOB_NORMALIZATION.md) | The tree substrate and normalization theorem of the chain. |

The code these describe is in git history at commit `3f99464`.

## Readings

[`readings/`](readings/): reading notes on Critch's bots, on robust program equilibria, and on the
tournament bots, with the tournament results (`.scm`). The engine's golden outcome inventories stay in
`engine/PrisonersDilemma/Research/Data/`.
