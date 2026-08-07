# Invasion graph on the OSGT payoff matrix

PD payoffs: `b=3.0`, `c=1.0` → `(T=3.0, R=2.0, P=0.0, S=-1.0)`. See `assumptions.json` for the full convention.

Vertex set (8): CooperateBot, CupodBot, DBot, DefectBot, DupocBot, OBot, TitForTatBot, EBot.

Strict edges (G>): **18**. Weak edges (G≥): **41**. Tied pairs (clause-(b) territory): **23**.

## Strongly connected components

| scc_id | size | is_terminal | members |
|---|---|---|---|
| 0 | 6 | True | CooperateBot, CupodBot, DBot, OBot, TitForTatBot, EBot |
| 1 | 1 | False | DefectBot |
| 2 | 1 | False | DupocBot |

Condensation has 3 nodes and 2 edges. Topological order: [1, 2, 0]. Terminal SCCs: [0]. See `sccs.json` for full adjacency.

## Cycles

Total simple cycles enumerated: **11** (cap = 10000, cap_hit = False).

Counts by length:
- length 2: 1
- length 3: 3
- length 4: 3
- length 5: 3
- length 6: 1

Two-cycles:
- CupodBot ↔ DBot

## Vertex roles

| vertex | in_deg | out_deg | role | scc_id |
|---|---|---|---|---|
| CooperateBot | 3 | 2 | in_cycle | 0 |
| CupodBot | 5 | 1 | in_cycle | 0 |
| DBot | 6 | 2 | in_cycle | 0 |
| DefectBot | 0 | 2 | clause_a_candidate | 1 |
| DupocBot | 0 | 2 | clause_a_candidate | 2 |
| EBot | 2 | 3 | in_cycle | 0 |
| OBot | 1 | 3 | in_cycle | 0 |
| TitForTatBot | 1 | 3 | in_cycle | 0 |

## Cross-check with ESS

Clause-(a) candidates: **2**. Pure ESS per `ess_summary.csv`: **0**. Disagreements (always shape: candidate but not ESS): **2**. See `cross_check.md` for the per-vertex narrative.

## Flagged input

The following edges and ties reference the red cell `(CupodBot, DupocBot)`, which is unresolved in Critch et al. 2022. Verdicts depending on these should be treated as conditional on the chosen action-pair resolution.

Strict edges touching the suspect cell:
- DupocBot → CupodBot

## Methodology

Edge convention: `i → j` iff `A[i, j] > A[j, j]` (strict invasion). Weak invasion: `i →= j` iff `A[i, j] ≥ A[j, j]`. Equality tolerance: `atol = 1e-12`. Built with `networkx=3.6.1`.
