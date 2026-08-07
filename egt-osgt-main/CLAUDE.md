# CLAUDE.md

## Operating instructions for coding agents

**Read this file before doing anything in this repository.** It is the single
source of truth for what this project is, what has been built, and what is
in progress. Every change to the codebase should be reflected here.

**After making changes, update this file** update any other section that 
is no longer accurate (e.g., the "Implemented" / "In progress" lists, module 
map, or dependencies). Do not let the codebase and this document drift apart.

---

## What this repository is

This repository contains an **evolutionary game theory (EGT) analysis of a
finite population of open-source agents** playing the anonymous repeated
Prisoner's Dilemma in the sense of Critch, Dennis, and Russell (2022),
*"Cooperative and uncooperative institution designs: Surprises and problems
in open-source game theory"* (arXiv:2208.07006). The inputs to the analysis
are an integer `N` (number of agent types) and a deterministic outcome
matrix recording, for each ordered pair (i, j), the action profile resulting
from a single match between agents i and j.

### Background: the Critch 2022 paper

Critch et al. study **program equilibria**: game-theoretic interactions in
which each agent is a program with full read access to the other agent's
source code. Because each agent can formally reason about the other before
choosing an action, the outcome of a single Prisoner's Dilemma between two
such agents is fully deterministic and need not coincide with classical
Nash predictions. The paper introduces a family of *formal verifier agents*
built from a bounded proof search of length `k`:

- **CooperateBot (CB) / DefectBot (DB):** unconditional baselines.
- **CUPOD(k)** ("Cooperate Unless Proof Of Defection"): defects only if it
  proves the opponent will defect against it; cooperates otherwise.
- **DUPOC(k)** ("Defect Unless Proof Of Cooperation"): cooperates only if
  it proves the opponent will cooperate against it; defects otherwise.
- **CIMCIC(k), DIMCID(k):** *conditional* variants that prove material
  implications rather than unconditional outcomes.

The central technical tool is the **Parametric Bounded Löb Theorem (PBLT)**,
a resource-bounded form of Löb's theorem. PBLT yields several counterintuitive
self-play results: CUPOD vs. CUPOD ends in `(D, D)`, while DUPOC vs. DUPOC
ends in `(C, C)`, contrary to most readers' intuitions. DUPOC-style agents
are unexploitable, reward legibly-cooperative opponents, and reward agents
that themselves reward legible cooperation, which makes the population-level
dynamics among such bots a natural and substantive question (the paper
poses it as Open Problem 2).

### The payoff matrix in this repository

The file `data/payoff_matrix.png` (and any machine-readable form derived
from it under `data/`) encodes the outcomes of one-shot Prisoner's Dilemma
matches among nine OSGT bot types:

`CooperateBot, CupodBot, DBot, DefectBot, DupocBot, OBot, TitForTatBot,
MirrorBot, EBot`.

Each cell `(i, j)` records the action pair `(action_i, action_j)`. The
matrix is **upper-triangular as displayed** (the lower triangle is masked
in black because outcomes are symmetric in the *game*, though payoffs to
each player may be asymmetric and are derived from the action pair via a
standard PD payoff convention). One cell — `(CupodBot, DupocBot)` — is
marked in red, indicating it is unresolved in the paper (corresponding to
an open problem in the Critch et al. analysis); the analysis must treat it
explicitly rather than silently assigning a value. The cell
`(MirrorBot, MirrorBot)` is labelled `none` because two MirrorBots induce
non-termination, and this too must be handled explicitly.

## What is implemented in this repository (high level)

The intended end state is a complete EGT pipeline on the supplied payoff
matrix: (i) ingestion of the action-pair matrix and conversion to a real
payoff matrix `A` under a configurable PD convention; (ii) static analysis
(ESS enumeration, invasion graph, face- and interior-equilibrium search);
(iii) deterministic replicator-dynamics simulation with basin estimation;
(iv) finite-population Moran-process analysis (fixation probabilities,
small-mutation-limit stationary distribution, stochastic stability) across
sweeps over population size `M` and selection intensity `β`; and (v) a
report layer producing figures, tables, and a written summary. Undefined
or contested entries of the payoff matrix (the red and `none` cells) are
handled by an explicit policy module rather than imputed silently.

**Implemented so far:** stages (i), (ii.a), (ii.b), (ii.c), and (ii.d).

- **Stage (i)** — data and ingestion. The action-pair CSV is loaded, the
  unresolved `(CupodBot, DupocBot)` cell is filled from a configured default,
  MirrorBot is excluded from the analysed matrix (handling its non-terminating
  self-pairing by exclusion), and the result is converted to the row-player
  payoff matrix `A` under `b > c > 0`.
- **Stage (ii.a) — pure-strategy ESS enumeration.** `src/static_analysis/`
  enumerates Maynard-Smith two-condition pure ESS over the non-symmetric `A`
  and emits a structured audit trail under `results/ess/`: per-type verdicts
  (`ess_summary.csv`), per-ordered-pair clause evaluations (`ess_pairwise.csv`),
  the numeric `A` (`payoff_matrix_numeric.csv`), `assumptions.json`, and a
  stand-alone `report.md`. Pairwise rows touching the red cell are flagged
  with `touches_suspect_cell=True`; the corresponding types carry a
  `"depends on red cell"` note in the summary. CLI:
  `conda run -n py-random python -m src.static_analysis.cli`.
- **Stage (ii.b) — invasion graph.** `src/invasion/` builds two
  `networkx.DiGraph` instances over the 8 OSGT types: `G>` (strict, edge
  `i → j` iff `A[i, j] > A[j, j]`) and `G≥` (weak, `A[i, j] ≥ A[j, j]`).
  The set `E(G≥) \ E(G>)` is exactly the tied pairs where ESS clause (b)
  bites. The pipeline computes strongly connected components, the
  condensation DAG via `nx.condensation`, all simple cycles
  (`nx.simple_cycles`, capped at 10000 with a length-bound fallback),
  per-vertex roles (`isolated`, `clause_a_candidate`, `in_cycle`,
  `impotent`, `transient`), and cross-checks the in-degree-zero set in
  `G>` against `ess_summary.csv` (in-degree-zero is necessary but not
  sufficient for ESS — disagreements are mapped to the responsible
  column ties). Edges and ties touching the red cell carry a
  `touches_suspect_cell` flag. Outputs under `results/invasion/`:
  `edges_strict.csv`, `edges_weak.csv`, `ties.csv`, `vertex_summary.csv`,
  `sccs.json`, `cycles.json`, `cross_check.md`, `assumptions.json`,
  `report.md`, the GEXF serialisations `graph.gexf` / `graph_weak.gexf`,
  and the visualisations `graph.svg` / `graph.png` (vertices coloured by
  role, strict edges solid, ties dashed, non-singleton SCCs in
  translucent boxes) plus `condensation.svg` / `condensation.png`.
  Layout preference: graphviz `dot` via `pygraphviz` (used when
  installed), then `pydot`, then a manual layered layout from the
  condensation's topological order, with `spring_layout(seed=...)` as a
  last resort. CLI:
  `conda run -n py-random python -m src.invasion.cli`.
- **Stage (ii.c) — face equilibrium enumeration and classification.**
  `src/faces/` enumerates every non-empty support `S ⊆ {1,…,N}` with
  `|S| ≥ 2` (no pruning by strict domination or any other criterion;
  `2^N − N − 1` rows total), solves the `(|S|+1)×(|S|+1)` block system
  `[[A_SS, -1], [1ᵀ, 0]] [x; c] = [0; 1]` for the unique
  algebraic fixed point `x_S*` via `scipy.linalg.solve`, computes the
  replicator Jacobian `J[a,b] = x_a · (A[a,b] − (Ax)_b − (Aᵀx)_b)` at
  `x*`, projects to the tangent space `{v ∈ R^|S| : 1ᵀv = 0}` using
  `scipy.linalg.null_space`, and reads stability off
  `scipy.linalg.eig(QᵀJQ)`. External invasion fitness `(Ax*)_k − c`
  is also recorded for every `k ∉ S`. Edge cases (singular `A_SS`,
  non-interior algebraic solution, `|S|=2` 1-D tangent, full-support
  vacuous external check) are recorded — never silently skipped.
  Outputs under `results/faces/`: `face_equilibria.parquet` (canonical),
  `face_equilibria.csv` (human-readable mirror, complex eigvals
  JSON-encoded), `assumptions.json` (tolerance, methods, library
  versions, inherited PD payoffs and undefined-cell policy), and
  `summary.md` (counts by `overall_class` plus enumerations of stable,
  singular, and non-hyperbolic rows). CLI:
  `conda run -n py-random python -m src.faces.run`.
- **Stage (ii.d) — Nash equilibrium enumeration (Method 2).**
  `src/nash/` enumerates every extreme Nash equilibrium of the symmetric
  bimatrix `(A, A^T)` via best-response polytopes and labelled vertex
  enumeration (Avis–Rosenberg–Savani–von Stengel). All computation runs
  in exact rational arithmetic (`fractions.Fraction`); the payoff matrix
  is shifted entrywise by `c_shift = -min(A) + 1` to make
  `A' > 0` (required by the polytope construction), then unshifted on
  output — `config.json` is never modified. Two independent
  implementations enumerate in parallel: **pygambit**
  (`pygambit.nash.enummixed_solve(rational=True)`, primary) and
  **lrsnash** (lrslib command-line tool, secondary). The pipeline
  asserts the two libraries agree on the extreme NE set as a hard
  cross-check; it also asserts every pure NE found by direct
  inspection appears in Method 2's output, that at least one symmetric
  NE exists (Nash 1951), and that every NE re-verifies as a best
  response on the **original** unshifted `A`. Extreme NE are
  classified as symmetric (`xi == eta`) or asymmetric (asymmetric NE
  pair with `(eta, xi)` by swap, sharing a pair id) and grouped into
  Nash components by exact-midpoint NE testing. Iterated pure strict
  dominance is logged. Outputs go to a versioned, per-run directory
  `results/nash/runs/<UTC-timestamp>_<short-hash>/`, with a
  `results/nash/latest` symlink to the most recent run and an
  append-only `results/nash/runs/INDEX.csv`. Per-run files:
  `equilibria.jsonl` (one extreme NE per line, schema pinned in
  `src/nash/io.py:EQUILIBRIA_FIELDS`), `equilibria_summary.md`,
  `nash_components.json`, `provenance.json` (CSV sha256, library
  versions, payoff shift, dominance log, wallclocks),
  `assumptions.json`, `dominance_log.json`, `verification_report.md`.
  Each equilibrium record carries: exact rationals + float
  approximations for the mixed strategies and payoffs, equilibrium
  payoffs `u, v` recovered in the **original** payoff scale,
  cooperation rate `Pr[(C, C)]` from the action-pair matrix `M`,
  symmetry classification, component id, suspect-cell flag (touches
  `(CupodBot, DupocBot)` per the invasion-stage convention), and
  discovery records from each finder. CLI:
  `conda run -n py-random python -m src.nash.cli`. Required
  dependencies (install into the `py-random` conda env): `pygambit`
  via `pip install pygambit`; `lrsnash` (lrslib binary) via
  `conda install -n py-random -c conda-forge lrslib`.

The remainder of stage (ii) is complete; stages (iii)–(v) are not yet
implemented.

---

## Repository layout (update when modules are added or removed)

```
.
├── CLAUDE.md                    # this file
├── config.json                  # configs parameters
├── Critch2022.pdf               # reference paper
├── data/
│   ├── payoff_matrix.png        # source image of the outcome table
│   └── payoff_matrix.csv        # machine-readable action-pair matrix (MirrorBot excluded)
├── src/
│   ├── ingest/                  # parsing the outcome table → payoff matrix A
│   │   ├── payoffs.py           # PD payoff convention + b>c>0 validation
│   │   ├── undefined_policy.py  # resolve red / non-terminating cells
│   │   └── matrix_loader.py     # CSV + config → numerical payoff matrix A
│   ├── static_analysis/         # ESS, invasion graph, face equilibria
│   │   ├── ess.py               # pure-strategy ESS enumeration (Maynard-Smith)
│   │   ├── reporting.py         # CSV / JSON / Markdown writers
│   │   └── cli.py               # load → enumerate → write results/ess/
│   ├── invasion/                # invasion graph G>/G≥ on the numeric A
│   │   ├── loader.py            # reuse results/ess/payoff_matrix_numeric.csv
│   │   ├── graph.py             # nx.DiGraph build for G> and G≥
│   │   ├── analysis.py          # SCCs, condensation, cycles, roles
│   │   ├── cross_check.py       # compare clause-(a) candidates vs ESS
│   │   ├── reporting.py         # CSV / JSON / Markdown / GEXF writers
│   │   ├── layout.py            # graphviz dot → manual layered → spring
│   │   ├── viz.py               # matplotlib renderer (graph + condensation)
│   │   └── cli.py               # load → build → analyse → write results/invasion/
│   ├── faces/                   # face equilibria: enumerate, solve, classify
│   │   ├── enumerate.py         # itertools.combinations over supports
│   │   ├── jacobian.py          # block solve + replicator Jacobian + tangent eigs
│   │   ├── classify.py          # within-face + external + overall classification
│   │   ├── io.py                # numeric A loader + parquet/CSV/JSON/MD writers
│   │   └── run.py               # CLI: load → enumerate → classify → write
│   ├── nash/                    # Nash equilibria via Method 2 (polytopes, exact)
│   │   ├── loader.py            # load (A, M) via invasion.loader + ingest pair-matrix
│   │   ├── game_construction.py # numpy A → Fraction matrix; build (A, A^T)
│   │   ├── payoff_shift.py      # c_shift = -min(A)+1; assert A_shifted > 0
│   │   ├── pure_ne.py           # O(N^3) direct pure-NE enumeration (sanity)
│   │   ├── dominance.py         # iterated pure strict dominance reducer
│   │   ├── extreme_ne.py        # shared ExtremeNE dataclass
│   │   ├── method2_pygambit.py  # pygambit.nash.enummixed_solve(rational=True)
│   │   ├── method2_lrsnash.py   # subprocess wrapper around lrsnash binary
│   │   ├── reconcile.py         # deduplicate; assert libraries agree
│   │   ├── verification.py     # exact-arithmetic best-response check on original A
│   │   ├── cooperation.py       # Pr[(C, C)] under (xi, eta) from action-pair M
│   │   ├── classification.py    # symmetric/asymmetric + pair matching + components
│   │   ├── io.py                # writers + run-id directories + INDEX.csv + symlink
│   │   └── cli.py               # load → shift → enumerate → reconcile → verify → write
│   ├── replicator/              # deterministic dynamics, basin estimation  (TODO)
│   ├── moran/                   # finite-population stochastic analysis  (TODO)
│   └── report/                  # figures, tables, written summaries  (TODO)
├── tests/                       # unit and validation tests
│   ├── test_payoffs.py          # PD parameter validation
│   ├── test_ess.py              # pure-strategy ESS enumeration + writers
│   ├── test_invasion_graph.py   # graph construction, attrs, edge cases
│   ├── test_invasion_analysis.py# SCC/cycle/role/condensation correctness
│   ├── test_invasion_crosscheck.py # clause-(a) vs ESS, tie-flip scenarios
│   ├── test_invasion_io.py      # schemas, GEXF round-trip, OSGT regression
│   ├── test_faces_hawk_dove.py  # 2x2 full-support asymp_stable, x_H=V/C
│   ├── test_faces_rps.py        # 3x3 zero-sum: non_hyperbolic, ±i/√3
│   ├── test_faces_coordination.py # 3x3 diag(1,1,1) sub-faces unstable
│   ├── test_faces_singular.py   # singular A_SS recorded not skipped
│   ├── test_faces_negative_component.py # non-interior algebraic x*
│   ├── test_faces_io.py         # column schema; parquet/CSV round-trip
│   ├── test_nash_method2.py     # Hawk-Dove, coordination, RPS, pure-NE + classify
│   ├── test_nash_io.py          # equilibria/provenance/components schema, INDEX.csv
│   └── test_nash_pipeline.py    # real-OSGT regression (DefectBot pure NE, etc.)
├── notebooks/                   # exploratory analyses
└── results/                     # generated artifacts (figures, tables)
    ├── ess/                     # ess_summary.csv, ess_pairwise.csv,
    │                            # payoff_matrix_numeric.csv,
    │                            # assumptions.json, report.md
    ├── invasion/                # edges_strict.csv, edges_weak.csv, ties.csv,
    │                            # vertex_summary.csv, sccs.json, cycles.json,
    │                            # cross_check.md, graph.gexf, graph_weak.gexf,
    │                            # assumptions.json, report.md,
    │                            # graph.svg/png, condensation.svg/png
    ├── faces/                   # face_equilibria.parquet, face_equilibria.csv,
    │                            # assumptions.json, summary.md
    └── nash/                    # per-run subdirectories under runs/<ts>_<hash>/
        ├── latest -> runs/...   # symlink to most recent run
        └── runs/                # INDEX.csv (append-only) + run dirs containing
                                 # equilibria.jsonl, equilibria_summary.md,
                                 # nash_components.json, provenance.json,
                                 # assumptions.json, dominance_log.json,
                                 # verification_report.md
```

## Conventions

- **Language:** Python 3.11+.
- **Environment:** Always run Python, `pytest`, `pip`, and any other Python
  tooling through the conda env `py-random`. Prefix shell commands with
  `conda run -n py-random ...` (e.g. `conda run -n py-random pytest`,
  `conda run -n py-random python -m src.ingest.matrix_loader`).
- **Numerics:** NumPy, SciPy, NetworkX. Prefer `numpy.random.default_rng`
  with seeds derived from a single master `SeedSequence` in `config.json`.
- **Graph code:** all directed-graph construction, SCC/condensation,
  cycle enumeration, and degree readouts go through `networkx`
  (`networkx.DiGraph`, `nx.strongly_connected_components`,
  `nx.condensation`, `nx.simple_cycles`, `nx.topological_sort`,
  `nx.isolates`). The graphviz `dot` layout (via `pygraphviz`) is the
  preferred backend for hierarchical visualisations; a manual layered
  layout from the condensation's topological order is the fallback when
  graphviz bindings are unavailable.
- **Payoff matrix `A`:** rows index the row player, columns the column
  player; `A[i, j]` is the row player's payoff. `A` is generally
  **not symmetric** — code must use the asymmetric-payoff forms of all
  EGT formulas.
- **Undefined entries:** the unresolved `(CupodBot, DupocBot)` cell and
  the non-terminating `(MirrorBot, MirrorBot)` cell are represented by a
  sentinel and routed through `src/ingest/undefined_policy.py`. Any
  computation that touches them must declare which policy it applied.
- **Reproducibility:** every experiment takes a seed and writes its
  configuration alongside its output.




