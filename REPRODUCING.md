# Reproducing the paper

This guide maps each claim of the paper *Open Source Game Theory: Formalization, Transparency, and Cooperation
in Program Games* to the code that backs it, and gives the command that checks it.

There are two kinds of claims and two ways to check them.

* **Theorems about programs** (the formal system `S`, the outcome of each pair of programs) are Lean 4 theorems.
  They are checked by building `arith/`; nothing is run.
* **Experiments** (equilibria, replicator dynamics, partial transparency) are Python computations on the outcomes
  the Lean build exports. Their results are tracked in `app/paper_results/` and can be re-read in a second or
  recomputed in about an hour.

## 1. Where things are

| Part of the paper | Where | How it is checked |
|---|---|---|
| Program equilibrium, τ-program equilibrium, undetectable deviations (the theory section and its proofs appendix) | The paper only | Proved on paper. Not mechanized. |
| The formal system `S`, its proof methods, transposition, `DupocBot` against `CupodBot`, the floors (the sections on `S` and on Lean, and their appendices) | [`arith/`](arith/) | `lake build` in `arith/` |
| The programs themselves and the evaluator that `arith/` arithmetizes | [`engine/PrisonersDilemma/`](engine/PrisonersDilemma/): `Program.lean`, `Dynamics.lean`, `Bots/`, `Tau/Bots/` | Built as a dependency of `arith/` |
| The outcome matrices and the PrudentBot row | [`app/generated/sprime_outcome_theorems.json`](app/generated/sprime_outcome_theorems.json), exported from the tagged theorems of `arith/` | `python -m pd_runner.paper.matrix` |
| Full and partial transparency experiments (the experiments section and its three appendices) | [`app/src/pd_runner/`](app/src/pd_runner/), results in [`app/paper_results/`](app/paper_results/) | `python -m pd_runner.paper.numbers`, `pytest tests/test_paper_numbers.py` |

The only interface between Lean and Python is the JSON export. Python never reads Lean source.

## 2. Names: the paper and the code

The code was written before the paper's vocabulary settled. Read the code through this table.

| The paper says | The code says |
|---|---|
| the formal system `S` | **PA-`S'`**, `S'`, `sprime`, `ArithS`: everything under `arith/` |
| (not in the paper) | **`S`**, `Pf`, "the engine's rule system": an earlier rule-based proof system in `engine/`, kept as a comparison. No theorem of `arith/` uses it. |
| program | bot, `Prog` |
| program library | zoo |
| the library `Σ` (8 programs) | `body8` |
| `Σ` without `CupodBot`; `Σ` + trolls; `Σ` + trolls + provers | `nonprovers+dupoc`; `body8+trolls`; `body8+trolls+provers` |
| `⊢_k φ`, `□_k φ` | `LenBox TAct k ⌜φ⌝`, written `□[k] φ` |
| outcome `(D, C)` for every `k` / for all large `k` | `OutcomeSpecA .universal … (some (.D, .C))` / `.eventual` |
| transposition `𝒯` of formulas, proofs and programs | `swap`, `lMap swap`, `Prog.transpose`, `transposeCode` |
| floor, hinge `H_k` | floor, `FloorSpecA`; the hinge is printed in each `dich_<L>_vs_<R>` statement |
| negative side of the hinge | `engine_side` (the default) |
| positive side of the hinge | `hinge_side` |
| τ-program, `TauBot(α)` | tau bot, `Tau<Name>`, `RowSpecA` |
| transparency level `t`, caution `α` | `t` (`--ts`), `alpha` (`--alphas`) |
| behavioral and syntactic transparency maps | `--family behavioral`, `--family syntactic` |
| extreme equilibria and their components | `egt/nash/` |
| replicator dynamics | `egt/replicator/` |

## 3. The formalization

### 3.1 Check it

```bash
cd arith
lake build --try-cache      # downloads the prebuilt Foundation artifacts, then builds about 3,500 modules
```

Lean `v4.33.1` (`lean-toolchain`); Foundation and mathlib are pinned. The default targets are the library and two
checkers, so a successful build means all of the following.

* Every theorem compiles. There is no `sorry`.
* **Axioms.** `ArithS/Audit/*.lean` run `#print axioms` on the results of each layer. Only `propext`,
  `Classical.choice` and `Quot.sound` appear.
* **Every cell is what its name says.** `ArithS/Outcome/Check.lean` validates each `@[outcomeA]` and `@[floorA]`
  theorem against its own name, checks that every declaration named like a cell is tagged, and checks that every
  pair of the paper's programs is a cell or a floor.
* **The same for the τ-rows.** `ArithS/Tau/Check.lean`.

`python3 scripts/check_tiers.py` (in `arith/`) checks the import direction between the trusted definitions, the
Löb argument, the results and the audit.

Size, as quoted in the paper: `git ls-files arith | grep '\.lean$' | xargs cat | wc -l` gives about 159,000 lines,
of which `arith/ArithS/Necessitation/` is about 96,000.

### 3.2 Read it

Open [`arith/ArithS/Tour.lean`](arith/ArithS/Tour.lean) first. In one file it restates the ten trusted definitions
at `ℕ` (each kept equal to its definition by `rfl`), walks through `DupocBot` against `CupodBot` step by step, and
`#check`s the headline theorems. Then [`arith/ArithS/README.md`](arith/ArithS/README.md) is the reading guide to
the rest.

### 3.3 Statement to theorem

Paths are relative to `arith/ArithS/`.

| In the paper | Lean | File |
|---|---|---|
| Language and theory of `S` | `LAct`, `TAct` | `Theory/LangAct.lean`, `Theory/TheoryAct.lean` |
| Proof length | `proofLen` | `Length/DerivationLength.lean` |
| Bounded provability `□_k` | `LenBox`, `codeBound` | `Box/BewV.lean`, `Length/Proper.lean` |
| Program codes | `progCode` | `Agents/Code.lean` |
| Names of programs | `codeTerm`, `descriptions` | `Agents/CodeTerm.lean`, `Agents/Guard.lean` |
| Names of formulas | `boxQuote` | `Agents/Code.lean` |
| Templates, the guard, substitution | `template`, `guardCode`, `substCode` | `Agents/Code.lean`, `Agents/Guard.lean`, `Agents/Subst.lean` |
| The evaluator | `EvalGraph` | `Eval/Eval.lean` |
| The outcome template | `OutcomeSpecA` | `Outcome/Spec.lean` |
| Soundness | `TAct_sound_nat` | `Readings.lean` |
| Completeness over the two readings | `TAct_complete_of_readings` | `Loeb/Diag.lean` |
| Bounded Löb | `family_found`; its one hypothesis is the theorem `boundedInnerNec_sixteen`, giving `pblt` | `Assembly/Family.lean`, `Necessitation/Package.lean` |
| Transposition of proofs | `lenBoxNat_swap_iff` | `Theory/Symmetry.lean` |
| Bridge (a transposed program's sentences) | `lMap_swap_sentenceAt_plays_of_transposableP` | `Agents/CodeTranspose.lean` |
| Transposition of outcomes | `outcomeAtA_transpose_of_transposableP`, `opposite_of_plays_transpose_of_transposableP` | `Cells/Transposition.lean` |
| `DupocBot` against `CupodBot` is `(D, C)` at every `k` | `outcome_DupocBot_vs_CupodBot` | `Outcome/Matrix/DupocBot.lean`, proof in `Cells/RedCellEngine.lean` |
| `DupocBot` against `DefectBot`, `CooperateBot`, itself | `outcome_DupocBot_vs_DefectBot`, `…_vs_CooperateBot`, `…_vs_DupocBot` | `Outcome/Matrix/DupocBot.lean` |
| `DIMCID` defects against every program | `dimcid_vs_closed` | `Cells/DimcidFlips.lean` |
| Open Problem 6: `DupocBot` against `DIMCID` | `outcome_DIMCID_vs_DupocBot` | `Outcome/Matrix/DIMCID.lean` |
| Open Problem 5: `CupodBot` against `CIMCIC` | `dich_CIMCIC_vs_CupodBot` | `Cells/FloorDichotomy.lean` |
| Open Problem 9: the PrudentBot row | `outcome_PrudentBot_vs_*` | `Outcome/Matrix/PrudentBot.lean`, `Outcome/Floors.lean` |
| A floor: both sides of its hinge | `dich_<L>_vs_<R>`, for example `dich_DupocBot_vs_CupodTrollBot` | `Cells/FloorDichotomy.lean`; `Cells/DupocTrollBot.lean` and `Cells/Dimdid.lean` for those two programs |
| A found hinge would settle bounded consistency | `hinge_con_reduction` | `Cells/ConReduction.lean` |
| The τ-rows of partial transparency | one `@[tau_rowA]` row per template | `Tau/Rows/*.lean` |

Two statements have no single Lean counterpart. Unexploitability is proved on paper for every opponent; in Lean it
can be read off the matrix, where the rows of `DefectBot`, `DupocBot` and `CIMCIC` contain no `(C, D)`. `AntiBot`
is an illustration and is not in the library.

### 3.4 The outcome matrices

```bash
cd app && uv sync --extra dev
uv run python -m pd_runner.paper.matrix                                  # the library Σ
uv run python -m pd_runner.paper.matrix --library body8+trolls+provers   # the twelve programs
```

This prints the matrix as it appears in the paper, then one line per pair of programs with the Lean theorem that
proves it and its file. A decided pair is one theorem `outcome_<L>_vs_<R>` in `arith/ArithS/Outcome/Matrix/<L>.lean`.
A pair on a hinge has a dichotomy `dich_<L>_vs_<R>` that proves both sides, and the matrix shows the negative side.
The export is refreshed with `lake exe export_sprime_outcomes` in `arith/`.

### 3.5 The programs

Each program of the paper is a Lean definition of a few lines: `engine/PrisonersDilemma/Bots/<Name>.lean`
(`CIMCIC`, `DIMCID` and `PrudentBot` are in `Bots/LlmGenerations/`). The τ-programs are in
`engine/PrisonersDilemma/Tau/Bots/`.

## 4. The experiments

### 4.1 Read the numbers

```bash
cd app && uv sync --extra dev
uv run python -m pd_runner.paper.numbers       # every number of the experiments section and its appendices
uv run pytest tests/test_paper_numbers.py      # the same numbers, asserted
```

`numbers` reads [`app/paper_results/`](app/paper_results/) and prints each number under the title of the section
that quotes it. The folder holds one JSON file per game at full transparency (payoff matrix, every extreme
equilibrium in exact rationals, where each sampled population ends) and one per fine-grid sweep. The tests also
check that each payoff matrix is the one the Lean export gives.

### 4.2 Table or figure to source

| In the paper | Where it comes from |
|---|---|
| Outcome matrix of `Σ`; of the twelve programs | `latex/scripts/gen_outcome_matrix_body.py`, with argument `full` for the twelve; same content as `paper.matrix` |
| PrudentBot's row | `latex/scripts/gen_prudent_row.py` |
| The 21 extreme equilibria of `Σ`, their three components, the `1/9` bound | `paper.numbers`, first block; `paper_results/full_transparency/body8__engine_side.json` |
| Final population composition under replicator dynamics, the Wilson intervals, the range of `DupocBot`'s share | `paper.numbers`, second block |
| Equilibrium outcomes across the four libraries | `paper.numbers`, third block; `paper_results/full_transparency/*__engine_side.json` |
| Sensitivity to the hinge at full transparency (text and figure) | `paper.numbers`, fourth block; `paper_results/full_transparency/body8__hinge_side.json` |
| Equilibrium outcomes under behavioral transparency: the table, `t*`, `t**`, the three windows where populations cycle | `paper.numbers`, fifth block; `paper_results/partial_transparency/behavioral_engine_side.json` |
| The syntactic thresholds; the positive side under partial transparency | `paper.numbers`, last block; the three other files of `paper_results/partial_transparency/` |
| The two partial-transparency figures | `latex/scripts/gen_partial_transparency_figs.py`, which reads the same snapshot and writes `app/generated/egt_fine/figures/` |

All generators are run from `app/`, for example `uv run python ../latex/scripts/gen_partial_transparency_figs.py`.

### 4.3 Recompute from scratch

```bash
app/scripts/rerun_paper_experiments.sh       # about an hour on a four-core laptop
git diff --stat app/paper_results            # expected: no change
```

The script runs the sweeps from the Lean export: the four libraries at full transparency, then `Σ` on the grid
`t = 0, 0.01, …, 1` for both signal families and both sides of the hinge. It then rebuilds `app/paper_results/`
with `python -m pd_runner.paper.snapshot`. Everything is seeded: a run from scratch into an empty folder reproduced the tracked snapshot byte for byte. The sweep
output itself (several thousand files under `app/generated/egt/runs` and `app/generated/egt_fine/`) is not tracked.
Pass a folder as first argument to write the sweep output elsewhere, and a second one for the snapshot.

### 4.4 Method to code

Paths are relative to `app/src/pd_runner/`.

| Method | Code |
|---|---|
| From outcomes to the payoff matrix of the meta-game | `tau/matrix.py` (the cells, the side of the hinge), `egt/ingest.py` (payoffs `T = 3, R = 2, P = 0, S = −1`) |
| Enumerating extreme equilibria, exact arithmetic | `egt/nash/` |
| Components of equilibria | `egt/nash/classification.py`, `group_components` |
| Replicator dynamics, the convergence criterion, the horizons | `egt/replicator/dynamics.py` (its docstring states the criterion) |
| Sampling populations, assigning end points to components, Wilson intervals | `egt/replicator/basins.py` |
| The threshold rule of a τ-program | `tau/play.py` |
| Behavioral and syntactic transparency maps, the transparency level `t` | `tau/channels.py`, `tau/signal.py`, `tau/syntax.py` |
| A sweep over `(t, α)` | `egt/pipeline.py` |

## 5. In the repository, not in the paper

* `engine/`'s rule-based proof system `S` and its own outcome theorems (`engine/PrisonersDilemma/Theorems/`), and the
  second export `outcome_theorems.json`. `app/generated/source_diff.md` lists where the two systems disagree.
* Programs beyond the paper's: `MirrorBot`, `JustBot`, `GuardianBot`, `WaryBot`, `LegibleBot`, `OptimBot`.
* Other evolutionary stages (`egt/moran/`, `egt/invasion/`, `egt/faces/`, `egt/static_analysis/`) and their generators
  `latex/scripts/gen_moran_body.py`, `gen_replicator_body.py`, `gen_zoo_ladder.py`, `gen_tau_body.py`,
  `gen_tau_grid_figs.py`, `gen_tau_ladder.py`. The tables and figures they wrote under `latex/figures and tables/`
  predate the current experiments section.
* `app/generated/egt/sweep_logs/`: the scripts of earlier, broader sweeps, kept as a record.
* `pipeline/` (bots and proofs written by a language-model agent) and `llm-distillation/`.
* `docs/`: the design notes. `docs/notes/EGT_FINDINGS_SPRIME.md` records numbers from before the equilibrium and
  replicator stages were corrected; `app/paper_results/` supersedes it.
