# `paper_results/` — the results the paper quotes

Written by `python -m pd_runner.paper.snapshot` from the sweep output; read by `python -m pd_runner.paper.numbers`,
by `tests/test_paper_numbers.py` and by the figure generator. Do not edit by hand. `../../REPRODUCING.md` says which
number of the paper comes from which file. In file names, `engine_side` is the negative side of the hinge and
`hinge_side` the positive side; `body8` is the paper's library `Σ`.

## `full_transparency/<library>__<side>.json`

One game: a library at full transparency, on one side of the hinge.

| Key | Content |
|---|---|
| `programs`, `payoff_matrix` | The row player's payoffs, `T = 3, R = 2, P = 0, S = −1`, rows and columns in the order of `programs` |
| `hinge_cells` | The ordered pairs whose outcome depends on a hinge |
| `equilibria` | Every extreme Nash equilibrium: each player's mix as exact fractions, `cooperation` = Pr[(C,C)], both payoffs, and the `component` it belongs to |
| `replicator_stage` | What the replicator stage recorded over its 1,001 interior starts (the centre of the simplex, then 1,000 uniform draws) |
| `uniform_starts` | The same integration restricted to the 1,000 uniform draws, which is what the paper reports: counts by component and by the set of programs present at the end, and the range of each program's final share |

## `partial_transparency/<family>_<side>.json`

One line per distinct game of the sweep `t = 0, 0.01, …, 1` over the caution levels. Several grid points can share
a game, because the outcome matrix changes only at finitely many `(t, α)`.

| Key | Content |
|---|---|
| `grid_points` | The `[t, α]` pairs at which this game is played |
| `components` | The equilibrium components: number of extreme equilibria and Pr[(C,C)] |
| `replicator` | `n` sampled populations and the component each one `reached`; `n_unconverged` did not settle |
| `cycle` | Only where more than half do not settle: the long-run average of Pr[(C,C)] and the programs that stay present |
