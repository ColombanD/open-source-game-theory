# EGT findings on the frozen paper sweeps — the results-section companion

*2026-09-02. The record of the first full analysis pass over the frozen paper
sweeps: what was run, the toolchain that reads it, every finding with its
evidence pointer, and the caveats that must ride along into §5. Written to be
opened next to the LaTeX when drafting Experiments/Results.*

---

## 1. What was run (provenance)

Code state: commit `df56c99` (the 2026-09-01 freeze: paper zoos, Def-4 kernel
substrate, MinConfidenceBot, σ-family sweeps) plus the 09-02 zoo-key rename
`body+natives` → `body+twins+natives`. Every matrix cell traces to a kernel
theorem (`is_fully_proven` on all 94 runs); the tau lift plays from the kernel
RowSpec bits (Def-4 substrate, certification 289/289/0).

| zoo | family | grid | distinct matrices |
|---|---|---|---|
| `body` (10) | behavioral | 6×6 | 16 |
| `body` | syntactic | 6×6 | 16 |
| `body+twins` (12) | behavioral | 6×6 | 17 |
| `body+twins` | syntactic | 6×6 | 15 |
| `body+twins+natives` (14) | behavioral | 6×6 | 18 |
| `body+twins+natives` | epsilon | 6×6 | 12 |

Grid: t ∈ {0, 0.2, 0.4, 0.6, 0.8, 1.0} × α ∈ {0, 0.3, 0.45, 0.62, 0.8, 1.0};
PD payoffs (D,C)=b, (C,C)=b−c, (D,D)=0, (C,D)=−c with the ingest defaults.
Moran per matrix: M ∈ {10, 50, 100} × β ∈ {0.01, 0.1, 1}; "the headline" always
means M=100, β=1 (strongest selection). Tau-layer reports were generated per
zoo (`generated/tau_report_{body,twins,natives}.html`). NOT yet run: `critch8`
(the appendix reproduction zoo).

Integrity (see §3): **0 hard failures**; sole soft finding = Nash cross-check
absent in 94/94 runs (`lrsnash` not installed — one sentence for Limitations).
Anchors verified: at t=1 (α>0) all families of a zoo share one fingerprint,
equal to the base matrix's.

## 2. Conventions the text must respect

* **α = 0 is degenerate**: `≥ α` at α = 0 makes every tau player an
  unconditional cooperator, so the t=1, α=0 matrix is the ALL-C matrix, not
  the base matrix. Excluded from every claim; keep the row in tables only as
  the labelled corner. α = 1 is the unanimity knife edge (dies immediately
  below t=1).
* **"Uniquely stochastically stable" is a strong-selection claim.** Robustness
  across the 9 (M, β) combos is typically 6/9 (weak selection clears no
  stochastic-stability cut, or admits Dup+TFT ties) — quote the headline with
  the (M=100, β=1) qualifier, or cite the robustness grid.
* **Identity ≠ cooperation.** At low t the Löbian types survive as DEFECTORS;
  a population-share curve is not a cooperation curve. The comparable realized
  quantity is the stationary cooperation rate Σᵢ share(i)·[i's self-cell is
  (C,C)] (monoculture approximation, valid under small mutation). This
  conflation was actually committed and caught during this analysis — the
  share curve visibly exceeded the static NE ceiling.
* **Report per phase region, not per grid point.** Cells sharing a matrix
  fingerprint are provably identical analyses (`grid_points` records the
  dedup); equal neighbours in the maps ARE the regions.
* **Extreme-NE vertex counts are geometry, not strategy content** (21 → 8 →
  121 non-monotone). The meaningful statistics are the COMPONENT count and the
  component-level cooperation classification; vertex counts go to the appendix
  with this caveat.
* **The behavioral run of `body+twins+natives` is the twinning observation,
  never the ablation** — under a feature-based σ the natives are Dupoc twins
  and the aggregator is confounded with twin-mass splitting. The ablation is
  the EPSILON run only.
* **Basins group by support**; mixed {Dup, CIM} supports are neutral drift
  inside a twin pair, not a new attractor.

## 3. The toolchain (all in `app/src/pd_runner/egt/`, run with `uv run python -m …`)

Read `runs/*/summary.json`, never the top-level `sweep_summary*.json` (one per
family, clobbered across zoos).

| module | job | outputs (under `generated/egt/analysis/`) |
|---|---|---|
| `pd_runner.egt.integrity` | gate: failures, honesty markers, anchor checks (α>0!) | console, exit code |
| `pd_runner.egt.analysis` | flatten to one row per (zoo, family, t, α) | `tidy.csv`, `phase_maps.md`, `family_diffs.md` |
| `pd_runner.egt.findings` | claim-driven sections incl. full-(M,β) drill-down | `findings.md` |
| `pd_runner.egt.nash_structure` | NE components classified by cooperation; static-vs-dynamic collapse | `nash_structure.{csv,md}`, `fig_collapse_*.png` |

Deeper drill-downs used: `moran/stationary.json` (9 (M,β) points with full
stationary shares + SS sets), `nash/latest/equilibria.jsonl`
(`cooperation_rate_float` + `component_id` per extreme NE),
`ess/payoff_matrix_numeric.csv` (diagonal > 0 ⇔ self-play (C,C)).

## 4. Findings (evidence pointer → paper section)

**F1 — Baseline (→ §5.1).** Body zoo at t=1: 0 pure ESS, 21 extreme NE in 3
components, 6 stable faces / 1013 supports, invasion SCCs 3; replicator
dominant support {Coop, Dup, TFT} with a 95% basin; DupocBot's stationary
share rises 11% → 89% with selection (the (M, β) table in `findings.md` §1).
No pure ESS on any zoo/family/point — statics can't select, which is the
argument for the dynamic stages (→ the "two analyses" design of §5.1.3).

**F2 — Critical transparency (→ §5.2, the headline figure).** Body/behavioral:
Dup uniquely stochastically stable on all of t ∈ [0.4, 1.0] × α ∈ [0.3, 0.8];
the collapse sits between 0.4 and 0.2, latest for moderate caution (α = 0.45,
0.62 survive at t = 0.2), and the t=0 outcome is defector ties. α = 1 dies
immediately below t=1. (`findings.md` §2; `phase_maps.md`.)

**F3 — The static and dynamic collapses COINCIDE (→ §5.2, the strongest new
result).** Classifying NE components by their best cooperation rate: the t at
which the fully-cooperative component leaves the Nash landscape equals the
Moran t* at every α where both are defined (α: 0.45→0.0, 0.62→0.2, 0.8→0.4,
1.0→0.8 on body/behavioral). Two independent methodologies — equilibrium
structure and stochastic selection — degrade at the same transparency
frontier. Moreover the realized stationary cooperation rate TRACKS the static
ceiling almost exactly ("the population saturates what rationality permits"),
with ONE asymmetric exception: at α = 0.3 the fully-cooperative equilibrium
survives at every t (t_static = none) while realized cooperation degrades
smoothly to ~0.64 — below t* cooperation remains rationally available but is
no longer selected. Also: stable faces → 0 below the collapse (no
asymptotically stable mixture exists at all). (`nash_structure.md`,
`fig_collapse_body_behavioral.png`.)

**F4 — Confusion structure matters at matched information (→ §5.2 family
contrast).** Behavioral vs syntactic disagree on a headline at 7/36 points on
`body` and 7/36 on `body+twins`; behavioral vs epsilon at 14/36 on the natives
zoo. Sharpest citable instance: at α = 0.8 on the syntactic channel,
cooperation dies at t* = 0.6 (→ Def) vs 0.4 behaviorally — HIGH CAUTION UNDER
SOURCE-BLUR FAILS EARLIER THAN UNDER BEHAVIOR-BLUR. (`family_diffs.md`,
`findings.md` §2.)

**F5 — The aggregator ablation orders blur tolerance: pessimist < expectation
< optimist (→ § aggregator ablation).** On `body+twins+natives`/epsilon at
M=100/β=1: for t ≥ 0.6 the Löbian class {Dup, CIM, Max, Min} holds ~95% in a
PERFECTLY NEUTRAL split (≈24% each; sum column = the two lifts) — the
aggregator is irrelevant until blur reaches the thresholds. Crossing them:
MinConfidence exits first (share → 0 by t=0.4 at α=0.3); in a mid-blur band
MaxConfidence alone takes 89–90% (t=0.2 at α∈{0.45, 0.62}; already t=0.6 at
α=0.8); at α=1 everything flattens (~31% class total, no SS). (`findings.md`
§4.)

**F6 — Zoo sensitivity: the CLASS is robust, the labels split (→ §5.1.3 /
appendix zoo influence).** body → body+twins changes the SS set at 24/30
points, but almost every change is `Dup` → `CIM+Dup` (the twin JOINS the
niche); 29/30 twins-zoo points show mixed {Dup, CIM} dominant supports
(neutral drift inside the pair). EGT's selection is stable at the level of the
behavioral equivalence class even when the roster changes — the corrective to
the coop-rate statistic's zoo-sensitivity, exactly as §5.1.3 argues.
(`findings.md` §5.)

**F7 — The Max band reproduces, narrower (→ appendix, twinning observation).**
On the 14-bot behavioral run MaxConfidence is uniquely stochastically stable
at {(0.2, 0.45), (0.2, 0.62), (0.4, 0.62), (0.4, 0.8)} — the archived
pre-freeze band (t ∈ [0.2, 0.6], α ≥ 0.45 on the 10-member zoo) survives
qualitatively. Frame as ambiguity-aversion-under-twinning, NOT ablation.
Bonus: at low α the SS set becomes {Def, Pru, TFT} — PrudentBot surfaces
precisely because it is DefectBot's behavioral twin. (`findings.md` §6.)

## 5. Why Moran carries the headline (the ladder — for the §5 narrative)

Nash: cooperation is one of 21 equilibria — selection problem, unanswered.
ESS: the classic static selector returns nothing (0 pure ESS) — statics
genuinely cannot decide. Replicator: 95% of starts reach the cooperative
cluster — strong but conditional on starts, infinite population, no noise,
and neutral continua (twins) leave "which point" open. Moran: finite
population + mutation + a selection dial; the stationary distribution is
start-independent, handles neutrality honestly (split shares, not fake
attractors), and its stochastic-stability limit is THE equilibrium-selection
answer. The one-breath summary: transparency converts Löbian cooperation from
one equilibrium among many into the selected outcome, robustly down to
t ≈ 0.4, with a quantified collapse to defection between 0.4 and 0.2 — and the
rational landscape itself (F3) collapses at the same frontier.

## 6. Figure inventory (current state: analysis-grade PNG; paper wants pgfplots)

* `fig_collapse_body_behavioral.png` — THE candidate §5.2 figure: 5 α-panels ×
  2 rows (static ceiling vs realized stationary coop rate; component/stable-
  face counts), Moran t* marked. Same figure exists per sweep (6 files).
* `phase_maps.md` — the (t, α) grids for the per-region reporting (candidate:
  render as a colored tile grid).
* Okabe-Ito palette as everywhere in the repo (blue #0072b2 = cooperation);
  its known contrast WARN ⇒ every figure ships a legend/direct labels AND the
  CSV table view (`tidy.csv`, `nash_structure.csv`).

## 7. Remaining before the results section is closeable

1. `critch8` sweep + its paragraph (appendix reproduction; transcription-diff
   framing already in CLAUDE.md/`CRITCH8_TRANSCRIPTION_DIFFS`).
2. Tau-layer descriptive figures (coop-mass degradation curves, matched-MI
   channel comparison) extracted from the per-zoo tau reports into
   paper-grade form; align α lists (they already match).
3. pgfplots/matplotlib-final versions of F2/F3/F5 figures from `tidy.csv` +
   `nash_structure.csv` (everything regenerates from CSV — no hand-drawn data).
4. Optional: `lrsnash` install + re-run for the cross-check box; otherwise the
   Limitations sentence stands.
5. The F3 coincidence deserves a robustness look at finer t resolution around
   the collapse (t ∈ {0.25 … 0.4} at α = 0.62/0.8) before claiming exact
   coincidence rather than grid-resolution coincidence.
