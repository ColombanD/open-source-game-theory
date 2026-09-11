---
name: project_egt_analysis_toolchain
description: "2026-09-02: the 4-module EGT analysis toolchain (integrity/analysis/findings/nash_structure) over the frozen sweeps; findings F1-F7 recorded in Research/Notes/EGT_FINDINGS.md; key traps (α=0 degenerate, identity≠cooperation, vertex counts misleading)"
metadata: 
  node_type: memory
  type: project
  originSessionId: 05c9d391-b3aa-498a-a32b-47991f52fc9e
  modified: 2026-09-02T10:01:14.673Z
---

**The results-section analysis lives in `Research/Notes/EGT_FINDINGS.md`** (the
authoritative record — findings F1–F7, conventions, figure inventory, remaining
work). Toolchain in `app/src/pd_runner/egt/`, each `uv run python -m pd_runner.egt.<m>`:
`integrity` (gate: 0 hard failures, anchors OK), `analysis` (tidy.csv + phase/diff
maps), `findings` (claim-driven, full-(M,β) drill-down), `nash_structure`
(NE components classified by cooperation rate; `fig_collapse_*.png`).

**Headline new result (F3):** the static collapse (fully-cooperative NE component
leaves the landscape) and the Moran collapse t* COINCIDE at every α on
body/behavioral; realized stationary coop rate tracks the static ceiling; the one
asymmetry is α=0.3 (cooperative NE survives all t, selection abandons it below t*).
Needs a finer-t robustness pass before claiming exact coincidence.

**Traps encoded there:** α=0 is degenerate (unconditional C — exclude from anchor
and claims); Löbian population SHARE ≠ cooperation rate (twins survive as
defectors at low t — use Σ share·[self-cell=(C,C)]); extreme-NE vertex counts are
polytope geometry (21→8→121 non-monotone — use component counts + classification);
read `runs/*/summary.json`, never top-level sweep_summary*.json (clobbered across
zoos); "uniquely stochastically stable" = strong-selection claim (robustness ~6/9).

Zoo key renamed 2026-09-02 by Colomban: `body+natives` → `body+twins+natives`
(everywhere incl. on-disk artifacts). `critch8` sweep still not run.

Related: [[project_paper_freeze_2026_09_01]], [[project_egt_next_stages]],
[[project_jmlr_paper_decisions]].
