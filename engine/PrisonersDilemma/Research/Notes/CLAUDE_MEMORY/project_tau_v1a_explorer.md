---
name: tau-v1a-explorer
description: "TauBots v1a Python explorer SHIPPED (app/src/pd_runner/tau/) — conventions fixed, 11-bot zoo, dial t∈[0,1]=normalized-MI transparency, report + /tau/report endpoint; key findings inside"
metadata: 
  node_type: memory
  type: project
  originSessionId: 66b62b39-d45b-4ed9-a5fc-396d101a2aeb
  modified: 2026-08-03T15:03:41.346Z
---

TauBots v1a (Phase 5 Python explorer) shipped 2026-08-03 in `app/src/pd_runner/tau/`
(matrix / signal / play / sweep / report + `tests/test_tau.py`). Design note:
`TAUBOTS.md (condensed 2026-08-26)`. Conventions Colomban fixed:

- **Zoo**: default `CERTIFIED_SUB_ZOO` = 11 bots — LegibleBot+JustBot REMOVED (behavioral
  twins), CupodBot ADMITTED via 2 stipulated cells (`CUPOD_STIPULATIONS`: Cupod-vs-Dupoc
  (C,D), Prudent-vs-Cupod (D,C)) → twin-free, transparency ceiling exactly 1.0. All 16
  stipulation assignments give the same twin-freeness (invariance = trustworthiness test).
  `PROVEN_ONLY_SUB_ZOO` (10 bots, kernel-only, ceiling 0.94) and `FULL_CERTIFIED_SUB_ZOO`
  (12 bots, ceiling 0.843) are the fallbacks. Open cells → restrict zoo (not renormalize);
  budgets → collapsed asymptotic outcome; tie-break `≥ α`; MirrorBot excluded (self-play
  proven `none`).
- **Dial (2026-08-03, per Colomban)**: `t ∈ [0,1]` with **t=1 = full transparency, t=0 =
  opaque**, and the dial IS the normalized-MI transparency (bisection-inverted, cached in
  `_TEMPERATURE_CACHE`). Raw softmax temperature is internal-only (`softmax_signal`,
  `signal_family_at_temperature`, `transparency`). t=0 maps to FINITE temp 1e4, not exact
  uniform (keeps knife-edge observable).

Key findings (tests pin all of these):
- Anchor theorem holds (t=1 tournament == base matrix, all α).
- Twins {CooperateBot,CupodTrollBot,LegibleBot}, {DupocBot,JustBot} — CupodBot's column
  splits CupodTrollBot on PROVEN data; Coop/Legible pair is behaviorally unseparable
  (residual = syntactic info only Löbian provers see → split-theorem material).
- Löbian fragility: at α=0.62 DupocBot/PrudentBot need the MOST transparency (~40%) before
  deviating; ranking is α-SENSITIVE (nearly inverts at 0.45) — always name α.
- Blur converts (D,D)→(C,C): "cooperation rises when opaque" = loss of conditioning, not
  cooperation (composition chart); exploitation PEAKS at ~25% transparency.
- Knife-edge trap: α exactly on an achievable coop fraction → float noise decides plays;
  sweeps must step BETWEEN `alpha_breakpoints`.

Report: `uv run python -m pd_runner.tau.report --open` (dependency-free inline SVG, 6
panels, α slider + σ-family radio) or the **"Run tau analysis" button** in the app UI →
`GET /tau/report?alphas=…`.

**σ channel families (2026-08-03, `tau/channels.py` + `tau/syntax.py`)** — three
families all calibrated onto the SAME MI dial (cross-family gaps at matched t = pure
confusion-structure effects): behavioral softmax (= exact BSC Bayes posterior — cite
this), ε-uniform null control (identity-based, no twin ceiling), syntactic/codebase
(L1 over Prog constructor-profile features regex-extracted from Bots/*.lean).
**Confusion-structure INVERSION**: Dupoc/Cupod syntactic near-twins (d=2) but
behavioral opposites; Coop/Defect syntactically adjacent constants; Coop/CupodTroll
behavioral near-twins but syntactic opposites. **DBot/TitForTatBot are syntactic
twins** (ceiling ≈0.947 — full code transparency cannot anchor). Colomban wants the
**AST ideas kept for later**: tree-edit distance via a Lean #eval S-expression
exporter, node-masking generative σ, sampling/reputation σ, theorem-library σ,
query-signature σ, mixtures — full roadmap appended to
TAUBOTS.md (condensed 2026-08-26) ("σ family roadmap").

Next steps per note: v1b thin Lean core (Signal/coopMass/tauPlay + anchor theorem), v2
compilation to Prog. Related: [[outcome-matrix-sheet-sync]].
