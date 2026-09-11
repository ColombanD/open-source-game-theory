---
name: project_paper_freeze_2026_09_01
description: "2026-09-01 freeze (commit df56c99, colomban-taubots): MinConfidenceBot (MIN native, zero new Löb), ConfidenceBot→MaxConfidenceBot rename, the 3 paper zoos (body/body+twins/body+twins+natives), Def-4 kernel substrate, σ-family EGT sweeps; cert 289/289/0"
metadata: 
  node_type: memory
  type: project
  originSessionId: 05c9d391-b3aa-498a-a32b-47991f52fc9e
  modified: 2026-09-02T09:43:05.720Z
---

**The paper experimental setup froze 2026-09-01** (one commit, `df56c99` on
`colomban-taubots`). Everything below is the CURRENT state; notes dated earlier may
use retired names/zoos.

**2026-09-02: zoo key `body+natives` RENAMED to `body+twins+natives`** (more accurate —
it is body+twins plus the two natives). Renamed everywhere: `tau/matrix.py` registry,
`egt/findings.py` filters, tests, CLAUDE.md, TAUBOTS.md, AND the on-disk sweep
artifacts (30 run dirs + summaries under `app/generated/egt/` migrated in place;
`analysis/` outputs regenerated). Old key appears only in the pre-freeze archive tarball.

- **MinConfidenceBot** — second NATIVE tau player, C/D-dual of MaxConfidenceBot
  (**renamed from ConfidenceBot** the same day; protected rename — `minconfidence`
  is a substring hazard, and the app's Tier-A1 `expected_confidence` field is
  UNRELATED, never rename it). Aggregator family {sum, max, min} over Dupoc's one
  test. KEY FACT: the port cost ZERO new Löb work — `sysGo`/`instGo` never read the
  template name for Dupoc's spec, so all entangled pairs among the three Dupoc-spec
  self-probers ({.dupoc, .maxconfidence, .minconfidence}) compile to the ONE system
  `cfdSys`; every bridge is `rfl`. 18 templates, census 18/18.
- **Paper zoos** (`tau/matrix.py`, explicit literal tuples): `body` (10 =
  old default + DIMCID, twin-free, fully proven — DEFAULT_ZOO), `body+twins`
  (12, +CIMCIC+PrudentBot; behavioral ceiling < 1 IS the measurement — pairs are
  AST-distant 3.57/8.82), `body+twins+natives` (14; run on the EPSILON family — Dupoc twin
  class there is {Dupoc, CIMCIC, Max, Min}). Retired: default, default+confidence,
  enlarged, full-certified, proven-only. `FULL_CERTIFIED_SUB_ZOO` = the true 15-bot
  max. Twin rule is ROW-based (own actions only — columns don't count).
- **Def-4 substrate**: `TauMatrix.test_bit` plays from kernel RowSpec bits
  (`kernel_row_bits` + `TEMPLATE_OF_BOT`), verified vs base cells at load (stale
  export RAISES), `is_kernel_backed` = provenance, `apply_contradictions` drops the
  rows (replay zoos play their wrong cells). Certification 289/289/0.
- **σ-family EGT sweeps**: `sweep(..., family=)` / `--family` / API field / UI
  dropdown; behavioral keeps legacy artifact naming byte-for-byte; other families
  get name-tagged run dirs + `sweep_summary_<family>.json`. At t=1 all families
  share the fingerprint (anchor, pinned by test).
- Pre-freeze EGT artifacts archived at
  `app/generated/egt/archive/egt_pre-paper-freeze_2026-09-01.tar.gz` (backs
  TAUBOTS.md §4's pre-freeze observations); `generated/tau_report.html` untracked.
- Paper sweep program: body (behavioral) for §5.1/§5.2; body+twins behavioral +
  syntactic (confusion structure); body+twins+natives epsilon (aggregator ablation);
  critch8 (appendix). Run sweeps SEQUENTIALLY (memory discipline).

Related: [[project_confidencebot_native_player]] (partly superseded),
[[project_tau_v1a_explorer]], [[project_egt_integration]], [[project_jmlr_paper_decisions]].
