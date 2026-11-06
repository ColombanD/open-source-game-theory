"""Test-suite wiring for the cell source (`SPRIME_SOURCE_OF_TRUTH.md` §1.3).

The default `CellSource` is PA-`S'`, whose export (`app/generated/sprime_outcome_
theorems.json`) is written by `lake exe export_sprime_outcomes`. Until that file exists
in a checkout, every default-source caller (the tau fixtures, the EGT smoke tests) would
fail with "the S' export does not exist". So, when the REAL export is absent, this
conftest points the `sprime` loader at the committed ledger-derived sample
(`tests/fixtures/sprime_outcome_theorems.sample.json`, built by
`tests/fixtures/make_sprime_fixture.py`) — the same document `PD_SPRIME_EXPORT` would
select. When the real export IS present it is used untouched, and
`tests/test_cell_source.py` runs its checks against BOTH documents.

`SPRIME_REAL_EXPORT` / `SPRIME_SAMPLE_EXPORT` are exported for the tests that
parametrize over the two.

The same pattern for the `S'` TAU ROWS (Phase 4): `app/generated/sprime_tau_rows.json`
(written by the same exporter) is pointed at the committed cell-derived sample
`tests/fixtures/sprime_tau_rows.sample.json` (`make_sprime_tau_fixture.py`) only while
the real file is absent; `tests/test_tau_rows_sprime.py` runs against both when both
exist, and `SPRIME_TAU_PARTIAL_EXPORT` is the two-row rollout sample.
"""

from __future__ import annotations

from pathlib import Path

from pd_runner.eval import outcome_matrix as _om
from pd_runner.tau import def4_theorems as _d4

_FIXTURES = Path(__file__).resolve().parent / "fixtures"
_GENERATED = Path(__file__).resolve().parents[1] / "generated"

SPRIME_SAMPLE_EXPORT = _FIXTURES / "sprime_outcome_theorems.sample.json"
SPRIME_REAL_EXPORT = _GENERATED / "sprime_outcome_theorems.json"

SPRIME_TAU_SAMPLE_EXPORT = _FIXTURES / "sprime_tau_rows.sample.json"
SPRIME_TAU_PARTIAL_EXPORT = _FIXTURES / "sprime_tau_rows.partial.sample.json"
SPRIME_TAU_REAL_EXPORT = _GENERATED / "sprime_tau_rows.json"

if not _om._EXPORT_FILES["sprime"].exists():
    _om._EXPORT_FILES["sprime"] = SPRIME_SAMPLE_EXPORT
if not _d4._TAU_EXPORT_FILES["sprime"].exists():
    _d4._TAU_EXPORT_FILES["sprime"] = SPRIME_TAU_SAMPLE_EXPORT
