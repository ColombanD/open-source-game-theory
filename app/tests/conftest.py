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
"""

from __future__ import annotations

from pathlib import Path

from pd_runner.eval import outcome_matrix as _om

SPRIME_SAMPLE_EXPORT = Path(__file__).resolve().parent / "fixtures" / "sprime_outcome_theorems.sample.json"
SPRIME_REAL_EXPORT = Path(__file__).resolve().parents[1] / "generated" / "sprime_outcome_theorems.json"

if not _om._EXPORT_FILES["sprime"].exists():
    _om._EXPORT_FILES["sprime"] = SPRIME_SAMPLE_EXPORT
