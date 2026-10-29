"""Test-suite wiring, mirroring `app/tests/conftest.py`: when the real PA-S' exports
(`app/generated/sprime_outcome_theorems.json`, `sprime_tau_rows.json`, written by
`lake exe export_sprime_outcomes`) are absent in a checkout, point the `sprime` loaders at the
committed samples under `app/tests/fixtures/`, so every default-source caller works.
"""

from __future__ import annotations

from pathlib import Path

from pd_runner.eval import outcome_matrix as _om
from pd_runner.tau import def4_theorems as _d4

_APP = Path(__file__).resolve().parents[2] / "app"
_FIXTURES = _APP / "tests" / "fixtures"

if not _om._EXPORT_FILES["sprime"].exists():
    _om._EXPORT_FILES["sprime"] = _FIXTURES / "sprime_outcome_theorems.sample.json"
if not _d4._TAU_EXPORT_FILES["sprime"].exists():
    _d4._TAU_EXPORT_FILES["sprime"] = _FIXTURES / "sprime_tau_rows.sample.json"
