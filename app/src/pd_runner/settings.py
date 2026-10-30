"""Matrix-level settings of the core app: which proof system's export is the ground truth
(`CELL_SOURCE`) and how a genuine `S'` floor is carried (`FLOOR_POLICY`).

The LLM pipeline's own knobs (models, budgets, retry policy) live in `pd_pipeline.settings`.
"""

from __future__ import annotations

import os
from typing import Literal

# ---------------------------------------------------------------------------
# Cell source — which proof system's matrix the app treats as ground truth
# ---------------------------------------------------------------------------
#
# Since 2026-09-30 (`docs/notes/SPRIME_SOURCE_OF_TRUTH.md` §0) the arithmetized
# system PA-`S'` (`arith/`, export `app/generated/sprime_outcome_theorems.json`) is the
# SOURCE OF TRUTH for the matrix, the tau layer and the EGT experiments; the engine's
# stipulated `S` (`app/generated/outcome_theorems.json`) stays loadable as the
# COMPARISON. Every loader takes `source=` / `floor_policy=` and defaults to these.
#
# `FloorPolicy` decides what a GENUINE FLOOR is in `S'`: a cell whose value hinges on
# bounded consistency of `TAct` at `k` (a hypothesis-free `dich_<L>_vs_<R>` dichotomy,
# never a theorem for one value). `engine_side` carries it as a labelled cell holding
# the `¬A_k` branch — the engine's stipulation, now visible (provenance
# `floor_dichotomy`); `restrict_zoo` treats floors as holes, so a zoo containing one
# fails totality loudly; `hinge_side` (2026-10-09, the ROBUSTNESS CHECK) carries the
# OTHER branch — every box hypothesis of the dichotomy TRUE (`eval/sprime_floors.
# HINGE_SIDE_PAIRS`, derived from the `dich_` statements), the mirror image of the
# engine's stipulation — so an experiment run under both policies brackets what the
# open consistency question can change. No kernel tau bit exists for that branch:
# under `hinge_side` the `S'` floor bits are left unstated (base-cell fallback).

CellSource = Literal["sprime", "engine"]
FloorPolicy = Literal["engine_side", "restrict_zoo", "hinge_side"]

CELL_SOURCES: tuple[str, ...] = ("sprime", "engine")
FLOOR_POLICIES: tuple[str, ...] = ("engine_side", "restrict_zoo", "hinge_side")


def _env_choice(var: str, default: str, allowed: tuple[str, ...]) -> str:
    value = os.getenv(var, default).strip() or default
    if value not in allowed:
        raise ValueError(
            f"{var}={value!r} is not one of {list(allowed)} — unset it for the default "
            f"({default!r}) or pick one of the allowed values"
        )
    return value


CELL_SOURCE: CellSource = _env_choice("PD_CELL_SOURCE", "sprime", CELL_SOURCES)  # type: ignore[assignment]
FLOOR_POLICY: FloorPolicy = _env_choice("PD_FLOOR_POLICY", "engine_side", FLOOR_POLICIES)  # type: ignore[assignment]


def resolve_source(source: str | None) -> CellSource:
    """`source` validated, or the configured default when None."""
    if source is None:
        return CELL_SOURCE
    if source not in CELL_SOURCES:
        raise ValueError(f"unknown cell source {source!r}; choose one of {list(CELL_SOURCES)}")
    return source  # type: ignore[return-value]


def resolve_floor_policy(policy: str | None) -> FloorPolicy:
    """`policy` validated, or the configured default when None."""
    if policy is None:
        return FLOOR_POLICY
    if policy not in FLOOR_POLICIES:
        raise ValueError(
            f"unknown floor policy {policy!r}; choose one of {list(FLOOR_POLICIES)}")
    return policy  # type: ignore[return-value]
