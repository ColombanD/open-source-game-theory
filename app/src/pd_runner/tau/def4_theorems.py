"""Fetch the Def-4 outcome theorems from the Lean library.

The base outcome matrix is unconditional (`outcome_A_vs_B = some (.C, .D)`), so
`eval/outcome_matrix.py` can read a cell as a single action pair. Def-4 cells
are **α-regime-quantified** — the same matchup is `(C, C)` below the boundary
and `(D, D)` above it — so they need their own scanner:

    theorem outcome_TauDupoc_vs_TauCooperate :
        ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL, θ ≤ wC + wTs + wTp + wL →
          ∃ N, outcome N (TauDupoc k θ wC wD wTs wTp wL) TauCooperate
            = some (.C, .C) := by

What this module extracts per theorem: the ordered tau-bot pair, the α-REGIME
CONDITION (`θ ≤ <mass expr>` or `<mass expr> < θ`), the mass expression itself,
and the resulting action pair. `certified_cell` then answers the question the
comparison actually asks — "what do the Lean theorems say this matchup is at
this (θ, w⃗)?" — by evaluating the regime conditions against concrete weights.

This makes `tau/compare.py` read the KERNEL for the Def-4 side rather than
trusting the Python re-derivation. Purely static: no Lean invocation, the
kernel already checked every statement.

**Scope.** Only the bots in `engine/PrisonersDilemma/Theorems/Tau/Matrix.lean`
have theorems. A tau bot modelled in Python but not yet built in Lean (e.g. the
hypothetical `TauEBot` used to demonstrate divergence) has NO certified cell,
and `certified_cell` returns `None` for it — that absence is the honest signal
that a result is predicted rather than proven, and the comparison reports it as
such instead of silently falling back to arithmetic.
"""

from __future__ import annotations

import re
from dataclasses import dataclass
from pathlib import Path


def _workspace_root() -> Path:
    return Path(__file__).resolve().parents[4]


TAU_THEOREMS_FILE = (
    _workspace_root()
    / "engine"
    / "PrisonersDilemma"
    / "Theorems"
    / "Tau"
    / "Matrix.lean"
)

# `theorem outcome_<A>_vs_<B><suffix> : <statement> :=` (with or without `by`).
# Tau bot names are alphanumeric; the optional suffix (`_highθ`) marks the
# complementary α-regime of an already-present pair.
#
# The statement body must NOT be allowed to run past its own `:=` into the next
# theorem — the term-mode proofs of the constant cells end in a bare `:=`, so a
# `:=\s*by`-anchored pattern would skip them AND swallow the following
# theorem's statement. `[^:]*(?::(?!=)[^:]*)*` matches any text containing no
# `:=`, which stops each statement at its own proof delimiter.
_THEOREM_RE = re.compile(
    r"theorem\s+outcome_(Tau[A-Za-z0-9]+)_vs_(Tau[A-Za-z0-9]+)(_high\S*)?\s*:"
    r"([^:]*(?::(?!=)[^:]*)*):=",
    re.DOTALL,
)
_PAIR_RE = re.compile(r"=\s*some\s*\(\s*\.([CD])\s*,\s*\.([CD])\s*\)")
# The α-regime guard: `θ ≤ wC + wTs + wTp + wL →` or `wC + … < θ →`
_LOW_REGIME_RE = re.compile(r"θ\s*≤\s*([\w\s+]+?)\s*→")
_HIGH_REGIME_RE = re.compile(r"([\w\s+]+?)\s*<\s*θ\s*→")
# Large-`k` shape: `∃ k₂, ∀ k, k₂ < k →`
_LARGE_K_RE = re.compile(r"∃\s*k₂\s*,\s*∀\s*k\s*,\s*k₂\s*<\s*k\s*→")


class Regime(str):
    """Which side of the α-boundary a theorem covers."""

    LOW = "low"  # θ ≤ mass  (the cooperative regime)
    HIGH = "high"  # mass < θ (the defect regime)
    UNCONDITIONAL = "unconditional"  # constants: no θ hypothesis at all


@dataclass(frozen=True)
class Def4Theorem:
    """One α-regime-quantified Def-4 outcome theorem, as stated in Lean."""

    name: str
    row: str
    col: str
    regime: str
    mass_terms: tuple[str, ...]
    """The weight variables summed in the regime condition, e.g. (wC, wTs, wTp, wL)."""
    actions: tuple[str, str]
    large_k: bool
    """True when the statement is the `∃k₂, ∀k > k₂` large-budget shape."""

    def applies(self, theta: int, weights: dict[str, int]) -> bool:
        """Does this theorem's regime cover the given (θ, w⃗)?"""
        if self.regime == Regime.UNCONDITIONAL:
            return True
        mass = sum(weights.get(term, 0) for term in self.mass_terms)
        return theta <= mass if self.regime == Regime.LOW else mass < theta


def _parse_mass_terms(expr: str) -> tuple[str, ...]:
    return tuple(t.strip() for t in expr.split("+") if t.strip())


def scan_def4_theorems(path: Path | None = None) -> list[Def4Theorem]:
    """Parse every Def-4 outcome theorem from the Lean matrix file."""
    src = (path or TAU_THEOREMS_FILE).read_text(encoding="utf-8")
    found: list[Def4Theorem] = []
    for match in _THEOREM_RE.finditer(src):
        row, col, suffix, statement = match.groups()
        pair = _PAIR_RE.search(statement)
        if not pair:
            continue
        low = _LOW_REGIME_RE.search(statement)
        high = _HIGH_REGIME_RE.search(statement)
        if high is not None:
            regime, terms = Regime.HIGH, _parse_mass_terms(high.group(1))
        elif low is not None:
            regime, terms = Regime.LOW, _parse_mass_terms(low.group(1))
        else:
            regime, terms = Regime.UNCONDITIONAL, ()
        found.append(
            Def4Theorem(
                name=f"outcome_{row}_vs_{col}{suffix or ''}",
                row=row,
                col=col,
                regime=regime,
                mass_terms=terms,
                actions=(pair.group(1), pair.group(2)),
                large_k=_LARGE_K_RE.search(statement) is not None,
            )
        )
    return found


class Def4Library:
    """The certified Def-4 cells, indexed for lookup at a concrete (θ, w⃗)."""

    def __init__(self, theorems: list[Def4Theorem]):
        self.theorems = theorems
        self._by_pair: dict[tuple[str, str], list[Def4Theorem]] = {}
        for t in theorems:
            self._by_pair.setdefault((t.row, t.col), []).append(t)

    @classmethod
    def load(cls, path: Path | None = None) -> Def4Library:
        return cls(scan_def4_theorems(path))

    @property
    def bots(self) -> tuple[str, ...]:
        names: set[str] = set()
        for t in self.theorems:
            names.add(t.row)
            names.add(t.col)
        return tuple(sorted(names))

    def cell(
        self, row: str, col: str, theta: int, weights: dict[str, int]
    ) -> tuple[str, str] | None:
        """The certified outcome for this matchup at (θ, w⃗), or None if uncovered.

        `None` means "no Lean theorem covers this cell in this regime" — either
        the bot has no theorems at all, or the (θ, w⃗) falls in a regime nobody
        proved (e.g. only the cooperative regime is stated for a mixed pair).
        It is NEVER a silent fallback to computed arithmetic.
        """
        for t in self._by_pair.get((row, col), []):
            if t.applies(theta, weights):
                return t.actions
        return None

    def covers(self, row: str, col: str) -> bool:
        return (row, col) in self._by_pair

    def regimes_for(self, row: str, col: str) -> tuple[str, ...]:
        return tuple(t.regime for t in self._by_pair.get((row, col), []))


# Map the Lean tau-bot names to the BASE bots they lift, so a Lean cell can be
# compared against the Python model's cell for the same matchup.
LEAN_TO_BASE: dict[str, str] = {
    "TauDupoc": "DupocBot",
    "TauCooperate": "CooperateBot",
    "TauDefect": "DefectBot",
    "TauTFTSim": "TitForTatBot",
    "TauTFTPf": "TitForTatBot",
    "TauEBot": "EBot",
}

BASE_TO_LEAN: dict[str, str] = {
    "DupocBot": "TauDupoc",
    "CooperateBot": "TauCooperate",
    "DefectBot": "TauDefect",
    "TitForTatBot": "TauTFTSim",
    "EBot": "TauEBot",
}
"""Default Lean counterpart per base bot (TFT defaults to the SIM variant).

`TauTFTPf` is reachable by name for anyone wanting the prover variant; on the
milestone-1 zoo the two are proven to have the same α-boundary, so the default
is the behavioral one that matches base `TitForTatBot`'s `.sim` guard.
"""


def main() -> None:
    lib = Def4Library.load()
    print(f"Def-4 theorems found: {len(lib.theorems)}")
    print(f"Tau bots with theorems: {', '.join(lib.bots)}")
    print()
    by_regime: dict[str, int] = {}
    for t in lib.theorems:
        by_regime[t.regime] = by_regime.get(t.regime, 0) + 1
    for regime, n in sorted(by_regime.items()):
        print(f"  {regime:<15} {n}")
    print()
    print("Cells (cooperative regime, θ=1 w⃗=all-1):")
    weights = {"wC": 1, "wD": 1, "wTs": 1, "wTp": 1, "wL": 1}
    bots = lib.bots
    width = max(len(b) for b in bots) + 2
    print(" " * width + "".join(b.replace("Tau", "").rjust(width) for b in bots))
    for row in bots:
        line = row.ljust(width)
        for col in bots:
            cell = lib.cell(row, col, 1, weights)
            line += (f"({cell[0]},{cell[1]})" if cell else "—").rjust(width)
        print(line)


if __name__ == "__main__":
    main()
