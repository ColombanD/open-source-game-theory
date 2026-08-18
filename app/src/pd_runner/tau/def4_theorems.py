"""Fetch the Def-4 outcome theorems from the Lean library.

.. warning:: (2026-08-13) The TauEBot window/exploitθ/highθ theorems fetched here
   are kernel-true statements about the RETRACTED crowd-exploiter σ-player, not
   about τ(EBot) under the corrected source-lift Def 4. See the retraction in
   TAUBOT_TRANSPARENCY_DESIGN.md Part III.

The base outcome matrix is unconditional (`outcome_A_vs_B = some (.C, .D)`), so
`eval/outcome_matrix.py` can read a cell as a single action pair. Def-4 cells
are **α-regime-quantified** — the same matchup changes outcome as θ crosses a
player's boundary — so they need their own scanner:

    theorem outcome_TauEBot_vs_TauDupoc :
        ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL wE, wC < θ → θ ≤ wC + wTs + wTp + wL →
          ∃ N, outcome N (TauEBot k θ …) (TauDupoc k θ …) = some (.C, .C) := by

What this module extracts per theorem: the ordered tau-bot pair, the LIST of
θ-hypotheses (each `θ ≤ <mass>` or `<mass> < θ`), and the resulting action
pair. Since the cascade refactor (2026-08-12) the theorems for any pair
PARTITION the θ-axis — the three cooperators share one boundary
(`wC + wTs + wTp + wL`) and TauEBot has three regimes (`_exploitθ` at
`θ ≤ wC`, the unsuffixed WINDOW `wC < θ ≤ wC+wTs+wTp+wL`, and `_highθ`) — so a
lookup at a concrete `(θ, w⃗)` simply evaluates every theorem's hypotheses in
conjunction and takes the (unique) one that applies. No per-side mass
bookkeeping is needed anymore: tau players are `.opp`-free, so instantiating a
matchup theorem at ONE player's own `(θ, w⃗)` always reads that player's
component correctly (`row_action`).

This makes `tau/compare.py` read the KERNEL for the Def-4 side rather than
trusting the Python re-derivation. Purely static: no Lean invocation, the
kernel already checked every statement.

**Scope.** Only the bots in `engine/PrisonersDilemma/Theorems/Tau/Matrix.lean`
have theorems. A tau bot modelled in Python but not yet built in Lean has NO
certified cell, and `certified_cell` returns `None` for it — that absence is
the honest signal that a result is predicted rather than proven, and the
comparison reports it as such instead of silently falling back to arithmetic.
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
# Tau bot names are alphanumeric; the optional suffix (`_highθ`, `_exploitθ`)
# marks which α-regime of the pair the theorem covers.
#
# The statement body must NOT be allowed to run past its own `:=` into the next
# theorem — the term-mode proofs of the constant cells end in a bare `:=`, so a
# `:=\s*by`-anchored pattern would skip them AND swallow the following
# theorem's statement. `[^:]*(?::(?!=)[^:]*)*` matches any text containing no
# `:=`, which stops each statement at its own proof delimiter.
_THEOREM_RE = re.compile(
    r"theorem\s+outcome_(Tau[A-Za-z0-9]+)_vs_(Tau[A-Za-z0-9]+)(_\S+)?\s*:"
    r"([^:]*(?::(?!=)[^:]*)*):=",
    re.DOTALL,
)
_PAIR_RE = re.compile(r"=\s*some\s*\(\s*\.([CD])\s*,\s*\.([CD])\s*\)")
# The θ-hypotheses: `θ ≤ wC + wTs + wTp + wL →` and `wC < θ →`
_LE_RE = re.compile(r"θ\s*≤\s*([\w\s+]+?)\s*→")
_LT_RE = re.compile(r"([\w\s+]+?)\s*<\s*θ\s*→")
# Large-`k` shape: `∃ k₂, ∀ k, k₂ < k →`
_LARGE_K_RE = re.compile(r"∃\s*k₂\s*,\s*∀\s*k\s*,\s*k₂\s*<\s*k\s*→")


class Regime(str):
    """Which α-regime of the pair a theorem covers (a reporting label; the
    lookup itself evaluates the hypotheses, not the label)."""

    LOW = "low"  # θ ≤ mass — the cooperators' cooperative regime
    HIGH = "high"  # mass < θ — everyone defects
    EXPLOIT = "exploit"  # θ ≤ wC — TauEBot's exploit stage fires (defects)
    WINDOW = "window"  # wC < θ ≤ mass — TauEBot's cooperation window
    UNCONDITIONAL = "unconditional"  # constants: no θ hypothesis at all


@dataclass(frozen=True)
class Def4Theorem:
    """One α-regime-quantified Def-4 outcome theorem, as stated in Lean."""

    name: str
    row: str
    col: str
    regime: str
    hypotheses: tuple[tuple[str, tuple[str, ...]], ...]
    """The θ-hypotheses, in statement order: `("le", terms)` means
    `θ ≤ Σ terms`, `("lt", terms)` means `Σ terms < θ`. All must hold for the
    theorem to apply (they are curried conjuncts in the Lean statement)."""

    actions: tuple[str, str]
    large_k: bool
    """True when the statement is the `∃k₂, ∀k > k₂` large-budget shape."""

    def applies(self, theta: int, weights: dict[str, int]) -> bool:
        """Does this theorem cover the given (θ, w⃗)?"""
        for op, terms in self.hypotheses:
            mass = sum(weights.get(t, 0) for t in terms)
            if op == "le" and not theta <= mass:
                return False
            if op == "lt" and not mass < theta:
                return False
        return True

    @property
    def mass_terms(self) -> tuple[str, ...]:
        """The first ≤-boundary's terms (reporting convenience)."""
        for op, terms in self.hypotheses:
            if op == "le":
                return terms
        return ()


def _parse_mass_terms(expr: str) -> tuple[str, ...]:
    return tuple(t.strip() for t in expr.split("+") if t.strip())


def _classify(suffix: str, hypotheses: tuple) -> str:
    if not hypotheses:
        return Regime.UNCONDITIONAL
    if suffix == "_exploitθ":
        return Regime.EXPLOIT
    if suffix == "_highθ":
        return Regime.HIGH
    if len(hypotheses) >= 2:
        return Regime.WINDOW
    return Regime.LOW if hypotheses[0][0] == "le" else Regime.HIGH


def scan_def4_theorems(path: Path | None = None) -> list[Def4Theorem]:
    """Parse every Def-4 outcome theorem from the Lean matrix file."""
    src = (path or TAU_THEOREMS_FILE).read_text(encoding="utf-8")
    found: list[Def4Theorem] = []
    for match in _THEOREM_RE.finditer(src):
        row, col, suffix, statement = match.groups()
        pair = _PAIR_RE.search(statement)
        if not pair:
            continue
        # Reconstruct the hypotheses in statement order so WINDOW reads
        # (wC < θ, θ ≤ mass) as written; order is irrelevant to `applies`.
        hyps: list[tuple[int, tuple[str, tuple[str, ...]]]] = []
        for m in _LE_RE.finditer(statement):
            hyps.append((m.start(), ("le", _parse_mass_terms(m.group(1)))))
        for m in _LT_RE.finditer(statement):
            hyps.append((m.start(), ("lt", _parse_mass_terms(m.group(1)))))
        # drop the `k₂ < k` budget quantifier the LT regex may have matched
        hypotheses = tuple(
            h for _, h in sorted(hyps) if h[1] and all(t != "k₂" for t in h[1])
        )
        found.append(
            Def4Theorem(
                name=f"outcome_{row}_vs_{col}{suffix or ''}",
                row=row,
                col=col,
                regime=_classify(suffix or "", hypotheses),
                hypotheses=hypotheses,
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

    def row_action(
        self, row: str, col: str, theta: int, weights: dict[str, int]
    ) -> str | None:
        """The ROW player's certified action at ITS OWN (θ, w⃗).

        In a tournament the two players see DIFFERENT signals, but tau players
        are `.opp`-free: each side's action depends only on its own signal. So
        instantiating the matchup's theorems at the row player's `(θ, w⃗)` and
        reading the ROW component is exact, whatever the column player's actual
        signal is. Since the pair's theorems partition the θ-axis, exactly one
        applies.
        """
        for t in self._by_pair.get((row, col), []):
            if t.applies(theta, weights):
                return t.actions[0]
        return None

    def cell(
        self, row: str, col: str, theta: int, weights: dict[str, int]
    ) -> tuple[str, str] | None:
        """The certified outcome for this matchup at a SHARED (θ, w⃗), or None.

        `None` means "no Lean theorem covers this cell in this regime" — either
        the bot has no theorems at all, or the (θ, w⃗) falls in a regime nobody
        proved. It is NEVER a silent fallback to computed arithmetic.
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

`TauTFTPf` is reachable by name for anyone wanting the prover variant; on this
zoo the two are proven to have the same α-boundary, so the default is the
behavioral one that matches base `TitForTatBot`'s `.sim` guard.
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
    weights = {"wC": 1, "wD": 1, "wTs": 1, "wTp": 1, "wL": 1, "wE": 1}
    bots = lib.bots
    width = max(len(b) for b in bots) + 2
    for theta, label in ((1, "θ=1: TauEBot's exploit stage fires on wC"),
                         (2, "θ=2: TauEBot's window"),
                         (5, "θ=5: above every boundary")):
        print()
        print(f"Cells at {label} (w⃗ = all-1):")
        print(" " * width + "".join(b.replace("Tau", "").rjust(width) for b in bots))
        for row in bots:
            line = row.ljust(width)
            for col in bots:
                cell = lib.cell(row, col, theta, weights)
                line += (f"({cell[0]},{cell[1]})" if cell else "—").rjust(width)
            print(line)


if __name__ == "__main__":
    main()
