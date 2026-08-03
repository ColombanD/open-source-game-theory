"""Tau tournaments and (t, α) phase diagrams.

The headline experiment: *how much transparency does Löbian cooperation need?*

A tau tournament at (t, α) runs every ordered pair of tau-lifted bots against
each other, each side seeing σ_t of the opponent. The summary statistic is the
**cooperation rate** — the fraction of cells where both sides play C. Sweeping
t traces how cooperation decays as transparency drops; sweeping α separates
that from the agents' own caution.

Because the tau layer is matrix arithmetic, a whole sweep is milliseconds and
the phase diagram is piecewise constant with finitely many breakpoints (see
`alpha_breakpoints`) — so it can be reported exactly rather than sampled.
"""

from __future__ import annotations

from dataclasses import dataclass, field

from pd_runner.tau.matrix import TauMatrix, load_tau_matrix
from pd_runner.tau.play import tau_match
from pd_runner.tau.signal import (
    behavioral_distance_matrix,
    signal_family,
    transparency,
)


@dataclass(frozen=True)
class TournamentResult:
    """One tau tournament at a fixed (t, α)."""

    temperature: float
    alpha: float
    transparency: float
    # Fraction of ordered pairs where BOTH sides cooperate.
    mutual_coop_rate: float
    # Fraction of ordered pairs where the row bot cooperates.
    coop_rate: float
    # Per-pair actions, keyed (row, col) -> (row_action, col_action).
    cells: dict[tuple[str, str], tuple[str, str]] = field(repr=False)
    # Bots that play C against every opponent / D against every opponent.
    unconditional_cooperators: tuple[str, ...] = ()
    unconditional_defectors: tuple[str, ...] = ()

    @property
    def is_degenerate(self) -> bool:
        """True when every bot plays unconditionally — the classical-PD limit."""
        n = len(self.unconditional_cooperators) + len(self.unconditional_defectors)
        return n == len({b for b, _ in self.cells})

    @property
    def composition(self) -> dict[str, float]:
        """Fractions of (C,C) / exploitation / (D,D) — the three game outcomes.

        `mutual_coop_rate` alone hides which of the other three outcomes it is
        displacing: as blur rises, exploitation can convert into cooperation
        (bots fooled into cooperating with defectors) while genuine mutual
        defection falls. That reads as "more cooperation" unless the split is
        shown. The three fractions sum to 1.

        Exploitation pools (C,D) and (D,C): the cell set is closed under
        transpose, so each exploited pairing appears once from each side.
        """
        total = len(self.cells)
        mutual_c = sum(1 for a, b in self.cells.values() if a == b == "C")
        mutual_d = sum(1 for a, b in self.cells.values() if a == b == "D")
        return {
            "CC": mutual_c / total,
            "exploit": (total - mutual_c - mutual_d) / total,
            "DD": mutual_d / total,
        }


def run_tournament(
    matrix: TauMatrix,
    temperature: float,
    alpha: float,
    distances: dict[tuple[str, str], int] | None = None,
) -> TournamentResult:
    """Every ordered tau-vs-tau pair at one (t, α)."""
    dist = distances if distances is not None else behavioral_distance_matrix(matrix)
    channel = signal_family(matrix, temperature, dist)

    cells: dict[tuple[str, str], tuple[str, str]] = {}
    for row in matrix.bots:
        for col in matrix.bots:
            out = tau_match(matrix, row, col, alpha, channel)
            cells[(row, col)] = (out.row_action, out.col_action)

    total = len(cells)
    mutual = sum(1 for a, b in cells.values() if a == "C" and b == "C")
    row_coop = sum(1 for a, _ in cells.values() if a == "C")

    always_c, always_d = [], []
    for b in matrix.bots:
        actions = {cells[(b, col)][0] for col in matrix.bots}
        if actions == {"C"}:
            always_c.append(b)
        elif actions == {"D"}:
            always_d.append(b)

    return TournamentResult(
        temperature=temperature,
        alpha=alpha,
        transparency=transparency(matrix, temperature, dist),
        mutual_coop_rate=mutual / total,
        coop_rate=row_coop / total,
        cells=cells,
        unconditional_cooperators=tuple(always_c),
        unconditional_defectors=tuple(always_d),
    )


def base_tournament_cells(matrix: TauMatrix) -> dict[tuple[str, str], tuple[str, str]]:
    """The base outcome matrix as tournament cells — the t = 0 target."""
    return {
        (row, col): (matrix.action(row, col), matrix.action(col, row))
        for row in matrix.bots
        for col in matrix.bots
    }


def anchor_holds(matrix: TauMatrix, alpha: float = 0.5) -> bool:
    """Anchor theorem check: at t = 0 the tau tournament IS the base matrix.

    Holds for every α ∈ (0, 1] since a point-mass cooperation mass is 0 or 1.
    """
    result = run_tournament(matrix, temperature=0.0, alpha=alpha)
    return result.cells == base_tournament_cells(matrix)


def sweep(
    matrix: TauMatrix,
    temperatures: list[float],
    alphas: list[float],
) -> list[TournamentResult]:
    """The (t, α) grid."""
    dist = behavioral_distance_matrix(matrix)
    return [
        run_tournament(matrix, t, a, dist)
        for t in temperatures
        for a in alphas
    ]


def logspace(low: float, high: float, count: int) -> list[float]:
    """Geometric spacing — temperature spans decades, so linear grids waste points."""
    if count < 2:
        return [low]
    ratio = (high / low) ** (1.0 / (count - 1))
    return [low * ratio**i for i in range(count)]


def main() -> None:
    import argparse

    parser = argparse.ArgumentParser(description="Run tau tournaments / phase sweeps.")
    parser.add_argument("--alphas", type=str, default="0.25,0.5,0.75,1.0")
    parser.add_argument("--t-min", type=float, default=0.05)
    parser.add_argument("--t-max", type=float, default=20.0)
    parser.add_argument("--t-steps", type=int, default=12)
    args = parser.parse_args()

    matrix = load_tau_matrix()
    alphas = [float(a) for a in args.alphas.split(",")]
    temperatures = [0.0] + logspace(args.t_min, args.t_max, args.t_steps)

    print(f"tau sweep over {len(matrix)} bots ({len(matrix) ** 2} ordered cells)")
    print(f"anchor theorem at t=0: {'HOLDS' if anchor_holds(matrix) else 'FAILS'}")
    print()
    header = f"{'t':>8} {'transp':>7} | " + " | ".join(
        f"α={a:<4} coop mutual" for a in alphas
    )
    print(header)
    print("-" * len(header))
    for t in temperatures:
        row = []
        transp = None
        for a in alphas:
            r = run_tournament(matrix, t, a)
            transp = r.transparency
            flag = "*" if r.is_degenerate else " "
            row.append(f"       {r.coop_rate:>5.2f} {r.mutual_coop_rate:>5.2f}{flag}")
        print(f"{t:>8.3f} {transp:>7.3f} | " + " | ".join(row))
    print("\n* = every bot plays unconditionally (classical-PD limit)")


if __name__ == "__main__":
    main()
