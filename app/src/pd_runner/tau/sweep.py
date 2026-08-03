"""Tau tournaments and (t, α) phase diagrams.

The headline experiment: *how much transparency does Löbian cooperation need?*

A tau tournament at (t, α) runs every ordered pair of tau-lifted bots against
each other, each side seeing σ_t of the opponent. `t ∈ [0, 1]` is the
transparency dial (1 = full transparency, 0 = opaque — see `tau.signal`). The
summary statistic is the **cooperation rate** — the fraction of cells where
both sides play C. Sweeping t traces how cooperation decays as transparency
drops; sweeping α separates that from the agents' own caution.

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
    signal_family_at_temperature,
    temperature_for_transparency,
    transparency,
)


@dataclass(frozen=True)
class TournamentResult:
    """One tau tournament at a fixed (t, α)."""

    # The dial: target transparency in [0, 1], 1 = full, 0 = opaque.
    t: float
    # The raw softmax temperature that realized the dial (internal knob).
    temperature: float
    alpha: float
    # MEASURED transparency of the channel — equals the dial up to bisection
    # tolerance, except above a twin ceiling, where it clamps.
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
    t: float,
    alpha: float,
    distances: dict[tuple[str, str], int] | None = None,
) -> TournamentResult:
    """Every ordered tau-vs-tau pair at one (t, α).

    `t ∈ [0, 1]` is the transparency dial: 1 = full (the base matrix), 0 =
    opaque (the classical-PD limit).
    """
    dist = distances if distances is not None else behavioral_distance_matrix(matrix)
    temperature = temperature_for_transparency(matrix, t, distances=dist)
    channel = signal_family_at_temperature(matrix, temperature, dist)

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
        t=t,
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
    """Anchor theorem check: at t = 1 the tau tournament IS the base matrix.

    Holds for every α ∈ (0, 1] since a point-mass cooperation mass is 0 or 1.
    """
    result = run_tournament(matrix, t=1.0, alpha=alpha)
    return result.cells == base_tournament_cells(matrix)


def sweep(
    matrix: TauMatrix,
    ts: list[float],
    alphas: list[float],
) -> list[TournamentResult]:
    """The (t, α) grid; t values are transparency dials in [0, 1]."""
    dist = behavioral_distance_matrix(matrix)
    return [
        run_tournament(matrix, t, a, dist)
        for t in ts
        for a in alphas
    ]


def main() -> None:
    import argparse

    parser = argparse.ArgumentParser(description="Run tau tournaments / phase sweeps.")
    parser.add_argument("--alphas", type=str, default="0.3,0.45,0.62,0.8")
    parser.add_argument("--t-steps", type=int, default=11,
                        help="linear steps on the transparency dial from 1.0 down to 0.0")
    args = parser.parse_args()

    matrix = load_tau_matrix()
    alphas = [float(a) for a in args.alphas.split(",")]
    steps = max(args.t_steps, 2)
    ts = [round(1.0 - i / (steps - 1), 4) for i in range(steps)]

    print(f"tau sweep over {len(matrix)} bots ({len(matrix) ** 2} ordered cells)")
    print(f"anchor theorem at t=1: {'HOLDS' if anchor_holds(matrix) else 'FAILS'}")
    print()
    header = f"{'t':>6} {'temp':>9} | " + " | ".join(
        f"α={a:<4} coop mutual" for a in alphas
    )
    print(header)
    print("-" * len(header))
    for t in ts:
        row = []
        temp = None
        for a in alphas:
            r = run_tournament(matrix, t, a)
            temp = r.temperature
            flag = "*" if r.is_degenerate else " "
            row.append(f"       {r.coop_rate:>5.2f} {r.mutual_coop_rate:>5.2f}{flag}")
        print(f"{t:>6.2f} {temp:>9.3f} | " + " | ".join(row))
    print("\nt = transparency dial (1 = full, 0 = opaque); temp = realized softmax temperature")
    print("* = every bot plays unconditionally (classical-PD limit)")


if __name__ == "__main__":
    main()
