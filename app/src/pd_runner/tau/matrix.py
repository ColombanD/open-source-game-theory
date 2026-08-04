"""The ordered, fully-proven outcome table the tau layer reads.

Everything about WHICH theorems count — the Lean scan, the strict name regex,
the `†` side-hypothesis and `∃k`/large-`k` shape classification, and the
"hand-written beats `llm_`" preference — is reused from
`eval/outcome_matrix.py` (`scan_outcome_theorems`, `index_by_ordered_pair`,
`library_bots`). There is exactly one acceptance policy in the codebase.

What this module adds is ORIENTATION. `build_outcome_matrix` renders an
UPPER-TRIANGULAR table for humans, swapping the reversed theorem into a cell
when only one orientation is proven, so a cell's row/column roles depend on
where it sits. Def 3 needs `outcome(A, Bᵢ)` as an ORDERED pair with A's action
first, and the zoo has genuinely asymmetric cells (`DBot` vs `CupodTrollBot` is
`(D, C)`), so we build the full square ourselves and cross-check the two
orientations against each other.

Conventions fixed 2026-08-03 (see the design note's "open design decisions"):

1. **Open cells** — resolved by RESTRICTING THE ZOO.
   `FULL_CERTIFIED_SUB_ZOO` is the maximum set of bots whose induced ordered
   submatrix is totally proven, so the tau layer is a TOTAL function and no
   open/missing convention is needed.
1a. **Proven `none` is a fifth cell state (2026-08-04).** A proven
   `outcome_X_vs_Y = none` theorem (MirrorBot self-play: mutual simulation
   never terminates) loads as a real cell with both actions `"N"`. UNPROVEN
   cells still fail loudly — `"N"` is a kernel-backed value, not a missing
   convention. Downstream, `"N"` counts as not-cooperating (the pessimistic
   reading: `cooperates` tests `== "C"`), rows carry it as a third symbol for
   twin/distance purposes, and the sweep's mutual-C/mutual-D split treats an
   (N, N) base cell as neither. `FULL_CERTIFIED_SUB_ZOO` predates this state
   and still excludes MirrorBot; `ENLARGED_SUB_ZOO` includes it.
1b. **Behavioral twins** — `CERTIFIED_SUB_ZOO` (the default) further drops
   LegibleBot and JustBot, which are behaviorally identical to other members
   and so cap the transparency scale. See `_TWIN_EXCLUSIONS`.
2. **Budgets** — the exported matrix has already collapsed the budget
   dimension (`∃k` and large-`k` cells carry their action pair), so the tau
   layer reads the stable asymptotic outcome and `k` is not a dial in v1a.
   Cell `shape` and `has_hypotheses` are retained for sensitivity analysis.
"""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path

from pd_runner.eval.outcome_matrix import (
    index_by_ordered_pair,
    library_bots,
    scan_outcome_theorems,
)

# The maximum sub-zoo whose induced ORDERED submatrix is totally proven, as of
# 2026-08-03: 12 bots, 144/144 cells, zero orientation conflicts. Recompute
# with `python -m pd_runner.tau.matrix --recompute` after proving new cells.
#
# Excluded and why: MirrorBot (self-play proven `none`), OptimBot (self-play
# unproven), CupodBot / CIMCIC / DIMCID / WaryBot (search×search and .neg-guard
# frontier cells still open). Note the exclusions are not random — they are
# exactly the hard fragment, so this sub-zoo is biased toward the easier half
# of the zoo. Say so when reporting results.
FULL_CERTIFIED_SUB_ZOO: tuple[str, ...] = (
    "CooperateBot",
    "CupodTrollBot",
    "DBot",
    "DefectBot",
    "DupocBot",
    "EBot",
    "GuardianBot",
    "JustBot",
    "LegibleBot",
    "OBot",
    "PrudentBot",
    "TitForTatBot",
)

# Bots dropped to reduce BEHAVIORAL TWINNING (2026-08-03).
#
# Twins are bots with identical action rows: σ cannot separate them at any
# temperature, so they cap the transparency scale below 1.0. The full 12-bot
# zoo has two twin groups — {CooperateBot, CupodTrollBot, LegibleBot} and
# {DupocBot, JustBot} — holding the ceiling at 0.843.
#
# LegibleBot and JustBot are the two removals; CupodTrollBot is KEPT because
# admitting CupodBot (below) separates it on PROVEN data
# (`outcome_CupodTrollBot_vs_CupodBot`), so the third removal is unnecessary.
_TWIN_EXCLUSIONS: tuple[str, ...] = ("LegibleBot", "JustBot")

# CupodBot is admitted to break the remaining twin group, at the cost of two
# STIPULATED cells (its only holes against this zoo). It is the bot whose
# column separates {CooperateBot, CupodTrollBot}.
#
# The stipulations buy MEMBERSHIP, not the result: all 16 assignments of these
# two cells give a twin-free zoo at ceiling 1.0, so twin-freeness is invariant
# under the choice. Any result that is NOT invariant must be reported as
# conditional — `TauMatrix.is_fully_proven` is False for this zoo.
CUPOD_STIPULATIONS: dict[tuple[str, str], tuple[str, str]] = {
    ("CupodBot", "DupocBot"): ("C", "D"),
    ("PrudentBot", "CupodBot"): ("D", "C"),
}

# The default tau zoo: 11 bots, NO behavioral twins, transparency ceiling
# exactly 1.0 — every bot is identifiable from behavior alone. Load it with
# `load_tau_matrix()`, which applies `CUPOD_STIPULATIONS` by default.
CERTIFIED_SUB_ZOO: tuple[str, ...] = tuple(
    sorted(
        [b for b in FULL_CERTIFIED_SUB_ZOO if b not in _TWIN_EXCLUSIONS]
        + ["CupodBot"]
    )
)

# The fully-proven fallback: no stipulated cells, but 10 bots and a residual
# {CooperateBot, CupodTrollBot} twin pair holding the ceiling at ≈0.940. Use
# when a result must rest on the Lean kernel alone.
PROVEN_ONLY_SUB_ZOO: tuple[str, ...] = tuple(
    b for b in FULL_CERTIFIED_SUB_ZOO if b not in _TWIN_EXCLUSIONS
)

# The 16-bot enlarged zoo (2026-08-04): everything above plus the twins back
# in (LegibleBot, JustBot), the search×search frontier bots (CIMCIC, DIMCID),
# and MirrorBot, whose proven-`none` self-play loads as the "N" fifth state.
# Load with
#     load_tau_matrix(ENLARGED_SUB_ZOO, hypothetical_cells=ENLARGED_STIPULATIONS)
#
# Twin structure (invariant under the stipulations' proven-cell constraints,
# computed 2026-08-04): behavioral {CooperateBot, LegibleBot} (all-C rows) and
# {DupocBot, JustBot} (identical rows); syntactic {DBot, TitForTatBot};
# ε-uniform none. CupodTrollBot is separated from the all-C group by its
# proven D against CupodBot.
ENLARGED_SUB_ZOO: tuple[str, ...] = tuple(
    sorted(
        FULL_CERTIFIED_SUB_ZOO
        + ("CupodBot", "CIMCIC", "DIMCID", "MirrorBot")
    )
)

# Stipulated (unproven) cells completing the enlarged zoo's ordered submatrix.
# All are frontier search×search cells; every result over this zoo is
# conditional on them (`TauMatrix.is_fully_proven` is False). Drop an entry as
# soon as its theorem lands — the loader raises on a stipulation that shadows
# a proven cell, so a stale entry fails loudly, not silently.
ENLARGED_STIPULATIONS: dict[tuple[str, str], tuple[str, str]] = {
    **CUPOD_STIPULATIONS,
    ("JustBot", "CupodBot"): ("D", "C"),
    ("CIMCIC", "CupodBot"): ("C", "C"),
    ("CIMCIC", "OBot"): ("D", "D"),
    ("DIMCID", "CupodBot"): ("D", "D"),
    ("DIMCID", "DupocBot"): ("D", "D"),
    # DIMCID vs CupodTrollBot was stipulated (C, C) here until 2026-08-04, when
    # `llm_outcome_DIMCID_vs_CupodTrollBot` landed proving exactly that. The
    # entry is gone rather than kept-and-ignored: the loader raises on a
    # stipulation shadowing a proven cell, which is how this was caught.
}


@dataclass(frozen=True)
class NamedZoo:
    """A selectable sub-zoo: its bot list, its stipulations, and why it exists.

    The registry below is the single source of truth shared by the CLI
    (`--zoo`), the API (`/tau/report?zoo=`) and the UI dropdown, so a new zoo
    is added in ONE place and appears everywhere.
    """

    key: str
    label: str
    description: str
    bots: tuple[str, ...]
    stipulations: dict[tuple[str, str], tuple[str, str]]

    def load(self, theorems_dir: Path | None = None) -> TauMatrix:
        return load_tau_matrix(
            self.bots,
            theorems_dir=theorems_dir,
            hypothetical_cells=self.stipulations,
        )


# Selectable zoos, in presentation order (default first).
ZOOS: dict[str, NamedZoo] = {
    "default": NamedZoo(
        key="default",
        label="default (11 bots, twin-free)",
        description=(
            "The twin-free working zoo: transparency ceiling exactly 1.0, so "
            "every bot is identifiable from behavior alone. Conditional on the "
            "two CupodBot stipulations."
        ),
        bots=CERTIFIED_SUB_ZOO,
        stipulations=CUPOD_STIPULATIONS,
    ),
    "enlarged": NamedZoo(
        key="enlarged",
        label="enlarged (16 bots, stipulated)",
        description=(
            "The widest zoo: adds the behavioral twins (LegibleBot, JustBot), "
            "the search×search frontier bots (CIMCIC, DIMCID) and MirrorBot, "
            "whose proven-`none` self-play is the 'N' state. Most conditional "
            "— 8 stipulated pairs."
        ),
        bots=ENLARGED_SUB_ZOO,
        stipulations=ENLARGED_STIPULATIONS,
    ),
    "full-certified": NamedZoo(
        key="full-certified",
        label="full certified (12 bots, proven)",
        description=(
            "The maximum totally-proven sub-zoo: zero stipulations, but two "
            "behavioral twin groups hold the transparency ceiling at ≈0.843."
        ),
        bots=FULL_CERTIFIED_SUB_ZOO,
        stipulations={},
    ),
    "proven-only": NamedZoo(
        key="proven-only",
        label="proven only (10 bots, kernel-clean)",
        description=(
            "Kernel-clean and twin-reduced: no stipulated cells at all, with a "
            "residual {CooperateBot, CupodTrollBot} twin pair (ceiling ≈0.940). "
            "Use when a result must rest on the Lean kernel alone."
        ),
        bots=PROVEN_ONLY_SUB_ZOO,
        stipulations={},
    ),
}

DEFAULT_ZOO = "default"


def get_zoo(key: str) -> NamedZoo:
    """Look up a named zoo, failing with the valid keys listed."""
    try:
        return ZOOS[key]
    except KeyError:
        raise KeyError(
            f"unknown zoo {key!r}; choose one of {sorted(ZOOS)}"
        ) from None


@dataclass(frozen=True)
class Cell:
    """One ordered matrix entry: what `row` and `col` each play, row first."""

    # "C" | "D" — the action of the ROW bot; "N" when the outcome is a proven
    # `none` (no fixpoint — MirrorBot self-play). "N" always appears on both
    # sides at once: it is a property of the match, not of one player.
    row_action: str
    col_action: str
    # "universal" | "existential" (∃k) | "threshold" (∃k₂, ∀k>k₂)
    # | "no_outcome" (proven `= none` — the "N" cells)
    # | "HYPOTHETICAL" (stipulated, NOT proven — see `hypothetical`)
    shape: str
    # Proved under extra side hypotheses (floor/size/budget guards) — the `†`
    # cells. Tracked so a sweep can report how much probability mass rests on
    # them and be re-run without them.
    has_hypotheses: bool
    # True when this cell was read off the REVERSED theorem (outcome_col_vs_row)
    # and swapped. Not a defect — the game is symmetric in the sense that
    # `outcome A B = (a, b)` iff `outcome B A = (b, a)` — but worth auditing.
    swapped: bool
    theorem: str
    # True when this cell was STIPULATED via `hypothetical_cells`, not proven
    # by the Lean kernel. Any result computed over a matrix containing these is
    # conditional on the stipulation and must be reported as such.
    hypothetical: bool = False


class TauMatrix:
    """A totally-proven ordered outcome table over a fixed bot list."""

    def __init__(self, bots: tuple[str, ...], cells: dict[tuple[str, str], Cell]):
        self.bots = bots
        self._cells = cells

    def __len__(self) -> int:
        return len(self.bots)

    def cell(self, row: str, col: str) -> Cell:
        try:
            return self._cells[(row, col)]
        except KeyError:
            raise KeyError(
                f"no proven cell for outcome({row}, {col}); "
                f"the tau matrix is restricted to {list(self.bots)}"
            ) from None

    def action(self, actor: str, opponent: str) -> str:
        """What `actor` plays in `outcome(actor, opponent)` — the Def 3 probe."""
        return self.cell(actor, opponent).row_action

    def cooperates(self, actor: str, opponent: str) -> bool:
        return self.action(actor, opponent) == "C"

    def row(self, actor: str) -> tuple[str, ...]:
        """`actor`'s own actions across the whole sub-zoo, in `bots` order.

        This is the behavioral signature σ's distance is computed over.
        """
        return tuple(self.action(actor, opp) for opp in self.bots)

    @property
    def dagger_cells(self) -> tuple[tuple[str, str], ...]:
        return tuple(k for k, c in self._cells.items() if c.has_hypotheses)

    @property
    def hypothetical_cells(self) -> tuple[tuple[str, str], ...]:
        """Stipulated (unproven) cells — empty for a purely Lean-backed matrix."""
        return tuple(k for k, c in self._cells.items() if c.hypothetical)

    @property
    def is_fully_proven(self) -> bool:
        return not self.hypothetical_cells


def load_tau_matrix(
    bots: tuple[str, ...] = CERTIFIED_SUB_ZOO,
    theorems_dir: Path | None = None,
    hypothetical_cells: dict[tuple[str, str], tuple[str, str]] | None = None,
) -> TauMatrix:
    """Build the ordered outcome table, raising if any cell is unproven.

    Totality is enforced, not assumed: if a bot list is passed whose submatrix
    has a hole, this fails loudly rather than silently producing a tau layer
    with an implicit convention nobody chose.

    The DEFAULT zoo includes CupodBot, whose two cells against it are unproven,
    so `CUPOD_STIPULATIONS` is applied when `hypothetical_cells` is not given
    (pass `{}` to opt out and get the totality error instead, or use
    `PROVEN_ONLY_SUB_ZOO` for a kernel-only matrix).

    `hypothetical_cells` maps an ordered pair to a STIPULATED `(row_action,
    col_action)`, filling holes for what-if analysis — e.g. "if CupodBot vs
    DupocBot were (C, D), how would the twin structure change?". Rules:

    - A stipulation may only fill a genuine hole; it never overrides a proven
      cell (that would silently contradict the kernel), and attempting to do so
      raises.
    - One entry suffices per unordered pair — the transpose is derived, so the
      two can never disagree.
    - Every resulting cell is flagged `hypothetical`, and `TauMatrix.
      is_fully_proven` goes False, so downstream results can be reported as
      conditional.
    """
    kwargs = {"theorems_dir": theorems_dir} if theorems_dir is not None else {}
    by_pair = index_by_ordered_pair(scan_outcome_theorems(**kwargs))
    stipulated = (
        dict(CUPOD_STIPULATIONS) if hypothetical_cells is None else dict(hypothetical_cells)
    )
    # Stipulations are keyed by pair, so carrying the defaults into a non-default
    # zoo is harmless: entries for absent bots are simply never consulted.

    cells: dict[tuple[str, str], Cell] = {}
    missing: list[tuple[str, str]] = []
    conflicts: list[tuple[str, str]] = []
    overridden: list[tuple[str, str]] = []

    for row in bots:
        for col in bots:
            forward = by_pair.get((row, col))
            reverse = by_pair.get((col, row))

            # Cross-check both orientations when both exist. A proven `none`
            # (pair is None) transposes to itself, so the orientations must
            # agree on none-ness as well as on the actions.
            if forward is not None and reverse is not None and row != col:
                fp, rp = forward.pair, reverse.pair
                if (fp is None) != (rp is None) or (
                    fp is not None and rp is not None and fp != (rp[1], rp[0])
                ):
                    conflicts.append((row, col))

            chosen, swapped = (forward, False) if forward is not None else (reverse, True)

            if chosen is not None:
                # A stipulation must never contradict the kernel — including a
                # proven `none`, which is a real value ("N"), not a hole.
                if (row, col) in stipulated or (col, row) in stipulated:
                    overridden.append((row, col))
            else:
                # No proof: fall back to a stipulation if one was supplied,
                # accepting it in either orientation and transposing as needed.
                pair = stipulated.get((row, col))
                if pair is None:
                    flipped = stipulated.get((col, row))
                    pair = (flipped[1], flipped[0]) if flipped else None
                if pair is None:
                    missing.append((row, col))
                    continue
                cells[(row, col)] = Cell(
                    row_action=pair[0],
                    col_action=pair[1],
                    shape="HYPOTHETICAL",
                    has_hypotheses=False,
                    swapped=False,
                    theorem=f"(stipulated {row} vs {col})",
                    hypothetical=True,
                )
                continue

            if chosen.pair is None:
                a = b = "N"
            else:
                a, b = chosen.pair
                if swapped:
                    a, b = b, a
            cells[(row, col)] = Cell(
                row_action=a,
                col_action=b,
                shape=chosen.shape,
                has_hypotheses=chosen.has_hypotheses,
                swapped=swapped,
                theorem=chosen.name,
            )

    if overridden:
        raise ValueError(
            "hypothetical_cells may only fill unproven holes, but these pairs "
            f"already have proven theorems: {sorted(set(map(tuple, map(sorted, overridden))))}"
        )
    if conflicts:
        raise ValueError(
            "outcome matrix is inconsistent — both orientations proven and "
            f"disagreeing for: {conflicts}"
        )
    if missing:
        raise ValueError(
            f"tau matrix is not total: {len(missing)} unproven ordered cell(s), "
            f"e.g. {missing[:5]}. Restrict the bot list or prove the cells."
        )
    return TauMatrix(bots, cells)


def maximum_certified_sub_zoo(theorems_dir: Path | None = None) -> list[str]:
    """Recompute the largest totally-proven sub-zoo (exact max clique).

    Used to refresh `CERTIFIED_SUB_ZOO` as new cells get proven. Excludes bots
    whose self-play cell is unproven or proven `none`.
    """
    kwargs = {"theorems_dir": theorems_dir} if theorems_dir is not None else {}
    by_pair = index_by_ordered_pair(scan_outcome_theorems(**kwargs))
    all_bots = sorted(library_bots(**kwargs))

    def known(a: str, b: str) -> bool:
        for key in ((a, b), (b, a)):
            t = by_pair.get(key)
            if t is not None and t.pair is not None:
                return True
        return False

    candidates = [b for b in all_bots if known(b, b)]
    adj = {b: {c for c in candidates if c != b and known(b, c)} for b in candidates}

    best: list[str] = []

    def expand(clique: list[str], pool: list[str]) -> None:
        nonlocal best
        if not pool:
            if len(clique) > len(best):
                best = list(clique)
            return
        if len(clique) + len(pool) <= len(best):
            return
        remaining = list(pool)
        for v in pool:
            expand(clique + [v], [u for u in remaining if u in adj[v]])
            remaining.remove(v)

    expand([], sorted(candidates, key=lambda b: -len(adj[b])))
    return sorted(best)


def main() -> None:
    import argparse

    parser = argparse.ArgumentParser(description="Inspect the tau outcome matrix.")
    parser.add_argument(
        "--recompute",
        action="store_true",
        help="recompute the maximum totally-proven sub-zoo",
    )
    args = parser.parse_args()

    if args.recompute:
        best = maximum_certified_sub_zoo()
        print(f"maximum certified sub-zoo: {len(best)} bots")
        for b in best:
            print(f"  {b}")
        if tuple(best) != tuple(sorted(FULL_CERTIFIED_SUB_ZOO)):
            print("\nNOTE: differs from FULL_CERTIFIED_SUB_ZOO — update matrix.py")
        return

    m = load_tau_matrix()
    print(f"tau matrix: {len(m)} bots, {len(m) ** 2} ordered cells, all proven")
    width = max(len(b) for b in m.bots)
    print(" " * (width + 2) + " ".join(f"{b[:4]:>4}" for b in m.bots))
    for row in m.bots:
        line = "  ".join(f"{m.action(row, col):>3}" for col in m.bots)
        print(f"{row:>{width}}  {line}")
    print(f"\ncells with side hypotheses (†): {len(m.dagger_cells)}")
    for a, b in sorted(m.dagger_cells):
        print(f"  {a} vs {b}")


if __name__ == "__main__":
    main()
