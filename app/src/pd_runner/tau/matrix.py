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
   Cell `shape` and `staggered` are retained for sensitivity analysis.
"""

from __future__ import annotations

from dataclasses import dataclass, field
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
#
# PrudentBot joined the exclusions on 2026-08-27, when the matrix cells became
# the SHARED-budget values: its only same-budget cooperation is with MirrorBot
# (excluded here), so on this zoo single-tier PrudentBot is behaviorally
# DefectBot — the two staggered (C, C) cells (vs DupocBot, vs JustBot) had been
# the only thing separating them, and those are now `*_staggered` non-cell
# theorems. It stays in FULL_CERTIFIED_SUB_ZOO and the enlarged zoo.
#
# GuardianBot followed the same day, a CASCADE of that removal: GuardianBot and
# TitForTatBot differed only at the PrudentBot column (Guardian trusts Prudent,
# TFT does not), so without PrudentBot they are twins. TitForTatBot is kept (a
# canonical opponent, Critch's classical bot); GuardianBot, an LLM-generated
# norm enforcer, stays in the full/enlarged zoos.
_TWIN_EXCLUSIONS: tuple[str, ...] = ("LegibleBot", "JustBot", "PrudentBot", "GuardianBot")

# CupodBot is admitted to break the remaining twin group: it is the bot whose
# column separates {CooperateBot, CupodTrollBot}. It USED to cost a stipulated
# cell; since 2026-08-25 this dict is EMPTY and the default zoo is fully proven.
#
# HISTORY. The red cell ("CupodBot", "DupocBot") — Critch's open problem — left
# on 2026-08-20 when `outcome_DupocBot_vs_CupodBot = (D, C)` was proven via the
# τ-transposition (`Base/Transpose.lean`). ("PrudentBot", "CupodBot") = (D, C)
# left on 2026-08-25 when `outcome_PrudentBot_vs_CupodBot` landed at every same
# budget — two else-play floors facing each other, the tau layer's argument
# (`cupod_prudent_plays_C`/`prudent_cupod_plays_D`) transplanted to the base
# shape. Both times the proven value matched the stipulation, and both times the
# loader's guard against a stipulation shadowing a proven cell forced the removal.
CUPOD_STIPULATIONS: dict[tuple[str, str], tuple[str, str]] = {}

# The default tau zoo: 9 bots (11 until 2026-08-27), NO behavioral twins,
# transparency ceiling exactly 1.0 — every bot is identifiable from behavior alone, and every cell is
# a kernel theorem. Load it with `load_tau_matrix()`.
CERTIFIED_SUB_ZOO: tuple[str, ...] = tuple(
    sorted(
        [b for b in FULL_CERTIFIED_SUB_ZOO if b not in _TWIN_EXCLUSIONS]
        + ["CupodBot"]
    )
)

# The fully-proven fallback: no stipulated cells, but 8 bots (10 until
# 2026-08-27) and a residual {CooperateBot, CupodTrollBot} twin pair holding the
# ceiling below 1.0. Use when a result must rest on the Lean kernel alone.
PROVEN_ONLY_SUB_ZOO: tuple[str, ...] = tuple(
    b for b in FULL_CERTIFIED_SUB_ZOO if b not in _TWIN_EXCLUSIONS
)

# The eight types the standalone `egt-osgt` repo analysed, kept so its
# published results stay reproducible against the certified matrix rather than
# against its hand-transcribed CSV.
#
# HISTORY: the cell `(CupodBot, DupocBot)` — the one Critch et al. leave
# unresolved and the standalone repo marked red and imputed from `config.json`
# — was for a long time this zoo's only hole (a nice independent confirmation
# that the gap was in the THEORY, not in either transcription). It is PROVEN
# since 2026-08-20 (`outcome_DupocBot_vs_CupodBot`, the τ-transposition
# route), with the value the standalone repo had imputed; this zoo is now
# fully proven with no stipulations.
CRITCH8_SUB_ZOO: tuple[str, ...] = (
    "CooperateBot",
    "CupodBot",
    "DBot",
    "DefectBot",
    "DupocBot",
    "OBot",
    "TitForTatBot",
    "EBot",
)

# Where the standalone repo's hand-transcribed matrix DISAGREES with the Lean
# library, measured 2026-08-10 against `egt-osgt-main/data/payoff_matrix.csv`
# as of commit bb51559: 56 of 62 filled cells agree, these 6 do not.
#
# `standalone` is what that CSV said; `certified` is what the theorem library
# proves. Four of the six are `dagger` cells — proven under a side hypothesis,
# so a reader comparing them should check the theorem's premises rather than
# assume a transcription slip. The `DBot`/`DupocBot` pair is NOT: those are
# plain universal theorems, so the CSV is simply wrong there.
#
# Kept as data rather than prose because the honest use of this zoo is
# "reproduce the standalone analysis and explain the delta", and that needs
# the delta enumerated.
CRITCH8_TRANSCRIPTION_DIFFS: dict[tuple[str, str], dict[str, tuple[str, str]]] = {
    ("CupodBot", "OBot"): {"standalone": ("D", "D"), "certified": ("C", "D")},
    ("OBot", "CupodBot"): {"standalone": ("D", "D"), "certified": ("D", "C")},
    ("DBot", "DupocBot"): {"standalone": ("C", "C"), "certified": ("C", "D")},
    ("DupocBot", "DBot"): {"standalone": ("C", "C"), "certified": ("D", "C")},
    ("DupocBot", "EBot"): {"standalone": ("C", "C"), "certified": ("D", "C")},
    ("EBot", "DupocBot"): {"standalone": ("C", "C"), "certified": ("C", "D")},
}

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
    # 2026-08-21: the last two DIMCID entries fell to theorems, again predicted
    # by the tau layer's ALIGNMENT RULE. `outcome_DIMCID_vs_CupodBot = (D, D)`
    # (ALIGNED — mutual bounded Löb on defection) confirmed its stipulation;
    # `outcome_DIMCID_vs_DupocBot = (C, D)` (ANTI-aligned — the floor forces both
    # defaults) FALSIFIED its `(D, D)`, the second wrong guess this method has
    # caught after `("CIMCIC", "CupodBot")`.
    # DIMCID vs CupodTrollBot was stipulated (C, C) here until 2026-08-04, when
    # `llm_outcome_DIMCID_vs_CupodTrollBot` landed proving exactly that. The
    # entry is gone rather than kept-and-ignored: the loader raises on a
    # stipulation shadowing a proven cell, which is how this was caught.
    # 2026-08-21: THREE more entries fell to theorems, all predicted by the tau
    # layer's entangled closures — `outcome_JustBot_vs_CupodBot = (D, C)` (as
    # stipulated), `outcome_CIMCIC_vs_OBot = (D, D)` (as stipulated), and
    # `outcome_CIMCIC_vs_CupodBot = (D, C)` — which FALSIFIED the (C, C) this
    # table had guessed: the (C, C) fixpoint is provability-inconsistent (Cupod's
    # trust is an else-play at every budget, so CIMCIC's search can never cite
    # it). Enlarged-zoo analyses run before this date were conditional on a
    # wrong cell.
}


@dataclass(frozen=True)
class NativePlayer:
    """A tau player that is NOT the lift of a base bot (2026-08-27).

    A tau player is a (per-hypothesis TEST, AGGREGATOR) pair. Every lift's test is
    its base bot's decision procedure and its aggregator is `sum ≥ α` (the C-mass
    of the signal). A NATIVE player borrows a base bot's test and aggregates
    differently — ConfidenceBot thresholds the MAX weight any single cooperating
    hypothesis carries (`play.max_mass`, Lean `Tau/Vote.lean::maxPlayer`).

    Two consequences the zoo registry relies on:

    * **As a HYPOTHESIS it IS its base bot.** What an opponent sees at point mass is
      the test alone (the aggregator is invisible there — the anchor), and the
      kernel certifies it: `Tau/Roster.lean` carries a `.confidence` slot whose row
      equals `dupocRow` and whose column equals every row's `.dupoc` bit
      (`confidenceRow_eq_dupocRow`, the `rfl` bridges in `Zoo.lean`; checked against
      the base matrix by `compare.direct_kernel_vs_base` via `BASE_OF`). So its
      matrix cells are a CLONE of its base's — `load_tau_matrix` builds them so and
      marks them `clone_of`.
    * **It is therefore a behavioral (and syntactic) twin of its base**, which caps
      the transparency ceiling of the distance-based σ families on any zoo holding
      both; the `epsilon` family is identity-based and unaffected. That is not a
      defect to prune away: for t < 1 the blur splits mass between the twins, and
      what that costs a MAX aggregator is exactly the phenomenon ConfidenceBot
      exists to measure.
    """

    name: str
    base: str
    """The base bot whose test it uses — and whose instance it is as a hypothesis."""
    aggregator: str
    """`"max"` — see `play.decision_mass`. Lifts are `"sum"`."""
    description: str


NATIVE_PLAYERS: dict[str, NativePlayer] = {
    "ConfidenceBot": NativePlayer(
        name="ConfidenceBot",
        base="DupocBot",
        aggregator="max",
        description=(
            "The ambiguity-averse Löbian cooperator: cooperate iff some SINGLE "
            "hypothesis carrying at least α of the signal on its own provably "
            "cooperates with me (Dupoc's test under the MAX aggregator). Lean: "
            "`Tau/Bots/TauConfidence.lean`, `ConfidenceBotZ`, `tauConfidence_phase`, "
            "`confidence_not_linear`."
        ),
    ),
}
"""The native players the zoo registry may admit, by name. Any zoo bot named here
is loaded as a clone of its base's cells and played with its own aggregator."""


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
    # Cells forced to a value that CONTRADICTS the Lean library. Empty for
    # every real zoo; non-empty only for replay zoos that exist to reproduce
    # an external dataset (see `superficial-standalone`). Kept separate from
    # `stipulations` — which may only ever fill a genuine hole — so the two
    # can never be confused, and so `load_tau_matrix`'s guard against
    # shadowing a proven cell stays intact.
    contradictions: dict[tuple[str, str], tuple[str, str]] = field(
        default_factory=dict
    )

    @property
    def contradicts_the_kernel(self) -> bool:
        """True for replay zoos whose cells are knowingly wrong."""
        return bool(self.contradictions)

    @property
    def natives(self) -> tuple[str, ...]:
        """The members that are NATIVE players (`NATIVE_PLAYERS`), not lifts."""
        return tuple(b for b in self.bots if b in NATIVE_PLAYERS)

    def load(self, theorems_dir: Path | None = None) -> TauMatrix:
        matrix = load_tau_matrix(
            self.bots,
            theorems_dir=theorems_dir,
            hypothetical_cells=self.stipulations,
        )
        if self.contradictions:
            matrix = apply_contradictions(matrix, self.contradictions)
        return matrix


# Selectable zoos, in presentation order (default first).
ZOOS: dict[str, NamedZoo] = {
    "default": NamedZoo(
        key="default",
        label="default (9 bots, twin-free)",
        description=(
            "The twin-free working zoo: transparency ceiling exactly 1.0, so "
            "every bot is identifiable from behavior alone. Conditional on the "
            "two CupodBot stipulations."
        ),
        bots=CERTIFIED_SUB_ZOO,
        stipulations=CUPOD_STIPULATIONS,
    ),
    "default+confidence": NamedZoo(
        key="default+confidence",
        label="default + ConfidenceBot (10 members, 1 native)",
        description=(
            "The twin-free default zoo plus ConfidenceBot, the first NATIVE tau "
            "player: Dupoc's Löbian test under the MAX aggregator — cooperate iff "
            "some single hypothesis carrying at least α of the signal on its own "
            "provably cooperates with me. As a HYPOTHESIS it is Dupoc's instance "
            "(a kernel-certified clone), hence a behavioral twin of DupocBot: the "
            "behavioral and syntactic σ families have a transparency ceiling below "
            "1 on this zoo and split mass between the twins for t < 1 — the cost of "
            "ambiguity aversion to a Löbian cooperator, which is the point. The "
            "epsilon family is identity-based and has no ceiling."
        ),
        bots=CERTIFIED_SUB_ZOO + ("ConfidenceBot",),
        stipulations=CUPOD_STIPULATIONS,
    ),
    "enlarged": NamedZoo(
        key="enlarged",
        label="enlarged (16 bots, stipulated)",
        description=(
            "The widest zoo: adds the behavioral twins (LegibleBot, JustBot), "
            "the search×search frontier bots (CIMCIC, DIMCID) and MirrorBot, "
            "whose proven-`none` self-play is the 'N' state. Most conditional "
            "— 7 stipulated pairs."
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
    "critch8": NamedZoo(
        key="critch8",
        label="critch8 (8 bots, the standalone-repo zoo)",
        description=(
            "The eight types the standalone egt-osgt repo analysed. Fully "
            "proven since 2026-08-20: its former one hole — (CupodBot, "
            "DupocBot), the 'red cell' Critch et al. left open — is now a "
            "theorem (outcome_DupocBot_vs_CupodBot, the τ-transposition "
            "route), with the value that repo's config.json had imputed. "
            "NOTE: this zoo does NOT reproduce that repo's numbers. Its "
            "hand-transcribed matrix disagrees with the Lean library on 6 of "
            "62 cells, so the analyses will differ — see "
            "CRITCH8_TRANSCRIPTION_DIFFS."
        ),
        bots=CRITCH8_SUB_ZOO,
        stipulations={
            k: v for k, v in CUPOD_STIPULATIONS.items()
            if k[0] in CRITCH8_SUB_ZOO and k[1] in CRITCH8_SUB_ZOO
        },
    ),
    "superficial-standalone": NamedZoo(
        key="superficial-standalone",
        label="superficial standalone (8 bots, KNOWINGLY WRONG)",
        description=(
            "A VALIDATION ZOO, not a result. Same eight types as critch8, but "
            "six cells are forced to the values in the standalone repo's "
            "hand-transcribed CSV — values the Lean library proves are WRONG. "
            "Its only purpose is to feed this pipeline exactly the input that "
            "repo used, so any remaining difference in the analysis isolates "
            "to the implementation rather than to the data. Never cite a "
            "number from this zoo as a finding."
        ),
        bots=CRITCH8_SUB_ZOO,
        stipulations={
            k: v for k, v in CUPOD_STIPULATIONS.items()
            if k[0] in CRITCH8_SUB_ZOO and k[1] in CRITCH8_SUB_ZOO
        },
        # The standalone side of every disagreement. One key per unordered
        # pair — `apply_contradictions` derives the transpose, so the replay
        # cannot become internally inconsistent.
        contradictions={
            pair: diff["standalone"]
            for pair, diff in CRITCH8_TRANSCRIPTION_DIFFS.items()
            if pair in (("CupodBot", "OBot"), ("DBot", "DupocBot"),
                        ("DupocBot", "EBot"))
        },
    ),
    "proven-only": NamedZoo(
        key="proven-only",
        label="proven only (8 bots, kernel-clean)",
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
    # "universal" | "threshold" (∃k₂, ∀k>k₂) | "no_outcome"
    # | "HYPOTHETICAL" | "CONTRADICTED"
    # | "no_outcome" (proven `= none` — the "N" cells)
    # | "HYPOTHETICAL" (stipulated, NOT proven — see `hypothetical`)
    shape: str
    # Proved under extra side hypotheses (floor/size/budget guards) — the `†`
    # cells. Tracked so a sweep can report how much probability mass rests on
    # them and be re-run without them.
    staggered: bool
    # True when this cell was read off the REVERSED theorem (outcome_col_vs_row)
    # and swapped. Not a defect — the game is symmetric in the sense that
    # `outcome A B = (a, b)` iff `outcome B A = (b, a)` — but worth auditing.
    swapped: bool
    theorem: str
    # True when this cell was STIPULATED via `hypothetical_cells`, not proven
    # by the Lean kernel. Any result computed over a matrix containing these is
    # conditional on the stipulation and must be reported as such.
    hypothetical: bool = False
    # Set when this cell belongs to a NATIVE player and was CLONED from its base's
    # cell: the `(base_row, base_col)` it copies (`NativePlayer`). The proof is the
    # base cell's; the kernel certifies the clone through the tau roster.
    clone_of: tuple[str, str] | None = None


class TauMatrix:
    """A totally-proven ordered outcome table over a fixed bot list."""

    def __init__(
        self,
        bots: tuple[str, ...],
        cells: dict[tuple[str, str], Cell],
        natives: dict[str, NativePlayer] | None = None,
    ):
        self.bots = bots
        self._cells = cells
        # The native players among `bots`, by name (empty for a pure base zoo).
        self.natives: dict[str, NativePlayer] = dict(natives or {})

    def aggregator(self, actor: str) -> str:
        """How `actor` thresholds its signal: `"sum"` (a lift — the C-mass) or a
        native player's own aggregator (`"max"`). See `play.decision_mass`."""
        native = self.natives.get(actor)
        return native.aggregator if native is not None else "sum"

    def source_bot(self, bot: str) -> str:
        """The base bot whose SOURCE `bot` presents in the hypothesis role — itself,
        or a native player's base (`NativePlayer.base`)."""
        native = self.natives.get(bot)
        return native.base if native is not None else bot

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
        return tuple(k for k, c in self._cells.items() if c.staggered)

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

    # NATIVE players (`NATIVE_PLAYERS`) have no theorems of their own: in the
    # hypothesis role each IS its base bot's instance, so its cells are CLONED from
    # the base's — looked up by base names, stored under the native's name, marked
    # `clone_of`. A native's base need not itself be in the zoo.
    natives = {b: NATIVE_PLAYERS[b] for b in bots if b in NATIVE_PLAYERS}
    base_of = {b: (natives[b].base if b in natives else b) for b in bots}

    for row in bots:
        for col in bots:
            brow, bcol = base_of[row], base_of[col]
            clone = (brow, bcol) if (brow, bcol) != (row, col) else None
            forward = by_pair.get((brow, bcol))
            reverse = by_pair.get((bcol, brow))

            # Cross-check both orientations when both exist. A proven `none`
            # (pair is None) transposes to itself, so the orientations must
            # agree on none-ness as well as on the actions.
            if forward is not None and reverse is not None and brow != bcol:
                fp, rp = forward.pair, reverse.pair
                if (fp is None) != (rp is None) or (
                    fp is not None and rp is not None and fp != (rp[1], rp[0])
                ):
                    conflicts.append((row, col))

            chosen, swapped = (forward, False) if forward is not None else (reverse, True)

            if chosen is not None:
                # A stipulation must never contradict the kernel — including a
                # proven `none`, which is a real value ("N"), not a hole.
                if (brow, bcol) in stipulated or (bcol, brow) in stipulated:
                    overridden.append((brow, bcol))
            else:
                # No proof: fall back to a stipulation if one was supplied,
                # accepting it in either orientation and transposing as needed.
                pair = stipulated.get((brow, bcol))
                if pair is None:
                    flipped = stipulated.get((bcol, brow))
                    pair = (flipped[1], flipped[0]) if flipped else None
                if pair is None:
                    missing.append((row, col))
                    continue
                cells[(row, col)] = Cell(
                    row_action=pair[0],
                    col_action=pair[1],
                    shape="HYPOTHETICAL",
                    staggered=False,
                    swapped=False,
                    theorem=f"(stipulated {brow} vs {bcol})",
                    hypothetical=True,
                    clone_of=clone,
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
                staggered=chosen.staggered,
                swapped=swapped,
                theorem=chosen.name,
                clone_of=clone,
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
    return TauMatrix(bots, cells, natives)


def apply_contradictions(
    matrix: TauMatrix,
    contradictions: dict[tuple[str, str], tuple[str, str]],
) -> TauMatrix:
    """Force cells to values that CONTRADICT the Lean library.

    This is not `hypothetical_cells`, and must not be confused with it. A
    stipulation fills a genuine hole; this deliberately overwrites a proven
    theorem with a different answer. There is exactly one legitimate use:
    replaying an EXTERNAL dataset through this pipeline so that a difference
    in results isolates to the implementation rather than to the input.

    Every touched cell is marked `hypothetical`, so `is_fully_proven` goes
    False and the whole downstream stack — the reports' "conditional" banners,
    the EGT provenance blocks — already treats the result as untrustworthy
    without needing to know why.

    Each entry is applied in BOTH orientations from a single key, so a replay
    matrix can never end up internally inconsistent in a way the source data
    was not.
    """
    cells = dict(matrix._cells)
    unknown: list[tuple[str, str]] = []

    for (row, col), pair in contradictions.items():
        if (row, col) not in cells:
            unknown.append((row, col))
            continue
        cells[(row, col)] = Cell(
            row_action=pair[0],
            col_action=pair[1],
            shape="CONTRADICTED",
            staggered=False,
            swapped=False,
            theorem=f"(contradicts the library: {row} vs {col})",
            hypothetical=True,
        )
        if row != col and (col, row) in cells:
            cells[(col, row)] = Cell(
                row_action=pair[1],
                col_action=pair[0],
                shape="CONTRADICTED",
                staggered=False,
                swapped=True,
                theorem=f"(contradicts the library: {row} vs {col})",
                hypothetical=True,
            )

    if unknown:
        raise ValueError(
            "contradictions name cells outside this zoo: "
            f"{sorted(unknown)}. The bot list and the override set must agree."
        )
    return TauMatrix(matrix.bots, cells, matrix.natives)


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
