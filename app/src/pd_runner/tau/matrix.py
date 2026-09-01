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
   (N, N) base cell as neither. No registered zoo carries MirrorBot; pass an
   explicit roster to `load_tau_matrix` to get the "N" state.
1b. **Behavioral twins** — the default roster (`PAPER_BODY_SUB_ZOO`) excludes
   every bot behaviorally identical to another member, since twins cap the
   transparency scale; see the paper-zoo design record below.
1c. **The Def-4 substrate (2026-09-01).** The tau lift PLAYS from the kernel
   rows: `TauMatrix.test_bit` reads each member's `@[tau_row]` RowSpec bits
   (`tau_rows.json`, via `def4_theorems.kernel_row_bits`), verified against the
   base cells at load time, with base cells as the fallback for template-less
   bots (`is_kernel_backed` reports which). Values never change — Def 3 ≡ Def 4
   is certified — only the provenance does; `action()` stays the base-cell
   reading for payoffs, display, and the replay zoos.
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

# The maximum sub-zoo whose induced ORDERED submatrix is totally proven,
# recomputed 2026-09-01: 15 bots, 225/225 cells, zero orientation conflicts,
# zero stipulations. Recompute with `python -m pd_runner.tau.matrix
# --recompute` after proving new cells.
#
# Excluded and why: MirrorBot (self-play is a proven `none` — the "N" state,
# not an action pair), and the still-open frontier — WaryBot (the .neg-guard
# refutation-floor census wall) and OptimBot (self-play unproven, two-budget
# box guard). The 2026-08 frontier closures (CupodBot, CIMCIC, DIMCID) all
# landed, so this roster is no longer biased toward the easy half of the zoo.
FULL_CERTIFIED_SUB_ZOO: tuple[str, ...] = (
    "CIMCIC",
    "CooperateBot",
    "CupodBot",
    "CupodTrollBot",
    "DBot",
    "DIMCID",
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

# ---------------------------------------------------------------------------
# The three PAPER zoos (frozen 2026-09-01) — the rosters the paper's
# experiments run on, enumerated explicitly so the frozen roster is the
# literal text of this file, not the output of a derivation. Design record:
#
# * BODY (10) — twin-free, fully proven, zero daggers, zero stipulations
#   (checked 2026-09-01: 100/100 ordered cells). Twin-free ⇒ the behavioral
#   transparency scale spans [0, 1], which the headline dial, the anchor and
#   the degradation curves all require. Membership notes:
#   - DIMCID is in: the one hard-fragment (search×search) bot that is both
#     fully proven and twin-free (nearest neighbour CupodBot at behavioral
#     distance 1 — the CupodTrollBot column separates them).
#   - CupodBot is in to SEPARATE {CooperateBot, CupodTrollBot} (its column
#     splits them, `outcome_CupodTrollBot_vs_CupodBot`). Its once-stipulated
#     cells are theorems since 2026-08-25 (the red cell fell 2026-08-20 via
#     the τ-transposition).
#   - Out as behavioral twins: LegibleBot & JustBot (≡ CooperateBot / DupocBot,
#     2026-08-03), PrudentBot (≡ DefectBot under the shared-budget cell
#     convention, 2026-08-27), GuardianBot (≡ TitForTatBot once PrudentBot
#     left — they differed only at his column), CIMCIC (≡ DupocBot by
#     theorem). Out for open/none cells: MirrorBot, WaryBot, OptimBot.
#
# * BODY+TWINS (12) adds CIMCIC and PrudentBot — twins ON PURPOSE. The
#   behavioral σ ceiling < 1 here is the MEASUREMENT, not a defect: both
#   pairs are syntactically far apart (normalized AST distance 3.57 / 8.82),
#   so this zoo serves the cross-family confusion-structure analysis
#   (behavioral vs syntactic at matched MI), never headline curves. Checked
#   2026-09-01: 144/144 proven, twin groups exactly {CIMCIC, DupocBot} and
#   {DefectBot, PrudentBot}.
#
# * BODY+NATIVES (14) adds the two native aggregator players over Dupoc's
#   test — MaxConfidenceBot (max) and MinConfidenceBot (min) — for the
#   aggregator ablation {sum, max, min} = {expectation, best case, worst
#   case}. Natives are Dupoc twins in the hypothesis role (clones), so run
#   this zoo on the EPSILON family, which is identity-based and has no twin
#   ceiling.
PAPER_BODY_SUB_ZOO: tuple[str, ...] = (
    "CooperateBot",
    "CupodBot",
    "CupodTrollBot",
    "DBot",
    "DIMCID",
    "DefectBot",
    "DupocBot",
    "EBot",
    "OBot",
    "TitForTatBot",
)
PAPER_TWINS_SUB_ZOO: tuple[str, ...] = (
    "CIMCIC",
    "CooperateBot",
    "CupodBot",
    "CupodTrollBot",
    "DBot",
    "DIMCID",
    "DefectBot",
    "DupocBot",
    "EBot",
    "OBot",
    "PrudentBot",
    "TitForTatBot",
)
PAPER_NATIVES_SUB_ZOO: tuple[str, ...] = (
    "CIMCIC",
    "CooperateBot",
    "CupodBot",
    "CupodTrollBot",
    "DBot",
    "DIMCID",
    "DefectBot",
    "DupocBot",
    "EBot",
    "MaxConfidenceBot",
    "MinConfidenceBot",
    "OBot",
    "PrudentBot",
    "TitForTatBot",
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

@dataclass(frozen=True)
class NativePlayer:
    """A tau player that is NOT the lift of a base bot (2026-08-27).

    A tau player is a (per-hypothesis TEST, AGGREGATOR) pair. Every lift's test is
    its base bot's decision procedure and its aggregator is `sum ≥ α` (the C-mass
    of the signal). A NATIVE player borrows a base bot's test and aggregates
    differently — MaxConfidenceBot thresholds the MAX weight any single cooperating
    hypothesis carries (`play.max_mass`, Lean `Tau/Vote.lean::maxPlayer`).

    Two consequences the zoo registry relies on:

    * **As a HYPOTHESIS it IS its base bot.** What an opponent sees at point mass is
      the test alone (the aggregator is invisible there — the anchor), and the
      kernel certifies it: `Tau/Roster.lean` carries a `.maxconfidence` slot whose row
      equals `dupocRow` and whose column equals every row's `.dupoc` bit
      (`maxconfidenceRow_eq_dupocRow`, the `rfl` bridges in `Zoo.lean`; checked against
      the base matrix by `compare.direct_kernel_vs_base` via `BASE_OF`). So its
      matrix cells are a CLONE of its base's — `load_tau_matrix` builds them so and
      marks them `clone_of`.
    * **It is therefore a behavioral (and syntactic) twin of its base**, which caps
      the transparency ceiling of the distance-based σ families on any zoo holding
      both; the `epsilon` family is identity-based and unaffected. That is not a
      defect to prune away: for t < 1 the blur splits mass between the twins, and
      what that costs a MAX aggregator is exactly the phenomenon MaxConfidenceBot
      exists to measure.
    """

    name: str
    base: str
    """The base bot whose test it uses — and whose instance it is as a hypothesis."""
    aggregator: str
    """`"max"` or `"min"` — see `play.decision_mass`. Lifts are `"sum"`."""
    description: str


NATIVE_PLAYERS: dict[str, NativePlayer] = {
    "MaxConfidenceBot": NativePlayer(
        name="MaxConfidenceBot",
        base="DupocBot",
        aggregator="max",
        description=(
            "The ambiguity-averse Löbian cooperator: cooperate iff some SINGLE "
            "hypothesis carrying at least α of the signal on its own provably "
            "cooperates with me (Dupoc's test under the MAX aggregator). Lean: "
            "`Tau/Bots/TauMaxConfidence.lean`, `MaxConfidenceBotZ`, `tauMaxConfidence_phase`, "
            "`maxconfidence_not_linear`."
        ),
    ),
    "MinConfidenceBot": NativePlayer(
        name="MinConfidenceBot",
        base="DupocBot",
        aggregator="min",
        description=(
            "MaxConfidenceBot's C/D-transposition dual, the Gilboa–Schmeidler "
            "pessimist: cooperate iff NO single hypothesis carrying more than "
            "1−α of the signal on its own provably defects against me — every "
            "hypothesis above that credibility must pass Dupoc's test (the MIN "
            "/ worst-case aggregator, `play.min_mass`). Lean: "
            "`Tau/Bots/TauMinConfidence.lean`, `MinConfidenceBotZ`, "
            "`tauMinConfidence_phase`, `minconfidence_not_linear`; roster slot "
            "`.minconfidence`, kernel row `minconfidenceRowSpec` (= dupocRow, "
            "certified via BASE_OF like MaxConfidenceBot's)."
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


# Selectable zoos, in presentation order: the three paper zoos first (body is
# the default), then the two replay zoos kept for reproduction/validation of
# the standalone egt-osgt repo. Retired 2026-09-01 (superseded by the paper
# zoos; rosters recoverable from git): default, default+maxconfidence, enlarged,
# full-certified, proven-only.
ZOOS: dict[str, NamedZoo] = {
    "body": NamedZoo(
        key="body",
        label="body (10 bots, the paper zoo)",
        description=(
            "The paper's body zoo. Twin-free (behavioral transparency scale "
            "spans [0, 1]), fully proven, zero daggers — and DIMCID brings "
            "one hard-fragment search×search bot in against the easier-half "
            "bias. All headline experiments run here."
        ),
        bots=PAPER_BODY_SUB_ZOO,
        stipulations={},
    ),
    "body+twins": NamedZoo(
        key="body+twins",
        label="body + twins (12 bots, cross-family analysis)",
        description=(
            "Body + CIMCIC + PrudentBot, the two behavioral twins (of "
            "DupocBot and DefectBot respectively) that are syntactically far "
            "apart. The behavioral σ ceiling < 1 here is the MEASUREMENT, not "
            "a defect: this zoo exists for the behavioral-vs-syntactic "
            "confusion-structure comparison at matched MI, never for "
            "headline curves."
        ),
        bots=PAPER_TWINS_SUB_ZOO,
        stipulations={},
    ),
    "body+natives": NamedZoo(
        key="body+natives",
        label="body + twins + natives (14 bots, aggregator ablation)",
        description=(
            "Body+twins plus the two native aggregator players over Dupoc's "
            "test: MaxConfidenceBot (max) and MinConfidenceBot (min) — the "
            "{sum, max, min} ablation. Natives are Dupoc twins as "
            "hypotheses, so run this zoo on the epsilon family (identity-"
            "based, no twin ceiling)."
        ),
        bots=PAPER_NATIVES_SUB_ZOO,
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
        stipulations={},
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
        stipulations={},
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
}

DEFAULT_ZOO = "body"


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
        kernel_rows: dict[str, dict[str, str]] | None = None,
    ):
        self.bots = bots
        self._cells = cells
        # The native players among `bots`, by name (empty for a pure base zoo).
        self.natives: dict[str, NativePlayer] = dict(natives or {})
        # The Def-4 substrate (2026-09-01): per-actor kernel test bits, from the
        # `@[tau_row]` RowSpec theorems (`def4_theorems.kernel_row_bits`), restricted
        # to this zoo. `test_bit`/`cooperates` read these when present; the base
        # cells are the fallback for bots without a kernel row. `load_tau_matrix`
        # verifies every kernel bit against the base cell at load time, so the two
        # sources can never silently disagree. A matrix built by
        # `apply_contradictions` carries NO kernel rows — a replay matrix is
        # knowingly wrong and must play from its contradicted cells.
        self.kernel_rows: dict[str, dict[str, str]] = dict(kernel_rows or {})

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
        """What `actor` plays in `outcome(actor, opponent)` — the Def 3 probe.

        This is the BASE-CELL reading (used for anchor payoffs, the matrix
        display, and the replay zoos); the tau lift's play thresholds `test_bit`
        instead, which prefers the kernel row.
        """
        return self.cell(actor, opponent).row_action

    def test_bit(self, actor: str, opponent: str) -> str:
        """`actor`'s per-hypothesis TEST bit at `opponent` — the quantity every
        aggregator (`sum`/`max`/`min`) is computed over.

        Def-4 substrate (2026-09-01): read from `actor`'s kernel-proven RowSpec
        row when the matrix carries one (load-time-verified equal to the base
        cell), else from the base cell — so the value never depends on the
        source, only the PROVENANCE does (`is_kernel_backed`)."""
        row = self.kernel_rows.get(actor)
        if row is not None and opponent in row:
            return row[opponent]
        return self.action(actor, opponent)

    def cooperates(self, actor: str, opponent: str) -> bool:
        return self.test_bit(actor, opponent) == "C"

    @property
    def kernel_backed_bots(self) -> tuple[str, ...]:
        """The members whose whole test row comes from the kernel export."""
        return tuple(
            b for b in self.bots
            if b in self.kernel_rows
            and all(h in self.kernel_rows[b] for h in self.bots)
        )

    @property
    def is_kernel_backed(self) -> bool:
        """True when EVERY member's test row is kernel-backed — the state of all
        three paper zoos. False for ad-hoc rosters holding a template-less bot
        and for replay matrices (`apply_contradictions` drops the rows)."""
        return len(self.kernel_backed_bots) == len(self.bots)

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


def _kernel_rows_for(
    bots: tuple[str, ...], cells: dict[tuple[str, str], Cell]
) -> dict[str, dict[str, str]]:
    """The Def-4 substrate for one roster: each member's kernel RowSpec bits,
    restricted to the roster and VERIFIED against the base cells (2026-09-01).

    Three deliberate behaviors:

    * A missing export file degrades to `{}` (Def-3 fallback) rather than failing
      the load — but a PRESENT export that disagrees with the theorems on any
      proven cell raises, because that can only mean a stale `tau_rows.json`
      (run `lake exe export_outcomes`) or a genuine Def 3 ≢ Def 4 break, and
      either must be loud. (An out-of-order export already raises inside
      `kernel_bits`.)
    * A bot with no template gets no row — `is_kernel_backed` goes False, the
      bits fall back to base cells, numbers unchanged.
    * A STIPULATED cell keeps its stipulation: the kernel bit is dropped for that
      pair, so what-if analyses answer the question they were asked.
    """
    from pd_runner.tau.def4_theorems import kernel_row_bits

    try:
        all_rows = kernel_row_bits()
    except FileNotFoundError:
        return {}
    rows: dict[str, dict[str, str]] = {}
    mismatches: list[str] = []
    for b in bots:
        full = all_rows.get(b)
        if full is None:
            continue
        row: dict[str, str] = {}
        for h in bots:
            if h not in full:
                continue
            cell = cells.get((b, h))
            if cell is None or cell.hypothetical:
                continue
            if full[h] != cell.row_action:
                mismatches.append(
                    f"{b} vs {h}: kernel row says {full[h]!r}, "
                    f"base cell ({cell.theorem}) says {cell.row_action!r}"
                )
            row[h] = full[h]
        rows[b] = row
    if mismatches:
        raise ValueError(
            "kernel tau rows disagree with the proven base cells — stale "
            "tau_rows.json (run `lake exe export_outcomes`) or a real "
            "Def 3 ≢ Def 4 break:\n  " + "\n  ".join(mismatches)
        )
    return rows


def load_tau_matrix(
    bots: tuple[str, ...] = PAPER_BODY_SUB_ZOO,
    theorems_dir: Path | None = None,
    hypothetical_cells: dict[tuple[str, str], tuple[str, str]] | None = None,
) -> TauMatrix:
    """Build the ordered outcome table, raising if any cell is unproven.

    Totality is enforced, not assumed: if a bot list is passed whose submatrix
    has a hole, this fails loudly rather than silently producing a tau layer
    with an implicit convention nobody chose. The default roster is the paper
    body zoo, which is fully proven — no stipulations needed or applied.

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
    stipulated = dict(hypothetical_cells) if hypothetical_cells is not None else {}

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
    return TauMatrix(bots, cells, natives, _kernel_rows_for(bots, cells))


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

    Used to refresh `FULL_CERTIFIED_SUB_ZOO` as new cells get proven. Excludes
    bots whose self-play cell is unproven or proven `none`.
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
