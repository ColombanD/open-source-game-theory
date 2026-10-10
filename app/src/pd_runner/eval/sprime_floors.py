"""The HINGE SIDE of the 26 PA-`S'` floor dichotomies (`FloorPolicy.hinge_side`, 2026-10-09).

A `S'` floor cell is a hypothesis-free dichotomy `dich_<L>_vs_<R>` (`arith/ArithS/Cells/
FloorDichotomy.lean`, sharpened in `Cells/PrudentLoose.lean` where `Outcome/Floors.lean` says
so): under `¬A_k` — the outer guard NOT provable within budget — the pair takes the ENGINE's
value (the `+k` floor stipulation, `FloorPolicy.engine_side`, what the export carries as
`pair`); under `A_k` it takes the other branch. `A_k` is inter-derivable with bounded
consistency of `TAct` at `k ± c`, open in both directions, so the engine-side experiments are
CONDITIONAL on one proof-complexity question. This table is the other answer.

**Convention.** `HINGE_SIDE_PAIRS[dich]` is the branch in which EVERY box hypothesis of the
dichotomy statement is TRUE (the outer hinge and, where the statement nests a partner's own
guard under `¬outer`, those too). It is the exact mirror of the engine side (every box
false): the two are the extreme worlds and bracket every mixed assignment. For the 17
single-hinge cells there is nothing to choose; for the 9 nested cells the all-true branch
is the outer-true branch, which the statements settle outright.

**Provenance.** Values are read off the `dich_` statements that `Outcome/Floors.lean` cites
(`FloorSpecA.of_dich …` / `obtain … := dich_…`), by `tests/test_floor_hinge_side.py`, which
re-parses those statements and asserts (a) the all-false branch equals the exported engine
pair and (b) the all-true branch equals this table — so the table cannot drift from Lean
unnoticed. It is NOT a theorem for one value any more than the engine side is: it is the
`A_k → …` half of each `dich_` theorem.

Keyed by the dichotomy name as exported (`floors[].dichotomy`), pair read from `<L>`'s side.
"""

from __future__ import annotations

HINGE_SIDE_PAIRS: dict[str, tuple[str, str]] = {
    # ── single hinge: the floor guard provable ⇒ the searcher cooperates ──
    "dich_DupocBot_vs_DBot": ("C", "C"),            # engine (D, C)
    "dich_DupocBot_vs_EBot": ("C", "C"),            # engine (D, C)
    "dich_DupocBot_vs_CupodTrollBot": ("C", "C"),   # engine (D, C)
    "dich_JustBot_vs_DBot": ("C", "C"),             # engine (D, C)
    "dich_JustBot_vs_EBot": ("C", "C"),             # engine (D, C)
    "dich_JustBot_vs_CupodTrollBot": ("C", "C"),    # engine (D, C)
    "dich_CIMCIC_vs_CupodTrollBot": ("C", "C"),     # engine (D, C)
    "dich_CIMCIC_vs_DBot": ("C", "C"),              # engine (D, C)
    "dich_CIMCIC_vs_EBot": ("C", "C"),              # engine (D, C)
    "dich_GuardianBot_vs_CIMCIC": ("C", "C"),       # engine (C, D)
    "dich_GuardianBot_vs_DupocBot": ("C", "C"),     # engine (C, D)
    "dich_GuardianBot_vs_JustBot": ("C", "C"),      # engine (C, D)
    "dich_CupodBot_vs_OBot": ("D", "D"),            # engine (C, D): Cupod's defection detector fires
    "dich_PrudentBot_vs_DupocBot": ("C", "C"),      # engine (D, D)
    "dich_PrudentBot_vs_PrudentBot": ("C", "C"),    # engine (D, D)
    "dich_PrudentBot_vs_EBot": ("C", "C"),          # engine (D, C), via dich_PrudentBot_vs_EBot_full
    # ── nested: the outer hinge true settles the pair outright ──
    "dich_JustBot_vs_PrudentBot": ("C", "C"),       # engine (D, D)
    "dich_CIMCIC_vs_PrudentBot": ("C", "C"),        # engine (D, D)
    "dich_GuardianBot_vs_PrudentBot": ("D", "D"),   # engine (C, D), via …_prudenceFound
    "dich_WaryBot_vs_DupocBot": ("D", "D"),         # engine (C, D)
    "dich_WaryBot_vs_JustBot": ("C", "C"),          # engine (C, D)
    "dich_WaryBot_vs_PrudentBot": ("C", "C"),       # engine (C, D), via …_prudenceFound
    "dich_CupodBot_vs_PrudentBot": ("D", "D"),      # engine (C, D), via …_prudenceFound
    "dich_PrudentBot_vs_CupodBot": ("D", "D"),      # engine (D, C), via …_prudenceFound
    "dich_JustBot_vs_CupodBot": ("C", "C"),         # engine (D, C)
    "dich_CIMCIC_vs_CupodBot": ("C", "C"),          # engine (D, C)
}


def hinge_side_pair(dichotomy: str, theorem: str = "") -> tuple[str, str]:
    """The `A_k` branch of `dichotomy`, or a `KeyError` naming the floor theorem — a
    floor the export knows and this table does not is a new dichotomy in Lean that
    nobody has read the other branch of yet; never default it."""
    try:
        return HINGE_SIDE_PAIRS[dichotomy]
    except KeyError:
        raise KeyError(
            f"no hinge-side value recorded for floor {theorem or '?'} ({dichotomy!r}); "
            "read its `dich_` statement and add the all-boxes-true branch to "
            "`eval/sprime_floors.HINGE_SIDE_PAIRS`"
        ) from None
