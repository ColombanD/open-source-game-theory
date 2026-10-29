"""`FloorPolicy.hinge_side` (2026-10-09): the OTHER branch of the 26 PA-`S'` floor dichotomies.

The engine-side experiments are conditional on `¬A_k` (the floor guard NOT provable within
budget — the engine's `+k` stipulation). `hinge_side` carries the `A_k` branch — every box
hypothesis of the `dich_` statement TRUE — so a run under both policies brackets what the open
bounded-consistency question can change. Tests:

* the committed table `eval/sprime_floors.HINGE_SIDE_PAIRS` is re-derived from the Lean
  statements `Outcome/Floors.lean` cites (a small parser over the `dich_` theorem statements),
  and the all-false branch of each equals the exported engine pair;
* the loaders carry the branch (`floor_branch`), never count a floor as a flip, and leave the
  kernel floor bits unstated;
* the EGT provenance (hash, run name, summary) separates the two branches.
"""

from __future__ import annotations

import json
import re
from pathlib import Path

import pytest

from pd_runner.eval import outcome_matrix as om
from pd_runner.eval.outcome_matrix import scan_outcome_theorems
from pd_runner.eval.sprime_floors import HINGE_SIDE_PAIRS, hinge_side_pair
from pd_runner.tau.matrix import PAPER_BODY_SUB_ZOO, PAPER_TWINS_SUB_ZOO, load_tau_matrix

ARITH = Path(__file__).resolve().parents[2] / "arith" / "ArithS"
DICH_SOURCES = (ARITH / "Cells" / "FloorDichotomy.lean", ARITH / "Cells" / "PrudentLoose.lean",
                ARITH / "Cells" / "DupocTrollBot.lean",  # the S'-only floor of DupocTrollBot (2026-10-13)
                ARITH / "Cells" / "Dimdid.lean")  # the three S'-only floors of DIMDID (2026-10-13)
FLOORS_LEAN = ARITH / "Outcome" / "Floors.lean"

needs_real_export = pytest.mark.skipif(
    not om._EXPORT_FILES["sprime"].exists(), reason="no S' export on disk")


# ── a tiny parser for the `dich_` statements ──────────────────────────────────────
#
# The statement body (after `∃ k₀, ∀ k, k₀ < k →`) is built from `LenBox TAct k (…)` atoms,
# `EvalGraph n (progCode L) (progCode R) (progCode L) (actCode .X)` atoms, `¬`, `∧`, `∨`, `→`
# and parentheses. We evaluate every box atom to one truth value and collect the EvalGraph
# facts that assignment forces.

_PROG = re.compile(r"\(progCode \(?([A-Za-z0-9]+)")


def _balanced(s: str, pos: int) -> int:
    depth = 0
    for i in range(pos, len(s)):
        if s[i] == "(":
            depth += 1
        elif s[i] == ")":
            depth -= 1
            if depth == 0:
                return i + 1
    raise ValueError("unbalanced parentheses")


def _tokenize(stmt: str) -> list[tuple[str, object]]:
    s = stmt.split("→", 1)[1]
    toks: list[tuple[str, object]] = []
    pos = 0
    while pos < len(s):
        ch = s[pos]
        if ch.isspace():
            pos += 1
        elif s.startswith("LenBox TAct k ", pos):
            end = _balanced(s, s.index("(", pos))
            toks.append(("BOX", s[pos:end]))
            pos = end
        elif s.startswith("EvalGraph", pos):
            end = s.index("(", pos)
            groups = []
            for _ in range(4):
                nxt = _balanced(s, end)
                groups.append(s[end:nxt])
                end = nxt
                while end < len(s) and s[end] == " ":
                    end += 1
            me = _PROG.match(groups[0]).group(1)  # type: ignore[union-attr]
            act = re.search(r"actCode \.([CD])", groups[3]).group(1)  # type: ignore[union-attr]
            toks.append(("EVAL", (me, act)))
            pos = end
        elif ch in "()¬∧∨→":
            toks.append((ch, ch))
            pos += 1
        else:
            raise ValueError(f"unexpected text {s[pos:pos + 40]!r}")
    return toks


class _Parser:
    # impl := disj ('→' impl)? ; disj := conj ('∨' conj)* ; conj := neg ('∧' neg)*
    # neg := '¬' neg | atom ; atom := BOX | EVAL | '(' impl ')'
    def __init__(self, toks):
        self.t = toks
        self.i = 0

    def peek(self):
        return self.t[self.i][0] if self.i < len(self.t) else None

    def eat(self, kind=None):
        tok = self.t[self.i]
        self.i += 1
        if kind is not None and tok[0] != kind:
            raise ValueError(f"expected {kind}, got {tok}")
        return tok

    def impl(self):
        left = self.disj()
        if self.peek() == "→":
            self.eat()
            return ("->", left, self.impl())
        return left

    def disj(self):
        left = self.conj()
        while self.peek() == "∨":
            self.eat()
            left = ("or", left, self.conj())
        return left

    def conj(self):
        left = self.neg()
        while self.peek() == "∧":
            self.eat()
            left = ("and", left, self.neg())
        return left

    def neg(self):
        if self.peek() == "¬":
            self.eat()
            return ("not", self.neg())
        return self.atom()

    def atom(self):
        kind, val = self.eat()
        if kind == "BOX":
            return ("box", val)
        if kind == "EVAL":
            return ("eval", val)
        if kind == "(":
            e = self.impl()
            self.eat(")")
            return e
        raise ValueError(f"unexpected token {kind}")


def _truth(e, val: bool) -> bool:
    k = e[0]
    if k == "box":
        return val
    if k == "not":
        return not _truth(e[1], val)
    if k == "or":
        return _truth(e[1], val) or _truth(e[2], val)
    if k == "and":
        return _truth(e[1], val) and _truth(e[2], val)
    raise ValueError(k)


def _forced(e, val: bool) -> set[tuple[str, str]]:
    k = e[0]
    if k == "eval":
        return {e[1]}
    if k == "and":
        return _forced(e[1], val) | _forced(e[2], val)
    if k == "->":
        return _forced(e[2], val) if _truth(e[1], val) else set()
    raise ValueError(k)


def _dich_statements() -> dict[str, str]:
    out: dict[str, str] = {}
    for f in DICH_SOURCES:
        for m in re.finditer(r"^theorem (dich_\w+) :\n(.*?):= by", f.read_text(encoding="utf-8"),
                             re.S | re.M):
            out[m.group(1)] = m.group(2)
    return out


def _dich_used_by_floors() -> dict[tuple[str, str], str]:
    """`(L, R) -> the dich_ theorem Outcome/Floors.lean proves the floor from`."""
    txt = FLOORS_LEAN.read_text(encoding="utf-8")
    used: dict[tuple[str, str], str] = {}
    for m in re.finditer(
            r"theorem outcome_(\w+?)_vs_(\w+?)_floor :(.*?)(?=\n@\[floorA\]|\nend ArithS)",
            txt, re.S):
        used[(m.group(1), m.group(2))] = re.search(r"(dich_\w+)", m.group(3)).group(1)  # type: ignore[union-attr]
    return used


def branches_from_lean() -> dict[str, tuple[tuple[str, str], tuple[str, str]]]:
    """`dich_<L>_vs_<R> -> (all-boxes-false pair, all-boxes-true pair)`, from Lean."""
    statements = _dich_statements()
    out = {}
    for (left, right), dich in _dich_used_by_floors().items():
        tree = _Parser(_tokenize(statements[dich])).impl()

        def pair(val: bool) -> tuple[str, str]:
            forced = dict(_forced(tree, val))
            return (forced[left], forced[right])

        out[f"dich_{left}_vs_{right}"] = (pair(False), pair(True))
    return out


# ── (a) the table is what Lean says ────────────────────────────────────────────────


@pytest.mark.skipif(not FLOORS_LEAN.exists(), reason="arith sources not on disk")
def test_hinge_side_table_matches_the_lean_dichotomies() -> None:
    lean = branches_from_lean()
    assert set(lean) == set(HINGE_SIDE_PAIRS), (
        "the floors Outcome/Floors.lean states and the hinge-side table disagree on the roster")
    for dich, (_engine, hinge) in lean.items():
        assert HINGE_SIDE_PAIRS[dich] == hinge, f"{dich}: Lean's A_k branch is {hinge}"


@pytest.mark.skipif(not FLOORS_LEAN.exists(), reason="arith sources not on disk")
@needs_real_export
def test_engine_side_branch_is_the_exported_pair() -> None:
    doc = json.loads(om._EXPORT_FILES["sprime"].read_text(encoding="utf-8"))
    exported = {f["dichotomy"]: tuple(f["pair"]) for f in doc["floors"]}
    lean = branches_from_lean()
    assert set(exported) == set(lean)
    for dich, (engine, _hinge) in lean.items():
        assert exported[dich] == engine, f"{dich}: export says {exported[dich]}, Lean's ¬A_k branch is {engine}"


def test_every_hinge_side_value_differs_from_the_engine_side() -> None:
    # The dichotomy would not be a dichotomy otherwise — and the check guards a typo
    # that silently makes the robustness run a no-op at one cell.
    if not FLOORS_LEAN.exists():
        pytest.skip("arith sources not on disk")
    for dich, (engine, hinge) in branches_from_lean().items():
        assert engine != hinge, dich


def test_unknown_dichotomy_is_an_error_not_a_default() -> None:
    with pytest.raises(KeyError, match="no hinge-side value recorded"):
        hinge_side_pair("dich_NewBot_vs_OtherBot", "outcome_NewBot_vs_OtherBot_floor")


# ── (b) the loaders ──────────────────────────────────────────────────────────────


@needs_real_export
def test_scan_under_hinge_side_carries_the_other_branch() -> None:
    engine_side = {t.name: t for t in scan_outcome_theorems(source="sprime", floor_policy="engine_side")}
    hinge_side = {t.name: t for t in scan_outcome_theorems(source="sprime", floor_policy="hinge_side")}
    assert set(engine_side) == set(hinge_side) and len(hinge_side) == 162  # 132 cells + 30 floors
    for name, t in hinge_side.items():
        e = engine_side[name]
        if t.is_floor:
            assert t.floor_branch == "hinge_side" and e.floor_branch == "engine_side"
            assert t.pair == HINGE_SIDE_PAIRS[t.dichotomy] and t.pair != e.pair
            assert t.hinge == e.hinge and t.dichotomy == e.dichotomy
        else:
            assert t.floor_branch == "" and t.pair == e.pair


@needs_real_export
def test_body_zoo_under_hinge_side() -> None:
    eng = load_tau_matrix(PAPER_BODY_SUB_ZOO, source="sprime", floor_policy="engine_side")
    hin = load_tau_matrix(PAPER_BODY_SUB_ZOO, source="sprime", floor_policy="hinge_side")
    assert hin.floor_policy == "hinge_side" and hin.is_fully_proven
    assert hin.floor_cells == eng.floor_cells and len(hin.floor_cells) == 8
    # The four body floors, hinge side: Cupod's detector fires, the three Löbian
    # searchers cooperate with the else-players they were defecting against.
    assert (hin.action("CupodBot", "OBot"), hin.action("OBot", "CupodBot")) == ("D", "D")
    for other in ("DBot", "EBot", "CupodTrollBot"):
        assert hin.action("DupocBot", other) == "C" and hin.action(other, "DupocBot") == "C"
        assert eng.action("DupocBot", other) == "D"
    for k in hin.floor_cells:
        assert hin.cell(*k).floor_branch == "hinge_side" and hin.cell(*k).is_floor
    # Every non-floor cell is untouched.
    for r in hin.bots:
        for c in hin.bots:
            if (r, c) not in hin.floor_cells:
                assert hin.cell(r, c) == eng.cell(r, c)
    # A floor is never a flip — the ≠ set is the same under both policies (DIMCID's).
    assert set(hin.flip_cells) == set(eng.flip_cells)
    assert not set(hin.flip_cells) & set(hin.floor_cells)
    # No kernel floor bit exists for the hinge branch: unstated, coverage drops.
    assert eng.is_kernel_backed and eng.kernel_bit_counts["floor_dichotomy"] == 8
    assert not hin.is_kernel_backed and hin.kernel_bit_counts["floor_dichotomy"] == 0
    assert hin.kernel_bit_counts["theorem"] == eng.kernel_bit_counts["theorem"]


@needs_real_export
def test_twins_zoo_under_hinge_side_flips_all_25_floor_rows() -> None:
    eng = load_tau_matrix(PAPER_TWINS_SUB_ZOO, source="sprime", floor_policy="engine_side")
    hin = load_tau_matrix(PAPER_TWINS_SUB_ZOO, source="sprime", floor_policy="hinge_side")
    assert len(hin.floor_cells) == 25
    for k in hin.floor_cells:
        assert hin.cell(*k).floor_branch == "hinge_side"
        assert (hin.cell(*k).row_action, hin.cell(*k).col_action) != (
            eng.cell(*k).row_action, eng.cell(*k).col_action)
    # Both orientations of a pair agree (the transpose is derived, never read twice).
    for r, c in hin.floor_cells:
        assert hin.action(r, c) == hin.cell(c, r).col_action


# ── (c) the EGT provenance ───────────────────────────────────────────────────────


@needs_real_export
def test_egt_identity_separates_the_two_branches() -> None:
    from pd_runner.egt.ingest import payoff_matrix_from_tau_matrix
    from pd_runner.egt.nash.loader import hash_payoff_matrix
    from pd_runner.egt.pipeline import RunPaths, SweepResult, sweep_summary_name

    eng = payoff_matrix_from_tau_matrix(
        load_tau_matrix(PAPER_BODY_SUB_ZOO, source="sprime", floor_policy="engine_side"), zoo="body")
    hin = payoff_matrix_from_tau_matrix(
        load_tau_matrix(PAPER_BODY_SUB_ZOO, source="sprime", floor_policy="hinge_side"), zoo="body")
    assert eng.floor_policy == "engine_side" and hin.floor_policy == "hinge_side"
    assert eng.floor_cells == hin.floor_cells
    assert hash_payoff_matrix(eng) != hash_payoff_matrix(hin)
    assert eng.assumptions()["floor_policy"] == "engine_side"
    assert hin.assumptions()["floor_policy"] == "hinge_side"
    pe, ph = RunPaths.for_matrix(eng), RunPaths.for_matrix(hin)
    assert pe.name.startswith("body_sprime_t100_") and "hinge" not in pe.name
    assert ph.name.startswith("body_sprime_hinge_side_t100_")
    assert sweep_summary_name("behavioral") == "sweep_summary.json"
    assert sweep_summary_name("behavioral", "hinge_side") == "sweep_summary_hinge_side.json"
    assert sweep_summary_name("syntactic", "hinge_side") == "sweep_summary_syntactic_hinge_side.json"
    assert SweepResult(zoo="body", runs=[], n_grid_points=0, seconds=0.0, out_root=Path("x"),
                       cell_source="sprime", floor_policy="hinge_side").summary()["floor_policy"] == "hinge_side"


# ── (d) the two floor-robustness zoos (2026-10-09) ────────────────────────────────


@needs_real_export
@pytest.mark.parametrize("zoo,size,n_floor_pairs", [("body8", 8, 3), ("nonprovers+dupoc", 7, 2)])
def test_floor_robustness_zoos_are_total_flip_free_and_twin_free(zoo, size, n_floor_pairs) -> None:
    from pd_runner.tau.matrix import ZOOS
    from pd_runner.tau.signal import behavioral_twins

    for policy in ("engine_side", "hinge_side"):
        m = ZOOS[zoo].load(source="sprime", floor_policy=policy)
        assert len(m) == size and m.is_fully_proven
        assert len(m.floor_pairs) == n_floor_pairs
        # Zero flips: on these rosters PA-S' and the engine agree on every non-floor
        # cell, so the floor policy is the ONLY difference between the two systems.
        assert m.flip_cells == ()
        # Twin-free on the engine side; on the hinge side body8's CupodBot and DupocBot
        # share an action ROW (EGT_FINDINGS_SPRIME.md §9.1), which the test records.
        twins = [g for g in behavioral_twins(m) if len(g) > 1]
        assert twins == ([("CupodBot", "DupocBot")] if (zoo, policy) == ("body8", "hinge_side") else [])
        assert "DIMCID" not in m.bots and "WaryBot" not in m.bots and "MirrorBot" not in m.bots
        assert "CupodTrollBot" not in m.bots and "CIMCIC" not in m.bots
