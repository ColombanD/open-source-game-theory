from pathlib import Path

import pytest

from pd_runner.eval.outcome_matrix import (
    append_status,
    build_outcome_matrix,
    format_matrix,
    library_bots,
    load_status,
    scan_outcome_theorems,
)


def test_library_bots_are_theorem_directories() -> None:
    bots = library_bots()
    assert "WaryBot" in bots and "LegibleBot" in bots and "GuardianBot" in bots
    # An empty placeholder directory still counts as a bot.
    assert "OptimBot" in bots
    # Tier variants (no directory of their own) are not library bots.
    assert "PrudentBot2" not in bots and "JustBot2" not in bots
    assert "LlmGenerations" not in bots


def test_scan_accepts_only_strict_names() -> None:
    theorems = scan_outcome_theorems()
    assert len(theorems) >= 95
    names = {t.name for t in theorems}
    assert "outcome_CooperateBot_vs_DefectBot" in names
    # llm_ prefix is accepted...
    assert "llm_outcome_CIMCIC_vs_CIMCIC" in names
    # ...but suffixed regime variants and tier-variant bots are not.
    assert "outcome_WaryBot_vs_DefectBot" in names
    assert "outcome_WaryBot_vs_DefectBot_floor" not in names
    assert "outcome_WaryBot_vs_DefectBot_defended" not in names
    assert "outcome_PrudentBot2_vs_PrudentBot2" not in names
    assert "outcome_JustBot2_vs_DBot" not in names
    assert "outcome_of_plays" not in names


def test_side_hypotheses_are_flagged() -> None:
    by_name = {t.name: t for t in scan_outcome_theorems()}
    assert by_name["outcome_CupodTrollBot_vs_DupocBot"].has_hypotheses
    assert not by_name["outcome_CooperateBot_vs_DefectBot"].has_hypotheses


def test_matrix_cells() -> None:
    bots, cells = build_outcome_matrix()
    assert cells[("CooperateBot", "DefectBot")] == "(C, D)"
    # Only outcome_DBot_vs_CooperateBot = (D, C) exists; the cell is swapped.
    assert cells[("CooperateBot", "DBot")] == "(C, D)"
    # Proven no-outcome renders as None.
    assert cells[("MirrorBot", "MirrorBot")] == "None"
    # Side hypotheses get the dagger flag.
    assert cells[("DupocBot", "CupodTrollBot")] == "(C, C) †"
    # WaryBot vs DefectBot: the unsuffixed large-k theorem wins, not the floor.
    assert cells[("DefectBot", "WaryBot")] == "(D, D)"
    # Curated statuses from outcome_status.toml.
    assert cells[("CupodBot", "DupocBot")] == "Open Problem"
    # Floor-only proofs (wrong statement shape) are curated as Need rework.
    assert cells[("DBot", "LegibleBot")] == "Need rework"
    # Untried pairs stay empty.
    assert cells[("CupodBot", "GuardianBot")] == ""


def test_status_file_tried_and_validation(tmp_path: Path) -> None:
    status = tmp_path / "status.toml"
    status.write_text(
        '[[tried]]\npair = ["CupodBot", "PrudentBot"]\nreason = "no luck"\n',
        encoding="utf-8",
    )
    _, cells = build_outcome_matrix(status_file=status)
    assert cells[("CupodBot", "PrudentBot")] == "Tried"

    status.write_text('[[open]]\npair = ["NoSuchBot", "DBot"]\n', encoding="utf-8")
    with pytest.raises(ValueError, match="NoSuchBot"):
        load_status(status, bots=library_bots())


def test_append_status_dedup_and_precedence(tmp_path: Path) -> None:
    status = tmp_path / "status.toml"

    assert append_status("tried", ("CupodBot", "GuardianBot"), "failed run", status)
    # Same pair (either order) is not re-appended to the same section...
    assert not append_status("tried", ("GuardianBot", "CupodBot"), "again", status)
    # ...and never downgrades: tried onto an open pair is refused.
    assert append_status("open", ("CupodBot", "GuardianBot"), "confirmed open", status)
    assert not append_status("tried", ("CupodBot", "GuardianBot"), "later failure", status)

    # Precedence: the pair is now both tried and open — open wins.
    assert load_status(status)[("CupodBot", "GuardianBot")] == "Open Problem"

    with pytest.raises(ValueError, match="unknown status section"):
        append_status("bogus", ("A", "B"), "", status)


def test_format_csv_quotes_pairs() -> None:
    import csv
    import io

    bots, cells = build_outcome_matrix()
    rendered = format_matrix(bots, cells, fmt="csv")
    # Cells contain commas, so CSV must quote them and round-trip cleanly.
    rows = list(csv.reader(io.StringIO(rendered)))
    assert rows[0] == ["Outcome Matrix", *bots]
    assert all(len(row) == len(bots) + 1 for row in rows)
    header_index = {bot: i + 1 for i, bot in enumerate(bots)}
    assert rows[1][header_index["DefectBot"]] == "(C, D)"


def test_format_tsv_is_upper_triangular() -> None:
    bots, cells = build_outcome_matrix()
    rendered = format_matrix(bots, cells, fmt="tsv")
    lines = rendered.split("\n")
    assert lines[0].split("\t") == ["Outcome Matrix", *bots]
    # Row i has i empty cells before the diagonal.
    third_row = lines[3].split("\t")
    assert third_row[0] == bots[2]
    assert third_row[1] == "" and third_row[2] == ""
    assert third_row[3] != ""
