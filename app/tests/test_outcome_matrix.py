from pd_runner.eval.outcome_matrix import (
    build_outcome_matrix,
    format_matrix,
    scan_outcome_theorems,
)


def test_scan_finds_all_outcome_theorems() -> None:
    theorems = scan_outcome_theorems()
    assert len(theorems) >= 79
    names = {t.name for t in theorems}
    assert "outcome_CooperateBot_vs_DefectBot" in names
    assert "outcome_PrudentBot2_vs_PrudentBot2" in names
    assert "outcome_of_plays" not in names


def test_matrix_cells() -> None:
    bots, cells = build_outcome_matrix()
    assert cells[("CooperateBot", "DefectBot")] == "(C, D)"
    # Only outcome_DBot_vs_CooperateBot = (D, C) exists; the cell is swapped.
    assert cells[("CooperateBot", "DBot")] == "(C, D)"
    assert cells[("MirrorBot", "MirrorBot")] == "none"
    assert cells[("CupodBot", "DupocBot")] == "Open Problem"


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
