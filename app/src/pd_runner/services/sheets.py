"""Push the outcome matrix to the tracking Google Sheet.

Auth is a Google Cloud service account: create one, download its JSON key to
`app/.secrets/sheets-service-account.json` (or point `PD_SHEETS_CREDENTIALS`
at it), and share the spreadsheet with the service account's email address
(Editor). The matrix is written to its own worksheet (`PD_SHEETS_WORKSHEET`,
default "Auto Matrix") so hand-written tabs are never touched; the target
worksheet is cleared and rewritten on every push.
"""

from __future__ import annotations

import os
from datetime import datetime, timezone
from pathlib import Path

from pd_runner.eval.outcome_matrix import (
    build_outcome_matrix,
    matrix_rows,
    prune_stale_statuses,
)

DEFAULT_SPREADSHEET_ID = "10oNMb88iDmsWcR6SBecopLhrlgilRU-htBB0q07eET8"
DEFAULT_WORKSHEET = "Auto Matrix"


class SheetsPushError(RuntimeError):
    """Configuration or API failure while pushing to Google Sheets."""


def _credentials_path() -> Path:
    env = os.environ.get("PD_SHEETS_CREDENTIALS")
    if env:
        return Path(env)
    # app/src/pd_runner/services/sheets.py -> app/
    return Path(__file__).resolve().parents[3] / ".secrets" / "sheets-service-account.json"


def sheets_configured() -> bool:
    """True when a service-account key is present (used for best-effort sync)."""
    return _credentials_path().exists()


def _apply_formatting(sheet, worksheet, bots: list[str], cells: dict[tuple[str, str], str]) -> None:
    """Mirror the hand-made tab's look: bold bordered headers, frozen panes,
    a black lower triangle, and highlighted Open Problem / Tried cells."""
    from gspread.utils import rowcol_to_a1

    n = len(bots)
    last_col = rowcol_to_a1(1, n + 1).rstrip("1")

    # Wipe stale formatting from previous pushes (clear() only removes values).
    sheet.batch_update({"requests": [{
        "repeatCell": {"range": {"sheetId": worksheet.id}, "fields": "userEnteredFormat"},
    }]})
    worksheet.freeze(rows=1, cols=1)

    black = {"red": 0, "green": 0, "blue": 0}
    light_red = {"red": 0.96, "green": 0.78, "blue": 0.77}
    light_yellow = {"red": 1, "green": 0.95, "blue": 0.78}
    light_green = {"red": 0.85, "green": 0.92, "blue": 0.83}
    light_blue = {"red": 0.79, "green": 0.85, "blue": 0.97}
    dark_text = {"foregroundColor": {"red": 0.13, "green": 0.13, "blue": 0.13}}
    solid = {"style": "SOLID", "color": black}
    borders = {"top": solid, "bottom": solid, "left": solid, "right": solid}

    formats = [
        {"range": f"A1:{last_col}1", "format": {"textFormat": {"bold": True}, "borders": borders}},
        {"range": f"A1:A{n + 1}", "format": {"textFormat": {"bold": True}, "borders": borders}},
        {"range": f"B2:{last_col}{n + 1}",
         "format": {"horizontalAlignment": "CENTER", "borders": borders}},
        # Legend/footer lines below the matrix (blank row, then two notes).
        {"range": f"A{n + 3}:A{n + 4}",
         "format": {"textFormat": {"italic": True, "foregroundColor": {"red": 0.45, "green": 0.45, "blue": 0.45}}}},
    ]
    # Row for bot i sits at sheet row i+2 and has i cells left of the diagonal.
    for i in range(1, n):
        formats.append({
            "range": f"B{i + 2}:{rowcol_to_a1(i + 2, i + 1)}",
            "format": {"backgroundColor": black},
        })
    for (row_bot, col_bot), value in cells.items():
        color = {"Open Problem": light_red, "Tried": light_yellow,
                 "None": light_green, "Need rework": light_blue}.get(value)
        if color is None:
            continue
        a1 = rowcol_to_a1(bots.index(row_bot) + 2, bots.index(col_bot) + 2)
        formats.append({"range": a1, "format": {"backgroundColor": color, "textFormat": dark_text}})
    worksheet.batch_format(formats)


def push_matrix(
    spreadsheet_id: str | None = None,
    worksheet_name: str | None = None,
    annotate: bool = False,
    prune_stale: bool = True,
) -> dict:
    """Rebuild the matrix from the theorem library and write it to the Sheet.

    By default first prunes outcome_status.toml entries whose pair has gained
    an accepted theorem since they were recorded — every sync self-cleans, so
    the post-proof-write sync removes the very entry that proof made stale.
    Returns a summary dict (worksheet, spreadsheet_url, cell counts by kind,
    pruned entries).
    """
    try:
        import gspread
    except ImportError as exc:  # pragma: no cover
        raise SheetsPushError("gspread is not installed — run `uv add gspread` in app/") from exc

    pruned = prune_stale_statuses() if prune_stale else []

    creds = _credentials_path()
    if not creds.exists():
        raise SheetsPushError(
            f"no service-account key at {creds} — create one in Google Cloud, share the "
            "spreadsheet with its email, and drop the JSON key there "
            "(or set PD_SHEETS_CREDENTIALS)"
        )
    spreadsheet_id = spreadsheet_id or os.environ.get("PD_SHEETS_SPREADSHEET_ID", DEFAULT_SPREADSHEET_ID)
    worksheet_name = worksheet_name or os.environ.get("PD_SHEETS_WORKSHEET", DEFAULT_WORKSHEET)

    bots, cells = build_outcome_matrix(annotate=annotate)
    rows = matrix_rows(bots, cells)
    stamp = datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M UTC")
    rows += [
        [],
        ["† proved under side hypotheses (floor/size/budget guards)"],
        [f"Auto-generated {stamp} by pd_runner.eval.outcome_matrix — do not edit; "
         "curate Open Problem/Tried in app/outcome_status.toml"],
    ]

    try:
        client = gspread.service_account(filename=str(creds))
        sheet = client.open_by_key(spreadsheet_id)
        try:
            worksheet = sheet.worksheet(worksheet_name)
        except gspread.exceptions.WorksheetNotFound:
            worksheet = sheet.add_worksheet(
                title=worksheet_name, rows=len(rows) + 10, cols=len(rows[0]) + 5,
            )
        worksheet.clear()
        worksheet.update(rows, "A1")
        _apply_formatting(sheet, worksheet, bots, cells)
    except gspread.exceptions.APIError as exc:
        raise SheetsPushError(f"Google Sheets API error: {exc}") from exc

    values = list(cells.values())
    return {
        "spreadsheet_url": sheet.url,
        "worksheet": worksheet_name,
        "bots": len(bots),
        "proven": sum(1 for v in values if v.startswith("(")),
        "none": sum(1 for v in values if v == "None"),
        "open": sum(1 for v in values if v == "Open Problem"),
        "tried": sum(1 for v in values if v == "Tried"),
        "rework": sum(1 for v in values if v == "Need rework"),
        "empty": sum(1 for v in values if v == ""),
        "pruned": [f"[[{section}]] {a} vs {b}" for section, a, b in pruned],
        "pushed_at": stamp,
    }
