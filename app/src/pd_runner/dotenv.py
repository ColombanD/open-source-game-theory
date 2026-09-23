"""Load `app/.env` into os.environ at package import.

Why this exists: `ANTHROPIC_API_KEY` must NOT be exported globally from a
shell rc file. A global export is inherited by every process on the machine —
including Claude Code, which then bills the API account instead of the Max
subscription (diagnosed 2026-08-03). Scoping the key to `app/.env` keeps it
available to this pipeline and nowhere else.

`anthropic.Anthropic()` reads ANTHROPIC_API_KEY from os.environ when it is
constructed, so loading the file at package import — before any client is
built — is all that is required; no call site changes.

Deliberately dependency-free (no python-dotenv) and deliberately minimal: this
parses `KEY=value` lines, not the full dotenv grammar. No interpolation, no
`export` prefixes, no multi-line values. Real environment variables always
win, so `ANTHROPIC_API_KEY=... uv run ...` and CI secrets still override.
"""

from __future__ import annotations

import os
from pathlib import Path

# app/ — the directory holding .env. This file is app/src/pd_runner/dotenv.py,
# so parents[2] is app/ (mirrors config.load_paths()'s app_root).
_APP_ROOT = Path(__file__).resolve().parents[2]


def parse_env_file(text: str) -> dict[str, str]:
    """Parse `KEY=value` lines. Ignores blanks, comments, and malformed lines."""
    values: dict[str, str] = {}
    for raw_line in text.splitlines():
        line = raw_line.strip()
        if not line or line.startswith("#"):
            continue
        if line.startswith("export "):
            line = line[len("export ") :].lstrip()
        key, sep, value = line.partition("=")
        if not sep:
            continue
        key = key.strip()
        if not key:
            continue
        value = value.strip()
        # Strip one layer of matching quotes, if present.
        if len(value) >= 2 and value[0] == value[-1] and value[0] in ("'", '"'):
            value = value[1:-1]
        values[key] = value
    return values


def load_dotenv(path: Path | None = None) -> list[str]:
    """Load `path` (default `app/.env`) into os.environ.

    Existing environment variables are never overwritten — an explicitly
    exported value beats the file. Empty values in the file are skipped so a
    placeholder line like `ANTHROPIC_API_KEY=` does not mask a real key set in
    the environment. Returns the names actually set, for logging/tests.
    """
    env_path = path if path is not None else _APP_ROOT / ".env"
    try:
        text = env_path.read_text(encoding="utf-8")
    except (OSError, UnicodeDecodeError):
        # Missing or unreadable .env is the normal case in CI and for
        # contributors who export credentials by other means.
        return []

    applied: list[str] = []
    for key, value in parse_env_file(text).items():
        if not value or key in os.environ:
            continue
        os.environ[key] = value
        applied.append(key)
    return applied
