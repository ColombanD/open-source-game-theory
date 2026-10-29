from __future__ import annotations

import re

_ACTION_RE = re.compile(r"\b(C|D)\b")


def parse_actions_from_stdout(stdout: str) -> tuple[str, str]:
    # Lean `#eval outcome ...` prints an Option-wrapped tuple containing two actions.
    # We parse the first line that exposes at least two `C`/`D` tokens.
    for line in stdout.splitlines():
        tokens = _ACTION_RE.findall(line)
        if len(tokens) >= 2:
            return tokens[0], tokens[1]
    raise ValueError(f"could not parse action tuple from Lean output: {stdout!r}")
