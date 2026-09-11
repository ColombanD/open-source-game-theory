---
name: Always use uv for Python package management
description: User requires uv instead of pip for all Python package operations in this project
type: feedback
originSessionId: 55ed2e5a-56aa-46e3-a402-7a228050a234
---
Always use `uv` for Python package operations — never `pip` directly.

- Install/sync: `uv sync` (inside `app/`)
- Add a dependency: `uv add <package>`
- Run scripts or tests: `uv run <cmd>`

**Why:** User preference — they explicitly corrected a `pip install` call and asked for uv to be used consistently. Also documented in CLAUDE.md at the project root.

**How to apply:** Any time you'd run `pip install`, `pip install -e`, or `python -m pip`, use the `uv` equivalent instead.
