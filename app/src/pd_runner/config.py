from __future__ import annotations

import os
from dataclasses import dataclass
from pathlib import Path


@dataclass(frozen=True)
class AppPaths:
    app_root: Path
    lean_engine_dir: Path
    generated_lean_dir: Path
    generated_logs_dir: Path


def load_paths() -> AppPaths:
    app_root = Path(__file__).resolve().parents[2]

    override = os.getenv("PD_LEAN_ENGINE_DIR") or os.getenv("PD_LEAN_CODE_DIR")
    lean_engine_dir = Path(override).resolve() if override else (app_root.parent / "engine").resolve()

    return AppPaths(
        app_root=app_root,
        lean_engine_dir=lean_engine_dir,
        generated_lean_dir=(app_root / "generated" / "lean"),
        generated_logs_dir=(app_root / "generated" / "logs"),
    )
