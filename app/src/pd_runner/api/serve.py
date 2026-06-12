"""Entrypoint for the FastAPI dev server."""

from __future__ import annotations

import argparse


def main() -> None:
    parser = argparse.ArgumentParser(description="Start the pd-runner API server")
    parser.add_argument("--host", default="127.0.0.1")
    parser.add_argument("--port", type=int, default=8000)
    parser.add_argument("--reload", action="store_true", help="Enable auto-reload (dev mode)")
    args = parser.parse_args()

    import uvicorn

    # In reload mode, only watch the source tree. The pipeline writes proof
    # attempts to `app/generated/` and runs `lake build` over `engine/`; without
    # these excludes the reloader restarts mid-run, wiping the in-memory job
    # store and stranding the UI on its last state ("stuck in ending").
    reload_kwargs: dict = {}
    if args.reload:
        from pathlib import Path
        src_dir = Path(__file__).resolve().parents[2]  # app/src
        reload_kwargs = {
            "reload_dirs": [str(src_dir)],
            "reload_excludes": ["*/generated/*", "generated/*"],
        }

    uvicorn.run(
        "pd_runner.api.main:app",
        host=args.host,
        port=args.port,
        reload=args.reload,
        **reload_kwargs,
    )


if __name__ == "__main__":
    main()
