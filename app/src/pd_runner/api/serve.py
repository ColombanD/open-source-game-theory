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
    uvicorn.run(
        "pd_runner.api.main:app",
        host=args.host,
        port=args.port,
        reload=args.reload,
    )


if __name__ == "__main__":
    main()
