"""End-to-end pipeline: measure an LLM's cooperation profile, then fit it.

For each bot in the library we query the model ``n`` times in a one-shot
transparent prisoner's dilemma against that bot, count how often it plays ``C``,
and use the frequency as the Bernoulli estimate ``x_i``. The full vector ``x`` is
then fit to the convex hull of the reference bots with the existing machinery,
and everything is written to a timestamped run folder.

The OpenRouter API key is loaded exclusively from a gitignored ``.env`` file at
the project root (see :func:`_load_api_key`).
"""

from __future__ import annotations

import json
import os
from dataclasses import dataclass
from datetime import datetime
from pathlib import Path

import numpy as np
from dotenv import load_dotenv

from .bot_descriptions import BOT_DESCRIPTIONS
from .data import load_library
from .fitting import fit_all
from .openrouter import make_client, query_action
from .prompt import build_prompt
from .reporting import format_report

API_KEY_ENV = "OPENROUTER_API_KEY"
# The key is loaded exclusively from a gitignored .env at the project root.
ENV_FILE = Path(__file__).resolve().parents[2] / ".env"
# Placeholder shipped in .env; treated as "not set" so a fresh clone fails loudly.
_API_KEY_PLACEHOLDER = "sk-or-replace-me"


def _load_api_key() -> str:
    """Load OPENROUTER_API_KEY from the project-root .env file.

    The ``.env`` file (gitignored) is the single source for the key. Raises a
    clear error if the file is missing or still holds the shipped placeholder.
    """
    if not ENV_FILE.is_file():
        raise RuntimeError(f"No .env file at {ENV_FILE}. Create it with "
                           f"{API_KEY_ENV}=<your-key>.")
    load_dotenv(ENV_FILE)
    api_key = os.environ.get(API_KEY_ENV)
    if not api_key or api_key == _API_KEY_PLACEHOLDER:
        raise RuntimeError(f"{API_KEY_ENV} is not set in {ENV_FILE} "
                           "(still the placeholder?).")
    return api_key


@dataclass
class RunConfig:
    """Configuration for a single pipeline run."""

    model: str
    n: int = 30
    temperature: float = 1.0
    reasoning_effort: str | None = None  # None -> reasoning param omitted entirely
    matrix_path: Path = Path("data/payoff_matrix.csv")
    output_root: Path = Path("runs")


def _model_slug(model: str) -> str:
    return model.replace("/", "-").replace(":", "-")


def run_pipeline(config: RunConfig) -> Path:
    """Run the full measure-then-fit pipeline; return the run folder path."""
    library = load_library(config.matrix_path)
    missing = [bot for bot in library.bots if bot not in BOT_DESCRIPTIONS]
    if missing:
        raise KeyError(f"No pseudocode description for bots: {missing}")

    client = make_client(_load_api_key())

    run_dir = _init_run_dir(config, library.bots)

    raw_responses: dict[str, dict] = {}
    x = np.full(library.n, np.nan)  # NaN until a bot is measured (crash-safe partials)

    for i, bot in enumerate(library.bots):
        print(f"[{i + 1}/{library.n}] {bot}: querying {config.n}x ...", flush=True)
        prompt = build_prompt(bot, BOT_DESCRIPTIONS[bot])  # identical across the N queries
        results = [query_action(client, config.model, prompt, config.temperature,
                                 config.reasoning_effort)
                   for _ in range(config.n)]
        # Archive the prompt once per bot alongside its responses.
        raw_responses[bot] = {"prompt": prompt,
                              "responses": [{"action": a, "raw": r} for a, r in results]}

        actions = [a for a, _ in results if a is not None]
        x[i] = actions.count("C") / len(actions) if actions else float("nan")
        print(f"  -> P(C) = {x[i]:.3f}  ({len(actions)}/{config.n} valid)", flush=True)
        # Crash safety: persist what we have so far after every bot.
        _save_data(run_dir, library.bots, x, raw_responses)

    fits = fit_all(library.R, x)
    report = format_report(library, fits, x)
    (run_dir / "report.txt").write_text(report)
    return run_dir


def _init_run_dir(config, bots) -> Path:
    """Create the timestamped run folder and write metadata.json up front."""
    timestamp = datetime.now().strftime("%Y-%m-%d_%H-%M-%S")
    run_dir = config.output_root / f"{timestamp}_{_model_slug(config.model)}"
    run_dir.mkdir(parents=True, exist_ok=True)
    (run_dir / "metadata.json").write_text(json.dumps({
        "model": config.model,
        "n": config.n,
        "temperature": config.temperature,
        "reasoning_effort": config.reasoning_effort,
        "timestamp": timestamp,
        "matrix_path": str(config.matrix_path),
        "bots": list(bots),
    }, indent=2))
    return run_dir


def _save_data(run_dir: Path, bots, x, raw_responses) -> None:
    """Write raw_responses.json and cooperation_vector.json (called per bot)."""
    (run_dir / "raw_responses.json").write_text(json.dumps(raw_responses, indent=2))
    (run_dir / "cooperation_vector.json").write_text(json.dumps({
        "bots": list(bots),
        "x": x.tolist(),
        "by_bot": dict(zip(bots, x.tolist())),
    }, indent=2))
