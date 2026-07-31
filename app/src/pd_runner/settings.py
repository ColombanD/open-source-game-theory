"""Single source of truth for agent configuration defaults.

Every knob that used to be a scattered literal (model IDs, token budgets,
iteration caps, retry delays, retrieval scoring constants) lives here.
Services, API schemas, and CLI argparse defaults all import from this module —
change a default once, and every entry point agrees.
"""

from __future__ import annotations

import os
from dataclasses import dataclass, field

# ---------------------------------------------------------------------------
# Model defaults
# ---------------------------------------------------------------------------

# The single default model for every agent (proof, bot writer, integration).
# All current eval baselines and the adaptive-thinking-stall workaround notes
# (see llm/client.py) are calibrated on opus-4-7; change this only at a
# designated re-baselining point so model and architecture effects stay
# separable in the thesis data.
DEFAULT_MODEL = "claude-opus-4-7"

# (input $/MTok, output $/MTok) — used for cost reporting in eval records.
MODEL_PRICES: dict[str, tuple[float, float]] = {
    "claude-opus-4-7": (5.0, 25.0),
    "claude-opus-4-8": (5.0, 25.0),
    "claude-sonnet-4-6": (3.0, 15.0),
    "claude-haiku-4-5": (1.0, 5.0),
}

# Cache pricing multipliers relative to input price (Anthropic ephemeral cache).
CACHE_READ_MULTIPLIER = 0.1
CACHE_WRITE_MULTIPLIER = 1.25

# LeanInteract checking for the agent's iteration loop (persistent REPL, env
# cache, sorry-GOAL extraction — the sketch-then-fill feature). Disable with
# PD_LEAN_INTERACT=0. Measured 2026-07-31 on the 16GB dev machine: cached-env
# checks ~0.03s vs ~0.7s warm `lake env lean` (~20x), env creation ~2s once
# per import block. Robustness: the memory guard runs at 0.95 (macOS reports
# near-full by design), cached envs replay through server restarts, and two
# consecutive failures disable the backend for the process (each fallback is
# only ever a slower-but-correct file compile). The verdict gate and library
# writer are NEVER affected — they always file-compile.
LEAN_INTERACT_ENABLED = os.getenv("PD_LEAN_INTERACT", "1") != "0"


# ---------------------------------------------------------------------------
# Retry policy
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class RetryPolicy:
    """Retry schedule for transient API failures.

    `delays_s` has one entry per retry: len(delays_s)+1 total attempts, the
    last of which re-raises on failure (no unguarded extra call).
    """

    delays_s: tuple[float, ...] = (5.0, 15.0, 30.0, 60.0)
    retry_statuses: frozenset[int] = frozenset({429, 500, 502, 503, 529})
    honor_retry_after: bool = True


# ---------------------------------------------------------------------------
# Few-shot retrieval
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class RetrievalConfig:
    """Scoring constants for the lexical few-shot retriever (llm/retrieval.py)."""

    max_files: int = 6
    reserved_cross_slots: int = 2   # extra cross-directory helper files (0 < score < dedicated)
    path_dedicated_score: int = 20  # file is path-dedicated to a target bot
    occurrence_cap: int = 10        # cap on content-mention score
    helpers_bonus: int = 1


# ---------------------------------------------------------------------------
# Eval guard — the explicit split of the old overloaded `exclude_bots` flag
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class EvalGuard:
    """Separates the two orthogonal concerns the old `exclude_bots` conflated.

    `hidden_bots` — leak prevention. One set drives all four leak surfaces
    (few-shot filtering, read_library_file denial, known-theorem suppression,
    LlmLemmas block filtering); they must always travel together, so they stay
    coupled under a single field.

    `allow_library_growth` — mutation prevention. Controls whether the Tier-1
    (`add_base_lemma`) and Tier-2 (`propose_pf_constructor`) growth tools are
    registered and whether the proposals prompt blocks are included.

    Production = EvalGuard() (nothing hidden, growth on) — byte-identical to
    the old empty-`exclude_bots` behavior. Eval = `EvalGuard.for_eval(bots)`.
    """

    hidden_bots: frozenset[str] = frozenset()
    allow_library_growth: bool = True

    @classmethod
    def for_eval(cls, hidden_bots: frozenset[str] | set[str]) -> "EvalGuard":
        return cls(hidden_bots=frozenset(hidden_bots), allow_library_growth=False)

    @classmethod
    def from_exclude_bots(cls, exclude_bots: frozenset[str] | set[str]) -> "EvalGuard":
        """Compat shim: derive the guard exactly as the old flag implied it."""
        exclude = frozenset(exclude_bots)
        return cls(hidden_bots=exclude, allow_library_growth=not exclude)


# ---------------------------------------------------------------------------
# Agent settings
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class AgentSettings:
    """Budgets and knobs for one proof-search run."""

    model: str = DEFAULT_MODEL
    max_tokens: int = 32_000
    thinking_effort: str = "medium"      # "none" | "low" | "medium" | "high"

    # Episode loop (services/proof_episodes.py)
    max_turns_per_episode: int = 10      # API round-trips per episode
    max_episodes: int = 3                # fresh-context restarts
    max_verification_bounces: int = 3    # failed submit_verdict(proved) retries per episode
    notebook_char_cap: int = 4_000
    context_token_guard: int = 350_000   # end episode gracefully before overflow

    retry: RetryPolicy = field(default_factory=RetryPolicy)
    retrieval: RetrievalConfig = field(default_factory=RetrievalConfig)


DEFAULT_SETTINGS = AgentSettings()

# Legacy flat defaults, kept as named constants so call sites that only need
# one knob don't have to construct an AgentSettings.
DEFAULT_MAX_TOKENS = DEFAULT_SETTINGS.max_tokens
DEFAULT_THINKING_EFFORT = DEFAULT_SETTINGS.thinking_effort
DEFAULT_MAX_ITERATIONS = 20              # legacy flat turn cap (pre-episode API surface)
# The engine-editing integration agent: same expected total budget as the old
# flat 60-turn cap, restructured as episodes (20 turns × 3 fresh contexts).
INTEGRATION_TURNS_PER_EPISODE = 20
INTEGRATION_MAX_EPISODES = 3
INTEGRATION_BUILD_BOUNCES = 3            # failed complete-verdict verifications per episode


def cost_usd(model: str, *, input_tokens: int, output_tokens: int,
             cache_read_tokens: int = 0, cache_creation_tokens: int = 0) -> float | None:
    """Dollar cost of a run, or None for unknown models."""
    prices = MODEL_PRICES.get(model)
    if prices is None:
        return None
    in_price, out_price = prices
    uncached = max(input_tokens, 0)
    return (
        uncached * in_price
        + cache_read_tokens * in_price * CACHE_READ_MULTIPLIER
        + cache_creation_tokens * in_price * CACHE_WRITE_MULTIPLIER
        + output_tokens * out_price
    ) / 1_000_000
