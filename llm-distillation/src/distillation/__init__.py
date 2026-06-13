"""Fit a per-opponent cooperation profile to the convex hull of reference bots."""

from .data import (
    ReferenceLibrary,
    format_reference_matrix,
    load_input_vector,
    load_library,
    parse_cd_string,
    parse_cell,
)
from .fitting import (
    FitResult,
    fit_all,
    fit_expected_hamming,
    fit_l1,
    fit_l2,
    fit_linf,
    is_identified,
    profile_stats,
)
from .reporting import format_fit, format_profile_stats, format_report
from .bot_descriptions import BOT_DESCRIPTIONS
from .prompt import build_prompt
from .openrouter import make_client, parse_action, query_action
from .pipeline import RunConfig, run_pipeline

__all__ = [
    "ReferenceLibrary",
    "load_library",
    "load_input_vector",
    "parse_cell",
    "parse_cd_string",
    "format_reference_matrix",
    "FitResult",
    "fit_all",
    "fit_l2",
    "fit_l1",
    "fit_linf",
    "fit_expected_hamming",
    "is_identified",
    "profile_stats",
    "format_report",
    "format_fit",
    "format_profile_stats",
    "BOT_DESCRIPTIONS",
    "build_prompt",
    "make_client",
    "parse_action",
    "query_action",
    "RunConfig",
    "run_pipeline",
]
