"""Human-readable reporting of fit results."""

from __future__ import annotations

import numpy as np

from .data import ReferenceLibrary
from .fitting import FitResult, profile_stats


def format_profile_stats(x: np.ndarray) -> str:
    """Metric-independent summaries of the input (reported once)."""
    stats = profile_stats(x)
    return (
        "Input profile summary (metric-independent):\n"
        f"  level     = mean(x)        = {stats['level']:.4f}  "
        "(overall cooperativeness)\n"
        f"  sharpness = mean(|x-0.5|)  = {stats['sharpness']:.4f}  "
        "(how decisive / near 0-1 the profile is)"
    )


def format_fit(result: FitResult, library: ReferenceLibrary) -> str:
    """Render one distance's fit: profile vs. input, weights, residual, checks."""
    bots = library.bots
    name_w = max(len(b) for b in bots)
    lines = [f"=== {result.metric} fit ==="]

    # Fitted profile alongside the input, coordinate by coordinate.
    lines.append("")
    lines.append("Fitted profile (R^T w*) vs input x, per opponent:")
    lines.append(f"  {'opponent'.ljust(name_w)}   x_i    fitted   diff")
    for j, bot in enumerate(bots):
        xi, fi = result.x[j], result.fitted[j]
        lines.append(
            f"  {bot.ljust(name_w)}  {xi:5.3f}  {fi:6.3f}  {fi - xi:+6.3f}"
        )

    # Optimal weights, only the bots with non-negligible mass.
    lines.append("")
    lines.append("Optimal weights w* (bots with non-negligible mass):")
    if result.active:
        for i in result.active:
            lines.append(f"  {bots[i].ljust(name_w)}  {result.weights[i]:.4f}")
    else:
        lines.append("  (none)")

    # Residual and its interpretation.
    lines.append("")
    lines.append(f"Residual ||R^T w* - x||  ({result.metric}) = {result.residual:.6f}")
    if result.residual <= 1e-6:
        lines.append(
            "  ~ 0: x is (numerically) realizable as a convex combination of "
            "library bots."
        )
    else:
        lines.append(
            "  > 0: NO convex combination of library bots can reproduce x; it "
            "sits off the library manifold (outside conv{r_i})."
        )

    # Identifiability of the weights.
    lines.append("")
    if result.identified:
        lines.append(
            "Identifiability: active reference rows are affinely independent -> "
            "weights are uniquely identified."
        )
    else:
        active_names = ", ".join(bots[i] for i in result.active)
        lines.append(
            "Identifiability: active reference rows are NOT affinely independent "
            f"({active_names}) -> the fitted point is unique but the weights are "
            "NOT. Mass can be shifted among the dependent rows (e.g. split between "
            "two identical rows) without changing the fit."
        )
    return "\n".join(lines)


def format_report(
    library: ReferenceLibrary, results: list[FitResult], x: np.ndarray
) -> str:
    """Full report: profile stats once, then every distance's fit."""
    blocks = [format_profile_stats(x), ""]
    for result in results:
        blocks.append(format_fit(result, library))
        blocks.append("")
    return "\n".join(blocks).rstrip() + "\n"
