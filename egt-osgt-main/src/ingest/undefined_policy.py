"""Policy for undefined / contested cells of the outcome matrix.

Two cells in the Critch et al. (2022) outcome table are not deterministic:

  * (CupodBot, DupocBot): unresolved in the paper (red cell).
  * (MirrorBot, MirrorBot): non-terminating (`none` cell).

We represent an undefined cell in the loaded action-pair matrix with the
sentinel ``UNDEFINED`` and resolve it explicitly via this module so that
no computation silently imputes a value.

The `(MirrorBot, MirrorBot)` case is handled upstream: MirrorBot is
excluded from the analysed CSV altogether. This module therefore only
needs to resolve the `(CupodBot, DupocBot)` entry.
"""

from __future__ import annotations

from typing import Mapping

from .payoffs import ActionPair, parse_action_pair

UNDEFINED = None  # sentinel used for blank CSV cells


def resolve_cupod_vs_dupoc(config: Mapping) -> ActionPair:
    """Read the configured default action pair for (CupodBot, DupocBot)."""
    raw = config["undefined_outcomes"]["cupod_vs_dupoc"]
    return parse_action_pair(raw)
