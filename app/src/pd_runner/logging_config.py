"""Logging configuration for pd_runner.

Usage:
    from pd_runner.logging_config import setup_logging
    setup_logging("DEBUG")   # or "INFO", "TRACE", "WARNING", etc.

All pd_runner loggers are children of the "pd_runner" root logger.

Log levels (most → least verbose):
  TRACE   (5)  — everything: system prompt, initial user message, LLM responses, tool calls/results, lean source
  DEBUG   (10) — LLM responses, tool calls/results, lean source (no initial prompts)
  INFO    (20) — tool call names and inputs only
  WARNING (30) — silent (default)
"""

from __future__ import annotations

import logging
import sys

LOGGER_NAME = "pd_runner"
TRACE = 5
logging.addLevelName(TRACE, "TRACE")


def get_logger(name: str) -> logging.Logger:
    return logging.getLogger(f"{LOGGER_NAME}.{name}")


def setup_logging(level: str = "WARNING") -> None:
    numeric = TRACE if level.upper() == "TRACE" else getattr(logging, level.upper(), None)
    if not isinstance(numeric, int):
        raise ValueError(f"Invalid log level: {level}")

    logger = logging.getLogger(LOGGER_NAME)
    logger.setLevel(numeric)

    if not logger.handlers:
        handler = logging.StreamHandler(sys.stderr)
        handler.setFormatter(logging.Formatter("%(asctime)s [%(levelname)s] %(name)s: %(message)s", datefmt="%H:%M:%S"))
        logger.addHandler(handler)
    else:
        logger.handlers[0].setLevel(numeric)
