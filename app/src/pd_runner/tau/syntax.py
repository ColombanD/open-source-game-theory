"""Syntactic (codebase) features and distances over the zoo.

The syntactic σ family asks: how confusable are two bots to an observer who
partially READS their source, rather than watching them play? Distance is a
weighted L1 over interpretable feature counts extracted from each bot's Lean
definition — "similar trees" in the concrete sense of similar constructor
profiles ("has a proof-search node", "how many sims", leaf polarities).

Why features instead of tree edit distance (v1 decision, 2026-08-03): the
feature vector needs only a comment-strip + token count over `Bots/*.lean`,
is trivially auditable, and already produces the phenomenon that makes the
syntactic channel interesting — the CONFUSION-STRUCTURE INVERSION:

  DupocBot vs CupodBot   syntactically near-twins (identical tree, three leaf
                         labels swapped: d = 2) but behaviorally OPPOSITE
                         dispositions (default-defect vs default-cooperate);
  CooperateBot vs        behavioral near-twins over the zoo, but syntactic
  CupodTrollBot          opposites (a single .const leaf vs a .search machine).

So the code channel confuses exactly the pairs the behavior channel separates,
and vice versa. Proper AST tree-edit distance and the node-masking generative
channel are the recorded upgrade path (see the design note's σ roadmap).

Bot references (`.bot DefectBot`, `CupodBot k` inside `.eq`) are counted as
opaque leaves (`bot` node count + `ref` name count), NOT inlined — the
referenced source is a pointer, and an observer glimpsing the term sees the
name, not the body.
"""

from __future__ import annotations

import re
from pathlib import Path

from pd_runner.tau.matrix import TauMatrix


def _workspace_root() -> Path:
    return Path(__file__).resolve().parents[4]


_BOTS_DIR = _workspace_root() / "engine" / "PrisonersDilemma" / "Bots"

# Fixed, interpretable feature order. Constructors that this zoo does not use
# yet (.box/.impl/.neg) are kept so the vector is stable as the zoo grows
# (LegibleBot uses .box, WaryBot uses .neg).
FEATURE_ORDER: tuple[str, ...] = (
    "search",  # bounded proof-search nodes — the Löbian marker
    "ite",     # behavioral branching
    "sim",     # counterfactual simulation nodes
    "box",     # provability operator inside a guard
    "plays",   # plays-atoms in guards
    "impl",    # implication guards
    "neg",     # negation guards
    "eq",      # syntactic-equality guards
    "bot",     # frozen-bot wrapper nodes
    "self",    # self references
    "opp",     # opponent references
    "ref",     # named references to other zoo bots (opaque leaves)
    "C",       # Action.C leaves (guard polarity + branch constants)
    "D",       # Action.D leaves
)

_COMMENT_RE = re.compile(r"--.*$", re.MULTILINE)
# `def <Name> ... := <body>` up to the next top-level def / end / EOF.
_DEF_TEMPLATE = r"def\s+{name}\b[^:]*:.*?:=\s*(?P<body>.*?)(?=\ndef\s|\nend\b|\Z)"

_KNOWN_BOT_NAME_RE = re.compile(r"\b([A-Z][A-Za-z0-9]*Bot[A-Za-z0-9]*)\b")


def bot_source(name: str, bots_dir: Path = _BOTS_DIR) -> str:
    """The comment-stripped body of `def <name>` from the Bots tree.

    Searches `Bots/*.lean` and `Bots/LlmGenerations/*.lean`. Fails loudly on a
    missing definition — a silent zero-vector would poison every distance.
    """
    pattern = re.compile(_DEF_TEMPLATE.format(name=re.escape(name)), re.DOTALL)
    candidates = [bots_dir / f"{name}.lean", bots_dir / "LlmGenerations" / f"{name}.lean"]
    candidates += sorted(bots_dir.rglob("*.lean"))
    for path in candidates:
        if not path.exists():
            continue
        text = _COMMENT_RE.sub("", path.read_text(encoding="utf-8"))
        match = pattern.search(text)
        if match:
            return match.group("body")
    raise FileNotFoundError(f"no `def {name}` found under {bots_dir}")


def feature_vector(source: str, self_name: str | None = None) -> tuple[int, ...]:
    """Token counts of the fixed feature set over a comment-stripped body."""
    counts = {
        "search": len(re.findall(r"\.search\b", source)),
        "ite": len(re.findall(r"\.ite\b", source)),
        "sim": len(re.findall(r"\.sim\b", source)),
        "box": len(re.findall(r"\.box\b", source)),
        "plays": len(re.findall(r"\.plays\b", source)),
        "impl": len(re.findall(r"\.impl\b", source)),
        "neg": len(re.findall(r"\.neg\b", source)),
        "eq": len(re.findall(r"\.eq\b", source)),
        "bot": len(re.findall(r"\.bot\b", source)),
        "self": len(re.findall(r"\.self\b", source)),
        "opp": len(re.findall(r"\.opp\b", source)),
        "C": len(re.findall(r"\bAction\.C\b", source)),
        "D": len(re.findall(r"\bAction\.D\b", source)),
    }
    refs = [n for n in _KNOWN_BOT_NAME_RE.findall(source) if n != self_name]
    counts["ref"] = len(refs)
    return tuple(counts[f] for f in FEATURE_ORDER)


def bot_feature_vectors(
    bots: tuple[str, ...],
    bots_dir: Path = _BOTS_DIR,
) -> dict[str, tuple[int, ...]]:
    return {b: feature_vector(bot_source(b, bots_dir), self_name=b) for b in bots}


def syntactic_distance_matrix(
    matrix: TauMatrix,
    bots_dir: Path = _BOTS_DIR,
) -> dict[tuple[str, str], int]:
    """L1 distance between feature vectors — same shape as the behavioral one.

    Unweighted on purpose (v1): every feature is a count of concrete syntax
    nodes, so L1 is "number of constructor-profile edits", the feature-space
    shadow of tree edit distance. A weighted variant (e.g. search-nodes worth
    more) is a one-line change once there is a reason to prefer one.
    """
    vectors = bot_feature_vectors(matrix.bots, bots_dir)
    return {
        (a, b): sum(abs(x - y) for x, y in zip(vectors[a], vectors[b]))
        for a in matrix.bots
        for b in matrix.bots
    }


def syntactic_twins(
    matrix: TauMatrix,
    bots_dir: Path = _BOTS_DIR,
) -> list[tuple[str, ...]]:
    """Groups with identical feature vectors — unseparable by this channel."""
    groups: dict[tuple[int, ...], list[str]] = {}
    for bot, vec in bot_feature_vectors(matrix.bots, bots_dir).items():
        groups.setdefault(vec, []).append(bot)
    return [tuple(sorted(g)) for g in groups.values() if len(g) > 1]
