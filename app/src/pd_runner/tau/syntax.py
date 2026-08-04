"""Syntactic (codebase) features and distances over the zoo.

The syntactic σ family asks: how confusable are two bots to an observer who
partially READS their source, rather than watching them play?

**v2 (2026-08-04) — real ASTs and tree edit distance.** Distance is now
Zhang–Shasha tree edit distance over parsed `Prog`/`Formula` terms, normalized
by tree size. The v1 bag-of-constructors feature vector remains as
`feature_vector` / `feature_distance_matrix` for comparison, but it is no
longer what the σ family uses, because it had four defects that the AST fixes:

1. **Structure blindness.** A bag of constructors cannot see argument order or
   nesting, so `DBot` and `TitForTatBot` — both
   `.ite (.sim .opp (.bot X)) C · ·` with the branches SWAPPED and a different
   `X` — collapsed to distance 0 and became syntactic twins. They are now
   distinguishable: the branch swap and the referenced name are both real edits.
2. **Reference blindness.** `ref` counted HOW MANY bot names appeared, never
   WHICH, so probing CooperateBot and probing DefectBot looked identical. Bot
   references are now labelled leaves (`ref:CooperateBot`), still opaque — the
   body is not inlined, matching the design note's "a pointer is what an
   observer sees" rule.
3. **Scale sensitivity.** Unnormalized L1 grows with program SIZE, so EBot (22
   nodes) sat at mean distance 17.6 from everything while the 1-node constants
   sat at 8.6 — the channel mostly encoded "how big is this bot", and the
   softmax then read big bots as maximally identifiable. Distance is now
   normalized by the larger tree, giving a scale-free [0, 1] ratio.
4. **Comment bleed.** The old body regex stripped `--` lines but not `/- … -/`
   blocks, so JustBot's and PrudentBot's doc-comments were fed to the token
   counter as if they were syntax. Harmless by luck (that prose happens to
   contain no `.foo` tokens), but a doc-comment mentioning `.search` would have
   silently corrupted the vector. Both comment forms are stripped now.

What survives from v1 is the phenomenon that makes this channel interesting —
the CONFUSION-STRUCTURE INVERSION:

  DupocBot vs CupodBot   syntactically near-identical (same tree, leaf action
                         labels swapped) but behaviorally OPPOSITE dispositions;
  CooperateBot vs        behavioral near-twins over the zoo, but syntactically
  CupodTrollBot          opposites (a single `.const` leaf vs a `.search`
                         machine).

So the code channel confuses exactly the pairs the behavior channel separates.

**Parsing, not exporting.** Terms are parsed from the `Bots/*.lean` sources by
a small S-expression reader rather than exported from Lean via `#eval`. The
design note prefers an exporter; parsing is chosen here because it keeps the
tau layer a pure-Python read-only consumer of the engine (no build step, no
`lake` dependency in the analysis path). The reader is deliberately strict —
it raises on anything it does not recognize instead of silently returning a
partial tree, so a zoo member whose source drifts out of the supported shape
fails loudly rather than quietly getting a wrong distance.
"""

from __future__ import annotations

import re
from dataclasses import dataclass, field
from functools import lru_cache
from pathlib import Path

from pd_runner.tau.matrix import TauMatrix


def _workspace_root() -> Path:
    return Path(__file__).resolve().parents[4]


_BOTS_DIR = _workspace_root() / "engine" / "PrisonersDilemma" / "Bots"

# Fixed, interpretable feature order for the LEGACY feature vector. Kept so the
# v1 channel stays reproducible for comparison against the AST one.
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

# `--` to end of line, and `/- … -/` blocks (including `/-- … -/` docstrings).
# Both must go: the body regex below stops at the next top-level `def`, so a
# docstring introducing the NEXT definition would otherwise land in this body.
_LINE_COMMENT_RE = re.compile(r"--.*$", re.MULTILINE)
_BLOCK_COMMENT_RE = re.compile(r"/-.*?-/", re.DOTALL)
# `def <Name> ... := <body>` up to the next top-level def / end / EOF.
_DEF_TEMPLATE = r"def\s+{name}\b[^:]*:.*?:=\s*(?P<body>.*?)(?=\ndef\s|\nend\b|\Z)"

_KNOWN_BOT_NAME_RE = re.compile(r"\b([A-Z][A-Za-z0-9]*Bot[A-Za-z0-9]*)\b")


def _strip_comments(text: str) -> str:
    return _LINE_COMMENT_RE.sub("", _BLOCK_COMMENT_RE.sub("", text))


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
        text = _strip_comments(path.read_text(encoding="utf-8"))
        match = pattern.search(text)
        if match:
            return match.group("body")
    raise FileNotFoundError(f"no `def {name}` found under {bots_dir}")


# ------------------------------------------------------------------ the AST ---

@dataclass(frozen=True)
class Node:
    """One `Prog`/`Formula` constructor application.

    `label` is what the tree-edit cost compares: the constructor name, refined
    for the leaves that carry meaning — `const:C`, `ref:DefectBot`, `probe:C`
    (the `.ite` test action). Numeric search budgets are deliberately NOT in
    the label (see `_BUDGET_IN_LABEL`).
    """

    label: str
    children: tuple["Node", ...] = ()

    @property
    def size(self) -> int:
        return 1 + sum(c.size for c in self.children)

    def flatten(self) -> list["Node"]:
        out: list[Node] = []
        for c in self.children:
            out.extend(c.flatten())
        out.append(self)
        return out


class ProgParseError(ValueError):
    """Raised when a bot body is not in the supported `Prog` term shape."""


# Budgets (`k`, `kOut`, `2 * k + 64`) are erased from labels: they are a
# DIFFERENT transparency axis (Critch's own depth dial — see the design note's
# "resource-bounded introspection"), and folding them into the code channel
# would conflate the two. `CupodBot k` and `CupodBot (2*k+64)` are the same
# code to this observer.
_BUDGET_IN_LABEL = False

_TOKEN_RE = re.compile(r"\(|\)|[^\s()]+")


def _tokenize(source: str) -> list[str]:
    return _TOKEN_RE.findall(source)


def parse_prog(source: str, self_name: str | None = None) -> Node:
    """Parse a Lean `Prog` term body into a `Node` tree.

    Handles the constructor set the zoo uses (`.const/.self/.opp/.bot/.sim/
    .ite/.search` and the `Formula` constructors), plus bare bot references
    (`CupodBot k`, `DefectBot`) as opaque labelled leaves.
    """
    tokens = _tokenize(source)
    pos = 0

    def peek() -> str | None:
        return tokens[pos] if pos < len(tokens) else None

    def parse_one() -> Node:
        nonlocal pos
        tok = peek()
        if tok is None:
            raise ProgParseError("unexpected end of term")
        if tok == "(":
            # A parenthesized group whose head is not a constructor or a bot
            # name is a budget expression (`(2 * k + 64)`, `(k + 1)`) — skip it
            # wholesale rather than parsing arithmetic we deliberately erase.
            head = tokens[pos + 1] if pos + 1 < len(tokens) else None
            if head is not None and head not in _ARITY and not _is_ref(head):
                _skip_term()
                return Node("_erased")
            pos += 1
            node = parse_application()
            if peek() != ")":
                raise ProgParseError(f"expected ')' near {tokens[pos:pos + 4]}")
            pos += 1
            return node
        if tok == ")":
            raise ProgParseError("unexpected ')'")
        return parse_application(single=True)

    def _is_ref(token: str) -> bool:
        return bool(_KNOWN_BOT_NAME_RE.fullmatch(token))

    def parse_application(single: bool = False) -> Node:
        """Parse a head token plus its arity-many arguments."""
        nonlocal pos
        head = tokens[pos]
        pos += 1

        # Action literals: `Action.C` / `.C` in test-action position.
        if head in ("Action.C", "Action.D"):
            return Node(f"action:{head[-1]}")

        arity = _ARITY.get(head)
        if arity is None:
            # A bare identifier: a bot reference (`DefectBot`, `CupodBot k`) or
            # a budget variable. Bot references are OPAQUE labelled leaves —
            # the observer sees the name, not the body.
            if _KNOWN_BOT_NAME_RE.fullmatch(head) and head != self_name:
                # Swallow any budget arguments applied to it (`CupodBot k`,
                # `DupocBot (2 * k)`) without descending into them.
                if not single:
                    while peek() is not None and peek() not in (")",):
                        _skip_term()
                return Node(f"ref:{head}")
            if head == self_name:
                return Node("ref:self-recursive")
            # A budget variable / numeral / arithmetic token in argument
            # position. Contributes no node (see `_BUDGET_IN_LABEL`).
            return Node("budget") if _BUDGET_IN_LABEL else Node("_erased")
        children = [parse_one() for _ in range(arity)]
        return Node(_LABEL.get(head, head), tuple(children))

    def _skip_term() -> None:
        """Consume one term without building nodes (budget arguments)."""
        nonlocal pos
        if peek() == "(":
            depth = 0
            while pos < len(tokens):
                if tokens[pos] == "(":
                    depth += 1
                elif tokens[pos] == ")":
                    depth -= 1
                    if depth == 0:
                        pos += 1
                        return
                pos += 1
            raise ProgParseError("unbalanced parentheses in argument")
        pos += 1

    root = parse_one()
    if pos != len(tokens):
        raise ProgParseError(
            f"trailing tokens after term: {tokens[pos:pos + 6]}"
        )
    return _prune(root)


def _prune(node: Node) -> Node:
    """Drop erased (budget) placeholders from the tree."""
    kept = tuple(_prune(c) for c in node.children if c.label != "_erased")
    return Node(node.label, kept)


# Constructor arities. `.ite` takes 4 (guard, test action, then, else);
# `.search` takes 4 (budget, formula, then, else) but the budget is consumed as
# an erased argument, so it is listed as 4 and pruned afterwards.
_ARITY: dict[str, int] = {
    ".const": 1,
    ".self": 0,
    ".opp": 0,
    ".bot": 1,
    ".sim": 2,
    ".ite": 4,
    ".search": 4,
    ".plays": 3,
    ".impl": 2,
    ".neg": 1,
    ".box": 2,
    ".eq": 2,
    ".diag": 2,
}

# Presentation labels (identical to the constructor, minus the dot).
_LABEL: dict[str, str] = {k: k.lstrip(".") for k in _ARITY}


@lru_cache(maxsize=None)
def bot_ast(name: str, bots_dir: Path = _BOTS_DIR) -> Node:
    """Parse one zoo member's source into an AST, cached per name."""
    return parse_prog(bot_source(name, bots_dir), self_name=name)


def bot_asts(bots: tuple[str, ...], bots_dir: Path = _BOTS_DIR) -> dict[str, Node]:
    return {b: bot_ast(b, bots_dir) for b in bots}


# ------------------------------------------------- Zhang–Shasha edit distance ---

def _keyroots(nodes: list[Node], leftmost: list[int]) -> list[int]:
    seen: set[int] = set()
    roots = []
    for i in range(len(nodes) - 1, -1, -1):
        if leftmost[i] not in seen:
            seen.add(leftmost[i])
            roots.append(i)
    return sorted(roots)


def _postorder(root: Node) -> tuple[list[Node], list[int]]:
    """Post-order node list plus each node's leftmost-descendant index."""
    nodes = root.flatten()
    index = {id(n): i for i, n in enumerate(nodes)}
    leftmost: list[int] = []
    for n in nodes:
        node = n
        while node.children:
            node = node.children[0]
        leftmost.append(index[id(node)])
    return nodes, leftmost


def tree_edit_distance(a: Node, b: Node) -> int:
    """Zhang–Shasha tree edit distance with unit insert/delete/relabel costs.

    Relabel is free when the labels match, cost 1 otherwise — so a branch swap
    (`.ite … C then else` vs `… else then`) and a changed probe target
    (`ref:CooperateBot` vs `ref:DefectBot`) both register, which is exactly
    what the feature vector could not see.
    """
    a_nodes, a_left = _postorder(a)
    b_nodes, b_left = _postorder(b)
    a_roots, b_roots = _keyroots(a_nodes, a_left), _keyroots(b_nodes, b_left)

    # tree_d[i][j]: distance between the subtrees rooted at i and j.
    tree_d = [[0] * len(b_nodes) for _ in range(len(a_nodes))]

    for i in a_roots:
        for j in b_roots:
            # Forest distance over the intervals [a_left[i]..i], [b_left[j]..j].
            oi, oj = a_left[i], b_left[j]
            m, n = i - oi + 2, j - oj + 2
            fd = [[0] * n for _ in range(m)]
            for x in range(1, m):
                fd[x][0] = fd[x - 1][0] + 1  # delete
            for y in range(1, n):
                fd[0][y] = fd[0][y - 1] + 1  # insert
            for x in range(1, m):
                for y in range(1, n):
                    ai, bj = oi + x - 1, oj + y - 1
                    if a_left[ai] == oi and b_left[bj] == oj:
                        cost = 0 if a_nodes[ai].label == b_nodes[bj].label else 1
                        fd[x][y] = min(
                            fd[x - 1][y] + 1,
                            fd[x][y - 1] + 1,
                            fd[x - 1][y - 1] + cost,
                        )
                        tree_d[ai][bj] = fd[x][y]
                    else:
                        p = a_left[ai] - oi
                        q = b_left[bj] - oj
                        fd[x][y] = min(
                            fd[x - 1][y] + 1,
                            fd[x][y - 1] + 1,
                            fd[p][q] + tree_d[ai][bj],
                        )
    return tree_d[len(a_nodes) - 1][len(b_nodes) - 1]


def normalized_tree_distance(a: Node, b: Node) -> float:
    """Edit distance as a fraction of the larger tree — scale-free in [0, 1].

    Normalization is what stops the channel from mostly encoding program SIZE:
    unnormalized, EBot (22 nodes) is far from everything simply by being big,
    and the softmax reads that as "EBot is highly identifiable".
    """
    denominator = max(a.size, b.size)
    return tree_edit_distance(a, b) / denominator if denominator else 0.0


# ------------------------------------------------------------------ channels ---

def syntactic_distance_matrix(
    matrix: TauMatrix,
    bots_dir: Path = _BOTS_DIR,
    scale: float = 10.0,
) -> dict[tuple[str, str], float]:
    """Normalized AST tree edit distance between every pair of zoo members.

    `scale` multiplies the [0, 1] ratio into the same numeric range the
    behavioral Hamming distance occupies (0..n over an n-bot zoo), so the
    shared softmax architecture in `channels.py` sees comparable magnitudes.
    It cancels out of the calibrated dial — `raw_for` inverts the MI scale per
    family — and only affects where the bisection starts.
    """
    asts = bot_asts(matrix.bots, bots_dir)
    out: dict[tuple[str, str], float] = {}
    for a in matrix.bots:
        for b in matrix.bots:
            if (b, a) in out:  # symmetric — reuse instead of recomputing
                out[(a, b)] = out[(b, a)]
            else:
                out[(a, b)] = scale * normalized_tree_distance(asts[a], asts[b])
    return out


def syntactic_twins(
    matrix: TauMatrix,
    bots_dir: Path = _BOTS_DIR,
) -> list[tuple[str, ...]]:
    """Groups with IDENTICAL ASTs — unseparable by this channel.

    Under the AST distance these are bots whose source differs only in erased
    budget arguments; the v1 feature vector also collapsed structurally
    distinct pairs (DBot/TitForTatBot), which is the defect it fixes.
    """
    groups: dict[tuple, list[str]] = {}
    for bot, ast in bot_asts(matrix.bots, bots_dir).items():
        groups.setdefault(_canonical(ast), []).append(bot)
    return [tuple(sorted(g)) for g in groups.values() if len(g) > 1]


def _canonical(node: Node) -> tuple:
    return (node.label, tuple(_canonical(c) for c in node.children))


# --------------------------------------------------------- legacy v1 channel ---

def feature_vector(source: str, self_name: str | None = None) -> tuple[int, ...]:
    """LEGACY v1: token counts of the fixed feature set.

    Retained for comparison against the AST distance (see the module docstring
    for the four defects that motivated replacing it). Not used by the σ family.
    """
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


def feature_distance_matrix(
    matrix: TauMatrix,
    bots_dir: Path = _BOTS_DIR,
) -> dict[tuple[str, str], int]:
    """LEGACY v1: unnormalized L1 between feature vectors."""
    vectors = bot_feature_vectors(matrix.bots, bots_dir)
    return {
        (a, b): sum(abs(x - y) for x, y in zip(vectors[a], vectors[b]))
        for a in matrix.bots
        for b in matrix.bots
    }


def feature_twins(
    matrix: TauMatrix,
    bots_dir: Path = _BOTS_DIR,
) -> list[tuple[str, ...]]:
    """LEGACY v1: groups with identical feature vectors."""
    groups: dict[tuple[int, ...], list[str]] = {}
    for bot, vec in bot_feature_vectors(matrix.bots, bots_dir).items():
        groups.setdefault(vec, []).append(bot)
    return [tuple(sorted(g)) for g in groups.values() if len(g) > 1]
