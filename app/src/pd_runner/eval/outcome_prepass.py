"""Deterministic outcome pre-pass via the engine's certified evaluator `evalG`.

Computes game outcomes for bot pairs BEFORE any LLM is involved, using
`PD.T31.outcomeG (guardFast fuelD)` — every `some (a, b)` it prints is
machine-certified to equal the classical `outcome` (`outcomeG_sound ∘
guardFast_sound`). Feed the determined cells to the proof agent as known
targets (statement first, proof second) instead of letting it burn
iterations discovering the outcome; `none` cells flag Löb boundaries,
budget floors, or guard shapes beyond the fast decider.

Run with:
    uv run python -m pd_runner.eval.outcome_prepass
    uv run python -m pd_runner.eval.outcome_prepass --bots GuardianBot --opponents CooperateBot,DefectBot
    uv run python -m pd_runner.eval.outcome_prepass --budgets 2,4 --resume

Design notes (calibrated 2026-07-29, hardened after two machine crashes):
  * One `lake env lean` process PER PAIR. Batched #evals looked attractive,
    but a pathological cell dies silently (interpreter stack overflow) and
    takes the whole batch's buffered output with it. Process isolation +
    wall-clock timeout is the only robust shape; olean loading amortizes
    through the OS file cache (~60s cold, ~10-30s warm on OneDrive).
  * Every lean process runs under a HARD MEMORY CAP (`lean -M`): the decFull
    hop sweeps on searcher-vs-searcher cells at k>2 balloon to many GB in
    seconds and took the whole machine down twice (unbounded, 3-6 workers).
    With the cap they die in ~10s with a clean `memory_exception`.
  * Both-searcher cells at k>2 are SKIPPED by default (100% infeasible in
    calibration); pass --force-hard to attempt them anyway.
  * Results append to JSONL as they complete (crash-proof); --resume skips
    cells already recorded.
  * The guard is `guardFastN` (2026-07-29): plays-atoms via `guardFast`,
    `.neg (.plays ...)` goal-directed in BOTH polarities (`Pf.atomNeg` + its
    certificate supplier), and every other non-atom shape committed FALSE
    when oversized (`k < φ.size` — the `pf_size_or_atom` size floor). Cells
    still undetermined for `.impl`/`.eq`/`.box` guards small enough to fire
    are annotated; `guardFull` handles those in principle but is infeasible
    in practice (silent death even at budget 2), so it is not used.
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import tempfile
import threading
import time
from collections.abc import Callable
from concurrent.futures import ThreadPoolExecutor, as_completed
from dataclasses import asdict, dataclass
from pathlib import Path

from pd_runner.config import load_paths

# ---------------------------------------------------------------------------
# Bot registry: name -> (module, expr template, search-guard shape).
# `expr` may use `{k}` for the budget parameter. `guard` is the top-level
# guard-formula shape of the bot's `.search` nodes (None = no search at all);
# `guardFast` can only commit on "plays".
#
# ARITY IS LOAD-BEARING. A bot taking two `Nat` budgets (`OptimBot`,
# `LegibleBot`) applied to one argument elaborates to `Nat → Prog`, not `Prog`
# — `outcomeG` then yields nothing and EVERY cell reads `undetermined`/`oom`
# at every budget against every opponent, which is indistinguishable from a
# genuine Löb boundary in the output. This silently invalidated the whole
# OptimBot row until 2026-08-05. `verify_registry_arity` below cross-checks
# each template against the binder list in the bot's own .lean source; call it
# from tests, and use `bot_spec_from_source` for freshly generated bots rather
# than hand-writing an entry.
# ---------------------------------------------------------------------------

_BOTS_NS = "PrisonersDilemma.Bots"
_LLM_NS = f"{_BOTS_NS}.LlmGenerations"


@dataclass(frozen=True)
class BotSpec:
    module: str
    expr: str
    guard: str | None  # "plays" | "neg" | "impl" | "eq" | "box" | None

    @property
    def arity(self) -> int:
        """Number of `{k}` budget slots this template applies."""
        return self.expr.count("{k}")


REGISTRY: dict[str, BotSpec] = {
    # constant / sim / ite bots — no proof search
    "CooperateBot": BotSpec(f"{_BOTS_NS}.CooperateBot", "CooperateBot", None),
    "DefectBot": BotSpec(f"{_BOTS_NS}.DefectBot", "DefectBot", None),
    "MirrorBot": BotSpec(f"{_BOTS_NS}.MirrorBot", "MirrorBot", None),
    "TitForTatBot": BotSpec(f"{_BOTS_NS}.TitForTatBot", "TitForTatBot", None),
    "EBot": BotSpec(f"{_BOTS_NS}.EBot", "EBot", None),
    "OBot": BotSpec(f"{_BOTS_NS}.OBot", "OBot", None),
    "DBot": BotSpec(f"{_BOTS_NS}.DBot", "DBot", None),
    # hand-written searchers
    "CupodBot": BotSpec(f"{_BOTS_NS}.CupodBot", "CupodBot {k}", "plays"),
    "DupocBot": BotSpec(f"{_BOTS_NS}.DupocBot", "DupocBot {k}", "plays"),
    "CupodTrollBot": BotSpec(f"{_BOTS_NS}.CupodTrollBot", "CupodTrollBot {k}", "eq"),
    # LLM-generation searchers
    "PrudentBot": BotSpec(f"{_LLM_NS}.PrudentBot", "PrudentBot {k}", "plays"),
    "JustBot": BotSpec(f"{_LLM_NS}.JustBot", "JustBot {k}", "plays"),
    "CIMCIC": BotSpec(f"{_LLM_NS}.CIMCIC", "CIMCIC {k}", "impl"),
    "DIMCID": BotSpec(f"{_LLM_NS}.DIMCID", "DIMCID {k}", "impl"),
    "OptimBot": BotSpec(f"{_LLM_NS}.OptimBot", "OptimBot {k} {k}", "plays"),
    "WaryBot": BotSpec(f"{_LLM_NS}.WaryBot", "WaryBot {k}", "neg"),
    "LegibleBot": BotSpec(f"{_LLM_NS}.LegibleBot", "LegibleBot {k} {k}", "box"),
    "GuardianBot": BotSpec(f"{_LLM_NS}.GuardianBot", "GuardianBot {k}", "plays"),
}

_DECIDER_MODULE = "PrisonersDilemma.Decidability.T31EngineDecider"
_DEFAULT_BOTS = "OptimBot,WaryBot,LegibleBot,GuardianBot"

# `def BotName (k : Nat) (j : Nat) : Prog` / `def BotName (k j : Nat) : Prog`
# Binders are parenthesised groups, so they may contain `:` — match them
# explicitly rather than with a colon-free run (which never matches `(k : Nat)`).
_DEF_RE_TMPL = r"^\s*def\s+{name}\s*(?P<binders>(?:\([^)]*\)\s*)*):\s*Prog\b"
_BINDER_RE = re.compile(r"\(([^:()]+):\s*Nat\s*\)")
# Head of the first `.search`'s guard formula: `.search <budget> (.plays ...`
_GUARD_RE = re.compile(r"\.search\s+\S+\s*\(\s*\.(plays|neg|impl|eq|box)\b")


def _lean_source_for(module: str, engine_dir: Path) -> str:
    return (engine_dir / Path(*module.split("."))).with_suffix(".lean").read_text(
        encoding="utf-8"
    )


def arity_from_source(name: str, source: str) -> int:
    """Count `Nat` budget binders on `def <name> ... : Prog`.

    Handles both `(k : Nat) (j : Nat)` and the grouped `(k j : Nat)` form.
    Returns 0 for a bot with no budget parameter (constant/sim/ite bots).
    """
    m = re.search(_DEF_RE_TMPL.format(name=re.escape(name)), source, re.MULTILINE)
    if not m:
        raise ValueError(f"no `def {name} ... : Prog` found in source")
    return sum(len(g.split()) for g in _BINDER_RE.findall(m.group("binders")))


def guard_from_source(source: str) -> str | None:
    """Guard-formula head of the bot's first `.search`, or None if search-free."""
    m = _GUARD_RE.search(source)
    return m.group(1) if m else None


def bot_spec_from_source(name: str, module: str, source: str) -> BotSpec:
    """Derive a BotSpec from a bot's Lean source — never guess arity."""
    arity = arity_from_source(name, source)
    expr = " ".join([name, *["{k}"] * arity])
    return BotSpec(module=module, expr=expr, guard=guard_from_source(source))


def verify_registry_arity(engine_dir: Path) -> dict[str, str]:
    """Cross-check every REGISTRY template against its .lean source.

    Returns {bot_name: complaint} for mismatches; empty dict means clean.
    Intended for tests and for a preflight check before a long sweep.
    """
    problems: dict[str, str] = {}
    for name, spec in REGISTRY.items():
        try:
            source = _lean_source_for(spec.module, engine_dir)
            expected = arity_from_source(name, source)
        except (OSError, ValueError) as exc:
            problems[name] = f"could not read/parse source: {exc}"
            continue
        if spec.arity != expected:
            problems[name] = (
                f"template {spec.expr!r} applies {spec.arity} budget arg(s) but "
                f"`def {name}` takes {expected} — the term will not elaborate to Prog"
            )
    return problems

_OUTCOME_RE = re.compile(r"some \(PD\.Action\.([CD]), PD\.Action\.([CD])\)")
_OOM_RE = re.compile(r"memory_exception|excessive memory consumption")


@dataclass
class CellResult:
    left: str
    right: str
    budget: int
    fuel_d: int
    fuel: int
    status: str  # determined | undetermined | timeout | oom | skipped | error
    outcome: str | None  # e.g. "(C, D)"
    note: str
    seconds: float


def _scratch_source(left: BotSpec, right: BotSpec, k: int, fuel_d: int, fuel: int) -> str:
    imports = sorted({left.module, right.module, _DECIDER_MODULE})
    lines = [f"import {m}" for m in imports]
    lines += [
        "open PD PD.Bots PD.T31",
        f"#eval outcomeG (guardFastN {fuel_d}) {fuel} "
        f"({left.expr.format(k=k)}) ({right.expr.format(k=k)})",
    ]
    return "\n".join(lines) + "\n"


def _undetermined_note(
    left_name: str, right_name: str, k: int,
    registry: dict[str, BotSpec] | None = None,
) -> str:
    reg = registry if registry is not None else REGISTRY
    exotic = [
        f"{n} ({reg[n].guard} guard)"
        for n in (left_name, right_name)
        if reg[n].guard not in (None, "plays", "neg")
    ]
    if exotic:
        return ("guard fits budget but shape is beyond guardFastN: "
                + ", ".join(exotic))
    return f"Löb boundary or budget floor at k={k}"


def _both_searchers(
    left_name: str, right_name: str,
    registry: dict[str, BotSpec] | None = None,
) -> bool:
    reg = registry if registry is not None else REGISTRY
    return reg[left_name].guard is not None and reg[right_name].guard is not None


def _run_cell(
    engine_dir: Path,
    left_name: str,
    right_name: str,
    k: int,
    fuel_d: int,
    fuel: int,
    timeout: int,
    memory_mb: int,
    registry: dict[str, BotSpec] | None = None,
) -> CellResult:
    reg = registry if registry is not None else REGISTRY
    left, right = reg[left_name], reg[right_name]
    start = time.monotonic()
    with tempfile.NamedTemporaryFile(
        "w", suffix=".lean", prefix="prepass_", dir="/tmp", delete=False
    ) as fh:
        fh.write(_scratch_source(left, right, k, fuel_d, fuel))
        scratch = Path(fh.name)
    try:
        proc = subprocess.run(
            ["lake", "env", "lean", "-M", str(memory_mb), str(scratch)],
            cwd=engine_dir,
            capture_output=True,
            text=True,
            timeout=timeout,
        )
    except subprocess.TimeoutExpired:
        return CellResult(
            left_name, right_name, k, fuel_d, fuel, "timeout", None,
            f"no verdict within {timeout}s (decFull hop sweep)",
            time.monotonic() - start,
        )
    finally:
        scratch.unlink(missing_ok=True)

    elapsed = time.monotonic() - start
    out = proc.stdout + proc.stderr
    m = _OUTCOME_RE.search(out)
    if m:
        return CellResult(
            left_name, right_name, k, fuel_d, fuel, "determined",
            f"({m.group(1)}, {m.group(2)})", "certified: outcomeG_sound ∘ guardFast_sound",
            elapsed,
        )
    if _OOM_RE.search(out):
        return CellResult(
            left_name, right_name, k, fuel_d, fuel, "oom", None,
            f"decFull sweep exceeded {memory_mb}MB cap — infeasible at this budget",
            elapsed,
        )
    if re.search(r"^none$", out, flags=re.MULTILINE):
        return CellResult(
            left_name, right_name, k, fuel_d, fuel, "undetermined", None,
            _undetermined_note(left_name, right_name, k, reg), elapsed,
        )
    tail = " | ".join(line for line in out.strip().splitlines() if "batteries" not in line)[-300:]
    return CellResult(
        left_name, right_name, k, fuel_d, fuel, "error", None,
        f"exit {proc.returncode}: {tail or 'no output (likely interpreter stack overflow)'}",
        elapsed,
    )


def _ensure_built(
    engine_dir: Path, names: list[str],
    registry: dict[str, BotSpec] | None = None,
) -> None:
    reg = registry if registry is not None else REGISTRY
    modules = sorted({reg[n].module for n in names} | {_DECIDER_MODULE})
    print(f"Building {len(modules)} modules (no-op when cached)...")
    proc = subprocess.run(
        ["lake", "build", *[f"+{m}" for m in modules]],
        cwd=engine_dir,
        capture_output=True,
        text=True,
        timeout=1800,
    )
    if proc.returncode != 0:
        raise SystemExit(f"lake build failed:\n{proc.stdout}\n{proc.stderr}")


def _print_report(results: list[CellResult]) -> None:
    if not results:
        print("no results")
        return
    width = max(len(f"{r.left} vs {r.right}") for r in results) + 2
    print()
    for k in sorted({r.budget for r in results}):
        print(f"=== budget k={k} ===")
        for r in sorted(results, key=lambda r: (r.left, r.right)):
            if r.budget != k:
                continue
            cell = r.outcome if r.outcome else r.status.upper()
            print(f"  {f'{r.left} vs {r.right}':<{width}} {cell:<14} [{r.seconds:5.1f}s] {r.note}")
    counts = {s: sum(1 for r in results if r.status == s) for s in
              ("determined", "undetermined", "timeout", "oom", "skipped", "error")}
    print(f"\n{counts['determined']}/{len(results)} cells determined "
          f"({', '.join(f'{v} {s}' for s, v in counts.items() if s != 'determined' and v)})")
    determined = [r for r in results if r.status == "determined"]
    if determined:
        print("\nProof-agent targets (highest determined budget per pair):")
        best: dict[tuple[str, str], CellResult] = {}
        for r in determined:
            key = (r.left, r.right)
            if key not in best or r.budget > best[key].budget:
                best[key] = r
        for r in best.values():
            a, b = r.outcome.strip("()").split(", ")
            print(
                f"  llm_outcome_{r.left}_vs_{r.right} (k={r.budget}): "
                f"= some (.{a}, .{b})"
            )


def run_cells(
    pairs: list[tuple[str, str, int]],
    *,
    registry: dict[str, BotSpec] | None = None,
    engine_dir: Path | None = None,
    fuel: int = 64,
    fuel_d: int | None = None,
    timeout: int = 90,
    memory_mb: int = 3072,
    jobs: int = 2,
    force_hard: bool = False,
    ensure_built: bool = True,
    on_result: Callable[[CellResult], None] | None = None,
    progress: Callable[[str], None] | None = None,
) -> list[CellResult]:
    """Evaluate `(left, right, budget)` cells with the certified evaluator.

    The library entry point behind the CLI: no argparse, no JSONL, no printing
    unless `progress` is supplied. Every `determined` result carries a
    machine-certified outcome (`outcomeG_sound ∘ guardFast_sound`).

    `registry` defaults to the module REGISTRY; pass a superset to include
    freshly generated bots (see `bot_spec_from_source`). `on_result` fires as
    each cell completes — use it to append to JSONL or drive a progress bar.
    Results come back in completion order, not input order.
    """
    reg = registry if registry is not None else REGISTRY
    engine = engine_dir if engine_dir is not None else load_paths().lean_engine_dir

    unknown = {n for (l, r, _) in pairs for n in (l, r) if n not in reg}
    if unknown:
        raise ValueError(f"unknown bot(s): {', '.join(sorted(unknown))}")

    if ensure_built:
        _ensure_built(engine, sorted({n for (l, r, _) in pairs for n in (l, r)}), reg)

    results: list[CellResult] = []
    write_lock = threading.Lock()

    def record(res: CellResult) -> None:
        with write_lock:
            results.append(res)
            if on_result is not None:
                on_result(res)

    tasks: list[tuple[str, str, int]] = []
    for (left, right, k) in pairs:
        if _both_searchers(left, right, reg) and k > 2 and not force_hard:
            record(CellResult(
                left, right, k, fuel_d if fuel_d is not None else k, fuel, "skipped", None,
                "both-searcher cell at k>2 (infeasible in calibration; force_hard to attempt)",
                0.0,
            ))
            continue
        tasks.append((left, right, k))

    with ThreadPoolExecutor(max_workers=jobs) as pool:
        futures = {
            pool.submit(
                _run_cell, engine, l, r, k,
                fuel_d if fuel_d is not None else k, fuel, timeout, memory_mb, reg,
            ): (l, r, k)
            for (l, r, k) in tasks
        }
        completed = 0
        for fut in as_completed(futures):
            res = fut.result()
            record(res)
            completed += 1
            if progress is not None:
                progress(
                    f"  [{completed}/{len(tasks)}] {res.left} vs {res.right} "
                    f"@k={res.budget}: {res.outcome or res.status.upper()}"
                )
    return results


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--bots", default=_DEFAULT_BOTS, help="comma-separated left-side bots")
    parser.add_argument("--opponents", default=",".join(REGISTRY), help="comma-separated right-side bots")
    parser.add_argument("--budgets", default="2,4", help="comma-separated guard budgets k")
    parser.add_argument("--fuel", type=int, default=64, help="evalG evaluator fuel")
    parser.add_argument("--fuel-d", type=int, default=None, help="guardFast decider fuel (default: k)")
    parser.add_argument("--timeout", type=int, default=90, help="per-pair wall-clock timeout (s)")
    parser.add_argument("--memory-mb", type=int, default=3072, help="per-pair lean memory cap (MB)")
    parser.add_argument("--jobs", type=int, default=2, help="concurrent lean processes")
    parser.add_argument("--force-hard", action="store_true",
                        help="also attempt both-searcher cells at k>2 (infeasible in calibration)")
    parser.add_argument("--resume", action="store_true", help="skip cells already in the output JSONL")
    parser.add_argument("--output", default=None, help="JSONL output path (appended per cell)")
    args = parser.parse_args()

    bots = [b.strip() for b in args.bots.split(",") if b.strip()]
    opponents = [b.strip() for b in args.opponents.split(",") if b.strip()]
    budgets = [int(k) for k in args.budgets.split(",")]
    for name in bots + opponents:
        if name not in REGISTRY:
            raise SystemExit(f"unknown bot {name!r}; known: {', '.join(REGISTRY)}")

    paths = load_paths()
    engine_dir = paths.lean_engine_dir
    out_path = Path(args.output) if args.output else (
        paths.app_root / "generated" / "prepass" / "prepass.jsonl"
    )
    out_path.parent.mkdir(parents=True, exist_ok=True)

    done: dict[tuple[str, str, int], CellResult] = {}
    if args.resume and out_path.exists():
        for line in out_path.read_text().splitlines():
            if line.strip():
                r = CellResult(**json.loads(line))
                done[(r.left, r.right, r.budget)] = r
        print(f"resume: {len(done)} cells already recorded in {out_path}")

    # Ordered pairs, deduped by unordered key: outcomeG (l, r) already yields
    # both plays, so (r, l) would be redundant (it is the swap).
    seen: set[frozenset[str]] = set()
    pairs: list[tuple[str, str]] = []
    for left in bots:
        for right in opponents:
            key = frozenset((left, right))
            if key in seen and left != right:
                continue
            seen.add(key)
            pairs.append((left, right))

    cells = [
        (l, r, k)
        for (l, r) in pairs
        for k in budgets
        if (l, r, k) not in done and (r, l, k) not in done
    ]

    print(f"{len(cells)} cells to run ({args.jobs} workers, {args.timeout}s timeout, "
          f"{args.memory_mb}MB cap each)")

    def append_jsonl(res: CellResult) -> None:
        with out_path.open("a") as fh:
            fh.write(json.dumps(asdict(res)) + "\n")

    fresh = run_cells(
        cells,
        engine_dir=engine_dir,
        fuel=args.fuel,
        fuel_d=args.fuel_d or None,  # CLI treats 0 as unset (pre-existing behavior)
        timeout=args.timeout,
        memory_mb=args.memory_mb,
        jobs=args.jobs,
        force_hard=args.force_hard,
        on_result=append_jsonl,
        progress=print,
    )

    _print_report(list(done.values()) + fresh)
    print(f"\nresults in {out_path}")


if __name__ == "__main__":
    main()
