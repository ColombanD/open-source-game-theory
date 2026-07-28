"""Constructor integration (Stage C/D of the accepted-proposal flow).

Turns an accepted Tier-2 constructor proposal into an engine change, safely:

  Stage C (machine): an integration agent works in a GIT WORKTREE of the repo —
  never the live tree. It edits whatever the build needs (the constructor +
  `sound_upto` arm + `Pf_mono` + `Pf.induct` wiring in the engine, census/motive
  repairs, the Metatheory mirror) until BOTH lake targets are green. A compiling
  `sound_upto` arm is the machine soundness gate: the extended system is sound,
  kernel-checked in context — strictly stronger than the standalone certificate.

  Stage D (human): the resulting `git diff` is presented for review. Only on
  acceptance is the patch applied to the real tree (with rebuild + rollback on
  failure) and the proposal marked integrated.

The live engine is never touched until Stage D acceptance.
"""

from __future__ import annotations

import json
import shutil
import subprocess
from dataclasses import dataclass
from pathlib import Path

from pd_runner.config import load_paths
from pd_runner.lean.executor import build_lean_project
from pd_runner.llm.client import AnthropicClient, ToolHandler, serialize_messages
from pd_runner.logging_config import get_logger
from pd_runner.services.constructor_proposals import proposals_dir

_log = get_logger("services.constructor_integration")

_LAKE_TARGETS = ("PrisonersDilemma", "Metatheory")
_OUTPUT_TAIL = 6000  # chars of lake output returned to the agent


class IntegrationError(RuntimeError):
    pass


@dataclass(frozen=True)
class IntegrationResult:
    proposal_name: str
    diff: str                # git diff of the worktree's engine changes
    summary: str             # the agent's final report
    iterations_used: int
    worktree_root: Path      # repo-level worktree (apply/cleanup handle it)


# ---------------------------------------------------------------------------
# Git worktree management
# ---------------------------------------------------------------------------

def _git(args: list[str], cwd: Path) -> subprocess.CompletedProcess:
    return subprocess.run(["git", *args], cwd=cwd, capture_output=True, text=True, check=False)


def _repo_root() -> Path:
    paths = load_paths()
    proc = _git(["rev-parse", "--show-toplevel"], paths.lean_engine_dir)
    if proc.returncode != 0:
        raise IntegrationError(f"engine dir is not inside a git repository: {proc.stderr}")
    return Path(proc.stdout.strip())


def _engine_rel(repo_root: Path) -> Path:
    """The engine directory path relative to the repo root."""
    return load_paths().lean_engine_dir.resolve().relative_to(repo_root)


def _integrations_dir() -> Path:
    d = load_paths().app_root / "generated" / "integrations"
    d.mkdir(parents=True, exist_ok=True)
    return d


def create_worktree(proposal_name: str) -> Path:
    """Create a detached worktree at HEAD and warm its lake cache. Returns its root.

    The worktree snapshots HEAD, so uncommitted ENGINE changes would be invisible
    to the integration — that is refused up front rather than silently ignored.
    """
    repo_root = _repo_root()
    engine_rel = _engine_rel(repo_root)

    dirty = _git(["status", "--porcelain", str(engine_rel)], repo_root)
    if dirty.stdout.strip():
        raise IntegrationError(
            "the engine has uncommitted changes; commit or stash them first — the "
            "integration worktree snapshots HEAD and would not see them:\n" + dirty.stdout
        )

    wt_root = _integrations_dir() / proposal_name / "worktree"
    if wt_root.exists():
        remove_worktree(wt_root)
    wt_root.parent.mkdir(parents=True, exist_ok=True)

    proc = _git(["worktree", "add", "--detach", str(wt_root), "HEAD"], repo_root)
    if proc.returncode != 0:
        raise IntegrationError(f"git worktree add failed: {proc.stderr}")

    # Warm the lake cache so the first build is incremental, not from scratch.
    # The cache is multi-GB: on APFS use copy-on-write clones (cp -c, instant,
    # near-zero extra disk); fall back to a regular copy elsewhere.
    src_cache = load_paths().lean_engine_dir / ".lake"
    dst_cache = wt_root / engine_rel / ".lake"
    if src_cache.exists() and not dst_cache.exists():
        _log.info("Warming lake cache in worktree (cloning .lake)...")
        clone = subprocess.run(
            ["cp", "-Rc", str(src_cache), str(dst_cache)],
            capture_output=True, text=True, check=False,
        )
        if clone.returncode != 0:
            shutil.rmtree(dst_cache, ignore_errors=True)
            _log.info("clonefile copy unavailable (%s); falling back to full copy", clone.stderr.strip())
            shutil.copytree(src_cache, dst_cache, symlinks=True)

    _log.info("Integration worktree ready at %s", wt_root)
    return wt_root


def remove_worktree(wt_root: Path) -> None:
    repo_root = _repo_root()
    proc = _git(["worktree", "remove", "--force", str(wt_root)], repo_root)
    if proc.returncode != 0:
        # Fall back to manual removal + prune (e.g. cache dirs block removal).
        shutil.rmtree(wt_root, ignore_errors=True)
        _git(["worktree", "prune"], repo_root)
    _log.info("Removed integration worktree %s", wt_root)


def worktree_diff(wt_root: Path) -> str:
    """The worktree's uncommitted changes, paths relative to the repo root."""
    proc = _git(["diff"], wt_root)
    if proc.returncode != 0:
        raise IntegrationError(f"git diff failed in worktree: {proc.stderr}")
    return proc.stdout


# ---------------------------------------------------------------------------
# Agent tools (bound to the worktree's engine dir)
# ---------------------------------------------------------------------------

def _make_tools(wt_engine_dir: Path) -> tuple[list[dict], ToolHandler]:
    schemas: list[dict] = [
        {
            "name": "read_engine_file",
            "description": (
                "Read a file under the engine (PrisonersDilemma/...) in YOUR worktree. "
                "Pass a path relative to the engine dir, e.g. "
                "'PrisonersDilemma/ProofSystem.lean' or 'PrisonersDilemma/Base/Soundness.lean'."
            ),
            "input_schema": {
                "type": "object",
                "properties": {"relative_path": {"type": "string"}},
                "required": ["relative_path"],
            },
        },
        {
            "name": "edit_engine_file",
            "description": (
                "Exact-string replacement in a file under the engine in YOUR worktree. "
                "`old_string` must occur EXACTLY ONCE in the file (include enough "
                "surrounding context to make it unique); it is replaced by `new_string`. "
                "The live engine is not touched — all edits land in the worktree and are "
                "human-reviewed as a diff before integration."
            ),
            "input_schema": {
                "type": "object",
                "properties": {
                    "relative_path": {"type": "string"},
                    "old_string": {"type": "string"},
                    "new_string": {"type": "string"},
                },
                "required": ["relative_path", "old_string", "new_string"],
            },
        },
        {
            "name": "run_lake_build",
            "description": (
                "Run `lake build <target>` in your worktree's engine. Both targets must "
                "end green: 'PrisonersDilemma' (the engine) and 'Metatheory' (decidability "
                "chain). Returns exit code and the tail of the output."
            ),
            "input_schema": {
                "type": "object",
                "properties": {
                    "target": {"type": "string", "enum": list(_LAKE_TARGETS)},
                },
                "required": ["target"],
            },
        },
    ]

    def _resolve(relative_path: str) -> Path | str:
        target = (wt_engine_dir / relative_path).resolve()
        if not str(target).startswith(str(wt_engine_dir.resolve())):
            return "Error: path escapes the engine directory"
        return target

    def read_engine_file(relative_path: str) -> str:
        target = _resolve(relative_path)
        if isinstance(target, str):
            return target
        if not target.exists():
            return f"Error: file not found: {relative_path}"
        if target.is_dir():
            entries = sorted(p.name + ("/" if p.is_dir() else "") for p in target.iterdir())
            return f"(directory) {relative_path}:\n" + "\n".join(entries)
        try:
            return target.read_text(encoding="utf-8")
        except OSError as exc:
            return f"Error reading file: {exc}"

    def edit_engine_file(relative_path: str, old_string: str, new_string: str) -> str:
        target = _resolve(relative_path)
        if isinstance(target, str):
            return target
        if not target.exists():
            return f"Error: file not found: {relative_path}"
        try:
            content = target.read_text(encoding="utf-8")
        except OSError as exc:
            return f"Error reading file: {exc}"
        count = content.count(old_string)
        if count == 0:
            return "Error: old_string not found in file (must match exactly, including whitespace)"
        if count > 1:
            return f"Error: old_string occurs {count} times — add surrounding context to make it unique"
        target.write_text(content.replace(old_string, new_string, 1), encoding="utf-8")
        return f"OK — edited {relative_path}"

    def run_lake_build(target: str) -> str:
        if target not in _LAKE_TARGETS:
            return f"Error: unknown target {target!r}; use one of {_LAKE_TARGETS}"
        result = build_lean_project(wt_engine_dir, target=target)
        out = (result.stdout or "") + "\n" + (result.stderr or "")
        if len(out) > _OUTPUT_TAIL:
            out = "...(truncated)...\n" + out[-_OUTPUT_TAIL:]
        return f"exit_code: {result.returncode}\n{out}"

    handler = ToolHandler()
    handler.register_fn("read_engine_file", read_engine_file)
    handler.register_fn("edit_engine_file", edit_engine_file)
    handler.register_fn("run_lake_build", run_lake_build)
    return schemas, handler


# ---------------------------------------------------------------------------
# Prompt
# ---------------------------------------------------------------------------

def _load_proposal(proposal_name: str) -> dict:
    pdir = proposals_dir() / proposal_name
    if not pdir.exists():
        raise IntegrationError(f"no proposal named {proposal_name!r} on file")
    bundle = {"name": proposal_name, "proposal_md": (pdir / "proposal.md").read_text(encoding="utf-8")}
    cert = pdir / "soundness_certificate.lean"
    bundle["certificate"] = cert.read_text(encoding="utf-8") if cert.exists() else ""
    unblocked = pdir / "unblocked_proof.lean"
    bundle["unblocked_proof"] = unblocked.read_text(encoding="utf-8") if unblocked.exists() else ""
    return bundle


def _build_integration_prompt(bundle: dict) -> str:
    unblocked_section = (
        "\n\n# The conditional outcome proof (compiled with the rule as hypothesis)\n\n"
        "```lean\n" + bundle["unblocked_proof"] + "\n```\n"
        "Do NOT add this to the engine — it is context showing how the rule will be used."
        if bundle["unblocked_proof"] else ""
    )
    return f"""\
You are integrating an ACCEPTED constructor proposal into the Lean 4 engine of the
open-source game theory project. You work in an isolated git worktree; a human will
review your full diff before it touches the real tree.

# The accepted proposal

{bundle["proposal_md"]}

# The compiled soundness certificate (proves the rule's interp-level content)

```lean
{bundle["certificate"]}
```{unblocked_section}

# Your job — the integration checklist, in order

1. `PrisonersDilemma/ProofSystem.lean`: add the constructor to the mutual `Pf` block,
   with the exact side-conditions from the proposal. Then extend the named eliminator
   `Pf.induct` (§4 of the file) with the new arm and its wiring (`PlaysProof.induct`
   is untouched unless the rule reads plays).
2. `PrisonersDilemma/Base/Soundness.lean`: add the `sound_upto` arm for the new rule.
   The soundness certificate above IS the interp-level content — adapt its proof.
3. Extend `Pf_mono` (budget monotonicity) with the new arm.
4. Rebuild the engine (`run_lake_build` target `PrisonersDilemma`) and REPAIR what
   breaks. The census architecture is TWO-TIER: the generic KERNELS in
   `Base/Exclusion.lean` (`no_provable_tailToS_floor` + the singleton wrapper and
   its shape instances, plus `tail_plays_readable`) induct over ALL constructors —
   they are the canaries and ALWAYS need a new arm. Check first whether the new
   rule's conclusion SELF-ANNIHILATES under the Guarded invariant (its antecedent
   carries its consequent's structure, like `implRefl`/`implK`/`implS`): then the
   kernel arm is two lines and NO downstream change is needed. If instead the arm
   needs a new KERNEL HYPOTHESIS (a shape disequality or a widened tail-set, as
   `ctxChain`'s `hctx` did), every matchup-specific instance in `Theorems/*/`
   (dir-local Helpers and vs-files) gains one bullet — `lake build` will list every
   site; the repairs are mechanical one-liners. Repair proofs freely, but do NOT
   delete or weaken any theorem STATEMENT without listing it under
   `STATEMENT CHANGES:` in your final report.
5. Rebuild the metatheory (`run_lake_build` target `Metatheory`) and repair it:
   the gate-parametric mirror `PfG` (a new rule mirror + gate decision), the
   `decFull` enumerator + its completeness, the decider disjuncts, and the T49
   substrate as needed.
6. Finish ONLY when BOTH targets build green.

# Rules

- Keep the diff MINIMAL: touch only what the checklist and the build force.
- Never use `sorry`/`admit`/`axiom`/`native_decide`.
- Do not modify lakefiles, tool configs, or anything outside `PrisonersDilemma/`.
- If after honest effort a repair is beyond reach, STOP and report
  `INTEGRATION BLOCKED` with the exact failing declaration and error — an honest
  block is far more valuable than a weakened theorem.
- When both targets are green, end with `INTEGRATION COMPLETE`, a summary of every
  file you touched and why, and (if any) the `STATEMENT CHANGES:` list.
"""


# ---------------------------------------------------------------------------
# Stage C: run the integration agent
# ---------------------------------------------------------------------------

def integrate_constructor(
    proposal_name: str,
    *,
    model: str = "claude-opus-4-7",
    max_iterations: int = 60,
    max_tokens: int = 32000,
    thinking_effort: str = "medium",
) -> IntegrationResult:
    """Run the integration agent in a fresh worktree; returns the diff for review.

    Raises IntegrationError if the agent blocks, the build is not green, or the
    diff is empty. The worktree is kept on success (Stage D applies from it) and
    on failure paths that merit inspection is removed.
    """
    bundle = _load_proposal(proposal_name)
    wt_root = create_worktree(proposal_name)
    repo_root = _repo_root()
    wt_engine_dir = wt_root / _engine_rel(repo_root)

    schemas, handler = _make_tools(wt_engine_dir)
    client = AnthropicClient(
        system_prompt=_build_integration_prompt(bundle),
        tools=schemas,
        model=model,
        max_iterations=max_iterations,
        max_tokens=max_tokens,
        thinking_effort=thinking_effort,
    )

    iteration_count = [0]
    original_call = handler.call

    def counting_call(tool_name: str, tool_input):
        iteration_count[0] += 1
        return original_call(tool_name, tool_input)

    handler.call = counting_call  # type: ignore[method-assign]

    try:
        final_text = client.run(
            "Integrate the proposal following the checklist. Read the relevant files "
            "first; edit; rebuild both targets until green.",
            tool_handler=handler,
        )
    except Exception:
        remove_worktree(wt_root)
        raise

    _persist_transcript(proposal_name, serialize_messages(client.last_messages), final_text)

    if "INTEGRATION COMPLETE" not in final_text:
        remove_worktree(wt_root)
        raise IntegrationError(
            f"integration agent did not complete (kept nothing — worktree removed).\n"
            f"Final report:\n{final_text}"
        )

    # Trust nothing: re-verify both targets ourselves before offering the diff.
    for target in _LAKE_TARGETS:
        result = build_lean_project(wt_engine_dir, target=target)
        if result.returncode != 0:
            remove_worktree(wt_root)
            raise IntegrationError(
                f"agent reported completion but `lake build {target}` fails:\n"
                f"{(result.stdout or '')[-3000:]}\n{(result.stderr or '')[-3000:]}"
            )

    diff = worktree_diff(wt_root)
    if not diff.strip():
        remove_worktree(wt_root)
        raise IntegrationError("integration produced an empty diff")

    return IntegrationResult(
        proposal_name=proposal_name,
        diff=diff,
        summary=final_text,
        iterations_used=iteration_count[0],
        worktree_root=wt_root,
    )


def _persist_transcript(proposal_name: str, transcript: list, final_text: str) -> None:
    try:
        d = _integrations_dir() / proposal_name
        d.mkdir(parents=True, exist_ok=True)
        (d / "transcript.json").write_text(
            json.dumps(transcript, indent=2, ensure_ascii=False, default=str), encoding="utf-8"
        )
        (d / "report.md").write_text(final_text, encoding="utf-8")
    except (OSError, TypeError, ValueError) as exc:
        _log.warning("Could not persist integration transcript: %s", exc)


# ---------------------------------------------------------------------------
# Stage D: apply the accepted diff to the real tree
# ---------------------------------------------------------------------------

def apply_integration(result: IntegrationResult) -> None:
    """Apply the reviewed diff to the live tree, rebuild, roll back on failure."""
    repo_root = _repo_root()
    patch_path = _integrations_dir() / result.proposal_name / "accepted.patch"
    patch_path.write_text(result.diff, encoding="utf-8")

    proc = _git(["apply", "--check", str(patch_path)], repo_root)
    if proc.returncode != 0:
        raise IntegrationError(f"patch does not apply cleanly to the live tree: {proc.stderr}")
    proc = _git(["apply", str(patch_path)], repo_root)
    if proc.returncode != 0:
        raise IntegrationError(f"git apply failed: {proc.stderr}")

    engine_dir = load_paths().lean_engine_dir
    for target in _LAKE_TARGETS:
        build = build_lean_project(engine_dir, target=target)
        if build.returncode != 0:
            revert = _git(["apply", "-R", str(patch_path)], repo_root)
            raise IntegrationError(
                f"live rebuild of {target} failed — patch "
                f"{'reverted' if revert.returncode == 0 else 'REVERT FAILED (manual cleanup needed!)'}.\n"
                f"{(build.stdout or '')[-3000:]}\n{(build.stderr or '')[-3000:]}"
            )

    # Mark the proposal integrated (prompts stop listing it as pending) and clean up.
    meta_path = proposals_dir() / result.proposal_name / "meta.json"
    try:
        meta = json.loads(meta_path.read_text(encoding="utf-8"))
        meta["status"] = "integrated"
        meta_path.write_text(json.dumps(meta, indent=2), encoding="utf-8")
    except (OSError, json.JSONDecodeError) as exc:
        _log.warning("Could not mark proposal integrated: %s", exc)

    remove_worktree(result.worktree_root)
    _log.info("Constructor %s integrated into the live engine", result.proposal_name)


def discard_integration(result: IntegrationResult) -> None:
    """Reject the diff: remove the worktree, keep the transcript for post-mortem."""
    remove_worktree(result.worktree_root)
