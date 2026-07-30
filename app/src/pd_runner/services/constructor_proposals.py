"""Constructor proposals (Tier 2 of the OUTCOME-OPEN escalation ladder).

When a needed principle is genuinely UNDERIVABLE from the existing `Pf` rules (Tier 1
fails), the agent may propose a NEW CONSTRUCTOR — but never applies it. Extending the
inductive changes what "compilation == correctness" means, and the project's own history
is the cautionary tale: `atom_complete_false_guard` was a human-added rule that was later
machine-checked INCONSISTENT. So proposals are evidence bundles for HUMAN review, with the
strongest machine-checkable evidence attached:

  * a **soundness certificate** — a theorem, compiled against the CURRENT unchanged
    engine, proving the rule's interp-level content (`premises.interp → conclusion.interp`
    under `Formula.interp`). Every sound rule the project ever added admits one; the
    inconsistent axiom's content is refutable, so its certificate could never compile.
    This gate rejects FALSE rules outright.
  * a **faithfulness rationale** — why a PA-like `S` (critch22 Appendix B) genuinely has
    this capability. This is the one judgment that is NOT machine-checkable (a semantic-
    completeness oracle `φ.interp → Pf k φ` is sound but destroys the Gödelian boundary),
    which is exactly why integration stays human-gated.

Integration itself (the constructor + its `sound_upto` arm + `Pf_mono`/`Pf.induct` arms +
the metatheory mirror — see `PF_ONLY_ROADMAP.md` Phase 4 for the full blast radius) is a
separate, human-initiated job. At that point the engine's own theorems form a canary
field: the floor/exclusion censuses quantify over ALL constructors, so an over-powered
rule makes them unprovable and the build fails loudly.
"""

from __future__ import annotations

import json
import re
import tempfile
from datetime import date
from pathlib import Path

from pd_runner.config import load_paths
from pd_runner.lean.executor import run_lean_proof_file
from pd_runner.logging_config import get_logger

_log = get_logger("services.constructor_proposals")

_FORBIDDEN_IN_CERT = [r"\baxiom\b", r"\bsorry\b", r"\badmit\b", r"\bnative_decide\b", r"\bunsafe\b"]


def proposals_dir() -> Path:
    # app_root/generated/… (config exposes generated_lean_dir = generated/lean)
    return load_paths().generated_lean_dir.parent / "constructor_proposals"


def _compile_in_engine(source: str, prefix: str):
    """Compile a Lean source in a temp file inside the engine dir; returns the result."""
    paths = load_paths()
    lean_dir = paths.lean_engine_dir
    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".lean", prefix=prefix, dir=lean_dir, delete=False
    ) as f:
        f.write(source)
        tmp = Path(f.name)
    try:
        return run_lean_proof_file(lean_dir, tmp)
    finally:
        tmp.unlink(missing_ok=True)


def propose(
    name: str,
    constructor_lean: str,
    soundness_certificate_lean: str,
    faithfulness_rationale: str,
    unblocks: str,
    unblocked_proof_lean: str = "",
) -> str:
    """Validate and persist a constructor proposal; returns a tool-style report.

    `unblocked_proof_lean` (optional, strongly encouraged) is the outcome proof the
    rule unblocks, with the proposed rule stated as an explicit hypothesis — compiled
    against the current engine and stored in the bundle, turning the "unblocks" claim
    into a machine artifact the integrator can reuse.
    """
    safe_name = "".join(c if c.isalnum() or c == "_" else "_" for c in name)
    if not safe_name:
        return "REJECTED: empty proposal name."

    if (proposals_dir() / safe_name).exists():
        return (
            f"REJECTED: a proposal named `{safe_name}` is already on file (awaiting human "
            "review). Do not re-file it — if it is what your proof needs, conclude "
            f"`OUTCOME OPEN — CONSTRUCTOR PROPOSED {safe_name}`. If your rule is genuinely "
            "different, use a different name."
        )

    for pattern in _FORBIDDEN_IN_CERT:
        if re.search(pattern, soundness_certificate_lean):
            return (
                f"REJECTED: the soundness certificate contains `{pattern.strip(chr(92)+'b')}` — "
                "it must be a complete, hole-free theorem compiled against the current engine."
            )
    if "theorem" not in soundness_certificate_lean and "lemma" not in soundness_certificate_lean:
        return "REJECTED: the soundness certificate must contain a `theorem` proving the rule's interp-level content."
    if len(faithfulness_rationale.strip()) < 80:
        return (
            "REJECTED: the faithfulness rationale is too thin. Explain WHY a PA-like `S` "
            "(critch22 Appendix B) genuinely has this capability — what finite syntactic "
            "activity of a real prover the rule transcribes, and why it does not smuggle in "
            "semantic completeness or general reflection."
        )

    # Compile the certificate against the CURRENT engine (temp file, like run_lean_proof).
    result = _compile_in_engine(soundness_certificate_lean, f"pd_cert_{safe_name}_")
    if result.returncode != 0:
        return (
            "CERTIFICATE FAILED TO COMPILE — the proposal was NOT recorded.\n"
            f"--- stdout ---\n{result.stdout or '(empty)'}\n"
            f"--- stderr ---\n{result.stderr or '(empty)'}\n"
            "A rule whose interp-level content cannot be proven in the current engine is "
            "either false or needs a different formulation. (Historical note: the one rule "
            "this project ever added without such a certificate was later machine-checked "
            "inconsistent.) Fix the certificate or reconsider the rule."
        )

    # Compile the conditional outcome proof (rule as hypothesis), when supplied.
    if unblocked_proof_lean.strip():
        for pattern in _FORBIDDEN_IN_CERT:
            if re.search(pattern, unblocked_proof_lean):
                return (
                    f"REJECTED: the unblocked proof contains `{pattern.strip(chr(92)+'b')}` — "
                    "it must be a complete, hole-free file with the proposed rule stated as "
                    "an explicit hypothesis. Fix it or omit unblocked_proof_lean."
                )
        result = _compile_in_engine(unblocked_proof_lean, f"pd_unblocked_{safe_name}_")
        if result.returncode != 0:
            return (
                "UNBLOCKED PROOF FAILED TO COMPILE — the proposal was NOT recorded.\n"
                f"--- stdout ---\n{result.stdout or '(empty)'}\n"
                f"--- stderr ---\n{result.stderr or '(empty)'}\n"
                "The conditional outcome proof must compile against the current engine with "
                "the proposed rule as an explicit hypothesis. Fix it, or omit "
                "unblocked_proof_lean and describe the unblocked theorem in `unblocks` only."
            )

    out = proposals_dir() / safe_name
    out.mkdir(parents=True, exist_ok=True)
    (out / "soundness_certificate.lean").write_text(soundness_certificate_lean, encoding="utf-8")
    has_unblocked_proof = bool(unblocked_proof_lean.strip())
    if has_unblocked_proof:
        (out / "unblocked_proof.lean").write_text(unblocked_proof_lean, encoding="utf-8")
    unblocked_proof_section = (
        "\n## Conditional outcome proof — COMPILED with the rule as hypothesis\n\n"
        "`unblocked_proof.lean` (in this directory) proves the unblocked outcome theorem "
        "against the CURRENT engine, with the proposed constructor stated as an explicit "
        "hypothesis. After integration, discharge the hypothesis with the real constructor.\n"
        if has_unblocked_proof else ""
    )
    (out / "proposal.md").write_text(
        f"""# Constructor proposal: `{safe_name}`

*Filed by the proof agent on {date.today().isoformat()}. Status: **awaiting human review**.*

## The proposed `Pf` constructor

```lean
{constructor_lean.strip()}
```

## Soundness certificate — COMPILED against the current engine

`soundness_certificate.lean` (in this directory) proves the rule's interp-level content
as a theorem over the UNCHANGED engine. This machine-checks that the rule is TRUE; it
does not (and cannot) check faithfulness.

## Faithfulness rationale (agent-authored — REVIEW THIS)

{faithfulness_rationale.strip()}

## What this unblocks

{unblocks.strip()}
{unblocked_proof_section}
## Integration checklist (human-initiated; see PF_ONLY_ROADMAP.md Phase 4 for scope)

- [ ] Faithfulness reviewed: is this a genuine capability of a PA-like `S`?
- [ ] Cost model reviewed: does the side-condition charge the transcript honestly?
- [ ] Constructor added to `ProofSystem.lean` (+ `sound_upto` arm, `Pf_mono` arm,
      `Pf.induct` hypothesis + wiring, `PlaysProof.induct` untouched)
- [ ] Engine target green — the floor/exclusion censuses are the canaries
- [ ] Metatheory: `PfG` mirror rule (+ gate decision), decider disjunct + completeness,
      T49 substrate node; both targets green
- [ ] Golden outcome inventory re-diffed
""",
        encoding="utf-8",
    )
    (out / "meta.json").write_text(
        json.dumps({
            "name": safe_name,
            "date": date.today().isoformat(),
            "unblocks": unblocks,
            "has_unblocked_proof": has_unblocked_proof,
        }, indent=2),
        encoding="utf-8",
    )
    _log.info("Constructor proposal recorded: %s", out)
    return (
        f"PROPOSAL RECORDED at generated/constructor_proposals/{safe_name}/ — the soundness "
        "certificate compiled against the current engine. The engine itself was NOT modified; "
        "a human will review the faithfulness rationale before any integration. You may now "
        f"finish with `submit_verdict(verdict=\"constructor_proposed\", "
        f"proposal_name=\"{safe_name}\", …)` and a short summary in `explanation`."
    )
