# Foundation Gap Register (Milestone A)

Date: 2026-04-14
Milestone: A - Foundation Integration Layer
Status: Closed for Milestone A handoff

## Purpose
Track unresolved wrappers, assumptions, and missing theorem links discovered during Foundation mapping.

## Gap Table

| Gap ID | Description | Current Workaround | Target Foundation Asset | Owner | Closure Milestone (E/F) | Status |
|---|---|---|---|---|---|---|
| GAP-A-001 | Foundation dependency not yet wired into engine build graph. | Planning docs only; no Lake dependency in engine. | Foundation package via `[[require]]` in engine/lakefile.toml pinned to commit `956c5a2fa87d32244c9b7595b8a76c5aa4ad4769`. | Build/Infra | E | Closed (Foundation-backed) |
| GAP-A-002 | Lean toolchain mismatch risk between engine and Foundation (`v4.29.0` upstream). | Deferred until dependency integration PR. | Foundation `lean-toolchain` compatibility (Lean 4.29.0). | Build/Infra | E | Closed (Compatible) |
| GAP-A-003 | No canonical engine-side import boundary for Foundation yet. | Implicit plan to import from root module only. | `Foundation` root import and selective module imports (for example `Foundation.Modal.Boxdot.GL_Grz`). | Engine/Proof | E | Closed (Foundation-backed) |
| GAP-A-004 | Critch Lemma 3.6 role is not yet encoded as a Lean theorem signature in this repo. | Candidate list tracked in concept mapping note. | Candidate theorem family: `LO.ProvabilityLogic.GLPlusBoxBot.arithmetical_completeness_iff`, `LO.Modal.Logic.iff_provable_GL_provable_box_S`, `LO.Modal.iff_provable_boxdot_GL_provable_Grz`. | Proof | E | Validated Candidate |
| GAP-A-005 | GL vs Grz theorem path for CUPOD proof pipeline is not finalized. | Keep both paths open in mapping docs. | Bridge theorem: `LO.Modal.iff_provable_boxdot_GL_provable_Grz`; completeness endpoints for GL/Grz. | Proof | E | Open |
| GAP-A-006 | Minimal glue API surface is not yet codified in Lean declarations. | Documented conceptually in Milestone A spec only. | Local wrapper layer over Foundation theorem calls in engine namespace (no re-proofs). | Engine/Proof | F | Open |
| GAP-A-007 | No verification run proving pinned dependency builds in this workspace. | Manual inspection of upstream metadata only. | `lake update && lake build` success in engine with Foundation dependency enabled. | Build/Infra | E | Closed (Verified) |
| GAP-A-008 | Temporary assumptions/wrappers are not yet tracked as code-level annotations. | Tracking currently exists only in Markdown notes. | Inline comments/docstrings on each wrapper with target Foundation identifier and closure milestone. | Engine/Proof | F | Open |

## Logging Rules
- Every temporary wrapper must have one gap entry.
- Every gap must point to an intended upstream theorem/module target.
- If a gap is resolved by existing Foundation material, note exact identifier and close entry.

## Status Legend
- Open
- Validated Candidate
- Implemented Locally (Temporary)
- Closed (Foundation-backed)

## Weekly Review
- [x] Open gaps re-triaged
- [x] Owners confirmed
- [x] Closures linked to concrete commits/notes

## Milestone A Handoff Summary
- Closed for A: GAP-A-001, GAP-A-002, GAP-A-003, GAP-A-007.
- Still active for later milestones: GAP-A-004, GAP-A-005, GAP-A-006, GAP-A-008.
- Build verification is complete and the Foundation pin is reproducible in this workspace.
