# Foundation Dependency Decision (Milestone A)

Date: 2026-04-14
Milestone: A - Foundation Integration Layer
Status: Accepted for Milestone A

## Decision Summary
Selected mode: Direct dependency (pinned commit)

## Rationale
- Build stability: High once pinned (Lake resolves a fixed revision deterministically).
- Upstream break risk: Low in day-to-day work because updates are opt-in via explicit pin bump.
- Traceability of theorem names: High (references map 1:1 to upstream module/theorem paths).
- Reproducibility for thesis results: High (exact commit hash recorded and lockfile captured).
- Revision pinning complexity: Low (single commit hash in dependency declaration).

## Decision Record
- Foundation source: https://github.com/formalizedformallogic/foundation
- Pin type: commit
- Pin value: 956c5a2fa87d32244c9b7595b8a76c5aa4ad4769
- Upstream package metadata (verified):
	- package name: Foundation
	- upstream Lean toolchain: leanprover/lean4:v4.29.0
- Engine integration point(s):
	- engine/lakefile.toml (add Foundation dependency)
	- engine/PrisonersDilemma.lean (add import Foundation or selective module imports)
	- engine/lake-manifest.json (generated/updated by lake update)

## Concrete Setup
Recommended dependency block for `engine/lakefile.toml`:

```toml
[[require]]
name = "Foundation"
scope = "formalizedformallogic"
rev = "956c5a2fa87d32244c9b7595b8a76c5aa4ad4769"
```

If scope-based resolution is unavailable in your local Lake version, use git URL form:

```toml
[[require]]
name = "Foundation"
git = "https://github.com/formalizedformallogic/foundation.git"
rev = "956c5a2fa87d32244c9b7595b8a76c5aa4ad4769"
```

Then run:

```bash
cd engine
lake update
lake build
```

Compatibility note:
- Foundation currently targets Lean `v4.29.0`; align `engine/lean-toolchain` before integration to avoid resolver/build mismatches.

## Tradeoff Matrix

| Criterion | Direct Dependency | Vendored Subset | Chosen | Notes |
|---|---|---|---|---|
| Maintenance burden | Lower ongoing maintenance | Higher (manual sync/cherry-pick) | Direct | Avoid carrying a fork unless required. |
| Update agility | High (pin bump PR) | Medium (manual merge process) | Direct | Commit pin controls rollout safely. |
| Reproducibility | High with commit pin + manifest | High if vendor snapshot is immutable | Direct | Both can work; direct is simpler to audit. |
| Diff/audit visibility | Good with explicit pin deltas | Good for local diffs, weaker upstream trace | Direct | Upstream theorem provenance stays explicit. |
| Setup friction | Medium (toolchain sync may be needed) | Medium-high (copy + upkeep) | Direct | One-time alignment cost is acceptable. |

## Rollback Plan
- Trigger conditions:
	- Foundation pin fails to build under target CI/toolchain.
	- Required theorem identifiers moved/renamed unexpectedly.
	- New dependency causes unacceptable build time or instability.
- Fallback mode: Temporary vendored subset snapshot under `engine/` while keeping mapping docs unchanged.
- Steps:
	1. Revert `engine/lakefile.toml` Foundation require block to previous known-good pin (or remove).
	2. Run `lake update` in `engine/` to regenerate `lake-manifest.json`.
	3. If needed, import from vendored snapshot module namespace and keep wrapper names stable.
	4. Log rollback reason and blocked theorem IDs in the Milestone A gap register.

## Approval
- [x] Decision reviewed
- [x] Pin verified in build flow (`lake update && lake build` in `engine/`)
- [ ] Rollback tested at least once

## Milestone A Closeout Note
- The direct dependency decision is now build-verified in this workspace.
- Rollback remains documented but untested, so the fallback path is still a contingency rather than an exercised procedure.
