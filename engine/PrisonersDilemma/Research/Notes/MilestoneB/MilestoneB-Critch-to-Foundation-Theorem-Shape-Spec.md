# Milestone B Spec: Critch-to-Foundation Theorem Shape

Date: 2026-04-15
Project: open-source-game-theory (Lean engine)
Roadmap Reference: Modal Logic + CUPOD Formalization Roadmap
Prerequisite: Milestone A complete
Status: Complete (documentation-level decision milestone)

## Milestone Objective
Identify the Lean theorem shape that best plays the role of Critch Lemma 3.6 inside the Foundation-backed proof pipeline, then stabilize that choice as the interface for later CUPOD integration.

## Milestone Completion Mode
Milestone B is a documentation-first milestone.
- Required: theorem-shape decision, interface contract, and mismatch/carry-over logging.
- Not required: new Lean wrapper modules or proof code in this milestone.

## In Scope
- Compare the existing Foundation candidates against the intended Critch Lemma 3.6 role.
- Encode the theorem-shape choice in a small local specification.
- Define the minimal wrapper boundary needed to use the chosen theorem in later milestones.
- Record any mismatch between the intended Critch statement and the available Foundation theorem family.

## Out of Scope
- Proving CUPOD self-play.
- Adding CUPOD model code.
- Closing all remaining Foundation gaps.
- Reworking Foundation internals.

## Inputs from Milestone A
- [Foundation Concept Mapping](../MilestoneA/Foundation-Concept-Mapping.md)
- [Foundation Dependency Decision](../MilestoneA/Foundation-Dependency-Decision.md)
- [Foundation Gap Register](../MilestoneA/Foundation-Gap-Register.md)
- Build-verified Foundation integration in `engine/`

## Candidate Theorem Family
Use the Milestone A mapping as the starting shortlist:
- `LO.ProvabilityLogic.GLPlusBoxBot.arithmetical_completeness_iff`
- `LO.Modal.Logic.iff_provable_GL_provable_box_S`
- `LO.Modal.iff_provable_boxdot_GL_provable_Grz`

## Initial Recommendation
Working choice:
- Primary theorem shape: `LO.ProvabilityLogic.GLPlusBoxBot.arithmetical_completeness_iff`
- Supporting bridge: `LO.Modal.iff_provable_boxdot_GL_provable_Grz`
- Secondary fallback: `LO.Modal.Logic.iff_provable_GL_provable_box_S`

Rationale:
- The primary theorem is the closest match to a completeness-style Lemma 3.6 role.
- It keeps the interface centered on provability/completeness rather than a more specialized translation lemma.
- The other two candidates are better treated as bridge theorems that normalize the statement into the GL/Grz and boxdot forms needed later.

## Lemma 3.6 Role Contract (Lean-Level, Project-Neutral)
Intended role of the selected theorem shape:
- Inputs:
	- a provability-logic/arithmetic context compatible with Foundation completeness theorems,
	- assumptions needed to interpret the chosen modal fragment,
	- optional bridge assumptions when translating across GL/Grz/boxdot.
- Output:
	- an equivalence-style completeness statement that can be used as the proof-theoretic handoff point for later CUPOD arguments.
- Deferred parameterization:
	- any explicit CUPOD/self-play indexing (for example `k`) is attached in Milestones C/E through a local wrapper statement, not in Milestone B.

## Candidate Comparison Table
| Candidate | Semantic Fit to Lemma 3.6 Role | Glue Needed | Bridge Strength | Risk | Decision |
|---|---|---|---|---|---|
| `LO.ProvabilityLogic.GLPlusBoxBot.arithmetical_completeness_iff` | High (completeness-style core) | Low | Medium | Medium (later parameterization) | Primary |
| `LO.Modal.iff_provable_boxdot_GL_provable_Grz` | Medium (translation bridge) | Low | High | Low | Supporting Bridge |
| `LO.Modal.Logic.iff_provable_GL_provable_box_S` | Medium (alternate bridge path) | Medium | Medium | Medium | Fallback |

## Working Interface Draft
- Expose one local alias or wrapper for the primary theorem shape.
- Keep the wrapper name Critch-facing, not Foundation-facing.
- Let later milestones assume:
	- a completeness-style theorem exists for the chosen modal fragment,
	- translation lemmas can be attached as separate bridge facts,
	- no local re-proof of the Foundation theorem is required.

Documentation-level interface boundary for Milestone C:
- Proposed interface name: `critchLemma36Shape`
- Expected assumptions: Foundation-compatible provability/completeness context.
- Expected conclusion: completeness-style equivalence handoff theorem for downstream CUPOD reasoning.
- Implementation timing: Lean declaration and wrapper code deferred to Milestone C (or E if extra glue is needed).

## Known Mismatch
- Critch Lemma 3.6 may be parameterized by the program size `k` or by a specific self-play encoding.
- Foundation currently gives theorem families, not a project-specific statement with CUPOD naming.
- This mismatch should become a named wrapper or gap in Milestone E/F if the final Lean statement needs extra parameters.

## Open for E/F
- E-carryover-1: encode the final `k`-aware/CUPOD-aware local theorem statement around the selected Foundation shape.
- E-carryover-2: resolve any remaining GL/Grz normalization detail not covered by the chosen bridge theorem in C/D.
- F-carryover-1: only if needed, add minimal local extension lemmas after C/D usage reveals a true gap.

## Selection Criteria
Choose the theorem shape that best satisfies all of the following:
- Matches the semantic role of Critch Lemma 3.6, not just the surface phrasing.
- Minimizes local glue code.
- Preserves a clear bridge to GL/Grz completeness or boxdot translation.
- Can be stated cleanly as a reusable Lean interface for later milestones.
- Avoids introducing duplicate modal/provability reasoning locally.

## Deliverables
1. Theorem Shape Decision
- A single preferred theorem family for the Lemma 3.6 role.
- A brief justification for why it is preferred over the alternatives.

2. Interface Draft
- A minimal local wrapper or alias, if needed, for the chosen theorem shape.
- A short note explaining what later milestones may assume from it.

3. Mismatch Log
- Any part of the Critch statement that is not directly covered by Foundation.
- Any follow-up gap that must move to Milestone E or F.

## Acceptance Criteria
Milestone B is complete when all are true:
- A preferred theorem shape is selected.
- The choice is documented in this folder.
- The local interface boundary is small and explicit (documentation-level is sufficient for Milestone B).
- Any unresolved mismatch is recorded as a named gap or follow-up note.
- The selection is stable enough for Milestone C to build on.

## Execution Checklist
- [x] Restate the intended role of Critch Lemma 3.6 in Lean terms.
- [x] Compare the three Foundation candidates against that role.
- [x] Pick the preferred theorem shape and document the reason.
- [x] Draft the smallest possible local interface contract around the chosen theorem (documentation-level).
- [x] Record any remaining mismatch for Milestone E/F.
- [x] Update the roadmap once the selection is stable.

## Notes
- This milestone is about selecting the proof interface, not proving the final CUPOD result.
- If the Critch statement decomposes into multiple Foundation theorems, prefer a primary theorem plus a named bridge lemma rather than forcing one oversized wrapper.
- Keep the spec narrow enough that Milestone C can depend on it directly.
