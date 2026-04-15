# Milestone A Spec: Foundation Integration Layer

Date: 2026-04-14
Project: open-source-game-theory (Lean engine)
Roadmap Reference: Modal Logic + CUPOD Formalization Roadmap

## Milestone Objective
Map project requirements for modal/provability logic onto FormalizedFormalLogic/Foundation, so Foundation can serve as the default backend for the CUPOD theorem pipeline.

## In-Scope
- Identify Foundation modules and theorem families relevant to:
  - modal logic syntax/semantics
  - provability logic (GL/Grz where applicable)
  - boxdot-style translation and arithmetical completeness hooks
- Define a concept mapping from local project terms to Foundation concepts.
- Decide dependency strategy:
  - direct Foundation dependency, or
  - vendored subset with clear rationale.
- Define the minimum local glue interface required in engine code.

## Out-of-Scope
- Proving CUPOD self-play theorem itself (Milestone D).
- Full reimplementation of modal/provability infrastructure locally.
- Deep encoding of proof strings/verifier internals.

## Deliverables
1. Foundation Mapping Table
- A concrete table from project concepts to Foundation modules/theorems.
- Each row includes status: available, wrapper needed, or gap.

2. Dependency Decision Record
- Chosen integration mode (direct or vendored).
- Tradeoff summary: maintenance, reproducibility, update cost, proof traceability.

3. Minimal Glue API Draft
- A small Lean-facing interface in engine terms for theorem flow.
- Candidate wrappers listed with naming convention and rationale.

4. Gap Register (Initial)
- Explicit list of unresolved assumptions/wrappers introduced in Milestone A.
- Owner and closure plan for each gap (Milestone E/F).

## Required Artifact Structure
Create and maintain these artifacts during Milestone A:

- `engine/PrisonersDilemma/Research/Notes/MilestoneA/Foundation-Concept-Mapping.md`
- `engine/PrisonersDilemma/Research/Notes/MilestoneA/Foundation-Dependency-Decision.md`
- `engine/PrisonersDilemma/Research/Notes/MilestoneA/Foundation-Gap-Register.md`

If code stubs are introduced, keep them isolated and clearly temporary.

## Concept Mapping Table Spec
Use this table schema in `Foundation-Concept-Mapping.md`:

| Project Concept | Foundation Candidate | Type (Module/Theorem/Def) | Match Level (Exact/Near/Unknown) | Local Glue Needed | Notes |
|---|---|---|---|---|---|
| Example: PBLT-style implication | TODO | Theorem | Unknown | Yes/No | Add theorem identifier once confirmed |

Minimum row coverage:
- Modal syntax and formula layer
- Semantics layer (frames/models/truth relation)
- Provability logic core
- GL and Grz theorem hooks
- Boxdot translation support
- Arithmetical completeness entry points
- Any theorem matching Lemma 3.6 role

## Dependency Decision Criteria
Use these criteria to choose direct vs vendored:
- Build stability in local and CI environments
- Upstream update frequency and break risk
- Ease of theorem-name traceability
- Reproducibility for thesis and archival results
- Complexity of pinning exact revisions

Decision must include:
- selected mode
- exact source/version or commit pin
- rollback plan if integration fails

## Minimal Glue API Requirements
The integration layer must:
- keep CUPOD-specific logic separate from Foundation internals
- expose only theorem-shape level interfaces needed by Milestones B and D
- avoid introducing duplicate logic that Foundation already provides
- annotate every temporary wrapper with:
  - why it exists
  - expected upstream theorem/definition target
  - closure milestone (E or F)

## Acceptance Criteria (Definition of Done)
Milestone A is complete when all are true:
- Mapping table exists and covers all minimum row categories.
- Every mapped item is labeled as exact, near, or gap.
- Dependency mode is chosen and documented with explicit rationale.
- Initial glue API surface is documented (and optionally stubbed) with bounded scope.
- Gap register exists with owners and closure paths.
- No local reimplementation of core modal/provability machinery was introduced without explicit justification.

## Execution Checklist
- [x] Survey Foundation repository structure and module index.
- [x] Populate first full draft of concept mapping table.
- [x] Identify candidate theorem(s) for Lemma 3.6 role.
- [x] Record direct vs vendored decision with commit pin strategy.
- [x] Draft minimal glue API boundary notes.
- [x] Open initial gap register entries.
- [x] Mark Milestone A roadmap item as mapped once acceptance criteria pass.

## Risks and Mitigations
- Risk: theorem names differ from expected Critch-style phrasing.
  - Mitigation: map by semantic role, then record exact identifiers once confirmed.
- Risk: integration friction from dependency management.
  - Mitigation: keep a small adapter boundary and pin versions early.
- Risk: accidental duplicate local formalization.
  - Mitigation: require a "Foundation already checked" note for each new local lemma.

## Handoff to Milestone B
Milestone B can start once Milestone A outputs provide:
- a confirmed theorem candidate set for the Lemma 3.6 role,
- a stable dependency choice,
- and a bounded glue interface with explicit unresolved gaps.
