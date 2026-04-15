# Milestone C Spec: CUPOD Model Integration

Date: 2026-04-15
Project: open-source-game-theory (Lean engine)
Roadmap Reference: Modal Logic + CUPOD Formalization Roadmap
Prerequisite: Milestones A and B complete
Status: Planned (code-first milestone)

## Milestone Objective
Add CUPOD to the bot/model layer and connect it to the Foundation-backed theorem-shape contract from Milestone B, while keeping the integration minimal and composable for Milestone D proofs.

## In Scope
- Add a CUPOD bot model under the existing bot namespace.
- Define any CUPOD configuration/parameter type needed for self-play statements (including future `k`-indexed variants).
- Expose a narrow proof-facing interface that references the Milestone B theorem-shape contract.
- Ensure CUPOD participates cleanly in existing pipeline/model universe structures.
- Add targeted tests/build checks for new model-level behavior.

## Out of Scope
- Full Theorem 3.4 self-play proof (Milestone D).
- Closing all Foundation mismatch gaps (Milestones E/F).
- Broad refactors unrelated to CUPOD integration.

## Inputs from Prior Milestones
- [Milestone B theorem-shape spec](../MilestoneB/MilestoneB-Critch-to-Foundation-Theorem-Shape-Spec.md)
- [Milestone A concept mapping](../MilestoneA/Foundation-Concept-Mapping.md)
- [Milestone A gap register](../MilestoneA/Foundation-Gap-Register.md)

## Proposed Code Touchpoints
- `engine/PrisonersDilemma/Models/Bots/CupodBot.lean` (new)
- `engine/PrisonersDilemma/Models/BotUniverse.lean` (update)
- `engine/PrisonersDilemma/Pipeline.lean` (update if CUPOD-specific route is needed)
- `engine/PrisonersDilemma/Proofs/CupodBot.lean` (new lightweight model-level lemmas)
- `engine/PrisonersDilemma.lean` (update imports)

## Integration Contract (from Milestone B)
Milestone C must consume the B-level theorem-shape contract without re-proving Foundation theory.

Required boundary:
- Keep a local proof-facing name for the selected theorem shape.
- Attach CUPOD-specific parameters locally (for example `k`) in project namespace.
- Isolate translation/bridge facts so Milestone D can call one clean interface.

## Deliverables
1. CUPOD Bot Model
- CUPOD bot definition in existing strategy/bot style.
- Deterministic semantics in terms of current `SourceAST` and action pipeline.

2. Universe/Pipeline Integration
- CUPOD bot included in bot registry/universe path used by tooling and proofs.
- Any parser/template hooks updated if required by current architecture.

3. Lightweight Proof Surface
- Small lemmas that characterize CUPOD model behavior needed by Milestone D setup.
- No deep theorem proving beyond model sanity and interface wiring.

4. Validation
- `lake build` passes after integration.
- Existing bot proofs remain stable.

## Acceptance Criteria
Milestone C is complete when all are true:
- CUPOD bot exists in model layer and compiles.
- CUPOD is discoverable/usable through bot universe/pipeline entry points.
- Proof surface includes only minimal lemmas needed for Milestone D handoff.
- No duplicate modal/provability infrastructure is introduced locally.
- Any unresolved theorem-shape mismatch is logged for E/F, not silently ignored.

## Execution Checklist (Code-First)
- [ ] Create `CupodBot` model file with initial behavior and parameter hooks.
- [ ] Wire CUPOD into `BotUniverse` and any pipeline registry points.
- [ ] Add `Proofs/CupodBot.lean` with minimal model-level lemmas.
- [ ] Add root imports and keep module graph clean.
- [ ] Run `lake build` and resolve integration regressions.
- [ ] Add or update tests if current test harness covers this layer.
- [ ] Record carry-over items for Milestone D/E/F.
- [ ] Update roadmap status/tracking for Milestone C when done.

## Risks and Mitigations
- Risk: CUPOD parameterization (`k`) conflicts with existing bot abstraction.
  - Mitigation: isolate parameters in a local config structure and provide a default constructor.
- Risk: pipeline registration creates coupling to proof modules.
  - Mitigation: keep model wiring in model/pipeline files; keep proofs in separate namespace.
- Risk: overbuilding theorem infrastructure during integration.
  - Mitigation: enforce minimal proof surface and defer theorem-heavy steps to D/E.

## Handoff to Milestone D
Milestone D can start once Milestone C provides:
- a compile-stable CUPOD model integrated in the engine,
- a narrow CUPOD proof surface aligned with the Milestone B theorem-shape contract,
- and explicit remaining gaps tracked for theorem completion work.
