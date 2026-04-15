# Modal Logic + CUPOD Formalization Roadmap

Date: 2026-04-13
Project: open-source-game-theory (Lean engine)

## Goal
Formally verify a Theorem 3.4 style result for CUPOD self-play (for sufficiently large k, CUPOD(k) vs CUPOD(k) yields D,D), while reusing the FormalizedFormalLogic/Foundation library as much as possible for modal logic, provability logic, completeness, and boxdot-style translation.

## Strategy Decision (Locked)
We will use a hybrid top-down approach with Foundation as the backend:
1. Reuse Foundation's modal/provability logic infrastructure instead of rebuilding modal logic from scratch.
2. Keep the CUPOD theorem flow explicit and small at the engine level.
3. Add only the smallest local glue needed to connect Critch-style statements to Foundation's existing theorems.
4. Replace any temporary assumptions with proofs only if Foundation does not already provide the needed theorem.

This gives fast traction while preserving rigor and minimizing duplicate formalization.

## Scope and Non-Goals
In scope:
- Integration planning around Foundation's modal logic, provability logic, GL, Grz, boxdot, and arithmetical completeness infrastructure.
- CUPOD bot model integration into the existing engine structure.
- Theorem pipeline from a Foundation-backed PBLT/Lob-style statement to CUPOD self-play.
- Minimal compatibility glue between our engine concepts and Foundation's theorem names / abstractions.

Out of scope (for first pass):
- Reimplementing modal logic or provability logic from first principles unless Foundation proves insufficient.
- Full low-level encoding of proof strings and exact character-level verifier internals.
- Complete reconstruction of all metatheory before any CUPOD results.

## Milestones

### Milestone A: Foundation Integration Layer
Status: [x] complete
Objective: Map the project's needs onto Foundation's existing modal/provability machinery.

### Milestone B: Critch-to-Foundation Theorem Shape
Status: [ ] Not started
Objective: Identify the theorem shape that plays the role of Lemma 3.6 in the Foundation-backed development.

### Milestone C: CUPOD Model Integration
Status: [ ] Not started
Objective: Add CUPOD to the bot layer in a way that plays nicely with the existing engine and the Foundation-backed theorem plan.

### Milestone D: Cupod Self-Play Theorem
Status: [ ] Not started
Objective: Derive the Theorem 3.4-style conclusion for Cupod self-play using the Foundation-backed theorem shape.

### Milestone E: Foundation Gap Closure
Status: [ ] Not started
Objective: Replace any temporary assumptions or wrappers with existing Foundation theorems, or isolate the minimal missing lemmas as local extensions.

### Milestone F: Optional Local Extensions
Status: [ ] Not started
Objective: Add only the smallest local extensions needed if Foundation is almost enough but not quite.

## Working Conventions
- Foundation is the default source of truth for modal/provability logic.
- Action-first theorem workflow remains default.
- Keep Cupod-specific code isolated from proof infrastructure.
- Every assumption or wrapper must be named and justified in comments/docs.
- Prefer small, composable lemmas over monolithic proofs.
- If Foundation already proves a fact, use it rather than re-proving it locally.

## Tracking Table
- [x] A. Foundation integration layer mapped
- [ ] B. PBLT/theorem-shape identified inside Foundation ecosystem
- [ ] C. CUPOD model integrated with pipeline
- [ ] D. Theorem 3.4 style result formalized
- [ ] E. Remaining gaps documented or closed
- [ ] F. Any local extensions minimized

## Immediate Next Step
Start Milestone B by tightening the theorem shape that plays the role of Lemma 3.6 inside the Foundation-backed development, using the completed Milestone A mapping, dependency decision, and build-verified Foundation integration.
