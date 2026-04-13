# Modal Logic + CUPOD Formalization Roadmap

Date: 2026-04-13
Project: open-source-game-theory (Lean engine)

## Goal
Formally verify a Theorem 3.4 style result for CUPOD self-play (for sufficiently large k, CUPOD(k) vs CUPOD(k) yields D,D), using a staged path through Parametric Bounded Lob Theorem (PBLT / Lemma 3.6).

## Strategy Decision (Locked)
We will use a hybrid top-down approach:
1. Build end-to-end CUPOD theorem flow early using explicit assumptions/interfaces.
2. Keep assumptions minimal and visible.
3. Replace assumptions progressively with deeper modal/provability formalization.

This gives fast traction without sacrificing long-term rigor.

## Scope and Non-Goals
In scope:
- Lean architecture for bounded provability and modal-style reasoning hooks.
- CUPOD bot model integration into existing engine structure.
- Theorem pipeline from PBLT assumptions to CUPOD self-play claim.

Out of scope (for first pass):
- Full low-level encoding of proof strings and exact character-level verifier internals.
- Complete foundational reconstruction of all metatheory before any CUPOD results.

## Milestones

### Milestone A: Logic Interface Layer
Status: [ ] Not started

Objective:
- Introduce an abstract interface for bounded provability concepts needed by PBLT.

Deliverables:
- Lean module namespace for logic/provability abstractions.
- Definitions for parameterized claims p(k), bounded box-like predicate, and growth assumptions.
- Minimal axioms/assumptions clearly documented.

Exit criteria:
- The interface compiles and can be imported by theorem files.

##

### Milestone B: Parametric Bounded Lob Theorem Skeleton
Status: [ ] Not started

Objective:
- State (and possibly partially prove) a Lean theorem matching Lemma 3.6 structure.

Deliverables:
- Lean theorem statement for PBLT with explicit hypotheses.
- Proof skeleton that isolates what remains assumed vs proved.

Exit criteria:
- The theorem is usable as a dependency for CUPOD proofs.

##

### Milestone C: CUPOD Bot Model Integration
Status: [ ] Not started

Objective:
- Add CUPOD model in the bot layer and align with ProgramModel pipeline.

Deliverables:
- Models/Bots/CupodBot module with strategy and source/action definitions.
- BotUniverse integration path (or parallel universe if cleaner during transition).

Exit criteria:
- CUPOD can participate in playActions / ActionClaim statements.

##

### Milestone D: Theorem 3.4-Style Result from PBLT
Status: [ ] Not started

Objective:
- Instantiate PBLT with CUPOD-specific p(k) and f(k)=k assumptions.

Deliverables:
- Proof file deriving eventual-defection self-play claim for CUPOD.
- Lean statement aligned with "for sufficiently large k" style.

Exit criteria:
- Compiling theorem that formalizes the target high-level claim under current assumptions.

##

### Milestone E: Assumption Discharge and Strengthening
Status: [ ] Not started

Objective:
- Replace abstract assumptions with concrete formalization where feasible.

Deliverables:
- Reduced axiom surface.
- Documentation of remaining trusted assumptions and why.

Exit criteria:
- A tighter, more foundational development than Milestone D with explicit trust boundary.

## Working Conventions
- Action-first theorem workflow remains default.
- Keep modal/provability files isolated from existing bot proofs to reduce churn.
- Every assumption must be named and justified in comments/docs.
- Prefer small, composable lemmas over monolithic proofs.

## Suggested File Layout (Planned)
- PrisonersDilemma/Logic/
  - Provability.lean
  - BoundedLob.lean
  - FixedPoint.lean (optional, if needed)
- PrisonersDilemma/Models/Bots/
  - CupodBot.lean
- PrisonersDilemma/Proofs/
  - Cupod.lean

## Tracking Table
- [ ] A. Logic interface compiles
- [ ] B. PBLT statement available to downstream proofs
- [ ] C. CUPOD model integrated with pipeline
- [ ] D. Theorem 3.4 style result formalized (assumption-aware)
- [ ] E. Assumptions reduced / trust boundary documented

## Immediate Next Step
Start Milestone A by drafting theorem/definition signatures first (no heavy proofs), then iterate on the smallest assumption set needed by Milestone B.
