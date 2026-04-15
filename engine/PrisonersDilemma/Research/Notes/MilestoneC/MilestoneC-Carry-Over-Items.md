# Milestone C Carry-Over Items for Milestone D/E/F

**Status:** Open for Milestones D-F

This document captures unresolved items from Milestone C (CUPOD Model Integration) that require deeper formal proof work in Milestones D, E, and F.

---

## 1. Self-Referential Strategy Formalization (D → Lemma 3.6 Instantiation)

**Current State:**
- CupodBot model created with self-referential intent: strategy probes CUPOD itself to decide between D/C.
- Implementation uses `sorry` placeholder in `source` definition because Lean's value semantics cannot directly encode mutual circular references.

**Deferred Work:**
- Provide formal mathematical semantics for CUPOD's self-reference using Foundation's modal logic framework.
- Map CUPOD strategy to GL-based or boxdot-based completeness theorem (Milestone B decision).
- Establish fixed-point equation: $s = \text{probe}(s, D) \to D : C$.

**Entry Point:**
- [engine/PrisonersDilemma/Research/Notes/MilestoneC/MilestoneC-CUPOD-Model-Integration-Spec.md](MilestoneC-CUPOD-Model-Integration-Spec.md)
- Foundation import: `Foundation.ProvabilityLogic.GLPlusBoxBot` (Milestone B selected theorem shape)

**Execution Path:**
1. Remove `sorry` from `CupodBot.source.strategy` via formal proof.
2. Establish equivalence between game-theoretic fixed-point and modal-logic provability.
3. Verify CUPOD satisfies "self-cooperative" property under Critch's mutual simulation framework.

---

## 2. Deterministic Behavior Proof (D → Optional Refinement)

**Current State:**
- CupodBot.action function defined and type-checked.
- No formal proof of determinism or action uniqueness.

**Deferred Work:**
- Prove: $\forall \text{oppSource}, \text{unique}(\text{action}(\text{oppSource}))$.
- Establish termination of the probing loop within fuel budget (100 steps default).

**Milestone D/E Decision:**
- If completeness theorem (Lemma 3.6 from B) requires determinism → include in D.
- If optional refinement → defer to E.

---

## 3. Mutual Simulation / Nash Equilibrium Analysis (E → Advanced)

**Current State:**
- CUPOD integrates with BotUniverse matchup infrastructure.
- No formal analysis of CUPOD's strategic properties in the PD tournament.

**Deferred Work:**
- Prove/disprove: CUPOD achieves mutual cooperation when playing against itself.
- Analyze: equilibrium properties against other bot types (DefectBot, TitForTat, OBot, Cooperate).
- Characterize: robustness of CUPOD's cooperative outcome when opponent deviates slightly.

**Milestone E Focus:**
- Use fixed-point framework from D to formalize mutual simulation.
- Potentially extend Foundation with CUPOD-specific lemmas for tournament analysis.

---

## 4. Proof Surface Expansion (D/E → Proof Infrastructure)

**Current State:**
- Proofs/CupodBot.lean contains 2 lightweight model-level lemmas:
  - `cupodBot_source_tag`: tag consistency
  - `cupodBot_strategy_eq`: strategy extraction

**Deferred Work:**
- Expand proof surface as deeper proofs are developed.
- Add lemmas for:
  - Action consistency with strategy evaluation
  - Fuel termination bounds
  - Fixed-point uniqueness
  - Critch-style compositionality

---

## 5. Integration Tests Expansion (Optional: C → F)

**Current State:**
- CupodBot integrates cleanly with BotUniverse (1685 jobs build, no errors).
- No suite of randomized or adversarial matchup tests.

**Deferred Work (if needed):**
- Create integration test harness for CUPOD vs. known bots.
- Validate strategy evaluation under various opponent sources.

**Status:**
- Out of scope for Milestone C (code-only integration).
- Defer to testing/evaluation phases if match-level verification required.

---

## Summary

| Item | Current | Phase | Blocker | Notes |
|------|---------|-------|---------|-------|
| Self-reference formalization | `sorry` | D | Modal logic framework | Requires Lemma 3.6 instantiation |
| Determinism proof | Pending | D/E | Fuel termination | Optional refinement |
| Nash / Tournament analysis | Pending | E | Fixed-point from D | Advanced game theory |
| Proof surface expansion | 2 lemmas | D/E | Core proofs | Scales with deeper work |
| Integration tests | Full build | F | Optional | Validate if needed |

---

**Next Step (Milestone D):**
1. Load Milestone B theorem-shape selected from [MilestoneB spec](../MilestoneB/MilestoneB-Critch-to-Foundation-Theorem-Shape-Spec.md).
2. Instantiate selected completeness theorem (GL/Grz/boxdot) with CUPOD strategy.
3. Remove `sorry` from CupodBot source definition via proof.
4. Validate via `lake build`.
