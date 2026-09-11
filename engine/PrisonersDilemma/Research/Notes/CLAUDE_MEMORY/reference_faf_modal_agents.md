---
name: faf-modal-agents-competitor
description: Formalized Agent Foundations (A. M. Berns) — Lean 4 mechanization of Barász 2014 UNBOUNDED modal agents; must be cited; narrows "first OSGT formalization" claim
metadata:
  type: reference
---

https://github.com/A-M-Berns/Formalized-Agent-Foundations (ModalAgents/), assessed 2026-09-07. Single-author, AI-orchestrated autoformalizations (Logical Induction, Cartesian Frames, FFS, Factored Spaces, Condensation, ModalAgents). Created 2026-03-28, active. Apache-2.0, CITATION.cff: Berns, A. M., "Formalized Agent Foundations".

**ModalAgents = Barász–Christiano–Fallenstein–Herreshoff–LaVictoire–Yudkowsky 2014**, GL-level: modal agents as GL formulas, Cooperate/Defect/Fair/PrudentBot, GL fixed points (de Jongh–Sambin via FormalizedFormalLogic/ProvabilityLogic), Thm 3.2, 4.7/4.8/4.10, arithmetic layer (agents as PA formulas, CliqueBot, Cor 4.9). Zero axioms. Thm 4.6 open. "Program equilibrium framing left for a future paper."

**ZERO overlap with our core**: no bounded provability/budgets/costs, no Critch/PBLT, no evaluator/programs, no floor, no transparency/EGT (grepped). Our claim "no proof assistant has costed derivability conditions" STILL TRUE.

**Paper consequences:** (1) narrow novelty to "first mechanization of Critch's RESOURCE-BOUNDED OSGT" — never repeat the workshop's "first Lean formalization of OSGT"; (2) cite in Related Work + use as Route-A evidence: their defection is irreducibly weak (`GL ⊬ outcome`, needs Con(PA) — the layer-1/layer-2 collapse our metatheory design avoids), CliqueBot numeral blows 8 GB; (3) their stack = natural substrate for BoundedGL's PA-model obligation (future work). Advice given: arXiv preprint fast; consider emailing Berns. Related: [[jmlr-paper-decisions]], [[boundedgl-interface]].
