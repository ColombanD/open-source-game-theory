---
name: project-weakenimpl-rule
description: weakenImpl Provable rule added to prove implication-guard bots (CIMCIC/DIMCID); incompleteness boundary for the dual cases
metadata: 
  node_type: memory
  type: project
  originSessionId: 0e89e4c0-be94-4940-9395-a8d71d212f23
---

To prove outcomes for implication-guard bots (CIMCIC, DIMCID) a new constructor
`Provable.weakenImpl` was added to the `Provable` inductive in
`engine/PrisonersDilemma/Derivation.lean`:

`| weakenImpl (φ ψ : Formula) (m : Nat) : Provable m ψ → (Formula.impl φ ψ).size ≤ k → Provable k (.impl φ ψ)`

**Why:** The original `Derivation` system (modusPonens/hypSyll/searchBranch/simStep/eqRefl) had
no implication-introduction, so an `.impl A B` guard was unprovable even when B was
true. It had to go on `Provable` (Prop), NOT `Derivation` (Type) — they can't share
a mutual block (universe mismatch), and the premise needs B's *provability* (atom or
struct), which Derivation can't carry. Sound (`interp (.impl φ ψ) = φ.interp → ψ.interp`,
discharged by `fun _ => ·`), faithful (PA proves `ψ ⊢ φ → ψ`), and adds NO new axiom.

**How to apply:** Adding a `Provable` constructor forces updating every recursor/cases
site: `playsProof_sound` and `Provable_sound` in `BaseTheorems.lean` (use `Provable.rec`
with POSITIONAL minor premises — the rec alternatives are anonymous binders, named args
like `(weakenImpl := …)` and `case weakenImpl` both FAIL), and the `cases` in
`proofSearch_monotone`.

**Incompleteness boundary:** Only the true-consequent direction is provable.
CIMCIC vs CooperateBot = (C,C) ✓, DIMCID vs DefectBot = (D,D) ✓. The duals
(CIMCIC vs DefectBot, DIMCID vs CooperateBot) need `proofSearch = false` on a
*vacuously-true* implication — a Π₁ unprovability claim the sound rules cannot
certify (the `= false` route needs `¬ interp`, but interp is true). Left unproved
on purpose (documented, no `sorry`). See [[project-llm-bot-outcomes-status]].
