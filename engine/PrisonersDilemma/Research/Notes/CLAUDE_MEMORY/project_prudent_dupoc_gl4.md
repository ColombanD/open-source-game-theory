---
name: project_prudent_dupoc_gl4
description: "PrudentBot×DupocBot (C,C) closed via new object-level GL-4 axiom box_provable_impl; the search-vs-search-no-.sim boundary"
metadata: 
  node_type: memory
  type: project
  originSessionId: d1ca0411-27eb-469c-b8f4-f3813cac7a66
---

PrudentBot vs DupocBot is the first **search-vs-search modal fixed point with NO unboxed `.sim` leg**. Both transparency legs are boxed: leg1 `□_k φ_D → φ_P` (PrudentBot `searchThenSearch_t`, prudence atom discharged), leg2 `□_k φ_P → φ_D` (DupocBot `searchBranch`). For MirrorBot/TFT one leg is an unboxed `.sim` (`simStep`) so `searchBranch`+`simStep` chain into `□φ→φ`; here neither is a `.sim`, so composing two boxed implications needs to strip a box.

**Resolution (done 2026-06-15):** added ONE new axiom `atom_box_provable_impl : ∀ k p q a, Provable k (.impl (.plays p q a) (.box k (.plays p q a)))` to `engine/PrisonersDilemma/Axioms.lean` — witness-free object-form **Σ₁-completeness for play-atoms**. RESTRICTED to `.plays` atoms (Σ₁), so true⟹provable is sound reflection (HBL / arithmetic content of GL necessitation), NOT the GL-EXCLUDED general converse-necessitation `φ→□φ` (unsound on Π₁ truths). Supplies the missing unboxed leg: `atom_box_provable_impl ⊳ leg2` (`implTrans`) gives `φ_P → φ_D`, composing with leg1 into `□_k φ_D → φ_D` — the role `simStep` plays for `.sim`. NOT the boxed-K the agent suggested (verified: boxK lands at interp not a Provable object; relaxed-budget K is a theorem but unchainable — box budget must stay fixed at k).

**Soundness IS verified** (this was the key correction): the axiom's soundness is witnessed by a kernel-checked THEOREM `BaseTheorems.atom_box_provable_impl_sound` (same statement under threshold `play fuel p q = some a ∧ atom_cost fuel ≤ k`), proved from `atom_complete`+`atom_monotone`+`box_provable`+`weakenImpl` — `#print axioms` of it = only [propext, Classical.choice, Quot.sound, atom_complete_false_guard, box_provable], NO new axiom. The axiom drops the threshold so it's usable WITNESS-FREE: the Löb premise `□_k φ_D → φ_D` must be built as a Provable object BEFORE the cooperative play exists; in its false case the antecedent `□_k φ_D` is unprovable (proved: `false_case_box_unprovable`), so no play witness, yet a Provable object of the vacuous implication is still needed — building THAT witness-free is the irreducible Π₁/reflection step (verified no-axiom restructure is impossible). Hence axiom, not theorem. `box_provable` now load-bearing.

**Result:** `outcome_PrudentBot_vs_DupocBot : ∃ k₂, ∀ k, k₂<k → ∃ fuel, outcome fuel (PrudentBot k) (DupocBot k) = some (.C,.C)` in `engine/PrisonersDilemma/Theorems/LlmGenerations/PrudentDupoc.lean`. `#print axioms` = [propext, Classical.choice, Quot.sound, PBLT, atom_box_provable_impl, atom_complete_false_guard]. PBLT untouched (user constraint). Full `lake build` green.

Same file also has `dupocShaped_self_loeb_interp` (zero-axiom proof that the cooperative Löb premise is interp-TRUE for any Dupoc-shaped cooperator vs any opponent), kept as the semantic justification that selecting (C,C) is sound (the cooperative equilibrium is consistent; GL-4 lets S *prove* it). The (D,D) equilibrium is also consistent — selecting (C,C) is the intended Critch fixed point.

If the agent declares PrudentBot×DupocBot OPEN, it is reading stale state — the outcome is now proved. Related: [[project_searchthensearch_rule]], [[project_llm_bot_outcomes_status]], [[project_search_bot_threshold_prompt]].
