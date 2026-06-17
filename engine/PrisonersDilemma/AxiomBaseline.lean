import PrisonersDilemma

/-!
# Axiom regression baseline (scratch)

Prints the axiom dependencies of representative outcome theorems so the
decidable-`eval` refactor can confirm the axiom set does not grow. Delete before
landing.
-/

open PD.Theorems

-- Const / atom-guard matchups (should be axiom-light)
#print axioms outcome_CooperateBot_vs_DefectBot
#print axioms outcome_DefectBot_vs_DefectBot

-- .search / .sim matchups
#print axioms outcome_PrudentBot_vs_MirrorBot
#print axioms outcome_PrudentBot_vs_PrudentBot

-- The two modal-fixed-point matchups (expected to keep atom_box_provable_impl + PBLT)
#print axioms outcome_PrudentBot_vs_DupocBot
#print axioms llm_outcome_JustBot_vs_DupocBot
