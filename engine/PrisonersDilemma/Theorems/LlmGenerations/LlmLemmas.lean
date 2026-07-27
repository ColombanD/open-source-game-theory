import PrisonersDilemma.BaseTheorems

/-!
# LlmLemmas — the proof agent's DERIVED-rule library

Theorems over the existing proof system `Pf`, added autonomously by the proof agent via
the `add_base_lemma` tool (Tier 1 of the OUTCOME-OPEN escalation ladder). Everything here
is kernel-checked against the unchanged engine — nothing is postulated, so this file
carries no trust obligations beyond the engine itself. Additive-only; each block below is
one tool call.
-/

open PD PD.BaseTheorems

namespace PD.LlmLemmas

/-- Seed example (the expected format): reflect a fired oracle back into provability. -/
theorem pf_of_proofSearch {k : Nat} {φ : Formula} (h : proofSearch k φ = true) : Pf k φ :=
  (proofSearch_spec k φ).1 h


/-! ### loeb_premise_boxMono (agent-added) -/

/-- Weaken a Löb premise's box subscript DOWN in the antecedent: from `□_b φ → φ`
    and `a ≤ b`, get `□_a φ → φ` (upward `boxMono` into the premise's antecedent). -/
theorem loeb_premise_boxMono {a b m K : Nat} {φ : Formula}
    (h : Pf m (.impl (.box b φ) φ)) (hab : a ≤ b)
    (hsz : (Formula.impl (.box a φ) (.box b φ)).size + m
           + (Formula.impl (.box a φ) φ).size ≤ K) :
    Pf K (.impl (.box a φ) φ) :=
  Pf.implTrans _ _ _ _ m
    (Pf.boxMono a b _ φ hab (Nat.le_refl _)) h hsz

end PD.LlmLemmas
