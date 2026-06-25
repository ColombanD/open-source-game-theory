import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Derivation
import PrisonersDilemma.Axioms
import PrisonersDilemma.BaseTheorems
import Mathlib.Data.Nat.Log

/-!
# Spike — honest object-antecedent GL axiom K + necessitation: does it close mutual-Löb?

The shipped `boxK` uses a META antecedent (a Lean proof-transformer) and fixes the output
box at budget `k` "for free". The user wants the FAITHFUL version: real GL axiom K with an
OBJECT antecedent `□_a(φ→ψ)`, plus necessitation (`box_provable`), accepting budget
inflation. This spike tests whether that chain actually derives `□_k φP → φP`.

Target chain (legPD : □_k φP → φD ; legDP : □_k φD → φP, both real `Provable`):
  1. box_provable legPD          : Provable b1 (□_k(□_kφP → φD))          [necessitation]
  2. realK (a=k)                 : □_k(□_kφP→φD) → (□_k(□_kφP) → □_k φD)   [object K]
       ⚠ but step 1 lands at budget b1, and realK's antecedent must be a `Provable _` of
         `□_k(□_kφP→φD)`. Provable at b1, fine if we don't fix the *outer* proof budget.
  3. box4 / box_provable         : □_kφP → □_k(□_kφP)                       [axiom 4]
  4. chain 3;2(applied) ;legDP.

Two budget frictions to watch (the suspected wall):
  (A) box4's inner box vs realK's antecedent box — do the BOX INDICES match (both k)?
  (B) realK's OUTPUT box □_k φD — does it meet legDP's □_k φD? (box index k both — should!)

Not imported by root. Build alone:
  lake env lean PrisonersDilemma/Research/Spikes/HonestKSpike.lean
-/

open PD
open PD.Axioms
open PD.BaseTheorems

namespace PD.HonestKSpike

/-! ## Honest object-antecedent K (atom consequent), output box at EXISTENTIAL budget.

`interp (□_a(φ→α) → (□_aφ → □_b α))` = `Provable a (φ→α) → Provable a φ → Provable b α`.
Premises ⟹ α.interp ⟹ (atom_complete) Provable (atom_cost n) α. So `b` is existential
(the cert budget), NOT `a`. This is the honest cost: boxing the (re-derived) atom costs
its certificate size, generally ≠ a. -/
axiom realK :
  ∀ (a : Nat) (φ : Formula) (p q : Prog) (c : Action),
    ∃ b K, Provable K (.impl (.box a (.impl φ (.plays p q c)))
                            (.impl (.box a φ) (.box b (.plays p q c))))

/-- realK soundness (the honest, existential-output form). -/
theorem realK_sound (a : Nat) (φ : Formula) (p q : Prog) (c : Action)
    (himp : Provable a (.impl φ (.plays p q c))) (hφ : Provable a φ) :
    ∃ b, Provable b (.plays p q c) := by
  have hi : (Formula.impl φ (.plays p q c)).interp := Provable_sound a _ himp
  have hf : φ.interp := Provable_sound a φ hφ
  obtain ⟨n, hn⟩ := hi hf
  exact ⟨atom_cost n, Provable.atom (atom_complete p q c n hn)⟩

/-! ## THE GATE: does the chain to `□_k φD → φP` (and then `□_k φP → φP`) close?

The output box of realK is `□_b φD` with b = cert budget. legDP needs `□_k φD`. So we are
forced to RECONCILE `□_b φD` back to `□_k φD`. That reconciliation is:
  Provable _ (□_b φD)  ⟹  Provable _ (□_k φD)?
which needs b = k OR a box-budget weakening rule. b is the cert budget (atom_cost n),
k is the bot's budget — DIFFERENT. There is NO sound rule to change a box's INDEX
(`□_b φ → □_k φ` would assert "provable at b ⟹ provable at k", false when k < b). -/

theorem honest_chain_gate (k : Nat) (pP qP pD qD : Prog) (bP bD : Action)
    (legPD : Provable k (.impl (.box k (.plays pP qP bP)) (.plays pD qD bD)))
    (legDP : Provable k (.impl (.box k (.plays pD qD bD)) (.plays pP qP bP))) :
    Provable k (.impl (.box k (.plays pP qP bP)) (.plays pP qP bP)) := by
  -- 1. necessitate legPD
  obtain ⟨b1, _, hNec⟩ := box_provable k (.impl (.box k (.plays pP qP bP)) (.plays pD qD bD)) legPD
  -- 2. realK with a = k: needs antecedent `□_k(□_kφP→φD)` at budget k. But hNec is at b1.
  --    Even if b1 happened to work, realK OUTPUTS `□_{b} φD` with b EXISTENTIAL (cert size).
  obtain ⟨bOut, KK, hK⟩ := realK k (.box k (.plays pP qP bP)) pD qD bD
  -- 3. legDP needs `□_k φD`; realK gives `□_{bOut} φD`. bOut ≠ k in general.
  --    To bridge □_{bOut}φD → □_k φD we'd need a box-INDEX weakening — UNSOUND in general.
  --    Mark the irreducible gap:
  sorry

end PD.HonestKSpike
