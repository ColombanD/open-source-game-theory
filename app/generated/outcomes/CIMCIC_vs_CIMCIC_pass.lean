import PrisonersDilemma.Bots.LlmGenerations.CIMCIC
import PrisonersDilemma.BaseTheorems

open PD PD.BaseTheorems PD.Bots

namespace PD.Theorems

theorem llm_outcome_CIMCIC_vs_CIMCIC :
    ∃ k₂, ∀ k, k₂ < k →
      ∃ fuel, outcome fuel (CIMCIC k) (CIMCIC k) = some (.C, .C) := by
  obtain ⟨K, hK⟩ := PD.linear_log2_add_le 4 47
  refine ⟨K, fun k hk => ?_⟩
  have hkK : K ≤ k := Nat.le_of_lt hk
  have hsz : (Formula.impl (.plays (CIMCIC k) (CIMCIC k) Action.C)
                            (.plays (CIMCIC k) (CIMCIC k) Action.C)).size ≤ k := by
    simp only [Formula.size, Prog.size, CIMCIC, numCost]
    have := hK k hkK
    omega
  have hguard : Pf k (.impl (.plays (CIMCIC k) (CIMCIC k) Action.C)
                             (.plays (CIMCIC k) (CIMCIC k) Action.C)) :=
    Pf.implRefl _ hsz
  have hps : proofSearch k
    ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.C)).subst (CIMCIC k) (CIMCIC k)) = true := by
    apply (proofSearch_spec _ _).2
    show Pf k _
    simp only [Formula.subst, Prog.subst]
    exact hguard
  refine ⟨2, ?_⟩
  unfold CIMCIC at hps
  have heval : eval 2 (CIMCIC k) (CIMCIC k) (CIMCIC k) = some Action.C := by
    unfold CIMCIC
    show (if proofSearch k _ = true then _ else _) = some Action.C
    rw [hps]
    rfl
  show outcome 2 (CIMCIC k) (CIMCIC k) = some (Action.C, Action.C)
  unfold outcome play
  rw [heval]
  rfl

end PD.Theorems
