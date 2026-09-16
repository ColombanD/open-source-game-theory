import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Bots.DupocBot
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Bots.LlmGenerations.JustBot
import PrisonersDilemma.Theorems.CooperateBot.Helpers
import PrisonersDilemma.Theorems.DupocBot.Helpers
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Base.Asymptotics
import PrisonersDilemma.Theorems.JustBot.Helpers
import PrisonersDilemma.Outcome

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

-- CooperateBot --

/-- JustBot's substituted guard against CooperateBot is true: CooperateBot
    cooperates against DupocBot (it cooperates against everything). -/
theorem proofSearch_true_for_JustBot_vs_CooperateBot :
    ∃ k, proofSearch k (Formula.plays CooperateBot (.bot (DupocBot k)) Action.C) = true := by
  obtain ⟨K, hK⟩ := linear_log2_add_le 1 11
  have hKK := hK K (le_refl K)
  exact ⟨K, (proofSearch_spec _ _).2 (Pf.atom ⟨PlaysProof.const, by
    simp only [Formula.size, DupocBot_size, CooperateBot, Prog.size, c_leaf]; omega⟩)⟩

/-- Threshold form: the certificate is a `Pf.atom` whose only side condition is the
    leaf cost plus the atom's own size (`log2 k + 11`, the frozen `.bot (DupocBot k)`
    carrying Dupoc's numeral; no `c_guard k` term), so it holds at every budget above
    that threshold rather than at a single witness. -/
theorem proofSearch_true_for_JustBot_vs_CooperateBot_ge (k : Nat) (hk : Nat.log2 k + 11 ≤ k) :
    proofSearch k (Formula.plays CooperateBot (.bot (DupocBot k)) Action.C) = true :=
  (proofSearch_spec _ _).2 (Pf.atom ⟨PlaysProof.const, by
    simp only [Formula.size, DupocBot_size, CooperateBot, Prog.size, c_leaf]; omega⟩)

/-- JustBot cooperates against CooperateBot: its guard succeeds. -/
theorem JustBot_plays_C_against_CooperateBot (k fuel : Nat)
    (hk : proofSearch k (Formula.plays CooperateBot (.bot (DupocBot k)) Action.C) = true) :
    play (fuel + 2) (JustBot k) CooperateBot = some .C := by
  refine JustBot_eval_step k fuel CooperateBot .C ?_
  simpa using! hk

/-- JustBot vs CooperateBot: mutual cooperation. -/
@[outcome]
theorem outcome_JustBot_vs_CooperateBot :
    OutcomeSpec .eventual 2
      JustBot (fun _ => CooperateBot) (some (.C, .C)) := by
  obtain ⟨K, hK⟩ := linear_log2_add_le 1 11
  refine ⟨K, fun k hlt fuel => ?_⟩
  have hk := proofSearch_true_for_JustBot_vs_CooperateBot_ge k
    (by have := hK k (Nat.le_of_lt hlt); omega)
  have hA : play (fuel + 2) (JustBot k) CooperateBot = some .C :=
    JustBot_plays_C_against_CooperateBot k fuel hk
  have hB : play (fuel + 2) CooperateBot (JustBot k) = some .C := by
    simpa [Nat.add_comm] using! play_CooperateBot (fuel + 1) (JustBot k)
  exact outcome_of_plays _ _ _ _ _ hA hB
end PD.Theorems
