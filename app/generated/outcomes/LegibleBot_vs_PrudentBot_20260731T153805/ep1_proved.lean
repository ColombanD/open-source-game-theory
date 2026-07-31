import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Bots.LlmGenerations.LegibleBot
import PrisonersDilemma.Bots.LlmGenerations.PrudentBot
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Theorems.LegibleBot.Helpers
import PrisonersDilemma.Theorems.PrudentBot.Helpers

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

theorem llm_outcome_LegibleBot_vs_PrudentBot :
    ∃ k₂, ∀ k, k₂ < k →
      ∃ fuel, outcome fuel (LegibleBot (2*k+64) k) (PrudentBot k) = some (.C, .D) := by
  -- LegibleBot cooperates with PrudentBot family
  obtain ⟨kA, hA⟩ := LegibleBot_cooperates_large (fun k => PrudentBot k) 100
    (fun k => by
      show (PrudentBot k).size ≤ 100 + 20 * Nat.log2 k
      simp only [PrudentBot, DefectBot, Prog.size, Formula.size, numCost]; omega)
  -- LegibleBot cooperates with .bot DefectBot family
  obtain ⟨kB, hB⟩ := LegibleBot_cooperates_large (fun _ => .bot DefectBot) 100
    (fun k => by
      show (Prog.bot DefectBot).size ≤ 100 + 20 * Nat.log2 k
      simp only [DefectBot, Prog.size]; omega)
  refine ⟨max kA kB, fun k hk => ?_⟩
  obtain ⟨n, hn⟩ := hA k (lt_of_le_of_lt (Nat.le_max_left _ _) hk)
  obtain ⟨nB, hnB⟩ := hB k (lt_of_le_of_lt (Nat.le_max_right _ _) hk)
  -- LegibleBot plays C vs PrudentBot
  have hLeg : play n (LegibleBot (2*k+64) k) (PrudentBot k) = some .C := hn
  -- LegibleBot plays C vs .bot DefectBot, so D-atom interp false
  have hInterpFalse : ¬ (Formula.plays (LegibleBot (2*k+64) k) (.bot DefectBot) .D).interp := by
    rintro ⟨m, hm⟩
    have hc : play (max nB m) (LegibleBot (2*k+64) k) (.bot DefectBot) = some .C :=
      eval_mono_le hnB _ (Nat.le_max_left _ _)
    have hd : play (max nB m) (LegibleBot (2*k+64) k) (.bot DefectBot) = some .D :=
      eval_mono_le hm _ (Nat.le_max_right _ _)
    rw [hc] at hd; cases hd
  -- PrudentBot's inner prudence guard fails
  have hInner : proofSearch k
      (.plays (LegibleBot (2*k+64) k) (.bot DefectBot) .D) = false := by
    cases hps : proofSearch k (.plays (LegibleBot (2*k+64) k) (.bot DefectBot) .D) with
    | true => exact absurd (proofSearch_sound _ _ hps) hInterpFalse
    | false => rfl
  -- PrudentBot plays D
  have hPrud : play (n + 3) (PrudentBot k) (LegibleBot (2*k+64) k) = some .D := by
    by_cases hc : proofSearch k
        (.plays (LegibleBot (2*k+64) k) (PrudentBot k) .C) = true
    · exact prudent_eval_inner_false k n (LegibleBot (2*k+64) k) hc hInner
    · have hf : proofSearch k
          (.plays (LegibleBot (2*k+64) k) (PrudentBot k) .C) = false := by
        cases hcc : proofSearch k (.plays (LegibleBot (2*k+64) k) (PrudentBot k) .C) with
        | true => exact absurd hcc hc
        | false => rfl
      have h2 := prudent_eval_outer_false k (n+1) (LegibleBot (2*k+64) k) hf
      rw [show n + 1 + 2 = n + 3 by omega] at h2
      exact h2
  have hLeg2 : play (n + 3) (LegibleBot (2*k+64) k) (PrudentBot k) = some .C :=
    eval_mono_le hLeg _ (by omega)
  exact ⟨n + 3, outcome_of_plays _ _ _ _ _ hLeg2 hPrud⟩

end PD.Theorems

