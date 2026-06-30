import PrisonersDilemma.Bots.LlmGenerations.JustBot
import PrisonersDilemma.Bots.CupodTrollBot
import PrisonersDilemma.Bots.CupodBot
import PrisonersDilemma.Bots.DupocBot

import PrisonersDilemma.Dynamics
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Theorems.Helpers
import PrisonersDilemma.Theorems.CupodTrollBot

open PD
open PD.Bots
open PD.BaseTheorems
namespace PD.Theorems

/-- JustBot cooperates against CupodTrollBot for large budget: its guard asks
    "does CupodTrollBot play C against (bot DupocBot)?" which is true, so once the
    budget covers the atom the guard fires. -/
theorem JustBot_plays_C_against_CupodTrollBot (k fuel : Nat)
    (hbudget : atom_cost (fuel + 2) ≤ k) :
    play (fuel + 2) (JustBot k) (CupodTrollBot k) = some .C := by
  -- CupodTrollBot cooperates against `.bot (DupocBot k)`.
  have hC : play (fuel + 2) (CupodTrollBot k) (.bot (DupocBot k)) = some .C :=
    CupodTrollBot_cooperates_against_bot k fuel (DupocBot k)
  have hatom : proofSearch (atom_cost (fuel + 2))
      (.plays (CupodTrollBot k) (.bot (DupocBot k)) .C) = true :=
    (proofSearch_spec _ _).2
      (Provable.atom (atom_complete (CupodTrollBot k) (.bot (DupocBot k)) .C (fuel + 2) hC))
  have hg : proofSearch k (.plays (CupodTrollBot k) (.bot (DupocBot k)) .C) = true :=
    proofSearch_monotone _ _ _ hbudget hatom
  show eval (fuel + 2) (JustBot k) (CupodTrollBot k) (JustBot k) = some .C
  unfold JustBot at hg ⊢
  simp [eval, Prog.subst, Formula.subst, hg]

theorem llm_outcome_JustBot_vs_CupodTrollBot :
    ∃ k₂, ∀ k, k₂ < k →
      ∃ fuel, outcome fuel (JustBot k) (CupodTrollBot k) = some (.C, .C) := by
  refine ⟨atom_cost 2, fun k hk => ⟨2, ?_⟩⟩
  have hbudget : atom_cost (0 + 2) ≤ k := by simpa using Nat.le_of_lt hk
  -- Direction A: JustBot cooperates.
  have hA : play 2 (JustBot k) (CupodTrollBot k) = some .C := by
    simpa using JustBot_plays_C_against_CupodTrollBot k 0 hbudget
  -- Direction B: CupodTrollBot cooperates (JustBot ≠ CupodBot).
  have hB : play 2 (CupodTrollBot k) (JustBot k) = some .C := by
    have := CupodTrollBot_cooperates_if_opp_not_CupodBot k 0 (JustBot k)
      (by simp [JustBot, CupodBot])
    simpa using this
  exact outcome_of_plays _ _ _ _ _ hA hB

end PD.Theorems
