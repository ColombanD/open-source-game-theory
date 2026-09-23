import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Bots.LlmGenerations.CIMCIC
import PrisonersDilemma.Bots.MirrorBot
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Base.Asymptotics

open PD
open PD.Bots
open PD.BaseTheorems
namespace PD.Theorems

theorem cimcic_mirror_guard_provable :
    ∃ K, ∀ k, k ≥ K →
      proofSearch k
        ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.C)).subst
          (CIMCIC k) MirrorBot) = true := by
  obtain ⟨K, hK⟩ := linear_log2_add_le 20 200
  refine ⟨K, fun k hk => ?_⟩
  refine (proofSearch_spec _ _).2 ?_
  show Pf k
    (Formula.impl (.plays (CIMCIC k) MirrorBot Action.C)
                  (.plays MirrorBot (CIMCIC k) Action.C))
  have h := Pf.simStep MirrorBot .opp .self (CIMCIC k) Action.C rfl (k := k)
  simp only [Prog.subst, MirrorBot] at h
  refine h ?_
  have hb := hK k hk
  simp only [numCost, Formula.size, Prog.size, CIMCIC]
  omega

/-- CIMCIC cooperates against MirrorBot: its guard fires, so it takes the
    `.const .C` branch. -/
theorem CIMCIC_plays_C_against_MirrorBot (k fuel : Nat)
    (hk : proofSearch k
        ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.C)).subst
          (CIMCIC k) MirrorBot) = true) :
    play (fuel + 2) (CIMCIC k) MirrorBot = some .C := by
  show (if proofSearch k
            ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.C)).subst
              (CIMCIC k) MirrorBot)
          then eval (fuel + 1) (CIMCIC k) MirrorBot (.const Action.C)
          else eval (fuel + 1) (CIMCIC k) MirrorBot (.const Action.D)) = some .C
  rw [hk]; simp [eval]

/-- MirrorBot mirrors CIMCIC's cooperate via the `.sim .opp .self` swap. -/
theorem MirrorBot_plays_C_against_CIMCIC (k fuel : Nat)
    (hk : proofSearch k
        ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.C)).subst
          (CIMCIC k) MirrorBot) = true) :
    play (fuel + 3) MirrorBot (CIMCIC k) = some .C := by
  have hCimcic : play (fuel + 2) (CIMCIC k) MirrorBot = some .C :=
    CIMCIC_plays_C_against_MirrorBot k fuel hk
  simpa [play, eval, Prog.subst, MirrorBot] using hCimcic

theorem llm_outcome_CIMCIC_vs_MirrorBot :
    ∃ k₂, ∀ k, k₂ < k →
      ∃ fuel, outcome fuel (CIMCIC k) MirrorBot = some (.C, .C) := by
  obtain ⟨K, hK⟩ := cimcic_mirror_guard_provable
  refine ⟨K, fun k hk => ⟨3, ?_⟩⟩
  have hg := hK k (Nat.le_of_lt hk)
  have hA : play 3 (CIMCIC k) MirrorBot = some .C := by
    simpa using CIMCIC_plays_C_against_MirrorBot k 1 hg
  have hB : play 3 MirrorBot (CIMCIC k) = some .C := by
    simpa using MirrorBot_plays_C_against_CIMCIC k 0 hg
  exact outcome_of_plays _ _ _ _ _ hA hB

end PD.Theorems
