import PrisonersDilemma.Bots.LlmGenerations.GuardianBot
import PrisonersDilemma.Bots.DBot
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Dynamics
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Base.Helpers

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

theorem gd_ps_true_guardian_vs_DBot (k : Nat) (hk : 5 ≤ k) :
    proofSearch k (.plays DBot (.bot CooperateBot) .D) = true := by
  refine (proofSearch_spec _ _).2 (Pf.atom
    ⟨PlaysProof.ite_t (PlaysProof.sim (PlaysProof.bot PlaysProof.const))
      (by decide) PlaysProof.const, ?_⟩)
  show c_leaf + c_node + c_node + c_leaf + c_node ≤ k
  simp only [c_leaf, c_node]
  omega

theorem gd_GuardianBot_plays_D_vs_DBot (k fuel : Nat) (hk : 5 ≤ k) :
    play (fuel + 2) (GuardianBot k) DBot = some .D := by
  have hg := gd_ps_true_guardian_vs_DBot k hk
  show eval (fuel + 2) (GuardianBot k) DBot (GuardianBot k) = some .D
  unfold GuardianBot
  simp [eval, Prog.subst, Formula.subst, hg]

theorem gd_GuardianBot_plays_D_vs_botDefect (k fuel : Nat) (hk : 5 ≤ k) :
    play (fuel + 2) (GuardianBot k) (.bot DefectBot) = some .D := by
  have hg : proofSearch k (.plays (.bot DefectBot) (.bot CooperateBot) .D) = true := by
    refine (proofSearch_spec _ _).2 (Pf.atom
      ⟨PlaysProof.bot PlaysProof.const, ?_⟩)
    show c_leaf + c_node ≤ k
    simp only [c_leaf, c_node]; omega
  show eval (fuel + 2) (GuardianBot k) (.bot DefectBot) (GuardianBot k) = some .D
  unfold GuardianBot
  simp [eval, Prog.subst, Formula.subst, hg]

theorem gd_DBot_plays_C_vs_GuardianBot (k fuel : Nat) (hk : 5 ≤ k) :
    play (fuel + 4) DBot (GuardianBot k) = some .C := by
  have hInner : play (fuel + 2) (GuardianBot k) (.bot DefectBot) = some .D :=
    gd_GuardianBot_plays_D_vs_botDefect k fuel hk
  have hGuard : eval (fuel + 3) DBot (GuardianBot k) (.sim .opp (.bot DefectBot)) = some .D :=
    eval_sim_opp_bot_of_play (fuel + 2) DBot (GuardianBot k) DefectBot Action.D hInner
  have hPlay := play_ite_from_guard
    fuel 3 DBot (GuardianBot k) (.sim .opp (.bot DefectBot))
    (.const Action.D) (.const Action.C) Action.C Action.D
    (by rfl) hGuard
  simpa [eval] using hPlay

theorem llm_outcome_GuardianBot_vs_DBot :
    ∃ k₂, ∀ k, k₂ < k →
      ∃ fuel, outcome fuel (GuardianBot k) DBot = some (.D, .C) := by
  refine ⟨5, fun k hk => ⟨4, ?_⟩⟩
  have hk5 : 5 ≤ k := by omega
  have hA : play 4 (GuardianBot k) DBot = some .D := by
    simpa using gd_GuardianBot_plays_D_vs_DBot k 2 hk5
  have hB : play 4 DBot (GuardianBot k) = some .C := by
    simpa using gd_DBot_plays_C_vs_GuardianBot k 0 hk5
  exact outcome_of_plays _ _ _ _ _ hA hB

end PD.Theorems
