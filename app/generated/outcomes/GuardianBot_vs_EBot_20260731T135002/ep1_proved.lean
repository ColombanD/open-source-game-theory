import PrisonersDilemma.Bots.LlmGenerations.GuardianBot
import PrisonersDilemma.Bots.EBot
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Bots.MirrorBot
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.BaseTheorems

open PD PD.BaseTheorems PD.Bots
namespace PD.Theorems

-- GuardianBot vs .bot DefectBot: guard "DefectBot plays D vs botCB" provable at k≥2
theorem gebot_guardian_D_vs_botDefect (k fuel : Nat) (hk : 2 ≤ k) :
    play (fuel + 2) (GuardianBot k) (.bot DefectBot) = some .D := by
  have hg : proofSearch k (.plays (.bot DefectBot) (.bot CooperateBot) .D) = true :=
    (proofSearch_spec _ _).2 (Pf.atom ⟨PlaysProof.bot PlaysProof.const, by simp only [c_leaf, c_node]; omega⟩)
  show eval (fuel + 2) (GuardianBot k) (.bot DefectBot) (GuardianBot k) = some .D
  unfold GuardianBot
  simp [eval, Prog.subst, Formula.subst, hg]

theorem gebot_guardian_C_vs_botCoop (k fuel : Nat) :
    play (fuel + 2) (GuardianBot k) (.bot CooperateBot) = some .C := by
  have hg : proofSearch k (.plays (.bot CooperateBot) (.bot CooperateBot) .D) = false := by
    cases h : proofSearch k (.plays (.bot CooperateBot) (.bot CooperateBot) .D) with
    | true =>
        exfalso
        obtain ⟨n, hn⟩ := proofSearch_sound _ _ h
        cases n with
        | zero => simp [play, eval] at hn
        | succ m => cases m with
          | zero => simp [play, eval] at hn
          | succ j =>
              rw [show play (j+2) (.bot CooperateBot) (.bot CooperateBot) = some .C from by
                    simp [play, eval, CooperateBot]] at hn
              cases hn
    | false => rfl
  show eval (fuel + 2) (GuardianBot k) (.bot CooperateBot) (GuardianBot k) = some .C
  unfold GuardianBot
  simp [eval, Prog.subst, Formula.subst, hg]

theorem gebot_ebot_C (k fuel : Nat) (hk : 2 ≤ k) :
    play (fuel + 6) EBot (GuardianBot k) = some .C := by
  have hP2 : play (fuel + 3) (GuardianBot k) (.bot CooperateBot) = some .C := by
    simpa [Nat.add_assoc] using gebot_guardian_C_vs_botCoop k (fuel + 1)
  have hG1 : eval (fuel + 5) EBot (GuardianBot k) (.sim .opp (.bot DefectBot)) = some .D := by
    simpa [Nat.add_assoc] using
      eval_sim_opp_bot_of_play (fuel + 4) EBot (GuardianBot k) DefectBot .D
        (by simpa [Nat.add_assoc] using gebot_guardian_D_vs_botDefect k (fuel + 2) hk)
  have hG2 : eval (fuel + 4) EBot (GuardianBot k) (.sim .opp (.bot CooperateBot)) = some .C := by
    simpa [Nat.add_assoc] using
      eval_sim_opp_bot_of_play (fuel + 3) EBot (GuardianBot k) CooperateBot .C hP2
  have hIte2 : eval (fuel + 5) EBot (GuardianBot k)
      (.ite (.sim .opp (.bot CooperateBot)) .C (.const .C)
        (.ite (.sim .opp (.bot MirrorBot)) .C (.const .C) (.const .D))) = some .C := by
    rw [eval_ite_from_guard _ _ _ _ _ _ _ _ hG2]; rfl
  show eval (fuel + 6) EBot (GuardianBot k)
      (.ite (.sim .opp (.bot DefectBot)) .C (.const .D)
        (.ite (.sim .opp (.bot CooperateBot)) .C (.const .C)
          (.ite (.sim .opp (.bot MirrorBot)) .C (.const .C) (.const .D)))) = some .C
  rw [eval_ite_from_guard _ _ _ _ _ _ _ _ hG1]
  simpa using hIte2

-- guard certificate for GuardianBot: EBot plays D vs .bot CooperateBot
theorem gebot_guard_cert (k : Nat) (hk : 3 ^ 5 ≤ k) :
    proofSearch k (.plays EBot (.bot CooperateBot) .D) = true := by
  have hplay : play 5 EBot (.bot CooperateBot) = some .D := by
    show eval 5 EBot (.bot CooperateBot) EBot = some .D
    simp [eval, EBot, Prog.subst, CooperateBot, DefectBot, MirrorBot]; decide
  have hcert : AtomProvable (3 ^ 5) (.plays EBot (.bot CooperateBot) .D) :=
    atom_complete_searchfree EBot (.bot CooperateBot) .D 5 rfl rfl hplay
  exact (proofSearch_spec _ _).2 (Pf.atom (atom_monotone (3 ^ 5) k _ hk hcert))

theorem gebot_guardian_D (k fuel : Nat)
    (hg : proofSearch k (.plays EBot (.bot CooperateBot) .D) = true) :
    play (fuel + 2) (GuardianBot k) EBot = some .D := by
  show eval (fuel + 2) (GuardianBot k) EBot (GuardianBot k) = some .D
  unfold GuardianBot
  simp [eval, Prog.subst, Formula.subst, hg]

theorem llm_outcome_GuardianBot_vs_EBot :
    ∃ k₂, ∀ k, k₂ < k →
      ∃ fuel, outcome fuel (GuardianBot k) EBot = some (.D, .C) := by
  refine ⟨3 ^ 5, fun k hk => ⟨6, ?_⟩⟩
  have hk2 : 2 ≤ k := by omega
  have hkcert : 3 ^ 5 ≤ k := by omega
  have hA : play 6 (GuardianBot k) EBot = some .D := by
    have := gebot_guardian_D k 4 (gebot_guard_cert k hkcert)
    simpa using this
  have hB : play 6 EBot (GuardianBot k) = some .C := by
    have := gebot_ebot_C k 0 hk2
    simpa using this
  exact outcome_of_plays _ _ _ _ _ hA hB

end PD.Theorems

