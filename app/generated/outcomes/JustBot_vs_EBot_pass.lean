import PrisonersDilemma.Bots.LlmGenerations.JustBot
import PrisonersDilemma.Bots.EBot
import PrisonersDilemma.Bots.DupocBot
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Bots.MirrorBot
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Axioms
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Theorems.Helpers
import PrisonersDilemma.Theorems.CooperateBot
import PrisonersDilemma.Theorems.DefectBot

open PD
open PD.Axioms
open PD.Bots
open PD.BaseTheorems
namespace PD.Theorems

theorem llm_outcome_JustBot_vs_EBot :
    ∃ k₂, ∀ k, k₂ < k →
      ∃ fuel, outcome fuel (JustBot k) EBot = some (.C, .C) := by
  refine ⟨atom_cost 6, ?_⟩
  intro k hk
  have h26 : atom_cost 2 ≤ atom_cost 6 := atom_cost_mono (by omega)
  have hb2 : atom_cost 2 ≤ k := by omega
  have hb6 : atom_cost 6 ≤ k := by omega
  -- proof-search facts
  have hPSf : proofSearch k (.plays (.bot DefectBot) (.bot (DupocBot k)) .C) = false := by
    cases h : proofSearch k (.plays (.bot DefectBot) (.bot (DupocBot k)) .C) with
    | true => exact absurd (proofSearch_sound _ _ h) (interp_bot_DefectBot_plays_C_false _)
    | false => rfl
  have hPS1 : proofSearch k (.plays (.bot CooperateBot) (.bot (DupocBot k)) .C) = true :=
    proofSearch_monotone (atom_cost 2) k _ hb2
      ((proofSearch_spec _ _).2 (Provable.atom
        (atom_complete (.bot CooperateBot) (.bot (DupocBot k)) .C 2
          (by simpa using play_bot_CooperateBot 0 (.bot (DupocBot k))))))
  -- DupocBot (wrapped) defects vs .bot DefectBot, cooperates vs .bot CooperateBot
  have lemA : ∀ j, play (j+3) (.bot (DupocBot k)) (.bot DefectBot) = some .D := by
    intro j
    show eval (j+3) (.bot (DupocBot k)) (.bot DefectBot) (.bot (DupocBot k)) = some .D
    unfold DupocBot at hPSf ⊢
    simp [eval, Prog.subst, Formula.subst, hPSf]
  have lemB : ∀ j, play (j+3) (.bot (DupocBot k)) (.bot CooperateBot) = some .C := by
    intro j
    show eval (j+3) (.bot (DupocBot k)) (.bot CooperateBot) (.bot (DupocBot k)) = some .C
    unfold DupocBot at hPS1 ⊢
    simp [eval, Prog.subst, Formula.subst, hPS1]
  -- EBot cooperates whenever the opponent defects vs DefectBot and cooperates vs CooperateBot
  have ebot_C : ∀ (op : Prog),
      (∀ j, play (j+3) op (.bot DefectBot) = some .D) →
      (∀ j, play (j+3) op (.bot CooperateBot) = some .C) →
      play 6 EBot op = some .C := by
    intro op hD hC
    have hG1 : eval 5 EBot op (.sim .opp (.bot DefectBot)) = some .D :=
      eval_sim_opp_bot_of_play 4 EBot op DefectBot Action.D (hD 1)
    have hG2 : eval 4 EBot op (.sim .opp (.bot CooperateBot)) = some .C :=
      eval_sim_opp_bot_of_play 3 EBot op CooperateBot Action.C (hC 0)
    have hInner : eval 5 EBot op
        (.ite (.sim .opp (.bot CooperateBot)) Action.C (.const Action.C)
          (.ite (.sim .opp (.bot MirrorBot)) Action.C (.const Action.C) (.const Action.D))) = some .C := by
      simpa using (eval_ite_from_guard 4 EBot op (.sim .opp (.bot CooperateBot)) (.const Action.C)
        (.ite (.sim .opp (.bot MirrorBot)) Action.C (.const Action.C) (.const Action.D))
        Action.C Action.C hG2)
    have hPlay := play_ite_from_guard 0 5 EBot op (.sim .opp (.bot DefectBot))
      (.const Action.D)
      (.ite (.sim .opp (.bot CooperateBot)) Action.C (.const Action.C)
        (.ite (.sim .opp (.bot MirrorBot)) Action.C (.const Action.C) (.const Action.D)))
      Action.C Action.D
      (by rfl) hG1
    simpa [hInner] using hPlay
  have hEO : play 6 EBot (.bot (DupocBot k)) = some .C := ebot_C (.bot (DupocBot k)) lemA lemB
  have hPS3 : proofSearch k (.plays EBot (.bot (DupocBot k)) .C) = true :=
    proofSearch_monotone (atom_cost 6) k _ hb6
      ((proofSearch_spec _ _).2 (Provable.atom
        (atom_complete EBot (.bot (DupocBot k)) .C 6 hEO)))
  -- JustBot vs EBot: cooperates
  have hJ : ∀ j, play (j+2) (JustBot k) EBot = some .C := by
    intro j
    show eval (j+2) (JustBot k) EBot (JustBot k) = some .C
    unfold JustBot
    unfold DupocBot at hPS3 ⊢
    simp [eval, Prog.subst, Formula.subst, hPS3]
  -- JustBot vs .bot DefectBot defects, vs .bot CooperateBot cooperates
  have lemC : ∀ j, play (j+2) (JustBot k) (.bot DefectBot) = some .D := by
    intro j
    show eval (j+2) (JustBot k) (.bot DefectBot) (JustBot k) = some .D
    unfold JustBot
    unfold DupocBot at hPSf ⊢
    simp [eval, Prog.subst, Formula.subst, hPSf]
  have lemD : ∀ j, play (j+2) (JustBot k) (.bot CooperateBot) = some .C := by
    intro j
    show eval (j+2) (JustBot k) (.bot CooperateBot) (JustBot k) = some .C
    unfold JustBot
    unfold DupocBot at hPS1 ⊢
    simp [eval, Prog.subst, Formula.subst, hPS1]
  have hEJ6 : play 6 EBot (JustBot k) = some .C :=
    ebot_C (JustBot k) (fun j => lemC (j+1)) (fun j => lemD (j+1))
  exact ⟨6, outcome_of_plays 6 (JustBot k) EBot .C .C (hJ 4) hEJ6⟩

end PD.Theorems
