import PrisonersDilemma.Bots.LlmGenerations.JustBot
import PrisonersDilemma.Bots.DBot
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Bots.DupocBot
import PrisonersDilemma.Dynamics
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Theorems.Helpers

open PD
open PD.Bots
open PD.BaseTheorems
namespace PD.Theorems

-- .bot DefectBot cannot play C against anything
theorem ps_false_bot_DefectBot_vs_bot_DupocBot_JB (k : Nat) :
    proofSearch k (.plays (.bot DefectBot) (.bot (DupocBot k)) .C) = false := by
  cases h : proofSearch k (.plays (.bot DefectBot) (.bot (DupocBot k)) .C) with
  | true =>
    exact absurd (proofSearch_sound _ _ h) (by
      rintro ⟨n, hn⟩
      rcases n with _ | _ | n
      · simp [play, eval] at hn
      · simp [play, eval] at hn
      · simp [play, eval, DefectBot] at hn)
  | false => rfl

-- .bot (DupocBot k) defects against .bot DefectBot: its guard fails (DefectBot plays D)
theorem bot_DupocBot_plays_D_against_bot_DefectBot_JB (k fuel : Nat) :
    play (fuel + 3) (.bot (DupocBot k)) (.bot DefectBot) = some .D := by
  have hg := ps_false_bot_DefectBot_vs_bot_DupocBot_JB k
  show eval (fuel + 3) (.bot (DupocBot k)) (.bot DefectBot) (.bot (DupocBot k)) = some .D
  unfold DupocBot at hg ⊢
  simp [eval, Prog.subst, Formula.subst, hg]

-- DBot cooperates against .bot (DupocBot k): its sim probe sees D, so takes .const .C
theorem DBot_plays_C_against_bot_DupocBot_JB (k fuel : Nat) :
    play (fuel + 5) DBot (.bot (DupocBot k)) = some .C := by
  have hInner : play (fuel + 3) (.bot (DupocBot k)) (.bot DefectBot) = some .D :=
    bot_DupocBot_plays_D_against_bot_DefectBot_JB k fuel
  have hGuard : eval (fuel + 4) DBot (.bot (DupocBot k)) (.sim .opp (.bot DefectBot)) = some .D := by
    simpa [Nat.add_assoc] using
      eval_sim_opp_bot_of_play (fuel + 3) DBot (.bot (DupocBot k)) DefectBot .D hInner
  have hPlay := play_ite_from_guard
    fuel 4 DBot (.bot (DupocBot k)) (.sim .opp (.bot DefectBot))
    (.const Action.D) (.const Action.C) Action.C Action.D
    (by rfl) hGuard
  simpa [eval] using hPlay

-- JustBot k defects against .bot DefectBot: its guard (.plays .bot DefectBot ...) fails
theorem JustBot_plays_D_against_bot_DefectBot_JB (k fuel : Nat) :
    play (fuel + 2) (JustBot k) (.bot DefectBot) = some .D := by
  have hg := ps_false_bot_DefectBot_vs_bot_DupocBot_JB k
  show eval (fuel + 2) (JustBot k) (.bot DefectBot) (JustBot k) = some .D
  unfold JustBot
  simp [eval, Prog.subst, Formula.subst, hg]

-- DBot cooperates against JustBot k: sim probe sees JustBot defects → DBot cooperates
theorem DBot_plays_C_against_JustBot_JB (k fuel : Nat) :
    play (fuel + 4) DBot (JustBot k) = some .C := by
  have hInner : play (fuel + 2) (JustBot k) (.bot DefectBot) = some .D :=
    JustBot_plays_D_against_bot_DefectBot_JB k fuel
  have hGuard : eval (fuel + 3) DBot (JustBot k) (.sim .opp (.bot DefectBot)) = some .D := by
    simpa [Nat.add_assoc] using
      eval_sim_opp_bot_of_play (fuel + 2) DBot (JustBot k) DefectBot .D hInner
  have hPlay := play_ite_from_guard
    fuel 3 DBot (JustBot k) (.sim .opp (.bot DefectBot))
    (.const Action.D) (.const Action.C) Action.C Action.D
    (by rfl) hGuard
  simpa [eval] using hPlay

-- JustBot cooperates against DBot when proof search fires
theorem JustBot_plays_C_against_DBot_JB (k fuel : Nat)
    (hk : proofSearch k (.plays DBot (.bot (DupocBot k)) .C) = true) :
    play (fuel + 2) (JustBot k) DBot = some .C := by
  show eval (fuel + 2) (JustBot k) DBot (JustBot k) = some .C
  unfold JustBot
  simp [eval, Prog.subst, Formula.subst, hk]

theorem llm_outcome_JustBot_vs_DBot (n : Nat) :
    ∃ k, outcome (n + 4) (JustBot k) DBot = some (.C, .C) := by
  let k := atom_cost 5
  refine ⟨k, ?_⟩
  have hPlay : play 5 DBot (.bot (DupocBot k)) = some .C := by
    simpa using DBot_plays_C_against_bot_DupocBot_JB k 0
  have hk : proofSearch k (.plays DBot (.bot (DupocBot k)) .C) = true :=
    (proofSearch_spec _ _).2 (Provable.atom (atom_complete DBot (.bot (DupocBot k)) .C 5 hPlay))
  have hA : play (n + 4) (JustBot k) DBot = some .C := by
    have h := JustBot_plays_C_against_DBot_JB k (n + 2) hk
    simpa [Nat.add_assoc] using h
  have hB : play (n + 4) DBot (JustBot k) = some .C :=
    DBot_plays_C_against_JustBot_JB k n
  exact outcome_of_plays _ _ _ _ _ hA hB

end PD.Theorems
