import PrisonersDilemma.Bots.EBot
import PrisonersDilemma.Bots.OBot
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Bots.DBot
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.Theorems.DBot
import PrisonersDilemma.Theorems.OBot
import PrisonersDilemma.Theorems.TitForTatBot
import PrisonersDilemma.Theorems.MirrorBot
import PrisonersDilemma.Theorems.EBot.Helpers


open PD.Bots
namespace PD.Theorems
/--
With `.bot`-wrapped bot references, EBot's third guard `(.sim .opp (.bot MirrorBot))`
is now an independent probe of "opp vs MirrorBot": substitution does not descend
into `.bot`, so `MirrorBot`'s placeholders bind to MirrorBot's own frame at unwrap
time rather than being captured by the outer EBot/EBot frame. In self-play this
makes the third guard cleanly evaluate to `C` (EBot mirrors itself against
MirrorBot, MirrorBot cooperates), so EBot cooperates with itself.
-/
theorem outcome_EBot_vs_EBot (fuel : Nat):
    outcome (fuel + 11) EBot EBot = some (.C, .C) := by
  -- Helpers: EBot's behaviour against `.bot`-wrapped probes.
  have hEBotBotD : ∀ k, eval (k + 6) EBot (.bot DefectBot) EBot = some .D := by
    intro k
    have hOuterG : eval (k + 5) EBot (.bot DefectBot) (.sim .opp (.bot DefectBot)) = some .D := by
      simp only [eval, Prog.subst, DefectBot]
    have hInnerG : eval (k + 4) EBot (.bot DefectBot) (.sim .opp (.bot CooperateBot)) = some .D := by
      simp only [eval, Prog.subst, DefectBot]
    have hInnerInnerG : eval (k + 3) EBot (.bot DefectBot) (.sim .opp (.bot MirrorBot)) = some .D := by
      simp only [eval, Prog.subst, DefectBot]
    have hInnerInnerIte : eval (k + 4) EBot (.bot DefectBot)
        (.ite (.sim .opp (.bot MirrorBot)) .C (.const .C) (.const .D)) = some .D := by
      rw [eval_ite_from_guard _ _ _ _ _ _ _ _ hInnerInnerG]; rfl
    have hInnerIte : eval (k + 5) EBot (.bot DefectBot)
        (.ite (.sim .opp (.bot CooperateBot)) .C (.const .C)
          (.ite (.sim .opp (.bot MirrorBot)) .C (.const .C) (.const .D))) = some .D := by
      rw [eval_ite_from_guard _ _ _ _ _ _ _ _ hInnerG]
      exact hInnerInnerIte
    show eval (k + 6) EBot (.bot DefectBot)
        (.ite (.sim .opp (.bot DefectBot)) .C (.const .D)
          (.ite (.sim .opp (.bot CooperateBot)) .C (.const .C)
            (.ite (.sim .opp (.bot MirrorBot)) .C (.const .C) (.const .D)))) = some .D
    rw [eval_ite_from_guard _ _ _ _ _ _ _ _ hOuterG]
    exact hInnerIte
  have hEBotBotC : ∀ k, eval (k + 4) EBot (.bot CooperateBot) EBot = some .D := by
    intro k
    have hOuterG : eval (k + 3) EBot (.bot CooperateBot) (.sim .opp (.bot DefectBot)) = some .C := by
      simp only [eval, Prog.subst, CooperateBot]
    show eval (k + 4) EBot (.bot CooperateBot)
        (.ite (.sim .opp (.bot DefectBot)) .C (.const .D)
          (.ite (.sim .opp (.bot CooperateBot)) .C (.const .C)
            (.ite (.sim .opp (.bot MirrorBot)) .C (.const .C) (.const .D)))) = some .D
    rw [eval_ite_from_guard _ _ _ _ _ _ _ _ hOuterG]; rfl
  have hEBotBotM : ∀ k, eval (k + 7) EBot (.bot MirrorBot) EBot = some .C := by
    intro k
    have hOuterG : eval (k + 6) EBot (.bot MirrorBot) (.sim .opp (.bot DefectBot)) = some .D := by
      simp only [eval, Prog.subst, MirrorBot, DefectBot]
    have hInnerG : eval (k + 5) EBot (.bot MirrorBot) (.sim .opp (.bot CooperateBot)) = some .C := by
      simp only [eval, Prog.subst, MirrorBot, CooperateBot]
    have hInnerIte : eval (k + 6) EBot (.bot MirrorBot)
        (.ite (.sim .opp (.bot CooperateBot)) .C (.const .C)
          (.ite (.sim .opp (.bot MirrorBot)) .C (.const .C) (.const .D))) = some .C := by
      rw [eval_ite_from_guard _ _ _ _ _ _ _ _ hInnerG]; rfl
    show eval (k + 7) EBot (.bot MirrorBot)
        (.ite (.sim .opp (.bot DefectBot)) .C (.const .D)
          (.ite (.sim .opp (.bot CooperateBot)) .C (.const .C)
            (.ite (.sim .opp (.bot MirrorBot)) .C (.const .C) (.const .D)))) = some .C
    rw [eval_ite_from_guard _ _ _ _ _ _ _ _ hOuterG]
    exact hInnerIte

  -- Self-play guards: each reduces to EBot vs (.bot Z) via L2.
  have hG1 : eval (fuel + 10) EBot EBot (.sim .opp (.bot DefectBot)) = some .D :=
    eval_sim_opp_bot_of_play _ _ _ _ _
      (play_from_eval _ _ _ _ (hEBotBotD (fuel + 3)))
  have hG2 : eval (fuel + 9) EBot EBot (.sim .opp (.bot CooperateBot)) = some .D :=
    eval_sim_opp_bot_of_play _ _ _ _ _
      (play_from_eval _ _ _ _ (hEBotBotC (fuel + 4)))
  have hG3 : eval (fuel + 8) EBot EBot (.sim .opp (.bot MirrorBot)) = some .C :=
    eval_sim_opp_bot_of_play _ _ _ _ _
      (play_from_eval _ _ _ _ (hEBotBotM fuel))

  have hInnerInnerIte : eval (fuel + 9) EBot EBot
      (.ite (.sim .opp (.bot MirrorBot)) .C (.const .C) (.const .D)) = some .C := by
    rw [eval_ite_from_guard _ _ _ _ _ _ _ _ hG3]; rfl
  have hInnerIte : eval (fuel + 10) EBot EBot
      (.ite (.sim .opp (.bot CooperateBot)) .C (.const .C)
        (.ite (.sim .opp (.bot MirrorBot)) .C (.const .C) (.const .D))) = some .C := by
    rw [eval_ite_from_guard _ _ _ _ _ _ _ _ hG2]
    exact hInnerInnerIte
  have hA : play (fuel + 11) EBot EBot = some .C := by
    show eval (fuel + 11) EBot EBot
        (.ite (.sim .opp (.bot DefectBot)) .C (.const .D)
          (.ite (.sim .opp (.bot CooperateBot)) .C (.const .C)
            (.ite (.sim .opp (.bot MirrorBot)) .C (.const .C) (.const .D)))) = some .C
    rw [eval_ite_from_guard _ _ _ _ _ _ _ _ hG1]
    exact hInnerIte
  simp [outcome, hA]

end PD.Theorems
