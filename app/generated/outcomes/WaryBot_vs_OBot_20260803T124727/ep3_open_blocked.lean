import PrisonersDilemma.Bots.LlmGenerations.WaryBot
import PrisonersDilemma.Bots.OBot
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.Base.Asymptotics
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Theorems.WaryBot.Helpers
import PrisonersDilemma.Theorems.CooperateBot.Helpers

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

theorem wob_botCB_plays_C_vs_wary (k : Nat) :
    play 2 (.bot CooperateBot) (WaryBot k) = some .C := by
  show eval 2 (.bot CooperateBot) (WaryBot k) (.bot CooperateBot) = some .C
  simp [eval, CooperateBot]

/-- No ≤k certificate concludes "OBot plays D vs WaryBot k". -/
theorem wob_no_D_tail (k : Nat) :
    ∀ K φ, Pf K φ → K ≤ k →
      TailTo (.plays OBot (WaryBot k) .D) φ → False := by
  intro K φ hp hK ht
  refine no_provable_probeFirst_tail k CooperateBot
      (.ite (.sim .opp (.bot DefectBot)) .C (.const .C) (.const .D))
      (.const .D) .C .D (.neg (.plays .opp .self .C)) (.const .D) (.const .C)
      ?_ ?_ ?_ K φ hp hK ?_
  · show ¬ (Formula.interp _)
    simp only [Formula.subst, Prog.subst, Formula.interp]
    intro hcontra
    exact hcontra ⟨2, wob_botCB_plays_C_vs_wary k⟩
  · intro k' ψ c0 c1 h; simp at h
  · intro L
    cases L with
    | nil => simp [ctxPlug]
    | cons hd tl =>
        cases hd with
        | searchL g' ψ' e' => simp [ctxPlug]
        | iteL z' aT' other' =>
            intro h
            simp only [ctxPlug, Prog.ite.injEq] at h
            exact const_ne_ctxPlug (by decide) tl h.2.2.1
  · simpa [OBot, WaryBot] using ht

end PD.Theorems

