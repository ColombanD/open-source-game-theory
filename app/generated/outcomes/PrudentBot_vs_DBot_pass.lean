import PrisonersDilemma.Bots.LlmGenerations.PrudentBot
import PrisonersDilemma.Bots.DBot
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Dynamics
import PrisonersDilemma.BaseTheorems

open PD
open PD.Bots
open PD.BaseTheorems
namespace PD.Theorems

private theorem ps_false_bot_DB_plays_C (k : Nat) (q : Prog) :
    proofSearch k (.plays (.bot DefectBot) q .C) = false := by
  cases h : proofSearch k (.plays (.bot DefectBot) q .C) with
  | true =>
    exfalso
    obtain ⟨n, hn⟩ := proofSearch_sound _ _ h
    rcases n with _ | _ | n
    · simp [play, eval] at hn
    · simp [play, eval, DefectBot] at hn
    · simp [play, eval, DefectBot] at hn
  | false => rfl

theorem llm_outcome_PrudentBot_vs_DBot :
    ∃ k₂, ∀ k, k₂ < k →
      ∃ fuel, outcome fuel (PrudentBot k) DBot = some (.D, .C) := by
  refine ⟨0, fun k _ => ⟨20, ?_⟩⟩
  have hfalse := ps_false_bot_DB_plays_C k
    ((Prog.opp.sim (Prog.const Action.D).bot).ite Action.D
      (Prog.search k (Formula.plays Prog.opp Prog.self Action.C) (Prog.const Action.C)
        (Prog.const Action.D))
      (Prog.const Action.D))
  simp only [DefectBot] at hfalse
  simp [outcome, play, eval, PrudentBot, DBot, DefectBot, Prog.subst, Formula.subst,
        show (Action.D == Action.C) = false from rfl,
        show (Action.C == Action.D) = false from rfl,
        hfalse]

end PD.Theorems
