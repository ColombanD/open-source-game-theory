import PrisonersDilemmaNew.Program
import PrisonersDilemmaNew.Dynamics
import PrisonersDilemmaNew.Bots.CooperateBot
import PrisonersDilemmaNew.Bots.DefectBot
import PrisonersDilemmaNew.Theorems.DefectBot

open PDNew
open PDNew.Bots

namespace PDNew.Theorems

-- CooperateBot always cooperates (with any fuel ≥ 1).
theorem play_CooperateBot (n : Nat) (opponent : Prog) :
      play (n+1) CooperateBot opponent = some .C := by
    unfold play eval CooperateBot
    simp only

-- The interpretation "CB plays D against q" is false.
-- This is the semantic content the soundness axiom will consume.
theorem interp_CooperateBot_plays_D_false (q : Prog) :
    ¬ (Formula.plays CooperateBot q .D).interp := by
  rintro ⟨n, hn⟩
  cases n with
  | zero   => simp only [play, eval, reduceCtorEq] at hn
  | succ m =>
      rw [play_CooperateBot] at hn
      cases hn

-- CooperateBot vs DefectBot: the cooperator is exploited, (C, D).
theorem outcome_CooperateBot_vs_DefectBot (n : Nat) :
    outcome (n+1) CooperateBot DefectBot = some (.C, .D) := by
  unfold outcome
  rw [play_CooperateBot, play_DefectBot]
  rfl

-- CooperateBot vs itself: mutual cooperation, (C, C).
theorem outcome_CooperateBot_vs_CooperateBot (n : Nat) :
    outcome (n+1) CooperateBot CooperateBot = some (.C, .C) := by
  unfold outcome
  rw [play_CooperateBot]
  rfl

end PDNew.Theorems
