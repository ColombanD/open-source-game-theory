import PrisonersDilemmaNew.Program
import PrisonersDilemmaNew.Dynamics
import PrisonersDilemmaNew.Bots.CooperateBot

open PDNew
open PDNew.Bots

namespace PDNew.Theorems

-- CooperateBot always cooperates (with any fuel ≥ 1).
theorem play_CooperateBot (n : Nat) (opponent : Prog) :
      play (n+1) CooperateBot opponent = some .C := by
    unfold play eval CooperateBot
    simp

-- Lemma 2: the interpretation "CB plays D against q" is false.
-- This is the semantic content the soundness axiom will consume.
theorem interp_CooperateBot_plays_D_false (q : Prog) :
    ¬ (Formula.plays CooperateBot q .D).interp := by
  rintro ⟨n, hn⟩
  cases n with
  | zero   => simp [play, eval] at hn
  | succ m =>
      rw [play_CooperateBot] at hn
      cases hn                -- some .C = some .D : impossible

end PDNew.Theorems
