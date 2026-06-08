import PrisonersDilemma.Program
import PrisonersDilemma.Derivation
import PrisonersDilemma.Bots.DefectBot

open PDNew
open PDNew.Bots

namespace PDNew.Theorems

-- DefectBot always defects (with any fuel ≥ 1).
theorem play_DefectBot (n : Nat) (opponent : Prog) :
      play (n+1) DefectBot opponent = some .D := by
    unfold play eval DefectBot
    simp

-- The interpretation "DB plays D against q" is true.
-- This is the semantic content the completeness axiom will consume.
theorem interp_DefectBot_plays_D_true (q : Prog) :
    (Formula.plays DefectBot q .D).interp := by
  unfold Formula.interp
  exists 1

theorem interp_DefectBot_plays_C_false (q : Prog) :
    ¬ (Formula.plays DefectBot q .C).interp := by
  rintro ⟨n, hn⟩
  cases n with
  | zero   => simp only [play, eval, reduceCtorEq] at hn
  | succ m =>
      rw [play_DefectBot] at hn
      cases hn

/-- `(.bot DefectBot)` always defects after at least two fuel steps. -/
theorem play_bot_DefectBot (n : Nat) (opponent : Prog) :
    play (n + 2) (.bot DefectBot) opponent = some .D := by
  simp [play, eval, DefectBot]

/-- The interpretation "(.bot DefectBot) plays C against q" is false. -/
theorem interp_bot_DefectBot_plays_C_false (q : Prog) :
    ¬ (Formula.plays (.bot DefectBot) q .C).interp := by
  rintro ⟨n, hn⟩
  cases n with
  | zero => simp only [play, eval, reduceCtorEq] at hn
  | succ m =>
      cases m with
      | zero => simp [play, eval] at hn
      | succ fuel =>
          rw [play_bot_DefectBot] at hn
          cases hn

-- DefectBot vs itself: mutual defection, (D, D).
theorem outcome_DefectBot_vs_DefectBot (n : Nat) :
    outcome (n+1) DefectBot DefectBot = some (.D, .D) := by
  unfold outcome
  rw [play_DefectBot]
  rfl

end PDNew.Theorems
