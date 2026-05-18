import PrisonersDilemma.Bots.TitForTatBot
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Theorems.Helpers

open PDNew
open PDNew.Bots
namespace PDNew.Theorems

theorem llm_outcome_TitForTatBot_vs_TitForTatBot (n : Nat) :
    outcome (n+7) TitForTatBot TitForTatBot = some (.C, .C) := by
  have hGuard : eval (n + 6) TitForTatBot TitForTatBot (.sim .opp (.bot CooperateBot)) = some .C := by
    simp [eval, Prog.subst, TitForTatBot, CooperateBot]; decide
  have hA : play (n + 7) TitForTatBot TitForTatBot = some .C := by
    have hPlay := play_ite_from_guard
      n 6 TitForTatBot TitForTatBot (.sim .opp (.bot CooperateBot))
      (.const Action.C) (.const Action.D)
      Action.C Action.C
      (by rfl) hGuard
    simpa [eval] using hPlay
  simp [outcome, hA]

end PDNew.Theorems
