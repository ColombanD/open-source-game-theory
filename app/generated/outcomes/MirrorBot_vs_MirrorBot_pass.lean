import PrisonersDilemma.Bots.MirrorBot

open PDNew
open PDNew.Bots
namespace PDNew.Theorems

-- MirrorBot vs MirrorBot diverges: play returns `none` at every fuel level.
-- Reason: MirrorBot = .sim .opp .self. Evaluating .sim closes p=.opp and
-- q=.self under (me=MirrorBot, opp=MirrorBot), giving p' = q' = MirrorBot.
-- The recursive call `eval n MirrorBot MirrorBot MirrorBot` is the same
-- shape with one less fuel, so the recursion bottoms out at `eval 0 = none`.
theorem play_MirrorBot_vs_MirrorBot_none : ∀ n, play n MirrorBot MirrorBot = none := by
  intro n
  induction n with
  | zero => rfl
  | succ k ih =>
    unfold play
    unfold MirrorBot at *
    show eval (k+1) (.sim .opp .self) (.sim .opp .self) (.sim .opp .self) = none
    simp only [eval, Prog.subst]
    exact ih

theorem outcome_MirrorBot_vs_MirrorBot_none : ∀ n, outcome n MirrorBot MirrorBot = none := by
  intro n
  simp [outcome, play_MirrorBot_vs_MirrorBot_none n]

-- The requested theorem `llm_outcome_MirrorBot_vs_MirrorBot` cannot be
-- proved with `some (.X, .Y)` on the RHS for ANY fuel: outcome is uniformly
-- `none`, so for every choice of (X, Y),
--   outcome (n + FUEL) MirrorBot MirrorBot = some (.X, .Y)
-- reduces to `none = some (.X, .Y)`, which is False.

end PDNew.Theorems
