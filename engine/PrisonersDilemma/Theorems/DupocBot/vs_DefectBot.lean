import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Bots.DupocBot
import PrisonersDilemma.Theorems.DefectBot.Helpers
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Base.Asymptotics
import PrisonersDilemma.Theorems.DupocBot.Helpers
import PrisonersDilemma.Outcome

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems
/-- DupocBot vs DefectBot: uses proof search being false -/
@[outcome]
theorem outcome_DupocBot_vs_DefectBot :
    OutcomeSpec .universal 2
      DupocBot (fun _ => DefectBot) (some (.D, .D)) := by
  intro k fuel
  -- Left side: Dupoc executes its `.search` guard. The guard's search fails (`¬ ⊢_k`,
  -- the formula is false) by the lemma above, so the `search` falls through to the final `.const .D` branch.
  have hA : play (fuel + 2) (DupocBot k) DefectBot = some .D := by
    show eval (fuel + 2) (DupocBot k) DefectBot (DupocBot k) = some .D
    -- `guard_false` tells us the proof search for “DefectBot plays C” fails.
    -- Once we unfold the bot, the remaining `simp` can simplify the search node
    -- and the constant branch all the way down to `.D`.
    have hg := proofSearch_false_for_DefectBot k
    unfold DupocBot at hg ⊢
    simp [eval, Prog.subst, Formula.subst, hg]
  -- Right side: DefectBot is definitionally the constant `.D` bot.
  have hB : play (fuel + 2) DefectBot (DupocBot k) = some .D := rfl
  -- Finally, `outcome` just packages the two `play` results together.
  simp [outcome, hA, hB]

end PD.Theorems
