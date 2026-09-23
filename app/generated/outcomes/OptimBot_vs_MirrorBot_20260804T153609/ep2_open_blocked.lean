import PrisonersDilemma.Bots.LlmGenerations.OptimBot
import PrisonersDilemma.Bots.MirrorBot
import PrisonersDilemma.Dynamics
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.Base.Asymptotics

open PD
open PD.Bots
open PD.BaseTheorems
namespace PD.Theorems

theorem omopt_plays_C (k fuel : Nat)
    (hg1 : proofSearch k (.plays MirrorBot (OptimBot k k) Action.C) = false)
    (hg3 : proofSearch k (.plays MirrorBot (OptimBot k k) Action.D) = false) :
    play (fuel + 5) (OptimBot k k) MirrorBot = some .C := by
  show eval (fuel + 5) (OptimBot k k) MirrorBot (OptimBot k k) = some .C
  unfold OptimBot at hg1 hg3 ⊢
  simp [eval, Prog.subst, Formula.subst, hg1, hg3]

theorem ommir_plays_C (k fuel : Nat)
    (hg1 : proofSearch k (.plays MirrorBot (OptimBot k k) Action.C) = false)
    (hg3 : proofSearch k (.plays MirrorBot (OptimBot k k) Action.D) = false) :
    play (fuel + 6) MirrorBot (OptimBot k k) = some .C := by
  have h := omopt_plays_C k fuel hg1 hg3
  show eval (fuel + 6) MirrorBot (OptimBot k k) MirrorBot = some .C
  simpa [eval, MirrorBot, Prog.subst] using h

end PD.Theorems

