import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Base.Asymptotics
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.Bots.LlmGenerations.CIMCIC
import PrisonersDilemma.Bots.OBot
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Bots.DefectBot

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

-- What are the ctxGuards of OBot vs CIMCIC?
example (k : Nat) : ctxGuards OBot (CIMCIC k)
    [.iteL CooperateBot Action.C (.const Action.D),
     .iteL DefectBot Action.C (.const Action.D)]
    = [.plays (CIMCIC k) (.bot CooperateBot) Action.C,
       .plays (CIMCIC k) (.bot DefectBot) Action.C] := by
  simp [ctxGuards, ctxGuard]

