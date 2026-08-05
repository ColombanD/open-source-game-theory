import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Bots.LlmGenerations.DIMCID
import PrisonersDilemma.Bots.CupodBot
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Base.Helpers

open PD
open PD.Bots
open PD.BaseTheorems

#eval show IO Unit from do
  IO.println s!"DIMCID 0 size: {DIMCID 0 |>.size}"
  IO.println s!"CupodBot 0 size: {CupodBot 0 |>.size}"
  IO.println s!"plays (CupodBot 0) (DIMCID 0) .D size: {(Formula.plays (CupodBot 0) (DIMCID 0) Action.D).size}"
  IO.println s!"plays (DIMCID 0) (CupodBot 0) .D size: {(Formula.plays (DIMCID 0) (CupodBot 0) Action.D).size}"
