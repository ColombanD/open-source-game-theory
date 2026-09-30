import ArithS.Outcome.Spec
import ArithS.Outcome.Attr
import ArithS.Cells.RedCellEngine
import ArithS.Cells.DimcidFlips
import ArithS.Cells.FlipCells
import ArithS.Cells.KhatCells
import ArithS.Cells.JustSlot
import ArithS.Cells.PrudentMirror
import ArithS.Cells.PrudentLoose
import ArithS.Cells.PositiveCells
import ArithS.Cells.SoundnessCells
import ArithS.Cells.SearchFree
import ArithS.Cells.CIMCIC
import ArithS.Cells.DIMCID
import ArithS.Cells.DupocMirror
import ArithS.Cells.JustBot
import ArithS.Necessitation.Package

/-!
# ArithS.Outcome.Matrix.TitForTatBot — the `S'` cells with `TitForTatBot` on the left

Each cell is the engine's statement (`OutcomeSpecA`, `Outcome/Spec.lean`) proved from the method-named
theorem of `Cells/` that carries the mathematics (named in each docstring). Values are PA-`S'` values:
where they contradict the engine's cell the docstring says FLIP (`Research/Notes/ROUTE_B_CENSUS.md`,
"S' status per cell").
-/

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus
open LAct
open PD.Bots

/-- `sf_TitForTatBot_vs_CooperateBot` -/
@[outcomeA]
theorem outcome_TitForTatBot_vs_CooperateBot :
    OutcomeSpecA .nobudget (const TitForTatBot) (const CooperateBot) (some (.C, .C)) :=
  OutcomeSpecA.nobudget_of (OutcomeAtA.of_evalGraph sf_TitForTatBot_vs_CooperateBot)

/-- `sf_TitForTatBot_vs_DBot` -/
@[outcomeA]
theorem outcome_TitForTatBot_vs_DBot :
    OutcomeSpecA .nobudget (const TitForTatBot) (const DBot) (some (.D, .C)) :=
  OutcomeSpecA.nobudget_of (OutcomeAtA.of_evalGraph sf_TitForTatBot_vs_DBot)

/-- `sf_TitForTatBot_vs_DefectBot` -/
@[outcomeA]
theorem outcome_TitForTatBot_vs_DefectBot :
    OutcomeSpecA .nobudget (const TitForTatBot) (const DefectBot) (some (.D, .D)) :=
  OutcomeSpecA.nobudget_of (OutcomeAtA.of_evalGraph sf_TitForTatBot_vs_DefectBot)

/-- `sf_TitForTatBot_vs_TitForTatBot` -/
@[outcomeA]
theorem outcome_TitForTatBot_vs_TitForTatBot :
    OutcomeSpecA .nobudget (const TitForTatBot) (const TitForTatBot) (some (.C, .C)) :=
  OutcomeSpecA.nobudget_of (OutcomeAtA.of_evalGraph sf_TitForTatBot_vs_TitForTatBot)

end ArithS
