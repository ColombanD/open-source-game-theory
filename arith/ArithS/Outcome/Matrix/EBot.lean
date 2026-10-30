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
import ArithS.Necessitation.Package
import ArithS.Cells.Common.Templates
import ArithS.Cells.Common.Probers
import ArithS.Cells.Common.Families
import ArithS.Cells.Common.Khat
import ArithS.Assembly.Cell
import ArithS.Eval.SimTest

/-!
# ArithS.Outcome.Matrix.EBot — the `S'` cells with `EBot` on the left

Each cell is the engine's statement (`OutcomeSpecA`, `Outcome/Spec.lean`) proved from the method-named
theorem of `Cells/` that carries the mathematics (named in each docstring). Values are PA-`S'` values:
where they contradict the engine's cell the docstring says FLIP (`docs/notes/ROUTE_B_CENSUS.md`,
"S' status per cell").
-/

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus
open LAct
open PD.Bots

/-- `sf_EBot_vs_CooperateBot` -/
@[outcomeA]
theorem outcome_EBot_vs_CooperateBot :
    OutcomeSpecA .nobudget (const EBot) (const CooperateBot) (some (.D, .C)) :=
  OutcomeSpecA.nobudget_of (OutcomeAtA.of_evalGraph sf_EBot_vs_CooperateBot)

/-- `sf_EBot_vs_DBot` -/
@[outcomeA]
theorem outcome_EBot_vs_DBot :
    OutcomeSpecA .nobudget (const EBot) (const DBot) (some (.D, .C)) :=
  OutcomeSpecA.nobudget_of (OutcomeAtA.of_evalGraph sf_EBot_vs_DBot)

/-- `sf_EBot_vs_DefectBot` -/
@[outcomeA]
theorem outcome_EBot_vs_DefectBot :
    OutcomeSpecA .nobudget (const EBot) (const DefectBot) (some (.D, .D)) :=
  OutcomeSpecA.nobudget_of (OutcomeAtA.of_evalGraph sf_EBot_vs_DefectBot)

/-- `sf_EBot_vs_EBot` -/
@[outcomeA]
theorem outcome_EBot_vs_EBot :
    OutcomeSpecA .nobudget (const EBot) (const EBot) (some (.C, .C)) :=
  OutcomeSpecA.nobudget_of (OutcomeAtA.of_evalGraph sf_EBot_vs_EBot)

/-- `sf_EBot_vs_MirrorBot` -/
@[outcomeA]
theorem outcome_EBot_vs_MirrorBot :
    OutcomeSpecA .nobudget (const EBot) (const MirrorBot) (some (.C, .C)) :=
  OutcomeSpecA.nobudget_of (OutcomeAtA.of_evalGraph sf_EBot_vs_MirrorBot)

/-- `sf_EBot_vs_OBot` -/
@[outcomeA]
theorem outcome_EBot_vs_OBot :
    OutcomeSpecA .nobudget (const EBot) (const OBot) (some (.C, .D)) :=
  OutcomeSpecA.nobudget_of (OutcomeAtA.of_evalGraph sf_EBot_vs_OBot)

/-- `sf_EBot_vs_TitForTatBot` -/
@[outcomeA]
theorem outcome_EBot_vs_TitForTatBot :
    OutcomeSpecA .nobudget (const EBot) (const TitForTatBot) (some (.C, .D)) :=
  OutcomeSpecA.nobudget_of (OutcomeAtA.of_evalGraph sf_EBot_vs_TitForTatBot)

end ArithS
