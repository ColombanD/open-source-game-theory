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
# ArithS.Outcome.Matrix.MirrorBot — the `S'` cells with `MirrorBot` on the left

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

/-- `sf_MirrorBot_vs_CooperateBot` -/
@[outcomeA]
theorem outcome_MirrorBot_vs_CooperateBot :
    OutcomeSpecA .nobudget (const MirrorBot) (const CooperateBot) (some (.C, .C)) :=
  OutcomeSpecA.nobudget_of (OutcomeAtA.of_evalGraph sf_MirrorBot_vs_CooperateBot)

/-- `sf_MirrorBot_vs_DBot` -/
@[outcomeA]
theorem outcome_MirrorBot_vs_DBot :
    OutcomeSpecA .nobudget (const MirrorBot) (const DBot) (some (.C, .C)) :=
  OutcomeSpecA.nobudget_of (OutcomeAtA.of_evalGraph sf_MirrorBot_vs_DBot)

/-- `sf_MirrorBot_vs_DefectBot` -/
@[outcomeA]
theorem outcome_MirrorBot_vs_DefectBot :
    OutcomeSpecA .nobudget (const MirrorBot) (const DefectBot) (some (.D, .D)) :=
  OutcomeSpecA.nobudget_of (OutcomeAtA.of_evalGraph sf_MirrorBot_vs_DefectBot)

/-- `sf_MirrorBot_vs_MirrorBot` -/
@[outcomeA]
theorem outcome_MirrorBot_vs_MirrorBot :
    OutcomeSpecA .nobudget (const MirrorBot) (const MirrorBot) (none) :=
  OutcomeSpecA.nobudget_of ⟨fun n a h ↦ sf_MirrorBot_vs_MirrorBot n a h, fun n a h ↦ sf_MirrorBot_vs_MirrorBot n a h⟩

/-- `sf_MirrorBot_vs_OBot` -/
@[outcomeA]
theorem outcome_MirrorBot_vs_OBot :
    OutcomeSpecA .nobudget (const MirrorBot) (const OBot) (some (.D, .D)) :=
  OutcomeSpecA.nobudget_of (OutcomeAtA.of_evalGraph sf_MirrorBot_vs_OBot)

/-- `sf_MirrorBot_vs_TitForTatBot` -/
@[outcomeA]
theorem outcome_MirrorBot_vs_TitForTatBot :
    OutcomeSpecA .nobudget (const MirrorBot) (const TitForTatBot) (some (.C, .C)) :=
  OutcomeSpecA.nobudget_of (OutcomeAtA.of_evalGraph sf_MirrorBot_vs_TitForTatBot)

end ArithS
