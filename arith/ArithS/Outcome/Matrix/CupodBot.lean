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
import ArithS.Cells.DupocEngine
import ArithS.Necessitation.Package
import ArithS.Cells.Common.Templates
import ArithS.Cells.Common.Probers
import ArithS.Cells.Common.Families
import ArithS.Cells.Common.Khat
import ArithS.Assembly.Cell
import ArithS.Eval.SimTest

/-!
# ArithS.Outcome.Matrix.CupodBot — the `S'` cells with `CupodBot` on the left

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

/-- `snd_CupodBot_vs_CooperateBot` -/
@[outcomeA]
theorem outcome_CupodBot_vs_CooperateBot :
    OutcomeSpecA .universal (bot CupodBot) (const CooperateBot) (some (.C, .C)) :=
  OutcomeSpecA.universal_of fun k ↦ OutcomeAtA.of_evalGraph (snd_CupodBot_vs_CooperateBot k)

/-- `pos_CupodBot_vs_DBot` -/
@[outcomeA]
theorem outcome_CupodBot_vs_DBot :
    OutcomeSpecA .eventual (bot CupodBot) (const DBot) (some (.C, .C)) :=
  OutcomeSpecA.eventual_of (by
    obtain ⟨k₀, h⟩ := pos_CupodBot_vs_DBot
    exact ⟨k₀, fun k hk ↦ OutcomeAtA.of_evalGraph (h k hk)⟩)

/-- `pos_CupodBot_vs_DefectBot` -/
@[outcomeA]
theorem outcome_CupodBot_vs_DefectBot :
    OutcomeSpecA .eventual (bot CupodBot) (const DefectBot) (some (.D, .D)) :=
  OutcomeSpecA.eventual_of (by
    obtain ⟨k₀, h⟩ := pos_CupodBot_vs_DefectBot
    exact ⟨k₀, fun k hk ↦ OutcomeAtA.of_evalGraph (h k hk)⟩)

/-- `pos_CupodBot_vs_EBot` -/
@[outcomeA]
theorem outcome_CupodBot_vs_EBot :
    OutcomeSpecA .eventual (bot CupodBot) (const EBot) (some (.C, .C)) :=
  OutcomeSpecA.eventual_of (by
    obtain ⟨k₀, h⟩ := pos_CupodBot_vs_EBot
    exact ⟨k₀, fun k hk ↦ OutcomeAtA.of_evalGraph (h k hk)⟩)

/-- `snd_CupodBot_vs_TitForTatBot` -/
@[outcomeA]
theorem outcome_CupodBot_vs_TitForTatBot :
    OutcomeSpecA .universal (bot CupodBot) (const TitForTatBot) (some (.C, .C)) :=
  OutcomeSpecA.universal_of fun k ↦ OutcomeAtA.of_evalGraph (snd_CupodBot_vs_TitForTatBot k)

/-- `loeb_CupodBot_vs_MirrorBot` (`Cells/DupocEngine.lean`; the hand-template version is `loeb_Cupod_vs_Mirror`) -/
@[outcomeA]
theorem outcome_CupodBot_vs_MirrorBot :
    OutcomeSpecA .eventual (bot CupodBot) (const MirrorBot) (some (.D, .D)) :=
  OutcomeSpecA.eventual_of (by
    obtain ⟨k₀, h⟩ := loeb_CupodBot_vs_MirrorBot
    exact ⟨k₀, fun k hk ↦ OutcomeAtA.of_evalGraph (h k hk)⟩)

/-- `loeb_CupodBot_vs_CupodBot` (`Cells/DupocEngine.lean`; the hand-template version is `dupoc_self_coop`, `Necessitation/Package.lean`) -/
@[outcomeA]
theorem outcome_CupodBot_vs_CupodBot :
    OutcomeSpecA .eventual (bot CupodBot) (bot CupodBot) (some (.D, .D)) :=
  OutcomeSpecA.eventual_of (by
    obtain ⟨k₀, h⟩ := loeb_CupodBot_vs_CupodBot
    exact ⟨k₀, fun k hk ↦ OutcomeAtA.of_evalGraph₂ (h k hk) (h k hk)⟩)

end ArithS
