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
# ArithS.Outcome.Matrix.WaryBot — the `S'` cells with `WaryBot` on the left

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

/-- `snd_WaryBot_vs_GuardianBot` -/
@[outcomeA]
theorem outcome_WaryBot_vs_GuardianBot :
    OutcomeSpecA .universal (bot WaryBot) (bot GuardianBot) (some (.C, .C)) :=
  OutcomeSpecA.universal_of fun k ↦ OutcomeAtA.of_evalGraph (snd_WaryBot_vs_GuardianBot k)

/-- `snd_WaryBot_vs_CooperateBot` -/
@[outcomeA]
theorem outcome_WaryBot_vs_CooperateBot :
    OutcomeSpecA .universal (bot WaryBot) (const CooperateBot) (some (.C, .C)) :=
  OutcomeSpecA.universal_of fun k ↦ OutcomeAtA.of_evalGraph (snd_WaryBot_vs_CooperateBot k)

/-- `snd_WaryBot_vs_CupodTrollBot` -/
@[outcomeA]
theorem outcome_WaryBot_vs_CupodTrollBot :
    OutcomeSpecA .universal (bot WaryBot) (bot CupodTrollBot) (some (.C, .C)) :=
  OutcomeSpecA.universal_of fun k ↦ OutcomeAtA.of_evalGraph (snd_WaryBot_vs_CupodTrollBot k)

/-- `pos_WaryBot_vs_DBot` -/
@[outcomeA]
theorem outcome_WaryBot_vs_DBot :
    OutcomeSpecA .eventual (bot WaryBot) (const DBot) (some (.C, .C)) :=
  OutcomeSpecA.eventual_of (by
    obtain ⟨k₀, h⟩ := pos_WaryBot_vs_DBot
    exact ⟨k₀, fun k hk ↦ OutcomeAtA.of_evalGraph (h k hk)⟩)

/-- `pos_WaryBot_vs_DefectBot` -/
@[outcomeA]
theorem outcome_WaryBot_vs_DefectBot :
    OutcomeSpecA .eventual (bot WaryBot) (const DefectBot) (some (.D, .D)) :=
  OutcomeSpecA.eventual_of (by
    obtain ⟨k₀, h⟩ := pos_WaryBot_vs_DefectBot
    exact ⟨k₀, fun k hk ↦ OutcomeAtA.of_evalGraph (h k hk)⟩)

/-- `pos_WaryBot_vs_EBot` -/
@[outcomeA]
theorem outcome_WaryBot_vs_EBot :
    OutcomeSpecA .eventual (bot WaryBot) (const EBot) (some (.C, .C)) :=
  OutcomeSpecA.eventual_of (by
    obtain ⟨k₀, h⟩ := pos_WaryBot_vs_EBot
    exact ⟨k₀, fun k hk ↦ OutcomeAtA.of_evalGraph (h k hk)⟩)

/-- `loeb_WaryBot_vs_MirrorBot` -/
@[outcomeA]
theorem outcome_WaryBot_vs_MirrorBot :
    OutcomeSpecA .eventual (bot WaryBot) (const MirrorBot) (some (.D, .D)) :=
  OutcomeSpecA.eventual_of (by
    obtain ⟨k₀, h⟩ := loeb_WaryBot_vs_MirrorBot
    exact ⟨k₀, fun k hk ↦ OutcomeAtA.of_evalGraph (h k hk)⟩)

/-- `snd_WaryBot_vs_TitForTatBot` -/
@[outcomeA]
theorem outcome_WaryBot_vs_TitForTatBot :
    OutcomeSpecA .universal (bot WaryBot) (const TitForTatBot) (some (.C, .C)) :=
  OutcomeSpecA.universal_of fun k ↦ OutcomeAtA.of_evalGraph (snd_WaryBot_vs_TitForTatBot k)

/-- `loeb_WaryBot_vs_WaryBot` -/
@[outcomeA]
theorem outcome_WaryBot_vs_WaryBot :
    OutcomeSpecA .eventual (bot WaryBot) (bot WaryBot) (some (.D, .D)) :=
  OutcomeSpecA.eventual_of (by
    obtain ⟨k₀, h⟩ := loeb_WaryBot_vs_WaryBot
    exact ⟨k₀, fun k hk ↦ OutcomeAtA.of_evalGraph (h k hk)⟩)

end ArithS
