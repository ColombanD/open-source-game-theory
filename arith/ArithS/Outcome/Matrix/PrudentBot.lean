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
# ArithS.Outcome.Matrix.PrudentBot — the `S'` cells with `PrudentBot` on the left

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

/-- `snd_PrudentBot_vs_CooperateBot` -/
@[outcomeA]
theorem outcome_PrudentBot_vs_CooperateBot :
    OutcomeSpecA .universal (bot PrudentBot) (const CooperateBot) (some (.D, .C)) :=
  OutcomeSpecA.universal_of fun k ↦ OutcomeAtA.of_evalGraph (snd_PrudentBot_vs_CooperateBot k)

/-- `snd_PrudentBot_vs_CupodTrollBot` -/
@[outcomeA]
theorem outcome_PrudentBot_vs_CupodTrollBot :
    OutcomeSpecA .universal (bot PrudentBot) (bot CupodTrollBot) (some (.D, .C)) :=
  OutcomeSpecA.universal_of fun k ↦ OutcomeAtA.of_evalGraph (snd_PrudentBot_vs_CupodTrollBot k)

/-- `snd_PrudentBot_vs_DBot` -/
@[outcomeA]
theorem outcome_PrudentBot_vs_DBot :
    OutcomeSpecA .universal (bot PrudentBot) (const DBot) (some (.D, .C)) :=
  OutcomeSpecA.universal_of fun k ↦ OutcomeAtA.of_evalGraph (snd_PrudentBot_vs_DBot k)

/-- `snd_PrudentBot_vs_DefectBot` -/
@[outcomeA]
theorem outcome_PrudentBot_vs_DefectBot :
    OutcomeSpecA .universal (bot PrudentBot) (const DefectBot) (some (.D, .D)) :=
  OutcomeSpecA.universal_of fun k ↦ OutcomeAtA.of_evalGraph (snd_PrudentBot_vs_DefectBot k)

/-- `loeb_Prudent_vs_Mirror` -/
@[outcomeA]
theorem outcome_PrudentBot_vs_MirrorBot :
    OutcomeSpecA .eventual (bot PrudentBot) (const MirrorBot) (some (.C, .C)) :=
  OutcomeSpecA.eventual_of (by
    obtain ⟨k₀, h⟩ := loeb_Prudent_vs_Mirror
    exact ⟨k₀, fun k hk ↦ by dsimp only [bot, const]; rw [progCode_PrudentBot, progCode_MirrorBot]; exact OutcomeAtA.of_evalGraph (h k hk)⟩)

/-- `snd_PrudentBot_vs_OBot` -/
@[outcomeA]
theorem outcome_PrudentBot_vs_OBot :
    OutcomeSpecA .universal (bot PrudentBot) (const OBot) (some (.D, .D)) :=
  OutcomeSpecA.universal_of fun k ↦ OutcomeAtA.of_evalGraph (snd_PrudentBot_vs_OBot k)

/-- `snd_PrudentBot_vs_TitForTatBot` -/
@[outcomeA]
theorem outcome_PrudentBot_vs_TitForTatBot :
    OutcomeSpecA .universal (bot PrudentBot) (const TitForTatBot) (some (.D, .D)) :=
  OutcomeSpecA.universal_of fun k ↦ OutcomeAtA.of_evalGraph (snd_PrudentBot_vs_TitForTatBot k)

end ArithS
