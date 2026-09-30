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
import ArithS.Cells.DupocEngine
import ArithS.Cells.JustBot
import ArithS.Necessitation.Package

/-!
# ArithS.Outcome.Matrix.DupocBot — the `S'` cells with `DupocBot` on the left

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

/-- `pos_DupocBot_vs_CooperateBot` -/
@[outcomeA]
theorem outcome_DupocBot_vs_CooperateBot :
    OutcomeSpecA .eventual (bot DupocBot) (const CooperateBot) (some (.C, .C)) :=
  OutcomeSpecA.eventual_of (by
    obtain ⟨k₀, h⟩ := pos_DupocBot_vs_CooperateBot
    exact ⟨k₀, fun k hk ↦ OutcomeAtA.of_evalGraph (h k hk)⟩)

/-- `snd_DupocBot_vs_DefectBot` -/
@[outcomeA]
theorem outcome_DupocBot_vs_DefectBot :
    OutcomeSpecA .universal (bot DupocBot) (const DefectBot) (some (.D, .D)) :=
  OutcomeSpecA.universal_of fun k ↦ OutcomeAtA.of_evalGraph (snd_DupocBot_vs_DefectBot k)

/-- `snd_DupocBot_vs_OBot` -/
@[outcomeA]
theorem outcome_DupocBot_vs_OBot :
    OutcomeSpecA .universal (bot DupocBot) (const OBot) (some (.D, .D)) :=
  OutcomeSpecA.universal_of fun k ↦ OutcomeAtA.of_evalGraph (snd_DupocBot_vs_OBot k)

/-- `khat_DupocBot_vs_TitForTatBot` -/
@[outcomeA]
theorem outcome_DupocBot_vs_TitForTatBot :
    OutcomeSpecA .eventual (bot DupocBot) (const TitForTatBot) (some (.C, .C)) :=
  OutcomeSpecA.eventual_of (by
    obtain ⟨k₀, h⟩ := khat_DupocBot_vs_TitForTatBot
    exact ⟨k₀, fun k hk ↦ OutcomeAtA.of_evalGraph (h k hk)⟩)

/-- `snd_DupocBot_vs_CupodBot` (`Cells/RedCellEngine.lean`; the hand-template version is `red_cell`) -/
@[outcomeA]
theorem outcome_DupocBot_vs_CupodBot :
    OutcomeSpecA .universal (bot DupocBot) (bot CupodBot) (some (.D, .C)) :=
  OutcomeSpecA.universal_of fun k ↦ OutcomeAtA.of_evalGraph (snd_DupocBot_vs_CupodBot k)

/-- `loeb_DupocBot_vs_MirrorBot` (`Cells/DupocEngine.lean`; the hand-template version is `loeb_Dupoc_vs_Mirror`) -/
@[outcomeA]
theorem outcome_DupocBot_vs_MirrorBot :
    OutcomeSpecA .eventual (bot DupocBot) (const MirrorBot) (some (.C, .C)) :=
  OutcomeSpecA.eventual_of (by
    obtain ⟨k₀, h⟩ := loeb_DupocBot_vs_MirrorBot
    exact ⟨k₀, fun k hk ↦ OutcomeAtA.of_evalGraph (h k hk)⟩)

/-- `loeb_DupocBot_vs_DupocBot` (`Cells/DupocEngine.lean`; the hand-template version is `dupoc_self_coop`, `Necessitation/Package.lean`) -/
@[outcomeA]
theorem outcome_DupocBot_vs_DupocBot :
    OutcomeSpecA .eventual (bot DupocBot) (bot DupocBot) (some (.C, .C)) :=
  OutcomeSpecA.eventual_of (by
    obtain ⟨k₀, h⟩ := loeb_DupocBot_vs_DupocBot
    exact ⟨k₀, fun k hk ↦ OutcomeAtA.of_evalGraph₂ (h k hk) (h k hk)⟩)

end ArithS
