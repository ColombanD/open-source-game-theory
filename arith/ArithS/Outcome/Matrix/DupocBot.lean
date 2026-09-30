import ArithS.Outcome.Spec
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
theorem outcome_DupocBot_vs_CooperateBot :
    OutcomeSpecA .eventual (bot DupocBot) (const CooperateBot) (some (.C, .C)) :=
  OutcomeSpecA.eventual_of (by
    obtain ⟨k₀, h⟩ := pos_DupocBot_vs_CooperateBot
    exact ⟨k₀, fun k hk ↦ OutcomeAtA.of_evalGraph (h k hk)⟩)

/-- `snd_DupocBot_vs_DefectBot` -/
theorem outcome_DupocBot_vs_DefectBot :
    OutcomeSpecA .universal (bot DupocBot) (const DefectBot) (some (.D, .D)) :=
  OutcomeSpecA.universal_of fun k ↦ OutcomeAtA.of_evalGraph (snd_DupocBot_vs_DefectBot k)

/-- `snd_DupocBot_vs_OBot` -/
theorem outcome_DupocBot_vs_OBot :
    OutcomeSpecA .universal (bot DupocBot) (const OBot) (some (.D, .D)) :=
  OutcomeSpecA.universal_of fun k ↦ OutcomeAtA.of_evalGraph (snd_DupocBot_vs_OBot k)

/-- `khat_DupocBot_vs_TitForTatBot` -/
theorem outcome_DupocBot_vs_TitForTatBot :
    OutcomeSpecA .eventual (bot DupocBot) (const TitForTatBot) (some (.C, .C)) :=
  OutcomeSpecA.eventual_of (by
    obtain ⟨k₀, h⟩ := khat_DupocBot_vs_TitForTatBot
    exact ⟨k₀, fun k hk ↦ OutcomeAtA.of_evalGraph (h k hk)⟩)

/-- `snd_DupocBot_vs_CupodBot` (`Cells/RedCellEngine.lean`; the hand-template version is `red_cell`) -/
theorem outcome_DupocBot_vs_CupodBot :
    OutcomeSpecA .universal (bot DupocBot) (bot CupodBot) (some (.D, .C)) :=
  OutcomeSpecA.universal_of fun k ↦ OutcomeAtA.of_evalGraph (snd_DupocBot_vs_CupodBot k)

/-! ### On the hand-template twins

These cells are stated on arith codes that are NOT the engine's `progCode`:
* `Dupoc k` (`Cells/RedCell.lean`): the searcher on the HAND template `guardTemplate 0`; the engine's `DupocBot k` carries the translated template `template (.plays .opp .self .C)` — a different code with a provably equivalent guard (`Agents/Code.lean`, "Sanity"), on which the Löb cells are not yet re-proved.
-/

/-- `loeb_Dupoc_vs_Mirror` -/
theorem outcome_Dupoc_vs_MirrorBot :
    OutcomeSpecA .eventual Dupoc (const MirrorBot) (some (.C, .C)) :=
  OutcomeSpecA.eventual_of (by
    obtain ⟨k₀, h⟩ := loeb_Dupoc_vs_Mirror
    exact ⟨k₀, fun k hk ↦ by dsimp only [bot, const]; rw [progCode_MirrorBot]; exact OutcomeAtA.of_evalGraph (h k hk)⟩)

/-- `dupoc_self_coop` (`Necessitation/Package.lean`) -/
theorem outcome_Dupoc_vs_Dupoc :
    OutcomeSpecA .eventual Dupoc Dupoc (some (.C, .C)) :=
  OutcomeSpecA.eventual_of (by
    obtain ⟨k₀, h⟩ := dupoc_self_coop
    exact ⟨k₀, fun k hk ↦ OutcomeAtA.of_evalGraph₂ (h k hk).1 (h k hk).1⟩)

end ArithS
