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
# ArithS.Outcome.Matrix.JustBot — the `S'` cells with `JustBot` on the left

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

/-- `pos_JustBot_vs_CooperateBot` -/
theorem outcome_JustBot_vs_CooperateBot :
    OutcomeSpecA .eventual (bot JustBot) (const CooperateBot) (some (.C, .C)) :=
  OutcomeSpecA.eventual_of (by
    obtain ⟨k₀, h⟩ := pos_JustBot_vs_CooperateBot
    exact ⟨k₀, fun k hk ↦ OutcomeAtA.of_evalGraph (h k hk)⟩)

/-- `snd_JustBot_vs_DefectBot` -/
theorem outcome_JustBot_vs_DefectBot :
    OutcomeSpecA .universal (bot JustBot) (const DefectBot) (some (.D, .D)) :=
  OutcomeSpecA.universal_of fun k ↦ OutcomeAtA.of_evalGraph (snd_JustBot_vs_DefectBot k)

/-- `snd_JustBot_vs_OBot` -/
theorem outcome_JustBot_vs_OBot :
    OutcomeSpecA .universal (bot JustBot) (const OBot) (some (.D, .D)) :=
  OutcomeSpecA.universal_of fun k ↦ OutcomeAtA.of_evalGraph (snd_JustBot_vs_OBot k)

/-- `khat_JustBot_vs_TitForTatBot` -/
theorem outcome_JustBot_vs_TitForTatBot :
    OutcomeSpecA .eventual (bot JustBot) (const TitForTatBot) (some (.C, .C)) :=
  OutcomeSpecA.eventual_of (by
    obtain ⟨k₀, h⟩ := khat_JustBot_vs_TitForTatBot
    exact ⟨k₀, fun k hk ↦ OutcomeAtA.of_evalGraph (h k hk)⟩)

/-! ### On the hand-template twins

These cells are stated on arith codes that are NOT the engine's `progCode`:
* `Just k` (`Cells/JustBot.lean`): JustBot on the hand template `guardTemplateJust k`.
* `Dupoc k` (`Cells/RedCell.lean`): the searcher on the HAND template `guardTemplate 0`; the engine's `DupocBot k` carries the translated template `template (.plays .opp .self .C)` — a different code with a provably equivalent guard (`Agents/Code.lean`, "Sanity"), on which the Löb cells are not yet re-proved.
* `Just7 k` (`Cells/JustSlot.lean`): JustBot with the CONSTANT budget-slot template (route (c)); plays as `Just k` at every fuel (`evalGraph_Just7_iff`).
-/

/-- `loeb_Just_vs_Mirror` -/
theorem outcome_Just_vs_MirrorBot :
    OutcomeSpecA .eventual Just (const MirrorBot) (some (.C, .C)) :=
  OutcomeSpecA.eventual_of (by
    obtain ⟨k₀, h⟩ := loeb_Just_vs_Mirror
    exact ⟨k₀, fun k hk ↦ by dsimp only [bot, const]; rw [progCode_MirrorBot]; exact OutcomeAtA.of_evalGraph (h k hk)⟩)

/-- `loeb_Just7_vs_Dupoc` -/
theorem outcome_Just7_vs_Dupoc :
    OutcomeSpecA .eventual Just7 Dupoc (some (.C, .C)) :=
  OutcomeSpecA.eventual_of (by
    obtain ⟨k₀, h⟩ := loeb_Just7_vs_Dupoc
    exact ⟨k₀, fun k hk ↦ OutcomeAtA.of_evalGraph (h k hk)⟩)

/-- `loeb_Just7_vs_Just7` -/
theorem outcome_Just7_vs_Just7 :
    OutcomeSpecA .eventual Just7 Just7 (some (.C, .C)) :=
  OutcomeSpecA.eventual_of (by
    obtain ⟨k₀, h⟩ := loeb_Just7_vs_Just7
    exact ⟨k₀, fun k hk ↦ OutcomeAtA.of_evalGraph₂ (h k hk) (h k hk)⟩)

end ArithS
