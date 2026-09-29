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
# ArithS.Outcome.Matrix.CupodBot — the `S'` cells with `CupodBot` on the left

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

/-- `snd_CupodBot_vs_CooperateBot` -/
theorem outcome_CupodBot_vs_CooperateBot :
    OutcomeSpecA .universal (bot CupodBot) (const CooperateBot) (some (.C, .C)) :=
  OutcomeSpecA.universal_of fun k ↦ OutcomeAtA.of_evalGraph (snd_CupodBot_vs_CooperateBot k)

/-- `pos_CupodBot_vs_DBot` -/
theorem outcome_CupodBot_vs_DBot :
    OutcomeSpecA .eventual (bot CupodBot) (const DBot) (some (.C, .C)) :=
  OutcomeSpecA.eventual_of (by
    obtain ⟨k₀, h⟩ := pos_CupodBot_vs_DBot
    exact ⟨k₀, fun k hk ↦ OutcomeAtA.of_evalGraph (h k hk)⟩)

/-- `pos_CupodBot_vs_DefectBot` -/
theorem outcome_CupodBot_vs_DefectBot :
    OutcomeSpecA .eventual (bot CupodBot) (const DefectBot) (some (.D, .D)) :=
  OutcomeSpecA.eventual_of (by
    obtain ⟨k₀, h⟩ := pos_CupodBot_vs_DefectBot
    exact ⟨k₀, fun k hk ↦ OutcomeAtA.of_evalGraph (h k hk)⟩)

/-- `pos_CupodBot_vs_EBot` -/
theorem outcome_CupodBot_vs_EBot :
    OutcomeSpecA .eventual (bot CupodBot) (const EBot) (some (.C, .C)) :=
  OutcomeSpecA.eventual_of (by
    obtain ⟨k₀, h⟩ := pos_CupodBot_vs_EBot
    exact ⟨k₀, fun k hk ↦ OutcomeAtA.of_evalGraph (h k hk)⟩)

/-- `snd_CupodBot_vs_TitForTatBot` -/
theorem outcome_CupodBot_vs_TitForTatBot :
    OutcomeSpecA .universal (bot CupodBot) (const TitForTatBot) (some (.C, .C)) :=
  OutcomeSpecA.universal_of fun k ↦ OutcomeAtA.of_evalGraph (snd_CupodBot_vs_TitForTatBot k)

/-! ### On the hand-template twins

These cells are stated on arith codes that are NOT the engine's `pcode`:
* `Cupod k`: τ of `Dupoc k` (same remark).
-/

/-- `loeb_Cupod_vs_Mirror` -/
theorem outcome_Cupod_vs_MirrorBot :
    OutcomeSpecA .eventual Cupod (const MirrorBot) (some (.D, .D)) :=
  OutcomeSpecA.eventual_of (by
    obtain ⟨k₀, h⟩ := loeb_Cupod_vs_Mirror
    exact ⟨k₀, fun k hk ↦ by dsimp only [bot, const]; rw [pcode_MirrorBot]; exact OutcomeAtA.of_evalGraph (h k hk)⟩)

/-- `dupoc_self_coop_unconditional` (`Necessitation/Package.lean`) -/
theorem outcome_Cupod_vs_Cupod :
    OutcomeSpecA .eventual Cupod Cupod (some (.D, .D)) :=
  OutcomeSpecA.eventual_of (by
    obtain ⟨k₀, h⟩ := dupoc_self_coop_unconditional
    exact ⟨k₀, fun k hk ↦ OutcomeAtA.of_evalGraph₂ (h k hk).2 (h k hk).2⟩)

end ArithS
