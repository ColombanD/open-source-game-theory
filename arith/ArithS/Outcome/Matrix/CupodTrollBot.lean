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
# ArithS.Outcome.Matrix.CupodTrollBot — the `S'` cells with `CupodTrollBot` on the left

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

/-- `snd_CupodTrollBot_vs_CooperateBot` -/
theorem outcome_CupodTrollBot_vs_CooperateBot :
    OutcomeSpecA .universal (bot CupodTrollBot) (const CooperateBot) (some (.C, .C)) :=
  OutcomeSpecA.universal_of fun k ↦ OutcomeAtA.of_evalGraph (snd_CupodTrollBot_vs_CooperateBot k)

/-! ### On the hand-template twins

* `CupodTroll7 k` (`Cells/KhatCells.lean`): CupodTrollBot with the constant budget-slot template; plays as
  `progCode (CupodTrollBot k)` in the program slot (`evalGraph_CupodTroll7_iff`), but as an OPPONENT its code
  (hence the partner's guard sentence) differs, so the cell stays on the twin.
-/

/-- `khat_CupodTrollBot_vs_CupodBot` (stated on the budget-slot twin `CupodTroll7 k`) -/
theorem outcome_CupodTroll7_vs_CupodBot :
    OutcomeSpecA .eventual CupodTroll7 (bot CupodBot) (some (.D, .D)) :=
  OutcomeSpecA.eventual_of (by
    obtain ⟨k₀, h⟩ := khat_CupodTrollBot_vs_CupodBot
    exact ⟨k₀, fun k hk ↦ OutcomeAtA.of_evalGraph (h k hk)⟩)

/-- `snd_CupodTrollBot_vs_CupodTrollBot` -/
theorem outcome_CupodTrollBot_vs_CupodTrollBot :
    OutcomeSpecA .universal (bot CupodTrollBot) (bot CupodTrollBot) (some (.C, .C)) :=
  OutcomeSpecA.universal_of fun k ↦ OutcomeAtA.of_evalGraph (snd_CupodTrollBot_vs_CupodTrollBot k)

/-- `snd_CupodTrollBot_vs_DBot` -/
theorem outcome_CupodTrollBot_vs_DBot :
    OutcomeSpecA .universal (bot CupodTrollBot) (const DBot) (some (.C, .D)) :=
  OutcomeSpecA.universal_of fun k ↦ OutcomeAtA.of_evalGraph (snd_CupodTrollBot_vs_DBot k)

/-- `snd_CupodTrollBot_vs_DefectBot` -/
theorem outcome_CupodTrollBot_vs_DefectBot :
    OutcomeSpecA .universal (bot CupodTrollBot) (const DefectBot) (some (.C, .D)) :=
  OutcomeSpecA.universal_of fun k ↦ OutcomeAtA.of_evalGraph (snd_CupodTrollBot_vs_DefectBot k)

/-- `snd_CupodTrollBot_vs_EBot` -/
theorem outcome_CupodTrollBot_vs_EBot :
    OutcomeSpecA .universal (bot CupodTrollBot) (const EBot) (some (.C, .D)) :=
  OutcomeSpecA.universal_of fun k ↦ OutcomeAtA.of_evalGraph (snd_CupodTrollBot_vs_EBot k)

/-- `snd_CupodTrollBot_vs_MirrorBot` -/
theorem outcome_CupodTrollBot_vs_MirrorBot :
    OutcomeSpecA .universal (bot CupodTrollBot) (const MirrorBot) (some (.C, .C)) :=
  OutcomeSpecA.universal_of fun k ↦ OutcomeAtA.of_evalGraph (snd_CupodTrollBot_vs_MirrorBot k)

/-- `snd_CupodTrollBot_vs_OBot` -/
theorem outcome_CupodTrollBot_vs_OBot :
    OutcomeSpecA .universal (bot CupodTrollBot) (const OBot) (some (.C, .C)) :=
  OutcomeSpecA.universal_of fun k ↦ OutcomeAtA.of_evalGraph (snd_CupodTrollBot_vs_OBot k)

/-- `snd_CupodTrollBot_vs_TitForTatBot` -/
theorem outcome_CupodTrollBot_vs_TitForTatBot :
    OutcomeSpecA .universal (bot CupodTrollBot) (const TitForTatBot) (some (.C, .C)) :=
  OutcomeSpecA.universal_of fun k ↦ OutcomeAtA.of_evalGraph (snd_CupodTrollBot_vs_TitForTatBot k)

end ArithS
