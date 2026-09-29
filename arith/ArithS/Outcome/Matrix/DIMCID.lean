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
# ArithS.Outcome.Matrix.DIMCID — the `S'` cells with `DIMCID` on the left

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

/-- `loeb_DIMCID_vs_DBot` -/
theorem outcome_DIMCID_vs_DBot :
    OutcomeSpecA .eventual (bot DIMCID) (const DBot) (some (.D, .C)) :=
  OutcomeSpecA.eventual_of (by
    obtain ⟨k₀, h⟩ := loeb_DIMCID_vs_DBot
    exact ⟨k₀, fun k hk ↦ OutcomeAtA.of_evalGraph (h k hk)⟩)

/-- `loeb_Dimcid_vs_Dimcid` -/
theorem outcome_DIMCID_vs_DIMCID :
    OutcomeSpecA .eventual (bot DIMCID) (bot DIMCID) (some (.D, .D)) :=
  OutcomeSpecA.eventual_of (by
    obtain ⟨k₀, h⟩ := loeb_Dimcid_vs_Dimcid
    exact ⟨k₀, fun k hk ↦ by dsimp only [bot, const]; rw [pcode_DIMCID]; exact OutcomeAtA.of_evalGraph₂ (h k hk) (h k hk)⟩)

/-- `loeb_DIMCID_vs_EBot` -/
theorem outcome_DIMCID_vs_EBot :
    OutcomeSpecA .eventual (bot DIMCID) (const EBot) (some (.D, .D)) :=
  OutcomeSpecA.eventual_of (by
    obtain ⟨k₀, h⟩ := loeb_DIMCID_vs_EBot
    exact ⟨k₀, fun k hk ↦ OutcomeAtA.of_evalGraph (h k hk)⟩)

/-- `loeb_Dimcid_vs_Mirror` -/
theorem outcome_DIMCID_vs_MirrorBot :
    OutcomeSpecA .eventual (bot DIMCID) (const MirrorBot) (some (.D, .D)) :=
  OutcomeSpecA.eventual_of (by
    obtain ⟨k₀, h⟩ := loeb_Dimcid_vs_Mirror
    exact ⟨k₀, fun k hk ↦ by dsimp only [bot, const]; rw [pcode_DIMCID, pcode_MirrorBot]; exact OutcomeAtA.of_evalGraph (h k hk)⟩)

/-- `loeb_DIMCID_vs_OBot` -/
theorem outcome_DIMCID_vs_OBot :
    OutcomeSpecA .eventual (bot DIMCID) (const OBot) (some (.D, .D)) :=
  OutcomeSpecA.eventual_of (by
    obtain ⟨k₀, h⟩ := loeb_DIMCID_vs_OBot
    exact ⟨k₀, fun k hk ↦ OutcomeAtA.of_evalGraph (h k hk)⟩)

/-- `loeb_DIMCID_vs_PrudentBot` -/
theorem outcome_DIMCID_vs_PrudentBot :
    OutcomeSpecA .eventual (bot DIMCID) (bot PrudentBot) (some (.D, .D)) :=
  OutcomeSpecA.eventual_of (by
    obtain ⟨k₀, h⟩ := loeb_DIMCID_vs_PrudentBot
    exact ⟨k₀, fun k hk ↦ OutcomeAtA.of_evalGraph (h k hk)⟩)

/-- `loeb_DIMCID_vs_TitForTatBot` -/
theorem outcome_DIMCID_vs_TitForTatBot :
    OutcomeSpecA .eventual (bot DIMCID) (const TitForTatBot) (some (.D, .D)) :=
  OutcomeSpecA.eventual_of (by
    obtain ⟨k₀, h⟩ := loeb_DIMCID_vs_TitForTatBot
    exact ⟨k₀, fun k hk ↦ OutcomeAtA.of_evalGraph (h k hk)⟩)

/-- `loeb_DIMCID_vs_CooperateBot` -/
theorem outcome_DIMCID_vs_CooperateBot :
    OutcomeSpecA .eventual (bot DIMCID) (const CooperateBot) (some (.D, .C)) :=
  OutcomeSpecA.eventual_of (by
    obtain ⟨k₀, h⟩ := loeb_DIMCID_vs_CooperateBot
    exact ⟨k₀, fun k hk ↦ OutcomeAtA.of_evalGraph (h k hk)⟩)

/-- `pos_DIMCID_vs_DefectBot` -/
theorem outcome_DIMCID_vs_DefectBot :
    OutcomeSpecA .eventual (bot DIMCID) (const DefectBot) (some (.D, .D)) :=
  OutcomeSpecA.eventual_of (by
    obtain ⟨k₀, h⟩ := pos_DIMCID_vs_DefectBot
    exact ⟨k₀, fun k hk ↦ OutcomeAtA.of_evalGraph (h k hk)⟩)

/-- `loeb_DIMCID_vs_DupocBot` — a FLIP: the engine has the UNIVERSAL `(C, D)` -/
theorem outcome_DIMCID_vs_DupocBot :
    OutcomeSpecA .eventual (bot DIMCID) (bot DupocBot) (some (.D, .D)) :=
  OutcomeSpecA.eventual_of (by
    obtain ⟨k₀, h⟩ := loeb_DIMCID_vs_DupocBot
    exact ⟨k₀, fun k hk ↦ OutcomeAtA.of_evalGraph (h k hk)⟩)

/-! ### On the hand-template twins

These cells are stated on arith codes that are NOT the engine's `pcode`:
* `Cupod k`: τ of `Dupoc k` (same remark).
* `CupodTroll7 k` (`Cells/KhatCells.lean`): CupodTrollBot with the constant budget-slot template; plays as `pcode (CupodTrollBot k)` in the program slot (`evalGraph_CupodTroll7_iff`), but as an OPPONENT its code (hence the partner's guard sentence) differs.
* `Just7 k` (`Cells/JustSlot.lean`): JustBot with the CONSTANT budget-slot template (route (c)); plays as `Just k` at every fuel (`evalGraph_Just7_iff`).
-/

/-- `loeb_Dimcid_vs_Cupod` -/
theorem outcome_DIMCID_vs_Cupod :
    OutcomeSpecA .eventual (bot DIMCID) Cupod (some (.D, .D)) :=
  OutcomeSpecA.eventual_of (by
    obtain ⟨k₀, h⟩ := loeb_Dimcid_vs_Cupod
    exact ⟨k₀, fun k hk ↦ by dsimp only [bot, const]; rw [pcode_DIMCID]; exact OutcomeAtA.of_evalGraph (h k hk)⟩)

/-- `loeb_DIMCID_vs_CupodTrollBot` (stated on the budget-slot twin `CupodTroll7 k`) -/
theorem outcome_DIMCID_vs_CupodTroll7 :
    OutcomeSpecA .eventual (bot DIMCID) CupodTroll7 (some (.D, .C)) :=
  OutcomeSpecA.eventual_of (by
    obtain ⟨k₀, h⟩ := loeb_DIMCID_vs_CupodTrollBot
    exact ⟨k₀, fun k hk ↦ OutcomeAtA.of_evalGraph (h k hk)⟩)

/-- `loeb_DIMCID_vs_JustBot` (stated on the budget-slot twin `Just7 k`) -/
theorem outcome_DIMCID_vs_Just7 :
    OutcomeSpecA .eventual (bot DIMCID) Just7 (some (.D, .D)) :=
  OutcomeSpecA.eventual_of (by
    obtain ⟨k₀, h⟩ := loeb_DIMCID_vs_JustBot
    exact ⟨k₀, fun k hk ↦ OutcomeAtA.of_evalGraph (h k hk)⟩)

end ArithS
