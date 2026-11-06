import ArithS.Outcome.Spec
import ArithS.Outcome.Attr
import ArithS.Cells.RedCellEngine
import ArithS.Cells.DimcidFlips
import ArithS.Cells.DimcidEngine
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
import ArithS.Cells.CupodTrollEngine
import ArithS.Necessitation.Package
import ArithS.Cells.Common.Templates
import ArithS.Cells.Common.Probers
import ArithS.Cells.Common.Families
import ArithS.Cells.Common.Khat
import ArithS.Assembly.Cell
import ArithS.Eval.SimTest

/-!
# ArithS.Outcome.Matrix.DIMCID — the `S'` cells with `DIMCID` on the left

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

/-- `loeb_DIMCID_vs_DBot` -/
@[outcomeA]
theorem outcome_DIMCID_vs_DBot :
    OutcomeSpecA .eventual (bot DIMCID) (const DBot) (some (.D, .C)) :=
  OutcomeSpecA.eventual_of (by
    obtain ⟨k₀, h⟩ := loeb_DIMCID_vs_DBot
    exact ⟨k₀, fun k hk ↦ OutcomeAtA.of_evalGraph (h k hk)⟩)

/-- `loeb_Dimcid_vs_Dimcid` -/
@[outcomeA]
theorem outcome_DIMCID_vs_DIMCID :
    OutcomeSpecA .eventual (bot DIMCID) (bot DIMCID) (some (.D, .D)) :=
  OutcomeSpecA.eventual_of (by
    obtain ⟨k₀, h⟩ := loeb_Dimcid_vs_Dimcid
    exact ⟨k₀, fun k hk ↦ by dsimp only [bot, const]; rw [progCode_DIMCID]; exact OutcomeAtA.of_evalGraph₂ (h k hk) (h k hk)⟩)

/-- `loeb_DIMCID_vs_EBot` -/
@[outcomeA]
theorem outcome_DIMCID_vs_EBot :
    OutcomeSpecA .eventual (bot DIMCID) (const EBot) (some (.D, .D)) :=
  OutcomeSpecA.eventual_of (by
    obtain ⟨k₀, h⟩ := loeb_DIMCID_vs_EBot
    exact ⟨k₀, fun k hk ↦ OutcomeAtA.of_evalGraph (h k hk)⟩)

/-- `loeb_Dimcid_vs_Mirror` -/
@[outcomeA]
theorem outcome_DIMCID_vs_MirrorBot :
    OutcomeSpecA .eventual (bot DIMCID) (const MirrorBot) (some (.D, .D)) :=
  OutcomeSpecA.eventual_of (by
    obtain ⟨k₀, h⟩ := loeb_Dimcid_vs_Mirror
    exact ⟨k₀, fun k hk ↦ by dsimp only [bot, const]; rw [progCode_DIMCID, progCode_MirrorBot]; exact OutcomeAtA.of_evalGraph (h k hk)⟩)

/-- `loeb_DIMCID_vs_OBot` -/
@[outcomeA]
theorem outcome_DIMCID_vs_OBot :
    OutcomeSpecA .eventual (bot DIMCID) (const OBot) (some (.D, .D)) :=
  OutcomeSpecA.eventual_of (by
    obtain ⟨k₀, h⟩ := loeb_DIMCID_vs_OBot
    exact ⟨k₀, fun k hk ↦ OutcomeAtA.of_evalGraph (h k hk)⟩)

/-- `loeb_DIMCID_vs_PrudentBot` -/
@[outcomeA]
theorem outcome_DIMCID_vs_PrudentBot :
    OutcomeSpecA .eventual (bot DIMCID) (bot PrudentBot) (some (.D, .D)) :=
  OutcomeSpecA.eventual_of (by
    obtain ⟨k₀, h⟩ := loeb_DIMCID_vs_PrudentBot
    exact ⟨k₀, fun k hk ↦ OutcomeAtA.of_evalGraph (h k hk)⟩)

/-- `loeb_DIMCID_vs_TitForTatBot` -/
@[outcomeA]
theorem outcome_DIMCID_vs_TitForTatBot :
    OutcomeSpecA .eventual (bot DIMCID) (const TitForTatBot) (some (.D, .D)) :=
  OutcomeSpecA.eventual_of (by
    obtain ⟨k₀, h⟩ := loeb_DIMCID_vs_TitForTatBot
    exact ⟨k₀, fun k hk ↦ OutcomeAtA.of_evalGraph (h k hk)⟩)

/-- `loeb_DIMCID_vs_CooperateBot` -/
@[outcomeA]
theorem outcome_DIMCID_vs_CooperateBot :
    OutcomeSpecA .eventual (bot DIMCID) (const CooperateBot) (some (.D, .C)) :=
  OutcomeSpecA.eventual_of (by
    obtain ⟨k₀, h⟩ := loeb_DIMCID_vs_CooperateBot
    exact ⟨k₀, fun k hk ↦ OutcomeAtA.of_evalGraph (h k hk)⟩)

/-- `pos_DIMCID_vs_DefectBot` -/
@[outcomeA]
theorem outcome_DIMCID_vs_DefectBot :
    OutcomeSpecA .eventual (bot DIMCID) (const DefectBot) (some (.D, .D)) :=
  OutcomeSpecA.eventual_of (by
    obtain ⟨k₀, h⟩ := pos_DIMCID_vs_DefectBot
    exact ⟨k₀, fun k hk ↦ OutcomeAtA.of_evalGraph (h k hk)⟩)

/-- `loeb_DIMCID_vs_DupocBot` — a FLIP: the engine has the UNIVERSAL `(C, D)` -/
@[outcomeA]
theorem outcome_DIMCID_vs_DupocBot :
    OutcomeSpecA .eventual (bot DIMCID) (bot DupocBot) (some (.D, .D)) :=
  OutcomeSpecA.eventual_of (by
    obtain ⟨k₀, h⟩ := loeb_DIMCID_vs_DupocBot
    exact ⟨k₀, fun k hk ↦ OutcomeAtA.of_evalGraph (h k hk)⟩)

/-- `loeb_DIMCID_vs_CupodBot` -/
@[outcomeA]
theorem outcome_DIMCID_vs_CupodBot :
    OutcomeSpecA .eventual (bot DIMCID) (bot CupodBot) (some (.D, .D)) :=
  OutcomeSpecA.eventual_of (by
    obtain ⟨k₀, h⟩ := loeb_DIMCID_vs_CupodBot
    exact ⟨k₀, fun k hk ↦ OutcomeAtA.of_evalGraph (h k hk)⟩)

/-! ### The two cells against the budget-snapshot bots, on the engine's own codes

`Cells/JustEngine.lean`, `Cells/CupodTrollEngine.lean` (2026-10-02): the engine's `JustBot k` and `CupodTrollBot k`
store constant templates since route (c) was made generic, so they are DESCRIBED opponents and
`dimcid_vs_described` applies to them directly; the hand-template twins `Just7 k`/`CupodTroll7 k` are retired
from the matrix. -/

/-- `loeb_DIMCID_vs_CupodTrollBot_engine` — FLIP: the engine has `(C, C)` -/
@[outcomeA]
theorem outcome_DIMCID_vs_CupodTrollBot :
    OutcomeSpecA .eventual (bot DIMCID) (bot CupodTrollBot) (some (.D, .C)) :=
  OutcomeSpecA.eventual_of (by
    obtain ⟨k₀, h⟩ := loeb_DIMCID_vs_CupodTrollBot_engine
    exact ⟨k₀, fun k hk ↦ OutcomeAtA.of_evalGraph (h k hk)⟩)

/-- `loeb_DIMCID_vs_JustBot_engine` — FLIP: the engine has `(C, D)` -/
@[outcomeA]
theorem outcome_DIMCID_vs_JustBot :
    OutcomeSpecA .eventual (bot DIMCID) (bot JustBot) (some (.D, .D)) :=
  OutcomeSpecA.eventual_of (by
    obtain ⟨k₀, h⟩ := loeb_DIMCID_vs_JustBot_engine
    exact ⟨k₀, fun k hk ↦ OutcomeAtA.of_evalGraph (h k hk)⟩)

end ArithS
