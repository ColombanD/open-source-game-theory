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
import ArithS.Cells.JustEngine
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
@[outcomeA]
theorem outcome_JustBot_vs_CooperateBot :
    OutcomeSpecA .eventual (bot JustBot) (const CooperateBot) (some (.C, .C)) :=
  OutcomeSpecA.eventual_of (by
    obtain ⟨k₀, h⟩ := pos_JustBot_vs_CooperateBot
    exact ⟨k₀, fun k hk ↦ OutcomeAtA.of_evalGraph (h k hk)⟩)

/-- `snd_JustBot_vs_DefectBot` -/
@[outcomeA]
theorem outcome_JustBot_vs_DefectBot :
    OutcomeSpecA .universal (bot JustBot) (const DefectBot) (some (.D, .D)) :=
  OutcomeSpecA.universal_of fun k ↦ OutcomeAtA.of_evalGraph (snd_JustBot_vs_DefectBot k)

/-- `snd_JustBot_vs_OBot` -/
@[outcomeA]
theorem outcome_JustBot_vs_OBot :
    OutcomeSpecA .universal (bot JustBot) (const OBot) (some (.D, .D)) :=
  OutcomeSpecA.universal_of fun k ↦ OutcomeAtA.of_evalGraph (snd_JustBot_vs_OBot k)

/-- `khat_JustBot_vs_TitForTatBot` -/
@[outcomeA]
theorem outcome_JustBot_vs_TitForTatBot :
    OutcomeSpecA .eventual (bot JustBot) (const TitForTatBot) (some (.C, .C)) :=
  OutcomeSpecA.eventual_of (by
    obtain ⟨k₀, h⟩ := khat_JustBot_vs_TitForTatBot
    exact ⟨k₀, fun k hk ↦ OutcomeAtA.of_evalGraph (h k hk)⟩)

/-! ### The Löb cells, on the engine's own `JustBot`

`Cells/JustEngine.lean` (2026-10-02): the engine's `progCode (JustBot k)` stores a CONSTANT template since route
(c) was made generic (`templateAt_phiJ`), so its Löb cells are re-run on it and the hand-template twins `Just k`
(`Cells/JustBot.lean`) and `Just7 k` (`Cells/JustSlot.lean`) are RETIRED from the matrix (their theorems stay in
`Cells/`, untagged). -/

/-- `loeb_JustBot_vs_MirrorBot` -/
@[outcomeA]
theorem outcome_JustBot_vs_MirrorBot :
    OutcomeSpecA .eventual (bot JustBot) (const MirrorBot) (some (.C, .C)) :=
  OutcomeSpecA.eventual_of (by
    obtain ⟨k₀, h⟩ := loeb_JustBot_vs_MirrorBot
    exact ⟨k₀, fun k hk ↦ OutcomeAtA.of_evalGraph (h k hk)⟩)

/-- `loeb_JustBot_vs_DupocBot` -/
@[outcomeA]
theorem outcome_JustBot_vs_DupocBot :
    OutcomeSpecA .eventual (bot JustBot) (bot DupocBot) (some (.C, .C)) :=
  OutcomeSpecA.eventual_of (by
    obtain ⟨k₀, h⟩ := loeb_JustBot_vs_DupocBot
    exact ⟨k₀, fun k hk ↦ OutcomeAtA.of_evalGraph (h k hk)⟩)

/-- `loeb_JustBot_vs_JustBot` -/
@[outcomeA]
theorem outcome_JustBot_vs_JustBot :
    OutcomeSpecA .eventual (bot JustBot) (bot JustBot) (some (.C, .C)) :=
  OutcomeSpecA.eventual_of (by
    obtain ⟨k₀, h⟩ := loeb_JustBot_vs_JustBot
    exact ⟨k₀, fun k hk ↦ OutcomeAtA.of_evalGraph₂ (h k hk) (h k hk)⟩)

end ArithS
