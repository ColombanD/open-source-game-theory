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
import ArithS.Cells.CimcicEngine
import ArithS.Cells.DIMCID
import ArithS.Cells.JustEngine
import ArithS.Necessitation.Package
import ArithS.Cells.Common.Templates
import ArithS.Cells.Common.Probers
import ArithS.Cells.Common.Families
import ArithS.Cells.Common.Khat
import ArithS.Assembly.Cell
import ArithS.Eval.SimTest

/-!
# ArithS.Outcome.Matrix.CIMCIC — the `S'` cells with `CIMCIC` on the left

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

/-- `pos_Cimcic_vs_Cimcic` -/
@[outcomeA]
theorem outcome_CIMCIC_vs_CIMCIC :
    OutcomeSpecA .eventual (bot CIMCIC) (bot CIMCIC) (some (.C, .C)) :=
  OutcomeSpecA.eventual_of (by
    obtain ⟨k₀, h⟩ := pos_Cimcic_vs_Cimcic
    exact ⟨k₀, fun k hk ↦ by dsimp only [bot, const]; rw [progCode_CIMCIC]; exact OutcomeAtA.of_evalGraph₂ (h k hk) (h k hk)⟩)

/-- `loeb_CIMCIC_vs_DIMCID` -/
@[outcomeA]
theorem outcome_CIMCIC_vs_DIMCID :
    OutcomeSpecA .eventual (bot CIMCIC) (bot DIMCID) (some (.D, .D)) :=
  OutcomeSpecA.eventual_of (by
    obtain ⟨k₀, h⟩ := loeb_CIMCIC_vs_DIMCID
    exact ⟨k₀, fun k hk ↦ OutcomeAtA.of_evalGraph (h k hk)⟩)

/-- `loeb_CIMCIC_vs_DupocBot` -/
@[outcomeA]
theorem outcome_CIMCIC_vs_DupocBot :
    OutcomeSpecA .eventual (bot CIMCIC) (bot DupocBot) (some (.C, .C)) :=
  OutcomeSpecA.eventual_of (by
    obtain ⟨k₀, h⟩ := loeb_CIMCIC_vs_DupocBot
    exact ⟨k₀, fun k hk ↦ OutcomeAtA.of_evalGraph (h k hk)⟩)

/-- `loeb_Cimcic_vs_Mirror` -/
@[outcomeA]
theorem outcome_CIMCIC_vs_MirrorBot :
    OutcomeSpecA .eventual (bot CIMCIC) (const MirrorBot) (some (.C, .C)) :=
  OutcomeSpecA.eventual_of (by
    obtain ⟨k₀, h⟩ := loeb_Cimcic_vs_Mirror
    exact ⟨k₀, fun k hk ↦ by dsimp only [bot, const]; rw [progCode_CIMCIC, progCode_MirrorBot]; exact OutcomeAtA.of_evalGraph (h k hk)⟩)

/-- `khat_CIMCIC_vs_TitForTatBot` -/
@[outcomeA]
theorem outcome_CIMCIC_vs_TitForTatBot :
    OutcomeSpecA .eventual (bot CIMCIC) (const TitForTatBot) (some (.C, .C)) :=
  OutcomeSpecA.eventual_of (by
    obtain ⟨k₀, h⟩ := khat_CIMCIC_vs_TitForTatBot
    exact ⟨k₀, fun k hk ↦ OutcomeAtA.of_evalGraph (h k hk)⟩)

/-- `pos_CIMCIC_vs_CooperateBot` -/
@[outcomeA]
theorem outcome_CIMCIC_vs_CooperateBot :
    OutcomeSpecA .eventual (bot CIMCIC) (const CooperateBot) (some (.C, .C)) :=
  OutcomeSpecA.eventual_of (by
    obtain ⟨k₀, h⟩ := pos_CIMCIC_vs_CooperateBot
    exact ⟨k₀, fun k hk ↦ OutcomeAtA.of_evalGraph (h k hk)⟩)

/-- `snd_CIMCIC_vs_DefectBot` -/
@[outcomeA]
theorem outcome_CIMCIC_vs_DefectBot :
    OutcomeSpecA .universal (bot CIMCIC) (const DefectBot) (some (.D, .D)) :=
  OutcomeSpecA.universal_of fun k ↦ OutcomeAtA.of_evalGraph (snd_CIMCIC_vs_DefectBot k)

/-- `snd_CIMCIC_vs_OBot` -/
@[outcomeA]
theorem outcome_CIMCIC_vs_OBot :
    OutcomeSpecA .eventual (bot CIMCIC) (const OBot) (some (.D, .D)) :=
  OutcomeSpecA.eventual_of (by
    obtain ⟨k₀, h⟩ := snd_CIMCIC_vs_OBot
    exact ⟨k₀, fun k hk ↦ OutcomeAtA.of_evalGraph (h k hk)⟩)

/-- `loeb_CIMCIC_vs_JustBot` (on the engine's own `JustBot`, `Cells/JustEngine.lean`, 2026-10-02; the hand-template
twin `Just7 k` is retired from the matrix) -/
@[outcomeA]
theorem outcome_CIMCIC_vs_JustBot :
    OutcomeSpecA .eventual (bot CIMCIC) (bot JustBot) (some (.C, .C)) :=
  OutcomeSpecA.eventual_of (by
    obtain ⟨k₀, h⟩ := loeb_CIMCIC_vs_JustBot
    exact ⟨k₀, fun k hk ↦ OutcomeAtA.of_evalGraph (h k hk)⟩)

end ArithS
