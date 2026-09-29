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
# ArithS.Outcome.Matrix.GuardianBot — the `S'` cells with `GuardianBot` on the left

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

/-- `snd_GuardianBot_vs_CupodBot` -/
theorem outcome_GuardianBot_vs_CupodBot :
    OutcomeSpecA .universal (bot GuardianBot) (bot CupodBot) (some (.C, .C)) :=
  OutcomeSpecA.universal_of fun k ↦ OutcomeAtA.of_evalGraph (snd_GuardianBot_vs_CupodBot k)

/-- `snd_GuardianBot_vs_CupodTrollBot` -/
theorem outcome_GuardianBot_vs_CupodTrollBot :
    OutcomeSpecA .universal (bot GuardianBot) (bot CupodTrollBot) (some (.C, .C)) :=
  OutcomeSpecA.universal_of fun k ↦ OutcomeAtA.of_evalGraph (snd_GuardianBot_vs_CupodTrollBot k)

/-- `pos_GuardianBot_vs_DBot` -/
theorem outcome_GuardianBot_vs_DBot :
    OutcomeSpecA .eventual (bot GuardianBot) (const DBot) (some (.D, .C)) :=
  OutcomeSpecA.eventual_of (by
    obtain ⟨k₀, h⟩ := pos_GuardianBot_vs_DBot
    exact ⟨k₀, fun k hk ↦ OutcomeAtA.of_evalGraph (h k hk)⟩)

/-- `loeb_GuardianBot_vs_DIMCID` -/
theorem outcome_GuardianBot_vs_DIMCID :
    OutcomeSpecA .eventual (bot GuardianBot) (bot DIMCID) (some (.D, .D)) :=
  OutcomeSpecA.eventual_of (by
    obtain ⟨k₀, h⟩ := loeb_GuardianBot_vs_DIMCID
    exact ⟨k₀, fun k hk ↦ OutcomeAtA.of_evalGraph (h k hk)⟩)

/-- `pos_GuardianBot_vs_EBot` -/
theorem outcome_GuardianBot_vs_EBot :
    OutcomeSpecA .eventual (bot GuardianBot) (const EBot) (some (.D, .C)) :=
  OutcomeSpecA.eventual_of (by
    obtain ⟨k₀, h⟩ := pos_GuardianBot_vs_EBot
    exact ⟨k₀, fun k hk ↦ OutcomeAtA.of_evalGraph (h k hk)⟩)

/-- `snd_GuardianBot_vs_GuardianBot` -/
theorem outcome_GuardianBot_vs_GuardianBot :
    OutcomeSpecA .universal (bot GuardianBot) (bot GuardianBot) (some (.C, .C)) :=
  OutcomeSpecA.universal_of fun k ↦ OutcomeAtA.of_evalGraph (snd_GuardianBot_vs_GuardianBot k)

/-- `pos_GuardianBot_vs_OBot` -/
theorem outcome_GuardianBot_vs_OBot :
    OutcomeSpecA .eventual (bot GuardianBot) (const OBot) (some (.C, .D)) :=
  OutcomeSpecA.eventual_of (by
    obtain ⟨k₀, h⟩ := pos_GuardianBot_vs_OBot
    exact ⟨k₀, fun k hk ↦ OutcomeAtA.of_evalGraph (h k hk)⟩)

/-- `snd_GuardianBot_vs_TitForTatBot` -/
theorem outcome_GuardianBot_vs_TitForTatBot :
    OutcomeSpecA .universal (bot GuardianBot) (const TitForTatBot) (some (.C, .C)) :=
  OutcomeSpecA.universal_of fun k ↦ OutcomeAtA.of_evalGraph (snd_GuardianBot_vs_TitForTatBot k)

/-- `snd_GuardianBot_vs_CooperateBot` -/
theorem outcome_GuardianBot_vs_CooperateBot :
    OutcomeSpecA .universal (bot GuardianBot) (const CooperateBot) (some (.C, .C)) :=
  OutcomeSpecA.universal_of fun k ↦ OutcomeAtA.of_evalGraph (snd_GuardianBot_vs_CooperateBot k)

/-- `pos_GuardianBot_vs_DefectBot` -/
theorem outcome_GuardianBot_vs_DefectBot :
    OutcomeSpecA .eventual (bot GuardianBot) (const DefectBot) (some (.D, .D)) :=
  OutcomeSpecA.eventual_of (by
    obtain ⟨k₀, h⟩ := pos_GuardianBot_vs_DefectBot
    exact ⟨k₀, fun k hk ↦ OutcomeAtA.of_evalGraph (h k hk)⟩)

/-- `snd_GuardianBot_vs_MirrorBot` -/
theorem outcome_GuardianBot_vs_MirrorBot :
    OutcomeSpecA .universal (bot GuardianBot) (const MirrorBot) (some (.C, .C)) :=
  OutcomeSpecA.universal_of fun k ↦ OutcomeAtA.of_evalGraph (snd_GuardianBot_vs_MirrorBot k)

end ArithS
