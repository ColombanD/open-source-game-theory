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
import ArithS.Cells.CupodTrollEngine
import ArithS.Necessitation.Package
import ArithS.Cells.Common.Templates
import ArithS.Cells.Common.Probers
import ArithS.Cells.Common.Families
import ArithS.Cells.Common.Khat
import ArithS.Assembly.Cell
import ArithS.Eval.SimTest

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
@[outcomeA]
theorem outcome_CupodTrollBot_vs_CooperateBot :
    OutcomeSpecA .universal (bot CupodTrollBot) (const CooperateBot) (some (.C, .C)) :=
  OutcomeSpecA.universal_of fun k ↦ OutcomeAtA.of_evalGraph (snd_CupodTrollBot_vs_CooperateBot k)

/-- `khat_CupodBot_vs_CupodTrollBot` (the pair in the other orientation, on the engine's own codes —
`Cells/CupodTrollEngine.lean`, 2026-10-02: the engine's `progCode (CupodTrollBot k)` stores a constant template
since route (c) was made generic, `templateAt_phiT`, so Cupod's guard describes it and the hand-template twin
`CupodTroll7 k` of `Cells/KhatCells.lean` is RETIRED from the matrix; CupodTroll's half is
`khat_CupodTrollBot_vs_CupodBot_engine`) -/
@[outcomeA]
theorem outcome_CupodTrollBot_vs_CupodBot :
    OutcomeSpecA .eventual (bot CupodTrollBot) (bot CupodBot) (some (.D, .D)) :=
  OutcomeSpecA.eventual_of (by
    obtain ⟨k₀, h⟩ := khat_CupodBot_vs_CupodTrollBot
    exact ⟨k₀, fun k hk ↦ OutcomeAtA.of_evalGraph₂ (h k hk).2 (h k hk).1⟩)

/-- `snd_CupodTrollBot_vs_CupodTrollBot` -/
@[outcomeA]
theorem outcome_CupodTrollBot_vs_CupodTrollBot :
    OutcomeSpecA .universal (bot CupodTrollBot) (bot CupodTrollBot) (some (.C, .C)) :=
  OutcomeSpecA.universal_of fun k ↦ OutcomeAtA.of_evalGraph (snd_CupodTrollBot_vs_CupodTrollBot k)

/-- `snd_CupodTrollBot_vs_DBot` -/
@[outcomeA]
theorem outcome_CupodTrollBot_vs_DBot :
    OutcomeSpecA .universal (bot CupodTrollBot) (const DBot) (some (.C, .D)) :=
  OutcomeSpecA.universal_of fun k ↦ OutcomeAtA.of_evalGraph (snd_CupodTrollBot_vs_DBot k)

/-- `snd_CupodTrollBot_vs_DefectBot` -/
@[outcomeA]
theorem outcome_CupodTrollBot_vs_DefectBot :
    OutcomeSpecA .universal (bot CupodTrollBot) (const DefectBot) (some (.C, .D)) :=
  OutcomeSpecA.universal_of fun k ↦ OutcomeAtA.of_evalGraph (snd_CupodTrollBot_vs_DefectBot k)

/-- `snd_CupodTrollBot_vs_EBot` -/
@[outcomeA]
theorem outcome_CupodTrollBot_vs_EBot :
    OutcomeSpecA .universal (bot CupodTrollBot) (const EBot) (some (.C, .D)) :=
  OutcomeSpecA.universal_of fun k ↦ OutcomeAtA.of_evalGraph (snd_CupodTrollBot_vs_EBot k)

/-- `snd_CupodTrollBot_vs_MirrorBot` -/
@[outcomeA]
theorem outcome_CupodTrollBot_vs_MirrorBot :
    OutcomeSpecA .universal (bot CupodTrollBot) (const MirrorBot) (some (.C, .C)) :=
  OutcomeSpecA.universal_of fun k ↦ OutcomeAtA.of_evalGraph (snd_CupodTrollBot_vs_MirrorBot k)

/-- `snd_CupodTrollBot_vs_OBot` -/
@[outcomeA]
theorem outcome_CupodTrollBot_vs_OBot :
    OutcomeSpecA .universal (bot CupodTrollBot) (const OBot) (some (.C, .C)) :=
  OutcomeSpecA.universal_of fun k ↦ OutcomeAtA.of_evalGraph (snd_CupodTrollBot_vs_OBot k)

/-- `snd_CupodTrollBot_vs_TitForTatBot` -/
@[outcomeA]
theorem outcome_CupodTrollBot_vs_TitForTatBot :
    OutcomeSpecA .universal (bot CupodTrollBot) (const TitForTatBot) (some (.C, .C)) :=
  OutcomeSpecA.universal_of fun k ↦ OutcomeAtA.of_evalGraph (snd_CupodTrollBot_vs_TitForTatBot k)

end ArithS
