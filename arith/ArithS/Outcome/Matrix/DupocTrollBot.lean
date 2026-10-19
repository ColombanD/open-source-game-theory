import ArithS.Outcome.Spec
import ArithS.Outcome.Attr
import ArithS.Cells.DupocTrollBot
import ArithS.Cells.DimdidTroll
import ArithS.Cells.DupocTrollPrudent

/-!
# ArithS.Outcome.Matrix.DupocTrollBot — the `S'` cells with `DupocTrollBot` on the left

`DupocTrollBot k` ("defect iff the opponent IS `DupocBot k`", 2026-10-13) has NO engine cell: these fourteen cells (twelve of 2026-10-13, the DIMDID pair of the same day, the PrudentBot pair of 2026-10-19) and
the floor `outcome_DupocTrollBot_vs_CIMCIC_floor` (`Outcome/Floors.lean`) are `S'`-only results
(`Research/Notes/ROUTE_B_CENSUS.md`, "S'-only cells"). Each is the engine's statement (`OutcomeSpecA`,
`Outcome/Spec.lean`) proved from the method-named theorem of `Cells/DupocTrollBot.lean` named in its docstring.
-/

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus
open LAct
open PD.Bots

/-- `snd_DupocTrollBot_vs_CooperateBot` -/
@[outcomeA]
theorem outcome_DupocTrollBot_vs_CooperateBot :
    OutcomeSpecA .universal (bot DupocTrollBot) (const CooperateBot) (some (.C, .C)) :=
  OutcomeSpecA.universal_of fun k ↦ OutcomeAtA.of_evalGraph (snd_DupocTrollBot_vs_CooperateBot k)

/-- `snd_DupocTrollBot_vs_CupodBot` -/
@[outcomeA]
theorem outcome_DupocTrollBot_vs_CupodBot :
    OutcomeSpecA .universal (bot DupocTrollBot) (bot CupodBot) (some (.C, .C)) :=
  OutcomeSpecA.universal_of fun k ↦ OutcomeAtA.of_evalGraph (snd_DupocTrollBot_vs_CupodBot k)

/-- `snd_DupocTrollBot_vs_CupodTrollBot` -/
@[outcomeA]
theorem outcome_DupocTrollBot_vs_CupodTrollBot :
    OutcomeSpecA .universal (bot DupocTrollBot) (bot CupodTrollBot) (some (.C, .C)) :=
  OutcomeSpecA.universal_of fun k ↦ OutcomeAtA.of_evalGraph (snd_DupocTrollBot_vs_CupodTrollBot k)

/-- `snd_DupocTrollBot_vs_DBot` -/
@[outcomeA]
theorem outcome_DupocTrollBot_vs_DBot :
    OutcomeSpecA .universal (bot DupocTrollBot) (const DBot) (some (.C, .D)) :=
  OutcomeSpecA.universal_of fun k ↦ OutcomeAtA.of_evalGraph (snd_DupocTrollBot_vs_DBot k)

/-- `loeb_DupocTrollBot_vs_DIMCID` (DIMCID's self-fulfilling guard against the described troll; the troll's
`.eq` guard is false at every `k`) -/
@[outcomeA]
theorem outcome_DupocTrollBot_vs_DIMCID :
    OutcomeSpecA .eventual (bot DupocTrollBot) (bot DIMCID) (some (.C, .D)) :=
  OutcomeSpecA.eventual_of (by
    obtain ⟨k₀, h⟩ := loeb_DupocTrollBot_vs_DIMCID
    exact ⟨k₀, fun k hk ↦ OutcomeAtA.of_evalGraph (h k hk)⟩)

/-- `snd_DupocTrollBot_vs_DefectBot` -/
@[outcomeA]
theorem outcome_DupocTrollBot_vs_DefectBot :
    OutcomeSpecA .universal (bot DupocTrollBot) (const DefectBot) (some (.C, .D)) :=
  OutcomeSpecA.universal_of fun k ↦ OutcomeAtA.of_evalGraph (snd_DupocTrollBot_vs_DefectBot k)

/-- `pos_DupocTrollBot_vs_DupocBot` (the troll FINDS the reflexive equation "`DupocBot k` IS `DupocBot k`" and
defects; Dupoc's guard "the troll cooperates with me" is then false) -/
@[outcomeA]
theorem outcome_DupocTrollBot_vs_DupocBot :
    OutcomeSpecA .eventual (bot DupocTrollBot) (bot DupocBot) (some (.D, .D)) :=
  OutcomeSpecA.eventual_of (by
    obtain ⟨k₀, h⟩ := pos_DupocTrollBot_vs_DupocBot
    exact ⟨k₀, fun k hk ↦ OutcomeAtA.of_evalGraph (h k hk)⟩)

/-- `snd_DupocTrollBot_vs_DupocTrollBot` -/
@[outcomeA]
theorem outcome_DupocTrollBot_vs_DupocTrollBot :
    OutcomeSpecA .universal (bot DupocTrollBot) (bot DupocTrollBot) (some (.C, .C)) :=
  OutcomeSpecA.universal_of fun k ↦ OutcomeAtA.of_evalGraph (snd_DupocTrollBot_vs_DupocTrollBot k)

/-- `snd_DupocTrollBot_vs_EBot` -/
@[outcomeA]
theorem outcome_DupocTrollBot_vs_EBot :
    OutcomeSpecA .universal (bot DupocTrollBot) (const EBot) (some (.C, .D)) :=
  OutcomeSpecA.universal_of fun k ↦ OutcomeAtA.of_evalGraph (snd_DupocTrollBot_vs_EBot k)

/-- `snd_PrudentBot_vs_DupocTrollBot` read from the troll's side (`Cells/DupocTrollPrudent.lean`, 2026-10-19). -/
@[outcomeA]
theorem outcome_DupocTrollBot_vs_PrudentBot :
    OutcomeSpecA .universal (bot DupocTrollBot) (bot PrudentBot) (some (.C, .D)) :=
  OutcomeSpecA.universal_of fun k ↦
    OutcomeAtA.of_evalGraph ⟨(snd_PrudentBot_vs_DupocTrollBot k).2, (snd_PrudentBot_vs_DupocTrollBot k).1⟩

/-- `snd_DupocTrollBot_vs_OBot` -/
@[outcomeA]
theorem outcome_DupocTrollBot_vs_OBot :
    OutcomeSpecA .universal (bot DupocTrollBot) (const OBot) (some (.C, .C)) :=
  OutcomeSpecA.universal_of fun k ↦ OutcomeAtA.of_evalGraph (snd_DupocTrollBot_vs_OBot k)

/-- `snd_DupocTrollBot_vs_TitForTatBot` -/
@[outcomeA]
theorem outcome_DupocTrollBot_vs_TitForTatBot :
    OutcomeSpecA .universal (bot DupocTrollBot) (const TitForTatBot) (some (.C, .C)) :=
  OutcomeSpecA.universal_of fun k ↦ OutcomeAtA.of_evalGraph (snd_DupocTrollBot_vs_TitForTatBot k)

/-- `snd_DIMDID_vs_DupocTrollBot` read from the troll's side (`Cells/DimdidTroll.lean`): the `.eq` guard is false
against DIMDID, so the troll cooperates, and DIMDID's guard is self-defeating. -/
@[outcomeA]
theorem outcome_DupocTrollBot_vs_DIMDID :
    OutcomeSpecA .universal (bot DupocTrollBot) (bot DIMDID) (some (.C, .C)) :=
  OutcomeSpecA.universal_of fun k ↦
    OutcomeAtA.of_evalGraph ⟨(snd_DIMDID_vs_DupocTrollBot k).2, (snd_DIMDID_vs_DupocTrollBot k).1⟩

end ArithS
