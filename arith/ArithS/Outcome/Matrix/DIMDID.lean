import ArithS.Outcome.Spec
import ArithS.Outcome.Attr
import ArithS.Cells.Dimdid
import ArithS.Cells.DimdidTroll
import ArithS.Outcome.Matrix.CIMCIC

/-!
# ArithS.Outcome.Matrix.DIMDID — the `S'` cells with `DIMDID` on the left

`DIMDID k` ("defect iff my defection provably implies yours", `engine/.../Bots/DIMDID.lean`, 2026-10-13) is the
C/D transposition of `CIMCIC k` (`DIMDID_eq_transpose`, by `rfl`). It has NO engine cell: every cell here is
an `S'`-only result, the engine's statement (`OutcomeSpecA`, `Outcome/Spec.lean`) proved either from the
method-named theorem of `Cells/Dimdid.lean` named in its docstring, or — where the partner's transposition is in
the zoo — from the CIMCIC cell by the general transposition theorem `outcomeSpecA_transpose`
(`Cells/Transposition.lean`): `DIMDID × DefectBot = τ(CIMCIC × CooperateBot)`, `DIMDID × CupodBot = τ(CIMCIC ×
DupocBot)`, `DIMDID × DIMDID = τ(CIMCIC × CIMCIC)`. Its three floors (× DupocBot, × CIMCIC, × PrudentBot) are in
`Outcome/Floors.lean`. The row, DIMDID's side: C against CooperateBot, TitForTatBot, DBot, EBot, CupodTrollBot
(and, engine side of the floors, against DupocBot, CIMCIC, PrudentBot); D against DefectBot, OBot, CupodBot,
DIMCID and itself. The cell against DupocTrollBot (`Cells/DimdidTroll.lean`, `snd_DIMDID_vs_DupocTrollBot`, `(C, C)`)
is stated in both orientations, here and in `Outcome/Matrix/DupocTrollBot.lean`.
-/

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus
open LAct
open PD.Bots

/-- `snd_DIMDID_vs_CooperateBot` (every `k`): the guard is self-defeating. -/
@[outcomeA]
theorem outcome_DIMDID_vs_CooperateBot :
    OutcomeSpecA .universal (bot DIMDID) (const CooperateBot) (some (.C, .C)) :=
  OutcomeSpecA.universal_of fun k ↦ OutcomeAtA.of_evalGraph (snd_DIMDID_vs_CooperateBot k)

/-- τ of `outcome_CIMCIC_vs_CooperateBot` (`pos_CIMCIC_vs_CooperateBot`): the guard "I defect ⇒ DefectBot defects
against me" is a `TAct`-theorem instance, found for all large `k`. -/
@[outcomeA]
theorem outcome_DIMDID_vs_DefectBot :
    OutcomeSpecA .eventual (bot DIMDID) (const DefectBot) (some (.D, .D)) :=
  (outcomeSpecA_transpose (L := CIMCIC) (R := fun _ ↦ CooperateBot) fragP_CIMCIC (fun _ ↦ rfl)
    (some (.C, .C))).mp outcome_CIMCIC_vs_CooperateBot

/-- `snd_DIMDID_vs_TitForTatBot` (every `k`). -/
@[outcomeA]
theorem outcome_DIMDID_vs_TitForTatBot :
    OutcomeSpecA .universal (bot DIMDID) (const TitForTatBot) (some (.C, .C)) :=
  OutcomeSpecA.universal_of fun k ↦ OutcomeAtA.of_evalGraph (snd_DIMDID_vs_TitForTatBot k)

/-- `pos_DIMDID_vs_DBot`: DBot sees DIMDID's FOUND defection against `.bot DefectBot` and cooperates. -/
@[outcomeA]
theorem outcome_DIMDID_vs_DBot :
    OutcomeSpecA .eventual (bot DIMDID) (const DBot) (some (.C, .C)) :=
  OutcomeSpecA.eventual_of (by
    obtain ⟨k₀, h⟩ := pos_DIMDID_vs_DBot
    exact ⟨k₀, fun k hk ↦ OutcomeAtA.of_evalGraph (h k hk)⟩)

/-- `pos_DIMDID_vs_EBot`. -/
@[outcomeA]
theorem outcome_DIMDID_vs_EBot :
    OutcomeSpecA .eventual (bot DIMDID) (const EBot) (some (.C, .C)) :=
  OutcomeSpecA.eventual_of (by
    obtain ⟨k₀, h⟩ := pos_DIMDID_vs_EBot
    exact ⟨k₀, fun k hk ↦ OutcomeAtA.of_evalGraph (h k hk)⟩)

/-- `snd_DIMDID_vs_CupodTrollBot` (every `k`): the troll's `.eq` guard is false. -/
@[outcomeA]
theorem outcome_DIMDID_vs_CupodTrollBot :
    OutcomeSpecA .universal (bot DIMDID) (bot CupodTrollBot) (some (.C, .C)) :=
  OutcomeSpecA.universal_of fun k ↦ OutcomeAtA.of_evalGraph (snd_DIMDID_vs_CupodTrollBot k)

/-- `snd_DIMDID_vs_DupocTrollBot` (every `k`): the troll's `.eq` guard is false (DIMDID's branch constants are not
Dupoc's), so it cooperates, and DIMDID's guard is self-defeating. -/
@[outcomeA]
theorem outcome_DIMDID_vs_DupocTrollBot :
    OutcomeSpecA .universal (bot DIMDID) (bot DupocTrollBot) (some (.C, .C)) :=
  OutcomeSpecA.universal_of fun k ↦ OutcomeAtA.of_evalGraph (snd_DIMDID_vs_DupocTrollBot k)

/-- `loeb_DIMDID_vs_OBot`: OBot sees DIMDID's defection against `.bot DefectBot`, DIMDID's guard against OBot is
found. -/
@[outcomeA]
theorem outcome_DIMDID_vs_OBot :
    OutcomeSpecA .eventual (bot DIMDID) (const OBot) (some (.D, .D)) :=
  OutcomeSpecA.eventual_of (by
    obtain ⟨k₀, h⟩ := loeb_DIMDID_vs_OBot
    exact ⟨k₀, fun k hk ↦ OutcomeAtA.of_evalGraph (h k hk)⟩)

/-- τ of `outcome_CIMCIC_vs_DupocBot` (`loeb_CIMCIC_vs_DupocBot`): the mutual Löb cell. -/
@[outcomeA]
theorem outcome_DIMDID_vs_CupodBot :
    OutcomeSpecA .eventual (bot DIMDID) (bot CupodBot) (some (.D, .D)) :=
  (outcomeSpecA_transpose (L := CIMCIC) (R := DupocBot) fragP_CIMCIC fragP_DupocBot (some (.C, .C))).mp
    outcome_CIMCIC_vs_DupocBot

/-- `loeb_DIMDID_vs_DIMCID`: the mutual family of "I defect ⇒ you defect" and "I cooperate ⇒ you defect". -/
@[outcomeA]
theorem outcome_DIMDID_vs_DIMCID :
    OutcomeSpecA .eventual (bot DIMDID) (bot DIMCID) (some (.D, .D)) :=
  OutcomeSpecA.eventual_of (by
    obtain ⟨k₀, h⟩ := loeb_DIMDID_vs_DIMCID
    exact ⟨k₀, fun k hk ↦ OutcomeAtA.of_evalGraph (h k hk)⟩)

/-- τ of `outcome_CIMCIC_vs_CIMCIC` (`pos_Cimcic_vs_Cimcic`): the guard against itself is a tautology. -/
@[outcomeA]
theorem outcome_DIMDID_vs_DIMDID :
    OutcomeSpecA .eventual (bot DIMDID) (bot DIMDID) (some (.D, .D)) :=
  (outcomeSpecA_transpose (L := CIMCIC) (R := CIMCIC) fragP_CIMCIC fragP_CIMCIC (some (.C, .C))).mp
    outcome_CIMCIC_vs_CIMCIC

end ArithS
