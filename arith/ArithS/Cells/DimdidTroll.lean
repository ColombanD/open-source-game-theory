import ArithS.Cells.Dimdid
import ArithS.Cells.DupocTrollBot

/-!
# ArithS.Cells.DimdidTroll — `DIMDID × DupocTrollBot = (C, C)` at every `k` (2026-10-13)

**Reading guide.** One SND cell, the last pair of the twelve-bot ladder zoo `body8 + CupodTrollBot + DupocTrollBot +
CIMCIC + DIMDID` (`Research/Notes/EGT_FINDINGS_SPRIME.md` §8.6). Facts: `progCode_DIMDID_ne_DupocBot`,
`snd_DIMDID_vs_DupocTrollBot`.

The troll's `.eq` guard "the opponent IS `DupocBot k`" is false against `DIMDID k` — the two codes differ already
in their branch constants (DIMDID: then `D`, else `C`; Dupoc: then `C`, else `D`), exactly as `CupodBot k` differs
from `DupocBot k` (`progCode_CupodBot_ne_DupocBot`) — so the troll takes its else branch and cooperates
(`dtb_C_of_ne`). DIMDID's guard "I defect ⇒ the troll defects" is then SELF-DEFEATING (`dimdid_selfref_not_found`):
a proof of it would make DIMDID defect while the troll still cooperates, so no proof exists within any budget and
DIMDID cooperates (`dimdid_C_of_probe`). Both plays at fuel 2, at every `k` — no hinge, no Löb: the same shape as
`snd_DIMDID_vs_CupodTrollBot`. Lives in its own module because `Cells/Dimdid` and `Cells/DupocTrollBot` do not
import each other.
-/

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open LAct
open PD.Bots

/-- DIMDID's and Dupoc's codes differ in their branch constants (DIMDID: then `D`, else `C`; Dupoc: then `C`,
else `D`) — the troll's `.eq` guard against DIMDID is false. -/
lemma progCode_DIMDID_ne_DupocBot (k : ℕ) : progCode (DIMDID k) ≠ progCode (DupocBot k) := by
  rw [progCode_DIMDID_search, progCode_DupocBot_search]
  intro e
  exact pConst_zero_ne_one (pSearch_inj e).2.2.1.symm

/-- `DIMDID × DupocTrollBot = (C, C)` at every `k`: the troll's `.eq` guard is false (DIMDID is not DupocBot), so
it cooperates, and DIMDID's guard is then self-defeating. -/
theorem snd_DIMDID_vs_DupocTrollBot (k : ℕ) :
    EvalGraph 2 (progCode (DIMDID k)) (progCode (DupocTrollBot k)) (progCode (DIMDID k)) (actCode .C) ∧
    EvalGraph 2 (progCode (DupocTrollBot k)) (progCode (DIMDID k)) (progCode (DupocTrollBot k)) (actCode .C) := by
  have hT := dtb_C_of_ne k (properPlayer_DIMDID k) (progCode_DIMDID_ne_DupocBot k)
  exact ⟨dimdid_C_of_probe k (properPlayer_DupocTrollBot k) hT, hT⟩

end ArithS
