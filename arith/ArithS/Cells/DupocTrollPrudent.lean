import ArithS.Cells.DupocTrollBot

/-!
# ArithS.Cells.DupocTrollPrudent — `PrudentBot × DupocTrollBot = (D, C)` (2026-10-19)

The one pair of the 15-template tau table (`Tau/Spec.lean`, `paperOrder` with `dupocTroll`) that
`Cells/DupocTrollBot.lean` did not state: PrudentBot is a paper template but not a member of any paper zoo, so
the cell was not needed for the EGT ladder — it is needed for the certification's cell-derived fixture
(`app/tests/fixtures/make_sprime_tau_fixture.py`, which walks `paperOrder²`). The argument is
`snd_PrudentBot_vs_CupodTrollBot`'s: Prudent's prudence guard ("the opponent defects against `DefectBot`") is
FALSE of the troll, which cooperates with the defector (`snd_DupocTrollBot_vs_botDB`), so by soundness it is never
found and Prudent defects; the troll's `.eq` guard is false (Prudent's code is not `DupocBot k`'s), so it
cooperates. Both at every `k`, pad 3. `S'`-only, like every DupocTroll cell.
-/

set_option linter.constructorNameAsVariable false

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open LAct
open PD.Bots
open ArithS.Tau

/-- Prudent's code is not Dupoc's: their then-branches differ (a search vs a constant). -/
lemma progCode_PrudentBot_ne_DupocBot (k : ℕ) : progCode (PrudentBot k) ≠ progCode (DupocBot k) := by
  rw [progCode_PrudentBot_search, progCode_DupocBot_search]
  intro e
  exact pConst_ne_pSearch _ _ _ _ _ (pSearch_inj e).2.2.1.symm

/-- `PrudentBot × DupocTrollBot = (D, C)`: the prudence guard is false of the troll (it trusts the defector), the
troll's identity guard is false of Prudent. -/
theorem snd_PrudentBot_vs_DupocTrollBot (k : ℕ) :
    EvalGraph 3 (progCode (PrudentBot k)) (progCode (DupocTrollBot k)) (progCode (PrudentBot k)) (actCode .D) ∧
    EvalGraph 3 (progCode (DupocTrollBot k)) (progCode (PrudentBot k)) (progCode (DupocTrollBot k)) (actCode .C) :=
  ⟨prudent_D_of_inner k (properPlayer_DupocTrollBot k) (snd_DupocTrollBot_vs_botDB k),
   EvalGraph.mono_le (by omega) (dtb_C_of_ne k (properPlayer_PrudentBot k) (progCode_PrudentBot_ne_DupocBot k))⟩

end ArithS
