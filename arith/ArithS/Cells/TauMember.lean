import ArithS.Bridge.Agent
import ArithS.Eval.TauCheck

/-!
# ArithS.Cells.TauMember — the closed member's guard, read at ℕ

Phase 2 of `SPRIME_SOURCE_OF_TRUTH.md`, the pronoun reading (2026-10-01), on the engine's symmetric system
`cfdSys k` (`Tau/Zoo.lean`): after `sysCloseCode` the member `i` is the code of the engine's closed member
(`sysCloseCode_cfdSys_member`, `Eval/TauCheck.lean`), whose guard is `.plays (.bot (.sys (cfdSys k) (1 - i)))
(.bot (.sys (cfdSys k) (1 - i))) C`. This file states what the evaluator consults at that node:

* `cfd_closed_guard_iff` — the guard code at ANY frame `(me, opp)` and node budget is the code of
  `sentenceAt me opp (closed guard)`, and that sentence holds in ℕ iff the partner, bot-wrapped, plays `C`
  against itself (`models_sentenceAt_plays`, the frozen bridge's truth equation);
* `evalGraph_cfdMember_closed_iff` — the search clause of the closed member, spelled out on that sentence.

Nothing here decides the member's outcome: the entangled families (Phase 3, mutual Löb on the member slots)
are the next step.
-/

set_option linter.constructorNameAsVariable false

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1
open LAct
open PD PD.Tau

/-- The closed guard of member `i`: the partner `.bot (.sys (cfdSys k) (1 - i))` plays `C` against itself. -/
def cfdClosedGuard (k i : ℕ) : PD.Formula :=
  .plays (.bot (.sys (cfdSys k) (1 - i))) (.bot (.sys (cfdSys k) (1 - i))) Action.C

theorem cfdClosedGuard_eq (k i : ℕ) : (cfdGuard i).sysClose (cfdSys k) = cfdClosedGuard k i := rfl

/-- **The truth equation of the closed member's guard.** -/
theorem cfd_closed_guard_iff (k i : ℕ) (me opp : PD.Prog) (K : ℕ) :
    guardCodeB (templateCode (cfdClosedGuard k i)) (progCode me) (progCode opp) K =
      ⌜sentenceAt me opp (cfdClosedGuard k i)⌝ ∧
    (ℕ↓[LAct] ⊧ sentenceAt me opp (cfdClosedGuard k i) ↔
      ∃ N, EvalGraph N (pBot (progCode (.sys (cfdSys k) (1 - i)))) (pBot (progCode (.sys (cfdSys k) (1 - i))))
        (pBot (progCode (.sys (cfdSys k) (1 - i)))) (actCode .C)) := by
  have hns : noSelfIdxF (cfdClosedGuard k i) = true := rfl
  refine ⟨?_, ?_⟩
  · rw [guardCodeB_of_template (isSemiformula_templateCode _ hns), quote_sentenceAt me opp _ hns]
  · unfold cfdClosedGuard
    rw [models_sentenceAt_plays me opp _ _ Action.C ⟨by simp, by simp⟩ ⟨by simp, by simp⟩, progCode_bot]

/-- **The search clause of the closed member**: at fuel `n + 1` in the frame `(me, opp)`, the closed member
plays `a` iff the sentence "the partner, bot-wrapped, plays C against itself" has a `TAct`-proof within `k`
and `C` is played, or it has none and `D` is played. -/
theorem evalGraph_cfdMember_closed_iff (k i : ℕ) (hi : i ≤ 1) (me opp : PD.Prog) (n a : ℕ) :
    EvalGraph (n + 1) (progCode me) (progCode opp) (sysCloseCode (progListCode (cfdSys k)) (progCode (cfdMember k i))) a ↔
    ((LenBox TAct k (⌜sentenceAt me opp (cfdClosedGuard k i)⌝ : ℕ) ∧ EvalGraph n (progCode me) (progCode opp) (pConst 0) a) ∨
     (¬ LenBox TAct k (⌜sentenceAt me opp (cfdClosedGuard k i)⌝ : ℕ) ∧ EvalGraph n (progCode me) (progCode opp) (pConst 1) a)) := by
  rw [sysCloseCode_cfdSys_member k i hi, cfdMember_eq]
  show EvalGraph (n + 1) (progCode me) (progCode opp)
    (progCode (.search k ((cfdGuard i).sysClose (cfdSys k)) (.const .C) (.const .D))) a ↔ _
  -- the stored template is the ABSTRACTED one (the closed guard names a system with `.search k` members, Phase 2d);
  -- the consulted sentence is the pre-abstraction guard (`EvalGraph.search_iff_at`)
  rw [cfdClosedGuard_eq, progCode_search, progCode_const, progCode_const,
    EvalGraph.search_iff_at (cfdClosedGuard k i) rfl, ← quote_sentenceAt me opp (cfdClosedGuard k i) rfl]
  rfl

end ArithS
