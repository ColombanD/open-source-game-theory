import ArithS.Bridge.Agent
import PrisonersDilemma.Dynamics

/-!
# ArithS.AgentConverse — the converse of T2-AGENT: `eval ↔ EvalGraph` on modest programs

**Given agreement on the consulted `□_k` facts, the arithmetized evaluator and the engine's
evaluator compute the same plays on modest programs (an equivalence).**

`ArithS.Agent` (T2-AGENT) turns an engine CERTIFICATE (`PlaysProof`) into a run of the
arithmetized evaluator, under the two one-directional oracle hypotheses `GuardAgreeT`/
`GuardAgreeF`. This module works with the engine's evaluator `PD.eval` itself and a SINGLE
two-sided oracle, and proves both directions:

* `GuardAgree` — the engine's `Pf` verdict and the arithmetized `□_k` verdict AGREE on the
  guards a modest match can consult: for a fragment formula `φ` (`fragF φ`) and proper modest
  players, `PD.Pf k (φ.subst me opp) ↔ LenBox TAct k (guardOf φ me opp)`. It is restricted
  to exactly the guards that are consulted, so it is the WEAKEST hypothesis both directions
  need. `GuardAgree.toT`/`GuardAgree.toF` show it subsumes the modest instances of both
  T2-AGENT hypotheses — the refutation form `F` falls out of engine soundness
  (`PD.BaseTheorems.Pf_sound`): a refuted guard cannot also be `Pf`-derivable, hence, by the
  `Iff`, cannot be found by the arithmetized search.
* `evalGraph_of_eval` — `PD.eval n me opp body = some a → ∃ N, EvalGraph N ⌜me⌝ ⌜opp⌝ ⌜body⌝ a`,
  by induction on the engine's fuel, unfolding `PD.eval` clause by clause (the `.ite` clause's
  `do`/`BEq` and the `.search` clause's `if proofSearch …` are bridged by `actCode_eq_of_beq`
  and `proofSearch_spec`). This does NOT go through `PlaysProof`, so it needs no refutation
  hypothesis at all.
* `eval_of_evalGraph` — the CONVERSE: `EvalGraph N ⌜me⌝ ⌜opp⌝ ⌜body⌝ r → ∃ a, r = actCode a ∧
  ∃ n, PD.eval n me opp body = some a`, by induction on the arithmetized fuel through the
  inversion lemmas of `ArithS.EvalN`. The result is generalized to an arbitrary code `r`:
  the `.ite` clause's guard result is a bare natural on the arithmetic side, and the induction
  must first learn that it is an action code. No injectivity of `progCode` is needed — the
  induction is on the fuel with the ENGINE program in the frame, `progCode` is unfolded by its
  equations, and the `.sim` step is `progCode_subst` read backwards.
* `eval_iff_evalGraph`, `play_iff_evalGraph`, `outcome_iff_evalGraph` — THE EQUIVALENCE, for
  bodies, plays and outcomes; `playsProof_evalGraph_of_guardAgree` re-derives T2-AGENT from the
  single `Iff` oracle (through `PD.BaseTheorems.playsProof_sound`).
* `plays_interp_iff` — for proper modest players the engine's truth of the atom
  `(.plays me opp a).interp` IS the truth in `ℕ` of its arithmetical translation
  `sentenceAt me' opp' (.plays me opp a)` (via `models_sentenceAt_plays`).

The tau constructors are excluded by `modestP` (their code is `0`); `Inv false` from
`ArithS.Agent` carries the frame invariant (proper modest players, modest body).
-/

set_option linter.constructorNameAsVariable false

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1
open LAct

/-! ### The two-sided oracle -/


/-! ### The engine's `BEq` on actions, read through `actCode` -/


lemma Inv.selfIdx {sf : Bool} {me op : PD.Prog} {j : ℕ} (h : Inv sf me op (.selfIdx j)) : False := by
  simpa [modestP] using h.2.2.2.2.1


/-! ### Engine → arithmetic: induction on the engine's fuel -/


/-! ### Arithmetic → engine: induction on the arithmetized fuel -/


/-! ### The equivalence -/


/-- An engine outcome is a pair of plays at a common fuel. -/
lemma outcome_eq_some_iff (n : ℕ) (p q : PD.Prog) (a b : PD.Action) :
    PD.outcome n p q = some (a, b) ↔ PD.play n p q = some a ∧ PD.play n q p = some b := by
  unfold PD.outcome
  cases PD.play n p q <;> cases PD.play n q p <;> simp [and_comm, eq_comm]


/-! ### The truth equation, engine side -/


end ArithS
