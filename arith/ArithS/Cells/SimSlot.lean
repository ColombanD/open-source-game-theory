import ArithS.Cells.JustSlot

/-!
# ArithS.Cells.SimSlot — a seven-variable searcher under `.sim` reads the OUTER frame

The faithfulness witness for the `.sim` debt of route (c) (`ROUTE_B_SCOPE.md` §6, discharged
2026-09-24). `JustV7 k := pSearch k ⌜guardTemplateJust7⌝ (pConst 0) (pConst 1)` (`Cells/JustSlot`) stores the
constant SEVEN-variable template `guardTemplateJust7`, whose budget slot `#6` names the snapshot `pBot (Dupoc k)`
inside the guard. Before the middle case of `substTemplate`, `substCode me opp (JustV7 k)` left the template
untouched, so `pSim (JustV7 k) q` would have run Just's guard against the INNER frame
(`substCode me opp q`, the simulated opponent) — against the engine's `Prog.subst`, which instantiates
every guard by the OUTER players. Now:

* `evalGraph_substCode_JustV7_iff`: the substituted `JustV7 k`, run in ANY frame `(me', opp')`,
  consults `guardCode ⌜guardTemplate 0⌝ (pBot (DupocV k)) opp` — the guard "the OUTER opponent `opp`
  cooperates with `pBot (Dupoc k)`", at the budget `k` of the node, exactly `just7_search_V`'s guard
  (the un-simulated `JustV7 k` in the frame `(me, opp)`, `guardCodeB_guardTemplateJust7`).
* `evalGraph_sim_JustV7`: therefore `pSim (JustV7 k) q` in the frame `(me, opp)` runs Just's guard
  against the outer `opp`, whatever `q` is — the behaviour of the engine's `.sim (JustBot k) q`
  (`Prog.subst` on `.search k φ p q` descends into `φ`, `Program.lean`).

Proof: `substCode_search` + `guardCodeB_substTemplate₇` (`ArithS.Subst`) + `guardCodeB_guardTemplateJust7`; the
six-variable analogue is `SimTest.sim_search_outer_guard`.
-/

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open LAct

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- **The substituted `JustV7 k` reads the OUTER frame**: run in ANY frame `(me', opp')`, its guard is
the guard against the outer opponent `opp` at its own budget `k` — `guardCodeB_guardTemplateJust7`'s value. -/
theorem evalGraph_substCode_JustV7_iff (n k me opp me' opp' a : V) :
    EvalGraph (n + 1) me' opp' (substCode me opp (JustV7 k)) a ↔
    ((LenBox TAct k (guardCode (⌜guardTemplate 0⌝ : V) (pBot (DupocV k)) opp) ∧
        EvalGraph n me' opp' (pConst 0) a) ∨
      (¬LenBox TAct k (guardCode (⌜guardTemplate 0⌝ : V) (pBot (DupocV k)) opp) ∧
        EvalGraph n me' opp' (pConst 1) a)) := by
  unfold JustV7
  rw [substCode_search, substCode_const, substCode_const, EvalGraph.search_iff,
    guardCodeB_substTemplate₇ (isSemiformula_quote₇ guardTemplateJust7), guardCodeB_guardTemplateJust7]

/-- **The faithfulness witness**: `pSim (JustV7 k) q` in the frame `(me, opp)` runs Just's guard against
the OUTER opponent `opp` (not against the simulated `substCode me opp q`), at the budget `k` — the
engine's `.sim (JustBot k) q`. -/
theorem evalGraph_sim_JustV7 (n k q me opp a : V) :
    EvalGraph (n + 1 + 1) me opp (pSim (JustV7 k) q) a ↔
    ((LenBox TAct k (guardCode (⌜guardTemplate 0⌝ : V) (pBot (DupocV k)) opp) ∧
        EvalGraph n (substCode me opp (JustV7 k)) (substCode me opp q) (pConst 0) a) ∨
      (¬LenBox TAct k (guardCode (⌜guardTemplate 0⌝ : V) (pBot (DupocV k)) opp) ∧
        EvalGraph n (substCode me opp (JustV7 k)) (substCode me opp q) (pConst 1) a)) := by
  rw [EvalGraph.sim_iff, evalGraph_substCode_JustV7_iff]

/-- The same read against a searcher's OWN kind: Just simulating itself against the opponent's
program consults the outer `opp`, and the inner run is the one `just7_search_V` describes. -/
theorem evalGraph_sim_JustV7_self (n k me opp a : V) :
    EvalGraph (n + 1 + 1) me opp (pSim (JustV7 k) pOpp) a ↔
    ((LenBox TAct k (guardCode (⌜guardTemplate 0⌝ : V) (pBot (DupocV k)) opp) ∧
        EvalGraph n (substCode me opp (JustV7 k)) opp (pConst 0) a) ∨
      (¬LenBox TAct k (guardCode (⌜guardTemplate 0⌝ : V) (pBot (DupocV k)) opp) ∧
        EvalGraph n (substCode me opp (JustV7 k)) opp (pConst 1) a)) := by
  rw [evalGraph_sim_JustV7, substCode_opp]

end ArithS
