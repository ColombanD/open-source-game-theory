import ArithS.Eval.Fixpoint
import ArithS.Notation

/-!
# ArithS.Eval — the evaluator, arithmetized

**Definition.** `EvalGraph n me opp p a`: with fuel `n`, in the frame `(me, opp)`, the program
code `p` plays the action `a`. It mirrors the engine's `Dynamics.eval` clause for clause
(the characterization `EvalGraph.case_iff` at the end of this file IS the definition a reader
should accept; the fixpoint construction behind it is `ArithS.Eval.Fixpoint`):

* `pConst a` plays `a`; `pSelf` runs `me` in the same frame; `pOpp` runs `opp` in the same frame;
  `pBot p` runs `p`; `pIte b a' p q` runs `b`, then `p` if it played `a'`, else `q`;
* `pSearch k g p q` runs `p` if `□[k] (guardCodeB g me opp k)` — the stored template `g` filled
  with the descriptions of the frame in `#0..#5` and the node's own budget in `#6`
  (`ArithS.Agents.Guard`; on a six-variable template this is `guardCode g me opp`,
  `guardCodeB_of_template`) has a `TAct`-proof of length `≤ k` — else `q`;
* `pSim p q` substitutes the frame into `p` and `q` (`substCode`, `ArithS.Agents.Subst`:
  `pSelf ↦ me`, `pOpp ↦ opp`, `pBot` frozen, stored templates instantiated with the OUTER
  descriptions) and runs `p'` in the frame `(p', q')` — the engine's `.sim` clause;
* the tau constructors (2026-09-30): `pTvote pNil θ p q` runs `p` iff `θ = 0`; `pTvote (pCons (ppair w I)
  rest) θ p q` runs `p` if `θ = 0`, else runs the entry `I` in its own frame `(pBot I, pBot I)` and continues
  with `pTvote rest (θ - w) p q` if it played `0` (`C`), with `pTvote rest θ p q` otherwise (the engine's
  `.tvote` peel, truncated subtraction); `pSys d i` looks member `i` up (`listGet d i = m + 1`,
  `ArithS.Agents.SysClose`) and runs `sysCloseCode d m` in the same frame (the engine's LAZY one-level
  unfold); `pSelfIdx j` (a dangling reference) and a bare list cons play nothing;
* fuel `0` plays nothing.

**Facts.** The graph is Σ₁-definable (`evalGraphDef`); sub-calls decrease the fuel but may grow the
other components, so the fixpoint is `Finite`, not `StrongFinite`, and functionality and fuel
monotonicity are proved at `V = ℕ` by ordinary induction (`ArithS.Eval.EvalN`: `EvalGraph.unique'`,
`EvalGraph.mono_le`). On search-free programs it runs in lockstep with the engine's `eval` at the
same fuel (`Cells/SearchFree.lean`). At ℕ: `eval_deterministic_nat` (`ArithS.Readings`).
-/

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1
open LAct

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- `EvalGraph n me opp p a`: with fuel `n`, in the frame `(me, opp)`, `p` plays `a`. -/
def EvalGraph (n me opp p a : V) : Prop := EvalFix.construction.Fixpoint ![] ⟪n, me, opp, p, a⟫

noncomputable def evalGraphDef : 𝚺₁.Semisentence 5 := .mkSigma
  “n me opp p a. ∃ pr, !pair₅Def pr n me opp p a ∧ !EvalFix.blueprint.fixpointDef pr”

private lemma eval_param_eq (p : Fin 0 → V) (x : V) :
    EvalFix.construction.Fixpoint p x = EvalFix.construction.Fixpoint ![] x := by
  rw [Subsingleton.elim p ![]]

lemma evalGraph_defined :
    𝚺₁.Defined (fun v : Fin 5 → V ↦ EvalGraph (v 0) (v 1) (v 2) (v 3) (v 4)) evalGraphDef := .mk fun v ↦ by
  simp [evalGraphDef, EvalFix.construction.fixpoint_defined.iff, EvalGraph]
  rw [eval_param_eq]

instance evalGraph_definable : 𝚺₁-Relation₅[V] EvalGraph := evalGraph_defined.to_definable

lemma EvalGraph.case_iff {n me opp p a : V} :
    EvalGraph n me opp p a ↔
    ∃ n', n = n' + 1 ∧
    ( p = pConst a ∨
      (p = pSelf ∧ EvalGraph n' me opp me a) ∨
      (p = pOpp ∧ EvalGraph n' me opp opp a) ∨
      (∃ p', p = pBot p' ∧ EvalGraph n' me opp p' a) ∨
      (∃ p' q, p = pSim p' q ∧
        EvalGraph n' (substCode me opp p') (substCode me opp q) (substCode me opp p') a) ∨
      (∃ b a' p' q r, p = pIte b a' p' q ∧ EvalGraph n' me opp b r ∧
        ((r = a' ∧ EvalGraph n' me opp p' a) ∨ (r ≠ a' ∧ EvalGraph n' me opp q a))) ∨
      (∃ k g p' q, p = pSearch k g p' q ∧
        ((LenBox TAct k (guardCodeB g me opp k) ∧ EvalGraph n' me opp p' a) ∨
         (¬LenBox TAct k (guardCodeB g me opp k) ∧ EvalGraph n' me opp q a))) ∨
      (∃ θ p' q, p = pTvote pNil θ p' q ∧
        ((θ = 0 ∧ EvalGraph n' me opp p' a) ∨ (θ ≠ 0 ∧ EvalGraph n' me opp q a))) ∨
      (∃ w I rest θ p' q, p = pTvote (pCons (ppair w I) rest) θ p' q ∧
        ((θ = 0 ∧ EvalGraph n' me opp p' a) ∨
         (θ ≠ 0 ∧ ∃ r, EvalGraph n' (pBot I) (pBot I) I r ∧
           ((r = 0 ∧ EvalGraph n' me opp (pTvote rest (θ - w) p' q) a) ∨
            (r ≠ 0 ∧ EvalGraph n' me opp (pTvote rest θ p' q) a))))) ∨
      (∃ d i m, p = pSys d i ∧ listGet d i = m + 1 ∧ EvalGraph n' me opp (sysCloseCode d m) a) ) := by
  rw [EvalGraph, EvalFix.construction.case]
  simp only [EvalFix.construction, EvalFix.Phi, Set.mem_setOf_eq, pair_ext_iff]
  constructor
  · rintro (⟨n₀, me₀, opp₀, a₀, h⟩ | ⟨n₀, me₀, opp₀, a₀, hc, h⟩ | ⟨n₀, me₀, opp₀, a₀, hc, h⟩ |
      ⟨n₀, me₀, opp₀, p₀, a₀, hc, h⟩ | ⟨n₀, me₀, opp₀, p', q, a₀, hc, h⟩ |
      ⟨n₀, me₀, opp₀, b, a', p', q, a₀, r, hb, hpq, h⟩ | ⟨n₀, me₀, opp₀, k, g, p', q, a₀, hpq, h⟩ |
      ⟨n₀, me₀, opp₀, θ, p', q, a₀, hpq, h⟩ | ⟨n₀, me₀, opp₀, w, I, rest, θ, p', q, a₀, hpq, h⟩ |
      ⟨n₀, me₀, opp₀, d, i, m, a₀, hm, hc, h⟩) <;>
      obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
    · exact ⟨n₀, rfl, Or.inl rfl⟩
    · exact ⟨n₀, rfl, Or.inr (Or.inl ⟨rfl, hc⟩)⟩
    · exact ⟨n₀, rfl, Or.inr (Or.inr (Or.inl ⟨rfl, hc⟩))⟩
    · exact ⟨n₀, rfl, Or.inr (Or.inr (Or.inr (Or.inl ⟨p₀, rfl, hc⟩)))⟩
    · exact ⟨n₀, rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p', q, rfl, hc⟩))))⟩
    · exact ⟨n₀, rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨b, a', p', q, r, rfl, hb, hpq⟩)))))⟩
    · exact ⟨n₀, rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨k, g, p', q, rfl, hpq⟩))))))⟩
    · exact ⟨n₀, rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨θ, p', q, rfl, hpq⟩)))))))⟩
    · exact ⟨n₀, rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨w, I, rest, θ, p', q, rfl, hpq⟩))))))))⟩
    · exact ⟨n₀, rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨d, i, m, rfl, hm, hc⟩))))))))⟩
  · rintro ⟨n', rfl, (rfl | ⟨rfl, hc⟩ | ⟨rfl, hc⟩ | ⟨p', rfl, hc⟩ | ⟨p', q, rfl, hc⟩ |
      ⟨b, a', p', q, r, rfl, hb, hpq⟩ | ⟨k, g, p', q, rfl, hpq⟩ | ⟨θ, p', q, rfl, hpq⟩ |
      ⟨w, I, rest, θ, p', q, rfl, hpq⟩ | ⟨d, i, m, rfl, hm, hc⟩)⟩
    · exact Or.inl ⟨n', me, opp, a, by simp⟩
    · exact Or.inr (Or.inl ⟨n', me, opp, a, hc, by simp⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨n', me, opp, a, hc, by simp⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨n', me, opp, p', a, hc, by simp⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n', me, opp, p', q, a, hc, by simp⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n', me, opp, b, a', p', q, a, r, hb, hpq, by simp⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n', me, opp, k, g, p', q, a, hpq, by simp⟩))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n', me, opp, θ, p', q, a, hpq, by simp⟩)))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨n', me, opp, w, I, rest, θ, p', q, a, hpq, by simp⟩))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨n', me, opp, d, i, m, a, hm, hc, by simp⟩))))))))

end ArithS
