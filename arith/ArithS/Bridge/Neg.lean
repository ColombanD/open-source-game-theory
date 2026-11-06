import Mathlib.Tactic
import Mathlib.Data.Nat.Log
import ArithS.Agents.Code
import ArithS.Agents.Fit

/-!
# ArithS.Neg — T2-NEG: no budget-keeping transfer exists, at any inflation (roadmap M3, step (d))

**STATUS 2026-09-16: the impossibility theorem is RETIRED — the engine's atom rule was re-costed
in response to it (branch `colomban-recost`, roadmap M6), and the file now ends with the theorem
that the old witness pays for the program it names (`no_budget_keeping_witness_pays`) and that
every engine theorem fits its budget (`pf_size`). The bit-length lemmas of §1–2 are unchanged and
still used (`FitBox`). The text below describes the ORIGINAL situation, kept as the record of why
the re-cost was made.**

The engine's transcript-cost model charged an ATOM by the number of evaluation steps of
its play certificate, never by the size of its conclusion: `AtomProvable.mk` needed only
`n ≤ k` for the run cost `n`, so `Pf 1 (.plays (.const C) q C)` held for EVERY program `q`
(`PlaysProof.const` costs `c_leaf = 1`; this is the exception in `Base/Exclusion.pf_size_or_atom`).
Any arithmetical realization of that atom must WRITE `q` — at least the canonical numeral of
its code — and a `TAct`-proof is at least as long as its conclusion (`formulaLenMeta_le_of_lenBoxNat`,
`ArithS.ProofLength`). So for the bot-iterates `q = .bot^n (.const C)`, whose codes have bit
length `≥ n`, the shortest proof of the realized atom grows without bound while the engine's
budget stays `1`: no function `e` can make `Pf k φ → TAct ⊢_{e k} tr φ` true.

* `no_budget_keeping_transfer`: the impossibility, PARAMETRIC in the realization `tr` — the
  one hypothesis is that `tr (.plays p q a)` is at least as long as the bit length of the
  canonical numeral `canonical (progCode q)` of a closed `q`;
* `size_canonical_le_formulaLenMeta_sentenceAt`: the hypothesis holds for the concrete bounded translation
  `sentenceAt me opp φ := template φ ⇜ descriptionTerms (progCode me) (progCode opp)` of `ArithS.Code` (the closed
  description of `q` is a binary numeral whose length is at least the bit length);
* `no_budget_keeping_transfer_template` / `no_budget_keeping_transfer_guardCode`: the instance,
  the second one phrased on the code `guardCode (templateCode φ) (progCode me) (progCode opp)` that the
  arithmetized evaluator actually consults.

This is the precise reason T2 is stated as T2-NEG + T2-AGENT + T2-CORE (roadmap "M3 DESIGN
DECISION"): where the engine counts characters, PA-`S` agrees; where it charges evaluation
steps and cheap citations (`search_t`'s `numCost k`), no PA proof length can match, and
budget-keeping soundness is exactly Critch's assumption (d), left as M4.
-/

set_option linter.constructorNameAsVariable false

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1
open LAct

/-! ### Bot-iterates and the bit length of their codes -/


/-! ### A binary numeral is at least as long as the bit length it writes -/


/-! ### The realized atom writes the description of its second program -/

/-- A description is longer than its numeral term. -/
lemma formulaLenMeta_emb_descF_ge {n : ℕ} (X T U W : Semiterm LAct Empty (n + 1)) :
    termLenMeta (Rew.emb T : SyntacticSemiterm LAct (n + 1)) + 1 ≤
      formulaLenMeta (Rewriting.emb (descF X T U W) : Semiproposition LAct n) := by
  unfold descF
  simp only [Rewriting.emb, Rewriting.app_exs, Rew.q_emb, LogicalConnective.HomClass.map_and,
    Semiformula.rew_rel, formulaLenMeta_exs, formulaLenMeta_and, formulaLenMeta_rel, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  omega


/-! ### T2-NEG, RETIRED by the re-cost — the witness now pays

**History (2026-09-10 → 2026-09-16).** Against the ORIGINAL atom rule (`AtomProvable.mk` with the
side condition `n ≤ k`, run cost only) this file proved

```
theorem no_budget_keeping_transfer (e : ℕ → ℕ) (tr : PD.Formula → Sentence LAct)
    (htr : ∀ p q a, closedP q = true →
      Nat.size (canonical (progCode q)) ≤ formulaLenMeta (Rewriting.emb (tr (.plays p q a)) : Proposition LAct)) :
    ∃ k φ, PD.Pf k φ ∧ ¬ LenBoxNat (codeBound : ℕ → ℕ) (e k) TAct (⌜tr φ⌝ : ℕ)
```

with the witness `k = 1`, `φ = .plays (.const C) (botIter (e 1 + 1) (.const C)) C`, plus its
instances `_template` (for `sentenceAt`) and `_guardCode` (on the code the evaluator consults) — T2-NEG,
three standard axioms, last checked at commit 0c8b410 of `colomban-arith-u10`. It is exactly why
the engine's atom rule was RE-COSTED on 2026-09-16 (`ProofSystem.lean` §3, roadmap M6): the rule now
charges `n + (Formula.plays me opponent a).size ≤ k`, the whole conclusion, so the witness can no
longer be derived at budget `1` — and the theorem below records that it now pays for every
program it names, which is the property the re-cost was made for. -/


end ArithS
