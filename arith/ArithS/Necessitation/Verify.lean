import ArithS.Necessitation.Frag2

/-!
# ArithS.Necessitation.Verify — `verifySteps ρ` as a Σ₁ function (`DESIGN_fragments.md` §6)

`Frag1`/`Frag2` deliver the ten per-tag NODE fragments (`fragAxL`, `fragVerum`, `nodeAnd`,
`nodeOr`, `nodeWk`, `nodeCut`, `nodeShift`, `nodeAll`, `nodeExs`, `nodeAxm`). This file
delivers the RECURSION that glues them into ONE flat step list for a whole derivation code `ρ`
(`DESIGN_fragments.md` §6.1–§6.4):

* §1 `le_appendV_mid` — the sub-vector bound `L' ≤ appendV u (appendV L' v)` that makes the
  fixpoint `StrongFinite` (§8.4 there).
* §2 `VerifyGraph W tbl ρ L` — the Δ₁ `Fixpoint` on the key `⟪ρ, L⟫`, the `DlenGraph` pattern
  (`DerivationLength.lean:55-211`): ten clauses, one per node tag, each ∃-wrapping its
  fragment's Σ₁ producer and concatenating the children's lists with `appendV`. With
  `case_iff` and the ten inversion lemmas.
* §3 existence, uniqueness and the function `verifySteps` (`Classical.choose!`, the `descFw`
  pattern) with its ten equations.
-/

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1
open LAct

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

set_option maxRecDepth 8000

/-! ## 1. The sub-vector bound (`DESIGN_fragments.md` §8.4) -/

/-- A vector is at most any vector it is a suffix of. -/
lemma le_appendV_self (u w : V) : w ≤ appendV u w := by
  induction u using adjoin_ISigma1.sigma1_succ_induction with
  | hP => definability
  | nil => simp
  | adjoin x u ih => rw [appendV_adjoin]; exact le_trans ih (le_of_lt (lt_adjoin' _ _))

/-- A vector is at most any vector it is a prefix of. -/
lemma le_appendV_prefix (u w : V) : u ≤ appendV u w := by
  induction u using adjoin_ISigma1.sigma1_succ_induction with
  | hP => definability
  | nil => simp
  | adjoin x u ih =>
    rw [appendV_adjoin, adjoin_def, adjoin_def]
    exact add_le_add (pair_le_pair_right x ih) (le_refl (1 : V))

/-- **`le_appendV_mid`** — a list spliced into the middle of a concatenation is bounded by the
whole: the `StrongFinite` ingredient for `VerifyGraph` (`DESIGN_fragments.md` §6.1/§8.4). -/
lemma le_appendV_mid (u w v : V) : w ≤ appendV u (appendV w v) :=
  le_trans (le_appendV_prefix w v) (le_appendV_self u (appendV w v))

end ArithS
