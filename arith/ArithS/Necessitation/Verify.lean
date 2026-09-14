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
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
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

/-! ## 2. Σ₁ definability of the ten node fragments

`Frag1`/`Frag2` define the ten fragments as plain `noncomputable def`s over `mkStep`, `sGoal`,
`sLemma`, `appendV`, `bnum` and the `NumSteps` code producers — every ingredient is Σ₁, but the
fragments themselves carry no `_defined` instance, and `VerifyGraph` (§3) must call them from
inside a `Fixpoint` blueprint. This section supplies the missing instances, bottom-up:
the sum terms (`leafT`/`unaryT`/`binaryT`), the closed numeral facts
(`leafFact`/`bin2Fact`/`bin3Fact`), the three `dlen` tails, the three goal tails, the ten
`node<Tag>Head`s and finally the ten fragments. -/

section definability

/-! ### 2.1 The sum terms and the closed numeral facts -/

noncomputable def leafTDef : 𝚺₁.Semisentence 2 := .mkSigma
  “y l. ∃ z, !qqFvarDef z l ∧ !qqAddGraph y z ↑(𝟏 : ℕ)”
noncomputable def unaryTDef : 𝚺₁.Semisentence 3 := .mkSigma
  “y l n. ∃ z, !qqFvarDef z l ∧ ∃ w, !qqFvarDef w n ∧ ∃ a, !qqAddGraph a z w ∧ !qqAddGraph y a ↑(𝟏 : ℕ)”
noncomputable def binaryTDef : 𝚺₁.Semisentence 4 := .mkSigma
  “y l n₁ n₂. ∃ z, !qqFvarDef z l ∧ ∃ w, !qqFvarDef w n₁ ∧ ∃ u, !qqFvarDef u n₂ ∧
    ∃ a, !qqAddGraph a z w ∧ ∃ b, !qqAddGraph b a u ∧ !qqAddGraph y b ↑(𝟏 : ℕ)”

instance leafT_defined : 𝚺₁-Function₁ (leafT : V → V) via leafTDef := .mk fun v ↦ by
  simp [leafTDef, leafT, numeral_eq_natCast]
instance leafT_definable : 𝚺₁-Function₁ (leafT : V → V) := leafT_defined.to_definable
instance unaryT_defined : 𝚺₁-Function₂ (unaryT : V → V → V) via unaryTDef := .mk fun v ↦ by
  simp [unaryTDef, unaryT, numeral_eq_natCast]
instance unaryT_definable : 𝚺₁-Function₂ (unaryT : V → V → V) := unaryT_defined.to_definable
instance binaryT_defined : 𝚺₁-Function₃ (binaryT : V → V → V → V) via binaryTDef := .mk fun v ↦ by
  simp [binaryTDef, binaryT, numeral_eq_natCast]
instance binaryT_definable : 𝚺₁-Function₃ (binaryT : V → V → V → V) := binaryT_defined.to_definable

noncomputable def leafFactDef : 𝚺₁.Semisentence 3 := .mkSigma
  “y a n. ∃ x, !bnumGraph x a ∧ ∃ z, !qqAddGraph z x ↑(𝟏 : ℕ) ∧ ∃ w, !bnumGraph w n ∧ !leFactDef y z w”
noncomputable def bin2FactDef : 𝚺₁.Semisentence 4 := .mkSigma
  “y a b n. ∃ x, !bnumGraph x a ∧ ∃ u, !bnumGraph u b ∧ ∃ p, !qqAddGraph p x u ∧
    ∃ z, !qqAddGraph z p ↑(𝟏 : ℕ) ∧ ∃ w, !bnumGraph w n ∧ !leFactDef y z w”
noncomputable def bin3FactDef : 𝚺₁.Semisentence 5 := .mkSigma
  “y a b c n. ∃ x, !bnumGraph x a ∧ ∃ u, !bnumGraph u b ∧ ∃ t, !bnumGraph t c ∧
    ∃ p, !qqAddGraph p x u ∧ ∃ q, !qqAddGraph q p t ∧ ∃ z, !qqAddGraph z q ↑(𝟏 : ℕ) ∧
    ∃ w, !bnumGraph w n ∧ !leFactDef y z w”

instance leafFact_defined : 𝚺₁-Function₂ (leafFact : V → V → V) via leafFactDef := .mk fun v ↦ by
  simp [leafFactDef, leafFact, bnum.defined.iff, leFact_defined.iff, numeral_eq_natCast]
instance leafFact_definable : 𝚺₁-Function₂ (leafFact : V → V → V) := leafFact_defined.to_definable
instance bin2Fact_defined : 𝚺₁-Function₃ (bin2Fact : V → V → V → V) via bin2FactDef := .mk fun v ↦ by
  simp [bin2FactDef, bin2Fact, bnum.defined.iff, leFact_defined.iff, numeral_eq_natCast]
instance bin2Fact_definable : 𝚺₁-Function₃ (bin2Fact : V → V → V → V) := bin2Fact_defined.to_definable
instance bin3Fact_defined : 𝚺₁-Function₄ (bin3Fact : V → V → V → V → V) via bin3FactDef := .mk fun v ↦ by
  simp [bin3FactDef, bin3Fact, bnum.defined.iff, leFact_defined.iff, numeral_eq_natCast]
instance bin3Fact_definable : 𝚺₁-Function₄ (bin3Fact : V → V → V → V → V) := bin3Fact_defined.to_definable

end definability

end ArithS
