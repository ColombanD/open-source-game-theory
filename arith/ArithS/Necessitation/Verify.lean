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

/-! ### 2.2 The three `dlen` tails and the three goal tails

`dlenLeafSteps W tblN l L n = mkStep W 41 ?[leafT l] ∷ mkStep W 105 ?[leafT l, ^&l, bnum L] ∷
sLemma (leafFact L n) (leafCode tblN L n) ∷ mkStep W 110 ?[bnum n, bnum L ^+ 𝟏, leafT l] ∷ 0`
(`Frag1.lean:537-552`), and the unary/binary tails in the same shape; `goalTail<K>` appends one
`sGoal` step. `sLemma A dA = ⟪7, A, dA⟫`, `sGoal e n s u = ⟪6, e, n, s, u⟫` (`Chain.lean:1395`)
are pair codes, so they enter the blueprints through `pairDef`. -/

noncomputable def dlenLeafStepsDef : 𝚺₁.Semisentence 6 := .mkSigma
  “y W tblN l L n. ∃ T, !leafTDef T l ∧ ∃ e₁, !adjoinDef e₁ T 0 ∧ ∃ s₁, !mkStepDef s₁ W 41 e₁ ∧
    ∃ z, !qqFvarDef z l ∧ ∃ bL, !bnumGraph bL L ∧ ∃ v₁, !adjoinDef v₁ bL 0 ∧ ∃ v₂, !adjoinDef v₂ z v₁ ∧
    ∃ e₂, !adjoinDef e₂ T v₂ ∧ ∃ s₂, !mkStepDef s₂ W 105 e₂ ∧
    ∃ A, !leafFactDef A L n ∧ ∃ dA, !leafCodeDef dA tblN L n ∧ ∃ q, !pairDef q A dA ∧ ∃ s₃, !pairDef s₃ 7 q ∧
    ∃ bn, !bnumGraph bn n ∧ ∃ bL1, !qqAddGraph bL1 bL ↑(𝟏 : ℕ) ∧ ∃ w₁, !adjoinDef w₁ T 0 ∧
    ∃ w₂, !adjoinDef w₂ bL1 w₁ ∧ ∃ e₄, !adjoinDef e₄ bn w₂ ∧ ∃ s₄, !mkStepDef s₄ W 110 e₄ ∧
    ∃ r₄, !adjoinDef r₄ s₄ 0 ∧ ∃ r₃, !adjoinDef r₃ s₃ r₄ ∧ ∃ r₂, !adjoinDef r₂ s₂ r₃ ∧ !adjoinDef y s₁ r₂”

instance dlenLeafSteps_defined :
    𝚺₁-Function₅ (dlenLeafSteps : V → V → V → V → V → V) via dlenLeafStepsDef := .mk fun v ↦ by
  simp [dlenLeafStepsDef, dlenLeafSteps, leafT_defined.iff, leafFact_defined.iff, leafCode_defined.iff,
    bnum.defined.iff, mkStep_defined.iff, sLemma, numeral_eq_natCast]
instance dlenLeafSteps_definable :
    𝚺₁.DefinableFunction₅ (dlenLeafSteps : V → V → V → V → V → V) := dlenLeafSteps_defined.to_definable

noncomputable def dlenUnaryStepsDef : 𝚺₁.Semisentence 8 := .mkSigma
  “y W tblN l n₁ L m₁ n. ∃ T, !unaryTDef T l n₁ ∧ ∃ e₁, !adjoinDef e₁ T 0 ∧ ∃ s₁, !mkStepDef s₁ W 41 e₁ ∧
    ∃ zl, !qqFvarDef zl l ∧ ∃ zn, !qqFvarDef zn n₁ ∧ ∃ bL, !bnumGraph bL L ∧ ∃ bm, !bnumGraph bm m₁ ∧
    ∃ v₁, !adjoinDef v₁ bm 0 ∧ ∃ v₂, !adjoinDef v₂ bL v₁ ∧ ∃ v₃, !adjoinDef v₃ zn v₂ ∧
    ∃ v₄, !adjoinDef v₄ zl v₃ ∧ ∃ e₂, !adjoinDef e₂ T v₄ ∧ ∃ s₂, !mkStepDef s₂ W 106 e₂ ∧
    ∃ A, !bin2FactDef A L m₁ n ∧ ∃ dA, !bin2CodeDef dA tblN L m₁ n ∧ ∃ q, !pairDef q A dA ∧
    ∃ s₃, !pairDef s₃ 7 q ∧
    ∃ bn, !bnumGraph bn n ∧ ∃ sm, !qqAddGraph sm bL bm ∧ ∃ sm1, !qqAddGraph sm1 sm ↑(𝟏 : ℕ) ∧
    ∃ w₁, !adjoinDef w₁ T 0 ∧ ∃ w₂, !adjoinDef w₂ sm1 w₁ ∧ ∃ e₄, !adjoinDef e₄ bn w₂ ∧
    ∃ s₄, !mkStepDef s₄ W 110 e₄ ∧
    ∃ r₄, !adjoinDef r₄ s₄ 0 ∧ ∃ r₃, !adjoinDef r₃ s₃ r₄ ∧ ∃ r₂, !adjoinDef r₂ s₂ r₃ ∧ !adjoinDef y s₁ r₂”

instance dlenUnarySteps_defined :
    𝚺₁.DefinedFunction (fun v : Fin 7 → V ↦ dlenUnarySteps (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6))
      dlenUnaryStepsDef := .mk fun v ↦ by
  simp [dlenUnaryStepsDef, dlenUnarySteps, unaryT_defined.iff, bin2Fact_defined.iff, bin2Code_defined.iff,
    bnum.defined.iff, mkStep_defined.iff, sLemma, numeral_eq_natCast]
instance dlenUnarySteps_definable :
    𝚺₁.DefinableFunction (fun v : Fin 7 → V ↦ dlenUnarySteps (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6)) :=
  dlenUnarySteps_defined.to_definable

noncomputable def dlenBinaryStepsDef : 𝚺₁.Semisentence 10 := .mkSigma
  “y W tblN l n₁ n₂ L m₁ m₂ n. ∃ T, !binaryTDef T l n₁ n₂ ∧ ∃ e₁, !adjoinDef e₁ T 0 ∧
    ∃ s₁, !mkStepDef s₁ W 41 e₁ ∧
    ∃ zl, !qqFvarDef zl l ∧ ∃ za, !qqFvarDef za n₁ ∧ ∃ zb, !qqFvarDef zb n₂ ∧
    ∃ bL, !bnumGraph bL L ∧ ∃ ba, !bnumGraph ba m₁ ∧ ∃ bb, !bnumGraph bb m₂ ∧
    ∃ v₁, !adjoinDef v₁ bb 0 ∧ ∃ v₂, !adjoinDef v₂ ba v₁ ∧ ∃ v₃, !adjoinDef v₃ bL v₂ ∧
    ∃ v₄, !adjoinDef v₄ zb v₃ ∧ ∃ v₅, !adjoinDef v₅ za v₄ ∧ ∃ v₆, !adjoinDef v₆ zl v₅ ∧
    ∃ e₂, !adjoinDef e₂ T v₆ ∧ ∃ s₂, !mkStepDef s₂ W 107 e₂ ∧
    ∃ A, !bin3FactDef A L m₁ m₂ n ∧ ∃ dA, !bin3CodeDef dA tblN L m₁ m₂ n ∧ ∃ q, !pairDef q A dA ∧
    ∃ s₃, !pairDef s₃ 7 q ∧
    ∃ bn, !bnumGraph bn n ∧ ∃ p₁, !qqAddGraph p₁ bL ba ∧ ∃ p₂, !qqAddGraph p₂ p₁ bb ∧
    ∃ p₃, !qqAddGraph p₃ p₂ ↑(𝟏 : ℕ) ∧
    ∃ w₁, !adjoinDef w₁ T 0 ∧ ∃ w₂, !adjoinDef w₂ p₃ w₁ ∧ ∃ e₄, !adjoinDef e₄ bn w₂ ∧
    ∃ s₄, !mkStepDef s₄ W 110 e₄ ∧
    ∃ r₄, !adjoinDef r₄ s₄ 0 ∧ ∃ r₃, !adjoinDef r₃ s₃ r₄ ∧ ∃ r₂, !adjoinDef r₂ s₂ r₃ ∧ !adjoinDef y s₁ r₂”

instance dlenBinarySteps_defined :
    𝚺₁.DefinedFunction
      (fun v : Fin 9 → V ↦ dlenBinarySteps (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8))
      dlenBinaryStepsDef := .mk fun v ↦ by
  simp [dlenBinaryStepsDef, dlenBinarySteps, binaryT_defined.iff, bin3Fact_defined.iff, bin3Code_defined.iff,
    bnum.defined.iff, mkStep_defined.iff, sLemma, numeral_eq_natCast]
instance dlenBinarySteps_definable :
    𝚺₁.DefinableFunction
      (fun v : Fin 9 → V ↦ dlenBinarySteps (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8)) :=
  dlenBinarySteps_defined.to_definable

noncomputable def goalTailLeafDef : 𝚺₁.Semisentence 7 := .mkSigma
  “y W tblN l L n s. ∃ D, !dlenLeafStepsDef D W tblN l L n ∧ ∃ z, !qqFvarDef z 0 ∧ ∃ T, !leafTDef T l ∧
    ∃ zs, !qqFvarDef zs s ∧ ∃ bn, !bnumGraph bn n ∧ ∃ q₁, !pairDef q₁ zs bn ∧ ∃ q₂, !pairDef q₂ T q₁ ∧
    ∃ q₃, !pairDef q₃ z q₂ ∧ ∃ g, !pairDef g 6 q₃ ∧ ∃ e, !adjoinDef e g 0 ∧ !appendVDef y D e”

instance goalTailLeaf_defined :
    𝚺₁.DefinedFunction (fun v : Fin 6 → V ↦ goalTailLeaf (v 0) (v 1) (v 2) (v 3) (v 4) (v 5))
      goalTailLeafDef := .mk fun v ↦ by
  simp [goalTailLeafDef, goalTailLeaf, dlenLeafSteps_defined.iff, leafT_defined.iff, bnum.defined.iff,
    appendV_defined.iff, sGoal, numeral_eq_natCast]
instance goalTailLeaf_definable :
    𝚺₁.DefinableFunction (fun v : Fin 6 → V ↦ goalTailLeaf (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)) :=
  goalTailLeaf_defined.to_definable

noncomputable def goalTailUnaryDef : 𝚺₁.Semisentence 9 := .mkSigma
  “y W tblN l n₁ L m₁ n s. ∃ D, !dlenUnaryStepsDef D W tblN l n₁ L m₁ n ∧ ∃ z, !qqFvarDef z 0 ∧
    ∃ T, !unaryTDef T l n₁ ∧ ∃ zs, !qqFvarDef zs s ∧ ∃ bn, !bnumGraph bn n ∧ ∃ q₁, !pairDef q₁ zs bn ∧
    ∃ q₂, !pairDef q₂ T q₁ ∧ ∃ q₃, !pairDef q₃ z q₂ ∧ ∃ g, !pairDef g 6 q₃ ∧ ∃ e, !adjoinDef e g 0 ∧
    !appendVDef y D e”

instance goalTailUnary_defined :
    𝚺₁.DefinedFunction (fun v : Fin 8 → V ↦ goalTailUnary (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7))
      goalTailUnaryDef := .mk fun v ↦ by
  simp [goalTailUnaryDef, goalTailUnary, dlenUnarySteps_defined.iff, unaryT_defined.iff, bnum.defined.iff,
    appendV_defined.iff, sGoal, numeral_eq_natCast]
instance goalTailUnary_definable :
    𝚺₁.DefinableFunction
      (fun v : Fin 8 → V ↦ goalTailUnary (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7)) :=
  goalTailUnary_defined.to_definable

noncomputable def goalTailBinaryDef : 𝚺₁.Semisentence 11 := .mkSigma
  “y W tblN l n₁ n₂ L m₁ m₂ n s. ∃ D, !dlenBinaryStepsDef D W tblN l n₁ n₂ L m₁ m₂ n ∧ ∃ z, !qqFvarDef z 0 ∧
    ∃ T, !binaryTDef T l n₁ n₂ ∧ ∃ zs, !qqFvarDef zs s ∧ ∃ bn, !bnumGraph bn n ∧ ∃ q₁, !pairDef q₁ zs bn ∧
    ∃ q₂, !pairDef q₂ T q₁ ∧ ∃ q₃, !pairDef q₃ z q₂ ∧ ∃ g, !pairDef g 6 q₃ ∧ ∃ e, !adjoinDef e g 0 ∧
    !appendVDef y D e”

instance goalTailBinary_defined :
    𝚺₁.DefinedFunction
      (fun v : Fin 10 → V ↦
        goalTailBinary (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8) (v 9))
      goalTailBinaryDef := .mk fun v ↦ by
  simp [goalTailBinaryDef, goalTailBinary, dlenBinarySteps_defined.iff, binaryT_defined.iff, bnum.defined.iff,
    appendV_defined.iff, sGoal, numeral_eq_natCast]
instance goalTailBinary_definable :
    𝚺₁.DefinableFunction
      (fun v : Fin 10 → V ↦
        goalTailBinary (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8) (v 9)) :=
  goalTailBinary_defined.to_definable

end definability

end ArithS
