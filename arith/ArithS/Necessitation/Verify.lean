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

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
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

/-! ### 2.3 The ten `node<Tag>Head` lists -/

noncomputable def fragAxLHeadDef : 𝚺₁.Semisentence 6 := .mkSigma
  “y W is il ip inp.
    ∃ t0, !qqFvarDef t0 is ∧ ∃ t1, !qqFvarDef t1 ip ∧ ∃ t2, !qqFvarDef t2 (is + 1) ∧ ∃ t3, !qqFvarDef t3
    (ip + 1) ∧ ∃ z0, !qqFvarDef z0 0 ∧ ∃ t5, !qqFvarDef t5 (inp + 1) ∧ ∃ t6, !qqFvarDef t6 (il + 1) ∧ ∃
    e0_0, !adjoinDef e0_0 t1 0 ∧ ∃ e0_1, !adjoinDef e0_1 t0 e0_0 ∧ ∃ s0, !mkStepDef s0 W 87 e0_1 ∧ ∃
    e1_0, !adjoinDef e1_0 z0 0 ∧ ∃ e1_1, !adjoinDef e1_1 t3 e1_0 ∧ ∃ e1_2, !adjoinDef e1_2 t2 e1_1 ∧ ∃
    s1, !mkStepDef s1 W 116 e1_2 ∧ ∃ e2_0, !adjoinDef e2_0 z0 0 ∧ ∃ e2_1, !adjoinDef e2_1 t5 e2_0 ∧ ∃
    e2_2, !adjoinDef e2_2 t3 e2_1 ∧ ∃ e2_3, !adjoinDef e2_3 t2 e2_2 ∧ ∃ s2, !mkStepDef s2 W 93 e2_3 ∧ ∃
    e3_0, !adjoinDef e3_0 t6 0 ∧ ∃ e3_1, !adjoinDef e3_1 t3 e3_0 ∧ ∃ e3_2, !adjoinDef e3_2 t2 e3_1 ∧ ∃
    e3_3, !adjoinDef e3_3 z0 e3_2 ∧ ∃ s3, !mkStepDef s3 W 99 e3_3 ∧ ∃ r3, !adjoinDef r3 s3 0 ∧ ∃ r2,
    !adjoinDef r2 s2 r3 ∧ ∃ r1, !adjoinDef r1 s1 r2 ∧ !adjoinDef y s0 r1”

instance fragAxLHead_defined :
    𝚺₁.DefinedFunction (fun v : Fin 5 → V ↦ fragAxLHead (v 0) (v 1) (v 2) (v 3) (v 4)) fragAxLHeadDef := .mk fun v ↦ by
  simp [fragAxLHeadDef, fragAxLHead, mkStep_defined.iff, numeral_eq_natCast]
instance fragAxLHead_definable :
    𝚺₁.DefinableFunction (fun v : Fin 5 → V ↦ fragAxLHead (v 0) (v 1) (v 2) (v 3) (v 4)) := fragAxLHead_defined.to_definable


noncomputable def fragVerumHeadDef : 𝚺₁.Semisentence 5 := .mkSigma
  “y W is il iv.
    ∃ t0, !qqFvarDef t0 is ∧ ∃ t1, !qqFvarDef t1 (is + 1) ∧ ∃ z0, !qqFvarDef z0 0 ∧ ∃ t3, !qqFvarDef t3
    (iv + 1) ∧ ∃ t4, !qqFvarDef t4 (il + 1) ∧ ∃ e0_0, !adjoinDef e0_0 t0 0 ∧ ∃ s0, !mkStepDef s0 W 88
    e0_0 ∧ ∃ e1_0, !adjoinDef e1_0 z0 0 ∧ ∃ e1_1, !adjoinDef e1_1 t1 e1_0 ∧ ∃ s1, !mkStepDef s1 W 117
    e1_1 ∧ ∃ e2_0, !adjoinDef e2_0 z0 0 ∧ ∃ e2_1, !adjoinDef e2_1 t3 e2_0 ∧ ∃ e2_2, !adjoinDef e2_2 t1
    e2_1 ∧ ∃ s2, !mkStepDef s2 W 94 e2_2 ∧ ∃ e3_0, !adjoinDef e3_0 t4 0 ∧ ∃ e3_1, !adjoinDef e3_1 t1 e3_0
    ∧ ∃ e3_2, !adjoinDef e3_2 z0 e3_1 ∧ ∃ s3, !mkStepDef s3 W 100 e3_2 ∧ ∃ r3, !adjoinDef r3 s3 0 ∧ ∃ r2,
    !adjoinDef r2 s2 r3 ∧ ∃ r1, !adjoinDef r1 s1 r2 ∧ !adjoinDef y s0 r1”

instance fragVerumHead_defined :
    𝚺₁.DefinedFunction (fun v : Fin 4 → V ↦ fragVerumHead (v 0) (v 1) (v 2) (v 3)) fragVerumHeadDef := .mk fun v ↦ by
  simp [fragVerumHeadDef, fragVerumHead, mkStep_defined.iff, numeral_eq_natCast]
instance fragVerumHead_definable :
    𝚺₁.DefinableFunction (fun v : Fin 4 → V ↦ fragVerumHead (v 0) (v 1) (v 2) (v 3)) := fragVerumHead_defined.to_definable


noncomputable def nodeAndHeadDef : 𝚺₁.Semisentence 13 := .mkSigma
  “y W is il ir ip iq id1 id2 icp icq in1 in2.
    ∃ t0, !qqFvarDef t0 is ∧ ∃ t1, !qqFvarDef t1 ip ∧ ∃ t2, !qqFvarDef t2 iq ∧ ∃ t3, !qqFvarDef t3 id1 ∧
    ∃ t4, !qqFvarDef t4 id2 ∧ ∃ t5, !qqFvarDef t5 (is + 1) ∧ ∃ t6, !qqFvarDef t6 (ip + 1) ∧ ∃ t7,
    !qqFvarDef t7 (iq + 1) ∧ ∃ t8, !qqFvarDef t8 (id1 + 1) ∧ ∃ t9, !qqFvarDef t9 (id2 + 1) ∧ ∃ z0,
    !qqFvarDef z0 0 ∧ ∃ t11, !qqFvarDef t11 (ir + 1) ∧ ∃ t12, !qqFvarDef t12 (icp + 1) ∧ ∃ t13,
    !qqFvarDef t13 (icq + 1) ∧ ∃ t14, !qqFvarDef t14 (in1 + 1) ∧ ∃ t15, !qqFvarDef t15 (in2 + 1) ∧ ∃ t16,
    !qqFvarDef t16 (il + 1) ∧ ∃ e0_0, !adjoinDef e0_0 t4 0 ∧ ∃ e0_1, !adjoinDef e0_1 t3 e0_0 ∧ ∃ e0_2,
    !adjoinDef e0_2 t2 e0_1 ∧ ∃ e0_3, !adjoinDef e0_3 t1 e0_2 ∧ ∃ e0_4, !adjoinDef e0_4 t0 e0_3 ∧ ∃ s0,
    !mkStepDef s0 W 89 e0_4 ∧ ∃ e1_0, !adjoinDef e1_0 z0 0 ∧ ∃ e1_1, !adjoinDef e1_1 t9 e1_0 ∧ ∃ e1_2,
    !adjoinDef e1_2 t8 e1_1 ∧ ∃ e1_3, !adjoinDef e1_3 t7 e1_2 ∧ ∃ e1_4, !adjoinDef e1_4 t6 e1_3 ∧ ∃ e1_5,
    !adjoinDef e1_5 t5 e1_4 ∧ ∃ s1, !mkStepDef s1 W 118 e1_5 ∧ ∃ e2_0, !adjoinDef e2_0 z0 0 ∧ ∃ e2_1,
    !adjoinDef e2_1 t13 e2_0 ∧ ∃ e2_2, !adjoinDef e2_2 t12 e2_1 ∧ ∃ e2_3, !adjoinDef e2_3 t11 e2_2 ∧ ∃
    e2_4, !adjoinDef e2_4 t9 e2_3 ∧ ∃ e2_5, !adjoinDef e2_5 t8 e2_4 ∧ ∃ e2_6, !adjoinDef e2_6 t7 e2_5 ∧ ∃
    e2_7, !adjoinDef e2_7 t6 e2_6 ∧ ∃ e2_8, !adjoinDef e2_8 t5 e2_7 ∧ ∃ s2, !mkStepDef s2 W 95 e2_8 ∧ ∃
    e3_0, !adjoinDef e3_0 t16 0 ∧ ∃ e3_1, !adjoinDef e3_1 t15 e3_0 ∧ ∃ e3_2, !adjoinDef e3_2 t14 e3_1 ∧ ∃
    e3_3, !adjoinDef e3_3 t9 e3_2 ∧ ∃ e3_4, !adjoinDef e3_4 t8 e3_3 ∧ ∃ e3_5, !adjoinDef e3_5 t7 e3_4 ∧ ∃
    e3_6, !adjoinDef e3_6 t6 e3_5 ∧ ∃ e3_7, !adjoinDef e3_7 t5 e3_6 ∧ ∃ e3_8, !adjoinDef e3_8 z0 e3_7 ∧ ∃
    s3, !mkStepDef s3 W 101 e3_8 ∧ ∃ r3, !adjoinDef r3 s3 0 ∧ ∃ r2, !adjoinDef r2 s2 r3 ∧ ∃ r1,
    !adjoinDef r1 s1 r2 ∧ !adjoinDef y s0 r1”

instance nodeAndHead_defined :
    𝚺₁.DefinedFunction (fun v : Fin 12 → V ↦ nodeAndHead (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8) (v 9) (v 10) (v 11)) nodeAndHeadDef := .mk fun v ↦ by
  simp [nodeAndHeadDef, nodeAndHead, mkStep_defined.iff, numeral_eq_natCast]
instance nodeAndHead_definable :
    𝚺₁.DefinableFunction (fun v : Fin 12 → V ↦ nodeAndHead (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8) (v 9) (v 10) (v 11)) := nodeAndHead_defined.to_definable


noncomputable def nodeOrHeadDef : 𝚺₁.Semisentence 11 := .mkSigma
  “y W is il ir ip iq id icq ic in1.
    ∃ t0, !qqFvarDef t0 is ∧ ∃ t1, !qqFvarDef t1 ip ∧ ∃ t2, !qqFvarDef t2 iq ∧ ∃ t3, !qqFvarDef t3 id ∧ ∃
    t4, !qqFvarDef t4 (is + 1) ∧ ∃ t5, !qqFvarDef t5 (ip + 1) ∧ ∃ t6, !qqFvarDef t6 (iq + 1) ∧ ∃ t7,
    !qqFvarDef t7 (id + 1) ∧ ∃ z0, !qqFvarDef z0 0 ∧ ∃ t9, !qqFvarDef t9 (ir + 1) ∧ ∃ t10, !qqFvarDef t10
    (icq + 1) ∧ ∃ t11, !qqFvarDef t11 (ic + 1) ∧ ∃ t12, !qqFvarDef t12 (in1 + 1) ∧ ∃ t13, !qqFvarDef t13
    (il + 1) ∧ ∃ e0_0, !adjoinDef e0_0 t3 0 ∧ ∃ e0_1, !adjoinDef e0_1 t2 e0_0 ∧ ∃ e0_2, !adjoinDef e0_2
    t1 e0_1 ∧ ∃ e0_3, !adjoinDef e0_3 t0 e0_2 ∧ ∃ s0, !mkStepDef s0 W 90 e0_3 ∧ ∃ e1_0, !adjoinDef e1_0
    z0 0 ∧ ∃ e1_1, !adjoinDef e1_1 t7 e1_0 ∧ ∃ e1_2, !adjoinDef e1_2 t6 e1_1 ∧ ∃ e1_3, !adjoinDef e1_3 t5
    e1_2 ∧ ∃ e1_4, !adjoinDef e1_4 t4 e1_3 ∧ ∃ s1, !mkStepDef s1 W 119 e1_4 ∧ ∃ e2_0, !adjoinDef e2_0 z0
    0 ∧ ∃ e2_1, !adjoinDef e2_1 t11 e2_0 ∧ ∃ e2_2, !adjoinDef e2_2 t10 e2_1 ∧ ∃ e2_3, !adjoinDef e2_3 t9
    e2_2 ∧ ∃ e2_4, !adjoinDef e2_4 t7 e2_3 ∧ ∃ e2_5, !adjoinDef e2_5 t6 e2_4 ∧ ∃ e2_6, !adjoinDef e2_6 t5
    e2_5 ∧ ∃ e2_7, !adjoinDef e2_7 t4 e2_6 ∧ ∃ s2, !mkStepDef s2 W 96 e2_7 ∧ ∃ e3_0, !adjoinDef e3_0 t13
    0 ∧ ∃ e3_1, !adjoinDef e3_1 t12 e3_0 ∧ ∃ e3_2, !adjoinDef e3_2 t7 e3_1 ∧ ∃ e3_3, !adjoinDef e3_3 t6
    e3_2 ∧ ∃ e3_4, !adjoinDef e3_4 t5 e3_3 ∧ ∃ e3_5, !adjoinDef e3_5 t4 e3_4 ∧ ∃ e3_6, !adjoinDef e3_6 z0
    e3_5 ∧ ∃ s3, !mkStepDef s3 W 102 e3_6 ∧ ∃ r3, !adjoinDef r3 s3 0 ∧ ∃ r2, !adjoinDef r2 s2 r3 ∧ ∃ r1,
    !adjoinDef r1 s1 r2 ∧ !adjoinDef y s0 r1”

instance nodeOrHead_defined :
    𝚺₁.DefinedFunction (fun v : Fin 10 → V ↦ nodeOrHead (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8) (v 9)) nodeOrHeadDef := .mk fun v ↦ by
  simp [nodeOrHeadDef, nodeOrHead, mkStep_defined.iff, numeral_eq_natCast]
instance nodeOrHead_definable :
    𝚺₁.DefinableFunction (fun v : Fin 10 → V ↦ nodeOrHead (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8) (v 9)) := nodeOrHead_defined.to_definable


noncomputable def nodeWkHeadDef : 𝚺₁.Semisentence 7 := .mkSigma
  “y W is il ic id in1.
    ∃ t0, !qqFvarDef t0 is ∧ ∃ t1, !qqFvarDef t1 id ∧ ∃ t2, !qqFvarDef t2 (is + 1) ∧ ∃ t3, !qqFvarDef t3
    (id + 1) ∧ ∃ z0, !qqFvarDef z0 0 ∧ ∃ t5, !qqFvarDef t5 (ic + 1) ∧ ∃ t6, !qqFvarDef t6 (in1 + 1) ∧ ∃
    t7, !qqFvarDef t7 (il + 1) ∧ ∃ e0_0, !adjoinDef e0_0 t1 0 ∧ ∃ e0_1, !adjoinDef e0_1 t0 e0_0 ∧ ∃ s0,
    !mkStepDef s0 W 91 e0_1 ∧ ∃ e1_0, !adjoinDef e1_0 z0 0 ∧ ∃ e1_1, !adjoinDef e1_1 t3 e1_0 ∧ ∃ e1_2,
    !adjoinDef e1_2 t2 e1_1 ∧ ∃ s1, !mkStepDef s1 W 120 e1_2 ∧ ∃ e2_0, !adjoinDef e2_0 z0 0 ∧ ∃ e2_1,
    !adjoinDef e2_1 t5 e2_0 ∧ ∃ e2_2, !adjoinDef e2_2 t3 e2_1 ∧ ∃ e2_3, !adjoinDef e2_3 t2 e2_2 ∧ ∃ s2,
    !mkStepDef s2 W 97 e2_3 ∧ ∃ e3_0, !adjoinDef e3_0 t7 0 ∧ ∃ e3_1, !adjoinDef e3_1 t6 e3_0 ∧ ∃ e3_2,
    !adjoinDef e3_2 t3 e3_1 ∧ ∃ e3_3, !adjoinDef e3_3 t2 e3_2 ∧ ∃ e3_4, !adjoinDef e3_4 z0 e3_3 ∧ ∃ s3,
    !mkStepDef s3 W 103 e3_4 ∧ ∃ r3, !adjoinDef r3 s3 0 ∧ ∃ r2, !adjoinDef r2 s2 r3 ∧ ∃ r1, !adjoinDef r1
    s1 r2 ∧ !adjoinDef y s0 r1”

instance nodeWkHead_defined :
    𝚺₁.DefinedFunction (fun v : Fin 6 → V ↦ nodeWkHead (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)) nodeWkHeadDef := .mk fun v ↦ by
  simp [nodeWkHeadDef, nodeWkHead, mkStep_defined.iff, numeral_eq_natCast]
instance nodeWkHead_definable :
    𝚺₁.DefinableFunction (fun v : Fin 6 → V ↦ nodeWkHead (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)) := nodeWkHead_defined.to_definable


noncomputable def nodeCutHeadDef : 𝚺₁.Semisentence 12 := .mkSigma
  “y W is il ip inp id1 id2 ic1 ic2 in1 in2.
    ∃ t0, !qqFvarDef t0 is ∧ ∃ t1, !qqFvarDef t1 ip ∧ ∃ t2, !qqFvarDef t2 id1 ∧ ∃ t3, !qqFvarDef t3 id2 ∧
    ∃ t4, !qqFvarDef t4 (is + 1) ∧ ∃ t5, !qqFvarDef t5 (ip + 1) ∧ ∃ t6, !qqFvarDef t6 (id1 + 1) ∧ ∃ t7,
    !qqFvarDef t7 (id2 + 1) ∧ ∃ z0, !qqFvarDef z0 0 ∧ ∃ t9, !qqFvarDef t9 (ic1 + 1) ∧ ∃ t10, !qqFvarDef
    t10 (inp + 1) ∧ ∃ t11, !qqFvarDef t11 (ic2 + 1) ∧ ∃ t12, !qqFvarDef t12 (in1 + 1) ∧ ∃ t13, !qqFvarDef
    t13 (in2 + 1) ∧ ∃ t14, !qqFvarDef t14 (il + 1) ∧ ∃ e0_0, !adjoinDef e0_0 t3 0 ∧ ∃ e0_1, !adjoinDef
    e0_1 t2 e0_0 ∧ ∃ e0_2, !adjoinDef e0_2 t1 e0_1 ∧ ∃ e0_3, !adjoinDef e0_3 t0 e0_2 ∧ ∃ s0, !mkStepDef
    s0 W 92 e0_3 ∧ ∃ e1_0, !adjoinDef e1_0 z0 0 ∧ ∃ e1_1, !adjoinDef e1_1 t7 e1_0 ∧ ∃ e1_2, !adjoinDef
    e1_2 t6 e1_1 ∧ ∃ e1_3, !adjoinDef e1_3 t5 e1_2 ∧ ∃ e1_4, !adjoinDef e1_4 t4 e1_3 ∧ ∃ s1, !mkStepDef
    s1 W 121 e1_4 ∧ ∃ e2_0, !adjoinDef e2_0 z0 0 ∧ ∃ e2_1, !adjoinDef e2_1 t11 e2_0 ∧ ∃ e2_2, !adjoinDef
    e2_2 t10 e2_1 ∧ ∃ e2_3, !adjoinDef e2_3 t9 e2_2 ∧ ∃ e2_4, !adjoinDef e2_4 t7 e2_3 ∧ ∃ e2_5,
    !adjoinDef e2_5 t6 e2_4 ∧ ∃ e2_6, !adjoinDef e2_6 t5 e2_5 ∧ ∃ e2_7, !adjoinDef e2_7 t4 e2_6 ∧ ∃ e2_8,
    !adjoinDef e2_8 ↑Arithmetic.zero e2_7 ∧ ∃ s2, !mkStepDef s2 W 98 e2_8 ∧ ∃ e3_0, !adjoinDef e3_0 t14 0
    ∧ ∃ e3_1, !adjoinDef e3_1 t13 e3_0 ∧ ∃ e3_2, !adjoinDef e3_2 t12 e3_1 ∧ ∃ e3_3, !adjoinDef e3_3 t7
    e3_2 ∧ ∃ e3_4, !adjoinDef e3_4 t6 e3_3 ∧ ∃ e3_5, !adjoinDef e3_5 t5 e3_4 ∧ ∃ e3_6, !adjoinDef e3_6 t4
    e3_5 ∧ ∃ e3_7, !adjoinDef e3_7 z0 e3_6 ∧ ∃ s3, !mkStepDef s3 W 104 e3_7 ∧ ∃ r3, !adjoinDef r3 s3 0 ∧
    ∃ r2, !adjoinDef r2 s2 r3 ∧ ∃ r1, !adjoinDef r1 s1 r2 ∧ !adjoinDef y s0 r1”

instance nodeCutHead_defined :
    𝚺₁.DefinedFunction (fun v : Fin 11 → V ↦ nodeCutHead (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8) (v 9) (v 10)) nodeCutHeadDef := .mk fun v ↦ by
  simp [nodeCutHeadDef, nodeCutHead, mkStep_defined.iff, numeral_eq_natCast]
instance nodeCutHead_definable :
    𝚺₁.DefinableFunction (fun v : Fin 11 → V ↦ nodeCutHead (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8) (v 9) (v 10)) := nodeCutHead_defined.to_definable


noncomputable def nodeShiftHeadDef : 𝚺₁.Semisentence 7 := .mkSigma
  “y W is il ic id in1.
    ∃ t0, !qqFvarDef t0 is ∧ ∃ t1, !qqFvarDef t1 id ∧ ∃ t2, !qqFvarDef t2 (is + 1) ∧ ∃ t3, !qqFvarDef t3
    (id + 1) ∧ ∃ z0, !qqFvarDef z0 0 ∧ ∃ t5, !qqFvarDef t5 (ic + 1) ∧ ∃ t6, !qqFvarDef t6 (in1 + 1) ∧ ∃
    t7, !qqFvarDef t7 (il + 1) ∧ ∃ e0_0, !adjoinDef e0_0 t1 0 ∧ ∃ e0_1, !adjoinDef e0_1 t0 e0_0 ∧ ∃ s0,
    !mkStepDef s0 W 128 e0_1 ∧ ∃ e1_0, !adjoinDef e1_0 z0 0 ∧ ∃ e1_1, !adjoinDef e1_1 t3 e1_0 ∧ ∃ e1_2,
    !adjoinDef e1_2 t2 e1_1 ∧ ∃ s1, !mkStepDef s1 W 142 e1_2 ∧ ∃ e2_0, !adjoinDef e2_0 z0 0 ∧ ∃ e2_1,
    !adjoinDef e2_1 t2 e2_0 ∧ ∃ e2_2, !adjoinDef e2_2 t5 e2_1 ∧ ∃ e2_3, !adjoinDef e2_3 t3 e2_2 ∧ ∃ s2,
    !mkStepDef s2 W 132 e2_3 ∧ ∃ e3_0, !adjoinDef e3_0 t7 0 ∧ ∃ e3_1, !adjoinDef e3_1 t6 e3_0 ∧ ∃ e3_2,
    !adjoinDef e3_2 t3 e3_1 ∧ ∃ e3_3, !adjoinDef e3_3 t2 e3_2 ∧ ∃ e3_4, !adjoinDef e3_4 z0 e3_3 ∧ ∃ s3,
    !mkStepDef s3 W 135 e3_4 ∧ ∃ r3, !adjoinDef r3 s3 0 ∧ ∃ r2, !adjoinDef r2 s2 r3 ∧ ∃ r1, !adjoinDef r1
    s1 r2 ∧ !adjoinDef y s0 r1”

instance nodeShiftHead_defined :
    𝚺₁.DefinedFunction (fun v : Fin 6 → V ↦ nodeShiftHead (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)) nodeShiftHeadDef := .mk fun v ↦ by
  simp [nodeShiftHeadDef, nodeShiftHead, mkStep_defined.iff, numeral_eq_natCast]
instance nodeShiftHead_definable :
    𝚺₁.DefinableFunction (fun v : Fin 6 → V ↦ nodeShiftHead (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)) := nodeShiftHead_defined.to_definable


noncomputable def nodeAllHeadDef : 𝚺₁.Semisentence 11 := .mkSigma
  “y W is il ir ip ifp iss ic id in1.
    ∃ t0, !qqFvarDef t0 is ∧ ∃ t1, !qqFvarDef t1 ip ∧ ∃ t2, !qqFvarDef t2 id ∧ ∃ t3, !qqFvarDef t3 (is +
    1) ∧ ∃ t4, !qqFvarDef t4 (ip + 1) ∧ ∃ t5, !qqFvarDef t5 (id + 1) ∧ ∃ z0, !qqFvarDef z0 0 ∧ ∃ t7,
    !qqFvarDef t7 (ir + 1) ∧ ∃ t8, !qqFvarDef t8 (ifp + 1) ∧ ∃ t9, !qqFvarDef t9 (iss + 1) ∧ ∃ t10,
    !qqFvarDef t10 (ic + 1) ∧ ∃ t11, !qqFvarDef t11 (in1 + 1) ∧ ∃ t12, !qqFvarDef t12 (il + 1) ∧ ∃ e0_0,
    !adjoinDef e0_0 t2 0 ∧ ∃ e0_1, !adjoinDef e0_1 t1 e0_0 ∧ ∃ e0_2, !adjoinDef e0_2 t0 e0_1 ∧ ∃ s0,
    !mkStepDef s0 W 126 e0_2 ∧ ∃ e1_0, !adjoinDef e1_0 z0 0 ∧ ∃ e1_1, !adjoinDef e1_1 t5 e1_0 ∧ ∃ e1_2,
    !adjoinDef e1_2 t4 e1_1 ∧ ∃ e1_3, !adjoinDef e1_3 t3 e1_2 ∧ ∃ s1, !mkStepDef s1 W 140 e1_3 ∧ ∃ e2_0,
    !adjoinDef e2_0 z0 0 ∧ ∃ e2_1, !adjoinDef e2_1 t10 e2_0 ∧ ∃ e2_2, !adjoinDef e2_2 t9 e2_1 ∧ ∃ e2_3,
    !adjoinDef e2_3 t8 e2_2 ∧ ∃ e2_4, !adjoinDef e2_4 t7 e2_3 ∧ ∃ e2_5, !adjoinDef e2_5 t5 e2_4 ∧ ∃ e2_6,
    !adjoinDef e2_6 t4 e2_5 ∧ ∃ e2_7, !adjoinDef e2_7 t3 e2_6 ∧ ∃ s2, !mkStepDef s2 W 130 e2_7 ∧ ∃ e3_0,
    !adjoinDef e3_0 t12 0 ∧ ∃ e3_1, !adjoinDef e3_1 t11 e3_0 ∧ ∃ e3_2, !adjoinDef e3_2 t5 e3_1 ∧ ∃ e3_3,
    !adjoinDef e3_3 t4 e3_2 ∧ ∃ e3_4, !adjoinDef e3_4 t3 e3_3 ∧ ∃ e3_5, !adjoinDef e3_5 z0 e3_4 ∧ ∃ s3,
    !mkStepDef s3 W 133 e3_5 ∧ ∃ r3, !adjoinDef r3 s3 0 ∧ ∃ r2, !adjoinDef r2 s2 r3 ∧ ∃ r1, !adjoinDef r1
    s1 r2 ∧ !adjoinDef y s0 r1”

instance nodeAllHead_defined :
    𝚺₁.DefinedFunction (fun v : Fin 10 → V ↦ nodeAllHead (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8) (v 9)) nodeAllHeadDef := .mk fun v ↦ by
  simp [nodeAllHeadDef, nodeAllHead, mkStep_defined.iff, numeral_eq_natCast]
instance nodeAllHead_definable :
    𝚺₁.DefinableFunction (fun v : Fin 10 → V ↦ nodeAllHead (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8) (v 9)) := nodeAllHead_defined.to_definable


noncomputable def nodeExsHeadDef : 𝚺₁.Semisentence 12 := .mkSigma
  “y W is il ir ip it ipt ic id ilt in1.
    ∃ t0, !qqFvarDef t0 is ∧ ∃ t1, !qqFvarDef t1 ip ∧ ∃ t2, !qqFvarDef t2 it ∧ ∃ t3, !qqFvarDef t3 id ∧ ∃
    t4, !qqFvarDef t4 (is + 1) ∧ ∃ t5, !qqFvarDef t5 (ip + 1) ∧ ∃ t6, !qqFvarDef t6 (it + 1) ∧ ∃ t7,
    !qqFvarDef t7 (id + 1) ∧ ∃ z0, !qqFvarDef z0 0 ∧ ∃ t9, !qqFvarDef t9 (ir + 1) ∧ ∃ t10, !qqFvarDef t10
    (ipt + 1) ∧ ∃ t11, !qqFvarDef t11 (ic + 1) ∧ ∃ t12, !qqFvarDef t12 (in1 + 1) ∧ ∃ t13, !qqFvarDef t13
    (il + 1) ∧ ∃ t14, !qqFvarDef t14 (ilt + 1) ∧ ∃ e0_0, !adjoinDef e0_0 t3 0 ∧ ∃ e0_1, !adjoinDef e0_1
    t2 e0_0 ∧ ∃ e0_2, !adjoinDef e0_2 t1 e0_1 ∧ ∃ e0_3, !adjoinDef e0_3 t0 e0_2 ∧ ∃ s0, !mkStepDef s0 W
    127 e0_3 ∧ ∃ e1_0, !adjoinDef e1_0 z0 0 ∧ ∃ e1_1, !adjoinDef e1_1 t7 e1_0 ∧ ∃ e1_2, !adjoinDef e1_2
    t6 e1_1 ∧ ∃ e1_3, !adjoinDef e1_3 t5 e1_2 ∧ ∃ e1_4, !adjoinDef e1_4 t4 e1_3 ∧ ∃ s1, !mkStepDef s1 W
    141 e1_4 ∧ ∃ e2_0, !adjoinDef e2_0 z0 0 ∧ ∃ e2_1, !adjoinDef e2_1 t11 e2_0 ∧ ∃ e2_2, !adjoinDef e2_2
    t10 e2_1 ∧ ∃ e2_3, !adjoinDef e2_3 t9 e2_2 ∧ ∃ e2_4, !adjoinDef e2_4 t7 e2_3 ∧ ∃ e2_5, !adjoinDef
    e2_5 t6 e2_4 ∧ ∃ e2_6, !adjoinDef e2_6 t5 e2_5 ∧ ∃ e2_7, !adjoinDef e2_7 t4 e2_6 ∧ ∃ e2_8, !adjoinDef
    e2_8 ↑Arithmetic.zero e2_7 ∧ ∃ s2, !mkStepDef s2 W 131 e2_8 ∧ ∃ e3_0, !adjoinDef e3_0 t14 0 ∧ ∃ e3_1,
    !adjoinDef e3_1 t13 e3_0 ∧ ∃ e3_2, !adjoinDef e3_2 t12 e3_1 ∧ ∃ e3_3, !adjoinDef e3_3 t7 e3_2 ∧ ∃
    e3_4, !adjoinDef e3_4 t6 e3_3 ∧ ∃ e3_5, !adjoinDef e3_5 t5 e3_4 ∧ ∃ e3_6, !adjoinDef e3_6 t4 e3_5 ∧ ∃
    e3_7, !adjoinDef e3_7 z0 e3_6 ∧ ∃ s3, !mkStepDef s3 W 134 e3_7 ∧ ∃ r3, !adjoinDef r3 s3 0 ∧ ∃ r2,
    !adjoinDef r2 s2 r3 ∧ ∃ r1, !adjoinDef r1 s1 r2 ∧ !adjoinDef y s0 r1”

instance nodeExsHead_defined :
    𝚺₁.DefinedFunction (fun v : Fin 11 → V ↦ nodeExsHead (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8) (v 9) (v 10)) nodeExsHeadDef := .mk fun v ↦ by
  simp [nodeExsHeadDef, nodeExsHead, mkStep_defined.iff, numeral_eq_natCast]
instance nodeExsHead_definable :
    𝚺₁.DefinableFunction (fun v : Fin 11 → V ↦ nodeExsHead (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8) (v 9) (v 10)) := nodeExsHead_defined.to_definable


noncomputable def nodeAxmHeadDef : 𝚺₁.Semisentence 5 := .mkSigma
  “y W is il ip.
    ∃ t0, !qqFvarDef t0 is ∧ ∃ t1, !qqFvarDef t1 ip ∧ ∃ t2, !qqFvarDef t2 (is + 1) ∧ ∃ t3, !qqFvarDef t3
    (ip + 1) ∧ ∃ z0, !qqFvarDef z0 0 ∧ ∃ t5, !qqFvarDef t5 (il + 1) ∧ ∃ e0_0, !adjoinDef e0_0 t1 0 ∧ ∃
    e0_1, !adjoinDef e0_1 t0 e0_0 ∧ ∃ s0, !mkStepDef s0 W 129 e0_1 ∧ ∃ e1_0, !adjoinDef e1_0 z0 0 ∧ ∃
    e1_1, !adjoinDef e1_1 t3 e1_0 ∧ ∃ e1_2, !adjoinDef e1_2 t2 e1_1 ∧ ∃ s1, !mkStepDef s1 W 143 e1_2 ∧ ∃
    e2_0, !adjoinDef e2_0 z0 0 ∧ ∃ e2_1, !adjoinDef e2_1 t3 e2_0 ∧ ∃ e2_2, !adjoinDef e2_2 t2 e2_1 ∧ ∃
    s2, !mkStepDef s2 W 137 e2_2 ∧ ∃ e3_0, !adjoinDef e3_0 t5 0 ∧ ∃ e3_1, !adjoinDef e3_1 t3 e3_0 ∧ ∃
    e3_2, !adjoinDef e3_2 t2 e3_1 ∧ ∃ e3_3, !adjoinDef e3_3 z0 e3_2 ∧ ∃ s3, !mkStepDef s3 W 136 e3_3 ∧ ∃
    r3, !adjoinDef r3 s3 0 ∧ ∃ r2, !adjoinDef r2 s2 r3 ∧ ∃ r1, !adjoinDef r1 s1 r2 ∧ !adjoinDef y s0 r1”

instance nodeAxmHead_defined :
    𝚺₁.DefinedFunction (fun v : Fin 4 → V ↦ nodeAxmHead (v 0) (v 1) (v 2) (v 3)) nodeAxmHeadDef := .mk fun v ↦ by
  simp [nodeAxmHeadDef, nodeAxmHead, mkStep_defined.iff, numeral_eq_natCast]
instance nodeAxmHead_definable :
    𝚺₁.DefinableFunction (fun v : Fin 4 → V ↦ nodeAxmHead (v 0) (v 1) (v 2) (v 3)) := nodeAxmHead_defined.to_definable

/-! ### 2.4 The ten fragments -/

noncomputable def fragAxLDef : 𝚺₁.Semisentence 9 := .mkSigma
  “y W tblN is il ip inp L n.
    ∃ H, !fragAxLHeadDef H W is il ip inp ∧ ∃ T, !goalTailLeafDef T W tblN (il + 1) L n (is + 1) ∧
    !appendVDef y H T”

instance fragAxL_defined :
    𝚺₁.DefinedFunction (fun v : Fin 8 → V ↦ fragAxL (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7)) fragAxLDef := .mk fun v ↦ by
  simp [fragAxLDef, fragAxL, fragAxLHead_defined.iff, goalTailLeaf_defined.iff, appendV_defined.iff,
    numeral_eq_natCast]
instance fragAxL_definable :
    𝚺₁.DefinableFunction (fun v : Fin 8 → V ↦ fragAxL (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7)) := fragAxL_defined.to_definable

noncomputable def fragVerumDef : 𝚺₁.Semisentence 8 := .mkSigma
  “y W tblN is il iv L n.
    ∃ H, !fragVerumHeadDef H W is il iv ∧ ∃ T, !goalTailLeafDef T W tblN (il + 1) L n (is + 1) ∧
    !appendVDef y H T”

instance fragVerum_defined :
    𝚺₁.DefinedFunction (fun v : Fin 7 → V ↦ fragVerum (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6)) fragVerumDef := .mk fun v ↦ by
  simp [fragVerumDef, fragVerum, fragVerumHead_defined.iff, goalTailLeaf_defined.iff, appendV_defined.iff,
    numeral_eq_natCast]
instance fragVerum_definable :
    𝚺₁.DefinableFunction (fun v : Fin 7 → V ↦ fragVerum (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6)) := fragVerum_defined.to_definable

noncomputable def nodeAndDef : 𝚺₁.Semisentence 18 := .mkSigma
  “y W tblN is il ir ip iq id1 id2 icp icq in1 in2 L m1 m2 n.
    ∃ H, !nodeAndHeadDef H W is il ir ip iq id1 id2 icp icq in1 in2 ∧ ∃ T, !goalTailBinaryDef T W tblN
    (il + 1) (in1 + 1) (in2 + 1) L m1 m2 n (is + 1) ∧ !appendVDef y H T”

instance nodeAnd_defined :
    𝚺₁.DefinedFunction (fun v : Fin 17 → V ↦ nodeAnd (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8) (v 9) (v 10) (v 11) (v 12) (v 13) (v 14) (v 15) (v 16)) nodeAndDef := .mk fun v ↦ by
  simp [nodeAndDef, nodeAnd, nodeAndHead_defined.iff, goalTailBinary_defined.iff, appendV_defined.iff,
    numeral_eq_natCast]
instance nodeAnd_definable :
    𝚺₁.DefinableFunction (fun v : Fin 17 → V ↦ nodeAnd (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8) (v 9) (v 10) (v 11) (v 12) (v 13) (v 14) (v 15) (v 16)) := nodeAnd_defined.to_definable

noncomputable def nodeOrDef : 𝚺₁.Semisentence 15 := .mkSigma
  “y W tblN is il ir ip iq id icq ic in1 L m1 n.
    ∃ H, !nodeOrHeadDef H W is il ir ip iq id icq ic in1 ∧ ∃ T, !goalTailUnaryDef T W tblN (il + 1) (in1
    + 1) L m1 n (is + 1) ∧ !appendVDef y H T”

instance nodeOr_defined :
    𝚺₁.DefinedFunction (fun v : Fin 14 → V ↦ nodeOr (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8) (v 9) (v 10) (v 11) (v 12) (v 13)) nodeOrDef := .mk fun v ↦ by
  simp [nodeOrDef, nodeOr, nodeOrHead_defined.iff, goalTailUnary_defined.iff, appendV_defined.iff,
    numeral_eq_natCast]
instance nodeOr_definable :
    𝚺₁.DefinableFunction (fun v : Fin 14 → V ↦ nodeOr (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8) (v 9) (v 10) (v 11) (v 12) (v 13)) := nodeOr_defined.to_definable

noncomputable def nodeWkDef : 𝚺₁.Semisentence 11 := .mkSigma
  “y W tblN is il ic id in1 L m1 n.
    ∃ H, !nodeWkHeadDef H W is il ic id in1 ∧ ∃ T, !goalTailUnaryDef T W tblN (il + 1) (in1 + 1) L m1 n
    (is + 1) ∧ !appendVDef y H T”

instance nodeWk_defined :
    𝚺₁.DefinedFunction (fun v : Fin 10 → V ↦ nodeWk (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8) (v 9)) nodeWkDef := .mk fun v ↦ by
  simp [nodeWkDef, nodeWk, nodeWkHead_defined.iff, goalTailUnary_defined.iff, appendV_defined.iff,
    numeral_eq_natCast]
instance nodeWk_definable :
    𝚺₁.DefinableFunction (fun v : Fin 10 → V ↦ nodeWk (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8) (v 9)) := nodeWk_defined.to_definable

noncomputable def nodeCutDef : 𝚺₁.Semisentence 17 := .mkSigma
  “y W tblN is il ip inp id1 id2 ic1 ic2 in1 in2 L m1 m2 n.
    ∃ H, !nodeCutHeadDef H W is il ip inp id1 id2 ic1 ic2 in1 in2 ∧ ∃ T, !goalTailBinaryDef T W tblN (il
    + 1) (in1 + 1) (in2 + 1) L m1 m2 n (is + 1) ∧ !appendVDef y H T”

instance nodeCut_defined :
    𝚺₁.DefinedFunction (fun v : Fin 16 → V ↦ nodeCut (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8) (v 9) (v 10) (v 11) (v 12) (v 13) (v 14) (v 15)) nodeCutDef := .mk fun v ↦ by
  simp [nodeCutDef, nodeCut, nodeCutHead_defined.iff, goalTailBinary_defined.iff, appendV_defined.iff,
    numeral_eq_natCast]
instance nodeCut_definable :
    𝚺₁.DefinableFunction (fun v : Fin 16 → V ↦ nodeCut (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8) (v 9) (v 10) (v 11) (v 12) (v 13) (v 14) (v 15)) := nodeCut_defined.to_definable

noncomputable def nodeShiftDef : 𝚺₁.Semisentence 11 := .mkSigma
  “y W tblN is il ic id in1 L m1 n.
    ∃ H, !nodeShiftHeadDef H W is il ic id in1 ∧ ∃ T, !goalTailUnaryDef T W tblN (il + 1) (in1 + 1) L m1
    n (is + 1) ∧ !appendVDef y H T”

instance nodeShift_defined :
    𝚺₁.DefinedFunction (fun v : Fin 10 → V ↦ nodeShift (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8) (v 9)) nodeShiftDef := .mk fun v ↦ by
  simp [nodeShiftDef, nodeShift, nodeShiftHead_defined.iff, goalTailUnary_defined.iff, appendV_defined.iff,
    numeral_eq_natCast]
instance nodeShift_definable :
    𝚺₁.DefinableFunction (fun v : Fin 10 → V ↦ nodeShift (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8) (v 9)) := nodeShift_defined.to_definable

noncomputable def nodeAllDef : 𝚺₁.Semisentence 15 := .mkSigma
  “y W tblN is il ir ip ifp iss ic id in1 L m1 n.
    ∃ H, !nodeAllHeadDef H W is il ir ip ifp iss ic id in1 ∧ ∃ T, !goalTailUnaryDef T W tblN (il + 1)
    (in1 + 1) L m1 n (is + 1) ∧ !appendVDef y H T”

instance nodeAll_defined :
    𝚺₁.DefinedFunction (fun v : Fin 14 → V ↦ nodeAll (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8) (v 9) (v 10) (v 11) (v 12) (v 13)) nodeAllDef := .mk fun v ↦ by
  simp [nodeAllDef, nodeAll, nodeAllHead_defined.iff, goalTailUnary_defined.iff, appendV_defined.iff,
    numeral_eq_natCast]
instance nodeAll_definable :
    𝚺₁.DefinableFunction (fun v : Fin 14 → V ↦ nodeAll (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8) (v 9) (v 10) (v 11) (v 12) (v 13)) := nodeAll_defined.to_definable

noncomputable def nodeExsDef : 𝚺₁.Semisentence 17 := .mkSigma
  “y W tblN is il ir ip it ipt ic id ilt in1 L Lt m1 n.
    ∃ H, !nodeExsHeadDef H W is il ir ip it ipt ic id ilt in1 ∧ ∃ T, !goalTailBinaryDef T W tblN (il + 1)
    (ilt + 1) (in1 + 1) L Lt m1 n (is + 1) ∧ !appendVDef y H T”

instance nodeExs_defined :
    𝚺₁.DefinedFunction (fun v : Fin 16 → V ↦ nodeExs (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8) (v 9) (v 10) (v 11) (v 12) (v 13) (v 14) (v 15)) nodeExsDef := .mk fun v ↦ by
  simp [nodeExsDef, nodeExs, nodeExsHead_defined.iff, goalTailBinary_defined.iff, appendV_defined.iff,
    numeral_eq_natCast]
instance nodeExs_definable :
    𝚺₁.DefinableFunction (fun v : Fin 16 → V ↦ nodeExs (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8) (v 9) (v 10) (v 11) (v 12) (v 13) (v 14) (v 15)) := nodeExs_defined.to_definable

noncomputable def nodeAxmDef : 𝚺₁.Semisentence 8 := .mkSigma
  “y W tblN is il ip L n.
    ∃ H, !nodeAxmHeadDef H W is il ip ∧ ∃ T, !goalTailLeafDef T W tblN (il + 1) L n (is + 1) ∧
    !appendVDef y H T”

instance nodeAxm_defined :
    𝚺₁.DefinedFunction (fun v : Fin 7 → V ↦ nodeAxm (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6)) nodeAxmDef := .mk fun v ↦ by
  simp [nodeAxmDef, nodeAxm, nodeAxmHead_defined.iff, goalTailLeaf_defined.iff, appendV_defined.iff,
    numeral_eq_natCast]
instance nodeAxm_definable :
    𝚺₁.DefinableFunction (fun v : Fin 7 → V ↦ nodeAxm (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6)) := nodeAxm_defined.to_definable

end definability

/-! ## 3. `VerifyGraph` — the Δ₁ fixpoint on the key `⟪ρ, L⟫` (`DESIGN_fragments.md` §6.1)

The recursion that glues the ten fragments of §2 into ONE flat step list for a whole derivation
code `ρ`. The key is the pair `⟪ρ, L⟫` (the `DlenGraph` pattern, `DerivationLength.lean:55-211`);
`StrongFinite` holds because every referenced child pair `⟪ρ', L'⟫` has `ρ' < ρ` (the Foundation
`*_lt_*` lemmas) and `L' ≤ L` (`le_appendV_mid` of §1 — `L'` is spliced into `L`).

**THE PROLOGUE IS NOT EMITTED HERE, and this is an explicit WEAKENING relative to
`DESIGN_fragments.md` §4.0.** There the clause reads
`frag<Tag> := pro₁ ++ L₁ ++ rec ++ pro₂ ++ L₂ ++ rec ++ node`, where `pro₁`/`pro₂` are the
copy-in / chain / re-description producers of §3.3–§3.6 that establish the CHILD's canonical
layout. Of those, `copySteps`, `chainSteps` and `eqSteps` have landed (`Layout.lean`), but
`certNeg/certShift/certSubst/certFree`, `lenSteps`, `memberList` and `numProof`'s layout
callers have not (`Cert.lean`, in flight; `DESIGN_fragments.md` §8.3). Assembling a prologue
out of half a kit would freeze the wrong interface. So this file defines the recursion with the
prologues as the Σ₁ parameters `pro₁ pro₂ : V` of the clause, existentially quantified and
constrained ONLY by their own membership in the concatenation — i.e. `VerifyGraph` relates `ρ`
to EVERY list of the right shape, and the uniqueness of §6.2 is therefore NOT claimed for it.
What IS claimed, and is what §6.1 exists for, is the structural core:

* the key, the ten clauses and their `appendV` gluing are exactly §6.1's;
* `Finite`/`StrongFinite` hold, so `Fixpoint.case` and `Fixpoint.induction` are available;
* the graph is Δ₁ (`fixpointDefΔ₁`), with `case_iff` and the ten inversion lemmas.

When `Cert`'s producers land, each clause's `∃ pro₁ pro₂` becomes `∃ pro₁, !proDef pro₁ … ∧ …`
— a one-line change per clause that turns the relation into a function and makes §6.2's
uniqueness provable. The index arguments `is il ir …` are likewise left as existentials: they
are what the prologue determines (`DESIGN_fragments.md` §4.11's "three static quantities").
-/

end ArithS
