import ArithS.Necessitation.Lib.Occ

/-!
# ArithS.Necessitation.Lib.Frag — the FRAGMENT rows of the library `Λ` (GENERATED)

`M4_BOUNDED_HBL/DESIGN_fragments.md` §8.1: the rows the ten per-tag fragments `verifySteps` need
that no earlier `Lib/*` file provides — copy-in (equality and the congruence rows, §3.3), the
identification walk (injectivity, §3.5), functionality (`pinSteps`, §4.10(i)), the chain/set
rows (§3.4, §4.5), the ten `fstIdx<Tag>` rows (§4.0), the top's node rows (§7.1), the exact
lengths (§3.6), the certification rows (bottom-up `neg`/`shift`/`subst`/`free` and the term
level, §3.6), the numeral rows N4/N5 (§2.4) and the `axm`(ii) shape rows (§4.10(ii)).

**This file is generated** by `arith/scripts/gen_frag.py` from ONE row table (the same table
generates `RowInstB.lean`, the row-shape and instantiation lemmas); edit the table, not this file.
Same convention as `Sets.lean`: body `xB : ArithmeticSemisentence m` written `“x₀ … x_{m-1}. B”`
(index order, `x₀ = #0` the innermost quantifier of `∀¹*`), `x := ∀¹* xB`, `models_x` (one `simp`
on the sentence structure), `pa_proves_x` (truth in every model of `𝗜𝚺₁` + completeness),
`lib_x`. Δ₁ hypotheses are taken `.pi`, conclusions `.sigma`; every auxiliary object is a
universal variable with its graph as a hypothesis; arities and indices are variables (the walk
instantiates them at chain numerals `cT`); the DSL literals `0`/`1`/`2` are the codes `𝟎`/`𝟏`/
`𝟏 ^+ 𝟏`; `bnumZeroCert`/`bnumOneCert` write `𝟎`/`𝟏` as the walk does (`func 0 0 0`,
`func 0 (0 + 1) 0`).

## Design row → delivered name

| group | delivered rows |
|---|---|
| copy | `eqTotal`, `eqRefl`, `eqSymm`, `eqTrans`, `congPi`, `congTPi`, `congTvPi`, `congUtvPi`, `congUfPi`, `congAnd`, `congOr`, `congAll`, `congExs`, `congRel`, `congNRel`, `congVerum`, `congFalsum`, `congFunc`, `congBvar`, `congFvar`, `congAdj`, `congLen`, `congTLen`, `congLenNum`, `congTLenNum`, `congMem`, `congMemSet`, `congFstIdx`, `congSubsetL`, `congSubsetR`, `congSetShiftL`, `congSetShiftR`, `congShiftL`, `congNegL`, `congSubstArg`, `congSubstL`, `congInsertL`, `congInsertS`, `congSetLenR`, `congIsFormulaSet` |
| ident | `eqOfAnd`, `eqOfOr`, `eqOfAll`, `eqOfExs`, `eqOfRel`, `eqOfNRel`, `eqOfVerum`, `eqOfFalsum`, `eqOfFunc`, `eqOfBvar`, `eqOfFvar`, `eqOfAdj` |
| fun | `qqAndFun`, `qqOrFun`, `qqAllFun`, `qqExsFun`, `qqRelFun`, `qqNRelFun`, `qqVerumFun`, `qqFalsumFun`, `qqFuncFun`, `qqBvarFun`, `qqFvarFun`, `adjoinFun`, `setShiftFun`, `setLenFun`, `lengthFun`, `termLenVecFun`, `listSumFun`, `formulaLenFun`, `termLenFun`, `fstIdxFun`, `insertFun`, `negFun`, `shiftFun`, `substsFun`, `substs1Fun`, `freeFun`, `bnumFun`, `nthFun`, `fvarVecFun`, `termShiftFun`, `termSubstFun`, `termBShiftFun`, `qqAllsFun`, `bvFun`, `qVecFun`, `termShiftVecFun`, `termSubstVecFun` |
| sets | `subsetAntisymm`, `setShiftInsert`, `setShiftEmpty` |
| fstIdx | `fstIdxAxL`, `fstIdxVerum`, `fstIdxAnd`, `fstIdxOr`, `fstIdxAll`, `fstIdxExs`, `fstIdxWk`, `fstIdxShift`, `fstIdxCut`, `fstIdxAxm` |
| nodes | `dlenDefIntro`, `proofIntro`, `instBIntro`, `gIntro`, `lengthTotal`, `bnumZeroCert`, `bnumOneCert`, `bnumEvenCert`, `bnumOddCert` |
| lengths | `termLenVecNil`, `termLenVecAdj`, `listSumNil`, `listSumAdj`, `formulaLenRelCert`, `formulaLenNRelCert`, `termLenFuncCert` |
| cert | `negRelCert`, `negNRelCert`, `negVerumCert`, `negFalsumCert`, `negAndCert`, `negOrCert`, `negAllCert`, `negExsCert`, `shiftRelCert`, `shiftNRelCert`, `shiftVerumCert`, `shiftFalsumCert`, `shiftAndCert`, `shiftOrCert`, `shiftAllCert`, `shiftExsCert`, `substsRelCert`, `substsNRelCert`, `substsVerumCert`, `substsFalsumCert`, `substsAndCert`, `substsOrCert`, `substsAllCert`, `substsExsCert`, `freeCert`, `substsSubsts1`, `tshvNilCert`, `tshvAdjCert`, `termShiftBvarCert`, `termShiftFvarCert`, `termShiftFuncCert`, `tsvNilCert`, `tsvAdjCert`, `termSubstBvarCert`, `termSubstFvarCert`, `termSubstFuncCert`, `tbshvNilCert`, `tbshvAdjCert`, `termBShiftBvarCert`, `termBShiftFvarCert`, `termBShiftFuncCert`, `qVecCert`, `qVecNth0`, `qVecNthSucc`, `nthAdjoinZero`, `nthAdjoinSucc` |
| num | `twoMulMul`, `twoMulOneMul`, `lengthZero`, `lengthOne`, `lengthTwoMul`, `lengthTwoMulOne` |
| axm | `qqAllsZero`, `qqAllsSucc`, `bvRel`, `bvNRel`, `bvVerum`, `bvFalsum`, `bvAnd`, `bvOr`, `bvAll`, `bvExs`, `termBVBvar`, `termBVFvar`, `termBVFunc`, `termBVVecNil`, `termBVVecAdj`, `listMaxNil`, `listMaxAdj`, `bvTotal`, `fvarVecTotal`, `fvarVecNth`, `maxTotal`, `subTotal`, `maxEqLeft`, `maxEqRight`, `subAddCancel`, `subOfLe` |
| chain | `insertTotalC`, `memInsertSelfC`, `subsetInsertC`, `subsetTransC`, `subsetMemC`, `emptySubsetC`, `fsetOfSubsetZeroC`, `isFormulaSetInsertC`, `fsetSigmaPiC`, `setLenTotalC`, `subsetReflC` |

Skipped / renamed, with the reason:
* `congTvPi`/`congUtvPi` conclude `.sigma` (the polarity convention; `isSemitermVecSigmaPiLAct`
  bridges), `congPi`/`congTPi` likewise; `congUfPi` keeps `.pi` on both sides (`indRec` consumes `.pi`).
* `dlenDefIntro` takes only `derivation.sigma d` (the `.pi` premise of §7.1 is redundant:
  `dlen_eq_of_graph`).
* `bnumEvenCert`/`bnumOddCert` are stated on the walk's `func`/`∷` facts for `𝟏`, `𝟐`, `𝟐 ^* t`,
  `(𝟐 ^* t) ^+ 𝟏` (no `qqAddGraph`/`qqMulGraph` objects — the walk never emits those).
* `twoMulMul`/`twoMulOneMul` and the `length*` rows are written in the DSL (`2 * x`), not in
  `Lengths.lean`'s `eqO/addO/twoMul` term syntax; a `numSteps` producer that mixes both crosses
  the same one-time syntax bridge as `dslSuccEqSuccO`.
* The per-`σ`/per-`χ` closed shape rows of `axm`(i) and the top are a FAMILY generated from a
  Lean term (`pinSteps`), not rows of this file. The `inst_` lemmas of the EXISTING `Nodes`/`Sets`/
  `Lengths`/`Occ` rows are the second table of `RowInstB.lean`.
* `qVecCert` (new): `qVec w` bottom-up from `termBShiftVec` and `#0 ∷ ·` (the `qVec` entries
  `qVecNth0`/`qVecNthSucc` are also delivered).
-/
namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open PeanoMinus ISigma0 ISigma1
open LAct

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

-- the generated closing tactic `first | rfl | assumption | trivial` trips the unused/unreachable-tactic linters
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
-- (`linter.unusedVariables`: the closed rows carry a dummy binder `x`, never referenced)

/-- `setShift (insert x s) = insert (shift x) (setShift s)` (`mem_ext` + `mem_setShift_iff`). -/
lemma setShift_insert (x s : V) : setShift LAct (insert x s) = insert (shift LAct x) (setShift LAct s) := by
  apply mem_ext; intro y
  simp only [mem_setShift_iff, mem_bitInsert_iff]
  constructor
  · rintro ⟨z, hz | hz, rfl⟩
    · left; rw [hz]
    · right; exact ⟨z, hz, rfl⟩
  · rintro (rfl | ⟨z, hz, rfl⟩)
    · exact ⟨x, Or.inl rfl, rfl⟩
    · exact ⟨z, Or.inr hz, rfl⟩

/-- `setShift 0 = 0` (`setShift_empty` with `∅ = 0`). -/
lemma setShift_zero : setShift LAct (0 : V) = 0 := setShift_empty

/-! ### A. Copy-in: equality and the congruence rows (§3.3) -/

/-- `∀ x, ∃ y, y = x` — a fresh eigenvariable equal to a known object (the copy step). -/
noncomputable def eqTotalB : ArithmeticSemisentence 1 :=
  “x. ∃ y, y = x”
noncomputable def eqTotal : ArithmeticSentence := ∀¹* eqTotalB
lemma models_eqTotal : V↓[ℒₒᵣ] ⊧ eqTotal ↔ ∀ x : V, ∃ y, y = x := by
  simp [eqTotal, eqTotalB, models_iff, Matrix.vecForall_iff]
theorem pa_proves_eqTotal : 𝗣𝗔 ⊢ eqTotal :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_eqTotal.mpr fun _ ↦ ⟨_, rfl⟩
theorem lib_eqTotal : Lib eqTotal := Lib.of_pa pa_proves_eqTotal

/-- `x = x`. -/
noncomputable def eqReflB : ArithmeticSemisentence 1 :=
  “x. x = x”
noncomputable def eqRefl : ArithmeticSentence := ∀¹* eqReflB
lemma models_eqRefl : V↓[ℒₒᵣ] ⊧ eqRefl ↔ ∀ x : V, x = x := by
  simp [eqRefl, eqReflB, models_iff, Matrix.vecForall_iff]
theorem pa_proves_eqRefl : 𝗣𝗔 ⊢ eqRefl :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_eqRefl.mpr fun _ ↦ rfl
theorem lib_eqRefl : Lib eqRefl := Lib.of_pa pa_proves_eqRefl

/-- `x = y → y = x`. -/
noncomputable def eqSymmB : ArithmeticSemisentence 2 :=
  “y x. x = y → y = x”
noncomputable def eqSymm : ArithmeticSentence := ∀¹* eqSymmB
lemma models_eqSymm : V↓[ℒₒᵣ] ⊧ eqSymm ↔ ∀ y x : V, x = y → y = x := by
  simp [eqSymm, eqSymmB, models_iff, Matrix.vecForall_iff]
theorem pa_proves_eqSymm : 𝗣𝗔 ⊢ eqSymm :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_eqSymm.mpr fun _ _ h ↦ h.symm
theorem lib_eqSymm : Lib eqSymm := Lib.of_pa pa_proves_eqSymm

/-- `x = y → y = z → x = z`. -/
noncomputable def eqTransB : ArithmeticSemisentence 3 :=
  “z y x. x = y → y = z → x = z”
noncomputable def eqTrans : ArithmeticSentence := ∀¹* eqTransB
lemma models_eqTrans : V↓[ℒₒᵣ] ⊧ eqTrans ↔ ∀ z y x : V, x = y → y = z → x = z := by
  simp [eqTrans, eqTransB, models_iff, Matrix.vecForall_iff]
theorem pa_proves_eqTrans : 𝗣𝗔 ⊢ eqTrans :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_eqTrans.mpr fun _ _ _ h₁ h₂ ↦ h₁.trans h₂
theorem lib_eqTrans : Lib eqTrans := Lib.of_pa pa_proves_eqTrans

/-- `y = x → IsSemiformula n x → IsSemiformula n y`. -/
noncomputable def congPiB : ArithmeticSemisentence 3 :=
  “y x n. y = x → !(isSemiformula LAct).pi n x → !(isSemiformula LAct).sigma n y”
noncomputable def congPi : ArithmeticSentence := ∀¹* congPiB
lemma models_congPi : V↓[ℒₒᵣ] ⊧ congPi ↔ ∀ y x n : V, y = x → IsSemiformula LAct n x → IsSemiformula LAct n y := by
  simp [congPi, congPiB, models_iff, Matrix.vecForall_iff]
theorem pa_proves_congPi : 𝗣𝗔 ⊢ congPi :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_congPi.mpr fun _ _ _ h1 h2 ↦ by subst_vars; first | rfl | assumption | trivial
theorem lib_congPi : Lib congPi := Lib.of_pa pa_proves_congPi

/-- `y = x → IsSemiterm n x → IsSemiterm n y`. -/
noncomputable def congTPiB : ArithmeticSemisentence 3 :=
  “y x n. y = x → !(isSemiterm LAct).pi n x → !(isSemiterm LAct).sigma n y”
noncomputable def congTPi : ArithmeticSentence := ∀¹* congTPiB
lemma models_congTPi : V↓[ℒₒᵣ] ⊧ congTPi ↔ ∀ y x n : V, y = x → IsSemiterm LAct n x → IsSemiterm LAct n y := by
  simp [congTPi, congTPiB, models_iff, Matrix.vecForall_iff]
theorem pa_proves_congTPi : 𝗣𝗔 ⊢ congTPi :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_congTPi.mpr fun _ _ _ h1 h2 ↦ by subst_vars; first | rfl | assumption | trivial
theorem lib_congTPi : Lib congTPi := Lib.of_pa pa_proves_congTPi

/-- `y = x → IsSemitermVec k n x → IsSemitermVec k n y`. -/
noncomputable def congTvPiB : ArithmeticSemisentence 4 :=
  “y x n k. y = x → !(isSemitermVec LAct).pi k n x → !(isSemitermVec LAct).sigma k n y”
noncomputable def congTvPi : ArithmeticSentence := ∀¹* congTvPiB
lemma models_congTvPi : V↓[ℒₒᵣ] ⊧ congTvPi ↔ ∀ y x n k : V, y = x → IsSemitermVec LAct k n x → IsSemitermVec LAct k n y := by
  simp [congTvPi, congTvPiB, models_iff, Matrix.vecForall_iff]
theorem pa_proves_congTvPi : 𝗣𝗔 ⊢ congTvPi :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_congTvPi.mpr fun _ _ _ _ h1 h2 ↦ by subst_vars; first | rfl | assumption | trivial
theorem lib_congTvPi : Lib congTvPi := Lib.of_pa pa_proves_congTvPi

/-- `y = x → IsUTermVec k x → IsUTermVec k y`. -/
noncomputable def congUtvPiB : ArithmeticSemisentence 3 :=
  “y x k. y = x → !(isUTermVec LAct).pi k x → !(isUTermVec LAct).sigma k y”
noncomputable def congUtvPi : ArithmeticSentence := ∀¹* congUtvPiB
lemma models_congUtvPi : V↓[ℒₒᵣ] ⊧ congUtvPi ↔ ∀ y x k : V, y = x → IsUTermVec LAct k x → IsUTermVec LAct k y := by
  simp [congUtvPi, congUtvPiB, models_iff, Matrix.vecForall_iff]
theorem pa_proves_congUtvPi : 𝗣𝗔 ⊢ congUtvPi :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_congUtvPi.mpr fun _ _ _ h1 h2 ↦ by subst_vars; first | rfl | assumption | trivial
theorem lib_congUtvPi : Lib congUtvPi := Lib.of_pa pa_proves_congUtvPi

/-- `r' = r → p' = p → q' = q → r = p ⋏ q → r' = p' ⋏ q'` (all arguments at once). -/
noncomputable def congAndB : ArithmeticSemisentence 6 :=
  “q' p' r' q p r. r' = r → p' = p → q' = q → !qqAndDef r p q → !qqAndDef r' p' q'”
noncomputable def congAnd : ArithmeticSentence := ∀¹* congAndB
lemma models_congAnd : V↓[ℒₒᵣ] ⊧ congAnd ↔ ∀ q' p' r' q p r : V, r' = r → p' = p → q' = q → r = p ^⋏ q → r' = p' ^⋏ q' := by
  simp [congAnd, congAndB, models_iff, Matrix.vecForall_iff]
theorem pa_proves_congAnd : 𝗣𝗔 ⊢ congAnd :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_congAnd.mpr fun _ _ _ _ _ _ h1 h2 h3 h4 ↦ by subst_vars; first | rfl | assumption | trivial
theorem lib_congAnd : Lib congAnd := Lib.of_pa pa_proves_congAnd

/-- the `⋎` congruence. -/
noncomputable def congOrB : ArithmeticSemisentence 6 :=
  “q' p' r' q p r. r' = r → p' = p → q' = q → !qqOrDef r p q → !qqOrDef r' p' q'”
noncomputable def congOr : ArithmeticSentence := ∀¹* congOrB
lemma models_congOr : V↓[ℒₒᵣ] ⊧ congOr ↔ ∀ q' p' r' q p r : V, r' = r → p' = p → q' = q → r = p ^⋎ q → r' = p' ^⋎ q' := by
  simp [congOr, congOrB, models_iff, Matrix.vecForall_iff]
theorem pa_proves_congOr : 𝗣𝗔 ⊢ congOr :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_congOr.mpr fun _ _ _ _ _ _ h1 h2 h3 h4 ↦ by subst_vars; first | rfl | assumption | trivial
theorem lib_congOr : Lib congOr := Lib.of_pa pa_proves_congOr

/-- the `∀` congruence. -/
noncomputable def congAllB : ArithmeticSemisentence 4 :=
  “p' q' p q. q' = q → p' = p → !qqAllDef q p → !qqAllDef q' p'”
noncomputable def congAll : ArithmeticSentence := ∀¹* congAllB
lemma models_congAll : V↓[ℒₒᵣ] ⊧ congAll ↔ ∀ p' q' p q : V, q' = q → p' = p → q = ^∀ p → q' = ^∀ p' := by
  simp [congAll, congAllB, models_iff, Matrix.vecForall_iff]
theorem pa_proves_congAll : 𝗣𝗔 ⊢ congAll :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_congAll.mpr fun _ _ _ _ h1 h2 h3 ↦ by subst_vars; first | rfl | assumption | trivial
theorem lib_congAll : Lib congAll := Lib.of_pa pa_proves_congAll

/-- the `∃` congruence. -/
noncomputable def congExsB : ArithmeticSemisentence 4 :=
  “p' q' p q. q' = q → p' = p → !qqExsDef q p → !qqExsDef q' p'”
noncomputable def congExs : ArithmeticSentence := ∀¹* congExsB
lemma models_congExs : V↓[ℒₒᵣ] ⊧ congExs ↔ ∀ p' q' p q : V, q' = q → p' = p → q = ^∃ p → q' = ^∃ p' := by
  simp [congExs, congExsB, models_iff, Matrix.vecForall_iff]
theorem pa_proves_congExs : 𝗣𝗔 ⊢ congExs :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_congExs.mpr fun _ _ _ _ h1 h2 h3 ↦ by subst_vars; first | rfl | assumption | trivial
theorem lib_congExs : Lib congExs := Lib.of_pa pa_proves_congExs

/-- the `rel` congruence (the symbol numerals are shared). -/
noncomputable def congRelB : ArithmeticSemisentence 6 :=
  “v' r' v R k r. r' = r → v' = v → !qqRelDef r k R v → !qqRelDef r' k R v'”
noncomputable def congRel : ArithmeticSentence := ∀¹* congRelB
lemma models_congRel : V↓[ℒₒᵣ] ⊧ congRel ↔ ∀ v' r' v R k r : V, r' = r → v' = v → r = ^rel k R v → r' = ^rel k R v' := by
  simp [congRel, congRelB, models_iff, Matrix.vecForall_iff]
theorem pa_proves_congRel : 𝗣𝗔 ⊢ congRel :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_congRel.mpr fun _ _ _ _ _ _ h1 h2 h3 ↦ by subst_vars; first | rfl | assumption | trivial
theorem lib_congRel : Lib congRel := Lib.of_pa pa_proves_congRel

/-- the `nrel` congruence. -/
noncomputable def congNRelB : ArithmeticSemisentence 6 :=
  “v' r' v R k r. r' = r → v' = v → !qqNRelDef r k R v → !qqNRelDef r' k R v'”
noncomputable def congNRel : ArithmeticSentence := ∀¹* congNRelB
lemma models_congNRel : V↓[ℒₒᵣ] ⊧ congNRel ↔ ∀ v' r' v R k r : V, r' = r → v' = v → r = ^nrel k R v → r' = ^nrel k R v' := by
  simp [congNRel, congNRelB, models_iff, Matrix.vecForall_iff]
theorem pa_proves_congNRel : 𝗣𝗔 ⊢ congNRel :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_congNRel.mpr fun _ _ _ _ _ _ h1 h2 h3 ↦ by subst_vars; first | rfl | assumption | trivial
theorem lib_congNRel : Lib congNRel := Lib.of_pa pa_proves_congNRel

/-- the `⊤` congruence. -/
noncomputable def congVerumB : ArithmeticSemisentence 2 :=
  “p' p. p' = p → !qqVerumDef p → !qqVerumDef p'”
noncomputable def congVerum : ArithmeticSentence := ∀¹* congVerumB
lemma models_congVerum : V↓[ℒₒᵣ] ⊧ congVerum ↔ ∀ p' p : V, p' = p → p = ^⊤ → p' = ^⊤ := by
  simp [congVerum, congVerumB, models_iff, Matrix.vecForall_iff]
theorem pa_proves_congVerum : 𝗣𝗔 ⊢ congVerum :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_congVerum.mpr fun _ _ h1 h2 ↦ by subst_vars; first | rfl | assumption | trivial
theorem lib_congVerum : Lib congVerum := Lib.of_pa pa_proves_congVerum

/-- the `⊥` congruence. -/
noncomputable def congFalsumB : ArithmeticSemisentence 2 :=
  “p' p. p' = p → !qqFalsumDef p → !qqFalsumDef p'”
noncomputable def congFalsum : ArithmeticSentence := ∀¹* congFalsumB
lemma models_congFalsum : V↓[ℒₒᵣ] ⊧ congFalsum ↔ ∀ p' p : V, p' = p → p = ^⊥ → p' = ^⊥ := by
  simp [congFalsum, congFalsumB, models_iff, Matrix.vecForall_iff]
theorem pa_proves_congFalsum : 𝗣𝗔 ⊢ congFalsum :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_congFalsum.mpr fun _ _ h1 h2 ↦ by subst_vars; first | rfl | assumption | trivial
theorem lib_congFalsum : Lib congFalsum := Lib.of_pa pa_proves_congFalsum

/-- the `func` congruence. -/
noncomputable def congFuncB : ArithmeticSemisentence 6 :=
  “v' t' v f k t. t' = t → v' = v → !qqFuncDef t k f v → !qqFuncDef t' k f v'”
noncomputable def congFunc : ArithmeticSentence := ∀¹* congFuncB
lemma models_congFunc : V↓[ℒₒᵣ] ⊧ congFunc ↔ ∀ v' t' v f k t : V, t' = t → v' = v → t = ^func k f v → t' = ^func k f v' := by
  simp [congFunc, congFuncB, models_iff, Matrix.vecForall_iff]
theorem pa_proves_congFunc : 𝗣𝗔 ⊢ congFunc :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_congFunc.mpr fun _ _ _ _ _ _ h1 h2 h3 ↦ by subst_vars; first | rfl | assumption | trivial
theorem lib_congFunc : Lib congFunc := Lib.of_pa pa_proves_congFunc

/-- the `#z` congruence. -/
noncomputable def congBvarB : ArithmeticSemisentence 3 :=
  “t' t z. t' = t → !qqBvarDef t z → !qqBvarDef t' z”
noncomputable def congBvar : ArithmeticSentence := ∀¹* congBvarB
lemma models_congBvar : V↓[ℒₒᵣ] ⊧ congBvar ↔ ∀ t' t z : V, t' = t → t = ^#z → t' = ^#z := by
  simp [congBvar, congBvarB, models_iff, Matrix.vecForall_iff]
theorem pa_proves_congBvar : 𝗣𝗔 ⊢ congBvar :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_congBvar.mpr fun _ _ _ h1 h2 ↦ by subst_vars; first | rfl | assumption | trivial
theorem lib_congBvar : Lib congBvar := Lib.of_pa pa_proves_congBvar

/-- the `&x` congruence. -/
noncomputable def congFvarB : ArithmeticSemisentence 3 :=
  “t' t x. t' = t → !qqFvarDef t x → !qqFvarDef t' x”
noncomputable def congFvar : ArithmeticSentence := ∀¹* congFvarB
lemma models_congFvar : V↓[ℒₒᵣ] ⊧ congFvar ↔ ∀ t' t x : V, t' = t → t = ^&x → t' = ^&x := by
  simp [congFvar, congFvarB, models_iff, Matrix.vecForall_iff]
theorem pa_proves_congFvar : 𝗣𝗔 ⊢ congFvar :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_congFvar.mpr fun _ _ _ h1 h2 ↦ by subst_vars; first | rfl | assumption | trivial
theorem lib_congFvar : Lib congFvar := Lib.of_pa pa_proves_congFvar

/-- the `∷` congruence. -/
noncomputable def congAdjB : ArithmeticSemisentence 6 :=
  “w' v' t' w v t. w' = w → t' = t → v' = v → !adjoinDef w t v → !adjoinDef w' t' v'”
noncomputable def congAdj : ArithmeticSentence := ∀¹* congAdjB
lemma models_congAdj : V↓[ℒₒᵣ] ⊧ congAdj ↔ ∀ w' v' t' w v t : V, w' = w → t' = t → v' = v → w = t ∷ v → w' = t' ∷ v' := by
  simp [congAdj, congAdjB, models_iff, Matrix.vecForall_iff]
theorem pa_proves_congAdj : 𝗣𝗔 ⊢ congAdj :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_congAdj.mpr fun _ _ _ _ _ _ h1 h2 h3 h4 ↦ by subst_vars; first | rfl | assumption | trivial
theorem lib_congAdj : Lib congAdj := Lib.of_pa pa_proves_congAdj

/-- `y = x → formulaLen x = l → formulaLen y = l`. -/
noncomputable def congLenB : ArithmeticSemisentence 3 :=
  “y x l. y = x → !(formulaLenGraph LAct) l x → !(formulaLenGraph LAct) l y”
noncomputable def congLen : ArithmeticSentence := ∀¹* congLenB
lemma models_congLen : V↓[ℒₒᵣ] ⊧ congLen ↔ ∀ y x l : V, y = x → l = formulaLen LAct x → l = formulaLen LAct y := by
  simp [congLen, congLenB, models_iff, Matrix.vecForall_iff, formulaLen.defined.iff]
theorem pa_proves_congLen : 𝗣𝗔 ⊢ congLen :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_congLen.mpr fun _ _ _ h1 h2 ↦ by subst_vars; first | rfl | assumption | trivial
theorem lib_congLen : Lib congLen := Lib.of_pa pa_proves_congLen

/-- `y = x → termLen x = l → termLen y = l`. -/
noncomputable def congTLenB : ArithmeticSemisentence 3 :=
  “y x l. y = x → !(termLenGraph LAct) l x → !(termLenGraph LAct) l y”
noncomputable def congTLen : ArithmeticSentence := ∀¹* congTLenB
lemma models_congTLen : V↓[ℒₒᵣ] ⊧ congTLen ↔ ∀ y x l : V, y = x → l = termLen LAct x → l = termLen LAct y := by
  simp [congTLen, congTLenB, models_iff, Matrix.vecForall_iff, termLen.defined.iff]
theorem pa_proves_congTLen : 𝗣𝗔 ⊢ congTLen :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_congTLen.mpr fun _ _ _ h1 h2 ↦ by subst_vars; first | rfl | assumption | trivial
theorem lib_congTLen : Lib congTLen := Lib.of_pa pa_proves_congTLen

/-- `l = l' → formulaLen y = l → formulaLen y = l'` (the numeral into the graph position, §3.6). -/
noncomputable def congLenNumB : ArithmeticSemisentence 3 :=
  “l' l y. l = l' → !(formulaLenGraph LAct) l y → !(formulaLenGraph LAct) l' y”
noncomputable def congLenNum : ArithmeticSentence := ∀¹* congLenNumB
lemma models_congLenNum : V↓[ℒₒᵣ] ⊧ congLenNum ↔ ∀ l' l y : V, l = l' → l = formulaLen LAct y → l' = formulaLen LAct y := by
  simp [congLenNum, congLenNumB, models_iff, Matrix.vecForall_iff, formulaLen.defined.iff]
theorem pa_proves_congLenNum : 𝗣𝗔 ⊢ congLenNum :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_congLenNum.mpr fun _ _ _ h1 h2 ↦ by subst_vars; first | rfl | assumption | trivial
theorem lib_congLenNum : Lib congLenNum := Lib.of_pa pa_proves_congLenNum

/-- the term-length twin of `congLenNum`. -/
noncomputable def congTLenNumB : ArithmeticSemisentence 3 :=
  “l' l t. l = l' → !(termLenGraph LAct) l t → !(termLenGraph LAct) l' t”
noncomputable def congTLenNum : ArithmeticSentence := ∀¹* congTLenNumB
lemma models_congTLenNum : V↓[ℒₒᵣ] ⊧ congTLenNum ↔ ∀ l' l t : V, l = l' → l = termLen LAct t → l' = termLen LAct t := by
  simp [congTLenNum, congTLenNumB, models_iff, Matrix.vecForall_iff, termLen.defined.iff]
theorem pa_proves_congTLenNum : 𝗣𝗔 ⊢ congTLenNum :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_congTLenNum.mpr fun _ _ _ h1 h2 ↦ by subst_vars; first | rfl | assumption | trivial
theorem lib_congTLenNum : Lib congTLenNum := Lib.of_pa pa_proves_congTLenNum

/-- `y = x → x ∈ s → y ∈ s`. -/
noncomputable def congMemB : ArithmeticSemisentence 3 :=
  “s y x. y = x → x ∈ s → y ∈ s”
noncomputable def congMem : ArithmeticSentence := ∀¹* congMemB
lemma models_congMem : V↓[ℒₒᵣ] ⊧ congMem ↔ ∀ s y x : V, y = x → x ∈ s → y ∈ s := by
  simp [congMem, congMemB, models_iff, Matrix.vecForall_iff]
theorem pa_proves_congMem : 𝗣𝗔 ⊢ congMem :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_congMem.mpr fun _ _ _ h1 h2 ↦ by subst_vars; first | rfl | assumption | trivial
theorem lib_congMem : Lib congMem := Lib.of_pa pa_proves_congMem

/-- `s' = s → x ∈ s → x ∈ s'`. -/
noncomputable def congMemSetB : ArithmeticSemisentence 3 :=
  “s' s x. s' = s → x ∈ s → x ∈ s'”
noncomputable def congMemSet : ArithmeticSentence := ∀¹* congMemSetB
lemma models_congMemSet : V↓[ℒₒᵣ] ⊧ congMemSet ↔ ∀ s' s x : V, s' = s → x ∈ s → x ∈ s' := by
  simp [congMemSet, congMemSetB, models_iff, Matrix.vecForall_iff]
theorem pa_proves_congMemSet : 𝗣𝗔 ⊢ congMemSet :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_congMemSet.mpr fun _ _ _ h1 h2 ↦ by subst_vars; first | rfl | assumption | trivial
theorem lib_congMemSet : Lib congMemSet := Lib.of_pa pa_proves_congMemSet

/-- `t' = t → fstIdx d = t → fstIdx d = t'` (moves a child's goal onto the row's sequent object, §3.4). -/
noncomputable def congFstIdxB : ArithmeticSemisentence 3 :=
  “t' t d. t' = t → !fstIdxDef t d → !fstIdxDef t' d”
noncomputable def congFstIdx : ArithmeticSentence := ∀¹* congFstIdxB
lemma models_congFstIdx : V↓[ℒₒᵣ] ⊧ congFstIdx ↔ ∀ t' t d : V, t' = t → t = fstIdx d → t' = fstIdx d := by
  simp [congFstIdx, congFstIdxB, models_iff, Matrix.vecForall_iff]
theorem pa_proves_congFstIdx : 𝗣𝗔 ⊢ congFstIdx :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_congFstIdx.mpr fun _ _ _ h1 h2 ↦ by subst_vars; first | rfl | assumption | trivial
theorem lib_congFstIdx : Lib congFstIdx := Lib.of_pa pa_proves_congFstIdx

/-- `t' = t → t ⊆ u → t' ⊆ u`. -/
noncomputable def congSubsetLB : ArithmeticSemisentence 3 :=
  “u t' t. t' = t → !bitSubsetDef t u → !bitSubsetDef t' u”
noncomputable def congSubsetL : ArithmeticSentence := ∀¹* congSubsetLB
lemma models_congSubsetL : V↓[ℒₒᵣ] ⊧ congSubsetL ↔ ∀ u t' t : V, t' = t → t ⊆ u → t' ⊆ u := by
  simp [congSubsetL, congSubsetLB, models_iff, Matrix.vecForall_iff]
theorem pa_proves_congSubsetL : 𝗣𝗔 ⊢ congSubsetL :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_congSubsetL.mpr fun _ _ _ h1 h2 ↦ by subst_vars; first | rfl | assumption | trivial
theorem lib_congSubsetL : Lib congSubsetL := Lib.of_pa pa_proves_congSubsetL

/-- `t' = t → t = setShift s → t' = setShift s`. -/
noncomputable def congSetShiftLB : ArithmeticSemisentence 3 :=
  “s t' t. t' = t → !(setShiftGraph LAct) t s → !(setShiftGraph LAct) t' s”
noncomputable def congSetShiftL : ArithmeticSentence := ∀¹* congSetShiftLB
lemma models_congSetShiftL : V↓[ℒₒᵣ] ⊧ congSetShiftL ↔ ∀ s t' t : V, t' = t → t = setShift LAct s → t' = setShift LAct s := by
  simp [congSetShiftL, congSetShiftLB, models_iff, Matrix.vecForall_iff, setShift.defined.iff]
theorem pa_proves_congSetShiftL : 𝗣𝗔 ⊢ congSetShiftL :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_congSetShiftL.mpr fun _ _ _ h1 h2 ↦ by subst_vars; first | rfl | assumption | trivial
theorem lib_congSetShiftL : Lib congSetShiftL := Lib.of_pa pa_proves_congSetShiftL

/-- `s' = s → t = setShift s → t = setShift s'`. -/
noncomputable def congSetShiftRB : ArithmeticSemisentence 3 :=
  “s' s t. s' = s → !(setShiftGraph LAct) t s → !(setShiftGraph LAct) t s'”
noncomputable def congSetShiftR : ArithmeticSentence := ∀¹* congSetShiftRB
lemma models_congSetShiftR : V↓[ℒₒᵣ] ⊧ congSetShiftR ↔ ∀ s' s t : V, s' = s → t = setShift LAct s → t = setShift LAct s' := by
  simp [congSetShiftR, congSetShiftRB, models_iff, Matrix.vecForall_iff, setShift.defined.iff]
theorem pa_proves_congSetShiftR : 𝗣𝗔 ⊢ congSetShiftR :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_congSetShiftR.mpr fun _ _ _ h1 h2 ↦ by subst_vars; first | rfl | assumption | trivial
theorem lib_congSetShiftR : Lib congSetShiftR := Lib.of_pa pa_proves_congSetShiftR

/-- `y' = y → y = shift x → y' = shift x`. -/
noncomputable def congShiftLB : ArithmeticSemisentence 3 :=
  “x y' y. y' = y → !(shiftGraph LAct) y x → !(shiftGraph LAct) y' x”
noncomputable def congShiftL : ArithmeticSentence := ∀¹* congShiftLB
lemma models_congShiftL : V↓[ℒₒᵣ] ⊧ congShiftL ↔ ∀ x y' y : V, y' = y → y = shift LAct x → y' = shift LAct x := by
  simp [congShiftL, congShiftLB, models_iff, Matrix.vecForall_iff, shift.defined.iff]
theorem pa_proves_congShiftL : 𝗣𝗔 ⊢ congShiftL :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_congShiftL.mpr fun _ _ _ h1 h2 ↦ by subst_vars; first | rfl | assumption | trivial
theorem lib_congShiftL : Lib congShiftL := Lib.of_pa pa_proves_congShiftL

/-- `n = n' → y = subst w n → y = subst w n'` (the top's `congSubstR`, §7.1). -/
noncomputable def congSubstArgB : ArithmeticSemisentence 4 :=
  “n' n w y. n = n' → !(substsGraph LAct) y w n → !(substsGraph LAct) y w n'”
noncomputable def congSubstArg : ArithmeticSentence := ∀¹* congSubstArgB
lemma models_congSubstArg : V↓[ℒₒᵣ] ⊧ congSubstArg ↔ ∀ n' n w y : V, n = n' → y = subst LAct w n → y = subst LAct w n' := by
  simp [congSubstArg, congSubstArgB, models_iff, Matrix.vecForall_iff, subst.defined.iff]
theorem pa_proves_congSubstArg : 𝗣𝗔 ⊢ congSubstArg :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_congSubstArg.mpr fun _ _ _ _ h1 h2 ↦ by subst_vars; first | rfl | assumption | trivial
theorem lib_congSubstArg : Lib congSubstArg := Lib.of_pa pa_proves_congSubstArg

/-- `s' = s → t = insert x s → t = insert x s'`. -/
noncomputable def congInsertSB : ArithmeticSemisentence 4 :=
  “s' s x t. s' = s → !insertDef t x s → !insertDef t x s'”
noncomputable def congInsertS : ArithmeticSentence := ∀¹* congInsertSB
lemma models_congInsertS : V↓[ℒₒᵣ] ⊧ congInsertS ↔ ∀ s' s x t : V, s' = s → t = insert x s → t = insert x s' := by
  simp [congInsertS, congInsertSB, models_iff, Matrix.vecForall_iff]
theorem pa_proves_congInsertS : 𝗣𝗔 ⊢ congInsertS :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_congInsertS.mpr fun _ _ _ _ h1 h2 ↦ by subst_vars; first | rfl | assumption | trivial
theorem lib_congInsertS : Lib congInsertS := Lib.of_pa pa_proves_congInsertS

/-- `s' = s → l = setLen s → l = setLen s'`. -/
noncomputable def congSetLenRB : ArithmeticSemisentence 3 :=
  “l s' s. s' = s → !(setLenDef LAct) l s → !(setLenDef LAct) l s'”
noncomputable def congSetLenR : ArithmeticSentence := ∀¹* congSetLenRB
lemma models_congSetLenR : V↓[ℒₒᵣ] ⊧ congSetLenR ↔ ∀ l s' s : V, s' = s → l = setLen LAct s → l = setLen LAct s' := by
  simp [congSetLenR, congSetLenRB, models_iff, Matrix.vecForall_iff, setLen_defined.iff]
theorem pa_proves_congSetLenR : 𝗣𝗔 ⊢ congSetLenR :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_congSetLenR.mpr fun _ _ _ h1 h2 ↦ by subst_vars; first | rfl | assumption | trivial
theorem lib_congSetLenR : Lib congSetLenR := Lib.of_pa pa_proves_congSetLenR

/-! ### B. Identification: the injectivity rows (§3.5) -/

/-- `x = p ⋏ q → y = p' ⋏ q' → p = p' → q = q' → x = y`. -/
noncomputable def eqOfAndB : ArithmeticSemisentence 6 :=
  “y q' p' q p x. !qqAndDef x p q → !qqAndDef y p' q' → p = p' → q = q' → x = y”
noncomputable def eqOfAnd : ArithmeticSentence := ∀¹* eqOfAndB
lemma models_eqOfAnd : V↓[ℒₒᵣ] ⊧ eqOfAnd ↔ ∀ y q' p' q p x : V, x = p ^⋏ q → y = p' ^⋏ q' → p = p' → q = q' → x = y := by
  simp [eqOfAnd, eqOfAndB, models_iff, Matrix.vecForall_iff]
theorem pa_proves_eqOfAnd : 𝗣𝗔 ⊢ eqOfAnd :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_eqOfAnd.mpr fun _ _ _ _ _ _ h1 h2 h3 h4 ↦ by subst_vars; first | rfl | assumption | trivial
theorem lib_eqOfAnd : Lib eqOfAnd := Lib.of_pa pa_proves_eqOfAnd

/-- the `⋎` identification. -/
noncomputable def eqOfOrB : ArithmeticSemisentence 6 :=
  “y q' p' q p x. !qqOrDef x p q → !qqOrDef y p' q' → p = p' → q = q' → x = y”
noncomputable def eqOfOr : ArithmeticSentence := ∀¹* eqOfOrB
lemma models_eqOfOr : V↓[ℒₒᵣ] ⊧ eqOfOr ↔ ∀ y q' p' q p x : V, x = p ^⋎ q → y = p' ^⋎ q' → p = p' → q = q' → x = y := by
  simp [eqOfOr, eqOfOrB, models_iff, Matrix.vecForall_iff]
theorem pa_proves_eqOfOr : 𝗣𝗔 ⊢ eqOfOr :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_eqOfOr.mpr fun _ _ _ _ _ _ h1 h2 h3 h4 ↦ by subst_vars; first | rfl | assumption | trivial
theorem lib_eqOfOr : Lib eqOfOr := Lib.of_pa pa_proves_eqOfOr

/-- the `∀` identification. -/
noncomputable def eqOfAllB : ArithmeticSemisentence 4 :=
  “y p' p x. !qqAllDef x p → !qqAllDef y p' → p = p' → x = y”
noncomputable def eqOfAll : ArithmeticSentence := ∀¹* eqOfAllB
lemma models_eqOfAll : V↓[ℒₒᵣ] ⊧ eqOfAll ↔ ∀ y p' p x : V, x = ^∀ p → y = ^∀ p' → p = p' → x = y := by
  simp [eqOfAll, eqOfAllB, models_iff, Matrix.vecForall_iff]
theorem pa_proves_eqOfAll : 𝗣𝗔 ⊢ eqOfAll :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_eqOfAll.mpr fun _ _ _ _ h1 h2 h3 ↦ by subst_vars; first | rfl | assumption | trivial
theorem lib_eqOfAll : Lib eqOfAll := Lib.of_pa pa_proves_eqOfAll

/-- the `∃` identification. -/
noncomputable def eqOfExsB : ArithmeticSemisentence 4 :=
  “y p' p x. !qqExsDef x p → !qqExsDef y p' → p = p' → x = y”
noncomputable def eqOfExs : ArithmeticSentence := ∀¹* eqOfExsB
lemma models_eqOfExs : V↓[ℒₒᵣ] ⊧ eqOfExs ↔ ∀ y p' p x : V, x = ^∃ p → y = ^∃ p' → p = p' → x = y := by
  simp [eqOfExs, eqOfExsB, models_iff, Matrix.vecForall_iff]
theorem pa_proves_eqOfExs : 𝗣𝗔 ⊢ eqOfExs :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_eqOfExs.mpr fun _ _ _ _ h1 h2 h3 ↦ by subst_vars; first | rfl | assumption | trivial
theorem lib_eqOfExs : Lib eqOfExs := Lib.of_pa pa_proves_eqOfExs

/-- the `rel` identification (the symbol numerals are syntactically shared). -/
noncomputable def eqOfRelB : ArithmeticSemisentence 6 :=
  “y v' v R k x. !qqRelDef x k R v → !qqRelDef y k R v' → v = v' → x = y”
noncomputable def eqOfRel : ArithmeticSentence := ∀¹* eqOfRelB
lemma models_eqOfRel : V↓[ℒₒᵣ] ⊧ eqOfRel ↔ ∀ y v' v R k x : V, x = ^rel k R v → y = ^rel k R v' → v = v' → x = y := by
  simp [eqOfRel, eqOfRelB, models_iff, Matrix.vecForall_iff]
theorem pa_proves_eqOfRel : 𝗣𝗔 ⊢ eqOfRel :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_eqOfRel.mpr fun _ _ _ _ _ _ h1 h2 h3 ↦ by subst_vars; first | rfl | assumption | trivial
theorem lib_eqOfRel : Lib eqOfRel := Lib.of_pa pa_proves_eqOfRel

/-- the `nrel` identification. -/
noncomputable def eqOfNRelB : ArithmeticSemisentence 6 :=
  “y v' v R k x. !qqNRelDef x k R v → !qqNRelDef y k R v' → v = v' → x = y”
noncomputable def eqOfNRel : ArithmeticSentence := ∀¹* eqOfNRelB
lemma models_eqOfNRel : V↓[ℒₒᵣ] ⊧ eqOfNRel ↔ ∀ y v' v R k x : V, x = ^nrel k R v → y = ^nrel k R v' → v = v' → x = y := by
  simp [eqOfNRel, eqOfNRelB, models_iff, Matrix.vecForall_iff]
theorem pa_proves_eqOfNRel : 𝗣𝗔 ⊢ eqOfNRel :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_eqOfNRel.mpr fun _ _ _ _ _ _ h1 h2 h3 ↦ by subst_vars; first | rfl | assumption | trivial
theorem lib_eqOfNRel : Lib eqOfNRel := Lib.of_pa pa_proves_eqOfNRel

/-- the `⊤` identification. -/
noncomputable def eqOfVerumB : ArithmeticSemisentence 2 :=
  “y x. !qqVerumDef x → !qqVerumDef y → x = y”
noncomputable def eqOfVerum : ArithmeticSentence := ∀¹* eqOfVerumB
lemma models_eqOfVerum : V↓[ℒₒᵣ] ⊧ eqOfVerum ↔ ∀ y x : V, x = ^⊤ → y = ^⊤ → x = y := by
  simp [eqOfVerum, eqOfVerumB, models_iff, Matrix.vecForall_iff]
theorem pa_proves_eqOfVerum : 𝗣𝗔 ⊢ eqOfVerum :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_eqOfVerum.mpr fun _ _ h1 h2 ↦ by subst_vars; first | rfl | assumption | trivial
theorem lib_eqOfVerum : Lib eqOfVerum := Lib.of_pa pa_proves_eqOfVerum

/-- the `⊥` identification. -/
noncomputable def eqOfFalsumB : ArithmeticSemisentence 2 :=
  “y x. !qqFalsumDef x → !qqFalsumDef y → x = y”
noncomputable def eqOfFalsum : ArithmeticSentence := ∀¹* eqOfFalsumB
lemma models_eqOfFalsum : V↓[ℒₒᵣ] ⊧ eqOfFalsum ↔ ∀ y x : V, x = ^⊥ → y = ^⊥ → x = y := by
  simp [eqOfFalsum, eqOfFalsumB, models_iff, Matrix.vecForall_iff]
theorem pa_proves_eqOfFalsum : 𝗣𝗔 ⊢ eqOfFalsum :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_eqOfFalsum.mpr fun _ _ h1 h2 ↦ by subst_vars; first | rfl | assumption | trivial
theorem lib_eqOfFalsum : Lib eqOfFalsum := Lib.of_pa pa_proves_eqOfFalsum

/-- the `func` identification. -/
noncomputable def eqOfFuncB : ArithmeticSemisentence 6 :=
  “t' v' v f k t. !qqFuncDef t k f v → !qqFuncDef t' k f v' → v = v' → t = t'”
noncomputable def eqOfFunc : ArithmeticSentence := ∀¹* eqOfFuncB
lemma models_eqOfFunc : V↓[ℒₒᵣ] ⊧ eqOfFunc ↔ ∀ t' v' v f k t : V, t = ^func k f v → t' = ^func k f v' → v = v' → t = t' := by
  simp [eqOfFunc, eqOfFuncB, models_iff, Matrix.vecForall_iff]
theorem pa_proves_eqOfFunc : 𝗣𝗔 ⊢ eqOfFunc :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_eqOfFunc.mpr fun _ _ _ _ _ _ h1 h2 h3 ↦ by subst_vars; first | rfl | assumption | trivial
theorem lib_eqOfFunc : Lib eqOfFunc := Lib.of_pa pa_proves_eqOfFunc

/-- the `#z` identification. -/
noncomputable def eqOfBvarB : ArithmeticSemisentence 3 :=
  “t' t z. !qqBvarDef t z → !qqBvarDef t' z → t = t'”
noncomputable def eqOfBvar : ArithmeticSentence := ∀¹* eqOfBvarB
lemma models_eqOfBvar : V↓[ℒₒᵣ] ⊧ eqOfBvar ↔ ∀ t' t z : V, t = ^#z → t' = ^#z → t = t' := by
  simp [eqOfBvar, eqOfBvarB, models_iff, Matrix.vecForall_iff]
theorem pa_proves_eqOfBvar : 𝗣𝗔 ⊢ eqOfBvar :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_eqOfBvar.mpr fun _ _ _ h1 h2 ↦ by subst_vars; first | rfl | assumption | trivial
theorem lib_eqOfBvar : Lib eqOfBvar := Lib.of_pa pa_proves_eqOfBvar

/-- the `&x` identification. -/
noncomputable def eqOfFvarB : ArithmeticSemisentence 3 :=
  “t' t x. !qqFvarDef t x → !qqFvarDef t' x → t = t'”
noncomputable def eqOfFvar : ArithmeticSentence := ∀¹* eqOfFvarB
lemma models_eqOfFvar : V↓[ℒₒᵣ] ⊧ eqOfFvar ↔ ∀ t' t x : V, t = ^&x → t' = ^&x → t = t' := by
  simp [eqOfFvar, eqOfFvarB, models_iff, Matrix.vecForall_iff]
theorem pa_proves_eqOfFvar : 𝗣𝗔 ⊢ eqOfFvar :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_eqOfFvar.mpr fun _ _ _ h1 h2 ↦ by subst_vars; first | rfl | assumption | trivial
theorem lib_eqOfFvar : Lib eqOfFvar := Lib.of_pa pa_proves_eqOfFvar

/-- the `∷` identification. -/
noncomputable def eqOfAdjB : ArithmeticSemisentence 6 :=
  “w' v' t' w v t. !adjoinDef w t v → !adjoinDef w' t' v' → t = t' → v = v' → w = w'”
noncomputable def eqOfAdj : ArithmeticSentence := ∀¹* eqOfAdjB
lemma models_eqOfAdj : V↓[ℒₒᵣ] ⊧ eqOfAdj ↔ ∀ w' v' t' w v t : V, w = t ∷ v → w' = t' ∷ v' → t = t' → v = v' → w = w' := by
  simp [eqOfAdj, eqOfAdjB, models_iff, Matrix.vecForall_iff]
theorem pa_proves_eqOfAdj : 𝗣𝗔 ⊢ eqOfAdj :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_eqOfAdj.mpr fun _ _ _ _ _ _ h1 h2 h3 h4 ↦ by subst_vars; first | rfl | assumption | trivial
theorem lib_eqOfAdj : Lib eqOfAdj := Lib.of_pa pa_proves_eqOfAdj

/-! ### C. Functionality (`pinSteps`, §4.10(i)) -/

/-- `y = p ⋏ q → y' = p ⋏ q → y = y'`. -/
noncomputable def qqAndFunB : ArithmeticSemisentence 4 :=
  “y' p q y. !qqAndDef y p q → !qqAndDef y' p q → y = y'”
noncomputable def qqAndFun : ArithmeticSentence := ∀¹* qqAndFunB
lemma models_qqAndFun : V↓[ℒₒᵣ] ⊧ qqAndFun ↔ ∀ y' p q y : V, y = p ^⋏ q → y' = p ^⋏ q → y = y' := by
  simp [qqAndFun, qqAndFunB, models_iff, Matrix.vecForall_iff]
theorem pa_proves_qqAndFun : 𝗣𝗔 ⊢ qqAndFun :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_qqAndFun.mpr fun _ _ _ _ h1 h2 ↦ by subst_vars; first | rfl | assumption | trivial
theorem lib_qqAndFun : Lib qqAndFun := Lib.of_pa pa_proves_qqAndFun

/-- functionality of `setShift`. -/
noncomputable def setShiftFunB : ArithmeticSemisentence 3 :=
  “y' s y. !(setShiftGraph LAct) y s → !(setShiftGraph LAct) y' s → y = y'”
noncomputable def setShiftFun : ArithmeticSentence := ∀¹* setShiftFunB
lemma models_setShiftFun : V↓[ℒₒᵣ] ⊧ setShiftFun ↔ ∀ y' s y : V, y = setShift LAct s → y' = setShift LAct s → y = y' := by
  simp [setShiftFun, setShiftFunB, models_iff, Matrix.vecForall_iff, setShift.defined.iff]
theorem pa_proves_setShiftFun : 𝗣𝗔 ⊢ setShiftFun :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_setShiftFun.mpr fun _ _ _ h1 h2 ↦ by subst_vars; first | rfl | assumption | trivial
theorem lib_setShiftFun : Lib setShiftFun := Lib.of_pa pa_proves_setShiftFun

/-! ### D. Sets: extensionality and `setShift` on a chain (§3.4, §4.5) -/

/-- `s ⊆ t → t ⊆ s → s = t` (extensionality of bit-sets, `mem_ext`). -/
noncomputable def subsetAntisymmB : ArithmeticSemisentence 2 :=
  “t s. !bitSubsetDef s t → !bitSubsetDef t s → s = t”
noncomputable def subsetAntisymm : ArithmeticSentence := ∀¹* subsetAntisymmB
lemma models_subsetAntisymm : V↓[ℒₒᵣ] ⊧ subsetAntisymm ↔ ∀ t s : V, s ⊆ t → t ⊆ s → s = t := by
  simp [subsetAntisymm, subsetAntisymmB, models_iff, Matrix.vecForall_iff]
theorem pa_proves_subsetAntisymm : 𝗣𝗔 ⊢ subsetAntisymm :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_subsetAntisymm.mpr fun _ _ h₁ h₂ ↦ mem_ext fun i ↦ ⟨fun h ↦ h₁ h, fun h ↦ h₂ h⟩
theorem lib_subsetAntisymm : Lib subsetAntisymm := Lib.of_pa pa_proves_subsetAntisymm

/-- `s' = insert x s → u = setShift s → y = shift x → u' = insert y u → u' = setShift s'` (`setShift_insert`). -/
noncomputable def setShiftInsertB : ArithmeticSemisentence 6 :=
  “u' u y x s' s. !insertDef s' x s → !(setShiftGraph LAct) u s → !(shiftGraph LAct) y x → !insertDef u' y u → !(setShiftGraph LAct) u' s'”
noncomputable def setShiftInsert : ArithmeticSentence := ∀¹* setShiftInsertB
lemma models_setShiftInsert : V↓[ℒₒᵣ] ⊧ setShiftInsert ↔ ∀ u' u y x s' s : V, s' = insert x s → u = setShift LAct s → y = shift LAct x → u' = insert y u → u' = setShift LAct s' := by
  simp [setShiftInsert, setShiftInsertB, models_iff, Matrix.vecForall_iff, setShift.defined.iff, shift.defined.iff]
theorem pa_proves_setShiftInsert : 𝗣𝗔 ⊢ setShiftInsert :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_setShiftInsert.mpr fun _ _ _ _ _ _ h₁ h₂ h₃ h₄ ↦ by subst_vars; exact (setShift_insert _ _).symm
theorem lib_setShiftInsert : Lib setShiftInsert := Lib.of_pa pa_proves_setShiftInsert

/-- `u = setShift ∅ → u = ∅` (`∅ = 0`). -/
noncomputable def setShiftEmptyB : ArithmeticSemisentence 1 :=
  “u. !(setShiftGraph LAct) u 0 → u = 0”
noncomputable def setShiftEmpty : ArithmeticSentence := ∀¹* setShiftEmptyB
lemma models_setShiftEmpty : V↓[ℒₒᵣ] ⊧ setShiftEmpty ↔ ∀ u : V, u = setShift LAct (0 : V) → u = (0 : V) := by
  simp [setShiftEmpty, setShiftEmptyB, models_iff, Matrix.vecForall_iff, setShift.defined.iff]
theorem pa_proves_setShiftEmpty : 𝗣𝗔 ⊢ setShiftEmpty :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_setShiftEmpty.mpr fun _ h₁ ↦ by subst_vars; exact setShift_zero
theorem lib_setShiftEmpty : Lib setShiftEmpty := Lib.of_pa pa_proves_setShiftEmpty

/-! ### E. The ten `fstIdx<Tag>` rows (§4.0 step 2) -/

/-- `e = axL s p → fstIdx e = s`. -/
noncomputable def fstIdxAxLB : ArithmeticSemisentence 3 :=
  “e p s. !axLGraph e s p → !fstIdxDef s e”
noncomputable def fstIdxAxL : ArithmeticSentence := ∀¹* fstIdxAxLB
lemma models_fstIdxAxL : V↓[ℒₒᵣ] ⊧ fstIdxAxL ↔ ∀ e p s : V, e = axL s p → s = fstIdx e := by
  simp [fstIdxAxL, fstIdxAxLB, models_iff, Matrix.vecForall_iff]
theorem pa_proves_fstIdxAxL : 𝗣𝗔 ⊢ fstIdxAxL :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_fstIdxAxL.mpr fun _ _ _ h₁ ↦ by subst_vars; simp
theorem lib_fstIdxAxL : Lib fstIdxAxL := Lib.of_pa pa_proves_fstIdxAxL

/-- `e = verumIntro s → fstIdx e = s`. -/
noncomputable def fstIdxVerumB : ArithmeticSemisentence 2 :=
  “e s. !verumIntroGraph e s → !fstIdxDef s e”
noncomputable def fstIdxVerum : ArithmeticSentence := ∀¹* fstIdxVerumB
lemma models_fstIdxVerum : V↓[ℒₒᵣ] ⊧ fstIdxVerum ↔ ∀ e s : V, e = verumIntro s → s = fstIdx e := by
  simp [fstIdxVerum, fstIdxVerumB, models_iff, Matrix.vecForall_iff]
theorem pa_proves_fstIdxVerum : 𝗣𝗔 ⊢ fstIdxVerum :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_fstIdxVerum.mpr fun _ _ h₁ ↦ by subst_vars; simp
theorem lib_fstIdxVerum : Lib fstIdxVerum := Lib.of_pa pa_proves_fstIdxVerum

/-- `e = andIntro s p q dp dq → fstIdx e = s`. -/
noncomputable def fstIdxAndB : ArithmeticSemisentence 6 :=
  “e dq dp q p s. !andIntroGraph e s p q dp dq → !fstIdxDef s e”
noncomputable def fstIdxAnd : ArithmeticSentence := ∀¹* fstIdxAndB
lemma models_fstIdxAnd : V↓[ℒₒᵣ] ⊧ fstIdxAnd ↔ ∀ e dq dp q p s : V, e = andIntro s p q dp dq → s = fstIdx e := by
  simp [fstIdxAnd, fstIdxAndB, models_iff, Matrix.vecForall_iff]
theorem pa_proves_fstIdxAnd : 𝗣𝗔 ⊢ fstIdxAnd :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_fstIdxAnd.mpr fun _ _ _ _ _ _ h₁ ↦ by subst_vars; simp
theorem lib_fstIdxAnd : Lib fstIdxAnd := Lib.of_pa pa_proves_fstIdxAnd

/-- `e = orIntro s p q d → fstIdx e = s`. -/
noncomputable def fstIdxOrB : ArithmeticSemisentence 5 :=
  “e d q p s. !orIntroGraph e s p q d → !fstIdxDef s e”
noncomputable def fstIdxOr : ArithmeticSentence := ∀¹* fstIdxOrB
lemma models_fstIdxOr : V↓[ℒₒᵣ] ⊧ fstIdxOr ↔ ∀ e d q p s : V, e = orIntro s p q d → s = fstIdx e := by
  simp [fstIdxOr, fstIdxOrB, models_iff, Matrix.vecForall_iff]
theorem pa_proves_fstIdxOr : 𝗣𝗔 ⊢ fstIdxOr :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_fstIdxOr.mpr fun _ _ _ _ _ h₁ ↦ by subst_vars; simp
theorem lib_fstIdxOr : Lib fstIdxOr := Lib.of_pa pa_proves_fstIdxOr

/-- `e = allIntro s p d → fstIdx e = s`. -/
noncomputable def fstIdxAllB : ArithmeticSemisentence 4 :=
  “e d p s. !allIntroGraph e s p d → !fstIdxDef s e”
noncomputable def fstIdxAll : ArithmeticSentence := ∀¹* fstIdxAllB
lemma models_fstIdxAll : V↓[ℒₒᵣ] ⊧ fstIdxAll ↔ ∀ e d p s : V, e = allIntro s p d → s = fstIdx e := by
  simp [fstIdxAll, fstIdxAllB, models_iff, Matrix.vecForall_iff]
theorem pa_proves_fstIdxAll : 𝗣𝗔 ⊢ fstIdxAll :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_fstIdxAll.mpr fun _ _ _ _ h₁ ↦ by subst_vars; simp
theorem lib_fstIdxAll : Lib fstIdxAll := Lib.of_pa pa_proves_fstIdxAll

/-- `e = exsIntro s p t d → fstIdx e = s`. -/
noncomputable def fstIdxExsB : ArithmeticSemisentence 5 :=
  “e d t p s. !exsIntroGraph e s p t d → !fstIdxDef s e”
noncomputable def fstIdxExs : ArithmeticSentence := ∀¹* fstIdxExsB
lemma models_fstIdxExs : V↓[ℒₒᵣ] ⊧ fstIdxExs ↔ ∀ e d t p s : V, e = exsIntro s p t d → s = fstIdx e := by
  simp [fstIdxExs, fstIdxExsB, models_iff, Matrix.vecForall_iff]
theorem pa_proves_fstIdxExs : 𝗣𝗔 ⊢ fstIdxExs :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_fstIdxExs.mpr fun _ _ _ _ _ h₁ ↦ by subst_vars; simp
theorem lib_fstIdxExs : Lib fstIdxExs := Lib.of_pa pa_proves_fstIdxExs

/-- `e = wkRule s d → fstIdx e = s`. -/
noncomputable def fstIdxWkB : ArithmeticSemisentence 3 :=
  “e d s. !wkRuleGraph e s d → !fstIdxDef s e”
noncomputable def fstIdxWk : ArithmeticSentence := ∀¹* fstIdxWkB
lemma models_fstIdxWk : V↓[ℒₒᵣ] ⊧ fstIdxWk ↔ ∀ e d s : V, e = wkRule s d → s = fstIdx e := by
  simp [fstIdxWk, fstIdxWkB, models_iff, Matrix.vecForall_iff]
theorem pa_proves_fstIdxWk : 𝗣𝗔 ⊢ fstIdxWk :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_fstIdxWk.mpr fun _ _ _ h₁ ↦ by subst_vars; simp
theorem lib_fstIdxWk : Lib fstIdxWk := Lib.of_pa pa_proves_fstIdxWk

/-- `e = shiftRule s d → fstIdx e = s` (the node's sequent is the shifted one, `introShiftB`). -/
noncomputable def fstIdxShiftB : ArithmeticSemisentence 3 :=
  “e d s. !shiftRuleGraph e s d → !fstIdxDef s e”
noncomputable def fstIdxShift : ArithmeticSentence := ∀¹* fstIdxShiftB
lemma models_fstIdxShift : V↓[ℒₒᵣ] ⊧ fstIdxShift ↔ ∀ e d s : V, e = shiftRule s d → s = fstIdx e := by
  simp [fstIdxShift, fstIdxShiftB, models_iff, Matrix.vecForall_iff]
theorem pa_proves_fstIdxShift : 𝗣𝗔 ⊢ fstIdxShift :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_fstIdxShift.mpr fun _ _ _ h₁ ↦ by subst_vars; simp
theorem lib_fstIdxShift : Lib fstIdxShift := Lib.of_pa pa_proves_fstIdxShift

/-- `e = cutRule s p d₁ d₂ → fstIdx e = s`. -/
noncomputable def fstIdxCutB : ArithmeticSemisentence 5 :=
  “e d₂ d₁ p s. !cutRuleGraph e s p d₁ d₂ → !fstIdxDef s e”
noncomputable def fstIdxCut : ArithmeticSentence := ∀¹* fstIdxCutB
lemma models_fstIdxCut : V↓[ℒₒᵣ] ⊧ fstIdxCut ↔ ∀ e d₂ d₁ p s : V, e = cutRule s p d₁ d₂ → s = fstIdx e := by
  simp [fstIdxCut, fstIdxCutB, models_iff, Matrix.vecForall_iff]
theorem pa_proves_fstIdxCut : 𝗣𝗔 ⊢ fstIdxCut :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_fstIdxCut.mpr fun _ _ _ _ _ h₁ ↦ by subst_vars; simp
theorem lib_fstIdxCut : Lib fstIdxCut := Lib.of_pa pa_proves_fstIdxCut

/-- `e = axm s p → fstIdx e = s`. -/
noncomputable def fstIdxAxmB : ArithmeticSemisentence 3 :=
  “e p s. !axmGraph e s p → !fstIdxDef s e”
noncomputable def fstIdxAxm : ArithmeticSentence := ∀¹* fstIdxAxmB
lemma models_fstIdxAxm : V↓[ℒₒᵣ] ⊧ fstIdxAxm ↔ ∀ e p s : V, e = axm s p → s = fstIdx e := by
  simp [fstIdxAxm, fstIdxAxmB, models_iff, Matrix.vecForall_iff]
theorem pa_proves_fstIdxAxm : 𝗣𝗔 ⊢ fstIdxAxm :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_fstIdxAxm.mpr fun _ _ _ h₁ ↦ by subst_vars; simp
theorem lib_fstIdxAxm : Lib fstIdxAxm := Lib.of_pa pa_proves_fstIdxAxm

/-! ### F. The top: `dlenDef`, `proof`, `instB`, `gBudget`, `‖·‖`, the `bnum` certification (§7.1) -/

/-- `derivation d → dlenGraph d n → dlen d = n` (the `dlenDef` graph from the derivation graph, §7.1 step 7). -/
noncomputable def dlenDefIntroB : ArithmeticSemisentence 2 :=
  “n d. !(derivation TAct).sigma d → !(dlenGraphDef LAct).sigma d n → !(dlenDef TAct) n d”
noncomputable def dlenDefIntro : ArithmeticSentence := ∀¹* dlenDefIntroB
lemma models_dlenDefIntro : V↓[ℒₒᵣ] ⊧ dlenDefIntro ↔ ∀ n d : V, Derivation TAct d → DlenGraph LAct d n → n = dlen TAct d := by
  simp [dlenDefIntro, dlenDefIntroB, models_iff, Matrix.vecForall_iff, dlen_defined.iff]
theorem pa_proves_dlenDefIntro : 𝗣𝗔 ⊢ dlenDefIntro :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_dlenDefIntro.mpr fun _ _ h₁ h₂ ↦ (dlen_eq_of_graph h₁ h₂).symm
theorem lib_dlenDefIntro : Lib dlenDefIntro := Lib.of_pa pa_proves_dlenDefIntro

/-- `s = insert g ∅ → fstIdx d = s → derivation d → proof d g`. -/
noncomputable def proofIntroB : ArithmeticSemisentence 3 :=
  “d g s. !insertDef s g 0 → !fstIdxDef s d → !(derivation TAct).sigma d → !(proof TAct).sigma d g”
noncomputable def proofIntro : ArithmeticSentence := ∀¹* proofIntroB
lemma models_proofIntro : V↓[ℒₒᵣ] ⊧ proofIntro ↔ ∀ d g s : V, s = insert g (0 : V) → s = fstIdx d → Derivation TAct d → Proof TAct d g := by
  simp [proofIntro, proofIntroB, models_iff, Matrix.vecForall_iff]
theorem pa_proves_proofIntro : 𝗣𝗔 ⊢ proofIntro :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_proofIntro.mpr fun _ _ _ h₁ h₂ h₃ ↦ ⟨by rw [← h₂, h₁]; exact mem_ext fun _ ↦ by simp, h₃⟩
theorem lib_proofIntro : Lib proofIntro := Lib.of_pa pa_proves_proofIntro

/-- `t = bnum k → v = t ∷ 0 → g = subst v n → g = instB n k`. -/
noncomputable def instBIntroB : ArithmeticSemisentence 5 :=
  “g v t k n. !bnumGraph t k → !adjoinDef v t 0 → !(substsGraph LAct) g v n → !instBGraph g n k”
noncomputable def instBIntro : ArithmeticSentence := ∀¹* instBIntroB
lemma models_instBIntro : V↓[ℒₒᵣ] ⊧ instBIntro ↔ ∀ g v t k n : V, t = bnum k → v = t ∷ (0 : V) → g = subst LAct v n → g = instB n k := by
  simp [instBIntro, instBIntroB, models_iff, Matrix.vecForall_iff, bnum.defined.iff, subst.defined.iff, instB.defined.iff]
theorem pa_proves_instBIntro : 𝗣𝗔 ⊢ instBIntro :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_instBIntro.mpr fun _ _ _ _ _ h1 h2 h3 ↦ by subst_vars; first | rfl | assumption | trivial
theorem lib_instBIntro : Lib instBIntro := Lib.of_pa pa_proves_instBIntro

/-- `t = func 0 0 0 → t = bnum 0` (`𝟎` as the walk writes it). -/
noncomputable def bnumZeroCertB : ArithmeticSemisentence 1 :=
  “t. !qqFuncDef t 0 0 0 → !bnumGraph t 0”
noncomputable def bnumZeroCert : ArithmeticSentence := ∀¹* bnumZeroCertB
lemma models_bnumZeroCert : V↓[ℒₒᵣ] ⊧ bnumZeroCert ↔ ∀ t : V, t = ^func (0 : V) (0 : V) (0 : V) → t = bnum (0 : V) := by
  simp [bnumZeroCert, bnumZeroCertB, models_iff, Matrix.vecForall_iff, bnum.defined.iff]
theorem pa_proves_bnumZeroCert : 𝗣𝗔 ⊢ bnumZeroCert :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_bnumZeroCert.mpr fun _ h₁ ↦ by subst_vars; rw [bnum_zero]; simp only [Arithmetic.zero, qqFuncN_eq_qqFunc, qqFunc_absolute, coe_zeroIndex_eq, Nat.cast_zero]
theorem lib_bnumZeroCert : Lib bnumZeroCert := Lib.of_pa pa_proves_bnumZeroCert

/-- `t = func 0 (0 + 1) 0 → t = bnum 1` (`𝟏` as the walk writes it). -/
noncomputable def bnumOneCertB : ArithmeticSemisentence 1 :=
  “t. !qqFuncDef t 0 (0 + 1) 0 → !bnumGraph t 1”
noncomputable def bnumOneCert : ArithmeticSentence := ∀¹* bnumOneCertB
lemma models_bnumOneCert : V↓[ℒₒᵣ] ⊧ bnumOneCert ↔ ∀ t : V, t = ^func (0 : V) ((0 : V) + 1) (0 : V) → t = bnum (1 : V) := by
  simp [bnumOneCert, bnumOneCertB, models_iff, Matrix.vecForall_iff, bnum.defined.iff]
theorem pa_proves_bnumOneCert : 𝗣𝗔 ⊢ bnumOneCert :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_bnumOneCert.mpr fun _ h₁ ↦ by subst_vars; rw [bnum_one]; simp only [Arithmetic.one, qqFuncN_eq_qqFunc, qqFunc_absolute, coe_oneIndex_eq, Nat.cast_zero, zero_add]
theorem lib_bnumOneCert : Lib bnumOneCert := Lib.of_pa pa_proves_bnumOneCert

/-- `1 ≤ m → t = bnum m → u = 𝟐 ^* t (as `func`/`∷` facts) → u = bnum (2 * m)` (`bnum_two_mul`). -/
noncomputable def bnumEvenCertB : ArithmeticSemisentence 9 :=
  “u v v' two w w' one t m. 1 ≤ m → !bnumGraph t m → !qqFuncDef one 0 (0 + 1) 0 → !adjoinDef w' one 0 → !adjoinDef w one w' → !qqFuncDef two (0 + 1 + 1) 0 w → !adjoinDef v' t 0 → !adjoinDef v two v' → !qqFuncDef u (0 + 1 + 1) (0 + 1) v → !bnumGraph u (2 * m)”
noncomputable def bnumEvenCert : ArithmeticSentence := ∀¹* bnumEvenCertB
lemma models_bnumEvenCert : V↓[ℒₒᵣ] ⊧ bnumEvenCert ↔ ∀ u v v' two w w' one t m : V, (1 : V) ≤ m → t = bnum m → one = ^func (0 : V) ((0 : V) + 1) (0 : V) → w' = one ∷ (0 : V) → w = one ∷ w' → two = ^func ((0 : V) + 1 + 1) (0 : V) w → v' = t ∷ (0 : V) → v = two ∷ v' → u = ^func ((0 : V) + 1 + 1) ((0 : V) + 1) v → u = bnum ((2 : V) * m) := by
  simp [bnumEvenCert, bnumEvenCertB, models_iff, Matrix.vecForall_iff, bnum.defined.iff]
theorem pa_proves_bnumEvenCert : 𝗣𝗔 ⊢ bnumEvenCert :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_bnumEvenCert.mpr fun _ _ _ _ _ _ _ _ _ h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ h₉ ↦ by subst_vars; rw [bnum_two_mul h₁]; simp only [qqTwo, qqMul, qqAdd, coe_mulIndex_eq, coe_addIndex_eq, Arithmetic.one, qqFuncN_eq_qqFunc, qqFunc_absolute, coe_oneIndex_eq, Nat.cast_zero, zero_add, one_add_one_eq_two]
theorem lib_bnumEvenCert : Lib bnumEvenCert := Lib.of_pa pa_proves_bnumEvenCert

/-- `1 ≤ m → t = bnum m → u = (𝟐 ^* t) ^+ 𝟏 (as `func`/`∷` facts) → u = bnum (2 * m + 1)` (`bnum_two_mul_add_one`). -/
noncomputable def bnumOddCertB : ArithmeticSemisentence 12 :=
  “u x x' s v v' two w w' one t m. 1 ≤ m → !bnumGraph t m → !qqFuncDef one 0 (0 + 1) 0 → !adjoinDef w' one 0 → !adjoinDef w one w' → !qqFuncDef two (0 + 1 + 1) 0 w → !adjoinDef v' t 0 → !adjoinDef v two v' → !qqFuncDef s (0 + 1 + 1) (0 + 1) v → !adjoinDef x' one 0 → !adjoinDef x s x' → !qqFuncDef u (0 + 1 + 1) 0 x → !bnumGraph u ((2 * m) + 1)”

/-! ### G. Lengths: `termLenVec`/`listSum` bottom-up, the atom lengths with universal `M, s` (§3.6) -/

/-- `termLenVec 0 0 = 0` (dummy binder `x`: a CLOSED row over a blueprint graph hangs `simp`). -/
noncomputable def termLenVecNilB : ArithmeticSemisentence 1 :=
  “x. !(termLenVecGraph LAct) 0 0 0”
noncomputable def termLenVecNil : ArithmeticSentence := ∀¹* termLenVecNilB
lemma models_termLenVecNil : V↓[ℒₒᵣ] ⊧ termLenVecNil ↔ ∀ x : V, (0 : V) = termLenVec LAct (0 : V) (0 : V) := by
  simp [termLenVecNil, termLenVecNilB, models_iff, Matrix.vecForall_iff, termLenVec.defined.iff]
theorem pa_proves_termLenVecNil : 𝗣𝗔 ⊢ termLenVecNil :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_termLenVecNil.mpr fun _ ↦ by exact termLenVec_nil.symm
theorem lib_termLenVecNil : Lib termLenVecNil := Lib.of_pa pa_proves_termLenVecNil

/-- `termLenVec (k + 1) (t ∷ v) = termLen t ∷ termLenVec k v` bottom-up. -/
noncomputable def termLenVecAdjB : ArithmeticSemisentence 8 :=
  “M' M l t v' v k n. !(isSemiterm LAct).pi n t → !(isUTermVec LAct).pi k v → !(termLenGraph LAct) l t → !(termLenVecGraph LAct) M k v → !adjoinDef v' t v → !adjoinDef M' l M → !(termLenVecGraph LAct) M' (k + 1) v'”
noncomputable def termLenVecAdj : ArithmeticSentence := ∀¹* termLenVecAdjB
lemma models_termLenVecAdj : V↓[ℒₒᵣ] ⊧ termLenVecAdj ↔ ∀ M' M l t v' v k n : V, IsSemiterm LAct n t → IsUTermVec LAct k v → l = termLen LAct t → M = termLenVec LAct k v → v' = t ∷ v → M' = l ∷ M → M' = termLenVec LAct (k + 1) v' := by
  simp [termLenVecAdj, termLenVecAdjB, models_iff, Matrix.vecForall_iff, termLen.defined.iff, termLenVec.defined.iff]
theorem pa_proves_termLenVecAdj : 𝗣𝗔 ⊢ termLenVecAdj :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_termLenVecAdj.mpr fun _ _ _ _ _ _ _ _ h₁ h₂ h₃ h₄ h₅ h₆ ↦ by subst_vars; exact (termLenVec_cons h₁.isUTerm h₂).symm
theorem lib_termLenVecAdj : Lib termLenVecAdj := Lib.of_pa pa_proves_termLenVecAdj

/-- `listSum 0 = 0` (dummy binder). -/
noncomputable def listSumNilB : ArithmeticSemisentence 1 :=
  “x. !listSumDef 0 0”
noncomputable def listSumNil : ArithmeticSentence := ∀¹* listSumNilB
lemma models_listSumNil : V↓[ℒₒᵣ] ⊧ listSumNil ↔ ∀ x : V, (0 : V) = listSum (0 : V) := by
  simp [listSumNil, listSumNilB, models_iff, Matrix.vecForall_iff, listSum_defined.iff]
theorem pa_proves_listSumNil : 𝗣𝗔 ⊢ listSumNil :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_listSumNil.mpr fun _ ↦ by exact listSum_nil.symm
theorem lib_listSumNil : Lib listSumNil := Lib.of_pa pa_proves_listSumNil

/-- `listSum (l ∷ M) = l + listSum M`. -/
noncomputable def listSumAdjB : ArithmeticSemisentence 5 :=
  “s' s l M M'. !listSumDef s M → !adjoinDef M' l M → !listSumDef s' M' → s' = (l + s)”
noncomputable def listSumAdj : ArithmeticSentence := ∀¹* listSumAdjB
lemma models_listSumAdj : V↓[ℒₒᵣ] ⊧ listSumAdj ↔ ∀ s' s l M M' : V, s = listSum M → M' = l ∷ M → s' = listSum M' → s' = (l + s) := by
  simp [listSumAdj, listSumAdjB, models_iff, Matrix.vecForall_iff, listSum_defined.iff]
theorem pa_proves_listSumAdj : 𝗣𝗔 ⊢ listSumAdj :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_listSumAdj.mpr fun _ _ _ _ _ h₁ h₂ h₃ ↦ by subst_vars; exact listSum_adjoin _ _
theorem lib_listSumAdj : Lib listSumAdj := Lib.of_pa pa_proves_listSumAdj

/-- `formulaLen (rel k R v) = listSum (termLenVec k v) + 1` with `M, s` universal (§3.6). -/
noncomputable def formulaLenRelCertB : ArithmeticSemisentence 7 :=
  “l s M p v R k. !LAct.isRel k R → !(isUTermVec LAct).pi k v → !qqRelDef p k R v → !(termLenVecGraph LAct) M k v → !listSumDef s M → !(formulaLenGraph LAct) l p → l = (s + 1)”
noncomputable def formulaLenRelCert : ArithmeticSentence := ∀¹* formulaLenRelCertB
lemma models_formulaLenRelCert : V↓[ℒₒᵣ] ⊧ formulaLenRelCert ↔ ∀ l s M p v R k : V, LAct.IsRel k R → IsUTermVec LAct k v → p = ^rel k R v → M = termLenVec LAct k v → s = listSum M → l = formulaLen LAct p → l = (s + 1) := by
  simp [formulaLenRelCert, formulaLenRelCertB, models_iff, Matrix.vecForall_iff, termLenVec.defined.iff, listSum_defined.iff, formulaLen.defined.iff]
theorem pa_proves_formulaLenRelCert : 𝗣𝗔 ⊢ formulaLenRelCert :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_formulaLenRelCert.mpr fun _ _ _ _ _ _ _ h₁ h₂ h₃ h₄ h₅ h₆ ↦ by subst_vars; exact formulaLen_rel h₁ h₂
theorem lib_formulaLenRelCert : Lib formulaLenRelCert := Lib.of_pa pa_proves_formulaLenRelCert

/-- the `nrel` twin. -/
noncomputable def formulaLenNRelCertB : ArithmeticSemisentence 7 :=
  “l s M p v R k. !LAct.isRel k R → !(isUTermVec LAct).pi k v → !qqNRelDef p k R v → !(termLenVecGraph LAct) M k v → !listSumDef s M → !(formulaLenGraph LAct) l p → l = (s + 1)”
noncomputable def formulaLenNRelCert : ArithmeticSentence := ∀¹* formulaLenNRelCertB
lemma models_formulaLenNRelCert : V↓[ℒₒᵣ] ⊧ formulaLenNRelCert ↔ ∀ l s M p v R k : V, LAct.IsRel k R → IsUTermVec LAct k v → p = ^nrel k R v → M = termLenVec LAct k v → s = listSum M → l = formulaLen LAct p → l = (s + 1) := by
  simp [formulaLenNRelCert, formulaLenNRelCertB, models_iff, Matrix.vecForall_iff, termLenVec.defined.iff, listSum_defined.iff, formulaLen.defined.iff]
theorem pa_proves_formulaLenNRelCert : 𝗣𝗔 ⊢ formulaLenNRelCert :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_formulaLenNRelCert.mpr fun _ _ _ _ _ _ _ h₁ h₂ h₃ h₄ h₅ h₆ ↦ by subst_vars; exact formulaLen_nrel h₁ h₂
theorem lib_formulaLenNRelCert : Lib formulaLenNRelCert := Lib.of_pa pa_proves_formulaLenNRelCert

/-- `termLen (func k f v) = listSum (termLenVec k v) + 1` with `M, s` universal. -/
noncomputable def termLenFuncCertB : ArithmeticSemisentence 7 :=
  “l s M t v f k. !LAct.isFunc k f → !(isUTermVec LAct).pi k v → !qqFuncDef t k f v → !(termLenVecGraph LAct) M k v → !listSumDef s M → !(termLenGraph LAct) l t → l = (s + 1)”
noncomputable def termLenFuncCert : ArithmeticSentence := ∀¹* termLenFuncCertB
lemma models_termLenFuncCert : V↓[ℒₒᵣ] ⊧ termLenFuncCert ↔ ∀ l s M t v f k : V, LAct.IsFunc k f → IsUTermVec LAct k v → t = ^func k f v → M = termLenVec LAct k v → s = listSum M → l = termLen LAct t → l = (s + 1) := by
  simp [termLenFuncCert, termLenFuncCertB, models_iff, Matrix.vecForall_iff, termLenVec.defined.iff, listSum_defined.iff, termLen.defined.iff]
theorem pa_proves_termLenFuncCert : 𝗣𝗔 ⊢ termLenFuncCert :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_termLenFuncCert.mpr fun _ _ _ _ _ _ _ h₁ h₂ h₃ h₄ h₅ h₆ ↦ by subst_vars; exact termLen_func h₁ h₂
theorem lib_termLenFuncCert : Lib termLenFuncCert := Lib.of_pa pa_proves_termLenFuncCert

/-! ### H. Certification: `neg`/`shift`/`subst`/`free` bottom-up, the term level, `qVec` (§3.6) -/

/-- `neg (rel k R v) = nrel k R v` bottom-up. -/
noncomputable def negRelCertB : ArithmeticSemisentence 5 :=
  “y v R k r. !LAct.isRel k R → !(isUTermVec LAct).pi k v → !qqRelDef r k R v → !qqNRelDef y k R v → !(negGraph LAct) y r”
noncomputable def negRelCert : ArithmeticSentence := ∀¹* negRelCertB
lemma models_negRelCert : V↓[ℒₒᵣ] ⊧ negRelCert ↔ ∀ y v R k r : V, LAct.IsRel k R → IsUTermVec LAct k v → r = ^rel k R v → y = ^nrel k R v → y = neg LAct r := by
  simp [negRelCert, negRelCertB, models_iff, Matrix.vecForall_iff]
theorem pa_proves_negRelCert : 𝗣𝗔 ⊢ negRelCert :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_negRelCert.mpr fun _ _ _ _ _ h₁ h₂ h₃ h₄ ↦ by subst_vars; exact (neg_rel h₁ h₂).symm
theorem lib_negRelCert : Lib negRelCert := Lib.of_pa pa_proves_negRelCert

/-- `neg (nrel k R v) = rel k R v` bottom-up. -/
noncomputable def negNRelCertB : ArithmeticSemisentence 5 :=
  “y v R k r. !LAct.isRel k R → !(isUTermVec LAct).pi k v → !qqNRelDef r k R v → !qqRelDef y k R v → !(negGraph LAct) y r”
noncomputable def negNRelCert : ArithmeticSentence := ∀¹* negNRelCertB
lemma models_negNRelCert : V↓[ℒₒᵣ] ⊧ negNRelCert ↔ ∀ y v R k r : V, LAct.IsRel k R → IsUTermVec LAct k v → r = ^nrel k R v → y = ^rel k R v → y = neg LAct r := by
  simp [negNRelCert, negNRelCertB, models_iff, Matrix.vecForall_iff]
theorem pa_proves_negNRelCert : 𝗣𝗔 ⊢ negNRelCert :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_negNRelCert.mpr fun _ _ _ _ _ h₁ h₂ h₃ h₄ ↦ by subst_vars; exact (neg_nrel h₁ h₂).symm
theorem lib_negNRelCert : Lib negNRelCert := Lib.of_pa pa_proves_negNRelCert

/-- `neg ⊤ = ⊥`. -/
noncomputable def negVerumCertB : ArithmeticSemisentence 2 :=
  “y r. !qqVerumDef r → !qqFalsumDef y → !(negGraph LAct) y r”
noncomputable def negVerumCert : ArithmeticSentence := ∀¹* negVerumCertB
lemma models_negVerumCert : V↓[ℒₒᵣ] ⊧ negVerumCert ↔ ∀ y r : V, r = ^⊤ → y = ^⊥ → y = neg LAct r := by
  simp [negVerumCert, negVerumCertB, models_iff, Matrix.vecForall_iff]
theorem pa_proves_negVerumCert : 𝗣𝗔 ⊢ negVerumCert :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_negVerumCert.mpr fun _ _ h₁ h₂ ↦ by subst_vars; exact neg_verum.symm
theorem lib_negVerumCert : Lib negVerumCert := Lib.of_pa pa_proves_negVerumCert

/-- `neg ⊥ = ⊤`. -/
noncomputable def negFalsumCertB : ArithmeticSemisentence 2 :=
  “y r. !qqFalsumDef r → !qqVerumDef y → !(negGraph LAct) y r”
noncomputable def negFalsumCert : ArithmeticSentence := ∀¹* negFalsumCertB
lemma models_negFalsumCert : V↓[ℒₒᵣ] ⊧ negFalsumCert ↔ ∀ y r : V, r = ^⊥ → y = ^⊤ → y = neg LAct r := by
  simp [negFalsumCert, negFalsumCertB, models_iff, Matrix.vecForall_iff]
theorem pa_proves_negFalsumCert : 𝗣𝗔 ⊢ negFalsumCert :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_negFalsumCert.mpr fun _ _ h₁ h₂ ↦ by subst_vars; exact neg_falsum.symm
theorem lib_negFalsumCert : Lib negFalsumCert := Lib.of_pa pa_proves_negFalsumCert

/-- `neg (p ⋏ q) = neg p ⋎ neg q` bottom-up. -/
noncomputable def negAndCertB : ArithmeticSemisentence 7 :=
  “y nq np r q p n. !(isSemiformula LAct).pi n p → !(isSemiformula LAct).pi n q → !qqAndDef r p q → !(negGraph LAct) np p → !(negGraph LAct) nq q → !qqOrDef y np nq → !(negGraph LAct) y r”
noncomputable def negAndCert : ArithmeticSentence := ∀¹* negAndCertB
lemma models_negAndCert : V↓[ℒₒᵣ] ⊧ negAndCert ↔ ∀ y nq np r q p n : V, IsSemiformula LAct n p → IsSemiformula LAct n q → r = p ^⋏ q → np = neg LAct p → nq = neg LAct q → y = np ^⋎ nq → y = neg LAct r := by
  simp [negAndCert, negAndCertB, models_iff, Matrix.vecForall_iff]
theorem pa_proves_negAndCert : 𝗣𝗔 ⊢ negAndCert :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_negAndCert.mpr fun _ _ _ _ _ _ _ h₁ h₂ h₃ h₄ h₅ h₆ ↦ by subst_vars; exact (neg_and h₁.isUFormula h₂.isUFormula).symm
theorem lib_negAndCert : Lib negAndCert := Lib.of_pa pa_proves_negAndCert

/-- `neg (p ⋎ q) = neg p ⋏ neg q` bottom-up. -/
noncomputable def negOrCertB : ArithmeticSemisentence 7 :=
  “y nq np r q p n. !(isSemiformula LAct).pi n p → !(isSemiformula LAct).pi n q → !qqOrDef r p q → !(negGraph LAct) np p → !(negGraph LAct) nq q → !qqAndDef y np nq → !(negGraph LAct) y r”
noncomputable def negOrCert : ArithmeticSentence := ∀¹* negOrCertB
lemma models_negOrCert : V↓[ℒₒᵣ] ⊧ negOrCert ↔ ∀ y nq np r q p n : V, IsSemiformula LAct n p → IsSemiformula LAct n q → r = p ^⋎ q → np = neg LAct p → nq = neg LAct q → y = np ^⋏ nq → y = neg LAct r := by
  simp [negOrCert, negOrCertB, models_iff, Matrix.vecForall_iff]
theorem pa_proves_negOrCert : 𝗣𝗔 ⊢ negOrCert :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_negOrCert.mpr fun _ _ _ _ _ _ _ h₁ h₂ h₃ h₄ h₅ h₆ ↦ by subst_vars; exact (neg_or h₁.isUFormula h₂.isUFormula).symm
theorem lib_negOrCert : Lib negOrCert := Lib.of_pa pa_proves_negOrCert

/-- `neg (∀ p) = ∃ neg p` bottom-up. -/
noncomputable def negAllCertB : ArithmeticSemisentence 5 :=
  “y np r p n. !(isSemiformula LAct).pi (n + 1) p → !qqAllDef r p → !(negGraph LAct) np p → !qqExsDef y np → !(negGraph LAct) y r”
noncomputable def negAllCert : ArithmeticSentence := ∀¹* negAllCertB
lemma models_negAllCert : V↓[ℒₒᵣ] ⊧ negAllCert ↔ ∀ y np r p n : V, IsSemiformula LAct (n + 1) p → r = ^∀ p → np = neg LAct p → y = ^∃ np → y = neg LAct r := by
  simp [negAllCert, negAllCertB, models_iff, Matrix.vecForall_iff]
theorem pa_proves_negAllCert : 𝗣𝗔 ⊢ negAllCert :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_negAllCert.mpr fun _ _ _ _ _ h₁ h₂ h₃ h₄ ↦ by subst_vars; exact (neg_all h₁.isUFormula).symm
theorem lib_negAllCert : Lib negAllCert := Lib.of_pa pa_proves_negAllCert

/-- `neg (∃ p) = ∀ neg p` bottom-up. -/
noncomputable def negExsCertB : ArithmeticSemisentence 5 :=
  “y np r p n. !(isSemiformula LAct).pi (n + 1) p → !qqExsDef r p → !(negGraph LAct) np p → !qqAllDef y np → !(negGraph LAct) y r”
noncomputable def negExsCert : ArithmeticSentence := ∀¹* negExsCertB
lemma models_negExsCert : V↓[ℒₒᵣ] ⊧ negExsCert ↔ ∀ y np r p n : V, IsSemiformula LAct (n + 1) p → r = ^∃ p → np = neg LAct p → y = ^∀ np → y = neg LAct r := by
  simp [negExsCert, negExsCertB, models_iff, Matrix.vecForall_iff]
theorem pa_proves_negExsCert : 𝗣𝗔 ⊢ negExsCert :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_negExsCert.mpr fun _ _ _ _ _ h₁ h₂ h₃ h₄ ↦ by subst_vars; exact (neg_ex h₁.isUFormula).symm
theorem lib_negExsCert : Lib negExsCert := Lib.of_pa pa_proves_negExsCert

/-- `shift (rel k R v) = rel k R (termShiftVec k v)` bottom-up. -/
noncomputable def shiftRelCertB : ArithmeticSemisentence 6 :=
  “y u v R k r. !LAct.isRel k R → !(isUTermVec LAct).pi k v → !qqRelDef r k R v → !(termShiftVecGraph LAct) u k v → !qqRelDef y k R u → !(shiftGraph LAct) y r”
noncomputable def shiftRelCert : ArithmeticSentence := ∀¹* shiftRelCertB
lemma models_shiftRelCert : V↓[ℒₒᵣ] ⊧ shiftRelCert ↔ ∀ y u v R k r : V, LAct.IsRel k R → IsUTermVec LAct k v → r = ^rel k R v → u = termShiftVec LAct k v → y = ^rel k R u → y = shift LAct r := by
  simp [shiftRelCert, shiftRelCertB, models_iff, Matrix.vecForall_iff, termShiftVec.defined.iff, shift.defined.iff]
theorem pa_proves_shiftRelCert : 𝗣𝗔 ⊢ shiftRelCert :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_shiftRelCert.mpr fun _ _ _ _ _ _ h₁ h₂ h₃ h₄ h₅ ↦ by subst_vars; exact (shift_rel h₁ h₂).symm
theorem lib_shiftRelCert : Lib shiftRelCert := Lib.of_pa pa_proves_shiftRelCert

/-- the `nrel` twin. -/
noncomputable def shiftNRelCertB : ArithmeticSemisentence 6 :=
  “y u v R k r. !LAct.isRel k R → !(isUTermVec LAct).pi k v → !qqNRelDef r k R v → !(termShiftVecGraph LAct) u k v → !qqNRelDef y k R u → !(shiftGraph LAct) y r”
noncomputable def shiftNRelCert : ArithmeticSentence := ∀¹* shiftNRelCertB
lemma models_shiftNRelCert : V↓[ℒₒᵣ] ⊧ shiftNRelCert ↔ ∀ y u v R k r : V, LAct.IsRel k R → IsUTermVec LAct k v → r = ^nrel k R v → u = termShiftVec LAct k v → y = ^nrel k R u → y = shift LAct r := by
  simp [shiftNRelCert, shiftNRelCertB, models_iff, Matrix.vecForall_iff, termShiftVec.defined.iff, shift.defined.iff]
theorem pa_proves_shiftNRelCert : 𝗣𝗔 ⊢ shiftNRelCert :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_shiftNRelCert.mpr fun _ _ _ _ _ _ h₁ h₂ h₃ h₄ h₅ ↦ by subst_vars; exact (shift_nrel h₁ h₂).symm
theorem lib_shiftNRelCert : Lib shiftNRelCert := Lib.of_pa pa_proves_shiftNRelCert

/-- `shift ⊤ = ⊤`. -/
noncomputable def shiftVerumCertB : ArithmeticSemisentence 2 :=
  “y r. !qqVerumDef r → !qqVerumDef y → !(shiftGraph LAct) y r”
noncomputable def shiftVerumCert : ArithmeticSentence := ∀¹* shiftVerumCertB
lemma models_shiftVerumCert : V↓[ℒₒᵣ] ⊧ shiftVerumCert ↔ ∀ y r : V, r = ^⊤ → y = ^⊤ → y = shift LAct r := by
  simp [shiftVerumCert, shiftVerumCertB, models_iff, Matrix.vecForall_iff, shift.defined.iff]
theorem pa_proves_shiftVerumCert : 𝗣𝗔 ⊢ shiftVerumCert :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_shiftVerumCert.mpr fun _ _ h₁ h₂ ↦ by subst_vars; exact shift_verum.symm
theorem lib_shiftVerumCert : Lib shiftVerumCert := Lib.of_pa pa_proves_shiftVerumCert

/-- `shift ⊥ = ⊥`. -/
noncomputable def shiftFalsumCertB : ArithmeticSemisentence 2 :=
  “y r. !qqFalsumDef r → !qqFalsumDef y → !(shiftGraph LAct) y r”
noncomputable def shiftFalsumCert : ArithmeticSentence := ∀¹* shiftFalsumCertB
lemma models_shiftFalsumCert : V↓[ℒₒᵣ] ⊧ shiftFalsumCert ↔ ∀ y r : V, r = ^⊥ → y = ^⊥ → y = shift LAct r := by
  simp [shiftFalsumCert, shiftFalsumCertB, models_iff, Matrix.vecForall_iff, shift.defined.iff]
theorem pa_proves_shiftFalsumCert : 𝗣𝗔 ⊢ shiftFalsumCert :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_shiftFalsumCert.mpr fun _ _ h₁ h₂ ↦ by subst_vars; exact shift_falsum.symm
theorem lib_shiftFalsumCert : Lib shiftFalsumCert := Lib.of_pa pa_proves_shiftFalsumCert

/-- `shift (p ⋏ q)` bottom-up. -/
noncomputable def shiftAndCertB : ArithmeticSemisentence 7 :=
  “y sq sp r q p n. !(isSemiformula LAct).pi n p → !(isSemiformula LAct).pi n q → !qqAndDef r p q → !(shiftGraph LAct) sp p → !(shiftGraph LAct) sq q → !qqAndDef y sp sq → !(shiftGraph LAct) y r”
noncomputable def shiftAndCert : ArithmeticSentence := ∀¹* shiftAndCertB
lemma models_shiftAndCert : V↓[ℒₒᵣ] ⊧ shiftAndCert ↔ ∀ y sq sp r q p n : V, IsSemiformula LAct n p → IsSemiformula LAct n q → r = p ^⋏ q → sp = shift LAct p → sq = shift LAct q → y = sp ^⋏ sq → y = shift LAct r := by
  simp [shiftAndCert, shiftAndCertB, models_iff, Matrix.vecForall_iff, shift.defined.iff]
theorem pa_proves_shiftAndCert : 𝗣𝗔 ⊢ shiftAndCert :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_shiftAndCert.mpr fun _ _ _ _ _ _ _ h₁ h₂ h₃ h₄ h₅ h₆ ↦ by subst_vars; exact (shift_and h₁.isUFormula h₂.isUFormula).symm
theorem lib_shiftAndCert : Lib shiftAndCert := Lib.of_pa pa_proves_shiftAndCert

/-- `shift (p ⋎ q)` bottom-up. -/
noncomputable def shiftOrCertB : ArithmeticSemisentence 7 :=
  “y sq sp r q p n. !(isSemiformula LAct).pi n p → !(isSemiformula LAct).pi n q → !qqOrDef r p q → !(shiftGraph LAct) sp p → !(shiftGraph LAct) sq q → !qqOrDef y sp sq → !(shiftGraph LAct) y r”
noncomputable def shiftOrCert : ArithmeticSentence := ∀¹* shiftOrCertB
lemma models_shiftOrCert : V↓[ℒₒᵣ] ⊧ shiftOrCert ↔ ∀ y sq sp r q p n : V, IsSemiformula LAct n p → IsSemiformula LAct n q → r = p ^⋎ q → sp = shift LAct p → sq = shift LAct q → y = sp ^⋎ sq → y = shift LAct r := by
  simp [shiftOrCert, shiftOrCertB, models_iff, Matrix.vecForall_iff, shift.defined.iff]
theorem pa_proves_shiftOrCert : 𝗣𝗔 ⊢ shiftOrCert :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_shiftOrCert.mpr fun _ _ _ _ _ _ _ h₁ h₂ h₃ h₄ h₅ h₆ ↦ by subst_vars; exact (shift_or h₁.isUFormula h₂.isUFormula).symm
theorem lib_shiftOrCert : Lib shiftOrCert := Lib.of_pa pa_proves_shiftOrCert

/-- `shift (∀ p)` bottom-up. -/
noncomputable def shiftAllCertB : ArithmeticSemisentence 5 :=
  “y sp r p n. !(isSemiformula LAct).pi (n + 1) p → !qqAllDef r p → !(shiftGraph LAct) sp p → !qqAllDef y sp → !(shiftGraph LAct) y r”
noncomputable def shiftAllCert : ArithmeticSentence := ∀¹* shiftAllCertB
lemma models_shiftAllCert : V↓[ℒₒᵣ] ⊧ shiftAllCert ↔ ∀ y sp r p n : V, IsSemiformula LAct (n + 1) p → r = ^∀ p → sp = shift LAct p → y = ^∀ sp → y = shift LAct r := by
  simp [shiftAllCert, shiftAllCertB, models_iff, Matrix.vecForall_iff, shift.defined.iff]
theorem pa_proves_shiftAllCert : 𝗣𝗔 ⊢ shiftAllCert :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_shiftAllCert.mpr fun _ _ _ _ _ h₁ h₂ h₃ h₄ ↦ by subst_vars; exact (shift_all h₁.isUFormula).symm
theorem lib_shiftAllCert : Lib shiftAllCert := Lib.of_pa pa_proves_shiftAllCert

/-- `shift (∃ p)` bottom-up. -/
noncomputable def shiftExsCertB : ArithmeticSemisentence 5 :=
  “y sp r p n. !(isSemiformula LAct).pi (n + 1) p → !qqExsDef r p → !(shiftGraph LAct) sp p → !qqExsDef y sp → !(shiftGraph LAct) y r”
noncomputable def shiftExsCert : ArithmeticSentence := ∀¹* shiftExsCertB
lemma models_shiftExsCert : V↓[ℒₒᵣ] ⊧ shiftExsCert ↔ ∀ y sp r p n : V, IsSemiformula LAct (n + 1) p → r = ^∃ p → sp = shift LAct p → y = ^∃ sp → y = shift LAct r := by
  simp [shiftExsCert, shiftExsCertB, models_iff, Matrix.vecForall_iff, shift.defined.iff]
theorem pa_proves_shiftExsCert : 𝗣𝗔 ⊢ shiftExsCert :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_shiftExsCert.mpr fun _ _ _ _ _ h₁ h₂ h₃ h₄ ↦ by subst_vars; exact (shift_exs h₁.isUFormula).symm
theorem lib_shiftExsCert : Lib shiftExsCert := Lib.of_pa pa_proves_shiftExsCert

/-- `subst w (rel k R v) = rel k R (termSubstVec k w v)` bottom-up. -/
noncomputable def substsRelCertB : ArithmeticSemisentence 7 :=
  “y u v R k r w. !LAct.isRel k R → !(isUTermVec LAct).pi k v → !qqRelDef r k R v → !(termSubstVecGraph LAct) u k w v → !qqRelDef y k R u → !(substsGraph LAct) y w r”
noncomputable def substsRelCert : ArithmeticSentence := ∀¹* substsRelCertB
lemma models_substsRelCert : V↓[ℒₒᵣ] ⊧ substsRelCert ↔ ∀ y u v R k r w : V, LAct.IsRel k R → IsUTermVec LAct k v → r = ^rel k R v → u = termSubstVec LAct k w v → y = ^rel k R u → y = subst LAct w r := by
  simp [substsRelCert, substsRelCertB, models_iff, Matrix.vecForall_iff, termSubstVec.defined.iff, subst.defined.iff]
theorem pa_proves_substsRelCert : 𝗣𝗔 ⊢ substsRelCert :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_substsRelCert.mpr fun _ _ _ _ _ _ _ h₁ h₂ h₃ h₄ h₅ ↦ by subst_vars; exact (substs_rel h₁ h₂).symm
theorem lib_substsRelCert : Lib substsRelCert := Lib.of_pa pa_proves_substsRelCert

/-- the `nrel` twin. -/
noncomputable def substsNRelCertB : ArithmeticSemisentence 7 :=
  “y u v R k r w. !LAct.isRel k R → !(isUTermVec LAct).pi k v → !qqNRelDef r k R v → !(termSubstVecGraph LAct) u k w v → !qqNRelDef y k R u → !(substsGraph LAct) y w r”
noncomputable def substsNRelCert : ArithmeticSentence := ∀¹* substsNRelCertB
lemma models_substsNRelCert : V↓[ℒₒᵣ] ⊧ substsNRelCert ↔ ∀ y u v R k r w : V, LAct.IsRel k R → IsUTermVec LAct k v → r = ^nrel k R v → u = termSubstVec LAct k w v → y = ^nrel k R u → y = subst LAct w r := by
  simp [substsNRelCert, substsNRelCertB, models_iff, Matrix.vecForall_iff, termSubstVec.defined.iff, subst.defined.iff]
theorem pa_proves_substsNRelCert : 𝗣𝗔 ⊢ substsNRelCert :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_substsNRelCert.mpr fun _ _ _ _ _ _ _ h₁ h₂ h₃ h₄ h₅ ↦ by subst_vars; exact (substs_nrel h₁ h₂).symm
theorem lib_substsNRelCert : Lib substsNRelCert := Lib.of_pa pa_proves_substsNRelCert

/-- `subst w ⊤ = ⊤`. -/
noncomputable def substsVerumCertB : ArithmeticSemisentence 3 :=
  “y r w. !qqVerumDef r → !qqVerumDef y → !(substsGraph LAct) y w r”
noncomputable def substsVerumCert : ArithmeticSentence := ∀¹* substsVerumCertB
lemma models_substsVerumCert : V↓[ℒₒᵣ] ⊧ substsVerumCert ↔ ∀ y r w : V, r = ^⊤ → y = ^⊤ → y = subst LAct w r := by
  simp [substsVerumCert, substsVerumCertB, models_iff, Matrix.vecForall_iff, subst.defined.iff]
theorem pa_proves_substsVerumCert : 𝗣𝗔 ⊢ substsVerumCert :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_substsVerumCert.mpr fun _ _ _ h₁ h₂ ↦ by subst_vars; exact (substs_verum _).symm
theorem lib_substsVerumCert : Lib substsVerumCert := Lib.of_pa pa_proves_substsVerumCert

/-- `subst w ⊥ = ⊥`. -/
noncomputable def substsFalsumCertB : ArithmeticSemisentence 3 :=
  “y r w. !qqFalsumDef r → !qqFalsumDef y → !(substsGraph LAct) y w r”
noncomputable def substsFalsumCert : ArithmeticSentence := ∀¹* substsFalsumCertB
lemma models_substsFalsumCert : V↓[ℒₒᵣ] ⊧ substsFalsumCert ↔ ∀ y r w : V, r = ^⊥ → y = ^⊥ → y = subst LAct w r := by
  simp [substsFalsumCert, substsFalsumCertB, models_iff, Matrix.vecForall_iff, subst.defined.iff]
theorem pa_proves_substsFalsumCert : 𝗣𝗔 ⊢ substsFalsumCert :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_substsFalsumCert.mpr fun _ _ _ h₁ h₂ ↦ by subst_vars; exact (substs_falsum _).symm
theorem lib_substsFalsumCert : Lib substsFalsumCert := Lib.of_pa pa_proves_substsFalsumCert

/-- `subst w (p ⋏ q)` bottom-up. -/
noncomputable def substsAndCertB : ArithmeticSemisentence 8 :=
  “y sq sp r q p n w. !(isSemiformula LAct).pi n p → !(isSemiformula LAct).pi n q → !qqAndDef r p q → !(substsGraph LAct) sp w p → !(substsGraph LAct) sq w q → !qqAndDef y sp sq → !(substsGraph LAct) y w r”
noncomputable def substsAndCert : ArithmeticSentence := ∀¹* substsAndCertB
lemma models_substsAndCert : V↓[ℒₒᵣ] ⊧ substsAndCert ↔ ∀ y sq sp r q p n w : V, IsSemiformula LAct n p → IsSemiformula LAct n q → r = p ^⋏ q → sp = subst LAct w p → sq = subst LAct w q → y = sp ^⋏ sq → y = subst LAct w r := by
  simp [substsAndCert, substsAndCertB, models_iff, Matrix.vecForall_iff, subst.defined.iff]
theorem pa_proves_substsAndCert : 𝗣𝗔 ⊢ substsAndCert :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_substsAndCert.mpr fun _ _ _ _ _ _ _ _ h₁ h₂ h₃ h₄ h₅ h₆ ↦ by subst_vars; exact (substs_and h₁.isUFormula h₂.isUFormula).symm
theorem lib_substsAndCert : Lib substsAndCert := Lib.of_pa pa_proves_substsAndCert

/-- `subst w (p ⋎ q)` bottom-up. -/
noncomputable def substsOrCertB : ArithmeticSemisentence 8 :=
  “y sq sp r q p n w. !(isSemiformula LAct).pi n p → !(isSemiformula LAct).pi n q → !qqOrDef r p q → !(substsGraph LAct) sp w p → !(substsGraph LAct) sq w q → !qqOrDef y sp sq → !(substsGraph LAct) y w r”
noncomputable def substsOrCert : ArithmeticSentence := ∀¹* substsOrCertB
lemma models_substsOrCert : V↓[ℒₒᵣ] ⊧ substsOrCert ↔ ∀ y sq sp r q p n w : V, IsSemiformula LAct n p → IsSemiformula LAct n q → r = p ^⋎ q → sp = subst LAct w p → sq = subst LAct w q → y = sp ^⋎ sq → y = subst LAct w r := by
  simp [substsOrCert, substsOrCertB, models_iff, Matrix.vecForall_iff, subst.defined.iff]
theorem pa_proves_substsOrCert : 𝗣𝗔 ⊢ substsOrCert :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_substsOrCert.mpr fun _ _ _ _ _ _ _ _ h₁ h₂ h₃ h₄ h₅ h₆ ↦ by subst_vars; exact (substs_or h₁.isUFormula h₂.isUFormula).symm
theorem lib_substsOrCert : Lib substsOrCert := Lib.of_pa pa_proves_substsOrCert

/-- `subst w (∀ p) = ∀ subst (qVec w) p` bottom-up. -/
noncomputable def substsAllCertB : ArithmeticSemisentence 7 :=
  “y sp u r p n w. !(isSemiformula LAct).pi (n + 1) p → !qqAllDef r p → !(qVecGraph LAct) u w → !(substsGraph LAct) sp u p → !qqAllDef y sp → !(substsGraph LAct) y w r”
noncomputable def substsAllCert : ArithmeticSentence := ∀¹* substsAllCertB
lemma models_substsAllCert : V↓[ℒₒᵣ] ⊧ substsAllCert ↔ ∀ y sp u r p n w : V, IsSemiformula LAct (n + 1) p → r = ^∀ p → u = qVec LAct w → sp = subst LAct u p → y = ^∀ sp → y = subst LAct w r := by
  simp [substsAllCert, substsAllCertB, models_iff, Matrix.vecForall_iff, qVec.defined.iff, subst.defined.iff]
theorem pa_proves_substsAllCert : 𝗣𝗔 ⊢ substsAllCert :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_substsAllCert.mpr fun _ _ _ _ _ _ _ h₁ h₂ h₃ h₄ h₅ ↦ by subst_vars; exact (substs_all h₁.isUFormula).symm
theorem lib_substsAllCert : Lib substsAllCert := Lib.of_pa pa_proves_substsAllCert

/-- `subst w (∃ p) = ∃ subst (qVec w) p` bottom-up. -/
noncomputable def substsExsCertB : ArithmeticSemisentence 7 :=
  “y sp u r p n w. !(isSemiformula LAct).pi (n + 1) p → !qqExsDef r p → !(qVecGraph LAct) u w → !(substsGraph LAct) sp u p → !qqExsDef y sp → !(substsGraph LAct) y w r”
noncomputable def substsExsCert : ArithmeticSentence := ∀¹* substsExsCertB
lemma models_substsExsCert : V↓[ℒₒᵣ] ⊧ substsExsCert ↔ ∀ y sp u r p n w : V, IsSemiformula LAct (n + 1) p → r = ^∃ p → u = qVec LAct w → sp = subst LAct u p → y = ^∃ sp → y = subst LAct w r := by
  simp [substsExsCert, substsExsCertB, models_iff, Matrix.vecForall_iff, qVec.defined.iff, subst.defined.iff]
theorem pa_proves_substsExsCert : 𝗣𝗔 ⊢ substsExsCert :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_substsExsCert.mpr fun _ _ _ _ _ _ _ h₁ h₂ h₃ h₄ h₅ ↦ by subst_vars; exact (substs_ex h₁.isUFormula).symm
theorem lib_substsExsCert : Lib substsExsCert := Lib.of_pa pa_proves_substsExsCert

/-- `z = &0 → sp = shift p → fp = substs1 z sp → fp = free p` (Foundation's definition of `free`). -/
noncomputable def freeCertB : ArithmeticSemisentence 4 :=
  “fp sp z p. !qqFvarDef z 0 → !(shiftGraph LAct) sp p → !(substs1Graph LAct) fp z sp → !(freeGraph LAct) fp p”
noncomputable def freeCert : ArithmeticSentence := ∀¹* freeCertB
lemma models_freeCert : V↓[ℒₒᵣ] ⊧ freeCert ↔ ∀ fp sp z p : V, z = ^&(0 : V) → sp = shift LAct p → fp = substs1 LAct z sp → fp = free LAct p := by
  simp [freeCert, freeCertB, models_iff, Matrix.vecForall_iff, shift.defined.iff, substs1.defined.iff, free.defined.iff]
theorem pa_proves_freeCert : 𝗣𝗔 ⊢ freeCert :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_freeCert.mpr fun _ _ _ _ h1 h2 h3 ↦ by subst_vars; first | rfl | assumption | trivial
theorem lib_freeCert : Lib freeCert := Lib.of_pa pa_proves_freeCert

/-- `w = t ∷ 0 → y = subst w p → y = substs1 t p` (the converse of `substs1Substs`). -/
noncomputable def substsSubsts1B : ArithmeticSemisentence 4 :=
  “y w t p. !adjoinDef w t 0 → !(substsGraph LAct) y w p → !(substs1Graph LAct) y t p”
noncomputable def substsSubsts1 : ArithmeticSentence := ∀¹* substsSubsts1B
lemma models_substsSubsts1 : V↓[ℒₒᵣ] ⊧ substsSubsts1 ↔ ∀ y w t p : V, w = t ∷ (0 : V) → y = subst LAct w p → y = substs1 LAct t p := by
  simp [substsSubsts1, substsSubsts1B, models_iff, Matrix.vecForall_iff, subst.defined.iff, substs1.defined.iff]
theorem pa_proves_substsSubsts1 : 𝗣𝗔 ⊢ substsSubsts1 :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_substsSubsts1.mpr fun _ _ _ _ h1 h2 ↦ by subst_vars; first | rfl | assumption | trivial
theorem lib_substsSubsts1 : Lib substsSubsts1 := Lib.of_pa pa_proves_substsSubsts1

/-- `termShiftVec 0 0 = 0` (dummy binder). -/
noncomputable def tshvNilCertB : ArithmeticSemisentence 1 :=
  “x. !(termShiftVecGraph LAct) 0 0 0”
noncomputable def tshvNilCert : ArithmeticSentence := ∀¹* tshvNilCertB
lemma models_tshvNilCert : V↓[ℒₒᵣ] ⊧ tshvNilCert ↔ ∀ x : V, (0 : V) = termShiftVec LAct (0 : V) (0 : V) := by
  simp [tshvNilCert, tshvNilCertB, models_iff, Matrix.vecForall_iff, termShiftVec.defined.iff]
theorem pa_proves_tshvNilCert : 𝗣𝗔 ⊢ tshvNilCert :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_tshvNilCert.mpr fun _ ↦ by exact termShiftVec_nil.symm
theorem lib_tshvNilCert : Lib tshvNilCert := Lib.of_pa pa_proves_tshvNilCert

/-- `termShiftVec (k + 1) (t ∷ v) = termShift t ∷ termShiftVec k v` bottom-up. -/
noncomputable def tshvAdjCertB : ArithmeticSemisentence 8 :=
  “u' u t' t v' v k n. !(isSemiterm LAct).pi n t → !(isUTermVec LAct).pi k v → !(termShiftGraph LAct) t' t → !(termShiftVecGraph LAct) u k v → !adjoinDef v' t v → !adjoinDef u' t' u → !(termShiftVecGraph LAct) u' (k + 1) v'”
noncomputable def tshvAdjCert : ArithmeticSentence := ∀¹* tshvAdjCertB
lemma models_tshvAdjCert : V↓[ℒₒᵣ] ⊧ tshvAdjCert ↔ ∀ u' u t' t v' v k n : V, IsSemiterm LAct n t → IsUTermVec LAct k v → t' = termShift LAct t → u = termShiftVec LAct k v → v' = t ∷ v → u' = t' ∷ u → u' = termShiftVec LAct (k + 1) v' := by
  simp [tshvAdjCert, tshvAdjCertB, models_iff, Matrix.vecForall_iff, termShift.defined.iff, termShiftVec.defined.iff]
theorem pa_proves_tshvAdjCert : 𝗣𝗔 ⊢ tshvAdjCert :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_tshvAdjCert.mpr fun _ _ _ _ _ _ _ _ h₁ h₂ h₃ h₄ h₅ h₆ ↦ by subst_vars; exact (termShiftVec_cons h₁.isUTerm h₂).symm
theorem lib_tshvAdjCert : Lib tshvAdjCert := Lib.of_pa pa_proves_tshvAdjCert

/-- `termShift #z = #z`. -/
noncomputable def termShiftBvarCertB : ArithmeticSemisentence 3 :=
  “t' t z. !qqBvarDef t z → !qqBvarDef t' z → !(termShiftGraph LAct) t' t”
noncomputable def termShiftBvarCert : ArithmeticSentence := ∀¹* termShiftBvarCertB
lemma models_termShiftBvarCert : V↓[ℒₒᵣ] ⊧ termShiftBvarCert ↔ ∀ t' t z : V, t = ^#z → t' = ^#z → t' = termShift LAct t := by
  simp [termShiftBvarCert, termShiftBvarCertB, models_iff, Matrix.vecForall_iff, termShift.defined.iff]
theorem pa_proves_termShiftBvarCert : 𝗣𝗔 ⊢ termShiftBvarCert :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_termShiftBvarCert.mpr fun _ _ _ h₁ h₂ ↦ by subst_vars; exact (termShift_bvar _).symm
theorem lib_termShiftBvarCert : Lib termShiftBvarCert := Lib.of_pa pa_proves_termShiftBvarCert

/-- `termShift &x = &(x + 1)`. -/
noncomputable def termShiftFvarCertB : ArithmeticSemisentence 3 :=
  “t' t x. !qqFvarDef t x → !qqFvarDef t' (x + 1) → !(termShiftGraph LAct) t' t”
noncomputable def termShiftFvarCert : ArithmeticSentence := ∀¹* termShiftFvarCertB
lemma models_termShiftFvarCert : V↓[ℒₒᵣ] ⊧ termShiftFvarCert ↔ ∀ t' t x : V, t = ^&x → t' = ^&(x + 1) → t' = termShift LAct t := by
  simp [termShiftFvarCert, termShiftFvarCertB, models_iff, Matrix.vecForall_iff, termShift.defined.iff]
theorem pa_proves_termShiftFvarCert : 𝗣𝗔 ⊢ termShiftFvarCert :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_termShiftFvarCert.mpr fun _ _ _ h₁ h₂ ↦ by subst_vars; exact (termShift_fvar _).symm
theorem lib_termShiftFvarCert : Lib termShiftFvarCert := Lib.of_pa pa_proves_termShiftFvarCert

/-- `termShift (func k f v) = func k f (termShiftVec k v)`. -/
noncomputable def termShiftFuncCertB : ArithmeticSemisentence 6 :=
  “t' u v f k t. !LAct.isFunc k f → !(isUTermVec LAct).pi k v → !qqFuncDef t k f v → !(termShiftVecGraph LAct) u k v → !qqFuncDef t' k f u → !(termShiftGraph LAct) t' t”
noncomputable def termShiftFuncCert : ArithmeticSentence := ∀¹* termShiftFuncCertB
lemma models_termShiftFuncCert : V↓[ℒₒᵣ] ⊧ termShiftFuncCert ↔ ∀ t' u v f k t : V, LAct.IsFunc k f → IsUTermVec LAct k v → t = ^func k f v → u = termShiftVec LAct k v → t' = ^func k f u → t' = termShift LAct t := by
  simp [termShiftFuncCert, termShiftFuncCertB, models_iff, Matrix.vecForall_iff, termShiftVec.defined.iff, termShift.defined.iff]
theorem pa_proves_termShiftFuncCert : 𝗣𝗔 ⊢ termShiftFuncCert :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_termShiftFuncCert.mpr fun _ _ _ _ _ _ h₁ h₂ h₃ h₄ h₅ ↦ by subst_vars; exact (termShift_func h₁ h₂).symm
theorem lib_termShiftFuncCert : Lib termShiftFuncCert := Lib.of_pa pa_proves_termShiftFuncCert

/-- `termSubstVec 0 w 0 = 0`. -/
noncomputable def tsvNilCertB : ArithmeticSemisentence 1 :=
  “w. !(termSubstVecGraph LAct) 0 0 w 0”
noncomputable def tsvNilCert : ArithmeticSentence := ∀¹* tsvNilCertB
lemma models_tsvNilCert : V↓[ℒₒᵣ] ⊧ tsvNilCert ↔ ∀ w : V, (0 : V) = termSubstVec LAct (0 : V) w (0 : V) := by
  simp [tsvNilCert, tsvNilCertB, models_iff, Matrix.vecForall_iff, termSubstVec.defined.iff]
theorem pa_proves_tsvNilCert : 𝗣𝗔 ⊢ tsvNilCert :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_tsvNilCert.mpr fun _ ↦ by exact (termSubstVec_nil _).symm
theorem lib_tsvNilCert : Lib tsvNilCert := Lib.of_pa pa_proves_tsvNilCert

/-- `termSubstVec (k + 1) w (t ∷ v) = termSubst w t ∷ termSubstVec k w v` bottom-up. -/
noncomputable def tsvAdjCertB : ArithmeticSemisentence 9 :=
  “u' u e t v' v w k n. !(isSemiterm LAct).pi n t → !(isUTermVec LAct).pi k v → !(termSubstGraph LAct) e w t → !(termSubstVecGraph LAct) u k w v → !adjoinDef v' t v → !adjoinDef u' e u → !(termSubstVecGraph LAct) u' (k + 1) w v'”
noncomputable def tsvAdjCert : ArithmeticSentence := ∀¹* tsvAdjCertB
lemma models_tsvAdjCert : V↓[ℒₒᵣ] ⊧ tsvAdjCert ↔ ∀ u' u e t v' v w k n : V, IsSemiterm LAct n t → IsUTermVec LAct k v → e = termSubst LAct w t → u = termSubstVec LAct k w v → v' = t ∷ v → u' = e ∷ u → u' = termSubstVec LAct (k + 1) w v' := by
  simp [tsvAdjCert, tsvAdjCertB, models_iff, Matrix.vecForall_iff, termSubst.defined.iff, termSubstVec.defined.iff]
theorem pa_proves_tsvAdjCert : 𝗣𝗔 ⊢ tsvAdjCert :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_tsvAdjCert.mpr fun _ _ _ _ _ _ _ _ _ h₁ h₂ h₃ h₄ h₅ h₆ ↦ by subst_vars; exact (termSubstVec_cons h₁.isUTerm h₂).symm
theorem lib_tsvAdjCert : Lib tsvAdjCert := Lib.of_pa pa_proves_tsvAdjCert

/-- `termSubst w #z = w.[z]`. -/
noncomputable def termSubstBvarCertB : ArithmeticSemisentence 4 :=
  “e w z t. !qqBvarDef t z → !nthDef e w z → !(termSubstGraph LAct) e w t”
noncomputable def termSubstBvarCert : ArithmeticSentence := ∀¹* termSubstBvarCertB
lemma models_termSubstBvarCert : V↓[ℒₒᵣ] ⊧ termSubstBvarCert ↔ ∀ e w z t : V, t = ^#z → e = w.[z] → e = termSubst LAct w t := by
  simp [termSubstBvarCert, termSubstBvarCertB, models_iff, Matrix.vecForall_iff, nth_defined.iff, termSubst.defined.iff]
theorem pa_proves_termSubstBvarCert : 𝗣𝗔 ⊢ termSubstBvarCert :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_termSubstBvarCert.mpr fun _ _ _ _ h₁ h₂ ↦ by subst_vars; exact (termSubst_bvar _).symm
theorem lib_termSubstBvarCert : Lib termSubstBvarCert := Lib.of_pa pa_proves_termSubstBvarCert

/-- `termSubst w &x = &x`. -/
noncomputable def termSubstFvarCertB : ArithmeticSemisentence 4 :=
  “e w x t. !qqFvarDef t x → !qqFvarDef e x → !(termSubstGraph LAct) e w t”
noncomputable def termSubstFvarCert : ArithmeticSentence := ∀¹* termSubstFvarCertB
lemma models_termSubstFvarCert : V↓[ℒₒᵣ] ⊧ termSubstFvarCert ↔ ∀ e w x t : V, t = ^&x → e = ^&x → e = termSubst LAct w t := by
  simp [termSubstFvarCert, termSubstFvarCertB, models_iff, Matrix.vecForall_iff, termSubst.defined.iff]
theorem pa_proves_termSubstFvarCert : 𝗣𝗔 ⊢ termSubstFvarCert :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_termSubstFvarCert.mpr fun _ _ _ _ h₁ h₂ ↦ by subst_vars; exact (termSubst_fvar _).symm
theorem lib_termSubstFvarCert : Lib termSubstFvarCert := Lib.of_pa pa_proves_termSubstFvarCert

/-- `termSubst w (func k f v) = func k f (termSubstVec k w v)`. -/
noncomputable def termSubstFuncCertB : ArithmeticSemisentence 7 :=
  “e u v f k t w. !LAct.isFunc k f → !(isUTermVec LAct).pi k v → !qqFuncDef t k f v → !(termSubstVecGraph LAct) u k w v → !qqFuncDef e k f u → !(termSubstGraph LAct) e w t”
noncomputable def termSubstFuncCert : ArithmeticSentence := ∀¹* termSubstFuncCertB
lemma models_termSubstFuncCert : V↓[ℒₒᵣ] ⊧ termSubstFuncCert ↔ ∀ e u v f k t w : V, LAct.IsFunc k f → IsUTermVec LAct k v → t = ^func k f v → u = termSubstVec LAct k w v → e = ^func k f u → e = termSubst LAct w t := by
  simp [termSubstFuncCert, termSubstFuncCertB, models_iff, Matrix.vecForall_iff, termSubstVec.defined.iff, termSubst.defined.iff]
theorem pa_proves_termSubstFuncCert : 𝗣𝗔 ⊢ termSubstFuncCert :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_termSubstFuncCert.mpr fun _ _ _ _ _ _ _ h₁ h₂ h₃ h₄ h₅ ↦ by subst_vars; exact (termSubst_func h₁ h₂).symm
theorem lib_termSubstFuncCert : Lib termSubstFuncCert := Lib.of_pa pa_proves_termSubstFuncCert

/-- `termBShiftVec 0 0 = 0` (dummy binder). -/
noncomputable def tbshvNilCertB : ArithmeticSemisentence 1 :=
  “x. !(termBShiftVecGraph LAct) 0 0 0”
noncomputable def tbshvNilCert : ArithmeticSentence := ∀¹* tbshvNilCertB
lemma models_tbshvNilCert : V↓[ℒₒᵣ] ⊧ tbshvNilCert ↔ ∀ x : V, (0 : V) = termBShiftVec LAct (0 : V) (0 : V) := by
  simp [tbshvNilCert, tbshvNilCertB, models_iff, Matrix.vecForall_iff, termBShiftVec.defined.iff]
theorem pa_proves_tbshvNilCert : 𝗣𝗔 ⊢ tbshvNilCert :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_tbshvNilCert.mpr fun _ ↦ by exact termBShiftVec_nil.symm
theorem lib_tbshvNilCert : Lib tbshvNilCert := Lib.of_pa pa_proves_tbshvNilCert

/-- `termBShiftVec (k + 1) (t ∷ v) = termBShift t ∷ termBShiftVec k v` bottom-up. -/
noncomputable def tbshvAdjCertB : ArithmeticSemisentence 8 :=
  “u' u t' t v' v k n. !(isSemiterm LAct).pi n t → !(isUTermVec LAct).pi k v → !(termBShiftGraph LAct) t' t → !(termBShiftVecGraph LAct) u k v → !adjoinDef v' t v → !adjoinDef u' t' u → !(termBShiftVecGraph LAct) u' (k + 1) v'”
noncomputable def tbshvAdjCert : ArithmeticSentence := ∀¹* tbshvAdjCertB
lemma models_tbshvAdjCert : V↓[ℒₒᵣ] ⊧ tbshvAdjCert ↔ ∀ u' u t' t v' v k n : V, IsSemiterm LAct n t → IsUTermVec LAct k v → t' = termBShift LAct t → u = termBShiftVec LAct k v → v' = t ∷ v → u' = t' ∷ u → u' = termBShiftVec LAct (k + 1) v' := by
  simp [tbshvAdjCert, tbshvAdjCertB, models_iff, Matrix.vecForall_iff, termBShift.defined.iff, termBShiftVec.defined.iff]
theorem pa_proves_tbshvAdjCert : 𝗣𝗔 ⊢ tbshvAdjCert :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_tbshvAdjCert.mpr fun _ _ _ _ _ _ _ _ h₁ h₂ h₃ h₄ h₅ h₆ ↦ by subst_vars; exact (termBShiftVec_cons h₁.isUTerm h₂).symm
theorem lib_tbshvAdjCert : Lib tbshvAdjCert := Lib.of_pa pa_proves_tbshvAdjCert

/-- `termBShift #z = #(z + 1)`. -/
noncomputable def termBShiftBvarCertB : ArithmeticSemisentence 3 :=
  “t' t z. !qqBvarDef t z → !qqBvarDef t' (z + 1) → !(termBShiftGraph LAct) t' t”
noncomputable def termBShiftBvarCert : ArithmeticSentence := ∀¹* termBShiftBvarCertB
lemma models_termBShiftBvarCert : V↓[ℒₒᵣ] ⊧ termBShiftBvarCert ↔ ∀ t' t z : V, t = ^#z → t' = ^#(z + 1) → t' = termBShift LAct t := by
  simp [termBShiftBvarCert, termBShiftBvarCertB, models_iff, Matrix.vecForall_iff, termBShift.defined.iff]
theorem pa_proves_termBShiftBvarCert : 𝗣𝗔 ⊢ termBShiftBvarCert :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_termBShiftBvarCert.mpr fun _ _ _ h₁ h₂ ↦ by subst_vars; exact (termBShift_bvar _).symm
theorem lib_termBShiftBvarCert : Lib termBShiftBvarCert := Lib.of_pa pa_proves_termBShiftBvarCert

/-- `termBShift &x = &x`. -/
noncomputable def termBShiftFvarCertB : ArithmeticSemisentence 3 :=
  “t' t x. !qqFvarDef t x → !qqFvarDef t' x → !(termBShiftGraph LAct) t' t”
noncomputable def termBShiftFvarCert : ArithmeticSentence := ∀¹* termBShiftFvarCertB
lemma models_termBShiftFvarCert : V↓[ℒₒᵣ] ⊧ termBShiftFvarCert ↔ ∀ t' t x : V, t = ^&x → t' = ^&x → t' = termBShift LAct t := by
  simp [termBShiftFvarCert, termBShiftFvarCertB, models_iff, Matrix.vecForall_iff, termBShift.defined.iff]
theorem pa_proves_termBShiftFvarCert : 𝗣𝗔 ⊢ termBShiftFvarCert :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_termBShiftFvarCert.mpr fun _ _ _ h₁ h₂ ↦ by subst_vars; exact (termBShift_fvar _).symm
theorem lib_termBShiftFvarCert : Lib termBShiftFvarCert := Lib.of_pa pa_proves_termBShiftFvarCert

/-- `termBShift (func k f v) = func k f (termBShiftVec k v)`. -/
noncomputable def termBShiftFuncCertB : ArithmeticSemisentence 6 :=
  “t' u v f k t. !LAct.isFunc k f → !(isUTermVec LAct).pi k v → !qqFuncDef t k f v → !(termBShiftVecGraph LAct) u k v → !qqFuncDef t' k f u → !(termBShiftGraph LAct) t' t”
noncomputable def termBShiftFuncCert : ArithmeticSentence := ∀¹* termBShiftFuncCertB
lemma models_termBShiftFuncCert : V↓[ℒₒᵣ] ⊧ termBShiftFuncCert ↔ ∀ t' u v f k t : V, LAct.IsFunc k f → IsUTermVec LAct k v → t = ^func k f v → u = termBShiftVec LAct k v → t' = ^func k f u → t' = termBShift LAct t := by
  simp [termBShiftFuncCert, termBShiftFuncCertB, models_iff, Matrix.vecForall_iff, termBShiftVec.defined.iff, termBShift.defined.iff]
theorem pa_proves_termBShiftFuncCert : 𝗣𝗔 ⊢ termBShiftFuncCert :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_termBShiftFuncCert.mpr fun _ _ _ _ _ _ h₁ h₂ h₃ h₄ h₅ ↦ by subst_vars; exact (termBShift_func h₁ h₂).symm
theorem lib_termBShiftFuncCert : Lib termBShiftFuncCert := Lib.of_pa pa_proves_termBShiftFuncCert

/-- `qVec w = #0 ∷ termBShiftVec (len w) w` bottom-up (`len w = k` from `IsUTermVec k w`). -/
noncomputable def qVecCertB : ArithmeticSemisentence 5 :=
  “u sw z w k. !(isUTermVec LAct).pi k w → !(termBShiftVecGraph LAct) sw k w → !qqBvarDef z 0 → !adjoinDef u z sw → !(qVecGraph LAct) u w”
noncomputable def qVecCert : ArithmeticSentence := ∀¹* qVecCertB
lemma models_qVecCert : V↓[ℒₒᵣ] ⊧ qVecCert ↔ ∀ u sw z w k : V, IsUTermVec LAct k w → sw = termBShiftVec LAct k w → z = ^#(0 : V) → u = z ∷ sw → u = qVec LAct w := by
  simp [qVecCert, qVecCertB, models_iff, Matrix.vecForall_iff, termBShiftVec.defined.iff, qVec.defined.iff]
theorem pa_proves_qVecCert : 𝗣𝗔 ⊢ qVecCert :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_qVecCert.mpr fun _ _ _ _ _ h₁ h₂ h₃ h₄ ↦ by subst_vars; unfold qVec; rw [h₁.lh]
theorem lib_qVecCert : Lib qVecCert := Lib.of_pa pa_proves_qVecCert

/-- `(qVec w).[0] = #0`. -/
noncomputable def qVecNth0B : ArithmeticSemisentence 2 :=
  “u w. !(qVecGraph LAct) u w → ∃ z, !qqBvarDef z 0 ∧ !nthDef z u 0”
noncomputable def qVecNth0 : ArithmeticSentence := ∀¹* qVecNth0B
lemma models_qVecNth0 : V↓[ℒₒᵣ] ⊧ qVecNth0 ↔ ∀ u w : V, u = qVec LAct w → ∃ z, z = ^#(0 : V) ∧ z = u.[(0 : V)] := by
  simp [qVecNth0, qVecNth0B, models_iff, Matrix.vecForall_iff, qVec.defined.iff, nth_defined.iff]
theorem pa_proves_qVecNth0 : 𝗣𝗔 ⊢ qVecNth0 :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_qVecNth0.mpr fun _ _ h ↦ ⟨_, rfl, by subst h; simp [qVec]⟩
theorem lib_qVecNth0 : Lib qVecNth0 := Lib.of_pa pa_proves_qVecNth0

/-- `i < k → (qVec w).[i + 1] = termBShift w.[i]` for a `k`-vector `w`. -/
noncomputable def qVecNthSuccB : ArithmeticSemisentence 6 :=
  “e' e u w i k. !(isUTermVec LAct).pi k w → i < k → !(qVecGraph LAct) u w → !nthDef e w i → !(termBShiftGraph LAct) e' e → !nthDef e' u (i + 1)”
noncomputable def qVecNthSucc : ArithmeticSentence := ∀¹* qVecNthSuccB
lemma models_qVecNthSucc : V↓[ℒₒᵣ] ⊧ qVecNthSucc ↔ ∀ e' e u w i k : V, IsUTermVec LAct k w → i < k → u = qVec LAct w → e = w.[i] → e' = termBShift LAct e → e' = u.[(i + 1)] := by
  simp [qVecNthSucc, qVecNthSuccB, models_iff, Matrix.vecForall_iff, qVec.defined.iff, nth_defined.iff, termBShift.defined.iff]
theorem pa_proves_qVecNthSucc : 𝗣𝗔 ⊢ qVecNthSucc :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_qVecNthSucc.mpr fun _ _ _ _ _ _ h₁ h₂ h₃ h₄ h₅ ↦ by subst_vars; unfold qVec; rw [nth_adjoin_succ, ← h₁.lh, nth_termBShiftVec h₁ h₂]
theorem lib_qVecNthSucc : Lib qVecNthSucc := Lib.of_pa pa_proves_qVecNthSucc

/-- `(t ∷ v).[0] = t`. -/
noncomputable def nthAdjoinZeroB : ArithmeticSemisentence 3 :=
  “w t v. !adjoinDef w t v → !nthDef t w 0”
noncomputable def nthAdjoinZero : ArithmeticSentence := ∀¹* nthAdjoinZeroB
lemma models_nthAdjoinZero : V↓[ℒₒᵣ] ⊧ nthAdjoinZero ↔ ∀ w t v : V, w = t ∷ v → t = w.[(0 : V)] := by
  simp [nthAdjoinZero, nthAdjoinZeroB, models_iff, Matrix.vecForall_iff, nth_defined.iff]
theorem pa_proves_nthAdjoinZero : 𝗣𝗔 ⊢ nthAdjoinZero :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_nthAdjoinZero.mpr fun _ _ _ h₁ ↦ by subst_vars; simp
theorem lib_nthAdjoinZero : Lib nthAdjoinZero := Lib.of_pa pa_proves_nthAdjoinZero

/-- `(t ∷ v).[i + 1] = v.[i]`. -/
noncomputable def nthAdjoinSuccB : ArithmeticSemisentence 5 :=
  “e w t v i. !adjoinDef w t v → !nthDef e v i → !nthDef e w (i + 1)”
noncomputable def nthAdjoinSucc : ArithmeticSentence := ∀¹* nthAdjoinSuccB
lemma models_nthAdjoinSucc : V↓[ℒₒᵣ] ⊧ nthAdjoinSucc ↔ ∀ e w t v i : V, w = t ∷ v → e = v.[i] → e = w.[(i + 1)] := by
  simp [nthAdjoinSucc, nthAdjoinSuccB, models_iff, Matrix.vecForall_iff, nth_defined.iff]
theorem pa_proves_nthAdjoinSucc : 𝗣𝗔 ⊢ nthAdjoinSucc :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_nthAdjoinSucc.mpr fun _ _ _ _ _ h₁ h₂ ↦ by subst_vars; simp
theorem lib_nthAdjoinSucc : Lib nthAdjoinSucc := Lib.of_pa pa_proves_nthAdjoinSucc

/-! ### I. Numerals N4/N5 (§2.4), in the DSL -/

/-- `x * (2 * y) = 2 * (x * y)` (N4, the even bit). -/
noncomputable def twoMulMulB : ArithmeticSemisentence 2 :=
  “y x. (x * (2 * y)) = (2 * (x * y))”
noncomputable def twoMulMul : ArithmeticSentence := ∀¹* twoMulMulB
lemma models_twoMulMul : V↓[ℒₒᵣ] ⊧ twoMulMul ↔ ∀ y x : V, (x * ((2 : V) * y)) = ((2 : V) * (x * y)) := by
  simp [twoMulMul, twoMulMulB, models_iff, Matrix.vecForall_iff]
theorem pa_proves_twoMulMul : 𝗣𝗔 ⊢ twoMulMul :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_twoMulMul.mpr fun _ _ ↦ mul_left_comm _ _ _
theorem lib_twoMulMul : Lib twoMulMul := Lib.of_pa pa_proves_twoMulMul

/-- `‖0‖ = 0` (N5; dummy binder). -/
noncomputable def lengthZeroB : ArithmeticSemisentence 1 :=
  “x. !lengthDef 0 0”
noncomputable def lengthZero : ArithmeticSentence := ∀¹* lengthZeroB
lemma models_lengthZero : V↓[ℒₒᵣ] ⊧ lengthZero ↔ ∀ x : V, (0 : V) = ‖(0 : V)‖ := by
  simp [lengthZero, lengthZeroB, models_iff, Matrix.vecForall_iff, length_defined.iff]
theorem pa_proves_lengthZero : 𝗣𝗔 ⊢ lengthZero :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_lengthZero.mpr fun _ ↦ length_zero.symm
theorem lib_lengthZero : Lib lengthZero := Lib.of_pa pa_proves_lengthZero

/-- `‖1‖ = 1` (N5; dummy binder). -/
noncomputable def lengthOneB : ArithmeticSemisentence 1 :=
  “x. !lengthDef 1 1”
noncomputable def lengthOne : ArithmeticSentence := ∀¹* lengthOneB
lemma models_lengthOne : V↓[ℒₒᵣ] ⊧ lengthOne ↔ ∀ x : V, (1 : V) = ‖(1 : V)‖ := by
  simp [lengthOne, lengthOneB, models_iff, Matrix.vecForall_iff, length_defined.iff]
theorem pa_proves_lengthOne : 𝗣𝗔 ⊢ lengthOne :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_lengthOne.mpr fun _ ↦ length_one.symm
theorem lib_lengthOne : Lib lengthOne := Lib.of_pa pa_proves_lengthOne

/-! ### J. `axm`(ii): `qqAlls`, `bv`, `termBV`, `listMax`, `fvarVec`, the `max`/`−` glue (§4.10(ii)) -/

/-- `qqAlls b 0 = b`. -/
noncomputable def qqAllsZeroB : ArithmeticSemisentence 1 :=
  “b. !qqAllsDef b b 0”
noncomputable def qqAllsZero : ArithmeticSentence := ∀¹* qqAllsZeroB
lemma models_qqAllsZero : V↓[ℒₒᵣ] ⊧ qqAllsZero ↔ ∀ b : V, b = qqAlls b (0 : V) := by
  simp [qqAllsZero, qqAllsZeroB, models_iff, Matrix.vecForall_iff, qqAlls_defined.iff]
theorem pa_proves_qqAllsZero : 𝗣𝗔 ⊢ qqAllsZero :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_qqAllsZero.mpr fun _ ↦ (qqAlls_zero _).symm
theorem lib_qqAllsZero : Lib qqAllsZero := Lib.of_pa pa_proves_qqAllsZero

/-- `qqAlls b (m + 1) = ∀ (qqAlls b m)`. -/
noncomputable def qqAllsSuccB : ArithmeticSemisentence 4 :=
  “p' p b m. !qqAllsDef p b m → !qqAllDef p' p → !qqAllsDef p' b (m + 1)”
noncomputable def qqAllsSucc : ArithmeticSentence := ∀¹* qqAllsSuccB
lemma models_qqAllsSucc : V↓[ℒₒᵣ] ⊧ qqAllsSucc ↔ ∀ p' p b m : V, p = qqAlls b m → p' = ^∀ p → p' = qqAlls b (m + 1) := by
  simp [qqAllsSucc, qqAllsSuccB, models_iff, Matrix.vecForall_iff, qqAlls_defined.iff]
theorem pa_proves_qqAllsSucc : 𝗣𝗔 ⊢ qqAllsSucc :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_qqAllsSucc.mpr fun _ _ _ _ h₁ h₂ ↦ by subst_vars; exact (qqAlls_succ _ _).symm
theorem lib_qqAllsSucc : Lib qqAllsSucc := Lib.of_pa pa_proves_qqAllsSucc

/-- `bv (p ⋏ q) = max (bv p) (bv q)`. -/
noncomputable def bvAndB : ArithmeticSemisentence 6 :=
  “m mq mp r q p. !(isUFormula LAct).pi p → !(isUFormula LAct).pi q → !qqAndDef r p q → !(bvGraph LAct) mp p → !(bvGraph LAct) mq q → !max.dfn m mp mq → !(bvGraph LAct) m r”
noncomputable def bvAnd : ArithmeticSentence := ∀¹* bvAndB
lemma models_bvAnd : V↓[ℒₒᵣ] ⊧ bvAnd ↔ ∀ m mq mp r q p : V, IsUFormula LAct p → IsUFormula LAct q → r = p ^⋏ q → mp = Bootstrapping.bv LAct p → mq = Bootstrapping.bv LAct q → m = max mp mq → m = Bootstrapping.bv LAct r := by
  simp [bvAnd, bvAndB, models_iff, Matrix.vecForall_iff, bv.defined.iff]
theorem pa_proves_bvAnd : 𝗣𝗔 ⊢ bvAnd :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_bvAnd.mpr fun _ _ _ _ _ _ h₁ h₂ h₃ h₄ h₅ h₆ ↦ by subst_vars; exact (bv_and h₁ h₂).symm
theorem lib_bvAnd : Lib bvAnd := Lib.of_pa pa_proves_bvAnd

/-! ### K. Chains: the `Sets`/`Lengths` rows of §3.4 re-issued with `inst_` lemmas (`Layout.chainSteps`) -/

/-- `∀ s x, ∃ t, t = insert x s` (`Sets.insertTotal`). -/
noncomputable def insertTotalCB : ArithmeticSemisentence 2 :=
  “s x. ∃ t, !insertDef t x s”
noncomputable def insertTotalC : ArithmeticSentence := ∀¹* insertTotalCB
lemma models_insertTotalC : V↓[ℒₒᵣ] ⊧ insertTotalC ↔ ∀ s x : V, ∃ t, t = insert x s := by
  simp [insertTotalC, insertTotalCB, models_iff, Matrix.vecForall_iff]
theorem pa_proves_insertTotalC : 𝗣𝗔 ⊢ insertTotalC :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_insertTotalC.mpr fun _ _ ↦ ⟨_, rfl⟩
theorem lib_insertTotalC : Lib insertTotalC := Lib.of_pa pa_proves_insertTotalC

/-- `t = insert x s → x ∈ t` (`Sets.memInsertSelf`). -/
noncomputable def memInsertSelfCB : ArithmeticSemisentence 3 :=
  “t s x. !insertDef t x s → x ∈ t”
noncomputable def memInsertSelfC : ArithmeticSentence := ∀¹* memInsertSelfCB
lemma models_memInsertSelfC : V↓[ℒₒᵣ] ⊧ memInsertSelfC ↔ ∀ t s x : V, t = insert x s → x ∈ t := by
  simp [memInsertSelfC, memInsertSelfCB, models_iff, Matrix.vecForall_iff]
theorem pa_proves_memInsertSelfC : 𝗣𝗔 ⊢ memInsertSelfC :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_memInsertSelfC.mpr fun _ _ _ h₁ ↦ by subst_vars; simp
theorem lib_memInsertSelfC : Lib memInsertSelfC := Lib.of_pa pa_proves_memInsertSelfC

/-- `t = insert x s → s ⊆ t` (`Sets.subsetInsert`). -/
noncomputable def subsetInsertCB : ArithmeticSemisentence 3 :=
  “t s x. !insertDef t x s → !bitSubsetDef s t”
noncomputable def subsetInsertC : ArithmeticSentence := ∀¹* subsetInsertCB
lemma models_subsetInsertC : V↓[ℒₒᵣ] ⊧ subsetInsertC ↔ ∀ t s x : V, t = insert x s → s ⊆ t := by
  simp [subsetInsertC, subsetInsertCB, models_iff, Matrix.vecForall_iff]
theorem pa_proves_subsetInsertC : 𝗣𝗔 ⊢ subsetInsertC :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_subsetInsertC.mpr fun _ _ _ h₁ ↦ by subst_vars; exact susbset_insert _ _
theorem lib_subsetInsertC : Lib subsetInsertC := Lib.of_pa pa_proves_subsetInsertC

/-- `s ⊆ t → t ⊆ u → s ⊆ u` (`Sets.subsetTrans`). -/
noncomputable def subsetTransCB : ArithmeticSemisentence 3 :=
  “u t s. !bitSubsetDef s t → !bitSubsetDef t u → !bitSubsetDef s u”
noncomputable def subsetTransC : ArithmeticSentence := ∀¹* subsetTransCB
lemma models_subsetTransC : V↓[ℒₒᵣ] ⊧ subsetTransC ↔ ∀ u t s : V, s ⊆ t → t ⊆ u → s ⊆ u := by
  simp [subsetTransC, subsetTransCB, models_iff, Matrix.vecForall_iff]
theorem pa_proves_subsetTransC : 𝗣𝗔 ⊢ subsetTransC :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_subsetTransC.mpr fun _ _ _ h₁ h₂ ↦ subset_trans h₁ h₂
theorem lib_subsetTransC : Lib subsetTransC := Lib.of_pa pa_proves_subsetTransC

/-- `s ⊆ t → x ∈ s → x ∈ t` (`Sets.subsetMem`). -/
noncomputable def subsetMemCB : ArithmeticSemisentence 3 :=
  “x t s. !bitSubsetDef s t → x ∈ s → x ∈ t”
noncomputable def subsetMemC : ArithmeticSentence := ∀¹* subsetMemCB
lemma models_subsetMemC : V↓[ℒₒᵣ] ⊧ subsetMemC ↔ ∀ x t s : V, s ⊆ t → x ∈ s → x ∈ t := by
  simp [subsetMemC, subsetMemCB, models_iff, Matrix.vecForall_iff]
theorem pa_proves_subsetMemC : 𝗣𝗔 ⊢ subsetMemC :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_subsetMemC.mpr fun _ _ _ h₁ h₂ ↦ h₁ h₂
theorem lib_subsetMemC : Lib subsetMemC := Lib.of_pa pa_proves_subsetMemC

/-- `0 ⊆ s` (`Sets.emptySubset`). -/
noncomputable def emptySubsetCB : ArithmeticSemisentence 1 :=
  “s. !bitSubsetDef 0 s”
noncomputable def emptySubsetC : ArithmeticSentence := ∀¹* emptySubsetCB
lemma models_emptySubsetC : V↓[ℒₒᵣ] ⊧ emptySubsetC ↔ ∀ s : V, (0 : V) ⊆ s := by
  simp [emptySubsetC, emptySubsetCB, models_iff, Matrix.vecForall_iff]
theorem pa_proves_emptySubsetC : 𝗣𝗔 ⊢ emptySubsetC :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_emptySubsetC.mpr fun s ↦ empty_subset s
theorem lib_emptySubsetC : Lib emptySubsetC := Lib.of_pa pa_proves_emptySubsetC

/-- `s ⊆ 0 → IsFormulaSet s` (vacuous: `s = 0`). -/
noncomputable def fsetOfSubsetZeroCB : ArithmeticSemisentence 1 :=
  “s. !bitSubsetDef s 0 → !(isFormulaSet LAct).sigma s”
noncomputable def fsetOfSubsetZeroC : ArithmeticSentence := ∀¹* fsetOfSubsetZeroCB
lemma models_fsetOfSubsetZeroC : V↓[ℒₒᵣ] ⊧ fsetOfSubsetZeroC ↔ ∀ s : V, s ⊆ (0 : V) → IsFormulaSet LAct s := by
  simp [fsetOfSubsetZeroC, fsetOfSubsetZeroCB, models_iff, Matrix.vecForall_iff]
theorem pa_proves_fsetOfSubsetZeroC : 𝗣𝗔 ⊢ fsetOfSubsetZeroC :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_fsetOfSubsetZeroC.mpr fun _ h p hp ↦ absurd (h hp) (by simp)
theorem lib_fsetOfSubsetZeroC : Lib fsetOfSubsetZeroC := Lib.of_pa pa_proves_fsetOfSubsetZeroC

/-- `IsFormulaSet s → IsFormula p → t = insert p s → IsFormulaSet t` (`Sets.isFormulaSetInsert`). -/
noncomputable def isFormulaSetInsertCB : ArithmeticSemisentence 3 :=
  “t p s. !(isFormulaSet LAct).pi s → !(isSemiformula LAct).pi 0 p → !insertDef t p s → !(isFormulaSet LAct).sigma t”
noncomputable def isFormulaSetInsertC : ArithmeticSentence := ∀¹* isFormulaSetInsertCB
lemma models_isFormulaSetInsertC : V↓[ℒₒᵣ] ⊧ isFormulaSetInsertC ↔ ∀ t p s : V, IsFormulaSet LAct s → IsSemiformula LAct (0 : V) p → t = insert p s → IsFormulaSet LAct t := by
  simp [isFormulaSetInsertC, isFormulaSetInsertCB, models_iff, Matrix.vecForall_iff]
theorem pa_proves_isFormulaSetInsertC : 𝗣𝗔 ⊢ isFormulaSetInsertC :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_isFormulaSetInsertC.mpr fun _ _ _ hs hp h ↦ by subst h; exact IsFormulaSet.insert_iff.mpr ⟨hp, hs⟩
theorem lib_isFormulaSetInsertC : Lib isFormulaSetInsertC := Lib.of_pa pa_proves_isFormulaSetInsertC

/-- `IsFormulaSet s → IsFormulaSet s` (the `.sigma → .pi` bridge, `Sets.isFormulaSetSigmaPi`). -/
noncomputable def fsetSigmaPiCB : ArithmeticSemisentence 1 :=
  “s. !(isFormulaSet LAct).sigma s → !(isFormulaSet LAct).pi s”
noncomputable def fsetSigmaPiC : ArithmeticSentence := ∀¹* fsetSigmaPiCB
lemma models_fsetSigmaPiC : V↓[ℒₒᵣ] ⊧ fsetSigmaPiC ↔ ∀ s : V, IsFormulaSet LAct s → IsFormulaSet LAct s := by
  simp [fsetSigmaPiC, fsetSigmaPiCB, models_iff, Matrix.vecForall_iff]
theorem pa_proves_fsetSigmaPiC : 𝗣𝗔 ⊢ fsetSigmaPiC :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_fsetSigmaPiC.mpr fun _ h ↦ h
theorem lib_fsetSigmaPiC : Lib fsetSigmaPiC := Lib.of_pa pa_proves_fsetSigmaPiC

/-- `∀ s, ∃ l, l = setLen s` (`Lengths.setLenTotal`). -/
noncomputable def setLenTotalCB : ArithmeticSemisentence 1 :=
  “s. ∃ l, !(setLenDef LAct) l s”
noncomputable def setLenTotalC : ArithmeticSentence := ∀¹* setLenTotalCB
lemma models_setLenTotalC : V↓[ℒₒᵣ] ⊧ setLenTotalC ↔ ∀ s : V, ∃ l, l = setLen LAct s := by
  simp [setLenTotalC, setLenTotalCB, models_iff, Matrix.vecForall_iff, setLen_defined.iff]
theorem pa_proves_setLenTotalC : 𝗣𝗔 ⊢ setLenTotalC :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_setLenTotalC.mpr fun _ ↦ ⟨_, rfl⟩
theorem lib_setLenTotalC : Lib setLenTotalC := Lib.of_pa pa_proves_setLenTotalC

/-- `s ⊆ s` (`Sets.subsetRefl`). -/
noncomputable def subsetReflCB : ArithmeticSemisentence 1 :=
  “s. !bitSubsetDef s s”
noncomputable def subsetReflC : ArithmeticSentence := ∀¹* subsetReflCB
lemma models_subsetReflC : V↓[ℒₒᵣ] ⊧ subsetReflC ↔ ∀ s : V, s ⊆ s := by
  simp [subsetReflC, subsetReflCB, models_iff, Matrix.vecForall_iff]
theorem pa_proves_subsetReflC : 𝗣𝗔 ⊢ subsetReflC :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_subsetReflC.mpr fun s ↦ subset_refl s
theorem lib_subsetReflC : Lib subsetReflC := Lib.of_pa pa_proves_subsetReflC

end ArithS
