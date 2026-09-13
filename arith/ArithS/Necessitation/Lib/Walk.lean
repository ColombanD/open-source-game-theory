import ArithS.Necessitation.Lib.Bridge

/-!
# ArithS.Necessitation.Lib.Walk — the library rows the formula WALK needs

`M4_BOUNDED_HBL/DESIGN_describe.md` §10 (items 1–5), the rows `describeSteps` and its top-down
companions use that no earlier `Lib/*` file provides. Same convention as `Sets.lean` (body
`xB : ArithmeticSemisentence m` in index order, `x := ∀¹* xB`, `models_x`, `pa_proves_x`,
`lib_x`; Δ₁ hypotheses `.pi`, conclusions `.sigma`):

1. **The `<` chain** (§3.3): `zeroLtSucc “y. 0 < y + 1”` and `succLtSucc “y x. x < y → x + 1 <
   y + 1”` — the bound-variable side condition `z < n` of `isSemitermBvar` is DERIVED by
   `z + 1` uses of these on chain numerals (`cT`, `WalkLemmas.lean`): the row's `0` IS `cT 0`
   and `y + 1` at `y := cT m` IS `cT (m + 1)` (the DSL's `+ 1` is the code `^+ 𝟏`).
2. **The symbol rows** (§3.2): one CLOSED sentence per `LAct` symbol, `isRelConst_eq/lt`
   (`=`, `<`: arity `2`, codes `0`, `1`) and `isFuncConst_zero/one/add/mul/cC/cD` (arities `0`,
   `0`, `2`, `2`, `0`, `0`; codes `0`, `1`, `0`, `1`, `2`, `3`; `LangAct.lean`,
   `isFunc_LAct_iff_V`/`isRel_LAct_iff_V`). Arity and code are written as CHAIN numerals
   `0 + 1 + ⋯ + 1`, not Foundation's `numeral` (`numeral 1 = 𝟏 ≠ 𝟎 ^+ 𝟏`), so that the
   instantiated antecedent `!LAct.isRel k R` of `isSemiformulaRel` at `k := cT 2` matches
   syntactically (`cTT_two`, `WalkLemmas.lean`). Used at `m = 0` (`useLemmaCode`, `allsIter 0`).
3. `isUTermVecOfSemitermVecLAct “v n k.”` — the `LAct` twin of `isUTermVecOfSemitermVecOR`
   (the commutation rows take `!(isUTermVec LAct).pi k v`, formation delivers `.sigma k n v`).
4. `isSemitermVecQVec “u w m n.”` — formation of the quantifier-bumped vector `qVec w`
   (`substSteps` under `∀/∃`, §9.3).
5. `substs1Substs “y w t p.”` — `substs1 t p = subst (t ∷ 0) p` (Foundation's definition, `rfl`),
   so an `exsIntro` instance `substs1Graph` is decomposed by the `substsGraph` rows (§9.3).
6. **Chain-numeral arity variants** (2026-09-13): `isSemiformulaSubsts1C`/`isFormulaFreeC` are
   `Formulas.lean`'s `isSemiformulaSubsts1`/`isFormulaFree` with the arity of the `1`-semiformula
   written `0 + 1` (the chain literal, code `cT 1 = 𝟎 ^+ 𝟏`) instead of the numeral `1` (code
   `𝟏 = numeral 1`; `RowInst.lean`'s header flagged the mismatch — a walk instance at `cT 1` matches
   the numeral rows only semantically, never syntactically). The two old rows stay (any consumer
   of the numeral form, e.g. an `axm`/`indRec` chain, keeps them); the walk standardizes on `cT`
   for EVERY arity (`DESIGN_describe.md` §1.4, decision 1). The bridge rows `piArityOneToC`
   (`“p. pi 1 p → sigma (0 + 1) p”`) and `piArityCToOne` (back) let a fragment convert a fact
   code between the two spellings (`piFact 𝟏 p ↔ piFact (cT 1) p`, both directions; semantically
   `IsSemiformula 1 p → IsSemiformula 1 p`). Code-level shapes and instantiations:
   `RowInst.lean` §3.C (`cTTm`, `quote_row_isSemiformulaSubsts1C`, …).
-/

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1
open LAct

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ### 1. The `<` chain -/

/-- `0 < y + 1`. -/
noncomputable def zeroLtSuccB : ArithmeticSemisentence 1 := “y. 0 < y + 1”
noncomputable def zeroLtSucc : ArithmeticSentence := ∀¹* zeroLtSuccB

lemma models_zeroLtSucc : V↓[ℒₒᵣ] ⊧ zeroLtSucc ↔ ∀ y : V, 0 < y + 1 := by
  simp [zeroLtSucc, zeroLtSuccB, models_iff]

theorem pa_proves_zeroLtSucc : 𝗣𝗔 ⊢ zeroLtSucc :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_zeroLtSucc.mpr fun y ↦
    lt_of_le_of_lt zero_le (lt_add_one y)

theorem lib_zeroLtSucc : Lib zeroLtSucc := Lib.of_pa pa_proves_zeroLtSucc

/-- `x < y → x + 1 < y + 1`. -/
noncomputable def succLtSuccB : ArithmeticSemisentence 2 := “y x. x < y → x + 1 < y + 1”
noncomputable def succLtSucc : ArithmeticSentence := ∀¹* succLtSuccB

lemma models_succLtSucc : V↓[ℒₒᵣ] ⊧ succLtSucc ↔ ∀ y x : V, x < y → x + 1 < y + 1 := by
  simp [succLtSucc, succLtSuccB, models_iff]

theorem pa_proves_succLtSucc : 𝗣𝗔 ⊢ succLtSucc :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_succLtSucc.mpr fun _ _ h ↦
    (add_lt_add_iff_right 1).mpr h

theorem lib_succLtSucc : Lib succLtSucc := Lib.of_pa pa_proves_succLtSucc

/-! ### 2. The symbol rows — closed sentences, chain numerals -/

/-- `LAct.IsRel 2 0` (`=`). -/
noncomputable def isRelConst_eqB : ArithmeticSemisentence 0 := “!LAct.isRel (0 + 1 + 1) 0”
noncomputable def isRelConst_eq : ArithmeticSentence := ∀¹* isRelConst_eqB

lemma models_isRelConst_eq : V↓[ℒₒᵣ] ⊧ isRelConst_eq ↔ LAct.IsRel (2 : V) 0 := by
  simp [isRelConst_eq, isRelConst_eqB, models_iff]; norm_num

theorem pa_proves_isRelConst_eq : 𝗣𝗔 ⊢ isRelConst_eq :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_isRelConst_eq.mpr
    (isRel_LAct_iff_V.mpr (Or.inl ⟨rfl, rfl⟩))

theorem lib_isRelConst_eq : Lib isRelConst_eq := Lib.of_pa pa_proves_isRelConst_eq

/-- `LAct.IsRel 2 1` (`<`). -/
noncomputable def isRelConst_ltB : ArithmeticSemisentence 0 := “!LAct.isRel (0 + 1 + 1) (0 + 1)”
noncomputable def isRelConst_lt : ArithmeticSentence := ∀¹* isRelConst_ltB

lemma models_isRelConst_lt : V↓[ℒₒᵣ] ⊧ isRelConst_lt ↔ LAct.IsRel (2 : V) 1 := by
  simp [isRelConst_lt, isRelConst_ltB, models_iff]; norm_num

theorem pa_proves_isRelConst_lt : 𝗣𝗔 ⊢ isRelConst_lt :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_isRelConst_lt.mpr
    (isRel_LAct_iff_V.mpr (Or.inr ⟨rfl, rfl⟩))

theorem lib_isRelConst_lt : Lib isRelConst_lt := Lib.of_pa pa_proves_isRelConst_lt

/-- `LAct.IsFunc 0 0` (`0`). -/
noncomputable def isFuncConst_zeroB : ArithmeticSemisentence 0 := “!LAct.isFunc 0 0”
noncomputable def isFuncConst_zero : ArithmeticSentence := ∀¹* isFuncConst_zeroB

lemma models_isFuncConst_zero : V↓[ℒₒᵣ] ⊧ isFuncConst_zero ↔ LAct.IsFunc (0 : V) 0 := by
  simp [isFuncConst_zero, isFuncConst_zeroB, models_iff]

theorem pa_proves_isFuncConst_zero : 𝗣𝗔 ⊢ isFuncConst_zero :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_isFuncConst_zero.mpr
    (isFunc_LAct_iff_V.mpr (Or.inl ⟨rfl, rfl⟩))

theorem lib_isFuncConst_zero : Lib isFuncConst_zero := Lib.of_pa pa_proves_isFuncConst_zero

/-- `LAct.IsFunc 0 1` (`1`). -/
noncomputable def isFuncConst_oneB : ArithmeticSemisentence 0 := “!LAct.isFunc 0 (0 + 1)”
noncomputable def isFuncConst_one : ArithmeticSentence := ∀¹* isFuncConst_oneB

lemma models_isFuncConst_one : V↓[ℒₒᵣ] ⊧ isFuncConst_one ↔ LAct.IsFunc (0 : V) 1 := by
  simp [isFuncConst_one, isFuncConst_oneB, models_iff]

theorem pa_proves_isFuncConst_one : 𝗣𝗔 ⊢ isFuncConst_one :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_isFuncConst_one.mpr
    (isFunc_LAct_iff_V.mpr (Or.inr (Or.inl ⟨rfl, rfl⟩)))

theorem lib_isFuncConst_one : Lib isFuncConst_one := Lib.of_pa pa_proves_isFuncConst_one

/-- `LAct.IsFunc 2 0` (`+`). -/
noncomputable def isFuncConst_addB : ArithmeticSemisentence 0 := “!LAct.isFunc (0 + 1 + 1) 0”
noncomputable def isFuncConst_add : ArithmeticSentence := ∀¹* isFuncConst_addB

lemma models_isFuncConst_add : V↓[ℒₒᵣ] ⊧ isFuncConst_add ↔ LAct.IsFunc (2 : V) 0 := by
  simp [isFuncConst_add, isFuncConst_addB, models_iff]; norm_num

theorem pa_proves_isFuncConst_add : 𝗣𝗔 ⊢ isFuncConst_add :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_isFuncConst_add.mpr
    (isFunc_LAct_iff_V.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))))

theorem lib_isFuncConst_add : Lib isFuncConst_add := Lib.of_pa pa_proves_isFuncConst_add

/-- `LAct.IsFunc 2 1` (`*`). -/
noncomputable def isFuncConst_mulB : ArithmeticSemisentence 0 := “!LAct.isFunc (0 + 1 + 1) (0 + 1)”
noncomputable def isFuncConst_mul : ArithmeticSentence := ∀¹* isFuncConst_mulB

lemma models_isFuncConst_mul : V↓[ℒₒᵣ] ⊧ isFuncConst_mul ↔ LAct.IsFunc (2 : V) 1 := by
  simp [isFuncConst_mul, isFuncConst_mulB, models_iff]; norm_num

theorem pa_proves_isFuncConst_mul : 𝗣𝗔 ⊢ isFuncConst_mul :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_isFuncConst_mul.mpr
    (isFunc_LAct_iff_V.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))))))

theorem lib_isFuncConst_mul : Lib isFuncConst_mul := Lib.of_pa pa_proves_isFuncConst_mul

/-- `LAct.IsFunc 0 2` (the action constant `c_C`). -/
noncomputable def isFuncConst_cCB : ArithmeticSemisentence 0 := “!LAct.isFunc 0 (0 + 1 + 1)”
noncomputable def isFuncConst_cC : ArithmeticSentence := ∀¹* isFuncConst_cCB

lemma models_isFuncConst_cC : V↓[ℒₒᵣ] ⊧ isFuncConst_cC ↔ LAct.IsFunc (0 : V) 2 := by
  simp [isFuncConst_cC, isFuncConst_cCB, models_iff]; norm_num

theorem pa_proves_isFuncConst_cC : 𝗣𝗔 ⊢ isFuncConst_cC :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_isFuncConst_cC.mpr
    (isFunc_LAct_iff_V.mpr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))

theorem lib_isFuncConst_cC : Lib isFuncConst_cC := Lib.of_pa pa_proves_isFuncConst_cC

/-- `LAct.IsFunc 0 3` (the action constant `c_D`). -/
noncomputable def isFuncConst_cDB : ArithmeticSemisentence 0 := “!LAct.isFunc 0 (0 + 1 + 1 + 1)”
noncomputable def isFuncConst_cD : ArithmeticSentence := ∀¹* isFuncConst_cDB

lemma models_isFuncConst_cD : V↓[ℒₒᵣ] ⊧ isFuncConst_cD ↔ LAct.IsFunc (0 : V) 3 := by
  simp [isFuncConst_cD, isFuncConst_cDB, models_iff]; norm_num

theorem pa_proves_isFuncConst_cD : 𝗣𝗔 ⊢ isFuncConst_cD :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_isFuncConst_cD.mpr
    (isFunc_LAct_iff_V.mpr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))))

theorem lib_isFuncConst_cD : Lib isFuncConst_cD := Lib.of_pa pa_proves_isFuncConst_cD

/-! ### 3. Vector rows -/

/-- `IsSemitermVec k n v → IsUTermVec k v` at `LAct`. -/
noncomputable def isUTermVecOfSemitermVecLActB : ArithmeticSemisentence 3 :=
  “v n k. !(isSemitermVec LAct).pi k n v → !(isUTermVec LAct).sigma k v”
noncomputable def isUTermVecOfSemitermVecLAct : ArithmeticSentence := ∀¹* isUTermVecOfSemitermVecLActB

lemma models_isUTermVecOfSemitermVecLAct :
    V↓[ℒₒᵣ] ⊧ isUTermVecOfSemitermVecLAct ↔ ∀ v n k : V, IsSemitermVec LAct k n v → IsUTermVec LAct k v := by
  simp [isUTermVecOfSemitermVecLAct, isUTermVecOfSemitermVecLActB, models_iff, Matrix.vecForall_iff]

theorem pa_proves_isUTermVecOfSemitermVecLAct : 𝗣𝗔 ⊢ isUTermVecOfSemitermVecLAct :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_isUTermVecOfSemitermVecLAct.mpr fun _ _ _ h ↦ h.isUTermVec

theorem lib_isUTermVecOfSemitermVecLAct : Lib isUTermVecOfSemitermVecLAct :=
  Lib.of_pa pa_proves_isUTermVecOfSemitermVecLAct

/-- `IsSemitermVec n m w → IsSemitermVec (n + 1) (m + 1) (qVec w)`. -/
noncomputable def isSemitermVecQVecB : ArithmeticSemisentence 4 :=
  “u w m n. !(isSemitermVec LAct).pi n m w → !(qVecGraph LAct) u w → !(isSemitermVec LAct).sigma (n + 1) (m + 1) u”
noncomputable def isSemitermVecQVec : ArithmeticSentence := ∀¹* isSemitermVecQVecB

lemma models_isSemitermVecQVec :
    V↓[ℒₒᵣ] ⊧ isSemitermVecQVec ↔
      ∀ u w m n : V, IsSemitermVec LAct n m w → u = qVec LAct w → IsSemitermVec LAct (n + 1) (m + 1) u := by
  simp [isSemitermVecQVec, isSemitermVecQVecB, models_iff, Matrix.vecForall_iff, qVec.defined.iff]

theorem pa_proves_isSemitermVecQVec : 𝗣𝗔 ⊢ isSemitermVecQVec :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_isSemitermVecQVec.mpr fun _ _ _ _ hw h ↦ by
    subst h; exact hw.qVec

theorem lib_isSemitermVecQVec : Lib isSemitermVecQVec := Lib.of_pa pa_proves_isSemitermVecQVec

/-- `w = t ∷ 0 → y = substs1 t p → y = subst w p`. -/
noncomputable def substs1SubstsB : ArithmeticSemisentence 4 :=
  “y w t p. !adjoinDef w t 0 → !(substs1Graph LAct) y t p → !(substsGraph LAct) y w p”
noncomputable def substs1Substs : ArithmeticSentence := ∀¹* substs1SubstsB

lemma models_substs1Substs :
    V↓[ℒₒᵣ] ⊧ substs1Substs ↔
      ∀ y w t p : V, w = t ∷ 0 → y = substs1 LAct t p → y = subst LAct w p := by
  simp [substs1Substs, substs1SubstsB, models_iff, Matrix.vecForall_iff, substs1.defined.iff,
    subst.defined.iff]

theorem pa_proves_substs1Substs : 𝗣𝗔 ⊢ substs1Substs :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_substs1Substs.mpr fun _ _ _ _ hw hy ↦ by
    subst hw hy; rfl

theorem lib_substs1Substs : Lib substs1Substs := Lib.of_pa pa_proves_substs1Substs

/-! ### 6. Chain-numeral arity variants and the arity-1 bridge rows -/

/-- `IsSemiterm n t → IsSemiformula (0 + 1) p → IsSemiformula n (substs1 t p)` — `isSemiformulaSubsts1`
with the arity `1` as the chain literal `0 + 1` (code `cT 1`). -/
noncomputable def isSemiformulaSubsts1CB : ArithmeticSemisentence 4 :=
  “y p t n. !(isSemiterm LAct).pi n t → !(isSemiformula LAct).pi (0 + 1) p → !(substs1Graph LAct) y t p → !(isSemiformula LAct).sigma n y”
noncomputable def isSemiformulaSubsts1C : ArithmeticSentence := ∀¹* isSemiformulaSubsts1CB

lemma models_isSemiformulaSubsts1C :
    V↓[ℒₒᵣ] ⊧ isSemiformulaSubsts1C ↔ ∀ y p t n : V, IsSemiterm LAct n t → IsSemiformula LAct 1 p → y = substs1 LAct t p → IsSemiformula LAct n y := by
  simp [isSemiformulaSubsts1C, isSemiformulaSubsts1CB, models_iff, Matrix.vecForall_iff, substs1.defined.iff]

theorem pa_proves_isSemiformulaSubsts1C : 𝗣𝗔 ⊢ isSemiformulaSubsts1C :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_isSemiformulaSubsts1C.mpr fun _ _ _ _ ht hp h ↦ by subst h; exact IsSemiformula.substs1 ht hp

theorem lib_isSemiformulaSubsts1C : Lib isSemiformulaSubsts1C := Lib.of_pa pa_proves_isSemiformulaSubsts1C

/-- `IsSemiformula (0 + 1) p → IsFormula (free p)` — `isFormulaFree` with the arity `1` as the chain
literal `0 + 1` (code `cT 1`). -/
noncomputable def isFormulaFreeCB : ArithmeticSemisentence 2 :=
  “y p. !(isSemiformula LAct).pi (0 + 1) p → !(freeGraph LAct) y p → !(isSemiformula LAct).sigma 0 y”
noncomputable def isFormulaFreeC : ArithmeticSentence := ∀¹* isFormulaFreeCB

lemma models_isFormulaFreeC :
    V↓[ℒₒᵣ] ⊧ isFormulaFreeC ↔ ∀ y p : V, IsSemiformula LAct 1 p → y = free LAct p → IsFormula LAct y := by
  simp [isFormulaFreeC, isFormulaFreeCB, models_iff, Matrix.vecForall_iff, free.defined.iff]

theorem pa_proves_isFormulaFreeC : 𝗣𝗔 ⊢ isFormulaFreeC :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_isFormulaFreeC.mpr fun _ _ hp h ↦ by subst h; exact hp.free

theorem lib_isFormulaFreeC : Lib isFormulaFreeC := Lib.of_pa pa_proves_isFormulaFreeC

/-- The arity-1 bridge, numeral to chain: `IsSemiformula 1 p → IsSemiformula (0 + 1) p`
(`piFact 𝟏 p` to `sigmaFact (cT 1) p` at the code level). -/
noncomputable def piArityOneToCB : ArithmeticSemisentence 1 :=
  “p. !(isSemiformula LAct).pi 1 p → !(isSemiformula LAct).sigma (0 + 1) p”
noncomputable def piArityOneToC : ArithmeticSentence := ∀¹* piArityOneToCB

lemma models_piArityOneToC :
    V↓[ℒₒᵣ] ⊧ piArityOneToC ↔ ∀ p : V, IsSemiformula LAct 1 p → IsSemiformula LAct 1 p := by
  simp [piArityOneToC, piArityOneToCB, models_iff]

theorem pa_proves_piArityOneToC : 𝗣𝗔 ⊢ piArityOneToC :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_piArityOneToC.mpr fun _ h ↦ h

theorem lib_piArityOneToC : Lib piArityOneToC := Lib.of_pa pa_proves_piArityOneToC

/-- The arity-1 bridge, chain to numeral: `IsSemiformula (0 + 1) p → IsSemiformula 1 p`
(`piFact (cT 1) p` to `sigmaFact 𝟏 p`). -/
noncomputable def piArityCToOneB : ArithmeticSemisentence 1 :=
  “p. !(isSemiformula LAct).pi (0 + 1) p → !(isSemiformula LAct).sigma 1 p”
noncomputable def piArityCToOne : ArithmeticSentence := ∀¹* piArityCToOneB

lemma models_piArityCToOne :
    V↓[ℒₒᵣ] ⊧ piArityCToOne ↔ ∀ p : V, IsSemiformula LAct 1 p → IsSemiformula LAct 1 p := by
  simp [piArityCToOne, piArityCToOneB, models_iff]

theorem pa_proves_piArityCToOne : 𝗣𝗔 ⊢ piArityCToOne :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_piArityCToOne.mpr fun _ h ↦ h

theorem lib_piArityCToOne : Lib piArityCToOne := Lib.of_pa pa_proves_piArityCToOne

end ArithS
