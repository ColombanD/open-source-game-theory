import ArithS.Necessitation.Lib.Basic

/-!
# ArithS.Necessitation.Lib.Lengths — the `lengths` rows of the library `Λ`

`DESIGN_inner_necessitation.md` §3.1 row `lengths` and §4.1–4.2. Same convention as
`Sets.lean` (body `xB : ArithmeticSemisentence m` in index order, `x := ∀¹* xB`, `models_x`,
`pa_proves_x`, `lib_x`). Two layers:

1. **Code level** (the `ℒₒᵣ` DSL over the package's graphs): totality of `formulaLen`,
   `termLen`, `termLenVec`, `listSum`, `setLen`, `bnum`; `setLen (insert x s) ≤ setLen s +
   formulaLen x` and `setLen ∅ = 0` (§4.2: the sequent length is BOUNDED, never computed);
   `formulaLen` of every constructor (`|p ⋏ q| = |p| + |q| + 1`, …, `|rel k R v| = Σ|vᵢ| + 1`),
   `formulaLen (neg p) = formulaLen p`, `termLen` of `#z`, `&x`, `func k f v`; and the
   bit-recursion laws of the binary-numeral CODE `bnum` (`bnum (2m) = 𝟐 ^* bnum m`,
   `bnum (2m+1) = (𝟐 ^* bnum m) ^+ 𝟏`, `Bnum.lean:345-348`).
2. **Term level** (§4.1, the `NumeralFacts.lean` pattern, in ITS syntax — `leF`, `twoMul`,
   `twoMulOne` — so the meta-level assembly instantiates them at `bnumT` exactly as
   `leEven`/`leOdd`): the laws that add two binary numerals bit by bit,
   `2x + 2y = 2(x+y)`, `2x + (2y+1) = 2(x+y)+1`, `(2x+1) + 2y = 2(x+y)+1`,
   `(2x+1) + (2y+1) = 2(x+y+1)`, the carry `(2x+1) + 1 = 2(x+1)`, and the order glue
   `n ≤ x → m ≤ y → n + m ≤ x + y`, `n ≤ x → n ≤ x + y`, transitivity, `x = y → x ≤ y`,
   `x ≤ y → x + 1 ≤ y + 1`, associativity/commutativity of `+`.

   Why no "internal value" law: a numeral in a sequent is a TERM, so "`n ≤ val (bnum a)`" is
   the formula `n ≤ bnumT a` and the bit laws above are exactly what the assembly needs (the
   package has no `termVal` graph, and none is required).
-/

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open PeanoMinus ISigma0 ISigma1
open LAct

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ### Code level: totality -/

/-- `∀ p, ∃ l, l = formulaLen p`. -/
noncomputable def formulaLenTotalB : ArithmeticSemisentence 1 := “p. ∃ l, !(formulaLenGraph LAct) l p”
noncomputable def formulaLenTotal : ArithmeticSentence := ∀¹* formulaLenTotalB

lemma models_formulaLenTotal : V↓[ℒₒᵣ] ⊧ formulaLenTotal ↔ ∀ p : V, ∃ l, l = formulaLen LAct p := by
  simp [formulaLenTotal, formulaLenTotalB, models_iff, formulaLen.defined.iff]

theorem pa_proves_formulaLenTotal : 𝗣𝗔 ⊢ formulaLenTotal :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_formulaLenTotal.mpr fun _ ↦ ⟨_, rfl⟩

theorem lib_formulaLenTotal : Lib formulaLenTotal := Lib.of_pa pa_proves_formulaLenTotal

/-- `∀ t, ∃ l, l = termLen t`. -/
noncomputable def termLenTotalB : ArithmeticSemisentence 1 := “t. ∃ l, !(termLenGraph LAct) l t”
noncomputable def termLenTotal : ArithmeticSentence := ∀¹* termLenTotalB

lemma models_termLenTotal : V↓[ℒₒᵣ] ⊧ termLenTotal ↔ ∀ t : V, ∃ l, l = termLen LAct t := by
  simp [termLenTotal, termLenTotalB, models_iff, termLen.defined.iff]

theorem pa_proves_termLenTotal : 𝗣𝗔 ⊢ termLenTotal :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_termLenTotal.mpr fun _ ↦ ⟨_, rfl⟩

theorem lib_termLenTotal : Lib termLenTotal := Lib.of_pa pa_proves_termLenTotal

/-- `∀ k v, ∃ M, M = termLenVec k v`. -/
noncomputable def termLenVecTotalB : ArithmeticSemisentence 2 := “v k. ∃ M, !(termLenVecGraph LAct) M k v”
noncomputable def termLenVecTotal : ArithmeticSentence := ∀¹* termLenVecTotalB

lemma models_termLenVecTotal :
    V↓[ℒₒᵣ] ⊧ termLenVecTotal ↔ ∀ v k : V, ∃ M, M = termLenVec LAct k v := by
  simp [termLenVecTotal, termLenVecTotalB, models_iff, termLenVec.defined.iff]

theorem pa_proves_termLenVecTotal : 𝗣𝗔 ⊢ termLenVecTotal :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_termLenVecTotal.mpr fun _ _ ↦ ⟨_, rfl⟩

theorem lib_termLenVecTotal : Lib termLenVecTotal := Lib.of_pa pa_proves_termLenVecTotal

/-- `∀ M, ∃ s, s = listSum M`. -/
noncomputable def listSumTotalB : ArithmeticSemisentence 1 := “M. ∃ s, !listSumDef s M”
noncomputable def listSumTotal : ArithmeticSentence := ∀¹* listSumTotalB

lemma models_listSumTotal : V↓[ℒₒᵣ] ⊧ listSumTotal ↔ ∀ M : V, ∃ s, s = listSum M := by
  simp [listSumTotal, listSumTotalB, models_iff, listSum_defined.iff]

theorem pa_proves_listSumTotal : 𝗣𝗔 ⊢ listSumTotal :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_listSumTotal.mpr fun _ ↦ ⟨_, rfl⟩

theorem lib_listSumTotal : Lib listSumTotal := Lib.of_pa pa_proves_listSumTotal

/-- `∀ s, ∃ l, l = setLen s`. -/
noncomputable def setLenTotalB : ArithmeticSemisentence 1 := “s. ∃ l, !(setLenDef LAct) l s”
noncomputable def setLenTotal : ArithmeticSentence := ∀¹* setLenTotalB

lemma models_setLenTotal : V↓[ℒₒᵣ] ⊧ setLenTotal ↔ ∀ s : V, ∃ l, l = setLen LAct s := by
  simp [setLenTotal, setLenTotalB, models_iff, setLen_defined.iff]

theorem pa_proves_setLenTotal : 𝗣𝗔 ⊢ setLenTotal :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_setLenTotal.mpr fun _ ↦ ⟨_, rfl⟩

theorem lib_setLenTotal : Lib setLenTotal := Lib.of_pa pa_proves_setLenTotal

/-- `∀ k, ∃ t, t = bnum k`. -/
noncomputable def bnumTotalB : ArithmeticSemisentence 1 := “k. ∃ t, !bnumGraph t k”
noncomputable def bnumTotal : ArithmeticSentence := ∀¹* bnumTotalB

lemma models_bnumTotal : V↓[ℒₒᵣ] ⊧ bnumTotal ↔ ∀ k : V, ∃ t, t = bnum k := by
  simp [bnumTotal, bnumTotalB, models_iff, bnum.defined.iff]

theorem pa_proves_bnumTotal : 𝗣𝗔 ⊢ bnumTotal :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_bnumTotal.mpr fun _ ↦ ⟨_, rfl⟩

theorem lib_bnumTotal : Lib bnumTotal := Lib.of_pa pa_proves_bnumTotal

/-! ### Code level: `setLen` -/

/-- `setLen (insert x s) ≤ setLen s + formulaLen x`. -/
noncomputable def setLenInsertLeB : ArithmeticSemisentence 6 :=
  “lx ls l t s x. !insertDef t x s → !(setLenDef LAct) l t → !(setLenDef LAct) ls s →
    !(formulaLenGraph LAct) lx x → l ≤ ls + lx”
noncomputable def setLenInsertLe : ArithmeticSentence := ∀¹* setLenInsertLeB

lemma models_setLenInsertLe :
    V↓[ℒₒᵣ] ⊧ setLenInsertLe ↔
    ∀ lx ls l t s x : V, t = insert x s → l = setLen LAct t → ls = setLen LAct s →
      lx = formulaLen LAct x → l ≤ ls + lx := by
  simp [setLenInsertLe, setLenInsertLeB, models_iff, Matrix.vecForall_iff, setLen_defined.iff,
    formulaLen.defined.iff]

theorem pa_proves_setLenInsertLe : 𝗣𝗔 ⊢ setLenInsertLe :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_setLenInsertLe.mpr fun _ _ _ _ s x ht hl hls hlx ↦ by
    subst ht; subst hl; subst hls; subst hlx; exact setLen_insert_le x s

theorem lib_setLenInsertLe : Lib setLenInsertLe := Lib.of_pa pa_proves_setLenInsertLe

/-- `setLen ∅ = 0`. -/
noncomputable def setLenEmptyB : ArithmeticSemisentence 1 := “l. !(setLenDef LAct) l 0 → l = 0”
noncomputable def setLenEmpty : ArithmeticSentence := ∀¹* setLenEmptyB

lemma models_setLenEmpty : V↓[ℒₒᵣ] ⊧ setLenEmpty ↔ ∀ l : V, l = setLen LAct 0 → l = 0 := by
  simp [setLenEmpty, setLenEmptyB, models_iff, Matrix.vecForall_iff, setLen_defined.iff]

theorem pa_proves_setLenEmpty : 𝗣𝗔 ⊢ setLenEmpty :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_setLenEmpty.mpr fun _ h ↦ by subst h; exact setLen_empty

theorem lib_setLenEmpty : Lib setLenEmpty := Lib.of_pa pa_proves_setLenEmpty

/-! ### Code level: `formulaLen`/`termLen` of the constructors -/

/-- `formulaLen (rel k R v) = listSum (termLenVec k v) + 1`. -/
noncomputable def formulaLenRelB : ArithmeticSemisentence 5 :=
  “l p v R k. !LAct.isRel k R → !(isUTermVec LAct).pi k v → !qqRelDef p k R v →
    !(formulaLenGraph LAct) l p → ∃ M s, !(termLenVecGraph LAct) M k v ∧ !listSumDef s M ∧ l = s + 1”
noncomputable def formulaLenRel : ArithmeticSentence := ∀¹* formulaLenRelB

lemma models_formulaLenRel :
    V↓[ℒₒᵣ] ⊧ formulaLenRel ↔
    ∀ l p v R k : V, LAct.IsRel k R → IsUTermVec LAct k v → p = ^rel k R v → l = formulaLen LAct p →
      ∃ M s, M = termLenVec LAct k v ∧ s = listSum M ∧ l = s + 1 := by
  simp [formulaLenRel, formulaLenRelB, models_iff, Matrix.vecForall_iff, formulaLen.defined.iff,
    termLenVec.defined.iff, listSum_defined.iff]

theorem pa_proves_formulaLenRel : 𝗣𝗔 ⊢ formulaLenRel :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_formulaLenRel.mpr fun _ _ _ _ _ hR hv hp hl ↦ by
    subst hp; subst hl; exact ⟨_, _, rfl, rfl, formulaLen_rel hR hv⟩

theorem lib_formulaLenRel : Lib formulaLenRel := Lib.of_pa pa_proves_formulaLenRel

/-- `formulaLen (nrel k R v) = listSum (termLenVec k v) + 1`. -/
noncomputable def formulaLenNRelB : ArithmeticSemisentence 5 :=
  “l p v R k. !LAct.isRel k R → !(isUTermVec LAct).pi k v → !qqNRelDef p k R v →
    !(formulaLenGraph LAct) l p → ∃ M s, !(termLenVecGraph LAct) M k v ∧ !listSumDef s M ∧ l = s + 1”
noncomputable def formulaLenNRel : ArithmeticSentence := ∀¹* formulaLenNRelB

lemma models_formulaLenNRel :
    V↓[ℒₒᵣ] ⊧ formulaLenNRel ↔
    ∀ l p v R k : V, LAct.IsRel k R → IsUTermVec LAct k v → p = ^nrel k R v → l = formulaLen LAct p →
      ∃ M s, M = termLenVec LAct k v ∧ s = listSum M ∧ l = s + 1 := by
  simp [formulaLenNRel, formulaLenNRelB, models_iff, Matrix.vecForall_iff, formulaLen.defined.iff,
    termLenVec.defined.iff, listSum_defined.iff]

theorem pa_proves_formulaLenNRel : 𝗣𝗔 ⊢ formulaLenNRel :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_formulaLenNRel.mpr fun _ _ _ _ _ hR hv hp hl ↦ by
    subst hp; subst hl; exact ⟨_, _, rfl, rfl, formulaLen_nrel hR hv⟩

theorem lib_formulaLenNRel : Lib formulaLenNRel := Lib.of_pa pa_proves_formulaLenNRel

/-- `formulaLen ⊤ = 1`. -/
noncomputable def formulaLenVerumB : ArithmeticSemisentence 2 :=
  “l p. !qqVerumDef p → !(formulaLenGraph LAct) l p → l = 1”
noncomputable def formulaLenVerum : ArithmeticSentence := ∀¹* formulaLenVerumB

lemma models_formulaLenVerum :
    V↓[ℒₒᵣ] ⊧ formulaLenVerum ↔ ∀ l p : V, p = ^⊤ → l = formulaLen LAct p → l = 1 := by
  simp [formulaLenVerum, formulaLenVerumB, models_iff, Matrix.vecForall_iff, formulaLen.defined.iff]

theorem pa_proves_formulaLenVerum : 𝗣𝗔 ⊢ formulaLenVerum :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_formulaLenVerum.mpr fun _ _ hp hl ↦ by
    subst hp; subst hl; exact formulaLen_verum

theorem lib_formulaLenVerum : Lib formulaLenVerum := Lib.of_pa pa_proves_formulaLenVerum

/-- `formulaLen ⊥ = 1`. -/
noncomputable def formulaLenFalsumB : ArithmeticSemisentence 2 :=
  “l p. !qqFalsumDef p → !(formulaLenGraph LAct) l p → l = 1”
noncomputable def formulaLenFalsum : ArithmeticSentence := ∀¹* formulaLenFalsumB

lemma models_formulaLenFalsum :
    V↓[ℒₒᵣ] ⊧ formulaLenFalsum ↔ ∀ l p : V, p = ^⊥ → l = formulaLen LAct p → l = 1 := by
  simp [formulaLenFalsum, formulaLenFalsumB, models_iff, Matrix.vecForall_iff, formulaLen.defined.iff]

theorem pa_proves_formulaLenFalsum : 𝗣𝗔 ⊢ formulaLenFalsum :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_formulaLenFalsum.mpr fun _ _ hp hl ↦ by
    subst hp; subst hl; exact formulaLen_falsum

theorem lib_formulaLenFalsum : Lib formulaLenFalsum := Lib.of_pa pa_proves_formulaLenFalsum

/-- `formulaLen (p ⋏ q) = formulaLen p + formulaLen q + 1`. -/
noncomputable def formulaLenAndB : ArithmeticSemisentence 7 :=
  “lr lq lp r q p n. !(isSemiformula LAct).pi n p → !(isSemiformula LAct).pi n q → !qqAndDef r p q →
    !(formulaLenGraph LAct) lp p → !(formulaLenGraph LAct) lq q → !(formulaLenGraph LAct) lr r →
    lr = lp + lq + 1”
noncomputable def formulaLenAnd : ArithmeticSentence := ∀¹* formulaLenAndB

lemma models_formulaLenAnd :
    V↓[ℒₒᵣ] ⊧ formulaLenAnd ↔
    ∀ lr lq lp r q p n : V, IsSemiformula LAct n p → IsSemiformula LAct n q → r = p ^⋏ q →
      lp = formulaLen LAct p → lq = formulaLen LAct q → lr = formulaLen LAct r → lr = lp + lq + 1 := by
  simp [formulaLenAnd, formulaLenAndB, models_iff, Matrix.vecForall_iff, formulaLen.defined.iff]

theorem pa_proves_formulaLenAnd : 𝗣𝗔 ⊢ formulaLenAnd :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_formulaLenAnd.mpr fun _ _ _ _ _ _ _ hp hq hr h₁ h₂ h₃ ↦ by
    subst hr; subst h₁; subst h₂; subst h₃; exact formulaLen_and hp.isUFormula hq.isUFormula

theorem lib_formulaLenAnd : Lib formulaLenAnd := Lib.of_pa pa_proves_formulaLenAnd

/-- `formulaLen (p ⋎ q) = formulaLen p + formulaLen q + 1`. -/
noncomputable def formulaLenOrB : ArithmeticSemisentence 7 :=
  “lr lq lp r q p n. !(isSemiformula LAct).pi n p → !(isSemiformula LAct).pi n q → !qqOrDef r p q →
    !(formulaLenGraph LAct) lp p → !(formulaLenGraph LAct) lq q → !(formulaLenGraph LAct) lr r →
    lr = lp + lq + 1”
noncomputable def formulaLenOr : ArithmeticSentence := ∀¹* formulaLenOrB

lemma models_formulaLenOr :
    V↓[ℒₒᵣ] ⊧ formulaLenOr ↔
    ∀ lr lq lp r q p n : V, IsSemiformula LAct n p → IsSemiformula LAct n q → r = p ^⋎ q →
      lp = formulaLen LAct p → lq = formulaLen LAct q → lr = formulaLen LAct r → lr = lp + lq + 1 := by
  simp [formulaLenOr, formulaLenOrB, models_iff, Matrix.vecForall_iff, formulaLen.defined.iff]

theorem pa_proves_formulaLenOr : 𝗣𝗔 ⊢ formulaLenOr :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_formulaLenOr.mpr fun _ _ _ _ _ _ _ hp hq hr h₁ h₂ h₃ ↦ by
    subst hr; subst h₁; subst h₂; subst h₃; exact formulaLen_or hp.isUFormula hq.isUFormula

theorem lib_formulaLenOr : Lib formulaLenOr := Lib.of_pa pa_proves_formulaLenOr

/-- `formulaLen (∀ p) = formulaLen p + 1`. -/
noncomputable def formulaLenAllB : ArithmeticSemisentence 5 :=
  “lq lp q p n. !(isSemiformula LAct).pi (n + 1) p → !qqAllDef q p →
    !(formulaLenGraph LAct) lp p → !(formulaLenGraph LAct) lq q → lq = lp + 1”
noncomputable def formulaLenAll : ArithmeticSentence := ∀¹* formulaLenAllB

lemma models_formulaLenAll :
    V↓[ℒₒᵣ] ⊧ formulaLenAll ↔
    ∀ lq lp q p n : V, IsSemiformula LAct (n + 1) p → q = ^∀ p →
      lp = formulaLen LAct p → lq = formulaLen LAct q → lq = lp + 1 := by
  simp [formulaLenAll, formulaLenAllB, models_iff, Matrix.vecForall_iff, formulaLen.defined.iff]

theorem pa_proves_formulaLenAll : 𝗣𝗔 ⊢ formulaLenAll :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_formulaLenAll.mpr fun _ _ _ _ _ hp hq h₁ h₂ ↦ by
    subst hq; subst h₁; subst h₂; exact formulaLen_all hp.isUFormula

theorem lib_formulaLenAll : Lib formulaLenAll := Lib.of_pa pa_proves_formulaLenAll

/-- `formulaLen (∃ p) = formulaLen p + 1`. -/
noncomputable def formulaLenExsB : ArithmeticSemisentence 5 :=
  “lq lp q p n. !(isSemiformula LAct).pi (n + 1) p → !qqExsDef q p →
    !(formulaLenGraph LAct) lp p → !(formulaLenGraph LAct) lq q → lq = lp + 1”
noncomputable def formulaLenExs : ArithmeticSentence := ∀¹* formulaLenExsB

lemma models_formulaLenExs :
    V↓[ℒₒᵣ] ⊧ formulaLenExs ↔
    ∀ lq lp q p n : V, IsSemiformula LAct (n + 1) p → q = ^∃ p →
      lp = formulaLen LAct p → lq = formulaLen LAct q → lq = lp + 1 := by
  simp [formulaLenExs, formulaLenExsB, models_iff, Matrix.vecForall_iff, formulaLen.defined.iff]

theorem pa_proves_formulaLenExs : 𝗣𝗔 ⊢ formulaLenExs :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_formulaLenExs.mpr fun _ _ _ _ _ hp hq h₁ h₂ ↦ by
    subst hq; subst h₁; subst h₂; exact formulaLen_exs hp.isUFormula

theorem lib_formulaLenExs : Lib formulaLenExs := Lib.of_pa pa_proves_formulaLenExs

/-- `formulaLen (neg p) = formulaLen p`. -/
noncomputable def formulaLenNegB : ArithmeticSemisentence 5 :=
  “ly lp y p n. !(isSemiformula LAct).pi n p → !(negGraph LAct) y p →
    !(formulaLenGraph LAct) lp p → !(formulaLenGraph LAct) ly y → ly = lp”
noncomputable def formulaLenNeg : ArithmeticSentence := ∀¹* formulaLenNegB

lemma models_formulaLenNeg :
    V↓[ℒₒᵣ] ⊧ formulaLenNeg ↔
    ∀ ly lp y p n : V, IsSemiformula LAct n p → y = neg LAct p →
      lp = formulaLen LAct p → ly = formulaLen LAct y → ly = lp := by
  simp [formulaLenNeg, formulaLenNegB, models_iff, Matrix.vecForall_iff, formulaLen.defined.iff,
    neg.defined.iff]

theorem pa_proves_formulaLenNeg : 𝗣𝗔 ⊢ formulaLenNeg :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_formulaLenNeg.mpr fun _ _ _ _ _ hp hy h₁ h₂ ↦ by
    subst hy; subst h₁; subst h₂; exact formulaLen_neg hp.isUFormula

theorem lib_formulaLenNeg : Lib formulaLenNeg := Lib.of_pa pa_proves_formulaLenNeg

/-- `termLen #z = z + 1`. -/
noncomputable def termLenBvarB : ArithmeticSemisentence 3 :=
  “l t z. !qqBvarDef t z → !(termLenGraph LAct) l t → l = z + 1”
noncomputable def termLenBvar : ArithmeticSentence := ∀¹* termLenBvarB

lemma models_termLenBvar :
    V↓[ℒₒᵣ] ⊧ termLenBvar ↔ ∀ l t z : V, t = qqBvar z → l = termLen LAct t → l = z + 1 := by
  simp [termLenBvar, termLenBvarB, models_iff, Matrix.vecForall_iff, termLen.defined.iff]

theorem pa_proves_termLenBvar : 𝗣𝗔 ⊢ termLenBvar :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_termLenBvar.mpr fun _ _ z ht hl ↦ by
    subst ht; subst hl; exact termLen_bvar z

theorem lib_termLenBvar : Lib termLenBvar := Lib.of_pa pa_proves_termLenBvar

/-- `termLen &x = x + 1`. -/
noncomputable def termLenFvarB : ArithmeticSemisentence 3 :=
  “l t x. !qqFvarDef t x → !(termLenGraph LAct) l t → l = x + 1”
noncomputable def termLenFvar : ArithmeticSentence := ∀¹* termLenFvarB

lemma models_termLenFvar :
    V↓[ℒₒᵣ] ⊧ termLenFvar ↔ ∀ l t x : V, t = qqFvar x → l = termLen LAct t → l = x + 1 := by
  simp [termLenFvar, termLenFvarB, models_iff, Matrix.vecForall_iff, termLen.defined.iff]

theorem pa_proves_termLenFvar : 𝗣𝗔 ⊢ termLenFvar :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_termLenFvar.mpr fun _ _ x ht hl ↦ by
    subst ht; subst hl; exact termLen_fvar x

theorem lib_termLenFvar : Lib termLenFvar := Lib.of_pa pa_proves_termLenFvar

/-- `termLen (func k f v) = listSum (termLenVec k v) + 1`. -/
noncomputable def termLenFuncB : ArithmeticSemisentence 5 :=
  “l t v f k. !LAct.isFunc k f → !(isUTermVec LAct).pi k v → !qqFuncDef t k f v →
    !(termLenGraph LAct) l t → ∃ M s, !(termLenVecGraph LAct) M k v ∧ !listSumDef s M ∧ l = s + 1”
noncomputable def termLenFunc : ArithmeticSentence := ∀¹* termLenFuncB

lemma models_termLenFunc :
    V↓[ℒₒᵣ] ⊧ termLenFunc ↔
    ∀ l t v f k : V, LAct.IsFunc k f → IsUTermVec LAct k v → t = qqFunc k f v → l = termLen LAct t →
      ∃ M s, M = termLenVec LAct k v ∧ s = listSum M ∧ l = s + 1 := by
  simp [termLenFunc, termLenFuncB, models_iff, Matrix.vecForall_iff, termLen.defined.iff,
    termLenVec.defined.iff, listSum_defined.iff]

theorem pa_proves_termLenFunc : 𝗣𝗔 ⊢ termLenFunc :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_termLenFunc.mpr fun _ _ _ _ _ hf hv ht hl ↦ by
    subst ht; subst hl; exact ⟨_, _, rfl, rfl, termLen_func hf hv⟩

theorem lib_termLenFunc : Lib termLenFunc := Lib.of_pa pa_proves_termLenFunc

/-! ### Code level: the bit recursion of the binary-numeral code `bnum` -/

/-- `1 ≤ m → bnum (2m) = 𝟐 ^* bnum m` (`𝟐 = 𝟏 ^+ 𝟏`, `𝟏` the code of the term `1`). -/
noncomputable def bnumEvenB : ArithmeticSemisentence 3 :=
  “u t m. 1 ≤ m → !bnumGraph t m → !bnumGraph u (2 * m) →
    ∃ one two, one = ↑Arithmetic.one ∧ !qqAddGraph two one one ∧ !qqMulGraph u two t”
noncomputable def bnumEven : ArithmeticSentence := ∀¹* bnumEvenB

lemma models_bnumEven :
    V↓[ℒₒᵣ] ⊧ bnumEven ↔
    ∀ u t m : V, 1 ≤ m → t = bnum m → u = bnum (2 * m) →
      ∃ one two : V, one = ((𝟏 : ℕ) : V) ∧ two = one ^+ one ∧ u = two ^* t := by
  simp [bnumEven, bnumEvenB, models_iff, Matrix.vecForall_iff, bnum.defined.iff,
    qqAdd_defined.iff, qqMul_defined.iff, numeral_eq_natCast]

theorem pa_proves_bnumEven : 𝗣𝗔 ⊢ bnumEven :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_bnumEven.mpr fun _ _ _ hm ht hu ↦ by
    subst ht; subst hu; exact ⟨_, _, rfl, rfl, by rw [bnum_two_mul hm]; rfl⟩

theorem lib_bnumEven : Lib bnumEven := Lib.of_pa pa_proves_bnumEven

/-- `1 ≤ m → bnum (2m + 1) = (𝟐 ^* bnum m) ^+ 𝟏`. -/
noncomputable def bnumOddB : ArithmeticSemisentence 3 :=
  “u t m. 1 ≤ m → !bnumGraph t m → !bnumGraph u (2 * m + 1) →
    ∃ one two s, one = ↑Arithmetic.one ∧ !qqAddGraph two one one ∧ !qqMulGraph s two t ∧
      !qqAddGraph u s one”
noncomputable def bnumOdd : ArithmeticSentence := ∀¹* bnumOddB

lemma models_bnumOdd :
    V↓[ℒₒᵣ] ⊧ bnumOdd ↔
    ∀ u t m : V, 1 ≤ m → t = bnum m → u = bnum (2 * m + 1) →
      ∃ one two s : V, one = ((𝟏 : ℕ) : V) ∧ two = one ^+ one ∧ s = two ^* t ∧ u = s ^+ one := by
  simp [bnumOdd, bnumOddB, models_iff, Matrix.vecForall_iff, bnum.defined.iff,
    qqAdd_defined.iff, qqMul_defined.iff, numeral_eq_natCast]

theorem pa_proves_bnumOdd : 𝗣𝗔 ⊢ bnumOdd :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_bnumOdd.mpr fun _ _ _ hm ht hu ↦ by
    subst ht; subst hu; exact ⟨_, _, _, rfl, rfl, rfl, by rw [bnum_two_mul_add_one hm]; rfl⟩

theorem lib_bnumOdd : Lib bnumOdd := Lib.of_pa pa_proves_bnumOdd

/-! ### Term level: the binary-numeral laws in `NumeralFacts`' syntax -/

section termLevel

/-- `t + u` as the raw `Add` atom (the syntax `twoMulOne` uses). -/
def addO {ξ : Type*} {n : ℕ} (t u : Semiterm ℒₒᵣ ξ n) : Semiterm ℒₒᵣ ξ n :=
  FirstOrder.Semiterm.func Language.Add.add ![t, u]

/-- `t = u` as the raw `Eq` atom. -/
def eqO {ξ : Type*} {n : ℕ} (t u : Semiterm ℒₒᵣ ξ n) : Semiformula ℒₒᵣ ξ n :=
  Semiformula.rel Language.Eq.eq ![t, u]

/-- `1` as the raw term. -/
def oneO {ξ : Type*} {n : ℕ} : Semiterm ℒₒᵣ ξ n := FirstOrder.Semiterm.func Language.One.one ![]

lemma twoMulOne_eq {ξ : Type*} {n : ℕ} (t : Semiterm ℒₒᵣ ξ n) : twoMulOne t = addO (twoMul t) oneO := rfl

/-- `2x + 2y = 2(x + y)`. -/
noncomputable def twoMulAddB : ArithmeticSemisentence 2 :=
  eqO (addO (twoMul #0) (twoMul #1)) (twoMul (addO #0 #1))
noncomputable def twoMulAdd : ArithmeticSentence := ∀¹* twoMulAddB

lemma models_twoMulAdd : V↓[ℒₒᵣ] ⊧ twoMulAdd ↔ ∀ x y : V, 2 * x + 2 * y = 2 * (x + y) := by
  simp [twoMulAdd, twoMulAddB, eqO, addO, twoMul, models_iff, Matrix.vecForall_iff, one_add_one_eq_two]

theorem pa_proves_twoMulAdd : 𝗣𝗔 ⊢ twoMulAdd :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_twoMulAdd.mpr fun x y ↦ (mul_add 2 x y).symm

theorem lib_twoMulAdd : Lib twoMulAdd := Lib.of_pa pa_proves_twoMulAdd

/-- `2x + (2y + 1) = 2(x + y) + 1`. -/
noncomputable def twoMulAddOneB : ArithmeticSemisentence 2 :=
  eqO (addO (twoMul #0) (twoMulOne #1)) (twoMulOne (addO #0 #1))
noncomputable def twoMulAddOne : ArithmeticSentence := ∀¹* twoMulAddOneB

lemma models_twoMulAddOne :
    V↓[ℒₒᵣ] ⊧ twoMulAddOne ↔ ∀ x y : V, 2 * x + (2 * y + 1) = 2 * (x + y) + 1 := by
  simp [twoMulAddOne, twoMulAddOneB, eqO, addO, twoMul, twoMulOne, models_iff, Matrix.vecForall_iff,
    one_add_one_eq_two]

theorem pa_proves_twoMulAddOne : 𝗣𝗔 ⊢ twoMulAddOne :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_twoMulAddOne.mpr fun x y ↦ by
    rw [← add_assoc, ← mul_add]

theorem lib_twoMulAddOne : Lib twoMulAddOne := Lib.of_pa pa_proves_twoMulAddOne

/-- `(2x + 1) + 2y = 2(x + y) + 1`. -/
noncomputable def twoMulOneAddB : ArithmeticSemisentence 2 :=
  eqO (addO (twoMulOne #0) (twoMul #1)) (twoMulOne (addO #0 #1))
noncomputable def twoMulOneAdd : ArithmeticSentence := ∀¹* twoMulOneAddB

lemma models_twoMulOneAdd :
    V↓[ℒₒᵣ] ⊧ twoMulOneAdd ↔ ∀ x y : V, 2 * x + 1 + 2 * y = 2 * (x + y) + 1 := by
  simp [twoMulOneAdd, twoMulOneAddB, eqO, addO, twoMul, twoMulOne, models_iff, Matrix.vecForall_iff,
    one_add_one_eq_two]

theorem pa_proves_twoMulOneAdd : 𝗣𝗔 ⊢ twoMulOneAdd :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_twoMulOneAdd.mpr fun x y ↦ by
    rw [add_right_comm, ← mul_add]

theorem lib_twoMulOneAdd : Lib twoMulOneAdd := Lib.of_pa pa_proves_twoMulOneAdd

/-- `(2x + 1) + (2y + 1) = 2(x + y + 1)`. -/
noncomputable def twoMulOneAddOneB : ArithmeticSemisentence 2 :=
  eqO (addO (twoMulOne #0) (twoMulOne #1)) (twoMul (addO (addO #0 #1) oneO))
noncomputable def twoMulOneAddOne : ArithmeticSentence := ∀¹* twoMulOneAddOneB

lemma models_twoMulOneAddOne :
    V↓[ℒₒᵣ] ⊧ twoMulOneAddOne ↔ ∀ x y : V, 2 * x + 1 + (2 * y + 1) = 2 * (x + y + 1) := by
  simp [twoMulOneAddOne, twoMulOneAddOneB, eqO, addO, twoMul, twoMulOne, oneO, models_iff,
    Matrix.vecForall_iff, one_add_one_eq_two]

theorem pa_proves_twoMulOneAddOne : 𝗣𝗔 ⊢ twoMulOneAddOne :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_twoMulOneAddOne.mpr fun x y ↦ by
    rw [mul_add, mul_add, mul_one, ← one_add_one_eq_two]; ac_rfl

theorem lib_twoMulOneAddOne : Lib twoMulOneAddOne := Lib.of_pa pa_proves_twoMulOneAddOne

/-- The carry: `(2x + 1) + 1 = 2(x + 1)`. -/
noncomputable def twoMulOneSuccB : ArithmeticSemisentence 1 :=
  eqO (addO (twoMulOne #0) oneO) (twoMul (addO #0 oneO))
noncomputable def twoMulOneSucc : ArithmeticSentence := ∀¹* twoMulOneSuccB

lemma models_twoMulOneSucc : V↓[ℒₒᵣ] ⊧ twoMulOneSucc ↔ ∀ x : V, 2 * x + 1 + 1 = 2 * (x + 1) := by
  simp [twoMulOneSucc, twoMulOneSuccB, eqO, addO, twoMul, twoMulOne, oneO, models_iff,
    Matrix.vecForall_iff, one_add_one_eq_two]

theorem pa_proves_twoMulOneSucc : 𝗣𝗔 ⊢ twoMulOneSucc :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_twoMulOneSucc.mpr fun x ↦ by
    rw [mul_add, mul_one, add_assoc, one_add_one_eq_two]

theorem lib_twoMulOneSucc : Lib twoMulOneSucc := Lib.of_pa pa_proves_twoMulOneSucc

/-- `n ≤ x → m ≤ y → n + m ≤ x + y`. -/
noncomputable def addLeAddB : ArithmeticSemisentence 4 :=
  leF #0 #2 🡒 leF #1 #3 🡒 leF (addO #0 #1) (addO #2 #3)
noncomputable def addLeAdd : ArithmeticSentence := ∀¹* addLeAddB

lemma models_addLeAdd :
    V↓[ℒₒᵣ] ⊧ addLeAdd ↔ ∀ n m x y : V, n ≤ x → m ≤ y → n + m ≤ x + y := by
  simp [addLeAdd, addLeAddB, leF, addO, models_iff, Matrix.vecForall_iff, le_def]

theorem pa_proves_addLeAdd : 𝗣𝗔 ⊢ addLeAdd :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_addLeAdd.mpr fun _ _ _ _ h₁ h₂ ↦ add_le_add h₁ h₂

theorem lib_addLeAdd : Lib addLeAdd := Lib.of_pa pa_proves_addLeAdd

/-- `n ≤ x → n ≤ x + y`. -/
noncomputable def leAddRightB : ArithmeticSemisentence 3 := leF #0 #1 🡒 leF #0 (addO #1 #2)
noncomputable def leAddRight : ArithmeticSentence := ∀¹* leAddRightB

lemma models_leAddRight : V↓[ℒₒᵣ] ⊧ leAddRight ↔ ∀ n x y : V, n ≤ x → n ≤ x + y := by
  simp [leAddRight, leAddRightB, leF, addO, models_iff, Matrix.vecForall_iff, le_def]

theorem pa_proves_leAddRight : 𝗣𝗔 ⊢ leAddRight :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_leAddRight.mpr fun _ _ _ h ↦ le_trans h le_self_add

theorem lib_leAddRight : Lib leAddRight := Lib.of_pa pa_proves_leAddRight

/-- `x ≤ y → y ≤ z → x ≤ z`. -/
noncomputable def leTransB : ArithmeticSemisentence 3 := leF #0 #1 🡒 leF #1 #2 🡒 leF #0 #2
noncomputable def leTrans : ArithmeticSentence := ∀¹* leTransB

lemma models_leTrans : V↓[ℒₒᵣ] ⊧ leTrans ↔ ∀ x y z : V, x ≤ y → y ≤ z → x ≤ z := by
  simp [leTrans, leTransB, leF, models_iff, Matrix.vecForall_iff, le_def]

theorem pa_proves_leTrans : 𝗣𝗔 ⊢ leTrans :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_leTrans.mpr fun _ _ _ h₁ h₂ ↦ le_trans h₁ h₂

theorem lib_leTrans : Lib leTrans := Lib.of_pa pa_proves_leTrans

/-- `x = y → x ≤ y`. -/
noncomputable def leOfEqB : ArithmeticSemisentence 2 := eqO #0 #1 🡒 leF #0 #1
noncomputable def leOfEq : ArithmeticSentence := ∀¹* leOfEqB

lemma models_leOfEq : V↓[ℒₒᵣ] ⊧ leOfEq ↔ ∀ x y : V, x = y → x ≤ y := by
  simp [leOfEq, leOfEqB, leF, eqO, models_iff, Matrix.vecForall_iff, le_def]

theorem pa_proves_leOfEq : 𝗣𝗔 ⊢ leOfEq :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_leOfEq.mpr fun _ _ h ↦ le_of_eq h

theorem lib_leOfEq : Lib leOfEq := Lib.of_pa pa_proves_leOfEq

/-- `x ≤ y → y = z → x ≤ z` (rewrite the bound by a numeral law). -/
noncomputable def leOfLeEqB : ArithmeticSemisentence 3 := leF #0 #1 🡒 eqO #1 #2 🡒 leF #0 #2
noncomputable def leOfLeEq : ArithmeticSentence := ∀¹* leOfLeEqB

lemma models_leOfLeEq : V↓[ℒₒᵣ] ⊧ leOfLeEq ↔ ∀ x y z : V, x ≤ y → y = z → x ≤ z := by
  simp [leOfLeEq, leOfLeEqB, leF, eqO, models_iff, Matrix.vecForall_iff, le_def]

theorem pa_proves_leOfLeEq : 𝗣𝗔 ⊢ leOfLeEq :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_leOfLeEq.mpr fun _ _ _ h e ↦ e ▸ h

theorem lib_leOfLeEq : Lib leOfLeEq := Lib.of_pa pa_proves_leOfLeEq

/-- `x ≤ y → x + 1 ≤ y + 1`. -/
noncomputable def succLeSuccB : ArithmeticSemisentence 2 := leF #0 #1 🡒 leF (addO #0 oneO) (addO #1 oneO)
noncomputable def succLeSucc : ArithmeticSentence := ∀¹* succLeSuccB

lemma models_succLeSucc : V↓[ℒₒᵣ] ⊧ succLeSucc ↔ ∀ x y : V, x ≤ y → x + 1 ≤ y + 1 := by
  simp [succLeSucc, succLeSuccB, leF, addO, oneO, models_iff, le_def]

theorem pa_proves_succLeSucc : 𝗣𝗔 ⊢ succLeSucc :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_succLeSucc.mpr fun _ _ h ↦ add_le_add h (le_refl 1)

theorem lib_succLeSucc : Lib succLeSucc := Lib.of_pa pa_proves_succLeSucc

/-- `x + y + z = x + (y + z)`. -/
noncomputable def addAssocB : ArithmeticSemisentence 3 :=
  eqO (addO (addO #0 #1) #2) (addO #0 (addO #1 #2))
noncomputable def addAssoc : ArithmeticSentence := ∀¹* addAssocB

lemma models_addAssoc : V↓[ℒₒᵣ] ⊧ addAssoc ↔ ∀ x y z : V, x + y + z = x + (y + z) := by
  simp [addAssoc, addAssocB, eqO, addO, models_iff, add_assoc]

theorem pa_proves_addAssoc : 𝗣𝗔 ⊢ addAssoc :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_addAssoc.mpr fun x y z ↦ add_assoc x y z

theorem lib_addAssoc : Lib addAssoc := Lib.of_pa pa_proves_addAssoc

/-- `x + y = y + x`. -/
noncomputable def addCommB : ArithmeticSemisentence 2 := eqO (addO #0 #1) (addO #1 #0)
noncomputable def addComm : ArithmeticSentence := ∀¹* addCommB

lemma models_addComm : V↓[ℒₒᵣ] ⊧ addComm ↔ ∀ x y : V, x + y = y + x := by
  simp [addComm, addCommB, eqO, addO, models_iff, add_comm]

theorem pa_proves_addComm : 𝗣𝗔 ⊢ addComm :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_addComm.mpr fun x y ↦ add_comm x y

theorem lib_addComm : Lib addComm := Lib.of_pa pa_proves_addComm

end termLevel

end ArithS
