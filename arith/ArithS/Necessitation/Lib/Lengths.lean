import ArithS.Necessitation.Lib.Basic

/-!
# ArithS.Necessitation.Lib.Lengths — the `lengths` rows of the library `Λ`

`DESIGN_inner_necessitation.md` §3.1 row `lengths` and §4.1–4.2. Same convention as
`Sets.lean` (body `xB : ArithmeticSemisentence m` in index order, `x := ∀¹* xB`, `models_x`,
`pa_proves_x`, `lib_x`). Two layers:

1. **Code level** (the `ℒₒᵣ` DSL over the package's graphs): totality of `formulaLen`,
   `termLen`, `termLenVec`, `listSum`, `sequentLen`, `binNumeral`; `sequentLen (insert x s) ≤ sequentLen s +
   formulaLen x` and `sequentLen ∅ = 0` (§4.2: the sequent length is BOUNDED, never computed);
   `formulaLen` of every constructor (`|p ⋏ q| = |p| + |q| + 1`, …, `|rel k R v| = Σ|vᵢ| + 1`),
   `formulaLen (neg p) = formulaLen p`, `termLen` of `#z`, `&x`, `func k f v`; and the
   bit-recursion laws of the binary-numeral CODE `binNumeral` (`binNumeral (2m) = 𝟐 ^* binNumeral m`,
   `binNumeral (2m+1) = (𝟐 ^* binNumeral m) ^+ 𝟏`, `BinNumeral.lean:345-348`).
2. **Term level** (§4.1, the `NumeralFacts.lean` pattern, in ITS syntax — `leF`, `twoMul`,
   `twoMulOne` — so the meta-level assembly instantiates them at `binNumeralMeta` exactly as
   `leEven`/`leOdd`): the laws that add two binary numerals bit by bit,
   `2x + 2y = 2(x+y)`, `2x + (2y+1) = 2(x+y)+1`, `(2x+1) + 2y = 2(x+y)+1`,
   `(2x+1) + (2y+1) = 2(x+y+1)`, the carry `(2x+1) + 1 = 2(x+1)`, and the order glue
   `n ≤ x → m ≤ y → n + m ≤ x + y`, `n ≤ x → n ≤ x + y`, transitivity, `x = y → x ≤ y`,
   `x ≤ y → x + 1 ≤ y + 1`, associativity/commutativity of `+`.

   Why no "internal value" law: a numeral in a sequent is a TERM, so "`n ≤ val (binNumeral a)`" is
   the formula `n ≤ binNumeralMeta a` and the bit laws above are exactly what the assembly needs (the
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

/-! ### Code level: `sequentLen` -/

/-- `sequentLen (insert x s) ≤ sequentLen s + formulaLen x`. -/
noncomputable def sequentLenInsertLeB : ArithmeticSemisentence 6 :=
  “lx ls l t s x. !insertDef t x s → !(sequentLenDef LAct) l t → !(sequentLenDef LAct) ls s →
    !(formulaLenGraph LAct) lx x → l ≤ ls + lx”
noncomputable def sequentLenInsertLe : ArithmeticSentence := ∀¹* sequentLenInsertLeB

lemma models_sequentLenInsertLe :
    V↓[ℒₒᵣ] ⊧ sequentLenInsertLe ↔
    ∀ lx ls l t s x : V, t = insert x s → l = sequentLen LAct t → ls = sequentLen LAct s →
      lx = formulaLen LAct x → l ≤ ls + lx := by
  simp [sequentLenInsertLe, sequentLenInsertLeB, models_iff, Matrix.vecForall_iff, sequentLen_defined.iff,
    formulaLen.defined.iff]

theorem pa_proves_sequentLenInsertLe : 𝗣𝗔 ⊢ sequentLenInsertLe :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_sequentLenInsertLe.mpr fun _ _ _ _ s x ht hl hls hlx ↦ by
    subst ht; subst hl; subst hls; subst hlx; exact sequentLen_insert_le x s

theorem lib_sequentLenInsertLe : Lib sequentLenInsertLe := Lib.of_pa pa_proves_sequentLenInsertLe

/-! ### Code level: `formulaLen`/`termLen` of the constructors -/

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

/-! ### Code level: the bit recursion of the binary-numeral code `binNumeral` -/

/-- `1 ≤ m → binNumeral (2m) = 𝟐 ^* binNumeral m` (`𝟐 = 𝟏 ^+ 𝟏`, `𝟏` the code of the term `1`). -/
noncomputable def binNumeralEvenB : ArithmeticSemisentence 3 :=
  “u t m. 1 ≤ m → !binNumeralGraph t m → !binNumeralGraph u (2 * m) →
    ∃ one two, one = ↑Arithmetic.one ∧ !qqAddGraph two one one ∧ !qqMulGraph u two t”
noncomputable def binNumeralEven : ArithmeticSentence := ∀¹* binNumeralEvenB

lemma models_binNumeralEven :
    V↓[ℒₒᵣ] ⊧ binNumeralEven ↔
    ∀ u t m : V, 1 ≤ m → t = binNumeral m → u = binNumeral (2 * m) →
      ∃ one two : V, one = ((𝟏 : ℕ) : V) ∧ two = one ^+ one ∧ u = two ^* t := by
  simp [binNumeralEven, binNumeralEvenB, models_iff, Matrix.vecForall_iff, binNumeral.defined.iff,
    qqAdd_defined.iff, qqMul_defined.iff, numeral_eq_natCast]

theorem pa_proves_binNumeralEven : 𝗣𝗔 ⊢ binNumeralEven :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_binNumeralEven.mpr fun _ _ _ hm ht hu ↦ by
    subst ht; subst hu; exact ⟨_, _, rfl, rfl, by rw [binNumeral_two_mul hm]; rfl⟩

theorem lib_binNumeralEven : Lib binNumeralEven := Lib.of_pa pa_proves_binNumeralEven

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

/-- `x ≤ y → y ≤ z → x ≤ z`. -/
noncomputable def leTransB : ArithmeticSemisentence 3 := leF #0 #1 🡒 leF #1 #2 🡒 leF #0 #2
noncomputable def leTrans : ArithmeticSentence := ∀¹* leTransB

lemma models_leTrans : V↓[ℒₒᵣ] ⊧ leTrans ↔ ∀ x y z : V, x ≤ y → y ≤ z → x ≤ z := by
  simp [leTrans, leTransB, leF, models_iff, Matrix.vecForall_iff, le_def]

theorem pa_proves_leTrans : 𝗣𝗔 ⊢ leTrans :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_leTrans.mpr fun _ _ _ h₁ h₂ ↦ le_trans h₁ h₂

theorem lib_leTrans : Lib leTrans := Lib.of_pa pa_proves_leTrans

/-- `x + y = y + x`. -/
noncomputable def addCommB : ArithmeticSemisentence 2 := eqO (addO #0 #1) (addO #1 #0)

end termLevel

end ArithS
