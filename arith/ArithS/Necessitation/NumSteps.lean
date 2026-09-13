import ArithS.Necessitation.Chain

/-!
# ArithS.Necessitation.NumSteps — Σ₁ provers of closed binary-numeral facts (derivation codes)

`M4_BOUNDED_HBL/DESIGN_fragments.md` §2.3–2.4 and `BRIEF.md` §11: every closed arithmetic
fact between binary numerals the fragments need (`bnum a + bnum b = bnum (a + b)`, `bnum a ≤
bnum b`, `bnum a + bnum b + bnum c + 1 ≤ bnum n`, …) is cut into the verification proof by ONE
`sLemma A dA` step whose data `dA` is a DERIVATION CODE of the singleton `{A}` — produced,
inside every model of `𝗜𝚺₁`, by the Σ₁ provers of this file, at a length polynomial in the
bit lengths (`termLen (bnum ·)`), never in the numbers.

The construction is `NumeralFacts.lean`'s bit recursion lifted to codes: a fact about `(a, b)` is
derived from the fact about `(a / 2, b / 2)` (and, for a carry, about `(a/2 + b/2, 1)`) by ONE
Horn row of the library instantiated at the sub-numerals (`useHornCode`, the row's proof code
read from a TABLE `tbl` — `NumTableOK tbl N B`, `exists_numTable`) and ONE lemma cut per
sub-fact (`cut1`, Chain's `lemmaCut_proof`). The recursion is a `Fixpoint` on `⟪a, b, d⟫`
(`AddGraph`, the `Bnum` pattern; `Finite` — the graph is Σ₁, all a Σ₁ function needs), with
existence + correctness + length by ONE Σ₁ order induction on `a + b` (bounded quantifiers) and
uniqueness by Π₁ induction. Everything else is non-recursive on top of `addCode` (`leCode`,
`ltCode`, the node bookkeeping facts) or a `PR` on a unary index (`cTEqCode`).

The rows are written in `NumeralFacts.lean`'s operator syntax (`eqO`/`leF`/`ltF`, `addO`,
`twoMul`, `twoMulOne`, `oneO`), so their codes are `impChain`s of canonical facts `eqFact`/
`leFact`/`ltFact` — `subst ?[t, u] P` with `P` the code of the `=`/`≤`/`<` operator sentence
(`Peq`; `Ple`, `Plt` of `Chain`/`RowInst`) — and `bnum`'s bit equations (`bnum (2m) = 𝟐 ^* bnum m`,
`bnum (2m + 1) = (𝟐 ^* bnum m) ^+ 𝟏`) match the rows' conclusions SYNTACTICALLY.

Delivered (DESIGN §2.4's table): N1 `addCode` (`addFact a b`), N2 `leCode` (`a ≤ b`), `ltCode`
(`a < b`), N7 (`oneLe` = `leCode 1 a`), the node bookkeeping facts N3 at fixed arities
(`bin3Fact`: `bnum a + bnum b + bnum c + 1 ≤ bnum n`, `bin2Fact`, `leafFact`, `sum2Fact`), and
N6 `cTEqCode` (`cT z = bnum z`, hence `cT z ≤ bnum z`). Each comes with its `DerivationOf`
theorem, a `dlen` bound, and its `sLemma` packaging (`LemmaOK` + `stepCost`).
-/

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open LAct

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

set_option linter.unusedSimpArgs false

/-! ## 1. Syntax: the `=` fact code, term codes of the operator syntax, numeral codes -/

section syntaxCodes

/-- The `=` operator sentence over `LAct` (the twin of `Chain.leS`). -/
noncomputable def eqS : Semisentence LAct 2 :=
  Semiformula.lMap emb (Rewriting.emb (Semiformula.Operator.Eq.eq : Semiformula.Operator ℒₒᵣ 2).sentence : ArithmeticSemisentence 2)
noncomputable def Peq : V := ⌜eqS⌝
lemma isSemiformula_Peq : IsSemiformula LAct ((2 : ℕ) : V) Peq := Sentence.quote_isSemiformula _

/-- `t = u` as a canonical fact code. -/
noncomputable def eqFact (a b : V) : V := subst LAct (listToVec [a, b]) Peq
noncomputable def eqFactDef : 𝚺₁.Semisentence 3 := fact2Def eqS
instance eqFact_defined : 𝚺₁-Function₂ (eqFact : V → V → V) via eqFactDef := fact2_defined eqS
instance eqFact_definable : 𝚺₁-Function₂ (eqFact : V → V → V) := eqFact_defined.to_definable

lemma isFormula_eqFact {a b : V} (ha : IsSemiterm LAct 0 a) (hb : IsSemiterm LAct 0 b) : IsFormula LAct (eqFact a b) :=
  isFormula_fact isSemiformula_Peq _ rfl (List.forall_mem_cons.mpr ⟨ha, List.forall_mem_cons.mpr ⟨hb, List.forall_mem_nil _⟩⟩)

lemma formulaLen_eqFact_le {B : V} (hB : 1 ≤ B) {a b : V} (ha : IsSemiterm LAct 0 a) (hb : IsSemiterm LAct 0 b)
    (hla : termLen LAct a ≤ B) (hlb : termLen LAct b ≤ B) :
    formulaLen LAct (eqFact a b) ≤ formulaLen LAct (Peq : V) * B :=
  formulaLen_fact_le hB isSemiformula_Peq _ rfl (List.forall_mem_cons.mpr ⟨⟨ha, hla⟩, List.forall_mem_cons.mpr ⟨⟨hb, hlb⟩, List.forall_mem_nil _⟩⟩)

lemma formulaLen_leFact_le {B : V} (hB : 1 ≤ B) {a b : V} (ha : IsSemiterm LAct 0 a) (hb : IsSemiterm LAct 0 b)
    (hla : termLen LAct a ≤ B) (hlb : termLen LAct b ≤ B) :
    formulaLen LAct (leFact a b) ≤ formulaLen LAct (Ple : V) * B :=
  formulaLen_fact_le hB isSemiformula_Ple _ rfl (List.forall_mem_cons.mpr ⟨⟨ha, hla⟩, List.forall_mem_cons.mpr ⟨⟨hb, hlb⟩, List.forall_mem_nil _⟩⟩)

/-- `0` as the raw term (the twin of `oneO`). -/
def zeroO {ξ : Type*} {n : ℕ} : Semiterm ℒₒᵣ ξ n := FirstOrder.Semiterm.func Language.Zero.zero ![]

/-! ### Quotes of the operator syntax -/

lemma quote_leF_closed {m : ℕ} (t u : ClosedSemiterm ℒₒᵣ m) :
    (⌜Semiformula.lMap emb (leF t u : Semisentence ℒₒᵣ m)⌝ : V) = leFact (⌜t⌝ : V) (⌜u⌝ : V) := by
  rw [leF_eq_operator]
  show (⌜Semiformula.lMap emb ((Rewriting.emb (Semiformula.Operator.LE.le : Semiformula.Operator ℒₒᵣ 2).sentence : ArithmeticSemisentence 2) ⇜ ![t, u])⌝ : V) = _
  rw [quote_lMap_emb_subst', matrixToVec_fin2]
  rfl

lemma quote_ltF_closed {m : ℕ} (t u : ClosedSemiterm ℒₒᵣ m) :
    (⌜Semiformula.lMap emb (ltF t u : Semisentence ℒₒᵣ m)⌝ : V) = ltFact (⌜t⌝ : V) (⌜u⌝ : V) := by
  rw [ltF_eq_operator]
  show (⌜Semiformula.lMap emb ((Rewriting.emb (Semiformula.Operator.LT.lt : Semiformula.Operator ℒₒᵣ 2).sentence : ArithmeticSemisentence 2) ⇜ ![t, u])⌝ : V) = _
  rw [quote_lMap_emb_subst', matrixToVec_fin2]
  rfl

lemma quote_eqO_closed {m : ℕ} (t u : ClosedSemiterm ℒₒᵣ m) :
    (⌜Semiformula.lMap emb (eqO t u : Semisentence ℒₒᵣ m)⌝ : V) = eqFact (⌜t⌝ : V) (⌜u⌝ : V) := by
  unfold eqO
  rw [← Semiformula.Operator.eq_def]
  show (⌜Semiformula.lMap emb ((Rewriting.emb (Semiformula.Operator.Eq.eq : Semiformula.Operator ℒₒᵣ 2).sentence : ArithmeticSemisentence 2) ⇜ ![t, u])⌝ : V) = _
  rw [quote_lMap_emb_subst', matrixToVec_fin2]
  rfl

lemma addO_eq_add {m : ℕ} (t u : ClosedSemiterm ℒₒᵣ m) : addO t u = ‘!!t + !!u’ := by
  show _ = Semiterm.Operator.Add.add.operator ![t, u]
  simp only [Semiterm.Operator.operator, Semiterm.Operator.Add.term_eq, Rew.func]
  unfold addO; congr 1

lemma mulO_eq_mul {m : ℕ} (t u : ClosedSemiterm ℒₒᵣ m) :
    (FirstOrder.Semiterm.func Language.Mul.mul ![t, u] : ClosedSemiterm ℒₒᵣ m) = ‘!!t * !!u’ := by
  show _ = Semiterm.Operator.Mul.mul.operator ![t, u]
  simp only [Semiterm.Operator.operator, Semiterm.Operator.Mul.term_eq, Rew.func]
  congr 1

lemma oneO_eq_one {m : ℕ} : (oneO : ClosedSemiterm ℒₒᵣ m) = ‘1’ := by
  have e : (‘1’ : ClosedSemiterm ℒₒᵣ m) = ↑(1 : ℕ) := by simp
  rw [e]
  change _ = (Semiterm.Operator.numeral ℒₒᵣ 1).operator ![]
  rw [Semiterm.Operator.numeral_one]
  simp [Semiterm.Operator.operator, Semiterm.Operator.One.term_eq, Rew.func, oneO]

lemma zeroO_eq_zero {m : ℕ} : (zeroO : ClosedSemiterm ℒₒᵣ m) = ‘0’ := by
  have e : (‘0’ : ClosedSemiterm ℒₒᵣ m) = ↑(0 : ℕ) := by simp
  rw [e]
  change _ = (Semiterm.Operator.numeral ℒₒᵣ 0).operator ![]
  rw [Semiterm.Operator.numeral_zero]
  simp [Semiterm.Operator.operator, Semiterm.Operator.Zero.term_eq, Rew.func, zeroO]

lemma quote_closed_mul_m {m : ℕ} (t u : ClosedSemiterm ℒₒᵣ m) :
    (⌜(‘!!t * !!u’ : ClosedSemiterm ℒₒᵣ m)⌝ : V) = (⌜t⌝ : V) ^* (⌜u⌝ : V) := by
  rw [Semiterm.empty_quote_eq, Semiterm.empty_typed_quote_mul]; rfl

lemma quote_addO_closed {m : ℕ} (t u : ClosedSemiterm ℒₒᵣ m) : (⌜addO t u⌝ : V) = (⌜t⌝ : V) ^+ (⌜u⌝ : V) := by
  rw [addO_eq_add, quote_closed_add_m]
lemma quote_oneO_closed {m : ℕ} : (⌜(oneO : ClosedSemiterm ℒₒᵣ m)⌝ : V) = 𝟏 := by
  rw [oneO_eq_one, quote_closed_one_m]
lemma quote_zeroO_closed {m : ℕ} : (⌜(zeroO : ClosedSemiterm ℒₒᵣ m)⌝ : V) = 𝟎 := by
  rw [zeroO_eq_zero, quote_closed_zero_m]
lemma quote_twoMul_closed {m : ℕ} (t : ClosedSemiterm ℒₒᵣ m) : (⌜twoMul t⌝ : V) = 𝟐 ^* (⌜t⌝ : V) := by
  have e : twoMul t = FirstOrder.Semiterm.func Language.Mul.mul ![addO oneO oneO, t] := rfl
  rw [e, mulO_eq_mul, quote_closed_mul_m, quote_addO_closed, quote_oneO_closed]; rfl
lemma quote_twoMulOne_closed {m : ℕ} (t : ClosedSemiterm ℒₒᵣ m) : (⌜twoMulOne t⌝ : V) = (𝟐 ^* (⌜t⌝ : V)) ^+ 𝟏 := by
  rw [twoMulOne_eq, quote_addO_closed, quote_twoMul_closed, quote_oneO_closed]

/-! ### Term codes of the numeral syntax at `LAct` -/

lemma isFunc_LAct_mulIndex : LAct.IsFunc (2 : V) (mulIndex : V) := isFunc_LAct_of_LOR (by simp)

lemma termSubst_qqMul' {w x y : V} (hx : IsUTerm LAct x) (hy : IsUTerm LAct y) :
    termSubst LAct w (x ^* y) = termSubst LAct w x ^* termSubst LAct w y := by
  unfold qqMul
  rw [termSubst_func isFunc_LAct_mulIndex (by simp [hx, hy]), termSubstVec_cons₂ hx hy]

lemma termSubst_qqTwo' (w : V) : termSubst LAct w (𝟐 : V) = 𝟐 := by
  unfold qqTwo
  rw [termSubst_qqAdd' (isSemiterm_qqOne_LAct 0).isUTerm (isSemiterm_qqOne_LAct 0).isUTerm, termSubst_qqOne']

@[simp] lemma isSemiterm_qqAdd_LAct_iff {n x y : V} :
    IsSemiterm LAct n (x ^+ y) ↔ IsSemiterm LAct n x ∧ IsSemiterm LAct n y := by
  unfold qqAdd
  rw [IsSemiterm.func]
  constructor
  · rintro ⟨_, h⟩
    exact ⟨by simpa using h.nth (i := 0) (by simp), by simpa using h.nth (i := 1) (by simp)⟩
  · rintro ⟨hx, hy⟩
    exact ⟨isFunc_LAct_addIndex, by simp [hx, hy]⟩

@[simp] lemma isSemiterm_qqMul_LAct_iff {n x y : V} :
    IsSemiterm LAct n (x ^* y) ↔ IsSemiterm LAct n x ∧ IsSemiterm LAct n y := by
  unfold qqMul
  rw [IsSemiterm.func]
  constructor
  · rintro ⟨_, h⟩
    exact ⟨by simpa using h.nth (i := 0) (by simp), by simpa using h.nth (i := 1) (by simp)⟩
  · rintro ⟨hx, hy⟩
    exact ⟨isFunc_LAct_mulIndex, by simp [hx, hy]⟩

@[simp] lemma isSemiterm_qqTwo_LAct (n : V) : IsSemiterm LAct n (𝟐 : V) := by
  unfold qqTwo; simp [isSemiterm_qqOne_LAct]

@[simp] lemma isSemiterm_qqOne_LAct' (n : V) : IsSemiterm LAct n (𝟏 : V) := isSemiterm_qqOne_LAct n
@[simp] lemma isSemiterm_qqZero_LAct' (n : V) : IsSemiterm LAct n (𝟎 : V) := isSemiterm_qqZero_LAct n

lemma isSemiterm_bnum_LAct (n a : V) : IsSemiterm LAct n (bnum a) := IsSemiterm.LAct_of_LOR (bnum_semiterm n a)

lemma isSemiterm_bv' {i n : ℕ} (h : i < n) : IsSemiterm LAct (n : V) (bv i) := isSemiterm_bv h

/-! ### Lengths of numeral codes (`Assembly/Uniform` has these at `V : Type` only) -/

lemma termLen_qqMulL {x y : V} (hx : IsUTerm LAct x) (hy : IsUTerm LAct y) :
    termLen LAct (x ^* y) = termLen LAct x + termLen LAct y + 1 := by
  unfold qqMul
  rw [termLen_func isFunc_LAct_mulIndex (by simp [hx, hy]), termLenVec_cons₂ hx hy, listSum_adjoin, listSum_adjoin,
    listSum_nil, add_zero]

lemma termLen_qqTwoL : termLen LAct (𝟐 : V) = 3 := by
  unfold qqTwo
  rw [termLen_qqAdd isFunc_LAct_addIndex (isSemiterm_qqOne_LAct 0).isUTerm (isSemiterm_qqOne_LAct 0).isUTerm,
    termLen_qqOne isFunc_LAct_oneIndex]
  norm_num

lemma termLen_bnum_two_mul {m : V} (hm : 1 ≤ m) : termLen LAct (bnum (2 * m)) = termLen LAct (bnum m) + 4 := by
  rw [bnum_two_mul hm, termLen_qqMulL (isSemiterm_qqTwo_LAct 0).isUTerm (isSemiterm_bnum_LAct 0 m).isUTerm,
    termLen_qqTwoL]
  ring

lemma termLen_bnum_two_mul_add_one {m : V} (hm : 1 ≤ m) :
    termLen LAct (bnum (2 * m + 1)) = termLen LAct (bnum m) + 6 := by
  rw [bnum_two_mul_add_one hm,
    termLen_qqAdd isFunc_LAct_addIndex (isSemiterm_qqMul_LAct_iff.mpr ⟨isSemiterm_qqTwo_LAct 0, isSemiterm_bnum_LAct 0 m⟩).isUTerm
      (isSemiterm_qqOne_LAct 0).isUTerm,
    termLen_qqMulL (isSemiterm_qqTwo_LAct 0).isUTerm (isSemiterm_bnum_LAct 0 m).isUTerm,
    termLen_qqTwoL, termLen_qqOne isFunc_LAct_oneIndex]
  ring

lemma termLen_bnum_zero : termLen LAct (bnum (0 : V)) = 1 := by
  rw [bnum_zero, termLen_qqZero isFunc_LAct_zeroIndex]
lemma termLen_bnum_one : termLen LAct (bnum (1 : V)) = 1 := by
  rw [bnum_one, termLen_qqOne isFunc_LAct_oneIndex]

lemma one_le_termLen_bnum (a : V) : 1 ≤ termLen LAct (bnum a) := by
  rcases zero_one_or_two_le a with rfl | rfl | h2
  · rw [termLen_bnum_zero]
  · rw [termLen_bnum_one]
  · obtain ⟨hm, _, he | ho⟩ := two_le_cases h2
    · rw [he, termLen_bnum_two_mul hm]; exact le_trans (by norm_num) le_add_self
    · rw [ho, termLen_bnum_two_mul_add_one hm]; exact le_trans (by norm_num) le_add_self

end syntaxCodes

/-! ## 2. The rows: the closed binary-arithmetic library

Same convention as `Lib/Lengths.lean` (body `nXB : ArithmeticSemisentence m` in index order,
`nX := ∀¹* nXB`, `models_nX`, `pa_proves_nX`, `lib_nX`), in `NumeralFacts.lean`'s operator syntax;
plus, per row, the PIECES (`nX_as : List V`, `nX_c : V` — the antecedents and the conclusion as
canonical fact codes over `bv i`), the row-shape lemma `quote_nXB : ⌜lMap emb nXB⌝ = impChain nX_as
nX_c`, and the instantiation lemma `inst_nX` at closed witnesses (the witness list is the DSL
variable list read RIGHT-TO-LEFT). -/

section rows

set_option linter.unusedVariables false

/-- Canonical instantiation of the fact codes (`instOuter_subst_listToVec` on `Peq`/`Ple`/`Plt`). -/
lemma instOuter_eqFact (es : List V) (hes : ∀ e ∈ es, IsSemiterm LAct 0 e) {t u : V}
    (ht : IsSemiterm LAct (es.length : V) t) (hu : IsSemiterm LAct (es.length : V) u) :
    instOuter LAct es (eqFact t u) =
      eqFact (termSubst LAct (listToVec es.reverse) t) (termSubst LAct (listToVec es.reverse) u) := by
  unfold eqFact
  rw [instOuter_subst_listToVec [t, u] isSemiformula_Peq rfl es hes (by simp [ht, hu])]
  rfl

lemma instOuter_leFact (es : List V) (hes : ∀ e ∈ es, IsSemiterm LAct 0 e) {t u : V}
    (ht : IsSemiterm LAct (es.length : V) t) (hu : IsSemiterm LAct (es.length : V) u) :
    instOuter LAct es (leFact t u) =
      leFact (termSubst LAct (listToVec es.reverse) t) (termSubst LAct (listToVec es.reverse) u) := by
  unfold leFact
  rw [instOuter_subst_listToVec [t, u] isSemiformula_Ple rfl es hes (by simp [ht, hu])]
  rfl

lemma instOuter_ltFact (es : List V) (hes : ∀ e ∈ es, IsSemiterm LAct 0 e) {t u : V}
    (ht : IsSemiterm LAct (es.length : V) t) (hu : IsSemiterm LAct (es.length : V) u) :
    instOuter LAct es (ltFact t u) =
      ltFact (termSubst LAct (listToVec es.reverse) t) (termSubst LAct (listToVec es.reverse) u) := by
  unfold ltFact
  rw [instOuter_subst_listToVec [t, u] isSemiformula_Plt rfl es hes (by simp [ht, hu])]
  rfl

@[simp] lemma isUTerm_qqAdd_LAct_iff {x y : V} : IsUTerm LAct (x ^+ y) ↔ IsUTerm LAct x ∧ IsUTerm LAct y := by
  unfold qqAdd
  rw [IsUTerm.func_iff]
  constructor
  · rintro ⟨_, h⟩
    exact ⟨by simpa using h.nth (i := 0) (by simp), by simpa using h.nth (i := 1) (by simp)⟩
  · rintro ⟨hx, hy⟩
    exact ⟨isFunc_LAct_addIndex, by simp [hx, hy]⟩

@[simp] lemma isUTerm_qqMul_LAct_iff {x y : V} : IsUTerm LAct (x ^* y) ↔ IsUTerm LAct x ∧ IsUTerm LAct y := by
  unfold qqMul
  rw [IsUTerm.func_iff]
  constructor
  · rintro ⟨_, h⟩
    exact ⟨by simpa using h.nth (i := 0) (by simp), by simpa using h.nth (i := 1) (by simp)⟩
  · rintro ⟨hx, hy⟩
    exact ⟨isFunc_LAct_mulIndex, by simp [hx, hy]⟩

@[simp] lemma isUTerm_qqTwo_LAct : IsUTerm LAct (𝟐 : V) := (isSemiterm_qqTwo_LAct 0).isUTerm
@[simp] lemma isUTerm_qqOne_LAct' : IsUTerm LAct (𝟏 : V) := (isSemiterm_qqOne_LAct 0).isUTerm
@[simp] lemma isUTerm_qqZero_LAct' : IsUTerm LAct (𝟎 : V) := (isSemiterm_qqZero_LAct 0).isUTerm
@[simp] lemma isUTerm_bv (i : ℕ) : IsUTerm LAct (bv i : V) := by simp [bv]

/-- Row 0: `∀ x : V, 0 + x = x`. -/
noncomputable def nZeroAddB : ArithmeticSemisentence 1 := eqO (addO zeroO #0) #0
noncomputable def nZeroAdd : ArithmeticSentence := ∀¹* nZeroAddB

lemma models_nZeroAdd : V↓[ℒₒᵣ] ⊧ nZeroAdd ↔ (∀ x : V, 0 + x = x) := by
  simp [nZeroAdd, nZeroAddB, eqO, addO, leF, ltF, twoMul, twoMulOne, oneO, zeroO, models_iff,
    Matrix.vecForall_iff, one_add_one_eq_two, le_def]

theorem pa_proves_nZeroAdd : 𝗣𝗔 ⊢ nZeroAdd :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_nZeroAdd.mpr (fun x ↦ zero_add x)

theorem lib_nZeroAdd : Lib nZeroAdd := Lib.of_pa pa_proves_nZeroAdd

noncomputable def nZeroAdd_as : List V := []
noncomputable def nZeroAdd_c : V := eqFact (𝟎 ^+ bv 0) (bv 0)

lemma quote_nZeroAddB : (⌜Semiformula.lMap emb nZeroAddB⌝ : V) = impChain LAct nZeroAdd_as nZeroAdd_c := by
  unfold nZeroAddB nZeroAdd_as nZeroAdd_c
  simp only [quote_lMap_emb_imp, quote_eqO_closed, quote_leF_closed, quote_ltF_closed, quote_addO_closed,
    quote_twoMul_closed, quote_twoMulOne_closed, quote_oneO_closed, quote_zeroO_closed, quote_closed_bvar_m,
    impChain_cons, impChain_nil]
  try rfl

lemma inst_nZeroAdd {x : V} (hx : IsSemiterm LAct 0 x) :
    nZeroAdd_as.map (instOuter LAct [x]) = ([] : List V) ∧
    instOuter LAct [x] nZeroAdd_c = eqFact ((𝟎 : V) ^+ x) x := by
  have hes : ∀ e ∈ ([x] : List V), IsSemiterm LAct 0 e := by simp [hx]
  unfold nZeroAdd_as nZeroAdd_c
  simp only [List.map, List.length_cons, List.length_nil]
  simp (disch := (simp [bv]; try norm_num)) only [instOuter_eqFact _ hes, instOuter_leFact _ hes, instOuter_ltFact _ hes]
  simp (disch := (simp [bv]; try norm_num)) only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
    termSubst_qqAdd', termSubst_qqMul', termSubst_bv, termSubst_qqTwo', termSubst_qqOne', termSubst_qqZero',
    List.getD_cons_zero, List.getD_cons_succ]
  all_goals (constructor <;> first | rfl | trivial)

/-- Row 1: `∀ x : V, x + 0 = x`. -/
noncomputable def nAddZeroB : ArithmeticSemisentence 1 := eqO (addO #0 zeroO) #0
noncomputable def nAddZero : ArithmeticSentence := ∀¹* nAddZeroB

lemma models_nAddZero : V↓[ℒₒᵣ] ⊧ nAddZero ↔ (∀ x : V, x + 0 = x) := by
  simp [nAddZero, nAddZeroB, eqO, addO, leF, ltF, twoMul, twoMulOne, oneO, zeroO, models_iff,
    Matrix.vecForall_iff, one_add_one_eq_two, le_def]

theorem pa_proves_nAddZero : 𝗣𝗔 ⊢ nAddZero :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_nAddZero.mpr (fun x ↦ add_zero x)

theorem lib_nAddZero : Lib nAddZero := Lib.of_pa pa_proves_nAddZero

noncomputable def nAddZero_as : List V := []
noncomputable def nAddZero_c : V := eqFact (bv 0 ^+ 𝟎) (bv 0)

lemma quote_nAddZeroB : (⌜Semiformula.lMap emb nAddZeroB⌝ : V) = impChain LAct nAddZero_as nAddZero_c := by
  unfold nAddZeroB nAddZero_as nAddZero_c
  simp only [quote_lMap_emb_imp, quote_eqO_closed, quote_leF_closed, quote_ltF_closed, quote_addO_closed,
    quote_twoMul_closed, quote_twoMulOne_closed, quote_oneO_closed, quote_zeroO_closed, quote_closed_bvar_m,
    impChain_cons, impChain_nil]
  try rfl

lemma inst_nAddZero {x : V} (hx : IsSemiterm LAct 0 x) :
    nAddZero_as.map (instOuter LAct [x]) = ([] : List V) ∧
    instOuter LAct [x] nAddZero_c = eqFact (x ^+ (𝟎 : V)) x := by
  have hes : ∀ e ∈ ([x] : List V), IsSemiterm LAct 0 e := by simp [hx]
  unfold nAddZero_as nAddZero_c
  simp only [List.map, List.length_cons, List.length_nil]
  simp (disch := (simp [bv]; try norm_num)) only [instOuter_eqFact _ hes, instOuter_leFact _ hes, instOuter_ltFact _ hes]
  simp (disch := (simp [bv]; try norm_num)) only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
    termSubst_qqAdd', termSubst_qqMul', termSubst_bv, termSubst_qqTwo', termSubst_qqOne', termSubst_qqZero',
    List.getD_cons_zero, List.getD_cons_succ]
  all_goals (constructor <;> first | rfl | trivial)

/-- Row 2: `(1 : V) + 1 = 2 * 1`. -/
noncomputable def nOneOneB : ArithmeticSemisentence 0 := eqO (addO oneO oneO) (twoMul oneO)
noncomputable def nOneOne : ArithmeticSentence := ∀¹* nOneOneB

lemma models_nOneOne : V↓[ℒₒᵣ] ⊧ nOneOne ↔ ((1 : V) + 1 = 2 * 1) := by
  simp [nOneOne, nOneOneB, eqO, addO, leF, ltF, twoMul, twoMulOne, oneO, zeroO, models_iff,
    Matrix.vecForall_iff, one_add_one_eq_two, le_def]

theorem pa_proves_nOneOne : 𝗣𝗔 ⊢ nOneOne :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_nOneOne.mpr (by rw [mul_one, one_add_one_eq_two])

theorem lib_nOneOne : Lib nOneOne := Lib.of_pa pa_proves_nOneOne

noncomputable def nOneOne_as : List V := []
noncomputable def nOneOne_c : V := eqFact (𝟏 ^+ 𝟏) (𝟐 ^* 𝟏)

lemma quote_nOneOneB : (⌜Semiformula.lMap emb nOneOneB⌝ : V) = impChain LAct nOneOne_as nOneOne_c := by
  unfold nOneOneB nOneOne_as nOneOne_c
  simp only [quote_lMap_emb_imp, quote_eqO_closed, quote_leF_closed, quote_ltF_closed, quote_addO_closed,
    quote_twoMul_closed, quote_twoMulOne_closed, quote_oneO_closed, quote_zeroO_closed, quote_closed_bvar_m,
    impChain_cons, impChain_nil]
  try rfl

lemma inst_nOneOne :
    nOneOne_as.map (instOuter LAct []) = ([] : List V) ∧ instOuter LAct [] nOneOne_c = eqFact ((𝟏 : V) ^+ (𝟏 : V)) ((𝟐 : V) ^* (𝟏 : V)) := ⟨rfl, rfl⟩

/-- Row 3: `(0 : V) + 1 = 1`. -/
noncomputable def nZeroOneB : ArithmeticSemisentence 0 := eqO (addO zeroO oneO) oneO
noncomputable def nZeroOne : ArithmeticSentence := ∀¹* nZeroOneB

lemma models_nZeroOne : V↓[ℒₒᵣ] ⊧ nZeroOne ↔ ((0 : V) + 1 = 1) := by
  simp [nZeroOne, nZeroOneB, eqO, addO, leF, ltF, twoMul, twoMulOne, oneO, zeroO, models_iff,
    Matrix.vecForall_iff, one_add_one_eq_two, le_def]

theorem pa_proves_nZeroOne : 𝗣𝗔 ⊢ nZeroOne :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_nZeroOne.mpr (zero_add 1)

theorem lib_nZeroOne : Lib nZeroOne := Lib.of_pa pa_proves_nZeroOne

noncomputable def nZeroOne_as : List V := []
noncomputable def nZeroOne_c : V := eqFact (𝟎 ^+ 𝟏) 𝟏

lemma quote_nZeroOneB : (⌜Semiformula.lMap emb nZeroOneB⌝ : V) = impChain LAct nZeroOne_as nZeroOne_c := by
  unfold nZeroOneB nZeroOne_as nZeroOne_c
  simp only [quote_lMap_emb_imp, quote_eqO_closed, quote_leF_closed, quote_ltF_closed, quote_addO_closed,
    quote_twoMul_closed, quote_twoMulOne_closed, quote_oneO_closed, quote_zeroO_closed, quote_closed_bvar_m,
    impChain_cons, impChain_nil]
  try rfl

lemma inst_nZeroOne :
    nZeroOne_as.map (instOuter LAct []) = ([] : List V) ∧ instOuter LAct [] nZeroOne_c = eqFact ((𝟎 : V) ^+ (𝟏 : V)) (𝟏 : V) := ⟨rfl, rfl⟩

/-- Row 4: `∀ x w : V, x + 1 = w → 1 + x = w`. -/
noncomputable def nOneAddB : ArithmeticSemisentence 2 := eqO (addO #0 oneO) #1 🡒 eqO (addO oneO #0) #1
noncomputable def nOneAdd : ArithmeticSentence := ∀¹* nOneAddB

lemma models_nOneAdd : V↓[ℒₒᵣ] ⊧ nOneAdd ↔ (∀ x w : V, x + 1 = w → 1 + x = w) := by
  simp [nOneAdd, nOneAddB, eqO, addO, leF, ltF, twoMul, twoMulOne, oneO, zeroO, models_iff,
    Matrix.vecForall_iff, one_add_one_eq_two, le_def]

theorem pa_proves_nOneAdd : 𝗣𝗔 ⊢ nOneAdd :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_nOneAdd.mpr (fun x w h ↦ by subst h; exact add_comm 1 x)

theorem lib_nOneAdd : Lib nOneAdd := Lib.of_pa pa_proves_nOneAdd

noncomputable def nOneAdd_as : List V := [eqFact (bv 0 ^+ 𝟏) (bv 1)]
noncomputable def nOneAdd_c : V := eqFact (𝟏 ^+ bv 0) (bv 1)

lemma quote_nOneAddB : (⌜Semiformula.lMap emb nOneAddB⌝ : V) = impChain LAct nOneAdd_as nOneAdd_c := by
  unfold nOneAddB nOneAdd_as nOneAdd_c
  simp only [quote_lMap_emb_imp, quote_eqO_closed, quote_leF_closed, quote_ltF_closed, quote_addO_closed,
    quote_twoMul_closed, quote_twoMulOne_closed, quote_oneO_closed, quote_zeroO_closed, quote_closed_bvar_m,
    impChain_cons, impChain_nil]
  try rfl

lemma inst_nOneAdd {x w : V} (hx : IsSemiterm LAct 0 x) (hw : IsSemiterm LAct 0 w) :
    nOneAdd_as.map (instOuter LAct [w, x]) = ([eqFact (x ^+ (𝟏 : V)) w] : List V) ∧
    instOuter LAct [w, x] nOneAdd_c = eqFact ((𝟏 : V) ^+ x) w := by
  have hes : ∀ e ∈ ([w, x] : List V), IsSemiterm LAct 0 e := by simp [hx, hw]
  unfold nOneAdd_as nOneAdd_c
  simp only [List.map, List.length_cons, List.length_nil]
  simp (disch := (simp [bv]; try norm_num)) only [instOuter_eqFact _ hes, instOuter_leFact _ hes, instOuter_ltFact _ hes]
  simp (disch := (simp [bv]; try norm_num)) only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
    termSubst_qqAdd', termSubst_qqMul', termSubst_bv, termSubst_qqTwo', termSubst_qqOne', termSubst_qqZero',
    List.getD_cons_zero, List.getD_cons_succ]
  all_goals (constructor <;> first | rfl | trivial)

/-- Row 5: `∀ x : V, x = x`. -/
noncomputable def nEqReflB : ArithmeticSemisentence 1 := eqO #0 #0
noncomputable def nEqRefl : ArithmeticSentence := ∀¹* nEqReflB

lemma models_nEqRefl : V↓[ℒₒᵣ] ⊧ nEqRefl ↔ (∀ x : V, x = x) := by
  simp [nEqRefl, nEqReflB, eqO, addO, leF, ltF, twoMul, twoMulOne, oneO, zeroO, models_iff,
    Matrix.vecForall_iff, one_add_one_eq_two, le_def]

theorem pa_proves_nEqRefl : 𝗣𝗔 ⊢ nEqRefl :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_nEqRefl.mpr (fun _ ↦ rfl)

theorem lib_nEqRefl : Lib nEqRefl := Lib.of_pa pa_proves_nEqRefl

noncomputable def nEqRefl_as : List V := []
noncomputable def nEqRefl_c : V := eqFact (bv 0) (bv 0)

lemma quote_nEqReflB : (⌜Semiformula.lMap emb nEqReflB⌝ : V) = impChain LAct nEqRefl_as nEqRefl_c := by
  unfold nEqReflB nEqRefl_as nEqRefl_c
  simp only [quote_lMap_emb_imp, quote_eqO_closed, quote_leF_closed, quote_ltF_closed, quote_addO_closed,
    quote_twoMul_closed, quote_twoMulOne_closed, quote_oneO_closed, quote_zeroO_closed, quote_closed_bvar_m,
    impChain_cons, impChain_nil]
  try rfl

lemma inst_nEqRefl {x : V} (hx : IsSemiterm LAct 0 x) :
    nEqRefl_as.map (instOuter LAct [x]) = ([] : List V) ∧
    instOuter LAct [x] nEqRefl_c = eqFact x x := by
  have hes : ∀ e ∈ ([x] : List V), IsSemiterm LAct 0 e := by simp [hx]
  unfold nEqRefl_as nEqRefl_c
  simp only [List.map, List.length_cons, List.length_nil]
  simp (disch := (simp [bv]; try norm_num)) only [instOuter_eqFact _ hes, instOuter_leFact _ hes, instOuter_ltFact _ hes]
  simp (disch := (simp [bv]; try norm_num)) only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
    termSubst_qqAdd', termSubst_qqMul', termSubst_bv, termSubst_qqTwo', termSubst_qqOne', termSubst_qqZero',
    List.getD_cons_zero, List.getD_cons_succ]
  all_goals (constructor <;> first | rfl | trivial)

/-- Row 6: `∀ x w : V, x + 1 = w → 2 * x + 1 + 1 = 2 * w`. -/
noncomputable def nCarryB : ArithmeticSemisentence 2 := eqO (addO #0 oneO) #1 🡒 eqO (addO (twoMulOne #0) oneO) (twoMul #1)
noncomputable def nCarry : ArithmeticSentence := ∀¹* nCarryB

lemma models_nCarry : V↓[ℒₒᵣ] ⊧ nCarry ↔ (∀ x w : V, x + 1 = w → 2 * x + 1 + 1 = 2 * w) := by
  simp [nCarry, nCarryB, eqO, addO, leF, ltF, twoMul, twoMulOne, oneO, zeroO, models_iff,
    Matrix.vecForall_iff, one_add_one_eq_two, le_def]

theorem pa_proves_nCarry : 𝗣𝗔 ⊢ nCarry :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_nCarry.mpr (fun x w h ↦ by subst h; ring)

theorem lib_nCarry : Lib nCarry := Lib.of_pa pa_proves_nCarry

noncomputable def nCarry_as : List V := [eqFact (bv 0 ^+ 𝟏) (bv 1)]
noncomputable def nCarry_c : V := eqFact (((𝟐 ^* bv 0) ^+ 𝟏) ^+ 𝟏) (𝟐 ^* bv 1)

lemma quote_nCarryB : (⌜Semiformula.lMap emb nCarryB⌝ : V) = impChain LAct nCarry_as nCarry_c := by
  unfold nCarryB nCarry_as nCarry_c
  simp only [quote_lMap_emb_imp, quote_eqO_closed, quote_leF_closed, quote_ltF_closed, quote_addO_closed,
    quote_twoMul_closed, quote_twoMulOne_closed, quote_oneO_closed, quote_zeroO_closed, quote_closed_bvar_m,
    impChain_cons, impChain_nil]
  try rfl

lemma inst_nCarry {x w : V} (hx : IsSemiterm LAct 0 x) (hw : IsSemiterm LAct 0 w) :
    nCarry_as.map (instOuter LAct [w, x]) = ([eqFact (x ^+ (𝟏 : V)) w] : List V) ∧
    instOuter LAct [w, x] nCarry_c = eqFact ((((𝟐 : V) ^* x) ^+ (𝟏 : V)) ^+ (𝟏 : V)) ((𝟐 : V) ^* w) := by
  have hes : ∀ e ∈ ([w, x] : List V), IsSemiterm LAct 0 e := by simp [hx, hw]
  unfold nCarry_as nCarry_c
  simp only [List.map, List.length_cons, List.length_nil]
  simp (disch := (simp [bv]; try norm_num)) only [instOuter_eqFact _ hes, instOuter_leFact _ hes, instOuter_ltFact _ hes]
  simp (disch := (simp [bv]; try norm_num)) only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
    termSubst_qqAdd', termSubst_qqMul', termSubst_bv, termSubst_qqTwo', termSubst_qqOne', termSubst_qqZero',
    List.getD_cons_zero, List.getD_cons_succ]
  all_goals (constructor <;> first | rfl | trivial)

/-- Row 7: `∀ x y z : V, x + y = z → 2 * x + 2 * y = 2 * z`. -/
noncomputable def nBit00B : ArithmeticSemisentence 3 := eqO (addO #0 #1) #2 🡒 eqO (addO (twoMul #0) (twoMul #1)) (twoMul #2)
noncomputable def nBit00 : ArithmeticSentence := ∀¹* nBit00B

lemma models_nBit00 : V↓[ℒₒᵣ] ⊧ nBit00 ↔ (∀ x y z : V, x + y = z → 2 * x + 2 * y = 2 * z) := by
  simp [nBit00, nBit00B, eqO, addO, leF, ltF, twoMul, twoMulOne, oneO, zeroO, models_iff,
    Matrix.vecForall_iff, one_add_one_eq_two, le_def]

theorem pa_proves_nBit00 : 𝗣𝗔 ⊢ nBit00 :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_nBit00.mpr (fun x y z h ↦ by subst h; ring)

theorem lib_nBit00 : Lib nBit00 := Lib.of_pa pa_proves_nBit00

noncomputable def nBit00_as : List V := [eqFact (bv 0 ^+ bv 1) (bv 2)]
noncomputable def nBit00_c : V := eqFact ((𝟐 ^* bv 0) ^+ (𝟐 ^* bv 1)) (𝟐 ^* bv 2)

lemma quote_nBit00B : (⌜Semiformula.lMap emb nBit00B⌝ : V) = impChain LAct nBit00_as nBit00_c := by
  unfold nBit00B nBit00_as nBit00_c
  simp only [quote_lMap_emb_imp, quote_eqO_closed, quote_leF_closed, quote_ltF_closed, quote_addO_closed,
    quote_twoMul_closed, quote_twoMulOne_closed, quote_oneO_closed, quote_zeroO_closed, quote_closed_bvar_m,
    impChain_cons, impChain_nil]
  try rfl

lemma inst_nBit00 {x y z : V} (hx : IsSemiterm LAct 0 x) (hy : IsSemiterm LAct 0 y) (hz : IsSemiterm LAct 0 z) :
    nBit00_as.map (instOuter LAct [z, y, x]) = ([eqFact (x ^+ y) z] : List V) ∧
    instOuter LAct [z, y, x] nBit00_c = eqFact (((𝟐 : V) ^* x) ^+ ((𝟐 : V) ^* y)) ((𝟐 : V) ^* z) := by
  have hes : ∀ e ∈ ([z, y, x] : List V), IsSemiterm LAct 0 e := by simp [hx, hy, hz]
  unfold nBit00_as nBit00_c
  simp only [List.map, List.length_cons, List.length_nil]
  simp (disch := (simp [bv]; try norm_num)) only [instOuter_eqFact _ hes, instOuter_leFact _ hes, instOuter_ltFact _ hes]
  simp (disch := (simp [bv]; try norm_num)) only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
    termSubst_qqAdd', termSubst_qqMul', termSubst_bv, termSubst_qqTwo', termSubst_qqOne', termSubst_qqZero',
    List.getD_cons_zero, List.getD_cons_succ]
  all_goals (constructor <;> first | rfl | trivial)

/-- Row 8: `∀ x y z : V, x + y = z → 2 * x + (2 * y + 1) = 2 * z + 1`. -/
noncomputable def nBit01B : ArithmeticSemisentence 3 := eqO (addO #0 #1) #2 🡒 eqO (addO (twoMul #0) (twoMulOne #1)) (twoMulOne #2)
noncomputable def nBit01 : ArithmeticSentence := ∀¹* nBit01B

lemma models_nBit01 : V↓[ℒₒᵣ] ⊧ nBit01 ↔ (∀ x y z : V, x + y = z → 2 * x + (2 * y + 1) = 2 * z + 1) := by
  simp [nBit01, nBit01B, eqO, addO, leF, ltF, twoMul, twoMulOne, oneO, zeroO, models_iff,
    Matrix.vecForall_iff, one_add_one_eq_two, le_def]

theorem pa_proves_nBit01 : 𝗣𝗔 ⊢ nBit01 :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_nBit01.mpr (fun x y z h ↦ by subst h; ring)

theorem lib_nBit01 : Lib nBit01 := Lib.of_pa pa_proves_nBit01

noncomputable def nBit01_as : List V := [eqFact (bv 0 ^+ bv 1) (bv 2)]
noncomputable def nBit01_c : V := eqFact ((𝟐 ^* bv 0) ^+ ((𝟐 ^* bv 1) ^+ 𝟏)) ((𝟐 ^* bv 2) ^+ 𝟏)

lemma quote_nBit01B : (⌜Semiformula.lMap emb nBit01B⌝ : V) = impChain LAct nBit01_as nBit01_c := by
  unfold nBit01B nBit01_as nBit01_c
  simp only [quote_lMap_emb_imp, quote_eqO_closed, quote_leF_closed, quote_ltF_closed, quote_addO_closed,
    quote_twoMul_closed, quote_twoMulOne_closed, quote_oneO_closed, quote_zeroO_closed, quote_closed_bvar_m,
    impChain_cons, impChain_nil]
  try rfl

lemma inst_nBit01 {x y z : V} (hx : IsSemiterm LAct 0 x) (hy : IsSemiterm LAct 0 y) (hz : IsSemiterm LAct 0 z) :
    nBit01_as.map (instOuter LAct [z, y, x]) = ([eqFact (x ^+ y) z] : List V) ∧
    instOuter LAct [z, y, x] nBit01_c = eqFact (((𝟐 : V) ^* x) ^+ (((𝟐 : V) ^* y) ^+ (𝟏 : V))) (((𝟐 : V) ^* z) ^+ (𝟏 : V)) := by
  have hes : ∀ e ∈ ([z, y, x] : List V), IsSemiterm LAct 0 e := by simp [hx, hy, hz]
  unfold nBit01_as nBit01_c
  simp only [List.map, List.length_cons, List.length_nil]
  simp (disch := (simp [bv]; try norm_num)) only [instOuter_eqFact _ hes, instOuter_leFact _ hes, instOuter_ltFact _ hes]
  simp (disch := (simp [bv]; try norm_num)) only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
    termSubst_qqAdd', termSubst_qqMul', termSubst_bv, termSubst_qqTwo', termSubst_qqOne', termSubst_qqZero',
    List.getD_cons_zero, List.getD_cons_succ]
  all_goals (constructor <;> first | rfl | trivial)

/-- Row 9: `∀ x y z : V, x + y = z → 2 * x + 1 + 2 * y = 2 * z + 1`. -/
noncomputable def nBit10B : ArithmeticSemisentence 3 := eqO (addO #0 #1) #2 🡒 eqO (addO (twoMulOne #0) (twoMul #1)) (twoMulOne #2)
noncomputable def nBit10 : ArithmeticSentence := ∀¹* nBit10B

lemma models_nBit10 : V↓[ℒₒᵣ] ⊧ nBit10 ↔ (∀ x y z : V, x + y = z → 2 * x + 1 + 2 * y = 2 * z + 1) := by
  simp [nBit10, nBit10B, eqO, addO, leF, ltF, twoMul, twoMulOne, oneO, zeroO, models_iff,
    Matrix.vecForall_iff, one_add_one_eq_two, le_def]

theorem pa_proves_nBit10 : 𝗣𝗔 ⊢ nBit10 :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_nBit10.mpr (fun x y z h ↦ by subst h; ring)

theorem lib_nBit10 : Lib nBit10 := Lib.of_pa pa_proves_nBit10

noncomputable def nBit10_as : List V := [eqFact (bv 0 ^+ bv 1) (bv 2)]
noncomputable def nBit10_c : V := eqFact (((𝟐 ^* bv 0) ^+ 𝟏) ^+ (𝟐 ^* bv 1)) ((𝟐 ^* bv 2) ^+ 𝟏)

lemma quote_nBit10B : (⌜Semiformula.lMap emb nBit10B⌝ : V) = impChain LAct nBit10_as nBit10_c := by
  unfold nBit10B nBit10_as nBit10_c
  simp only [quote_lMap_emb_imp, quote_eqO_closed, quote_leF_closed, quote_ltF_closed, quote_addO_closed,
    quote_twoMul_closed, quote_twoMulOne_closed, quote_oneO_closed, quote_zeroO_closed, quote_closed_bvar_m,
    impChain_cons, impChain_nil]
  try rfl

lemma inst_nBit10 {x y z : V} (hx : IsSemiterm LAct 0 x) (hy : IsSemiterm LAct 0 y) (hz : IsSemiterm LAct 0 z) :
    nBit10_as.map (instOuter LAct [z, y, x]) = ([eqFact (x ^+ y) z] : List V) ∧
    instOuter LAct [z, y, x] nBit10_c = eqFact ((((𝟐 : V) ^* x) ^+ (𝟏 : V)) ^+ ((𝟐 : V) ^* y)) (((𝟐 : V) ^* z) ^+ (𝟏 : V)) := by
  have hes : ∀ e ∈ ([z, y, x] : List V), IsSemiterm LAct 0 e := by simp [hx, hy, hz]
  unfold nBit10_as nBit10_c
  simp only [List.map, List.length_cons, List.length_nil]
  simp (disch := (simp [bv]; try norm_num)) only [instOuter_eqFact _ hes, instOuter_leFact _ hes, instOuter_ltFact _ hes]
  simp (disch := (simp [bv]; try norm_num)) only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
    termSubst_qqAdd', termSubst_qqMul', termSubst_bv, termSubst_qqTwo', termSubst_qqOne', termSubst_qqZero',
    List.getD_cons_zero, List.getD_cons_succ]
  all_goals (constructor <;> first | rfl | trivial)

/-- Row 10: `∀ x y z w : V, x + y = z → z + 1 = w → 2 * x + 1 + (2 * y + 1) = 2 * w`. -/
noncomputable def nBit11B : ArithmeticSemisentence 4 := eqO (addO #0 #1) #2 🡒 eqO (addO #2 oneO) #3 🡒 eqO (addO (twoMulOne #0) (twoMulOne #1)) (twoMul #3)
noncomputable def nBit11 : ArithmeticSentence := ∀¹* nBit11B

lemma models_nBit11 : V↓[ℒₒᵣ] ⊧ nBit11 ↔ (∀ x y z w : V, x + y = z → z + 1 = w → 2 * x + 1 + (2 * y + 1) = 2 * w) := by
  simp [nBit11, nBit11B, eqO, addO, leF, ltF, twoMul, twoMulOne, oneO, zeroO, models_iff,
    Matrix.vecForall_iff, one_add_one_eq_two, le_def]

theorem pa_proves_nBit11 : 𝗣𝗔 ⊢ nBit11 :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_nBit11.mpr (fun x y z w h h' ↦ by subst h; subst h'; ring)

theorem lib_nBit11 : Lib nBit11 := Lib.of_pa pa_proves_nBit11

noncomputable def nBit11_as : List V := [eqFact (bv 0 ^+ bv 1) (bv 2), eqFact (bv 2 ^+ 𝟏) (bv 3)]
noncomputable def nBit11_c : V := eqFact (((𝟐 ^* bv 0) ^+ 𝟏) ^+ ((𝟐 ^* bv 1) ^+ 𝟏)) (𝟐 ^* bv 3)

lemma quote_nBit11B : (⌜Semiformula.lMap emb nBit11B⌝ : V) = impChain LAct nBit11_as nBit11_c := by
  unfold nBit11B nBit11_as nBit11_c
  simp only [quote_lMap_emb_imp, quote_eqO_closed, quote_leF_closed, quote_ltF_closed, quote_addO_closed,
    quote_twoMul_closed, quote_twoMulOne_closed, quote_oneO_closed, quote_zeroO_closed, quote_closed_bvar_m,
    impChain_cons, impChain_nil]
  try rfl

lemma inst_nBit11 {x y z w : V} (hx : IsSemiterm LAct 0 x) (hy : IsSemiterm LAct 0 y) (hz : IsSemiterm LAct 0 z) (hw : IsSemiterm LAct 0 w) :
    nBit11_as.map (instOuter LAct [w, z, y, x]) = ([eqFact (x ^+ y) z, eqFact (z ^+ (𝟏 : V)) w] : List V) ∧
    instOuter LAct [w, z, y, x] nBit11_c = eqFact ((((𝟐 : V) ^* x) ^+ (𝟏 : V)) ^+ (((𝟐 : V) ^* y) ^+ (𝟏 : V))) ((𝟐 : V) ^* w) := by
  have hes : ∀ e ∈ ([w, z, y, x] : List V), IsSemiterm LAct 0 e := by simp [hx, hy, hz, hw]
  unfold nBit11_as nBit11_c
  simp only [List.map, List.length_cons, List.length_nil]
  simp (disch := (simp [bv]; try norm_num)) only [instOuter_eqFact _ hes, instOuter_leFact _ hes, instOuter_ltFact _ hes]
  simp (disch := (simp [bv]; try norm_num)) only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
    termSubst_qqAdd', termSubst_qqMul', termSubst_bv, termSubst_qqTwo', termSubst_qqOne', termSubst_qqZero',
    List.getD_cons_zero, List.getD_cons_succ]
  all_goals (constructor <;> first | rfl | trivial)

/-- Row 11: `∀ x y z : V, x + y = z → x ≤ z`. -/
noncomputable def nLeOfAddB : ArithmeticSemisentence 3 := eqO (addO #0 #1) #2 🡒 leF #0 #2
noncomputable def nLeOfAdd : ArithmeticSentence := ∀¹* nLeOfAddB

lemma models_nLeOfAdd : V↓[ℒₒᵣ] ⊧ nLeOfAdd ↔ (∀ x y z : V, x + y = z → x ≤ z) := by
  simp [nLeOfAdd, nLeOfAddB, eqO, addO, leF, ltF, twoMul, twoMulOne, oneO, zeroO, models_iff,
    Matrix.vecForall_iff, one_add_one_eq_two, le_def]

theorem pa_proves_nLeOfAdd : 𝗣𝗔 ⊢ nLeOfAdd :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_nLeOfAdd.mpr (fun x y z h ↦ by subst h; exact le_self_add)

theorem lib_nLeOfAdd : Lib nLeOfAdd := Lib.of_pa pa_proves_nLeOfAdd

noncomputable def nLeOfAdd_as : List V := [eqFact (bv 0 ^+ bv 1) (bv 2)]
noncomputable def nLeOfAdd_c : V := leFact (bv 0) (bv 2)

lemma quote_nLeOfAddB : (⌜Semiformula.lMap emb nLeOfAddB⌝ : V) = impChain LAct nLeOfAdd_as nLeOfAdd_c := by
  unfold nLeOfAddB nLeOfAdd_as nLeOfAdd_c
  simp only [quote_lMap_emb_imp, quote_eqO_closed, quote_leF_closed, quote_ltF_closed, quote_addO_closed,
    quote_twoMul_closed, quote_twoMulOne_closed, quote_oneO_closed, quote_zeroO_closed, quote_closed_bvar_m,
    impChain_cons, impChain_nil]
  try rfl

lemma inst_nLeOfAdd {x y z : V} (hx : IsSemiterm LAct 0 x) (hy : IsSemiterm LAct 0 y) (hz : IsSemiterm LAct 0 z) :
    nLeOfAdd_as.map (instOuter LAct [z, y, x]) = ([eqFact (x ^+ y) z] : List V) ∧
    instOuter LAct [z, y, x] nLeOfAdd_c = leFact x z := by
  have hes : ∀ e ∈ ([z, y, x] : List V), IsSemiterm LAct 0 e := by simp [hx, hy, hz]
  unfold nLeOfAdd_as nLeOfAdd_c
  simp only [List.map, List.length_cons, List.length_nil]
  simp (disch := (simp [bv]; try norm_num)) only [instOuter_eqFact _ hes, instOuter_leFact _ hes, instOuter_ltFact _ hes]
  simp (disch := (simp [bv]; try norm_num)) only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
    termSubst_qqAdd', termSubst_qqMul', termSubst_bv, termSubst_qqTwo', termSubst_qqOne', termSubst_qqZero',
    List.getD_cons_zero, List.getD_cons_succ]
  all_goals (constructor <;> first | rfl | trivial)

/-- Row 12: `∀ x w z : V, x + 1 = w → w ≤ z → x < z`. -/
noncomputable def nLtOfSuccLeB : ArithmeticSemisentence 3 := eqO (addO #0 oneO) #1 🡒 leF #1 #2 🡒 ltF #0 #2
noncomputable def nLtOfSuccLe : ArithmeticSentence := ∀¹* nLtOfSuccLeB

lemma models_nLtOfSuccLe : V↓[ℒₒᵣ] ⊧ nLtOfSuccLe ↔ (∀ x w z : V, x + 1 = w → w ≤ z → x < z) := by
  simp [nLtOfSuccLe, nLtOfSuccLeB, eqO, addO, leF, ltF, twoMul, twoMulOne, oneO, zeroO, models_iff,
    Matrix.vecForall_iff, one_add_one_eq_two, le_def]

theorem pa_proves_nLtOfSuccLe : 𝗣𝗔 ⊢ nLtOfSuccLe :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_nLtOfSuccLe.mpr (fun x w z h h' ↦ by subst h; exact lt_of_lt_of_le (lt_add_one x) h')

theorem lib_nLtOfSuccLe : Lib nLtOfSuccLe := Lib.of_pa pa_proves_nLtOfSuccLe

noncomputable def nLtOfSuccLe_as : List V := [eqFact (bv 0 ^+ 𝟏) (bv 1), leFact (bv 1) (bv 2)]
noncomputable def nLtOfSuccLe_c : V := ltFact (bv 0) (bv 2)

lemma quote_nLtOfSuccLeB : (⌜Semiformula.lMap emb nLtOfSuccLeB⌝ : V) = impChain LAct nLtOfSuccLe_as nLtOfSuccLe_c := by
  unfold nLtOfSuccLeB nLtOfSuccLe_as nLtOfSuccLe_c
  simp only [quote_lMap_emb_imp, quote_eqO_closed, quote_leF_closed, quote_ltF_closed, quote_addO_closed,
    quote_twoMul_closed, quote_twoMulOne_closed, quote_oneO_closed, quote_zeroO_closed, quote_closed_bvar_m,
    impChain_cons, impChain_nil]
  try rfl

lemma inst_nLtOfSuccLe {x w z : V} (hx : IsSemiterm LAct 0 x) (hw : IsSemiterm LAct 0 w) (hz : IsSemiterm LAct 0 z) :
    nLtOfSuccLe_as.map (instOuter LAct [z, w, x]) = ([eqFact (x ^+ (𝟏 : V)) w, leFact w z] : List V) ∧
    instOuter LAct [z, w, x] nLtOfSuccLe_c = ltFact x z := by
  have hes : ∀ e ∈ ([z, w, x] : List V), IsSemiterm LAct 0 e := by simp [hx, hw, hz]
  unfold nLtOfSuccLe_as nLtOfSuccLe_c
  simp only [List.map, List.length_cons, List.length_nil]
  simp (disch := (simp [bv]; try norm_num)) only [instOuter_eqFact _ hes, instOuter_leFact _ hes, instOuter_ltFact _ hes]
  simp (disch := (simp [bv]; try norm_num)) only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
    termSubst_qqAdd', termSubst_qqMul', termSubst_bv, termSubst_qqTwo', termSubst_qqOne', termSubst_qqZero',
    List.getD_cons_zero, List.getD_cons_succ]
  all_goals (constructor <;> first | rfl | trivial)

/-- Row 13: `∀ a b c s t u n : V, a + b = s → s + c = t → t + 1 = u → u ≤ n → a + b + c + 1 ≤ n`. -/
noncomputable def nSum3SuccLeB : ArithmeticSemisentence 7 := eqO (addO #0 #1) #3 🡒 eqO (addO #3 #2) #4 🡒 eqO (addO #4 oneO) #5 🡒 leF #5 #6 🡒 leF (addO (addO (addO #0 #1) #2) oneO) #6
noncomputable def nSum3SuccLe : ArithmeticSentence := ∀¹* nSum3SuccLeB

lemma models_nSum3SuccLe : V↓[ℒₒᵣ] ⊧ nSum3SuccLe ↔ (∀ a b c s t u n : V, a + b = s → s + c = t → t + 1 = u → u ≤ n → a + b + c + 1 ≤ n) := by
  simp [nSum3SuccLe, nSum3SuccLeB, eqO, addO, leF, ltF, twoMul, twoMulOne, oneO, zeroO, models_iff,
    Matrix.vecForall_iff, one_add_one_eq_two, le_def]

theorem pa_proves_nSum3SuccLe : 𝗣𝗔 ⊢ nSum3SuccLe :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_nSum3SuccLe.mpr (fun a b c s t u n h1 h2 h3 h4 ↦ by subst h1; subst h2; subst h3; exact h4)

theorem lib_nSum3SuccLe : Lib nSum3SuccLe := Lib.of_pa pa_proves_nSum3SuccLe

noncomputable def nSum3SuccLe_as : List V := [eqFact (bv 0 ^+ bv 1) (bv 3), eqFact (bv 3 ^+ bv 2) (bv 4), eqFact (bv 4 ^+ 𝟏) (bv 5), leFact (bv 5) (bv 6)]
noncomputable def nSum3SuccLe_c : V := leFact (((bv 0 ^+ bv 1) ^+ bv 2) ^+ 𝟏) (bv 6)

lemma quote_nSum3SuccLeB : (⌜Semiformula.lMap emb nSum3SuccLeB⌝ : V) = impChain LAct nSum3SuccLe_as nSum3SuccLe_c := by
  unfold nSum3SuccLeB nSum3SuccLe_as nSum3SuccLe_c
  simp only [quote_lMap_emb_imp, quote_eqO_closed, quote_leF_closed, quote_ltF_closed, quote_addO_closed,
    quote_twoMul_closed, quote_twoMulOne_closed, quote_oneO_closed, quote_zeroO_closed, quote_closed_bvar_m,
    impChain_cons, impChain_nil]
  try rfl

lemma inst_nSum3SuccLe {a b c s t u n : V} (ha : IsSemiterm LAct 0 a) (hb : IsSemiterm LAct 0 b) (hc : IsSemiterm LAct 0 c) (hs : IsSemiterm LAct 0 s) (ht : IsSemiterm LAct 0 t) (hu : IsSemiterm LAct 0 u) (hn : IsSemiterm LAct 0 n) :
    nSum3SuccLe_as.map (instOuter LAct [n, u, t, s, c, b, a]) = ([eqFact (a ^+ b) s, eqFact (s ^+ c) t, eqFact (t ^+ (𝟏 : V)) u, leFact u n] : List V) ∧
    instOuter LAct [n, u, t, s, c, b, a] nSum3SuccLe_c = leFact (((a ^+ b) ^+ c) ^+ (𝟏 : V)) n := by
  have hes : ∀ e ∈ ([n, u, t, s, c, b, a] : List V), IsSemiterm LAct 0 e := by simp [ha, hb, hc, hs, ht, hu, hn]
  unfold nSum3SuccLe_as nSum3SuccLe_c
  simp only [List.map, List.length_cons, List.length_nil]
  simp (disch := (simp [bv]; try norm_num)) only [instOuter_eqFact _ hes, instOuter_leFact _ hes, instOuter_ltFact _ hes]
  simp (disch := (simp [bv]; try norm_num)) only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
    termSubst_qqAdd', termSubst_qqMul', termSubst_bv, termSubst_qqTwo', termSubst_qqOne', termSubst_qqZero',
    List.getD_cons_zero, List.getD_cons_succ]
  all_goals (constructor <;> first | rfl | trivial)

/-- Row 14: `∀ a b s u n : V, a + b = s → s + 1 = u → u ≤ n → a + b + 1 ≤ n`. -/
noncomputable def nSum2SuccLeB : ArithmeticSemisentence 5 := eqO (addO #0 #1) #2 🡒 eqO (addO #2 oneO) #3 🡒 leF #3 #4 🡒 leF (addO (addO #0 #1) oneO) #4
noncomputable def nSum2SuccLe : ArithmeticSentence := ∀¹* nSum2SuccLeB

lemma models_nSum2SuccLe : V↓[ℒₒᵣ] ⊧ nSum2SuccLe ↔ (∀ a b s u n : V, a + b = s → s + 1 = u → u ≤ n → a + b + 1 ≤ n) := by
  simp [nSum2SuccLe, nSum2SuccLeB, eqO, addO, leF, ltF, twoMul, twoMulOne, oneO, zeroO, models_iff,
    Matrix.vecForall_iff, one_add_one_eq_two, le_def]

theorem pa_proves_nSum2SuccLe : 𝗣𝗔 ⊢ nSum2SuccLe :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_nSum2SuccLe.mpr (fun a b s u n h1 h2 h3 ↦ by subst h1; subst h2; exact h3)

theorem lib_nSum2SuccLe : Lib nSum2SuccLe := Lib.of_pa pa_proves_nSum2SuccLe

noncomputable def nSum2SuccLe_as : List V := [eqFact (bv 0 ^+ bv 1) (bv 2), eqFact (bv 2 ^+ 𝟏) (bv 3), leFact (bv 3) (bv 4)]
noncomputable def nSum2SuccLe_c : V := leFact ((bv 0 ^+ bv 1) ^+ 𝟏) (bv 4)

lemma quote_nSum2SuccLeB : (⌜Semiformula.lMap emb nSum2SuccLeB⌝ : V) = impChain LAct nSum2SuccLe_as nSum2SuccLe_c := by
  unfold nSum2SuccLeB nSum2SuccLe_as nSum2SuccLe_c
  simp only [quote_lMap_emb_imp, quote_eqO_closed, quote_leF_closed, quote_ltF_closed, quote_addO_closed,
    quote_twoMul_closed, quote_twoMulOne_closed, quote_oneO_closed, quote_zeroO_closed, quote_closed_bvar_m,
    impChain_cons, impChain_nil]
  try rfl

lemma inst_nSum2SuccLe {a b s u n : V} (ha : IsSemiterm LAct 0 a) (hb : IsSemiterm LAct 0 b) (hs : IsSemiterm LAct 0 s) (hu : IsSemiterm LAct 0 u) (hn : IsSemiterm LAct 0 n) :
    nSum2SuccLe_as.map (instOuter LAct [n, u, s, b, a]) = ([eqFact (a ^+ b) s, eqFact (s ^+ (𝟏 : V)) u, leFact u n] : List V) ∧
    instOuter LAct [n, u, s, b, a] nSum2SuccLe_c = leFact ((a ^+ b) ^+ (𝟏 : V)) n := by
  have hes : ∀ e ∈ ([n, u, s, b, a] : List V), IsSemiterm LAct 0 e := by simp [ha, hb, hs, hu, hn]
  unfold nSum2SuccLe_as nSum2SuccLe_c
  simp only [List.map, List.length_cons, List.length_nil]
  simp (disch := (simp [bv]; try norm_num)) only [instOuter_eqFact _ hes, instOuter_leFact _ hes, instOuter_ltFact _ hes]
  simp (disch := (simp [bv]; try norm_num)) only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
    termSubst_qqAdd', termSubst_qqMul', termSubst_bv, termSubst_qqTwo', termSubst_qqOne', termSubst_qqZero',
    List.getD_cons_zero, List.getD_cons_succ]
  all_goals (constructor <;> first | rfl | trivial)

/-- Row 15: `∀ a u n : V, a + 1 = u → u ≤ n → a + 1 ≤ n`. -/
noncomputable def nSuccLeB : ArithmeticSemisentence 3 := eqO (addO #0 oneO) #1 🡒 leF #1 #2 🡒 leF (addO #0 oneO) #2
noncomputable def nSuccLe : ArithmeticSentence := ∀¹* nSuccLeB

lemma models_nSuccLe : V↓[ℒₒᵣ] ⊧ nSuccLe ↔ (∀ a u n : V, a + 1 = u → u ≤ n → a + 1 ≤ n) := by
  simp [nSuccLe, nSuccLeB, eqO, addO, leF, ltF, twoMul, twoMulOne, oneO, zeroO, models_iff,
    Matrix.vecForall_iff, one_add_one_eq_two, le_def]

theorem pa_proves_nSuccLe : 𝗣𝗔 ⊢ nSuccLe :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_nSuccLe.mpr (fun a u n h1 h2 ↦ by subst h1; exact h2)

theorem lib_nSuccLe : Lib nSuccLe := Lib.of_pa pa_proves_nSuccLe

noncomputable def nSuccLe_as : List V := [eqFact (bv 0 ^+ 𝟏) (bv 1), leFact (bv 1) (bv 2)]
noncomputable def nSuccLe_c : V := leFact (bv 0 ^+ 𝟏) (bv 2)

lemma quote_nSuccLeB : (⌜Semiformula.lMap emb nSuccLeB⌝ : V) = impChain LAct nSuccLe_as nSuccLe_c := by
  unfold nSuccLeB nSuccLe_as nSuccLe_c
  simp only [quote_lMap_emb_imp, quote_eqO_closed, quote_leF_closed, quote_ltF_closed, quote_addO_closed,
    quote_twoMul_closed, quote_twoMulOne_closed, quote_oneO_closed, quote_zeroO_closed, quote_closed_bvar_m,
    impChain_cons, impChain_nil]
  try rfl

lemma inst_nSuccLe {a u n : V} (ha : IsSemiterm LAct 0 a) (hu : IsSemiterm LAct 0 u) (hn : IsSemiterm LAct 0 n) :
    nSuccLe_as.map (instOuter LAct [n, u, a]) = ([eqFact (a ^+ (𝟏 : V)) u, leFact u n] : List V) ∧
    instOuter LAct [n, u, a] nSuccLe_c = leFact (a ^+ (𝟏 : V)) n := by
  have hes : ∀ e ∈ ([n, u, a] : List V), IsSemiterm LAct 0 e := by simp [ha, hu, hn]
  unfold nSuccLe_as nSuccLe_c
  simp only [List.map, List.length_cons, List.length_nil]
  simp (disch := (simp [bv]; try norm_num)) only [instOuter_eqFact _ hes, instOuter_leFact _ hes, instOuter_ltFact _ hes]
  simp (disch := (simp [bv]; try norm_num)) only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
    termSubst_qqAdd', termSubst_qqMul', termSubst_bv, termSubst_qqTwo', termSubst_qqOne', termSubst_qqZero',
    List.getD_cons_zero, List.getD_cons_succ]
  all_goals (constructor <;> first | rfl | trivial)

/-- Row 16: `∀ a b s n : V, a + b = s → s ≤ n → a + b ≤ n`. -/
noncomputable def nSum2LeB : ArithmeticSemisentence 4 := eqO (addO #0 #1) #2 🡒 leF #2 #3 🡒 leF (addO #0 #1) #3
noncomputable def nSum2Le : ArithmeticSentence := ∀¹* nSum2LeB

lemma models_nSum2Le : V↓[ℒₒᵣ] ⊧ nSum2Le ↔ (∀ a b s n : V, a + b = s → s ≤ n → a + b ≤ n) := by
  simp [nSum2Le, nSum2LeB, eqO, addO, leF, ltF, twoMul, twoMulOne, oneO, zeroO, models_iff,
    Matrix.vecForall_iff, one_add_one_eq_two, le_def]

theorem pa_proves_nSum2Le : 𝗣𝗔 ⊢ nSum2Le :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_nSum2Le.mpr (fun a b s n h1 h2 ↦ by subst h1; exact h2)

theorem lib_nSum2Le : Lib nSum2Le := Lib.of_pa pa_proves_nSum2Le

noncomputable def nSum2Le_as : List V := [eqFact (bv 0 ^+ bv 1) (bv 2), leFact (bv 2) (bv 3)]
noncomputable def nSum2Le_c : V := leFact (bv 0 ^+ bv 1) (bv 3)

lemma quote_nSum2LeB : (⌜Semiformula.lMap emb nSum2LeB⌝ : V) = impChain LAct nSum2Le_as nSum2Le_c := by
  unfold nSum2LeB nSum2Le_as nSum2Le_c
  simp only [quote_lMap_emb_imp, quote_eqO_closed, quote_leF_closed, quote_ltF_closed, quote_addO_closed,
    quote_twoMul_closed, quote_twoMulOne_closed, quote_oneO_closed, quote_zeroO_closed, quote_closed_bvar_m,
    impChain_cons, impChain_nil]
  try rfl

lemma inst_nSum2Le {a b s n : V} (ha : IsSemiterm LAct 0 a) (hb : IsSemiterm LAct 0 b) (hs : IsSemiterm LAct 0 s) (hn : IsSemiterm LAct 0 n) :
    nSum2Le_as.map (instOuter LAct [n, s, b, a]) = ([eqFact (a ^+ b) s, leFact s n] : List V) ∧
    instOuter LAct [n, s, b, a] nSum2Le_c = leFact (a ^+ b) n := by
  have hes : ∀ e ∈ ([n, s, b, a] : List V), IsSemiterm LAct 0 e := by simp [ha, hb, hs, hn]
  unfold nSum2Le_as nSum2Le_c
  simp only [List.map, List.length_cons, List.length_nil]
  simp (disch := (simp [bv]; try norm_num)) only [instOuter_eqFact _ hes, instOuter_leFact _ hes, instOuter_ltFact _ hes]
  simp (disch := (simp [bv]; try norm_num)) only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
    termSubst_qqAdd', termSubst_qqMul', termSubst_bv, termSubst_qqTwo', termSubst_qqOne', termSubst_qqZero',
    List.getD_cons_zero, List.getD_cons_succ]
  all_goals (constructor <;> first | rfl | trivial)

/-- Row 17: `∀ x y w : V, x = y → y + 1 = w → x + 1 = w`. -/
noncomputable def nSuccCongB : ArithmeticSemisentence 3 := eqO #0 #1 🡒 eqO (addO #1 oneO) #2 🡒 eqO (addO #0 oneO) #2
noncomputable def nSuccCong : ArithmeticSentence := ∀¹* nSuccCongB

lemma models_nSuccCong : V↓[ℒₒᵣ] ⊧ nSuccCong ↔ (∀ x y w : V, x = y → y + 1 = w → x + 1 = w) := by
  simp [nSuccCong, nSuccCongB, eqO, addO, leF, ltF, twoMul, twoMulOne, oneO, zeroO, models_iff,
    Matrix.vecForall_iff, one_add_one_eq_two, le_def]

theorem pa_proves_nSuccCong : 𝗣𝗔 ⊢ nSuccCong :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_nSuccCong.mpr (fun x y w h1 h2 ↦ by subst h1; exact h2)

theorem lib_nSuccCong : Lib nSuccCong := Lib.of_pa pa_proves_nSuccCong

noncomputable def nSuccCong_as : List V := [eqFact (bv 0) (bv 1), eqFact (bv 1 ^+ 𝟏) (bv 2)]
noncomputable def nSuccCong_c : V := eqFact (bv 0 ^+ 𝟏) (bv 2)

lemma quote_nSuccCongB : (⌜Semiformula.lMap emb nSuccCongB⌝ : V) = impChain LAct nSuccCong_as nSuccCong_c := by
  unfold nSuccCongB nSuccCong_as nSuccCong_c
  simp only [quote_lMap_emb_imp, quote_eqO_closed, quote_leF_closed, quote_ltF_closed, quote_addO_closed,
    quote_twoMul_closed, quote_twoMulOne_closed, quote_oneO_closed, quote_zeroO_closed, quote_closed_bvar_m,
    impChain_cons, impChain_nil]
  try rfl

lemma inst_nSuccCong {x y w : V} (hx : IsSemiterm LAct 0 x) (hy : IsSemiterm LAct 0 y) (hw : IsSemiterm LAct 0 w) :
    nSuccCong_as.map (instOuter LAct [w, y, x]) = ([eqFact x y, eqFact (y ^+ (𝟏 : V)) w] : List V) ∧
    instOuter LAct [w, y, x] nSuccCong_c = eqFact (x ^+ (𝟏 : V)) w := by
  have hes : ∀ e ∈ ([w, y, x] : List V), IsSemiterm LAct 0 e := by simp [hx, hy, hw]
  unfold nSuccCong_as nSuccCong_c
  simp only [List.map, List.length_cons, List.length_nil]
  simp (disch := (simp [bv]; try norm_num)) only [instOuter_eqFact _ hes, instOuter_leFact _ hes, instOuter_ltFact _ hes]
  simp (disch := (simp [bv]; try norm_num)) only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
    termSubst_qqAdd', termSubst_qqMul', termSubst_bv, termSubst_qqTwo', termSubst_qqOne', termSubst_qqZero',
    List.getD_cons_zero, List.getD_cons_succ]
  all_goals (constructor <;> first | rfl | trivial)

/-- Row 18: `∀ x y : V, x = y → x ≤ y`. -/
noncomputable def nLeOfEqB : ArithmeticSemisentence 2 := eqO #0 #1 🡒 leF #0 #1
noncomputable def nLeOfEq : ArithmeticSentence := ∀¹* nLeOfEqB

lemma models_nLeOfEq : V↓[ℒₒᵣ] ⊧ nLeOfEq ↔ (∀ x y : V, x = y → x ≤ y) := by
  simp [nLeOfEq, nLeOfEqB, eqO, addO, leF, ltF, twoMul, twoMulOne, oneO, zeroO, models_iff,
    Matrix.vecForall_iff, one_add_one_eq_two, le_def]

theorem pa_proves_nLeOfEq : 𝗣𝗔 ⊢ nLeOfEq :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_nLeOfEq.mpr (fun x y h ↦ by subst h; exact le_refl x)

theorem lib_nLeOfEq : Lib nLeOfEq := Lib.of_pa pa_proves_nLeOfEq

noncomputable def nLeOfEq_as : List V := [eqFact (bv 0) (bv 1)]
noncomputable def nLeOfEq_c : V := leFact (bv 0) (bv 1)

lemma quote_nLeOfEqB : (⌜Semiformula.lMap emb nLeOfEqB⌝ : V) = impChain LAct nLeOfEq_as nLeOfEq_c := by
  unfold nLeOfEqB nLeOfEq_as nLeOfEq_c
  simp only [quote_lMap_emb_imp, quote_eqO_closed, quote_leF_closed, quote_ltF_closed, quote_addO_closed,
    quote_twoMul_closed, quote_twoMulOne_closed, quote_oneO_closed, quote_zeroO_closed, quote_closed_bvar_m,
    impChain_cons, impChain_nil]
  try rfl

lemma inst_nLeOfEq {x y : V} (hx : IsSemiterm LAct 0 x) (hy : IsSemiterm LAct 0 y) :
    nLeOfEq_as.map (instOuter LAct [y, x]) = ([eqFact x y] : List V) ∧
    instOuter LAct [y, x] nLeOfEq_c = leFact x y := by
  have hes : ∀ e ∈ ([y, x] : List V), IsSemiterm LAct 0 e := by simp [hx, hy]
  unfold nLeOfEq_as nLeOfEq_c
  simp only [List.map, List.length_cons, List.length_nil]
  simp (disch := (simp [bv]; try norm_num)) only [instOuter_eqFact _ hes, instOuter_leFact _ hes, instOuter_ltFact _ hes]
  simp (disch := (simp [bv]; try norm_num)) only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
    termSubst_qqAdd', termSubst_qqMul', termSubst_bv, termSubst_qqTwo', termSubst_qqOne', termSubst_qqZero',
    List.getD_cons_zero, List.getD_cons_succ]
  all_goals (constructor <;> first | rfl | trivial)

end rows

/-! ## 3. The table: the rows' proof codes and pieces, in every model

`NumTableOK tbl N B`: row `i` of `tbl` is `⟪dΛ, vecOf as, c⟫` — the row's `TAct`-proof code
(`Proof TAct dΛ (∀^m (impChain as c))`, `dlen dΛ ≤ N`) with its pieces; `B` bounds every row body
and the three predicate codes `Peq/Ple/Plt`. `exists_numTable`: ONE standard `(N, B)` serves every
model (`Lib.univ_code` row by row). -/

section table

/-- The pieces of a row are semiformulas when its `impChain` is. -/
lemma pieces_of_impChain {n : V} : ∀ {as : List V} {c : V}, IsSemiformula LAct n (impChain LAct as c) →
    (∀ a ∈ as, IsSemiformula LAct n a) ∧ IsSemiformula LAct n c
  | [], _, h => ⟨fun _ h' ↦ absurd h' List.not_mem_nil, h⟩
  | a :: as, c, h => by
    rw [impChain_cons, IsSemiformula.imp] at h
    obtain ⟨has, hc⟩ := pieces_of_impChain h.2
    refine ⟨fun a' ha' ↦ ?_, hc⟩
    rcases List.mem_cons.mp ha' with rfl | ha'
    · exact h.1
    · exact has a' ha'

/-- The code length of a quoted semisentence is its meta length, in every model (any arity). -/
lemma formulaLen_quote_semisentence_V' {m : ℕ} (χ : Semisentence LAct m) :
    formulaLen LAct (⌜χ⌝ : V) = ((flen (Rewriting.emb χ : Semiproposition LAct m) : ℕ) : V) := by
  rw [Sentence.quote_def, formulaLen_quote]

/-- The standard length of a row body (its embedded meta length). -/
def rowLen {m : ℕ} (Bd : ArithmeticSemisentence m) : ℕ :=
  flen (Rewriting.emb (Semiformula.lMap emb Bd) : Semiproposition LAct m)

/-- The `<` operator sentence over `LAct` (`RowInst.Plt = ⌜ltS⌝`). -/
noncomputable def ltS : Semisentence LAct 2 :=
  Semiformula.lMap emb (Rewriting.emb (Semiformula.Operator.LT.lt : Semiformula.Operator ℒₒᵣ 2).sentence : ArithmeticSemisentence 2)
lemma Plt_eq_quote : (Plt : V) = ⌜ltS⌝ := rfl

/-- Row `i` of `tbl` is `⟪dΛ, vecOf as, c⟫`, sound for `∀^m (impChain as c)` at length `≤ N`, body `≤ B`. -/
def NumRowOK (tbl : V) (i : ℕ) (N B : V) (m : ℕ) (as : List V) (c : V) : Prop :=
  π₁ (π₂ tbl.[(i : V)]) = vecOf as ∧ π₂ (π₂ tbl.[(i : V)]) = c ∧
  (∀ a ∈ as, IsSemiformula LAct (m : V) a) ∧ IsSemiformula LAct (m : V) c ∧
  Proof TAct (π₁ tbl.[(i : V)]) (allsIter m (impChain LAct as c)) ∧
  dlen TAct (π₁ tbl.[(i : V)]) ≤ N ∧ formulaLen LAct (impChain LAct as c) ≤ B

lemma numRowOK_of {tbl : V} {i : ℕ} {N B : V} {m : ℕ} {as : List V} {c d : V}
    (Bd : ArithmeticSemisentence m)
    (hrow : tbl.[(i : V)] = ⟪d, vecOf as, c⟫)
    (hq : (⌜Semiformula.lMap emb Bd⌝ : V) = impChain LAct as c)
    (hd : Proof TAct d (qqAlls (⌜Semiformula.lMap emb Bd⌝ : V) (m : V))) (hN : dlen TAct d ≤ N)
    (hB : ((rowLen Bd : ℕ) : V) ≤ B) : NumRowOK tbl i N B m as c := by
  have hsf : IsSemiformula LAct (m : V) (impChain LAct as c) := hq ▸ Sentence.quote_isSemiformula _
  obtain ⟨has, hc⟩ := pieces_of_impChain hsf
  refine ⟨by rw [hrow]; simp, by rw [hrow]; simp, has, hc, ?_, by rw [hrow]; simpa using hN, ?_⟩
  · rw [hrow, pi₁_pair, ← hq, ← qqAlls_natCast]; exact hd
  · rw [← hq, formulaLen_quote_semisentence_V']; exact hB

def rZeroAdd : ℕ := 0
def rAddZero : ℕ := 1
def rOneOne : ℕ := 2
def rZeroOne : ℕ := 3
def rOneAdd : ℕ := 4
def rEqRefl : ℕ := 5
def rCarry : ℕ := 6
def rBit00 : ℕ := 7
def rBit01 : ℕ := 8
def rBit10 : ℕ := 9
def rBit11 : ℕ := 10
def rLeOfAdd : ℕ := 11
def rLtOfSuccLe : ℕ := 12
def rSum3SuccLe : ℕ := 13
def rSum2SuccLe : ℕ := 14
def rSuccLe : ℕ := 15
def rSum2Le : ℕ := 16
def rSuccCong : ℕ := 17
def rLeOfEq : ℕ := 18

/-- **The table is sound**: every row, plus the bounds on the predicate codes. -/
def NumTableOK (tbl N B : V) : Prop :=
  NumRowOK tbl rZeroAdd N B 1 nZeroAdd_as nZeroAdd_c ∧
  NumRowOK tbl rAddZero N B 1 nAddZero_as nAddZero_c ∧
  NumRowOK tbl rOneOne N B 0 nOneOne_as nOneOne_c ∧
  NumRowOK tbl rZeroOne N B 0 nZeroOne_as nZeroOne_c ∧
  NumRowOK tbl rOneAdd N B 2 nOneAdd_as nOneAdd_c ∧
  NumRowOK tbl rEqRefl N B 1 nEqRefl_as nEqRefl_c ∧
  NumRowOK tbl rCarry N B 2 nCarry_as nCarry_c ∧
  NumRowOK tbl rBit00 N B 3 nBit00_as nBit00_c ∧
  NumRowOK tbl rBit01 N B 3 nBit01_as nBit01_c ∧
  NumRowOK tbl rBit10 N B 3 nBit10_as nBit10_c ∧
  NumRowOK tbl rBit11 N B 4 nBit11_as nBit11_c ∧
  NumRowOK tbl rLeOfAdd N B 3 nLeOfAdd_as nLeOfAdd_c ∧
  NumRowOK tbl rLtOfSuccLe N B 3 nLtOfSuccLe_as nLtOfSuccLe_c ∧
  NumRowOK tbl rSum3SuccLe N B 7 nSum3SuccLe_as nSum3SuccLe_c ∧
  NumRowOK tbl rSum2SuccLe N B 5 nSum2SuccLe_as nSum2SuccLe_c ∧
  NumRowOK tbl rSuccLe N B 3 nSuccLe_as nSuccLe_c ∧
  NumRowOK tbl rSum2Le N B 4 nSum2Le_as nSum2Le_c ∧
  NumRowOK tbl rSuccCong N B 3 nSuccCong_as nSuccCong_c ∧
  NumRowOK tbl rLeOfEq N B 2 nLeOfEq_as nLeOfEq_c ∧
  formulaLen LAct (Peq : V) ≤ B ∧
  formulaLen LAct (Ple : V) ≤ B ∧
  formulaLen LAct (Plt : V) ≤ B ∧
  1 ≤ B

/-- **A proof table for the closed binary-arithmetic library exists in every model**, with ONE
standard pair of bounds `(N, B)` (`Lib.univ_code` per row). -/
theorem exists_numTable : ∃ N B : ℕ, ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁],
    ∃ tbl : V, NumTableOK tbl (N : V) (B : V) := by
  obtain ⟨N0, h0⟩ := (lib_nZeroAdd).univ_code
  obtain ⟨N1, h1⟩ := (lib_nAddZero).univ_code
  obtain ⟨N2, h2⟩ := (lib_nOneOne).univ_code
  obtain ⟨N3, h3⟩ := (lib_nZeroOne).univ_code
  obtain ⟨N4, h4⟩ := (lib_nOneAdd).univ_code
  obtain ⟨N5, h5⟩ := (lib_nEqRefl).univ_code
  obtain ⟨N6, h6⟩ := (lib_nCarry).univ_code
  obtain ⟨N7, h7⟩ := (lib_nBit00).univ_code
  obtain ⟨N8, h8⟩ := (lib_nBit01).univ_code
  obtain ⟨N9, h9⟩ := (lib_nBit10).univ_code
  obtain ⟨N10, h10⟩ := (lib_nBit11).univ_code
  obtain ⟨N11, h11⟩ := (lib_nLeOfAdd).univ_code
  obtain ⟨N12, h12⟩ := (lib_nLtOfSuccLe).univ_code
  obtain ⟨N13, h13⟩ := (lib_nSum3SuccLe).univ_code
  obtain ⟨N14, h14⟩ := (lib_nSum2SuccLe).univ_code
  obtain ⟨N15, h15⟩ := (lib_nSuccLe).univ_code
  obtain ⟨N16, h16⟩ := (lib_nSum2Le).univ_code
  obtain ⟨N17, h17⟩ := (lib_nSuccCong).univ_code
  obtain ⟨N18, h18⟩ := (lib_nLeOfEq).univ_code
  refine ⟨N0 + N1 + N2 + N3 + N4 + N5 + N6 + N7 + N8 + N9 + N10 + N11 + N12 + N13 + N14 + N15 + N16 + N17 + N18, rowLen nZeroAddB + rowLen nAddZeroB + rowLen nOneOneB + rowLen nZeroOneB + rowLen nOneAddB + rowLen nEqReflB + rowLen nCarryB + rowLen nBit00B + rowLen nBit01B + rowLen nBit10B + rowLen nBit11B + rowLen nLeOfAddB + rowLen nLtOfSuccLeB + rowLen nSum3SuccLeB + rowLen nSum2SuccLeB + rowLen nSuccLeB + rowLen nSum2LeB + rowLen nSuccCongB + rowLen nLeOfEqB + flen (Rewriting.emb eqS : Semiproposition LAct 2) + flen (Rewriting.emb leS : Semiproposition LAct 2) + flen (Rewriting.emb ltS : Semiproposition LAct 2) + 1, fun V _ _ ↦ ?_⟩
  obtain ⟨d0, hd0, hl0⟩ := h0 V
  obtain ⟨d1, hd1, hl1⟩ := h1 V
  obtain ⟨d2, hd2, hl2⟩ := h2 V
  obtain ⟨d3, hd3, hl3⟩ := h3 V
  obtain ⟨d4, hd4, hl4⟩ := h4 V
  obtain ⟨d5, hd5, hl5⟩ := h5 V
  obtain ⟨d6, hd6, hl6⟩ := h6 V
  obtain ⟨d7, hd7, hl7⟩ := h7 V
  obtain ⟨d8, hd8, hl8⟩ := h8 V
  obtain ⟨d9, hd9, hl9⟩ := h9 V
  obtain ⟨d10, hd10, hl10⟩ := h10 V
  obtain ⟨d11, hd11, hl11⟩ := h11 V
  obtain ⟨d12, hd12, hl12⟩ := h12 V
  obtain ⟨d13, hd13, hl13⟩ := h13 V
  obtain ⟨d14, hd14, hl14⟩ := h14 V
  obtain ⟨d15, hd15, hl15⟩ := h15 V
  obtain ⟨d16, hd16, hl16⟩ := h16 V
  obtain ⟨d17, hd17, hl17⟩ := h17 V
  obtain ⟨d18, hd18, hl18⟩ := h18 V
  refine ⟨vecOf [⟪d0, vecOf nZeroAdd_as, nZeroAdd_c⟫, ⟪d1, vecOf nAddZero_as, nAddZero_c⟫, ⟪d2, vecOf nOneOne_as, nOneOne_c⟫, ⟪d3, vecOf nZeroOne_as, nZeroOne_c⟫, ⟪d4, vecOf nOneAdd_as, nOneAdd_c⟫, ⟪d5, vecOf nEqRefl_as, nEqRefl_c⟫, ⟪d6, vecOf nCarry_as, nCarry_c⟫, ⟪d7, vecOf nBit00_as, nBit00_c⟫, ⟪d8, vecOf nBit01_as, nBit01_c⟫, ⟪d9, vecOf nBit10_as, nBit10_c⟫, ⟪d10, vecOf nBit11_as, nBit11_c⟫, ⟪d11, vecOf nLeOfAdd_as, nLeOfAdd_c⟫, ⟪d12, vecOf nLtOfSuccLe_as, nLtOfSuccLe_c⟫, ⟪d13, vecOf nSum3SuccLe_as, nSum3SuccLe_c⟫, ⟪d14, vecOf nSum2SuccLe_as, nSum2SuccLe_c⟫, ⟪d15, vecOf nSuccLe_as, nSuccLe_c⟫, ⟪d16, vecOf nSum2Le_as, nSum2Le_c⟫, ⟪d17, vecOf nSuccCong_as, nSuccCong_c⟫, ⟪d18, vecOf nLeOfEq_as, nLeOfEq_c⟫], ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact numRowOK_of nZeroAddB (by unfold rZeroAdd; rw [nth_vecOf _ 0 (by simp)]; rfl) quote_nZeroAddB hd0
      (le_trans hl0 (by exact_mod_cast (by omega : N0 ≤ N0 + N1 + N2 + N3 + N4 + N5 + N6 + N7 + N8 + N9 + N10 + N11 + N12 + N13 + N14 + N15 + N16 + N17 + N18)))
      (by exact_mod_cast (by omega : rowLen nZeroAddB ≤ rowLen nZeroAddB + rowLen nAddZeroB + rowLen nOneOneB + rowLen nZeroOneB + rowLen nOneAddB + rowLen nEqReflB + rowLen nCarryB + rowLen nBit00B + rowLen nBit01B + rowLen nBit10B + rowLen nBit11B + rowLen nLeOfAddB + rowLen nLtOfSuccLeB + rowLen nSum3SuccLeB + rowLen nSum2SuccLeB + rowLen nSuccLeB + rowLen nSum2LeB + rowLen nSuccCongB + rowLen nLeOfEqB + flen (Rewriting.emb eqS : Semiproposition LAct 2) + flen (Rewriting.emb leS : Semiproposition LAct 2) + flen (Rewriting.emb ltS : Semiproposition LAct 2) + 1))
  · exact numRowOK_of nAddZeroB (by unfold rAddZero; rw [nth_vecOf _ 1 (by simp)]; rfl) quote_nAddZeroB hd1
      (le_trans hl1 (by exact_mod_cast (by omega : N1 ≤ N0 + N1 + N2 + N3 + N4 + N5 + N6 + N7 + N8 + N9 + N10 + N11 + N12 + N13 + N14 + N15 + N16 + N17 + N18)))
      (by exact_mod_cast (by omega : rowLen nAddZeroB ≤ rowLen nZeroAddB + rowLen nAddZeroB + rowLen nOneOneB + rowLen nZeroOneB + rowLen nOneAddB + rowLen nEqReflB + rowLen nCarryB + rowLen nBit00B + rowLen nBit01B + rowLen nBit10B + rowLen nBit11B + rowLen nLeOfAddB + rowLen nLtOfSuccLeB + rowLen nSum3SuccLeB + rowLen nSum2SuccLeB + rowLen nSuccLeB + rowLen nSum2LeB + rowLen nSuccCongB + rowLen nLeOfEqB + flen (Rewriting.emb eqS : Semiproposition LAct 2) + flen (Rewriting.emb leS : Semiproposition LAct 2) + flen (Rewriting.emb ltS : Semiproposition LAct 2) + 1))
  · exact numRowOK_of nOneOneB (by unfold rOneOne; rw [nth_vecOf _ 2 (by simp)]; rfl) quote_nOneOneB hd2
      (le_trans hl2 (by exact_mod_cast (by omega : N2 ≤ N0 + N1 + N2 + N3 + N4 + N5 + N6 + N7 + N8 + N9 + N10 + N11 + N12 + N13 + N14 + N15 + N16 + N17 + N18)))
      (by exact_mod_cast (by omega : rowLen nOneOneB ≤ rowLen nZeroAddB + rowLen nAddZeroB + rowLen nOneOneB + rowLen nZeroOneB + rowLen nOneAddB + rowLen nEqReflB + rowLen nCarryB + rowLen nBit00B + rowLen nBit01B + rowLen nBit10B + rowLen nBit11B + rowLen nLeOfAddB + rowLen nLtOfSuccLeB + rowLen nSum3SuccLeB + rowLen nSum2SuccLeB + rowLen nSuccLeB + rowLen nSum2LeB + rowLen nSuccCongB + rowLen nLeOfEqB + flen (Rewriting.emb eqS : Semiproposition LAct 2) + flen (Rewriting.emb leS : Semiproposition LAct 2) + flen (Rewriting.emb ltS : Semiproposition LAct 2) + 1))
  · exact numRowOK_of nZeroOneB (by unfold rZeroOne; rw [nth_vecOf _ 3 (by simp)]; rfl) quote_nZeroOneB hd3
      (le_trans hl3 (by exact_mod_cast (by omega : N3 ≤ N0 + N1 + N2 + N3 + N4 + N5 + N6 + N7 + N8 + N9 + N10 + N11 + N12 + N13 + N14 + N15 + N16 + N17 + N18)))
      (by exact_mod_cast (by omega : rowLen nZeroOneB ≤ rowLen nZeroAddB + rowLen nAddZeroB + rowLen nOneOneB + rowLen nZeroOneB + rowLen nOneAddB + rowLen nEqReflB + rowLen nCarryB + rowLen nBit00B + rowLen nBit01B + rowLen nBit10B + rowLen nBit11B + rowLen nLeOfAddB + rowLen nLtOfSuccLeB + rowLen nSum3SuccLeB + rowLen nSum2SuccLeB + rowLen nSuccLeB + rowLen nSum2LeB + rowLen nSuccCongB + rowLen nLeOfEqB + flen (Rewriting.emb eqS : Semiproposition LAct 2) + flen (Rewriting.emb leS : Semiproposition LAct 2) + flen (Rewriting.emb ltS : Semiproposition LAct 2) + 1))
  · exact numRowOK_of nOneAddB (by unfold rOneAdd; rw [nth_vecOf _ 4 (by simp)]; rfl) quote_nOneAddB hd4
      (le_trans hl4 (by exact_mod_cast (by omega : N4 ≤ N0 + N1 + N2 + N3 + N4 + N5 + N6 + N7 + N8 + N9 + N10 + N11 + N12 + N13 + N14 + N15 + N16 + N17 + N18)))
      (by exact_mod_cast (by omega : rowLen nOneAddB ≤ rowLen nZeroAddB + rowLen nAddZeroB + rowLen nOneOneB + rowLen nZeroOneB + rowLen nOneAddB + rowLen nEqReflB + rowLen nCarryB + rowLen nBit00B + rowLen nBit01B + rowLen nBit10B + rowLen nBit11B + rowLen nLeOfAddB + rowLen nLtOfSuccLeB + rowLen nSum3SuccLeB + rowLen nSum2SuccLeB + rowLen nSuccLeB + rowLen nSum2LeB + rowLen nSuccCongB + rowLen nLeOfEqB + flen (Rewriting.emb eqS : Semiproposition LAct 2) + flen (Rewriting.emb leS : Semiproposition LAct 2) + flen (Rewriting.emb ltS : Semiproposition LAct 2) + 1))
  · exact numRowOK_of nEqReflB (by unfold rEqRefl; rw [nth_vecOf _ 5 (by simp)]; rfl) quote_nEqReflB hd5
      (le_trans hl5 (by exact_mod_cast (by omega : N5 ≤ N0 + N1 + N2 + N3 + N4 + N5 + N6 + N7 + N8 + N9 + N10 + N11 + N12 + N13 + N14 + N15 + N16 + N17 + N18)))
      (by exact_mod_cast (by omega : rowLen nEqReflB ≤ rowLen nZeroAddB + rowLen nAddZeroB + rowLen nOneOneB + rowLen nZeroOneB + rowLen nOneAddB + rowLen nEqReflB + rowLen nCarryB + rowLen nBit00B + rowLen nBit01B + rowLen nBit10B + rowLen nBit11B + rowLen nLeOfAddB + rowLen nLtOfSuccLeB + rowLen nSum3SuccLeB + rowLen nSum2SuccLeB + rowLen nSuccLeB + rowLen nSum2LeB + rowLen nSuccCongB + rowLen nLeOfEqB + flen (Rewriting.emb eqS : Semiproposition LAct 2) + flen (Rewriting.emb leS : Semiproposition LAct 2) + flen (Rewriting.emb ltS : Semiproposition LAct 2) + 1))
  · exact numRowOK_of nCarryB (by unfold rCarry; rw [nth_vecOf _ 6 (by simp)]; rfl) quote_nCarryB hd6
      (le_trans hl6 (by exact_mod_cast (by omega : N6 ≤ N0 + N1 + N2 + N3 + N4 + N5 + N6 + N7 + N8 + N9 + N10 + N11 + N12 + N13 + N14 + N15 + N16 + N17 + N18)))
      (by exact_mod_cast (by omega : rowLen nCarryB ≤ rowLen nZeroAddB + rowLen nAddZeroB + rowLen nOneOneB + rowLen nZeroOneB + rowLen nOneAddB + rowLen nEqReflB + rowLen nCarryB + rowLen nBit00B + rowLen nBit01B + rowLen nBit10B + rowLen nBit11B + rowLen nLeOfAddB + rowLen nLtOfSuccLeB + rowLen nSum3SuccLeB + rowLen nSum2SuccLeB + rowLen nSuccLeB + rowLen nSum2LeB + rowLen nSuccCongB + rowLen nLeOfEqB + flen (Rewriting.emb eqS : Semiproposition LAct 2) + flen (Rewriting.emb leS : Semiproposition LAct 2) + flen (Rewriting.emb ltS : Semiproposition LAct 2) + 1))
  · exact numRowOK_of nBit00B (by unfold rBit00; rw [nth_vecOf _ 7 (by simp)]; rfl) quote_nBit00B hd7
      (le_trans hl7 (by exact_mod_cast (by omega : N7 ≤ N0 + N1 + N2 + N3 + N4 + N5 + N6 + N7 + N8 + N9 + N10 + N11 + N12 + N13 + N14 + N15 + N16 + N17 + N18)))
      (by exact_mod_cast (by omega : rowLen nBit00B ≤ rowLen nZeroAddB + rowLen nAddZeroB + rowLen nOneOneB + rowLen nZeroOneB + rowLen nOneAddB + rowLen nEqReflB + rowLen nCarryB + rowLen nBit00B + rowLen nBit01B + rowLen nBit10B + rowLen nBit11B + rowLen nLeOfAddB + rowLen nLtOfSuccLeB + rowLen nSum3SuccLeB + rowLen nSum2SuccLeB + rowLen nSuccLeB + rowLen nSum2LeB + rowLen nSuccCongB + rowLen nLeOfEqB + flen (Rewriting.emb eqS : Semiproposition LAct 2) + flen (Rewriting.emb leS : Semiproposition LAct 2) + flen (Rewriting.emb ltS : Semiproposition LAct 2) + 1))
  · exact numRowOK_of nBit01B (by unfold rBit01; rw [nth_vecOf _ 8 (by simp)]; rfl) quote_nBit01B hd8
      (le_trans hl8 (by exact_mod_cast (by omega : N8 ≤ N0 + N1 + N2 + N3 + N4 + N5 + N6 + N7 + N8 + N9 + N10 + N11 + N12 + N13 + N14 + N15 + N16 + N17 + N18)))
      (by exact_mod_cast (by omega : rowLen nBit01B ≤ rowLen nZeroAddB + rowLen nAddZeroB + rowLen nOneOneB + rowLen nZeroOneB + rowLen nOneAddB + rowLen nEqReflB + rowLen nCarryB + rowLen nBit00B + rowLen nBit01B + rowLen nBit10B + rowLen nBit11B + rowLen nLeOfAddB + rowLen nLtOfSuccLeB + rowLen nSum3SuccLeB + rowLen nSum2SuccLeB + rowLen nSuccLeB + rowLen nSum2LeB + rowLen nSuccCongB + rowLen nLeOfEqB + flen (Rewriting.emb eqS : Semiproposition LAct 2) + flen (Rewriting.emb leS : Semiproposition LAct 2) + flen (Rewriting.emb ltS : Semiproposition LAct 2) + 1))
  · exact numRowOK_of nBit10B (by unfold rBit10; rw [nth_vecOf _ 9 (by simp)]; rfl) quote_nBit10B hd9
      (le_trans hl9 (by exact_mod_cast (by omega : N9 ≤ N0 + N1 + N2 + N3 + N4 + N5 + N6 + N7 + N8 + N9 + N10 + N11 + N12 + N13 + N14 + N15 + N16 + N17 + N18)))
      (by exact_mod_cast (by omega : rowLen nBit10B ≤ rowLen nZeroAddB + rowLen nAddZeroB + rowLen nOneOneB + rowLen nZeroOneB + rowLen nOneAddB + rowLen nEqReflB + rowLen nCarryB + rowLen nBit00B + rowLen nBit01B + rowLen nBit10B + rowLen nBit11B + rowLen nLeOfAddB + rowLen nLtOfSuccLeB + rowLen nSum3SuccLeB + rowLen nSum2SuccLeB + rowLen nSuccLeB + rowLen nSum2LeB + rowLen nSuccCongB + rowLen nLeOfEqB + flen (Rewriting.emb eqS : Semiproposition LAct 2) + flen (Rewriting.emb leS : Semiproposition LAct 2) + flen (Rewriting.emb ltS : Semiproposition LAct 2) + 1))
  · exact numRowOK_of nBit11B (by unfold rBit11; rw [nth_vecOf _ 10 (by simp)]; rfl) quote_nBit11B hd10
      (le_trans hl10 (by exact_mod_cast (by omega : N10 ≤ N0 + N1 + N2 + N3 + N4 + N5 + N6 + N7 + N8 + N9 + N10 + N11 + N12 + N13 + N14 + N15 + N16 + N17 + N18)))
      (by exact_mod_cast (by omega : rowLen nBit11B ≤ rowLen nZeroAddB + rowLen nAddZeroB + rowLen nOneOneB + rowLen nZeroOneB + rowLen nOneAddB + rowLen nEqReflB + rowLen nCarryB + rowLen nBit00B + rowLen nBit01B + rowLen nBit10B + rowLen nBit11B + rowLen nLeOfAddB + rowLen nLtOfSuccLeB + rowLen nSum3SuccLeB + rowLen nSum2SuccLeB + rowLen nSuccLeB + rowLen nSum2LeB + rowLen nSuccCongB + rowLen nLeOfEqB + flen (Rewriting.emb eqS : Semiproposition LAct 2) + flen (Rewriting.emb leS : Semiproposition LAct 2) + flen (Rewriting.emb ltS : Semiproposition LAct 2) + 1))
  · exact numRowOK_of nLeOfAddB (by unfold rLeOfAdd; rw [nth_vecOf _ 11 (by simp)]; rfl) quote_nLeOfAddB hd11
      (le_trans hl11 (by exact_mod_cast (by omega : N11 ≤ N0 + N1 + N2 + N3 + N4 + N5 + N6 + N7 + N8 + N9 + N10 + N11 + N12 + N13 + N14 + N15 + N16 + N17 + N18)))
      (by exact_mod_cast (by omega : rowLen nLeOfAddB ≤ rowLen nZeroAddB + rowLen nAddZeroB + rowLen nOneOneB + rowLen nZeroOneB + rowLen nOneAddB + rowLen nEqReflB + rowLen nCarryB + rowLen nBit00B + rowLen nBit01B + rowLen nBit10B + rowLen nBit11B + rowLen nLeOfAddB + rowLen nLtOfSuccLeB + rowLen nSum3SuccLeB + rowLen nSum2SuccLeB + rowLen nSuccLeB + rowLen nSum2LeB + rowLen nSuccCongB + rowLen nLeOfEqB + flen (Rewriting.emb eqS : Semiproposition LAct 2) + flen (Rewriting.emb leS : Semiproposition LAct 2) + flen (Rewriting.emb ltS : Semiproposition LAct 2) + 1))
  · exact numRowOK_of nLtOfSuccLeB (by unfold rLtOfSuccLe; rw [nth_vecOf _ 12 (by simp)]; rfl) quote_nLtOfSuccLeB hd12
      (le_trans hl12 (by exact_mod_cast (by omega : N12 ≤ N0 + N1 + N2 + N3 + N4 + N5 + N6 + N7 + N8 + N9 + N10 + N11 + N12 + N13 + N14 + N15 + N16 + N17 + N18)))
      (by exact_mod_cast (by omega : rowLen nLtOfSuccLeB ≤ rowLen nZeroAddB + rowLen nAddZeroB + rowLen nOneOneB + rowLen nZeroOneB + rowLen nOneAddB + rowLen nEqReflB + rowLen nCarryB + rowLen nBit00B + rowLen nBit01B + rowLen nBit10B + rowLen nBit11B + rowLen nLeOfAddB + rowLen nLtOfSuccLeB + rowLen nSum3SuccLeB + rowLen nSum2SuccLeB + rowLen nSuccLeB + rowLen nSum2LeB + rowLen nSuccCongB + rowLen nLeOfEqB + flen (Rewriting.emb eqS : Semiproposition LAct 2) + flen (Rewriting.emb leS : Semiproposition LAct 2) + flen (Rewriting.emb ltS : Semiproposition LAct 2) + 1))
  · exact numRowOK_of nSum3SuccLeB (by unfold rSum3SuccLe; rw [nth_vecOf _ 13 (by simp)]; rfl) quote_nSum3SuccLeB hd13
      (le_trans hl13 (by exact_mod_cast (by omega : N13 ≤ N0 + N1 + N2 + N3 + N4 + N5 + N6 + N7 + N8 + N9 + N10 + N11 + N12 + N13 + N14 + N15 + N16 + N17 + N18)))
      (by exact_mod_cast (by omega : rowLen nSum3SuccLeB ≤ rowLen nZeroAddB + rowLen nAddZeroB + rowLen nOneOneB + rowLen nZeroOneB + rowLen nOneAddB + rowLen nEqReflB + rowLen nCarryB + rowLen nBit00B + rowLen nBit01B + rowLen nBit10B + rowLen nBit11B + rowLen nLeOfAddB + rowLen nLtOfSuccLeB + rowLen nSum3SuccLeB + rowLen nSum2SuccLeB + rowLen nSuccLeB + rowLen nSum2LeB + rowLen nSuccCongB + rowLen nLeOfEqB + flen (Rewriting.emb eqS : Semiproposition LAct 2) + flen (Rewriting.emb leS : Semiproposition LAct 2) + flen (Rewriting.emb ltS : Semiproposition LAct 2) + 1))
  · exact numRowOK_of nSum2SuccLeB (by unfold rSum2SuccLe; rw [nth_vecOf _ 14 (by simp)]; rfl) quote_nSum2SuccLeB hd14
      (le_trans hl14 (by exact_mod_cast (by omega : N14 ≤ N0 + N1 + N2 + N3 + N4 + N5 + N6 + N7 + N8 + N9 + N10 + N11 + N12 + N13 + N14 + N15 + N16 + N17 + N18)))
      (by exact_mod_cast (by omega : rowLen nSum2SuccLeB ≤ rowLen nZeroAddB + rowLen nAddZeroB + rowLen nOneOneB + rowLen nZeroOneB + rowLen nOneAddB + rowLen nEqReflB + rowLen nCarryB + rowLen nBit00B + rowLen nBit01B + rowLen nBit10B + rowLen nBit11B + rowLen nLeOfAddB + rowLen nLtOfSuccLeB + rowLen nSum3SuccLeB + rowLen nSum2SuccLeB + rowLen nSuccLeB + rowLen nSum2LeB + rowLen nSuccCongB + rowLen nLeOfEqB + flen (Rewriting.emb eqS : Semiproposition LAct 2) + flen (Rewriting.emb leS : Semiproposition LAct 2) + flen (Rewriting.emb ltS : Semiproposition LAct 2) + 1))
  · exact numRowOK_of nSuccLeB (by unfold rSuccLe; rw [nth_vecOf _ 15 (by simp)]; rfl) quote_nSuccLeB hd15
      (le_trans hl15 (by exact_mod_cast (by omega : N15 ≤ N0 + N1 + N2 + N3 + N4 + N5 + N6 + N7 + N8 + N9 + N10 + N11 + N12 + N13 + N14 + N15 + N16 + N17 + N18)))
      (by exact_mod_cast (by omega : rowLen nSuccLeB ≤ rowLen nZeroAddB + rowLen nAddZeroB + rowLen nOneOneB + rowLen nZeroOneB + rowLen nOneAddB + rowLen nEqReflB + rowLen nCarryB + rowLen nBit00B + rowLen nBit01B + rowLen nBit10B + rowLen nBit11B + rowLen nLeOfAddB + rowLen nLtOfSuccLeB + rowLen nSum3SuccLeB + rowLen nSum2SuccLeB + rowLen nSuccLeB + rowLen nSum2LeB + rowLen nSuccCongB + rowLen nLeOfEqB + flen (Rewriting.emb eqS : Semiproposition LAct 2) + flen (Rewriting.emb leS : Semiproposition LAct 2) + flen (Rewriting.emb ltS : Semiproposition LAct 2) + 1))
  · exact numRowOK_of nSum2LeB (by unfold rSum2Le; rw [nth_vecOf _ 16 (by simp)]; rfl) quote_nSum2LeB hd16
      (le_trans hl16 (by exact_mod_cast (by omega : N16 ≤ N0 + N1 + N2 + N3 + N4 + N5 + N6 + N7 + N8 + N9 + N10 + N11 + N12 + N13 + N14 + N15 + N16 + N17 + N18)))
      (by exact_mod_cast (by omega : rowLen nSum2LeB ≤ rowLen nZeroAddB + rowLen nAddZeroB + rowLen nOneOneB + rowLen nZeroOneB + rowLen nOneAddB + rowLen nEqReflB + rowLen nCarryB + rowLen nBit00B + rowLen nBit01B + rowLen nBit10B + rowLen nBit11B + rowLen nLeOfAddB + rowLen nLtOfSuccLeB + rowLen nSum3SuccLeB + rowLen nSum2SuccLeB + rowLen nSuccLeB + rowLen nSum2LeB + rowLen nSuccCongB + rowLen nLeOfEqB + flen (Rewriting.emb eqS : Semiproposition LAct 2) + flen (Rewriting.emb leS : Semiproposition LAct 2) + flen (Rewriting.emb ltS : Semiproposition LAct 2) + 1))
  · exact numRowOK_of nSuccCongB (by unfold rSuccCong; rw [nth_vecOf _ 17 (by simp)]; rfl) quote_nSuccCongB hd17
      (le_trans hl17 (by exact_mod_cast (by omega : N17 ≤ N0 + N1 + N2 + N3 + N4 + N5 + N6 + N7 + N8 + N9 + N10 + N11 + N12 + N13 + N14 + N15 + N16 + N17 + N18)))
      (by exact_mod_cast (by omega : rowLen nSuccCongB ≤ rowLen nZeroAddB + rowLen nAddZeroB + rowLen nOneOneB + rowLen nZeroOneB + rowLen nOneAddB + rowLen nEqReflB + rowLen nCarryB + rowLen nBit00B + rowLen nBit01B + rowLen nBit10B + rowLen nBit11B + rowLen nLeOfAddB + rowLen nLtOfSuccLeB + rowLen nSum3SuccLeB + rowLen nSum2SuccLeB + rowLen nSuccLeB + rowLen nSum2LeB + rowLen nSuccCongB + rowLen nLeOfEqB + flen (Rewriting.emb eqS : Semiproposition LAct 2) + flen (Rewriting.emb leS : Semiproposition LAct 2) + flen (Rewriting.emb ltS : Semiproposition LAct 2) + 1))
  · exact numRowOK_of nLeOfEqB (by unfold rLeOfEq; rw [nth_vecOf _ 18 (by simp)]; rfl) quote_nLeOfEqB hd18
      (le_trans hl18 (by exact_mod_cast (by omega : N18 ≤ N0 + N1 + N2 + N3 + N4 + N5 + N6 + N7 + N8 + N9 + N10 + N11 + N12 + N13 + N14 + N15 + N16 + N17 + N18)))
      (by exact_mod_cast (by omega : rowLen nLeOfEqB ≤ rowLen nZeroAddB + rowLen nAddZeroB + rowLen nOneOneB + rowLen nZeroOneB + rowLen nOneAddB + rowLen nEqReflB + rowLen nCarryB + rowLen nBit00B + rowLen nBit01B + rowLen nBit10B + rowLen nBit11B + rowLen nLeOfAddB + rowLen nLtOfSuccLeB + rowLen nSum3SuccLeB + rowLen nSum2SuccLeB + rowLen nSuccLeB + rowLen nSum2LeB + rowLen nSuccCongB + rowLen nLeOfEqB + flen (Rewriting.emb eqS : Semiproposition LAct 2) + flen (Rewriting.emb leS : Semiproposition LAct 2) + flen (Rewriting.emb ltS : Semiproposition LAct 2) + 1))
  · rw [Peq, formulaLen_quote_semisentence_V']; exact_mod_cast (by omega : flen (Rewriting.emb eqS : Semiproposition LAct 2) ≤ rowLen nZeroAddB + rowLen nAddZeroB + rowLen nOneOneB + rowLen nZeroOneB + rowLen nOneAddB + rowLen nEqReflB + rowLen nCarryB + rowLen nBit00B + rowLen nBit01B + rowLen nBit10B + rowLen nBit11B + rowLen nLeOfAddB + rowLen nLtOfSuccLeB + rowLen nSum3SuccLeB + rowLen nSum2SuccLeB + rowLen nSuccLeB + rowLen nSum2LeB + rowLen nSuccCongB + rowLen nLeOfEqB + flen (Rewriting.emb eqS : Semiproposition LAct 2) + flen (Rewriting.emb leS : Semiproposition LAct 2) + flen (Rewriting.emb ltS : Semiproposition LAct 2) + 1)
  · rw [Ple, formulaLen_quote_semisentence_V']; exact_mod_cast (by omega : flen (Rewriting.emb leS : Semiproposition LAct 2) ≤ rowLen nZeroAddB + rowLen nAddZeroB + rowLen nOneOneB + rowLen nZeroOneB + rowLen nOneAddB + rowLen nEqReflB + rowLen nCarryB + rowLen nBit00B + rowLen nBit01B + rowLen nBit10B + rowLen nBit11B + rowLen nLeOfAddB + rowLen nLtOfSuccLeB + rowLen nSum3SuccLeB + rowLen nSum2SuccLeB + rowLen nSuccLeB + rowLen nSum2LeB + rowLen nSuccCongB + rowLen nLeOfEqB + flen (Rewriting.emb eqS : Semiproposition LAct 2) + flen (Rewriting.emb leS : Semiproposition LAct 2) + flen (Rewriting.emb ltS : Semiproposition LAct 2) + 1)
  · rw [Plt_eq_quote, formulaLen_quote_semisentence_V']; exact_mod_cast (by omega : flen (Rewriting.emb ltS : Semiproposition LAct 2) ≤ rowLen nZeroAddB + rowLen nAddZeroB + rowLen nOneOneB + rowLen nZeroOneB + rowLen nOneAddB + rowLen nEqReflB + rowLen nCarryB + rowLen nBit00B + rowLen nBit01B + rowLen nBit10B + rowLen nBit11B + rowLen nLeOfAddB + rowLen nLtOfSuccLeB + rowLen nSum3SuccLeB + rowLen nSum2SuccLeB + rowLen nSuccLeB + rowLen nSum2LeB + rowLen nSuccCongB + rowLen nLeOfEqB + flen (Rewriting.emb eqS : Semiproposition LAct 2) + flen (Rewriting.emb leS : Semiproposition LAct 2) + flen (Rewriting.emb ltS : Semiproposition LAct 2) + 1)
  · exact_mod_cast (by omega : 1 ≤ rowLen nZeroAddB + rowLen nAddZeroB + rowLen nOneOneB + rowLen nZeroOneB + rowLen nOneAddB + rowLen nEqReflB + rowLen nCarryB + rowLen nBit00B + rowLen nBit01B + rowLen nBit10B + rowLen nBit11B + rowLen nLeOfAddB + rowLen nLtOfSuccLeB + rowLen nSum3SuccLeB + rowLen nSum2SuccLeB + rowLen nSuccLeB + rowLen nSum2LeB + rowLen nSuccCongB + rowLen nLeOfEqB + flen (Rewriting.emb eqS : Semiproposition LAct 2) + flen (Rewriting.emb leS : Semiproposition LAct 2) + flen (Rewriting.emb ltS : Semiproposition LAct 2) + 1)

end table


/-! ## 4. The combinators: the goal leaf, the lemma cut, a table-driven Horn use, the step shapes

A closed fact `A` is derived in the singleton context `sing A = {A}` (the goal, positive; a known
sub-fact `F` enters NEGATED by a lemma cut on its own derivation `dF`), by ONE row of the table
instantiated at witnesses `ev` whose antecedent instances are the cut-in facts and whose conclusion
instance IS `A`, closed by the leaf `goalLeaf` (`axL` on `A`/`neg A`). Three shapes: `step0` (no
sub-fact), `step1` (one), `step2` (two). Each is a Σ₁ function of its data (the row's proof code is
READ FROM the table), with a `DerivationOf` theorem and the uniform bound `nodeCost N B E`. -/

section combinators

/-- `axL (insert (neg A) Γ) A`: closes `insert (neg A) Γ` when `A ∈ Γ`. -/
noncomputable def goalLeaf (Γ A : V) : V := axL (insert (neg LAct A) Γ) A
noncomputable def goalLeafDef : 𝚺₁.Semisentence 3 := .mkSigma
  “y Γ A. ∃ n, !(negGraph LAct) n A ∧ ∃ S, !insertDef S n Γ ∧ !axLGraph y S A”
instance goalLeaf_defined : 𝚺₁-Function₂ (goalLeaf : V → V → V) via goalLeafDef := .mk
  fun v ↦ by simp [goalLeafDef, neg.defined.iff, goalLeaf]

theorem goalLeaf_proof {Γ A : V} (hΓ : IsFormulaSet LAct Γ) (hA : IsFormula LAct A) (h : A ∈ Γ) :
    DerivationOf TAct (goalLeaf Γ A) (insert (neg LAct A) Γ) :=
  ⟨by simp [goalLeaf], Derivation.axL (by simp [hΓ, hA]) (by simp [h]) (by simp)⟩

theorem dlen_goalLeaf_le {Γ A : V} (hΓ : IsFormulaSet LAct Γ) (hA : IsFormula LAct A) (h : A ∈ Γ) :
    dlen TAct (goalLeaf Γ A) ≤ setLen LAct Γ + formulaLen LAct A + 1 := by
  have hpf := goalLeaf_proof hΓ hA h
  rw [dlen_eq_of_graph hpf.2 (DlenGraph.axL_iff.mpr rfl)]
  have := setLen_insert_le (L := LAct) (neg LAct A) Γ
  rw [formulaLen_neg hA.isUFormula] at this
  gcongr

/-- The lemma cut (Chain's `lemmaCut`): `cutRule Γ F (wkRule (insert F Γ) dF) e`. -/
noncomputable def cut1 (Γ F dF e : V) : V := cutRule Γ F (wkToCode (insert F Γ) dF) e
noncomputable def cut1Def : 𝚺₁.Semisentence 5 := .mkSigma
  “y Γ F dF e. ∃ S, !insertDef S F Γ ∧ ∃ w, !wkRuleGraph w S dF ∧ !cutRuleGraph y Γ F w e”
instance cut1_defined : 𝚺₁-Function₄ (cut1 : V → V → V → V → V) via cut1Def := .mk
  fun v ↦ by simp [cut1Def, cut1, wkToCode]

theorem cut1_proof {Γ F dF e : V} (hΓ : IsFormulaSet LAct Γ) (hF : IsFormula LAct F)
    (hdF : DerivationOf TAct dF (insert F 0)) (he : DerivationOf TAct e (insert (neg LAct F) Γ)) :
    DerivationOf TAct (cut1 Γ F dF e) Γ := lemmaCut_proof hΓ hF hdF he

theorem dlen_cut1_le {Γ F dF e : V} (hΓ : IsFormulaSet LAct Γ) (hF : IsFormula LAct F)
    (hdF : DerivationOf TAct dF (insert F 0)) (he : DerivationOf TAct e (insert (neg LAct F) Γ)) :
    dlen TAct (cut1 Γ F dF e) ≤ dlen TAct e + (dlen TAct dF + 2 * setLen LAct Γ + 2 * formulaLen LAct F + 2) :=
  dlen_lemmaCut_le hΓ hF hdF he

/-- Use row `i` of the table at witnesses `ev` to close the goal `A ∈ Γ`. -/
noncomputable def hornGoal (tbl i Γ ev A : V) : V :=
  useHornV LAct Γ ev (π₁ (π₂ tbl.[i])) (π₂ (π₂ tbl.[i])) (π₁ tbl.[i]) (goalLeaf Γ A)
noncomputable def hornGoalDef : 𝚺₁.Semisentence 6 := .mkSigma
  “y tbl i Γ ev A. ∃ r, !nthDef r tbl i ∧ ∃ dΛ, !pi₁Def dΛ r ∧ ∃ p, !pi₂Def p r ∧ ∃ as, !pi₁Def as p ∧
    ∃ c, !pi₂Def c p ∧ ∃ g, !goalLeafDef g Γ A ∧ !(useHornVDef LAct) y Γ ev as c dΛ g”
instance hornGoal_defined : 𝚺₁-Function₅ (hornGoal : V → V → V → V → V → V) via hornGoalDef := .mk
  fun v ↦ by simp [hornGoalDef, goalLeaf_defined.iff, useHornV_defined.iff, hornGoal]

/-- Antecedent instances read off an `inst_` lemma. -/
lemma neg_mem_of_map {es as fs : List V} {Γ : V} (hmap : as.map (instOuter LAct es) = fs)
    (h : ∀ f ∈ fs, neg LAct f ∈ Γ) : ∀ a ∈ as, neg LAct (instOuter LAct es a) ∈ Γ :=
  fun _ ha ↦ h _ (hmap ▸ List.mem_map_of_mem ha)

theorem hornGoal_proof {tbl : V} {i : ℕ} {N B : V} {m : ℕ} {as : List V} {c : V}
    (hrow : NumRowOK tbl i N B m as c) {Γ A : V} (es : List V) (hm : es.length = m)
    (hes : ∀ e ∈ es, IsSemiterm LAct 0 e) (hΓ : IsFormulaSet LAct Γ)
    (hneg : ∀ a ∈ as, neg LAct (instOuter LAct es a) ∈ Γ) (hc : instOuter LAct es c = A) (hA : A ∈ Γ) :
    DerivationOf TAct (hornGoal tbl (i : V) Γ (vecOf es) A) Γ := by
  obtain ⟨h1, h2, has, hcf, hΛ, -, -⟩ := hrow
  unfold hornGoal
  rw [h1, h2]
  have has' : ∀ a ∈ as, IsSemiformula LAct (es.length : V) a := by rw [hm]; exact has
  have hcf' : IsSemiformula LAct (es.length : V) c := by rw [hm]; exact hcf
  rw [useHornV_vecOf Γ es as has' hcf' hes]
  have hA' : IsFormula LAct A := hc ▸ isFormula_instOuter es hcf' hes
  refine useHornCode_proof has' hcf' hes hΓ (subset_refl Γ) hneg (by rw [hm]; exact hΛ) ?_
  rw [hc]; exact goalLeaf_proof hΓ hA' hA

/-- **The bound for a table-driven Horn use** (rows of arity `≤ 7` with `≤ 4` antecedents, witnesses
of length `≤ E`): `≤ N + 20|Γ| + 120·B·E + |A| + 480`. -/
theorem dlen_hornGoal_le {tbl : V} {i : ℕ} {N B : V} {m : ℕ} {as : List V} {c : V}
    (hrow : NumRowOK tbl i N B m as c) {Γ A E : V} (es : List V) (hm : es.length = m)
    (hes : ∀ e ∈ es, IsSemiterm LAct 0 e ∧ termLen LAct e ≤ E) (hE : 1 ≤ E) (hB : 1 ≤ B)
    (hΓ : IsFormulaSet LAct Γ)
    (hneg : ∀ a ∈ as, neg LAct (instOuter LAct es a) ∈ Γ) (hc : instOuter LAct es c = A) (hA : A ∈ Γ)
    (hm7 : m ≤ 7) (hj4 : as.length ≤ 4) :
    dlen TAct (hornGoal tbl (i : V) Γ (vecOf es) A) ≤
      N + 20 * setLen LAct Γ + 120 * (B * E) + formulaLen LAct A + 480 := by
  obtain ⟨h1, h2, has, hcf, hΛ, hN, hlen⟩ := hrow
  unfold hornGoal
  rw [h1, h2]
  have hes₁ : ∀ e ∈ es, IsSemiterm LAct 0 e := fun e he ↦ (hes e he).1
  have has' : ∀ a ∈ as, IsSemiformula LAct (es.length : V) a := by rw [hm]; exact has
  have hcf' : IsSemiformula LAct (es.length : V) c := by rw [hm]; exact hcf
  rw [useHornV_vecOf Γ es as has' hcf' hes₁]
  have hA' : IsFormula LAct A := hc ▸ isFormula_instOuter es hcf' hes₁
  have hleaf : DerivationOf TAct (goalLeaf Γ A) (insert (neg LAct (instOuter LAct es c)) Γ) := by
    rw [hc]; exact goalLeaf_proof hΓ hA' hA
  have hleafLen := dlen_goalLeaf_le hΓ hA' hA
  have hF : formulaLen LAct (impChain LAct as c) * E ≤ B * E :=
    mul_le_mul_of_nonneg_right hlen zero_le
  have hbound := dlen_useHornCode_le (T := TAct) (E := E) (F := B * E) hE has' hcf' hes hΓ (subset_refl Γ)
    hneg (by rw [hm]; exact hΛ) hleaf hF
  refine le_trans hbound ?_
  have hm' : (es.length : V) ≤ 7 := by rw [hm]; exact_mod_cast hm7
  have hj' : (as.length : V) ≤ 4 := by exact_mod_cast hj4
  have hchain : formulaLen LAct (impChain LAct as c) ≤ B * E := le_trans hlen (le_mul_of_one_le_right zero_le hE)
  have hEF : E ≤ B * E := le_mul_of_one_le_left zero_le hB
  have hN' : dlen TAct (π₁ tbl.[(i : V)]) ≤ N := hN
  calc dlen TAct (π₁ tbl.[(i : V)]) + dlen TAct (goalLeaf Γ A) + ((es.length : V) + 3) * setLen LAct Γ
        + ((es.length : V) + 1) * ((es.length : V) + 1) * (B * E + (es.length : V))
        + formulaLen LAct (impChain LAct as c) + (es.length : V) * E + 2 * (es.length : V) + 3
        + (2 * (as.length : V) + 1) * (setLen LAct Γ + ((as.length : V) + 1) * (B * E) + 1)
      ≤ N + (setLen LAct Γ + formulaLen LAct A + 1) + (7 + 3) * setLen LAct Γ
        + (7 + 1) * (7 + 1) * (B * E + 7) + B * E + 7 * (B * E) + 2 * 7 + 3
        + (2 * 4 + 1) * (setLen LAct Γ + (4 + 1) * (B * E) + 1) := by
        gcongr
    _ = N + 20 * setLen LAct Γ + 117 * (B * E) + formulaLen LAct A + 475 := by ring
    _ ≤ N + 20 * setLen LAct Γ + 120 * (B * E) + formulaLen LAct A + 480 := by
        have h1 : (117 : V) * (B * E) ≤ 120 * (B * E) := mul_le_mul_of_nonneg_right (by norm_num) zero_le
        have h2 : (475 : V) ≤ 480 := by norm_num
        calc N + 20 * setLen LAct Γ + 117 * (B * E) + formulaLen LAct A + 475
            ≤ N + 20 * setLen LAct Γ + 120 * (B * E) + formulaLen LAct A + 480 := by gcongr

/-! ### The step shapes -/

/-- The singleton context `{A}`. -/
noncomputable def sing (A : V) : V := insert A 0

lemma isFormulaSet_sing {A : V} (hA : IsFormula LAct A) : IsFormulaSet LAct (sing A) := by
  simp only [sing, IsFormulaSet.insert_iff, hA, true_and]
  exact IsFormulaSet.empty

lemma setLen_sing_le (A : V) : setLen LAct (sing A) ≤ formulaLen LAct A := by
  unfold sing
  refine le_trans (setLen_insert_le _ _) ?_
  rw [show (0 : V) = ∅ from rfl, setLen_empty, zero_add]

lemma mem_sing (A : V) : A ∈ sing A := by simp [sing]

/-- No sub-fact: `hornGoal tbl i {A} ev A`. -/
noncomputable def step0 (tbl i ev A : V) : V := hornGoal tbl i (sing A) ev A
/-- One sub-fact `F` (derivation `dF`), cut in first. -/
noncomputable def step1 (tbl i F dF ev A : V) : V :=
  cut1 (sing A) F dF (hornGoal tbl i (insert (neg LAct F) (sing A)) ev A)
/-- Two sub-facts `F₁, F₂`. -/
noncomputable def step2 (tbl i F₁ d₁ F₂ d₂ ev A : V) : V :=
  cut1 (sing A) F₁ d₁ (cut1 (insert (neg LAct F₁) (sing A)) F₂ d₂
    (hornGoal tbl i (insert (neg LAct F₂) (insert (neg LAct F₁) (sing A))) ev A))

noncomputable def step0Def : 𝚺₁.Semisentence 5 := .mkSigma
  “y tbl i ev A. ∃ S, !insertDef S A 0 ∧ !hornGoalDef y tbl i S ev A”
instance step0_defined : 𝚺₁-Function₄ (step0 : V → V → V → V → V) via step0Def := .mk
  fun v ↦ by simp [step0Def, hornGoal_defined.iff, step0, sing]

noncomputable def step1Def : 𝚺₁.Semisentence 7 := .mkSigma
  “y tbl i F dF ev A. ∃ S, !insertDef S A 0 ∧ ∃ nF, !(negGraph LAct) nF F ∧ ∃ S', !insertDef S' nF S ∧
    ∃ h, !hornGoalDef h tbl i S' ev A ∧ !cut1Def y S F dF h”
instance step1_defined :
    𝚺₁.DefinedFunction (fun v : Fin 6 → V ↦ step1 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)) step1Def := .mk
  fun v ↦ by simp [step1Def, neg.defined.iff, hornGoal_defined.iff, cut1_defined.iff, step1, sing]

noncomputable def step2Def : 𝚺₁.Semisentence 9 := .mkSigma
  “y tbl i F₁ d₁ F₂ d₂ ev A. ∃ S, !insertDef S A 0 ∧ ∃ n₁, !(negGraph LAct) n₁ F₁ ∧ ∃ S₁, !insertDef S₁ n₁ S ∧
    ∃ n₂, !(negGraph LAct) n₂ F₂ ∧ ∃ S₂, !insertDef S₂ n₂ S₁ ∧ ∃ h, !hornGoalDef h tbl i S₂ ev A ∧
    ∃ c₂, !cut1Def c₂ S₁ F₂ d₂ h ∧ !cut1Def y S F₁ d₁ c₂”
instance step2_defined :
    𝚺₁.DefinedFunction (fun v : Fin 8 → V ↦ step2 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7)) step2Def := .mk
  fun v ↦ by simp [step2Def, neg.defined.iff, hornGoal_defined.iff, cut1_defined.iff, step2, sing]

/-- The uniform per-node cost: `N + 700·B·E` (`E` bounds every term length of the node, `B` every
row body and the predicate codes). -/
noncomputable def nodeCost (N B E : V) : V := N + 700 * (B * E)

theorem step0_proof {tbl : V} {i : ℕ} {N B : V} {m : ℕ} {as : List V} {c : V}
    (hrow : NumRowOK tbl i N B m as c) {A : V} (es : List V) (hm : es.length = m)
    (hes : ∀ e ∈ es, IsSemiterm LAct 0 e) (hA : IsFormula LAct A)
    (hmap : as.map (instOuter LAct es) = []) (hc : instOuter LAct es c = A) :
    DerivationOf TAct (step0 tbl (i : V) (vecOf es) A) (sing A) :=
  hornGoal_proof hrow es hm hes (isFormulaSet_sing hA)
    (neg_mem_of_map hmap (fun _ h ↦ absurd h List.not_mem_nil)) hc (mem_sing A)

theorem step1_proof {tbl : V} {i : ℕ} {N B : V} {m : ℕ} {as : List V} {c : V}
    (hrow : NumRowOK tbl i N B m as c) {A F dF : V} (es : List V) (hm : es.length = m)
    (hes : ∀ e ∈ es, IsSemiterm LAct 0 e) (hA : IsFormula LAct A) (hF : IsFormula LAct F)
    (hdF : DerivationOf TAct dF (sing F))
    (hmap : as.map (instOuter LAct es) = [F]) (hc : instOuter LAct es c = A) :
    DerivationOf TAct (step1 tbl (i : V) F dF (vecOf es) A) (sing A) :=
  cut1_proof (isFormulaSet_sing hA) hF hdF
    (hornGoal_proof hrow es hm hes (by simp [isFormulaSet_sing hA, hF])
      (neg_mem_of_map hmap (fun f hf ↦ by simp at hf; subst hf; simp)) hc (by simp [mem_sing]))

theorem step2_proof {tbl : V} {i : ℕ} {N B : V} {m : ℕ} {as : List V} {c : V}
    (hrow : NumRowOK tbl i N B m as c) {A F₁ d₁ F₂ d₂ : V} (es : List V) (hm : es.length = m)
    (hes : ∀ e ∈ es, IsSemiterm LAct 0 e) (hA : IsFormula LAct A) (hF₁ : IsFormula LAct F₁)
    (hF₂ : IsFormula LAct F₂) (hd₁ : DerivationOf TAct d₁ (sing F₁)) (hd₂ : DerivationOf TAct d₂ (sing F₂))
    (hmap : as.map (instOuter LAct es) = [F₁, F₂]) (hc : instOuter LAct es c = A) :
    DerivationOf TAct (step2 tbl (i : V) F₁ d₁ F₂ d₂ (vecOf es) A) (sing A) :=
  cut1_proof (isFormulaSet_sing hA) hF₁ hd₁
    (cut1_proof (by simp [isFormulaSet_sing hA, hF₁]) hF₂ hd₂
      (hornGoal_proof hrow es hm hes (by simp [isFormulaSet_sing hA, hF₁, hF₂])
        (neg_mem_of_map hmap (fun f hf ↦ by simp at hf; rcases hf with rfl | rfl <;> simp)) hc
        (by simp [mem_sing])))

/-! ### The step bounds: each shape costs the sub-derivations plus ONE `nodeCost` -/

lemma one_le_BE {B E : V} (hB : 1 ≤ B) (hE : 1 ≤ E) : 1 ≤ B * E :=
  le_trans hB (le_mul_of_one_le_right zero_le hE)

theorem dlen_step0_le {tbl : V} {i : ℕ} {N B : V} {m : ℕ} {as : List V} {c : V}
    (hrow : NumRowOK tbl i N B m as c) {A E : V} (es : List V) (hm : es.length = m)
    (hes : ∀ e ∈ es, IsSemiterm LAct 0 e ∧ termLen LAct e ≤ E) (hE : 1 ≤ E) (hB : 1 ≤ B)
    (hA : IsFormula LAct A) (hmap : as.map (instOuter LAct es) = []) (hc : instOuter LAct es c = A)
    (hm7 : m ≤ 7) (hj4 : as.length ≤ 4) (hAP : formulaLen LAct A ≤ B * E) :
    dlen TAct (step0 tbl (i : V) (vecOf es) A) ≤ nodeCost N B E := by
  have h1 : 1 ≤ B * E := one_le_BE hB hE
  have hsA : setLen LAct (sing A) ≤ B * E := le_trans (setLen_sing_le A) hAP
  have hh := dlen_hornGoal_le hrow es hm hes hE hB (isFormulaSet_sing hA)
    (neg_mem_of_map hmap (fun _ h ↦ absurd h List.not_mem_nil)) hc (mem_sing A) hm7 hj4
  have e480 : (480 : V) ≤ 480 * (B * E) := le_mul_of_one_le_right zero_le h1
  unfold step0 nodeCost
  refine le_trans hh ?_
  calc N + 20 * setLen LAct (sing A) + 120 * (B * E) + formulaLen LAct A + 480
      ≤ N + 20 * (B * E) + 120 * (B * E) + B * E + 480 * (B * E) := by gcongr
    _ = N + 621 * (B * E) := by ring
    _ ≤ N + 700 * (B * E) := by gcongr; norm_num

theorem dlen_step1_le {tbl : V} {i : ℕ} {N B : V} {m : ℕ} {as : List V} {c : V}
    (hrow : NumRowOK tbl i N B m as c) {A F dF E : V} (es : List V) (hm : es.length = m)
    (hes : ∀ e ∈ es, IsSemiterm LAct 0 e ∧ termLen LAct e ≤ E) (hE : 1 ≤ E) (hB : 1 ≤ B)
    (hA : IsFormula LAct A) (hF : IsFormula LAct F) (hdF : DerivationOf TAct dF (sing F))
    (hmap : as.map (instOuter LAct es) = [F]) (hc : instOuter LAct es c = A)
    (hm7 : m ≤ 7) (hj4 : as.length ≤ 4) (hAP : formulaLen LAct A ≤ B * E) (hFP : formulaLen LAct F ≤ B * E) :
    dlen TAct (step1 tbl (i : V) F dF (vecOf es) A) ≤ dlen TAct dF + nodeCost N B E := by
  have h1 : 1 ≤ B * E := one_le_BE hB hE
  have hes₁ : ∀ e ∈ es, IsSemiterm LAct 0 e := fun e he ↦ (hes e he).1
  have hΓ' : IsFormulaSet LAct (insert (neg LAct F) (sing A)) := by simp [isFormulaSet_sing hA, hF]
  have hΓ'len : setLen LAct (insert (neg LAct F) (sing A)) ≤ B * E + B * E := by
    refine le_trans (setLen_insert_le _ _) ?_
    rw [formulaLen_neg hF.isUFormula]
    exact add_le_add (le_trans (setLen_sing_le A) hAP) hFP
  have hsA : setLen LAct (sing A) ≤ B * E := le_trans (setLen_sing_le A) hAP
  have hneg := neg_mem_of_map (Γ := insert (neg LAct F) (sing A)) hmap (fun f hf ↦ by simp at hf; subst hf; simp)
  have hh := dlen_hornGoal_le hrow es hm hes hE hB hΓ' hneg hc (by simp [mem_sing]) hm7 hj4
  have hhorn := hornGoal_proof hrow es hm hes₁ hΓ' hneg hc (by simp [mem_sing])
  have hcut := dlen_cut1_le (isFormulaSet_sing hA) hF hdF hhorn
  have e480 : (480 : V) ≤ 480 * (B * E) := le_mul_of_one_le_right zero_le h1
  have e2 : (2 : V) ≤ 2 * (B * E) := le_mul_of_one_le_right zero_le h1
  unfold step1 nodeCost
  refine le_trans hcut ?_
  calc dlen TAct (hornGoal tbl (i : V) (insert (neg LAct F) (sing A)) (vecOf es) A)
        + (dlen TAct dF + 2 * setLen LAct (sing A) + 2 * formulaLen LAct F + 2)
      ≤ (N + 20 * (B * E + B * E) + 120 * (B * E) + B * E + 480 * (B * E))
        + (dlen TAct dF + 2 * (B * E) + 2 * (B * E) + 2 * (B * E)) := by
        gcongr
        exact le_trans hh (by gcongr)
    _ = dlen TAct dF + (N + 647 * (B * E)) := by ring
    _ ≤ dlen TAct dF + (N + 700 * (B * E)) := by gcongr; norm_num

theorem dlen_step2_le {tbl : V} {i : ℕ} {N B : V} {m : ℕ} {as : List V} {c : V}
    (hrow : NumRowOK tbl i N B m as c) {A F₁ d₁ F₂ d₂ E : V} (es : List V) (hm : es.length = m)
    (hes : ∀ e ∈ es, IsSemiterm LAct 0 e ∧ termLen LAct e ≤ E) (hE : 1 ≤ E) (hB : 1 ≤ B)
    (hA : IsFormula LAct A) (hF₁ : IsFormula LAct F₁) (hF₂ : IsFormula LAct F₂)
    (hd₁ : DerivationOf TAct d₁ (sing F₁)) (hd₂ : DerivationOf TAct d₂ (sing F₂))
    (hmap : as.map (instOuter LAct es) = [F₁, F₂]) (hc : instOuter LAct es c = A)
    (hm7 : m ≤ 7) (hj4 : as.length ≤ 4) (hAP : formulaLen LAct A ≤ B * E)
    (hF₁P : formulaLen LAct F₁ ≤ B * E) (hF₂P : formulaLen LAct F₂ ≤ B * E) :
    dlen TAct (step2 tbl (i : V) F₁ d₁ F₂ d₂ (vecOf es) A) ≤ dlen TAct d₁ + dlen TAct d₂ + nodeCost N B E := by
  have h1 : 1 ≤ B * E := one_le_BE hB hE
  have hes₁ : ∀ e ∈ es, IsSemiterm LAct 0 e := fun e he ↦ (hes e he).1
  have hΓ₁ : IsFormulaSet LAct (insert (neg LAct F₁) (sing A)) := by simp [isFormulaSet_sing hA, hF₁]
  have hΓ₂ : IsFormulaSet LAct (insert (neg LAct F₂) (insert (neg LAct F₁) (sing A))) := by
    simp [isFormulaSet_sing hA, hF₁, hF₂]
  have hsA : setLen LAct (sing A) ≤ B * E := le_trans (setLen_sing_le A) hAP
  have hΓ₁len : setLen LAct (insert (neg LAct F₁) (sing A)) ≤ B * E + B * E := by
    refine le_trans (setLen_insert_le _ _) ?_
    rw [formulaLen_neg hF₁.isUFormula]
    exact add_le_add hsA hF₁P
  have hΓ₂len : setLen LAct (insert (neg LAct F₂) (insert (neg LAct F₁) (sing A))) ≤ B * E + B * E + B * E := by
    refine le_trans (setLen_insert_le _ _) ?_
    rw [formulaLen_neg hF₂.isUFormula]
    exact add_le_add hΓ₁len hF₂P
  have hneg := neg_mem_of_map (Γ := insert (neg LAct F₂) (insert (neg LAct F₁) (sing A))) hmap
    (fun f hf ↦ by simp at hf; rcases hf with rfl | rfl <;> simp)
  have hh := dlen_hornGoal_le hrow es hm hes hE hB hΓ₂ hneg hc (by simp [mem_sing]) hm7 hj4
  have hhorn := hornGoal_proof hrow es hm hes₁ hΓ₂ hneg hc (by simp [mem_sing])
  have hcut₂ := dlen_cut1_le hΓ₁ hF₂ hd₂ hhorn
  have hinner := cut1_proof hΓ₁ hF₂ hd₂ hhorn
  have hcut₁ := dlen_cut1_le (isFormulaSet_sing hA) hF₁ hd₁ hinner
  have e480 : (480 : V) ≤ 480 * (B * E) := le_mul_of_one_le_right zero_le h1
  have e2 : (2 : V) ≤ 2 * (B * E) := le_mul_of_one_le_right zero_le h1
  unfold step2 nodeCost
  refine le_trans hcut₁ ?_
  calc dlen TAct (cut1 (insert (neg LAct F₁) (sing A)) F₂ d₂
          (hornGoal tbl (i : V) (insert (neg LAct F₂) (insert (neg LAct F₁) (sing A))) (vecOf es) A))
        + (dlen TAct d₁ + 2 * setLen LAct (sing A) + 2 * formulaLen LAct F₁ + 2)
      ≤ ((N + 20 * (B * E + B * E + B * E) + 120 * (B * E) + B * E + 480 * (B * E))
          + (dlen TAct d₂ + 2 * (B * E + B * E) + 2 * (B * E) + 2 * (B * E)))
        + (dlen TAct d₁ + 2 * (B * E) + 2 * (B * E) + 2 * (B * E)) := by
        gcongr
        refine le_trans hcut₂ ?_
        gcongr
        exact le_trans hh (by gcongr)
    _ = dlen TAct d₁ + dlen TAct d₂ + (N + 675 * (B * E)) := by ring
    _ ≤ dlen TAct d₁ + dlen TAct d₂ + (N + 700 * (B * E)) := by gcongr; norm_num

end combinators


/-! ## 5. The successor chain: `succFact z := bnum z + 1 = bnum (z + 1)`

`succCode tbl z` — a `Fixpoint` on `⟪z, d⟫` (parameter `tbl`): `z = 0` by row `zeroOne`, `z = 1` by
`oneOne`, `z = 2m` by `eqRefl` at `bnum (2m + 1)` (the fact is syntactically reflexive), `z = 2m + 1`
by `carry` at `(bnum m, bnum (m + 1))` from the fact for `m` — a CHAIN of `‖z‖ + 1` nodes. -/

section succ

/-- `|bnum n| ≤ 6‖n‖ + 1` in every model (`Assembly/Uniform.termLen_bnum_le_V` at `Type*`). -/
theorem termLen_bnum_le (n : V) : termLen LAct (bnum n) ≤ 6 * ‖n‖ + 1 := by
  induction n using ISigma1.pi1_order_induction with
  | hP => definability
  | ind n ih =>
    rcases zero_one_or_two_le n with rfl | rfl | h2
    · rw [termLen_bnum_zero, length_zero]; simp
    · rw [termLen_bnum_one, length_one, mul_one]; exact le_add_self
    obtain ⟨hm, hlt, he | ho⟩ := two_le_cases h2
    · have ih' := ih (n / 2) hlt
      rw [he, termLen_bnum_two_mul hm, length_two_mul_of_pos (lt_of_lt_of_le zero_lt_one hm)]
      calc termLen LAct (bnum (n / 2)) + 4 ≤ (6 * ‖n / 2‖ + 1) + 4 := by gcongr
        _ ≤ (6 * ‖n / 2‖ + 1) + 4 + 2 := le_self_add
        _ = 6 * (‖n / 2‖ + 1) + 1 := by ring
    · have ih' := ih (n / 2) hlt
      rw [ho, termLen_bnum_two_mul_add_one hm, length_two_mul_add_one]
      calc termLen LAct (bnum (n / 2)) + 6 ≤ (6 * ‖n / 2‖ + 1) + 6 := by gcongr
        _ = 6 * (‖n / 2‖ + 1) + 1 := by ring

/-- `succFact z := bnum z + 1 = bnum (z + 1)`. -/
noncomputable def succFact (z : V) : V := eqFact (bnum z ^+ 𝟏) (bnum (z + 1))
noncomputable def succFactDef : 𝚺₁.Semisentence 2 := .mkSigma
  “y z. ∃ t, !bnumGraph t z ∧ ∃ s, !qqAddGraph s t ↑Arithmetic.one ∧ ∃ t', !bnumGraph t' (z + 1) ∧ !eqFactDef y s t'”
instance succFact_defined : 𝚺₁-Function₁ (succFact : V → V) via succFactDef := .mk fun v ↦ by
  simp [succFactDef, bnum.defined.iff, qqAdd_defined.iff, eqFact_defined.iff, succFact, numeral_eq_natCast]
instance succFact_definable : 𝚺₁-Function₁ (succFact : V → V) := succFact_defined.to_definable

noncomputable def singDef : 𝚺₁.Semisentence 2 := .mkSigma “y A. !insertDef y A 0”
instance sing_defined : 𝚺₁-Function₁ (sing : V → V) via singDef := .mk fun v ↦ by simp [singDef, sing]
instance sing_definable : 𝚺₁-Function₁ (sing : V → V) := sing_defined.to_definable

def nodeCostDef : 𝚺₀.Semisentence 4 := .mkSigma “y N B E. y = N + 700 * (B * E)”
instance nodeCost_defined : 𝚺₀-Function₃ (nodeCost : V → V → V → V) via nodeCostDef := .mk fun v ↦ by
  simp [nodeCostDef, nodeCost, numeral_eq_natCast]
instance nodeCost_definable : 𝚺₀-Function₃ (nodeCost : V → V → V → V) := nodeCost_defined.to_definable

lemma nodeCost_mono {N B E E' : V} (h : E ≤ E') : nodeCost N B E ≤ nodeCost N B E' := by
  unfold nodeCost; gcongr

lemma isFormula_succFact (z : V) : IsFormula LAct (succFact z) :=
  isFormula_eqFact (by simp [isSemiterm_bnum_LAct]) (isSemiterm_bnum_LAct 0 _)

lemma termLen_bnum_add_one (z : V) : termLen LAct (bnum z ^+ 𝟏) = termLen LAct (bnum z) + 2 := by
  rw [termLen_qqAdd isFunc_LAct_addIndex (isSemiterm_bnum_LAct 0 z).isUTerm (isSemiterm_qqOne_LAct 0).isUTerm,
    termLen_qqOne isFunc_LAct_oneIndex]
  ring

/-- `|succFact z| ≤ B·E` once `B ≥ |Peq|` and `E ≥ 6‖z + 1‖ + 3`. -/
lemma formulaLen_succFact_le {B E z : V} (hPeq : formulaLen LAct (Peq : V) ≤ B) (hE : 6 * ‖z + 1‖ + 3 ≤ E) :
    formulaLen LAct (succFact z) ≤ B * E := by
  have hE1 : 1 ≤ E := le_trans (by norm_num) (le_trans le_add_self hE)
  have h1 : termLen LAct (bnum z ^+ 𝟏) ≤ E := by
    rw [termLen_bnum_add_one]
    calc termLen LAct (bnum z) + 2 ≤ (6 * ‖z‖ + 1) + 2 := by gcongr; exact termLen_bnum_le z
      _ ≤ 6 * ‖z + 1‖ + 3 := by
          have := length_monotone (le_self_add : z ≤ z + 1)
          calc 6 * ‖z‖ + 1 + 2 = 6 * ‖z‖ + 3 := by ring
            _ ≤ 6 * ‖z + 1‖ + 3 := by gcongr
      _ ≤ E := hE
  have h2 : termLen LAct (bnum (z + 1)) ≤ E :=
    le_trans (termLen_bnum_le _) (le_trans (by gcongr; norm_num : 6 * ‖z + 1‖ + 1 ≤ 6 * ‖z + 1‖ + 3) hE)
  exact le_trans (formulaLen_eqFact_le hE1 (by simp [isSemiterm_bnum_LAct]) (isSemiterm_bnum_LAct 0 _) h1 h2)
    (mul_le_mul_of_nonneg_right hPeq zero_le)

lemma termLen_bnum_le_E {x z E : V} (hx : x ≤ z + 1) (hE : 6 * ‖z + 1‖ + 3 ≤ E) : termLen LAct (bnum x) ≤ E :=
  le_trans (termLen_bnum_le x) (le_trans (by have := length_monotone hx; gcongr; norm_num) hE)

namespace SuccG

/-- The graph: `⟪z, d⟫` where `d` is the successor-fact derivation of `z`. -/
def Phi (tbl : V) (C : Set V) (pr : V) : Prop :=
  ∃ z d, pr = ⟪z, d⟫ ∧
  ( (z = 0 ∧ d = step0 tbl 3 (vecOf []) (succFact 0)) ∨
    (z = 1 ∧ d = step0 tbl 2 (vecOf []) (succFact 1)) ∨
    (∃ m, 1 ≤ m ∧ z = 2 * m ∧ d = step0 tbl 5 (vecOf [bnum (2 * m + 1)]) (succFact z)) ∨
    (∃ m d', 1 ≤ m ∧ z = 2 * m + 1 ∧ ⟪m, d'⟫ ∈ C ∧
      d = step1 tbl 6 (succFact m) d' (vecOf [bnum (m + 1), bnum m]) (succFact z)) )

noncomputable def blueprint : Fixpoint.Blueprint 1 := ⟨.mkDelta
  (.mkSigma “pr C tbl.
    ∃ z <⁺ pr, ∃ d <⁺ pr, !pairDef pr z d ∧
    ( (z = 0 ∧ ∃ A, !succFactDef A 0 ∧ ∃ x, !step0Def x tbl 3 0 A ∧ d = x) ∨
      (z = 1 ∧ ∃ A, !succFactDef A 1 ∧ ∃ x, !step0Def x tbl 2 0 A ∧ d = x) ∨
      (∃ m < z, 1 ≤ m ∧ z = 2 * m ∧ ∃ t, !bnumGraph t (2 * m + 1) ∧ ∃ ev, !adjoinDef ev t 0 ∧
        ∃ A, !succFactDef A z ∧ ∃ x, !step0Def x tbl 5 ev A ∧ d = x) ∨
      (∃ m < z, ∃ d' < d, 1 ≤ m ∧ z = 2 * m + 1 ∧ :⟪m, d'⟫:∈ C ∧ ∃ F, !succFactDef F m ∧
        ∃ t1, !bnumGraph t1 (m + 1) ∧ ∃ t0, !bnumGraph t0 m ∧ ∃ v0, !adjoinDef v0 t0 0 ∧
        ∃ ev, !adjoinDef ev t1 v0 ∧ ∃ A, !succFactDef A z ∧ ∃ x, !step1Def x tbl 6 F d' ev A ∧ d = x) )”)
  (.mkPi “pr C tbl.
    ∃ z <⁺ pr, ∃ d <⁺ pr, !pairDef pr z d ∧
    ( (z = 0 ∧ ∀ A, !succFactDef A 0 → ∀ x, !step0Def x tbl 3 0 A → d = x) ∨
      (z = 1 ∧ ∀ A, !succFactDef A 1 → ∀ x, !step0Def x tbl 2 0 A → d = x) ∨
      (∃ m < z, 1 ≤ m ∧ z = 2 * m ∧ ∀ t, !bnumGraph t (2 * m + 1) → ∀ ev, !adjoinDef ev t 0 →
        ∀ A, !succFactDef A z → ∀ x, !step0Def x tbl 5 ev A → d = x) ∨
      (∃ m < z, ∃ d' < d, 1 ≤ m ∧ z = 2 * m + 1 ∧ :⟪m, d'⟫:∈ C ∧ ∀ F, !succFactDef F m →
        ∀ t1, !bnumGraph t1 (m + 1) → ∀ t0, !bnumGraph t0 m → ∀ v0, !adjoinDef v0 t0 0 →
        ∀ ev, !adjoinDef ev t1 v0 → ∀ A, !succFactDef A z → ∀ x, !step1Def x tbl 6 F d' ev A → d = x) )”)⟩

lemma d_lt_step1 (tbl i F d' ev A : V) : d' < step1 tbl i F d' ev A :=
  lt_trans (d_lt_wkRule _ _) (d₁_lt_cutRule _ _ _ _)

/-- `Phi` with the bounds the blueprint carries. -/
private lemma phi_iff (tbl C pr : V) :
    Phi tbl {x | x ∈ C} pr ↔
    ∃ z ≤ pr, ∃ d ≤ pr, pr = ⟪z, d⟫ ∧
    ( (z = 0 ∧ d = step0 tbl 3 (vecOf []) (succFact 0)) ∨
      (z = 1 ∧ d = step0 tbl 2 (vecOf []) (succFact 1)) ∨
      (∃ m < z, 1 ≤ m ∧ z = 2 * m ∧ d = step0 tbl 5 (vecOf [bnum (2 * m + 1)]) (succFact z)) ∨
      (∃ m < z, ∃ d' < d, 1 ≤ m ∧ z = 2 * m + 1 ∧ ⟪m, d'⟫ ∈ C ∧
        d = step1 tbl 6 (succFact m) d' (vecOf [bnum (m + 1), bnum m]) (succFact z)) ) := by
  constructor
  · rintro ⟨z, d, rfl, h⟩
    refine ⟨z, le_pair_left _ _, d, le_pair_right _ _, rfl, ?_⟩
    rcases h with h | h | ⟨m, hm, rfl, rfl⟩ | ⟨m, d', hm, rfl, hC, rfl⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl ⟨m, Bnum.lt_two_mul hm, hm, rfl, rfl⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨m, Bnum.lt_two_mul_add_one hm, d', d_lt_step1 _ _ _ _ _ _, hm, rfl, hC, rfl⟩))
  · rintro ⟨z, _, d, _, rfl, h⟩
    refine ⟨z, d, rfl, ?_⟩
    rcases h with h | h | ⟨m, _, hm, rfl, rfl⟩ | ⟨m, _, d', _, hm, rfl, hC, rfl⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl ⟨m, hm, rfl, rfl⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨m, d', hm, rfl, hC, rfl⟩))

noncomputable def construction : Fixpoint.Construction V blueprint where
  Φ := fun v ↦ Phi (v 0)
  defined := .mk <| by
    constructor
    · intro v
      simp [blueprint, succFact_defined.iff, bnum.defined.iff, step0_defined.iff, step1_defined.iff,
        numeral_eq_natCast]
    · intro v
      symm
      simpa [blueprint, succFact_defined.iff, bnum.defined.iff, step0_defined.iff, step1_defined.iff,
        numeral_eq_natCast] using phi_iff (v 2) (v 1) (v 0)
  monotone := by
    rintro C C' hC _ pr ⟨z, d, rfl, h⟩
    refine ⟨z, d, rfl, ?_⟩
    rcases h with h | h | h | ⟨m, d', hm, rfl, hC', rfl⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr ⟨m, d', hm, rfl, hC hC', rfl⟩))

instance : construction.Finite V where
  finite := by
    rintro C _ pr ⟨z, d, rfl, h⟩
    rcases h with h | h | h | ⟨m, d', hm, rfl, hC', rfl⟩
    · exact ⟨0, z, _, rfl, Or.inl h⟩
    · exact ⟨0, z, _, rfl, Or.inr (Or.inl h)⟩
    · exact ⟨0, z, _, rfl, Or.inr (Or.inr (Or.inl h))⟩
    · exact ⟨⟪m, d'⟫ + 1, _, _, rfl, Or.inr (Or.inr (Or.inr ⟨m, d', hm, rfl, ⟨hC', lt_add_one _⟩, rfl⟩))⟩

end SuccG

/-- `SuccGraph tbl z d`: `d` is the successor-fact derivation of `z` over the table `tbl`. -/
def SuccGraph (tbl z d : V) : Prop := SuccG.construction.Fixpoint ![tbl] ⟪z, d⟫

noncomputable def succGraphDef : 𝚺₁.Semisentence 3 := .mkSigma
  “tbl z d. ∃ p, !pairDef p z d ∧ !SuccG.blueprint.fixpointDef p tbl”

instance succGraph_defined : 𝚺₁-Relation₃ (SuccGraph : V → V → V → Prop) via succGraphDef := .mk fun v ↦ by
  simp [succGraphDef, SuccG.construction.eval_fixpointDef, SuccGraph]
  have e : (fun _ : Fin 1 ↦ v 0) = ![v 0] := by funext i; fin_cases i; rfl
  rw [e]
instance succGraph_definable : 𝚺₁-Relation₃ (SuccGraph : V → V → V → Prop) := succGraph_defined.to_definable

lemma SuccGraph.case_iff {tbl z d : V} :
    SuccGraph tbl z d ↔
    (z = 0 ∧ d = step0 tbl 3 (vecOf []) (succFact 0)) ∨
    (z = 1 ∧ d = step0 tbl 2 (vecOf []) (succFact 1)) ∨
    (∃ m, 1 ≤ m ∧ z = 2 * m ∧ d = step0 tbl 5 (vecOf [bnum (2 * m + 1)]) (succFact z)) ∨
    (∃ m d', 1 ≤ m ∧ z = 2 * m + 1 ∧ SuccGraph tbl m d' ∧
      d = step1 tbl 6 (succFact m) d' (vecOf [bnum (m + 1), bnum m]) (succFact z)) :=
  Iff.trans SuccG.construction.case (by simp [SuccG.construction, SuccG.Phi, SuccGraph])

lemma SuccGraph.zero_iff {tbl d : V} : SuccGraph tbl 0 d ↔ d = step0 tbl 3 (vecOf []) (succFact 0) := by
  rw [SuccGraph.case_iff]
  constructor
  · rintro (⟨_, rfl⟩ | ⟨h, _⟩ | ⟨m, hm, h, _⟩ | ⟨m, _, hm, h, _⟩)
    · rfl
    · exact absurd h.symm Arithmetic.one_ne_zero
    · exact absurd h.symm (two_mul_ne_zero hm)
    · exact absurd h.symm (two_mul_add_one_ne_zero m)
  · rintro rfl; exact Or.inl ⟨rfl, rfl⟩

lemma SuccGraph.one_iff {tbl d : V} : SuccGraph tbl 1 d ↔ d = step0 tbl 2 (vecOf []) (succFact 1) := by
  rw [SuccGraph.case_iff]
  constructor
  · rintro (⟨h, _⟩ | ⟨_, rfl⟩ | ⟨m, hm, h, _⟩ | ⟨m, _, hm, h, _⟩)
    · exact absurd h Arithmetic.one_ne_zero
    · rfl
    · exact absurd h.symm (two_mul_ne_one m)
    · exact absurd h.symm (two_mul_add_one_ne_one hm)
  · rintro rfl; exact Or.inr (Or.inl ⟨rfl, rfl⟩)

lemma SuccGraph.two_mul_iff {tbl m d : V} (hm : 1 ≤ m) :
    SuccGraph tbl (2 * m) d ↔ d = step0 tbl 5 (vecOf [bnum (2 * m + 1)]) (succFact (2 * m)) := by
  rw [SuccGraph.case_iff]
  constructor
  · rintro (⟨h, _⟩ | ⟨h, _⟩ | ⟨m', _, h, rfl⟩ | ⟨m', _, _, h, _⟩)
    · exact absurd h (two_mul_ne_zero hm)
    · exact absurd h (two_mul_ne_one m)
    · obtain rfl := two_mul_inj h; rfl
    · exact absurd h (two_mul_ne_two_mul_add_one m m')
  · rintro rfl; exact Or.inr (Or.inr (Or.inl ⟨m, hm, rfl, rfl⟩))

lemma SuccGraph.two_mul_add_one_iff {tbl m d : V} (hm : 1 ≤ m) :
    SuccGraph tbl (2 * m + 1) d ↔ ∃ d', SuccGraph tbl m d' ∧
      d = step1 tbl 6 (succFact m) d' (vecOf [bnum (m + 1), bnum m]) (succFact (2 * m + 1)) := by
  rw [SuccGraph.case_iff]
  constructor
  · rintro (⟨h, _⟩ | ⟨h, _⟩ | ⟨m', _, h, _⟩ | ⟨m', d', _, h, hd', rfl⟩)
    · exact absurd h (two_mul_add_one_ne_zero m)
    · exact absurd h (two_mul_add_one_ne_one hm)
    · exact absurd h.symm (two_mul_ne_two_mul_add_one m' m)
    · obtain rfl := two_mul_add_one_inj h; exact ⟨d', hd', rfl⟩
  · rintro ⟨d', hd', rfl⟩; exact Or.inr (Or.inr (Or.inr ⟨m, d', hm, rfl, hd', rfl⟩))

lemma succGraph_exists (tbl z : V) : ∃ d, SuccGraph tbl z d := by
  induction z using ISigma1.sigma1_order_induction with
  | hP => definability
  | ind z ih =>
    rcases zero_one_or_two_le z with rfl | rfl | h2
    · exact ⟨_, SuccGraph.zero_iff.mpr rfl⟩
    · exact ⟨_, SuccGraph.one_iff.mpr rfl⟩
    obtain ⟨hm, hlt, he | ho⟩ := two_le_cases h2
    · rw [he]; exact ⟨_, (SuccGraph.two_mul_iff hm).mpr rfl⟩
    · obtain ⟨d', hd'⟩ := ih (z / 2) hlt
      rw [ho]; exact ⟨_, (SuccGraph.two_mul_add_one_iff hm).mpr ⟨d', hd', rfl⟩⟩

lemma succGraph_unique (tbl z : V) : ∀ d₁ d₂, SuccGraph tbl z d₁ → SuccGraph tbl z d₂ → d₁ = d₂ := by
  induction z using ISigma1.pi1_order_induction with
  | hP => definability
  | ind z ih =>
    intro d₁ d₂ h₁ h₂
    rcases zero_one_or_two_le z with rfl | rfl | h2
    · rw [SuccGraph.zero_iff] at h₁ h₂; rw [h₁, h₂]
    · rw [SuccGraph.one_iff] at h₁ h₂; rw [h₁, h₂]
    obtain ⟨hm, hlt, he | ho⟩ := two_le_cases h2
    · rw [he] at h₁ h₂
      rw [(SuccGraph.two_mul_iff hm).mp h₁, (SuccGraph.two_mul_iff hm).mp h₂]
    · rw [ho] at h₁ h₂
      obtain ⟨e₁, he₁, rfl⟩ := (SuccGraph.two_mul_add_one_iff hm).mp h₁
      obtain ⟨e₂, he₂, rfl⟩ := (SuccGraph.two_mul_add_one_iff hm).mp h₂
      rw [ih (z / 2) hlt e₁ e₂ he₁ he₂]

lemma succGraph_existsUnique (tbl z : V) : ∃! d, SuccGraph tbl z d := by
  obtain ⟨d, hd⟩ := succGraph_exists tbl z
  exact ExistsUnique.intro d hd (fun d' h' ↦ succGraph_unique tbl z d' d h' hd)

/-- **The successor-fact prover**: the derivation code of `{bnum z + 1 = bnum (z + 1)}`. -/
noncomputable def succCode (tbl z : V) : V := Classical.choose! (succGraph_existsUnique tbl z)

lemma succCode_graph (tbl z : V) : SuccGraph tbl z (succCode tbl z) :=
  Classical.choose!_spec (succGraph_existsUnique tbl z)

lemma succCode_eq_of_graph {tbl z d : V} (h : SuccGraph tbl z d) : succCode tbl z = d :=
  succGraph_unique tbl z _ _ (succCode_graph tbl z) h

noncomputable def succCodeDef : 𝚺₁.Semisentence 3 := .mkSigma “y tbl z. !succGraphDef tbl z y”

/-- TRAP: a full `simp` on this goal explodes (unification through `succGraphDef`'s fixpoint formula);
rewrite step by step with the substitution instantiated explicitly. -/
instance succCode_defined : 𝚺₁-Function₂ (succCode : V → V → V) via succCodeDef := .mk fun v ↦ by
  simp only [succCodeDef]
  rw [HierarchySymbol.Semiformula.val_mkSigma, Semiformula.eval_substs ![#1, #2, #0] succGraphDef.val,
    succGraph_defined.iff]
  simp only [Function.comp_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons, Semiterm.val_bvar, Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
  constructor
  · intro h; exact (succCode_eq_of_graph h).symm
  · intro h; rw [h]; exact succCode_graph _ _
instance succCode_definable : 𝚺₁-Function₂ (succCode : V → V → V) := succCode_defined.to_definable

end succ


/-! ## 6. Soundness and length of `succCode`; its `sLemma` packaging -/

section succSound

/-- The length bound of the successor chain: `(‖z‖ + 1)` nodes, each `≤ nodeCost N B (6‖z + 1‖ + 3)`. -/
noncomputable def succBound (N B z : V) : V := (‖z‖ + 1) * nodeCost N B (6 * ‖z + 1‖ + 3)

lemma cast_rZeroOne : ((rZeroOne : ℕ) : V) = 3 := by simp [rZeroOne]
lemma cast_rOneOne : ((rOneOne : ℕ) : V) = 2 := by simp [rOneOne]
lemma cast_rEqRefl : ((rEqRefl : ℕ) : V) = 5 := by simp [rEqRefl]
lemma cast_rCarry : ((rCarry : ℕ) : V) = 6 := by simp [rCarry]

lemma one_le_E {z : V} : 1 ≤ 6 * ‖z + 1‖ + 3 := le_trans (by norm_num) le_add_self

lemma succFact_two_mul {m : V} (hm : 1 ≤ m) : succFact (2 * m) = eqFact (bnum (2 * m + 1)) (bnum (2 * m + 1)) := by
  unfold succFact
  rw [bnum_two_mul hm, bnum_two_mul_add_one hm]

lemma succFact_two_mul_add_one {m : V} (hm : 1 ≤ m) :
    succFact (2 * m + 1) = eqFact ((((𝟐 : V) ^* bnum m) ^+ 𝟏) ^+ 𝟏) (𝟐 ^* bnum (m + 1)) := by
  unfold succFact
  rw [bnum_two_mul_add_one hm, show 2 * m + 1 + 1 = 2 * (m + 1) by ring,
    bnum_two_mul (le_trans hm le_self_add)]

/-- **Soundness and length of the successor chain**, by Π₁ order induction on `z`. -/
theorem succGraph_sound {tbl N B : V} (htbl : NumTableOK tbl N B) (z : V) :
    ∀ d, SuccGraph tbl z d → DerivationOf TAct d (sing (succFact z)) ∧ dlen TAct d ≤ succBound N B z := by
  induction z using ISigma1.pi1_order_induction with
  | hP => simp only [succBound]; definability
  | ind z ih =>
    intro d hd
    obtain ⟨-, -, hr2, hr3, -, hr5, hr6, -, -, -, -, -, -, -, -, -, -, -, -, hPeq, -, -, hB⟩ := htbl
    rcases zero_one_or_two_le z with rfl | rfl | h2
    · rw [SuccGraph.zero_iff] at hd
      subst hd
      have hc : instOuter LAct [] nZeroOne_c = succFact (0 : V) := by
        rw [inst_nZeroOne.2]; simp [succFact]
      have hpf := step0_proof hr3 [] rfl (by simp) (isFormula_succFact 0) inst_nZeroOne.1 hc
      have hlen := dlen_step0_le hr3 (E := 6 * ‖(1 : V)‖ + 3) [] rfl (by simp) (le_trans (by norm_num) le_add_self) hB
        (isFormula_succFact 0) inst_nZeroOne.1 hc (by norm_num) (by simp [nZeroOne_as])
        (formulaLen_succFact_le hPeq (by rw [zero_add]))
      rw [cast_rZeroOne] at hpf hlen
      refine ⟨hpf, ?_⟩
      rw [succBound, length_zero, zero_add, one_mul]
      exact hlen
    · rw [SuccGraph.one_iff] at hd
      subst hd
      have hc : instOuter LAct [] nOneOne_c = succFact (1 : V) := by
        rw [inst_nOneOne.2]
        unfold succFact
        rw [bnum_one, show (1 : V) + 1 = 2 * 1 by ring, bnum_two_mul le_rfl, bnum_one]
      have hpf := step0_proof hr2 [] rfl (by simp) (isFormula_succFact 1) inst_nOneOne.1 hc
      have hlen := dlen_step0_le hr2 (E := 6 * ‖(1 : V) + 1‖ + 3) [] rfl (by simp) one_le_E hB
        (isFormula_succFact 1) inst_nOneOne.1 hc (by norm_num) (by simp [nOneOne_as])
        (formulaLen_succFact_le hPeq le_rfl)
      rw [cast_rOneOne] at hpf hlen
      refine ⟨hpf, ?_⟩
      rw [succBound, length_one]
      exact le_trans hlen (le_mul_of_one_le_left zero_le (by norm_num))
    obtain ⟨hm, hlt, he | ho⟩ := two_le_cases h2
    · rw [he] at hd ⊢
      rw [SuccGraph.two_mul_iff hm] at hd
      subst hd
      have hx : IsSemiterm LAct 0 (bnum (2 * (z / 2) + 1)) := isSemiterm_bnum_LAct 0 _
      have hc : instOuter LAct [bnum (2 * (z / 2) + 1)] nEqRefl_c = succFact (2 * (z / 2)) := by
        rw [(inst_nEqRefl hx).2, succFact_two_mul hm]
      have hes : ∀ e ∈ [bnum (2 * (z / 2) + 1)], IsSemiterm LAct 0 e ∧ termLen LAct e ≤ 6 * ‖2 * (z / 2) + 1‖ + 3 := by
        simp only [List.mem_singleton, forall_eq]
        exact ⟨hx, termLen_bnum_le_E le_rfl le_rfl⟩
      have hpf := step0_proof hr5 [bnum (2 * (z / 2) + 1)] rfl (fun e he ↦ (hes e he).1) (isFormula_succFact _)
        (inst_nEqRefl hx).1 hc
      have hlen := dlen_step0_le hr5 [bnum (2 * (z / 2) + 1)] rfl hes one_le_E hB (isFormula_succFact _)
        (inst_nEqRefl hx).1 hc (by norm_num) (by simp [nEqRefl_as]) (formulaLen_succFact_le hPeq le_rfl)
      rw [cast_rEqRefl] at hpf hlen
      refine ⟨hpf, le_trans hlen (le_mul_of_one_le_left zero_le ?_)⟩
      exact le_trans (by norm_num) le_add_self
    · rw [ho] at hd ⊢
      rw [SuccGraph.two_mul_add_one_iff hm] at hd
      obtain ⟨d', hd', rfl⟩ := hd
      obtain ⟨hpf', hlen'⟩ := ih (z / 2) hlt d' hd'
      set m := z / 2 with hm_def
      have hx : IsSemiterm LAct 0 (bnum m) := isSemiterm_bnum_LAct 0 _
      have hw : IsSemiterm LAct 0 (bnum (m + 1)) := isSemiterm_bnum_LAct 0 _
      have hmap : nCarry_as.map (instOuter LAct [bnum (m + 1), bnum m]) = [succFact m] := (inst_nCarry hx hw).1
      have hc : instOuter LAct [bnum (m + 1), bnum m] nCarry_c = succFact (2 * m + 1) := by
        rw [(inst_nCarry hx hw).2, succFact_two_mul_add_one hm]
      have hle1 : m + 1 ≤ 2 * m + 1 + 1 := by
        rw [two_mul]
        exact le_trans (by gcongr; exact le_self_add : m + 1 ≤ m + m + 1) le_self_add
      have hle0 : m ≤ 2 * m + 1 + 1 := le_trans le_self_add hle1
      have hE : 6 * ‖m + 1‖ + 3 ≤ 6 * ‖2 * m + 1 + 1‖ + 3 := by
        have := length_monotone hle1
        gcongr
      have hes : ∀ e ∈ [bnum (m + 1), bnum m], IsSemiterm LAct 0 e ∧ termLen LAct e ≤ 6 * ‖2 * m + 1 + 1‖ + 3 := by
        intro e he
        simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl
        · exact ⟨hw, termLen_bnum_le_E (z := 2 * m + 1) hle1 le_rfl⟩
        · exact ⟨hx, termLen_bnum_le_E (z := 2 * m + 1) hle0 le_rfl⟩
      have hpf := step1_proof hr6 [bnum (m + 1), bnum m] rfl (fun e he ↦ (hes e he).1) (isFormula_succFact _)
        (isFormula_succFact m) hpf' hmap hc
      have hlen := dlen_step1_le hr6 [bnum (m + 1), bnum m] rfl hes one_le_E hB (isFormula_succFact _)
        (isFormula_succFact m) hpf' hmap hc (by norm_num) (by simp [nCarry_as])
        (formulaLen_succFact_le hPeq le_rfl)
        (formulaLen_succFact_le hPeq (le_trans le_rfl hE))
      rw [cast_rCarry] at hpf hlen
      refine ⟨hpf, ?_⟩
      unfold succBound at hlen' ⊢
      rw [length_two_mul_add_one]
      calc dlen TAct (step1 tbl 6 (succFact m) d' (vecOf [bnum (m + 1), bnum m]) (succFact (2 * m + 1)))
          ≤ dlen TAct d' + nodeCost N B (6 * ‖2 * m + 1 + 1‖ + 3) := hlen
        _ ≤ (‖m‖ + 1) * nodeCost N B (6 * ‖2 * m + 1 + 1‖ + 3) + nodeCost N B (6 * ‖2 * m + 1 + 1‖ + 3) := by
            gcongr
            exact le_trans hlen' (mul_le_mul_of_nonneg_left (nodeCost_mono hE) zero_le)
        _ = (‖m‖ + 1 + 1) * nodeCost N B (6 * ‖2 * m + 1 + 1‖ + 3) := by ring

/-- **`succCode` is a derivation of `{bnum z + 1 = bnum (z + 1)}`**, in every model, over any sound table. -/
theorem succCode_proof {tbl N B : V} (htbl : NumTableOK tbl N B) (z : V) :
    DerivationOf TAct (succCode tbl z) (sing (succFact z)) :=
  (succGraph_sound htbl z _ (succCode_graph tbl z)).1

/-- **`dlen (succCode tbl z) ≤ (‖z‖ + 1) · (N + 700·B·(6‖z + 1‖ + 3))`** — quadratic in the bit length. -/
theorem dlen_succCode_le {tbl N B : V} (htbl : NumTableOK tbl N B) (z : V) :
    dlen TAct (succCode tbl z) ≤ (‖z‖ + 1) * nodeCost N B (6 * ‖z + 1‖ + 3) :=
  (succGraph_sound htbl z _ (succCode_graph tbl z)).2

/-- The `sLemma` step of the successor fact is applicable (`LemmaOK`), … -/
theorem lemmaOK_succ {tbl N B : V} (htbl : NumTableOK tbl N B) (z : V) :
    LemmaOK (sLemma (succFact z) (succCode tbl z)) := by
  refine ⟨?_, ?_⟩
  · show IsFormula LAct (π₁ (π₂ (sLemma (succFact z) (succCode tbl z))))
    simp only [sLemma, pi₂_pair, pi₁_pair]
    exact isFormula_succFact z
  · show DerivationOf TAct (π₂ (π₂ (sLemma (succFact z) (succCode tbl z)))) (insert (π₁ (π₂ (sLemma (succFact z) (succCode tbl z)))) 0)
    simp only [sLemma, pi₂_pair, pi₁_pair]
    exact succCode_proof htbl z

/-- … and its cost: `stepCost N' E Γ (sLemma A dA) = dlen dA + 2|Γ| + 2|A| + 2` with `dlen dA ≤ succBound`. -/
theorem stepCost_lemma_succ {tbl N B N' E Γ : V} (htbl : NumTableOK tbl N B) (z : V) :
    stepCost N' E Γ (sLemma (succFact z) (succCode tbl z)) ≤
      succBound N B z + 2 * setLen LAct Γ + 2 * formulaLen LAct (succFact z) + 2 := by
  rw [stepCost_tag7 (by simp [sTag, sLemma])]
  simp only [sLemA, sLemD, sLemma, pi₂_pair, pi₁_pair]
  gcongr
  exact dlen_succCode_le htbl z

end succSound


/-! ## 7. Addition: `addFact a b := bnum a + bnum b = bnum (a + b)`

`addCode tbl a b` — a `Fixpoint` on `⟪a, b, d⟫`: `a = 0`/`b = 0` by `zeroAdd`/`addZero`; `a = 1` by
`oneAdd` from `succCode b`; `b = 1` IS `succCode a` (`bnum 1 = 𝟏`); `a, b ≥ 2` by the four bit rows
from the fact for `(a / 2, b / 2)` — and, for `11`, the carry `succCode (a/2 + b/2)`. A chain of
`‖a‖ + 1` add-nodes, each with at most one successor chain: `(‖a‖ + 1)(‖a + b‖ + 2)` nodes. -/

section add

/-- `addFact a b := bnum a + bnum b = bnum (a + b)`. -/
noncomputable def addFact (a b : V) : V := eqFact (bnum a ^+ bnum b) (bnum (a + b))
noncomputable def addFactDef : 𝚺₁.Semisentence 3 := .mkSigma
  “y a b. ∃ ta, !bnumGraph ta a ∧ ∃ tb, !bnumGraph tb b ∧ ∃ s, !qqAddGraph s ta tb ∧ ∃ t, !bnumGraph t (a + b) ∧
    !eqFactDef y s t”
instance addFact_defined : 𝚺₁-Function₂ (addFact : V → V → V) via addFactDef := .mk fun v ↦ by
  simp [addFactDef, bnum.defined.iff, qqAdd_defined.iff, eqFact_defined.iff, addFact]
instance addFact_definable : 𝚺₁-Function₂ (addFact : V → V → V) := addFact_defined.to_definable

lemma isFormula_addFact (a b : V) : IsFormula LAct (addFact a b) :=
  isFormula_eqFact (by simp [isSemiterm_bnum_LAct]) (isSemiterm_bnum_LAct 0 _)

lemma addFact_zero_left (b : V) : addFact 0 b = eqFact ((𝟎 : V) ^+ bnum b) (bnum b) := by
  unfold addFact; rw [bnum_zero, zero_add]
lemma addFact_zero_right (a : V) : addFact a 0 = eqFact (bnum a ^+ (𝟎 : V)) (bnum a) := by
  unfold addFact; rw [bnum_zero, add_zero]
lemma addFact_one_left (b : V) : addFact 1 b = eqFact ((𝟏 : V) ^+ bnum b) (bnum (b + 1)) := by
  unfold addFact; rw [bnum_one, add_comm]
lemma addFact_one_right (a : V) : addFact a 1 = succFact a := by
  unfold addFact succFact; rw [bnum_one]
lemma addFact_bit00 {a' b' : V} (ha : 1 ≤ a') (hb : 1 ≤ b') :
    addFact (2 * a') (2 * b') = eqFact (((𝟐 : V) ^* bnum a') ^+ (𝟐 ^* bnum b')) (𝟐 ^* bnum (a' + b')) := by
  unfold addFact
  rw [bnum_two_mul ha, bnum_two_mul hb, show 2 * a' + 2 * b' = 2 * (a' + b') by ring, bnum_two_mul (le_trans ha le_self_add)]
lemma addFact_bit01 {a' b' : V} (ha : 1 ≤ a') (hb : 1 ≤ b') :
    addFact (2 * a') (2 * b' + 1) = eqFact (((𝟐 : V) ^* bnum a') ^+ ((𝟐 ^* bnum b') ^+ 𝟏)) ((𝟐 ^* bnum (a' + b')) ^+ 𝟏) := by
  unfold addFact
  rw [bnum_two_mul ha, bnum_two_mul_add_one hb, show 2 * a' + (2 * b' + 1) = 2 * (a' + b') + 1 by ring,
    bnum_two_mul_add_one (le_trans ha le_self_add)]
lemma addFact_bit10 {a' b' : V} (ha : 1 ≤ a') (hb : 1 ≤ b') :
    addFact (2 * a' + 1) (2 * b') = eqFact ((((𝟐 : V) ^* bnum a') ^+ 𝟏) ^+ (𝟐 ^* bnum b')) ((𝟐 ^* bnum (a' + b')) ^+ 𝟏) := by
  unfold addFact
  rw [bnum_two_mul_add_one ha, bnum_two_mul hb, show 2 * a' + 1 + 2 * b' = 2 * (a' + b') + 1 by ring,
    bnum_two_mul_add_one (le_trans ha le_self_add)]
lemma addFact_bit11 {a' b' : V} (ha : 1 ≤ a') (hb : 1 ≤ b') :
    addFact (2 * a' + 1) (2 * b' + 1) =
      eqFact ((((𝟐 : V) ^* bnum a') ^+ 𝟏) ^+ ((𝟐 ^* bnum b') ^+ 𝟏)) (𝟐 ^* bnum (a' + b' + 1)) := by
  unfold addFact
  rw [bnum_two_mul_add_one ha, bnum_two_mul_add_one hb, show 2 * a' + 1 + (2 * b' + 1) = 2 * (a' + b' + 1) by ring,
    bnum_two_mul (le_trans ha (le_trans le_self_add le_self_add))]

/-- `|addFact a b| ≤ B·E` once `B ≥ |Peq|` and `E ≥ 12‖a + b‖ + 3`. -/
lemma formulaLen_addFact_le {B E a b : V} (hPeq : formulaLen LAct (Peq : V) ≤ B) (hE : 12 * ‖a + b‖ + 3 ≤ E) :
    formulaLen LAct (addFact a b) ≤ B * E := by
  have hE1 : 1 ≤ E := le_trans (by norm_num) (le_trans le_add_self hE)
  have ha := length_monotone (le_self_add : a ≤ a + b)
  have hb := length_monotone (le_add_self : b ≤ a + b)
  have h1 : termLen LAct (bnum a ^+ bnum b) ≤ E := by
    rw [termLen_qqAdd isFunc_LAct_addIndex (isSemiterm_bnum_LAct 0 a).isUTerm (isSemiterm_bnum_LAct 0 b).isUTerm]
    calc termLen LAct (bnum a) + termLen LAct (bnum b) + 1 ≤ (6 * ‖a‖ + 1) + (6 * ‖b‖ + 1) + 1 := by
          gcongr <;> exact termLen_bnum_le _
      _ ≤ (6 * ‖a + b‖ + 1) + (6 * ‖a + b‖ + 1) + 1 := by gcongr
      _ = 12 * ‖a + b‖ + 3 := by ring
      _ ≤ E := hE
  have h2 : termLen LAct (bnum (a + b)) ≤ E :=
    le_trans (termLen_bnum_le _) (le_trans (by
      calc 6 * ‖a + b‖ + 1 ≤ 12 * ‖a + b‖ + 1 := by gcongr; norm_num
        _ ≤ 12 * ‖a + b‖ + 3 := by gcongr; norm_num) hE)
  exact le_trans (formulaLen_eqFact_le hE1 (by simp [isSemiterm_bnum_LAct]) (isSemiterm_bnum_LAct 0 _) h1 h2)
    (mul_le_mul_of_nonneg_right hPeq zero_le)

lemma termLen_bnum_le_E' {x s E : V} (hx : x ≤ s) (hE : 12 * ‖s‖ + 3 ≤ E) : termLen LAct (bnum x) ≤ E :=
  le_trans (termLen_bnum_le x) (le_trans (by
    have := length_monotone hx
    calc 6 * ‖x‖ + 1 ≤ 6 * ‖s‖ + 1 := by gcongr
      _ ≤ 12 * ‖s‖ + 3 := by gcongr <;> norm_num) hE)

lemma succE_le_addE {x s : V} (hx : x + 1 ≤ s) : 6 * ‖x + 1‖ + 3 ≤ 12 * ‖s‖ + 3 := by
  have := length_monotone hx
  calc 6 * ‖x + 1‖ + 3 ≤ 6 * ‖s‖ + 3 := by gcongr
    _ ≤ 12 * ‖s‖ + 3 := by gcongr; norm_num

lemma one_le_addE {s : V} : 1 ≤ 12 * ‖s‖ + 3 := le_trans (by norm_num) le_add_self

lemma d_lt_step2 (tbl i F₁ d₁ F₂ d₂ ev A : V) : d₁ < step2 tbl i F₁ d₁ F₂ d₂ ev A :=
  lt_trans (d_lt_wkRule _ _) (d₁_lt_cutRule _ _ _ _)

namespace AddG

/-- The graph: `⟪a, b, d⟫` where `d` is the addition-fact derivation of `(a, b)`. -/
def Phi (tbl : V) (C : Set V) (pr : V) : Prop :=
  ∃ a b d, pr = ⟪a, b, d⟫ ∧
  ( (a = 0 ∧ d = step0 tbl 0 (vecOf [bnum b]) (addFact 0 b)) ∨
    (1 ≤ a ∧ b = 0 ∧ d = step0 tbl 1 (vecOf [bnum a]) (addFact a 0)) ∨
    (a = 1 ∧ 1 ≤ b ∧ d = step1 tbl 4 (succFact b) (succCode tbl b) (vecOf [bnum (b + 1), bnum b]) (addFact 1 b)) ∨
    (2 ≤ a ∧ b = 1 ∧ d = succCode tbl a) ∨
    (∃ a' b' d', 1 ≤ a' ∧ 1 ≤ b' ∧ a = 2 * a' ∧ b = 2 * b' ∧ ⟪a', b', d'⟫ ∈ C ∧
      d = step1 tbl 7 (addFact a' b') d' (vecOf [bnum (a' + b'), bnum b', bnum a']) (addFact a b)) ∨
    (∃ a' b' d', 1 ≤ a' ∧ 1 ≤ b' ∧ a = 2 * a' ∧ b = 2 * b' + 1 ∧ ⟪a', b', d'⟫ ∈ C ∧
      d = step1 tbl 8 (addFact a' b') d' (vecOf [bnum (a' + b'), bnum b', bnum a']) (addFact a b)) ∨
    (∃ a' b' d', 1 ≤ a' ∧ 1 ≤ b' ∧ a = 2 * a' + 1 ∧ b = 2 * b' ∧ ⟪a', b', d'⟫ ∈ C ∧
      d = step1 tbl 9 (addFact a' b') d' (vecOf [bnum (a' + b'), bnum b', bnum a']) (addFact a b)) ∨
    (∃ a' b' d', 1 ≤ a' ∧ 1 ≤ b' ∧ a = 2 * a' + 1 ∧ b = 2 * b' + 1 ∧ ⟪a', b', d'⟫ ∈ C ∧
      d = step2 tbl 10 (addFact a' b') d' (succFact (a' + b')) (succCode tbl (a' + b'))
        (vecOf [bnum (a' + b' + 1), bnum (a' + b'), bnum b', bnum a']) (addFact a b)) )

noncomputable def blueprint : Fixpoint.Blueprint 1 := ⟨.mkDelta
  (.mkSigma “pr C tbl.
    ∃ a <⁺ pr, ∃ q <⁺ pr, !pairDef pr a q ∧ ∃ b <⁺ q, ∃ d <⁺ q, !pairDef q b d ∧
    ( (a = 0 ∧ ∃ t, !bnumGraph t b ∧ ∃ ev, !adjoinDef ev t 0 ∧ ∃ A, !addFactDef A 0 b ∧
        ∃ x, !step0Def x tbl 0 ev A ∧ d = x) ∨
      (1 ≤ a ∧ b = 0 ∧ ∃ t, !bnumGraph t a ∧ ∃ ev, !adjoinDef ev t 0 ∧ ∃ A, !addFactDef A a 0 ∧
        ∃ x, !step0Def x tbl 1 ev A ∧ d = x) ∨
      (a = 1 ∧ 1 ≤ b ∧ ∃ F, !succFactDef F b ∧ ∃ dF, !succCodeDef dF tbl b ∧ ∃ t1, !bnumGraph t1 (b + 1) ∧
        ∃ t0, !bnumGraph t0 b ∧ ∃ v0, !adjoinDef v0 t0 0 ∧ ∃ ev, !adjoinDef ev t1 v0 ∧ ∃ A, !addFactDef A 1 b ∧
        ∃ x, !step1Def x tbl 4 F dF ev A ∧ d = x) ∨
      (2 ≤ a ∧ b = 1 ∧ ∃ x, !succCodeDef x tbl a ∧ d = x) ∨
      (∃ a' < a, ∃ b' < b, ∃ d' < d, 1 ≤ a' ∧ 1 ≤ b' ∧ a = 2 * a' ∧ b = 2 * b' ∧
        (∃ q', !pairDef q' b' d' ∧ :⟪a', q'⟫:∈ C) ∧ ∃ F, !addFactDef F a' b' ∧
        ∃ t2, !bnumGraph t2 (a' + b') ∧ ∃ t1, !bnumGraph t1 b' ∧ ∃ t0, !bnumGraph t0 a' ∧
        ∃ v0, !adjoinDef v0 t0 0 ∧ ∃ v1, !adjoinDef v1 t1 v0 ∧ ∃ ev, !adjoinDef ev t2 v1 ∧
        ∃ A, !addFactDef A a b ∧ ∃ x, !step1Def x tbl 7 F d' ev A ∧ d = x) ∨
      (∃ a' < a, ∃ b' < b, ∃ d' < d, 1 ≤ a' ∧ 1 ≤ b' ∧ a = 2 * a' ∧ b = 2 * b' + 1 ∧
        (∃ q', !pairDef q' b' d' ∧ :⟪a', q'⟫:∈ C) ∧ ∃ F, !addFactDef F a' b' ∧
        ∃ t2, !bnumGraph t2 (a' + b') ∧ ∃ t1, !bnumGraph t1 b' ∧ ∃ t0, !bnumGraph t0 a' ∧
        ∃ v0, !adjoinDef v0 t0 0 ∧ ∃ v1, !adjoinDef v1 t1 v0 ∧ ∃ ev, !adjoinDef ev t2 v1 ∧
        ∃ A, !addFactDef A a b ∧ ∃ x, !step1Def x tbl 8 F d' ev A ∧ d = x) ∨
      (∃ a' < a, ∃ b' < b, ∃ d' < d, 1 ≤ a' ∧ 1 ≤ b' ∧ a = 2 * a' + 1 ∧ b = 2 * b' ∧
        (∃ q', !pairDef q' b' d' ∧ :⟪a', q'⟫:∈ C) ∧ ∃ F, !addFactDef F a' b' ∧
        ∃ t2, !bnumGraph t2 (a' + b') ∧ ∃ t1, !bnumGraph t1 b' ∧ ∃ t0, !bnumGraph t0 a' ∧
        ∃ v0, !adjoinDef v0 t0 0 ∧ ∃ v1, !adjoinDef v1 t1 v0 ∧ ∃ ev, !adjoinDef ev t2 v1 ∧
        ∃ A, !addFactDef A a b ∧ ∃ x, !step1Def x tbl 9 F d' ev A ∧ d = x) ∨
      (∃ a' < a, ∃ b' < b, ∃ d' < d, 1 ≤ a' ∧ 1 ≤ b' ∧ a = 2 * a' + 1 ∧ b = 2 * b' + 1 ∧
        (∃ q', !pairDef q' b' d' ∧ :⟪a', q'⟫:∈ C) ∧ ∃ F, !addFactDef F a' b' ∧
        ∃ G, !succFactDef G (a' + b') ∧ ∃ dG, !succCodeDef dG tbl (a' + b') ∧
        ∃ t3, !bnumGraph t3 (a' + b' + 1) ∧ ∃ t2, !bnumGraph t2 (a' + b') ∧ ∃ t1, !bnumGraph t1 b' ∧
        ∃ t0, !bnumGraph t0 a' ∧ ∃ v0, !adjoinDef v0 t0 0 ∧ ∃ v1, !adjoinDef v1 t1 v0 ∧
        ∃ v2, !adjoinDef v2 t2 v1 ∧ ∃ ev, !adjoinDef ev t3 v2 ∧
        ∃ A, !addFactDef A a b ∧ ∃ x, !step2Def x tbl 10 F d' G dG ev A ∧ d = x) )”)
  (.mkPi “pr C tbl.
    ∃ a <⁺ pr, ∃ q <⁺ pr, !pairDef pr a q ∧ ∃ b <⁺ q, ∃ d <⁺ q, !pairDef q b d ∧
    ( (a = 0 ∧ ∀ t, !bnumGraph t b → ∀ ev, !adjoinDef ev t 0 → ∀ A, !addFactDef A 0 b →
        ∀ x, !step0Def x tbl 0 ev A → d = x) ∨
      (1 ≤ a ∧ b = 0 ∧ ∀ t, !bnumGraph t a → ∀ ev, !adjoinDef ev t 0 → ∀ A, !addFactDef A a 0 →
        ∀ x, !step0Def x tbl 1 ev A → d = x) ∨
      (a = 1 ∧ 1 ≤ b ∧ ∀ F, !succFactDef F b → ∀ dF, !succCodeDef dF tbl b → ∀ t1, !bnumGraph t1 (b + 1) →
        ∀ t0, !bnumGraph t0 b → ∀ v0, !adjoinDef v0 t0 0 → ∀ ev, !adjoinDef ev t1 v0 → ∀ A, !addFactDef A 1 b →
        ∀ x, !step1Def x tbl 4 F dF ev A → d = x) ∨
      (2 ≤ a ∧ b = 1 ∧ ∀ x, !succCodeDef x tbl a → d = x) ∨
      (∃ a' < a, ∃ b' < b, ∃ d' < d, 1 ≤ a' ∧ 1 ≤ b' ∧ a = 2 * a' ∧ b = 2 * b' ∧
        (∀ q', !pairDef q' b' d' → :⟪a', q'⟫:∈ C) ∧ ∀ F, !addFactDef F a' b' →
        ∀ t2, !bnumGraph t2 (a' + b') → ∀ t1, !bnumGraph t1 b' → ∀ t0, !bnumGraph t0 a' →
        ∀ v0, !adjoinDef v0 t0 0 → ∀ v1, !adjoinDef v1 t1 v0 → ∀ ev, !adjoinDef ev t2 v1 →
        ∀ A, !addFactDef A a b → ∀ x, !step1Def x tbl 7 F d' ev A → d = x) ∨
      (∃ a' < a, ∃ b' < b, ∃ d' < d, 1 ≤ a' ∧ 1 ≤ b' ∧ a = 2 * a' ∧ b = 2 * b' + 1 ∧
        (∀ q', !pairDef q' b' d' → :⟪a', q'⟫:∈ C) ∧ ∀ F, !addFactDef F a' b' →
        ∀ t2, !bnumGraph t2 (a' + b') → ∀ t1, !bnumGraph t1 b' → ∀ t0, !bnumGraph t0 a' →
        ∀ v0, !adjoinDef v0 t0 0 → ∀ v1, !adjoinDef v1 t1 v0 → ∀ ev, !adjoinDef ev t2 v1 →
        ∀ A, !addFactDef A a b → ∀ x, !step1Def x tbl 8 F d' ev A → d = x) ∨
      (∃ a' < a, ∃ b' < b, ∃ d' < d, 1 ≤ a' ∧ 1 ≤ b' ∧ a = 2 * a' + 1 ∧ b = 2 * b' ∧
        (∀ q', !pairDef q' b' d' → :⟪a', q'⟫:∈ C) ∧ ∀ F, !addFactDef F a' b' →
        ∀ t2, !bnumGraph t2 (a' + b') → ∀ t1, !bnumGraph t1 b' → ∀ t0, !bnumGraph t0 a' →
        ∀ v0, !adjoinDef v0 t0 0 → ∀ v1, !adjoinDef v1 t1 v0 → ∀ ev, !adjoinDef ev t2 v1 →
        ∀ A, !addFactDef A a b → ∀ x, !step1Def x tbl 9 F d' ev A → d = x) ∨
      (∃ a' < a, ∃ b' < b, ∃ d' < d, 1 ≤ a' ∧ 1 ≤ b' ∧ a = 2 * a' + 1 ∧ b = 2 * b' + 1 ∧
        (∀ q', !pairDef q' b' d' → :⟪a', q'⟫:∈ C) ∧ ∀ F, !addFactDef F a' b' →
        ∀ G, !succFactDef G (a' + b') → ∀ dG, !succCodeDef dG tbl (a' + b') →
        ∀ t3, !bnumGraph t3 (a' + b' + 1) → ∀ t2, !bnumGraph t2 (a' + b') → ∀ t1, !bnumGraph t1 b' →
        ∀ t0, !bnumGraph t0 a' → ∀ v0, !adjoinDef v0 t0 0 → ∀ v1, !adjoinDef v1 t1 v0 →
        ∀ v2, !adjoinDef v2 t2 v1 → ∀ ev, !adjoinDef ev t3 v2 →
        ∀ A, !addFactDef A a b → ∀ x, !step2Def x tbl 10 F d' G dG ev A → d = x) )”)⟩

/-- `Phi` with the bounds the blueprint carries. -/
private lemma phi_iff (tbl C pr : V) :
    Phi tbl {x | x ∈ C} pr ↔
    ∃ a ≤ pr, ∃ q ≤ pr, pr = ⟪a, q⟫ ∧ ∃ b ≤ q, ∃ d ≤ q, q = ⟪b, d⟫ ∧
    ( (a = 0 ∧ d = step0 tbl 0 (vecOf [bnum b]) (addFact 0 b)) ∨
      (1 ≤ a ∧ b = 0 ∧ d = step0 tbl 1 (vecOf [bnum a]) (addFact a 0)) ∨
      (a = 1 ∧ 1 ≤ b ∧ d = step1 tbl 4 (succFact b) (succCode tbl b) (vecOf [bnum (b + 1), bnum b]) (addFact 1 b)) ∨
      (2 ≤ a ∧ b = 1 ∧ d = succCode tbl a) ∨
      (∃ a' < a, ∃ b' < b, ∃ d' < d, 1 ≤ a' ∧ 1 ≤ b' ∧ a = 2 * a' ∧ b = 2 * b' ∧ ⟪a', b', d'⟫ ∈ C ∧
        d = step1 tbl 7 (addFact a' b') d' (vecOf [bnum (a' + b'), bnum b', bnum a']) (addFact a b)) ∨
      (∃ a' < a, ∃ b' < b, ∃ d' < d, 1 ≤ a' ∧ 1 ≤ b' ∧ a = 2 * a' ∧ b = 2 * b' + 1 ∧ ⟪a', b', d'⟫ ∈ C ∧
        d = step1 tbl 8 (addFact a' b') d' (vecOf [bnum (a' + b'), bnum b', bnum a']) (addFact a b)) ∨
      (∃ a' < a, ∃ b' < b, ∃ d' < d, 1 ≤ a' ∧ 1 ≤ b' ∧ a = 2 * a' + 1 ∧ b = 2 * b' ∧ ⟪a', b', d'⟫ ∈ C ∧
        d = step1 tbl 9 (addFact a' b') d' (vecOf [bnum (a' + b'), bnum b', bnum a']) (addFact a b)) ∨
      (∃ a' < a, ∃ b' < b, ∃ d' < d, 1 ≤ a' ∧ 1 ≤ b' ∧ a = 2 * a' + 1 ∧ b = 2 * b' + 1 ∧ ⟪a', b', d'⟫ ∈ C ∧
        d = step2 tbl 10 (addFact a' b') d' (succFact (a' + b')) (succCode tbl (a' + b'))
          (vecOf [bnum (a' + b' + 1), bnum (a' + b'), bnum b', bnum a']) (addFact a b)) ) := by
  constructor
  · rintro ⟨a, b, d, rfl, h⟩
    refine ⟨a, le_pair_left _ _, ⟪b, d⟫, le_pair_right _ _, rfl, b, le_pair_left _ _, d, le_pair_right _ _, rfl, ?_⟩
    rcases h with h | h | h | h | ⟨a', b', d', ha, hb, rfl, rfl, hC, rfl⟩ | ⟨a', b', d', ha, hb, rfl, rfl, hC, rfl⟩ |
      ⟨a', b', d', ha, hb, rfl, rfl, hC, rfl⟩ | ⟨a', b', d', ha, hb, rfl, rfl, hC, rfl⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨a', Bnum.lt_two_mul ha, b', Bnum.lt_two_mul hb, d', SuccG.d_lt_step1 _ _ _ _ _ _, ha, hb, rfl, rfl, hC, rfl⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨a', Bnum.lt_two_mul ha, b', Bnum.lt_two_mul_add_one hb, d', SuccG.d_lt_step1 _ _ _ _ _ _, ha, hb, rfl, rfl, hC, rfl⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨a', Bnum.lt_two_mul_add_one ha, b', Bnum.lt_two_mul hb, d', SuccG.d_lt_step1 _ _ _ _ _ _, ha, hb, rfl, rfl, hC, rfl⟩))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨a', Bnum.lt_two_mul_add_one ha, b', Bnum.lt_two_mul_add_one hb, d', d_lt_step2 _ _ _ _ _ _ _ _, ha, hb, rfl, rfl, hC, rfl⟩))))))
  · rintro ⟨a, _, q, _, rfl, b, _, d, _, rfl, h⟩
    refine ⟨a, b, d, rfl, ?_⟩
    rcases h with h | h | h | h | ⟨a', _, b', _, d', _, ha, hb, rfl, rfl, hC, rfl⟩ | ⟨a', _, b', _, d', _, ha, hb, rfl, rfl, hC, rfl⟩ |
      ⟨a', _, b', _, d', _, ha, hb, rfl, rfl, hC, rfl⟩ | ⟨a', _, b', _, d', _, ha, hb, rfl, rfl, hC, rfl⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨a', b', d', ha, hb, rfl, rfl, hC, rfl⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨a', b', d', ha, hb, rfl, rfl, hC, rfl⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨a', b', d', ha, hb, rfl, rfl, hC, rfl⟩))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨a', b', d', ha, hb, rfl, rfl, hC, rfl⟩))))))

set_option maxHeartbeats 3000000 in
noncomputable def construction : Fixpoint.Construction V blueprint where
  Φ := fun v ↦ Phi (v 0)
  defined := .mk <| by
    constructor
    · intro v
      simp [blueprint, addFact_defined.iff, succFact_defined.iff, succCode_defined.iff, bnum.defined.iff,
        step0_defined.iff, step1_defined.iff, step2_defined.iff, numeral_eq_natCast]
    · intro v
      symm
      simpa [blueprint, addFact_defined.iff, succFact_defined.iff, succCode_defined.iff, bnum.defined.iff,
        step0_defined.iff, step1_defined.iff, step2_defined.iff, numeral_eq_natCast] using phi_iff (v 2) (v 1) (v 0)
  monotone := by
    rintro C C' hC _ pr ⟨a, b, d, rfl, h⟩
    refine ⟨a, b, d, rfl, ?_⟩
    rcases h with h | h | h | h | ⟨a', b', d', ha, hb, rfl, rfl, hC', rfl⟩ | ⟨a', b', d', ha, hb, rfl, rfl, hC', rfl⟩ |
      ⟨a', b', d', ha, hb, rfl, rfl, hC', rfl⟩ | ⟨a', b', d', ha, hb, rfl, rfl, hC', rfl⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨a', b', d', ha, hb, rfl, rfl, hC hC', rfl⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨a', b', d', ha, hb, rfl, rfl, hC hC', rfl⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨a', b', d', ha, hb, rfl, rfl, hC hC', rfl⟩))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨a', b', d', ha, hb, rfl, rfl, hC hC', rfl⟩))))))

instance : construction.Finite V where
  finite := by
    rintro C _ pr ⟨a, b, d, rfl, h⟩
    rcases h with h | h | h | h | ⟨a', b', d', ha, hb, rfl, rfl, hC', rfl⟩ | ⟨a', b', d', ha, hb, rfl, rfl, hC', rfl⟩ |
      ⟨a', b', d', ha, hb, rfl, rfl, hC', rfl⟩ | ⟨a', b', d', ha, hb, rfl, rfl, hC', rfl⟩
    · exact ⟨0, a, b, d, rfl, Or.inl h⟩
    · exact ⟨0, a, b, d, rfl, Or.inr (Or.inl h)⟩
    · exact ⟨0, a, b, d, rfl, Or.inr (Or.inr (Or.inl h))⟩
    · exact ⟨0, a, b, d, rfl, Or.inr (Or.inr (Or.inr (Or.inl h)))⟩
    · exact ⟨⟪a', b', d'⟫ + 1, _, _, _, rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨a', b', d', ha, hb, rfl, rfl, ⟨hC', lt_add_one _⟩, rfl⟩))))⟩
    · exact ⟨⟪a', b', d'⟫ + 1, _, _, _, rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨a', b', d', ha, hb, rfl, rfl, ⟨hC', lt_add_one _⟩, rfl⟩)))))⟩
    · exact ⟨⟪a', b', d'⟫ + 1, _, _, _, rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨a', b', d', ha, hb, rfl, rfl, ⟨hC', lt_add_one _⟩, rfl⟩))))))⟩
    · exact ⟨⟪a', b', d'⟫ + 1, _, _, _, rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨a', b', d', ha, hb, rfl, rfl, ⟨hC', lt_add_one _⟩, rfl⟩))))))⟩

end AddG

/-- `AddGraph tbl a b d`: `d` is the addition-fact derivation of `(a, b)` over the table `tbl`. -/
def AddGraph (tbl a b d : V) : Prop := AddG.construction.Fixpoint ![tbl] ⟪a, b, d⟫

noncomputable def addGraphDef : 𝚺₁.Semisentence 4 := .mkSigma
  “tbl a b d. ∃ q, !pairDef q b d ∧ ∃ p, !pairDef p a q ∧ !AddG.blueprint.fixpointDef p tbl”

instance addGraph_defined : 𝚺₁-Relation₄ (AddGraph : V → V → V → V → Prop) via addGraphDef := .mk fun v ↦ by
  simp [addGraphDef, AddG.construction.eval_fixpointDef, AddGraph]
  have e : (fun _ : Fin 1 ↦ v 0) = ![v 0] := by funext i; fin_cases i; rfl
  rw [e]
instance addGraph_definable : 𝚺₁-Relation₄ (AddGraph : V → V → V → V → Prop) := addGraph_defined.to_definable

lemma AddGraph.case_iff {tbl a b d : V} :
    AddGraph tbl a b d ↔
    (a = 0 ∧ d = step0 tbl 0 (vecOf [bnum b]) (addFact 0 b)) ∨
    (1 ≤ a ∧ b = 0 ∧ d = step0 tbl 1 (vecOf [bnum a]) (addFact a 0)) ∨
    (a = 1 ∧ 1 ≤ b ∧ d = step1 tbl 4 (succFact b) (succCode tbl b) (vecOf [bnum (b + 1), bnum b]) (addFact 1 b)) ∨
    (2 ≤ a ∧ b = 1 ∧ d = succCode tbl a) ∨
    (∃ a' b' d', 1 ≤ a' ∧ 1 ≤ b' ∧ a = 2 * a' ∧ b = 2 * b' ∧ AddGraph tbl a' b' d' ∧
      d = step1 tbl 7 (addFact a' b') d' (vecOf [bnum (a' + b'), bnum b', bnum a']) (addFact a b)) ∨
    (∃ a' b' d', 1 ≤ a' ∧ 1 ≤ b' ∧ a = 2 * a' ∧ b = 2 * b' + 1 ∧ AddGraph tbl a' b' d' ∧
      d = step1 tbl 8 (addFact a' b') d' (vecOf [bnum (a' + b'), bnum b', bnum a']) (addFact a b)) ∨
    (∃ a' b' d', 1 ≤ a' ∧ 1 ≤ b' ∧ a = 2 * a' + 1 ∧ b = 2 * b' ∧ AddGraph tbl a' b' d' ∧
      d = step1 tbl 9 (addFact a' b') d' (vecOf [bnum (a' + b'), bnum b', bnum a']) (addFact a b)) ∨
    (∃ a' b' d', 1 ≤ a' ∧ 1 ≤ b' ∧ a = 2 * a' + 1 ∧ b = 2 * b' + 1 ∧ AddGraph tbl a' b' d' ∧
      d = step2 tbl 10 (addFact a' b') d' (succFact (a' + b')) (succCode tbl (a' + b'))
        (vecOf [bnum (a' + b' + 1), bnum (a' + b'), bnum b', bnum a']) (addFact a b)) :=
  Iff.trans AddG.construction.case (by simp [AddG.construction, AddG.Phi, AddGraph])

end add

end ArithS
