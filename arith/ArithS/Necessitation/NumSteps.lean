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

/-- `∀ x : V, 0 + x = x`. -/
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

/-- `∀ x : V, x + 0 = x`. -/
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

/-- `(1 : V) + 1 = 2 * 1`. -/
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

/-- `∀ x : V, 1 + 2 * x = 2 * x + 1`. -/
noncomputable def nOneAddEvenB : ArithmeticSemisentence 1 := eqO (addO oneO (twoMul #0)) (twoMulOne #0)
noncomputable def nOneAddEven : ArithmeticSentence := ∀¹* nOneAddEvenB

lemma models_nOneAddEven : V↓[ℒₒᵣ] ⊧ nOneAddEven ↔ (∀ x : V, 1 + 2 * x = 2 * x + 1) := by
  simp [nOneAddEven, nOneAddEvenB, eqO, addO, leF, ltF, twoMul, twoMulOne, oneO, zeroO, models_iff,
    Matrix.vecForall_iff, one_add_one_eq_two, le_def]

theorem pa_proves_nOneAddEven : 𝗣𝗔 ⊢ nOneAddEven :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_nOneAddEven.mpr (fun x ↦ add_comm 1 (2 * x))

theorem lib_nOneAddEven : Lib nOneAddEven := Lib.of_pa pa_proves_nOneAddEven

noncomputable def nOneAddEven_as : List V := []
noncomputable def nOneAddEven_c : V := eqFact (𝟏 ^+ (𝟐 ^* bv 0)) ((𝟐 ^* bv 0) ^+ 𝟏)

lemma quote_nOneAddEvenB : (⌜Semiformula.lMap emb nOneAddEvenB⌝ : V) = impChain LAct nOneAddEven_as nOneAddEven_c := by
  unfold nOneAddEvenB nOneAddEven_as nOneAddEven_c
  simp only [quote_lMap_emb_imp, quote_eqO_closed, quote_leF_closed, quote_ltF_closed, quote_addO_closed,
    quote_twoMul_closed, quote_twoMulOne_closed, quote_oneO_closed, quote_zeroO_closed, quote_closed_bvar_m,
    impChain_cons, impChain_nil]
  try rfl

lemma inst_nOneAddEven {x : V} (hx : IsSemiterm LAct 0 x) :
    nOneAddEven_as.map (instOuter LAct [x]) = ([] : List V) ∧
    instOuter LAct [x] nOneAddEven_c = eqFact ((𝟏 : V) ^+ ((𝟐 : V) ^* x)) (((𝟐 : V) ^* x) ^+ (𝟏 : V)) := by
  have hes : ∀ e ∈ ([x] : List V), IsSemiterm LAct 0 e := by simp [hx]
  unfold nOneAddEven_as nOneAddEven_c
  simp only [List.map, List.length_cons, List.length_nil]
  simp (disch := (simp [bv]; try norm_num)) only [instOuter_eqFact _ hes, instOuter_leFact _ hes, instOuter_ltFact _ hes]
  simp (disch := (simp [bv]; try norm_num)) only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
    termSubst_qqAdd', termSubst_qqMul', termSubst_bv, termSubst_qqTwo', termSubst_qqOne', termSubst_qqZero',
    List.getD_cons_zero, List.getD_cons_succ]
  all_goals (constructor <;> first | rfl | trivial)

/-- `∀ x w : V, x + 1 = w → 1 + (2 * x + 1) = 2 * w`. -/
noncomputable def nOneAddOddB : ArithmeticSemisentence 2 := eqO (addO #0 oneO) #1 🡒 eqO (addO oneO (twoMulOne #0)) (twoMul #1)
noncomputable def nOneAddOdd : ArithmeticSentence := ∀¹* nOneAddOddB

lemma models_nOneAddOdd : V↓[ℒₒᵣ] ⊧ nOneAddOdd ↔ (∀ x w : V, x + 1 = w → 1 + (2 * x + 1) = 2 * w) := by
  simp [nOneAddOdd, nOneAddOddB, eqO, addO, leF, ltF, twoMul, twoMulOne, oneO, zeroO, models_iff,
    Matrix.vecForall_iff, one_add_one_eq_two, le_def]

theorem pa_proves_nOneAddOdd : 𝗣𝗔 ⊢ nOneAddOdd :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_nOneAddOdd.mpr (fun x w h ↦ by subst h; ring)

theorem lib_nOneAddOdd : Lib nOneAddOdd := Lib.of_pa pa_proves_nOneAddOdd

noncomputable def nOneAddOdd_as : List V := [eqFact (bv 0 ^+ 𝟏) (bv 1)]
noncomputable def nOneAddOdd_c : V := eqFact (𝟏 ^+ ((𝟐 ^* bv 0) ^+ 𝟏)) (𝟐 ^* bv 1)

lemma quote_nOneAddOddB : (⌜Semiformula.lMap emb nOneAddOddB⌝ : V) = impChain LAct nOneAddOdd_as nOneAddOdd_c := by
  unfold nOneAddOddB nOneAddOdd_as nOneAddOdd_c
  simp only [quote_lMap_emb_imp, quote_eqO_closed, quote_leF_closed, quote_ltF_closed, quote_addO_closed,
    quote_twoMul_closed, quote_twoMulOne_closed, quote_oneO_closed, quote_zeroO_closed, quote_closed_bvar_m,
    impChain_cons, impChain_nil]
  try rfl

lemma inst_nOneAddOdd {x w : V} (hx : IsSemiterm LAct 0 x) (hw : IsSemiterm LAct 0 w) :
    nOneAddOdd_as.map (instOuter LAct [w, x]) = ([eqFact (x ^+ (𝟏 : V)) w] : List V) ∧
    instOuter LAct [w, x] nOneAddOdd_c = eqFact ((𝟏 : V) ^+ (((𝟐 : V) ^* x) ^+ (𝟏 : V))) ((𝟐 : V) ^* w) := by
  have hes : ∀ e ∈ ([w, x] : List V), IsSemiterm LAct 0 e := by simp [hx, hw]
  unfold nOneAddOdd_as nOneAddOdd_c
  simp only [List.map, List.length_cons, List.length_nil]
  simp (disch := (simp [bv]; try norm_num)) only [instOuter_eqFact _ hes, instOuter_leFact _ hes, instOuter_ltFact _ hes]
  simp (disch := (simp [bv]; try norm_num)) only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
    termSubst_qqAdd', termSubst_qqMul', termSubst_bv, termSubst_qqTwo', termSubst_qqOne', termSubst_qqZero',
    List.getD_cons_zero, List.getD_cons_succ]
  all_goals (constructor <;> first | rfl | trivial)

/-- `∀ x : V, x = x`. -/
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

/-- `∀ x w : V, x + 1 = w → 2 * x + 1 + 1 = 2 * w`. -/
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

/-- `∀ x y z : V, x + y = z → 2 * x + 2 * y = 2 * z`. -/
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

/-- `∀ x y z : V, x + y = z → 2 * x + (2 * y + 1) = 2 * z + 1`. -/
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

/-- `∀ x y z : V, x + y = z → 2 * x + 1 + 2 * y = 2 * z + 1`. -/
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

/-- `∀ x y z w : V, x + y = z → z + 1 = w → 2 * x + 1 + (2 * y + 1) = 2 * w`. -/
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

/-- `∀ x y z : V, x + y = z → x ≤ z`. -/
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

/-- `∀ x w z : V, x + 1 = w → w ≤ z → x < z`. -/
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

/-- `∀ a b c s t u n : V, a + b = s → s + c = t → t + 1 = u → u ≤ n → a + b + c + 1 ≤ n`. -/
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

/-- `∀ a b s u n : V, a + b = s → s + 1 = u → u ≤ n → a + b + 1 ≤ n`. -/
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

/-- `∀ a u n : V, a + 1 = u → u ≤ n → a + 1 ≤ n`. -/
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

/-- `∀ a b s n : V, a + b = s → s ≤ n → a + b ≤ n`. -/
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

/-- `∀ x y w : V, x = y → y + 1 = w → x + 1 = w`. -/
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

/-- `∀ x y : V, x = y → x ≤ y`. -/
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

end ArithS
