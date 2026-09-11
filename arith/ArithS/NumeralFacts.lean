import ArithS.InstV

/-!
# ArithS.NumeralFacts — short `TAct` proofs of `numeral c ≤ bnumT k`

M4 item U9 step 2 (`Research/Notes/M4_BOUNDED_HBL/BRIEF.md` §6): the final meta step of PBLT
instantiates `TAct ⊢ ∀¹ (numeral k̂ ≤ #0 🡒 ψ)` at the binary numeral `bnumT k` and must
discharge the antecedent `numeral k̂ ≤ bnumT k` with a SHORT proof — short in `size k` (the bit
length), never in `k`.

**Statement** (`lenProvable_le_bnumT`): for every constant `c` there are `C₀ C₁` with
`LenProvable fbound (C₀ + C₁ · size k · size k) TAct ⌜numeral c ≤ bnumT k⌝` for all `k ≥ c`
(and the strict twin `lenProvable_lt_bnumT` for `k > c`). The sentence is
`leF (↑c) (Semiterm.lMap emb (bnumT k))` with `leF t u := t = u ⋎ t < u` (Foundation's `≤`
operator on unfolding, `leF_eq_operator`) and `↑c` Foundation's unary numeral of the constant
`c` in `LAct` (`lMap_emb_numeral`: the same as the `ℒₒᵣ` numeral embedded along `emb`, i.e.
`Template.numT c`). It is EXACTLY the antecedent of the instance of `∀¹ (leF ↑c #0 🡒 ψ)` at
`bnumT k` (`substs_leF_imp`), so a `Cut.lenProvable_mp` discharges it.

**Construction** (all META: `Derivation2` terms and `mlen`, through the bridges of `Cut.lean`):
1. Two uniform PA lemmas, `∀ x, c ≤ x → c ≤ 2x` and `∀ x, c ≤ x → c ≤ 2x + 1`, obtained by the
   completeness theorem (`Arithmetic.complete 𝗣𝗔`) and transported to `TAct` along `emb`
   (`CutV`'s pattern); their proof lengths are EXISTENTIAL constants
   (`lenProvable_of_provable`: a `TAct ⊢ σ` is a `Derivation2`, quoted back at its `mlen`).
2. Bit recursion on `k`: `bnumT k` is `2 · bnumT (k/2)` or `2 · bnumT (k/2) + 1`
   (`bnumT_even`/`bnumT_odd`); instantiate the relevant lemma at `bnumT (k/2)`
   (`InstV.lenProvable_inst_size`, cost `O(|instance| + size k)`) and cut with the fact for
   `k/2` (`lenProvable_mp`, cost `O(|sentence|)`). Each step costs a constant plus
   `O(size k)` — the current numeral has `≤ 6 · size k + 1` symbols — and there are `size k`
   steps: `O(size k)²` in total (`step_le`, then `lenProvable_le_bnumT`).
3. Base: `k ∈ [c, 2c + 1]` — finitely many TRUE Δ₀ sentences, each `TAct`-provable by
   completeness with SOME length; `C₀` is the maximum over the range (`base_le`).

Constants are never numeric (Cantor coding makes them astronomical); everything is packaged
existentially. `O(size k)²` is what the per-bit instantiation cost forces (every step pays at
least the current numeral's length); the brief's budget function absorbs it.
-/

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus
open LAct

/-! ### Syntax: the `≤`/`<` atoms, the terms `2·t` and `2·t + 1` -/

section atoms

variable {L : Language}

/-- `t ≤ u` as `t = u ⋎ t < u` — Foundation's `≤`-operator on unfolding (`leF_eq_operator`). -/
def leF [L.Eq] [L.LT] {ξ : Type*} {n : ℕ} (t u : Semiterm L ξ n) : Semiformula L ξ n :=
  Semiformula.rel Language.Eq.eq ![t, u] ⋎ Semiformula.rel Language.LT.lt ![t, u]

/-- `t < u` as the atom. -/
def ltF [L.LT] {ξ : Type*} {n : ℕ} (t u : Semiterm L ξ n) : Semiformula L ξ n :=
  Semiformula.rel Language.LT.lt ![t, u]

lemma leF_eq_operator [L.Eq] [L.LT] {ξ : Type*} {n : ℕ} (t u : Semiterm L ξ n) :
    leF t u = Semiformula.Operator.LE.le.operator ![t, u] :=
  (Semiformula.Operator.le_def t u).symm

lemma ltF_eq_operator [L.LT] {ξ : Type*} {n : ℕ} (t u : Semiterm L ξ n) :
    ltF t u = Semiformula.Operator.LT.lt.operator ![t, u] :=
  (Semiformula.Operator.lt_def t u).symm

/-- The term `(1 + 1) · t`. -/
def twoMul [L.One] [L.Add] [L.Mul] {ξ : Type*} {n : ℕ} (t : Semiterm L ξ n) : Semiterm L ξ n :=
  FirstOrder.Semiterm.func Language.Mul.mul
    ![FirstOrder.Semiterm.func Language.Add.add ![FirstOrder.Semiterm.func Language.One.one ![], FirstOrder.Semiterm.func Language.One.one ![]], t]

/-- The term `(1 + 1) · t + 1`. -/
def twoMulOne [L.One] [L.Add] [L.Mul] {ξ : Type*} {n : ℕ} (t : Semiterm L ξ n) : Semiterm L ξ n :=
  FirstOrder.Semiterm.func Language.Add.add ![twoMul t, FirstOrder.Semiterm.func Language.One.one ![]]

variable {ξ₁ ξ₂ : Type*} {n₁ n₂ : ℕ}

lemma rew_leF [L.Eq] [L.LT] (ω : Rew L ξ₁ n₁ ξ₂ n₂) (t u : Semiterm L ξ₁ n₁) :
    ω ▹ leF t u = leF (ω t) (ω u) := by
  simp [leF]

lemma rew_ltF [L.LT] (ω : Rew L ξ₁ n₁ ξ₂ n₂) (t u : Semiterm L ξ₁ n₁) :
    ω ▹ ltF t u = ltF (ω t) (ω u) := by
  simp [ltF]

lemma rew_twoMul [L.One] [L.Add] [L.Mul] (ω : Rew L ξ₁ n₁ ξ₂ n₂) (t : Semiterm L ξ₁ n₁) :
    ω (twoMul t) = twoMul (ω t) := by
  simp [twoMul, Rew.func]

lemma rew_twoMulOne [L.One] [L.Add] [L.Mul] (ω : Rew L ξ₁ n₁ ξ₂ n₂) (t : Semiterm L ξ₁ n₁) :
    ω (twoMulOne t) = twoMulOne (ω t) := by
  simp [twoMulOne, rew_twoMul, Rew.func]

end atoms

/-! ### `bnumT` in this syntax -/

section bnum

lemma oneT_eq : (‘1’ : ClosedSemiterm ℒₒᵣ 0) = FirstOrder.Semiterm.func Language.One.one ![] := by
  have e : (‘1’ : ClosedSemiterm ℒₒᵣ 0) = ↑(1 : ℕ) := by simp
  rw [e]
  change (Semiterm.Operator.numeral ℒₒᵣ 1).operator ![] = _
  rw [Semiterm.Operator.numeral_one]
  simp [Semiterm.Operator.operator, Semiterm.Operator.One.term_eq, Rew.func]

lemma mulT_eq (t u : ClosedSemiterm ℒₒᵣ 0) :
    (‘!!t * !!u’ : ClosedSemiterm ℒₒᵣ 0) = FirstOrder.Semiterm.func Language.Mul.mul ![t, u] := by
  rw [show (‘!!t * !!u’ : ClosedSemiterm ℒₒᵣ 0) = Semiterm.Operator.Mul.mul.operator ![t, u] from rfl]
  simp only [Semiterm.Operator.operator, Semiterm.Operator.Mul.term_eq, Rew.func]
  congr 1

lemma addT_eq (t u : ClosedSemiterm ℒₒᵣ 0) :
    (‘!!t + !!u’ : ClosedSemiterm ℒₒᵣ 0) = FirstOrder.Semiterm.func Language.Add.add ![t, u] := by
  rw [show (‘!!t + !!u’ : ClosedSemiterm ℒₒᵣ 0) = Semiterm.Operator.Add.add.operator ![t, u] from rfl]
  simp only [Semiterm.Operator.operator, Semiterm.Operator.Add.term_eq, Rew.func]
  congr 1

lemma twoT_eq : twoT = FirstOrder.Semiterm.func Language.Add.add
    ![FirstOrder.Semiterm.func Language.One.one ![], FirstOrder.Semiterm.func Language.One.one ![]] := by
  unfold twoT
  rw [show (‘1 + 1’ : ClosedSemiterm ℒₒᵣ 0) = ‘!!(‘1’ : ClosedSemiterm ℒₒᵣ 0) + !!(‘1’ : ClosedSemiterm ℒₒᵣ 0)’ from rfl,
    addT_eq, oneT_eq]

/-- `bnumT_even` in the raw syntax: `bnumT n = twoMul (bnumT (n / 2))` for even `n ≥ 2`. -/
lemma bnumT_even' {n : ℕ} (h2 : 2 ≤ n) (he : n % 2 = 0) : bnumT n = twoMul (bnumT (n / 2)) := by
  rw [bnumT_even h2 he, mulT_eq, twoT_eq]; rfl

/-- `bnumT_odd` in the raw syntax: `bnumT n = twoMulOne (bnumT (n / 2))` for odd `n ≥ 2`. -/
lemma bnumT_odd' {n : ℕ} (h2 : 2 ≤ n) (ho : n % 2 = 1) : bnumT n = twoMulOne (bnumT (n / 2)) := by
  rw [bnumT_odd h2 ho, addT_eq, mulT_eq, twoT_eq, oneT_eq]; rfl

end bnum

/-! ### `lMap emb`: the `ℒₒᵣ` syntax is the `LAct` syntax -/

section emb

variable {ξ : Type*} {n : ℕ}

/-- `lMap emb` commutes with substitution into an embedded closed-variable term. -/
lemma lMap_emb_subst_emb {k : ℕ} (v : Fin k → Semiterm ℒₒᵣ ξ n) (t : Semiterm ℒₒᵣ Empty k) :
    Semiterm.lMap emb (Rew.subst v (Rew.emb t)) =
      Rew.subst (fun i ↦ Semiterm.lMap emb (v i)) (Rew.emb (Semiterm.lMap emb t)) := by
  induction t with
  | bvar x => simp
  | fvar x => exact x.elim
  | func f w ih => simp [Rew.func, Semiterm.lMap_func, ih, Function.comp_def]

/-- `lMap emb` of an operator application is the application of the mapped operator. -/
lemma lMap_emb_operator {k : ℕ} (o : Semiterm.Operator ℒₒᵣ k) (v : Fin k → Semiterm ℒₒᵣ ξ n) :
    Semiterm.lMap emb (o.operator v) =
      (⟨Semiterm.lMap emb o.term⟩ : Semiterm.Operator LAct k).operator (fun i ↦ Semiterm.lMap emb (v i)) :=
  lMap_emb_subst_emb v o.term

lemma lMap_emb_add_term :
    (⟨Semiterm.lMap emb (Semiterm.Operator.Add.add : Semiterm.Operator ℒₒᵣ 2).term⟩ : Semiterm.Operator LAct 2) =
      Semiterm.Operator.Add.add := by
  simp only [Semiterm.Operator.Add.term_eq, Semiterm.lMap_func]
  rfl

/-- The unary numeral OPERATOR of `c` is mapped to `LAct`'s. -/
lemma lMap_emb_numeral_term (c : ℕ) :
    Semiterm.lMap emb (Semiterm.Operator.numeral ℒₒᵣ c).term = (Semiterm.Operator.numeral LAct c).term := by
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    rcases c with _ | _ | c
    · simp only [Semiterm.Operator.numeral_zero, Semiterm.Operator.Zero.term_eq, Semiterm.lMap_func]
      congr 1
      exact Subsingleton.elim _ _
    · simp only [Nat.zero_add, Semiterm.Operator.numeral_one, Semiterm.Operator.One.term_eq,
        Semiterm.lMap_func]
      congr 1
      exact Subsingleton.elim _ _
    · rw [Semiterm.Operator.numeral_succ (L := ℒₒᵣ) (z := c + 1) (by omega),
        Semiterm.Operator.numeral_succ (L := LAct) (z := c + 1) (by omega)]
      change Semiterm.lMap emb (Semiterm.Operator.Add.add.operator
          fun i ↦ (![Semiterm.Operator.numeral ℒₒᵣ (c + 1), Semiterm.Operator.One.one] i).term) =
        Semiterm.Operator.Add.add.operator
          fun i ↦ (![Semiterm.Operator.numeral LAct (c + 1), Semiterm.Operator.One.one] i).term
      rw [lMap_emb_operator, lMap_emb_add_term]
      congr 1
      funext i
      fin_cases i
      · exact ih (c + 1) (by omega)
      · show Semiterm.lMap emb (Semiterm.Operator.One.one : Semiterm.Operator ℒₒᵣ 0).term =
          (Semiterm.Operator.One.one : Semiterm.Operator LAct 0).term
        simp only [Semiterm.Operator.One.term_eq, Semiterm.lMap_func]
        congr 1
        exact Subsingleton.elim _ _

/-- The unary numeral of `c` embedded along `emb` is `LAct`'s unary numeral of `c`
(`Template.numT c = ↑c`). -/
lemma lMap_emb_numeral (c : ℕ) :
    Semiterm.lMap emb (↑c : Semiterm ℒₒᵣ ξ n) = (↑c : Semiterm LAct ξ n) := by
  simp only [Semiterm.numeral, Semiterm.Operator.const]
  rw [lMap_emb_operator, lMap_emb_numeral_term]
  congr 1
  exact Subsingleton.elim _ _

lemma lMap_emb_leF (t u : Semiterm ℒₒᵣ ξ n) :
    Semiformula.lMap emb (leF t u) = leF (Semiterm.lMap emb t) (Semiterm.lMap emb u) := by
  simp [leF, Semiformula.lMap_rel]

lemma lMap_emb_ltF (t u : Semiterm ℒₒᵣ ξ n) :
    Semiformula.lMap emb (ltF t u) = ltF (Semiterm.lMap emb t) (Semiterm.lMap emb u) := by
  simp [ltF, Semiformula.lMap_rel]

lemma lMap_emb_twoMul (t : Semiterm ℒₒᵣ ξ n) :
    Semiterm.lMap emb (twoMul t) = twoMul (Semiterm.lMap emb t) := by
  simp [twoMul, Semiterm.lMap_func]

lemma lMap_emb_twoMulOne (t : Semiterm ℒₒᵣ ξ n) :
    Semiterm.lMap emb (twoMulOne t) = twoMulOne (Semiterm.lMap emb t) := by
  simp [twoMulOne, Semiterm.lMap_func, lMap_emb_twoMul]

end emb

/-! ### A `TAct`-theorem has SOME proof length -/

/-- Every `TAct ⊢ σ` is a `Derivation2` (`provable_iff_derivable2`), quoted back at its own
`mlen` (`lenProvable_of_derivation`): the length is an existential constant. -/
theorem lenProvable_of_provable {σ : Sentence LAct} (h : TAct ⊢ σ) :
    ∃ N : ℕ, LenProvable (fbound : ℕ → ℕ) N TAct (⌜σ⌝ : ℕ) := by
  obtain ⟨b⟩ := provable_iff_derivable2.mp h
  exact ⟨mlen b, lenProvable_of_derivation smallCodes_LAct smallRelCodes_LAct b le_rfl⟩

/-! ### The two uniform PA lemmas: `c ≤ x → c ≤ 2x` and `c ≤ x → c ≤ 2x + 1` -/

section uniform

/-- `c ≤ #0 🡒 c ≤ (1 + 1) · #0`, over `ℒₒᵣ`. -/
def leEven (c : ℕ) : Semisentence ℒₒᵣ 1 := leF (↑c) #0 🡒 leF (↑c) (twoMul #0)

/-- `c ≤ #0 🡒 c ≤ (1 + 1) · #0 + 1`, over `ℒₒᵣ`. -/
def leOdd (c : ℕ) : Semisentence ℒₒᵣ 1 := leF (↑c) #0 🡒 leF (↑c) (twoMulOne #0)

/-- The same over `LAct`. -/
def leEvenA (c : ℕ) : Semisentence LAct 1 := leF (↑c) #0 🡒 leF (↑c) (twoMul #0)

def leOddA (c : ℕ) : Semisentence LAct 1 := leF (↑c) #0 🡒 leF (↑c) (twoMulOne #0)

lemma lMap_emb_leEven (c : ℕ) : Semiformula.lMap emb (leEven c) = leEvenA c := by
  unfold leEven leEvenA
  rw [LogicalConnective.HomClass.map_imply, lMap_emb_leF, lMap_emb_leF, lMap_emb_numeral,
    lMap_emb_twoMul]
  rfl

lemma lMap_emb_leOdd (c : ℕ) : Semiformula.lMap emb (leOdd c) = leOddA c := by
  unfold leOdd leOddA
  rw [LogicalConnective.HomClass.map_imply, lMap_emb_leF, lMap_emb_leF, lMap_emb_numeral,
    lMap_emb_twoMulOne]
  rfl

variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

lemma models_leEven (c : ℕ) : M↓[ℒₒᵣ] ⊧ (∀¹ leEven c : Sentence ℒₒᵣ) := by
  simp [leEven, leF, twoMul, models_iff, numeral_eq_natCast]
  intro x hx
  exact le_def.mp (le_trans (le_def.mpr hx) (by rw [one_add_one_eq_two]; exact le_two_mul_left))

lemma models_leOdd (c : ℕ) : M↓[ℒₒᵣ] ⊧ (∀¹ leOdd c : Sentence ℒₒᵣ) := by
  simp [leOdd, leF, twoMulOne, twoMul, models_iff, numeral_eq_natCast]
  intro x hx
  exact le_def.mp (le_trans (le_def.mpr hx)
    (le_trans (by rw [one_add_one_eq_two]; exact le_two_mul_left) le_self_add))

end uniform

section paProves

theorem pa_proves_leEven (c : ℕ) : 𝗣𝗔 ⊢ (∀¹ leEven c : Sentence ℒₒᵣ) :=
  complete 𝗣𝗔 _ fun (_ : Type) _ _ ↦ models_leEven c

theorem pa_proves_leOdd (c : ℕ) : 𝗣𝗔 ⊢ (∀¹ leOdd c : Sentence ℒₒᵣ) :=
  complete 𝗣𝗔 _ fun (_ : Type) _ _ ↦ models_leOdd c

/-- Transport of a `PA` theorem to `TAct` along `emb` (`CutV`'s pattern: soundness,
`lMap_models_lMap`, completeness for `LAct`-theories). -/
theorem tact_proves_lMap_emb {σ : Sentence ℒₒᵣ} (h : 𝗣𝗔 ⊢ σ) : TAct ⊢ Semiformula.lMap emb σ := by
  refine Theory.Proof.complete fun (s : Struc.{0} LAct) hs ↦ ?_
  have hPA : s ⊧* Theory.lMap LAct.emb 𝗣𝗔 :=
    Semantics.ModelsSet.of_subset hs lMap_emb_PA_subset_TAct
  exact lMap_models_lMap (Theory.Proof.sound h) hPA

/-- **The even uniform lemma at `TAct`**: `∀ x, c ≤ x → c ≤ 2x`. -/
theorem tact_proves_leEvenA (c : ℕ) : TAct ⊢ (∀¹ leEvenA c : Sentence LAct) := by
  have := tact_proves_lMap_emb (pa_proves_leEven c)
  rwa [Semiformula.lMap_all, lMap_emb_leEven] at this

/-- **The odd uniform lemma at `TAct`**: `∀ x, c ≤ x → c ≤ 2x + 1`. -/
theorem tact_proves_leOddA (c : ℕ) : TAct ⊢ (∀¹ leOddA c : Sentence LAct) := by
  have := tact_proves_lMap_emb (pa_proves_leOdd c)
  rwa [Semiformula.lMap_all, lMap_emb_leOdd] at this

end paProves

/-! ### The base cases: `c ≤ bnumT k` for each fixed `k ≥ c` -/

section base

variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

lemma val_twoT_M : twoT.val (s := standardModel M) ![] Empty.elim = 2 := by
  unfold twoT; simp [one_add_one_eq_two]

/-- The binary numeral of `n` denotes the cast of `n` in every model of `PA`
(`Det.val_bnumT_V`, re-proved here: `Det` is not upstream). -/
theorem val_bnumT_M (n : ℕ) : (bnumT n).val (s := standardModel M) ![] Empty.elim = (n : M) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | _ | k
    · rw [bnumT_zero]; simp
    · rw [bnumT_one]; simp
    · by_cases he : (k + 1 + 1) % 2 = 0
      · rw [bnumT_even (by omega) he]
        simp [val_twoT_M, ih ((k + 1 + 1) / 2) (by omega)]
        have h2 : k + 1 + 1 = 2 * ((k + 1 + 1) / 2) := by omega
        have h3 : ((k : M) + 1 + 1) = ((k + 1 + 1 : ℕ) : M) := by norm_cast
        rw [h3]
        conv_rhs => rw [h2]
        push_cast
        rfl
      · rw [bnumT_odd (by omega) (by omega)]
        simp [val_twoT_M, ih ((k + 1 + 1) / 2) (by omega)]
        have h2 : k + 1 = 2 * ((k + 1 + 1) / 2) := by omega
        have h3 : ((k : M) + 1) = ((k + 1 : ℕ) : M) := by norm_cast
        rw [h3]
        conv_rhs => rw [h2]
        push_cast
        rfl

lemma models_le_bnumT {c k : ℕ} (h : c ≤ k) :
    M↓[ℒₒᵣ] ⊧ (leF (↑c) (bnumT k) : Sentence ℒₒᵣ) := by
  simp [leF, models_iff, numeral_eq_natCast, val_bnumT_M]
  omega

theorem pa_proves_le_bnumT {c k : ℕ} (h : c ≤ k) : 𝗣𝗔 ⊢ (leF (↑c) (bnumT k) : Sentence ℒₒᵣ) :=
  complete 𝗣𝗔 _ fun (_ : Type) _ _ ↦ models_le_bnumT h

/-- Each base case is a `TAct` theorem: `c ≤ bnumT k` for `k ≥ c`. -/
theorem tact_proves_le_bnumT {c k : ℕ} (h : c ≤ k) :
    TAct ⊢ (leF (↑c) (Semiterm.lMap emb (bnumT k)) : Sentence LAct) := by
  have := tact_proves_lMap_emb (pa_proves_le_bnumT h)
  rwa [lMap_emb_leF, lMap_emb_numeral] at this

end base

/-! ### Lengths of the sentences in the chain -/

section lengths

/-- The instance of `leF ↑c #0 🡒 ψ` at a closed term `t`: the antecedent is EXACTLY
`leF ↑c t` (the shape `lenProvable_le_bnumT` delivers). -/
lemma substs_leF_imp (c : ℕ) (ψ : Semisentence LAct 1) (t : ClosedSemiterm LAct 0) :
    ((leF (↑c) #0 🡒 ψ : Semisentence LAct 1) ⇜ ![t] : Sentence LAct) =
      (leF (↑c) t 🡒 (ψ ⇜ ![t] : Sentence LAct)) := by
  simp [rew_leF]

lemma substs_ltF_imp (c : ℕ) (ψ : Semisentence LAct 1) (t : ClosedSemiterm LAct 0) :
    ((ltF (↑c) #0 🡒 ψ : Semisentence LAct 1) ⇜ ![t] : Sentence LAct) =
      (ltF (↑c) t 🡒 (ψ ⇜ ![t] : Sentence LAct)) := by
  simp [rew_ltF]

lemma substs_leEvenA (c : ℕ) (t : ClosedSemiterm LAct 0) :
    (leEvenA c ⇜ ![t] : Sentence LAct) = (leF (↑c) t 🡒 leF (↑c) (twoMul t)) := by
  simp [leEvenA, rew_leF, rew_twoMul]

lemma substs_leOddA (c : ℕ) (t : ClosedSemiterm LAct 0) :
    (leOddA c ⇜ ![t] : Sentence LAct) = (leF (↑c) t 🡒 leF (↑c) (twoMulOne t)) := by
  simp [leOddA, rew_leF, rew_twoMulOne]

variable {L : Language} [L.Encodable] [L.LORDefinable]

lemma tlen_twoMul [L.One] [L.Add] [L.Mul] {n : ℕ} (t : SyntacticSemiterm L n) :
    tlen (twoMul t) = tlen t + 4 := by
  simp [twoMul, tlen_func, Fin.sum_univ_two]
  omega

lemma tlen_twoMulOne [L.One] [L.Add] [L.Mul] {n : ℕ} (t : SyntacticSemiterm L n) :
    tlen (twoMulOne t) = tlen t + 6 := by
  simp [twoMulOne, tlen_twoMul, Fin.sum_univ_two]

omit [L.Encodable] [L.LORDefinable] in
lemma flen_imply_sentence (φ ψ : Sentence L) :
    flen ((φ 🡒 ψ : Sentence L) : Proposition L) =
      flen (φ : Proposition L) + flen (ψ : Proposition L) + 1 := by
  rw [show ((φ 🡒 ψ : Sentence L) : Proposition L) = (φ : Proposition L) 🡒 (ψ : Proposition L) by simp,
    flen_imply]

omit [L.Encodable] [L.LORDefinable] in
/-- `|t ≤ u| = 2|t| + 2|u| + 3`. -/
lemma flen_leF_sentence [L.Eq] [L.LT] (t u : ClosedSemiterm L 0) :
    flen ((leF t u : Sentence L) : Proposition L) =
      2 * tlen (Rew.emb t : SyntacticSemiterm L 0) + 2 * tlen (Rew.emb u : SyntacticSemiterm L 0) + 3 := by
  simp [leF, Fin.sum_univ_two]
  omega

omit [L.Encodable] [L.LORDefinable] in
lemma flen_ltF_sentence [L.LT] (t u : ClosedSemiterm L 0) :
    flen ((ltF t u : Sentence L) : Proposition L) =
      tlen (Rew.emb t : SyntacticSemiterm L 0) + tlen (Rew.emb u : SyntacticSemiterm L 0) + 1 := by
  simp [ltF, Fin.sum_univ_two]

/-- The embedded binary numeral has the meta length of the `ℒₒᵣ` term (`InstV.termLen_bnum_nat`'s
route: `term_emb_lMap_emb'` + `tlen_lMap`). -/
lemma tlen_emb_lMap_bnumT (k : ℕ) :
    tlen (Rew.emb (Semiterm.lMap emb (bnumT k)) : SyntacticSemiterm LAct 0) =
      tlen (Rew.emb (bnumT k) : SyntacticSemiterm ℒₒᵣ 0) := by
  rw [term_emb_lMap_emb', tlen_lMap]

lemma tlen_emb_numeral (c : ℕ) :
    tlen (Rew.emb (↑c : ClosedSemiterm LAct 0) : SyntacticSemiterm LAct 0) =
      tlen (↑c : SyntacticSemiterm LAct 0) := by
  simp

lemma tlen_emb_twoMul (t : ClosedSemiterm LAct 0) :
    tlen (Rew.emb (twoMul t) : SyntacticSemiterm LAct 0) = tlen (Rew.emb t : SyntacticSemiterm LAct 0) + 4 := by
  rw [rew_twoMul, tlen_twoMul]

lemma tlen_emb_twoMulOne (t : ClosedSemiterm LAct 0) :
    tlen (Rew.emb (twoMulOne t) : SyntacticSemiterm LAct 0) = tlen (Rew.emb t : SyntacticSemiterm LAct 0) + 6 := by
  rw [rew_twoMulOne, tlen_twoMulOne]

end lengths

/-! ### The recursion step: one bit, cost `A + B · size (k / 2)` -/

section step

/-- One bit of the recursion: from `c ≤ bnumT (k/2)` at length `n` to `c ≤ bnumT k` at length
`n + A + B · size (k/2)`, for constants `A B` depending only on `c` (the two uniform lemmas'
lengths, `|↑c|`, and the templates' lengths). -/
theorem step_le (c : ℕ) : ∃ A B : ℕ, ∀ k : ℕ, 2 ≤ k → ∀ n : ℕ,
    LenProvable (fbound : ℕ → ℕ) n TAct
      (⌜(leF (↑c) (Semiterm.lMap emb (bnumT (k / 2))) : Sentence LAct)⌝ : ℕ) →
    LenProvable (fbound : ℕ → ℕ) (n + A + B * Nat.size (k / 2)) TAct
      (⌜(leF (↑c) (Semiterm.lMap emb (bnumT k)) : Sentence LAct)⌝ : ℕ) := by
  obtain ⟨Ne, hNe⟩ := lenProvable_of_provable (tact_proves_leEvenA c)
  obtain ⟨No, hNo⟩ := lenProvable_of_provable (tact_proves_leOddA c)
  refine ⟨Ne + No + 60 * tlen (↑c : SyntacticSemiterm LAct 0)
      + 3 * flen ((leEvenA c : Semisentence LAct 1) : Semiproposition LAct 1)
      + 3 * flen ((leOddA c : Semisentence LAct 1) : Semiproposition LAct 1) + 400, 400,
    fun k h2 n h ↦ ?_⟩
  have hβ := tlen_bnumT (k / 2)
  by_cases he : k % 2 = 0
  · have hi := lenProvable_inst_size (leEvenA c) (k / 2) hNe
    rw [substs_leEvenA] at hi
    have hcut := lenProvable_mp hi h
    have ht : twoMul (Semiterm.lMap emb (bnumT (k / 2))) = Semiterm.lMap emb (bnumT k) := by
      rw [bnumT_even' h2 he, lMap_emb_twoMul]
    rw [ht] at hcut
    refine lenProvable_fbound_mono ?_ hcut
    rw [← ht, flen_imply_sentence, flen_leF_sentence, flen_leF_sentence, tlen_emb_twoMul,
      tlen_emb_lMap_bnumT, tlen_emb_numeral]
    omega
  · have ho : k % 2 = 1 := by omega
    have hi := lenProvable_inst_size (leOddA c) (k / 2) hNo
    rw [substs_leOddA] at hi
    have hcut := lenProvable_mp hi h
    have ht : twoMulOne (Semiterm.lMap emb (bnumT (k / 2))) = Semiterm.lMap emb (bnumT k) := by
      rw [bnumT_odd' h2 ho, lMap_emb_twoMulOne]
    rw [ht] at hcut
    refine lenProvable_fbound_mono ?_ hcut
    rw [← ht, flen_imply_sentence, flen_leF_sentence, flen_leF_sentence, tlen_emb_twoMulOne,
      tlen_emb_lMap_bnumT, tlen_emb_numeral]
    omega

end step

/-! ### The base range: finitely many constant proofs -/

section baseRange

/-- For every bound `R`, ONE length `C₀` serves every base case `c ≤ k < R`. -/
theorem base_le (c : ℕ) : ∀ R : ℕ, ∃ C₀ : ℕ, ∀ k : ℕ, k < R → c ≤ k →
    LenProvable (fbound : ℕ → ℕ) C₀ TAct
      (⌜(leF (↑c) (Semiterm.lMap emb (bnumT k)) : Sentence LAct)⌝ : ℕ)
  | 0 => ⟨0, fun _ hk _ ↦ absurd hk (Nat.not_lt_zero _)⟩
  | R + 1 => by
    obtain ⟨C, hC⟩ := base_le c R
    by_cases hcR : c ≤ R
    · obtain ⟨N, hN⟩ := lenProvable_of_provable (tact_proves_le_bnumT hcR)
      refine ⟨max C N, fun k hk hck ↦ ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with h | rfl
      · exact lenProvable_fbound_mono (le_max_left _ _) (hC k h hck)
      · exact lenProvable_fbound_mono (le_max_right _ _) hN
    · exact ⟨C, fun k hk hck ↦ hC k (by omega) hck⟩

end baseRange

/-! ### The theorem -/

/-- **Short `TAct` proofs of `c ≤ bnumT k`**: for every constant `c` there are `C₀ C₁` with a
`TAct`-proof of `leF ↑c (lMap emb (bnumT k))` of length `≤ C₀ + C₁ · size k · size k` for every
`k ≥ c` — quadratic in the BIT LENGTH of `k`, `≺ k`. Strong induction on `k`: below `2c + 2`
the base range (`base_le`); above, `k/2 ≥ c` and one recursion step (`step_le`) on the
induction hypothesis, with `size (k/2) < size k` (`size_div_two_lt`) paying the step. -/
theorem lenProvable_le_bnumT (c : ℕ) :
    ∃ C₀ C₁ : ℕ, ∀ k : ℕ, c ≤ k →
      LenProvable (fbound : ℕ → ℕ) (C₀ + C₁ * Nat.size k * Nat.size k) TAct
        (⌜(leF (↑c) (Semiterm.lMap emb (bnumT k)) : Sentence LAct)⌝ : ℕ) := by
  obtain ⟨A, B, hstep⟩ := step_le c
  obtain ⟨C₀, hbase⟩ := base_le c (2 * c + 2)
  refine ⟨C₀, A + B, fun k ↦ ?_⟩
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hck
    by_cases hk : k < 2 * c + 2
    · exact lenProvable_fbound_mono (Nat.le_add_right _ _) (hbase k hk hck)
    · have h2 : 2 ≤ k := by omega
      have hj := ih (k / 2) (by omega) (by omega)
      refine lenProvable_fbound_mono ?_ (hstep k h2 _ hj)
      have hlt := size_div_two_lt k h2
      have hpos : 1 ≤ Nat.size (k / 2) := Nat.size_pos.mpr (by omega)
      set s' := Nat.size (k / 2) with hs'
      set s := Nat.size k with hs
      have e1 : A + B * s' ≤ (A + B) * s' := by nlinarith
      have e3 : (A + B) * s' * (s' + 1) ≤ (A + B) * s * s :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
      nlinarith [e1, e3]

/-! ### The strict twin: `c < bnumT k` for `k > c` -/

section strict

/-- `c + 1 ≤ #0 🡒 c < #0`, over `ℒₒᵣ`. -/
def leSuccLt (c : ℕ) : Semisentence ℒₒᵣ 1 := leF (↑(c + 1)) #0 🡒 ltF (↑c) #0

/-- The same over `LAct`. -/
def leSuccLtA (c : ℕ) : Semisentence LAct 1 := leF (↑(c + 1)) #0 🡒 ltF (↑c) #0

lemma lMap_emb_leSuccLt (c : ℕ) : Semiformula.lMap emb (leSuccLt c) = leSuccLtA c := by
  unfold leSuccLt leSuccLtA
  rw [LogicalConnective.HomClass.map_imply, lMap_emb_leF, lMap_emb_ltF, lMap_emb_numeral,
    lMap_emb_numeral]
  rfl

variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

lemma models_leSuccLt (c : ℕ) : M↓[ℒₒᵣ] ⊧ (∀¹ leSuccLt c : Sentence ℒₒᵣ) := by
  simp [leSuccLt, leF, ltF, models_iff, numeral_eq_natCast]
  intro x hx
  exact lt_of_lt_of_le (lt_add_one (c : M)) (le_def.mpr hx)

theorem pa_proves_leSuccLt (c : ℕ) : 𝗣𝗔 ⊢ (∀¹ leSuccLt c : Sentence ℒₒᵣ) :=
  complete 𝗣𝗔 _ fun (_ : Type) _ _ ↦ models_leSuccLt c

theorem tact_proves_leSuccLtA (c : ℕ) : TAct ⊢ (∀¹ leSuccLtA c : Sentence LAct) := by
  have := tact_proves_lMap_emb (pa_proves_leSuccLt c)
  rwa [Semiformula.lMap_all, lMap_emb_leSuccLt] at this

lemma substs_leSuccLtA (c : ℕ) (t : ClosedSemiterm LAct 0) :
    (leSuccLtA c ⇜ ![t] : Sentence LAct) = (leF (↑(c + 1)) t 🡒 ltF (↑c) t) := by
  simp [leSuccLtA, rew_leF, rew_ltF]

/-- **Short `TAct` proofs of `c < bnumT k`** for `k > c`: the `≤`-theorem at `c + 1` and one
cut with the uniform lemma `c + 1 ≤ x → c < x` instantiated at `bnumT k` (`O(size k)` extra). -/
theorem lenProvable_lt_bnumT (c : ℕ) :
    ∃ C₀ C₁ : ℕ, ∀ k : ℕ, c < k →
      LenProvable (fbound : ℕ → ℕ) (C₀ + C₁ * Nat.size k * Nat.size k) TAct
        (⌜(ltF (↑c) (Semiterm.lMap emb (bnumT k)) : Sentence LAct)⌝ : ℕ) := by
  obtain ⟨D₀, D₁, hle⟩ := lenProvable_le_bnumT (c + 1)
  obtain ⟨N, hN⟩ := lenProvable_of_provable (tact_proves_leSuccLtA c)
  refine ⟨D₀ + N + 30 * tlen (↑(c + 1) : SyntacticSemiterm LAct 0)
      + 15 * tlen (↑c : SyntacticSemiterm LAct 0)
      + 3 * flen ((leSuccLtA c : Semisentence LAct 1) : Semiproposition LAct 1) + 200,
    D₁ + 300, fun k hck ↦ ?_⟩
  have h := hle k hck
  have hi := lenProvable_inst_size (leSuccLtA c) k hN
  rw [substs_leSuccLtA] at hi
  have hcut := lenProvable_mp hi h
  refine lenProvable_fbound_mono ?_ hcut
  rw [flen_imply_sentence, flen_leF_sentence, flen_ltF_sentence, tlen_emb_lMap_bnumT,
    tlen_emb_numeral, tlen_emb_numeral]
  have hβ := tlen_bnumT k
  have hs : Nat.size k ≤ Nat.size k * Nat.size k := Nat.le_mul_self _
  have e : (D₁ + 300) * Nat.size k * Nat.size k = D₁ * Nat.size k * Nat.size k + 300 * (Nat.size k * Nat.size k) := by
    ring
  omega

end strict

end ArithS
