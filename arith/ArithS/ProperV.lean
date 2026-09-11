import ArithS.CutV
import ArithS.BewV

/-!
# ArithS.ProperV — properness of derivation codes inside every model of `IΣ₁`

`ArithS.Proper` proves properness at `V = ℕ` THROUGH QUOTES (`quote_derivation_le`: the code
of a meta derivation `d : T ⟹₂ Γ` is below a tower in `mlen d`), and `ArithS.CutV` therefore
states properness inside a model as a HYPOTHESIS (`ProperV V T`), discharged only at ℕ
(`properV_nat`). This module proves it in EVERY model, without quotes:

```
properV_of_small : SmallCodesV V L → SmallRelCodesV V L → ∀ (T : Theory L) [T.Δ₁], ProperV V T
properV_TAct     : ProperV V TAct
```

The chain of `Proper.lean` is redone on the INTERNAL codes by the internal induction principles:

* towers `EV s = exp (exp s)`, `FV s = exp (EV s)` (Σ₁-definable; `fbound k = FV (12 k) + 1` by
  `rfl`), closed under pairing at two levels (`pair_EV`, `pair_FV`, from the sharp pair bound
  `⟪a, b⟫ + 1 ≤ (max a b + 1)²` proved from the definition of `pair`) and, for `FV`, under
  one bit-set level (`exp_EV_succ_le_FV`);
* terms: `IsUTerm L t → 1 ≤ termLen L t ∧ t ≤ EV (8 · termLen L t)` (`isUTerm_le_EV`, by
  `IsUTerm.induction 𝚺`), with the argument vector bounded by `Π₁`-induction on its length
  (`vec_EV`: entries below `EV (8 lᵢ)` with `lᵢ ≥ 1` give a vector below `EV (8 Σ lᵢ + 2)`);
* formulas: `IsSemiformula L n p → 1 ≤ formulaLen L p ∧ p ≤ EV (8 · formulaLen L p)`
  (`isSemiformula_le_EV`, by `IsSemiformula.sigma1_structural_induction`);
* sequents: `IsFormulaSet L s → s ≤ FV (8 · setLen L s + 1)` (`isFormulaSet_le_FV`, by
  `lt_exp_iff` on the bit-set and `formulaLen_le_setLen_of_mem`);
* derivations: `Derivation T d → DlenGraph L d n → d ≤ FV (12 n)` (`derivation_le_FV`, by
  `Derivation.induction1 𝚷` — the `DlenGraph.*_iff` inversion clauses give each node's length
  from its premises, and every node is `⟪s, tag, rest⟫ + 1` with `s, rest ≤ FV (12 Y)` for `Y`
  the length without the node's own `+ 1`).

The symbol-code hypotheses are the INTERNAL statements `SmallCodesV V L : ∀ k f, L.IsFunc k f →
f ≤ 8` (resp. `IsRel`); the meta `SmallCodes L` of `Proper.lean` does not imply them for an
arbitrary language (a nonstandard model may have nonstandard symbol codes), but for `LAct` and
`ℒₒᵣ` the symbol sets are explicit finite Δ₀-disjunctions, so both hold in every model
(`smallCodesV_LAct`, `smallCodesV_LOR`, …).

Consequences (all unconditional, every model of `IΣ₁`): `lenProvableV_cut_V'` and
`lenProvableV_cut_V_sharp'` (bounded D2 for `LenProvableV TAct`, no `hP`), and the bridge
`lenDerivable_iff_lenProvableV : LenDerivable TAct k φ ↔ LenProvableV TAct k φ` — the Löb
argument's Σ₁ box (no code bound) and the evaluator's Δ₁ box (`ArithS.BewV`) coincide.
-/

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ### The towers, inside `V` -/

/-- `EV s = exp (exp s)`, the internal `E`. -/
noncomputable def EV (s : V) : V := Exp.exp (Exp.exp s)

/-- `FV s = exp (exp (exp s))`, the internal `F`; `fbound k = FV (12 k) + 1`. -/
noncomputable def FV (s : V) : V := Exp.exp (EV s)

def EVDef : 𝚺₁.Semisentence 2 := .mkSigma
  “y s. ∃ a, !(expDef.ofZero 𝚺₁) a s ∧ !(expDef.ofZero 𝚺₁) y a”

def FVDef : 𝚺₁.Semisentence 2 := .mkSigma
  “y s. ∃ a, !(expDef.ofZero 𝚺₁) a s ∧ ∃ b, !(expDef.ofZero 𝚺₁) b a ∧ !(expDef.ofZero 𝚺₁) y b”

instance EV_defined : 𝚺₁-Function₁[V] EV via EVDef := .mk fun v ↦ by
  simp [EVDef, EV, expDef, ← exponential_graph]

instance EV_definable : 𝚺₁-Function₁[V] EV := EV_defined.to_definable

instance EV_definable' : Γ-[m + 1]-Function₁[V] EV := EV_definable.of_sigmaOne

instance FV_defined : 𝚺₁-Function₁[V] FV via FVDef := .mk fun v ↦ by
  simp [FVDef, FV, EV, expDef, ← exponential_graph]

instance FV_definable : 𝚺₁-Function₁[V] FV := FV_defined.to_definable

instance FV_definable' : Γ-[m + 1]-Function₁[V] FV := FV_definable.of_sigmaOne

lemma fbound_eq_FV (k : V) : fbound k = FV (12 * k) + 1 := rfl

lemma EV_mono {s t : V} (h : s ≤ t) : EV s ≤ EV t :=
  exp_monotone_le.mpr (exp_monotone_le.mpr h)

lemma FV_mono {s t : V} (h : s ≤ t) : FV s ≤ FV t :=
  exp_monotone_le.mpr (EV_mono h)

lemma two_le_EV (s : V) : 2 ≤ EV s := by
  have : Exp.exp (1 : V) ≤ Exp.exp (Exp.exp s) := exp_monotone_le.mpr (one_le_exp s)
  simpa [EV] using this

lemma le_EV (s : V) : s ≤ EV s :=
  le_trans (lt_exp s).le (lt_exp _).le

lemma EV_le_FV (s : V) : EV s ≤ FV s := (lt_exp _).le

lemma le_FV (s : V) : s ≤ FV s := le_trans (le_EV s) (EV_le_FV s)

lemma exp_two : Exp.exp (2 : V) = 4 := by
  rw [show (2 : V) = 1 + 1 by norm_num, exp_succ, exp_one]; norm_num

lemma exp_four : Exp.exp (4 : V) = 16 := by
  rw [show (4 : V) = 2 + 1 + 1 by norm_num, exp_succ, exp_succ, exp_two]; norm_num

lemma EV_zero : EV (0 : V) = 2 := by simp [EV]
lemma EV_one : EV (1 : V) = 4 := by simp [EV, exp_two]
lemma EV_two : EV (2 : V) = 16 := by simp [EV, exp_two, exp_four]
lemma FV_one : FV (1 : V) = 16 := by simp [FV, EV_one, exp_four]

lemma four_le_EV {s : V} (h : 1 ≤ s) : 4 ≤ EV s := le_trans (le_of_eq EV_one.symm) (EV_mono h)
lemma eight_le_EV {s : V} (h : 2 ≤ s) : 8 ≤ EV s :=
  le_trans (by rw [EV_two]; norm_num) (EV_mono h)
lemma sixteen_le_FV {s : V} (h : 1 ≤ s) : 16 ≤ FV s := le_trans (le_of_eq FV_one.symm) (FV_mono h)

lemma exp_two_mul (a : V) : Exp.exp (2 * a) = Exp.exp a * Exp.exp a := by
  rw [exp_even, sq]

lemma exp_four_mul (a : V) : Exp.exp (4 * a) = Exp.exp a * Exp.exp a * (Exp.exp a * Exp.exp a) := by
  rw [show 4 * a = 2 * (2 * a) by ring, exp_two_mul, exp_two_mul]

lemma EV_add_one (s : V) : EV (s + 1) = EV s * EV s := by
  simp only [EV]; rw [exp_succ, exp_two_mul]

lemma EV_add_two (s : V) : EV (s + 2) = EV s * EV s * (EV s * EV s) := by
  simp only [EV]; rw [show s + 2 = s + 1 + 1 by ring, exp_succ, exp_succ, ← mul_assoc,
    show (2 : V) * 2 = 4 by norm_num, exp_four_mul]

/-- `(x + 1) * (x + 1) ≤ x * x * (x * x)` for `2 ≤ x`. -/
lemma succ_sq_le_pow_four {x : V} (hx : 2 ≤ x) : (x + 1) * (x + 1) ≤ x * x * (x * x) := by
  have h1 : 1 ≤ x := le_trans (by norm_num) hx
  have hxx : 4 ≤ x * x := le_trans (by norm_num : (4 : V) ≤ 2 * 2) (mul_le_mul hx hx (by norm_num) (by positivity))
  calc (x + 1) * (x + 1) = x * x + 2 * x + 1 := by ring
    _ ≤ x * x + x * x + x * x :=
        add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_right hx (by positivity)))
          (le_trans (by norm_num) hxx)
    _ = 3 * (x * x) := by ring
    _ ≤ (x * x) * (x * x) := by gcongr; exact le_trans (by norm_num) hxx
    _ = x * x * (x * x) := by ring


/-! ### Pairing costs two tower levels; one bit-set costs one `F`-level -/

/-- The sharp pair bound: `⟪a, b⟫ < (max a b + 1)²`, in the form we use. -/
lemma pair_succ_le_sq {a b x : V} (ha : a ≤ x) (hb : b ≤ x) : ⟪a, b⟫ + 1 ≤ (x + 1) * (x + 1) := by
  unfold pair
  split_ifs with h
  · calc b * b + a + 1 ≤ x * x + x + 1 := by gcongr
      _ ≤ x * x + x + x + 1 := by
          rw [add_right_comm (x * x + x) x 1]; exact le_self_add
      _ = (x + 1) * (x + 1) := by ring
  · calc a * a + a + b + 1 ≤ x * x + x + x + 1 := by gcongr
      _ = (x + 1) * (x + 1) := by ring

lemma pair_EV {a b s : V} (ha : a ≤ EV s) (hb : b ≤ EV s) : ⟪a, b⟫ + 1 ≤ EV (s + 2) := by
  rw [EV_add_two]
  exact le_trans (pair_succ_le_sq ha hb) (succ_sq_le_pow_four (two_le_EV s))

lemma pair_EV_le {a b s : V} (ha : a ≤ EV s) (hb : b ≤ EV s) : ⟪a, b⟫ ≤ EV (s + 2) :=
  le_trans le_self_add (pair_EV ha hb)

lemma FV_add_two (s : V) : FV s * FV s * (FV s * FV s) ≤ FV (s + 2) := by
  simp only [FV]
  rw [← exp_four_mul, EV_add_two]
  apply exp_monotone_le.mpr
  have h2 := two_le_EV s
  have h8 : 4 ≤ EV s * EV s * EV s :=
    le_trans (by norm_num : (4 : V) ≤ 2 * 2 * 2)
      (mul_le_mul (mul_le_mul h2 h2 (by norm_num) (by positivity)) h2 (by norm_num) (by positivity))
  calc 4 * EV s ≤ EV s * EV s * EV s * EV s := mul_le_mul_of_nonneg_right h8 (by positivity)
    _ = EV s * EV s * (EV s * EV s) := by ring

lemma pair_FV {a b s : V} (ha : a ≤ FV s) (hb : b ≤ FV s) : ⟪a, b⟫ + 1 ≤ FV (s + 2) :=
  le_trans (pair_succ_le_sq ha hb)
    (le_trans (succ_sq_le_pow_four (le_trans (two_le_EV s) (EV_le_FV s))) (FV_add_two s))

lemma pair_FV_le {a b s : V} (ha : a ≤ FV s) (hb : b ≤ FV s) : ⟪a, b⟫ ≤ FV (s + 2) :=
  le_trans le_self_add (pair_FV ha hb)

/-- One bit-set level: `exp (EV s + 1) ≤ FV (s + 1)`. -/
lemma exp_EV_succ_le_FV (s : V) : Exp.exp (EV s + 1) ≤ FV (s + 1) := by
  simp only [FV]
  rw [EV_add_one]
  apply exp_monotone_le.mpr
  have h2 := two_le_EV s
  calc EV s + 1 ≤ EV s + EV s := by gcongr; exact le_trans (by norm_num) h2
    _ = 2 * EV s := by ring
    _ ≤ EV s * EV s := mul_le_mul_of_nonneg_right h2 (by positivity)


/-! ### Vectors: `k` entries below `EV (8 lᵢ)` with `lᵢ ≥ 1` give a code below `EV (8 Σ lᵢ + 2)` -/

/-- The vector bound, by `Π₁`-induction on the length. -/
lemma vec_EV : ∀ k : V, ∀ w u : V, len w = k → len u = k →
    (∀ i < k, 1 ≤ u.[i] ∧ w.[i] ≤ EV (8 * u.[i])) → w ≤ EV (8 * listSum u + 2) := by
  intro k
  induction k using ISigma1.pi1_succ_induction with
  | hP => definability
  | zero =>
    intro w u hw _ _
    rw [len_zero_iff_eq_nil.mp hw]
    exact zero_le
  | succ k ih =>
    intro w u hw hu H
    rcases nil_or_adjoin w with rfl | ⟨x, w', rfl⟩
    · exact zero_le
    rcases nil_or_adjoin u with rfl | ⟨l, u', rfl⟩
    · simp at hu
    have hw' : len w' = k := by simpa using hw
    have hu' : len u' = k := by simpa using hu
    have h0 := H 0 (by simp)
    simp only [nth_adjoin_zero] at h0
    have ih' : w' ≤ EV (8 * listSum u' + 2) :=
      ih w' u' hw' hu' fun i hi ↦ by simpa using H (i + 1) (by simpa using hi)
    have hl : 8 * listSum u' + 2 ≤ 8 * l + 8 * listSum u' := by
      rw [add_comm]
      exact add_le_add_left (le_trans (by norm_num) (le_mul_of_one_le_right (by norm_num) h0.1)) _
    have hx : x ≤ EV (8 * l + 8 * listSum u') := le_trans h0.2 (EV_mono le_self_add)
    have hw'' : w' ≤ EV (8 * l + 8 * listSum u') := le_trans ih' (EV_mono hl)
    rw [adjoin_def, listSum_adjoin]
    exact le_trans (pair_EV hx hw'') (EV_mono (le_of_eq (by ring)))

/-! ### Small symbol codes, inside `V` -/

/-- Function-symbol codes bounded by `8`, as an internal statement. -/
abbrev SmallCodesV (V : Type*) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (L : Language) [L.Encodable]
    [L.LORDefinable] : Prop :=
  ∀ k f : V, L.IsFunc k f → f ≤ 8

/-- Relation-symbol codes bounded by `8`, as an internal statement. -/
abbrev SmallRelCodesV (V : Type*) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (L : Language) [L.Encodable]
    [L.LORDefinable] : Prop :=
  ∀ k r : V, L.IsRel k r → r ≤ 8

lemma isFunc_LAct_iff_V {k f : V} :
    LAct.IsFunc k f ↔
    (k = 0 ∧ f = 0) ∨ (k = 0 ∧ f = 1) ∨ (k = 0 ∧ f = 2) ∨ (k = 0 ∧ f = 3) ∨ (k = 2 ∧ f = 0) ∨ (k = 2 ∧ f = 1) := by
  rw [isFunc_def]
  have : (LAct).isFunc = .mkSigma “k f. (k = 0 ∧ f = 0) ∨ (k = 0 ∧ f = 1) ∨ (k = 0 ∧ f = 2) ∨
    (k = 0 ∧ f = 3) ∨ (k = 2 ∧ f = 0) ∨ (k = 2 ∧ f = 1)” := rfl
  rw [this]; simp

lemma isRel_LAct_iff_V {k r : V} :
    LAct.IsRel k r ↔ (k = 2 ∧ r = 0) ∨ (k = 2 ∧ r = 1) := by
  rw [isRel_def]
  have : (LAct).isRel = .mkSigma “k r. (k = 2 ∧ r = 0) ∨ (k = 2 ∧ r = 1)” := rfl
  rw [this]; simp

theorem smallCodesV_LAct : SmallCodesV V LAct := fun k f h ↦ by
  rcases isFunc_LAct_iff_V.mp h with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;>
    norm_num

theorem smallRelCodesV_LAct : SmallRelCodesV V LAct := fun k r h ↦ by
  rcases isRel_LAct_iff_V.mp h with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> norm_num

lemma isFunc_LOR_iff_V {k f : V} : (ℒₒᵣ).IsFunc k f ↔
    (k = 0 ∧ f = 0) ∨ (k = 0 ∧ f = 1) ∨ (k = 2 ∧ f = 0) ∨ (k = 2 ∧ f = 1) := by
  rw [isFunc_def (L := ℒₒᵣ), Bootstrapping.Arithmetic.func_def_LOR]; simp

lemma isRel_LOR_iff_V {k r : V} : (ℒₒᵣ).IsRel k r ↔ (k = 2 ∧ r = 0) ∨ (k = 2 ∧ r = 1) := by
  rw [isRel_def (L := ℒₒᵣ), Bootstrapping.Arithmetic.rel_def_LOR]; simp

theorem smallCodesV_LOR : SmallCodesV V ℒₒᵣ := fun k f h ↦ by
  rcases isFunc_LOR_iff_V.mp h with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> norm_num

theorem smallRelCodesV_LOR : SmallRelCodesV V ℒₒᵣ := fun k r h ↦ by
  rcases isRel_LOR_iff_V.mp h with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> norm_num

lemma add_le_eight_mul_succ (a : V) {c : V} (hc : c ≤ 8) : 8 * a + c ≤ 8 * (a + 1) := by
  rw [mul_add, mul_one]; exact add_le_add le_rfl hc

/-! ### Term codes are bounded by `EV (8 · termLen)` -/

section terms

variable {L : Language} [L.Encodable] [L.LORDefinable]

/-- The symbol-node chain shared by `^func` and `^rel/^nrel`: with the argument vector below
`EV (8 S + 2)` (`vec_EV`), the arity `k ≤ v`, the symbol code `≤ 8` and the tag `≤ 2`, the node
is below `EV (8 (S + 1))`. -/
lemma symbol_node_EV {t k f v S : V} (ht : t ≤ 2) (hk : k ≤ v) (hf : f ≤ 8)
    (hv : v ≤ EV (8 * S + 2)) : ⟪t, k, f, v⟫ + 1 ≤ EV (8 * (S + 1)) := by
  have hf' : f ≤ EV (8 * S + 2) := le_trans hf (eight_le_EV le_add_self)
  have h1 := pair_EV_le hf' hv
  have hk' : k ≤ EV (8 * S + 2 + 2) := le_trans hk (le_trans hv (EV_mono le_self_add))
  have h2 := pair_EV_le hk' h1
  have ht' : t ≤ EV (8 * S + 2 + 2 + 2) := le_trans ht (two_le_EV _)
  have h3 := pair_EV ht' h2
  exact le_trans h3 (EV_mono (le_of_eq (by ring)))

/-- **Term codes are proper**: `IsUTerm L t → t ≤ EV (8 · termLen L t)` (with `1 ≤ termLen`). -/
theorem isUTerm_le_EV (hL : SmallCodesV V L) :
    ∀ t : V, IsUTerm L t → 1 ≤ termLen L t ∧ t ≤ EV (8 * termLen L t) := by
  apply IsUTerm.induction 𝚺 (P := fun t ↦ 1 ≤ termLen L t ∧ t ≤ EV (8 * termLen L t))
  · definability
  · intro z
    rw [termLen_bvar]
    refine ⟨le_add_self, ?_⟩
    have hz : z ≤ EV (8 * z + 6) :=
      le_trans (le_trans (le_mul_of_one_le_left (zero_le) (by norm_num)) le_self_add) (le_EV _)
    exact le_trans (pair_EV (zero_le) hz) (EV_mono (le_of_eq (by ring)))
  · intro x
    rw [termLen_fvar]
    refine ⟨le_add_self, ?_⟩
    have hx : x ≤ EV (8 * x + 6) :=
      le_trans (le_trans (le_mul_of_one_le_left (zero_le) (by norm_num)) le_self_add) (le_EV _)
    have h1 : (1 : V) ≤ EV (8 * x + 6) := le_trans (by norm_num) (two_le_EV _)
    exact le_trans (pair_EV h1 hx) (EV_mono (le_of_eq (by ring)))
  · intro k f v hf hv ih
    rw [termLen_func hf hv]
    refine ⟨le_add_self, ?_⟩
    have hvec : v ≤ EV (8 * listSum (termLenVec L k v) + 2) :=
      vec_EV k v _ hv.lh.symm (len_termLenVec hv) fun i hi ↦ by
        rw [nth_termLenVec hv hi]; exact ih i hi
    have hk : k ≤ v := hv.lh ▸ len_le v
    exact symbol_node_EV (by norm_num) hk (hL k f hf) hvec

theorem isSemiterm_le_EV (hL : SmallCodesV V L) {n t : V} (ht : IsSemiterm L n t) :
    t ≤ EV (8 * termLen L t) := (isUTerm_le_EV hL t ht.isUTerm).2

theorem one_le_termLen_V {n t : V} (ht : IsSemiterm L n t) : 1 ≤ termLen L t := by
  rcases IsUTerm.case ht.isUTerm with ⟨z, rfl⟩ | ⟨x, rfl⟩ | ⟨k, f, v, hf, hv, rfl⟩
  · simp
  · simp
  · rw [termLen_func hf hv]; exact le_add_self

end terms

/-! ### Formula codes are bounded by `EV (8 · formulaLen)` -/

section formulas

variable {L : Language} [L.Encodable] [L.LORDefinable]

/-- **Formula codes are proper**: `IsSemiformula L n p → p ≤ EV (8 · formulaLen L p)`
(with `1 ≤ formulaLen`). -/
theorem isSemiformula_le_EV (hL : SmallCodesV V L) (hR : SmallRelCodesV V L) {n p : V}
    (hp : IsSemiformula L n p) : 1 ≤ formulaLen L p ∧ p ≤ EV (8 * formulaLen L p) := by
  apply IsSemiformula.sigma1_structural_induction
    (P := fun _ p ↦ 1 ≤ formulaLen L p ∧ p ≤ EV (8 * formulaLen L p)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hp
  · definability
  · intro n k r v hr hv
    rw [formulaLen_rel hr hv.isUTerm]
    refine ⟨le_add_self, ?_⟩
    have hvec : v ≤ EV (8 * listSum (termLenVec L k v) + 2) :=
      vec_EV k v _ hv.lh (len_termLenVec hv.isUTerm) fun i hi ↦ by
        rw [nth_termLenVec hv.isUTerm hi]; exact isUTerm_le_EV hL _ (hv.nth hi).isUTerm
    have hk : k ≤ v := hv.lh ▸ len_le v
    exact symbol_node_EV (by norm_num) hk (hR k r hr) hvec
  · intro n k r v hr hv
    rw [formulaLen_nrel hr hv.isUTerm]
    refine ⟨le_add_self, ?_⟩
    have hvec : v ≤ EV (8 * listSum (termLenVec L k v) + 2) :=
      vec_EV k v _ hv.lh (len_termLenVec hv.isUTerm) fun i hi ↦ by
        rw [nth_termLenVec hv.isUTerm hi]; exact isUTerm_le_EV hL _ (hv.nth hi).isUTerm
    have hk : k ≤ v := hv.lh ▸ len_le v
    exact symbol_node_EV (by norm_num) hk (hR k r hr) hvec
  · intro n
    rw [formulaLen_verum]
    refine ⟨le_refl _, ?_⟩
    unfold qqVerum
    have h := pair_EV (s := 0) (a := (2 : V)) (b := 0) (le_of_eq EV_zero.symm) (zero_le)
    exact le_trans h (EV_mono (by norm_num))
  · intro n
    rw [formulaLen_falsum]
    refine ⟨le_refl _, ?_⟩
    unfold qqFalsum
    have h := pair_EV (s := 1) (a := (3 : V)) (b := 0) (by rw [EV_one]; norm_num) (zero_le)
    exact le_trans h (EV_mono (by norm_num))
  · intro n p q hp hq ihp ihq
    rw [formulaLen_and hp.isUFormula hq.isUFormula]
    refine ⟨le_add_self, ?_⟩
    unfold qqAnd
    have hp' : p ≤ EV (8 * (formulaLen L p + formulaLen L q)) :=
      le_trans ihp.2 (EV_mono (by rw [mul_add]; exact le_self_add))
    have hq' : q ≤ EV (8 * (formulaLen L p + formulaLen L q)) :=
      le_trans ihq.2 (EV_mono (by rw [mul_add]; exact le_add_self))
    have h1 := pair_EV_le hp' hq'
    have h4 : (4 : V) ≤ EV (8 * (formulaLen L p + formulaLen L q) + 2) := four_le_EV (le_trans (by norm_num) le_add_self)
    exact le_trans (pair_EV h4 h1) (EV_mono (le_trans (le_of_eq (by ring))
      (add_le_eight_mul_succ (formulaLen L p + formulaLen L q) (c := 4) (by norm_num))))
  · intro n p q hp hq ihp ihq
    rw [formulaLen_or hp.isUFormula hq.isUFormula]
    refine ⟨le_add_self, ?_⟩
    unfold qqOr
    have hp' : p ≤ EV (8 * (formulaLen L p + formulaLen L q)) :=
      le_trans ihp.2 (EV_mono (by rw [mul_add]; exact le_self_add))
    have hq' : q ≤ EV (8 * (formulaLen L p + formulaLen L q)) :=
      le_trans ihq.2 (EV_mono (by rw [mul_add]; exact le_add_self))
    have h1 := pair_EV_le hp' hq'
    have h5 : (5 : V) ≤ EV (8 * (formulaLen L p + formulaLen L q) + 2) :=
      le_trans (by norm_num) (eight_le_EV le_add_self)
    exact le_trans (pair_EV h5 h1) (EV_mono (le_trans (le_of_eq (by ring))
      (add_le_eight_mul_succ (formulaLen L p + formulaLen L q) (c := 4) (by norm_num))))
  · intro n p hp ihp
    rw [formulaLen_all hp.isUFormula]
    refine ⟨le_add_self, ?_⟩
    unfold qqAll
    have h6 : (6 : V) ≤ EV (8 * formulaLen L p) :=
      le_trans (by norm_num) (eight_le_EV (le_trans (by norm_num) (le_mul_of_one_le_right (by norm_num) ihp.1)))
    exact le_trans (pair_EV h6 ihp.2) (EV_mono (add_le_eight_mul_succ (formulaLen L p) (c := 2) (by norm_num)))
  · intro n p hp ihp
    rw [formulaLen_exs hp.isUFormula]
    refine ⟨le_add_self, ?_⟩
    unfold qqExs
    have h7 : (7 : V) ≤ EV (8 * formulaLen L p) :=
      le_trans (by norm_num) (eight_le_EV (le_trans (by norm_num) (le_mul_of_one_le_right (by norm_num) ihp.1)))
    exact le_trans (pair_EV h7 ihp.2) (EV_mono (add_le_eight_mul_succ (formulaLen L p) (c := 2) (by norm_num)))

theorem isFormula_le_EV (hL : SmallCodesV V L) (hR : SmallRelCodesV V L) {p : V}
    (hp : IsFormula L p) : p ≤ EV (8 * formulaLen L p) := (isSemiformula_le_EV hL hR hp).2

theorem one_le_formulaLen_V {n p : V} (hp : IsSemiformula L n p) : 1 ≤ formulaLen L p := by
  rcases IsSemiformula.case_iff.mp hp with
    ⟨k, R, v, hR, hv, rfl⟩ | ⟨k, R, v, hR, hv, rfl⟩ | rfl | rfl | ⟨p₁, p₂, h₁, h₂, rfl⟩ |
    ⟨p₁, p₂, h₁, h₂, rfl⟩ | ⟨p₁, h₁, rfl⟩ | ⟨p₁, h₁, rfl⟩
  · rw [formulaLen_rel hR hv.isUTerm]; exact le_add_self
  · rw [formulaLen_nrel hR hv.isUTerm]; exact le_add_self
  · simp
  · simp
  · rw [formulaLen_and h₁.isUFormula h₂.isUFormula]; exact le_add_self
  · rw [formulaLen_or h₁.isUFormula h₂.isUFormula]; exact le_add_self
  · rw [formulaLen_all h₁.isUFormula]; exact le_add_self
  · rw [formulaLen_exs h₁.isUFormula]; exact le_add_self

end formulas


/-! ### Sequent codes (bit-sets of formula codes) are bounded by `FV (8 · setLen + 1)` -/

section sequents

variable {L : Language} [L.Encodable] [L.LORDefinable]

/-- The partial sums of `setLen` are monotone in the index. -/
lemma setLenAux_le_add (s i : V) : ∀ j, setLenAux L s i ≤ setLenAux L s (i + j) := by
  intro j
  induction j using ISigma1.sigma1_succ_induction with
  | hP => definability
  | zero => simp
  | succ j ih =>
    rw [← add_assoc, setLenAux_succ]
    split_ifs
    · exact le_trans ih le_self_add
    · exact ih

lemma setLenAux_mono {s i j : V} (h : i ≤ j) : setLenAux L s i ≤ setLenAux L s j := by
  obtain ⟨k, rfl⟩ := exists_add_of_le h
  exact setLenAux_le_add s i k

/-- A member's symbol count is at most the sequent's. -/
lemma formulaLen_le_setLen_of_mem {p s : V} (h : p ∈ s) : formulaLen L p ≤ setLen L s := by
  have h1 : formulaLen L p ≤ setLenAux L s (p + 1) := by
    rw [setLenAux_succ_of_mem h]; exact le_add_self
  exact le_trans h1 (setLenAux_mono (lt_iff_succ_le.mp (lt_of_mem h)))

/-- **Sequent codes are proper**: `IsFormulaSet L s → s ≤ FV (8 · setLen L s + 1)`. -/
theorem isFormulaSet_le_FV (hL : SmallCodesV V L) (hR : SmallRelCodesV V L) {s : V}
    (hs : IsFormulaSet L s) : s ≤ FV (8 * setLen L s + 1) := by
  have h1 : s < Exp.exp (EV (8 * setLen L s) + 1) := by
    rw [lt_exp_iff]
    intro j hj
    have hjE : j ≤ EV (8 * setLen L s) :=
      le_trans (isFormula_le_EV hL hR (hs j hj))
        (EV_mono (mul_le_mul_of_nonneg_left (formulaLen_le_setLen_of_mem hj) (by positivity)))
    exact lt_of_le_of_lt hjE (lt_add_one _)
  exact le_trans h1.le (exp_EV_succ_le_FV _)

end sequents

/-! ### Derivation codes are bounded by `FV (12 · dlen)` -/

section derivations

variable {L : Language} [L.Encodable] [L.LORDefinable]

lemma DlenGraph.one_le {d n : V} (h : DlenGraph L d n) : 1 ≤ n := by
  rcases DlenGraph.case_iff.mp h with
    ⟨s, p, rfl, rfl⟩ | ⟨s, rfl, rfl⟩ | ⟨s, p, q, dp, dq, np, nq, _, _, rfl, rfl⟩ |
    ⟨s, p, q, d', n', _, rfl, rfl⟩ | ⟨s, p, d', n', _, rfl, rfl⟩ | ⟨s, p, t, d', n', _, rfl, rfl⟩ |
    ⟨s, d', n', _, rfl, rfl⟩ | ⟨s, d', n', _, rfl, rfl⟩ | ⟨s, p, d₁, d₂, n₁, n₂, _, _, rfl, rfl⟩ |
    ⟨s, p, rfl, rfl⟩ <;> exact le_add_self

/-- The conclusion sequent is charged by every node. -/
lemma DlenGraph.setLen_fstIdx_le {d n : V} (h : DlenGraph L d n) : setLen L (fstIdx d) ≤ n := by
  rcases DlenGraph.case_iff.mp h with
    ⟨s, p, rfl, rfl⟩ | ⟨s, rfl, rfl⟩ | ⟨s, p, q, dp, dq, np, nq, _, _, rfl, rfl⟩ |
    ⟨s, p, q, d', n', _, rfl, rfl⟩ | ⟨s, p, d', n', _, rfl, rfl⟩ | ⟨s, p, t, d', n', _, rfl, rfl⟩ |
    ⟨s, d', n', _, rfl, rfl⟩ | ⟨s, d', n', _, rfl, rfl⟩ | ⟨s, p, d₁, d₂, n₁, n₂, _, _, rfl, rfl⟩ |
    ⟨s, p, rfl, rfl⟩ <;> simp only [fstIdx_axL, fstIdx_verumIntro, fstIdx_andIntro, fstIdx_orIntro,
      fstIdx_allIntro, fstIdx_exsIntro, fstIdx_wkRule, fstIdx_shiftRule, fstIdx_cutRule, fstIdx_axm] <;>
    first | exact le_self_add | (simp only [add_assoc]; exact le_self_add)

/-- A node `⟪s, t, r⟫ + 1` with `s, r ≤ FV X` and tag `t ≤ 9` is below `FV (X + 4)`. -/
lemma node_FV {s t r X : V} (hX : 1 ≤ X) (hs : s ≤ FV X) (ht : t ≤ 9) (hr : r ≤ FV X) :
    ⟪s, t, r⟫ + 1 ≤ FV (X + 4) := by
  have ht' : t ≤ FV X := le_trans ht (le_trans (by norm_num) (sixteen_le_FV hX))
  have h1 := pair_FV_le ht' hr
  have h2 := pair_FV (le_trans hs (FV_mono le_self_add)) h1
  exact le_trans h2 (FV_mono (le_of_eq (by ring)))

lemma le_FV_add {x X c : V} (h : x ≤ FV X) : x ≤ FV (X + c) := le_trans h (FV_mono le_self_add)

lemma add_le_twelve_mul_succ (Y : V) {c : V} (hc : c ≤ 12) : 12 * Y + c ≤ 12 * (Y + 1) := by
  rw [mul_add, mul_one]; exact add_le_add le_rfl hc

/-- The rule-node shape: `s ≤ FV (12 Y)`, the rest `r ≤ FV X` with `12 Y ≤ X ≤ 12 Y + 8`. -/
lemma rule_node_FV {s t r X Y : V} (hY : 1 ≤ Y) (hYX : 12 * Y ≤ X) (hX : X + 4 ≤ 12 * (Y + 1))
    (hs : s ≤ FV (12 * Y)) (ht : t ≤ 9) (hr : r ≤ FV X) : ⟪s, t, r⟫ + 1 ≤ FV (12 * (Y + 1)) := by
  have hX1 : 1 ≤ X := le_trans hY (le_trans (le_mul_of_one_le_left zero_le (by norm_num)) hYX)
  exact le_trans (node_FV hX1 (le_trans hs (FV_mono hYX)) ht hr) (FV_mono hX)

lemma eight_succ_le_twelve {sl n Y : V} (hn : 1 ≤ n) (hY : sl + n ≤ Y) : 8 * sl + 1 ≤ 12 * Y := by
  calc 8 * sl + 1 ≤ 12 * sl + 12 * n :=
        add_le_add (mul_le_mul_of_nonneg_right (by norm_num) zero_le)
          (le_trans (by norm_num : (1 : V) ≤ 12) (le_mul_of_one_le_right (by norm_num) hn))
    _ = 12 * (sl + n) := by ring
    _ ≤ 12 * Y := mul_le_mul_of_nonneg_left hY (by positivity)

lemma eight_succ_le_twelve_self {sl : V} (h : 1 ≤ sl) : 8 * sl + 1 ≤ 12 * sl := by
  calc 8 * sl + 1 ≤ 8 * sl + 4 * sl :=
        add_le_add le_rfl (le_trans (by norm_num : (1 : V) ≤ 4) (le_mul_of_one_le_right (by norm_num) h))
    _ = 12 * sl := by ring

lemma eight_le_twelve_of_le {a b Y : V} (h : a ≤ b) (hY : b ≤ Y) : 8 * a ≤ 12 * Y :=
  mul_le_mul (by norm_num) (le_trans h hY) zero_le zero_le

lemma formula_le_FV (hL : SmallCodesV V L) (hR : SmallRelCodesV V L) {n p X : V}
    (hp : IsSemiformula L n p) (h : 8 * formulaLen L p ≤ X) : p ≤ FV X :=
  le_trans (isSemiformula_le_EV hL hR hp).2 (le_trans (EV_le_FV _) (FV_mono h))

lemma term_le_FV (hL : SmallCodesV V L) {n t X : V} (ht : IsSemiterm L n t)
    (h : 8 * termLen L t ≤ X) : t ≤ FV X :=
  le_trans (isSemiterm_le_EV hL ht) (le_trans (EV_le_FV _) (FV_mono h))


variable {T : Theory L} [T.Δ₁]

/-- **Derivation codes are proper**, inside `V`: a `T`-derivation code of length `n`
(`DlenGraph L d n`) is below `FV (12 n)`. By `Derivation.induction1` on the `Π₁` predicate. -/
theorem derivation_le_FV (hL : SmallCodesV V L) (hR : SmallRelCodesV V L) {d : V}
    (hd : Derivation T d) : ∀ n, DlenGraph L d n → d ≤ FV (12 * n) := by
  apply Derivation.induction1 𝚷 (T := T) (P := fun d ↦ ∀ n, DlenGraph L d n → d ≤ FV (12 * n))
    (by definability) hd
  -- axL
  · intro s hs p hp _ n hn
    obtain rfl := DlenGraph.axL_iff.mp hn
    have hsl : 1 ≤ setLen L s :=
      le_trans (one_le_formulaLen_V (hs p hp)) (formulaLen_le_setLen_of_mem hp)
    have hs' : s ≤ FV (12 * setLen L s) :=
      le_trans (isFormulaSet_le_FV hL hR hs) (FV_mono (eight_succ_le_twelve_self hsl))
    have hp' : p ≤ FV (12 * setLen L s) :=
      formula_le_FV hL hR (hs p hp) (eight_le_twelve_of_le (formulaLen_le_setLen_of_mem hp) le_rfl)
    unfold Bootstrapping.axL
    exact rule_node_FV hsl le_rfl (add_le_twelve_mul_succ _ (by norm_num)) hs' (by norm_num) hp'
  -- verumIntro
  · intro s hs hv n hn
    obtain rfl := DlenGraph.verumIntro_iff.mp hn
    have hsl : 1 ≤ setLen L s :=
      le_trans (one_le_formulaLen_V (hs _ hv)) (formulaLen_le_setLen_of_mem hv)
    have hs' : s ≤ FV (12 * setLen L s) :=
      le_trans (isFormulaSet_le_FV hL hR hs) (FV_mono (eight_succ_le_twelve_self hsl))
    unfold Bootstrapping.verumIntro
    exact rule_node_FV hsl le_rfl (add_le_twelve_mul_succ _ (by norm_num)) hs' (by norm_num) zero_le
  -- andIntro
  · intro s hs p q dp dq hpq hdp hdq ihp ihq n hn
    obtain ⟨np, nq, gp, gq, rfl⟩ := DlenGraph.andIntro_iff.mp hn
    have hnp := gp.one_le
    have hpq' : IsFormula L p ∧ IsFormula L q := by simpa using hs _ hpq
    have hfl : formulaLen L p + formulaLen L q + 1 ≤ setLen L s := by
      have := formulaLen_le_setLen_of_mem (L := L) hpq
      rwa [formulaLen_and hpq'.1.isUFormula hpq'.2.isUFormula] at this
    set Y := setLen L s + np + nq with hYdef
    have hsY : setLen L s + np ≤ Y := le_self_add
    have hslY : setLen L s ≤ Y := le_trans le_self_add hsY
    have hY : 1 ≤ Y := le_trans hnp (le_trans le_add_self hsY)
    have hs' : s ≤ FV (12 * Y) :=
      le_trans (isFormulaSet_le_FV hL hR hs) (FV_mono (eight_succ_le_twelve hnp hsY))
    have hp' : p ≤ FV (12 * Y) := formula_le_FV hL hR hpq'.1
      (eight_le_twelve_of_le (le_trans (le_trans le_self_add le_self_add) hfl) hslY)
    have hq' : q ≤ FV (12 * Y) := formula_le_FV hL hR hpq'.2
      (eight_le_twelve_of_le (le_trans (le_trans le_add_self le_self_add) hfl) hslY)
    have hdp' : dp ≤ FV (12 * Y) := le_trans (ihp np gp)
      (FV_mono (mul_le_mul_of_nonneg_left (le_trans le_add_self hsY) (by positivity)))
    have hdq' : dq ≤ FV (12 * Y) := le_trans (ihq nq gq)
      (FV_mono (mul_le_mul_of_nonneg_left le_add_self (by positivity)))
    have h1 := pair_FV_le hdp' hdq'
    have h2 := pair_FV_le (le_trans hq' (FV_mono le_self_add)) h1
    have h3 := pair_FV_le (le_FV_add (le_FV_add hp')) h2
    unfold Bootstrapping.andIntro
    exact rule_node_FV hY (by simp only [add_assoc]; exact le_self_add)
      (le_trans (le_of_eq (by ring)) (add_le_twelve_mul_succ Y (c := 10) (by norm_num)))
      hs' (by norm_num) h3
  -- orIntro
  · intro s hs p q d' hpq hd' ih n hn
    obtain ⟨n', g, rfl⟩ := DlenGraph.orIntro_iff.mp hn
    have hn' := g.one_le
    have hpq' : IsFormula L p ∧ IsFormula L q := by simpa using hs _ hpq
    have hfl : formulaLen L p + formulaLen L q + 1 ≤ setLen L s := by
      have := formulaLen_le_setLen_of_mem (L := L) hpq
      rwa [formulaLen_or hpq'.1.isUFormula hpq'.2.isUFormula] at this
    set Y := setLen L s + n' with hYdef
    have hslY : setLen L s ≤ Y := le_self_add
    have hY : 1 ≤ Y := le_trans hn' le_add_self
    have hs' : s ≤ FV (12 * Y) :=
      le_trans (isFormulaSet_le_FV hL hR hs) (FV_mono (eight_succ_le_twelve hn' le_rfl))
    have hp' : p ≤ FV (12 * Y) := formula_le_FV hL hR hpq'.1
      (eight_le_twelve_of_le (le_trans (le_trans le_self_add le_self_add) hfl) hslY)
    have hq' : q ≤ FV (12 * Y) := formula_le_FV hL hR hpq'.2
      (eight_le_twelve_of_le (le_trans (le_trans le_add_self le_self_add) hfl) hslY)
    have hd'' : d' ≤ FV (12 * Y) := le_trans (ih n' g)
      (FV_mono (mul_le_mul_of_nonneg_left le_add_self (by positivity)))
    have h1 := pair_FV_le hq' hd''
    have h2 := pair_FV_le (le_trans hp' (FV_mono le_self_add)) h1
    unfold Bootstrapping.orIntro
    exact rule_node_FV hY (by simp only [add_assoc]; exact le_self_add)
      (le_trans (le_of_eq (by ring)) (add_le_twelve_mul_succ Y (c := 8) (by norm_num)))
      hs' (by norm_num) h2
  -- allIntro
  · intro s hs p d' hp hd' ih n hn
    obtain ⟨n', g, rfl⟩ := DlenGraph.allIntro_iff.mp hn
    have hn' := g.one_le
    have hp' : IsSemiformula L 1 p := by simpa using hs _ hp
    have hfl : formulaLen L p + 1 ≤ setLen L s := by
      have := formulaLen_le_setLen_of_mem (L := L) hp
      rwa [formulaLen_all hp'.isUFormula] at this
    set Y := setLen L s + n' with hYdef
    have hslY : setLen L s ≤ Y := le_self_add
    have hY : 1 ≤ Y := le_trans hn' le_add_self
    have hs' : s ≤ FV (12 * Y) :=
      le_trans (isFormulaSet_le_FV hL hR hs) (FV_mono (eight_succ_le_twelve hn' le_rfl))
    have hp'' : p ≤ FV (12 * Y) := formula_le_FV hL hR hp'
      (eight_le_twelve_of_le (le_trans le_self_add hfl) hslY)
    have hd'' : d' ≤ FV (12 * Y) := le_trans (ih n' g)
      (FV_mono (mul_le_mul_of_nonneg_left le_add_self (by positivity)))
    have h1 := pair_FV_le hp'' hd''
    unfold Bootstrapping.allIntro
    exact rule_node_FV hY le_self_add
      (le_trans (le_of_eq (by ring)) (add_le_twelve_mul_succ Y (c := 6) (by norm_num)))
      hs' (by norm_num) h1
  -- exsIntro
  · intro s hs p t d' hp ht hd' ih n hn
    obtain ⟨n', g, rfl⟩ := DlenGraph.exsIntro_iff.mp hn
    have hn' := g.one_le
    have hp' : IsSemiformula L 1 p := by simpa using hs _ hp
    have hfl : formulaLen L p + 1 ≤ setLen L s := by
      have := formulaLen_le_setLen_of_mem (L := L) hp
      rwa [formulaLen_exs hp'.isUFormula] at this
    set Y := setLen L s + termLen L t + n' with hYdef
    have hsY : setLen L s + n' ≤ Y := add_le_add le_self_add le_rfl
    have hslY : setLen L s ≤ Y := le_trans le_self_add hsY
    have htY : termLen L t ≤ Y := le_trans le_add_self le_self_add
    have hY : 1 ≤ Y := le_trans hn' le_add_self
    have hs' : s ≤ FV (12 * Y) :=
      le_trans (isFormulaSet_le_FV hL hR hs) (FV_mono (eight_succ_le_twelve hn' hsY))
    have hp'' : p ≤ FV (12 * Y) := formula_le_FV hL hR hp'
      (eight_le_twelve_of_le (le_trans le_self_add hfl) hslY)
    have ht' : t ≤ FV (12 * Y) := term_le_FV hL ht (eight_le_twelve_of_le le_rfl htY)
    have hd'' : d' ≤ FV (12 * Y) := le_trans (ih n' g)
      (FV_mono (mul_le_mul_of_nonneg_left le_add_self (by positivity)))
    have h1 := pair_FV_le ht' hd''
    have h2 := pair_FV_le (le_trans hp'' (FV_mono le_self_add)) h1
    unfold Bootstrapping.exsIntro
    exact rule_node_FV hY (by simp only [add_assoc]; exact le_self_add)
      (le_trans (le_of_eq (by ring)) (add_le_twelve_mul_succ Y (c := 8) (by norm_num)))
      hs' (by norm_num) h2
  -- wkRule
  · intro s hs d' _ _ ih n hn
    obtain ⟨n', g, rfl⟩ := DlenGraph.wkRule_iff.mp hn
    have hn' := g.one_le
    set Y := setLen L s + n' with hYdef
    have hY : 1 ≤ Y := le_trans hn' le_add_self
    have hs' : s ≤ FV (12 * Y) :=
      le_trans (isFormulaSet_le_FV hL hR hs) (FV_mono (eight_succ_le_twelve hn' le_rfl))
    have hd'' : d' ≤ FV (12 * Y) := le_trans (ih n' g)
      (FV_mono (mul_le_mul_of_nonneg_left le_add_self (by positivity)))
    unfold Bootstrapping.wkRule
    exact rule_node_FV hY le_rfl (add_le_twelve_mul_succ Y (c := 4) (by norm_num)) hs' (by norm_num) hd''
  -- shiftRule
  · intro s hs d' _ _ ih n hn
    obtain ⟨n', g, rfl⟩ := DlenGraph.shiftRule_iff.mp hn
    have hn' := g.one_le
    set Y := setLen L s + n' with hYdef
    have hY : 1 ≤ Y := le_trans hn' le_add_self
    have hs' : s ≤ FV (12 * Y) :=
      le_trans (isFormulaSet_le_FV hL hR hs) (FV_mono (eight_succ_le_twelve hn' le_rfl))
    have hd'' : d' ≤ FV (12 * Y) := le_trans (ih n' g)
      (FV_mono (mul_le_mul_of_nonneg_left le_add_self (by positivity)))
    unfold Bootstrapping.shiftRule
    exact rule_node_FV hY le_rfl (add_le_twelve_mul_succ Y (c := 4) (by norm_num)) hs' (by norm_num) hd''
  -- cutRule
  · intro s hs p d₁ d₂ hd₁ hd₂ ih₁ ih₂ n hn
    obtain ⟨n₁, n₂, g₁, g₂, rfl⟩ := DlenGraph.cutRule_iff.mp hn
    have hn₁ := g₁.one_le
    have hpF : IsFormula L p := (IsFormulaSet.insert_iff.mp hd₁.isFormulaSet).1
    have hfl : formulaLen L p ≤ n₁ := by
      have h1 : formulaLen L p ≤ setLen L (fstIdx d₁) := by
        rw [hd₁.1]; exact formulaLen_le_setLen_of_mem (by simp)
      exact le_trans h1 g₁.setLen_fstIdx_le
    set Y := setLen L s + n₁ + n₂ with hYdef
    have hsY : setLen L s + n₁ ≤ Y := le_self_add
    have hn₁Y : n₁ ≤ Y := le_trans le_add_self hsY
    have hY : 1 ≤ Y := le_trans hn₁ hn₁Y
    have hs' : s ≤ FV (12 * Y) :=
      le_trans (isFormulaSet_le_FV hL hR hs) (FV_mono (eight_succ_le_twelve hn₁ hsY))
    have hp' : p ≤ FV (12 * Y) := formula_le_FV hL hR hpF (eight_le_twelve_of_le hfl hn₁Y)
    have hd₁' : d₁ ≤ FV (12 * Y) := le_trans (ih₁ n₁ g₁)
      (FV_mono (mul_le_mul_of_nonneg_left hn₁Y (by positivity)))
    have hd₂' : d₂ ≤ FV (12 * Y) := le_trans (ih₂ n₂ g₂)
      (FV_mono (mul_le_mul_of_nonneg_left le_add_self (by positivity)))
    have h1 := pair_FV_le hd₁' hd₂'
    have h2 := pair_FV_le (le_trans hp' (FV_mono le_self_add)) h1
    unfold Bootstrapping.cutRule
    exact rule_node_FV hY (by simp only [add_assoc]; exact le_self_add)
      (le_trans (le_of_eq (by ring)) (add_le_twelve_mul_succ Y (c := 8) (by norm_num)))
      hs' (by norm_num) h2
  -- axm
  · intro s hs p hp _ n hn
    obtain rfl := DlenGraph.axm_iff.mp hn
    have hsl : 1 ≤ setLen L s :=
      le_trans (one_le_formulaLen_V (hs p hp)) (formulaLen_le_setLen_of_mem hp)
    have hs' : s ≤ FV (12 * setLen L s) :=
      le_trans (isFormulaSet_le_FV hL hR hs) (FV_mono (eight_succ_le_twelve_self hsl))
    have hp' : p ≤ FV (12 * setLen L s) :=
      formula_le_FV hL hR (hs p hp) (eight_le_twelve_of_le (formulaLen_le_setLen_of_mem hp) le_rfl)
    unfold Bootstrapping.axm
    exact rule_node_FV hsl le_rfl (add_le_twelve_mul_succ _ (by norm_num)) hs' (by norm_num) hp'

/-- `Derivation T d → d ≤ FV (12 · dlen T d)`. -/
theorem derivation_le_FV_dlen (hL : SmallCodesV V L) (hR : SmallRelCodesV V L) {d : V}
    (hd : Derivation T d) : d ≤ FV (12 * dlen T d) :=
  derivation_le_FV hL hR hd _ (dlen_graph hd)

end derivations

/-! ### Properness inside every model -/

section properness

variable {L : Language} [L.Encodable] [L.LORDefinable]

/-- **Properness inside `V`**, for every Δ₁ theory over a language with small symbol codes:
a `T`-proof code of length `≤ k` is below `fbound k = FV (12 k) + 1`. No quotes: the chain
term → formula → sequent → derivation is redone by the internal induction principles. -/
theorem properV_of_small (hL : SmallCodesV V L) (hR : SmallRelCodesV V L) (T : Theory L) [T.Δ₁] :
    ProperV V T := by
  intro k d φ hd hk
  rw [fbound_eq_FV]
  exact lt_of_le_of_lt
    (le_trans (derivation_le_FV_dlen hL hR hd.2) (FV_mono (mul_le_mul_of_nonneg_left hk (by positivity))))
    (lt_add_one _)

/-- **`TAct` is proper inside every model of `IΣ₁`** — the hypothesis of `lenProvableV_cut_V`
discharged, V-generically. -/
theorem properV_TAct : ProperV V TAct := properV_of_small smallCodesV_LAct smallRelCodesV_LAct TAct

/-- Every Δ₁ arithmetic theory (e.g. `𝗣𝗔`, `𝗜𝚺₁`) is proper inside every model of `IΣ₁`. -/
theorem properV_LOR (T : ArithmeticTheory) [T.Δ₁] : ProperV V T :=
  properV_of_small smallCodesV_LOR smallRelCodesV_LOR T

end properness

/-! ### Consequences: the `LenProvableV` theorems without the properness hypothesis -/

section consequences

/-- **Bounded D2 on codes at `TAct`, inside every model of `IΣ₁`, unconditional**
(`LenProvableV`-shaped, uniform constants `c₁ = 10, c₀ = 9`). -/
theorem lenProvableV_cut_V' (a b φ ψ : V) (hφ : IsSemiformula LAct 0 φ) (hψ : IsSemiformula LAct 0 ψ) :
    LenProvableV TAct a (Bootstrapping.imp LAct φ ψ) → LenProvableV TAct b φ →
    LenProvableV TAct (a + b + 10 * (formulaLen LAct φ + formulaLen LAct ψ) + 9) ψ :=
  lenProvableV_cut_V properV_TAct a b φ ψ hφ hψ

/-- The sharp form, unconditional. -/
theorem lenProvableV_cut_V_sharp' {a b φ ψ : V} (hφ : IsFormula LAct φ) (hψ : IsFormula LAct ψ) :
    LenProvableV TAct a (Bootstrapping.imp LAct φ ψ) → LenProvableV TAct b φ →
    LenProvableV TAct (a + b + 5 * formulaLen LAct φ + 10 * formulaLen LAct ψ + 9) ψ :=
  lenProvableV_cut_V_sharp properV_TAct hφ hψ

/-- **The bridge**: for a proper theory the code bound of `LenProvableV` is invisible —
`LenDerivable T k φ ↔ LenProvableV T k φ` in every model. -/
theorem lenDerivable_iff_lenProvableV_of {L : Language} [L.Encodable] [L.LORDefinable]
    {T : Theory L} [T.Δ₁] (hP : ProperV V T) (k φ : V) :
    LenDerivable T k φ ↔ LenProvableV T k φ :=
  ⟨fun ⟨d, hd, hk⟩ ↦ ⟨d, hP k d φ hd hk, hd, hk⟩, fun ⟨d, _, hd, hk⟩ ↦ ⟨d, hd, hk⟩⟩

/-- **`LenDerivable TAct k φ ↔ LenProvableV TAct k φ`** in every model of `IΣ₁`: the Löb
argument's Σ₁ box (no code bound) and the evaluator's Δ₁ box agree. -/
theorem lenDerivable_iff_lenProvableV (k φ : V) :
    LenDerivable TAct k φ ↔ LenProvableV TAct k φ :=
  lenDerivable_iff_lenProvableV_of properV_TAct k φ

end consequences

end ArithS
