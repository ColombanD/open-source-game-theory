import ArithS.Assembly.Uniform

/-!
# ArithS.Assembly.Cell — the Löbian cell at ℕ (U9): Dupoc cooperates with itself, Cupod defects
against itself, in PA-`S`, for all large `k`, conditional on bounded inner necessitation

`Research/Notes/M4_BOUNDED_HBL/BRIEF.md` §6 (U9, steps 1–4). Everything is a theorem GIVEN
`BoundedInnerNec d` (Critch's assumption (d), `Assembly/Prep.lean` §6).

1. **The meta closure** (`exists_psi_instance_length`): from `pblt_uniform` —
   `TAct ⊢ ∀¹ (leF ↑k̂ #0 🡒 psi)` — a proof code at ℕ of some length `N₃`
   (`lenProvable_of_provable`), instantiated at `bnumT k` (`lenProvable_inst_size`, U3),
   the antecedent `numeral k̂ ≤ bnumT k` discharged by `NumeralFacts.lenProvable_le_bnumT`
   through one `Cut.lenProvable_mp`: `LenProvable fbound (K₀ + K₁·size k + K₂·size k²) TAct
   ⌜psi ⇜ ![bnumT k]⌝` for all `k ≥ k̂` — QUADRATIC in the bit length, which is why
   `gBudget k = ‖k‖³` (`Prep.lean`).
2. **Below the budget** (`quadratic_le_cube`, `size_eq_length`): `K₀ + K₁ s + K₂ s² ≤ s³` once
   `s ≥ K₀ + K₁ + K₂ + 1`, and `‖k‖ = Nat.size k` at ℕ; so for `k ≥ 2^{K₀+K₁+K₂+1}` the meta
   closure IS the box `□_{g k} psi(k)` the chain assumes (`quote_instB`, properness at ℕ).
3. **The cell** (`dupoc_self_coop`, `dupoc_finds_guard`): U8's chain at `V = ℕ`
   (`chain_V`, `chain_guard_V`) with `chainBound ≤ k` from `chainBound_poly` +
   `poly_size_le_eventually` — Critch's Theorem 3.7 in PA-`S`.

Every threshold and constant is EXISTENTIAL; `k₀` is "some standard number" and is never
quoted. At `V = ℕ`, `≤` is PeanoMinus's `le_def` while `<` is `Nat.lt`
(`HANDOVER_ARITHMETIZED_S.md` §6): the thresholds below are STRICT (`k₀ < k`, unambiguous), and
the V-generic statements of `Assembly/Uniform.lean` are fed through `le_def.mpr`.
-/

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open LAct

/-! ### 1. The bit length at ℕ -/

/-- Foundation's bit length at `ℕ` is `Nat.size`. -/
lemma size_eq_length (k : ℕ) : Nat.size k = ‖k‖ := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · obtain ⟨y, hy, hexp, hlt⟩ := log_pos (V := ℕ) hk
    have e : y = 2 ^ log k := by rw [← exp_of_exponential hexp, exp_nat_eq_two_pow]
    rw [length_of_pos hk]
    subst e
    apply le_antisymm
    · exact Nat.size_le.mpr (by rw [pow_succ]; omega)
    · exact Nat.lt_size.mpr (by rcases le_def.mp hy with h | h <;> omega)

/-- Transitivity of Foundation's `≤` at `ℕ`, instance-agnostic (`le_def` on both sides). -/
lemma le_def_trans {a b c : ℕ} (h₁ : a = b ∨ a < b) (h₂ : b = c ∨ b < c) : a = c ∨ a < c := by omega

/-- `K₀ + K₁ s + K₂ s² ≤ s³` once `s ≥ K₀ + K₁ + K₂ + 1`. -/
lemma quadratic_le_cube (K₀ K₁ K₂ s : ℕ) (hs : K₀ + K₁ + K₂ + 1 ≤ s) :
    K₀ + K₁ * s + K₂ * s * s ≤ s * s * s := by
  have h1 : 1 ≤ s := by omega
  have hss : s ≤ s * s := Nat.le_mul_of_pos_left s h1
  have h0 : K₀ ≤ K₀ * (s * s) := Nat.le_mul_of_pos_right K₀ (Nat.mul_pos h1 h1)
  have hK₁ : K₁ * s ≤ K₁ * (s * s) := Nat.mul_le_mul_left K₁ hss
  calc K₀ + K₁ * s + K₂ * s * s ≤ K₀ * (s * s) + K₁ * (s * s) + K₂ * (s * s) := by
        rw [Nat.mul_assoc K₂]; omega
    _ = (K₀ + K₁ + K₂) * (s * s) := by ring
    _ ≤ s * (s * s) := Nat.mul_le_mul_right _ (by omega)
    _ = s * s * s := by ring

/-! ### 2. The meta closure: a short proof of `psi(k)` at ℕ, quadratic in the bit length -/

/-- The length of a substitution instance at the binary numeral, at `ℕ`:
`flen (φ ⇜ ![bnumT k]) ≤ flen φ · (6·size k + 2)`. -/
lemma flen_subst_bnumT_le (φ : Semisentence LAct 1) (k : ℕ) :
    flen ((φ ⇜ ![Semiterm.lMap emb (bnumT k)] : Sentence LAct) : Proposition LAct) ≤
      flen (φ : Semiproposition LAct 1) * (6 * Nat.size k + 2) := by
  refine le_trans (flen_subst_le φ ![Semiterm.lMap emb (bnumT k)]) ?_
  refine Nat.mul_le_mul_left _ ?_
  rw [Fin.sum_univ_one]
  simp only [Matrix.cons_val_zero]
  rw [tlen_emb_lMap_bnumT]
  have := tlen_bnumT k
  omega

/-- **The meta closure (U9 steps 1–3)**: given bounded inner necessitation, there are standard
`k̂ K₀ K₁ K₂` with `LenProvable fbound (K₀ + K₁·size k + K₂·size k²) TAct ⌜psi ⇜ ![bnumT k]⌝`
for every `k > k̂` — the uniform theorem instantiated at `k` and its antecedent cut away. -/
theorem exists_psi_instance_length {d : ℕ} (hE : BoundedInnerNec d) :
    ∃ kHat K₀ K₁ K₂ : ℕ, ∀ k : ℕ, kHat < k →
      LenProvable (fbound : ℕ → ℕ) (K₀ + K₁ * Nat.size k + K₂ * Nat.size k * Nat.size k) TAct
        (⌜(psi ⇜ ![Semiterm.lMap emb (bnumT k)] : Sentence LAct)⌝ : ℕ) := by
  obtain ⟨kHat, hprov⟩ := pblt_uniform hE
  obtain ⟨N₃, hN₃⟩ := lenProvable_of_provable hprov
  obtain ⟨C₀, C₁, hle⟩ := lenProvable_le_bnumT kHat
  refine ⟨kHat,
    N₃ + 13 * flen (((leF (↑kHat) #0 : Semisentence LAct 1) 🡒 psi : Semisentence LAct 1) : Semiproposition LAct 1)
      + 8 + C₀ + 20 * tlen (Rew.emb (↑kHat : ClosedSemiterm LAct 0) : SyntacticSemiterm LAct 0) + 50
      + 20 * flen (psi : Semiproposition LAct 1) + 9,
    30 * flen (((leF (↑kHat) #0 : Semisentence LAct 1) 🡒 psi : Semisentence LAct 1) : Semiproposition LAct 1)
      + 126 + 60 * flen (psi : Semiproposition LAct 1),
    C₁, fun k hk ↦ ?_⟩
  -- step 1: instantiate the uniform theorem at `bnumT k`; step 2: the antecedent (`NumeralFacts`)
  have h1 := lenProvable_inst_size ((leF (↑kHat) #0 : Semisentence LAct 1) 🡒 psi) k hN₃
  have h2 := hle k (Nat.le_of_lt hk)
  -- abbreviations, introduced AFTER the facts so that they fold everywhere
  set fχ := flen (((leF (↑kHat) #0 : Semisentence LAct 1) 🡒 psi : Semisentence LAct 1) : Semiproposition LAct 1)
    with hfχ
  set fψ := flen (psi : Semiproposition LAct 1) with hfψ
  set a := tlen (Rew.emb (↑kHat : ClosedSemiterm LAct 0) : SyntacticSemiterm LAct 0) with ha
  set t : ClosedSemiterm LAct 0 := Semiterm.lMap emb (bnumT k) with ht
  set s := Nat.size k with hs
  have hχt : flen ((((leF (↑kHat) #0 : Semisentence LAct 1) 🡒 psi) ⇜ ![t] : Sentence LAct) : Proposition LAct)
      ≤ fχ * (6 * s + 2) := flen_subst_bnumT_le _ k
  have h1' : LenProvable (fbound : ℕ → ℕ) (N₃ + 5 * (fχ * (6 * s + 2)) + 3 * fχ + 6 * s + 8) TAct
      (⌜(((leF (↑kHat) #0 : Semisentence LAct 1) 🡒 psi) ⇜ ![t] : Sentence LAct)⌝ : ℕ) :=
    lenProvable_fbound_mono (by omega) h1
  rw [substs_leF_imp] at h1'
  -- step 3: cut
  have h3 := lenProvable_mp h1' h2
  refine lenProvable_fbound_mono ?_ h3
  -- the bookkeeping
  have hψt : flen ((psi ⇜ ![t] : Sentence LAct) : Proposition LAct) ≤ fψ * (6 * s + 2) :=
    flen_subst_bnumT_le psi k
  have hleF : flen ((leF (↑kHat) t : Sentence LAct) : Proposition LAct) ≤ 2 * a + 2 * (6 * s + 1) + 3 := by
    rw [flen_leF_sentence, ht, tlen_emb_lMap_bnumT]
    have : tlen (Rew.emb (bnumT k) : SyntacticSemiterm ℒₒᵣ 0) ≤ 6 * s + 1 := tlen_bnumT k
    omega
  calc _ ≤ N₃ + 5 * (fχ * (6 * s + 2)) + 3 * fχ + 6 * s + 8 + (C₀ + C₁ * s * s)
        + 10 * ((2 * a + 2 * (6 * s + 1) + 3) + fψ * (6 * s + 2)) + 9 := by gcongr
    _ = N₃ + 13 * fχ + 8 + C₀ + 20 * a + 50 + 20 * fψ + 9 + (30 * fχ + 126 + 60 * fψ) * s
        + C₁ * s * s := by ring

/-! ### 3. The cell -/

/-- **The cell, packaged (U9 steps 3–4)**: for all large `k`, both searchers find their guards
(`EvalGraph`, fuel 2) and both guard boxes hold — U8's chain at `V = ℕ` with `chainBound ≤ k`
from `chainBound_poly` + `poly_size_le_eventually`, and the meta closure as the box
`□_{g k} psi(k)` (`quote_instB`, properness at ℕ, `quadratic_le_cube`). -/
theorem cell_core {d : ℕ} (hE : BoundedInnerNec d) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      (EvalGraph 2 (Dupoc k) (Dupoc k) (Dupoc k) 0 ∧ EvalGraph 2 (Cupod k) (Cupod k) (Cupod k) 1) ∧
      (LenProvableV TAct k (guardCode (⌜GtmplA 0⌝ : ℕ) (Dupoc k) (Dupoc k)) ∧
        LenProvableV TAct k (guardCode (⌜GtmplA 1⌝ : ℕ) (Cupod k) (Cupod k))) := by
  obtain ⟨N₁, hN₁⟩ := exists_forward_length
  obtain ⟨Cψ, hCψ⟩ := hE.nec psi
  obtain ⟨C, hC⟩ := chainBound_poly N₁ d Cψ
  obtain ⟨kHat₁, hkHat₁⟩ := poly_size_le_eventually C (3 * d + 3)
  obtain ⟨kHat, K₀, K₁, K₂, hmeta⟩ := exists_psi_instance_length hE
  refine ⟨kHat₁ + kHat + 2 ^ (K₀ + K₁ + K₂ + 1), fun k hk ↦ ?_⟩
  have hnec : NecAt d Cψ ℕ := fun k ↦ hCψ ℕ k
  have h2pow : 2 ≤ 2 ^ (K₀ + K₁ + K₂ + 1) := Nat.le_self_pow (Nat.succ_ne_zero _) 2
  have h1k : 1 < k := by omega
  -- `1 ≤ ‖k‖` and the budget inequality, in Foundation's `≤`
  have hs1 := length_monotone (V := ℕ) (le_def.mpr (Or.inr h1k))
  rw [length_one] at hs1
  have hbound := le_def.mpr (le_def_trans (le_def.mp (hC ℕ k hs1))
    (le_def.mp (hkHat₁ ℕ k (le_def.mpr (Or.inr (by rw [natCast_nat]; omega))))))
  -- the meta closure, as the box on codes, below the budget
  have hbox : LenDerivable TAct (gBudget k) (instB (⌜psi⌝ : ℕ) k) := by
    have h := hmeta k (by omega)
    rw [← lenProvableV_nat, ← lenDerivable_iff_lenProvableV] at h
    have hq : instB (⌜psi⌝ : ℕ) k = ⌜(psi ⇜ ![Semiterm.lMap emb (bnumT k)] : Sentence LAct)⌝ := by
      have := quote_instB (V := ℕ) psi k
      rwa [natCast_nat] at this
    rw [← hq] at h
    refine lenDerivable_mono_V ?_ h
    have hsize : K₀ + K₁ + K₂ + 1 ≤ Nat.size k := Nat.lt_size.mpr (by omega)
    have hcube := quadratic_le_cube K₀ K₁ K₂ (Nat.size k) hsize
    unfold gBudget
    rw [← size_eq_length]
    exact le_def.mpr (Nat.eq_or_lt_of_le hcube)
  exact ⟨chain_V hnec (hN₁ ℕ) k hbound hbox, chain_guard_V hnec (hN₁ ℕ) k hbound hbox⟩

/-- **Critch's Theorem 3.7 in PA-`S`, conditional on bounded inner necessitation**: for all
large `k`, `Dupoc k` cooperates with itself and `Cupod k` defects against itself (fuel `2`). -/
theorem dupoc_self_coop {d : ℕ} (hE : BoundedInnerNec d) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 2 (Dupoc k) (Dupoc k) (Dupoc k) 0 ∧ EvalGraph 2 (Cupod k) (Cupod k) (Cupod k) 1 := by
  obtain ⟨k₀, h⟩ := cell_core hE
  exact ⟨k₀, fun k hk ↦ (h k hk).1⟩

/-- **The box form**: for all large `k`, Dupoc actually FINDS a proof of its guard against itself
within its budget `k` (and so does Cupod). -/
theorem dupoc_finds_guard {d : ℕ} (hE : BoundedInnerNec d) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      LenProvableV TAct k (guardCode (⌜GtmplA 0⌝ : ℕ) (Dupoc k) (Dupoc k)) ∧
      LenProvableV TAct k (guardCode (⌜GtmplA 1⌝ : ℕ) (Cupod k) (Cupod k)) := by
  obtain ⟨k₀, h⟩ := cell_core hE
  exact ⟨k₀, fun k hk ↦ (h k hk).2⟩

end ArithS
