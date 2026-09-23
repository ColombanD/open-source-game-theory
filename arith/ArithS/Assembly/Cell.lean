import ArithS.Assembly.Uniform

/-!
# ArithS.Assembly.Cell — the Löbian cell at ℕ (U9): Dupoc cooperates with itself, Cupod defects
against itself, in PA-`S`, for all large `k`, conditional on bounded inner necessitation

`Research/Notes/M4_BOUNDED_HBL/BRIEF.md` §6 (U9, steps 1–4). Everything is a theorem GIVEN
`BoundedInnerNec d` (Critch's assumption (d), `Assembly/Prep.lean` §6).

**Since 2026-09-23 (`ROUTE_B_SCOPE.md` §3 Phase 1) this file is an INSTANTIATION of
`Assembly/Family.lean`'s cell half at `p := pConj`, slack `(7, 8)`, Löb premise
`loebSound_pConj`.** The generic steps live there under the names `size_eq_length`,
`quadratic_le_cube`, `flen_subst_bnumT_le`, `exists_psiF_instance_length` and **`family_found`**
(the arithmetized `pblt_engine`: the family's box found within its budget with the slack to
spare, for all large `k : ℕ`); this file draws the cell from `family_found pConj` by the
∧-elimination (`pconj_both_V`, `pconj_guards_V`). Every theorem keeps its 2026-09-12 statement.

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
   (`family_found`) — Critch's Theorem 3.7 in PA-`S`.

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

/-! ### 1. The meta closure: a short proof of `psi(k)` at ℕ, quadratic in the bit length -/

/-- **The meta closure (U9 steps 1–3)**: given bounded inner necessitation, there are standard
`k̂ K₀ K₁ K₂` with `LenProvable fbound (K₀ + K₁·size k + K₂·size k²) TAct ⌜psi ⇜ ![bnumT k]⌝`
for every `k > k̂` — the uniform theorem instantiated at `k` and its antecedent cut away. -/
theorem exists_psi_instance_length {d : ℕ} (hE : BoundedInnerNec d) :
    ∃ kHat K₀ K₁ K₂ : ℕ, ∀ k : ℕ, kHat < k →
      LenProvable (fbound : ℕ → ℕ) (K₀ + K₁ * Nat.size k + K₂ * Nat.size k * Nat.size k) TAct
        (⌜(psi ⇜ ![Semiterm.lMap emb (bnumT k)] : Sentence LAct)⌝ : ℕ) :=
  exists_psiF_instance_length pConj hE loebSound_pConj

/-! ### 2. The cell -/

/-- The ∧-elimination slack of `pconj_both_V` at ℕ, below the family slack `(7, 8)` — in the
`le_def` shape (`Nat.le` in, Foundation's `≤` out), for VARIABLE lengths. -/
lemma pConj_slack_nat (a x y z k : ℕ) (hz : z = x + y + 1) (h : a + 7 + 8 * z ≤ k) :
    a + 8 * (x + y) + 7 = k ∨ a + 8 * (x + y) + 7 < k := by
  subst hz; omega

/-- **The cell, packaged (U9 steps 3–4)**: for all large `k`, both searchers find their guards
(`EvalGraph`, fuel 2) and both guard boxes hold — `family_found` at `pConj` (U8's chain at
`V = ℕ` with `chainBound ≤ k` and the meta closure as the box `□_{g k} psi(k)`), then the
∧-elimination on codes. -/
theorem cell_core {d : ℕ} (hE : BoundedInnerNec d) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      (EvalGraph 2 (Dupoc k) (Dupoc k) (Dupoc k) 0 ∧ EvalGraph 2 (Cupod k) (Cupod k) (Cupod k) 1) ∧
      (LenProvableV TAct k (guardCode (⌜GtmplA 0⌝ : ℕ) (Dupoc k) (Dupoc k)) ∧
        LenProvableV TAct k (guardCode (⌜GtmplA 1⌝ : ℕ) (Cupod k) (Cupod k))) := by
  obtain ⟨k₀, h⟩ := family_found pConj hE loebSound_pConj
  refine ⟨k₀, fun k hk ↦ ?_⟩
  obtain ⟨a, ha, hpc⟩ := h k hk
  have ha' := le_def.mpr (pConj_slack_nat a _ _ _ k (formulaLen_instB_pConj (V := ℕ) k) ha)
  exact ⟨pconj_both_V k a ha' hpc, pconj_guards_V k a ha' hpc⟩

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
