import ArithS.Cells.Common.Families
import ArithS.Necessitation.Package

/-!
# ArithS.Cells.Common.Khat — from `TAct ⊢ ∀¹ q` to "found at every large `k`": the `k̂`-chain

Consolidation stage 6 (`Research/Notes/ROUTE_B_CELLS_MAP.md`). The lemmas that turn a
`TAct`-theorem (or a box consequence) into a guard FOUND within the budget for all large `k`, MOVED here
unchanged (names, statements, proofs) from `Cells/CIMCIC`, `Cells/PositiveCells`, `Cells/KhatCells` and
`Cells/FlipCells`:

1. `linear_size_le_eventually` (ex-CIMCIC; `poly_size_le_eventually` at degree 1, the `^ 1` removed).
2. **The `k̂ = 0` case**: `tact_all_of_both` (a `∀¹ q` true in both readings is a `TAct`-theorem) and
   `found_of_all` (its instance at `binNumeral k` fits `k` for all large `k`, cost `K₀ + K₁·size k`) — the body
   of `pos_Cimcic_vs_Cimcic_guard`, which is now `found_of_all tact_proves_qCC`.
3. **The `k̂`-chain**: `found_of_all_V` (in EVERY model), `tact_all_above_of_both`,
   `exists_instance_length_above`, `found_of_all_above` (a guard true only above a threshold is found
   for all large `k`, cost `K₀ + K₁·size k + K₂·size k²`).
4. **Through another searcher's box**: `BoxConseq`, `loebSound_iff_boxConseq`, `box_conseq_uniform`,
   `substs_imp`, `total_le_eventually`, `found_of_box_conseq`.

Imports `Necessitation/Package` for `BoundedInnerNec` and the chain (`chain_core_VF`) and
`Common/Families` for `nat_le_of_le_def`.
-/

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open LAct

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ### 1. From `TAct ⊢ ∀¹ q` to "found at every large `k`" (the `k̂ = 0` case) -/

section closure

/-- **Linear functions of the bit length are eventually below `k`** (`poly_size_le_eventually` at
degree 1, with the `^ 1` removed in the V-generic instance — at ℕ the two `Monoid` instances on
`‖k‖ ^ 1` do not match syntactically). -/
theorem linear_size_le_eventually (C : ℕ) :
    ∃ kHat : ℕ, ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (k : V),
      (kHat : V) ≤ k → (C : V) * ‖k‖ ≤ k := by
  obtain ⟨kHat, h⟩ := poly_size_le_eventually C 1
  exact ⟨kHat, fun V _ _ k hk ↦ by have := h V k hk; rwa [pow_one] at this⟩

/-- **A `TAct`-theorem `∀¹ q` true in both readings, by completeness** (`tact_proves_qCC`'s shape). -/
theorem tact_all_of_both (q : Semisentence LAct 1)
    (hstd : ∀ (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (x : M),
      Semiformula.Eval (s := stdReadingV M) ![x] Empty.elim q)
    (hswap : ∀ (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (x : M),
      Semiformula.Eval (s := swappedReading M) ![x] Empty.elim q) :
    TAct ⊢ ∀¹ q := by
  refine TAct_complete_of_readings _ fun M _ _ ↦ ?_
  have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
  constructor
  · simp only [Semiformula.eval_all]
    intro x
    rw [← stdReadingV_eq_stdReading]
    exact hstd M x
  · simp only [Semiformula.eval_all]
    intro x
    exact hswap M x

/-- **The instance of a `TAct`-theorem `∀¹ q` at `binNumeral k` fits the budget `k` for all large `k`**
(`pos_Cimcic_vs_Cimcic_guard`'s body, generic in `q` and in the guard-code family `G`): the instance
costs `K₀ + K₁·size k` (`lenBoxNat_inst_size` + `formulaLenMeta_subst_binNumeralMeta_le`), below `k` eventually
(`linear_size_le_eventually`). -/
theorem found_of_all {q : Semisentence LAct 1} (hq : TAct ⊢ ∀¹ q) (G : ℕ → ℕ)
    (hG : ∀ k, G k = instB (⌜q⌝ : ℕ) k) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k → LenBox TAct k (G k) := by
  obtain ⟨N₃, hN₃⟩ := lenBoxNat_of_provable hq
  obtain ⟨kHat, hkHat⟩ :=
    linear_size_le_eventually (N₃ + 13 * formulaLenMeta (q : Semiproposition LAct 1) + 8 + 30 * formulaLenMeta (q : Semiproposition LAct 1) + 6)
  refine ⟨kHat + 1, fun k hk ↦ ?_⟩
  have h1 := lenBoxNat_inst_size q k hN₃
  have hqt := formulaLenMeta_subst_binNumeralMeta_le q k
  set fq := formulaLenMeta (q : Semiproposition LAct 1) with hfq
  set s := Nat.size k with hs
  have hs1 : 0 < s := Nat.lt_size.mpr (by rw [pow_zero]; omega)
  have hpoly := hkHat ℕ k (le_def.mpr (Or.inr (by rw [natCast_nat]; omega)))
  rw [natCast_nat, ← size_eq_length] at hpoly
  have hpoly' : (N₃ + 13 * fq + 8 + 30 * fq + 6) * s ≤ k := by
    rcases le_def.mp hpoly with h | h
    · exact Nat.le_of_eq h
    · exact Nat.le_of_lt h
  have hle : N₃ + 5 * formulaLenMeta ((q ⇜ ![Semiterm.lMap emb (binNumeralMeta k)] : Sentence LAct) : Proposition LAct)
      + 3 * fq + 6 * s + 8 ≤ k := by
    calc N₃ + 5 * formulaLenMeta ((q ⇜ ![Semiterm.lMap emb (binNumeralMeta k)] : Sentence LAct) : Proposition LAct)
          + 3 * fq + 6 * s + 8
        ≤ N₃ + 5 * (fq * (6 * s + 2)) + 3 * fq + 6 * s + 8 := by gcongr
      _ = (N₃ + 13 * fq + 8) + (30 * fq + 6) * s := by ring
      _ ≤ (N₃ + 13 * fq + 8) * s + (30 * fq + 6) * s := by
          gcongr; exact Nat.le_mul_of_pos_right _ hs1
      _ = (N₃ + 13 * fq + 8 + 30 * fq + 6) * s := by ring
      _ ≤ k := hpoly'
  have h2 := lenBoxNat_codeBound_mono hle h1
  rw [← lenBox_nat] at h2
  have hq' : instB (⌜q⌝ : ℕ) k = ⌜(q ⇜ ![Semiterm.lMap emb (binNumeralMeta k)] : Sentence LAct)⌝ := by
    have := quote_instB (V := ℕ) q k
    rwa [natCast_nat] at this
  rw [hG, hq']
  exact h2

end closure

/-! ### 2. The `k̂`-chain -/

section chain

/-- **A `TAct`-theorem `∀¹ q` is found at every large budget, in EVERY model** (the V-generic
`found_of_all`): the proof of `∀¹ q` is a standard object (`exists_lenBoxUnbounded_V_of_proof`), its
instance at `binNumeral k` costs `N + 5·|q|·|binNumeral k| + 3·|q| + |binNumeral k| + 7` (`lenBoxUnbounded_instB_V'`), linear
in `‖k‖` (`termLen_binNumeral_le_V'`), below `k` above a standard threshold (`linear_size_le_eventually`). -/
theorem found_of_all_V {q : Semisentence LAct 1} (hq : TAct ⊢ ∀¹ q) :
    ∃ kHat : ℕ, ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (k : V),
      (kHat : V) ≤ k → LenBox TAct k (instB (⌜q⌝ : V) k) := by
  obtain ⟨N, hN⟩ := exists_lenBoxUnbounded_V_of_proof (∀¹ q) hq
  set fq := formulaLenMeta (q : Semiproposition LAct 1) with hfq
  obtain ⟨kHat, hkHat⟩ := linear_size_le_eventually (N + 35 * fq + 3 * fq + 7 + 7)
  refine ⟨kHat + 2, fun V _ _ k hk ↦ ?_⟩
  have hk₀ : (kHat : V) ≤ k := le_trans (by push_cast; exact le_self_add) hk
  have hs1 : 1 ≤ ‖k‖ := by
    have h1 : (1 : V) ≤ k := le_trans (by push_cast; exact le_add_left one_le_two) hk
    have := length_monotone h1
    rwa [length_one] at this
  have h := hN V
  rw [quote_all_sentence] at h
  have h1 := lenBoxUnbounded_instB_V' (V := V) (k := k) (Sentence.quote_isSemiformul₁ q) h
  rw [formulaLen_quote_semisentence_V, ← hfq] at h1
  have ht : termLen LAct (binNumeral k) ≤ 7 * ‖k‖ := termLen_binNumeral_le_V' hs1
  have hpoly := hkHat V k hk₀
  refine (lenBoxUnbounded_iff_lenBox _ _).mp (lenBoxUnbounded_mono_V (le_trans ?_ hpoly) h1)
  have e1 : (N : V) ≤ N * ‖k‖ := le_mul_of_one_le_right (by simp) hs1
  have e2 : (5 : V) * ((fq : V) * termLen LAct (binNumeral k)) ≤ 35 * fq * ‖k‖ := by
    calc (5 : V) * ((fq : V) * termLen LAct (binNumeral k)) ≤ 5 * ((fq : V) * (7 * ‖k‖)) := by gcongr
      _ = 35 * fq * ‖k‖ := by ring
  have e3 : (3 : V) * (fq : V) ≤ 3 * fq * ‖k‖ := le_mul_of_one_le_right (by simp) hs1
  have e4 : (7 : V) ≤ 7 * ‖k‖ := le_mul_of_one_le_right (by simp) hs1
  calc (N : V) + 5 * ((fq : V) * termLen LAct (binNumeral k)) + 3 * (fq : V) + termLen LAct (binNumeral k) + 7
      ≤ N * ‖k‖ + 35 * fq * ‖k‖ + 3 * fq * ‖k‖ + 7 * ‖k‖ + 7 * ‖k‖ := by gcongr
    _ = ((N + 35 * fq + 3 * fq + 7 + 7 : ℕ) : V) * ‖k‖ := by push_cast; ring

/-- **A conditional `TAct`-theorem from truth above a standard threshold, in both readings**
(`pblt_uniformF`'s closing step, for an arbitrary `q`): `TAct ⊢ ∀¹ (k̂ ≤ #0 🡒 q)`. -/
theorem tact_all_above_of_both (q : Semisentence LAct 1) (kHat : ℕ)
    (hstd : ∀ (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (x : M), (kHat : M) ≤ x →
      Semiformula.Eval (s := stdReadingV M) ![x] Empty.elim q)
    (hswap : ∀ (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (x : M), (kHat : M) ≤ x →
      Semiformula.Eval (s := swappedReading M) ![x] Empty.elim q) :
    TAct ⊢ ∀¹ ((leF (↑kHat) #0 : Semisentence LAct 1) 🡒 q) := by
  refine TAct_complete_of_readings _ fun M _ _ ↦ ?_
  have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
  constructor
  · simp only [Semiformula.eval_all, LogicalConnective.HomClass.map_imply, LogicalConnective.Prop.arrow_eq]
    intro x hx
    rw [← stdReadingV_eq_stdReading]
    exact hstd M x ((eval_leF_numeral_bvar _ stdReading_lMap_emb kHat x).mp hx)
  · simp only [Semiformula.eval_all, LogicalConnective.HomClass.map_imply, LogicalConnective.Prop.arrow_eq]
    intro x hx
    exact hswap M x ((eval_leF_numeral_bvar _ swappedReading_lMap_emb kHat x).mp hx)

/-- **The instance of a conditional `TAct`-theorem at `binNumeral k`, its antecedent cut away**
(`exists_psiF_instance_length` for an arbitrary consequent): cost `K₀ + K₁·size k + K₂·size k²`. -/
theorem exists_instance_length_above (q : Semisentence LAct 1) (kHat : ℕ)
    (hq : TAct ⊢ ∀¹ ((leF (↑kHat) #0 : Semisentence LAct 1) 🡒 q)) :
    ∃ K₀ K₁ K₂ : ℕ, ∀ k : ℕ, kHat < k →
      LenBoxNat (codeBound : ℕ → ℕ) (K₀ + K₁ * Nat.size k + K₂ * Nat.size k * Nat.size k) TAct
        (⌜(q ⇜ ![Semiterm.lMap emb (binNumeralMeta k)] : Sentence LAct)⌝ : ℕ) := by
  obtain ⟨N₃, hN₃⟩ := lenBoxNat_of_provable hq
  obtain ⟨C₀, C₁, hle⟩ := lenBoxNat_le_binNumeralMeta kHat
  refine ⟨N₃ + 13 * formulaLenMeta (((leF (↑kHat) #0 : Semisentence LAct 1) 🡒 q : Semisentence LAct 1) : Semiproposition LAct 1)
      + 8 + C₀ + 20 * termLenMeta (Rew.emb (↑kHat : ClosedSemiterm LAct 0) : SyntacticSemiterm LAct 0) + 50
      + 20 * formulaLenMeta (q : Semiproposition LAct 1) + 9,
    30 * formulaLenMeta (((leF (↑kHat) #0 : Semisentence LAct 1) 🡒 q : Semisentence LAct 1) : Semiproposition LAct 1)
      + 126 + 60 * formulaLenMeta (q : Semiproposition LAct 1),
    C₁, fun k hk ↦ ?_⟩
  have h1 := lenBoxNat_inst_size ((leF (↑kHat) #0 : Semisentence LAct 1) 🡒 q) k hN₃
  have h2 := hle k (Nat.le_of_lt hk)
  set fχ := formulaLenMeta (((leF (↑kHat) #0 : Semisentence LAct 1) 🡒 q : Semisentence LAct 1) : Semiproposition LAct 1)
    with hfχ
  set fψ := formulaLenMeta (q : Semiproposition LAct 1) with hfψ
  set a := termLenMeta (Rew.emb (↑kHat : ClosedSemiterm LAct 0) : SyntacticSemiterm LAct 0) with ha
  set t : ClosedSemiterm LAct 0 := Semiterm.lMap emb (binNumeralMeta k) with ht
  set s := Nat.size k with hs
  have hχt : formulaLenMeta ((((leF (↑kHat) #0 : Semisentence LAct 1) 🡒 q) ⇜ ![t] : Sentence LAct) : Proposition LAct)
      ≤ fχ * (6 * s + 2) := formulaLenMeta_subst_binNumeralMeta_le _ k
  have h1' : LenBoxNat (codeBound : ℕ → ℕ) (N₃ + 5 * (fχ * (6 * s + 2)) + 3 * fχ + 6 * s + 8) TAct
      (⌜(((leF (↑kHat) #0 : Semisentence LAct 1) 🡒 q) ⇜ ![t] : Sentence LAct)⌝ : ℕ) :=
    lenBoxNat_codeBound_mono (by omega) h1
  rw [substs_leF_imp] at h1'
  have h3 := lenBoxNat_mp h1' h2
  refine lenBoxNat_codeBound_mono ?_ h3
  have hψt : formulaLenMeta ((q ⇜ ![t] : Sentence LAct) : Proposition LAct) ≤ fψ * (6 * s + 2) :=
    formulaLenMeta_subst_binNumeralMeta_le q k
  have hleF : formulaLenMeta ((leF (↑kHat) t : Sentence LAct) : Proposition LAct) ≤ 2 * a + 2 * (6 * s + 1) + 3 := by
    rw [formulaLenMeta_leF_sentence, ht, termLenMeta_emb_lMap_binNumeralMeta]
    have : termLenMeta (Rew.emb (binNumeralMeta k) : SyntacticSemiterm ℒₒᵣ 0) ≤ 6 * s + 1 := termLenMeta_binNumeralMeta k
    omega
  calc _ ≤ N₃ + 5 * (fχ * (6 * s + 2)) + 3 * fχ + 6 * s + 8 + (C₀ + C₁ * s * s)
        + 10 * ((2 * a + 2 * (6 * s + 1) + 3) + fψ * (6 * s + 2)) + 9 := by gcongr
    _ = N₃ + 13 * fχ + 8 + C₀ + 20 * a + 50 + 20 * fψ + 9 + (30 * fχ + 126 + 60 * fψ) * s
        + C₁ * s * s := by ring

/-- **`found_of_all` with an antecedent — the `k̂`-chain**: a guard family that is the `binNumeral k`-instance
of a formula `q` provable in `TAct` for `k ≥ k̂` is found within the budget `k` for all large `k`
(the instance at `binNumeral k`, the antecedent discharged by `lenBoxNat_le_binNumeralMeta` through one
`Cut.lenBoxNat_mp`, the quadratic cost below `k` by `quadratic_le_cube` + `poly_size_le_eventually`). -/
theorem found_of_all_above {q : Semisentence LAct 1} (kHat : ℕ)
    (hq : TAct ⊢ ∀¹ ((leF (↑kHat) #0 : Semisentence LAct 1) 🡒 q)) (G : ℕ → ℕ)
    (hG : ∀ k, G k = instB (⌜q⌝ : ℕ) k) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k → LenBox TAct k (G k) := by
  obtain ⟨K₀, K₁, K₂, hmeta⟩ := exists_instance_length_above q kHat hq
  obtain ⟨kHat₁, hkHat₁⟩ := poly_size_le_eventually 1 3
  refine ⟨kHat₁ + kHat + 2 ^ (K₀ + K₁ + K₂ + 1), fun k hk ↦ ?_⟩
  have h2pow : 2 ≤ 2 ^ (K₀ + K₁ + K₂ + 1) := Nat.le_self_pow (Nat.succ_ne_zero _) 2
  have h := hmeta k (by omega)
  have hsize : K₀ + K₁ + K₂ + 1 ≤ Nat.size k := Nat.lt_size.mpr (by omega)
  have hcube := quadratic_le_cube K₀ K₁ K₂ (Nat.size k) hsize
  have hpoly := hkHat₁ ℕ k (le_def.mpr (Or.inr (by rw [natCast_nat]; omega)))
  rw [natCast_nat, ← size_eq_length, one_mul] at hpoly
  have hpoly' : Nat.size k ^ 3 ≤ k := by
    rcases le_def.mp hpoly with h | h
    · exact Nat.le_of_eq h
    · exact Nat.le_of_lt h
  have hle : K₀ + K₁ * Nat.size k + K₂ * Nat.size k * Nat.size k ≤ k := by
    refine le_trans hcube (le_trans (le_of_eq ?_) hpoly')
    ring
  have h2 := lenBoxNat_codeBound_mono hle h
  rw [← lenBox_nat] at h2
  have hq' : instB (⌜q⌝ : ℕ) k = ⌜(q ⇜ ![Semiterm.lMap emb (binNumeralMeta k)] : Sentence LAct)⌝ := by
    have := quote_instB (V := ℕ) q k
    rwa [natCast_nat] at this
  rw [hG, hq']
  exact h2

end chain

/-! ### 3. The box-consequence lemma: a guard whose truth needs another searcher's Löb-found guard -/

section boxConseq

/-- **A consequence of the family's box**: `q(k)` holds in both readings whenever the `k`-instance of `p`
has a `TAct`-proof with the slack to spare — the shape of `LoebSound`, with the conclusion `q` in place of
`p` (`LoebSound p S₀ S₁ = BoxConseq p p S₀ S₁`). For a guard `q` that describes ANOTHER searcher's play,
`q(k)` is true once that searcher's guard is found, i.e. once its family `p` has such a proof. -/
def BoxConseq (p q : Semisentence LAct 1) (S₀ S₁ : ℕ) : Prop :=
  ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔] (k a : V),
    a + (S₀ : V) + (S₁ : V) * formulaLen LAct (instB (⌜p⌝ : V) k) ≤ k →
    LenBoxUnbounded TAct a (instB (⌜p⌝ : V) k) →
    Semiformula.Eval (s := stdReading V) ![k] Empty.elim q ∧ Semiformula.Eval (s := swappedReading V) ![k] Empty.elim q


/-- **The uniform theorem of a box consequence** (`pblt_uniformF`'s shape, with `q` in the conclusion and the
box `Box_g (psiF p)` as an explicit antecedent): `TAct ⊢ ∀ k, (k̂ ≤ k → (Box_g (psiF p) (k) → q(k)))` — by
completeness, since in every model the chain (`chain_core_VF`) turns the box into a proof of `p(k)` with the
slack to spare, and `hq` turns that into `q(k)`. Needs NO Löb premise: the box is assumed, not derived. -/
theorem box_conseq_uniform (p : Semisentence LAct 1) {S₀ S₁ d : ℕ} (hE : BoundedInnerNec d)
    (q : Semisentence LAct 1) (hq : BoxConseq p q S₀ S₁) :
    ∃ kHat : ℕ, TAct ⊢ ∀¹ ((leF (↑kHat) #0 : Semisentence LAct 1) 🡒 (Box_g (psiF p) 🡒 q)) := by
  obtain ⟨N₁, hN₁⟩ := exists_forward_lengthF p
  obtain ⟨Cψ, hCψ⟩ := hE.nec (psiF p)
  obtain ⟨C, hC⟩ := chainBoundF_poly p S₀ S₁ N₁ d Cψ
  obtain ⟨kHat₀, hkHat₀⟩ := poly_size_le_eventually C (3 * d + 3)
  refine ⟨kHat₀ + 1, TAct_complete_of_readings _ fun M _ _ ↦ ?_⟩
  have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
  have key : ∀ k : M, ((kHat₀ + 1 : ℕ) : M) ≤ k → LenBoxUnbounded TAct (gBudget k) (instB (⌜psiF p⌝ : M) k) →
      Semiformula.Eval (s := stdReading M) ![k] Empty.elim q ∧
      Semiformula.Eval (s := swappedReading M) ![k] Empty.elim q := by
    intro k hk hbox
    have hk₀ : (kHat₀ : M) ≤ k := le_trans (by push_cast; exact le_self_add) hk
    have hs1 : 1 ≤ ‖k‖ := by
      have h1 : (1 : M) ≤ k := le_trans (by push_cast; exact le_add_self) hk
      have := length_monotone h1
      rwa [length_one] at this
    have hbound : chainBoundF p S₀ S₁ N₁ d Cψ k ≤ k := le_trans (hC M k hs1) (hkHat₀ M k hk₀)
    have hnec : NecAtF p d Cψ M := fun k ↦ hCψ M k
    obtain ⟨a, ha, hp⟩ := chain_core_VF p hnec (hN₁ M) k hbound hbox
    exact hq M k a ha hp
  constructor
  · simp only [Semiformula.eval_all, LogicalConnective.HomClass.map_imply, LogicalConnective.Prop.arrow_eq]
    intro x hx hbox
    rw [eval_Box_g_iff_std] at hbox
    exact (key x ((eval_leF_numeral_bvar _ stdReading_lMap_emb _ x).mp hx) hbox).1
  · simp only [Semiformula.eval_all, LogicalConnective.HomClass.map_imply, LogicalConnective.Prop.arrow_eq]
    intro x hx hbox
    rw [eval_Box_g_iff_swap] at hbox
    exact (key x ((eval_leF_numeral_bvar _ swappedReading_lMap_emb _ x).mp hx) hbox).2


/-- Substitution distributes over the implication. -/
lemma substs_imp (φ ψ : Semisentence LAct 1) (t : ClosedSemiterm LAct 0) :
    ((φ 🡒 ψ : Semisentence LAct 1) ⇜ ![t] : Sentence LAct) =
      ((φ ⇜ ![t] : Sentence LAct) 🡒 (ψ ⇜ ![t] : Sentence LAct)) := by
  simp

/-- **The total cost of the instantiated chain is polylog**: `A + B‖k‖ + C₁‖k‖² + Cψ(gBudget k ^ d + 1) ≤ k` for
all large `k`, in every model (the `PLE` bookkeeping of `Assembly/Family.lean` §6). -/
theorem total_le_eventually (A B C₁ Cψ d : ℕ) :
    ∃ kHat : ℕ, ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (k : V), (kHat : V) ≤ k →
      (A : V) + (B : V) * ‖k‖ + (C₁ : V) * ‖k‖ * ‖k‖ + (Cψ : V) * (gBudget k ^ d + 1) ≤ k := by
  obtain ⟨kHat, h⟩ := poly_size_le_eventually (A + B + C₁ + Cψ * 2) (3 * d + 2)
  refine ⟨kHat + 1, fun V _ _ k hk ↦ ?_⟩
  have hk₀ : (kHat : V) ≤ k := le_trans (by push_cast; exact le_self_add) hk
  have hs1 : 1 ≤ ‖k‖ := by
    have h1 : (1 : V) ≤ k := le_trans (by push_cast; exact le_add_self) hk
    have := length_monotone h1
    rwa [length_one] at this
  refine le_trans ?_ (h V k hk₀)
  have hA : PLE ‖k‖ (A : V) A (3 * d + 2) := PLE.mono hs1 (PLE.const A) le_rfl (Nat.zero_le _)
  have hB : PLE ‖k‖ ((B : V) * ‖k‖) B (3 * d + 2) :=
    PLE.mono hs1 (PLE.mul (PLE.const B) PLE.var) (by omega) (by omega)
  have hC : PLE ‖k‖ ((C₁ : V) * ‖k‖ * ‖k‖) C₁ (3 * d + 2) :=
    PLE.mono hs1 (PLE.mul (PLE.mul (PLE.const C₁) PLE.var) PLE.var) (by omega) (by omega)
  have hg : PLE ‖k‖ (gBudget k ^ d + 1) (1 + 1) (3 * d) :=
    PLE.add (PLE.mono hs1 (PLE.pow (PLE_gBudget hs1) d) (by simp) le_rfl)
      (PLE.mono hs1 PLE.one le_rfl (Nat.zero_le _))
  have hD : PLE ‖k‖ ((Cψ : V) * (gBudget k ^ d + 1)) (Cψ * 2) (3 * d + 2) :=
    PLE.mono hs1 (PLE.mul (PLE.const Cψ) hg) (by omega) (by omega)
  exact PLE.add (PLE.add (PLE.add hA hB) hC) hD

/-- **A box consequence is FOUND within the budget for all large `k`** (the general "`k̂`-chain"): given
bounded inner necessitation, the family's Löb premise (for the meta closure, i.e. the box at ℕ) and
`BoxConseq p q`, the guard-code family `G k = instB ⌜q⌝ k` has a `TAct`-proof within `k` for all large
`k`. The proof: the uniform theorem `∀ k, (k̂ ≤ k → (Box_g (psiF p) (k) → q(k)))` (`box_conseq_uniform`)
instantiated at `binNumeral k` (`lenBoxNat_inst_size`), the numeral antecedent cut away
(`NumeralFacts.lenBoxNat_le_binNumeralMeta`), the box antecedent cut away with the necessitated meta closure
(`exists_psiF_instance_length` + `BoundedInnerNec.nec` at ℕ), the total `A + B·size k + C₁·size k² +
Cψ·(gBudget k ^ d + 1)` polylog (`total_le_eventually`). -/
theorem found_of_box_conseq (p : Semisentence LAct 1) {S₀ S₁ d : ℕ} (hE : BoundedInnerNec d)
    (hs : LoebSound p S₀ S₁) (q : Semisentence LAct 1) (hq : BoxConseq p q S₀ S₁) (G : ℕ → ℕ)
    (hG : ∀ k, G k = instB (⌜q⌝ : ℕ) k) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k → LenBox TAct k (G k) := by
  obtain ⟨kHat, hprov⟩ := box_conseq_uniform p hE q hq
  obtain ⟨N₃, hN₃⟩ := lenBoxNat_of_provable hprov
  obtain ⟨C₀, C₁, hle⟩ := lenBoxNat_le_binNumeralMeta kHat
  obtain ⟨kHat', K₀, K₁, K₂, hmeta⟩ := exists_psiF_instance_length p hE hs
  obtain ⟨Cψ, hCψ⟩ := hE.nec (psiF p)
  set fr := formulaLenMeta (((leF (↑kHat) #0 : Semisentence LAct 1) 🡒 (Box_g (psiF p) 🡒 q) : Semisentence LAct 1) :
    Semiproposition LAct 1) with hfr
  set fB := formulaLenMeta (Box_g (psiF p) : Semiproposition LAct 1) with hfB
  set fq := formulaLenMeta (q : Semiproposition LAct 1) with hfq
  set c := termLenMeta (Rew.emb (↑kHat : ClosedSemiterm LAct 0) : SyntacticSemiterm LAct 0) with hc
  obtain ⟨kHat₂, hkHat₂⟩ := total_le_eventually (N₃ + 13 * fr + C₀ + 20 * c + 40 * fB + 40 * fq + 86)
    (30 * fr + 120 * fB + 120 * fq + 126) C₁ Cψ d
  refine ⟨kHat + kHat' + 2 ^ (K₀ + K₁ + K₂ + 1) + kHat₂ + 1, fun k hk ↦ ?_⟩
  have h2pow : 2 ≤ 2 ^ (K₀ + K₁ + K₂ + 1) := Nat.le_self_pow (Nat.succ_ne_zero _) 2
  -- the meta closure, as the box on codes, below the budget `gBudget k` (as in `family_found`)
  have hbox : LenBoxUnbounded TAct (gBudget k) (instB (⌜psiF p⌝ : ℕ) k) := by
    have h := hmeta k (by omega)
    rw [← lenBox_nat, ← lenBoxUnbounded_iff_lenBox] at h
    have hq : instB (⌜psiF p⌝ : ℕ) k = ⌜(psiF p ⇜ ![Semiterm.lMap emb (binNumeralMeta k)] : Sentence LAct)⌝ := by
      have := quote_instB (V := ℕ) (psiF p) k
      rwa [natCast_nat] at this
    rw [← hq] at h
    refine lenBoxUnbounded_mono_V ?_ h
    have hsize : K₀ + K₁ + K₂ + 1 ≤ Nat.size k := Nat.lt_size.mpr (by omega)
    have hcube := quadratic_le_cube K₀ K₁ K₂ (Nat.size k) hsize
    unfold gBudget
    rw [← size_eq_length]
    exact le_def.mpr (Nat.eq_or_lt_of_le hcube)
  -- the necessitated box: `TAct ⊢ Box_g (psiF p) (k)` at polylog length
  obtain ⟨e, he, hBx⟩ := hCψ ℕ k hbox
  -- step 1: instantiate the uniform theorem at `binNumeralMeta k`; step 2: the numeral antecedent; the budget
  have h1 := lenBoxNat_inst_size ((leF (↑kHat) #0 : Semisentence LAct 1) 🡒 (Box_g (psiF p) 🡒 q)) k hN₃
  have h2 := hle k (by omega)
  have hpoly := hkHat₂ ℕ k (le_def.mpr (Or.inr (by rw [natCast_nat]; omega)))
  simp only [natCast_nat] at hpoly he
  rw [← size_eq_length] at hpoly
  -- abbreviations, introduced AFTER the facts so that they fold everywhere
  set t : ClosedSemiterm LAct 0 := Semiterm.lMap emb (binNumeralMeta k) with ht
  set s := Nat.size k with hs
  have hBx' : LenBoxNat (codeBound : ℕ → ℕ) e TAct (⌜(Box_g (psiF p) ⇜ ![t] : Sentence LAct)⌝ : ℕ) := by
    have hqB : instB (⌜Box_g (psiF p)⌝ : ℕ) k = ⌜(Box_g (psiF p) ⇜ ![t] : Sentence LAct)⌝ := by
      have := quote_instB (V := ℕ) (Box_g (psiF p)) k
      rwa [natCast_nat] at this
    rw [lenBoxUnbounded_iff_lenBox, lenBox_nat, hqB] at hBx
    exact hBx
  have hrt : formulaLenMeta ((((leF (↑kHat) #0 : Semisentence LAct 1) 🡒 (Box_g (psiF p) 🡒 q)) ⇜ ![t] : Sentence LAct) :
      Proposition LAct) ≤ fr * (6 * s + 2) := formulaLenMeta_subst_binNumeralMeta_le _ k
  have h1' : LenBoxNat (codeBound : ℕ → ℕ) (N₃ + 5 * (fr * (6 * s + 2)) + 3 * fr + 6 * s + 8) TAct
      (⌜(((leF (↑kHat) #0 : Semisentence LAct 1) 🡒 (Box_g (psiF p) 🡒 q)) ⇜ ![t] : Sentence LAct)⌝ : ℕ) :=
    lenBoxNat_codeBound_mono (by omega) h1
  rw [substs_leF_imp, substs_imp] at h1'
  -- step 3: the two cuts
  have h3 := lenBoxNat_mp h1' h2
  have h4 := lenBoxNat_mp h3 hBx'
  -- the bookkeeping
  have hBt : formulaLenMeta ((Box_g (psiF p) ⇜ ![t] : Sentence LAct) : Proposition LAct) ≤ fB * (6 * s + 2) :=
    formulaLenMeta_subst_binNumeralMeta_le _ k
  have hqt : formulaLenMeta ((q ⇜ ![t] : Sentence LAct) : Proposition LAct) ≤ fq * (6 * s + 2) := formulaLenMeta_subst_binNumeralMeta_le _ k
  have hleF : formulaLenMeta ((leF (↑kHat) t : Sentence LAct) : Proposition LAct) ≤ 2 * c + 2 * (6 * s + 1) + 3 := by
    rw [formulaLenMeta_leF_sentence, ht, termLenMeta_emb_lMap_binNumeralMeta]
    have : termLenMeta (Rew.emb (binNumeralMeta k) : SyntacticSemiterm ℒₒᵣ 0) ≤ 6 * s + 1 := termLenMeta_binNumeralMeta k
    omega
  have hBqt := formulaLenMeta_imply_sentence (Box_g (psiF p) ⇜ ![t] : Sentence LAct) (q ⇜ ![t] : Sentence LAct)
  have hpoly' := nat_le_of_le_def (le_def.mp hpoly)
  have he' := nat_le_of_le_def (le_def.mp he)
  have hq' : instB (⌜q⌝ : ℕ) k = ⌜(q ⇜ ![t] : Sentence LAct)⌝ := by
    have := quote_instB (V := ℕ) q k
    rwa [natCast_nat] at this
  rw [hG, hq', lenBox_nat]
  refine lenBoxNat_codeBound_mono (le_trans ?_ hpoly') h4
  calc _ ≤ N₃ + 5 * (fr * (6 * s + 2)) + 3 * fr + 6 * s + 8 + (C₀ + C₁ * s * s)
        + 10 * ((2 * c + 2 * (6 * s + 1) + 3) + (fB * (6 * s + 2) + fq * (6 * s + 2) + 1)) + 9 + e
        + 10 * (fB * (6 * s + 2) + fq * (6 * s + 2)) + 9 := by
          rw [hBqt]; gcongr
    _ = N₃ + 13 * fr + C₀ + 20 * c + 40 * fB + 40 * fq + 86 + (30 * fr + 120 * fB + 120 * fq + 126) * s
        + C₁ * s * s + e := by ring
    _ ≤ _ := Nat.add_le_add_left he' _

end boxConseq

end ArithS
