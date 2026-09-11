import ArithS.Assembly.Prep
import ArithS.NumeralFacts

/-!
# ArithS.Assembly.Uniform — the uniform PBLT chain (U8) in every model of `𝗜𝚺₁`

`Research/Notes/M4_BOUNDED_HBL/BRIEF.md` §6 (U8, steps 1–8) with the §7 addendum (the Löb
family is the conjunction `pConj := qDupoc ⋏ qCupod`, the models are the two standard readings
`stdActS`/`swapActS`). Everything is a theorem GIVEN the one named hypothesis
`BoundedInnerNec d c c₁ c₀` (`Assembly/Prep.lean` §6, Critch's assumption (d)).

0. **Lengths of the binary numeral in every model.** `termLen_bnum_le_V : |bnum k| ≤ 6‖k‖ + 1`
   (the V-generic twin of `Bnum.tlen_bnumT`, by `pi1_order_induction` on the bit recursion).
1. **Polynomials in the bit length are eventually below `k`** (`poly_size_le_eventually`): for
   all `C m : ℕ` there is a STANDARD threshold `kHat` with `C·‖k‖^m ≤ k` for every `k ≥ kHat` in every
   model — including nonstandard `k`. No induction inside `V`: split `log k = M·q + r`
   (`M := m + 1`), `(exp q)^M ≤ exp (log k) ≤ k` (`Exponential.add_mul`, monotonicity), and
   Foundation's `sq_len_le_three_mul` at `exp q` gives `(q+1)² ≤ 3·exp q`; so
   `‖k‖^{2M} ≤ M^{2M}·3^M·k`, which cancels to `C‖k‖^M ≤ k` once `‖k‖ ≥ C·M^{2M}·3^M`.
2. **The two standard readings are models of `TAct`** (`stdActS_models_TAct`,
   `swapActS_models_TAct`) for every `M ⊧ 𝗣𝗔` — so the fixed point `psi_fixed_point` is TRUE in
   both (`eval_psi_fixed_point_std`/`_swap`), and its forward direction is a `TAct`-theorem
   (`psi_forward`, by `tact_complete'`) with a bounded proof code in every model
   (`exists_forward_length`), instantiated at `k` by Quantifier Distribution and `instB_quote_imp`
   twice (`forward_inst_V`).
3. **The chain** (`chain_core_V`/`chain_V`/`chain_guard_V`): cut the instantiated forward
   direction with the assumed box `□_{g k} psi(k)`, apply bounded inner necessitation, cut again,
   and eliminate the conjunction — `chainBound` is the total budget consumed, and
   `chainBound_poly` bounds it by `C·‖k‖^{3d+3}` uniformly in `V`.
4. **Truth of `psi` in both readings** (`psi_true_V`): for `k` above a standard threshold, in
   every model — the fixed point plus the chain plus `poly_size_le_eventually`.
5. **The uniform theorem** (`pblt_uniform`): `TAct ⊢ ∀ k, (kHat ≤ k → psi(k))`, by `tact_complete'`;
   the antecedent is `leF ↑kHat #0` (`NumeralFacts.leF`), so `NumeralFacts.substs_leF_imp` and
   `lenProvable_le_bnumT` discharge it at ℕ (U9, `Assembly/Cell.lean`).

Every threshold and constant is EXISTENTIAL (`HANDOVER_ARITHMETIZED_S.md` §5–6); `simp` never
sees a closed quote of `psi`/`pConj`; `omega` is never asked about `V`.
-/

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open LAct

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ### 0. The length of the binary numeral, in every model -/

section bnumLen

lemma termLen_zero_LAct : termLen LAct (𝟎 : V) = 1 := by
  rw [show (𝟎 : V) = ^func 0 (zeroIndex : V) 0 by
      simp [Arithmetic.zero, qqFuncN_eq_qqFunc, qqFunc, nat_cast_pair]; try rfl,
    termLen_func (InstV.isFunc_LAct_of_LOR (by simp)) (by simp)]; simp

lemma termLen_one_LAct : termLen LAct (𝟏 : V) = 1 := by
  rw [show (𝟏 : V) = ^func 0 (oneIndex : V) 0 by
      simp [Arithmetic.one, qqFuncN_eq_qqFunc, qqFunc, nat_cast_pair]; try rfl,
    termLen_func (InstV.isFunc_LAct_of_LOR (by simp)) (by simp)]; simp

lemma termLenVec_two {x y : V} (hx : IsUTerm LAct x) (hy : IsUTerm LAct y) :
    listSum (termLenVec LAct 2 (x ∷ y ∷ (0 : V))) = termLen LAct x + termLen LAct y := by
  have e1 : termLenVec LAct (0 + 1) (y ∷ (0 : V)) = termLen LAct y ∷ (0 : V) := by
    rw [termLenVec_cons hy (by simp), termLenVec_nil]
  rw [zero_add] at e1
  have e : termLenVec LAct (1 + 1) (x ∷ y ∷ (0 : V)) = termLen LAct x ∷ termLen LAct y ∷ (0 : V) := by
    rw [termLenVec_cons hx (by simp [hy]), e1]
  rw [one_add_one_eq_two] at e
  rw [e]; simp

lemma termLen_qqMul_LAct {x y : V} (hx : IsUTerm ℒₒᵣ x) (hy : IsUTerm ℒₒᵣ y) :
    termLen LAct (x ^* y) = termLen LAct x + termLen LAct y + 1 := by
  have hx' : IsUTerm LAct x := (InstV.isSemiterm_LAct_of_LOR hx.isSemiterm).isUTerm
  have hy' : IsUTerm LAct y := (InstV.isSemiterm_LAct_of_LOR hy.isSemiterm).isUTerm
  unfold qqMul
  rw [termLen_func (InstV.isFunc_LAct_of_LOR (by simp)) (by simp [hx', hy']),
    show (?[x, y] : V) = x ∷ y ∷ (0 : V) from rfl, termLenVec_two hx' hy']

lemma termLen_qqAdd_LAct {x y : V} (hx : IsUTerm ℒₒᵣ x) (hy : IsUTerm ℒₒᵣ y) :
    termLen LAct (x ^+ y) = termLen LAct x + termLen LAct y + 1 := by
  have hx' : IsUTerm LAct x := (InstV.isSemiterm_LAct_of_LOR hx.isSemiterm).isUTerm
  have hy' : IsUTerm LAct y := (InstV.isSemiterm_LAct_of_LOR hy.isSemiterm).isUTerm
  unfold qqAdd
  rw [termLen_func (InstV.isFunc_LAct_of_LOR (by simp)) (by simp [hx', hy']),
    show (?[x, y] : V) = x ∷ y ∷ (0 : V) from rfl, termLenVec_two hx' hy']

lemma termLen_qqTwo_LAct : termLen LAct (𝟐 : V) = 3 := by
  rw [qqTwo, termLen_qqAdd_LAct (one_semiterm (n := 0)).isUTerm (one_semiterm (n := 0)).isUTerm,
    termLen_one_LAct, one_add_one_eq_two, two_add_one_eq_three]

/-- **The `LAct` symbol count of the binary numeral, in every model**: `|bnum n| ≤ 6‖n‖ + 1`
(the V-generic twin of `tlen_bnumT`; by order induction on the bit recursion of `bnum`). -/
theorem termLen_bnum_le_V (n : V) : termLen LAct (bnum n) ≤ 6 * ‖n‖ + 1 := by
  induction n using ISigma1.pi1_order_induction with
  | hP => definability
  | ind n ih =>
    rcases zero_one_or_two_le n with rfl | rfl | h2
    · rw [bnum_zero, termLen_zero_LAct, length_zero]; simp
    · rw [bnum_one, termLen_one_LAct, length_one, mul_one]
      exact le_add_self
    obtain ⟨hm, hlt, he | ho⟩ := two_le_cases h2
    · have ih' := ih (n / 2) hlt
      rw [he, bnum_two_mul hm, termLen_qqMul_LAct (qqTwo_semiterm (k := 0)).isUTerm (bnum_uterm _),
        termLen_qqTwo_LAct, length_two_mul_of_pos (lt_of_lt_of_le zero_lt_one hm)]
      calc 3 + termLen LAct (bnum (n / 2)) + 1 ≤ 3 + (6 * ‖n / 2‖ + 1) + 1 := by gcongr
        _ = 6 * ‖n / 2‖ + 5 := by ring
        _ ≤ 6 * ‖n / 2‖ + 5 + 2 := le_self_add
        _ = 6 * (‖n / 2‖ + 1) + 1 := by ring
    · have ih' := ih (n / 2) hlt
      rw [ho, bnum_two_mul_add_one hm,
        termLen_qqAdd_LAct
          (by simp [qqMul, bnum_semiterm 0 (n / 2)] : IsSemiterm ℒₒᵣ 0 (𝟐 ^* bnum (n / 2))).isUTerm
          (one_semiterm (n := 0)).isUTerm,
        termLen_qqMul_LAct (qqTwo_semiterm (k := 0)).isUTerm (bnum_uterm _), termLen_qqTwo_LAct,
        termLen_one_LAct,
        length_two_mul_add_one]
      calc 3 + termLen LAct (bnum (n / 2)) + 1 + 1 + 1 ≤ 3 + (6 * ‖n / 2‖ + 1) + 1 + 1 + 1 := by gcongr
        _ = 6 * (‖n / 2‖ + 1) + 1 := by ring

/-- `|bnum n| ≤ 7‖n‖` once `1 ≤ ‖n‖`. -/
lemma termLen_bnum_le_V' {n : V} (hn : 1 ≤ ‖n‖) : termLen LAct (bnum n) ≤ 7 * ‖n‖ :=
  calc termLen LAct (bnum n) ≤ 6 * ‖n‖ + 1 := termLen_bnum_le_V n
    _ ≤ 6 * ‖n‖ + ‖n‖ := by gcongr
    _ = 7 * ‖n‖ := by ring

end bnumLen

/-! ### 1. Polynomials in the bit length are eventually below `k`, in every model -/

section poly

/-- `Exponential q z → Exponential (M·q) (z^M)` for a standard `M` (`Exponential.add_mul`
iterated). -/
lemma exponential_natMul_pow (M : ℕ) {q z : V} (h : Exponential q z) :
    Exponential ((M : V) * q) (z ^ M) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Nat.cast_succ, add_mul, one_mul, pow_succ]
    exact Exponential.add_mul ih h

/-- The standard power of two, as an exponential in every model. -/
lemma exponential_natCast_two_pow (n : ℕ) : Exponential (n : V) ((2 ^ n : ℕ) : V) := by
  have := exponential_exp (n : V)
  rwa [← nat_cast_exp, exp_nat_eq_two_pow] at this

/-- `‖k‖ ≥ n + 1` once `k ≥ 2^n`, in every model. -/
lemma length_ge_of_two_pow_le {n : ℕ} {k : V} (h : ((2 ^ n : ℕ) : V) ≤ k) : (n : V) + 1 ≤ ‖k‖ := by
  have := length_monotone h
  rwa [(exponential_natCast_two_pow (V := V) n).length_eq] at this

/-- **Polynomials in the bit length are eventually below `k`, in every model of `𝗜𝚺₁`**: for all
`C m : ℕ` there is a standard `kHat` with `C·‖k‖^m ≤ k` for every `k ≥ kHat` — nonstandard `k`
included. -/
theorem poly_size_le_eventually (C m : ℕ) :
    ∃ kHat : ℕ, ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (k : V),
      (kHat : V) ≤ k → (C : V) * ‖k‖ ^ m ≤ k := by
  -- `M := m + 1 ≥ 1`; the threshold on the bit length and on `k`.
  refine ⟨2 ^ (C * (m + 1) ^ (2 * (m + 1)) * 3 ^ (m + 1) + 1), fun V _ _ k hk ↦ ?_⟩
  set L₀ : ℕ := C * (m + 1) ^ (2 * (m + 1)) * 3 ^ (m + 1) + 1 with hL₀
  have hlen : (L₀ : V) + 1 ≤ ‖k‖ := length_ge_of_two_pow_le hk
  have hL₀pos : (0 : V) < (L₀ : V) := by
    rw [hL₀]; push_cast; exact lt_of_lt_of_le _root_.zero_lt_one le_add_self
  have hk0 : 0 < k := length_pos_iff.mp (lt_of_lt_of_le (lt_of_lt_of_le _root_.zero_lt_one le_add_self) hlen)
  -- `j := log k`, `‖k‖ = j + 1`, `exp j ≤ k`.
  set j := log k with hj
  have hkj : ‖k‖ = j + 1 := length_of_pos hk0
  have hy : Exponential j (Exp.exp j) := exponential_exp j
  have hyk : Exp.exp j ≤ k := exponential_log_le_self hk0 hy
  -- `j = M·q + r`, `r < M`.
  set q := j / ((m + 1 : ℕ) : V) with hq
  set r := j % ((m + 1 : ℕ) : V) with hr
  have hMpos : (0 : V) < ((m + 1 : ℕ) : V) := Nat.cast_pos.mpr (Nat.succ_pos m)
  have hdiv : ((m + 1 : ℕ) : V) * q + r = j := div_add_mod j _
  have hrM : r < ((m + 1 : ℕ) : V) := mod_lt j hMpos
  -- `z := exp q`: `(q + 1)² ≤ 3z` and `z^M ≤ k`.
  set z := Exp.exp q with hz
  have hzq : Exponential q z := exponential_exp q
  have hsq : (q + 1) ^ 2 ≤ 3 * z := by
    have := sq_len_le_three_mul z
    rwa [hzq.length_eq] at this
  have hzM : Exponential (((m + 1 : ℕ) : V) * q) (z ^ (m + 1)) := exponential_natMul_pow (m + 1) hzq
  have hzMk : z ^ (m + 1) ≤ k :=
    le_trans (Exponential.monotone_le hzM hy (by rw [← hdiv]; exact le_self_add)) hyk
  -- `(q + 1)^{2M} ≤ 3^M·k`.
  have h1 : (q + 1) ^ (2 * (m + 1)) ≤ (3 : V) ^ (m + 1) * k :=
    calc (q + 1) ^ (2 * (m + 1)) = ((q + 1) ^ 2) ^ (m + 1) := pow_mul _ _ _
      _ ≤ (3 * z) ^ (m + 1) := pow_le_pow_left₀ (by simp) hsq _
      _ = (3 : V) ^ (m + 1) * z ^ (m + 1) := mul_pow _ _ _
      _ ≤ (3 : V) ^ (m + 1) * k := by gcongr
  -- `j + 1 ≤ M(q + 1)`.
  have h2 : j + 1 ≤ ((m + 1 : ℕ) : V) * (q + 1) := by
    rw [← hdiv, mul_add, mul_one, add_assoc]
    gcongr
    exact lt_iff_succ_le.mp hrM
  -- `(j + 1)^{2M} ≤ M^{2M}·3^M·k`.
  have h3 : (j + 1) ^ (2 * (m + 1)) ≤ ((m + 1 : ℕ) : V) ^ (2 * (m + 1)) * (3 : V) ^ (m + 1) * k :=
    calc (j + 1) ^ (2 * (m + 1)) ≤ (((m + 1 : ℕ) : V) * (q + 1)) ^ (2 * (m + 1)) :=
          pow_le_pow_left₀ (by simp) h2 _
      _ = ((m + 1 : ℕ) : V) ^ (2 * (m + 1)) * (q + 1) ^ (2 * (m + 1)) := mul_pow _ _ _
      _ ≤ ((m + 1 : ℕ) : V) ^ (2 * (m + 1)) * ((3 : V) ^ (m + 1) * k) := by gcongr
      _ = ((m + 1 : ℕ) : V) ^ (2 * (m + 1)) * (3 : V) ^ (m + 1) * k := by ring
  -- `L₀ ≤ (j + 1)^M`.
  have hL : (L₀ : V) ≤ j + 1 := by
    rw [← hkj]; exact le_trans le_self_add hlen
  have hj1 : (1 : V) ≤ j + 1 := le_add_self
  have hL' : (L₀ : V) ≤ (j + 1) ^ (m + 1) := le_trans hL (le_self_pow₀ hj1 (Nat.succ_ne_zero m))
  -- The master inequality with `L₀` multiplied in, then cancelled.
  have hmain : (L₀ : V) * ((C : V) * (j + 1) ^ (m + 1)) ≤ (L₀ : V) * k := by
    calc (L₀ : V) * ((C : V) * (j + 1) ^ (m + 1))
        ≤ (j + 1) ^ (m + 1) * ((C : V) * (j + 1) ^ (m + 1)) := by gcongr
      _ = (C : V) * (j + 1) ^ (2 * (m + 1)) := by ring
      _ ≤ (C : V) * (((m + 1 : ℕ) : V) ^ (2 * (m + 1)) * (3 : V) ^ (m + 1) * k) := by gcongr
      _ = ((C * (m + 1) ^ (2 * (m + 1)) * 3 ^ (m + 1) : ℕ) : V) * k := by push_cast; ring
      _ ≤ (L₀ : V) * k := by
          gcongr
          rw [hL₀]; exact le_self_add
  have hfin : (C : V) * (j + 1) ^ (m + 1) ≤ k := le_of_mul_le_mul_left hmain hL₀pos
  rw [hkj]
  exact le_trans (mul_le_mul' le_rfl (pow_le_pow_right₀ hj1 (Nat.le_succ m))) hfin

end poly

/-! ### 2. The two standard readings are models of `TAct` -/

section models

variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

lemma eval_axNe_stdActS : Semiformula.Eval (s := stdActS M) ![] Empty.elim axNe := by
  unfold axNe
  simp only [Semiformula.eval_nrel, cterm]
  change ¬ ((0 : M) = 1)
  exact zero_ne_one

lemma eval_axNe'_stdActS : Semiformula.Eval (s := stdActS M) ![] Empty.elim axNe' := by
  unfold axNe'
  simp only [Semiformula.eval_nrel, cterm]
  change ¬ ((1 : M) = 0)
  exact _root_.one_ne_zero

/-- **The standard reading is a model of `TAct`** for every `M ⊧ 𝗣𝗔`: the `PA` axioms through
the reduct, the four action axioms by evaluation. -/
theorem stdActS_models_TAct : (stdActS M).toStruc ⊧* TAct := by
  refine Semantics.modelsSet_iff.mpr fun φ hφ ↦ ?_
  rcases hφ with rfl | rfl | rfl | rfl | ⟨σ, hσ, rfl⟩
  · exact eval_axAct_stdActS
  · exact eval_axAct'_stdActS
  · exact eval_axNe_stdActS M
  · exact eval_axNe'_stdActS M
  · exact (Semiformula.models_lMap (s₂ := stdActS M) (Φ := emb)).mpr
      (by rw [stdActS_lMap_emb]; exact Theory.models M 𝗣𝗔 hσ)

/-- **The transposed reading is a model of `TAct`**: `TAct` is τ-closed (`lMap_swap_mem_TAct`)
and `swapActS M` is the pull-back of `stdActS M` along `swap`. -/
theorem swapActS_models_TAct : (swapActS M).toStruc ⊧* TAct := by
  refine Semantics.modelsSet_iff.mpr fun φ hφ ↦ ?_
  have h : (stdActS M).toStruc ⊧ Semiformula.lMap swap φ :=
    Semantics.modelsSet_iff.mp (stdActS_models_TAct M) (lMap_swap_mem_TAct hφ)
  exact (Semiformula.models_lMap (s₂ := stdActS M) (Φ := swap)).mp h

/-- The fixed point, evaluated in the standard reading: `psi(x) ↔ (Box_g psi (x) → pConj(x))`. -/
theorem eval_psi_fixed_point_std (x : M) :
    Semiformula.Eval (s := stdActS M) ![x] Empty.elim psi ↔
      (Semiformula.Eval (s := stdActS M) ![x] Empty.elim (Box_g psi) →
        Semiformula.Eval (s := stdActS M) ![x] Empty.elim pConj) := by
  let _ : Structure LAct M := stdActS M
  have : M↓[LAct] ⊧* TAct := stdActS_models_TAct M
  have h := models_psi_fixed_point (M := M)
  rw [models_iff] at h
  simp only [Semiformula.Realize, Semiformula.eval_all, LogicalConnective.HomClass.map_iff,
    LogicalConnective.Prop.iff_eq, LogicalConnective.HomClass.map_imply,
    LogicalConnective.Prop.arrow_eq] at h
  exact h x

/-- The fixed point, evaluated in the transposed reading. -/
theorem eval_psi_fixed_point_swap (x : M) :
    Semiformula.Eval (s := swapActS M) ![x] Empty.elim psi ↔
      (Semiformula.Eval (s := swapActS M) ![x] Empty.elim (Box_g psi) →
        Semiformula.Eval (s := swapActS M) ![x] Empty.elim pConj) := by
  let _ : Structure LAct M := swapActS M
  have : M↓[LAct] ⊧* TAct := swapActS_models_TAct M
  have h := models_psi_fixed_point (M := M)
  rw [models_iff] at h
  simp only [Semiformula.Realize, Semiformula.eval_all, LogicalConnective.HomClass.map_iff,
    LogicalConnective.Prop.iff_eq, LogicalConnective.HomClass.map_imply,
    LogicalConnective.Prop.arrow_eq] at h
  exact h x

end models

/-! ### 3. The forward direction of the fixed point, with a length, instantiated at `k` -/

section forward

/-- The one-variable body of the forward direction: `psi 🡒 (Box_g psi 🡒 pConj)`. -/
noncomputable abbrev chi₁ : Semisentence LAct 1 := psi 🡒 (Box_g psi 🡒 pConj)

/-- **`TAct ⊢ ∀ k, psi(k) → (Box_g psi (k) → pConj(k))`** — the forward direction of
`psi_fixed_point`, by completeness over the two readings. -/
theorem psi_forward : TAct ⊢ ∀¹ chi₁ := by
  refine tact_complete' _ fun M _ _ ↦ ?_
  constructor
  · simp only [chi₁, Semiformula.eval_all, LogicalConnective.HomClass.map_imply,
      LogicalConnective.Prop.arrow_eq]
    intro x hx
    exact (eval_psi_fixed_point_std M x).mp hx
  · simp only [chi₁, Semiformula.eval_all, LogicalConnective.HomClass.map_imply,
      LogicalConnective.Prop.arrow_eq]
    intro x hx
    exact (eval_psi_fixed_point_swap M x).mp hx

/-- The forward direction has a bounded proof code, of some standard length `N₁`, in every model. -/
theorem exists_forward_length : ∃ N₁ : ℕ, ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁],
    LenDerivable TAct (N₁ : V) (⌜(∀¹ chi₁ : Sentence LAct)⌝ : V) :=
  exists_lenDerivable_V_of_proof _ psi_forward

/-- The `k`-instance of `⌜chi₁⌝` is the code implication `psi(k) → (Box_g psi (k) → pConj(k))`. -/
lemma instB_quote_chi₁ (k : V) :
    instB (⌜chi₁⌝ : V) k =
      Bootstrapping.imp LAct (instB (⌜psi⌝ : V) k)
        (Bootstrapping.imp LAct (instB (⌜Box_g psi⌝ : V) k) (instB (⌜pConj⌝ : V) k)) := by
  rw [chi₁, instB_quote_imp, instB_quote_imp]

/-- **The instantiated forward direction** (U8 step 1): from `□_{N₁} ∀¹ chi₁`, a proof code of
`psi(k) → (Box_g psi (k) → pConj(k))` of length `≤ N₁ + 5|chi₁(k)| + 3|chi₁| + |bnum k| + 7`. -/
theorem forward_inst_V {N₁ : V} (h : LenDerivable TAct N₁ (⌜(∀¹ chi₁ : Sentence LAct)⌝ : V)) (k : V) :
    LenDerivable TAct
      (N₁ + 5 * formulaLen LAct (instB (⌜chi₁⌝ : V) k) + 3 * formulaLen LAct (⌜chi₁⌝ : V)
        + termLen LAct (bnum k) + 7)
      (Bootstrapping.imp LAct (instB (⌜psi⌝ : V) k)
        (Bootstrapping.imp LAct (instB (⌜Box_g psi⌝ : V) k) (instB (⌜pConj⌝ : V) k))) := by
  rw [quote_all_sentence] at h
  obtain ⟨d, hd, hlen⟩ := lenDerivable_instB_V (k := k) (Sentence.quote_isSemiformul₁ chi₁) h
  refine ⟨d, ?_, hlen⟩
  rwa [instB_quote_chi₁] at hd

end forward

/-! ### 4. The chain -/

section chain

/-- Short names for the lengths the chain pays. -/
local notation "‖" χ "‖ᵢ" k => formulaLen LAct (instB (⌜χ⌝ : V) k)

/-- **The total budget consumed by the chain** at `k`, for the length `N₁` of the forward direction
and the constants `d c c₁ c₀` of bounded inner necessitation: the instantiation (U3), the cut with
the assumed box (U2), the necessitation expansion (U5), the second cut (U2) and the
∧-elimination (`pconj_both_V`). -/
noncomputable def chainBound (N₁ d c c₁ c₀ : ℕ) (k : V) : V :=
  ((N₁ : V) + 5 * formulaLen LAct (instB (⌜chi₁⌝ : V) k) + 3 * formulaLen LAct (⌜chi₁⌝ : V)
      + termLen LAct (bnum k) + 7)
    + gBudget k + 5 * formulaLen LAct (instB (⌜psi⌝ : V) k)
      + 10 * (formulaLen LAct (instB (⌜Box_g psi⌝ : V) k) + formulaLen LAct (instB (⌜pConj⌝ : V) k) + 1) + 9
    + (gBudget k ^ d + (c : V) + (c₁ : V) * ((flen (psi : Semiproposition LAct 1) : V) + ‖k‖) + (c₀ : V))
      + 5 * formulaLen LAct (instB (⌜Box_g psi⌝ : V) k) + 10 * formulaLen LAct (instB (⌜pConj⌝ : V) k) + 9
    + 8 * (formulaLen LAct (instB (⌜qDupoc⌝ : V) k) + formulaLen LAct (instB (⌜qCupod⌝ : V) k)) + 7

lemma isFormula_imp_instB (φ ψ : Semisentence LAct 1) (k : V) :
    IsFormula LAct (Bootstrapping.imp LAct (instB (⌜φ⌝ : V) k) (instB (⌜ψ⌝ : V) k)) := by
  unfold Bootstrapping.imp
  simp [isFormula_instB_quote φ k, isFormula_instB_quote ψ k]

/-- **The chain, core form** (U8 steps 1–5): given the forward direction at length `N₁`, the
assumed box `□_{g k} psi(k)` and `chainBound ≤ k`, a proof code of `pConj(k)` of some length `a`
below the ∧-elimination threshold of `pconj_both_V`. -/
theorem chain_core_V {d c c₁ c₀ : ℕ} (hE : BoundedInnerNec d c c₁ c₀)
    {N₁ : ℕ} (hN₁ : LenDerivable TAct (N₁ : V) (⌜(∀¹ chi₁ : Sentence LAct)⌝ : V)) (k : V)
    (hk : chainBound N₁ d c c₁ c₀ k ≤ k)
    (hbox : LenDerivable TAct (gBudget k) (instB (⌜psi⌝ : V) k)) :
    ∃ a : V,
      a + 8 * (formulaLen LAct (instB (⌜qDupoc⌝ : V) k) + formulaLen LAct (instB (⌜qCupod⌝ : V) k)) + 7 ≤ k ∧
      LenDerivable TAct a (instB (⌜pConj⌝ : V) k) := by
  have hψ := isFormula_instB_quote psi k
  have hB := isFormula_instB_quote (Box_g psi) k
  have hP := isFormula_instB_quote pConj k
  -- step 1: the instantiated forward direction
  have h2 := forward_inst_V hN₁ k
  -- step 3: cut with the assumed box
  have h3 := lenDerivable_cut_V hψ (isFormula_imp_instB (Box_g psi) pConj k) h2 hbox
  -- step 4: bounded inner necessitation
  obtain ⟨e, he, hBx⟩ := hE.nec V psi k hbox
  -- step 5: cut again
  have h5 := lenDerivable_cut_V hB hP h3 hBx
  refine ⟨_, ?_, h5⟩
  refine le_trans ?_ hk
  unfold chainBound
  rw [formulaLen_imp hB.isUFormula hP.isUFormula]
  gcongr

/-- **The chain** (U8 steps 1–6): both searchers find their guards. -/
theorem chain_V {d c c₁ c₀ : ℕ} (hE : BoundedInnerNec d c c₁ c₀)
    {N₁ : ℕ} (hN₁ : LenDerivable TAct (N₁ : V) (⌜(∀¹ chi₁ : Sentence LAct)⌝ : V)) (k : V)
    (hk : chainBound N₁ d c c₁ c₀ k ≤ k)
    (hbox : LenDerivable TAct (gBudget k) (instB (⌜psi⌝ : V) k)) :
    EvalGraph 2 (DupocV k) (DupocV k) (DupocV k) 0 ∧ EvalGraph 2 (CupodV k) (CupodV k) (CupodV k) 1 := by
  obtain ⟨a, ha, hpc⟩ := chain_core_V hE hN₁ k hk hbox
  exact pconj_both_V k a ha hpc

/-- **The chain, box form**: Dupoc actually FINDS a proof of its guard within its budget. -/
theorem chain_guard_V {d c c₁ c₀ : ℕ} (hE : BoundedInnerNec d c c₁ c₀)
    {N₁ : ℕ} (hN₁ : LenDerivable TAct (N₁ : V) (⌜(∀¹ chi₁ : Sentence LAct)⌝ : V)) (k : V)
    (hk : chainBound N₁ d c c₁ c₀ k ≤ k)
    (hbox : LenDerivable TAct (gBudget k) (instB (⌜psi⌝ : V) k)) :
    LenProvableV TAct k (guardCode (⌜GtmplA 0⌝ : V) (DupocV k) (DupocV k)) ∧
    LenProvableV TAct k (guardCode (⌜GtmplA 1⌝ : V) (CupodV k) (CupodV k)) := by
  obtain ⟨a, ha, hpc⟩ := chain_core_V hE hN₁ k hk hbox
  rw [instB_quote_pConj] at hpc
  have hx := isFormula_instB_quote qDupoc k
  have hy := isFormula_instB_quote qCupod k
  have h₁ := lenDerivable_mono_V ha (lenDerivable_andL_V hx hy hpc)
  have h₂ := lenDerivable_mono_V ha (lenDerivable_andR_V hx hy hpc)
  rw [lenDerivable_iff_lenProvableV, ← guardCode_DupocV_eq_instB] at h₁
  rw [lenDerivable_iff_lenProvableV, ← guardCode_CupodV_eq_instB] at h₂
  exact ⟨h₁, h₂⟩

end chain

/-! ### 5. The budget is polynomial in the bit length -/

section polyBound

/-- `x ≤ A·s^n` — the bookkeeping predicate for polynomial bounds in `s := ‖k‖`. -/
def PLE (s x : V) (A n : ℕ) : Prop := x ≤ (A : V) * s ^ n

namespace PLE

variable {s : V}

lemma of_le {x y : V} {A n : ℕ} (h : x ≤ y) (hy : PLE s y A n) : PLE s x A n := le_trans h hy

lemma const (a : ℕ) : PLE s (a : V) a 0 := by
  unfold PLE; rw [pow_zero, mul_one]

lemma one : PLE s (1 : V) 1 0 := by
  unfold PLE; rw [pow_zero, mul_one, Nat.cast_one]

lemma literal (n : ℕ) [n.AtLeastTwo] : PLE s (OfNat.ofNat n : V) n 0 := by
  unfold PLE; rw [pow_zero, mul_one]; exact le_rfl

lemma var : PLE s s 1 1 := by
  unfold PLE; rw [pow_one, Nat.cast_one, one_mul]

lemma add {x y : V} {A B n : ℕ} (h₁ : PLE s x A n) (h₂ : PLE s y B n) : PLE s (x + y) (A + B) n := by
  unfold PLE at *
  rw [Nat.cast_add, add_mul]
  exact add_le_add h₁ h₂

lemma mul {x y : V} {A B n p : ℕ} (h₁ : PLE s x A n) (h₂ : PLE s y B p) :
    PLE s (x * y) (A * B) (n + p) := by
  unfold PLE at *
  rw [Nat.cast_mul, pow_add]
  calc x * y ≤ ((A : V) * s ^ n) * ((B : V) * s ^ p) := mul_le_mul' h₁ h₂
    _ = (A : V) * (B : V) * (s ^ n * s ^ p) := by ring

lemma pow {x : V} {A n : ℕ} (h : PLE s x A n) (e : ℕ) : PLE s (x ^ e) (A ^ e) (n * e) := by
  unfold PLE at *
  rw [Nat.cast_pow, pow_mul, ← mul_pow]
  exact pow_le_pow_left₀ (by simp) h e

lemma mono (hs : 1 ≤ s) {x : V} {A B n m : ℕ} (h : PLE s x A n) (hA : A ≤ B) (hn : n ≤ m) :
    PLE s x B m := by
  unfold PLE at *
  refine le_trans h ?_
  exact mul_le_mul' (Nat.cast_le.mpr hA) (pow_le_pow_right₀ hs hn)

end PLE

/-- The code length of a quoted one-variable semisentence is its meta length, in every model. -/
lemma formulaLen_quote_semisentence_V (χ : Semisentence LAct 1) :
    formulaLen LAct (⌜χ⌝ : V) = ((flen (χ : Semiproposition LAct 1) : ℕ) : V) := by
  rw [Sentence.quote_def, formulaLen_quote]

lemma PLE_quote (χ : Semisentence LAct 1) (k : V) :
    PLE ‖k‖ (formulaLen LAct (⌜χ⌝ : V)) (flen (χ : Semiproposition LAct 1)) 0 := by
  rw [formulaLen_quote_semisentence_V]; exact PLE.const _

/-- `|bnum k| ≤ 7‖k‖` once `1 ≤ ‖k‖`, in the bookkeeping form. -/
lemma PLE_bnum {k : V} (hs : 1 ≤ ‖k‖) : PLE ‖k‖ (termLen LAct (bnum k)) 7 1 :=
  PLE.of_le (termLen_bnum_le_V' hs) (PLE.mono hs (PLE.mul (PLE.literal 7) PLE.var) le_rfl le_rfl)

/-- `|instB ⌜χ⌝ k| ≤ (flen χ · 7)·‖k‖` once `1 ≤ ‖k‖`. -/
lemma PLE_instB (χ : Semisentence LAct 1) {k : V} (hs : 1 ≤ ‖k‖) :
    PLE ‖k‖ (formulaLen LAct (instB (⌜χ⌝ : V) k)) (flen (χ : Semiproposition LAct 1) * 7) 1 :=
  PLE.of_le (formulaLen_instB_le (Sentence.quote_isSemiformul₁ χ) k)
    (PLE.mono hs (PLE.mul (PLE_quote χ k) (PLE_bnum hs)) le_rfl le_rfl)

/-- `gBudget k = ‖k‖³` is polynomial. -/
lemma PLE_gBudget {k : V} (hs : 1 ≤ ‖k‖) : PLE ‖k‖ (gBudget k) 1 3 := by
  unfold gBudget
  exact PLE.mono hs (PLE.mul (PLE.mul PLE.var PLE.var) PLE.var) le_rfl le_rfl

/-- **The chain's budget is polynomial in the bit length, uniformly in `V`**: for every choice of
the constants there is `C : ℕ` with `chainBound ≤ C·‖k‖^{3d+3}` in every model, once `1 ≤ ‖k‖`
(a pure term, so that the coefficient is read off the bookkeeping combinators). -/
theorem chainBound_PLE (N₁ d c c₁ c₀ : ℕ) :
    ∃ C : ℕ, ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (k : V), 1 ≤ ‖k‖ →
      PLE ‖k‖ (chainBound N₁ d c c₁ c₀ k) C (3 * d + 3) :=
  ⟨_, fun V _ _ k hs ↦
    have hm3 : 3 ≤ 3 * d + 3 := by omega
    have hm1 : 1 ≤ 3 * d + 3 := by omega
    have hm0 : 0 ≤ 3 * d + 3 := by omega
    have hmd : 3 * d ≤ 3 * d + 3 := by omega
    -- the atoms, all lifted to the exponent `3d + 3`
    have hχ₁ := PLE.mono hs (PLE_instB chi₁ hs) le_rfl hm1
    have hψ := PLE.mono hs (PLE_instB psi hs) le_rfl hm1
    have hB := PLE.mono hs (PLE_instB (Box_g psi) hs) le_rfl hm1
    have hP := PLE.mono hs (PLE_instB pConj hs) le_rfl hm1
    have hD := PLE.mono hs (PLE_instB qDupoc hs) le_rfl hm1
    have hC := PLE.mono hs (PLE_instB qCupod hs) le_rfl hm1
    have hg := PLE.mono hs (PLE_gBudget hs) le_rfl hm3
    have hgd := PLE.mono hs (PLE.pow (PLE_gBudget hs) d) le_rfl hmd
    have hlen := PLE.mono hs PLE.var le_rfl hm1
    have hT := PLE.mono hs (PLE_bnum hs) le_rfl hm1
    have hq := PLE.mono hs (PLE_quote chi₁ k) le_rfl hm0
    have hcst : ∀ a : ℕ, PLE ‖k‖ (a : V) a (3 * d + 3) := fun a ↦ PLE.mono hs (PLE.const a) le_rfl hm0
    have hone : PLE ‖k‖ (1 : V) 1 (3 * d + 3) := PLE.mono hs PLE.one le_rfl hm0
    have hlit : ∀ (n : ℕ) [n.AtLeastTwo], PLE ‖k‖ (OfNat.ofNat n : V) n (3 * d + 3) :=
      fun n _ ↦ PLE.mono hs (PLE.literal n) le_rfl hm0
    -- scalar products with a literal or a constant keep the exponent
    have smul : ∀ (n : ℕ) [n.AtLeastTwo] {x : V} {A : ℕ}, PLE ‖k‖ x A (3 * d + 3) →
        PLE ‖k‖ ((OfNat.ofNat n : V) * x) (n * A) (3 * d + 3) := fun n _ x A h ↦
      PLE.mono hs (PLE.mul (PLE.literal n) h) le_rfl (by omega)
    have cmul : ∀ (a : ℕ) {x : V} {A : ℕ}, PLE ‖k‖ x A (3 * d + 3) →
        PLE ‖k‖ ((a : V) * x) (a * A) (3 * d + 3) := fun a x A h ↦
      PLE.mono hs (PLE.mul (PLE.const a) h) le_rfl (by omega)
    -- the summands of `chainBound`, in order
    have t₁ := (hcst N₁).add (smul 5 hχ₁)
    have t₂ := t₁.add (smul 3 hq)
    have t₃ := t₂.add hT
    have t₄ := t₃.add (hlit 7)
    have t₅ := t₄.add hg
    have t₆ := t₅.add (smul 5 hψ)
    have t₇ := t₆.add (smul 10 ((hB.add hP).add hone))
    have t₈ := t₇.add (hlit 9)
    have t₉ := t₈.add (((hgd.add (hcst c)).add (cmul c₁ ((hcst _).add hlen))).add (hcst c₀))
    have t₁₀ := t₉.add (smul 5 hB)
    have t₁₁ := t₁₀.add (smul 10 hP)
    have t₁₂ := t₁₁.add (hlit 9)
    have t₁₃ := t₁₂.add (smul 8 (hD.add hC))
    t₁₃.add (hlit 7)⟩

/-- **The chain's budget is polynomial in the bit length, uniformly in `V`.** -/
theorem chainBound_poly (N₁ d c c₁ c₀ : ℕ) :
    ∃ C : ℕ, ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (k : V), 1 ≤ ‖k‖ →
      chainBound N₁ d c c₁ c₀ k ≤ (C : V) * ‖k‖ ^ (3 * d + 3) := by
  obtain ⟨C, hC⟩ := chainBound_PLE N₁ d c c₁ c₀
  exact ⟨C, fun V _ _ k hs ↦ hC V k hs⟩

end polyBound

/-! ### 6. Truth of `psi` in both readings, and the uniform theorem -/

section uniform

/-- **`psi(k)` is true in both readings for every large `k`, in every model of `𝗜𝚺₁`**, given
bounded inner necessitation: for `k` above a standard threshold `kHat`, the box `Box_g psi (k)`
implies `pConj(k)` (the chain), so `psi(k)` holds by the fixed point. -/
theorem psi_true_V {d c c₁ c₀ : ℕ} (hE : BoundedInnerNec d c c₁ c₀) :
    ∃ kHat : ℕ, ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔] (k : V), (kHat : V) ≤ k →
      Semiformula.Eval (s := stdActS V) ![k] Empty.elim psi ∧
      Semiformula.Eval (s := swapActS V) ![k] Empty.elim psi := by
  obtain ⟨N₁, hN₁⟩ := exists_forward_length
  obtain ⟨C, hC⟩ := chainBound_poly N₁ d c c₁ c₀
  obtain ⟨kHat₀, hkHat₀⟩ := poly_size_le_eventually C (3 * d + 3)
  refine ⟨kHat₀ + 1, fun V _ _ k hk ↦ ?_⟩
  have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
  have hk₀ : (kHat₀ : V) ≤ k := le_trans (by push_cast; exact le_self_add) hk
  have hs : 1 ≤ ‖k‖ := by
    have h1 : (1 : V) ≤ k := le_trans (by push_cast; exact le_add_self) hk
    have := length_monotone h1
    rwa [length_one] at this
  have hbound : chainBound N₁ d c c₁ c₀ k ≤ k := le_trans (hC V k hs) (hkHat₀ V k hk₀)
  constructor
  · refine (eval_psi_fixed_point_std V k).mpr fun hbox ↦ ?_
    rw [eval_Box_g_iff_std] at hbox
    obtain ⟨h1, h2⟩ := chain_V hE (hN₁ V) k hbound hbox
    exact (eval_pConj_iff_stdActS k).mpr ⟨⟨2, h1⟩, ⟨2, h2⟩⟩
  · refine (eval_psi_fixed_point_swap V k).mpr fun hbox ↦ ?_
    rw [eval_Box_g_iff_swap] at hbox
    obtain ⟨h1, h2⟩ := chain_V hE (hN₁ V) k hbound hbox
    exact (eval_pConj_iff_swap k).mpr ⟨⟨2, h1⟩, ⟨2, h2⟩⟩

/-- The antecedent `leF ↑c #0` evaluated at `x` in a structure with standard reduct is `c ≤ x`. -/
lemma eval_leF_numeral_bvar {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (S : Structure LAct M)
    (hS : Structure.lMap emb S = standardModel M) (c : ℕ) (x : M) :
    Semiformula.Eval (s := S) ![x] Empty.elim (leF (↑c) #0 : Semisentence LAct 1) ↔ (c : M) ≤ x := by
  have e : (leF (↑c) #0 : Semisentence LAct 1) =
      Semiformula.lMap emb (leF (↑c) #0 : Semisentence ℒₒᵣ 1) := by
    rw [lMap_emb_leF, lMap_emb_numeral]; rfl
  rw [e, Semiformula.eval_lMap, hS]
  simp [leF, numeral_eq_natCast, le_def]

/-- **The uniform theorem (U8 step 8)**: given bounded inner necessitation, there is a standard
`kHat` with `TAct ⊢ ∀ k, (kHat ≤ k → psi(k))` — the antecedent in the shape `leF ↑kHat #0` that
`NumeralFacts.lenProvable_le_bnumT` discharges at ℕ. -/
theorem pblt_uniform {d c c₁ c₀ : ℕ} (hE : BoundedInnerNec d c c₁ c₀) :
    ∃ kHat : ℕ, TAct ⊢ ∀¹ ((leF (↑kHat) #0 : Semisentence LAct 1) 🡒 psi) := by
  obtain ⟨kHat, hkHat⟩ := psi_true_V hE
  refine ⟨kHat, tact_complete' _ fun M _ _ ↦ ?_⟩
  have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
  constructor
  · simp only [Semiformula.eval_all, LogicalConnective.HomClass.map_imply, LogicalConnective.Prop.arrow_eq]
    intro x hx
    exact (hkHat M x ((eval_leF_numeral_bvar _ stdActS_lMap_emb kHat x).mp hx)).1
  · simp only [Semiformula.eval_all, LogicalConnective.HomClass.map_imply, LogicalConnective.Prop.arrow_eq]
    intro x hx
    exact (hkHat M x ((eval_leF_numeral_bvar _ swapActS_lMap_emb kHat x).mp hx)).2

end uniform

end ArithS
