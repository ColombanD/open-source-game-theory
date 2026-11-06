import ArithS.Assembly.Prep
import ArithS.Loeb.NumeralFacts

/-!
# ArithS.Assembly.Family — the PBLT assembly, parametrized by the Löb family

`docs/notes/ROUTE_B_SCOPE.md` §3 Phase 1. Everything `Assembly/Uniform.lean` and
`Assembly/Cell.lean` did for the ONE family `pConj := qDupoc ⋏ qCupod` is done here for an
ARBITRARY target `p : Semisentence LAct 1` (the sentence-with-budget-variable the argument must
make true) and a SLACK `(S₀, S₁)` (the budget the family's consumer needs AFTER obtaining the box
of `p(k)`, as `S₀ + S₁·|instB ⌜p⌝ k|` — for `pConj` it is the ∧-elimination `7 + 8·|pConj(k)|`).
The two pConj files are now instantiations of this one (`psi = psiF pConj` by `rfl`).

0. **Generic material, moved verbatim** from `Uniform.lean` §0–§2 and §5 and `Cell.lean` §1–§2
   (`termLen_binNumeral_le_V`, `poly_size_le_eventually`, the two readings as models of `TAct`, the `PLE`
   calculus, `size_eq_length`, `quadratic_le_cube`, `formulaLenMeta_subst_binNumeralMeta_le`, `eval_leF_numeral_bvar`).
1. **The family's fixed point.** `thetaF p := boxCoreA 🡒 (p ⇜ ![#1])` (`#0` the code slot, `#1`
   the budget — `Prep.theta`'s convention), `psiF p := tactFixedpoint (thetaF p)`, the code slot
   resolved by `thetaF_subst_code` (`Prep.pConjL_subst` was already generic in the substituted
   formula: `liftL_subst`), so `psiF_fixed_point p : TAct ⊢ ∀¹ (psiF p 🡘 (Box_g (psiF p) 🡒 p))`,
   true in both readings (`eval_psiF_fixed_point_std`/`_swap`).
2. **The forward direction** `chiF p := psiF p 🡒 (Box_g (psiF p) 🡒 p)`, a `TAct`-theorem
   (`psiF_forward`) with a bounded proof code in every model (`exists_forward_lengthF`),
   instantiated at `k` (`forward_inst_VF`).
3. **The chain** (`chain_core_VF`): cut the instantiated forward direction with the assumed box
   `□_{g k} psiF p (k)`, apply bounded inner necessitation (`NecAtF`), cut again; the budget
   `chainBoundF p S₀ S₁ N₁ d C k` is `Uniform.chainBound` with the ∧-elimination summand replaced
   by the slack, and `chainBoundF_poly` bounds it by `C·‖k‖^{3d+3}` uniformly in `V`.
4. **The bounded Löb premise as ONE named hypothesis**: `LoebSound p S₀ S₁` — "a proof of the
   `k`-instance of `p` within budget `k`, minus the slack, makes `p(k)` true in both standard
   readings" (□p → p, the family's own content: for `pConj` it is `pconj_both_V` + the truth
   equations, `Uniform.loebSound_pConj`). Then `psiF_true_V` (`psiF p (k)` true in both readings
   for all large `k`, in every model) and **`pblt_uniformF`**: `TAct ⊢ ∀ k, (k̂ ≤ k → psiF p (k))`.
5. **The cell half at ℕ**: `exists_psiF_instance_length` (the uniform theorem instantiated at
   `binNumeralMeta k`, its antecedent cut away — quadratic in the bit length) and **`family_found`**, the
   arithmetized `pblt_engine`: for all large `k : ℕ` the `k`-instance of `p` has a `TAct`-proof
   code of length `a` with `a + S₀ + S₁·|instB ⌜p⌝ k| ≤ k` — the family's box is found within its
   budget, with the slack to spare.

Conventions (`HANDOVER_ARITHMETIZED_S.md` §5–6): every threshold and constant is EXISTENTIAL;
`simp` never sees a closed quote (`p` is a VARIABLE here, and the pConj instances only `exact`);
`omega` is never asked about `V`. At `V = ℕ`, a `≤` written in a ℕ-statement is `Nat.le`
(`instLENat`) while a V-generic statement instantiated at `ℕ` carries Foundation's
`instLE_foundation` (`le_def : a ≤ b ↔ a = b ∨ a < b`); `family_found` states `Nat.le`, exactly as
`Cell.cell_core` reads its thresholds, and bridges through `le_def`.
-/

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open LAct

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ### 0. The length of the binary numeral, in every model -/

section binNumeralLen

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

/-- **The `LAct` symbol count of the binary numeral, in every model**: `|binNumeral n| ≤ 6‖n‖ + 1`
(the V-generic twin of `termLenMeta_binNumeralMeta`; by order induction on the bit recursion of `binNumeral`). -/
theorem termLen_binNumeral_le_V (n : V) : termLen LAct (binNumeral n) ≤ 6 * ‖n‖ + 1 := by
  induction n using ISigma1.pi1_order_induction with
  | hP => definability
  | ind n ih =>
    rcases zero_one_or_two_le n with rfl | rfl | h2
    · rw [binNumeral_zero, termLen_zero_LAct, length_zero]; simp
    · rw [binNumeral_one, termLen_one_LAct, length_one, mul_one]
      exact le_add_self
    obtain ⟨hm, hlt, he | ho⟩ := two_le_cases h2
    · have ih' := ih (n / 2) hlt
      rw [he, binNumeral_two_mul hm, termLen_qqMul_LAct (qqTwo_semiterm (k := 0)).isUTerm (binNumeral_uterm _),
        termLen_qqTwo_LAct, length_two_mul_of_pos (lt_of_lt_of_le zero_lt_one hm)]
      calc 3 + termLen LAct (binNumeral (n / 2)) + 1 ≤ 3 + (6 * ‖n / 2‖ + 1) + 1 := by gcongr
        _ = 6 * ‖n / 2‖ + 5 := by ring
        _ ≤ 6 * ‖n / 2‖ + 5 + 2 := le_self_add
        _ = 6 * (‖n / 2‖ + 1) + 1 := by ring
    · have ih' := ih (n / 2) hlt
      rw [ho, binNumeral_two_mul_add_one hm,
        termLen_qqAdd_LAct
          (by simp [qqMul, binNumeral_semiterm 0 (n / 2)] : IsSemiterm ℒₒᵣ 0 (𝟐 ^* binNumeral (n / 2))).isUTerm
          (one_semiterm (n := 0)).isUTerm,
        termLen_qqMul_LAct (qqTwo_semiterm (k := 0)).isUTerm (binNumeral_uterm _), termLen_qqTwo_LAct,
        termLen_one_LAct,
        length_two_mul_add_one]
      calc 3 + termLen LAct (binNumeral (n / 2)) + 1 + 1 + 1 ≤ 3 + (6 * ‖n / 2‖ + 1) + 1 + 1 + 1 := by gcongr
        _ = 6 * (‖n / 2‖ + 1) + 1 := by ring

/-- `|binNumeral n| ≤ 7‖n‖` once `1 ≤ ‖n‖`. -/
lemma termLen_binNumeral_le_V' {n : V} (hn : 1 ≤ ‖n‖) : termLen LAct (binNumeral n) ≤ 7 * ‖n‖ :=
  calc termLen LAct (binNumeral n) ≤ 6 * ‖n‖ + 1 := termLen_binNumeral_le_V n
    _ ≤ 6 * ‖n‖ + ‖n‖ := by gcongr
    _ = 7 * ‖n‖ := by ring

end binNumeralLen

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

lemma eval_constNe_stdReading : Semiformula.Eval (s := stdReading M) ![] Empty.elim constNe := by
  unfold constNe
  simp only [Semiformula.eval_nrel, cterm]
  change ¬ ((0 : M) = 1)
  exact zero_ne_one

lemma eval_constNe'_stdReading : Semiformula.Eval (s := stdReading M) ![] Empty.elim constNe' := by
  unfold constNe'
  simp only [Semiformula.eval_nrel, cterm]
  change ¬ ((1 : M) = 0)
  exact _root_.one_ne_zero

/-- **The standard reading is a model of `TAct`** for every `M ⊧ 𝗣𝗔`: the `PA` axioms through
the reduct, the four action axioms by evaluation. -/
theorem stdReading_models_TAct : (stdReading M).toStruc ⊧* TAct := by
  refine Semantics.modelsSet_iff.mpr fun φ hφ ↦ ?_
  rcases hφ with rfl | rfl | rfl | rfl | ⟨σ, hσ, rfl⟩
  · exact eval_actionAxiom_stdReading
  · exact eval_actionAxiom'_stdReading
  · exact eval_constNe_stdReading M
  · exact eval_constNe'_stdReading M
  · exact (Semiformula.models_lMap (s₂ := stdReading M) (Φ := emb)).mpr
      (by rw [stdReading_lMap_emb]; exact Theory.models M 𝗣𝗔 hσ)

/-- **The transposed reading is a model of `TAct`**: `TAct` is τ-closed (`lMap_swap_mem_TAct`)
and `swappedReading M` is the pull-back of `stdReading M` along `swap`. -/
theorem swappedReading_models_TAct : (swappedReading M).toStruc ⊧* TAct := by
  refine Semantics.modelsSet_iff.mpr fun φ hφ ↦ ?_
  have h : (stdReading M).toStruc ⊧ Semiformula.lMap swap φ :=
    Semantics.modelsSet_iff.mp (stdReading_models_TAct M) (lMap_swap_mem_TAct hφ)
  exact (Semiformula.models_lMap (s₂ := stdReading M) (Φ := swap)).mp h

/-! ### 3. The family's fixed point -/

/-- **`p` lifted to the two-variable context of `θ`** (`#1` = the budget). `Prep.pConjL` is
`liftL pConj` by `rfl`. -/
noncomputable def liftL (p : Semisentence LAct 1) : Semisentence LAct 2 := p ⇜ ![#1]

lemma pConjL_eq_liftL : pConjL = liftL pConj := rfl

/-- **`θ_p(n, k) := (∃ a, a = g(k) ∧ bewB a n k) 🡒 p(k)`** — `#0` the CODE slot `n`, `#1` the
budget `k`. `Prep.theta` is `thetaF pConj` by `rfl`. -/
noncomputable def thetaF (p : Semisentence LAct 1) : Semisentence LAct 2 := boxCoreA 🡒 liftL p

lemma thetaF_def (p : Semisentence LAct 1) : thetaF p = boxCoreA 🡒 liftL p := rfl

lemma theta_eq_thetaF : theta = thetaF pConj := rfl

/-- Filling the code slot of `liftL p` and re-indexing the budget gives `p` back
(`Prep.pConjL_subst`, generic in the lifted formula). -/
lemma liftL_subst (p : Semisentence LAct 1) (t : Semiterm LAct Empty 1) : liftL p ⇜ ![t, #0] = p := by
  unfold liftL Rewriting.subst
  rw [← TransitiveRewriting.comp_app, comp_subst_eq]
  have e : (fun i : Fin 1 ↦ (Rew.subst ![t, (#0 : Semiterm LAct Empty 1)] : Rew LAct Empty 2 Empty 1)
      ((![#1] : Fin 1 → Semiterm LAct Empty 2) i)) = ![(#0 : Semiterm LAct Empty 1)] := by
    funext i; fin_cases i; simp
  rw [e]
  exact subst_bvar_id p

/-- **The code slot filled**: `θ_p ⇜ ![⌜χ⌝, #0] = Box_g χ 🡒 p`, syntactically. -/
theorem thetaF_subst_code (p χ : Semisentence LAct 1) :
    thetaF p ⇜ ![Semiterm.lMap emb (⌜χ⌝ : ArithmeticSemiterm Empty 1), #0] = Box_g χ 🡒 p := by
  rw [thetaF_def, Box_g_def]
  unfold Rewriting.subst
  rw [LogicalConnective.HomClass.map_imply]
  congr 1
  exact liftL_subst p _

/-- **The fixed point of the family's argument**: `psiF p := tactFixedpoint (thetaF p)`.
`Prep.psi` is `psiF pConj` by `rfl`. -/
noncomputable def psiF (p : Semisentence LAct 1) : Semisentence LAct 1 := tactFixedpoint (thetaF p)

lemma psi_eq_psiF : psi = psiF pConj := rfl

/-- **`TAct ⊢ ∀ k, psiF p (k) ↔ (Box_g (psiF p) (k) → p(k))`** — the parametric diagonal lemma
with the code slot resolved by `thetaF_subst_code`. -/
theorem psiF_fixed_point (p : Semisentence LAct 1) :
    TAct ⊢ ∀¹ (psiF p 🡘 (Box_g (psiF p) 🡒 p)) := by
  have h := tact_parametric_diagonal₁ (thetaF p)
  rw [thetaF_subst_code] at h
  exact h

/-- The fixed point holds in every model of `TAct` (soundness). -/
theorem models_psiF_fixed_point (p : Semisentence LAct 1) {M : Type*} [Nonempty M] [Structure LAct M]
    [M↓[LAct] ⊧* TAct] : M↓[LAct] ⊧ ∀¹ (psiF p 🡘 (Box_g (psiF p) 🡒 p)) :=
  models_of_provable inferInstance (psiF_fixed_point p)

/-- The fixed point, evaluated in the standard reading: `psiF p (x) ↔ (Box_g (psiF p) (x) → p(x))`. -/
theorem eval_psiF_fixed_point_std (p : Semisentence LAct 1) (x : M) :
    Semiformula.Eval (s := stdReading M) ![x] Empty.elim (psiF p) ↔
      (Semiformula.Eval (s := stdReading M) ![x] Empty.elim (Box_g (psiF p)) →
        Semiformula.Eval (s := stdReading M) ![x] Empty.elim p) := by
  let _ : Structure LAct M := stdReading M
  have : M↓[LAct] ⊧* TAct := stdReading_models_TAct M
  have h := models_psiF_fixed_point p (M := M)
  rw [models_iff] at h
  simp only [Semiformula.Realize, Semiformula.eval_all, LogicalConnective.HomClass.map_iff,
    LogicalConnective.Prop.iff_eq, LogicalConnective.HomClass.map_imply,
    LogicalConnective.Prop.arrow_eq] at h
  exact h x

/-- The fixed point, evaluated in the transposed reading. -/
theorem eval_psiF_fixed_point_swap (p : Semisentence LAct 1) (x : M) :
    Semiformula.Eval (s := swappedReading M) ![x] Empty.elim (psiF p) ↔
      (Semiformula.Eval (s := swappedReading M) ![x] Empty.elim (Box_g (psiF p)) →
        Semiformula.Eval (s := swappedReading M) ![x] Empty.elim p) := by
  let _ : Structure LAct M := swappedReading M
  have : M↓[LAct] ⊧* TAct := swappedReading_models_TAct M
  have h := models_psiF_fixed_point p (M := M)
  rw [models_iff] at h
  simp only [Semiformula.Realize, Semiformula.eval_all, LogicalConnective.HomClass.map_iff,
    LogicalConnective.Prop.iff_eq, LogicalConnective.HomClass.map_imply,
    LogicalConnective.Prop.arrow_eq] at h
  exact h x

end models

/-! ### 4. The forward direction of the fixed point, with a length, instantiated at `k` -/

section forward

/-- The one-variable body of the forward direction: `psiF p 🡒 (Box_g (psiF p) 🡒 p)`. -/
noncomputable abbrev chiF (p : Semisentence LAct 1) : Semisentence LAct 1 :=
  psiF p 🡒 (Box_g (psiF p) 🡒 p)

/-- **`TAct ⊢ ∀ k, psiF p (k) → (Box_g (psiF p) (k) → p(k))`** — the forward direction of
`psiF_fixed_point`, by completeness over the two readings. -/
theorem psiF_forward (p : Semisentence LAct 1) : TAct ⊢ ∀¹ chiF p := by
  refine TAct_complete_of_readings _ fun M _ _ ↦ ?_
  constructor
  · simp only [chiF, Semiformula.eval_all, LogicalConnective.HomClass.map_imply,
      LogicalConnective.Prop.arrow_eq]
    intro x hx
    exact (eval_psiF_fixed_point_std M p x).mp hx
  · simp only [chiF, Semiformula.eval_all, LogicalConnective.HomClass.map_imply,
      LogicalConnective.Prop.arrow_eq]
    intro x hx
    exact (eval_psiF_fixed_point_swap M p x).mp hx

/-- The forward direction has a bounded proof code, of some standard length `N₁`, in every model. -/
theorem exists_forward_lengthF (p : Semisentence LAct 1) :
    ∃ N₁ : ℕ, ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁],
      LenBoxUnbounded TAct (N₁ : V) (⌜(∀¹ chiF p : Sentence LAct)⌝ : V) :=
  exists_lenBoxUnbounded_V_of_proof _ (psiF_forward p)

/-- The `k`-instance of `⌜chiF p⌝` is the code implication `psiF p (k) → (Box_g (psiF p) (k) → p(k))`. -/
lemma instB_quote_chiF (p : Semisentence LAct 1) (k : V) :
    instB (⌜chiF p⌝ : V) k =
      Bootstrapping.imp LAct (instB (⌜psiF p⌝ : V) k)
        (Bootstrapping.imp LAct (instB (⌜Box_g (psiF p)⌝ : V) k) (instB (⌜p⌝ : V) k)) := by
  rw [chiF, instB_quote_imp, instB_quote_imp]

/-- **The instantiated forward direction** (U8 step 1): from `□_{N₁} ∀¹ chiF p`, a proof code of
`psiF p (k) → (Box_g (psiF p) (k) → p(k))` of length `≤ N₁ + 5|chiF p (k)| + 3|chiF p| + |binNumeral k| + 7`. -/
theorem forward_inst_VF (p : Semisentence LAct 1) {N₁ : V}
    (h : LenBoxUnbounded TAct N₁ (⌜(∀¹ chiF p : Sentence LAct)⌝ : V)) (k : V) :
    LenBoxUnbounded TAct
      (N₁ + 5 * formulaLen LAct (instB (⌜chiF p⌝ : V) k) + 3 * formulaLen LAct (⌜chiF p⌝ : V)
        + termLen LAct (binNumeral k) + 7)
      (Bootstrapping.imp LAct (instB (⌜psiF p⌝ : V) k)
        (Bootstrapping.imp LAct (instB (⌜Box_g (psiF p)⌝ : V) k) (instB (⌜p⌝ : V) k))) := by
  rw [quote_all_sentence] at h
  obtain ⟨d, hd, hlen⟩ := lenBoxUnbounded_instB_V (k := k) (Sentence.quote_isSemiformul₁ (chiF p)) h
  refine ⟨d, ?_, hlen⟩
  rwa [instB_quote_chiF] at hd

end forward

/-! ### 5. The chain -/

section chain

/-- **Bounded inner necessitation at `psiF p`, in one model, with its constant `Cψ`** — the
instance of `BoundedInnerNec.nec (psiF p)` the chain consumes. -/
def NecAtF (p : Semisentence LAct 1) (d Cψ : ℕ) (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] : Prop :=
  ∀ k : V, LenBoxUnbounded TAct (gBudget k) (instB (⌜psiF p⌝ : V) k) →
    ∃ e : V, e ≤ (Cψ : V) * ((gBudget k) ^ d + 1) ∧ LenBoxUnbounded TAct e (instB (⌜Box_g (psiF p)⌝ : V) k)

/-- **The total budget consumed by the chain** at `k`, for the family `p` with slack `(S₀, S₁)`,
the length `N₁` of the forward direction and the constants `d`, `Cψ` of bounded inner
necessitation at `psiF p`: the instantiation (U3), the cut with the assumed box (U2), the
necessitation expansion (U5), the second cut (U2) and the slack `S₀ + S₁·|p(k)|` the consumer
needs after the box (for `pConj`: the ∧-elimination of `pconj_both_V`). -/
noncomputable def chainBoundF (p : Semisentence LAct 1) (S₀ S₁ N₁ d Cψ : ℕ) (k : V) : V :=
  ((N₁ : V) + 5 * formulaLen LAct (instB (⌜chiF p⌝ : V) k) + 3 * formulaLen LAct (⌜chiF p⌝ : V)
      + termLen LAct (binNumeral k) + 7)
    + gBudget k + 5 * formulaLen LAct (instB (⌜psiF p⌝ : V) k)
      + 10 * (formulaLen LAct (instB (⌜Box_g (psiF p)⌝ : V) k) + formulaLen LAct (instB (⌜p⌝ : V) k) + 1) + 9
    + (Cψ : V) * (gBudget k ^ d + 1)
      + 5 * formulaLen LAct (instB (⌜Box_g (psiF p)⌝ : V) k) + 10 * formulaLen LAct (instB (⌜p⌝ : V) k) + 9
    + (S₀ : V) + (S₁ : V) * formulaLen LAct (instB (⌜p⌝ : V) k)

lemma isFormula_imp_instB (φ ψ : Semisentence LAct 1) (k : V) :
    IsFormula LAct (Bootstrapping.imp LAct (instB (⌜φ⌝ : V) k) (instB (⌜ψ⌝ : V) k)) := by
  unfold Bootstrapping.imp
  simp [isFormula_instB_quote φ k, isFormula_instB_quote ψ k]

/-- **The chain, core form** (U8 steps 1–5, any family): given the forward direction at length
`N₁`, the assumed box `□_{g k} psiF p (k)` and `chainBoundF ≤ k`, a proof code of `p(k)` of some
length `a` with the slack to spare: `a + S₀ + S₁·|p(k)| ≤ k`. -/
theorem chain_core_VF (p : Semisentence LAct 1) {S₀ S₁ d Cψ : ℕ} (hnec : NecAtF p d Cψ V)
    {N₁ : ℕ} (hN₁ : LenBoxUnbounded TAct (N₁ : V) (⌜(∀¹ chiF p : Sentence LAct)⌝ : V)) (k : V)
    (hk : chainBoundF p S₀ S₁ N₁ d Cψ k ≤ k)
    (hbox : LenBoxUnbounded TAct (gBudget k) (instB (⌜psiF p⌝ : V) k)) :
    ∃ a : V, a + (S₀ : V) + (S₁ : V) * formulaLen LAct (instB (⌜p⌝ : V) k) ≤ k ∧
      LenBoxUnbounded TAct a (instB (⌜p⌝ : V) k) := by
  have hψ := isFormula_instB_quote (psiF p) k
  have hB := isFormula_instB_quote (Box_g (psiF p)) k
  have hP := isFormula_instB_quote p k
  -- step 1: the instantiated forward direction
  have h2 := forward_inst_VF p hN₁ k
  -- step 3: cut with the assumed box
  have h3 := lenBoxUnbounded_mp hψ (isFormula_imp_instB (Box_g (psiF p)) p k) h2 hbox
  -- step 4: bounded inner necessitation
  obtain ⟨e, he, hBx⟩ := hnec k hbox
  -- step 5: cut again
  have h5 := lenBoxUnbounded_mp hB hP h3 hBx
  refine ⟨_, ?_, h5⟩
  refine le_trans ?_ hk
  unfold chainBoundF
  rw [formulaLen_imp hB.isUFormula hP.isUFormula]
  gcongr

end chain

/-! ### 6. The budget is polynomial in the bit length -/

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
    formulaLen LAct (⌜χ⌝ : V) = ((formulaLenMeta (χ : Semiproposition LAct 1) : ℕ) : V) := by
  rw [Sentence.quote_def, formulaLen_quote]

lemma PLE_quote (χ : Semisentence LAct 1) (k : V) :
    PLE ‖k‖ (formulaLen LAct (⌜χ⌝ : V)) (formulaLenMeta (χ : Semiproposition LAct 1)) 0 := by
  rw [formulaLen_quote_semisentence_V]; exact PLE.const _

/-- `|binNumeral k| ≤ 7‖k‖` once `1 ≤ ‖k‖`, in the bookkeeping form. -/
lemma PLE_binNumeral {k : V} (hs : 1 ≤ ‖k‖) : PLE ‖k‖ (termLen LAct (binNumeral k)) 7 1 :=
  PLE.of_le (termLen_binNumeral_le_V' hs) (PLE.mono hs (PLE.mul (PLE.literal 7) PLE.var) le_rfl le_rfl)

/-- `|instB ⌜χ⌝ k| ≤ (formulaLenMeta χ · 7)·‖k‖` once `1 ≤ ‖k‖`. -/
lemma PLE_instB (χ : Semisentence LAct 1) {k : V} (hs : 1 ≤ ‖k‖) :
    PLE ‖k‖ (formulaLen LAct (instB (⌜χ⌝ : V) k)) (formulaLenMeta (χ : Semiproposition LAct 1) * 7) 1 :=
  PLE.of_le (formulaLen_instB_le (Sentence.quote_isSemiformul₁ χ) k)
    (PLE.mono hs (PLE.mul (PLE_quote χ k) (PLE_binNumeral hs)) le_rfl le_rfl)

/-- `gBudget k = ‖k‖³` is polynomial. -/
lemma PLE_gBudget {k : V} (hs : 1 ≤ ‖k‖) : PLE ‖k‖ (gBudget k) 1 3 := by
  unfold gBudget
  exact PLE.mono hs (PLE.mul (PLE.mul PLE.var PLE.var) PLE.var) le_rfl le_rfl

/-- **The chain's budget is polynomial in the bit length, uniformly in `V`**: for every family,
slack and choice of the constants there is `C : ℕ` with `chainBoundF ≤ C·‖k‖^{3d+3}` in every
model, once `1 ≤ ‖k‖` (a pure term, so that the coefficient is read off the bookkeeping
combinators; the slack's bound is `PLE_instB`). -/
theorem chainBoundF_PLE (p : Semisentence LAct 1) (S₀ S₁ N₁ d Cψ : ℕ) :
    ∃ C : ℕ, ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (k : V), 1 ≤ ‖k‖ →
      PLE ‖k‖ (chainBoundF p S₀ S₁ N₁ d Cψ k) C (3 * d + 3) :=
  ⟨_, fun V _ _ k hs ↦
    have hm3 : 3 ≤ 3 * d + 3 := by omega
    have hm1 : 1 ≤ 3 * d + 3 := by omega
    have hm0 : 0 ≤ 3 * d + 3 := by omega
    have hmd : 3 * d ≤ 3 * d + 3 := by omega
    -- the atoms, all lifted to the exponent `3d + 3`
    have hχ₁ := PLE.mono hs (PLE_instB (chiF p) hs) le_rfl hm1
    have hψ := PLE.mono hs (PLE_instB (psiF p) hs) le_rfl hm1
    have hB := PLE.mono hs (PLE_instB (Box_g (psiF p)) hs) le_rfl hm1
    have hP := PLE.mono hs (PLE_instB p hs) le_rfl hm1
    have hg := PLE.mono hs (PLE_gBudget hs) le_rfl hm3
    have hgd := PLE.mono hs (PLE.pow (PLE_gBudget hs) d) le_rfl hmd
    have hT := PLE.mono hs (PLE_binNumeral hs) le_rfl hm1
    have hq := PLE.mono hs (PLE_quote (chiF p) k) le_rfl hm0
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
    -- the summands of `chainBoundF`, in order
    have t₁ := (hcst N₁).add (smul 5 hχ₁)
    have t₂ := t₁.add (smul 3 hq)
    have t₃ := t₂.add hT
    have t₄ := t₃.add (hlit 7)
    have t₅ := t₄.add hg
    have t₆ := t₅.add (smul 5 hψ)
    have t₇ := t₆.add (smul 10 ((hB.add hP).add hone))
    have t₈ := t₇.add (hlit 9)
    have t₉ := t₈.add (cmul Cψ (hgd.add hone))
    have t₁₀ := t₉.add (smul 5 hB)
    have t₁₁ := t₁₀.add (smul 10 hP)
    have t₁₂ := t₁₁.add (hlit 9)
    have t₁₃ := t₁₂.add (hcst S₀)
    t₁₃.add (cmul S₁ hP)⟩

/-- **The chain's budget is polynomial in the bit length, uniformly in `V`.** -/
theorem chainBoundF_poly (p : Semisentence LAct 1) (S₀ S₁ N₁ d Cψ : ℕ) :
    ∃ C : ℕ, ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (k : V), 1 ≤ ‖k‖ →
      chainBoundF p S₀ S₁ N₁ d Cψ k ≤ (C : V) * ‖k‖ ^ (3 * d + 3) := by
  obtain ⟨C, hC⟩ := chainBoundF_PLE p S₀ S₁ N₁ d Cψ
  exact ⟨C, fun V _ _ k hs ↦ hC V k hs⟩

end polyBound

/-! ### 7. The bounded Löb premise, truth of `psiF p` in both readings, and the uniform theorem -/

section uniform

/-- **The bounded Löb premise of a family — `□p → p` with the slack** (Critch 2019 Thm 3, the
hypothesis of the parametric bounded Löb theorem, family by family): in every model of `𝗣𝗔`,
a `TAct`-proof code of the `k`-instance of `p` of length `a` with `a + S₀ + S₁·|p(k)| ≤ k`
makes `p(k)` TRUE in both standard readings. For `pConj` this is the ∧-elimination on codes
plus the two search clauses and the truth equations (`Uniform.loebSound_pConj`, slack
`(7, 8)`); for a floor-paying family it is where `BoundedReflection` enters
(`ROUTE_B_SCOPE.md` §3 Phase 3). -/
def LoebSound (p : Semisentence LAct 1) (S₀ S₁ : ℕ) : Prop :=
  ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔] (k a : V),
    a + (S₀ : V) + (S₁ : V) * formulaLen LAct (instB (⌜p⌝ : V) k) ≤ k →
    LenBoxUnbounded TAct a (instB (⌜p⌝ : V) k) →
    Semiformula.Eval (s := stdReading V) ![k] Empty.elim p ∧
    Semiformula.Eval (s := swappedReading V) ![k] Empty.elim p

/-- **`psiF p (k)` is true in both readings for every large `k`, in every model of `𝗣𝗔`**, given
bounded inner necessitation and the family's Löb premise: for `k` above a standard threshold
`kHat`, the box `Box_g (psiF p) (k)` yields a proof of `p(k)` with the slack to spare (the chain),
hence `p(k)` (`LoebSound`), so `psiF p (k)` holds by the fixed point. -/
theorem psiF_true_V (p : Semisentence LAct 1) {S₀ S₁ d : ℕ} (hE : BoundedInnerNec d)
    (hs : LoebSound p S₀ S₁) :
    ∃ kHat : ℕ, ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔] (k : V), (kHat : V) ≤ k →
      Semiformula.Eval (s := stdReading V) ![k] Empty.elim (psiF p) ∧
      Semiformula.Eval (s := swappedReading V) ![k] Empty.elim (psiF p) := by
  obtain ⟨N₁, hN₁⟩ := exists_forward_lengthF p
  obtain ⟨Cψ, hCψ⟩ := hE.nec (psiF p)
  obtain ⟨C, hC⟩ := chainBoundF_poly p S₀ S₁ N₁ d Cψ
  obtain ⟨kHat₀, hkHat₀⟩ := poly_size_le_eventually C (3 * d + 3)
  refine ⟨kHat₀ + 1, fun V _ _ k hk ↦ ?_⟩
  have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
  have hk₀ : (kHat₀ : V) ≤ k := le_trans (by push_cast; exact le_self_add) hk
  have hs1 : 1 ≤ ‖k‖ := by
    have h1 : (1 : V) ≤ k := le_trans (by push_cast; exact le_add_self) hk
    have := length_monotone h1
    rwa [length_one] at this
  have hbound : chainBoundF p S₀ S₁ N₁ d Cψ k ≤ k := le_trans (hC V k hs1) (hkHat₀ V k hk₀)
  have hnec : NecAtF p d Cψ V := fun k ↦ hCψ V k
  constructor
  · refine (eval_psiF_fixed_point_std V p k).mpr fun hbox ↦ ?_
    rw [eval_Box_g_iff_std] at hbox
    obtain ⟨a, ha, hp⟩ := chain_core_VF p hnec (hN₁ V) k hbound hbox
    exact (hs V k a ha hp).1
  · refine (eval_psiF_fixed_point_swap V p k).mpr fun hbox ↦ ?_
    rw [eval_Box_g_iff_swap] at hbox
    obtain ⟨a, ha, hp⟩ := chain_core_VF p hnec (hN₁ V) k hbound hbox
    exact (hs V k a ha hp).2

/-- The antecedent `leF ↑c #0` evaluated at `x` in a structure with standard reduct is `c ≤ x`. -/
lemma eval_leF_numeral_bvar {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (S : Structure LAct M)
    (hS : Structure.lMap emb S = standardModel M) (c : ℕ) (x : M) :
    Semiformula.Eval (s := S) ![x] Empty.elim (leF (↑c) #0 : Semisentence LAct 1) ↔ (c : M) ≤ x := by
  have e : (leF (↑c) #0 : Semisentence LAct 1) =
      Semiformula.lMap emb (leF (↑c) #0 : Semisentence ℒₒᵣ 1) := by
    rw [lMap_emb_leF, lMap_emb_numeral]; rfl
  rw [e, Semiformula.eval_lMap, hS]
  simp [leF, numeral_eq_natCast, le_def]

/-- **The uniform theorem of a family (U8 step 8, the arithmetized parametric bounded Löb
theorem)**: given bounded inner necessitation and the family's Löb premise, there is a standard
`kHat` with `TAct ⊢ ∀ k, (kHat ≤ k → psiF p (k))` — the antecedent in the shape `leF ↑kHat #0`
that `NumeralFacts.lenBoxNat_le_binNumeralMeta` discharges at ℕ. -/
theorem pblt_uniformF (p : Semisentence LAct 1) {S₀ S₁ d : ℕ} (hE : BoundedInnerNec d)
    (hs : LoebSound p S₀ S₁) :
    ∃ kHat : ℕ, TAct ⊢ ∀¹ ((leF (↑kHat) #0 : Semisentence LAct 1) 🡒 psiF p) := by
  obtain ⟨kHat, hkHat⟩ := psiF_true_V p hE hs
  refine ⟨kHat, TAct_complete_of_readings _ fun M _ _ ↦ ?_⟩
  have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
  constructor
  · simp only [Semiformula.eval_all, LogicalConnective.HomClass.map_imply, LogicalConnective.Prop.arrow_eq]
    intro x hx
    exact (hkHat M x ((eval_leF_numeral_bvar _ stdReading_lMap_emb kHat x).mp hx)).1
  · simp only [Semiformula.eval_all, LogicalConnective.HomClass.map_imply, LogicalConnective.Prop.arrow_eq]
    intro x hx
    exact (hkHat M x ((eval_leF_numeral_bvar _ swappedReading_lMap_emb kHat x).mp hx)).2

end uniform

/-! ### 8. The cell half at ℕ: the meta closure and the family's box, found within its budget -/

section cell

/-! #### The bit length at ℕ -/

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

/-! #### The meta closure: a short proof of `psiF p (k)` at ℕ, quadratic in the bit length -/

/-- The length of a substitution instance at the binary numeral, at `ℕ`:
`formulaLenMeta (φ ⇜ ![binNumeralMeta k]) ≤ formulaLenMeta φ · (6·size k + 2)`. -/
lemma formulaLenMeta_subst_binNumeralMeta_le (φ : Semisentence LAct 1) (k : ℕ) :
    formulaLenMeta ((φ ⇜ ![Semiterm.lMap emb (binNumeralMeta k)] : Sentence LAct) : Proposition LAct) ≤
      formulaLenMeta (φ : Semiproposition LAct 1) * (6 * Nat.size k + 2) := by
  refine le_trans (formulaLenMeta_subst_le φ ![Semiterm.lMap emb (binNumeralMeta k)]) ?_
  refine Nat.mul_le_mul_left _ ?_
  rw [Fin.sum_univ_one]
  simp only [Matrix.cons_val_zero]
  rw [termLenMeta_emb_lMap_binNumeralMeta]
  have := termLenMeta_binNumeralMeta k
  omega


/-- **The meta closure (U9 steps 1–3, any family)**: given bounded inner necessitation and the
family's Löb premise, there are standard `k̂ K₀ K₁ K₂` with
`LenBoxNat codeBound (K₀ + K₁·size k + K₂·size k²) TAct ⌜psiF p ⇜ ![binNumeralMeta k]⌝` for every `k > k̂`
— the uniform theorem instantiated at `k` and its antecedent cut away. -/
theorem exists_psiF_instance_length (p : Semisentence LAct 1) {S₀ S₁ d : ℕ} (hE : BoundedInnerNec d)
    (hs : LoebSound p S₀ S₁) :
    ∃ kHat K₀ K₁ K₂ : ℕ, ∀ k : ℕ, kHat < k →
      LenBoxNat (codeBound : ℕ → ℕ) (K₀ + K₁ * Nat.size k + K₂ * Nat.size k * Nat.size k) TAct
        (⌜(psiF p ⇜ ![Semiterm.lMap emb (binNumeralMeta k)] : Sentence LAct)⌝ : ℕ) := by
  obtain ⟨kHat, hprov⟩ := pblt_uniformF p hE hs
  obtain ⟨N₃, hN₃⟩ := lenBoxNat_of_provable hprov
  obtain ⟨C₀, C₁, hle⟩ := lenBoxNat_le_binNumeralMeta kHat
  refine ⟨kHat,
    N₃ + 13 * formulaLenMeta (((leF (↑kHat) #0 : Semisentence LAct 1) 🡒 psiF p : Semisentence LAct 1) : Semiproposition LAct 1)
      + 8 + C₀ + 20 * termLenMeta (Rew.emb (↑kHat : ClosedSemiterm LAct 0) : SyntacticSemiterm LAct 0) + 50
      + 20 * formulaLenMeta (psiF p : Semiproposition LAct 1) + 9,
    30 * formulaLenMeta (((leF (↑kHat) #0 : Semisentence LAct 1) 🡒 psiF p : Semisentence LAct 1) : Semiproposition LAct 1)
      + 126 + 60 * formulaLenMeta (psiF p : Semiproposition LAct 1),
    C₁, fun k hk ↦ ?_⟩
  -- step 1: instantiate the uniform theorem at `binNumeralMeta k`; step 2: the antecedent (`NumeralFacts`)
  have h1 := lenBoxNat_inst_size ((leF (↑kHat) #0 : Semisentence LAct 1) 🡒 psiF p) k hN₃
  have h2 := hle k (Nat.le_of_lt hk)
  -- abbreviations, introduced AFTER the facts so that they fold everywhere
  set fχ := formulaLenMeta (((leF (↑kHat) #0 : Semisentence LAct 1) 🡒 psiF p : Semisentence LAct 1) : Semiproposition LAct 1)
    with hfχ
  set fψ := formulaLenMeta (psiF p : Semiproposition LAct 1) with hfψ
  set a := termLenMeta (Rew.emb (↑kHat : ClosedSemiterm LAct 0) : SyntacticSemiterm LAct 0) with ha
  set t : ClosedSemiterm LAct 0 := Semiterm.lMap emb (binNumeralMeta k) with ht
  set s := Nat.size k with hs
  have hχt : formulaLenMeta ((((leF (↑kHat) #0 : Semisentence LAct 1) 🡒 psiF p) ⇜ ![t] : Sentence LAct) : Proposition LAct)
      ≤ fχ * (6 * s + 2) := formulaLenMeta_subst_binNumeralMeta_le _ k
  have h1' : LenBoxNat (codeBound : ℕ → ℕ) (N₃ + 5 * (fχ * (6 * s + 2)) + 3 * fχ + 6 * s + 8) TAct
      (⌜(((leF (↑kHat) #0 : Semisentence LAct 1) 🡒 psiF p) ⇜ ![t] : Sentence LAct)⌝ : ℕ) :=
    lenBoxNat_codeBound_mono (by omega) h1
  rw [substs_leF_imp] at h1'
  -- step 3: cut
  have h3 := lenBoxNat_mp h1' h2
  refine lenBoxNat_codeBound_mono ?_ h3
  -- the bookkeeping
  have hψt : formulaLenMeta ((psiF p ⇜ ![t] : Sentence LAct) : Proposition LAct) ≤ fψ * (6 * s + 2) :=
    formulaLenMeta_subst_binNumeralMeta_le (psiF p) k
  have hleF : formulaLenMeta ((leF (↑kHat) t : Sentence LAct) : Proposition LAct) ≤ 2 * a + 2 * (6 * s + 1) + 3 := by
    rw [formulaLenMeta_leF_sentence, ht, termLenMeta_emb_lMap_binNumeralMeta]
    have : termLenMeta (Rew.emb (binNumeralMeta k) : SyntacticSemiterm ℒₒᵣ 0) ≤ 6 * s + 1 := termLenMeta_binNumeralMeta k
    omega
  calc _ ≤ N₃ + 5 * (fχ * (6 * s + 2)) + 3 * fχ + 6 * s + 8 + (C₀ + C₁ * s * s)
        + 10 * ((2 * a + 2 * (6 * s + 1) + 3) + fψ * (6 * s + 2)) + 9 := by gcongr
    _ = N₃ + 13 * fχ + 8 + C₀ + 20 * a + 50 + 20 * fψ + 9 + (30 * fχ + 126 + 60 * fψ) * s
        + C₁ * s * s := by ring

/-- **The family's box is found within its budget, with the slack to spare (the arithmetized
`pblt_engine`)**: given bounded inner necessitation and the family's Löb premise, for all large
`k : ℕ` the `k`-instance of `p` has a `TAct`-proof code of some length `a` with
`a + S₀ + S₁·|p(k)| ≤ k` — U8's chain at `V = ℕ` with `chainBoundF ≤ k` from `chainBoundF_poly`
+ `poly_size_le_eventually`, and the meta closure as the box `□_{g k} psiF p (k)` (`quote_instB`,
properness at ℕ, `quadratic_le_cube`). The `≤` is `Nat.le`; the V-generic chain's
`instLE_foundation` is bridged by `le_def`. -/
theorem family_found (p : Semisentence LAct 1) {S₀ S₁ d : ℕ} (hE : BoundedInnerNec d)
    (hs : LoebSound p S₀ S₁) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k → ∃ a : ℕ,
      a + S₀ + S₁ * formulaLen LAct (instB (⌜p⌝ : ℕ) k) ≤ k ∧ LenBoxUnbounded TAct a (instB (⌜p⌝ : ℕ) k) := by
  obtain ⟨N₁, hN₁⟩ := exists_forward_lengthF p
  obtain ⟨Cψ, hCψ⟩ := hE.nec (psiF p)
  obtain ⟨C, hC⟩ := chainBoundF_poly p S₀ S₁ N₁ d Cψ
  obtain ⟨kHat₁, hkHat₁⟩ := poly_size_le_eventually C (3 * d + 3)
  obtain ⟨kHat, K₀, K₁, K₂, hmeta⟩ := exists_psiF_instance_length p hE hs
  refine ⟨kHat₁ + kHat + 2 ^ (K₀ + K₁ + K₂ + 1), fun k hk ↦ ?_⟩
  have hnec : NecAtF p d Cψ ℕ := fun k ↦ hCψ ℕ k
  have h2pow : 2 ≤ 2 ^ (K₀ + K₁ + K₂ + 1) := Nat.le_self_pow (Nat.succ_ne_zero _) 2
  have h1k : 1 < k := by omega
  -- `1 ≤ ‖k‖` and the budget inequality, in Foundation's `≤`
  have hs1 := length_monotone (V := ℕ) (le_def.mpr (Or.inr h1k))
  rw [length_one] at hs1
  have hbound := le_def.mpr (le_def_trans (le_def.mp (hC ℕ k hs1))
    (le_def.mp (hkHat₁ ℕ k (le_def.mpr (Or.inr (by rw [natCast_nat]; omega))))))
  -- the meta closure, as the box on codes, below the budget
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
  obtain ⟨a, ha, hp⟩ := chain_core_VF p hnec (hN₁ ℕ) k hbound hbox
  refine ⟨a, ?_, hp⟩
  rw [natCast_nat, natCast_nat] at ha
  rcases le_def.mp ha with h | h <;> omega

end cell

end ArithS
