import ArithS.Assembly.Family

/-!
# ArithS.Assembly.Uniform — the uniform PBLT chain (U8) at the conjunction family `pConj`

`docs/notes/archive/M4_BOUNDED_HBL/BRIEF.md` §6 (U8, steps 1–8) with the §7 addendum (the Löb
family is the conjunction `pConj := qDupoc ⋏ qCupod`, the models are the two standard readings
`stdReading`/`swappedReading`). Everything is a theorem GIVEN the one named hypothesis
`BoundedInnerNec d` (`Assembly/Prep.lean` §6, Critch's assumption (d): a per-`χ` constant `C_χ`
and a polynomial expansion `C_χ · (g(k)^d + 1)`).

**Since `ROUTE_B_SCOPE.md` §3 Phase 1 this file is an INSTANTIATION of the
family-parametric assembly `Assembly/Family.lean` at `p := pConj` with slack `(S₀, S₁) = (7, 8)`**
— the ∧-elimination of `pconj_both_V` costs `8(|qDupoc(k)| + |qCupod(k)|) + 7 ≤ 7 + 8·|pConj(k)|`
(`formulaLen_instB_pConj`). `psi = psiF pConj`, `chi₁ = chiF pConj`, `NecAt = NecAtF pConj`,
`chainBound = chainBoundF pConj 7 8` (all by `rfl`); the family's Löb premise is
**`loebSound_pConj : LoebSound pConj 7 8`** (the search clauses + the truth equations in both
readings), and every theorem below keeps its original statement, now a corollary of the generic
one. The generic material that used to open this file (`termLen_binNumeral_le_V`,
`poly_size_le_eventually`, the two readings as models of `TAct`, the `PLE` calculus,
`eval_leF_numeral_bvar`) lives in `Family.lean` under the same names.

1. `eval_psi_fixed_point_std`/`_swap`: the fixed point is TRUE in both readings.
2. `psi_forward`, `exists_forward_length`, `forward_inst_V`: the forward direction, with a
   length, instantiated at `k`.
3. **The chain** (`chain_core_V`/`chain_V`/`chain_guard_V`) with its budget `chainBound` and
   `chainBound_poly`.
4. `loebSound_pConj`, `psi_true_V`, **`pblt_uniform`**: `TAct ⊢ ∀ k, (kHat ≤ k → psi(k))`.

Every threshold and constant is EXISTENTIAL (`HANDOVER_ARITHMETIZED_S.md` §5–6); `simp` never
sees a closed quote of `psi`/`pConj`; `omega` is never asked about `V`.
-/

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open LAct

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ### 1. The fixed point in both readings -/

section models

variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

/-- The fixed point, evaluated in the standard reading: `psi(x) ↔ (Box_g psi (x) → pConj(x))`. -/
theorem eval_psi_fixed_point_std (x : M) :
    Semiformula.Eval (s := stdReading M) ![x] Empty.elim psi ↔
      (Semiformula.Eval (s := stdReading M) ![x] Empty.elim (Box_g psi) →
        Semiformula.Eval (s := stdReading M) ![x] Empty.elim pConj) :=
  eval_psiF_fixed_point_std M pConj x

/-- The fixed point, evaluated in the transposed reading. -/
theorem eval_psi_fixed_point_swap (x : M) :
    Semiformula.Eval (s := swappedReading M) ![x] Empty.elim psi ↔
      (Semiformula.Eval (s := swappedReading M) ![x] Empty.elim (Box_g psi) →
        Semiformula.Eval (s := swappedReading M) ![x] Empty.elim pConj) :=
  eval_psiF_fixed_point_swap M pConj x

end models

/-! ### 2. The forward direction of the fixed point, with a length, instantiated at `k` -/

section forward

/-- The one-variable body of the forward direction: `psi 🡒 (Box_g psi 🡒 pConj)` (`chiF pConj`). -/
noncomputable abbrev chi₁ : Semisentence LAct 1 := chiF pConj

lemma chi₁_def : chi₁ = psi 🡒 (Box_g psi 🡒 pConj) := rfl

/-- **`TAct ⊢ ∀ k, psi(k) → (Box_g psi (k) → pConj(k))`** — the forward direction of
`psi_fixed_point`, by completeness over the two readings. -/
theorem psi_forward : TAct ⊢ ∀¹ chi₁ := psiF_forward pConj

/-- The forward direction has a bounded proof code, of some standard length `N₁`, in every model. -/
theorem exists_forward_length : ∃ N₁ : ℕ, ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁],
    LenBoxUnbounded TAct (N₁ : V) (⌜(∀¹ chi₁ : Sentence LAct)⌝ : V) :=
  exists_forward_lengthF pConj

/-- The `k`-instance of `⌜chi₁⌝` is the code implication `psi(k) → (Box_g psi (k) → pConj(k))`. -/
lemma instB_quote_chi₁ (k : V) :
    instB (⌜chi₁⌝ : V) k =
      Bootstrapping.imp LAct (instB (⌜psi⌝ : V) k)
        (Bootstrapping.imp LAct (instB (⌜Box_g psi⌝ : V) k) (instB (⌜pConj⌝ : V) k)) :=
  instB_quote_chiF pConj k

/-- **The instantiated forward direction** (U8 step 1): from `□_{N₁} ∀¹ chi₁`, a proof code of
`psi(k) → (Box_g psi (k) → pConj(k))` of length `≤ N₁ + 5|chi₁(k)| + 3|chi₁| + |binNumeral k| + 7`. -/
theorem forward_inst_V {N₁ : V} (h : LenBoxUnbounded TAct N₁ (⌜(∀¹ chi₁ : Sentence LAct)⌝ : V)) (k : V) :
    LenBoxUnbounded TAct
      (N₁ + 5 * formulaLen LAct (instB (⌜chi₁⌝ : V) k) + 3 * formulaLen LAct (⌜chi₁⌝ : V)
        + termLen LAct (binNumeral k) + 7)
      (Bootstrapping.imp LAct (instB (⌜psi⌝ : V) k)
        (Bootstrapping.imp LAct (instB (⌜Box_g psi⌝ : V) k) (instB (⌜pConj⌝ : V) k))) :=
  forward_inst_VF pConj h k

end forward

/-! ### 3. The chain -/

section chain

/-- **Bounded inner necessitation at `psi`, in one model, with its constant `Cψ`** — the
instance of `BoundedInnerNec.nec psi` the chain consumes (`NecAtF pConj`). -/
def NecAt (d Cψ : ℕ) (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] : Prop := NecAtF pConj d Cψ V

/-- **The total budget consumed by the chain** at `k`, for the length `N₁` of the forward direction
and the constants `d`, `Cψ` of bounded inner necessitation at `psi`: `chainBoundF pConj 7 8` —
the instantiation (U3), the cut with the assumed box (U2), the necessitation expansion (U5), the
second cut (U2) and the ∧-elimination slack `7 + 8·|pConj(k)|` (`pconj_both_V`). -/
noncomputable def chainBound (N₁ d Cψ : ℕ) (k : V) : V := chainBoundF pConj 7 8 N₁ d Cψ k

/-- `|pConj(k)| = |qDupoc(k)| + |qCupod(k)| + 1` on codes. -/
lemma formulaLen_instB_pConj (k : V) :
    formulaLen LAct (instB (⌜pConj⌝ : V) k) =
      formulaLen LAct (instB (⌜qDupoc⌝ : V) k) + formulaLen LAct (instB (⌜qCupod⌝ : V) k) + 1 := by
  rw [instB_quote_pConj,
    formulaLen_and (isFormula_instB_quote qDupoc k).isUFormula (isFormula_instB_quote qCupod k).isUFormula]

/-- The ∧-elimination slack of `pconj_both_V` is below the family slack `(7, 8)` at `pConj`
(for VARIABLE lengths `x y z`, so that `push_cast` never sees a quote). -/
lemma pConj_slack_le (a x y z : V) (h : z = x + y + 1) :
    a + 8 * (x + y) + 7 ≤ a + ((7 : ℕ) : V) + ((8 : ℕ) : V) * z := by
  subst h
  push_cast
  calc a + 8 * (x + y) + 7 ≤ a + 8 * (x + y) + 7 + 8 := le_self_add
    _ = a + 7 + 8 * (x + y + 1) := by ring

/-- **The chain, core form** (U8 steps 1–5): given the forward direction at length `N₁`, the
assumed box `□_{g k} psi(k)` and `chainBound ≤ k`, a proof code of `pConj(k)` of some length `a`
below the ∧-elimination threshold of `pconj_both_V`. -/
theorem chain_core_V {d Cψ : ℕ} (hnec : NecAt d Cψ V)
    {N₁ : ℕ} (hN₁ : LenBoxUnbounded TAct (N₁ : V) (⌜(∀¹ chi₁ : Sentence LAct)⌝ : V)) (k : V)
    (hk : chainBound N₁ d Cψ k ≤ k)
    (hbox : LenBoxUnbounded TAct (gBudget k) (instB (⌜psi⌝ : V) k)) :
    ∃ a : V,
      a + 8 * (formulaLen LAct (instB (⌜qDupoc⌝ : V) k) + formulaLen LAct (instB (⌜qCupod⌝ : V) k)) + 7 ≤ k ∧
      LenBoxUnbounded TAct a (instB (⌜pConj⌝ : V) k) := by
  obtain ⟨a, ha, h⟩ := chain_core_VF pConj hnec hN₁ k hk hbox
  exact ⟨a, le_trans (pConj_slack_le a _ _ _ (formulaLen_instB_pConj k)) ha, h⟩

/-- **The chain** (U8 steps 1–6): both searchers find their guards. -/
theorem chain_V {d Cψ : ℕ} (hnec : NecAt d Cψ V)
    {N₁ : ℕ} (hN₁ : LenBoxUnbounded TAct (N₁ : V) (⌜(∀¹ chi₁ : Sentence LAct)⌝ : V)) (k : V)
    (hk : chainBound N₁ d Cψ k ≤ k)
    (hbox : LenBoxUnbounded TAct (gBudget k) (instB (⌜psi⌝ : V) k)) :
    EvalGraph 2 (DupocV k) (DupocV k) (DupocV k) 0 ∧ EvalGraph 2 (CupodV k) (CupodV k) (CupodV k) 1 := by
  obtain ⟨a, ha, hpc⟩ := chain_core_V hnec hN₁ k hk hbox
  exact pconj_both_V k a ha hpc

/-- **Both searchers FIND their guards from a box of the conjunction** (the box form of
`pconj_both_V`): a proof code of `pConj(k)` of length `≤ a` with the ∧-elimination slack below `k`
gives `LenBox TAct k` of both guard codes. -/
theorem pconj_guards_V (k : V) (a : V)
    (ha : a + 8 * (formulaLen LAct (instB (⌜qDupoc⌝ : V) k) + formulaLen LAct (instB (⌜qCupod⌝ : V) k)) + 7 ≤ k)
    (hpc : LenBoxUnbounded TAct a (instB (⌜pConj⌝ : V) k)) :
    LenBox TAct k (guardCode (⌜guardTemplate 0⌝ : V) (DupocV k) (DupocV k)) ∧
    LenBox TAct k (guardCode (⌜guardTemplate 1⌝ : V) (CupodV k) (CupodV k)) := by
  rw [instB_quote_pConj] at hpc
  have hx := isFormula_instB_quote qDupoc k
  have hy := isFormula_instB_quote qCupod k
  have h₁ := lenBoxUnbounded_mono_V ha (lenBoxUnbounded_andL_V hx hy hpc)
  have h₂ := lenBoxUnbounded_mono_V ha (lenBoxUnbounded_andR_V hx hy hpc)
  rw [lenBoxUnbounded_iff_lenBox, ← guardCode_DupocV_eq_instB] at h₁
  rw [lenBoxUnbounded_iff_lenBox, ← guardCode_CupodV_eq_instB] at h₂
  exact ⟨h₁, h₂⟩

/-- **The chain, box form**: Dupoc actually FINDS a proof of its guard within its budget. -/
theorem chain_guard_V {d Cψ : ℕ} (hnec : NecAt d Cψ V)
    {N₁ : ℕ} (hN₁ : LenBoxUnbounded TAct (N₁ : V) (⌜(∀¹ chi₁ : Sentence LAct)⌝ : V)) (k : V)
    (hk : chainBound N₁ d Cψ k ≤ k)
    (hbox : LenBoxUnbounded TAct (gBudget k) (instB (⌜psi⌝ : V) k)) :
    LenBox TAct k (guardCode (⌜guardTemplate 0⌝ : V) (DupocV k) (DupocV k)) ∧
    LenBox TAct k (guardCode (⌜guardTemplate 1⌝ : V) (CupodV k) (CupodV k)) := by
  obtain ⟨a, ha, hpc⟩ := chain_core_V hnec hN₁ k hk hbox
  exact pconj_guards_V k a ha hpc

end chain

/-! ### 4. The budget is polynomial in the bit length -/

section polyBound

/-- **The chain's budget is polynomial in the bit length, uniformly in `V`**: for every choice of
the constants there is `C : ℕ` with `chainBound ≤ C·‖k‖^{3d+3}` in every model, once `1 ≤ ‖k‖`
(`chainBoundF_PLE` at `pConj`). -/
theorem chainBound_PLE (N₁ d Cψ : ℕ) :
    ∃ C : ℕ, ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (k : V), 1 ≤ ‖k‖ →
      PLE ‖k‖ (chainBound N₁ d Cψ k) C (3 * d + 3) :=
  chainBoundF_PLE pConj 7 8 N₁ d Cψ

/-- **The chain's budget is polynomial in the bit length, uniformly in `V`.** -/
theorem chainBound_poly (N₁ d Cψ : ℕ) :
    ∃ C : ℕ, ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (k : V), 1 ≤ ‖k‖ →
      chainBound N₁ d Cψ k ≤ (C : V) * ‖k‖ ^ (3 * d + 3) :=
  chainBoundF_poly pConj 7 8 N₁ d Cψ

end polyBound

/-! ### 5. The Löb premise at `pConj`, truth of `psi` in both readings, and the uniform theorem -/

section uniform

/-- **The bounded Löb premise of the conjunction family, slack `(7, 8)`**: a proof code of
`pConj(k)` of length `a` with `a + 7 + 8·|pConj(k)| ≤ k` makes both searchers find their guards
(`pconj_both_V`, the ∧-elimination on codes + the two search clauses), so `pConj(k)` is TRUE in
both readings (`eval_pConj_iff_stdReading`, `eval_pConj_iff_swap`). -/
theorem loebSound_pConj : LoebSound pConj 7 8 := by
  intro V _ _ k a ha h
  have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
  have ha' : a + 8 * (formulaLen LAct (instB (⌜qDupoc⌝ : V) k) + formulaLen LAct (instB (⌜qCupod⌝ : V) k)) + 7 ≤ k :=
    le_trans (pConj_slack_le a _ _ _ (formulaLen_instB_pConj k)) ha
  obtain ⟨h1, h2⟩ := pconj_both_V k a ha' h
  exact ⟨(eval_pConj_iff_stdReading k).mpr ⟨⟨2, h1⟩, ⟨2, h2⟩⟩,
    (eval_pConj_iff_swap k).mpr ⟨⟨2, h1⟩, ⟨2, h2⟩⟩⟩

/-- **`psi(k)` is true in both readings for every large `k`, in every model of `𝗜𝚺₁`**, given
bounded inner necessitation: for `k` above a standard threshold `kHat`, the box `Box_g psi (k)`
implies `pConj(k)` (the chain), so `psi(k)` holds by the fixed point. -/
theorem psi_true_V {d : ℕ} (hE : BoundedInnerNec d) :
    ∃ kHat : ℕ, ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔] (k : V), (kHat : V) ≤ k →
      Semiformula.Eval (s := stdReading V) ![k] Empty.elim psi ∧
      Semiformula.Eval (s := swappedReading V) ![k] Empty.elim psi :=
  psiF_true_V pConj hE loebSound_pConj

/-- **The uniform theorem (U8 step 8)**: given bounded inner necessitation, there is a standard
`kHat` with `TAct ⊢ ∀ k, (kHat ≤ k → psi(k))` — the antecedent in the shape `leF ↑kHat #0` that
`NumeralFacts.lenBoxNat_le_binNumeralMeta` discharges at ℕ. -/
theorem pblt_uniform {d : ℕ} (hE : BoundedInnerNec d) :
    ∃ kHat : ℕ, TAct ⊢ ∀¹ ((leF (↑kHat) #0 : Semisentence LAct 1) 🡒 psi) :=
  pblt_uniformF pConj hE loebSound_pConj

end uniform

end ArithS
