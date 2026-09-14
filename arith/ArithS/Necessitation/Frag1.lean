import ArithS.Necessitation.Frag1Rows

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open LAct

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

/-! ## 0.1 `NoDrop'` — the non-dropping tags including the two cuts (6, 7) -/

section noDrop'

/-- **A well-tagged list, cuts admitted**: every step carries one of the seven non-dropping tags
(`0`–`4` of `NoDrop`, plus the goal cut `6` and the lemma cut `7`). -/
def NoDrop' (S : V) : Prop :=
  ∀ i < len S, sTag S.[i] = 0 ∨ sTag S.[i] = 1 ∨ sTag S.[i] = 2 ∨ sTag S.[i] = 3 ∨ sTag S.[i] = 4 ∨
    sTag S.[i] = 6 ∨ sTag S.[i] = 7

instance noDrop'_definable : 𝚫₁-Predicate (NoDrop' : V → Prop) := by
  unfold NoDrop' sTag; definability

lemma NoDrop.noDrop' {S : V} (h : NoDrop S) : NoDrop' S := fun i hi ↦ by
  rcases h i hi with h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))

lemma noDrop'_nil : NoDrop' (0 : V) := fun i hi ↦ by simp at hi

lemma noDrop'_appendV {S₁ S₂ : V} (h₁ : NoDrop' S₁) (h₂ : NoDrop' S₂) : NoDrop' (appendV S₁ S₂) := by
  intro i hi
  rw [len_appendV] at hi
  rcases lt_or_ge i (len S₁) with h | h
  · rw [nth_appendV_lt S₁ S₂ i h]; exact h₁ i h
  · obtain ⟨j, rfl⟩ : ∃ j, i = len S₁ + j := ⟨i - len S₁, (add_tsub_cancel_of_le h).symm⟩
    rw [nth_appendV_add]; exact h₂ j (lt_of_add_lt_add_left hi)

lemma noDrop'_single {s : V}
    (h : sTag s = 0 ∨ sTag s = 1 ∨ sTag s = 2 ∨ sTag s = 3 ∨ sTag s = 4 ∨ sTag s = 6 ∨ sTag s = 7) :
    NoDrop' (?[s] : V) := by
  intro i hi
  rw [len_adjoin, len_nil, zero_add] at hi
  rcases zero_or_succ i with rfl | ⟨i, rfl⟩
  · simpa using h
  · exact absurd hi (not_lt.mpr le_add_self)

lemma noDrop'_cons {s S : V}
    (h : sTag s = 0 ∨ sTag s = 1 ∨ sTag s = 2 ∨ sTag s = 3 ∨ sTag s = 4 ∨ sTag s = 6 ∨ sTag s = 7)
    (hS : NoDrop' S) : NoDrop' (s ∷ S) := by
  rw [cons_eq_appendV_single]; exact noDrop'_appendV (noDrop'_single h) hS

/-- **A fact survives a cut-admitting list, shifted once per eigenvariable step.** -/
lemma mem_ctxVec_of_mem' {Γ₀ S x : V} (hS : NoDrop' S) (hx : x ∈ Γ₀) :
    ∀ j ≤ len S, shiftIterV x (shiftsAux S j) ∈ (ctxVec Γ₀ S).[j] := by
  intro j
  induction j using ISigma1.pi1_succ_induction with
  | hP => definability
  | zero => intro _; simpa using hx
  | succ j ih =>
    intro hj
    have hj' : j < len S := lt_of_lt_of_le (lt_add_one j) hj
    have ih' := ih (le_of_lt hj')
    rw [nth_ctxVec_succ Γ₀ S hj']
    rcases hS j hj' with h | h | h | h | h | h | h
    · rw [shiftsAux_succ_of_noShift (by rw [h]; norm_num)]
      exact mem_ctxAfter_of_noShift' (Or.inl h) ih'
    · rw [shiftsAux_succ_of_noShift (by rw [h]; norm_num)]
      exact mem_ctxAfter_of_noShift' (Or.inr (Or.inl h)) ih'
    · rw [shiftsAux_succ_of_shift (Or.inl h), shiftIterV_succ]
      exact mem_ctxAfter_of_shift (Or.inl h) ih'
    · rw [shiftsAux_succ_of_shift (Or.inr h), shiftIterV_succ]
      exact mem_ctxAfter_of_shift (Or.inr h) ih'
    · rw [shiftsAux_succ_of_noShift (by rw [h]; norm_num)]
      exact mem_ctxAfter_of_noShift' (Or.inr (Or.inr (Or.inl h))) ih'
    · rw [shiftsAux_succ_of_noShift (by rw [h]; norm_num)]
      exact mem_ctxAfter_of_noShift' (Or.inr (Or.inr (Or.inr (Or.inl h)))) ih'
    · rw [shiftsAux_succ_of_noShift (by rw [h]; norm_num)]
      exact mem_ctxAfter_of_noShift' (Or.inr (Or.inr (Or.inr (Or.inr h)))) ih'

lemma mem_finalCtx_of_mem' {Γ₀ S x : V} (hS : NoDrop' S) (hx : x ∈ Γ₀) :
    shiftIterV x (shiftsV S) ∈ finalCtx Γ₀ S :=
  mem_ctxVec_of_mem' hS hx (len S) le_rfl

end noDrop'

/-! ## 0.2 `StepOK`/`ListOK` are monotone in the witness cap `M` -/

section mono

lemma HornOK.mono {tbl E M M' Γ s : V} (hM : M ≤ M') (h : HornOK tbl E M Γ s) : HornOK tbl E M' Γ s :=
  ⟨h.1, h.2.1, le_trans h.2.2.1 hM, le_trans h.2.2.2.1 hM, h.2.2.2.2.1, h.2.2.2.2.2⟩

lemma StepOK.mono {tbl E M M' Γ s : V} (hM : M ≤ M') (h : StepOK tbl E M Γ s) : StepOK tbl E M' Γ s := by
  obtain ⟨hΓ, h⟩ := h
  refine ⟨hΓ, ?_⟩
  rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | h | h | h | h | h
  · exact Or.inl ⟨h1, h2.mono hM, h3⟩
  · exact Or.inr (Or.inl ⟨h1, h2.mono hM, h3⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨h1, h2.mono hM, h3⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))

lemma ListOK.mono {tbl E M M' Γ S : V} (hM : M ≤ M') (h : ListOK tbl E M Γ S) : ListOK tbl E M' Γ S :=
  fun i hi ↦ (h i hi).mono hM

end mono

/-! ## 0.3 The cost of an appended list is the sum of the costs -/

section costAppend

lemma nthFromEnd_appendV_lt (S₁ S₂ : V) {k : V} (hk : k < len S₂) :
    nthFromEnd (appendV S₁ S₂) k = nthFromEnd S₂ k := by
  obtain ⟨a, ha⟩ : ∃ a, len S₂ = a + (k + 1) :=
    ⟨len S₂ - (k + 1), (tsub_add_cancel_of_le (lt_iff_succ_le.mp hk)).symm⟩
  rw [nthFromEnd_eq (v := S₂) ha,
    nthFromEnd_eq (v := appendV S₁ S₂) (a := len S₁ + a) (by rw [len_appendV, ha, add_assoc]), nth_appendV_add]

lemma nthFromEnd_appendV_add (S₁ S₂ : V) {k : V} (hk : k < len S₁) :
    nthFromEnd (appendV S₁ S₂) (len S₂ + k) = nthFromEnd S₁ k := by
  obtain ⟨a, ha⟩ : ∃ a, len S₁ = a + (k + 1) :=
    ⟨len S₁ - (k + 1), (tsub_add_cancel_of_le (lt_iff_succ_le.mp hk)).symm⟩
  rw [nthFromEnd_eq (v := S₁) ha,
    nthFromEnd_eq (v := appendV S₁ S₂) (a := a) (by rw [len_appendV, ha]; ring),
    nth_appendV_lt _ _ a (by rw [ha]; exact lt_add_of_pos_right _ (lt_of_lt_of_le _root_.zero_lt_one le_add_self))]

lemma nthFromEnd_ctxVec_appendV_lt (Γ S₁ S₂ : V) {k : V} (hk : k < len S₂) :
    nthFromEnd (ctxVec Γ (appendV S₁ S₂)) (k + 1) = nthFromEnd (ctxVec (finalCtx Γ S₁) S₂) (k + 1) := by
  obtain ⟨a, ha⟩ : ∃ a, len S₂ = a + (k + 1) :=
    ⟨len S₂ - (k + 1), (tsub_add_cancel_of_le (lt_iff_succ_le.mp hk)).symm⟩
  have ha' : a ≤ len S₂ := by rw [ha]; exact le_self_add
  rw [nthFromEnd_eq (v := ctxVec (finalCtx Γ S₁) S₂) (a := a) (by rw [len_ctxVec, ha, add_assoc]),
    nthFromEnd_eq (v := ctxVec Γ (appendV S₁ S₂)) (a := len S₁ + a)
      (by rw [len_ctxVec, len_appendV, ha]; ring),
    nth_ctxVec_appendV_add Γ S₁ S₂ a ha']

lemma nthFromEnd_ctxVec_appendV_add (Γ S₁ S₂ : V) {k : V} (hk : k < len S₁) :
    nthFromEnd (ctxVec Γ (appendV S₁ S₂)) (len S₂ + k + 1) = nthFromEnd (ctxVec Γ S₁) (k + 1) := by
  obtain ⟨a, ha⟩ : ∃ a, len S₁ = a + (k + 1) :=
    ⟨len S₁ - (k + 1), (tsub_add_cancel_of_le (lt_iff_succ_le.mp hk)).symm⟩
  have ha' : a ≤ len S₁ := by rw [ha]; exact le_self_add
  rw [nthFromEnd_eq (v := ctxVec Γ S₁) (a := a) (by rw [len_ctxVec, ha, add_assoc]),
    nthFromEnd_eq (v := ctxVec Γ (appendV S₁ S₂)) (a := a)
      (by rw [len_ctxVec, len_appendV, ha]; ring),
    nth_ctxVec_appendV_le Γ S₁ S₂ ha']

lemma costAux_appendV_lo (N E Γ S₁ S₂ : V) : ∀ j ≤ len S₂,
    costAux N E (ctxVec Γ (appendV S₁ S₂)) (appendV S₁ S₂) j = costAux N E (ctxVec (finalCtx Γ S₁) S₂) S₂ j := by
  intro j
  induction j using ISigma1.sigma1_succ_induction with
  | hP => definability
  | zero => intro _; simp
  | succ j ih =>
    intro hj
    have hj' : j < len S₂ := lt_of_lt_of_le (lt_add_one j) hj
    rw [costAux_succ, costAux_succ, ih (le_of_lt hj'), nthFromEnd_appendV_lt _ _ hj',
      nthFromEnd_ctxVec_appendV_lt _ _ _ hj']

lemma costAux_appendV_hi (N E Γ S₁ S₂ : V) : ∀ i ≤ len S₁,
    costAux N E (ctxVec Γ (appendV S₁ S₂)) (appendV S₁ S₂) (len S₂ + i) =
      costAux N E (ctxVec (finalCtx Γ S₁) S₂) S₂ (len S₂) + costAux N E (ctxVec Γ S₁) S₁ i := by
  intro i
  induction i using ISigma1.sigma1_succ_induction with
  | hP => definability
  | zero => intro _; rw [add_zero, costAux_zero, add_zero, costAux_appendV_lo _ _ _ _ _ _ le_rfl]
  | succ i ih =>
    intro hi
    have hi' : i < len S₁ := lt_of_lt_of_le (lt_add_one i) hi
    rw [← add_assoc, costAux_succ, costAux_succ, ih (le_of_lt hi'), nthFromEnd_appendV_add _ _ hi',
      nthFromEnd_ctxVec_appendV_add _ _ _ hi', add_assoc]

/-- **The cost of an appended list**: the first list at `Γ`, the second at the first's final context. -/
theorem costSum_appendV (N E Γ S₁ S₂ : V) :
    costSum N E Γ (appendV S₁ S₂) = costSum N E Γ S₁ + costSum N E (finalCtx Γ S₁) S₂ := by
  unfold costSum
  rw [len_appendV, add_comm (len S₁), costAux_appendV_hi _ _ _ _ _ _ le_rfl, add_comm]

lemma costSum_single (N E Γ s : V) : costSum N E Γ ?[s] = stepCost N E Γ s := by
  unfold costSum
  rw [len_adjoin, len_nil, zero_add, ← zero_add (1 : V), costAux_succ, costAux_zero, zero_add,
    nthFromEnd_eq (v := ctxVec Γ ?[s]) (a := 0) (by simp),
    nthFromEnd_eq (v := ?[s]) (a := 0) (by simp), nth_ctxVec_zero, nth_adjoin_zero]

lemma costSum_cons (N E Γ s S : V) : costSum N E Γ (s ∷ S) = stepCost N E Γ s + costSum N E (ctxAfter Γ s) S := by
  rw [cons_eq_appendV_single, costSum_appendV, costSum_single, finalCtx_single]

lemma costSum_nil (N E Γ : V) : costSum N E Γ 0 = 0 := by simp [costSum]

end costAppend

/-! ## 0.4 Binary numerals are shift-invariant -/

section bnumShift

lemma termShift_qqMul_LAct {x y : V} (hx : IsUTerm LAct x) (hy : IsUTerm LAct y) :
    termShift LAct (x ^* y) = termShift LAct x ^* termShift LAct y := by
  unfold qqMul
  rw [termShift_func isFunc_LAct_mul (by simp [hx, hy]), termShiftVec_cons₂ hx hy]

lemma termShift_qqTwo_LAct : termShift LAct (𝟐 : V) = 𝟐 := by
  unfold qqTwo
  rw [termShift_qqAdd isFunc_LAct_addIndex qqOne_uterm_LAct qqOne_uterm_LAct, termShift_qqOne isFunc_LAct_oneIndex]

/-- A binary numeral has no free variables: `termShift (bnum n) = bnum n`. -/
lemma termShift_bnum (n : V) : termShift LAct (bnum n) = bnum n := by
  induction n using ISigma1.pi1_order_induction with
  | hP => definability
  | ind n ih =>
    rcases zero_one_or_two_le n with rfl | rfl | h2
    · rw [bnum_zero, termShift_qqZero isFunc_LAct_zeroIndex]
    · rw [bnum_one, termShift_qqOne isFunc_LAct_oneIndex]
    obtain ⟨hm, hlt, he | ho⟩ := two_le_cases h2
    · rw [he, bnum_two_mul hm, termShift_qqMul_LAct isUTerm_qqTwo_LAct (isSemiterm_bnum_LAct 0 _).isUTerm,
        termShift_qqTwo_LAct, ih (n / 2) hlt]
    · rw [ho, bnum_two_mul_add_one hm,
        termShift_qqAdd isFunc_LAct_addIndex (isUTerm_qqMul_iff.mpr ⟨isUTerm_qqTwo_LAct, (isSemiterm_bnum_LAct 0 _).isUTerm⟩)
          qqOne_uterm_LAct,
        termShift_qqMul_LAct isUTerm_qqTwo_LAct (isSemiterm_bnum_LAct 0 _).isUTerm, termShift_qqTwo_LAct,
        ih (n / 2) hlt, termShift_qqOne isFunc_LAct_oneIndex]

lemma termShift_bnum_add_one (n : V) : termShift LAct (bnum n ^+ 𝟏) = bnum n ^+ 𝟏 := by
  rw [termShift_qqAdd isFunc_LAct_addIndex (isSemiterm_bnum_LAct 0 _).isUTerm qqOne_uterm_LAct, termShift_bnum,
    termShift_qqOne isFunc_LAct_oneIndex]

end bnumShift


/-! ## 1. `goalElim` — recovering a child's goal: `sElimExs`×2 + `sSplit`×3 -/

section goalElim

/-- The goal body after the first elimination: `d := &0`, `n` still `#0`. -/
noncomputable def goalBody1 (s u : V) : V :=
  derFact (^&0) ^⋏ (fstIdxFact s (^&0) ^⋏ (dlenFact (^&0) (bv 0) ^⋏ leFact (bv 0) u))

noncomputable def goalBody1Def : 𝚺₁.Semisentence 3 := .mkSigma
  “y s u. ∃ z, !qqFvarDef z 0 ∧ ∃ b0, !qqBvarDef b0 0 ∧ ∃ f1, !derFactDef f1 z ∧ ∃ f2, !fstIdxFactDef f2 s z ∧
    ∃ f3, !dlenFactDef f3 z b0 ∧ ∃ f4, !leFactDef f4 b0 u ∧ ∃ c3, !qqAndDef c3 f3 f4 ∧ ∃ c2, !qqAndDef c2 f2 c3 ∧
    !qqAndDef y f1 c2”
instance goalBody1_defined : 𝚺₁-Function₂ (goalBody1 : V → V → V) via goalBody1Def := .mk
  fun v ↦ by
    simp [goalBody1Def, derFact_defined.iff, fstIdxFact_defined.iff, dlenFact_defined.iff, leFact_defined.iff,
      goalBody1, bv]
instance goalBody1_definable : 𝚺₁-Function₂ (goalBody1 : V → V → V) := goalBody1_defined.to_definable

/-- **The recovery list** of a child's goal fact `goalFact s u` (DESIGN_fragments §2.2): eliminate `d`, eliminate
`n`, split the three conjunctions. Leaves `d = &1`, `n = &0` and the four facts, with the closed witnesses
shifted twice. -/
noncomputable def goalElim (s u : V) : V :=
  sElimExs (^∃ goalBody s u) ∷
  sElimExs (goalBody1 (termShift LAct s) (termShift LAct u)) ∷
  sSplit (derFact (^&1))
    (fstIdxFact (termShift LAct (termShift LAct s)) (^&1) ^⋏
      (dlenFact (^&1) (^&0) ^⋏ leFact (^&0) (termShift LAct (termShift LAct u)))) ∷
  sSplit (fstIdxFact (termShift LAct (termShift LAct s)) (^&1))
    (dlenFact (^&1) (^&0) ^⋏ leFact (^&0) (termShift LAct (termShift LAct u))) ∷
  sSplit (dlenFact (^&1) (^&0)) (leFact (^&0) (termShift LAct (termShift LAct u))) ∷ (0 : V)

noncomputable def goalElimDef : 𝚺₁.Semisentence 3 := .mkSigma
  “y s u. ∃ b, !goalBodyDef b s u ∧ ∃ p1, !qqExsDef p1 b ∧ ∃ st1, !pairDef st1 3 p1 ∧
    ∃ s1, !(termShiftGraph LAct) s1 s ∧ ∃ u1, !(termShiftGraph LAct) u1 u ∧ ∃ b1, !goalBody1Def b1 s1 u1 ∧
    ∃ st2, !pairDef st2 3 b1 ∧ ∃ s2, !(termShiftGraph LAct) s2 s1 ∧ ∃ u2, !(termShiftGraph LAct) u2 u1 ∧
    ∃ z1, !qqFvarDef z1 1 ∧ ∃ z0, !qqFvarDef z0 0 ∧ ∃ f1, !derFactDef f1 z1 ∧ ∃ f2, !fstIdxFactDef f2 s2 z1 ∧
    ∃ f3, !dlenFactDef f3 z1 z0 ∧ ∃ f4, !leFactDef f4 z0 u2 ∧ ∃ c3, !qqAndDef c3 f3 f4 ∧ ∃ c2, !qqAndDef c2 f2 c3 ∧
    ∃ q3, !pairDef q3 f3 f4 ∧ ∃ st5, !pairDef st5 4 q3 ∧ ∃ q2, !pairDef q2 f2 c3 ∧ ∃ st4, !pairDef st4 4 q2 ∧
    ∃ q1, !pairDef q1 f1 c2 ∧ ∃ st3, !pairDef st3 4 q1 ∧ ∃ v5, !adjoinDef v5 st5 0 ∧ ∃ v4, !adjoinDef v4 st4 v5 ∧
    ∃ v3, !adjoinDef v3 st3 v4 ∧ ∃ v2, !adjoinDef v2 st2 v3 ∧ !adjoinDef y st1 v2”
instance goalElim_defined : 𝚺₁-Function₂ (goalElim : V → V → V) via goalElimDef := .mk
  fun v ↦ by
    simp [goalElimDef, goalBody_defined.iff, goalBody1_defined.iff, termShift.defined.iff, derFact_defined.iff,
      fstIdxFact_defined.iff, dlenFact_defined.iff, leFact_defined.iff, goalElim, sElimExs, sSplit]
instance goalElim_definable : 𝚺₁-Function₂ (goalElim : V → V → V) := goalElim_defined.to_definable

lemma len_goalElim (s u : V) : len (goalElim s u) = 5 := by
  unfold goalElim; simp [len_adjoin]; norm_num

/-- The context the recovery list leaves. -/
noncomputable def goalElimCtx (Γ s u : V) : V :=
  insert (neg LAct (dlenFact (^&1 : V) (^&0)))
    (insert (neg LAct (leFact (^&0) (termShift LAct (termShift LAct u))))
      (insert (neg LAct (fstIdxFact (termShift LAct (termShift LAct s)) (^&1)))
        (insert (neg LAct (dlenFact (^&1) (^&0) ^⋏ leFact (^&0) (termShift LAct (termShift LAct u))))
          (insert (neg LAct (derFact (^&1)))
            (insert (neg LAct (fstIdxFact (termShift LAct (termShift LAct s)) (^&1) ^⋏
                (dlenFact (^&1) (^&0) ^⋏ leFact (^&0) (termShift LAct (termShift LAct u)))))
              (insert (neg LAct (goalInst (^&1) (^&0) (termShift LAct (termShift LAct s))
                  (termShift LAct (termShift LAct u))))
                (setShift LAct (insert (neg LAct (^∃ goalBody1 (termShift LAct s) (termShift LAct u)))
                  (setShift LAct Γ)))))))))

lemma isSemiformula_goalBody1 {s u : V} (hs : IsSemiterm LAct 0 s) (hu : IsSemiterm LAct 0 u) :
    IsSemiformula LAct ((1 : ℕ) : V) (goalBody1 s u) := by
  have hs1 : IsSemiterm LAct 1 s := isSemiterm_of_le hs zero_le
  have hu1 : IsSemiterm LAct 1 u := isSemiterm_of_le hu zero_le
  have hf : IsSemiterm LAct 1 (^&0 : V) := by simp
  have hb0 : IsSemiterm LAct 1 (bv 0 : V) := by simpa using (isSemiterm_bv (n := 1) (i := 0) (by norm_num) : IsSemiterm LAct ((1 : ℕ) : V) (bv 0))
  unfold goalBody1
  refine IsSemiformula.and.mpr ⟨?_, IsSemiformula.and.mpr ⟨?_, IsSemiformula.and.mpr ⟨?_, ?_⟩⟩⟩
  · exact isSemiformula_substRow isSemiformula_Pderiv [^&0] rfl (by simp [hf])
  · exact isSemiformula_substRow isSemiformula_PfstIdx [s, ^&0] rfl (by simp [hf, hs1])
  · exact isSemiformula_substRow isSemiformula_Pdlen [^&0, bv 0] rfl (by simp [hf, hb0])
  · exact isSemiformula_substRow isSemiformula_Ple [bv 0, u] rfl (by simp [hu1, hb0])

/-- The first elimination: `free (∃ goalBody s u) = ∃ goalBody1 (shift s) (shift u)`. -/
lemma free_exs_goalBody {s u : V} (hs : IsSemiterm LAct 0 s) (hu : IsSemiterm LAct 0 u) :
    free LAct (^∃ goalBody s u) = ^∃ goalBody1 (termShift LAct s) (termShift LAct u) := by
  have hs2 : IsSemiterm LAct 2 s := isSemiterm_of_le hs zero_le
  have hu2 : IsSemiterm LAct 2 u := isSemiterm_of_le hu zero_le
  have hb1 : IsSemiterm LAct 2 (bv 1 : V) := by simpa using (isSemiterm_bv (n := 2) (i := 1) (by norm_num) : IsSemiterm LAct ((2 : ℕ) : V) (bv 1))
  have hb0 : IsSemiterm LAct 2 (bv 0 : V) := by simpa using (isSemiterm_bv (n := 2) (i := 0) (by norm_num) : IsSemiterm LAct ((2 : ℕ) : V) (bv 0))
  have h1 : IsSemiformula LAct ((1 + 1 : ℕ) : V) (derFact (bv 1)) :=
    isSemiformula_substRow isSemiformula_Pderiv [bv 1] rfl (by simp [hb1])
  have h2 : IsSemiformula LAct ((1 + 1 : ℕ) : V) (fstIdxFact s (bv 1)) :=
    isSemiformula_substRow isSemiformula_PfstIdx [s, bv 1] rfl (by simp [hb1, hs2])
  have h3 : IsSemiformula LAct ((1 + 1 : ℕ) : V) (dlenFact (bv 1) (bv 0)) :=
    isSemiformula_substRow isSemiformula_Pdlen [bv 1, bv 0] rfl (by simp [hb1, hb0])
  have h4 : IsSemiformula LAct ((1 + 1 : ℕ) : V) (leFact (bv 0) u) :=
    isSemiformula_substRow isSemiformula_Ple [bv 0, u] rfl (by simp [hu2, hb0])
  have h34 : IsSemiformula LAct ((1 + 1 : ℕ) : V) (dlenFact (bv 1) (bv 0) ^⋏ leFact (bv 0) u) :=
    IsSemiformula.and.mpr ⟨h3, h4⟩
  have h234 : IsSemiformula LAct ((1 + 1 : ℕ) : V) (fstIdxFact s (bv 1) ^⋏ (dlenFact (bv 1) (bv 0) ^⋏ leFact (bv 0) u)) :=
    IsSemiformula.and.mpr ⟨h2, h34⟩
  have hq : IsSemiformula LAct ((1 + 1 : ℕ) : V) (goalBody s u) := IsSemiformula.and.mpr ⟨h1, h234⟩
  have h := freeIter_exsIter 1 1 hq
  rw [← freeIter_one]
  change freeIter LAct 1 (exsIter 1 (goalBody s u)) = exsIter 1 _
  rw [h]
  congr 1
  simp only [goalBody, goalBody1]
  rw [freeIterAt_and 1 1 h1 h234, freeIterAt_and 1 1 h2 h34, freeIterAt_and 1 1 h3 h4]
  unfold derFact fstIdxFact dlenFact leFact
  rw [freeIterAt_subst_listToVec 1 1 [bv 1] isSemiformula_Pderiv shift_Pderiv rfl (by simp [hb1]),
    freeIterAt_subst_listToVec 1 1 [s, bv 1] isSemiformula_PfstIdx shift_PfstIdx rfl (by simp [hb1, hs2]),
    freeIterAt_subst_listToVec 1 1 [bv 1, bv 0] isSemiformula_Pdlen shift_Pdlen rfl (by simp [hb1, hb0]),
    freeIterAt_subst_listToVec 1 1 [bv 0, u] isSemiformula_Ple shift_Ple rfl (by simp [hu2, hb0])]
  simp only [List.map_cons, List.map_nil]
  rw [freeIterT_bv_ge 1 1 1 le_rfl (by norm_num), freeIterT_bv_lt 1 1 0 (by norm_num),
    freeIterT_closed 1 hs 1, freeIterT_closed 1 hu 1]
  simp

/-- The second elimination: `free (goalBody1 s u) = goalInst &1 &0 (shift s) (shift u)`. -/
lemma free_goalBody1 {s u : V} (hs : IsSemiterm LAct 0 s) (hu : IsSemiterm LAct 0 u) :
    free LAct (goalBody1 s u) = goalInst (^&1) (^&0) (termShift LAct s) (termShift LAct u) := by
  have hs1 : IsSemiterm LAct 1 s := isSemiterm_of_le hs zero_le
  have hu1 : IsSemiterm LAct 1 u := isSemiterm_of_le hu zero_le
  have hf : IsSemiterm LAct 1 (^&0 : V) := by simp
  have hf0 : IsSemiterm LAct 0 (^&0 : V) := by simp
  have hb0 : IsSemiterm LAct 1 (bv 0 : V) := by simpa using (isSemiterm_bv (n := 1) (i := 0) (by norm_num) : IsSemiterm LAct ((1 : ℕ) : V) (bv 0))
  have h1 : IsSemiformula LAct ((1 + 0 : ℕ) : V) (derFact (^&0)) :=
    isSemiformula_substRow isSemiformula_Pderiv [^&0] rfl (by simp [hf])
  have h2 : IsSemiformula LAct ((1 + 0 : ℕ) : V) (fstIdxFact s (^&0)) :=
    isSemiformula_substRow isSemiformula_PfstIdx [s, ^&0] rfl (by simp [hf, hs1])
  have h3 : IsSemiformula LAct ((1 + 0 : ℕ) : V) (dlenFact (^&0) (bv 0)) :=
    isSemiformula_substRow isSemiformula_Pdlen [^&0, bv 0] rfl (by simp [hf, hb0])
  have h4 : IsSemiformula LAct ((1 + 0 : ℕ) : V) (leFact (bv 0) u) :=
    isSemiformula_substRow isSemiformula_Ple [bv 0, u] rfl (by simp [hu1, hb0])
  have h34 : IsSemiformula LAct ((1 + 0 : ℕ) : V) (dlenFact (^&0) (bv 0) ^⋏ leFact (bv 0) u) :=
    IsSemiformula.and.mpr ⟨h3, h4⟩
  have h234 : IsSemiformula LAct ((1 + 0 : ℕ) : V) (fstIdxFact s (^&0) ^⋏ (dlenFact (^&0) (bv 0) ^⋏ leFact (bv 0) u)) :=
    IsSemiformula.and.mpr ⟨h2, h34⟩
  rw [← freeIter_one, ← freeIterAt_zero_eq]
  unfold goalBody1 goalInst
  rw [freeIterAt_and 0 1 h1 h234, freeIterAt_and 0 1 h2 h34, freeIterAt_and 0 1 h3 h4]
  unfold derFact fstIdxFact dlenFact leFact
  rw [freeIterAt_subst_listToVec 0 1 [^&0] isSemiformula_Pderiv shift_Pderiv rfl (by simp [hf]),
    freeIterAt_subst_listToVec 0 1 [s, ^&0] isSemiformula_PfstIdx shift_PfstIdx rfl (by simp [hf, hs1]),
    freeIterAt_subst_listToVec 0 1 [^&0, bv 0] isSemiformula_Pdlen shift_Pdlen rfl (by simp [hf, hb0]),
    freeIterAt_subst_listToVec 0 1 [bv 0, u] isSemiformula_Ple shift_Ple rfl (by simp [hu1, hb0])]
  simp only [List.map_cons, List.map_nil]
  rw [freeIterT_closed 0 hf0 1, freeIterT_bv0 1 0 (by norm_num), freeIterT_closed 0 hs 1, freeIterT_closed 0 hu 1]
  simp [termShift_fvar]

/-- **`goalElim` is applicable**: given the goal fact, the five steps are OK (at any cap `M`), cut-admitting,
shift twice, and leave `d = &1`, `n = &0` with the four facts — the final context is `goalElimCtx`. -/
theorem goalElim_ok (M : ℕ) {tbl N E Γ s u : V} (htbl : TableOK tbl N) (hΓ : IsFormulaSet LAct Γ)
    (hs : IsSemiterm LAct 0 s) (hu : IsSemiterm LAct 0 u) (hg : neg LAct (goalFact s u) ∈ Γ) :
    ListOK tbl E (M : V) Γ (goalElim s u) ∧ NoDrop' (goalElim s u) ∧ shiftsV (goalElim s u) = 2 ∧
    finalCtx Γ (goalElim s u) = goalElimCtx Γ s u ∧
    neg LAct (derFact (^&1 : V)) ∈ finalCtx Γ (goalElim s u) ∧
    neg LAct (fstIdxFact (termShift LAct (termShift LAct s)) (^&1)) ∈ finalCtx Γ (goalElim s u) ∧
    neg LAct (dlenFact (^&1 : V) (^&0)) ∈ finalCtx Γ (goalElim s u) ∧
    neg LAct (leFact (^&0) (termShift LAct (termShift LAct u))) ∈ finalCtx Γ (goalElim s u) := by
  set s' := termShift LAct s with hs'
  set u' := termShift LAct u with hu'
  set s'' := termShift LAct s' with hs''
  set u'' := termShift LAct u' with hu''
  have hs'0 : IsSemiterm LAct 0 s' := hs.termShift
  have hu'0 : IsSemiterm LAct 0 u' := hu.termShift
  have hs''0 : IsSemiterm LAct 0 s'' := hs'0.termShift
  have hu''0 : IsSemiterm LAct 0 u'' := hu'0.termShift
  have hf1 : IsSemiterm LAct 0 (^&1 : V) := by simp
  have hf0 : IsSemiterm LAct 0 (^&0 : V) := by simp
  -- the formulas
  have hA₁ : IsFormula LAct (derFact (^&1 : V)) := isFormula_derFact hf1
  have hA₂ : IsFormula LAct (fstIdxFact s'' (^&1)) := isFormula_fstIdxFact hs''0 hf1
  have hA₃ : IsFormula LAct (dlenFact (^&1 : V) (^&0)) := isFormula_dlenFact hf1 hf0
  have hA₄ : IsFormula LAct (leFact (^&0) u'') := isFormula_leFact hf0 hu''0
  have hR₂ : IsFormula LAct (dlenFact (^&1 : V) (^&0) ^⋏ leFact (^&0) u'') := by simp [hA₃, hA₄]
  have hR₁ : IsFormula LAct (fstIdxFact s'' (^&1) ^⋏ (dlenFact (^&1) (^&0) ^⋏ leFact (^&0) u'')) := by simp [hA₂, hR₂]
  have hP₁ : IsSemiformula LAct 1 (^∃ goalBody s u) := by
    have := isSemiformula_exs_cast (m := 1) (p := goalBody s u) (isSemiformula_goalBody hs hu)
    simpa using this
  have hP₂ : IsSemiformula LAct 1 (goalBody1 s' u') := by simpa using isSemiformula_goalBody1 hs'0 hu'0
  have hInst : goalInst (^&1) (^&0) s'' u'' = derFact (^&1) ^⋏ (fstIdxFact s'' (^&1) ^⋏ (dlenFact (^&1) (^&0) ^⋏ leFact (^&0) u'')) := rfl
  -- step 1
  have ok₁ : StepOK tbl E (M : V) Γ (sElimExs (^∃ goalBody s u)) := by
    refine ⟨hΓ, Or.inr (Or.inr (Or.inr (Or.inl ⟨by simp, ?_, ?_⟩)))⟩
    · simp only [sElimExs, pi₂_pair]; exact hP₁
    · simp only [sElimExs, pi₂_pair]; exact hg
  have cx₁ : ctxAfter Γ (sElimExs (^∃ goalBody s u)) = insert (neg LAct (^∃ goalBody1 s' u')) (setShift LAct Γ) := by
    rw [ctxAfter_tag3 (by simp)]; simp only [sElimExs, pi₂_pair]; rw [free_exs_goalBody hs hu]
  have hΓ₁ : IsFormulaSet LAct (insert (neg LAct (^∃ goalBody1 s' u')) (setShift LAct Γ)) :=
    cx₁ ▸ isFormulaSet_ctxAfter M htbl ok₁
  -- step 2
  have ok₂ : StepOK tbl E (M : V) (insert (neg LAct (^∃ goalBody1 s' u')) (setShift LAct Γ)) (sElimExs (goalBody1 s' u')) := by
    refine ⟨hΓ₁, Or.inr (Or.inr (Or.inr (Or.inl ⟨by simp, ?_, ?_⟩)))⟩
    · simp only [sElimExs, pi₂_pair]; exact hP₂
    · simp only [sElimExs, pi₂_pair]; simp
  have cx₂ : ctxAfter (insert (neg LAct (^∃ goalBody1 s' u')) (setShift LAct Γ)) (sElimExs (goalBody1 s' u')) =
      insert (neg LAct (goalInst (^&1) (^&0) s'' u''))
        (setShift LAct (insert (neg LAct (^∃ goalBody1 s' u')) (setShift LAct Γ))) := by
    rw [ctxAfter_tag3 (by simp)]; simp only [sElimExs, pi₂_pair]; rw [free_goalBody1 hs'0 hu'0]
  set Γ₂ := insert (neg LAct (goalInst (^&1) (^&0) s'' u''))
    (setShift LAct (insert (neg LAct (^∃ goalBody1 s' u')) (setShift LAct Γ))) with hΓ₂def
  have hΓ₂ : IsFormulaSet LAct Γ₂ := cx₂ ▸ isFormulaSet_ctxAfter M htbl ok₂
  -- step 3
  have ok₃ : StepOK tbl E (M : V) Γ₂ (sSplit (derFact (^&1)) (fstIdxFact s'' (^&1) ^⋏ (dlenFact (^&1) (^&0) ^⋏ leFact (^&0) u''))) := by
    refine ⟨hΓ₂, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by simp, ?_, ?_, ?_⟩))))⟩
    · simp only [sSplit, pi₂_pair, pi₁_pair]; exact hA₁
    · simp only [sSplit, pi₂_pair, pi₁_pair]; exact hR₁
    · simp only [sSplit, pi₂_pair, pi₁_pair]; rw [hΓ₂def, ← hInst]; simp
  have cx₃ : ctxAfter Γ₂ (sSplit (derFact (^&1)) (fstIdxFact s'' (^&1) ^⋏ (dlenFact (^&1) (^&0) ^⋏ leFact (^&0) u''))) =
      insert (neg LAct (derFact (^&1))) (insert (neg LAct (fstIdxFact s'' (^&1) ^⋏ (dlenFact (^&1) (^&0) ^⋏ leFact (^&0) u''))) Γ₂) := by
    rw [ctxAfter_tag4 (by simp)]; simp only [sSplit, pi₂_pair, pi₁_pair]
  set Γ₃ := insert (neg LAct (derFact (^&1))) (insert (neg LAct (fstIdxFact s'' (^&1) ^⋏ (dlenFact (^&1) (^&0) ^⋏ leFact (^&0) u''))) Γ₂) with hΓ₃def
  have hΓ₃ : IsFormulaSet LAct Γ₃ := cx₃ ▸ isFormulaSet_ctxAfter M htbl ok₃
  -- step 4
  have ok₄ : StepOK tbl E (M : V) Γ₃ (sSplit (fstIdxFact s'' (^&1)) (dlenFact (^&1) (^&0) ^⋏ leFact (^&0) u'')) := by
    refine ⟨hΓ₃, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by simp, ?_, ?_, ?_⟩))))⟩
    · simp only [sSplit, pi₂_pair, pi₁_pair]; exact hA₂
    · simp only [sSplit, pi₂_pair, pi₁_pair]; exact hR₂
    · simp only [sSplit, pi₂_pair, pi₁_pair]; rw [hΓ₃def]; simp
  have cx₄ : ctxAfter Γ₃ (sSplit (fstIdxFact s'' (^&1)) (dlenFact (^&1) (^&0) ^⋏ leFact (^&0) u'')) =
      insert (neg LAct (fstIdxFact s'' (^&1))) (insert (neg LAct (dlenFact (^&1) (^&0) ^⋏ leFact (^&0) u'')) Γ₃) := by
    rw [ctxAfter_tag4 (by simp)]; simp only [sSplit, pi₂_pair, pi₁_pair]
  set Γ₄ := insert (neg LAct (fstIdxFact s'' (^&1))) (insert (neg LAct (dlenFact (^&1) (^&0) ^⋏ leFact (^&0) u'')) Γ₃) with hΓ₄def
  have hΓ₄ : IsFormulaSet LAct Γ₄ := cx₄ ▸ isFormulaSet_ctxAfter M htbl ok₄
  -- step 5
  have ok₅ : StepOK tbl E (M : V) Γ₄ (sSplit (dlenFact (^&1) (^&0)) (leFact (^&0) u'')) := by
    refine ⟨hΓ₄, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by simp, ?_, ?_, ?_⟩))))⟩
    · simp only [sSplit, pi₂_pair, pi₁_pair]; exact hA₃
    · simp only [sSplit, pi₂_pair, pi₁_pair]; exact hA₄
    · simp only [sSplit, pi₂_pair, pi₁_pair]; rw [hΓ₄def]; simp
  have cx₅ : ctxAfter Γ₄ (sSplit (dlenFact (^&1) (^&0)) (leFact (^&0) u'')) =
      insert (neg LAct (dlenFact (^&1) (^&0))) (insert (neg LAct (leFact (^&0) u'')) Γ₄) := by
    rw [ctxAfter_tag4 (by simp)]; simp only [sSplit, pi₂_pair, pi₁_pair]
  -- assembly
  have hfin : finalCtx Γ (goalElim s u) = goalElimCtx Γ s u := by
    unfold goalElim
    rw [finalCtx_cons, cx₁, finalCtx_cons, cx₂, finalCtx_cons, cx₃, finalCtx_cons, cx₄, finalCtx_single, cx₅]
    rfl
  refine ⟨?_, ?_, ?_, hfin, ?_, ?_, ?_, ?_⟩
  · unfold goalElim
    refine listOK_cons ok₁ ?_
    rw [cx₁]
    refine listOK_cons ok₂ ?_
    rw [cx₂]
    refine listOK_cons ok₃ ?_
    rw [cx₃]
    refine listOK_cons ok₄ ?_
    rw [cx₄]
    exact listOK_single ok₅
  · unfold goalElim
    exact noDrop'_cons (by simp) (noDrop'_cons (by simp) (noDrop'_cons (by simp) (noDrop'_cons (by simp)
      (noDrop'_single (by simp)))))
  · unfold goalElim
    rw [shiftsV_cons, shiftsV_cons, shiftsV_cons, shiftsV_cons, shiftsV_single]
    simp; norm_num
  · rw [hfin]; unfold goalElimCtx; simp [hs'', hs', hu'', hu']
  · rw [hfin]; unfold goalElimCtx; simp [hs'', hs', hu'', hu']
  · rw [hfin]; unfold goalElimCtx; simp [hs'', hs', hu'', hu']
  · rw [hfin]; unfold goalElimCtx; simp [hs'', hs', hu'', hu']

end goalElim

/-! ## 2. The `dlen` tails: `eqRefl`, the bound row, the closed `sLemma`, `leTrans`, then `sGoal` -/

section tails

/-- The sum terms the `dlen` rows produce, at the length index `l` and the children's `n` indices. -/
noncomputable def leafT (l : V) : V := (^&l : V) ^+ (𝟏 : V)
noncomputable def unaryT (l n₁ : V) : V := ((^&l : V) ^+ (^&n₁ : V)) ^+ (𝟏 : V)
noncomputable def binaryT (l n₁ n₂ : V) : V := (((^&l : V) ^+ (^&n₁ : V)) ^+ (^&n₂ : V)) ^+ (𝟏 : V)

lemma isSemiterm_leafT (l : V) : IsSemiterm LAct 0 (leafT l) :=
  isSemiterm_qqAdd_LAct (by simp) (isSemiterm_qqOne_LAct 0)
lemma isSemiterm_unaryT (l n₁ : V) : IsSemiterm LAct 0 (unaryT l n₁) :=
  isSemiterm_qqAdd_LAct (isSemiterm_qqAdd_LAct (by simp) (by simp)) (isSemiterm_qqOne_LAct 0)
lemma isSemiterm_binaryT (l n₁ n₂ : V) : IsSemiterm LAct 0 (binaryT l n₁ n₂) :=
  isSemiterm_qqAdd_LAct (isSemiterm_qqAdd_LAct (isSemiterm_qqAdd_LAct (by simp) (by simp)) (by simp))
    (isSemiterm_qqOne_LAct 0)

lemma termLen_leafT (l : V) : termLen LAct (leafT l) = l + 3 := by
  unfold leafT
  rw [termLen_qqAdd isFunc_LAct_addIndex (by simp) qqOne_uterm_LAct, termLen_fvar, termLen_qqOne isFunc_LAct_oneIndex]
  ring
lemma termLen_unaryT (l n₁ : V) : termLen LAct (unaryT l n₁) = l + n₁ + 5 := by
  unfold unaryT
  rw [termLen_qqAdd isFunc_LAct_addIndex (by simp) qqOne_uterm_LAct,
    termLen_qqAdd isFunc_LAct_addIndex (by simp) (by simp), termLen_fvar, termLen_fvar,
    termLen_qqOne isFunc_LAct_oneIndex]
  ring
lemma termLen_binaryT (l n₁ n₂ : V) : termLen LAct (binaryT l n₁ n₂) = l + n₁ + n₂ + 7 := by
  unfold binaryT
  rw [termLen_qqAdd isFunc_LAct_addIndex (by simp) qqOne_uterm_LAct,
    termLen_qqAdd isFunc_LAct_addIndex (by simp) (by simp),
    termLen_qqAdd isFunc_LAct_addIndex (by simp) (by simp), termLen_fvar, termLen_fvar, termLen_fvar,
    termLen_qqOne isFunc_LAct_oneIndex]
  ring

lemma termLen_fvar_succ_le {i E : V} (h : i + 2 ≤ E) : termLen LAct (^&(i + 1) : V) ≤ E :=
  termLen_fvar_le (by rw [add_assoc, one_add_one_eq_two]; exact h)
lemma termLen_bnum_le_bkE {x n E : V} (hx : x ≤ n) (hE : 18 * ‖n‖ + 7 ≤ E) : termLen LAct (bnum x) ≤ E :=
  le_trans (termLen_bnum_le_bk hx) (le_trans (by gcongr <;> norm_num) hE)

/-- **The leaf tail** (`dlen ν = setLen s + 1`): `eqRefl T`, `dlenLeafLe`, the closed `leafFact L n`, `leTrans`. -/
noncomputable def dlenLeafSteps (W tblN l L n : V) : V :=
  mkStep W 41 ?[leafT l] ∷ mkStep W 105 ?[leafT l, ^&l, bnum L] ∷
  sLemma (leafFact L n) (leafCode tblN L n) ∷ mkStep W 110 ?[bnum n, bnum L ^+ 𝟏, leafT l] ∷ (0 : V)

/-- **The unary tail** (`dlen ν = setLen s + n₁ + 1`). -/
noncomputable def dlenUnarySteps (W tblN l n₁ L m₁ n : V) : V :=
  mkStep W 41 ?[unaryT l n₁] ∷ mkStep W 106 ?[unaryT l n₁, ^&l, ^&n₁, bnum L, bnum m₁] ∷
  sLemma (bin2Fact L m₁ n) (bin2Code tblN L m₁ n) ∷
  mkStep W 110 ?[bnum n, (bnum L ^+ bnum m₁) ^+ 𝟏, unaryT l n₁] ∷ (0 : V)

/-- **The binary tail** (`dlen ν = setLen s + n₁ + n₂ + 1`). -/
noncomputable def dlenBinarySteps (W tblN l n₁ n₂ L m₁ m₂ n : V) : V :=
  mkStep W 41 ?[binaryT l n₁ n₂] ∷
  mkStep W 107 ?[binaryT l n₁ n₂, ^&l, ^&n₁, ^&n₂, bnum L, bnum m₁, bnum m₂] ∷
  sLemma (bin3Fact L m₁ m₂ n) (bin3Code tblN L m₁ m₂ n) ∷
  mkStep W 110 ?[bnum n, ((bnum L ^+ bnum m₁) ^+ bnum m₂) ^+ 𝟏, binaryT l n₁ n₂] ∷ (0 : V)

lemma stepOK_sLemma {tbl E M Γ A dA : V} (hΓ : IsFormulaSet LAct Γ) (h : LemmaOK (sLemma A dA)) :
    StepOK tbl E M Γ (sLemma A dA) :=
  ⟨hΓ, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by simp, h⟩))))))⟩

lemma ctxAfter_sLemma (Γ A dA : V) : ctxAfter Γ (sLemma A dA) = insert (neg LAct A) Γ := by
  rw [ctxAfter_tag7 (by simp), sLemA_sLemma]

/-- The final context of the leaf tail. -/
noncomputable def dlenLeafCtx (Γ l L n : V) : V :=
  insert (neg LAct (leFact (leafT l) (bnum n))) (insert (neg LAct (leafFact L n))
    (insert (neg LAct (leFact (leafT l) (bnum L ^+ 𝟏))) (insert (neg LAct (eqFactB (leafT l) (leafT l))) Γ)))

theorem dlenLeafSteps_ok {tbl N E Γ W tblN N' B' l L n : V} (htbl : TableOK tbl N) (hF : Frag1Table tbl)
    (hWp : W = frag1Pieces) (htblN : NumTableOK tblN N' B') (hΓ : IsFormulaSet LAct Γ)
    (hl : l + 3 ≤ E) (hn : 18 * ‖n‖ + 7 ≤ E) (hLn : L + 1 ≤ n)
    (hle : neg LAct (leFact (^&l) (bnum L)) ∈ Γ) :
    ListOK tbl E ((8 : ℕ) : V) Γ (dlenLeafSteps W tblN l L n) ∧ NoDrop' (dlenLeafSteps W tblN l L n) ∧
    shiftsV (dlenLeafSteps W tblN l L n) = 0 ∧ len (dlenLeafSteps W tblN l L n) = 4 ∧
    finalCtx Γ (dlenLeafSteps W tblN l L n) = dlenLeafCtx Γ l L n ∧
    neg LAct (leFact (leafT l) (bnum n)) ∈ finalCtx Γ (dlenLeafSteps W tblN l L n) := by
  have hLnn : L ≤ n := le_trans le_self_add hLn
  have hT : IsSemiterm LAct 0 (leafT l) := isSemiterm_leafT l
  have hTE : termLen LAct (leafT l) ≤ E := by rw [termLen_leafT]; exact hl
  have hl0 : IsSemiterm LAct 0 (^&l : V) := by simp
  have hlE : termLen LAct (^&l : V) ≤ E := termLen_fvar_le (le_trans (by gcongr; norm_num) hl)
  have hbL : IsSemiterm LAct 0 (bnum L) := isSemiterm_bnum_LAct 0 L
  have hbLE : termLen LAct (bnum L) ≤ E := termLen_bnum_le_bkE hLnn hn
  have hbn : IsSemiterm LAct 0 (bnum n) := isSemiterm_bnum_LAct 0 n
  have hbnE : termLen LAct (bnum n) ≤ E := termLen_bnum_le_bkE le_rfl hn
  have hbL1 : IsSemiterm LAct 0 (bnum L ^+ 𝟏) := isSemiterm_qqAdd_LAct hbL (isSemiterm_qqOne_LAct 0)
  have hbL1E : termLen LAct (bnum L ^+ 𝟏) ≤ E := le_trans (termLen_leafT_le hLnn) hn
  -- step 1: eqRefl
  obtain ⟨ok₁, tg₁, cx₁⟩ := flok_eqRefl htbl hF hWp hΓ hT hTE
  set Γ₁ := insert (neg LAct (eqFactB (leafT l) (leafT l))) Γ with hΓ₁def
  have hΓ₁ : IsFormulaSet LAct Γ₁ := cx₁ ▸ isFormulaSet_ctxAfter 8 htbl ok₁
  -- step 2: dlenLeafLe
  obtain ⟨ok₂, tg₂, cx₂⟩ := fok_dlenLeafLe htbl hF hWp hΓ₁ hT hTE hl0 hlE hbL hbLE
    (by rw [hΓ₁def]; simp [leafT]) (by rw [hΓ₁def]; simp [hle])
  set Γ₂ := insert (neg LAct (leFact (leafT l) (bnum L ^+ 𝟏))) Γ₁ with hΓ₂def
  have hΓ₂ : IsFormulaSet LAct Γ₂ := cx₂ ▸ isFormulaSet_ctxAfter 8 htbl ok₂
  -- step 3: the closed fact
  have ok₃ : StepOK tbl E ((8 : ℕ) : V) Γ₂ (sLemma (leafFact L n) (leafCode tblN L n)) :=
    stepOK_sLemma hΓ₂ (lemmaOK_leaf htblN hLn)
  have cx₃ := ctxAfter_sLemma Γ₂ (leafFact L n) (leafCode tblN L n)
  set Γ₃ := insert (neg LAct (leafFact L n)) Γ₂ with hΓ₃def
  have hΓ₃ : IsFormulaSet LAct Γ₃ := cx₃ ▸ isFormulaSet_ctxAfter 8 htbl ok₃
  -- step 4: leTrans
  obtain ⟨ok₄, tg₄, cx₄⟩ := fok_leTrans htbl hF hWp hΓ₃ hbn hbnE hbL1 hbL1E hT hTE
    (by rw [hΓ₃def, hΓ₂def]; simp) (by rw [hΓ₃def]; simp [leafFact])
  have hfin : finalCtx Γ (dlenLeafSteps W tblN l L n) = dlenLeafCtx Γ l L n := by
    unfold dlenLeafSteps
    rw [finalCtx_cons, cx₁, finalCtx_cons, cx₂, finalCtx_cons, cx₃, finalCtx_single, cx₄]
    rfl
  refine ⟨?_, ?_, ?_, ?_, hfin, ?_⟩
  · unfold dlenLeafSteps
    refine listOK_cons ok₁ ?_
    rw [cx₁]
    refine listOK_cons ok₂ ?_
    rw [cx₂]
    refine listOK_cons ok₃ ?_
    rw [cx₃]
    exact listOK_single ok₄
  · unfold dlenLeafSteps
    exact noDrop'_cons (by rw [tg₁]; simp) (noDrop'_cons (by rw [tg₂]; simp)
      (noDrop'_cons (by simp) (noDrop'_single (by rw [tg₄]; simp))))
  · unfold dlenLeafSteps
    rw [shiftsV_cons, shiftsV_cons, shiftsV_cons, shiftsV_single, tg₁, tg₂, tg₄]
    simp
  · unfold dlenLeafSteps; simp [len_adjoin]; norm_num
  · rw [hfin]; unfold dlenLeafCtx; simp

/-- The final context of the unary tail. -/
noncomputable def dlenUnaryCtx (Γ l n₁ L m₁ n : V) : V :=
  insert (neg LAct (leFact (unaryT l n₁) (bnum n))) (insert (neg LAct (bin2Fact L m₁ n))
    (insert (neg LAct (leFact (unaryT l n₁) ((bnum L ^+ bnum m₁) ^+ 𝟏)))
      (insert (neg LAct (eqFactB (unaryT l n₁) (unaryT l n₁))) Γ)))

theorem dlenUnarySteps_ok {tbl N E Γ W tblN N' B' l n₁ L m₁ n : V} (htbl : TableOK tbl N) (hF : Frag1Table tbl)
    (hWp : W = frag1Pieces) (htblN : NumTableOK tblN N' B') (hΓ : IsFormulaSet LAct Γ)
    (hl : l + n₁ + 5 ≤ E) (hn : 18 * ‖n‖ + 7 ≤ E) (hLn : L + m₁ + 1 ≤ n)
    (hle : neg LAct (leFact (^&l) (bnum L)) ∈ Γ) (hle₁ : neg LAct (leFact (^&n₁) (bnum m₁)) ∈ Γ) :
    ListOK tbl E ((8 : ℕ) : V) Γ (dlenUnarySteps W tblN l n₁ L m₁ n) ∧ NoDrop' (dlenUnarySteps W tblN l n₁ L m₁ n) ∧
    shiftsV (dlenUnarySteps W tblN l n₁ L m₁ n) = 0 ∧ len (dlenUnarySteps W tblN l n₁ L m₁ n) = 4 ∧
    finalCtx Γ (dlenUnarySteps W tblN l n₁ L m₁ n) = dlenUnaryCtx Γ l n₁ L m₁ n ∧
    neg LAct (leFact (unaryT l n₁) (bnum n)) ∈ finalCtx Γ (dlenUnarySteps W tblN l n₁ L m₁ n) := by
  have hLn' : L + m₁ ≤ n := le_trans le_self_add hLn
  have hLnn : L ≤ n := le_trans le_self_add hLn'
  have hmn : m₁ ≤ n := le_trans le_add_self hLn'
  have hT : IsSemiterm LAct 0 (unaryT l n₁) := isSemiterm_unaryT l n₁
  have hTE : termLen LAct (unaryT l n₁) ≤ E := by rw [termLen_unaryT]; exact hl
  have hl0 : IsSemiterm LAct 0 (^&l : V) := by simp
  have hlE : termLen LAct (^&l : V) ≤ E := by
    refine termLen_fvar_le (le_trans ?_ hl)
    calc l + 1 ≤ (l + n₁) + 1 := by gcongr; exact le_self_add
      _ ≤ l + n₁ + 5 := by gcongr; norm_num
  have hn0 : IsSemiterm LAct 0 (^&n₁ : V) := by simp
  have hnE : termLen LAct (^&n₁ : V) ≤ E := by
    refine termLen_fvar_le (le_trans ?_ hl)
    calc n₁ + 1 ≤ (l + n₁) + 1 := by gcongr; exact le_add_self
      _ ≤ l + n₁ + 5 := by gcongr; norm_num
  have hbL : IsSemiterm LAct 0 (bnum L) := isSemiterm_bnum_LAct 0 L
  have hbLE : termLen LAct (bnum L) ≤ E := termLen_bnum_le_bkE hLnn hn
  have hbm : IsSemiterm LAct 0 (bnum m₁) := isSemiterm_bnum_LAct 0 m₁
  have hbmE : termLen LAct (bnum m₁) ≤ E := termLen_bnum_le_bkE hmn hn
  have hbn : IsSemiterm LAct 0 (bnum n) := isSemiterm_bnum_LAct 0 n
  have hbnE : termLen LAct (bnum n) ≤ E := termLen_bnum_le_bkE le_rfl hn
  have hS : IsSemiterm LAct 0 ((bnum L ^+ bnum m₁) ^+ 𝟏) :=
    isSemiterm_qqAdd_LAct (isSemiterm_qqAdd_LAct hbL hbm) (isSemiterm_qqOne_LAct 0)
  have hSE : termLen LAct ((bnum L ^+ bnum m₁) ^+ 𝟏) ≤ E := le_trans (termLen_bin2T_le hLnn hmn) hn
  obtain ⟨ok₁, tg₁, cx₁⟩ := flok_eqRefl htbl hF hWp hΓ hT hTE
  set Γ₁ := insert (neg LAct (eqFactB (unaryT l n₁) (unaryT l n₁))) Γ with hΓ₁def
  have hΓ₁ : IsFormulaSet LAct Γ₁ := cx₁ ▸ isFormulaSet_ctxAfter 8 htbl ok₁
  obtain ⟨ok₂, tg₂, cx₂⟩ := fok_dlenUnaryLe htbl hF hWp hΓ₁ hT hTE hl0 hlE hn0 hnE hbL hbLE hbm hbmE
    (by rw [hΓ₁def]; simp [unaryT]) (by rw [hΓ₁def]; simp [hle]) (by rw [hΓ₁def]; simp [hle₁])
  set Γ₂ := insert (neg LAct (leFact (unaryT l n₁) ((bnum L ^+ bnum m₁) ^+ 𝟏))) Γ₁ with hΓ₂def
  have hΓ₂ : IsFormulaSet LAct Γ₂ := cx₂ ▸ isFormulaSet_ctxAfter 8 htbl ok₂
  have ok₃ : StepOK tbl E ((8 : ℕ) : V) Γ₂ (sLemma (bin2Fact L m₁ n) (bin2Code tblN L m₁ n)) :=
    stepOK_sLemma hΓ₂ (lemmaOK_bin2 htblN hLn)
  have cx₃ := ctxAfter_sLemma Γ₂ (bin2Fact L m₁ n) (bin2Code tblN L m₁ n)
  set Γ₃ := insert (neg LAct (bin2Fact L m₁ n)) Γ₂ with hΓ₃def
  have hΓ₃ : IsFormulaSet LAct Γ₃ := cx₃ ▸ isFormulaSet_ctxAfter 8 htbl ok₃
  obtain ⟨ok₄, tg₄, cx₄⟩ := fok_leTrans htbl hF hWp hΓ₃ hbn hbnE hS hSE hT hTE
    (by rw [hΓ₃def, hΓ₂def]; simp) (by rw [hΓ₃def]; simp [bin2Fact])
  have hfin : finalCtx Γ (dlenUnarySteps W tblN l n₁ L m₁ n) = dlenUnaryCtx Γ l n₁ L m₁ n := by
    unfold dlenUnarySteps
    rw [finalCtx_cons, cx₁, finalCtx_cons, cx₂, finalCtx_cons, cx₃, finalCtx_single, cx₄]
    rfl
  refine ⟨?_, ?_, ?_, ?_, hfin, ?_⟩
  · unfold dlenUnarySteps
    refine listOK_cons ok₁ ?_
    rw [cx₁]
    refine listOK_cons ok₂ ?_
    rw [cx₂]
    refine listOK_cons ok₃ ?_
    rw [cx₃]
    exact listOK_single ok₄
  · unfold dlenUnarySteps
    exact noDrop'_cons (by rw [tg₁]; simp) (noDrop'_cons (by rw [tg₂]; simp)
      (noDrop'_cons (by simp) (noDrop'_single (by rw [tg₄]; simp))))
  · unfold dlenUnarySteps
    rw [shiftsV_cons, shiftsV_cons, shiftsV_cons, shiftsV_single, tg₁, tg₂, tg₄]
    simp
  · unfold dlenUnarySteps; simp [len_adjoin]; norm_num
  · rw [hfin]; unfold dlenUnaryCtx; simp

/-- The final context of the binary tail. -/
noncomputable def dlenBinaryCtx (Γ l n₁ n₂ L m₁ m₂ n : V) : V :=
  insert (neg LAct (leFact (binaryT l n₁ n₂) (bnum n))) (insert (neg LAct (bin3Fact L m₁ m₂ n))
    (insert (neg LAct (leFact (binaryT l n₁ n₂) (((bnum L ^+ bnum m₁) ^+ bnum m₂) ^+ 𝟏)))
      (insert (neg LAct (eqFactB (binaryT l n₁ n₂) (binaryT l n₁ n₂))) Γ)))

theorem dlenBinarySteps_ok {tbl N E Γ W tblN N' B' l n₁ n₂ L m₁ m₂ n : V} (htbl : TableOK tbl N) (hF : Frag1Table tbl)
    (hWp : W = frag1Pieces) (htblN : NumTableOK tblN N' B') (hΓ : IsFormulaSet LAct Γ)
    (hl : l + n₁ + n₂ + 7 ≤ E) (hn : 18 * ‖n‖ + 7 ≤ E) (hLn : L + m₁ + m₂ + 1 ≤ n)
    (hle : neg LAct (leFact (^&l) (bnum L)) ∈ Γ) (hle₁ : neg LAct (leFact (^&n₁) (bnum m₁)) ∈ Γ)
    (hle₂ : neg LAct (leFact (^&n₂) (bnum m₂)) ∈ Γ) :
    ListOK tbl E ((8 : ℕ) : V) Γ (dlenBinarySteps W tblN l n₁ n₂ L m₁ m₂ n) ∧
    NoDrop' (dlenBinarySteps W tblN l n₁ n₂ L m₁ m₂ n) ∧
    shiftsV (dlenBinarySteps W tblN l n₁ n₂ L m₁ m₂ n) = 0 ∧ len (dlenBinarySteps W tblN l n₁ n₂ L m₁ m₂ n) = 4 ∧
    finalCtx Γ (dlenBinarySteps W tblN l n₁ n₂ L m₁ m₂ n) = dlenBinaryCtx Γ l n₁ n₂ L m₁ m₂ n ∧
    neg LAct (leFact (binaryT l n₁ n₂) (bnum n)) ∈ finalCtx Γ (dlenBinarySteps W tblN l n₁ n₂ L m₁ m₂ n) := by
  have hLn' : L + m₁ + m₂ ≤ n := le_trans le_self_add hLn
  have hLm : L + m₁ ≤ n := le_trans le_self_add hLn'
  have hLnn : L ≤ n := le_trans le_self_add hLm
  have hm₁ : m₁ ≤ n := le_trans le_add_self hLm
  have hm₂ : m₂ ≤ n := le_trans le_add_self hLn'
  have hT : IsSemiterm LAct 0 (binaryT l n₁ n₂) := isSemiterm_binaryT l n₁ n₂
  have hTE : termLen LAct (binaryT l n₁ n₂) ≤ E := by rw [termLen_binaryT]; exact hl
  have hl0 : IsSemiterm LAct 0 (^&l : V) := by simp
  have hlE : termLen LAct (^&l : V) ≤ E := by
    refine termLen_fvar_le (le_trans ?_ hl)
    calc l + 1 ≤ (l + n₁ + n₂) + 1 := by gcongr; exact le_trans le_self_add le_self_add
      _ ≤ l + n₁ + n₂ + 7 := by gcongr; norm_num
  have hn0 : IsSemiterm LAct 0 (^&n₁ : V) := by simp
  have hnE : termLen LAct (^&n₁ : V) ≤ E := by
    refine termLen_fvar_le (le_trans ?_ hl)
    calc n₁ + 1 ≤ (l + n₁ + n₂) + 1 := by gcongr; exact le_trans le_add_self le_self_add
      _ ≤ l + n₁ + n₂ + 7 := by gcongr; norm_num
  have hn0' : IsSemiterm LAct 0 (^&n₂ : V) := by simp
  have hnE' : termLen LAct (^&n₂ : V) ≤ E := by
    refine termLen_fvar_le (le_trans ?_ hl)
    calc n₂ + 1 ≤ (l + n₁ + n₂) + 1 := by gcongr; exact le_add_self
      _ ≤ l + n₁ + n₂ + 7 := by gcongr; norm_num
  have hbL : IsSemiterm LAct 0 (bnum L) := isSemiterm_bnum_LAct 0 L
  have hbLE : termLen LAct (bnum L) ≤ E := termLen_bnum_le_bkE hLnn hn
  have hbm : IsSemiterm LAct 0 (bnum m₁) := isSemiterm_bnum_LAct 0 m₁
  have hbmE : termLen LAct (bnum m₁) ≤ E := termLen_bnum_le_bkE hm₁ hn
  have hbm' : IsSemiterm LAct 0 (bnum m₂) := isSemiterm_bnum_LAct 0 m₂
  have hbmE' : termLen LAct (bnum m₂) ≤ E := termLen_bnum_le_bkE hm₂ hn
  have hbn : IsSemiterm LAct 0 (bnum n) := isSemiterm_bnum_LAct 0 n
  have hbnE : termLen LAct (bnum n) ≤ E := termLen_bnum_le_bkE le_rfl hn
  have hS : IsSemiterm LAct 0 (((bnum L ^+ bnum m₁) ^+ bnum m₂) ^+ 𝟏) :=
    isSemiterm_qqAdd_LAct (isSemiterm_qqAdd_LAct (isSemiterm_qqAdd_LAct hbL hbm) hbm') (isSemiterm_qqOne_LAct 0)
  have hSE : termLen LAct (((bnum L ^+ bnum m₁) ^+ bnum m₂) ^+ 𝟏) ≤ E := le_trans (termLen_bin3T_le hLnn hm₁ hm₂) hn
  obtain ⟨ok₁, tg₁, cx₁⟩ := flok_eqRefl htbl hF hWp hΓ hT hTE
  set Γ₁ := insert (neg LAct (eqFactB (binaryT l n₁ n₂) (binaryT l n₁ n₂))) Γ with hΓ₁def
  have hΓ₁ : IsFormulaSet LAct Γ₁ := cx₁ ▸ isFormulaSet_ctxAfter 8 htbl ok₁
  obtain ⟨ok₂, tg₂, cx₂⟩ := fok_dlenBinaryLe htbl hF hWp hΓ₁ hT hTE hl0 hlE hn0 hnE hn0' hnE' hbL hbLE hbm hbmE hbm' hbmE'
    (by rw [hΓ₁def]; simp [binaryT]) (by rw [hΓ₁def]; simp [hle]) (by rw [hΓ₁def]; simp [hle₁])
    (by rw [hΓ₁def]; simp [hle₂])
  set Γ₂ := insert (neg LAct (leFact (binaryT l n₁ n₂) (((bnum L ^+ bnum m₁) ^+ bnum m₂) ^+ 𝟏))) Γ₁ with hΓ₂def
  have hΓ₂ : IsFormulaSet LAct Γ₂ := cx₂ ▸ isFormulaSet_ctxAfter 8 htbl ok₂
  have ok₃ : StepOK tbl E ((8 : ℕ) : V) Γ₂ (sLemma (bin3Fact L m₁ m₂ n) (bin3Code tblN L m₁ m₂ n)) :=
    stepOK_sLemma hΓ₂ (lemmaOK_bin3 htblN hLn)
  have cx₃ := ctxAfter_sLemma Γ₂ (bin3Fact L m₁ m₂ n) (bin3Code tblN L m₁ m₂ n)
  set Γ₃ := insert (neg LAct (bin3Fact L m₁ m₂ n)) Γ₂ with hΓ₃def
  have hΓ₃ : IsFormulaSet LAct Γ₃ := cx₃ ▸ isFormulaSet_ctxAfter 8 htbl ok₃
  obtain ⟨ok₄, tg₄, cx₄⟩ := fok_leTrans htbl hF hWp hΓ₃ hbn hbnE hS hSE hT hTE
    (by rw [hΓ₃def, hΓ₂def]; simp) (by rw [hΓ₃def]; simp [bin3Fact])
  have hfin : finalCtx Γ (dlenBinarySteps W tblN l n₁ n₂ L m₁ m₂ n) = dlenBinaryCtx Γ l n₁ n₂ L m₁ m₂ n := by
    unfold dlenBinarySteps
    rw [finalCtx_cons, cx₁, finalCtx_cons, cx₂, finalCtx_cons, cx₃, finalCtx_single, cx₄]
    rfl
  refine ⟨?_, ?_, ?_, ?_, hfin, ?_⟩
  · unfold dlenBinarySteps
    refine listOK_cons ok₁ ?_
    rw [cx₁]
    refine listOK_cons ok₂ ?_
    rw [cx₂]
    refine listOK_cons ok₃ ?_
    rw [cx₃]
    exact listOK_single ok₄
  · unfold dlenBinarySteps
    exact noDrop'_cons (by rw [tg₁]; simp) (noDrop'_cons (by rw [tg₂]; simp)
      (noDrop'_cons (by simp) (noDrop'_single (by rw [tg₄]; simp))))
  · unfold dlenBinarySteps
    rw [shiftsV_cons, shiftsV_cons, shiftsV_cons, shiftsV_single, tg₁, tg₂, tg₄]
    simp
  · unfold dlenBinarySteps; simp [len_adjoin]; norm_num
  · rw [hfin]; unfold dlenBinaryCtx; simp

/-- **The goal-closing step is applicable** once the four facts are in context. -/
lemma stepOK_sGoal {tbl E M Γ e n s u : V} (hΓ : IsFormulaSet LAct Γ)
    (he : IsSemiterm LAct 0 e) (hel : termLen LAct e ≤ E) (hn : IsSemiterm LAct 0 n) (hnl : termLen LAct n ≤ E)
    (hs : IsSemiterm LAct 0 s) (hsl : termLen LAct s ≤ E) (hu : IsSemiterm LAct 0 u) (hul : termLen LAct u ≤ E)
    (h₁ : neg LAct (derFact e) ∈ Γ) (h₂ : neg LAct (fstIdxFact s e) ∈ Γ) (h₃ : neg LAct (dlenFact e n) ∈ Γ)
    (h₄ : neg LAct (leFact n u) ∈ Γ) : StepOK tbl E M Γ (sGoal e n s u) := by
  refine ⟨hΓ, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by simp, ?_⟩))))))⟩
  unfold GoalOK
  simp only [sGoalE_sGoal, sGoalN_sGoal, sGoalS_sGoal, sGoalU_sGoal]
  exact ⟨he, hel, hn, hnl, hs, hsl, hu, hul, h₁, h₂, h₃, h₄⟩

lemma ctxAfter_sGoal (Γ e n s u : V) : ctxAfter Γ (sGoal e n s u) = insert (neg LAct (goalFact s u)) Γ := by
  rw [ctxAfter_tag6 (by simp), sGoalS_sGoal, sGoalU_sGoal]

/-- **The leaf tail with its goal step**: `dlenLeafSteps` then `sGoal &0 (leafT l) &s (bnum n)`. -/
noncomputable def goalTailLeaf (W tblN l L n s : V) : V :=
  appendV (dlenLeafSteps W tblN l L n) ?[sGoal (^&0) (leafT l) (^&s) (bnum n)]
noncomputable def goalTailUnary (W tblN l n₁ L m₁ n s : V) : V :=
  appendV (dlenUnarySteps W tblN l n₁ L m₁ n) ?[sGoal (^&0) (unaryT l n₁) (^&s) (bnum n)]
noncomputable def goalTailBinary (W tblN l n₁ n₂ L m₁ m₂ n s : V) : V :=
  appendV (dlenBinarySteps W tblN l n₁ n₂ L m₁ m₂ n) ?[sGoal (^&0) (binaryT l n₁ n₂) (^&s) (bnum n)]

theorem goalTailLeaf_ok {tbl N E Γ W tblN N' B' l L n s : V} (htbl : TableOK tbl N) (hF : Frag1Table tbl)
    (hWp : W = frag1Pieces) (htblN : NumTableOK tblN N' B') (hΓ : IsFormulaSet LAct Γ)
    (hl : l + 3 ≤ E) (hsE : s + 1 ≤ E) (hn : 18 * ‖n‖ + 7 ≤ E) (hLn : L + 1 ≤ n)
    (hle : neg LAct (leFact (^&l) (bnum L)) ∈ Γ) (hder : neg LAct (derFact (^&0 : V)) ∈ Γ)
    (hfst : neg LAct (fstIdxFact (^&s) (^&0)) ∈ Γ) (hdl : neg LAct (dlenFact (^&0 : V) (leafT l)) ∈ Γ) :
    ListOK tbl E ((8 : ℕ) : V) Γ (goalTailLeaf W tblN l L n s) ∧ NoDrop' (goalTailLeaf W tblN l L n s) ∧
    shiftsV (goalTailLeaf W tblN l L n s) = 0 ∧ len (goalTailLeaf W tblN l L n s) = 5 ∧
    finalCtx Γ (goalTailLeaf W tblN l L n s) = insert (neg LAct (goalFact (^&s) (bnum n))) (dlenLeafCtx Γ l L n) ∧
    neg LAct (goalFact (^&s) (bnum n)) ∈ finalCtx Γ (goalTailLeaf W tblN l L n s) := by
  obtain ⟨hok, hnd, hsv, hlen, hfin, hmem⟩ := dlenLeafSteps_ok htbl hF hWp htblN hΓ hl hn hLn hle
  have hΓ' : IsFormulaSet LAct (finalCtx Γ (dlenLeafSteps W tblN l L n)) := finalCtx_isFormulaSet 8 htbl hΓ hok
  have hf0 : IsSemiterm LAct 0 (^&0 : V) := by simp
  have hf0E : termLen LAct (^&0 : V) ≤ E := termLen_fvar_le (le_trans (by norm_num) hsE)
  have hT : IsSemiterm LAct 0 (leafT l) := isSemiterm_leafT l
  have hTE : termLen LAct (leafT l) ≤ E := by rw [termLen_leafT]; exact hl
  have hs0 : IsSemiterm LAct 0 (^&s : V) := by simp
  have hsE' : termLen LAct (^&s : V) ≤ E := termLen_fvar_le hsE
  have hbn : IsSemiterm LAct 0 (bnum n) := isSemiterm_bnum_LAct 0 n
  have hbnE : termLen LAct (bnum n) ≤ E := termLen_bnum_le_bkE le_rfl hn
  have okG : StepOK tbl E ((8 : ℕ) : V) (finalCtx Γ (dlenLeafSteps W tblN l L n)) (sGoal (^&0) (leafT l) (^&s) (bnum n)) :=
    stepOK_sGoal hΓ' hf0 hf0E hT hTE hs0 hsE' hbn hbnE (by rw [hfin]; unfold dlenLeafCtx; simp [hder])
      (by rw [hfin]; unfold dlenLeafCtx; simp [hfst]) (by rw [hfin]; unfold dlenLeafCtx; simp [hdl]) hmem
  have hfin' : finalCtx Γ (goalTailLeaf W tblN l L n s) =
      insert (neg LAct (goalFact (^&s) (bnum n))) (dlenLeafCtx Γ l L n) := by
    unfold goalTailLeaf
    rw [finalCtx_appendV, finalCtx_single, ctxAfter_sGoal, hfin]
  refine ⟨listOK_appendV hok (listOK_single okG), noDrop'_appendV hnd (noDrop'_single (by simp)), ?_, ?_, hfin', ?_⟩
  · unfold goalTailLeaf; rw [shiftsV_appendV, hsv, shiftsV_single]; simp
  · unfold goalTailLeaf; rw [len_appendV, hlen, len_adjoin, len_nil]; norm_num
  · rw [hfin']; simp

theorem goalTailUnary_ok {tbl N E Γ W tblN N' B' l n₁ L m₁ n s : V} (htbl : TableOK tbl N) (hF : Frag1Table tbl)
    (hWp : W = frag1Pieces) (htblN : NumTableOK tblN N' B') (hΓ : IsFormulaSet LAct Γ)
    (hl : l + n₁ + 5 ≤ E) (hsE : s + 1 ≤ E) (hn : 18 * ‖n‖ + 7 ≤ E) (hLn : L + m₁ + 1 ≤ n)
    (hle : neg LAct (leFact (^&l) (bnum L)) ∈ Γ) (hle₁ : neg LAct (leFact (^&n₁) (bnum m₁)) ∈ Γ)
    (hder : neg LAct (derFact (^&0 : V)) ∈ Γ) (hfst : neg LAct (fstIdxFact (^&s) (^&0)) ∈ Γ)
    (hdl : neg LAct (dlenFact (^&0 : V) (unaryT l n₁)) ∈ Γ) :
    ListOK tbl E ((8 : ℕ) : V) Γ (goalTailUnary W tblN l n₁ L m₁ n s) ∧ NoDrop' (goalTailUnary W tblN l n₁ L m₁ n s) ∧
    shiftsV (goalTailUnary W tblN l n₁ L m₁ n s) = 0 ∧ len (goalTailUnary W tblN l n₁ L m₁ n s) = 5 ∧
    finalCtx Γ (goalTailUnary W tblN l n₁ L m₁ n s) =
      insert (neg LAct (goalFact (^&s) (bnum n))) (dlenUnaryCtx Γ l n₁ L m₁ n) ∧
    neg LAct (goalFact (^&s) (bnum n)) ∈ finalCtx Γ (goalTailUnary W tblN l n₁ L m₁ n s) := by
  obtain ⟨hok, hnd, hsv, hlen, hfin, hmem⟩ := dlenUnarySteps_ok htbl hF hWp htblN hΓ hl hn hLn hle hle₁
  have hΓ' : IsFormulaSet LAct (finalCtx Γ (dlenUnarySteps W tblN l n₁ L m₁ n)) := finalCtx_isFormulaSet 8 htbl hΓ hok
  have hf0 : IsSemiterm LAct 0 (^&0 : V) := by simp
  have hf0E : termLen LAct (^&0 : V) ≤ E := termLen_fvar_le (le_trans (by norm_num) hsE)
  have hT : IsSemiterm LAct 0 (unaryT l n₁) := isSemiterm_unaryT l n₁
  have hTE : termLen LAct (unaryT l n₁) ≤ E := by rw [termLen_unaryT]; exact hl
  have hs0 : IsSemiterm LAct 0 (^&s : V) := by simp
  have hsE' : termLen LAct (^&s : V) ≤ E := termLen_fvar_le hsE
  have hbn : IsSemiterm LAct 0 (bnum n) := isSemiterm_bnum_LAct 0 n
  have hbnE : termLen LAct (bnum n) ≤ E := termLen_bnum_le_bkE le_rfl hn
  have okG : StepOK tbl E ((8 : ℕ) : V) (finalCtx Γ (dlenUnarySteps W tblN l n₁ L m₁ n))
      (sGoal (^&0) (unaryT l n₁) (^&s) (bnum n)) :=
    stepOK_sGoal hΓ' hf0 hf0E hT hTE hs0 hsE' hbn hbnE (by rw [hfin]; unfold dlenUnaryCtx; simp [hder])
      (by rw [hfin]; unfold dlenUnaryCtx; simp [hfst]) (by rw [hfin]; unfold dlenUnaryCtx; simp [hdl]) hmem
  have hfin' : finalCtx Γ (goalTailUnary W tblN l n₁ L m₁ n s) =
      insert (neg LAct (goalFact (^&s) (bnum n))) (dlenUnaryCtx Γ l n₁ L m₁ n) := by
    unfold goalTailUnary
    rw [finalCtx_appendV, finalCtx_single, ctxAfter_sGoal, hfin]
  refine ⟨listOK_appendV hok (listOK_single okG), noDrop'_appendV hnd (noDrop'_single (by simp)), ?_, ?_, hfin', ?_⟩
  · unfold goalTailUnary; rw [shiftsV_appendV, hsv, shiftsV_single]; simp
  · unfold goalTailUnary; rw [len_appendV, hlen, len_adjoin, len_nil]; norm_num
  · rw [hfin']; simp

theorem goalTailBinary_ok {tbl N E Γ W tblN N' B' l n₁ n₂ L m₁ m₂ n s : V} (htbl : TableOK tbl N) (hF : Frag1Table tbl)
    (hWp : W = frag1Pieces) (htblN : NumTableOK tblN N' B') (hΓ : IsFormulaSet LAct Γ)
    (hl : l + n₁ + n₂ + 7 ≤ E) (hsE : s + 1 ≤ E) (hn : 18 * ‖n‖ + 7 ≤ E) (hLn : L + m₁ + m₂ + 1 ≤ n)
    (hle : neg LAct (leFact (^&l) (bnum L)) ∈ Γ) (hle₁ : neg LAct (leFact (^&n₁) (bnum m₁)) ∈ Γ)
    (hle₂ : neg LAct (leFact (^&n₂) (bnum m₂)) ∈ Γ)
    (hder : neg LAct (derFact (^&0 : V)) ∈ Γ) (hfst : neg LAct (fstIdxFact (^&s) (^&0)) ∈ Γ)
    (hdl : neg LAct (dlenFact (^&0 : V) (binaryT l n₁ n₂)) ∈ Γ) :
    ListOK tbl E ((8 : ℕ) : V) Γ (goalTailBinary W tblN l n₁ n₂ L m₁ m₂ n s) ∧
    NoDrop' (goalTailBinary W tblN l n₁ n₂ L m₁ m₂ n s) ∧
    shiftsV (goalTailBinary W tblN l n₁ n₂ L m₁ m₂ n s) = 0 ∧ len (goalTailBinary W tblN l n₁ n₂ L m₁ m₂ n s) = 5 ∧
    finalCtx Γ (goalTailBinary W tblN l n₁ n₂ L m₁ m₂ n s) =
      insert (neg LAct (goalFact (^&s) (bnum n))) (dlenBinaryCtx Γ l n₁ n₂ L m₁ m₂ n) ∧
    neg LAct (goalFact (^&s) (bnum n)) ∈ finalCtx Γ (goalTailBinary W tblN l n₁ n₂ L m₁ m₂ n s) := by
  obtain ⟨hok, hnd, hsv, hlen, hfin, hmem⟩ := dlenBinarySteps_ok htbl hF hWp htblN hΓ hl hn hLn hle hle₁ hle₂
  have hΓ' : IsFormulaSet LAct (finalCtx Γ (dlenBinarySteps W tblN l n₁ n₂ L m₁ m₂ n)) :=
    finalCtx_isFormulaSet 8 htbl hΓ hok
  have hf0 : IsSemiterm LAct 0 (^&0 : V) := by simp
  have hf0E : termLen LAct (^&0 : V) ≤ E := termLen_fvar_le (le_trans (by norm_num) hsE)
  have hT : IsSemiterm LAct 0 (binaryT l n₁ n₂) := isSemiterm_binaryT l n₁ n₂
  have hTE : termLen LAct (binaryT l n₁ n₂) ≤ E := by rw [termLen_binaryT]; exact hl
  have hs0 : IsSemiterm LAct 0 (^&s : V) := by simp
  have hsE' : termLen LAct (^&s : V) ≤ E := termLen_fvar_le hsE
  have hbn : IsSemiterm LAct 0 (bnum n) := isSemiterm_bnum_LAct 0 n
  have hbnE : termLen LAct (bnum n) ≤ E := termLen_bnum_le_bkE le_rfl hn
  have okG : StepOK tbl E ((8 : ℕ) : V) (finalCtx Γ (dlenBinarySteps W tblN l n₁ n₂ L m₁ m₂ n))
      (sGoal (^&0) (binaryT l n₁ n₂) (^&s) (bnum n)) :=
    stepOK_sGoal hΓ' hf0 hf0E hT hTE hs0 hsE' hbn hbnE (by rw [hfin]; unfold dlenBinaryCtx; simp [hder])
      (by rw [hfin]; unfold dlenBinaryCtx; simp [hfst]) (by rw [hfin]; unfold dlenBinaryCtx; simp [hdl]) hmem
  have hfin' : finalCtx Γ (goalTailBinary W tblN l n₁ n₂ L m₁ m₂ n s) =
      insert (neg LAct (goalFact (^&s) (bnum n))) (dlenBinaryCtx Γ l n₁ n₂ L m₁ m₂ n) := by
    unfold goalTailBinary
    rw [finalCtx_appendV, finalCtx_single, ctxAfter_sGoal, hfin]
  refine ⟨listOK_appendV hok (listOK_single okG), noDrop'_appendV hnd (noDrop'_single (by simp)), ?_, ?_, hfin', ?_⟩
  · unfold goalTailBinary; rw [shiftsV_appendV, hsv, shiftsV_single]; simp
  · unfold goalTailBinary; rw [len_appendV, hlen, len_adjoin, len_nil]; norm_num
  · rw [hfin']; simp

end tails

/-! ## 3. The leaf fragments `fragAxL`, `fragVerum` (DESIGN_fragments §4.1–4.2)

Layout assumed (indices of the objects in `Γ`, all as `^&i`): the sequent `s` at `is`, its length object at
`il` with `setLenFact &il &is` and the numeral bound `leFact &il (bnum L)`, `fsetPiFact &is`, and the members
with their membership facts — for `axL` the member `p` at `ip`, `neg p` at `inp`, `negFact &inp &ip` (the
identification of the two members as negations of each other is ASSUMED: it comes from `eqSteps` on the walk
dossiers when the members were described separately), for `verumIntro` the member `⊤` at `iv` with
`verumFact &iv`. `L` and `n` are the values `setLen s` and `dlen ν` (the closed `sLemma` needs `L + 1 ≤ n`). -/

section leaves

/-- A layout fact of `Γ` reappears in the head's context (the one shift, then inserts). -/
lemma shift_mem_head3 {Γ x a b c f : V} (hx : x ∈ Γ) :
    shift LAct x ∈ insert a (insert b (insert c (insert f (setShift LAct Γ)))) := by
  have := mem_shift_insert (f := f) hx
  simp [this]

/-- The four node steps of `axL`: `tot_axL`, `fstIdx_axL`, `Intro_axL`, `Dlen_axL`. -/
noncomputable def fragAxLHead (W is il ip inp : V) : V :=
  mkStep W 87 ?[^&is, ^&ip] ∷ mkStep W 116 ?[^&(is + 1), ^&(ip + 1), ^&0] ∷
  mkStep W 93 ?[^&(is + 1), ^&(ip + 1), ^&(inp + 1), ^&0] ∷
  mkStep W 99 ?[^&0, ^&(is + 1), ^&(ip + 1), ^&(il + 1)] ∷ (0 : V)

/-- **The `axL` fragment**: the head, then the leaf tail closing `goalFact &(is+1) (bnum n)`. -/
noncomputable def fragAxL (W tblN is il ip inp L n : V) : V :=
  appendV (fragAxLHead W is il ip inp) (goalTailLeaf W tblN (il + 1) L n (is + 1))

noncomputable def fragAxLHeadCtx (Γ is il ip : V) : V :=
  insert (neg LAct (dlenFact (^&0 : V) (leafT (il + 1))))
    (insert (neg LAct (derFact (^&0 : V)))
      (insert (neg LAct (fstIdxFact (^&(is + 1)) (^&0)))
        (insert (neg LAct (axLFact (^&0 : V) (^&(is + 1)) (^&(ip + 1)))) (setShift LAct Γ))))

theorem fragAxLHead_ok {tbl N E Γ W is il ip inp : V} (htbl : TableOK tbl N) (hF : Frag1Table tbl)
    (hWp : W = frag1Pieces) (hΓ : IsFormulaSet LAct Γ)
    (his : is + 2 ≤ E) (hil : il + 2 ≤ E) (hip : ip + 2 ≤ E) (hinp : inp + 2 ≤ E)
    (hfs : neg LAct (fsetPiFact (^&is)) ∈ Γ) (hmp : neg LAct (memFact (^&ip) (^&is)) ∈ Γ)
    (hneg : neg LAct (negFact (^&inp) (^&ip)) ∈ Γ) (hmnp : neg LAct (memFact (^&inp) (^&is)) ∈ Γ)
    (hsl : neg LAct (setLenFact (^&il) (^&is)) ∈ Γ) :
    ListOK tbl E ((8 : ℕ) : V) Γ (fragAxLHead W is il ip inp) ∧ NoDrop' (fragAxLHead W is il ip inp) ∧
    shiftsV (fragAxLHead W is il ip inp) = 1 ∧ len (fragAxLHead W is il ip inp) = 4 ∧
    finalCtx Γ (fragAxLHead W is il ip inp) = fragAxLHeadCtx Γ is il ip := by
  have hi0 : IsSemiterm LAct 0 (^&is : V) := by simp
  have hiE : termLen LAct (^&is : V) ≤ E := termLen_fvar_le (le_trans (by gcongr; norm_num) his)
  have hp0 : IsSemiterm LAct 0 (^&ip : V) := by simp
  have hpE : termLen LAct (^&ip : V) ≤ E := termLen_fvar_le (le_trans (by gcongr; norm_num) hip)
  have hnp0 : IsSemiterm LAct 0 (^&inp : V) := by simp
  have hl0 : IsSemiterm LAct 0 (^&il : V) := by simp
  have hi1 : IsSemiterm LAct 0 (^&(is + 1) : V) := by simp
  have hi1E : termLen LAct (^&(is + 1) : V) ≤ E := termLen_fvar_succ_le his
  have hp1 : IsSemiterm LAct 0 (^&(ip + 1) : V) := by simp
  have hp1E : termLen LAct (^&(ip + 1) : V) ≤ E := termLen_fvar_succ_le hip
  have hnp1 : IsSemiterm LAct 0 (^&(inp + 1) : V) := by simp
  have hnp1E : termLen LAct (^&(inp + 1) : V) ≤ E := termLen_fvar_succ_le hinp
  have hl1 : IsSemiterm LAct 0 (^&(il + 1) : V) := by simp
  have hl1E : termLen LAct (^&(il + 1) : V) ≤ E := termLen_fvar_succ_le hil
  have hf0 : IsSemiterm LAct 0 (^&0 : V) := by simp
  have hf0E : termLen LAct (^&0 : V) ≤ E :=
    termLen_fvar_le (by rw [zero_add]; exact le_trans (by norm_num) (le_trans le_add_self his))
  -- step 1: tot_axL
  obtain ⟨ok₁, tg₁, cx₁⟩ := fok_totAxL htbl hF hWp hΓ hi0 hiE hp0 hpE
  rw [termShift_fvar, termShift_fvar, Nat.cast_zero] at cx₁
  set Γ₁ := insert (neg LAct (axLFact (^&0 : V) (^&(is + 1)) (^&(ip + 1)))) (setShift LAct Γ) with hΓ₁def
  have hΓ₁ : IsFormulaSet LAct Γ₁ := cx₁ ▸ isFormulaSet_ctxAfter 8 htbl ok₁
  -- the shifted layout facts
  have tfs : neg LAct (fsetPiFact (^&(is + 1))) ∈ Γ₁ := by
    have := mem_shift_insert (f := neg LAct (axLFact (^&0 : V) (^&(is + 1)) (^&(ip + 1)))) hfs
    rwa [shift_neg (isFormula_fsetPiFact hi0), shift_fsetPiFact hi0, termShift_fvar] at this
  have tmp : neg LAct (memFact (^&(ip + 1)) (^&(is + 1))) ∈ Γ₁ := by
    have := mem_shift_insert (f := neg LAct (axLFact (^&0 : V) (^&(is + 1)) (^&(ip + 1)))) hmp
    rwa [shift_neg (isFormula_memFact hp0 hi0), shift_memFact hp0 hi0, termShift_fvar, termShift_fvar] at this
  have tneg : neg LAct (negFact (^&(inp + 1)) (^&(ip + 1))) ∈ Γ₁ := by
    have := mem_shift_insert (f := neg LAct (axLFact (^&0 : V) (^&(is + 1)) (^&(ip + 1)))) hneg
    rwa [shift_neg (isFormula_negFact hnp0 hp0), shift_negFact hnp0 hp0, termShift_fvar, termShift_fvar] at this
  have tmnp : neg LAct (memFact (^&(inp + 1)) (^&(is + 1))) ∈ Γ₁ := by
    have := mem_shift_insert (f := neg LAct (axLFact (^&0 : V) (^&(is + 1)) (^&(ip + 1)))) hmnp
    rwa [shift_neg (isFormula_memFact hnp0 hi0), shift_memFact hnp0 hi0, termShift_fvar, termShift_fvar] at this
  have tsl : neg LAct (setLenFact (^&(il + 1)) (^&(is + 1))) ∈ Γ₁ := by
    have := mem_shift_insert (f := neg LAct (axLFact (^&0 : V) (^&(is + 1)) (^&(ip + 1)))) hsl
    rwa [shift_neg (isFormula_setLenFact hl0 hi0), shift_setLenFact hl0 hi0, termShift_fvar, termShift_fvar] at this
  -- step 2: fstIdx_axL
  obtain ⟨ok₂, tg₂, cx₂⟩ := fok_fstIdxAxL htbl hF hWp hΓ₁ hi1 hi1E hp1 hp1E hf0 hf0E (by rw [hΓ₁def]; simp)
  set Γ₂ := insert (neg LAct (fstIdxFact (^&(is + 1)) (^&0))) Γ₁ with hΓ₂def
  have hΓ₂ : IsFormulaSet LAct Γ₂ := cx₂ ▸ isFormulaSet_ctxAfter 8 htbl ok₂
  -- step 3: Intro_axL
  obtain ⟨ok₃, tg₃, cx₃⟩ := fok_introAxL htbl hF hWp hΓ₂ hi1 hi1E hp1 hp1E hnp1 hnp1E hf0 hf0E
    (by rw [hΓ₂def]; simp [tfs]) (by rw [hΓ₂def]; simp [tmp]) (by rw [hΓ₂def]; simp [tneg])
    (by rw [hΓ₂def]; simp [tmnp]) (by rw [hΓ₂def, hΓ₁def]; simp)
  set Γ₃ := insert (neg LAct (derFact (^&0 : V))) Γ₂ with hΓ₃def
  have hΓ₃ : IsFormulaSet LAct Γ₃ := cx₃ ▸ isFormulaSet_ctxAfter 8 htbl ok₃
  -- step 4: Dlen_axL
  obtain ⟨ok₄, tg₄, cx₄⟩ := fok_dlenAxL htbl hF hWp hΓ₃ hf0 hf0E hi1 hi1E hp1 hp1E hl1 hl1E
    (by rw [hΓ₃def, hΓ₂def, hΓ₁def]; simp) (by rw [hΓ₃def, hΓ₂def]; simp [tsl])
  have hfin : finalCtx Γ (fragAxLHead W is il ip inp) = fragAxLHeadCtx Γ is il ip := by
    unfold fragAxLHead
    rw [finalCtx_cons, cx₁, finalCtx_cons, cx₂, finalCtx_cons, cx₃, finalCtx_single, cx₄]
    rfl
  refine ⟨?_, ?_, ?_, ?_, hfin⟩
  · unfold fragAxLHead
    refine listOK_cons ok₁ ?_
    rw [cx₁]
    refine listOK_cons ok₂ ?_
    rw [cx₂]
    refine listOK_cons ok₃ ?_
    rw [cx₃]
    exact listOK_single ok₄
  · unfold fragAxLHead
    exact noDrop'_cons (by rw [tg₁]; simp) (noDrop'_cons (by rw [tg₂]; simp)
      (noDrop'_cons (by rw [tg₃]; simp) (noDrop'_single (by rw [tg₄]; simp))))
  · unfold fragAxLHead
    rw [shiftsV_cons, shiftsV_cons, shiftsV_cons, shiftsV_single, tg₁, tg₂, tg₃, tg₄]
    simp
  · unfold fragAxLHead; simp [len_adjoin]; norm_num

/-- **`fragAxL` is applicable**: from the leaf's layout, nine steps and one shift, ending with the node's goal
fact `goalFact &(is+1) (bnum n)` — the sequent object now at `&(is+1)`. -/
theorem fragAxL_ok {tbl N E Γ W tblN N' B' is il ip inp L n : V} (htbl : TableOK tbl N) (hF : Frag1Table tbl)
    (hWp : W = frag1Pieces) (htblN : NumTableOK tblN N' B') (hΓ : IsFormulaSet LAct Γ)
    (his : is + 2 ≤ E) (hil : il + 4 ≤ E) (hip : ip + 2 ≤ E) (hinp : inp + 2 ≤ E) (hn : 18 * ‖n‖ + 7 ≤ E)
    (hLn : L + 1 ≤ n)
    (hfs : neg LAct (fsetPiFact (^&is)) ∈ Γ) (hmp : neg LAct (memFact (^&ip) (^&is)) ∈ Γ)
    (hneg : neg LAct (negFact (^&inp) (^&ip)) ∈ Γ) (hmnp : neg LAct (memFact (^&inp) (^&is)) ∈ Γ)
    (hsl : neg LAct (setLenFact (^&il) (^&is)) ∈ Γ) (hle : neg LAct (leFact (^&il) (bnum L)) ∈ Γ) :
    ListOK tbl E ((8 : ℕ) : V) Γ (fragAxL W tblN is il ip inp L n) ∧ NoDrop' (fragAxL W tblN is il ip inp L n) ∧
    shiftsV (fragAxL W tblN is il ip inp L n) = 1 ∧ len (fragAxL W tblN is il ip inp L n) = 9 ∧
    neg LAct (goalFact (^&(is + 1)) (bnum n)) ∈ finalCtx Γ (fragAxL W tblN is il ip inp L n) := by
  have hil2 : il + 2 ≤ E := le_trans (by gcongr; norm_num) hil
  obtain ⟨hok, hnd, hsv, hlen, hfin⟩ := fragAxLHead_ok htbl hF hWp hΓ his hil2 hip hinp hfs hmp hneg hmnp hsl
  have hΓ' : IsFormulaSet LAct (finalCtx Γ (fragAxLHead W is il ip inp)) := finalCtx_isFormulaSet 8 htbl hΓ hok
  have hl0 : IsSemiterm LAct 0 (^&il : V) := by simp
  have hbL : IsSemiterm LAct 0 (bnum L) := isSemiterm_bnum_LAct 0 L
  have hle' : neg LAct (leFact (^&(il + 1)) (bnum L)) ∈ finalCtx Γ (fragAxLHead W is il ip inp) := by
    rw [hfin]; unfold fragAxLHeadCtx
    have := shift_mem_head3 (a := neg LAct (dlenFact (^&0 : V) (leafT (il + 1)))) (b := neg LAct (derFact (^&0 : V)))
      (c := neg LAct (fstIdxFact (^&(is + 1)) (^&0)))
      (f := neg LAct (axLFact (^&0 : V) (^&(is + 1)) (^&(ip + 1)))) hle
    rwa [shift_neg (isFormula_leFact hl0 hbL), shift_leFact hl0 hbL, termShift_fvar, termShift_bnum] at this
  obtain ⟨tok, tnd, tsv, tlen, tfin, tmem⟩ := goalTailLeaf_ok htbl hF hWp htblN hΓ'
    (by rw [show il + 1 + 3 = il + 4 by ring]; exact hil) (by rw [add_assoc, one_add_one_eq_two]; exact his) hn hLn hle'
    (by rw [hfin]; unfold fragAxLHeadCtx; simp) (by rw [hfin]; unfold fragAxLHeadCtx; simp)
    (by rw [hfin]; unfold fragAxLHeadCtx; simp)
  refine ⟨listOK_appendV hok tok, noDrop'_appendV hnd tnd, ?_, ?_, ?_⟩
  · unfold fragAxL; rw [shiftsV_appendV, hsv, tsv, add_zero]
  · unfold fragAxL; rw [len_appendV, hlen, tlen]; norm_num
  · unfold fragAxL; rw [finalCtx_appendV]; exact tmem

/-- The four node steps of `verumIntro`: `tot_verumIntro`, `fstIdx_verum`, `Intro_verum`, `Dlen_verum`. -/
noncomputable def fragVerumHead (W is il iv : V) : V :=
  mkStep W 88 ?[^&is] ∷ mkStep W 117 ?[^&(is + 1), ^&0] ∷
  mkStep W 94 ?[^&(is + 1), ^&(iv + 1), ^&0] ∷ mkStep W 100 ?[^&0, ^&(is + 1), ^&(il + 1)] ∷ (0 : V)

/-- **The `verumIntro` fragment**. -/
noncomputable def fragVerum (W tblN is il iv L n : V) : V :=
  appendV (fragVerumHead W is il iv) (goalTailLeaf W tblN (il + 1) L n (is + 1))

noncomputable def fragVerumHeadCtx (Γ is il : V) : V :=
  insert (neg LAct (dlenFact (^&0 : V) (leafT (il + 1))))
    (insert (neg LAct (derFact (^&0 : V)))
      (insert (neg LAct (fstIdxFact (^&(is + 1)) (^&0)))
        (insert (neg LAct (verumIntroFact (^&0 : V) (^&(is + 1)))) (setShift LAct Γ))))

theorem fragVerumHead_ok {tbl N E Γ W is il iv : V} (htbl : TableOK tbl N) (hF : Frag1Table tbl)
    (hWp : W = frag1Pieces) (hΓ : IsFormulaSet LAct Γ)
    (his : is + 2 ≤ E) (hil : il + 2 ≤ E) (hiv : iv + 2 ≤ E)
    (hfs : neg LAct (fsetPiFact (^&is)) ∈ Γ) (hv : neg LAct (verumFact (^&iv)) ∈ Γ)
    (hmv : neg LAct (memFact (^&iv) (^&is)) ∈ Γ) (hsl : neg LAct (setLenFact (^&il) (^&is)) ∈ Γ) :
    ListOK tbl E ((8 : ℕ) : V) Γ (fragVerumHead W is il iv) ∧ NoDrop' (fragVerumHead W is il iv) ∧
    shiftsV (fragVerumHead W is il iv) = 1 ∧ len (fragVerumHead W is il iv) = 4 ∧
    finalCtx Γ (fragVerumHead W is il iv) = fragVerumHeadCtx Γ is il := by
  have hi0 : IsSemiterm LAct 0 (^&is : V) := by simp
  have hiE : termLen LAct (^&is : V) ≤ E := termLen_fvar_le (le_trans (by gcongr; norm_num) his)
  have hv0 : IsSemiterm LAct 0 (^&iv : V) := by simp
  have hl0 : IsSemiterm LAct 0 (^&il : V) := by simp
  have hi1 : IsSemiterm LAct 0 (^&(is + 1) : V) := by simp
  have hi1E : termLen LAct (^&(is + 1) : V) ≤ E := termLen_fvar_succ_le his
  have hv1 : IsSemiterm LAct 0 (^&(iv + 1) : V) := by simp
  have hv1E : termLen LAct (^&(iv + 1) : V) ≤ E := termLen_fvar_succ_le hiv
  have hl1 : IsSemiterm LAct 0 (^&(il + 1) : V) := by simp
  have hl1E : termLen LAct (^&(il + 1) : V) ≤ E := termLen_fvar_succ_le hil
  have hf0 : IsSemiterm LAct 0 (^&0 : V) := by simp
  have hf0E : termLen LAct (^&0 : V) ≤ E :=
    termLen_fvar_le (by rw [zero_add]; exact le_trans (by norm_num) (le_trans le_add_self his))
  obtain ⟨ok₁, tg₁, cx₁⟩ := fok_totVerumIntro htbl hF hWp hΓ hi0 hiE
  rw [termShift_fvar, Nat.cast_zero] at cx₁
  set Γ₁ := insert (neg LAct (verumIntroFact (^&0 : V) (^&(is + 1)))) (setShift LAct Γ) with hΓ₁def
  have hΓ₁ : IsFormulaSet LAct Γ₁ := cx₁ ▸ isFormulaSet_ctxAfter 8 htbl ok₁
  have tfs : neg LAct (fsetPiFact (^&(is + 1))) ∈ Γ₁ := by
    have := mem_shift_insert (f := neg LAct (verumIntroFact (^&0 : V) (^&(is + 1)))) hfs
    rwa [shift_neg (isFormula_fsetPiFact hi0), shift_fsetPiFact hi0, termShift_fvar] at this
  have tv : neg LAct (verumFact (^&(iv + 1))) ∈ Γ₁ := by
    have := mem_shift_insert (f := neg LAct (verumIntroFact (^&0 : V) (^&(is + 1)))) hv
    rwa [shift_neg (isFormula_verumFact hv0), shift_verumFact hv0, termShift_fvar] at this
  have tmv : neg LAct (memFact (^&(iv + 1)) (^&(is + 1))) ∈ Γ₁ := by
    have := mem_shift_insert (f := neg LAct (verumIntroFact (^&0 : V) (^&(is + 1)))) hmv
    rwa [shift_neg (isFormula_memFact hv0 hi0), shift_memFact hv0 hi0, termShift_fvar, termShift_fvar] at this
  have tsl : neg LAct (setLenFact (^&(il + 1)) (^&(is + 1))) ∈ Γ₁ := by
    have := mem_shift_insert (f := neg LAct (verumIntroFact (^&0 : V) (^&(is + 1)))) hsl
    rwa [shift_neg (isFormula_setLenFact hl0 hi0), shift_setLenFact hl0 hi0, termShift_fvar, termShift_fvar] at this
  obtain ⟨ok₂, tg₂, cx₂⟩ := fok_fstIdxVerum htbl hF hWp hΓ₁ hi1 hi1E hf0 hf0E (by rw [hΓ₁def]; simp)
  set Γ₂ := insert (neg LAct (fstIdxFact (^&(is + 1)) (^&0))) Γ₁ with hΓ₂def
  have hΓ₂ : IsFormulaSet LAct Γ₂ := cx₂ ▸ isFormulaSet_ctxAfter 8 htbl ok₂
  obtain ⟨ok₃, tg₃, cx₃⟩ := fok_introVerum htbl hF hWp hΓ₂ hi1 hi1E hv1 hv1E hf0 hf0E
    (by rw [hΓ₂def]; simp [tfs]) (by rw [hΓ₂def]; simp [tv]) (by rw [hΓ₂def]; simp [tmv])
    (by rw [hΓ₂def, hΓ₁def]; simp)
  set Γ₃ := insert (neg LAct (derFact (^&0 : V))) Γ₂ with hΓ₃def
  have hΓ₃ : IsFormulaSet LAct Γ₃ := cx₃ ▸ isFormulaSet_ctxAfter 8 htbl ok₃
  obtain ⟨ok₄, tg₄, cx₄⟩ := fok_dlenVerum htbl hF hWp hΓ₃ hf0 hf0E hi1 hi1E hl1 hl1E
    (by rw [hΓ₃def, hΓ₂def, hΓ₁def]; simp) (by rw [hΓ₃def, hΓ₂def]; simp [tsl])
  have hfin : finalCtx Γ (fragVerumHead W is il iv) = fragVerumHeadCtx Γ is il := by
    unfold fragVerumHead
    rw [finalCtx_cons, cx₁, finalCtx_cons, cx₂, finalCtx_cons, cx₃, finalCtx_single, cx₄]
    rfl
  refine ⟨?_, ?_, ?_, ?_, hfin⟩
  · unfold fragVerumHead
    refine listOK_cons ok₁ ?_
    rw [cx₁]
    refine listOK_cons ok₂ ?_
    rw [cx₂]
    refine listOK_cons ok₃ ?_
    rw [cx₃]
    exact listOK_single ok₄
  · unfold fragVerumHead
    exact noDrop'_cons (by rw [tg₁]; simp) (noDrop'_cons (by rw [tg₂]; simp)
      (noDrop'_cons (by rw [tg₃]; simp) (noDrop'_single (by rw [tg₄]; simp))))
  · unfold fragVerumHead
    rw [shiftsV_cons, shiftsV_cons, shiftsV_cons, shiftsV_single, tg₁, tg₂, tg₃, tg₄]
    simp
  · unfold fragVerumHead; simp [len_adjoin]; norm_num

/-- **`fragVerum` is applicable**. -/
theorem fragVerum_ok {tbl N E Γ W tblN N' B' is il iv L n : V} (htbl : TableOK tbl N) (hF : Frag1Table tbl)
    (hWp : W = frag1Pieces) (htblN : NumTableOK tblN N' B') (hΓ : IsFormulaSet LAct Γ)
    (his : is + 2 ≤ E) (hil : il + 4 ≤ E) (hiv : iv + 2 ≤ E) (hn : 18 * ‖n‖ + 7 ≤ E) (hLn : L + 1 ≤ n)
    (hfs : neg LAct (fsetPiFact (^&is)) ∈ Γ) (hv : neg LAct (verumFact (^&iv)) ∈ Γ)
    (hmv : neg LAct (memFact (^&iv) (^&is)) ∈ Γ) (hsl : neg LAct (setLenFact (^&il) (^&is)) ∈ Γ)
    (hle : neg LAct (leFact (^&il) (bnum L)) ∈ Γ) :
    ListOK tbl E ((8 : ℕ) : V) Γ (fragVerum W tblN is il iv L n) ∧ NoDrop' (fragVerum W tblN is il iv L n) ∧
    shiftsV (fragVerum W tblN is il iv L n) = 1 ∧ len (fragVerum W tblN is il iv L n) = 9 ∧
    neg LAct (goalFact (^&(is + 1)) (bnum n)) ∈ finalCtx Γ (fragVerum W tblN is il iv L n) := by
  have hil2 : il + 2 ≤ E := le_trans (by gcongr; norm_num) hil
  obtain ⟨hok, hnd, hsv, hlen, hfin⟩ := fragVerumHead_ok htbl hF hWp hΓ his hil2 hiv hfs hv hmv hsl
  have hΓ' : IsFormulaSet LAct (finalCtx Γ (fragVerumHead W is il iv)) := finalCtx_isFormulaSet 8 htbl hΓ hok
  have hl0 : IsSemiterm LAct 0 (^&il : V) := by simp
  have hbL : IsSemiterm LAct 0 (bnum L) := isSemiterm_bnum_LAct 0 L
  have hle' : neg LAct (leFact (^&(il + 1)) (bnum L)) ∈ finalCtx Γ (fragVerumHead W is il iv) := by
    rw [hfin]; unfold fragVerumHeadCtx
    have := shift_mem_head3 (a := neg LAct (dlenFact (^&0 : V) (leafT (il + 1)))) (b := neg LAct (derFact (^&0 : V)))
      (c := neg LAct (fstIdxFact (^&(is + 1)) (^&0)))
      (f := neg LAct (verumIntroFact (^&0 : V) (^&(is + 1)))) hle
    rwa [shift_neg (isFormula_leFact hl0 hbL), shift_leFact hl0 hbL, termShift_fvar, termShift_bnum] at this
  obtain ⟨tok, tnd, tsv, tlen, tfin, tmem⟩ := goalTailLeaf_ok htbl hF hWp htblN hΓ'
    (by rw [show il + 1 + 3 = il + 4 by ring]; exact hil) (by rw [add_assoc, one_add_one_eq_two]; exact his) hn hLn hle'
    (by rw [hfin]; unfold fragVerumHeadCtx; simp) (by rw [hfin]; unfold fragVerumHeadCtx; simp)
    (by rw [hfin]; unfold fragVerumHeadCtx; simp)
  refine ⟨listOK_appendV hok tok, noDrop'_appendV hnd tnd, ?_, ?_, ?_⟩
  · unfold fragVerum; rw [shiftsV_appendV, hsv, tsv, add_zero]
  · unfold fragVerum; rw [len_appendV, hlen, tlen]; norm_num
  · unfold fragVerum; rw [finalCtx_appendV]; exact tmem

end leaves

/-! ## 4. The node fragments `nodeAnd`, `nodeOr`, `nodeWk`, `nodeCut` (DESIGN_fragments §4.3, §4.4, §4.7, §4.9)

Each is the `node(ν)` list of §4.0 for a node whose children have been recovered (`goalElim`): the totality
step, `fstIdx_tag`, `Intro_tag`, `Dlen_tag` (four steps, one shift), then the `dlen` tail and `sGoal`.
LAYOUT ASSUMED at `Γ` (indices of the objects, as `^&i`): the sequent `s` at `is` (with `fsetPiFact` for `wk`),
its length object at `il` (`setLenFact &il &is`, `leFact &il (bnum L)`), the principal member `r` at `ir` with
its shape fact and `memFact &ir &is`, its immediate sub-formulas at `ip`, `iq`; for every child `i`: its
derivation object at `idᵢ` with `derFact`, its length object at `inᵢ` with `dlenFact &idᵢ &inᵢ` and the numeral
bound `leFact &inᵢ (bnum mᵢ)` (what `goalElim` leaves), and the row's sequent object `cᵢ` at `icᵢ` with its
`insFact` (the `insertTotal` object) and `fstIdxFact &icᵢ &idᵢ` — the child's goal fact MOVED onto `cᵢ` by
`congFstIdx`; the identification of the child's chain top with `cᵢ` (§3.4) is NOT produced here. For `wk` the
child's sequent object `c` at `ic` carries `subsetFact &ic &is` instead, and for `cut` the cut formula `p` at
`ip` and its negation at `inp` carry `negFact &inp &ip`. `L`, `mᵢ`, `n` are the values `setLen s`, `dlen dᵢ`,
`dlen ν`; the closed `sLemma` needs the recurrence `L + Σ mᵢ + 1 ≤ n` (true by `DlenGraph.<tag>_iff`). -/

section nodes

/-! ### 4.1 `andIntro` -/

noncomputable def nodeAndHead (W is il ir ip iq id₁ id₂ icp icq in₁ in₂ : V) : V :=
  mkStep W 89 ?[^&is, ^&ip, ^&iq, ^&id₁, ^&id₂] ∷
  mkStep W 118 ?[^&(is + 1), ^&(ip + 1), ^&(iq + 1), ^&(id₁ + 1), ^&(id₂ + 1), ^&0] ∷
  mkStep W 95 ?[^&(is + 1), ^&(ip + 1), ^&(iq + 1), ^&(id₁ + 1), ^&(id₂ + 1), ^&(ir + 1), ^&(icp + 1), ^&(icq + 1), ^&0] ∷
  mkStep W 101 ?[^&0, ^&(is + 1), ^&(ip + 1), ^&(iq + 1), ^&(id₁ + 1), ^&(id₂ + 1), ^&(in₁ + 1), ^&(in₂ + 1), ^&(il + 1)] ∷
  (0 : V)

/-- **The `andIntro` node fragment**. -/
noncomputable def nodeAnd (W tblN is il ir ip iq id₁ id₂ icp icq in₁ in₂ L m₁ m₂ n : V) : V :=
  appendV (nodeAndHead W is il ir ip iq id₁ id₂ icp icq in₁ in₂)
    (goalTailBinary W tblN (il + 1) (in₁ + 1) (in₂ + 1) L m₁ m₂ n (is + 1))

noncomputable def nodeAndHeadCtx (Γ is il ip iq id₁ id₂ in₁ in₂ : V) : V :=
  insert (neg LAct (dlenFact (^&0 : V) (binaryT (il + 1) (in₁ + 1) (in₂ + 1))))
    (insert (neg LAct (derFact (^&0 : V)))
      (insert (neg LAct (fstIdxFact (^&(is + 1)) (^&0)))
        (insert (neg LAct (andIntroFact (^&0 : V) (^&(is + 1)) (^&(ip + 1)) (^&(iq + 1)) (^&(id₁ + 1)) (^&(id₂ + 1))))
          (setShift LAct Γ))))

theorem nodeAndHead_ok {tbl N E Γ W is il ir ip iq id₁ id₂ icp icq in₁ in₂ : V} (htbl : TableOK tbl N)
    (hF : Frag1Table tbl) (hWp : W = frag1Pieces) (hΓ : IsFormulaSet LAct Γ)
    (his : is + 2 ≤ E) (hil : il + 2 ≤ E) (hir : ir + 2 ≤ E) (hip : ip + 2 ≤ E) (hiq : iq + 2 ≤ E)
    (hid₁ : id₁ + 2 ≤ E) (hid₂ : id₂ + 2 ≤ E) (hicp : icp + 2 ≤ E) (hicq : icq + 2 ≤ E)
    (hin₁ : in₁ + 2 ≤ E) (hin₂ : in₂ + 2 ≤ E)
    (hand : neg LAct (andFact (^&ir) (^&ip) (^&iq)) ∈ Γ) (hmr : neg LAct (memFact (^&ir) (^&is)) ∈ Γ)
    (hf₁ : neg LAct (fstIdxFact (^&icp) (^&id₁)) ∈ Γ) (hi₁ : neg LAct (insFact (^&icp) (^&ip) (^&is)) ∈ Γ)
    (hd₁ : neg LAct (derFact (^&id₁ : V)) ∈ Γ) (hn₁ : neg LAct (dlenFact (^&id₁ : V) (^&in₁)) ∈ Γ)
    (hf₂ : neg LAct (fstIdxFact (^&icq) (^&id₂)) ∈ Γ) (hi₂ : neg LAct (insFact (^&icq) (^&iq) (^&is)) ∈ Γ)
    (hd₂ : neg LAct (derFact (^&id₂ : V)) ∈ Γ) (hn₂ : neg LAct (dlenFact (^&id₂ : V) (^&in₂)) ∈ Γ)
    (hsl : neg LAct (setLenFact (^&il) (^&is)) ∈ Γ) :
    ListOK tbl E ((9 : ℕ) : V) Γ (nodeAndHead W is il ir ip iq id₁ id₂ icp icq in₁ in₂) ∧
    NoDrop' (nodeAndHead W is il ir ip iq id₁ id₂ icp icq in₁ in₂) ∧
    shiftsV (nodeAndHead W is il ir ip iq id₁ id₂ icp icq in₁ in₂) = 1 ∧
    len (nodeAndHead W is il ir ip iq id₁ id₂ icp icq in₁ in₂) = 4 ∧
    finalCtx Γ (nodeAndHead W is il ir ip iq id₁ id₂ icp icq in₁ in₂) = nodeAndHeadCtx Γ is il ip iq id₁ id₂ in₁ in₂ := by
  have h89 : ((8 : ℕ) : V) ≤ ((9 : ℕ) : V) := by exact_mod_cast (by decide : (8 : ℕ) ≤ 9)
  have his0 : IsSemiterm LAct 0 (^&is : V) := by simp
  have hisE : termLen LAct (^&is : V) ≤ E := termLen_fvar_le (le_trans (by gcongr; norm_num) his)
  have his1 : IsSemiterm LAct 0 (^&(is + 1) : V) := by simp
  have his1E : termLen LAct (^&(is + 1) : V) ≤ E := termLen_fvar_succ_le his
  have hil0 : IsSemiterm LAct 0 (^&il : V) := by simp
  have hilE : termLen LAct (^&il : V) ≤ E := termLen_fvar_le (le_trans (by gcongr; norm_num) hil)
  have hil1 : IsSemiterm LAct 0 (^&(il + 1) : V) := by simp
  have hil1E : termLen LAct (^&(il + 1) : V) ≤ E := termLen_fvar_succ_le hil
  have hir0 : IsSemiterm LAct 0 (^&ir : V) := by simp
  have hirE : termLen LAct (^&ir : V) ≤ E := termLen_fvar_le (le_trans (by gcongr; norm_num) hir)
  have hir1 : IsSemiterm LAct 0 (^&(ir + 1) : V) := by simp
  have hir1E : termLen LAct (^&(ir + 1) : V) ≤ E := termLen_fvar_succ_le hir
  have hip0 : IsSemiterm LAct 0 (^&ip : V) := by simp
  have hipE : termLen LAct (^&ip : V) ≤ E := termLen_fvar_le (le_trans (by gcongr; norm_num) hip)
  have hip1 : IsSemiterm LAct 0 (^&(ip + 1) : V) := by simp
  have hip1E : termLen LAct (^&(ip + 1) : V) ≤ E := termLen_fvar_succ_le hip
  have hiq0 : IsSemiterm LAct 0 (^&iq : V) := by simp
  have hiqE : termLen LAct (^&iq : V) ≤ E := termLen_fvar_le (le_trans (by gcongr; norm_num) hiq)
  have hiq1 : IsSemiterm LAct 0 (^&(iq + 1) : V) := by simp
  have hiq1E : termLen LAct (^&(iq + 1) : V) ≤ E := termLen_fvar_succ_le hiq
  have hid₁0 : IsSemiterm LAct 0 (^&id₁ : V) := by simp
  have hid₁E : termLen LAct (^&id₁ : V) ≤ E := termLen_fvar_le (le_trans (by gcongr; norm_num) hid₁)
  have hid₁1 : IsSemiterm LAct 0 (^&(id₁ + 1) : V) := by simp
  have hid₁1E : termLen LAct (^&(id₁ + 1) : V) ≤ E := termLen_fvar_succ_le hid₁
  have hid₂0 : IsSemiterm LAct 0 (^&id₂ : V) := by simp
  have hid₂E : termLen LAct (^&id₂ : V) ≤ E := termLen_fvar_le (le_trans (by gcongr; norm_num) hid₂)
  have hid₂1 : IsSemiterm LAct 0 (^&(id₂ + 1) : V) := by simp
  have hid₂1E : termLen LAct (^&(id₂ + 1) : V) ≤ E := termLen_fvar_succ_le hid₂
  have hicp0 : IsSemiterm LAct 0 (^&icp : V) := by simp
  have hicpE : termLen LAct (^&icp : V) ≤ E := termLen_fvar_le (le_trans (by gcongr; norm_num) hicp)
  have hicp1 : IsSemiterm LAct 0 (^&(icp + 1) : V) := by simp
  have hicp1E : termLen LAct (^&(icp + 1) : V) ≤ E := termLen_fvar_succ_le hicp
  have hicq0 : IsSemiterm LAct 0 (^&icq : V) := by simp
  have hicqE : termLen LAct (^&icq : V) ≤ E := termLen_fvar_le (le_trans (by gcongr; norm_num) hicq)
  have hicq1 : IsSemiterm LAct 0 (^&(icq + 1) : V) := by simp
  have hicq1E : termLen LAct (^&(icq + 1) : V) ≤ E := termLen_fvar_succ_le hicq
  have hin₁0 : IsSemiterm LAct 0 (^&in₁ : V) := by simp
  have hin₁E : termLen LAct (^&in₁ : V) ≤ E := termLen_fvar_le (le_trans (by gcongr; norm_num) hin₁)
  have hin₁1 : IsSemiterm LAct 0 (^&(in₁ + 1) : V) := by simp
  have hin₁1E : termLen LAct (^&(in₁ + 1) : V) ≤ E := termLen_fvar_succ_le hin₁
  have hin₂0 : IsSemiterm LAct 0 (^&in₂ : V) := by simp
  have hin₂E : termLen LAct (^&in₂ : V) ≤ E := termLen_fvar_le (le_trans (by gcongr; norm_num) hin₂)
  have hin₂1 : IsSemiterm LAct 0 (^&(in₂ + 1) : V) := by simp
  have hin₂1E : termLen LAct (^&(in₂ + 1) : V) ≤ E := termLen_fvar_succ_le hin₂
  have hf0 : IsSemiterm LAct 0 (^&0 : V) := by simp
  have hf0E : termLen LAct (^&0 : V) ≤ E :=
    termLen_fvar_le (by rw [zero_add]; exact le_trans (by norm_num) (le_trans le_add_self his))
  -- step 1: tot_andIntro
  obtain ⟨ok₁, tg₁, cx₁⟩ := fok_totAndIntro htbl hF hWp hΓ his0 hisE hip0 hipE hiq0 hiqE hid₁0 hid₁E hid₂0 hid₂E
  rw [termShift_fvar, termShift_fvar, termShift_fvar, termShift_fvar, termShift_fvar, Nat.cast_zero] at cx₁
  set F := neg LAct (andIntroFact (^&0 : V) (^&(is + 1)) (^&(ip + 1)) (^&(iq + 1)) (^&(id₁ + 1)) (^&(id₂ + 1))) with hFdef
  set Γ₁ := insert F (setShift LAct Γ) with hΓ₁def
  have hΓ₁ : IsFormulaSet LAct Γ₁ := cx₁ ▸ isFormulaSet_ctxAfter 8 htbl ok₁
  have tand : neg LAct (andFact (^&(ir + 1)) (^&(ip + 1)) (^&(iq + 1))) ∈ Γ₁ := by
    have := mem_shift_insert (f := F) hand
    rwa [shift_neg (isFormula_andFact hir0 hip0 hiq0), shift_andFact hir0 hip0 hiq0, termShift_fvar, termShift_fvar, termShift_fvar] at this
  have tmr : neg LAct (memFact (^&(ir + 1)) (^&(is + 1))) ∈ Γ₁ := by
    have := mem_shift_insert (f := F) hmr
    rwa [shift_neg (isFormula_memFact hir0 his0), shift_memFact hir0 his0, termShift_fvar, termShift_fvar] at this
  have tf₁ : neg LAct (fstIdxFact (^&(icp + 1)) (^&(id₁ + 1))) ∈ Γ₁ := by
    have := mem_shift_insert (f := F) hf₁
    rwa [shift_neg (isFormula_fstIdxFact hicp0 hid₁0), shift_fstIdxFact hicp0 hid₁0, termShift_fvar, termShift_fvar] at this
  have ti₁ : neg LAct (insFact (^&(icp + 1)) (^&(ip + 1)) (^&(is + 1))) ∈ Γ₁ := by
    have := mem_shift_insert (f := F) hi₁
    rwa [shift_neg (isFormula_insFact hicp0 hip0 his0), shift_insFact hicp0 hip0 his0, termShift_fvar, termShift_fvar, termShift_fvar] at this
  have td₁ : neg LAct (derFact (^&(id₁ + 1) : V)) ∈ Γ₁ := by
    have := mem_shift_insert (f := F) hd₁
    rwa [shift_neg (isFormula_derFact hid₁0), shift_derFact hid₁0, termShift_fvar] at this
  have tn₁ : neg LAct (dlenFact (^&(id₁ + 1) : V) (^&(in₁ + 1))) ∈ Γ₁ := by
    have := mem_shift_insert (f := F) hn₁
    rwa [shift_neg (isFormula_dlenFact hid₁0 hin₁0), shift_dlenFact hid₁0 hin₁0, termShift_fvar, termShift_fvar] at this
  have tf₂ : neg LAct (fstIdxFact (^&(icq + 1)) (^&(id₂ + 1))) ∈ Γ₁ := by
    have := mem_shift_insert (f := F) hf₂
    rwa [shift_neg (isFormula_fstIdxFact hicq0 hid₂0), shift_fstIdxFact hicq0 hid₂0, termShift_fvar, termShift_fvar] at this
  have ti₂ : neg LAct (insFact (^&(icq + 1)) (^&(iq + 1)) (^&(is + 1))) ∈ Γ₁ := by
    have := mem_shift_insert (f := F) hi₂
    rwa [shift_neg (isFormula_insFact hicq0 hiq0 his0), shift_insFact hicq0 hiq0 his0, termShift_fvar, termShift_fvar, termShift_fvar] at this
  have td₂ : neg LAct (derFact (^&(id₂ + 1) : V)) ∈ Γ₁ := by
    have := mem_shift_insert (f := F) hd₂
    rwa [shift_neg (isFormula_derFact hid₂0), shift_derFact hid₂0, termShift_fvar] at this
  have tn₂ : neg LAct (dlenFact (^&(id₂ + 1) : V) (^&(in₂ + 1))) ∈ Γ₁ := by
    have := mem_shift_insert (f := F) hn₂
    rwa [shift_neg (isFormula_dlenFact hid₂0 hin₂0), shift_dlenFact hid₂0 hin₂0, termShift_fvar, termShift_fvar] at this
  have tsl : neg LAct (setLenFact (^&(il + 1)) (^&(is + 1))) ∈ Γ₁ := by
    have := mem_shift_insert (f := F) hsl
    rwa [shift_neg (isFormula_setLenFact hil0 his0), shift_setLenFact hil0 his0, termShift_fvar, termShift_fvar] at this
  -- step 2: fstIdx_and
  obtain ⟨ok₂, tg₂, cx₂⟩ := fok_fstIdxAnd htbl hF hWp hΓ₁ his1 his1E hip1 hip1E hiq1 hiq1E hid₁1 hid₁1E hid₂1 hid₂1E hf0 hf0E
    (by rw [hΓ₁def, hFdef]; simp)
  set Γ₂ := insert (neg LAct (fstIdxFact (^&(is + 1)) (^&0))) Γ₁ with hΓ₂def
  have hΓ₂ : IsFormulaSet LAct Γ₂ := cx₂ ▸ isFormulaSet_ctxAfter 8 htbl ok₂
  -- step 3: Intro_and
  obtain ⟨ok₃, tg₃, cx₃⟩ := fok_introAnd htbl hF hWp hΓ₂ his1 his1E hip1 hip1E hiq1 hiq1E hid₁1 hid₁1E hid₂1 hid₂1E
    hir1 hir1E hicp1 hicp1E hicq1 hicq1E hf0 hf0E
    (by rw [hΓ₂def, hΓ₁def, hFdef]; simp) (by rw [hΓ₂def]; simp [tand]) (by rw [hΓ₂def]; simp [tmr])
    (by rw [hΓ₂def]; simp [tf₁]) (by rw [hΓ₂def]; simp [ti₁]) (by rw [hΓ₂def]; simp [td₁])
    (by rw [hΓ₂def]; simp [tf₂]) (by rw [hΓ₂def]; simp [ti₂]) (by rw [hΓ₂def]; simp [td₂])
  set Γ₃ := insert (neg LAct (derFact (^&0 : V))) Γ₂ with hΓ₃def
  have hΓ₃ : IsFormulaSet LAct Γ₃ := cx₃ ▸ isFormulaSet_ctxAfter 9 htbl ok₃
  -- step 4: Dlen_and
  obtain ⟨ok₄, tg₄, cx₄⟩ := fok_dlenAnd htbl hF hWp hΓ₃ hf0 hf0E his1 his1E hip1 hip1E hiq1 hiq1E hid₁1 hid₁1E
    hid₂1 hid₂1E hin₁1 hin₁1E hin₂1 hin₂1E hil1 hil1E
    (by rw [hΓ₃def, hΓ₂def, hΓ₁def, hFdef]; simp) (by rw [hΓ₃def, hΓ₂def]; simp [tn₁])
    (by rw [hΓ₃def, hΓ₂def]; simp [tn₂]) (by rw [hΓ₃def, hΓ₂def]; simp [tsl])
  have hfin : finalCtx Γ (nodeAndHead W is il ir ip iq id₁ id₂ icp icq in₁ in₂) =
      nodeAndHeadCtx Γ is il ip iq id₁ id₂ in₁ in₂ := by
    unfold nodeAndHead
    rw [finalCtx_cons, cx₁, finalCtx_cons, cx₂, finalCtx_cons, cx₃, finalCtx_single, cx₄]
    rfl
  refine ⟨?_, ?_, ?_, ?_, hfin⟩
  · unfold nodeAndHead
    refine listOK_cons (ok₁.mono h89) ?_
    rw [cx₁]
    refine listOK_cons (ok₂.mono h89) ?_
    rw [cx₂]
    refine listOK_cons ok₃ ?_
    rw [cx₃]
    exact listOK_single ok₄
  · unfold nodeAndHead
    exact noDrop'_cons (by rw [tg₁]; simp) (noDrop'_cons (by rw [tg₂]; simp)
      (noDrop'_cons (by rw [tg₃]; simp) (noDrop'_single (by rw [tg₄]; simp))))
  · unfold nodeAndHead
    rw [shiftsV_cons, shiftsV_cons, shiftsV_cons, shiftsV_single, tg₁, tg₂, tg₃, tg₄]
    simp
  · unfold nodeAndHead; simp [len_adjoin]; norm_num

/-- **`nodeAnd` is applicable** (cap `M = 9`: `Intro_and` and `Dlen_and` have nine witnesses). -/
theorem nodeAnd_ok {tbl N E Γ W tblN N' B' is il ir ip iq id₁ id₂ icp icq in₁ in₂ L m₁ m₂ n : V}
    (htbl : TableOK tbl N) (hF : Frag1Table tbl) (hWp : W = frag1Pieces) (htblN : NumTableOK tblN N' B')
    (hΓ : IsFormulaSet LAct Γ)
    (his : is + 2 ≤ E) (hir : ir + 2 ≤ E) (hip : ip + 2 ≤ E) (hiq : iq + 2 ≤ E)
    (hid₁ : id₁ + 2 ≤ E) (hid₂ : id₂ + 2 ≤ E) (hicp : icp + 2 ≤ E) (hicq : icq + 2 ≤ E)
    (hT : il + in₁ + in₂ + 10 ≤ E) (hn : 18 * ‖n‖ + 7 ≤ E) (hLn : L + m₁ + m₂ + 1 ≤ n)
    (hand : neg LAct (andFact (^&ir) (^&ip) (^&iq)) ∈ Γ) (hmr : neg LAct (memFact (^&ir) (^&is)) ∈ Γ)
    (hf₁ : neg LAct (fstIdxFact (^&icp) (^&id₁)) ∈ Γ) (hi₁ : neg LAct (insFact (^&icp) (^&ip) (^&is)) ∈ Γ)
    (hd₁ : neg LAct (derFact (^&id₁ : V)) ∈ Γ) (hn₁ : neg LAct (dlenFact (^&id₁ : V) (^&in₁)) ∈ Γ)
    (hle₁ : neg LAct (leFact (^&in₁) (bnum m₁)) ∈ Γ)
    (hf₂ : neg LAct (fstIdxFact (^&icq) (^&id₂)) ∈ Γ) (hi₂ : neg LAct (insFact (^&icq) (^&iq) (^&is)) ∈ Γ)
    (hd₂ : neg LAct (derFact (^&id₂ : V)) ∈ Γ) (hn₂ : neg LAct (dlenFact (^&id₂ : V) (^&in₂)) ∈ Γ)
    (hle₂ : neg LAct (leFact (^&in₂) (bnum m₂)) ∈ Γ)
    (hsl : neg LAct (setLenFact (^&il) (^&is)) ∈ Γ) (hle : neg LAct (leFact (^&il) (bnum L)) ∈ Γ) :
    ListOK tbl E ((9 : ℕ) : V) Γ (nodeAnd W tblN is il ir ip iq id₁ id₂ icp icq in₁ in₂ L m₁ m₂ n) ∧
    NoDrop' (nodeAnd W tblN is il ir ip iq id₁ id₂ icp icq in₁ in₂ L m₁ m₂ n) ∧
    shiftsV (nodeAnd W tblN is il ir ip iq id₁ id₂ icp icq in₁ in₂ L m₁ m₂ n) = 1 ∧
    len (nodeAnd W tblN is il ir ip iq id₁ id₂ icp icq in₁ in₂ L m₁ m₂ n) = 9 ∧
    neg LAct (goalFact (^&(is + 1)) (bnum n)) ∈
      finalCtx Γ (nodeAnd W tblN is il ir ip iq id₁ id₂ icp icq in₁ in₂ L m₁ m₂ n) := by
  have h89 : ((8 : ℕ) : V) ≤ ((9 : ℕ) : V) := by exact_mod_cast (by decide : (8 : ℕ) ≤ 9)
  have hil : il + 2 ≤ E := le_trans (add_le_add (le_trans le_self_add le_self_add) (by norm_num)) hT
  have hin₁ : in₁ + 2 ≤ E := le_trans (add_le_add (le_trans le_add_self le_self_add) (by norm_num)) hT
  have hin₂ : in₂ + 2 ≤ E := le_trans (add_le_add le_add_self (by norm_num)) hT
  obtain ⟨hok, hnd, hsv, hlen, hfin⟩ := nodeAndHead_ok htbl hF hWp hΓ his hil hir hip hiq hid₁ hid₂ hicp hicq hin₁ hin₂
    hand hmr hf₁ hi₁ hd₁ hn₁ hf₂ hi₂ hd₂ hn₂ hsl
  have hΓ' : IsFormulaSet LAct (finalCtx Γ (nodeAndHead W is il ir ip iq id₁ id₂ icp icq in₁ in₂)) :=
    finalCtx_isFormulaSet 9 htbl hΓ hok
  have hl0 : IsSemiterm LAct 0 (^&il : V) := by simp
  have hn10 : IsSemiterm LAct 0 (^&in₁ : V) := by simp
  have hn20 : IsSemiterm LAct 0 (^&in₂ : V) := by simp
  have hbL : IsSemiterm LAct 0 (bnum L) := isSemiterm_bnum_LAct 0 L
  have hbm₁ : IsSemiterm LAct 0 (bnum m₁) := isSemiterm_bnum_LAct 0 m₁
  have hbm₂ : IsSemiterm LAct 0 (bnum m₂) := isSemiterm_bnum_LAct 0 m₂
  have tr : ∀ x ∈ Γ, shift LAct x ∈ finalCtx Γ (nodeAndHead W is il ir ip iq id₁ id₂ icp icq in₁ in₂) := by
    intro x hx; rw [hfin]; unfold nodeAndHeadCtx; exact shift_mem_head3 hx
  have hle' : neg LAct (leFact (^&(il + 1)) (bnum L)) ∈ finalCtx Γ (nodeAndHead W is il ir ip iq id₁ id₂ icp icq in₁ in₂) := by
    have := tr _ hle
    rwa [shift_neg (isFormula_leFact hl0 hbL), shift_leFact hl0 hbL, termShift_fvar, termShift_bnum] at this
  have hle₁' : neg LAct (leFact (^&(in₁ + 1)) (bnum m₁)) ∈ finalCtx Γ (nodeAndHead W is il ir ip iq id₁ id₂ icp icq in₁ in₂) := by
    have := tr _ hle₁
    rwa [shift_neg (isFormula_leFact hn10 hbm₁), shift_leFact hn10 hbm₁, termShift_fvar, termShift_bnum] at this
  have hle₂' : neg LAct (leFact (^&(in₂ + 1)) (bnum m₂)) ∈ finalCtx Γ (nodeAndHead W is il ir ip iq id₁ id₂ icp icq in₁ in₂) := by
    have := tr _ hle₂
    rwa [shift_neg (isFormula_leFact hn20 hbm₂), shift_leFact hn20 hbm₂, termShift_fvar, termShift_bnum] at this
  obtain ⟨tok, tnd, tsv, tlen, tfin, tmem⟩ := goalTailBinary_ok htbl hF hWp htblN hΓ'
    (by rw [show il + 1 + (in₁ + 1) + (in₂ + 1) + 7 = il + in₁ + in₂ + 10 by ring]; exact hT)
    (by rw [add_assoc, one_add_one_eq_two]; exact his) hn hLn hle' hle₁' hle₂'
    (by rw [hfin]; unfold nodeAndHeadCtx; simp) (by rw [hfin]; unfold nodeAndHeadCtx; simp)
    (by rw [hfin]; unfold nodeAndHeadCtx; simp)
  refine ⟨listOK_appendV hok (tok.mono h89), noDrop'_appendV hnd tnd, ?_, ?_, ?_⟩
  · unfold nodeAnd; rw [shiftsV_appendV, hsv, tsv, add_zero]
  · unfold nodeAnd; rw [len_appendV, hlen, tlen]; norm_num
  · unfold nodeAnd; rw [finalCtx_appendV]; exact tmem

/-! ### 4.2 `orIntro` (`c' = insert q s` at `icq`, `c = insert p c'` at `ic`) -/

noncomputable def nodeOrHead (W is il ir ip iq id icq ic in₁ : V) : V :=
  mkStep W 90 ?[^&is, ^&ip, ^&iq, ^&id] ∷
  mkStep W 119 ?[^&(is + 1), ^&(ip + 1), ^&(iq + 1), ^&(id + 1), ^&0] ∷
  mkStep W 96 ?[^&(is + 1), ^&(ip + 1), ^&(iq + 1), ^&(id + 1), ^&(ir + 1), ^&(icq + 1), ^&(ic + 1), ^&0] ∷
  mkStep W 102 ?[^&0, ^&(is + 1), ^&(ip + 1), ^&(iq + 1), ^&(id + 1), ^&(in₁ + 1), ^&(il + 1)] ∷ (0 : V)

/-- **The `orIntro` node fragment**. -/
noncomputable def nodeOr (W tblN is il ir ip iq id icq ic in₁ L m₁ n : V) : V :=
  appendV (nodeOrHead W is il ir ip iq id icq ic in₁) (goalTailUnary W tblN (il + 1) (in₁ + 1) L m₁ n (is + 1))

noncomputable def nodeOrHeadCtx (Γ is il ip iq id in₁ : V) : V :=
  insert (neg LAct (dlenFact (^&0 : V) (unaryT (il + 1) (in₁ + 1))))
    (insert (neg LAct (derFact (^&0 : V)))
      (insert (neg LAct (fstIdxFact (^&(is + 1)) (^&0)))
        (insert (neg LAct (orIntroFact (^&0 : V) (^&(is + 1)) (^&(ip + 1)) (^&(iq + 1)) (^&(id + 1))))
          (setShift LAct Γ))))

theorem nodeOrHead_ok {tbl N E Γ W is il ir ip iq id icq ic in₁ : V} (htbl : TableOK tbl N)
    (hF : Frag1Table tbl) (hWp : W = frag1Pieces) (hΓ : IsFormulaSet LAct Γ)
    (his : is + 2 ≤ E) (hil : il + 2 ≤ E) (hir : ir + 2 ≤ E) (hip : ip + 2 ≤ E) (hiq : iq + 2 ≤ E)
    (hid : id + 2 ≤ E) (hicq : icq + 2 ≤ E) (hic : ic + 2 ≤ E) (hin₁ : in₁ + 2 ≤ E)
    (hor : neg LAct (orFact (^&ir) (^&ip) (^&iq)) ∈ Γ) (hmr : neg LAct (memFact (^&ir) (^&is)) ∈ Γ)
    (hf : neg LAct (fstIdxFact (^&ic) (^&id)) ∈ Γ) (hiq' : neg LAct (insFact (^&icq) (^&iq) (^&is)) ∈ Γ)
    (hip' : neg LAct (insFact (^&ic) (^&ip) (^&icq)) ∈ Γ)
    (hd : neg LAct (derFact (^&id : V)) ∈ Γ) (hn₁ : neg LAct (dlenFact (^&id : V) (^&in₁)) ∈ Γ)
    (hsl : neg LAct (setLenFact (^&il) (^&is)) ∈ Γ) :
    ListOK tbl E ((8 : ℕ) : V) Γ (nodeOrHead W is il ir ip iq id icq ic in₁) ∧
    NoDrop' (nodeOrHead W is il ir ip iq id icq ic in₁) ∧
    shiftsV (nodeOrHead W is il ir ip iq id icq ic in₁) = 1 ∧ len (nodeOrHead W is il ir ip iq id icq ic in₁) = 4 ∧
    finalCtx Γ (nodeOrHead W is il ir ip iq id icq ic in₁) = nodeOrHeadCtx Γ is il ip iq id in₁ := by
  have his0 : IsSemiterm LAct 0 (^&is : V) := by simp
  have hisE : termLen LAct (^&is : V) ≤ E := termLen_fvar_le (le_trans (by gcongr; norm_num) his)
  have his1 : IsSemiterm LAct 0 (^&(is + 1) : V) := by simp
  have his1E : termLen LAct (^&(is + 1) : V) ≤ E := termLen_fvar_succ_le his
  have hil0 : IsSemiterm LAct 0 (^&il : V) := by simp
  have hilE : termLen LAct (^&il : V) ≤ E := termLen_fvar_le (le_trans (by gcongr; norm_num) hil)
  have hil1 : IsSemiterm LAct 0 (^&(il + 1) : V) := by simp
  have hil1E : termLen LAct (^&(il + 1) : V) ≤ E := termLen_fvar_succ_le hil
  have hir0 : IsSemiterm LAct 0 (^&ir : V) := by simp
  have hirE : termLen LAct (^&ir : V) ≤ E := termLen_fvar_le (le_trans (by gcongr; norm_num) hir)
  have hir1 : IsSemiterm LAct 0 (^&(ir + 1) : V) := by simp
  have hir1E : termLen LAct (^&(ir + 1) : V) ≤ E := termLen_fvar_succ_le hir
  have hip0 : IsSemiterm LAct 0 (^&ip : V) := by simp
  have hipE : termLen LAct (^&ip : V) ≤ E := termLen_fvar_le (le_trans (by gcongr; norm_num) hip)
  have hip1 : IsSemiterm LAct 0 (^&(ip + 1) : V) := by simp
  have hip1E : termLen LAct (^&(ip + 1) : V) ≤ E := termLen_fvar_succ_le hip
  have hiq0 : IsSemiterm LAct 0 (^&iq : V) := by simp
  have hiqE : termLen LAct (^&iq : V) ≤ E := termLen_fvar_le (le_trans (by gcongr; norm_num) hiq)
  have hiq1 : IsSemiterm LAct 0 (^&(iq + 1) : V) := by simp
  have hiq1E : termLen LAct (^&(iq + 1) : V) ≤ E := termLen_fvar_succ_le hiq
  have hid0 : IsSemiterm LAct 0 (^&id : V) := by simp
  have hidE : termLen LAct (^&id : V) ≤ E := termLen_fvar_le (le_trans (by gcongr; norm_num) hid)
  have hid1 : IsSemiterm LAct 0 (^&(id + 1) : V) := by simp
  have hid1E : termLen LAct (^&(id + 1) : V) ≤ E := termLen_fvar_succ_le hid
  have hicq0 : IsSemiterm LAct 0 (^&icq : V) := by simp
  have hicqE : termLen LAct (^&icq : V) ≤ E := termLen_fvar_le (le_trans (by gcongr; norm_num) hicq)
  have hicq1 : IsSemiterm LAct 0 (^&(icq + 1) : V) := by simp
  have hicq1E : termLen LAct (^&(icq + 1) : V) ≤ E := termLen_fvar_succ_le hicq
  have hic0 : IsSemiterm LAct 0 (^&ic : V) := by simp
  have hicE : termLen LAct (^&ic : V) ≤ E := termLen_fvar_le (le_trans (by gcongr; norm_num) hic)
  have hic1 : IsSemiterm LAct 0 (^&(ic + 1) : V) := by simp
  have hic1E : termLen LAct (^&(ic + 1) : V) ≤ E := termLen_fvar_succ_le hic
  have hin₁0 : IsSemiterm LAct 0 (^&in₁ : V) := by simp
  have hin₁E : termLen LAct (^&in₁ : V) ≤ E := termLen_fvar_le (le_trans (by gcongr; norm_num) hin₁)
  have hin₁1 : IsSemiterm LAct 0 (^&(in₁ + 1) : V) := by simp
  have hin₁1E : termLen LAct (^&(in₁ + 1) : V) ≤ E := termLen_fvar_succ_le hin₁
  have hf0 : IsSemiterm LAct 0 (^&0 : V) := by simp
  have hf0E : termLen LAct (^&0 : V) ≤ E :=
    termLen_fvar_le (by rw [zero_add]; exact le_trans (by norm_num) (le_trans le_add_self his))
  obtain ⟨ok₁, tg₁, cx₁⟩ := fok_totOrIntro htbl hF hWp hΓ his0 hisE hip0 hipE hiq0 hiqE hid0 hidE
  rw [termShift_fvar, termShift_fvar, termShift_fvar, termShift_fvar, Nat.cast_zero] at cx₁
  set F := neg LAct (orIntroFact (^&0 : V) (^&(is + 1)) (^&(ip + 1)) (^&(iq + 1)) (^&(id + 1))) with hFdef
  set Γ₁ := insert F (setShift LAct Γ) with hΓ₁def
  have hΓ₁ : IsFormulaSet LAct Γ₁ := cx₁ ▸ isFormulaSet_ctxAfter 8 htbl ok₁
  have tor : neg LAct (orFact (^&(ir + 1)) (^&(ip + 1)) (^&(iq + 1))) ∈ Γ₁ := by
    have := mem_shift_insert (f := F) hor
    rwa [shift_neg (isFormula_orFact hir0 hip0 hiq0), shift_orFact hir0 hip0 hiq0, termShift_fvar, termShift_fvar, termShift_fvar] at this
  have tmr : neg LAct (memFact (^&(ir + 1)) (^&(is + 1))) ∈ Γ₁ := by
    have := mem_shift_insert (f := F) hmr
    rwa [shift_neg (isFormula_memFact hir0 his0), shift_memFact hir0 his0, termShift_fvar, termShift_fvar] at this
  have tf : neg LAct (fstIdxFact (^&(ic + 1)) (^&(id + 1))) ∈ Γ₁ := by
    have := mem_shift_insert (f := F) hf
    rwa [shift_neg (isFormula_fstIdxFact hic0 hid0), shift_fstIdxFact hic0 hid0, termShift_fvar, termShift_fvar] at this
  have tiq : neg LAct (insFact (^&(icq + 1)) (^&(iq + 1)) (^&(is + 1))) ∈ Γ₁ := by
    have := mem_shift_insert (f := F) hiq'
    rwa [shift_neg (isFormula_insFact hicq0 hiq0 his0), shift_insFact hicq0 hiq0 his0, termShift_fvar, termShift_fvar, termShift_fvar] at this
  have tip : neg LAct (insFact (^&(ic + 1)) (^&(ip + 1)) (^&(icq + 1))) ∈ Γ₁ := by
    have := mem_shift_insert (f := F) hip'
    rwa [shift_neg (isFormula_insFact hic0 hip0 hicq0), shift_insFact hic0 hip0 hicq0, termShift_fvar, termShift_fvar, termShift_fvar] at this
  have td : neg LAct (derFact (^&(id + 1) : V)) ∈ Γ₁ := by
    have := mem_shift_insert (f := F) hd
    rwa [shift_neg (isFormula_derFact hid0), shift_derFact hid0, termShift_fvar] at this
  have tn₁ : neg LAct (dlenFact (^&(id + 1) : V) (^&(in₁ + 1))) ∈ Γ₁ := by
    have := mem_shift_insert (f := F) hn₁
    rwa [shift_neg (isFormula_dlenFact hid0 hin₁0), shift_dlenFact hid0 hin₁0, termShift_fvar, termShift_fvar] at this
  have tsl : neg LAct (setLenFact (^&(il + 1)) (^&(is + 1))) ∈ Γ₁ := by
    have := mem_shift_insert (f := F) hsl
    rwa [shift_neg (isFormula_setLenFact hil0 his0), shift_setLenFact hil0 his0, termShift_fvar, termShift_fvar] at this
  obtain ⟨ok₂, tg₂, cx₂⟩ := fok_fstIdxOr htbl hF hWp hΓ₁ his1 his1E hip1 hip1E hiq1 hiq1E hid1 hid1E hf0 hf0E
    (by rw [hΓ₁def, hFdef]; simp)
  set Γ₂ := insert (neg LAct (fstIdxFact (^&(is + 1)) (^&0))) Γ₁ with hΓ₂def
  have hΓ₂ : IsFormulaSet LAct Γ₂ := cx₂ ▸ isFormulaSet_ctxAfter 8 htbl ok₂
  obtain ⟨ok₃, tg₃, cx₃⟩ := fok_introOr htbl hF hWp hΓ₂ his1 his1E hip1 hip1E hiq1 hiq1E hid1 hid1E hir1 hir1E
    hicq1 hicq1E hic1 hic1E hf0 hf0E
    (by rw [hΓ₂def, hΓ₁def, hFdef]; simp) (by rw [hΓ₂def]; simp [tor]) (by rw [hΓ₂def]; simp [tmr])
    (by rw [hΓ₂def]; simp [tf]) (by rw [hΓ₂def]; simp [tiq]) (by rw [hΓ₂def]; simp [tip]) (by rw [hΓ₂def]; simp [td])
  set Γ₃ := insert (neg LAct (derFact (^&0 : V))) Γ₂ with hΓ₃def
  have hΓ₃ : IsFormulaSet LAct Γ₃ := cx₃ ▸ isFormulaSet_ctxAfter 8 htbl ok₃
  obtain ⟨ok₄, tg₄, cx₄⟩ := fok_dlenOr htbl hF hWp hΓ₃ hf0 hf0E his1 his1E hip1 hip1E hiq1 hiq1E hid1 hid1E
    hin₁1 hin₁1E hil1 hil1E
    (by rw [hΓ₃def, hΓ₂def, hΓ₁def, hFdef]; simp) (by rw [hΓ₃def, hΓ₂def]; simp [tn₁])
    (by rw [hΓ₃def, hΓ₂def]; simp [tsl])
  have hfin : finalCtx Γ (nodeOrHead W is il ir ip iq id icq ic in₁) = nodeOrHeadCtx Γ is il ip iq id in₁ := by
    unfold nodeOrHead
    rw [finalCtx_cons, cx₁, finalCtx_cons, cx₂, finalCtx_cons, cx₃, finalCtx_single, cx₄]
    rfl
  refine ⟨?_, ?_, ?_, ?_, hfin⟩
  · unfold nodeOrHead
    refine listOK_cons ok₁ ?_
    rw [cx₁]
    refine listOK_cons ok₂ ?_
    rw [cx₂]
    refine listOK_cons ok₃ ?_
    rw [cx₃]
    exact listOK_single ok₄
  · unfold nodeOrHead
    exact noDrop'_cons (by rw [tg₁]; simp) (noDrop'_cons (by rw [tg₂]; simp)
      (noDrop'_cons (by rw [tg₃]; simp) (noDrop'_single (by rw [tg₄]; simp))))
  · unfold nodeOrHead
    rw [shiftsV_cons, shiftsV_cons, shiftsV_cons, shiftsV_single, tg₁, tg₂, tg₃, tg₄]
    simp
  · unfold nodeOrHead; simp [len_adjoin]; norm_num

/-- **`nodeOr` is applicable**. -/
theorem nodeOr_ok {tbl N E Γ W tblN N' B' is il ir ip iq id icq ic in₁ L m₁ n : V}
    (htbl : TableOK tbl N) (hF : Frag1Table tbl) (hWp : W = frag1Pieces) (htblN : NumTableOK tblN N' B')
    (hΓ : IsFormulaSet LAct Γ)
    (his : is + 2 ≤ E) (hir : ir + 2 ≤ E) (hip : ip + 2 ≤ E) (hiq : iq + 2 ≤ E)
    (hid : id + 2 ≤ E) (hicq : icq + 2 ≤ E) (hic : ic + 2 ≤ E)
    (hT : il + in₁ + 7 ≤ E) (hn : 18 * ‖n‖ + 7 ≤ E) (hLn : L + m₁ + 1 ≤ n)
    (hor : neg LAct (orFact (^&ir) (^&ip) (^&iq)) ∈ Γ) (hmr : neg LAct (memFact (^&ir) (^&is)) ∈ Γ)
    (hf : neg LAct (fstIdxFact (^&ic) (^&id)) ∈ Γ) (hiq' : neg LAct (insFact (^&icq) (^&iq) (^&is)) ∈ Γ)
    (hip' : neg LAct (insFact (^&ic) (^&ip) (^&icq)) ∈ Γ)
    (hd : neg LAct (derFact (^&id : V)) ∈ Γ) (hn₁ : neg LAct (dlenFact (^&id : V) (^&in₁)) ∈ Γ)
    (hle₁ : neg LAct (leFact (^&in₁) (bnum m₁)) ∈ Γ)
    (hsl : neg LAct (setLenFact (^&il) (^&is)) ∈ Γ) (hle : neg LAct (leFact (^&il) (bnum L)) ∈ Γ) :
    ListOK tbl E ((8 : ℕ) : V) Γ (nodeOr W tblN is il ir ip iq id icq ic in₁ L m₁ n) ∧
    NoDrop' (nodeOr W tblN is il ir ip iq id icq ic in₁ L m₁ n) ∧
    shiftsV (nodeOr W tblN is il ir ip iq id icq ic in₁ L m₁ n) = 1 ∧
    len (nodeOr W tblN is il ir ip iq id icq ic in₁ L m₁ n) = 9 ∧
    neg LAct (goalFact (^&(is + 1)) (bnum n)) ∈ finalCtx Γ (nodeOr W tblN is il ir ip iq id icq ic in₁ L m₁ n) := by
  have hil : il + 2 ≤ E := le_trans (add_le_add le_self_add (by norm_num)) hT
  have hin₁ : in₁ + 2 ≤ E := le_trans (add_le_add le_add_self (by norm_num)) hT
  obtain ⟨hok, hnd, hsv, hlen, hfin⟩ := nodeOrHead_ok htbl hF hWp hΓ his hil hir hip hiq hid hicq hic hin₁
    hor hmr hf hiq' hip' hd hn₁ hsl
  have hΓ' : IsFormulaSet LAct (finalCtx Γ (nodeOrHead W is il ir ip iq id icq ic in₁)) :=
    finalCtx_isFormulaSet 8 htbl hΓ hok
  have hl0 : IsSemiterm LAct 0 (^&il : V) := by simp
  have hn10 : IsSemiterm LAct 0 (^&in₁ : V) := by simp
  have hbL : IsSemiterm LAct 0 (bnum L) := isSemiterm_bnum_LAct 0 L
  have hbm₁ : IsSemiterm LAct 0 (bnum m₁) := isSemiterm_bnum_LAct 0 m₁
  have tr : ∀ x ∈ Γ, shift LAct x ∈ finalCtx Γ (nodeOrHead W is il ir ip iq id icq ic in₁) := by
    intro x hx; rw [hfin]; unfold nodeOrHeadCtx; exact shift_mem_head3 hx
  have hle' : neg LAct (leFact (^&(il + 1)) (bnum L)) ∈ finalCtx Γ (nodeOrHead W is il ir ip iq id icq ic in₁) := by
    have := tr _ hle
    rwa [shift_neg (isFormula_leFact hl0 hbL), shift_leFact hl0 hbL, termShift_fvar, termShift_bnum] at this
  have hle₁' : neg LAct (leFact (^&(in₁ + 1)) (bnum m₁)) ∈ finalCtx Γ (nodeOrHead W is il ir ip iq id icq ic in₁) := by
    have := tr _ hle₁
    rwa [shift_neg (isFormula_leFact hn10 hbm₁), shift_leFact hn10 hbm₁, termShift_fvar, termShift_bnum] at this
  obtain ⟨tok, tnd, tsv, tlen, tfin, tmem⟩ := goalTailUnary_ok htbl hF hWp htblN hΓ'
    (by rw [show il + 1 + (in₁ + 1) + 5 = il + in₁ + 7 by ring]; exact hT)
    (by rw [add_assoc, one_add_one_eq_two]; exact his) hn hLn hle' hle₁'
    (by rw [hfin]; unfold nodeOrHeadCtx; simp) (by rw [hfin]; unfold nodeOrHeadCtx; simp)
    (by rw [hfin]; unfold nodeOrHeadCtx; simp)
  refine ⟨listOK_appendV hok tok, noDrop'_appendV hnd tnd, ?_, ?_, ?_⟩
  · unfold nodeOr; rw [shiftsV_appendV, hsv, tsv, add_zero]
  · unfold nodeOr; rw [len_appendV, hlen, tlen]; norm_num
  · unfold nodeOr; rw [finalCtx_appendV]; exact tmem

/-! ### 4.3 `wkRule` (the child's sequent object `c` at `ic`, `c ⊆ s`) -/

noncomputable def nodeWkHead (W is il ic id in₁ : V) : V :=
  mkStep W 91 ?[^&is, ^&id] ∷ mkStep W 120 ?[^&(is + 1), ^&(id + 1), ^&0] ∷
  mkStep W 97 ?[^&(is + 1), ^&(id + 1), ^&(ic + 1), ^&0] ∷
  mkStep W 103 ?[^&0, ^&(is + 1), ^&(id + 1), ^&(in₁ + 1), ^&(il + 1)] ∷ (0 : V)

/-- **The `wkRule` node fragment**. -/
noncomputable def nodeWk (W tblN is il ic id in₁ L m₁ n : V) : V :=
  appendV (nodeWkHead W is il ic id in₁) (goalTailUnary W tblN (il + 1) (in₁ + 1) L m₁ n (is + 1))

noncomputable def nodeWkHeadCtx (Γ is il id in₁ : V) : V :=
  insert (neg LAct (dlenFact (^&0 : V) (unaryT (il + 1) (in₁ + 1))))
    (insert (neg LAct (derFact (^&0 : V)))
      (insert (neg LAct (fstIdxFact (^&(is + 1)) (^&0)))
        (insert (neg LAct (wkRuleFact (^&0 : V) (^&(is + 1)) (^&(id + 1)))) (setShift LAct Γ))))

theorem nodeWkHead_ok {tbl N E Γ W is il ic id in₁ : V} (htbl : TableOK tbl N)
    (hF : Frag1Table tbl) (hWp : W = frag1Pieces) (hΓ : IsFormulaSet LAct Γ)
    (his : is + 2 ≤ E) (hil : il + 2 ≤ E) (hic : ic + 2 ≤ E) (hid : id + 2 ≤ E) (hin₁ : in₁ + 2 ≤ E)
    (hfs : neg LAct (fsetPiFact (^&is)) ∈ Γ) (hf : neg LAct (fstIdxFact (^&ic) (^&id)) ∈ Γ)
    (hsub : neg LAct (subsetFact (^&ic) (^&is)) ∈ Γ)
    (hd : neg LAct (derFact (^&id : V)) ∈ Γ) (hn₁ : neg LAct (dlenFact (^&id : V) (^&in₁)) ∈ Γ)
    (hsl : neg LAct (setLenFact (^&il) (^&is)) ∈ Γ) :
    ListOK tbl E ((8 : ℕ) : V) Γ (nodeWkHead W is il ic id in₁) ∧ NoDrop' (nodeWkHead W is il ic id in₁) ∧
    shiftsV (nodeWkHead W is il ic id in₁) = 1 ∧ len (nodeWkHead W is il ic id in₁) = 4 ∧
    finalCtx Γ (nodeWkHead W is il ic id in₁) = nodeWkHeadCtx Γ is il id in₁ := by
  have his0 : IsSemiterm LAct 0 (^&is : V) := by simp
  have hisE : termLen LAct (^&is : V) ≤ E := termLen_fvar_le (le_trans (by gcongr; norm_num) his)
  have his1 : IsSemiterm LAct 0 (^&(is + 1) : V) := by simp
  have his1E : termLen LAct (^&(is + 1) : V) ≤ E := termLen_fvar_succ_le his
  have hil0 : IsSemiterm LAct 0 (^&il : V) := by simp
  have hilE : termLen LAct (^&il : V) ≤ E := termLen_fvar_le (le_trans (by gcongr; norm_num) hil)
  have hil1 : IsSemiterm LAct 0 (^&(il + 1) : V) := by simp
  have hil1E : termLen LAct (^&(il + 1) : V) ≤ E := termLen_fvar_succ_le hil
  have hic0 : IsSemiterm LAct 0 (^&ic : V) := by simp
  have hicE : termLen LAct (^&ic : V) ≤ E := termLen_fvar_le (le_trans (by gcongr; norm_num) hic)
  have hic1 : IsSemiterm LAct 0 (^&(ic + 1) : V) := by simp
  have hic1E : termLen LAct (^&(ic + 1) : V) ≤ E := termLen_fvar_succ_le hic
  have hid0 : IsSemiterm LAct 0 (^&id : V) := by simp
  have hidE : termLen LAct (^&id : V) ≤ E := termLen_fvar_le (le_trans (by gcongr; norm_num) hid)
  have hid1 : IsSemiterm LAct 0 (^&(id + 1) : V) := by simp
  have hid1E : termLen LAct (^&(id + 1) : V) ≤ E := termLen_fvar_succ_le hid
  have hin₁0 : IsSemiterm LAct 0 (^&in₁ : V) := by simp
  have hin₁E : termLen LAct (^&in₁ : V) ≤ E := termLen_fvar_le (le_trans (by gcongr; norm_num) hin₁)
  have hin₁1 : IsSemiterm LAct 0 (^&(in₁ + 1) : V) := by simp
  have hin₁1E : termLen LAct (^&(in₁ + 1) : V) ≤ E := termLen_fvar_succ_le hin₁
  have hf0 : IsSemiterm LAct 0 (^&0 : V) := by simp
  have hf0E : termLen LAct (^&0 : V) ≤ E :=
    termLen_fvar_le (by rw [zero_add]; exact le_trans (by norm_num) (le_trans le_add_self his))
  obtain ⟨ok₁, tg₁, cx₁⟩ := fok_totWkRule htbl hF hWp hΓ his0 hisE hid0 hidE
  rw [termShift_fvar, termShift_fvar, Nat.cast_zero] at cx₁
  set F := neg LAct (wkRuleFact (^&0 : V) (^&(is + 1)) (^&(id + 1))) with hFdef
  set Γ₁ := insert F (setShift LAct Γ) with hΓ₁def
  have hΓ₁ : IsFormulaSet LAct Γ₁ := cx₁ ▸ isFormulaSet_ctxAfter 8 htbl ok₁
  have tfs : neg LAct (fsetPiFact (^&(is + 1))) ∈ Γ₁ := by
    have := mem_shift_insert (f := F) hfs
    rwa [shift_neg (isFormula_fsetPiFact his0), shift_fsetPiFact his0, termShift_fvar] at this
  have tf : neg LAct (fstIdxFact (^&(ic + 1)) (^&(id + 1))) ∈ Γ₁ := by
    have := mem_shift_insert (f := F) hf
    rwa [shift_neg (isFormula_fstIdxFact hic0 hid0), shift_fstIdxFact hic0 hid0, termShift_fvar, termShift_fvar] at this
  have tsub : neg LAct (subsetFact (^&(ic + 1)) (^&(is + 1))) ∈ Γ₁ := by
    have := mem_shift_insert (f := F) hsub
    rwa [shift_neg (isFormula_subsetFact hic0 his0), shift_subsetFact hic0 his0, termShift_fvar, termShift_fvar] at this
  have td : neg LAct (derFact (^&(id + 1) : V)) ∈ Γ₁ := by
    have := mem_shift_insert (f := F) hd
    rwa [shift_neg (isFormula_derFact hid0), shift_derFact hid0, termShift_fvar] at this
  have tn₁ : neg LAct (dlenFact (^&(id + 1) : V) (^&(in₁ + 1))) ∈ Γ₁ := by
    have := mem_shift_insert (f := F) hn₁
    rwa [shift_neg (isFormula_dlenFact hid0 hin₁0), shift_dlenFact hid0 hin₁0, termShift_fvar, termShift_fvar] at this
  have tsl : neg LAct (setLenFact (^&(il + 1)) (^&(is + 1))) ∈ Γ₁ := by
    have := mem_shift_insert (f := F) hsl
    rwa [shift_neg (isFormula_setLenFact hil0 his0), shift_setLenFact hil0 his0, termShift_fvar, termShift_fvar] at this
  obtain ⟨ok₂, tg₂, cx₂⟩ := fok_fstIdxWk htbl hF hWp hΓ₁ his1 his1E hid1 hid1E hf0 hf0E (by rw [hΓ₁def, hFdef]; simp)
  set Γ₂ := insert (neg LAct (fstIdxFact (^&(is + 1)) (^&0))) Γ₁ with hΓ₂def
  have hΓ₂ : IsFormulaSet LAct Γ₂ := cx₂ ▸ isFormulaSet_ctxAfter 8 htbl ok₂
  obtain ⟨ok₃, tg₃, cx₃⟩ := fok_introWk htbl hF hWp hΓ₂ his1 his1E hid1 hid1E hic1 hic1E hf0 hf0E
    (by rw [hΓ₂def]; simp [tfs]) (by rw [hΓ₂def]; simp [tf]) (by rw [hΓ₂def]; simp [tsub])
    (by rw [hΓ₂def]; simp [td]) (by rw [hΓ₂def, hΓ₁def, hFdef]; simp)
  set Γ₃ := insert (neg LAct (derFact (^&0 : V))) Γ₂ with hΓ₃def
  have hΓ₃ : IsFormulaSet LAct Γ₃ := cx₃ ▸ isFormulaSet_ctxAfter 8 htbl ok₃
  obtain ⟨ok₄, tg₄, cx₄⟩ := fok_dlenWk htbl hF hWp hΓ₃ hf0 hf0E his1 his1E hid1 hid1E hin₁1 hin₁1E hil1 hil1E
    (by rw [hΓ₃def, hΓ₂def, hΓ₁def, hFdef]; simp) (by rw [hΓ₃def, hΓ₂def]; simp [tn₁])
    (by rw [hΓ₃def, hΓ₂def]; simp [tsl])
  have hfin : finalCtx Γ (nodeWkHead W is il ic id in₁) = nodeWkHeadCtx Γ is il id in₁ := by
    unfold nodeWkHead
    rw [finalCtx_cons, cx₁, finalCtx_cons, cx₂, finalCtx_cons, cx₃, finalCtx_single, cx₄]
    rfl
  refine ⟨?_, ?_, ?_, ?_, hfin⟩
  · unfold nodeWkHead
    refine listOK_cons ok₁ ?_
    rw [cx₁]
    refine listOK_cons ok₂ ?_
    rw [cx₂]
    refine listOK_cons ok₃ ?_
    rw [cx₃]
    exact listOK_single ok₄
  · unfold nodeWkHead
    exact noDrop'_cons (by rw [tg₁]; simp) (noDrop'_cons (by rw [tg₂]; simp)
      (noDrop'_cons (by rw [tg₃]; simp) (noDrop'_single (by rw [tg₄]; simp))))
  · unfold nodeWkHead
    rw [shiftsV_cons, shiftsV_cons, shiftsV_cons, shiftsV_single, tg₁, tg₂, tg₃, tg₄]
    simp
  · unfold nodeWkHead; simp [len_adjoin]; norm_num

/-- **`nodeWk` is applicable**. -/
theorem nodeWk_ok {tbl N E Γ W tblN N' B' is il ic id in₁ L m₁ n : V}
    (htbl : TableOK tbl N) (hF : Frag1Table tbl) (hWp : W = frag1Pieces) (htblN : NumTableOK tblN N' B')
    (hΓ : IsFormulaSet LAct Γ)
    (his : is + 2 ≤ E) (hic : ic + 2 ≤ E) (hid : id + 2 ≤ E)
    (hT : il + in₁ + 7 ≤ E) (hn : 18 * ‖n‖ + 7 ≤ E) (hLn : L + m₁ + 1 ≤ n)
    (hfs : neg LAct (fsetPiFact (^&is)) ∈ Γ) (hf : neg LAct (fstIdxFact (^&ic) (^&id)) ∈ Γ)
    (hsub : neg LAct (subsetFact (^&ic) (^&is)) ∈ Γ)
    (hd : neg LAct (derFact (^&id : V)) ∈ Γ) (hn₁ : neg LAct (dlenFact (^&id : V) (^&in₁)) ∈ Γ)
    (hle₁ : neg LAct (leFact (^&in₁) (bnum m₁)) ∈ Γ)
    (hsl : neg LAct (setLenFact (^&il) (^&is)) ∈ Γ) (hle : neg LAct (leFact (^&il) (bnum L)) ∈ Γ) :
    ListOK tbl E ((8 : ℕ) : V) Γ (nodeWk W tblN is il ic id in₁ L m₁ n) ∧ NoDrop' (nodeWk W tblN is il ic id in₁ L m₁ n) ∧
    shiftsV (nodeWk W tblN is il ic id in₁ L m₁ n) = 1 ∧ len (nodeWk W tblN is il ic id in₁ L m₁ n) = 9 ∧
    neg LAct (goalFact (^&(is + 1)) (bnum n)) ∈ finalCtx Γ (nodeWk W tblN is il ic id in₁ L m₁ n) := by
  have hil : il + 2 ≤ E := le_trans (add_le_add le_self_add (by norm_num)) hT
  have hin₁ : in₁ + 2 ≤ E := le_trans (add_le_add le_add_self (by norm_num)) hT
  obtain ⟨hok, hnd, hsv, hlen, hfin⟩ := nodeWkHead_ok htbl hF hWp hΓ his hil hic hid hin₁ hfs hf hsub hd hn₁ hsl
  have hΓ' : IsFormulaSet LAct (finalCtx Γ (nodeWkHead W is il ic id in₁)) := finalCtx_isFormulaSet 8 htbl hΓ hok
  have hl0 : IsSemiterm LAct 0 (^&il : V) := by simp
  have hn10 : IsSemiterm LAct 0 (^&in₁ : V) := by simp
  have hbL : IsSemiterm LAct 0 (bnum L) := isSemiterm_bnum_LAct 0 L
  have hbm₁ : IsSemiterm LAct 0 (bnum m₁) := isSemiterm_bnum_LAct 0 m₁
  have tr : ∀ x ∈ Γ, shift LAct x ∈ finalCtx Γ (nodeWkHead W is il ic id in₁) := by
    intro x hx; rw [hfin]; unfold nodeWkHeadCtx; exact shift_mem_head3 hx
  have hle' : neg LAct (leFact (^&(il + 1)) (bnum L)) ∈ finalCtx Γ (nodeWkHead W is il ic id in₁) := by
    have := tr _ hle
    rwa [shift_neg (isFormula_leFact hl0 hbL), shift_leFact hl0 hbL, termShift_fvar, termShift_bnum] at this
  have hle₁' : neg LAct (leFact (^&(in₁ + 1)) (bnum m₁)) ∈ finalCtx Γ (nodeWkHead W is il ic id in₁) := by
    have := tr _ hle₁
    rwa [shift_neg (isFormula_leFact hn10 hbm₁), shift_leFact hn10 hbm₁, termShift_fvar, termShift_bnum] at this
  obtain ⟨tok, tnd, tsv, tlen, tfin, tmem⟩ := goalTailUnary_ok htbl hF hWp htblN hΓ'
    (by rw [show il + 1 + (in₁ + 1) + 5 = il + in₁ + 7 by ring]; exact hT)
    (by rw [add_assoc, one_add_one_eq_two]; exact his) hn hLn hle' hle₁'
    (by rw [hfin]; unfold nodeWkHeadCtx; simp) (by rw [hfin]; unfold nodeWkHeadCtx; simp)
    (by rw [hfin]; unfold nodeWkHeadCtx; simp)
  refine ⟨listOK_appendV hok tok, noDrop'_appendV hnd tnd, ?_, ?_, ?_⟩
  · unfold nodeWk; rw [shiftsV_appendV, hsv, tsv, add_zero]
  · unfold nodeWk; rw [len_appendV, hlen, tlen]; norm_num
  · unfold nodeWk; rw [finalCtx_appendV]; exact tmem

/-! ### 4.4 `cutRule` (the cut formula `p` at `ip`, `neg p` at `inp`; `c₁ = insert p s` at `ic₁`, `c₂ = insert (neg p) s` at `ic₂`) -/

noncomputable def nodeCutHead (W is il ip inp id₁ id₂ ic₁ ic₂ in₁ in₂ : V) : V :=
  mkStep W 92 ?[^&is, ^&ip, ^&id₁, ^&id₂] ∷
  mkStep W 121 ?[^&(is + 1), ^&(ip + 1), ^&(id₁ + 1), ^&(id₂ + 1), ^&0] ∷
  mkStep W 98 ?[(𝟎 : V), ^&(is + 1), ^&(ip + 1), ^&(id₁ + 1), ^&(id₂ + 1), ^&(ic₁ + 1), ^&(inp + 1), ^&(ic₂ + 1), ^&0] ∷
  mkStep W 104 ?[^&0, ^&(is + 1), ^&(ip + 1), ^&(id₁ + 1), ^&(id₂ + 1), ^&(in₁ + 1), ^&(in₂ + 1), ^&(il + 1)] ∷ (0 : V)

/-- **The `cutRule` node fragment**. -/
noncomputable def nodeCut (W tblN is il ip inp id₁ id₂ ic₁ ic₂ in₁ in₂ L m₁ m₂ n : V) : V :=
  appendV (nodeCutHead W is il ip inp id₁ id₂ ic₁ ic₂ in₁ in₂)
    (goalTailBinary W tblN (il + 1) (in₁ + 1) (in₂ + 1) L m₁ m₂ n (is + 1))

noncomputable def nodeCutHeadCtx (Γ is il ip id₁ id₂ in₁ in₂ : V) : V :=
  insert (neg LAct (dlenFact (^&0 : V) (binaryT (il + 1) (in₁ + 1) (in₂ + 1))))
    (insert (neg LAct (derFact (^&0 : V)))
      (insert (neg LAct (fstIdxFact (^&(is + 1)) (^&0)))
        (insert (neg LAct (cutRuleFact (^&0 : V) (^&(is + 1)) (^&(ip + 1)) (^&(id₁ + 1)) (^&(id₂ + 1))))
          (setShift LAct Γ))))

theorem nodeCutHead_ok {tbl N E Γ W is il ip inp id₁ id₂ ic₁ ic₂ in₁ in₂ : V} (htbl : TableOK tbl N)
    (hF : Frag1Table tbl) (hWp : W = frag1Pieces) (hΓ : IsFormulaSet LAct Γ)
    (his : is + 2 ≤ E) (hil : il + 2 ≤ E) (hip : ip + 2 ≤ E) (hinp : inp + 2 ≤ E)
    (hid₁ : id₁ + 2 ≤ E) (hid₂ : id₂ + 2 ≤ E) (hic₁ : ic₁ + 2 ≤ E) (hic₂ : ic₂ + 2 ≤ E)
    (hin₁ : in₁ + 2 ≤ E) (hin₂ : in₂ + 2 ≤ E)
    (hf₁ : neg LAct (fstIdxFact (^&ic₁) (^&id₁)) ∈ Γ) (hi₁ : neg LAct (insFact (^&ic₁) (^&ip) (^&is)) ∈ Γ)
    (hd₁ : neg LAct (derFact (^&id₁ : V)) ∈ Γ) (hn₁ : neg LAct (dlenFact (^&id₁ : V) (^&in₁)) ∈ Γ)
    (hf₂ : neg LAct (fstIdxFact (^&ic₂) (^&id₂)) ∈ Γ) (hneg : neg LAct (negFact (^&inp) (^&ip)) ∈ Γ)
    (hi₂ : neg LAct (insFact (^&ic₂) (^&inp) (^&is)) ∈ Γ)
    (hd₂ : neg LAct (derFact (^&id₂ : V)) ∈ Γ) (hn₂ : neg LAct (dlenFact (^&id₂ : V) (^&in₂)) ∈ Γ)
    (hsl : neg LAct (setLenFact (^&il) (^&is)) ∈ Γ) :
    ListOK tbl E ((9 : ℕ) : V) Γ (nodeCutHead W is il ip inp id₁ id₂ ic₁ ic₂ in₁ in₂) ∧
    NoDrop' (nodeCutHead W is il ip inp id₁ id₂ ic₁ ic₂ in₁ in₂) ∧
    shiftsV (nodeCutHead W is il ip inp id₁ id₂ ic₁ ic₂ in₁ in₂) = 1 ∧
    len (nodeCutHead W is il ip inp id₁ id₂ ic₁ ic₂ in₁ in₂) = 4 ∧
    finalCtx Γ (nodeCutHead W is il ip inp id₁ id₂ ic₁ ic₂ in₁ in₂) = nodeCutHeadCtx Γ is il ip id₁ id₂ in₁ in₂ := by
  have h89 : ((8 : ℕ) : V) ≤ ((9 : ℕ) : V) := by exact_mod_cast (by decide : (8 : ℕ) ≤ 9)
  have his0 : IsSemiterm LAct 0 (^&is : V) := by simp
  have hisE : termLen LAct (^&is : V) ≤ E := termLen_fvar_le (le_trans (by gcongr; norm_num) his)
  have his1 : IsSemiterm LAct 0 (^&(is + 1) : V) := by simp
  have his1E : termLen LAct (^&(is + 1) : V) ≤ E := termLen_fvar_succ_le his
  have hil0 : IsSemiterm LAct 0 (^&il : V) := by simp
  have hilE : termLen LAct (^&il : V) ≤ E := termLen_fvar_le (le_trans (by gcongr; norm_num) hil)
  have hil1 : IsSemiterm LAct 0 (^&(il + 1) : V) := by simp
  have hil1E : termLen LAct (^&(il + 1) : V) ≤ E := termLen_fvar_succ_le hil
  have hip0 : IsSemiterm LAct 0 (^&ip : V) := by simp
  have hipE : termLen LAct (^&ip : V) ≤ E := termLen_fvar_le (le_trans (by gcongr; norm_num) hip)
  have hip1 : IsSemiterm LAct 0 (^&(ip + 1) : V) := by simp
  have hip1E : termLen LAct (^&(ip + 1) : V) ≤ E := termLen_fvar_succ_le hip
  have hinp0 : IsSemiterm LAct 0 (^&inp : V) := by simp
  have hinpE : termLen LAct (^&inp : V) ≤ E := termLen_fvar_le (le_trans (by gcongr; norm_num) hinp)
  have hinp1 : IsSemiterm LAct 0 (^&(inp + 1) : V) := by simp
  have hinp1E : termLen LAct (^&(inp + 1) : V) ≤ E := termLen_fvar_succ_le hinp
  have hid₁0 : IsSemiterm LAct 0 (^&id₁ : V) := by simp
  have hid₁E : termLen LAct (^&id₁ : V) ≤ E := termLen_fvar_le (le_trans (by gcongr; norm_num) hid₁)
  have hid₁1 : IsSemiterm LAct 0 (^&(id₁ + 1) : V) := by simp
  have hid₁1E : termLen LAct (^&(id₁ + 1) : V) ≤ E := termLen_fvar_succ_le hid₁
  have hid₂0 : IsSemiterm LAct 0 (^&id₂ : V) := by simp
  have hid₂E : termLen LAct (^&id₂ : V) ≤ E := termLen_fvar_le (le_trans (by gcongr; norm_num) hid₂)
  have hid₂1 : IsSemiterm LAct 0 (^&(id₂ + 1) : V) := by simp
  have hid₂1E : termLen LAct (^&(id₂ + 1) : V) ≤ E := termLen_fvar_succ_le hid₂
  have hic₁0 : IsSemiterm LAct 0 (^&ic₁ : V) := by simp
  have hic₁E : termLen LAct (^&ic₁ : V) ≤ E := termLen_fvar_le (le_trans (by gcongr; norm_num) hic₁)
  have hic₁1 : IsSemiterm LAct 0 (^&(ic₁ + 1) : V) := by simp
  have hic₁1E : termLen LAct (^&(ic₁ + 1) : V) ≤ E := termLen_fvar_succ_le hic₁
  have hic₂0 : IsSemiterm LAct 0 (^&ic₂ : V) := by simp
  have hic₂E : termLen LAct (^&ic₂ : V) ≤ E := termLen_fvar_le (le_trans (by gcongr; norm_num) hic₂)
  have hic₂1 : IsSemiterm LAct 0 (^&(ic₂ + 1) : V) := by simp
  have hic₂1E : termLen LAct (^&(ic₂ + 1) : V) ≤ E := termLen_fvar_succ_le hic₂
  have hin₁0 : IsSemiterm LAct 0 (^&in₁ : V) := by simp
  have hin₁E : termLen LAct (^&in₁ : V) ≤ E := termLen_fvar_le (le_trans (by gcongr; norm_num) hin₁)
  have hin₁1 : IsSemiterm LAct 0 (^&(in₁ + 1) : V) := by simp
  have hin₁1E : termLen LAct (^&(in₁ + 1) : V) ≤ E := termLen_fvar_succ_le hin₁
  have hin₂0 : IsSemiterm LAct 0 (^&in₂ : V) := by simp
  have hin₂E : termLen LAct (^&in₂ : V) ≤ E := termLen_fvar_le (le_trans (by gcongr; norm_num) hin₂)
  have hin₂1 : IsSemiterm LAct 0 (^&(in₂ + 1) : V) := by simp
  have hin₂1E : termLen LAct (^&(in₂ + 1) : V) ≤ E := termLen_fvar_succ_le hin₂
  have hf0 : IsSemiterm LAct 0 (^&0 : V) := by simp
  have hf0E : termLen LAct (^&0 : V) ≤ E :=
    termLen_fvar_le (by rw [zero_add]; exact le_trans (by norm_num) (le_trans le_add_self his))
  have hx0 : IsSemiterm LAct 0 (𝟎 : V) := isSemiterm_qqZero_LAct 0
  have hxE : termLen LAct (𝟎 : V) ≤ E := by
    rw [termLen_qqZero isFunc_LAct_zeroIndex]; exact le_trans (by norm_num) (le_trans le_add_self his)
  obtain ⟨ok₁, tg₁, cx₁⟩ := fok_totCutRule htbl hF hWp hΓ his0 hisE hip0 hipE hid₁0 hid₁E hid₂0 hid₂E
  rw [termShift_fvar, termShift_fvar, termShift_fvar, termShift_fvar, Nat.cast_zero] at cx₁
  set F := neg LAct (cutRuleFact (^&0 : V) (^&(is + 1)) (^&(ip + 1)) (^&(id₁ + 1)) (^&(id₂ + 1))) with hFdef
  set Γ₁ := insert F (setShift LAct Γ) with hΓ₁def
  have hΓ₁ : IsFormulaSet LAct Γ₁ := cx₁ ▸ isFormulaSet_ctxAfter 8 htbl ok₁
  have tf₁ : neg LAct (fstIdxFact (^&(ic₁ + 1)) (^&(id₁ + 1))) ∈ Γ₁ := by
    have := mem_shift_insert (f := F) hf₁
    rwa [shift_neg (isFormula_fstIdxFact hic₁0 hid₁0), shift_fstIdxFact hic₁0 hid₁0, termShift_fvar, termShift_fvar] at this
  have ti₁ : neg LAct (insFact (^&(ic₁ + 1)) (^&(ip + 1)) (^&(is + 1))) ∈ Γ₁ := by
    have := mem_shift_insert (f := F) hi₁
    rwa [shift_neg (isFormula_insFact hic₁0 hip0 his0), shift_insFact hic₁0 hip0 his0, termShift_fvar, termShift_fvar, termShift_fvar] at this
  have td₁ : neg LAct (derFact (^&(id₁ + 1) : V)) ∈ Γ₁ := by
    have := mem_shift_insert (f := F) hd₁
    rwa [shift_neg (isFormula_derFact hid₁0), shift_derFact hid₁0, termShift_fvar] at this
  have tn₁ : neg LAct (dlenFact (^&(id₁ + 1) : V) (^&(in₁ + 1))) ∈ Γ₁ := by
    have := mem_shift_insert (f := F) hn₁
    rwa [shift_neg (isFormula_dlenFact hid₁0 hin₁0), shift_dlenFact hid₁0 hin₁0, termShift_fvar, termShift_fvar] at this
  have tf₂ : neg LAct (fstIdxFact (^&(ic₂ + 1)) (^&(id₂ + 1))) ∈ Γ₁ := by
    have := mem_shift_insert (f := F) hf₂
    rwa [shift_neg (isFormula_fstIdxFact hic₂0 hid₂0), shift_fstIdxFact hic₂0 hid₂0, termShift_fvar, termShift_fvar] at this
  have tneg : neg LAct (negFact (^&(inp + 1)) (^&(ip + 1))) ∈ Γ₁ := by
    have := mem_shift_insert (f := F) hneg
    rwa [shift_neg (isFormula_negFact hinp0 hip0), shift_negFact hinp0 hip0, termShift_fvar, termShift_fvar] at this
  have ti₂ : neg LAct (insFact (^&(ic₂ + 1)) (^&(inp + 1)) (^&(is + 1))) ∈ Γ₁ := by
    have := mem_shift_insert (f := F) hi₂
    rwa [shift_neg (isFormula_insFact hic₂0 hinp0 his0), shift_insFact hic₂0 hinp0 his0, termShift_fvar, termShift_fvar, termShift_fvar] at this
  have td₂ : neg LAct (derFact (^&(id₂ + 1) : V)) ∈ Γ₁ := by
    have := mem_shift_insert (f := F) hd₂
    rwa [shift_neg (isFormula_derFact hid₂0), shift_derFact hid₂0, termShift_fvar] at this
  have tn₂ : neg LAct (dlenFact (^&(id₂ + 1) : V) (^&(in₂ + 1))) ∈ Γ₁ := by
    have := mem_shift_insert (f := F) hn₂
    rwa [shift_neg (isFormula_dlenFact hid₂0 hin₂0), shift_dlenFact hid₂0 hin₂0, termShift_fvar, termShift_fvar] at this
  have tsl : neg LAct (setLenFact (^&(il + 1)) (^&(is + 1))) ∈ Γ₁ := by
    have := mem_shift_insert (f := F) hsl
    rwa [shift_neg (isFormula_setLenFact hil0 his0), shift_setLenFact hil0 his0, termShift_fvar, termShift_fvar] at this
  obtain ⟨ok₂, tg₂, cx₂⟩ := fok_fstIdxCut htbl hF hWp hΓ₁ his1 his1E hip1 hip1E hid₁1 hid₁1E hid₂1 hid₂1E hf0 hf0E
    (by rw [hΓ₁def, hFdef]; simp)
  set Γ₂ := insert (neg LAct (fstIdxFact (^&(is + 1)) (^&0))) Γ₁ with hΓ₂def
  have hΓ₂ : IsFormulaSet LAct Γ₂ := cx₂ ▸ isFormulaSet_ctxAfter 8 htbl ok₂
  obtain ⟨ok₃, tg₃, cx₃⟩ := fok_introCut htbl hF hWp hΓ₂ hx0 hxE his1 his1E hip1 hip1E hid₁1 hid₁1E hid₂1 hid₂1E
    hic₁1 hic₁1E hinp1 hinp1E hic₂1 hic₂1E hf0 hf0E
    (by rw [hΓ₂def, hΓ₁def, hFdef]; simp) (by rw [hΓ₂def]; simp [tf₁]) (by rw [hΓ₂def]; simp [ti₁])
    (by rw [hΓ₂def]; simp [td₁]) (by rw [hΓ₂def]; simp [tf₂]) (by rw [hΓ₂def]; simp [tneg])
    (by rw [hΓ₂def]; simp [ti₂]) (by rw [hΓ₂def]; simp [td₂])
  set Γ₃ := insert (neg LAct (derFact (^&0 : V))) Γ₂ with hΓ₃def
  have hΓ₃ : IsFormulaSet LAct Γ₃ := cx₃ ▸ isFormulaSet_ctxAfter 9 htbl ok₃
  obtain ⟨ok₄, tg₄, cx₄⟩ := fok_dlenCut htbl hF hWp hΓ₃ hf0 hf0E his1 his1E hip1 hip1E hid₁1 hid₁1E hid₂1 hid₂1E
    hin₁1 hin₁1E hin₂1 hin₂1E hil1 hil1E
    (by rw [hΓ₃def, hΓ₂def, hΓ₁def, hFdef]; simp) (by rw [hΓ₃def, hΓ₂def]; simp [tn₁])
    (by rw [hΓ₃def, hΓ₂def]; simp [tn₂]) (by rw [hΓ₃def, hΓ₂def]; simp [tsl])
  have hfin : finalCtx Γ (nodeCutHead W is il ip inp id₁ id₂ ic₁ ic₂ in₁ in₂) =
      nodeCutHeadCtx Γ is il ip id₁ id₂ in₁ in₂ := by
    unfold nodeCutHead
    rw [finalCtx_cons, cx₁, finalCtx_cons, cx₂, finalCtx_cons, cx₃, finalCtx_single, cx₄]
    rfl
  refine ⟨?_, ?_, ?_, ?_, hfin⟩
  · unfold nodeCutHead
    refine listOK_cons (ok₁.mono h89) ?_
    rw [cx₁]
    refine listOK_cons (ok₂.mono h89) ?_
    rw [cx₂]
    refine listOK_cons ok₃ ?_
    rw [cx₃]
    exact listOK_single (ok₄.mono h89)
  · unfold nodeCutHead
    exact noDrop'_cons (by rw [tg₁]; simp) (noDrop'_cons (by rw [tg₂]; simp)
      (noDrop'_cons (by rw [tg₃]; simp) (noDrop'_single (by rw [tg₄]; simp))))
  · unfold nodeCutHead
    rw [shiftsV_cons, shiftsV_cons, shiftsV_cons, shiftsV_single, tg₁, tg₂, tg₃, tg₄]
    simp
  · unfold nodeCutHead; simp [len_adjoin]; norm_num

/-- **`nodeCut` is applicable** (cap `M = 9`: `Intro_cut` is a nine-variable row with a dummy witness `𝟎`). -/
theorem nodeCut_ok {tbl N E Γ W tblN N' B' is il ip inp id₁ id₂ ic₁ ic₂ in₁ in₂ L m₁ m₂ n : V}
    (htbl : TableOK tbl N) (hF : Frag1Table tbl) (hWp : W = frag1Pieces) (htblN : NumTableOK tblN N' B')
    (hΓ : IsFormulaSet LAct Γ)
    (his : is + 2 ≤ E) (hip : ip + 2 ≤ E) (hinp : inp + 2 ≤ E)
    (hid₁ : id₁ + 2 ≤ E) (hid₂ : id₂ + 2 ≤ E) (hic₁ : ic₁ + 2 ≤ E) (hic₂ : ic₂ + 2 ≤ E)
    (hT : il + in₁ + in₂ + 10 ≤ E) (hn : 18 * ‖n‖ + 7 ≤ E) (hLn : L + m₁ + m₂ + 1 ≤ n)
    (hf₁ : neg LAct (fstIdxFact (^&ic₁) (^&id₁)) ∈ Γ) (hi₁ : neg LAct (insFact (^&ic₁) (^&ip) (^&is)) ∈ Γ)
    (hd₁ : neg LAct (derFact (^&id₁ : V)) ∈ Γ) (hn₁ : neg LAct (dlenFact (^&id₁ : V) (^&in₁)) ∈ Γ)
    (hle₁ : neg LAct (leFact (^&in₁) (bnum m₁)) ∈ Γ)
    (hf₂ : neg LAct (fstIdxFact (^&ic₂) (^&id₂)) ∈ Γ) (hneg : neg LAct (negFact (^&inp) (^&ip)) ∈ Γ)
    (hi₂ : neg LAct (insFact (^&ic₂) (^&inp) (^&is)) ∈ Γ)
    (hd₂ : neg LAct (derFact (^&id₂ : V)) ∈ Γ) (hn₂ : neg LAct (dlenFact (^&id₂ : V) (^&in₂)) ∈ Γ)
    (hle₂ : neg LAct (leFact (^&in₂) (bnum m₂)) ∈ Γ)
    (hsl : neg LAct (setLenFact (^&il) (^&is)) ∈ Γ) (hle : neg LAct (leFact (^&il) (bnum L)) ∈ Γ) :
    ListOK tbl E ((9 : ℕ) : V) Γ (nodeCut W tblN is il ip inp id₁ id₂ ic₁ ic₂ in₁ in₂ L m₁ m₂ n) ∧
    NoDrop' (nodeCut W tblN is il ip inp id₁ id₂ ic₁ ic₂ in₁ in₂ L m₁ m₂ n) ∧
    shiftsV (nodeCut W tblN is il ip inp id₁ id₂ ic₁ ic₂ in₁ in₂ L m₁ m₂ n) = 1 ∧
    len (nodeCut W tblN is il ip inp id₁ id₂ ic₁ ic₂ in₁ in₂ L m₁ m₂ n) = 9 ∧
    neg LAct (goalFact (^&(is + 1)) (bnum n)) ∈
      finalCtx Γ (nodeCut W tblN is il ip inp id₁ id₂ ic₁ ic₂ in₁ in₂ L m₁ m₂ n) := by
  have h89 : ((8 : ℕ) : V) ≤ ((9 : ℕ) : V) := by exact_mod_cast (by decide : (8 : ℕ) ≤ 9)
  have hil : il + 2 ≤ E := le_trans (add_le_add (le_trans le_self_add le_self_add) (by norm_num)) hT
  have hin₁ : in₁ + 2 ≤ E := le_trans (add_le_add (le_trans le_add_self le_self_add) (by norm_num)) hT
  have hin₂ : in₂ + 2 ≤ E := le_trans (add_le_add le_add_self (by norm_num)) hT
  obtain ⟨hok, hnd, hsv, hlen, hfin⟩ := nodeCutHead_ok htbl hF hWp hΓ his hil hip hinp hid₁ hid₂ hic₁ hic₂ hin₁ hin₂
    hf₁ hi₁ hd₁ hn₁ hf₂ hneg hi₂ hd₂ hn₂ hsl
  have hΓ' : IsFormulaSet LAct (finalCtx Γ (nodeCutHead W is il ip inp id₁ id₂ ic₁ ic₂ in₁ in₂)) :=
    finalCtx_isFormulaSet 9 htbl hΓ hok
  have hl0 : IsSemiterm LAct 0 (^&il : V) := by simp
  have hn10 : IsSemiterm LAct 0 (^&in₁ : V) := by simp
  have hn20 : IsSemiterm LAct 0 (^&in₂ : V) := by simp
  have hbL : IsSemiterm LAct 0 (bnum L) := isSemiterm_bnum_LAct 0 L
  have hbm₁ : IsSemiterm LAct 0 (bnum m₁) := isSemiterm_bnum_LAct 0 m₁
  have hbm₂ : IsSemiterm LAct 0 (bnum m₂) := isSemiterm_bnum_LAct 0 m₂
  have tr : ∀ x ∈ Γ, shift LAct x ∈ finalCtx Γ (nodeCutHead W is il ip inp id₁ id₂ ic₁ ic₂ in₁ in₂) := by
    intro x hx; rw [hfin]; unfold nodeCutHeadCtx; exact shift_mem_head3 hx
  have hle' : neg LAct (leFact (^&(il + 1)) (bnum L)) ∈ finalCtx Γ (nodeCutHead W is il ip inp id₁ id₂ ic₁ ic₂ in₁ in₂) := by
    have := tr _ hle
    rwa [shift_neg (isFormula_leFact hl0 hbL), shift_leFact hl0 hbL, termShift_fvar, termShift_bnum] at this
  have hle₁' : neg LAct (leFact (^&(in₁ + 1)) (bnum m₁)) ∈ finalCtx Γ (nodeCutHead W is il ip inp id₁ id₂ ic₁ ic₂ in₁ in₂) := by
    have := tr _ hle₁
    rwa [shift_neg (isFormula_leFact hn10 hbm₁), shift_leFact hn10 hbm₁, termShift_fvar, termShift_bnum] at this
  have hle₂' : neg LAct (leFact (^&(in₂ + 1)) (bnum m₂)) ∈ finalCtx Γ (nodeCutHead W is il ip inp id₁ id₂ ic₁ ic₂ in₁ in₂) := by
    have := tr _ hle₂
    rwa [shift_neg (isFormula_leFact hn20 hbm₂), shift_leFact hn20 hbm₂, termShift_fvar, termShift_bnum] at this
  obtain ⟨tok, tnd, tsv, tlen, tfin, tmem⟩ := goalTailBinary_ok htbl hF hWp htblN hΓ'
    (by rw [show il + 1 + (in₁ + 1) + (in₂ + 1) + 7 = il + in₁ + in₂ + 10 by ring]; exact hT)
    (by rw [add_assoc, one_add_one_eq_two]; exact his) hn hLn hle' hle₁' hle₂'
    (by rw [hfin]; unfold nodeCutHeadCtx; simp) (by rw [hfin]; unfold nodeCutHeadCtx; simp)
    (by rw [hfin]; unfold nodeCutHeadCtx; simp)
  refine ⟨listOK_appendV hok (tok.mono h89), noDrop'_appendV hnd tnd, ?_, ?_, ?_⟩
  · unfold nodeCut; rw [shiftsV_appendV, hsv, tsv, add_zero]
  · unfold nodeCut; rw [len_appendV, hlen, tlen]; norm_num
  · unfold nodeCut; rw [finalCtx_appendV]; exact tmem

end nodes

/-! ## 5. Cost (DESIGN_fragments §5)

The fragments mix Horn steps (tags 0/1/2, costed by `stepCost_le_of_stepOK`) with the eliminations and
splits of `goalElim` (tags 3/4), the goal cut (tag 6) and the closed lemma cut (tag 7). A SIZE DISCIPLINE
`SizeOK Q D S` records, per non-Horn step, the size of the formula it handles (`≤ Q`) and the length of a
lemma's derivation (`≤ D`); with `ListOK` at cap `M` and a table bound `B` on the row bodies, every step grows
the context ADDITIVELY by `growK B E Q = 4BE + 2Q` and costs at most `costK + (3M + 11)·(|Γ| + fvOccS Γ)`,
whence `costSum ≤ len S · (costK + (3M+11)·ctxBound)` — the shape §5 sums. The goal-fact size `|goalFact s ū|`
is kept SYMBOLIC (as §5's `|G_code|`): `goalElim` is bounded by `4·|goalFact|` through its two `free`
equations, and a fragment's `Q` must dominate its own goal fact and its closed lemma fact. -/

section cost

/-! ### 5.1 The Horn bounds at an arbitrary cap `M` -/

theorem ctxAfter_len_le_M (M : ℕ) {tbl N E B Γ s : V} (hE : 1 ≤ E) (htbl : TableOK tbl N)
    (hok : StepOK tbl E (M : V) Γ s) (ht : sTag s = 0 ∨ sTag s = 1 ∨ sTag s = 2)
    (hB : formulaLen LAct (rowB tbl.[sRow s]) ≤ B) :
    setLen LAct (ctxAfter Γ s) ≤ setLen LAct Γ + fvOccS LAct Γ + 4 * (B * E) ∧
    fvOccS LAct (ctxAfter Γ s) ≤ fvOccS LAct Γ + 4 * (B * E) := by
  obtain ⟨hΓ, h⟩ := hok
  rcases h with ⟨ht0, hh, hrow⟩ | ⟨ht1, hh, hrow⟩ | ⟨ht2, hh, hrow⟩ | ⟨ht3, _⟩ | ⟨ht4, _⟩ | ⟨ht5, _⟩ | ⟨ht6, _⟩ | ⟨ht7, _⟩
  · obtain ⟨es, l, hes_eq, hl_eq, hm, hes', hneg'⟩ := hh.lists M
    have hes : ∀ e ∈ es, IsTerm LAct e := fun e he ↦ (hes' e he).1
    have hrowF := (htbl _ hh.1).1
    rw [hm, hrow, hl_eq, impChainV_vecOf] at hrowF
    obtain ⟨has, hc⟩ := isSemiformula_of_impChain hrowF
    rw [hrow, hl_eq, impChainV_vecOf] at hB
    have hcB : formulaLen LAct (sC s) ≤ B := le_trans (formulaLen_le_impChain has hc) hB
    have hlen : formulaLen LAct (instOuter LAct es (sC s)) ≤ B * E :=
      le_trans (formulaLen_instOuter_le hE es hc hes') (mul_le_mul_of_nonneg_right hcB zero_le)
    have hF : IsFormula LAct (instOuter LAct es (sC s)) := isFormula_instOuter es hc hes
    rw [ctxAfter_tag0 ht0, hes_eq, subst_revV_vecOf es hc hes]
    constructor
    · calc setLen LAct (insert (neg LAct (instOuter LAct es (sC s))) Γ)
          ≤ setLen LAct Γ + formulaLen LAct (neg LAct (instOuter LAct es (sC s))) := setLen_insert_le _ _
        _ = setLen LAct Γ + formulaLen LAct (instOuter LAct es (sC s)) := by rw [formulaLen_neg hF.isUFormula]
        _ ≤ setLen LAct Γ + B * E := add_le_add le_rfl hlen
        _ ≤ setLen LAct Γ + fvOccS LAct Γ + 4 * (B * E) := by
            rw [add_assoc]; exact add_le_add le_rfl (le_trans (le_trans (le_of_eq (one_mul _).symm)
              (mul_le_mul_of_nonneg_right (by norm_num) zero_le)) le_add_self)
    · calc fvOccS LAct (insert (neg LAct (instOuter LAct es (sC s))) Γ)
          ≤ fvOccS LAct Γ + fvOccF LAct (neg LAct (instOuter LAct es (sC s))) := fvOccS_insert_le _ _
        _ = fvOccS LAct Γ + fvOccF LAct (instOuter LAct es (sC s)) := by rw [fvOccF_neg hF.isUFormula]
        _ ≤ fvOccS LAct Γ + B * E := add_le_add le_rfl (le_trans (fvOccF_le_formulaLen hF.isUFormula) hlen)
        _ ≤ fvOccS LAct Γ + 4 * (B * E) := add_le_add le_rfl
            (le_trans (le_of_eq (one_mul _).symm) (mul_le_mul_of_nonneg_right (by norm_num) zero_le))
  · obtain ⟨es, l, hes_eq, hl_eq, hm, hes', hneg'⟩ := hh.lists M
    have hes : ∀ e ∈ es, IsTerm LAct e := fun e he ↦ (hes' e he).1
    have hrowF := (htbl _ hh.1).1
    rw [hm, hrow, hl_eq, impChainV_vecOf] at hrowF
    obtain ⟨has, hc⟩ := isSemiformula_of_impChain hrowF
    obtain ⟨hc₁, hc₂⟩ := IsSemiformula.and.mp hc
    rw [hrow, hl_eq, impChainV_vecOf] at hB
    have hcB : formulaLen LAct ((π₁ (sC s)) ^⋏ (π₂ (sC s))) ≤ B := le_trans (formulaLen_le_impChain has hc) hB
    rw [formulaLen_and hc₁.isUFormula hc₂.isUFormula] at hcB
    have hc₁B : formulaLen LAct (π₁ (sC s)) ≤ B := le_trans (le_trans le_self_add le_self_add) hcB
    have hc₂B : formulaLen LAct (π₂ (sC s)) ≤ B := le_trans (le_trans le_add_self le_self_add) hcB
    have hlen₁ : formulaLen LAct (instOuter LAct es (π₁ (sC s))) ≤ B * E :=
      le_trans (formulaLen_instOuter_le hE es hc₁ hes') (mul_le_mul_of_nonneg_right hc₁B zero_le)
    have hlen₂ : formulaLen LAct (instOuter LAct es (π₂ (sC s))) ≤ B * E :=
      le_trans (formulaLen_instOuter_le hE es hc₂ hes') (mul_le_mul_of_nonneg_right hc₂B zero_le)
    have hF₁ : IsFormula LAct (instOuter LAct es (π₁ (sC s))) := isFormula_instOuter es hc₁ hes
    have hF₂ : IsFormula LAct (instOuter LAct es (π₂ (sC s))) := isFormula_instOuter es hc₂ hes
    rw [ctxAfter_tag1 ht1, hes_eq, subst_revV_vecOf es hc₁ hes, subst_revV_vecOf es hc₂ hes]
    have h4 : B * E + B * E ≤ 4 * (B * E) := by
      rw [show B * E + B * E = 2 * (B * E) by ring]; exact mul_le_mul_of_nonneg_right (by norm_num) zero_le
    constructor
    · calc setLen LAct (insert (neg LAct (instOuter LAct es (π₁ (sC s))))
              (insert (neg LAct (instOuter LAct es (π₂ (sC s)))) Γ))
          ≤ setLen LAct (insert (neg LAct (instOuter LAct es (π₂ (sC s)))) Γ)
              + formulaLen LAct (neg LAct (instOuter LAct es (π₁ (sC s)))) := setLen_insert_le _ _
        _ ≤ (setLen LAct Γ + formulaLen LAct (neg LAct (instOuter LAct es (π₂ (sC s)))))
              + formulaLen LAct (neg LAct (instOuter LAct es (π₁ (sC s)))) := add_le_add (setLen_insert_le _ _) le_rfl
        _ ≤ (setLen LAct Γ + B * E) + B * E := by
            rw [formulaLen_neg hF₁.isUFormula, formulaLen_neg hF₂.isUFormula]
            exact add_le_add (add_le_add le_rfl hlen₂) hlen₁
        _ ≤ setLen LAct Γ + fvOccS LAct Γ + 4 * (B * E) := by
            rw [add_assoc, add_assoc]; exact add_le_add le_rfl (le_trans h4 le_add_self)
    · calc fvOccS LAct (insert (neg LAct (instOuter LAct es (π₁ (sC s))))
              (insert (neg LAct (instOuter LAct es (π₂ (sC s)))) Γ))
          ≤ fvOccS LAct (insert (neg LAct (instOuter LAct es (π₂ (sC s)))) Γ)
              + fvOccF LAct (neg LAct (instOuter LAct es (π₁ (sC s)))) := fvOccS_insert_le _ _
        _ ≤ (fvOccS LAct Γ + fvOccF LAct (neg LAct (instOuter LAct es (π₂ (sC s)))))
              + fvOccF LAct (neg LAct (instOuter LAct es (π₁ (sC s)))) := add_le_add (fvOccS_insert_le _ _) le_rfl
        _ ≤ (fvOccS LAct Γ + B * E) + B * E := by
            rw [fvOccF_neg hF₁.isUFormula, fvOccF_neg hF₂.isUFormula]
            exact add_le_add (add_le_add le_rfl (le_trans (fvOccF_le_formulaLen hF₂.isUFormula) hlen₂))
              (le_trans (fvOccF_le_formulaLen hF₁.isUFormula) hlen₁)
        _ ≤ fvOccS LAct Γ + 4 * (B * E) := by rw [add_assoc]; exact add_le_add le_rfl h4
  · obtain ⟨es, l, hes_eq, hl_eq, hm, hes', hneg'⟩ := hh.lists M
    have hes : ∀ e ∈ es, IsTerm LAct e := fun e he ↦ (hes' e he).1
    have hrowF := (htbl _ hh.1).1
    rw [hm, hrow, hl_eq, impChainV_vecOf] at hrowF
    obtain ⟨has, hc⟩ := isSemiformula_of_impChain hrowF
    have hR : IsSemiformula LAct ((es.length : V) + 1) (sC s) := IsSemiformula.exs.mp hc
    rw [hrow, hl_eq, impChainV_vecOf] at hB
    have hR' : IsSemiformula LAct 1 (instOuterAt LAct 1 es (sC s)) := isSemiformula_one_instOuterAt es hR hes
    have hlen : formulaLen LAct (instOuterAt LAct 1 es (sC s)) ≤ B * E := by
      have h := formulaLen_exs_instOuterAt_le hE has hR hes' (F := B * E)
        (mul_le_mul_of_nonneg_right hB zero_le)
      rw [formulaLen_exs hR'.isUFormula] at h
      exact le_trans le_self_add h
    have hfree : formulaLen LAct (free LAct (instOuterAt LAct 1 es (sC s))) ≤ 2 * (B * E) :=
      le_trans (formulaLen_free_le hR') (mul_le_mul_of_nonneg_left hlen zero_le)
    have hF : IsFormula LAct (free LAct (instOuterAt LAct 1 es (sC s))) := hR'.free
    have hocc : fvOccF LAct (free LAct (instOuterAt LAct 1 es (sC s))) ≤ 2 * (B * E) := by
      calc fvOccF LAct (free LAct (instOuterAt LAct 1 es (sC s)))
          ≤ fvOccF LAct (instOuterAt LAct 1 es (sC s)) + bvOccF LAct (instOuterAt LAct 1 es (sC s)) := fvOccF_free_le' hR'
        _ ≤ formulaLen LAct (instOuterAt LAct 1 es (sC s)) + formulaLen LAct (instOuterAt LAct 1 es (sC s)) :=
            add_le_add (fvOccF_le_formulaLen hR'.isUFormula) (bvOccF_le_formulaLen hR'.isUFormula)
        _ ≤ B * E + B * E := add_le_add hlen hlen
        _ = 2 * (B * E) := by ring
    rw [ctxAfter_tag2 ht2, hes_eq, subst_qVec_revV_vecOf es hR hes]
    have h2 : 2 * (B * E) ≤ 4 * (B * E) := mul_le_mul_of_nonneg_right (by norm_num) zero_le
    constructor
    · calc setLen LAct (insert (neg LAct (free LAct (instOuterAt LAct 1 es (sC s)))) (setShift LAct Γ))
          ≤ setLen LAct (setShift LAct Γ) + formulaLen LAct (neg LAct (free LAct (instOuterAt LAct 1 es (sC s)))) :=
            setLen_insert_le _ _
        _ ≤ (setLen LAct Γ + fvOccS LAct Γ) + 2 * (B * E) := by
            rw [formulaLen_neg hF.isUFormula]; exact add_le_add (setLen_setShift_le_occ hΓ) hfree
        _ ≤ setLen LAct Γ + fvOccS LAct Γ + 4 * (B * E) := add_le_add le_rfl h2
    · calc fvOccS LAct (insert (neg LAct (free LAct (instOuterAt LAct 1 es (sC s)))) (setShift LAct Γ))
          ≤ fvOccS LAct (setShift LAct Γ) + fvOccF LAct (neg LAct (free LAct (instOuterAt LAct 1 es (sC s)))) :=
            fvOccS_insert_le _ _
        _ ≤ fvOccS LAct Γ + 2 * (B * E) := by
            rw [fvOccF_neg hF.isUFormula]; exact add_le_add (fvOccS_setShift_le hΓ) hocc
        _ ≤ fvOccS LAct Γ + 4 * (B * E) := add_le_add le_rfl h2
  · exfalso; rw [ht3] at ht; norm_num at ht
  · exfalso; rw [ht4] at ht; norm_num at ht
  · exfalso; rw [ht5] at ht; norm_num at ht
  · exfalso; rw [ht6] at ht; norm_num at ht
  · exfalso; rw [ht7] at ht; norm_num at ht


noncomputable def stepKM (N E B M : V) : V :=
  hornCost N E 0 M M B + (6 * (B * E) + 4) + introCost N E 0 M M B

lemma hornCost_GM (N E G M B : V) : hornCost N E G M M B = hornCost N E 0 M M B + (3 * M + 4) * G := by
  unfold hornCost; ring
lemma introCost_GM (N E G M B : V) : introCost N E G M M B = introCost N E 0 M M B + (3 * M + 10) * G := by
  unfold introCost; ring

/-- `stepCost_le_of_stepOK` at an arbitrary cap. -/
theorem stepCost_le_of_stepOK_M (M : ℕ) {tbl N E B Γ s : V} (hok : StepOK tbl E (M : V) Γ s)
    (ht : sTag s = 0 ∨ sTag s = 1 ∨ sTag s = 2) (hB : formulaLen LAct (rowB tbl.[sRow s]) ≤ B) :
    stepCost N E Γ s ≤ stepKM N E B M + (3 * (M : V) + 10) * setLen LAct Γ := by
  obtain ⟨_, h⟩ := hok
  have hle : (3 * (M : V) + 4) * setLen LAct Γ ≤ (3 * (M : V) + 10) * setLen LAct Γ :=
    mul_le_mul_of_nonneg_right (by gcongr; norm_num) zero_le
  rcases h with ⟨ht0, hh, hrow⟩ | ⟨ht1, hh, hrow⟩ | ⟨ht2, hh, hrow⟩ | ⟨ht3, _⟩ | ⟨ht4, _⟩ | ⟨ht5, _⟩ | ⟨ht6, _⟩ | ⟨ht7, _⟩
  · rw [stepCost_tag0 ht0]
    rw [hrow] at hB
    have hm : len (sEv s) ≤ (M : V) := hh.2.2.1
    have hj : len (sAs s) ≤ (M : V) := hh.2.2.2.1
    calc hornCost N E (setLen LAct Γ) (len (sEv s)) (len (sAs s)) (formulaLen LAct (impChainV LAct (sAs s) (sC s)))
        ≤ hornCost N E (setLen LAct Γ) (M : V) (M : V) B := by unfold hornCost; gcongr
      _ = hornCost N E 0 (M : V) (M : V) B + (3 * (M : V) + 4) * setLen LAct Γ := hornCost_GM _ _ _ _ _
      _ ≤ stepKM N E B M + (3 * (M : V) + 10) * setLen LAct Γ := by
          unfold stepKM; exact add_le_add (le_trans le_self_add le_self_add) hle
  · rw [stepCost_tag1 ht1]
    rw [hrow] at hB
    have hm : len (sEv s) ≤ (M : V) := hh.2.2.1
    have hj : len (sAs s) ≤ (M : V) := hh.2.2.2.1
    calc hornCost N E (setLen LAct Γ) (len (sEv s)) (len (sAs s))
            (formulaLen LAct (impChainV LAct (sAs s) ((π₁ (sC s)) ^⋏ (π₂ (sC s)))))
          + 2 * setLen LAct Γ + 6 * (formulaLen LAct (impChainV LAct (sAs s) ((π₁ (sC s)) ^⋏ (π₂ (sC s)))) * E) + 4
        ≤ hornCost N E (setLen LAct Γ) (M : V) (M : V) B + 2 * setLen LAct Γ + 6 * (B * E) + 4 := by
          gcongr <;> (unfold hornCost; gcongr)
      _ = (hornCost N E 0 (M : V) (M : V) B + (6 * (B * E) + 4)) + (3 * (M : V) + 6) * setLen LAct Γ := by
          rw [hornCost_GM]; ring
      _ ≤ stepKM N E B M + (3 * (M : V) + 10) * setLen LAct Γ := by
          unfold stepKM
          exact add_le_add le_self_add (mul_le_mul_of_nonneg_right (by gcongr; norm_num) zero_le)
  · rw [stepCost_tag2 ht2]
    rw [hrow] at hB
    have hm : len (sEv s) ≤ (M : V) := hh.2.2.1
    have hj : len (sAs s) ≤ (M : V) := hh.2.2.2.1
    calc introCost N E (setLen LAct Γ) (len (sEv s)) (len (sAs s)) (formulaLen LAct (impChainV LAct (sAs s) (^∃ (sC s))))
        ≤ introCost N E (setLen LAct Γ) (M : V) (M : V) B := by unfold introCost; gcongr
      _ = introCost N E 0 (M : V) (M : V) B + (3 * (M : V) + 10) * setLen LAct Γ := introCost_GM _ _ _ _ _
      _ ≤ stepKM N E B M + (3 * (M : V) + 10) * setLen LAct Γ := by
          unfold stepKM; exact add_le_add le_add_self le_rfl
  · exfalso; rw [ht3] at ht; norm_num at ht
  · exfalso; rw [ht4] at ht; norm_num at ht
  · exfalso; rw [ht5] at ht; norm_num at ht
  · exfalso; rw [ht6] at ht; norm_num at ht
  · exfalso; rw [ht7] at ht; norm_num at ht

/-! ### 5.2 The size discipline -/

/-- The size data of a step (context-free): Horn steps carry none (the table bound `B` covers them); an
elimination carries `|P|`, a split `|p| + |q|`, a goal cut `|goalFact s ū|`, a lemma cut `|A|` and `dlen dA`. -/
def StepSizeOK (Q D s : V) : Prop :=
  sTag s = 0 ∨ sTag s = 1 ∨ sTag s = 2 ∨
  (sTag s = 3 ∧ formulaLen LAct (π₂ s) ≤ Q) ∨
  (sTag s = 4 ∧ formulaLen LAct (π₁ (π₂ s)) + formulaLen LAct (π₂ (π₂ s)) ≤ Q) ∨
  (sTag s = 6 ∧ formulaLen LAct (goalFact (sGoalS s) (sGoalU s)) ≤ Q) ∨
  (sTag s = 7 ∧ formulaLen LAct (sLemA s) ≤ Q ∧ dlen TAct (sLemD s) ≤ D)

def SizeOK (Q D S : V) : Prop := ∀ i < len S, StepSizeOK Q D S.[i]

lemma sizeOK_nil (Q D : V) : SizeOK Q D (0 : V) := fun i hi ↦ by simp at hi

lemma sizeOK_appendV {Q D S₁ S₂ : V} (h₁ : SizeOK Q D S₁) (h₂ : SizeOK Q D S₂) : SizeOK Q D (appendV S₁ S₂) := by
  intro i hi
  rw [len_appendV] at hi
  rcases lt_or_ge i (len S₁) with h | h
  · rw [nth_appendV_lt S₁ S₂ i h]; exact h₁ i h
  · obtain ⟨j, rfl⟩ : ∃ j, i = len S₁ + j := ⟨i - len S₁, (add_tsub_cancel_of_le h).symm⟩
    rw [nth_appendV_add]; exact h₂ j (lt_of_add_lt_add_left hi)

lemma sizeOK_single {Q D s : V} (h : StepSizeOK Q D s) : SizeOK Q D (?[s] : V) := by
  intro i hi
  rw [len_adjoin, len_nil, zero_add] at hi
  rcases zero_or_succ i with rfl | ⟨i, rfl⟩
  · simpa using h
  · exact absurd hi (not_lt.mpr le_add_self)

lemma sizeOK_cons {Q D s S : V} (h : StepSizeOK Q D s) (hS : SizeOK Q D S) : SizeOK Q D (s ∷ S) := by
  rw [cons_eq_appendV_single]; exact sizeOK_appendV (sizeOK_single h) hS

lemma StepSizeOK.mono {Q Q' D D' s : V} (hQ : Q ≤ Q') (hD : D ≤ D') (h : StepSizeOK Q D s) : StepSizeOK Q' D' s := by
  rcases h with h | h | h | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h', h''⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h, le_trans h' hQ⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h, le_trans h' hQ⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h, le_trans h' hQ⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h, le_trans h' hQ, le_trans h'' hD⟩)))))

lemma SizeOK.mono {Q Q' D D' S : V} (hQ : Q ≤ Q') (hD : D ≤ D') (h : SizeOK Q D S) : SizeOK Q' D' S :=
  fun i hi ↦ (h i hi).mono hQ hD

/-- The per-tag data of an applicable non-Horn step. -/
lemma stepOK_tag3_data {tbl E M Γ s : V} (hok : StepOK tbl E M Γ s) (h3 : sTag s = 3) :
    IsSemiformula LAct 1 (π₂ s) := by
  obtain ⟨_, h⟩ := hok
  rcases h with ⟨h0, _⟩ | ⟨h0, _⟩ | ⟨h0, _⟩ | ⟨_, hP, _⟩ | ⟨h0, _⟩ | ⟨h0, _⟩ | ⟨h0, _⟩ | ⟨h0, _⟩
  all_goals first | exact hP | (exfalso; rw [h0] at h3; norm_num at h3)
lemma stepOK_tag4_data {tbl E M Γ s : V} (hok : StepOK tbl E M Γ s) (h4 : sTag s = 4) :
    IsFormula LAct (π₁ (π₂ s)) ∧ IsFormula LAct (π₂ (π₂ s)) := by
  obtain ⟨_, h⟩ := hok
  rcases h with ⟨h0, _⟩ | ⟨h0, _⟩ | ⟨h0, _⟩ | ⟨h0, _⟩ | ⟨_, hp, hq, _⟩ | ⟨h0, _⟩ | ⟨h0, _⟩ | ⟨h0, _⟩
  all_goals first | exact ⟨hp, hq⟩ | (exfalso; rw [h0] at h4; norm_num at h4)
lemma stepOK_tag6_data {tbl E M Γ s : V} (hok : StepOK tbl E M Γ s) (h6 : sTag s = 6) :
    IsSemiterm LAct 0 (sGoalS s) ∧ IsSemiterm LAct 0 (sGoalU s) := by
  obtain ⟨_, h⟩ := hok
  rcases h with ⟨h0, _⟩ | ⟨h0, _⟩ | ⟨h0, _⟩ | ⟨h0, _⟩ | ⟨h0, _⟩ | ⟨h0, _⟩ | ⟨_, hG⟩ | ⟨h0, _⟩
  all_goals first | exact ⟨hG.2.2.2.2.1, hG.2.2.2.2.2.2.1⟩ | (exfalso; rw [h0] at h6; norm_num at h6)
lemma stepOK_tag7_data {tbl E M Γ s : V} (hok : StepOK tbl E M Γ s) (h7 : sTag s = 7) :
    IsFormula LAct (sLemA s) := by
  obtain ⟨_, h⟩ := hok
  rcases h with ⟨h0, _⟩ | ⟨h0, _⟩ | ⟨h0, _⟩ | ⟨h0, _⟩ | ⟨h0, _⟩ | ⟨h0, _⟩ | ⟨h0, _⟩ | ⟨_, hL⟩
  all_goals first | exact hL.1 | (exfalso; rw [h0] at h7; norm_num at h7)
lemma stepOK_horn_row_lt {tbl E M Γ s : V} (hok : StepOK tbl E M Γ s)
    (ht : sTag s = 0 ∨ sTag s = 1 ∨ sTag s = 2) : sRow s < len tbl := by
  obtain ⟨_, h⟩ := hok
  rcases h with ⟨_, hh, _⟩ | ⟨_, hh, _⟩ | ⟨_, hh, _⟩ | ⟨h0, _⟩ | ⟨h0, _⟩ | ⟨h0, _⟩ | ⟨h0, _⟩ | ⟨h0, _⟩
  all_goals first | exact hh.1 | (exfalso; rcases ht with ht | ht | ht <;> (rw [h0] at ht; norm_num at ht))

/-! ### 5.3 One disciplined step: additive growth, affine cost -/

noncomputable def growK (B E Q : V) : V := 4 * (B * E) + 2 * Q
noncomputable def costK (N E B M Q D : V) : V := stepKM N E B M + 27 * (Q * E) + 2 * E + 7 * Q + D + 42

theorem step_grow_cost (M : ℕ) {tbl N E B Q D Γ s : V} (hE : 1 ≤ E) (htbl : TableOK tbl N)
    (hBt : ∀ j < len tbl, formulaLen LAct (rowB tbl.[j]) ≤ B)
    (hok : StepOK tbl E (M : V) Γ s) (hsz : StepSizeOK Q D s) :
    (setLen LAct (ctxAfter Γ s) ≤ setLen LAct Γ + fvOccS LAct Γ + growK B E Q ∧
     fvOccS LAct (ctxAfter Γ s) ≤ fvOccS LAct Γ + growK B E Q) ∧
    stepCost N E Γ s ≤ costK N E B M Q D + (3 * (M : V) + 11) * (setLen LAct Γ + fvOccS LAct Γ) := by
  have hΓ : IsFormulaSet LAct Γ := hok.1
  have hG4 : 4 * (B * E) ≤ growK B E Q := le_self_add
  have hQ2 : 2 * Q ≤ growK B E Q := le_add_self
  have hQ1 : Q ≤ growK B E Q := le_trans (le_trans (le_of_eq (one_mul Q).symm) (mul_le_mul_of_nonneg_right (by norm_num) zero_le)) hQ2
  have hcoef : (3 * (M : V) + 10) * setLen LAct Γ ≤ (3 * (M : V) + 11) * (setLen LAct Γ + fvOccS LAct Γ) :=
    mul_le_mul (by gcongr; norm_num) le_self_add zero_le zero_le
  have hK0 : stepKM N E B M ≤ costK N E B M Q D := by unfold costK; exact le_trans le_self_add (le_trans le_self_add (le_trans le_self_add (le_trans le_self_add le_self_add)))
  -- the Horn cases
  have horn : (sTag s = 0 ∨ sTag s = 1 ∨ sTag s = 2) →
      (setLen LAct (ctxAfter Γ s) ≤ setLen LAct Γ + fvOccS LAct Γ + growK B E Q ∧
       fvOccS LAct (ctxAfter Γ s) ≤ fvOccS LAct Γ + growK B E Q) ∧
      stepCost N E Γ s ≤ costK N E B M Q D + (3 * (M : V) + 11) * (setLen LAct Γ + fvOccS LAct Γ) := by
    intro ht
    have hB := hBt _ (stepOK_horn_row_lt hok ht)
    obtain ⟨g1, g2⟩ := ctxAfter_len_le_M M hE htbl hok ht hB
    refine ⟨⟨le_trans g1 (add_le_add le_rfl hG4), le_trans g2 (add_le_add le_rfl hG4)⟩, ?_⟩
    exact le_trans (stepCost_le_of_stepOK_M M hok ht hB) (add_le_add hK0 hcoef)
  rcases hsz with h | h | h | ⟨h3, hP⟩ | ⟨h4, hpq⟩ | ⟨h6, hg⟩ | ⟨h7, hA, hD⟩
  · exact horn (Or.inl h)
  · exact horn (Or.inr (Or.inl h))
  · exact horn (Or.inr (Or.inr h))
  · -- tag 3
    have hP1 := stepOK_tag3_data hok h3
    have hF : IsFormula LAct (free LAct (π₂ s)) := hP1.free
    have hfl : formulaLen LAct (free LAct (π₂ s)) ≤ 2 * Q :=
      le_trans (formulaLen_free_le hP1) (mul_le_mul_of_nonneg_left hP zero_le)
    rw [ctxAfter_tag3 h3, stepCost_tag3 h3]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · calc setLen LAct (insert (neg LAct (free LAct (π₂ s))) (setShift LAct Γ))
          ≤ setLen LAct (setShift LAct Γ) + formulaLen LAct (neg LAct (free LAct (π₂ s))) := setLen_insert_le _ _
        _ ≤ (setLen LAct Γ + fvOccS LAct Γ) + 2 * Q := by
            rw [formulaLen_neg hF.isUFormula]; exact add_le_add (setLen_setShift_le_occ hΓ) hfl
        _ ≤ setLen LAct Γ + fvOccS LAct Γ + growK B E Q := add_le_add le_rfl hQ2
    · calc fvOccS LAct (insert (neg LAct (free LAct (π₂ s))) (setShift LAct Γ))
          ≤ fvOccS LAct (setShift LAct Γ) + fvOccF LAct (neg LAct (free LAct (π₂ s))) := fvOccS_insert_le _ _
        _ ≤ fvOccS LAct Γ + 2 * Q := by
            rw [fvOccF_neg hF.isUFormula]
            exact add_le_add (fvOccS_setShift_le hΓ) (le_trans (fvOccF_le_formulaLen hF.isUFormula) hfl)
        _ ≤ fvOccS LAct Γ + growK B E Q := add_le_add le_rfl hQ2
    · calc 4 * setLen LAct Γ + setLen LAct (setShift LAct Γ) + 7 * formulaLen LAct (π₂ s) + 10
          ≤ 4 * setLen LAct Γ + (setLen LAct Γ + fvOccS LAct Γ) + 7 * Q + 10 := by
            gcongr; exact setLen_setShift_le_occ hΓ
        _ = (7 * Q + 10) + (5 * setLen LAct Γ + fvOccS LAct Γ) := by ring
        _ ≤ costK N E B M Q D + (3 * (M : V) + 11) * (setLen LAct Γ + fvOccS LAct Γ) := by
            refine add_le_add ?_ ?_
            · unfold costK
              calc 7 * Q + 10 ≤ 7 * Q + 42 := by gcongr; norm_num
                _ ≤ stepKM N E B M + 27 * (Q * E) + 2 * E + 7 * Q + D + 42 := by
                    rw [show stepKM N E B M + 27 * (Q * E) + 2 * E + 7 * Q + D + 42
                      = (7 * Q + 42) + (stepKM N E B M + 27 * (Q * E) + 2 * E + D) by ring]
                    exact le_self_add
            · calc 5 * setLen LAct Γ + fvOccS LAct Γ ≤ 11 * (setLen LAct Γ + fvOccS LAct Γ) := by
                    rw [mul_add]; exact add_le_add (mul_le_mul_of_nonneg_right (by norm_num) zero_le)
                      (le_trans (le_of_eq (one_mul _).symm) (mul_le_mul_of_nonneg_right (by norm_num) zero_le))
                _ ≤ (3 * (M : V) + 11) * (setLen LAct Γ + fvOccS LAct Γ) :=
                    mul_le_mul_of_nonneg_right le_add_self zero_le
  · -- tag 4
    obtain ⟨hp, hq⟩ := stepOK_tag4_data hok h4
    rw [ctxAfter_tag4 h4, stepCost_tag4 h4]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · calc setLen LAct (insert (neg LAct (π₁ (π₂ s))) (insert (neg LAct (π₂ (π₂ s))) Γ))
          ≤ setLen LAct (insert (neg LAct (π₂ (π₂ s))) Γ) + formulaLen LAct (neg LAct (π₁ (π₂ s))) := setLen_insert_le _ _
        _ ≤ (setLen LAct Γ + formulaLen LAct (neg LAct (π₂ (π₂ s)))) + formulaLen LAct (neg LAct (π₁ (π₂ s))) :=
            add_le_add (setLen_insert_le _ _) le_rfl
        _ = setLen LAct Γ + (formulaLen LAct (π₁ (π₂ s)) + formulaLen LAct (π₂ (π₂ s))) := by
            rw [formulaLen_neg hp.isUFormula, formulaLen_neg hq.isUFormula]; ring
        _ ≤ setLen LAct Γ + fvOccS LAct Γ + growK B E Q := by
            rw [add_assoc]; exact add_le_add le_rfl (le_trans (le_trans hpq hQ1) le_add_self)
    · calc fvOccS LAct (insert (neg LAct (π₁ (π₂ s))) (insert (neg LAct (π₂ (π₂ s))) Γ))
          ≤ fvOccS LAct (insert (neg LAct (π₂ (π₂ s))) Γ) + fvOccF LAct (neg LAct (π₁ (π₂ s))) := fvOccS_insert_le _ _
        _ ≤ (fvOccS LAct Γ + fvOccF LAct (neg LAct (π₂ (π₂ s)))) + fvOccF LAct (neg LAct (π₁ (π₂ s))) :=
            add_le_add (fvOccS_insert_le _ _) le_rfl
        _ ≤ fvOccS LAct Γ + (formulaLen LAct (π₁ (π₂ s)) + formulaLen LAct (π₂ (π₂ s))) := by
            rw [fvOccF_neg hp.isUFormula, fvOccF_neg hq.isUFormula, add_assoc, add_comm (formulaLen LAct (π₁ (π₂ s)))]
            exact add_le_add le_rfl (add_le_add (fvOccF_le_formulaLen hq.isUFormula) (fvOccF_le_formulaLen hp.isUFormula))
        _ ≤ fvOccS LAct Γ + growK B E Q := add_le_add le_rfl (le_trans hpq hQ1)
    · calc 2 * setLen LAct Γ + 3 * formulaLen LAct (π₁ (π₂ s)) + 3 * formulaLen LAct (π₂ (π₂ s)) + 4
          = (3 * (formulaLen LAct (π₁ (π₂ s)) + formulaLen LAct (π₂ (π₂ s))) + 4) + 2 * setLen LAct Γ := by ring
        _ ≤ (3 * Q + 4) + 2 * setLen LAct Γ := by gcongr
        _ ≤ costK N E B M Q D + (3 * (M : V) + 11) * (setLen LAct Γ + fvOccS LAct Γ) := by
            refine add_le_add ?_ ?_
            · unfold costK
              calc 3 * Q + 4 ≤ 7 * Q + 42 := by gcongr <;> norm_num
                _ ≤ stepKM N E B M + 27 * (Q * E) + 2 * E + 7 * Q + D + 42 := by
                    rw [show stepKM N E B M + 27 * (Q * E) + 2 * E + 7 * Q + D + 42
                      = (7 * Q + 42) + (stepKM N E B M + 27 * (Q * E) + 2 * E + D) by ring]
                    exact le_self_add
            · exact mul_le_mul (by norm_num) le_self_add zero_le zero_le
  · -- tag 6
    obtain ⟨hs, hu⟩ := stepOK_tag6_data hok h6
    have hF : IsFormula LAct (goalFact (sGoalS s) (sGoalU s)) := isFormula_goalFact hs hu
    rw [ctxAfter_tag6 h6, stepCost_tag6 h6]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · calc setLen LAct (insert (neg LAct (goalFact (sGoalS s) (sGoalU s))) Γ)
          ≤ setLen LAct Γ + formulaLen LAct (neg LAct (goalFact (sGoalS s) (sGoalU s))) := setLen_insert_le _ _
        _ ≤ setLen LAct Γ + Q := by rw [formulaLen_neg hF.isUFormula]; exact add_le_add le_rfl hg
        _ ≤ setLen LAct Γ + fvOccS LAct Γ + growK B E Q := by
            rw [add_assoc]; exact add_le_add le_rfl (le_trans hQ1 le_add_self)
    · calc fvOccS LAct (insert (neg LAct (goalFact (sGoalS s) (sGoalU s))) Γ)
          ≤ fvOccS LAct Γ + fvOccF LAct (neg LAct (goalFact (sGoalS s) (sGoalU s))) := fvOccS_insert_le _ _
        _ ≤ fvOccS LAct Γ + Q := by
            rw [fvOccF_neg hF.isUFormula]
            exact add_le_add le_rfl (le_trans (fvOccF_le_formulaLen hF.isUFormula) hg)
        _ ≤ fvOccS LAct Γ + growK B E Q := add_le_add le_rfl hQ1
    · unfold goalCost
      calc 11 * setLen LAct Γ + 27 * (formulaLen LAct (goalFact (sGoalS s) (sGoalU s)) * E) + 2 * E + 42
          ≤ 11 * setLen LAct Γ + 27 * (Q * E) + 2 * E + 42 := by gcongr
        _ = (27 * (Q * E) + 2 * E + 42) + 11 * setLen LAct Γ := by ring
        _ ≤ costK N E B M Q D + (3 * (M : V) + 11) * (setLen LAct Γ + fvOccS LAct Γ) := by
            refine add_le_add ?_ ?_
            · unfold costK
              rw [show stepKM N E B M + 27 * (Q * E) + 2 * E + 7 * Q + D + 42
                = (27 * (Q * E) + 2 * E + 42) + (stepKM N E B M + 7 * Q + D) by ring]
              exact le_self_add
            · exact mul_le_mul le_add_self le_self_add zero_le zero_le
  · -- tag 7
    have hAF := stepOK_tag7_data hok h7
    rw [ctxAfter_tag7 h7, stepCost_tag7 h7]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · calc setLen LAct (insert (neg LAct (sLemA s)) Γ)
          ≤ setLen LAct Γ + formulaLen LAct (neg LAct (sLemA s)) := setLen_insert_le _ _
        _ ≤ setLen LAct Γ + Q := by rw [formulaLen_neg hAF.isUFormula]; exact add_le_add le_rfl hA
        _ ≤ setLen LAct Γ + fvOccS LAct Γ + growK B E Q := by
            rw [add_assoc]; exact add_le_add le_rfl (le_trans hQ1 le_add_self)
    · calc fvOccS LAct (insert (neg LAct (sLemA s)) Γ)
          ≤ fvOccS LAct Γ + fvOccF LAct (neg LAct (sLemA s)) := fvOccS_insert_le _ _
        _ ≤ fvOccS LAct Γ + Q := by
            rw [fvOccF_neg hAF.isUFormula]; exact add_le_add le_rfl (le_trans (fvOccF_le_formulaLen hAF.isUFormula) hA)
        _ ≤ fvOccS LAct Γ + growK B E Q := add_le_add le_rfl hQ1
    · calc dlen TAct (sLemD s) + 2 * setLen LAct Γ + 2 * formulaLen LAct (sLemA s) + 2
          ≤ D + 2 * setLen LAct Γ + 2 * Q + 2 := by gcongr
        _ = (D + 2 * Q + 2) + 2 * setLen LAct Γ := by ring
        _ ≤ costK N E B M Q D + (3 * (M : V) + 11) * (setLen LAct Γ + fvOccS LAct Γ) := by
            refine add_le_add ?_ ?_
            · unfold costK
              calc D + 2 * Q + 2 ≤ D + 7 * Q + 42 := by gcongr <;> norm_num
                _ ≤ stepKM N E B M + 27 * (Q * E) + 2 * E + 7 * Q + D + 42 := by
                    rw [show stepKM N E B M + 27 * (Q * E) + 2 * E + 7 * Q + D + 42
                      = (D + 7 * Q + 42) + (stepKM N E B M + 27 * (Q * E) + 2 * E) by ring]
                    exact le_self_add
            · exact mul_le_mul (by norm_num) le_self_add zero_le zero_le

/-! ### 5.4 The list: additive context growth and the cost sum -/

/-- The uniform context bound of a disciplined list of `L` steps (growth constant `G`). -/
noncomputable def ctxBoundG (G Γ L : V) : V := setLen LAct Γ + L * fvOccS LAct Γ + (L * L + L) * G

theorem ctxVec_len_le_sizeOK (M : ℕ) {tbl N E B Q D Γ S : V} (hE : 1 ≤ E) (htbl : TableOK tbl N)
    (hBt : ∀ j < len tbl, formulaLen LAct (rowB tbl.[j]) ≤ B)
    (hok : ListOK tbl E (M : V) Γ S) (hsz : SizeOK Q D S) :
    ∀ i ≤ len S, fvOccS LAct (ctxVec Γ S).[i] ≤ fvOccS LAct Γ + i * growK B E Q ∧
      setLen LAct (ctxVec Γ S).[i] ≤ setLen LAct Γ + i * fvOccS LAct Γ + (i * i + i) * growK B E Q := by
  intro i
  induction i using ISigma1.pi1_succ_induction with
  | hP => definability
  | zero => intro _; simp
  | succ i ih =>
    intro hi
    have hi' : i < len S := lt_of_lt_of_le (lt_add_one i) hi
    obtain ⟨hO, hG⟩ := ih (le_of_lt hi')
    obtain ⟨⟨hG', hO'⟩, _⟩ := step_grow_cost M hE htbl hBt (hok i hi') (hsz i hi')
    rw [nth_ctxVec_succ Γ S hi']
    constructor
    · calc fvOccS LAct (ctxAfter (ctxVec Γ S).[i] S.[i])
          ≤ fvOccS LAct (ctxVec Γ S).[i] + growK B E Q := hO'
        _ ≤ (fvOccS LAct Γ + i * growK B E Q) + growK B E Q := add_le_add hO le_rfl
        _ = fvOccS LAct Γ + (i + 1) * growK B E Q := by ring
    · calc setLen LAct (ctxAfter (ctxVec Γ S).[i] S.[i])
          ≤ setLen LAct (ctxVec Γ S).[i] + fvOccS LAct (ctxVec Γ S).[i] + growK B E Q := hG'
        _ ≤ (setLen LAct Γ + i * fvOccS LAct Γ + (i * i + i) * growK B E Q)
              + (fvOccS LAct Γ + i * growK B E Q) + growK B E Q := add_le_add (add_le_add hG hO) le_rfl
        _ = setLen LAct Γ + (i + 1) * fvOccS LAct Γ + ((i + 1) * (i + 1)) * growK B E Q := by ring
        _ ≤ setLen LAct Γ + (i + 1) * fvOccS LAct Γ + ((i + 1) * (i + 1) + (i + 1)) * growK B E Q := by
            rw [add_mul ((i + 1) * (i + 1))]; exact add_le_add le_rfl le_self_add

/-- **The cost of a disciplined list**: `len S` times the affine per-step bound at the uniform context bound. -/
theorem costSum_le_of_sizeOK (M : ℕ) {tbl N E B Q D Γ S : V} (hE : 1 ≤ E) (htbl : TableOK tbl N)
    (hBt : ∀ j < len tbl, formulaLen LAct (rowB tbl.[j]) ≤ B)
    (hok : ListOK tbl E (M : V) Γ S) (hsz : SizeOK Q D S) :
    costSum N E Γ S ≤ len S * (costK N E B M Q D +
      (3 * (M : V) + 11) * (ctxBoundG (growK B E Q) Γ (len S) + (fvOccS LAct Γ + len S * growK B E Q))) := by
  have hbound := ctxVec_len_le_sizeOK M hE htbl hBt hok hsz
  set K := costK N E B M Q D +
    (3 * (M : V) + 11) * (ctxBoundG (growK B E Q) Γ (len S) + (fvOccS LAct Γ + len S * growK B E Q)) with hK
  have hctx : ∀ i ≤ len S, setLen LAct (ctxVec Γ S).[i] + fvOccS LAct (ctxVec Γ S).[i] ≤
      ctxBoundG (growK B E Q) Γ (len S) + (fvOccS LAct Γ + len S * growK B E Q) := by
    intro i hi
    obtain ⟨hO, hG⟩ := hbound i hi
    refine add_le_add (le_trans hG ?_) (le_trans hO ?_)
    · unfold ctxBoundG; gcongr
    · gcongr
  have key : ∀ j ≤ len S, costAux N E (ctxVec Γ S) S j ≤ j * K := by
    intro j
    induction j using ISigma1.pi1_succ_induction with
    | hP => definability
    | zero => intro _; simp
    | succ j ihj =>
      intro hj
      have hj' : j ≤ len S := le_trans le_self_add hj
      obtain ⟨i, hi⟩ : ∃ i, len S = i + (j + 1) := ⟨len S - (j + 1), (tsub_add_cancel_of_le hj).symm⟩
      have hi' : i < len S := by rw [hi]; exact lt_add_of_pos_right _ (lt_of_lt_of_le _root_.zero_lt_one le_add_self)
      have hC : nthFromEnd (ctxVec Γ S) (j + 1) = (ctxVec Γ S).[i] :=
        nthFromEnd_eq (a := i) (by rw [len_ctxVec, hi, add_assoc])
      have hS : nthFromEnd S j = S.[i] := nthFromEnd_eq (a := i) hi
      rw [costAux_succ, hC, hS]
      obtain ⟨_, hc⟩ := step_grow_cost M hE htbl hBt (hok i hi') (hsz i hi')
      calc costAux N E (ctxVec Γ S) S j + stepCost N E (ctxVec Γ S).[i] S.[i]
          ≤ j * K + (costK N E B M Q D + (3 * (M : V) + 11) * (setLen LAct (ctxVec Γ S).[i] + fvOccS LAct (ctxVec Γ S).[i])) :=
            add_le_add (ihj hj') hc
        _ ≤ j * K + K := by
            rw [hK]; exact add_le_add le_rfl (add_le_add le_rfl (mul_le_mul_of_nonneg_left (hctx i (le_of_lt hi')) zero_le))
        _ = (j + 1) * K := by ring
  exact key (len S) le_rfl

/-! ### 5.5 The size discipline of each producer -/

lemma ftag_eqRefl {W : V} (hWp : W = frag1Pieces) (ev : V) : sTag (mkStep W (41 : V) ev) = 0 := by
  subst hWp
  have e : mkStep frag1Pieces (41 : V) ev = mkStep layoutPieces (41 : V) ev := by
    have := mkStep_frag1Pieces_lt 41 (by decide) ev; simpa using this
  rw [e]; exact ltag_eqRefl rfl ev

lemma stepSizeOK_horn0 {Q D W i ev : V} (h : sTag (mkStep W i ev) = 0) : StepSizeOK Q D (mkStep W i ev) := Or.inl h
lemma stepSizeOK_horn2 {Q D W i ev : V} (h : sTag (mkStep W i ev) = 2) : StepSizeOK Q D (mkStep W i ev) :=
  Or.inr (Or.inr (Or.inl h))
lemma stepSizeOK_sLemma {Q D A dA : V} (hA : formulaLen LAct A ≤ Q) (hd : dlen TAct dA ≤ D) :
    StepSizeOK Q D (sLemma A dA) :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by simp, by simpa using hA, by simpa using hd⟩)))))
lemma stepSizeOK_sGoal {Q D e n s u : V} (h : formulaLen LAct (goalFact s u) ≤ Q) : StepSizeOK Q D (sGoal e n s u) :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by simp, by simpa using h⟩)))))
lemma stepSizeOK_sElimExs {Q D P : V} (h : formulaLen LAct P ≤ Q) : StepSizeOK Q D (sElimExs P) :=
  Or.inr (Or.inr (Or.inr (Or.inl ⟨by simp, by simpa [sElimExs] using h⟩)))
lemma stepSizeOK_sSplit {Q D p q : V} (h : formulaLen LAct p + formulaLen LAct q ≤ Q) : StepSizeOK Q D (sSplit p q) :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by simp, by simpa [sSplit] using h⟩))))

/-- **`goalElim` is disciplined at `Q = 4·|goalFact s u|`** (through its two `free` equations). -/
theorem sizeOK_goalElim {D s u : V} (hs : IsSemiterm LAct 0 s) (hu : IsSemiterm LAct 0 u) :
    SizeOK (4 * formulaLen LAct (goalFact s u)) D (goalElim s u) := by
  set G := formulaLen LAct (goalFact s u) with hGdef
  have hs'0 : IsSemiterm LAct 0 (termShift LAct s) := hs.termShift
  have hu'0 : IsSemiterm LAct 0 (termShift LAct u) := hu.termShift
  have hs''0 : IsSemiterm LAct 0 (termShift LAct (termShift LAct s)) := hs'0.termShift
  have hu''0 : IsSemiterm LAct 0 (termShift LAct (termShift LAct u)) := hu'0.termShift
  have hf1 : IsSemiterm LAct 0 (^&1 : V) := by simp
  have hf0 : IsSemiterm LAct 0 (^&0 : V) := by simp
  have hB2 : IsSemiformula LAct ((2 : ℕ) : V) (goalBody s u) := isSemiformula_goalBody hs hu
  have hP1 : IsSemiformula LAct 1 (^∃ goalBody s u) := by
    have := isSemiformula_exs_cast (m := 1) (p := goalBody s u) hB2
    simpa using this
  have hP2 : IsSemiformula LAct 1 (goalBody1 (termShift LAct s) (termShift LAct u)) := by
    simpa using isSemiformula_goalBody1 hs'0 hu'0
  -- |∃ goalBody| + 1 = |goalFact|
  have e1 : formulaLen LAct (^∃ goalBody s u) + 1 = G := by
    rw [hGdef, show goalFact s u = ^∃ (^∃ goalBody s u) from rfl, formulaLen_exs hP1.isUFormula]
  have h1 : formulaLen LAct (^∃ goalBody s u) ≤ G := by rw [← e1]; exact le_self_add
  -- |goalBody1| + 1 = |free (∃ goalBody)| ≤ 2|∃ goalBody|
  have e2 : formulaLen LAct (goalBody1 (termShift LAct s) (termShift LAct u)) + 1 =
      formulaLen LAct (free LAct (^∃ goalBody s u)) := by
    rw [free_exs_goalBody hs hu, formulaLen_exs hP2.isUFormula]
  have h2 : formulaLen LAct (goalBody1 (termShift LAct s) (termShift LAct u)) ≤ 2 * G := by
    have := formulaLen_free_le hP1
    rw [← e2] at this
    exact le_trans le_self_add (le_trans this (mul_le_mul_of_nonneg_left h1 zero_le))
  -- |goalInst| = |free goalBody1| ≤ 2|goalBody1|
  have hA₁ : IsFormula LAct (derFact (^&1 : V)) := isFormula_derFact hf1
  have hA₂ : IsFormula LAct (fstIdxFact (termShift LAct (termShift LAct s)) (^&1)) := isFormula_fstIdxFact hs''0 hf1
  have hA₃ : IsFormula LAct (dlenFact (^&1 : V) (^&0)) := isFormula_dlenFact hf1 hf0
  have hA₄ : IsFormula LAct (leFact (^&0) (termShift LAct (termShift LAct u))) := isFormula_leFact hf0 hu''0
  have hR₂ : IsFormula LAct (dlenFact (^&1 : V) (^&0) ^⋏ leFact (^&0) (termShift LAct (termShift LAct u))) := by simp [hA₃, hA₄]
  have hR₁ : IsFormula LAct (fstIdxFact (termShift LAct (termShift LAct s)) (^&1) ^⋏
      (dlenFact (^&1 : V) (^&0) ^⋏ leFact (^&0) (termShift LAct (termShift LAct u)))) := by simp [hA₂, hR₂]
  have e3 : formulaLen LAct (goalInst (^&1) (^&0) (termShift LAct (termShift LAct s)) (termShift LAct (termShift LAct u))) =
      formulaLen LAct (free LAct (goalBody1 (termShift LAct s) (termShift LAct u))) := by
    rw [free_goalBody1 hs'0 hu'0]
  have h3 : formulaLen LAct (goalInst (^&1) (^&0) (termShift LAct (termShift LAct s)) (termShift LAct (termShift LAct u))) ≤ 4 * G := by
    rw [e3]
    exact le_trans (formulaLen_free_le hP2) (le_trans (mul_le_mul_of_nonneg_left h2 zero_le) (le_of_eq (by ring)))
  have hInst : goalInst (^&1) (^&0) (termShift LAct (termShift LAct s)) (termShift LAct (termShift LAct u)) =
      derFact (^&1) ^⋏ (fstIdxFact (termShift LAct (termShift LAct s)) (^&1) ^⋏
        (dlenFact (^&1) (^&0) ^⋏ leFact (^&0) (termShift LAct (termShift LAct u)))) := rfl
  rw [hInst, formulaLen_and hA₁.isUFormula hR₁.isUFormula] at h3
  have h4 : formulaLen LAct (derFact (^&1 : V)) + formulaLen LAct (fstIdxFact (termShift LAct (termShift LAct s)) (^&1) ^⋏
      (dlenFact (^&1 : V) (^&0) ^⋏ leFact (^&0) (termShift LAct (termShift LAct u)))) ≤ 4 * G := le_trans le_self_add h3
  have h5 : formulaLen LAct (fstIdxFact (termShift LAct (termShift LAct s)) (^&1)) +
      formulaLen LAct (dlenFact (^&1 : V) (^&0) ^⋏ leFact (^&0) (termShift LAct (termShift LAct u))) ≤ 4 * G := by
    have := le_trans le_add_self h4
    rw [formulaLen_and hA₂.isUFormula hR₂.isUFormula] at this
    exact le_trans le_self_add this
  have h6 : formulaLen LAct (dlenFact (^&1 : V) (^&0)) + formulaLen LAct (leFact (^&0) (termShift LAct (termShift LAct u))) ≤ 4 * G := by
    have := le_trans le_add_self h5
    rw [formulaLen_and hA₃.isUFormula hA₄.isUFormula] at this
    exact le_trans le_self_add this
  unfold goalElim
  refine sizeOK_cons (stepSizeOK_sElimExs (le_trans h1 (by rw [show 4 * G = G + 3 * G by ring]; exact le_self_add)))
    (sizeOK_cons (stepSizeOK_sElimExs (le_trans h2 (by rw [show 4 * G = 2 * G + 2 * G by ring]; exact le_self_add)))
    (sizeOK_cons (stepSizeOK_sSplit h4) (sizeOK_cons (stepSizeOK_sSplit h5) (sizeOK_single (stepSizeOK_sSplit h6)))))

theorem costSum_goalElim_le (M : ℕ) {tbl N E B Γ s u : V} (hE : 1 ≤ E) (htbl : TableOK tbl N)
    (hBt : ∀ j < len tbl, formulaLen LAct (rowB tbl.[j]) ≤ B) (hΓ : IsFormulaSet LAct Γ)
    (hs : IsSemiterm LAct 0 s) (hu : IsSemiterm LAct 0 u) (hg : neg LAct (goalFact s u) ∈ Γ) :
    costSum N E Γ (goalElim s u) ≤ 5 * (costK N E B M (4 * formulaLen LAct (goalFact s u)) 0 +
      (3 * (M : V) + 11) * (ctxBoundG (growK B E (4 * formulaLen LAct (goalFact s u))) Γ 5 +
        (fvOccS LAct Γ + 5 * growK B E (4 * formulaLen LAct (goalFact s u))))) := by
  have := costSum_le_of_sizeOK M hE htbl hBt (goalElim_ok M htbl hΓ hs hu hg).1 (sizeOK_goalElim (D := 0) hs hu)
  rwa [len_goalElim] at this

/-- The size discipline of the tails: `Q` dominates the closed lemma fact, `D` its derivation. -/
theorem sizeOK_dlenLeafSteps {Q D W tblN l L n : V} (hWp : W = frag1Pieces)
    (hA : formulaLen LAct (leafFact L n) ≤ Q) (hD : dlen TAct (leafCode tblN L n) ≤ D) :
    SizeOK Q D (dlenLeafSteps W tblN l L n) := by
  unfold dlenLeafSteps
  exact sizeOK_cons (stepSizeOK_horn0 (ftag_eqRefl hWp _)) (sizeOK_cons (stepSizeOK_horn0 (ftag_dlenLeafLe hWp _))
    (sizeOK_cons (stepSizeOK_sLemma hA hD) (sizeOK_single (stepSizeOK_horn0 (ftag_leTrans hWp _)))))
theorem sizeOK_dlenUnarySteps {Q D W tblN l n₁ L m₁ n : V} (hWp : W = frag1Pieces)
    (hA : formulaLen LAct (bin2Fact L m₁ n) ≤ Q) (hD : dlen TAct (bin2Code tblN L m₁ n) ≤ D) :
    SizeOK Q D (dlenUnarySteps W tblN l n₁ L m₁ n) := by
  unfold dlenUnarySteps
  exact sizeOK_cons (stepSizeOK_horn0 (ftag_eqRefl hWp _)) (sizeOK_cons (stepSizeOK_horn0 (ftag_dlenUnaryLe hWp _))
    (sizeOK_cons (stepSizeOK_sLemma hA hD) (sizeOK_single (stepSizeOK_horn0 (ftag_leTrans hWp _)))))
theorem sizeOK_dlenBinarySteps {Q D W tblN l n₁ n₂ L m₁ m₂ n : V} (hWp : W = frag1Pieces)
    (hA : formulaLen LAct (bin3Fact L m₁ m₂ n) ≤ Q) (hD : dlen TAct (bin3Code tblN L m₁ m₂ n) ≤ D) :
    SizeOK Q D (dlenBinarySteps W tblN l n₁ n₂ L m₁ m₂ n) := by
  unfold dlenBinarySteps
  exact sizeOK_cons (stepSizeOK_horn0 (ftag_eqRefl hWp _)) (sizeOK_cons (stepSizeOK_horn0 (ftag_dlenBinaryLe hWp _))
    (sizeOK_cons (stepSizeOK_sLemma hA hD) (sizeOK_single (stepSizeOK_horn0 (ftag_leTrans hWp _)))))

theorem sizeOK_goalTailLeaf {Q D W tblN l L n s : V} (hWp : W = frag1Pieces)
    (hA : formulaLen LAct (leafFact L n) ≤ Q) (hD : dlen TAct (leafCode tblN L n) ≤ D)
    (hg : formulaLen LAct (goalFact (^&s) (bnum n)) ≤ Q) : SizeOK Q D (goalTailLeaf W tblN l L n s) :=
  sizeOK_appendV (sizeOK_dlenLeafSteps hWp hA hD) (sizeOK_single (stepSizeOK_sGoal hg))
theorem sizeOK_goalTailUnary {Q D W tblN l n₁ L m₁ n s : V} (hWp : W = frag1Pieces)
    (hA : formulaLen LAct (bin2Fact L m₁ n) ≤ Q) (hD : dlen TAct (bin2Code tblN L m₁ n) ≤ D)
    (hg : formulaLen LAct (goalFact (^&s) (bnum n)) ≤ Q) : SizeOK Q D (goalTailUnary W tblN l n₁ L m₁ n s) :=
  sizeOK_appendV (sizeOK_dlenUnarySteps hWp hA hD) (sizeOK_single (stepSizeOK_sGoal hg))
theorem sizeOK_goalTailBinary {Q D W tblN l n₁ n₂ L m₁ m₂ n s : V} (hWp : W = frag1Pieces)
    (hA : formulaLen LAct (bin3Fact L m₁ m₂ n) ≤ Q) (hD : dlen TAct (bin3Code tblN L m₁ m₂ n) ≤ D)
    (hg : formulaLen LAct (goalFact (^&s) (bnum n)) ≤ Q) : SizeOK Q D (goalTailBinary W tblN l n₁ n₂ L m₁ m₂ n s) :=
  sizeOK_appendV (sizeOK_dlenBinarySteps hWp hA hD) (sizeOK_single (stepSizeOK_sGoal hg))

/-- The closed lemma facts are `|Ple|·E`-small once `E` bounds the numeral terms. -/
lemma formulaLen_leafFact_le {B E L n : V} (hE : 1 ≤ E) (hPle : formulaLen LAct (Ple : V) ≤ B)
    (hn : 18 * ‖n‖ + 7 ≤ E) (hLn : L ≤ n) : formulaLen LAct (leafFact L n) ≤ B * E :=
  le_trans (formulaLen_leFact_le hE (isSemiterm_qqAdd_LAct (isSemiterm_bnum_LAct 0 L) (isSemiterm_qqOne_LAct 0))
    (isSemiterm_bnum_LAct 0 n) (le_trans (termLen_leafT_le hLn) hn) (termLen_bnum_le_bkE le_rfl hn))
    (mul_le_mul_of_nonneg_right hPle zero_le)
lemma formulaLen_bin2Fact_le {B E L m n : V} (hE : 1 ≤ E) (hPle : formulaLen LAct (Ple : V) ≤ B)
    (hn : 18 * ‖n‖ + 7 ≤ E) (hL : L ≤ n) (hm : m ≤ n) : formulaLen LAct (bin2Fact L m n) ≤ B * E :=
  le_trans (formulaLen_leFact_le hE
    (isSemiterm_qqAdd_LAct (isSemiterm_qqAdd_LAct (isSemiterm_bnum_LAct 0 L) (isSemiterm_bnum_LAct 0 m)) (isSemiterm_qqOne_LAct 0))
    (isSemiterm_bnum_LAct 0 n) (le_trans (termLen_bin2T_le hL hm) hn) (termLen_bnum_le_bkE le_rfl hn))
    (mul_le_mul_of_nonneg_right hPle zero_le)
lemma formulaLen_bin3Fact_le {B E L m₁ m₂ n : V} (hE : 1 ≤ E) (hPle : formulaLen LAct (Ple : V) ≤ B)
    (hn : 18 * ‖n‖ + 7 ≤ E) (hL : L ≤ n) (hm₁ : m₁ ≤ n) (hm₂ : m₂ ≤ n) : formulaLen LAct (bin3Fact L m₁ m₂ n) ≤ B * E :=
  le_trans (formulaLen_leFact_le hE
    (isSemiterm_qqAdd_LAct (isSemiterm_qqAdd_LAct (isSemiterm_qqAdd_LAct (isSemiterm_bnum_LAct 0 L) (isSemiterm_bnum_LAct 0 m₁))
      (isSemiterm_bnum_LAct 0 m₂)) (isSemiterm_qqOne_LAct 0))
    (isSemiterm_bnum_LAct 0 n) (le_trans (termLen_bin3T_le hL hm₁ hm₂) hn) (termLen_bnum_le_bkE le_rfl hn))
    (mul_le_mul_of_nonneg_right hPle zero_le)

/-! ### 5.6 The fragments' costs -/

/-- The size discipline of `fragAxL`: `Q` dominates `B·E` (the closed leaf fact) and the node's goal fact. -/
theorem sizeOK_fragAxL {Q D W tblN is il ip inp L n : V} (hWp : W = frag1Pieces)
    (hA : formulaLen LAct (leafFact L n) ≤ Q) (hD : dlen TAct (leafCode tblN L n) ≤ D)
    (hg : formulaLen LAct (goalFact (^&(is + 1)) (bnum n)) ≤ Q) : SizeOK Q D (fragAxL W tblN is il ip inp L n) := by
  unfold fragAxL fragAxLHead
  exact sizeOK_appendV (sizeOK_cons (stepSizeOK_horn2 (ftag_totAxL hWp _)) (sizeOK_cons (stepSizeOK_horn0 (ftag_fstIdxAxL hWp _))
    (sizeOK_cons (stepSizeOK_horn0 (ftag_introAxL hWp _)) (sizeOK_single (stepSizeOK_horn0 (ftag_dlenAxL hWp _))))))
    (sizeOK_goalTailLeaf hWp hA hD hg)

/-- **The cost of `fragAxL`** (§5's shape): nine steps, each `≤ costK + (3·8+11)·ctxBound`, with `Q :=
B·E + |goalFact &(is+1) (bnum n)|` (the closed leaf fact and the goal fact) and `D := dlen (leafCode tblN L n)`. -/
theorem costSum_fragAxL_le {tbl N E B Γ W tblN N' B' is il ip inp L n : V} (htbl : TableOK tbl N) (hF : Frag1Table tbl)
    (hWp : W = frag1Pieces) (htblN : NumTableOK tblN N' B') (hΓ : IsFormulaSet LAct Γ)
    (hBt : ∀ j < len tbl, formulaLen LAct (rowB tbl.[j]) ≤ B) (hPle : formulaLen LAct (Ple : V) ≤ B)
    (his : is + 2 ≤ E) (hil : il + 4 ≤ E) (hip : ip + 2 ≤ E) (hinp : inp + 2 ≤ E) (hn : 18 * ‖n‖ + 7 ≤ E)
    (hLn : L + 1 ≤ n)
    (hfs : neg LAct (fsetPiFact (^&is)) ∈ Γ) (hmp : neg LAct (memFact (^&ip) (^&is)) ∈ Γ)
    (hneg : neg LAct (negFact (^&inp) (^&ip)) ∈ Γ) (hmnp : neg LAct (memFact (^&inp) (^&is)) ∈ Γ)
    (hsl : neg LAct (setLenFact (^&il) (^&is)) ∈ Γ) (hle : neg LAct (leFact (^&il) (bnum L)) ∈ Γ) :
    costSum N E Γ (fragAxL W tblN is il ip inp L n) ≤
      9 * (costK N E B 8 (B * E + formulaLen LAct (goalFact (^&(is + 1)) (bnum n))) (dlen TAct (leafCode tblN L n)) +
        (3 * ((8 : ℕ) : V) + 11) * (ctxBoundG (growK B E (B * E + formulaLen LAct (goalFact (^&(is + 1)) (bnum n)))) Γ 9 +
          (fvOccS LAct Γ + 9 * growK B E (B * E + formulaLen LAct (goalFact (^&(is + 1)) (bnum n)))))) := by
  have hE : 1 ≤ E := le_trans (by norm_num) (le_trans le_add_self hn)
  obtain ⟨hok, _, _, hlen, _⟩ := fragAxL_ok htbl hF hWp htblN hΓ his hil hip hinp hn hLn hfs hmp hneg hmnp hsl hle
  have hsz := sizeOK_fragAxL (W := W) (tblN := tblN) (is := is) (il := il) (ip := ip) (inp := inp) hWp
    (le_trans (formulaLen_leafFact_le hE hPle hn (le_trans le_self_add hLn)) le_self_add)
    (le_refl (dlen TAct (leafCode tblN L n))) le_add_self
  have := costSum_le_of_sizeOK 8 hE htbl hBt hok hsz
  rwa [hlen] at this

theorem sizeOK_fragVerum {Q D W tblN is il iv L n : V} (hWp : W = frag1Pieces)
    (hA : formulaLen LAct (leafFact L n) ≤ Q) (hD : dlen TAct (leafCode tblN L n) ≤ D)
    (hg : formulaLen LAct (goalFact (^&(is + 1)) (bnum n)) ≤ Q) : SizeOK Q D (fragVerum W tblN is il iv L n) := by
  unfold fragVerum fragVerumHead
  exact sizeOK_appendV (sizeOK_cons (stepSizeOK_horn2 (ftag_totVerumIntro hWp _)) (sizeOK_cons (stepSizeOK_horn0 (ftag_fstIdxVerum hWp _))
    (sizeOK_cons (stepSizeOK_horn0 (ftag_introVerum hWp _)) (sizeOK_single (stepSizeOK_horn0 (ftag_dlenVerum hWp _))))))
    (sizeOK_goalTailLeaf hWp hA hD hg)

theorem costSum_fragVerum_le {tbl N E B Γ W tblN N' B' is il iv L n : V} (htbl : TableOK tbl N) (hF : Frag1Table tbl)
    (hWp : W = frag1Pieces) (htblN : NumTableOK tblN N' B') (hΓ : IsFormulaSet LAct Γ)
    (hBt : ∀ j < len tbl, formulaLen LAct (rowB tbl.[j]) ≤ B) (hPle : formulaLen LAct (Ple : V) ≤ B)
    (his : is + 2 ≤ E) (hil : il + 4 ≤ E) (hiv : iv + 2 ≤ E) (hn : 18 * ‖n‖ + 7 ≤ E) (hLn : L + 1 ≤ n)
    (hfs : neg LAct (fsetPiFact (^&is)) ∈ Γ) (hv : neg LAct (verumFact (^&iv)) ∈ Γ)
    (hmv : neg LAct (memFact (^&iv) (^&is)) ∈ Γ) (hsl : neg LAct (setLenFact (^&il) (^&is)) ∈ Γ)
    (hle : neg LAct (leFact (^&il) (bnum L)) ∈ Γ) :
    costSum N E Γ (fragVerum W tblN is il iv L n) ≤
      9 * (costK N E B 8 (B * E + formulaLen LAct (goalFact (^&(is + 1)) (bnum n))) (dlen TAct (leafCode tblN L n)) +
        (3 * ((8 : ℕ) : V) + 11) * (ctxBoundG (growK B E (B * E + formulaLen LAct (goalFact (^&(is + 1)) (bnum n)))) Γ 9 +
          (fvOccS LAct Γ + 9 * growK B E (B * E + formulaLen LAct (goalFact (^&(is + 1)) (bnum n)))))) := by
  have hE : 1 ≤ E := le_trans (by norm_num) (le_trans le_add_self hn)
  obtain ⟨hok, _, _, hlen, _⟩ := fragVerum_ok htbl hF hWp htblN hΓ his hil hiv hn hLn hfs hv hmv hsl hle
  have hsz := sizeOK_fragVerum (W := W) (tblN := tblN) (is := is) (il := il) (iv := iv) hWp
    (le_trans (formulaLen_leafFact_le hE hPle hn (le_trans le_self_add hLn)) le_self_add)
    (le_refl (dlen TAct (leafCode tblN L n))) le_add_self
  have := costSum_le_of_sizeOK 8 hE htbl hBt hok hsz
  rwa [hlen] at this

theorem sizeOK_nodeAnd {Q D W tblN is il ir ip iq id₁ id₂ icp icq in₁ in₂ L m₁ m₂ n : V} (hWp : W = frag1Pieces)
    (hA : formulaLen LAct (bin3Fact L m₁ m₂ n) ≤ Q) (hD : dlen TAct (bin3Code tblN L m₁ m₂ n) ≤ D)
    (hg : formulaLen LAct (goalFact (^&(is + 1)) (bnum n)) ≤ Q) :
    SizeOK Q D (nodeAnd W tblN is il ir ip iq id₁ id₂ icp icq in₁ in₂ L m₁ m₂ n) := by
  unfold nodeAnd nodeAndHead
  exact sizeOK_appendV (sizeOK_cons (stepSizeOK_horn2 (ftag_totAndIntro hWp _)) (sizeOK_cons (stepSizeOK_horn0 (ftag_fstIdxAnd hWp _))
    (sizeOK_cons (stepSizeOK_horn0 (ftag_introAnd hWp _)) (sizeOK_single (stepSizeOK_horn0 (ftag_dlenAnd hWp _))))))
    (sizeOK_goalTailBinary hWp hA hD hg)

theorem costSum_nodeAnd_le {tbl N E B Γ W tblN N' B' is il ir ip iq id₁ id₂ icp icq in₁ in₂ L m₁ m₂ n : V}
    (htbl : TableOK tbl N) (hF : Frag1Table tbl) (hWp : W = frag1Pieces) (htblN : NumTableOK tblN N' B')
    (hΓ : IsFormulaSet LAct Γ)
    (hBt : ∀ j < len tbl, formulaLen LAct (rowB tbl.[j]) ≤ B) (hPle : formulaLen LAct (Ple : V) ≤ B)
    (his : is + 2 ≤ E) (hir : ir + 2 ≤ E) (hip : ip + 2 ≤ E) (hiq : iq + 2 ≤ E)
    (hid₁ : id₁ + 2 ≤ E) (hid₂ : id₂ + 2 ≤ E) (hicp : icp + 2 ≤ E) (hicq : icq + 2 ≤ E)
    (hT : il + in₁ + in₂ + 10 ≤ E) (hn : 18 * ‖n‖ + 7 ≤ E) (hLn : L + m₁ + m₂ + 1 ≤ n)
    (hand : neg LAct (andFact (^&ir) (^&ip) (^&iq)) ∈ Γ) (hmr : neg LAct (memFact (^&ir) (^&is)) ∈ Γ)
    (hf₁ : neg LAct (fstIdxFact (^&icp) (^&id₁)) ∈ Γ) (hi₁ : neg LAct (insFact (^&icp) (^&ip) (^&is)) ∈ Γ)
    (hd₁ : neg LAct (derFact (^&id₁ : V)) ∈ Γ) (hn₁ : neg LAct (dlenFact (^&id₁ : V) (^&in₁)) ∈ Γ)
    (hle₁ : neg LAct (leFact (^&in₁) (bnum m₁)) ∈ Γ)
    (hf₂ : neg LAct (fstIdxFact (^&icq) (^&id₂)) ∈ Γ) (hi₂ : neg LAct (insFact (^&icq) (^&iq) (^&is)) ∈ Γ)
    (hd₂ : neg LAct (derFact (^&id₂ : V)) ∈ Γ) (hn₂ : neg LAct (dlenFact (^&id₂ : V) (^&in₂)) ∈ Γ)
    (hle₂ : neg LAct (leFact (^&in₂) (bnum m₂)) ∈ Γ)
    (hsl : neg LAct (setLenFact (^&il) (^&is)) ∈ Γ) (hle : neg LAct (leFact (^&il) (bnum L)) ∈ Γ) :
    costSum N E Γ (nodeAnd W tblN is il ir ip iq id₁ id₂ icp icq in₁ in₂ L m₁ m₂ n) ≤
      9 * (costK N E B 9 (B * E + formulaLen LAct (goalFact (^&(is + 1)) (bnum n))) (dlen TAct (bin3Code tblN L m₁ m₂ n)) +
        (3 * ((9 : ℕ) : V) + 11) * (ctxBoundG (growK B E (B * E + formulaLen LAct (goalFact (^&(is + 1)) (bnum n)))) Γ 9 +
          (fvOccS LAct Γ + 9 * growK B E (B * E + formulaLen LAct (goalFact (^&(is + 1)) (bnum n)))))) := by
  have hE : 1 ≤ E := le_trans (by norm_num) (le_trans le_add_self hn)
  have hLn' : L + m₁ + m₂ ≤ n := le_trans le_self_add hLn
  obtain ⟨hok, _, _, hlen, _⟩ := nodeAnd_ok htbl hF hWp htblN hΓ his hir hip hiq hid₁ hid₂ hicp hicq hT hn hLn
    hand hmr hf₁ hi₁ hd₁ hn₁ hle₁ hf₂ hi₂ hd₂ hn₂ hle₂ hsl hle
  have hsz := sizeOK_nodeAnd (W := W) (tblN := tblN) (is := is) (il := il) (ir := ir) (ip := ip) (iq := iq)
    (id₁ := id₁) (id₂ := id₂) (icp := icp) (icq := icq) (in₁ := in₁) (in₂ := in₂) hWp
    (le_trans (formulaLen_bin3Fact_le hE hPle hn (le_trans (le_trans le_self_add le_self_add) hLn')
      (le_trans (le_trans le_add_self le_self_add) hLn') (le_trans le_add_self hLn')) le_self_add)
    (le_refl (dlen TAct (bin3Code tblN L m₁ m₂ n))) le_add_self
  have := costSum_le_of_sizeOK 9 hE htbl hBt hok hsz
  rwa [hlen] at this

theorem sizeOK_nodeOr {Q D W tblN is il ir ip iq id icq ic in₁ L m₁ n : V} (hWp : W = frag1Pieces)
    (hA : formulaLen LAct (bin2Fact L m₁ n) ≤ Q) (hD : dlen TAct (bin2Code tblN L m₁ n) ≤ D)
    (hg : formulaLen LAct (goalFact (^&(is + 1)) (bnum n)) ≤ Q) :
    SizeOK Q D (nodeOr W tblN is il ir ip iq id icq ic in₁ L m₁ n) := by
  unfold nodeOr nodeOrHead
  exact sizeOK_appendV (sizeOK_cons (stepSizeOK_horn2 (ftag_totOrIntro hWp _)) (sizeOK_cons (stepSizeOK_horn0 (ftag_fstIdxOr hWp _))
    (sizeOK_cons (stepSizeOK_horn0 (ftag_introOr hWp _)) (sizeOK_single (stepSizeOK_horn0 (ftag_dlenOr hWp _))))))
    (sizeOK_goalTailUnary hWp hA hD hg)

theorem costSum_nodeOr_le {tbl N E B Γ W tblN N' B' is il ir ip iq id icq ic in₁ L m₁ n : V}
    (htbl : TableOK tbl N) (hF : Frag1Table tbl) (hWp : W = frag1Pieces) (htblN : NumTableOK tblN N' B')
    (hΓ : IsFormulaSet LAct Γ)
    (hBt : ∀ j < len tbl, formulaLen LAct (rowB tbl.[j]) ≤ B) (hPle : formulaLen LAct (Ple : V) ≤ B)
    (his : is + 2 ≤ E) (hir : ir + 2 ≤ E) (hip : ip + 2 ≤ E) (hiq : iq + 2 ≤ E)
    (hid : id + 2 ≤ E) (hicq : icq + 2 ≤ E) (hic : ic + 2 ≤ E)
    (hT : il + in₁ + 7 ≤ E) (hn : 18 * ‖n‖ + 7 ≤ E) (hLn : L + m₁ + 1 ≤ n)
    (hor : neg LAct (orFact (^&ir) (^&ip) (^&iq)) ∈ Γ) (hmr : neg LAct (memFact (^&ir) (^&is)) ∈ Γ)
    (hf : neg LAct (fstIdxFact (^&ic) (^&id)) ∈ Γ) (hiq' : neg LAct (insFact (^&icq) (^&iq) (^&is)) ∈ Γ)
    (hip' : neg LAct (insFact (^&ic) (^&ip) (^&icq)) ∈ Γ)
    (hd : neg LAct (derFact (^&id : V)) ∈ Γ) (hn₁ : neg LAct (dlenFact (^&id : V) (^&in₁)) ∈ Γ)
    (hle₁ : neg LAct (leFact (^&in₁) (bnum m₁)) ∈ Γ)
    (hsl : neg LAct (setLenFact (^&il) (^&is)) ∈ Γ) (hle : neg LAct (leFact (^&il) (bnum L)) ∈ Γ) :
    costSum N E Γ (nodeOr W tblN is il ir ip iq id icq ic in₁ L m₁ n) ≤
      9 * (costK N E B 8 (B * E + formulaLen LAct (goalFact (^&(is + 1)) (bnum n))) (dlen TAct (bin2Code tblN L m₁ n)) +
        (3 * ((8 : ℕ) : V) + 11) * (ctxBoundG (growK B E (B * E + formulaLen LAct (goalFact (^&(is + 1)) (bnum n)))) Γ 9 +
          (fvOccS LAct Γ + 9 * growK B E (B * E + formulaLen LAct (goalFact (^&(is + 1)) (bnum n)))))) := by
  have hE : 1 ≤ E := le_trans (by norm_num) (le_trans le_add_self hn)
  have hLn' : L + m₁ ≤ n := le_trans le_self_add hLn
  obtain ⟨hok, _, _, hlen, _⟩ := nodeOr_ok htbl hF hWp htblN hΓ his hir hip hiq hid hicq hic hT hn hLn
    hor hmr hf hiq' hip' hd hn₁ hle₁ hsl hle
  have hsz := sizeOK_nodeOr (W := W) (tblN := tblN) (is := is) (il := il) (ir := ir) (ip := ip) (iq := iq)
    (id := id) (icq := icq) (ic := ic) (in₁ := in₁) hWp
    (le_trans (formulaLen_bin2Fact_le hE hPle hn (le_trans le_self_add hLn') (le_trans le_add_self hLn')) le_self_add)
    (le_refl (dlen TAct (bin2Code tblN L m₁ n))) le_add_self
  have := costSum_le_of_sizeOK 8 hE htbl hBt hok hsz
  rwa [hlen] at this

theorem sizeOK_nodeWk {Q D W tblN is il ic id in₁ L m₁ n : V} (hWp : W = frag1Pieces)
    (hA : formulaLen LAct (bin2Fact L m₁ n) ≤ Q) (hD : dlen TAct (bin2Code tblN L m₁ n) ≤ D)
    (hg : formulaLen LAct (goalFact (^&(is + 1)) (bnum n)) ≤ Q) :
    SizeOK Q D (nodeWk W tblN is il ic id in₁ L m₁ n) := by
  unfold nodeWk nodeWkHead
  exact sizeOK_appendV (sizeOK_cons (stepSizeOK_horn2 (ftag_totWkRule hWp _)) (sizeOK_cons (stepSizeOK_horn0 (ftag_fstIdxWk hWp _))
    (sizeOK_cons (stepSizeOK_horn0 (ftag_introWk hWp _)) (sizeOK_single (stepSizeOK_horn0 (ftag_dlenWk hWp _))))))
    (sizeOK_goalTailUnary hWp hA hD hg)

theorem costSum_nodeWk_le {tbl N E B Γ W tblN N' B' is il ic id in₁ L m₁ n : V}
    (htbl : TableOK tbl N) (hF : Frag1Table tbl) (hWp : W = frag1Pieces) (htblN : NumTableOK tblN N' B')
    (hΓ : IsFormulaSet LAct Γ)
    (hBt : ∀ j < len tbl, formulaLen LAct (rowB tbl.[j]) ≤ B) (hPle : formulaLen LAct (Ple : V) ≤ B)
    (his : is + 2 ≤ E) (hic : ic + 2 ≤ E) (hid : id + 2 ≤ E)
    (hT : il + in₁ + 7 ≤ E) (hn : 18 * ‖n‖ + 7 ≤ E) (hLn : L + m₁ + 1 ≤ n)
    (hfs : neg LAct (fsetPiFact (^&is)) ∈ Γ) (hf : neg LAct (fstIdxFact (^&ic) (^&id)) ∈ Γ)
    (hsub : neg LAct (subsetFact (^&ic) (^&is)) ∈ Γ)
    (hd : neg LAct (derFact (^&id : V)) ∈ Γ) (hn₁ : neg LAct (dlenFact (^&id : V) (^&in₁)) ∈ Γ)
    (hle₁ : neg LAct (leFact (^&in₁) (bnum m₁)) ∈ Γ)
    (hsl : neg LAct (setLenFact (^&il) (^&is)) ∈ Γ) (hle : neg LAct (leFact (^&il) (bnum L)) ∈ Γ) :
    costSum N E Γ (nodeWk W tblN is il ic id in₁ L m₁ n) ≤
      9 * (costK N E B 8 (B * E + formulaLen LAct (goalFact (^&(is + 1)) (bnum n))) (dlen TAct (bin2Code tblN L m₁ n)) +
        (3 * ((8 : ℕ) : V) + 11) * (ctxBoundG (growK B E (B * E + formulaLen LAct (goalFact (^&(is + 1)) (bnum n)))) Γ 9 +
          (fvOccS LAct Γ + 9 * growK B E (B * E + formulaLen LAct (goalFact (^&(is + 1)) (bnum n)))))) := by
  have hE : 1 ≤ E := le_trans (by norm_num) (le_trans le_add_self hn)
  have hLn' : L + m₁ ≤ n := le_trans le_self_add hLn
  obtain ⟨hok, _, _, hlen, _⟩ := nodeWk_ok htbl hF hWp htblN hΓ his hic hid hT hn hLn hfs hf hsub hd hn₁ hle₁ hsl hle
  have hsz := sizeOK_nodeWk (W := W) (tblN := tblN) (is := is) (il := il) (ic := ic) (id := id) (in₁ := in₁) hWp
    (le_trans (formulaLen_bin2Fact_le hE hPle hn (le_trans le_self_add hLn') (le_trans le_add_self hLn')) le_self_add)
    (le_refl (dlen TAct (bin2Code tblN L m₁ n))) le_add_self
  have := costSum_le_of_sizeOK 8 hE htbl hBt hok hsz
  rwa [hlen] at this

theorem sizeOK_nodeCut {Q D W tblN is il ip inp id₁ id₂ ic₁ ic₂ in₁ in₂ L m₁ m₂ n : V} (hWp : W = frag1Pieces)
    (hA : formulaLen LAct (bin3Fact L m₁ m₂ n) ≤ Q) (hD : dlen TAct (bin3Code tblN L m₁ m₂ n) ≤ D)
    (hg : formulaLen LAct (goalFact (^&(is + 1)) (bnum n)) ≤ Q) :
    SizeOK Q D (nodeCut W tblN is il ip inp id₁ id₂ ic₁ ic₂ in₁ in₂ L m₁ m₂ n) := by
  unfold nodeCut nodeCutHead
  exact sizeOK_appendV (sizeOK_cons (stepSizeOK_horn2 (ftag_totCutRule hWp _)) (sizeOK_cons (stepSizeOK_horn0 (ftag_fstIdxCut hWp _))
    (sizeOK_cons (stepSizeOK_horn0 (ftag_introCut hWp _)) (sizeOK_single (stepSizeOK_horn0 (ftag_dlenCut hWp _))))))
    (sizeOK_goalTailBinary hWp hA hD hg)

theorem costSum_nodeCut_le {tbl N E B Γ W tblN N' B' is il ip inp id₁ id₂ ic₁ ic₂ in₁ in₂ L m₁ m₂ n : V}
    (htbl : TableOK tbl N) (hF : Frag1Table tbl) (hWp : W = frag1Pieces) (htblN : NumTableOK tblN N' B')
    (hΓ : IsFormulaSet LAct Γ)
    (hBt : ∀ j < len tbl, formulaLen LAct (rowB tbl.[j]) ≤ B) (hPle : formulaLen LAct (Ple : V) ≤ B)
    (his : is + 2 ≤ E) (hip : ip + 2 ≤ E) (hinp : inp + 2 ≤ E)
    (hid₁ : id₁ + 2 ≤ E) (hid₂ : id₂ + 2 ≤ E) (hic₁ : ic₁ + 2 ≤ E) (hic₂ : ic₂ + 2 ≤ E)
    (hT : il + in₁ + in₂ + 10 ≤ E) (hn : 18 * ‖n‖ + 7 ≤ E) (hLn : L + m₁ + m₂ + 1 ≤ n)
    (hf₁ : neg LAct (fstIdxFact (^&ic₁) (^&id₁)) ∈ Γ) (hi₁ : neg LAct (insFact (^&ic₁) (^&ip) (^&is)) ∈ Γ)
    (hd₁ : neg LAct (derFact (^&id₁ : V)) ∈ Γ) (hn₁ : neg LAct (dlenFact (^&id₁ : V) (^&in₁)) ∈ Γ)
    (hle₁ : neg LAct (leFact (^&in₁) (bnum m₁)) ∈ Γ)
    (hf₂ : neg LAct (fstIdxFact (^&ic₂) (^&id₂)) ∈ Γ) (hneg : neg LAct (negFact (^&inp) (^&ip)) ∈ Γ)
    (hi₂ : neg LAct (insFact (^&ic₂) (^&inp) (^&is)) ∈ Γ)
    (hd₂ : neg LAct (derFact (^&id₂ : V)) ∈ Γ) (hn₂ : neg LAct (dlenFact (^&id₂ : V) (^&in₂)) ∈ Γ)
    (hle₂ : neg LAct (leFact (^&in₂) (bnum m₂)) ∈ Γ)
    (hsl : neg LAct (setLenFact (^&il) (^&is)) ∈ Γ) (hle : neg LAct (leFact (^&il) (bnum L)) ∈ Γ) :
    costSum N E Γ (nodeCut W tblN is il ip inp id₁ id₂ ic₁ ic₂ in₁ in₂ L m₁ m₂ n) ≤
      9 * (costK N E B 9 (B * E + formulaLen LAct (goalFact (^&(is + 1)) (bnum n))) (dlen TAct (bin3Code tblN L m₁ m₂ n)) +
        (3 * ((9 : ℕ) : V) + 11) * (ctxBoundG (growK B E (B * E + formulaLen LAct (goalFact (^&(is + 1)) (bnum n)))) Γ 9 +
          (fvOccS LAct Γ + 9 * growK B E (B * E + formulaLen LAct (goalFact (^&(is + 1)) (bnum n)))))) := by
  have hE : 1 ≤ E := le_trans (by norm_num) (le_trans le_add_self hn)
  have hLn' : L + m₁ + m₂ ≤ n := le_trans le_self_add hLn
  obtain ⟨hok, _, _, hlen, _⟩ := nodeCut_ok htbl hF hWp htblN hΓ his hip hinp hid₁ hid₂ hic₁ hic₂ hT hn hLn
    hf₁ hi₁ hd₁ hn₁ hle₁ hf₂ hneg hi₂ hd₂ hn₂ hle₂ hsl hle
  have hsz := sizeOK_nodeCut (W := W) (tblN := tblN) (is := is) (il := il) (ip := ip) (inp := inp)
    (id₁ := id₁) (id₂ := id₂) (ic₁ := ic₁) (ic₂ := ic₂) (in₁ := in₁) (in₂ := in₂) hWp
    (le_trans (formulaLen_bin3Fact_le hE hPle hn (le_trans (le_trans le_self_add le_self_add) hLn')
      (le_trans (le_trans le_add_self le_self_add) hLn') (le_trans le_add_self hLn')) le_self_add)
    (le_refl (dlen TAct (bin3Code tblN L m₁ m₂ n))) le_add_self
  have := costSum_le_of_sizeOK 9 hE htbl hBt hok hsz
  rwa [hlen] at this

end cost

end ArithS
