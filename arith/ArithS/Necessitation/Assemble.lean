import ArithS.Necessitation.Top
import ArithS.Necessitation.Verify2
import ArithS.Necessitation.Pin
import ArithS.Necessitation.NodeSize

/-!
# ArithS.Necessitation.Assemble — the kit over `VerifyGraph'`, the root bridge, and the assembly

`Top.lean`'s kits quantify over the OLD relation `VerifyGraph W tblN` (`Verify.lean`), which `Verify2.lean`
superseded by `VerifyGraph' Ww Wl Wc W₁ W₂ W T A` (computed prologues, the `axm` certificate table `A`).
This file restates the verify kit over the new relation (`VerifyKit'''`), bridges the top's ROOT layout to
the node layout `verifyGraph'_ok` expects, discharges the kit from `verifyGraph'_ok_pow`, and assembles
`BoundedInnerNec 24` conditional on the named oracles.

**Why the kit cannot live in `Top.lean`:** `Verify2.lean` imports `Top.lean` (for `RootLayout`, `kitQ`, …),
so a kit mentioning `VerifyGraph'` has to sit ABOVE `Verify2` — here.

**The root bridge (§2).** `verifyGraph'_ok` wants the root laid out CANONICALLY at offset `0`
(`NodeLay … (fstIdx ρ)`: the member dossier at `&(3 + mLen x)`, the chain `&2 = insert &(3 + mLen x) 𝟎`, the
fold base `&1`, the length `&0`, plus the numeric `lenFact`/`leFact`), while the top's `RootLayout Γ x i`
has the consecutive triple `&i = setLen &(i+1)`, `&(i+1) = insert &(i+2) 𝟎`, `&(i+2) = x` and no numeric
length. The two shapes are incompatible at any common offset (the fold base sits between the length and
the chain), so the bridge RE-LAYS the root sequent `{x}` from scratch (`layoutSteps`, a fresh copy of the
member `x'` and of the sequent `s'`), and then IDENTIFIES the two copies: `eqSteps` (the identification walk
of the two dossiers of `x`) gives `x₀ = x'`, two `congMem`/`emptySubsetC`/`insertSubset` triples give
`s₀ ⊆ s'` and `s' ⊆ s₀`, `subsetAntisymm` gives `s₀ = s'`. After the verify list `L` (whose goal fact is
about the FRESH sequent `s'`), a RETARGET block moves the goal onto the ROOT sequent `s₀`: `goalElim`
(recover `d = &1`, `n = &0` and `fstIdxFact s' d`), `congFstIdx` (`fstIdxFact s₀ d`), `sGoal`
(re-close `goalFact s₀ (bnum (dlen ρ))`). So the kit's list is `vList = bridge ++ L ++ retarget`, and its
`ok` conjunct has EXACTLY `VerifyKit''.ok`'s shape — the goal at `&(i + 1 + shiftsV vList)` on the root
sequent — which is why `top_main'''` is `top_main''` with the list renamed. **Index reconciliation chosen:**
the goal is RETARGETED onto the root sequent (no index identity for the singleton is needed: the
identification makes the two sequent objects provably equal in the object proof).
-/

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open PeanoMinus ISigma0 ISigma1
open LAct

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSectionVars false
set_option maxRecDepth 20000

/-! ## 1. The singleton sequent `{x}`: its member list and its canonical layout, read off -/

section singleton

lemma len_memberList_single (x : V) : len (memberList (insert x (0 : V))) = 1 := by
  have h1 : 1 ≤ len (memberList (insert x (0 : V))) := one_le_len_memberList_insert x 0
  refine le_antisymm ?_ h1
  by_contra hlt
  have hlt' : 1 < len (memberList (insert x (0 : V))) := not_le.mp hlt
  have h0 : (memberList (insert x (0 : V))).[0] ∈ insert x (0 : V) :=
    nth_memberList_mem (lt_of_lt_of_le _root_.zero_lt_one h1)
  have h1' : (memberList (insert x (0 : V))).[1] ∈ insert x (0 : V) := nth_memberList_mem hlt'
  have e0 : (memberList (insert x (0 : V))).[0] = x := by
    rcases mem_bitInsert_iff.mp h0 with h | h
    · exact h
    · simp at h
  have e1 : (memberList (insert x (0 : V))).[1] = x := by
    rcases mem_bitInsert_iff.mp h1' with h | h
    · exact h
    · simp at h
  have := memberList_nodup (lt_of_lt_of_le _root_.zero_lt_one h1) hlt' (e0.trans e1.symm)
  exact _root_.zero_ne_one this

lemma memberList_single (x : V) : memberList (insert x (0 : V)) = x ∷ 0 := by
  refine nth_ext' 1 (len_memberList_single x) (by simp) ?_
  intro i hi
  rcases zero_or_succ i with rfl | ⟨i, rfl⟩
  · have h0 : (memberList (insert x (0 : V))).[0] ∈ insert x (0 : V) :=
      nth_memberList_mem (by rw [len_memberList_single]; exact _root_.zero_lt_one)
    rw [nth_adjoin_zero]
    rcases mem_bitInsert_iff.mp h0 with h | h
    · exact h
    · simp at h
  · exact absurd hi (not_lt.mpr le_add_self)

/-- The index of the (fresh) member `x` in the canonical layout of `{x}` at chain offset `i`:
`mTop i 1 (mLen Wc T x + 0) = i + (2·1 + 1 + (mLen Wc T x + 0))`. -/
noncomputable def sTop (Wc T x i : V) : V := mTop i 1 (mLen Wc T x + 0)

lemma sTop_eq (Wc T x i : V) : sTop Wc T x i = i + 3 + mLen Wc T x := by
  unfold sTop mTop; ring

/-- **The canonical layout of `{x}`, read off**: the member's dossier, `piFact`, the chain fact
`&(i+2) = insert &(sTop) 𝟎` (the innermost member's `prevI` IS the literal `𝟎`), and the membership fact. -/
lemma layout_single {Ww Wc T Γ x i : V} (h : Layout Ww Wc T Γ (insert x (0 : V)) i) :
    DossF Ww Γ 0 x (sTop Wc T x i) ∧
    neg LAct (piFact (𝟎 : V) (^&(sTop Wc T x i))) ∈ Γ ∧
    neg LAct (insFact (^&(i + 2)) (^&(sTop Wc T x i)) (𝟎 : V)) ∈ Γ ∧
    neg LAct (memFact (^&(sTop Wc T x i)) (^&(i + 2))) ∈ Γ := by
  have hk : (0 : V) < len (memberList (insert x (0 : V))) := by
    rw [len_memberList_single]; exact _root_.zero_lt_one
  obtain ⟨hD, hpi, _, hins, _, hm⟩ := h.1 0 hk
  simp only [memberList_single, len_adjoin, len_nil, zero_add, offVec_adjoin, tailShift_nil, nth_adjoin_zero] at hD hpi hins hm
  have e2 : i + (1 + 1 + 0) = i + 2 := by ring
  have e2' : i + (1 + 1) = i + 2 := by ring
  have hprev : prevI i 1 0 = (𝟎 : V) := by
    unfold prevI; exact prevAt_of_eq (by ring)
  rw [e2, hprev] at hins
  rw [e2'] at hm
  exact ⟨hD, hpi, hins, hm⟩

end singleton

/-! ## 2. The identification of the two copies of the root: `x₀ = x'` (the walk `eqSteps`), then `s₀ = s'`
(`congMem` ×2, `emptySubsetC` ×2, `insertSubset` ×2, `subsetAntisymm`) — a Horn-only, shift-free block -/

section identRoot

/-- **The identification block.** `x₀ = &jx₀`, `s₀ = &js₀` (the root copy, `insFact &js₀ &jx₀ 𝟎`,
`memFact &jx₀ &js₀`); `x' = &jx'`, `s' = &js'` (the fresh layout copy, `insFact &js' &jx' 𝟎`, `memFact &jx' &js'`).
Leaves `eqFactB &js₀ &js'`. All steps are `frag1Pieces` Horn rows (42 `eqSymm`, 62 `congMem`, 81 `emptySubsetC`,
112 `insertSubset`, 75 `subsetAntisymm`). -/
noncomputable def identRoot (Wl x jx₀ jx' js₀ js' : V) : V :=
  appendV (eqSteps Wl jx₀ jx' x)
    (mkStep frag1Pieces 42 ?[^&jx₀, ^&jx'] ∷
     mkStep frag1Pieces 62 ?[^&jx', ^&jx₀, ^&js'] ∷
     mkStep frag1Pieces 62 ?[^&jx₀, ^&jx', ^&js₀] ∷
     mkStep frag1Pieces 81 ?[^&js'] ∷
     mkStep frag1Pieces 81 ?[^&js₀] ∷
     mkStep frag1Pieces 112 ?[(𝟎 : V), ^&js', ^&jx₀, ^&js₀] ∷
     mkStep frag1Pieces 112 ?[(𝟎 : V), ^&js₀, ^&jx', ^&js'] ∷
     mkStep frag1Pieces 75 ?[^&js₀, ^&js'] ∷ (0 : V))

set_option maxHeartbeats 1000000 in
/-- **The identification block is applicable** (cap `8`, Horn-only, shift-free, `≤ 2·eqCount x + 9` steps) and
leaves `eqFactB &js₀ &js'`. -/
theorem identRoot_ok {tbl N Wl x jx₀ jx' js₀ js' E Γ : V} (htbl : TableOK tbl N) (hP : ProTable tbl)
    (hWl : Wl = layoutPieces) (hx : IsSemiformula LAct 0 x) (hΓ : IsFormulaSet LAct Γ)
    (hE : 2 * (0 + formulaLen LAct x) + 12 ≤ E) (hE₀ : jx₀ + eqCount x + 1 ≤ E) (hE' : jx' + eqCount x + 1 ≤ E)
    (hEs₀ : js₀ + 1 ≤ E) (hEs' : js' + 1 ≤ E)
    (hD₀ : DossF walkPieces Γ 0 x jx₀) (hD' : DossF walkPieces Γ 0 x jx')
    (hm₀ : neg LAct (memFact (^&jx₀) (^&js₀)) ∈ Γ) (hm' : neg LAct (memFact (^&jx') (^&js')) ∈ Γ)
    (hi₀ : neg LAct (insFact (^&js₀) (^&jx₀) (𝟎 : V)) ∈ Γ) (hi' : neg LAct (insFact (^&js') (^&jx') (𝟎 : V)) ∈ Γ) :
    ListOK tbl E ((8 : ℕ) : V) Γ (identRoot Wl x jx₀ jx' js₀ js') ∧ NoDrop (identRoot Wl x jx₀ jx' js₀ js') ∧
    HornOnly (identRoot Wl x jx₀ jx' js₀ js') ∧ shiftsV (identRoot Wl x jx₀ jx' js₀ js') = 0 ∧
    len (identRoot Wl x jx₀ jx' js₀ js') ≤ 2 * eqCount x + 9 ∧
    neg LAct (eqFactB (^&js₀) (^&js')) ∈ finalCtx Γ (identRoot Wl x jx₀ jx' js₀ js') := by
  have hW := hP.walkTable
  have hL := hP.layoutTable
  have hF := hP.frag1Table
  have hE1 : (1 : V) ≤ E := le_trans (by norm_num) (le_trans le_add_self hE)
  have hx₀E : jx₀ + 1 ≤ E := le_trans (add_le_add le_self_add le_rfl) hE₀
  have hx'E : jx' + 1 ≤ E := le_trans (add_le_add le_self_add le_rfl) hE'
  have h0l : termLen LAct (𝟎 : V) ≤ E := termLen_zeroV_le hE1
  -- the walk
  have hDA₀ := dossierAt_of_dossF htbl hW rfl hx hD₀
  have hDA' := dossierAt_of_dossF htbl hW rfl hx hD'
  obtain ⟨eok, end_, eho, esh, elen, efact⟩ := eqSteps_ok htbl hL hWl rfl hx hE hE₀ hE' hΓ hDA₀ hDA'
  obtain ⟨Γe, hΓe⟩ : ∃ Γ', Γ' = finalCtx Γ (eqSteps Wl jx₀ jx' x) := ⟨_, rfl⟩
  rw [← hΓe] at efact
  have hΓef : IsFormulaSet LAct Γe := by rw [hΓe]; exact finalCtx_isFormulaSet 8 htbl hΓ eok
  have tre : ∀ y ∈ Γ, y ∈ Γe := fun y hy ↦ by rw [hΓe]; exact tr_of_zero end_ esh hy
  -- the eight Horn steps
  obtain ⟨ok₁, tg₁, cx₁⟩ := flok_eqSymm htbl hF rfl hΓef (hf_ jx₀) (termLen_fvar_le' hx₀E) (hf_ jx') (termLen_fvar_le' hx'E) efact
  obtain ⟨Γ₁, hΓ₁⟩ : ∃ Γ', Γ' = insert (neg LAct (eqFactB (^&jx') (^&jx₀))) Γe := ⟨_, rfl⟩
  rw [← hΓ₁] at cx₁
  have hΓ₁f : IsFormulaSet LAct Γ₁ := by rw [← cx₁]; exact isFormulaSet_ctxAfter 8 htbl ok₁
  have tr₁ : ∀ y ∈ Γe, y ∈ Γ₁ := fun y hy ↦ by rw [hΓ₁]; exact memIns hy
  have f₁ : neg LAct (eqFactB (^&jx') (^&jx₀)) ∈ Γ₁ := by rw [hΓ₁]; exact memInsSelf _ _
  obtain ⟨ok₂, tg₂, cx₂⟩ := flok_congMem htbl hF rfl hΓ₁f (hf_ jx') (termLen_fvar_le' hx'E) (hf_ jx₀) (termLen_fvar_le' hx₀E)
    (hf_ js') (termLen_fvar_le' hEs') (tr₁ _ efact) (tr₁ _ (tre _ hm'))
  obtain ⟨Γ₂, hΓ₂⟩ : ∃ Γ', Γ' = insert (neg LAct (memFact (^&jx₀) (^&js'))) Γ₁ := ⟨_, rfl⟩
  rw [← hΓ₂] at cx₂
  have hΓ₂f : IsFormulaSet LAct Γ₂ := by rw [← cx₂]; exact isFormulaSet_ctxAfter 8 htbl ok₂
  have tr₂ : ∀ y ∈ Γ₁, y ∈ Γ₂ := fun y hy ↦ by rw [hΓ₂]; exact memIns hy
  have f₂ : neg LAct (memFact (^&jx₀) (^&js')) ∈ Γ₂ := by rw [hΓ₂]; exact memInsSelf _ _
  obtain ⟨ok₃, tg₃, cx₃⟩ := flok_congMem htbl hF rfl hΓ₂f (hf_ jx₀) (termLen_fvar_le' hx₀E) (hf_ jx') (termLen_fvar_le' hx'E)
    (hf_ js₀) (termLen_fvar_le' hEs₀) (tr₂ _ f₁) (tr₂ _ (tr₁ _ (tre _ hm₀)))
  obtain ⟨Γ₃, hΓ₃⟩ : ∃ Γ', Γ' = insert (neg LAct (memFact (^&jx') (^&js₀))) Γ₂ := ⟨_, rfl⟩
  rw [← hΓ₃] at cx₃
  have hΓ₃f : IsFormulaSet LAct Γ₃ := by rw [← cx₃]; exact isFormulaSet_ctxAfter 8 htbl ok₃
  have tr₃ : ∀ y ∈ Γ₂, y ∈ Γ₃ := fun y hy ↦ by rw [hΓ₃]; exact memIns hy
  have f₃ : neg LAct (memFact (^&jx') (^&js₀)) ∈ Γ₃ := by rw [hΓ₃]; exact memInsSelf _ _
  obtain ⟨ok₄, tg₄, cx₄⟩ := flok_emptySubsetC htbl hF rfl hΓ₃f (hf_ js') (termLen_fvar_le' hEs')
  obtain ⟨Γ₄, hΓ₄⟩ : ∃ Γ', Γ' = insert (neg LAct (subsetFact (𝟎 : V) (^&js'))) Γ₃ := ⟨_, rfl⟩
  rw [← hΓ₄] at cx₄
  have hΓ₄f : IsFormulaSet LAct Γ₄ := by rw [← cx₄]; exact isFormulaSet_ctxAfter 8 htbl ok₄
  have tr₄ : ∀ y ∈ Γ₃, y ∈ Γ₄ := fun y hy ↦ by rw [hΓ₄]; exact memIns hy
  have f₄ : neg LAct (subsetFact (𝟎 : V) (^&js')) ∈ Γ₄ := by rw [hΓ₄]; exact memInsSelf _ _
  obtain ⟨ok₅, tg₅, cx₅⟩ := flok_emptySubsetC htbl hF rfl hΓ₄f (hf_ js₀) (termLen_fvar_le' hEs₀)
  obtain ⟨Γ₅, hΓ₅⟩ : ∃ Γ', Γ' = insert (neg LAct (subsetFact (𝟎 : V) (^&js₀))) Γ₄ := ⟨_, rfl⟩
  rw [← hΓ₅] at cx₅
  have hΓ₅f : IsFormulaSet LAct Γ₅ := by rw [← cx₅]; exact isFormulaSet_ctxAfter 8 htbl ok₅
  have tr₅ : ∀ y ∈ Γ₄, y ∈ Γ₅ := fun y hy ↦ by rw [hΓ₅]; exact memIns hy
  have f₅ : neg LAct (subsetFact (𝟎 : V) (^&js₀)) ∈ Γ₅ := by rw [hΓ₅]; exact memInsSelf _ _
  obtain ⟨ok₆, tg₆, cx₆⟩ := fok_insertSubset htbl hF rfl hΓ₅f h0_ h0l (hf_ js') (termLen_fvar_le' hEs') (hf_ jx₀)
    (termLen_fvar_le' hx₀E) (hf_ js₀) (termLen_fvar_le' hEs₀) (tr₅ _ f₄) (tr₅ _ (tr₄ _ (tr₃ _ f₂)))
    (tr₅ _ (tr₄ _ (tr₃ _ (tr₂ _ (tr₁ _ (tre _ hi₀))))))
  obtain ⟨Γ₆, hΓ₆⟩ : ∃ Γ', Γ' = insert (neg LAct (subsetFact (^&js₀) (^&js'))) Γ₅ := ⟨_, rfl⟩
  rw [← hΓ₆] at cx₆
  have hΓ₆f : IsFormulaSet LAct Γ₆ := by rw [← cx₆]; exact isFormulaSet_ctxAfter 8 htbl ok₆
  have tr₆ : ∀ y ∈ Γ₅, y ∈ Γ₆ := fun y hy ↦ by rw [hΓ₆]; exact memIns hy
  have f₆ : neg LAct (subsetFact (^&js₀) (^&js')) ∈ Γ₆ := by rw [hΓ₆]; exact memInsSelf _ _
  obtain ⟨ok₇, tg₇, cx₇⟩ := fok_insertSubset htbl hF rfl hΓ₆f h0_ h0l (hf_ js₀) (termLen_fvar_le' hEs₀) (hf_ jx')
    (termLen_fvar_le' hx'E) (hf_ js') (termLen_fvar_le' hEs') (tr₆ _ f₅) (tr₆ _ (tr₅ _ (tr₄ _ f₃)))
    (tr₆ _ (tr₅ _ (tr₄ _ (tr₃ _ (tr₂ _ (tr₁ _ (tre _ hi')))))))
  obtain ⟨Γ₇, hΓ₇⟩ : ∃ Γ', Γ' = insert (neg LAct (subsetFact (^&js') (^&js₀))) Γ₆ := ⟨_, rfl⟩
  rw [← hΓ₇] at cx₇
  have hΓ₇f : IsFormulaSet LAct Γ₇ := by rw [← cx₇]; exact isFormulaSet_ctxAfter 8 htbl ok₇
  have tr₇ : ∀ y ∈ Γ₆, y ∈ Γ₇ := fun y hy ↦ by rw [hΓ₇]; exact memIns hy
  have f₇ : neg LAct (subsetFact (^&js') (^&js₀)) ∈ Γ₇ := by rw [hΓ₇]; exact memInsSelf _ _
  obtain ⟨ok₈, tg₈, cx₈⟩ := flok_subsetAntisymm htbl hF rfl hΓ₇f (hf_ js₀) (termLen_fvar_le' hEs₀) (hf_ js') (termLen_fvar_le' hEs')
    (tr₇ _ f₆) f₇
  -- the assembly
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold identRoot
    refine listOK_appendV eok ?_
    rw [← hΓe]
    refine listOK_cons ok₁ ?_; rw [cx₁]
    refine listOK_cons ok₂ ?_; rw [cx₂]
    refine listOK_cons ok₃ ?_; rw [cx₃]
    refine listOK_cons ok₄ ?_; rw [cx₄]
    refine listOK_cons ok₅ ?_; rw [cx₅]
    refine listOK_cons ok₆ ?_; rw [cx₆]
    refine listOK_cons ok₇ ?_; rw [cx₇]
    exact listOK_single ok₈
  · unfold identRoot
    exact noDrop_appendV end_ (noDrop_cons (Or.inl tg₁) (noDrop_cons (Or.inl tg₂) (noDrop_cons (Or.inl tg₃)
      (noDrop_cons (Or.inl tg₄) (noDrop_cons (Or.inl tg₅) (noDrop_cons (Or.inl tg₆) (noDrop_cons (Or.inl tg₇)
      (noDrop_single (Or.inl tg₈)))))))))
  · unfold identRoot
    exact hornOnly_appendV eho (hornOnly_cons (Or.inl tg₁) (hornOnly_cons (Or.inl tg₂) (hornOnly_cons (Or.inl tg₃)
      (hornOnly_cons (Or.inl tg₄) (hornOnly_cons (Or.inl tg₅) (hornOnly_cons (Or.inl tg₆) (hornOnly_cons (Or.inl tg₇)
      (hornOnly_single (Or.inl tg₈)))))))))
  · unfold identRoot
    rw [shiftsV_appendV, esh, shiftsV_cons_tag0 tg₁, shiftsV_cons_tag0 tg₂, shiftsV_cons_tag0 tg₃, shiftsV_cons_tag0 tg₄,
      shiftsV_cons_tag0 tg₅, shiftsV_cons_tag0 tg₆, shiftsV_cons_tag0 tg₇, shiftsV_single_tag0 tg₈, add_zero]
  · unfold identRoot
    rw [len_appendV]
    simp only [len_adjoin, len_nil]
    calc len (eqSteps Wl jx₀ jx' x) + (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) = len (eqSteps Wl jx₀ jx' x) + 8 := by ring
      _ ≤ 2 * eqCount x + 1 + 8 := add_le_add elen le_rfl
      _ = 2 * eqCount x + 9 := by ring
  · unfold identRoot
    rw [finalCtx_appendV, ← hΓe, finalCtx_cons, cx₁, finalCtx_cons, cx₂, finalCtx_cons, cx₃, finalCtx_cons, cx₄,
      finalCtx_cons, cx₅, finalCtx_cons, cx₆, finalCtx_cons, cx₇, finalCtx_single, cx₈]
    exact memInsSelf _ _

end identRoot

/-! ## 3. The retarget block: the goal fact of the FRESH sequent `s'` moved onto the ROOT sequent `s₀`
(`goalElim`, `congFstIdx`, `sGoal`) — two shifts, seven steps -/

section retargetRoot

/-- **The retarget block** at `s' = &js'`, `s₀ = &js₀` (with `eqFactB &js₀ &js'` in context): recover `d = &1`,
`n = &0` and `fstIdxFact &(js'+2) &1` (`goalElim`, 2 shifts), `congFstIdx` to `fstIdxFact &(js₀+2) &1`, then
`sGoal &1 &0 &(js₀+2) (bnum d)` re-closes `goalFact &(js₀+2) (bnum d)`. -/
noncomputable def retargetRoot (js' js₀ d : V) : V :=
  appendV (goalElim (^&js') (bnum d))
    (mkStep frag1Pieces 122 ?[^&1, ^&(js' + 2), ^&(js₀ + 2)] ∷
     sGoal (^&1) (^&0) (^&(js₀ + 2)) (bnum d) ∷ (0 : V))

lemma len_retargetRoot (js' js₀ d : V) : len (retargetRoot js' js₀ d) = 7 := by
  unfold retargetRoot; rw [len_appendV, len_goalElim]; simp [len_adjoin]; norm_num

/-- **The retarget block is applicable** (cap `8`, cut-admitting, exactly two shifts) and leaves the goal fact on
the root sequent, at `&(js₀ + 2)`. -/
theorem retargetRoot_ok {tbl N js' js₀ d E Γ : V} (htbl : TableOK tbl N) (hF : Frag1Table tbl)
    (hΓ : IsFormulaSet LAct Γ) (hE₀ : js₀ + 3 ≤ E) (hE' : js' + 3 ≤ E) (hEd : termLen LAct (bnum d) ≤ E)
    (hgoal : neg LAct (goalFact (^&js') (bnum d)) ∈ Γ) (heq : neg LAct (eqFactB (^&js₀) (^&js')) ∈ Γ) :
    ListOK tbl E ((8 : ℕ) : V) Γ (retargetRoot js' js₀ d) ∧ NoDrop' (retargetRoot js' js₀ d) ∧
    shiftsV (retargetRoot js' js₀ d) = 2 ∧
    neg LAct (goalFact (^&(js₀ + 2)) (bnum d)) ∈ finalCtx Γ (retargetRoot js' js₀ d) := by
  have hbd : IsSemiterm LAct (0 : V) (bnum d) := isSemiterm_bnum_LAct 0 d
  have hE3 : (3 : V) ≤ E := le_trans le_add_self hE₀
  have hl0 : termLen LAct (^&0 : V) ≤ E := termLen_fvar_le' (le_trans (by norm_num) hE3)
  have hl1 : termLen LAct (^&1 : V) ≤ E := termLen_fvar_le' (le_trans (by norm_num) hE3)
  have hls' : termLen LAct (^&(js' + 2) : V) ≤ E := termLen_fvar_le' (by
    calc js' + 2 + 1 = js' + 3 := by ring
      _ ≤ E := hE')
  have hls₀ : termLen LAct (^&(js₀ + 2) : V) ≤ E := termLen_fvar_le' (by
    calc js₀ + 2 + 1 = js₀ + 3 := by ring
      _ ≤ E := hE₀)
  have e2' : (js' : V) + 1 + 1 = js' + 2 := by ring
  -- the recovery
  obtain ⟨gok, gnd, gsh, _, gder, gfst, gdlen, gle⟩ := goalElim_ok 8 htbl hΓ (hf_ js') hbd hgoal
  rw [termShift_fvar, termShift_fvar, e2'] at gfst
  rw [termShift_bnum, termShift_bnum] at gle
  obtain ⟨Γ₀, hΓ₀⟩ : ∃ Γ', Γ' = finalCtx Γ (goalElim (^&js') (bnum d)) := ⟨_, rfl⟩
  rw [← hΓ₀] at gder gfst gdlen gle
  have hΓ₀f : IsFormulaSet LAct Γ₀ := by rw [hΓ₀]; exact finalCtx_isFormulaSet 8 htbl hΓ gok
  have heq₀ : neg LAct (eqFactB (^&(js₀ + 2)) (^&(js' + 2))) ∈ Γ₀ := by
    have := mem_finalCtx_of_mem' gnd heq
    rw [gsh, shiftIterV_neg (isFormula_eqFactB (hf_ _) (hf_ _)), shiftIterV_eqFactB (hf_ _) (hf_ _),
      termShiftIterV_fvar, termShiftIterV_fvar, ← hΓ₀] at this
    exact this
  -- `congFstIdx`
  obtain ⟨ok₁, tg₁, cx₁⟩ := fok_congFstIdx htbl hF rfl hΓ₀f (hf_ 1) hl1 (hf_ (js' + 2)) hls' (hf_ (js₀ + 2)) hls₀ heq₀ gfst
  obtain ⟨Γ₁, hΓ₁⟩ : ∃ Γ', Γ' = insert (neg LAct (fstIdxFact (^&(js₀ + 2)) (^&1))) Γ₀ := ⟨_, rfl⟩
  rw [← hΓ₁] at cx₁
  have hΓ₁f : IsFormulaSet LAct Γ₁ := by rw [← cx₁]; exact isFormulaSet_ctxAfter 8 htbl ok₁
  have tr₁ : ∀ y ∈ Γ₀, y ∈ Γ₁ := fun y hy ↦ by rw [hΓ₁]; exact memIns hy
  have f₁ : neg LAct (fstIdxFact (^&(js₀ + 2)) (^&1)) ∈ Γ₁ := by rw [hΓ₁]; exact memInsSelf _ _
  -- `sGoal`
  have ok₂ : StepOK tbl E ((8 : ℕ) : V) Γ₁ (sGoal (^&1) (^&0) (^&(js₀ + 2)) (bnum d)) :=
    stepOK_sGoal hΓ₁f (hf_ 1) hl1 (hf_ 0) hl0 (hf_ (js₀ + 2)) hls₀ hbd hEd (tr₁ _ gder) f₁ (tr₁ _ gdlen) (tr₁ _ gle)
  have cx₂ := ctxAfter_sGoal Γ₁ (^&1 : V) (^&0) (^&(js₀ + 2)) (bnum d)
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold retargetRoot
    refine listOK_appendV gok ?_
    rw [← hΓ₀]
    refine listOK_cons ok₁ ?_; rw [cx₁]
    exact listOK_single ok₂
  · unfold retargetRoot
    exact noDrop'_appendV gnd (noDrop'_cons (Or.inl tg₁)
      (noDrop'_single (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by simp)))))))))
  · unfold retargetRoot
    rw [shiftsV_appendV, gsh, shiftsV_cons_tag0 tg₁, shiftsV_single]
    simp
  · unfold retargetRoot
    rw [finalCtx_appendV, ← hΓ₀, finalCtx_cons, cx₁, finalCtx_single, cx₂]
    exact memInsSelf _ _

/-- The retarget block is size-disciplined once `Q` dominates `4·|goalFact &js' (bnum d)|` and
`|goalFact &(js₀+2) (bnum d)|`. -/
lemma sizeOK_retargetRoot {Q D js' js₀ d : V} (hQ : 4 * formulaLen LAct (goalFact (^&js') (bnum d)) ≤ Q)
    (hQ' : formulaLen LAct (goalFact (^&(js₀ + 2)) (bnum d)) ≤ Q) : SizeOK Q D (retargetRoot js' js₀ d) := by
  unfold retargetRoot
  refine sizeOK_appendV ((sizeOK_goalElim (D := D) (hf_ js') (isSemiterm_bnum_LAct 0 d)).mono hQ le_rfl) ?_
  exact sizeOK_cons (stepSizeOK_horn0 (ftag_congFstIdx rfl _)) (sizeOK_single (stepSizeOK_sGoal hQ'))

end retargetRoot

/-! ## 4. The bridged verify list `vList = layoutSteps {x} ++ identRoot ++ L ++ retargetRoot` and its `ok` -/

section vList

/-- **The bridged verify list** at root offset `i` (root member `x = &(i+2)`, root sequent `&(i+1)`): the fresh
canonical layout of `{x}` (`β` shifts), the identification (`x₀ = &(i+β+2)` with `x' = &(sTop Wc T x 0)`,
`s₀ = &(i+β+1)` with `s' = &2`), the verify list `L` of the graph, and the retarget of the goal onto `s₀`. -/
noncomputable def vList (Wl Wc W T x i ρ L : V) : V :=
  appendV (layoutSteps walkPieces Wl Wc W T (insert x 0))
    (appendV (identRoot Wl x (i + shiftsV (layoutSteps walkPieces Wl Wc W T (insert x 0)) + 2) (sTop Wc T x 0)
        (i + shiftsV (layoutSteps walkPieces Wl Wc W T (insert x 0)) + 1) (0 + 2))
      (appendV L (retargetRoot (0 + 2 + shiftsV L)
        (i + shiftsV (layoutSteps walkPieces Wl Wc W T (insert x 0)) + 1 + shiftsV L) (dlen TAct ρ))))

lemma pow6_eq_p6 (x : V) : x ^ 6 = p6 x := by simp only [p6]; ring

lemma succ_le_pow6 (d : V) : d + 1 ≤ (d + 1) ^ 6 := by
  rw [pow6_eq_p6]; exact le_p6_self le_add_self

/-- The cap discipline of the bridged list: a quantity `≤ c·(d+1)^6 + a·(d+1) + b·i` is below `E` once
`Ckv·((d+1)^6 + i) ≤ E` with `c + a ≤ Ckv`, `b ≤ Ckv`. -/
lemma cap_gen {Ckv E d i X c a b : V} (hE : Ckv * ((d + 1) ^ 6 + i) ≤ E) (hca : c + a ≤ Ckv) (hb : b ≤ Ckv)
    (hX : X ≤ c * (d + 1) ^ 6 + a * (d + 1) + b * i) : X ≤ E := by
  refine le_trans hX (le_trans ?_ hE)
  calc c * (d + 1) ^ 6 + a * (d + 1) + b * i ≤ c * (d + 1) ^ 6 + a * (d + 1) ^ 6 + Ckv * i :=
        add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_left (succ_le_pow6 d) zero_le))
          (mul_le_mul_of_nonneg_right hb zero_le)
    _ = (c + a) * (d + 1) ^ 6 + Ckv * i := by ring
    _ ≤ Ckv * (d + 1) ^ 6 + Ckv * i := add_le_add (mul_le_mul_of_nonneg_right hca zero_le) le_rfl
    _ = Ckv * ((d + 1) ^ 6 + i) := by ring

/-- `{x} = insert x 0` (the sequent of a `Proof`). -/
lemma singleton_eq_insert_zero (x : V) : ({x} : V) = insert x (0 : V) := mem_ext fun _ ↦ by simp

set_option maxHeartbeats 2000000 in
/-- **The bridged verify list is applicable at the ROOT layout** (the `ok` half of the kit `VerifyKit3`): from
`Proof TAct ρ x`, `RootLayout Γ x i` and the cap `Ck·((dlen ρ + 1)^6 + i) ≤ E`, every graph list `L` yields
`vList` applicable at cap `9`, cut-admitting, with `shiftsV ≤ Ck·(dlen ρ + 1)^6`, leaving the goal fact on the
ROOT sequent at `&(i + 1 + shiftsV vList)`. `Ck = Ck' + 50` with `Ck'` the constant of `verifyGraph'_ok_pow`. -/
theorem vList_ok : ∃ Ck : ℕ, ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    {tbl N N' B' Wl Wc W₁ W₂ W T A Cv E ρ x Γ i L : V},
    TableOK tbl N → ProTable tbl → NumTableOK T N' B' → Wl = layoutPieces → Wc = certPieces →
    W₁ = frag1Pieces → W₂ = frag2Pieces → W = proPieces → AxmTableOK tbl E walkPieces A Cv →
    Proof TAct ρ x → IsSemiformula LAct 0 x → RootLayout Γ x i → IsFormulaSet LAct Γ →
    (Ck : V) * ((dlen TAct ρ + 1) ^ 6 + i) ≤ E → VerifyGraph' walkPieces Wl Wc W₁ W₂ W T A ρ L →
    ListOK tbl E ((9 : ℕ) : V) Γ (vList Wl Wc W T x i ρ L) ∧ NoDrop' (vList Wl Wc W T x i ρ L) ∧
    shiftsV (vList Wl Wc W T x i ρ L) ≤ (Ck : V) * (dlen TAct ρ + 1) ^ 6 ∧
    neg LAct (goalFact (^&(i + 1 + shiftsV (vList Wl Wc W T x i ρ L))) (bnum (dlen TAct ρ))) ∈
      finalCtx Γ (vList Wl Wc W T x i ρ L) := by
  obtain ⟨Ck', hV⟩ := verifyGraph'_ok_pow
  refine ⟨Ck' + 50, fun V _ _ tbl N N' B' Wl Wc W₁ W₂ W T A Cv E ρ x Γ i L htbl hP htblN hWl hWc hW₁ hW₂ hWp hA hρ hx hR hΓ hE hL ↦ ?_⟩
  have hW := hP.walkTable
  have hF := hP.frag1Table
  have hd : Derivation TAct ρ := hρ.2
  have hfst : fstIdx ρ = insert x 0 := by rw [hρ.1]; exact singleton_eq_insert_zero x
  obtain ⟨d, hdd⟩ : ∃ d, d = dlen TAct ρ := ⟨_, rfl⟩
  obtain ⟨Ckv, hCkv⟩ : ∃ c : V, c = ((Ck' + 50 : ℕ) : V) := ⟨_, rfl⟩
  rw [← hCkv, ← hdd] at hE
  have hCk' : (Ck' : V) ≤ Ckv := by rw [hCkv]; push_cast; exact le_self_add
  have hC : ∀ a : ℕ, a ≤ 50 → ((a : ℕ) : V) ≤ Ckv := fun a ha ↦ by
    rw [hCkv]; push_cast; exact le_trans (by exact_mod_cast ha) le_add_self
  have hC1 : (1 : V) ≤ Ckv := by rw [hCkv]; push_cast; exact le_trans (by norm_num) le_add_self
  have hd1 : (1 : V) ≤ d := hdd ▸ one_le_dlen hd
  -- sizes of the root member
  have hxs : IsFormulaSet LAct (insert x (0 : V)) := IsFormulaSet.insert_iff.mpr ⟨hx, IsFormulaSet.empty⟩
  have hsD : setLen LAct (insert x (0 : V)) ≤ d := by rw [hdd, ← hfst]; exact setLen_fstIdx_le_dlen hd
  have hxD : formulaLen LAct x ≤ d := le_trans (formulaLen_le_setLen_of_mem (L := LAct) (by simp)) hsD
  have hxD1 : formulaLen LAct x ≤ d + 1 := le_trans hxD le_self_add
  have hcnt : eqCount x + 1 ≤ 2 * (d + 1) := le_trans (eqCount_succ_le htbl hW hx) (mul_le_mul_of_nonneg_left hxD1 zero_le)
  have hmL : mLen Wc T x + 1 ≤ 2 * (d + 1) := le_trans (mLen_succ_le hWc T hx) (mul_le_mul_of_nonneg_left hxD1 zero_le)
  have hmS : mShift walkPieces Wc T x ≤ 4 * (d + 1) := le_trans (mShift_le htbl hW hWc T hx) (mul_le_mul_of_nonneg_left hxD1 zero_le)
  have hE1 : (1 : V) ≤ E := cap_gen hE (c := 0) (a := 1) (b := 0) (by rw [zero_add]; exact hC1) zero_le
    (by rw [zero_mul, zero_add, zero_mul, add_zero, one_mul]; exact le_add_self)
  -- (1) the fresh layout of `{x}`
  have hk1 : 1 ≤ len (memberList (insert x (0 : V))) := by rw [len_memberList_single]
  have hE13 : 13 * d + 18 * ‖d‖ + 8 ≤ E := cap_gen hE (c := 0) (a := 39) (b := 0) (by rw [zero_add]; exact hC 39 (by norm_num)) zero_le (by
    rw [zero_mul, zero_add, zero_mul, add_zero]
    calc 13 * d + 18 * ‖d‖ + 8 ≤ (13 + 18 + 8) * (d + 1) := lin_cap 13 18 8 d
      _ = 39 * (d + 1) := by ring)
  obtain ⟨bok, bnd, bsh, blen, bLay⟩ := layoutSteps_ok htbl hP htblN hWl hWc hWp hxs hk1 hsD hE13 hΓ
  obtain ⟨β, hβ⟩ : ∃ b, b = shiftsV (layoutSteps walkPieces Wl Wc W T (insert x 0)) := ⟨_, rfl⟩
  have hβle : β ≤ 7 * (d + 1) := by
    rw [hβ, bsh, memberList_single, tailShift_adjoin, tailShift_nil, len_adjoin, len_nil]
    calc _ = mShift walkPieces Wc T x + 3 := by ring
      _ ≤ 4 * (d + 1) + 3 := add_le_add hmS le_rfl
      _ ≤ 4 * (d + 1) + 3 * (d + 1) := add_le_add le_rfl (le_mul_of_one_le_right zero_le le_add_self)
      _ = 7 * (d + 1) := by ring
  obtain ⟨Γ₁, hΓ₁⟩ : ∃ Γ', Γ' = finalCtx Γ (layoutSteps walkPieces Wl Wc W T (insert x 0)) := ⟨_, rfl⟩
  rw [← hΓ₁] at bLay
  have hΓ₁f : IsFormulaSet LAct Γ₁ := by rw [hΓ₁]; exact finalCtx_isFormulaSet 8 htbl hΓ bok
  have hR₁ : RootLayout Γ₁ x (i + β) := by rw [hΓ₁, hβ]; exact hR.transport bnd
  obtain ⟨hD₀, _, hi₀, _, hm₀, _⟩ := hR₁
  obtain ⟨hD', _, hi', hm'⟩ := layout_single bLay
  -- (2) the identification
  have hsT : sTop Wc T x 0 ≤ 3 * (d + 1) := by
    rw [sTop_eq]
    calc 0 + 3 + mLen Wc T x = mLen Wc T x + 1 + 2 := by ring
      _ ≤ 2 * (d + 1) + 2 := add_le_add hmL le_rfl
      _ ≤ 2 * (d + 1) + (d + 1) := add_le_add le_rfl (le_trans (by norm_num) (add_le_add hd1 le_rfl))
      _ = 3 * (d + 1) := by ring
  have hIE : 2 * (0 + formulaLen LAct x) + 12 ≤ E := cap_gen hE (c := 0) (a := 14) (b := 0)
    (by rw [zero_add]; exact hC 14 (by norm_num)) zero_le (by
      rw [zero_mul, zero_add, zero_mul, add_zero, zero_add]
      calc 2 * formulaLen LAct x + 12 ≤ 2 * (d + 1) + 12 * (d + 1) :=
            add_le_add (mul_le_mul_of_nonneg_left hxD1 zero_le) (le_mul_of_one_le_right zero_le le_add_self)
        _ = 14 * (d + 1) := by ring)
  have hIE₀ : i + β + 2 + eqCount x + 1 ≤ E := cap_gen hE (c := 0) (a := 11) (b := 1)
    (by rw [zero_add]; exact hC 11 (by norm_num)) hC1 (by
      rw [zero_mul, zero_add]
      calc i + β + 2 + eqCount x + 1 = β + 2 + (eqCount x + 1) + i := by ring
        _ ≤ 7 * (d + 1) + 2 * (d + 1) + 2 * (d + 1) + i :=
            add_le_add (add_le_add (add_le_add hβle (le_mul_of_one_le_right zero_le le_add_self)) hcnt) le_rfl
        _ = 11 * (d + 1) + 1 * i := by ring)
  have hIE' : sTop Wc T x 0 + eqCount x + 1 ≤ E := cap_gen hE (c := 0) (a := 5) (b := 0)
    (by rw [zero_add]; exact hC 5 (by norm_num)) zero_le (by
      rw [zero_mul, zero_add, zero_mul, add_zero, add_assoc]
      calc sTop Wc T x 0 + (eqCount x + 1) ≤ 3 * (d + 1) + 2 * (d + 1) := add_le_add hsT hcnt
        _ = 5 * (d + 1) := by ring)
  have hIs₀ : i + β + 1 + 1 ≤ E := cap_gen hE (c := 0) (a := 9) (b := 1)
    (by rw [zero_add]; exact hC 9 (by norm_num)) hC1 (by
      rw [zero_mul, zero_add]
      calc i + β + 1 + 1 = β + 2 + i := by ring
        _ ≤ 7 * (d + 1) + 2 * (d + 1) + i := add_le_add (add_le_add hβle (le_mul_of_one_le_right zero_le le_add_self)) le_rfl
        _ = 9 * (d + 1) + 1 * i := by ring)
  have hIs' : 0 + 2 + 1 ≤ E := cap_gen hE (c := 0) (a := 3) (b := 0) (by rw [zero_add]; exact hC 3 (by norm_num)) zero_le (by
    rw [zero_mul, zero_add, zero_mul, add_zero, zero_add]
    calc (2 : V) + 1 = 3 * 1 := by norm_num
      _ ≤ 3 * (d + 1) := mul_le_mul_of_nonneg_left le_add_self zero_le)
  obtain ⟨iok, ind, iho, ish, ilen, ieq⟩ := identRoot_ok htbl hP hWl hx hΓ₁f hIE hIE₀ hIE' hIs₀ hIs' hD₀ hD' hm₀ hm' hi₀ hi'
  obtain ⟨Γ₂, hΓ₂⟩ : ∃ Γ', Γ' = finalCtx Γ₁ (identRoot Wl x (i + β + 2) (sTop Wc T x 0) (i + β + 1) (0 + 2)) := ⟨_, rfl⟩
  rw [← hΓ₂] at ieq
  have hΓ₂f : IsFormulaSet LAct Γ₂ := by rw [hΓ₂]; exact finalCtx_isFormulaSet 8 htbl hΓ₁f iok
  have tr₂ : ∀ y ∈ Γ₁, y ∈ Γ₂ := fun y hy ↦ by rw [hΓ₂]; exact tr_of_zero ind ish hy
  have hLay₂ : NodeLay walkPieces Wc T Γ₂ (fstIdx ρ) := by
    rw [hfst]; exact Or.inl ⟨hk1, bLay.mono tr₂⟩
  -- (3) the verify list
  have hEv : (Ck' : V) * (dlen TAct ρ + 1) ^ 6 ≤ E := by
    rw [← hdd]
    exact cap_gen hE (c := (Ck' : V)) (a := 0) (b := 0) (by rw [add_zero]; exact hCk') zero_le
      (by rw [zero_mul, add_zero, zero_mul, add_zero])
  obtain ⟨vok, vnd, vsh, vgoal⟩ := hV V htbl hP htblN rfl hWl hWc hW₁ hW₂ hWp hA hd hEv L Γ₂ hL hΓ₂f hLay₂
  rw [← hdd] at vsh vgoal
  obtain ⟨σ, hσ⟩ : ∃ s, s = shiftsV L := ⟨_, rfl⟩
  rw [← hσ] at vsh vgoal
  have hσle : σ ≤ (Ck' : V) * (d + 1) ^ 6 := vsh
  rw [hfst, len_memberList_single] at vgoal
  have e12 : (1 : V) + 1 + σ = 0 + 2 + σ := by ring
  rw [e12] at vgoal
  obtain ⟨Γ₃, hΓ₃⟩ : ∃ Γ', Γ' = finalCtx Γ₂ L := ⟨_, rfl⟩
  rw [← hΓ₃] at vgoal
  have hΓ₃f : IsFormulaSet LAct Γ₃ := by rw [hΓ₃]; exact finalCtx_isFormulaSet 9 htbl hΓ₂f vok
  have ieq₃ : neg LAct (eqFactB (^&(i + β + 1 + σ)) (^&(0 + 2 + σ))) ∈ Γ₃ := by
    have := tr_fact vnd (isFormula_eqFactB (hf_ _) (hf_ _)) ieq
    rw [shiftIterV_eqFactB (hf_ _) (hf_ _), termShiftIterV_fvar, termShiftIterV_fvar, ← hσ, ← hΓ₃] at this
    exact this
  -- (4) the retarget
  have hRE₀ : i + β + 1 + σ + 3 ≤ E := cap_gen hE (c := (Ck' : V)) (a := 11) (b := 1)
    (by rw [hCkv]; push_cast; exact add_le_add le_rfl (by norm_num)) hC1 (by
      calc i + β + 1 + σ + 3 = σ + (β + 4) + i := by ring
        _ ≤ (Ck' : V) * (d + 1) ^ 6 + (7 * (d + 1) + 4 * (d + 1)) + i :=
            add_le_add (add_le_add hσle (add_le_add hβle (le_mul_of_one_le_right zero_le le_add_self))) le_rfl
        _ = (Ck' : V) * (d + 1) ^ 6 + 11 * (d + 1) + 1 * i := by ring)
  have hRE' : 0 + 2 + σ + 3 ≤ E := cap_gen hE (c := (Ck' : V)) (a := 5) (b := 0)
    (by rw [hCkv]; push_cast; exact add_le_add le_rfl (by norm_num)) zero_le (by
      rw [zero_mul, add_zero]
      calc 0 + 2 + σ + 3 = σ + 5 := by ring
        _ ≤ (Ck' : V) * (d + 1) ^ 6 + 5 * (d + 1) := add_le_add hσle (le_mul_of_one_le_right zero_le le_add_self))
  have hEd : termLen LAct (bnum d) ≤ E := cap_gen hE (c := 0) (a := 7) (b := 0)
    (by rw [zero_add]; exact hC 7 (by norm_num)) zero_le (by
      rw [zero_mul, zero_add, zero_mul, add_zero]
      calc termLen LAct (bnum d) ≤ 6 * ‖d‖ + 1 := termLen_bnum_le_V d
        _ ≤ 6 * (d + 1) + 1 * (d + 1) :=
            add_le_add (mul_le_mul_of_nonneg_left (le_trans (length_le d) le_self_add) zero_le)
              (by rw [one_mul]; exact le_add_self)
        _ = 7 * (d + 1) := by ring)
  obtain ⟨rok, rnd, rsh, rgoal⟩ := retargetRoot_ok htbl hF hΓ₃f hRE₀ hRE' hEd vgoal ieq₃
  -- the assembly
  have hsh : shiftsV (vList Wl Wc W T x i ρ L) = β + (0 + (σ + 2)) := by
    unfold vList
    rw [shiftsV_appendV, shiftsV_appendV, shiftsV_appendV, ← hβ, ← hσ, ← hdd, ish, rsh]
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold vList
    rw [← hβ, ← hdd, ← hσ]
    refine listOK_appendV (bok.mono (by exact_mod_cast (by decide : (8 : ℕ) ≤ 9))) ?_
    rw [← hΓ₁]
    refine listOK_appendV (iok.mono (by exact_mod_cast (by decide : (8 : ℕ) ≤ 9))) ?_
    rw [← hΓ₂]
    refine listOK_appendV vok ?_
    rw [← hΓ₃]
    exact rok.mono (by exact_mod_cast (by decide : (8 : ℕ) ≤ 9))
  · unfold vList
    rw [← hβ, ← hdd, ← hσ]
    exact noDrop'_appendV bnd (noDrop'_appendV ind.noDrop' (noDrop'_appendV vnd rnd))
  · rw [hsh, ← hdd, ← hCkv]
    calc β + (0 + (σ + 2)) = σ + (β + 2) := by ring
      _ ≤ (Ck' : V) * (d + 1) ^ 6 + (7 * (d + 1) + 2 * (d + 1)) :=
          add_le_add hσle (add_le_add hβle (le_mul_of_one_le_right zero_le le_add_self))
      _ = (Ck' : V) * (d + 1) ^ 6 + 9 * (d + 1) := by ring
      _ ≤ (Ck' : V) * (d + 1) ^ 6 + 9 * (d + 1) ^ 6 := add_le_add le_rfl (mul_le_mul_of_nonneg_left (succ_le_pow6 d) zero_le)
      _ = ((Ck' : V) + 9) * (d + 1) ^ 6 := by ring
      _ ≤ Ckv * (d + 1) ^ 6 := mul_le_mul_of_nonneg_right (by rw [hCkv]; push_cast; exact add_le_add le_rfl (by norm_num)) zero_le
  · rw [hsh, ← hdd]
    have e : i + 1 + (β + (0 + (σ + 2))) = i + β + 1 + σ + 2 := by ring
    rw [e]
    unfold vList
    rw [← hβ, ← hdd, ← hσ, finalCtx_appendV, ← hΓ₁, finalCtx_appendV, ← hΓ₂, finalCtx_appendV, ← hΓ₃]
    exact rgoal

end vList

end ArithS
