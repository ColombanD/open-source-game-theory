import ArithS.Necessitation.Top
import ArithS.Necessitation.Verify2
import ArithS.Necessitation.Verify3
import ArithS.Necessitation.Verify4
import ArithS.Necessitation.Pin
import ArithS.Necessitation.NodeSize
import ArithS.Assembly.Cell

/-!
# ArithS.Necessitation.Assemble — the kit over `VerifyGraph'`, the root bridge, and the assembly

`Top.lean`'s kits quantify over the OLD relation `VerifyGraph W tblN` (`Verify.lean`), which `Verify2.lean`
superseded by `VerifyGraph' Ww Wl Wc W₁ W₂ W T A` (computed prologues, the `axm` certificate table `A`).
This file restates the verify kit over the new relation (`VerifyKit'''`), bridges the top's ROOT layout to
the node layout `verifyGraph'_ok` expects, discharges the kit from `verifyGraph''_ok_pow4`, and assembles
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

lemma succ_le_pow4 (d : V) : d + 1 ≤ (d + 1) ^ 4 := le_pow4 (d + 1)

/-- The cap discipline of the bridged list: a quantity `≤ c·(d+1)^4 + a·(d+1) + b·i` is below `E` once
`Ckv·((d+1)^4 + i) ≤ E` with `c + a ≤ Ckv`, `b ≤ Ckv`. -/
lemma cap_gen {Ckv E d i X c a b : V} (hE : Ckv * ((d + 1) ^ 4 + i) ≤ E) (hca : c + a ≤ Ckv) (hb : b ≤ Ckv)
    (hX : X ≤ c * (d + 1) ^ 4 + a * (d + 1) + b * i) : X ≤ E := by
  refine le_trans hX (le_trans ?_ hE)
  calc c * (d + 1) ^ 4 + a * (d + 1) + b * i ≤ c * (d + 1) ^ 4 + a * (d + 1) ^ 4 + Ckv * i :=
        add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_left (succ_le_pow4 d) zero_le))
          (mul_le_mul_of_nonneg_right hb zero_le)
    _ = (c + a) * (d + 1) ^ 4 + Ckv * i := by ring
    _ ≤ Ckv * (d + 1) ^ 4 + Ckv * i := add_le_add (mul_le_mul_of_nonneg_right hca zero_le) le_rfl
    _ = Ckv * ((d + 1) ^ 4 + i) := by ring

/-- `{x} = insert x 0` (the sequent of a `Proof`). -/
lemma singleton_eq_insert_zero (x : V) : ({x} : V) = insert x (0 : V) := mem_ext fun _ ↦ by simp

end vList

/-! ## 5. The size half: the goal fact's length, the size oracle for the graph's list, the kit -/

section goalLen

/-- `derFact (bv 1)` and `dlenFact (bv 1) (bv 0)` are codes of STANDARD semisentences (the two `goalBody`
conjuncts that mention only bound variables), so their lengths are standard constants. -/
noncomputable def derB1 : ArithmeticSemisentence 2 :=
  (↑(derivation TAct).sigma : ArithmeticSemisentence 1) ⇜ ![#1]
noncomputable def dlenB10 : ArithmeticSemisentence 2 :=
  (↑(dlenGraphDef LAct).sigma : ArithmeticSemisentence 2) ⇜ ![#1, #0]

lemma derFact_bv1_eq : (derFact (bv 1) : V) = ⌜Semiformula.lMap emb derB1⌝ := by
  unfold derFact Pderiv derivS derB1
  symm; row_shapeB

lemma dlenFact_bv10_eq : (dlenFact (bv 1) (bv 0) : V) = ⌜Semiformula.lMap emb dlenB10⌝ := by
  unfold dlenFact Pdlen dlenS dlenB10
  symm; row_shapeB

/-- The three standard constants of the goal fact's length. -/
noncomputable def cDer : ℕ := flen (Rewriting.emb (Semiformula.lMap emb derB1) : Semiproposition LAct 2)
noncomputable def cDlen : ℕ := flen (Rewriting.emb (Semiformula.lMap emb dlenB10) : Semiproposition LAct 2)
noncomputable def cFst : ℕ := flen (Rewriting.emb fstIdxS : Semiproposition LAct 2)

lemma formulaLen_derFact_bv1 : formulaLen LAct (derFact (bv 1) : V) = (cDer : V) := by
  rw [derFact_bv1_eq, formulaLen_quote_semisentence_V']; rfl
lemma formulaLen_dlenFact_bv10 : formulaLen LAct (dlenFact (bv 1) (bv 0) : V) = (cDlen : V) := by
  rw [dlenFact_bv10_eq, formulaLen_quote_semisentence_V']; rfl
lemma formulaLen_PfstIdx : formulaLen LAct (PfstIdx : V) = (cFst : V) := by
  unfold PfstIdx; rw [formulaLen_quote_semisentence_V']; rfl

-- TRAP (2026-09-15): these are `flen`s of the GIANT `derivation`/`dlenGraph` sentences; any tactic that whnf's them
-- (`push_cast`/`norm_num`/`omega` normalising a `Nat.cast`) evaluates the closed constant and STALLS — irreducible.
attribute [irreducible] cDer cDlen cFst

/-- A two-entry substitution vector `[s, #1]` (closed `s`, the identity at position `1`) is substitution-disciplined. -/
lemma substInv_closed_bv1 {B s : V} (hs : IsSemiterm LAct 0 s) (hls : termLen LAct s ≤ B) :
    SubstInv LAct B (listToVec [s, bv 1]) := by
  intro i hi
  rw [len_listToVec] at hi
  obtain ⟨i, rfl⟩ := eq_nat_of_lt_nat hi
  have hi' : i < 2 := by exact_mod_cast hi
  rw [nth_listToVec]
  rcases i with _ | _ | i
  · exact Or.inr ⟨hs, hls⟩
  · exact Or.inl rfl
  · exfalso; omega

/-- `[#0, u]` likewise. -/
lemma substInv_bv0_closed {B u : V} (hu : IsSemiterm LAct 0 u) (hlu : termLen LAct u ≤ B) :
    SubstInv LAct B (listToVec [bv 0, u]) := by
  intro i hi
  rw [len_listToVec] at hi
  obtain ⟨i, rfl⟩ := eq_nat_of_lt_nat hi
  have hi' : i < 2 := by exact_mod_cast hi
  rw [nth_listToVec]
  rcases i with _ | _ | i
  · exact Or.inl rfl
  · exact Or.inr ⟨hu, hlu⟩
  · exfalso; omega

/-- **The goal fact's length**: `|goalFact s u| ≤ cDer + cDlen + (cFst + |Ple|)·B + 5` for closed `s, u` of
length `≤ B`. -/
lemma formulaLen_goalFact_le {B : V} (hB : 1 ≤ B) {s u : V} (hs : IsSemiterm LAct 0 s) (hu : IsSemiterm LAct 0 u)
    (hls : termLen LAct s ≤ B) (hlu : termLen LAct u ≤ B) :
    formulaLen LAct (goalFact s u) ≤ (cDer : V) + (cDlen : V) + ((cFst : V) + formulaLen LAct (Ple : V)) * B + 5 := by
  have hb := isSemiformula_goalBody hs hu
  unfold goalBody at hb
  simp only [IsSemiformula.and] at hb
  obtain ⟨h1, h2, h3, h4⟩ := hb
  rw [formulaLen_goalFact hs hu]
  unfold goalBody
  rw [formulaLen_and h1.isUFormula (by simp [h2.isUFormula, h3.isUFormula, h4.isUFormula]),
    formulaLen_and h2.isUFormula (by simp [h3.isUFormula, h4.isUFormula]),
    formulaLen_and h3.isUFormula h4.isUFormula, formulaLen_derFact_bv1, formulaLen_dlenFact_bv10]
  have hs2 : IsSemiterm LAct (2 : V) s := isSemiterm_of_le hs zero_le
  have hu2 : IsSemiterm LAct (2 : V) u := isSemiterm_of_le hu zero_le
  have hF : formulaLen LAct (fstIdxFact s (bv 1)) ≤ (cFst : V) * B := by
    rw [← formulaLen_PfstIdx]
    exact formulaLen_subst_le hB isSemiformula_PfstIdx _ _
      (isSemitermVec_listToVec [s, bv 1] (fun x hx ↦ by
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hs2
        · rcases List.mem_cons.mp hx with rfl | hx
          · exact isSemiterm_bv_two 1 (by norm_num)
          · simp at hx))
      (substInv_closed_bv1 hs hls)
  have hL : formulaLen LAct (leFact (bv 0) u) ≤ formulaLen LAct (Ple : V) * B :=
    formulaLen_subst_le hB isSemiformula_Ple _ _
      (isSemitermVec_listToVec [bv 0, u] (fun x hx ↦ by
        rcases List.mem_cons.mp hx with rfl | hx
        · exact isSemiterm_bv_two 0 (by norm_num)
        · rcases List.mem_cons.mp hx with rfl | hx
          · exact hu2
          · simp at hx))
      (substInv_bv0_closed hu hlu)
  calc (cDer : V) + (formulaLen LAct (fstIdxFact s (bv 1)) + ((cDlen : V) + formulaLen LAct (leFact (bv 0) u) + 1) + 1) + 1 + 2
      ≤ (cDer : V) + ((cFst : V) * B + ((cDlen : V) + formulaLen LAct (Ple : V) * B + 1) + 1) + 1 + 2 :=
        add_le_add (add_le_add (add_le_add le_rfl (add_le_add (add_le_add hF (add_le_add (add_le_add le_rfl hL) le_rfl)) le_rfl)) le_rfl) le_rfl
    _ = (cDer : V) + (cDlen : V) + ((cFst : V) + formulaLen LAct (Ple : V)) * B + 5 := by ring

end goalLen

/-! ## 6. The size half: the size oracle for the graph's list, the bridged list's length and sizes, the kit -/

section sizeHalf

/-- **The size oracle** — the ONE remaining proof debt of the verify list (named, explicit): every graph list is
`≤ Cz·(dlen ρ + 1)^6` long and size-disciplined at the kit's `Q = kitQ Cz B E`, `D = kitD Cz (dlen ρ)`.
`verifyGraph'_ok` (`Verify2.lean` §8) proves `ListOK`/`NoDrop'`/`shiftsV`/the goal fact but NOT `len`/`SizeOK`; the
per-tag `sizeOK_pro<Tag>` lemmas of `Prologue.lean` §11 take `Layout` hypotheses (the identification loops' Horn-only
status is only known through their `ok` lemmas), so discharging this needs a second `Derivation.induction1 𝚷` glue
carrying the node layouts — `Verify2.lean` §8.9 with `SizeOK ∧ len` conjuncts (the `axm` entries' `SizeOK Cv Cv` come
from `AxmTableOK`). Morally true (every payload is a numeral fact of a `NumSteps` derivation or a goal fact), not yet
machine-checked. -/
def VerifySizeOracle (tbl B Wl Wc W₁ W₂ W T : V) (Cz : ℕ) : Prop :=
  ∀ {E A Cv ρ L : V}, AxmTableOK' tbl E walkPieces A Cv → Derivation TAct ρ →
    VerifyGraph'' walkPieces Wl Wc W₁ W₂ W T A ρ L →
    len L ≤ (Cz : V) * (dlen TAct ρ + 1) ^ 4 ∧ SizeOK (kitQ (Cz : V) B E) (kitD (Cz : V) (dlen TAct ρ)) L

/-- **The goal-fact size constant, PACKAGED EXISTENTIALLY** (`4·(cDer + cDlen + cFst + 6)`). TRAP (2026-09-15): a
`def cGoal : ℕ := 4 * (cDer + …)` STALLS every proof that touches it (`unfold; push_cast; ring`, `omega` after
`unfold`): the kernel's `Nat` arithmetic whnf's `cDer = flen ⌜derivation…⌝` to a literal — the giant-DSL-constant
trap of the handover. So the constant is a witness whose only interface is the cast identity, proved by pure `rw`s. -/
theorem exists_cGoal : ∃ c : ℕ, ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁],
    (c : V) = 4 * ((cDer : V) + cDlen + cFst + 6) :=
  ⟨4 * (cDer + cDlen + cFst + 6), fun V _ _ ↦ by
    rw [Nat.cast_mul, Nat.cast_add, Nat.cast_add, Nat.cast_add, Nat.cast_ofNat, Nat.cast_ofNat]⟩

/-- **The kit constant** (the goal-fact constant is ADDED as an opaque summand at the use site): `Ck'` (of
`verifyGraph''_ok_pow4`) + the bridge's caps + the oracle's `Cz` + the length and size constants of the bridge
(`19B' + 25`, `27N' + 525600B'` from `layQ`/`layD`). -/
def asmCk (Ck' Cz N' B' : ℕ) : ℕ :=
  Ck' + 50 + Cz + 65 + (19 * B' + 25) + (27 * N' + 525600 * B')

lemma cTE_le (d : V) : cTE d ≤ 19 * (d + 1) := by
  unfold cTE
  calc 2 * d + 12 * ‖d + 1‖ + 5 ≤ 2 * (d + 1) + 12 * (d + 1) + 5 * (d + 1) :=
        add_le_add (add_le_add (mul_le_mul_of_nonneg_left le_self_add zero_le)
          (mul_le_mul_of_nonneg_left (length_le _) zero_le)) (le_mul_of_one_le_right zero_le le_add_self)
    _ = 19 * (d + 1) := by ring

/-- `layQ B B' d ≤ (19B' + 25)·(B+1)(E+1)` for `d ≤ E`. -/
lemma layQ_le (B B' d E : V) (hdE : d ≤ E) : layQ B B' d ≤ (19 * B' + 25) * ((B + 1) * (E + 1)) := by
  unfold layQ lenQ sum2Q
  have h1 : B' * cTE d ≤ 19 * B' * (d + 1) := by
    calc B' * cTE d ≤ B' * (19 * (d + 1)) := mul_le_mul_of_nonneg_left (cTE_le d) zero_le
      _ = 19 * B' * (d + 1) := by ring
  have h2 : B * (18 * ‖d‖ + 7) ≤ 25 * B * (d + 1) := by
    calc B * (18 * ‖d‖ + 7) ≤ B * (18 * (d + 1) + 7 * (d + 1)) := mul_le_mul_of_nonneg_left (add_le_add
          (mul_le_mul_of_nonneg_left (le_trans (length_le d) le_self_add) zero_le)
          (le_mul_of_one_le_right zero_le le_add_self)) zero_le
      _ = 25 * B * (d + 1) := by ring
  calc B' * cTE d + B * (18 * ‖d‖ + 7) ≤ 19 * B' * (d + 1) + 25 * B * (d + 1) := add_le_add h1 h2
    _ = (19 * B' + 25 * B) * (d + 1) := by ring
    _ ≤ ((19 * B' + 25) * (B + 1)) * (E + 1) :=
        mul_le_mul (le_of_add_eq' (c := 19 * B' * B + 25) (by ring)) (add_le_add hdE le_rfl) zero_le zero_le
    _ = (19 * B' + 25) * ((B + 1) * (E + 1)) := by ring

lemma nodeCost_le' (N' B' : V) {e c : V} (h : e ≤ c) : nodeCost N' B' e ≤ N' + 800 * B' * c := by
  unfold nodeCost
  calc N' + 800 * (B' * e) ≤ N' + 800 * (B' * c) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h zero_le) zero_le)
    _ = N' + 800 * B' * c := by ring

/-- `layD N' B' d ≤ (27N' + 525600B')·(d+1)³`. -/
lemma layD_le (N' B' d : V) : layD N' B' d ≤ (27 * N' + 525600 * B') * (d + 1) ^ 3 := by
  unfold layD lenD sum2D
  have hl1 : ‖d‖ + 2 ≤ 3 * (d + 1) := by
    calc ‖d‖ + 2 ≤ (d + 1) + 2 * (d + 1) :=
          add_le_add (le_trans (length_le d) le_self_add) (le_mul_of_one_le_right zero_le le_add_self)
      _ = 3 * (d + 1) := by ring
  have hl2 : ‖d‖ + 1 ≤ 2 * (d + 1) := by
    calc ‖d‖ + 1 ≤ (d + 1) + (d + 1) := add_le_add (le_trans (length_le d) le_self_add) le_add_self
      _ = 2 * (d + 1) := by ring
  have hn1 : nodeCost N' B' (cTE d) ≤ (N' + 15200 * B') * (d + 1) := by
    calc nodeCost N' B' (cTE d) ≤ N' + 800 * B' * (19 * (d + 1)) := nodeCost_le' N' B' (cTE_le d)
      _ = N' + 15200 * B' * (d + 1) := by ring
      _ ≤ N' * (d + 1) + 15200 * B' * (d + 1) := add_le_add (le_mul_of_one_le_right zero_le le_add_self) le_rfl
      _ = (N' + 15200 * B') * (d + 1) := by ring
  have hn2 : nodeCost N' B' (18 * ‖d‖ + 7) ≤ (N' + 20000 * B') * (d + 1) := by
    have h25 : 18 * ‖d‖ + 7 ≤ 25 * (d + 1) := by
      calc 18 * ‖d‖ + 7 ≤ 18 * (d + 1) + 7 * (d + 1) := add_le_add
            (mul_le_mul_of_nonneg_left (le_trans (length_le d) le_self_add) zero_le)
            (le_mul_of_one_le_right zero_le le_add_self)
        _ = 25 * (d + 1) := by ring
    calc nodeCost N' B' (18 * ‖d‖ + 7) ≤ N' + 800 * B' * (25 * (d + 1)) := nodeCost_le' N' B' h25
      _ = N' + 20000 * B' * (d + 1) := by ring
      _ ≤ N' * (d + 1) + 20000 * B' * (d + 1) := add_le_add (le_mul_of_one_le_right zero_le le_add_self) le_rfl
      _ = (N' + 20000 * B') * (d + 1) := by ring
  calc (d + 1) * (‖d‖ + 2) * nodeCost N' B' (cTE d) + 4 * ((‖d‖ + 1) * (‖d‖ + 2) * nodeCost N' B' (18 * ‖d‖ + 7))
      ≤ (d + 1) * (3 * (d + 1)) * ((N' + 15200 * B') * (d + 1)) +
          4 * ((2 * (d + 1)) * (3 * (d + 1)) * ((N' + 20000 * B') * (d + 1))) :=
        add_le_add (mul_le_mul (mul_le_mul_of_nonneg_left hl1 zero_le) hn1 zero_le zero_le)
          (mul_le_mul_of_nonneg_left (mul_le_mul (mul_le_mul hl2 hl1 zero_le zero_le) hn2 zero_le zero_le) zero_le)
    _ = (27 * N' + 525600 * B') * (d + 1) ^ 3 := by ring

/-- `4·|goalFact &j u| ≤ kitQ Ckv B E` once `4(cDer + cDlen + cFst + 6) ≤ Ckv` (`j + 1 ≤ E`, `|u| ≤ E`, `|Ple| ≤ B`). -/
lemma goalFact4_le_kitQ {Ckv B E j u : V} (hE1 : 1 ≤ E) (hPle : formulaLen LAct (Ple : V) ≤ B) (hj : j + 1 ≤ E)
    (hu : IsSemiterm LAct 0 u) (hlu : termLen LAct u ≤ E) (hC : 4 * ((cDer : V) + cDlen + cFst + 6) ≤ Ckv) :
    4 * formulaLen LAct (goalFact (^&j) u) ≤ kitQ Ckv B E := by
  have h := formulaLen_goalFact_le hE1 (hf_ j) hu (termLen_fvar_le' hj) hlu
  have hBE : (1 : V) ≤ (B + 1) * (E + 1) := one_le_mul_of_one_le_of_one_le le_add_self le_add_self
  have hmain : formulaLen LAct (goalFact (^&j) u) ≤ ((cDer : V) + cDlen + cFst + 6) * ((B + 1) * (E + 1)) := by
    refine le_trans h ?_
    calc (cDer : V) + cDlen + ((cFst : V) + formulaLen LAct (Ple : V)) * E + 5
        = ((cDer : V) + cDlen + 5) + ((cFst : V) + formulaLen LAct (Ple : V)) * E := by ring
      _ ≤ ((cDer : V) + cDlen + 5) * ((B + 1) * (E + 1)) + (((cFst : V) + 1) * (B + 1)) * (E + 1) :=
          add_le_add (le_mul_of_one_le_right zero_le hBE)
            (mul_le_mul (le_trans (add_le_add le_rfl hPle) (le_of_add_eq' (c := (cFst : V) * B + 1) (by ring)))
              le_self_add zero_le zero_le)
      _ = ((cDer : V) + cDlen + cFst + 6) * ((B + 1) * (E + 1)) := by ring
  unfold kitQ
  calc 4 * formulaLen LAct (goalFact (^&j) u) ≤ 4 * (((cDer : V) + cDlen + cFst + 6) * ((B + 1) * (E + 1))) :=
        mul_le_mul_of_nonneg_left hmain zero_le
    _ = (4 * ((cDer : V) + cDlen + cFst + 6)) * ((B + 1) * (E + 1)) := by ring
    _ ≤ Ckv * ((B + 1) * (E + 1)) := mul_le_mul_of_nonneg_right hC zero_le

set_option maxHeartbeats 2000000 in
/-- **The bridged verify list is applicable at the ROOT layout** (the `ok` half of the kit `VerifyKit3`): from
`Proof TAct ρ x`, `RootLayout Γ x i` and the cap `Ck·((dlen ρ + 1)^6 + i) ≤ E`, every graph list `L` yields
`vList` applicable at cap `9`, cut-admitting, with `shiftsV ≤ Ck·(dlen ρ + 1)^6`, leaving the goal fact on the
ROOT sequent at `&(i + 1 + shiftsV vList)`. `Ck = Ck' + 50` with `Ck'` the constant of `verifyGraph''_ok_pow4`. -/
theorem vList_full (N' B' Cz Cv : ℕ) : ∃ Ck : ℕ, 1 ≤ Ck ∧ ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    {tbl N B Wl Wc W₁ W₂ W T A E ρ x Γ i L : V},
    TableOK tbl N → ProTable tbl → (∀ j < len tbl, formulaLen LAct (rowB tbl.[j]) ≤ B) →
    formulaLen LAct (Ple : V) ≤ B → NumTableOK T (N' : V) (B' : V) → Wl = layoutPieces → Wc = certPieces →
    W₁ = frag1Pieces → W₂ = frag2Pieces → W = proPieces → VerifySizeOracle tbl B Wl Wc W₁ W₂ W T Cz →
    AxmTableOK' tbl E walkPieces A (Cv : V) →
    Proof TAct ρ x → IsSemiformula LAct 0 x → RootLayout Γ x i → IsFormulaSet LAct Γ →
    (Ck : V) * ((dlen TAct ρ + 1) ^ 4 + i) ≤ E → VerifyGraph'' walkPieces Wl Wc W₁ W₂ W T A ρ L →
    ListOK tbl E ((9 : ℕ) : V) Γ (vList Wl Wc W T x i ρ L) ∧ NoDrop' (vList Wl Wc W T x i ρ L) ∧
    shiftsV (vList Wl Wc W T x i ρ L) ≤ (Ck : V) * (dlen TAct ρ + 1) ^ 4 ∧
    neg LAct (goalFact (^&(i + 1 + shiftsV (vList Wl Wc W T x i ρ L))) (bnum (dlen TAct ρ))) ∈
      finalCtx Γ (vList Wl Wc W T x i ρ L) ∧
    len (vList Wl Wc W T x i ρ L) ≤ (Ck : V) * (dlen TAct ρ + 1) ^ 4 ∧
    SizeOK (kitQ (Ck : V) B E) (kitD (Ck : V) (dlen TAct ρ)) (vList Wl Wc W T x i ρ L) := by
  obtain ⟨Ck', hV⟩ := verifyGraph''_ok_pow4
  obtain ⟨cG, hcG⟩ := exists_cGoal
  have hle : ∀ a : ℕ, a ≤ asmCk Ck' Cz N' B' + cG → a ≤ (asmCk Ck' Cz N' B' + cG) * (Cv + 1) := fun a h ↦
    le_trans h (Nat.le_mul_of_pos_right _ (Nat.succ_pos Cv))
  refine ⟨(asmCk Ck' Cz N' B' + cG) * (Cv + 1), hle 1 (by unfold asmCk; omega),
    fun V _ _ tbl N B Wl Wc W₁ W₂ W T A E ρ x Γ i L htbl hP hBt hPle htblN hWl hWc hW₁ hW₂ hWp hsize hA hρ hx hR hΓ hE hL ↦ ?_⟩
  have hW := hP.walkTable
  have hF := hP.frag1Table
  have hd : Derivation TAct ρ := hρ.2
  have hfst : fstIdx ρ = insert x 0 := by rw [hρ.1]; exact singleton_eq_insert_zero x
  obtain ⟨d, hdd⟩ : ∃ d, d = dlen TAct ρ := ⟨_, rfl⟩
  obtain ⟨Ckv, hCkv⟩ : ∃ c : V, c = (((asmCk Ck' Cz N' B' + cG) * (Cv + 1) : ℕ) : V) := ⟨_, rfl⟩
  rw [← hCkv, ← hdd] at hE
  have hCk' : (Ck' : V) ≤ Ckv := by rw [hCkv]; exact_mod_cast (hle Ck' (by unfold asmCk; omega))
  have hC : ∀ a : ℕ, a ≤ 50 → ((a : ℕ) : V) ≤ Ckv := fun a ha ↦ by
    rw [hCkv]; exact_mod_cast (hle a (by unfold asmCk; omega))
  have hC1 : (1 : V) ≤ Ckv := by rw [hCkv]; exact_mod_cast (hle 1 (by unfold asmCk; omega))
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
  have hCkCv : (Ck' : V) * ((Cv : V) + 1) ≤ Ckv := by
    rw [hCkv]; exact_mod_cast Nat.mul_le_mul_right (Cv + 1) (show Ck' ≤ asmCk Ck' Cz N' B' + cG by unfold asmCk; omega)
  have hCkc : ∀ c : ℕ, c ≤ 50 → (Ck' : V) * ((Cv : V) + 1) + (c : V) ≤ Ckv := fun c hc ↦ by
    rw [hCkv]
    exact_mod_cast (calc Ck' * (Cv + 1) + c ≤ Ck' * (Cv + 1) + c * (Cv + 1) :=
          Nat.add_le_add_left (Nat.le_mul_of_pos_right c (Nat.succ_pos Cv)) _
      _ = (Ck' + c) * (Cv + 1) := by ring
      _ ≤ (asmCk Ck' Cz N' B' + cG) * (Cv + 1) := Nat.mul_le_mul_right _ (by unfold asmCk; omega))
  have hEv : (Ck' : V) * ((Cv : V) + 1) * (dlen TAct ρ + 1) ^ 4 ≤ E := by
    rw [← hdd]
    exact cap_gen hE (c := (Ck' : V) * ((Cv : V) + 1)) (a := 0) (b := 0) (by rw [add_zero]; exact hCkCv) zero_le
      (by rw [zero_mul, add_zero, zero_mul, add_zero])
  obtain ⟨vok, vnd, vsh, vgoal⟩ := hV V htbl hP htblN rfl hWl hWc hW₁ hW₂ hWp hA hd hEv L Γ₂ hL hΓ₂f hLay₂
  rw [← hdd] at vsh vgoal
  obtain ⟨σ, hσ⟩ : ∃ s, s = shiftsV L := ⟨_, rfl⟩
  rw [← hσ] at vsh vgoal
  have hσle : σ ≤ (Ck' : V) * ((Cv : V) + 1) * (d + 1) ^ 4 := vsh
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
  have hRE₀ : i + β + 1 + σ + 3 ≤ E := cap_gen hE (c := (Ck' : V) * ((Cv : V) + 1)) (a := 11) (b := 1)
    (hCkc 11 (by norm_num)) hC1 (by
      calc i + β + 1 + σ + 3 = σ + (β + 4) + i := by ring
        _ ≤ (Ck' : V) * ((Cv : V) + 1) * (d + 1) ^ 4 + (7 * (d + 1) + 4 * (d + 1)) + i :=
            add_le_add (add_le_add hσle (add_le_add hβle (le_mul_of_one_le_right zero_le le_add_self))) le_rfl
        _ = (Ck' : V) * ((Cv : V) + 1) * (d + 1) ^ 4 + 11 * (d + 1) + 1 * i := by ring)
  have hRE' : 0 + 2 + σ + 3 ≤ E := cap_gen hE (c := (Ck' : V) * ((Cv : V) + 1)) (a := 5) (b := 0)
    (hCkc 5 (by norm_num)) zero_le (by
      rw [zero_mul, add_zero]
      calc 0 + 2 + σ + 3 = σ + 5 := by ring
        _ ≤ (Ck' : V) * ((Cv : V) + 1) * (d + 1) ^ 4 + 5 * (d + 1) := add_le_add hσle (le_mul_of_one_le_right zero_le le_add_self))
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
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
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
      _ ≤ (Ck' : V) * ((Cv : V) + 1) * (d + 1) ^ 4 + (7 * (d + 1) + 2 * (d + 1)) :=
          add_le_add hσle (add_le_add hβle (le_mul_of_one_le_right zero_le le_add_self))
      _ = (Ck' : V) * ((Cv : V) + 1) * (d + 1) ^ 4 + 9 * (d + 1) := by ring
      _ ≤ (Ck' : V) * ((Cv : V) + 1) * (d + 1) ^ 4 + 9 * (d + 1) ^ 4 := add_le_add le_rfl (mul_le_mul_of_nonneg_left (succ_le_pow4 d) zero_le)
      _ = ((Ck' : V) * ((Cv : V) + 1) + 9) * (d + 1) ^ 4 := by ring
      _ ≤ Ckv * (d + 1) ^ 4 := mul_le_mul_of_nonneg_right (hCkc 9 (by norm_num)) zero_le
  · rw [hsh, ← hdd]
    have e : i + 1 + (β + (0 + (σ + 2))) = i + β + 1 + σ + 2 := by ring
    rw [e]
    unfold vList
    rw [← hβ, ← hdd, ← hσ, finalCtx_appendV, ← hΓ₁, finalCtx_appendV, ← hΓ₂, finalCtx_appendV, ← hΓ₃]
    exact rgoal
  · -- the length
    rw [← hdd, ← hCkv]
    unfold vList
    rw [← hβ, ← hdd, ← hσ, len_appendV, len_appendV, len_appendV, len_retargetRoot]
    have h1 := len_layoutSteps_le hWc walkPieces Wl W T hxs
    rw [len_memberList_single] at h1
    have h3 := (hsize hA hd hL).1
    rw [← hdd] at h3
    calc len (layoutSteps walkPieces Wl Wc W T (insert x 0)) +
          (len (identRoot Wl x (i + β + 2) (sTop Wc T x 0) (i + β + 1) (0 + 2)) + (len L + 7))
        ≤ (26 * d + 13 * 1 + 6) + ((2 * (2 * (d + 1)) + 9) + ((Cz : V) * (d + 1) ^ 4 + 7)) := by
          refine add_le_add (le_trans h1 (add_le_add (add_le_add (mul_le_mul_of_nonneg_left hsD zero_le) le_rfl) le_rfl))
            (add_le_add (le_trans ilen ?_) (add_le_add h3 le_rfl))
          exact add_le_add (mul_le_mul_of_nonneg_left (le_trans le_self_add hcnt) zero_le) le_rfl
      _ = 26 * d + 4 * (d + 1) + 35 + (Cz : V) * (d + 1) ^ 4 := by ring
      _ ≤ 26 * (d + 1) + 4 * (d + 1) + 35 * (d + 1) + (Cz : V) * (d + 1) ^ 4 :=
          add_le_add (add_le_add (add_le_add (mul_le_mul_of_nonneg_left le_self_add zero_le) le_rfl)
            (le_mul_of_one_le_right zero_le le_add_self)) le_rfl
      _ = 65 * (d + 1) + (Cz : V) * (d + 1) ^ 4 := by ring
      _ ≤ 65 * (d + 1) ^ 4 + (Cz : V) * (d + 1) ^ 4 :=
          add_le_add (mul_le_mul_of_nonneg_left (succ_le_pow4 d) zero_le) le_rfl
      _ = (65 + (Cz : V)) * (d + 1) ^ 4 := by ring
      _ ≤ Ckv * (d + 1) ^ 4 := mul_le_mul_of_nonneg_right
          (by rw [hCkv]; exact_mod_cast (hle (65 + Cz) (by unfold asmCk; omega))) zero_le
  · -- the sizes
    rw [← hdd, ← hCkv]
    unfold vList
    rw [← hβ, ← hdd, ← hσ]
    have hdE : d ≤ E := cap_gen hE (c := 0) (a := 1) (b := 0) (by rw [zero_add]; exact hC1) zero_le
      (by rw [zero_mul, zero_add, zero_mul, add_zero, one_mul]; exact le_self_add)
    have hQz : kitQ (Cz : V) B E ≤ kitQ Ckv B E := mul_le_mul_of_nonneg_right
      (by rw [hCkv]; exact_mod_cast (hle (Cz) (by unfold asmCk; omega))) zero_le
    have hDz : kitD (Cz : V) d ≤ kitD Ckv d := mul_le_mul_of_nonneg_right
      (by rw [hCkv]; exact_mod_cast (hle (Cz) (by unfold asmCk; omega))) zero_le
    have hlQ : layQ B (B' : V) d ≤ kitQ Ckv B E := le_trans (layQ_le B (B' : V) d E hdE) (mul_le_mul_of_nonneg_right
      (by rw [hCkv]; exact_mod_cast (hle (19 * B' + 25) (by unfold asmCk; omega))) zero_le)
    have hlD : layD (N' : V) (B' : V) d ≤ kitD Ckv d := le_trans (layD_le (N' : V) (B' : V) d) (mul_le_mul_of_nonneg_right
      (by rw [hCkv]; exact_mod_cast (hle (27 * N' + 525600 * B') (by unfold asmCk; omega))) zero_le)
    have hsz := (hsize hA hd hL).2
    rw [← hdd] at hsz
    have hcGoal : 4 * ((cDer : V) + cDlen + cFst + 6) ≤ Ckv := by
      rw [← hcG V, hCkv]; exact_mod_cast (hle cG (by omega))
    have hbd : IsSemiterm LAct (0 : V) (bnum d) := isSemiterm_bnum_LAct 0 d
    have hg1 : 4 * formulaLen LAct (goalFact (^&(0 + 2 + σ)) (bnum d)) ≤ kitQ Ckv B E :=
      goalFact4_le_kitQ hE1 hPle (le_trans (add_le_add (le_refl (0 + 2 + σ)) (by norm_num : (1 : V) ≤ 3)) hRE') hbd hEd hcGoal
    have hg2 : formulaLen LAct (goalFact (^&(i + β + 1 + σ + 2)) (bnum d)) ≤ kitQ Ckv B E :=
      le_trans (le_mul_of_one_le_left zero_le (by norm_num : (1 : V) ≤ 4))
        (goalFact4_le_kitQ hE1 hPle (le_trans (le_of_eq (by ring)) hRE₀) hbd hEd hcGoal)
    refine sizeOK_appendV ((sizeOK_layoutSteps hWl hWc hWp htblN hPle hxs hsD).mono hlQ hlD) ?_
    refine sizeOK_appendV (sizeOK_of_hornOnly iho) ?_
    exact sizeOK_appendV (hsz.mono hQz hDz) (sizeOK_retargetRoot hg1 hg2)

end sizeHalf

/-! ## 7. The kit over `VerifyGraph'`, its instance, the package, and the assembly -/

section kit3

/-- **`VerifyKit'''`** — `Top.VerifyKit''` restated over `Verify3`'s `VerifyGraph'' walkPieces Wl Wc W₁ W₂ W T A` with the
shifted `axm` certificate table `A` (`AxmTableOK' tbl E walkPieces A Cv`, `Cv` the table's standard constant) and the ROOT BRIDGE folded in:
the list the kit certifies is `vList Wl Wc W T x i ρ L` (`layoutSteps {x} ++ identRoot ++ L ++ retargetRoot`), whose
`ok`/`cost` conjuncts have EXACTLY `VerifyKit''`'s shapes (the goal on the root sequent at `&(i + 1 + shiftsV)`, the
coarse cost at `Q = kitQ Ck B E`, `D = kitD Ck (dlen ρ)`, the multiplier `Ck·(dlen ρ + 1)^m`, the cap
`Ck·((dlen ρ + 1)^m + i) ≤ E`). `IsSemiformula 0 x` is an extra hypothesis (the top has it). -/
structure VerifyKit''' (tbl N B Wl Wc W₁ W₂ W T : V) (Cv : ℕ) (Ck : ℕ) (m : ℕ) : Prop where
  ok : ∀ {ρ x Γ i E A L : V}, Proof TAct ρ x → IsSemiformula LAct 0 x → RootLayout Γ x i → IsFormulaSet LAct Γ →
    (Ck : V) * ((dlen TAct ρ + 1) ^ m + i) ≤ E → AxmTableOK' tbl E walkPieces A (Cv : V) →
    VerifyGraph'' walkPieces Wl Wc W₁ W₂ W T A ρ L →
    ListOK tbl E ((9 : ℕ) : V) Γ (vList Wl Wc W T x i ρ L) ∧ NoDrop' (vList Wl Wc W T x i ρ L) ∧
    shiftsV (vList Wl Wc W T x i ρ L) ≤ (Ck : V) * (dlen TAct ρ + 1) ^ m ∧
    neg LAct (goalFact (^&(i + 1 + shiftsV (vList Wl Wc W T x i ρ L))) (bnum (dlen TAct ρ))) ∈
      finalCtx Γ (vList Wl Wc W T x i ρ L)
  cost : ∀ {ρ x Γ i E A L : V}, Proof TAct ρ x → IsSemiformula LAct 0 x → RootLayout Γ x i → IsFormulaSet LAct Γ →
    (Ck : V) * ((dlen TAct ρ + 1) ^ m + i) ≤ E → AxmTableOK' tbl E walkPieces A (Cv : V) →
    VerifyGraph'' walkPieces Wl Wc W₁ W₂ W T A ρ L →
    costSum N E Γ (vList Wl Wc W T x i ρ L) ≤ (Ck : V) * (dlen TAct ρ + 1) ^ m *
      (costK N E B ((9 : ℕ) : V) (kitQ (Ck : V) B E) (kitD (Ck : V) (dlen TAct ρ)) +
        38 * (ctxBoundG (growK B E (kitQ (Ck : V) B E)) Γ ((Ck : V) * (dlen TAct ρ + 1) ^ m) +
          (fvOccS LAct Γ + (Ck : V) * (dlen TAct ρ + 1) ^ m * growK B E (kitQ (Ck : V) B E)))) ∧
    setLen LAct (finalCtx Γ (vList Wl Wc W T x i ρ L)) ≤
      ctxBoundG (growK B E (kitQ (Ck : V) B E)) Γ ((Ck : V) * (dlen TAct ρ + 1) ^ m) ∧
    fvOccS LAct (finalCtx Γ (vList Wl Wc W T x i ρ L)) ≤
      fvOccS LAct Γ + (Ck : V) * (dlen TAct ρ + 1) ^ m * growK B E (kitQ (Ck : V) B E)

/-- **`VerifyKit'''` holds at `m = 4`** on any prologue table, given the size oracle: the `ok` half is
`vList_full`'s, the cost half is `Frag1.costSum_le_of_sizeOK 9`/`ctxVec_len_le_sizeOK 9` over the whole bridged list
(exactly as `Pin.pinKit'_of`), with the explicit constant `asmCk Ck' Cz N' B'`. -/
theorem verifyKit'''_of (N' B' Cz Cv : ℕ) : ∃ Ck : ℕ, ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    {tbl N B Wl Wc W₁ W₂ W T : V},
    TableOK tbl N → ProTable tbl → (∀ j < len tbl, formulaLen LAct (rowB tbl.[j]) ≤ B) →
    formulaLen LAct (Ple : V) ≤ B → NumTableOK T (N' : V) (B' : V) → Wl = layoutPieces → Wc = certPieces →
    W₁ = frag1Pieces → W₂ = frag2Pieces → W = proPieces → VerifySizeOracle tbl B Wl Wc W₁ W₂ W T Cz →
    VerifyKit''' tbl N B Wl Wc W₁ W₂ W T Cv Ck 4 := by
  obtain ⟨Ck, hCk1, h⟩ := vList_full N' B' Cz Cv
  refine ⟨Ck, fun V _ _ tbl N B Wl Wc W₁ W₂ W T htbl hP hBt hPle htblN hWl hWc hW₁ hW₂ hWp hsize ↦ ⟨?_, ?_⟩⟩
  · intro ρ x Γ i E A L hρ hx hR hΓ hE hA hL
    obtain ⟨ok, nd, sh, goal, -, -⟩ := h V htbl hP hBt hPle htblN hWl hWc hW₁ hW₂ hWp hsize hA hρ hx hR hΓ hE hL
    exact ⟨ok, nd, sh, goal⟩
  · intro ρ x Γ i E A L hρ hx hR hΓ hE hA hL
    obtain ⟨ok, nd, sh, goal, hlen, hsz⟩ := h V htbl hP hBt hPle htblN hWl hWc hW₁ hW₂ hWp hsize hA hρ hx hR hΓ hE hL
    have hE1 : (1 : V) ≤ E := by
      refine le_trans ?_ hE
      exact one_le_mul_of_one_le_of_one_le (by exact_mod_cast hCk1)
        (le_trans le_add_self (le_trans (succ_le_pow4 (dlen TAct ρ)) le_self_add))
    have cost := costSum_le_of_sizeOK 9 hE1 htbl hBt ok hsz
    obtain ⟨hF, hS⟩ := ctxVec_len_le_sizeOK 9 hE1 htbl hBt ok hsz (len (vList Wl Wc W T x i ρ L)) le_rfl
    have h38 : (3 * ((9 : ℕ) : V) + 11) = 38 := by push_cast; norm_num
    refine ⟨?_, ?_, ?_⟩
    · refine le_trans cost ?_
      rw [h38]
      refine mul_le_mul hlen ?_ zero_le zero_le
      refine add_le_add le_rfl (mul_le_mul_of_nonneg_left ?_ zero_le)
      exact add_le_add (ctxBoundG_mono2 le_rfl hlen) (add_le_add le_rfl (mul_le_mul_of_nonneg_right hlen zero_le))
    · show setLen LAct (ctxVec Γ (vList Wl Wc W T x i ρ L)).[len (vList Wl Wc W T x i ρ L)] ≤ _
      exact le_trans hS (ctxBoundG_mono2 le_rfl hlen)
    · show fvOccS LAct (ctxVec Γ (vList Wl Wc W T x i ρ L)).[len (vList Wl Wc W T x i ρ L)] ≤ _
      exact le_trans hF (add_le_add le_rfl (mul_le_mul_of_nonneg_right hlen zero_le))

/-- **The kit package over `VerifyGraph'`**: one table per model (with the row-body bound `B` covering `Plength`,
`Peq`, `Ple`), the three numeral tables, the six piece tables, the graph's EXISTENCE half (`A` per `ρ` and `E`, at
the E-room `Cv·p3(dlen ρ + 1) + 6·dlen ρ + 1` — from `verifyGraph''_exists_unconditional`), the kit and the pins. -/
def KitPackage''' (N B N' B' N₂ B₂ N₃ B₃ Ck Cv : ℕ) (Cχ : Semisentence LAct 1 → ℕ) (m : ℕ) : Prop :=
  ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁],
    ∃ tbl Wl Wc W₁ W₂ W T tblL tblM : V, TableOK tbl N ∧ TopTable tbl ∧
      (∀ j < len tbl, formulaLen LAct (rowB tbl.[j]) ≤ B) ∧
      formulaLen LAct (Plength : V) ≤ B ∧ formulaLen LAct (Peq : V) ≤ B ∧ formulaLen LAct (Ple : V) ≤ B ∧
      NumTableOK T N' B' ∧ LenTableOK tblL N₂ B₂ ∧ MulTableOK tblM N₃ B₃ ∧
      (∀ ρ E : V, Derivation TAct ρ → (Cv : V) * p3 (dlen TAct ρ + 1) + 6 * dlen TAct ρ + 1 ≤ E →
        ∃ A L : V, AxmTableOK' tbl E walkPieces A Cv ∧ VerifyGraph'' walkPieces Wl Wc W₁ W₂ W T A ρ L) ∧
      VerifyKit''' tbl N B Wl Wc W₁ W₂ W T Cv Ck m ∧ ∀ χ, PinKit' χ tbl N B (Cχ χ)

/-- The witness cap of `top_main'''`: `Top.Etop''` plus the E-room of the certificate table, `Cv·p3(d+1) + 6·d + 1`. -/
noncomputable def Etop''' (χ : Semisentence LAct 1) (k d : V) (Ck Cχ Cv : ℕ) (m : ℕ) : V :=
  Etop'' χ k d Ck Cχ m + ((Cv : V) * p3 (d + 1) + 6 * d + 1)

lemma le_Etop'''_top (χ : Semisentence LAct 1) (k d : V) (Ck Cχ Cv : ℕ) (m : ℕ) :
    Etop'' χ k d Ck Cχ m ≤ Etop''' χ k d Ck Cχ Cv m := le_self_add
lemma le_Etop'''_axm (χ : Semisentence LAct 1) (k d : V) (Ck Cχ Cv : ℕ) (m : ℕ) :
    (Cv : V) * p3 (d + 1) + 6 * d + 1 ≤ Etop''' χ k d Ck Cχ Cv m := le_add_self

end kit3

theorem top_main''' (χ : Semisentence LAct 1) (m : ℕ) {tbl N B Wl Wc W₁ W₂ W tN A N' B' tblL N₂ B₂ tblM N₃ B₃ : V}
    {Ck Cχ Cv : ℕ}
    (htbl : TableOK tbl N) (hT : TopTable tbl) (hB : ∀ j < len tbl, formulaLen LAct (rowB tbl.[j]) ≤ B)
    (hPl : formulaLen LAct (Plength : V) ≤ B) (hPeq : formulaLen LAct (Peq : V) ≤ B) (hPle : formulaLen LAct (Ple : V) ≤ B)
    (htblN : NumTableOK tN N' B') (htblL : LenTableOK tblL N₂ B₂) (htblM : MulTableOK tblM N₃ B₃)
    (hkit : VerifyKit''' tbl N B Wl Wc W₁ W₂ W tN Cv Ck m) (hpin : PinKit' χ tbl N B Cχ)
    {k ρ : V} (hρ : Proof TAct ρ (instB (⌜χ⌝ : V) k)) (hlen : dlen TAct ρ ≤ gBudget k)
    {L E : V} (hL : VerifyGraph'' walkPieces Wl Wc W₁ W₂ W tN A ρ L) (hA : AxmTableOK' tbl E walkPieces A (Cv : V))
    (hE : Etop'' χ k (dlen TAct ρ) Ck Cχ m ≤ E) :
    ∃ e Lr : V, LenDerivable TAct e (instB (⌜Box_g χ⌝ : V) k) ∧
      Lr + 4 ≤ 12 * formulaLen LAct (instB (⌜χ⌝ : V) k) + 13 ∧
      e ≤ topBound'' N B E Ck Cχ ‖k‖ (dlen TAct ρ) (setLen LAct (insert (boxFact (qNum χ) (bnum k)) (∅ : V)))
        (fvOccS LAct (insert (boxFact (qNum χ) (bnum k)) (∅ : V))) Lr (topD N' B' N₂ B₂ N₃ B₃ k (dlen TAct ρ)) m := by
  obtain ⟨x, hxdef⟩ : ∃ x, x = instB (⌜χ⌝ : V) k := ⟨_, rfl⟩
  obtain ⟨T, hTdef⟩ : ∃ T, T = boxFact (qNum χ) (bnum k) := ⟨_, rfl⟩
  obtain ⟨Γ₀, hΓ₀def⟩ : ∃ Γ₀ : V, Γ₀ = insert T (∅ : V) := ⟨_, rfl⟩
  rw [← hxdef] at hρ ⊢
  rw [← hTdef, ← hΓ₀def]
  have hx : IsSemiformula LAct 0 x := hxdef ▸ isFormula_instB_quote χ k
  have hq : IsSemiterm LAct (0 : V) (qNum χ) := isSemiterm_qNum χ
  have hbk : IsSemiterm LAct (0 : V) (bnum k) := isSemiterm_bnum_LAct 0 k
  have hTf : IsFormula LAct T := hTdef ▸ isFormula_boxFact hq hbk
  have hΓ₀ : IsFormulaSet LAct Γ₀ := hΓ₀def ▸ IsFormulaSet.insert_iff.mpr ⟨hTf, IsFormulaSet.empty⟩
  have hTmem : T ∈ Γ₀ := by rw [hΓ₀def]; simp
  -- the cap requirements, read off `Etop`
  have hE0 : Etop'' χ k (dlen TAct ρ) Ck Cχ m ≤ E := hE
  have r_walk : eWalk χ k ≤ E := le_trans (le_Etop''_walk χ k (dlen TAct ρ) Ck Cχ m) hE0
  have r_pin : ePin k Cχ ≤ E := le_trans (le_Etop''_pin χ k (dlen TAct ρ) Ck Cχ m) hE0
  have r_ver : eVer'' k (dlen TAct ρ) Ck Cχ m ≤ E := le_trans (le_Etop''_ver χ k (dlen TAct ρ) Ck Cχ m) hE0
  have r_js : eJs'' k (dlen TAct ρ) Ck Cχ m ≤ E := le_trans (le_Etop''_js χ k (dlen TAct ρ) Ck Cχ m) hE0
  have r_q : eQ χ ≤ E := le_trans (le_Etop''_q χ k (dlen TAct ρ) Ck Cχ m) hE0
  have r_k : eK k ≤ E := le_trans (le_Etop''_k χ k (dlen TAct ρ) Ck Cχ m) hE0
  have r_l : eL k ≤ E := le_trans (le_Etop''_l χ k (dlen TAct ρ) Ck Cχ m) hE0
  have r_b : eB k ≤ E := le_trans (le_Etop''_b χ k (dlen TAct ρ) Ck Cχ m) hE0
  have r_g : eG k ≤ E := le_trans (le_Etop''_g χ k (dlen TAct ρ) Ck Cχ m) hE0
  have r_d : eD (dlen TAct ρ) ≤ E := le_trans (le_Etop''_d χ k (dlen TAct ρ) Ck Cχ m) hE0
  have r_n5 : eN5 k ≤ E := le_trans (le_Etop''_n5 χ k (dlen TAct ρ) Ck Cχ m) hE0
  have r_n4a : eN4a k ≤ E := le_trans (le_Etop''_n4a χ k (dlen TAct ρ) Ck Cχ m) hE0
  have r_n4b : eN4b k ≤ E := le_trans (le_Etop''_n4b χ k (dlen TAct ρ) Ck Cχ m) hE0
  unfold eWalk at r_walk
  rw [← hxdef] at r_walk
  unfold ePin at r_pin
  unfold eVer'' at r_ver
  unfold eJs'' at r_js
  unfold eQ at r_q
  unfold eK at r_k
  unfold eL at r_l
  unfold eB at r_b
  unfold eG at r_g
  unfold eD at r_d
  unfold eN5 at r_n5
  unfold eN4a at r_n4a
  unfold eN4b at r_n4b
  have hE1 : (1 : V) ≤ E := le_trans (by norm_num) (le_trans le_add_self r_walk)
  -- (1) the root block
  obtain ⟨rok, rnd, rho, rsh, rlen, rlay⟩ := rootSteps_ok htbl hT hx hΓ₀ r_walk
  set Γ₁ := finalCtx Γ₀ (rootSteps x) with hΓ₁def
  have hΓ₁ : IsFormulaSet LAct Γ₁ := finalCtx_isFormulaSet 8 htbl hΓ₀ rok
  have rB : ∀ i < len (rootSteps x), formulaLen LAct (rowB tbl.[sRow (rootSteps x).[i]]) ≤ B :=
    fun i hi ↦ hB _ (sRow_lt_of_stepOK (rok i hi) (rho i hi))
  have rcost := costSum_le_of_hornOnly hE1 htbl rok rho rB
  obtain ⟨rF, rS⟩ := ctxVec_len_le hE1 htbl rok rho rB (len (rootSteps x)) le_rfl
  have rF' : fvOccS LAct Γ₁ ≤ topF1 B E (fvOccS LAct Γ₀) (len (rootSteps x)) := rF
  have rS' : setLen LAct Γ₁ ≤ topS1 B E (setLen LAct Γ₀) (fvOccS LAct Γ₀) (len (rootSteps x)) := rS
  -- (2) the pin block
  obtain ⟨P, pok, pnd, psh, pinst, pcost, pS, pF⟩ := hpin.pin k (hxdef ▸ rlay) hΓ₁ r_pin
  set Γ₂ := finalCtx Γ₁ P with hΓ₂def
  have hΓ₂ : IsFormulaSet LAct Γ₂ := finalCtx_isFormulaSet 9 htbl hΓ₁ pok
  have lay₂ : RootLayout Γ₂ x (0 + shiftsV P) := rlay.transport pnd
  -- (3) the verification block
  have r_ver' : (Ck : V) * ((dlen TAct ρ + 1) ^ m + (0 + shiftsV P)) ≤ E :=
    le_trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl (add_le_add le_rfl psh)) zero_le) r_ver
  obtain ⟨vok, vnd, vsh, vgoal⟩ := hkit.ok hρ hx lay₂ hΓ₂ r_ver' hA hL
  obtain ⟨vcost, vS, vF⟩ := hkit.cost hρ hx lay₂ hΓ₂ r_ver' hA hL
  obtain ⟨L₁, hL₁⟩ : ∃ L₁, L₁ = vList Wl Wc W tN x (0 + shiftsV P) ρ L := ⟨_, rfl⟩
  rw [← hL₁] at vok vnd vsh vgoal vcost vS vF
  set Γ₃ := finalCtx Γ₂ L₁ with hΓ₃def
  have hΓ₃ : IsFormulaSet LAct Γ₃ := finalCtx_isFormulaSet 9 htbl hΓ₂ vok
  have lay₃ : RootLayout Γ₃ x (0 + shiftsV P + shiftsV L₁) := lay₂.transport vnd
  set js := 0 + shiftsV P + 1 + shiftsV L₁ with hjsdef
  have hins₃ : neg LAct (insFact (^&js) (^&(js + 1)) (𝟎 : V)) ∈ Γ₃ := by
    have := lay₃.2.2.1
    have e1 : (0 : V) + shiftsV P + shiftsV L₁ + 1 = js := by rw [hjsdef]; ring
    have e2 : (0 : V) + shiftsV P + shiftsV L₁ + 2 = js + 1 := by rw [hjsdef]; ring
    rwa [e1, e2] at this
  have hinst₃ : neg LAct (instBFact (^&(js + 1)) (qNum χ) (bnum k)) ∈ Γ₃ := by
    have := mem_finalCtx_of_mem' vnd pinst
    rw [shiftIterV_neg (isFormula_instBFact (by simp) hq hbk), shiftIterV_instBFact (by simp) hq hbk,
      termShiftIterV_fvar, termShiftIterV_qNum, termShiftIterV_bnumTop] at this
    have e : (0 : V) + 2 + shiftsV P + shiftsV L₁ = js + 1 := by rw [hjsdef]; ring
    rwa [e] at this
  -- (4) the closing block
  have r_js' : js + 4 ≤ E := by
    refine le_trans ?_ r_js
    rw [hjsdef]
    calc (0 : V) + shiftsV P + 1 + shiftsV L₁ + 4 ≤ 0 + (Cχ : V) * (‖k‖ + 1) + 1 + (Ck : V) * (dlen TAct ρ + 1) ^ m + 4 :=
          add_le_add (add_le_add (add_le_add (add_le_add le_rfl psh) le_rfl) vsh) le_rfl
      _ = (Cχ : V) * (‖k‖ + 1) + 1 + (Ck : V) * (dlen TAct ρ + 1) ^ m + 4 := by rw [zero_add]
  obtain ⟨cok, cnd, csh, clen, cT⟩ := closeSteps_ok χ htbl hT htblN htblL htblM hΓ₃ hlen r_js' r_q r_k r_l r_b r_g r_d
    vgoal hins₃ hinst₃
  set Γ₄ := finalCtx Γ₃ (closeSteps χ k ρ js tN tblL tblM) with hΓ₄def
  have hΓ₄ : IsFormulaSet LAct Γ₄ := finalCtx_isFormulaSet 8 htbl hΓ₃ cok
  -- the whole list
  set S := topList χ k ρ P L₁ tN tblL tblM with hSdef
  have h89 : ((8 : ℕ) : V) ≤ ((9 : ℕ) : V) := by exact_mod_cast (by decide : (8 : ℕ) ≤ 9)
  have hSfin : finalCtx Γ₀ S = Γ₄ := by
    rw [hSdef, topList, ← hxdef, ← hjsdef, finalCtx_appendV, finalCtx_appendV, finalCtx_appendV, ← hΓ₁def,
      ← hΓ₂def, ← hΓ₃def]
  have hok : ListOK tbl E ((9 : ℕ) : V) Γ₀ S := by
    rw [hSdef, topList, ← hxdef, ← hjsdef]
    refine listOK_appendV (rok.mono h89) ?_
    rw [← hΓ₁def]
    refine listOK_appendV pok ?_
    rw [← hΓ₂def]
    refine listOK_appendV vok ?_
    rw [← hΓ₃def]
    exact cok.mono h89
  have hnd : NoDrop' S := by
    rw [hSdef, topList, ← hxdef, ← hjsdef]
    exact noDrop'_appendV rnd.noDrop' (noDrop'_appendV pnd (noDrop'_appendV vnd cnd))
  have hT₄ : T ∈ Γ₄ := by
    have := mem_finalCtx_of_mem' hnd hTmem
    rw [hSfin, hTdef, shiftIterV_target] at this
    rw [hTdef]; exact this
  have hnT₄ : neg LAct T ∈ Γ₄ := by rw [hTdef]; exact cT
  -- the leaf and the derivation
  have hleaf : DerivationOf TAct (axL Γ₄ T) Γ₄ := ⟨by simp, Derivation.axL hΓ₄ hT₄ hnT₄⟩
  have hleaf' : DerivationOf TAct (axL Γ₄ T) (ctxVec Γ₀ S).[len S] := by
    show DerivationOf TAct (axL Γ₄ T) (finalCtx Γ₀ S); rw [hSfin]; exact hleaf
  have hdlen_leaf : dlen TAct (axL Γ₄ T) = setLen LAct Γ₄ + 1 :=
    dlen_eq_of_graph hleaf.2 (DlenGraph.axL_iff.mpr rfl)
  have hproof : DerivationOf TAct (chainCode tbl Γ₀ S (axL Γ₄ T)) Γ₀ := chainCode_proof 9 htbl hok hleaf'
  have hcost := dlen_chainCode_le 9 hE1 htbl hok hleaf'
  -- the closing block's cost
  have hgoalLen : formulaLen LAct (goalFact (^&js) (bnum (dlen TAct ρ))) ≤ setLen LAct Γ₃ := by
    have h := formulaLen_le_setLen_of_mem (L := LAct) vgoal
    rwa [formulaLen_neg_eq (isFormula_goalFact (by simp) (isSemiterm_bnum_LAct 0 _))] at h
  set Q := topQ'' B E Ck Cχ ‖k‖ (dlen TAct ρ) (setLen LAct Γ₀) (fvOccS LAct Γ₀) (len (rootSteps x)) m with hQdef
  set D := topD N' B' N₂ B₂ N₃ B₃ k (dlen TAct ρ) with hDdef
  have hS2 : setLen LAct Γ₂ ≤ topS2' B E Cχ ‖k‖ (setLen LAct Γ₀) (fvOccS LAct Γ₀) (len (rootSteps x)) :=
    le_trans pS (ctxBoundG_le_ctxB rS' rF')
  have hF2 : fvOccS LAct Γ₂ ≤ topF2' B E Cχ ‖k‖ (fvOccS LAct Γ₀) (len (rootSteps x)) :=
    le_trans pF (add_le_add rF' le_rfl)
  have hS3 : setLen LAct Γ₃ ≤ topS3'' B E Ck Cχ ‖k‖ (dlen TAct ρ) (setLen LAct Γ₀) (fvOccS LAct Γ₀) (len (rootSteps x)) m :=
    le_trans vS (ctxBoundG_le_ctxB hS2 hF2)
  have hF3 : fvOccS LAct Γ₃ ≤ topF3'' B E Ck Cχ ‖k‖ (dlen TAct ρ) (fvOccS LAct Γ₀) (len (rootSteps x)) m :=
    le_trans vF (add_le_add hF2 le_rfl)
  have hBE : B * E ≤ Q := by rw [hQdef, topQ'']; exact le_add_self
  have hQg : 4 * formulaLen LAct (goalFact (^&js) (bnum (dlen TAct ρ))) ≤ Q := by
    rw [hQdef, topQ'']
    exact le_trans (mul_le_mul_of_nonneg_left (le_trans hgoalLen hS3) zero_le) le_self_add
  have hsz : SizeOK Q D (closeSteps χ k ρ js tN tblL tblM) := by
    unfold closeSteps
    refine sizeOK_appendV ((sizeOK_goalElim (D := D) (by simp) (isSemiterm_bnum_LAct 0 _)).mono hQg le_rfl) ?_
    have hE1' : (1 : V) ≤ E := hE1
    have hbd : IsSemiterm LAct (0 : V) (bnum (dlen TAct ρ)) := isSemiterm_bnum_LAct 0 _
    have hbg : IsSemiterm LAct (0 : V) (bnum (gBudget k)) := isSemiterm_bnum_LAct 0 _
    refine sizeOK_cons (stepSizeOK_sLemma (le_trans (formulaLen_lengthEqFact_le hPl r_n5) hBE)
      (le_trans (dlen_lengthEqCode_le htblN htblL k) (by rw [hDdef, topD]; exact le_trans le_self_add (le_trans le_self_add le_self_add)))) ?_
    refine sizeOK_cons (stepSizeOK_sLemma (le_trans (formulaLen_mulFact_le hPeq r_n4a) hBE)
      (le_trans (dlen_mulEqCode_le htblN htblM _ _) (by rw [hDdef, topD]; exact le_trans le_add_self (le_trans le_self_add le_self_add)))) ?_
    refine sizeOK_cons (stepSizeOK_sLemma (le_trans (formulaLen_mulFact_le hPeq r_n4b) hBE)
      (le_trans (dlen_mulEqCode_le htblN htblM _ _) (by rw [hDdef, topD]; exact le_trans le_add_self le_self_add))) ?_
    refine sizeOK_cons (stepSizeOK_sLemma
      (le_trans (formulaLen_leFact_le hE1' hbd hbg r_d r_g) (le_trans (mul_le_mul_of_nonneg_right hPle zero_le) hBE))
      (le_trans (dlen_leCode_le' htblN hlen) (by rw [hDdef, topD]; exact le_add_self))) ?_
    refine sizeOK_cons (stepSizeOK_horn0 (ttag_dlenDefIntro rfl _)) ?_
    refine sizeOK_cons (stepSizeOK_horn0 (ttag_proofIntro rfl _)) ?_
    refine sizeOK_cons (stepSizeOK_horn0 (ttag_leTrans _)) ?_
    refine sizeOK_cons (stepSizeOK_horn0 (ttag_lenDerIntro rfl _)) ?_
    refine sizeOK_cons (stepSizeOK_horn0 (ttag_gIntroNum rfl _)) ?_
    exact sizeOK_single (stepSizeOK_horn0 (ttag_boxIntro rfl _))
  have ccost := costSum_le_of_sizeOK 8 hE1 htbl hB cok hsz
  rw [clen] at ccost
  obtain ⟨_, cS⟩ := ctxVec_len_le_sizeOK 8 hE1 htbl hB cok hsz (len (closeSteps χ k ρ js tN tblL tblM)) le_rfl
  have cS' : setLen LAct Γ₄ ≤ setLen LAct Γ₃ + len (closeSteps χ k ρ js tN tblL tblM) * fvOccS LAct Γ₃ +
      (len (closeSteps χ k ρ js tN tblL tblM) * len (closeSteps χ k ρ js tN tblL tblM) +
        len (closeSteps χ k ρ js tN tblL tblM)) * growK B E Q := cS
  rw [clen] at cS'
  -- the total
  refine ⟨dlen TAct (chainCode tbl Γ₀ S (axL Γ₄ T)), len (rootSteps x), ?_, rlen, ?_⟩
  · refine ⟨chainCode tbl Γ₀ S (axL Γ₄ T), ?_, le_refl (dlen TAct (chainCode tbl Γ₀ S (axL Γ₄ T)))⟩
    rw [target_eq_boxFact, ← hTdef]
    have e : insert T (∅ : V) = {T} := mem_ext fun _ ↦ by simp
    show DerivationOf TAct _ {T}
    rw [← e, ← hΓ₀def]; exact hproof
  · have hsplit : costSum N E Γ₀ S = costSum N E Γ₀ (rootSteps x) +
        (costSum N E Γ₁ P + (costSum N E Γ₂ L₁ + costSum N E Γ₃ (closeSteps χ k ρ js tN tblL tblM))) := by
      rw [hSdef, topList, ← hxdef, ← hjsdef, costSum_appendV, costSum_appendV, costSum_appendV, ← hΓ₁def, ← hΓ₂def,
        ← hΓ₃def]
    have h_leaf : setLen LAct Γ₄ + 1 ≤ topS3'' B E Ck Cχ ‖k‖ (dlen TAct ρ) (setLen LAct Γ₀) (fvOccS LAct Γ₀) (len (rootSteps x)) m +
        15 * topF3'' B E Ck Cχ ‖k‖ (dlen TAct ρ) (fvOccS LAct Γ₀) (len (rootSteps x)) m + (15 * 15 + 15) * growK B E Q + 1 :=
      add_le_add (le_trans cS' (add_le_add (add_le_add hS3 (mul_le_mul_of_nonneg_left hF3 zero_le)) le_rfl)) le_rfl
    have h_root : costSum N E Γ₀ (rootSteps x) ≤
        len (rootSteps x) * (stepK N E B + 36 * topS1 B E (setLen LAct Γ₀) (fvOccS LAct Γ₀) (len (rootSteps x))) := by
      unfold topS1; unfold ctxBound at rcost; exact rcost
    have h_pin : costSum N E Γ₁ P ≤ (Cχ : V) * (‖k‖ + 1) *
        (costK N E B ((9 : ℕ) : V) (kitQ (Cχ : V) B E) (kitD (Cχ : V) ‖k‖) +
          38 * (ctxB (growK B E (kitQ (Cχ : V) B E)) (topS1 B E (setLen LAct Γ₀) (fvOccS LAct Γ₀) (len (rootSteps x)))
            (topF1 B E (fvOccS LAct Γ₀) (len (rootSteps x))) ((Cχ : V) * (‖k‖ + 1)) +
            (topF1 B E (fvOccS LAct Γ₀) (len (rootSteps x)) + (Cχ : V) * (‖k‖ + 1) * growK B E (kitQ (Cχ : V) B E)))) :=
      le_trans pcost (mul_le_mul_of_nonneg_left (add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (add_le_add (ctxBoundG_le_ctxB rS' rF') (add_le_add rF' le_rfl)) zero_le)) zero_le)
    have h_ver : costSum N E Γ₂ L₁ ≤ (Ck : V) * (dlen TAct ρ + 1) ^ m *
        (costK N E B ((9 : ℕ) : V) (kitQ (Ck : V) B E) (kitD (Ck : V) (dlen TAct ρ)) +
          38 * (ctxB (growK B E (kitQ (Ck : V) B E)) (topS2' B E Cχ ‖k‖ (setLen LAct Γ₀) (fvOccS LAct Γ₀) (len (rootSteps x)))
            (topF2' B E Cχ ‖k‖ (fvOccS LAct Γ₀) (len (rootSteps x))) ((Ck : V) * (dlen TAct ρ + 1) ^ m) +
            (topF2' B E Cχ ‖k‖ (fvOccS LAct Γ₀) (len (rootSteps x)) + (Ck : V) * (dlen TAct ρ + 1) ^ m * growK B E (kitQ (Ck : V) B E)))) :=
      le_trans vcost (mul_le_mul_of_nonneg_left (add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (add_le_add (ctxBoundG_le_ctxB hS2 hF2) (add_le_add hF2 le_rfl)) zero_le)) zero_le)
    have h_close : costSum N E Γ₃ (closeSteps χ k ρ js tN tblL tblM) ≤
        15 * (costK N E B ((8 : ℕ) : V) Q D + (3 * ((8 : ℕ) : V) + 11) *
          ((topS3'' B E Ck Cχ ‖k‖ (dlen TAct ρ) (setLen LAct Γ₀) (fvOccS LAct Γ₀) (len (rootSteps x)) m +
            15 * topF3'' B E Ck Cχ ‖k‖ (dlen TAct ρ) (fvOccS LAct Γ₀) (len (rootSteps x)) m + (15 * 15 + 15) * growK B E Q) +
           (topF3'' B E Ck Cχ ‖k‖ (dlen TAct ρ) (fvOccS LAct Γ₀) (len (rootSteps x)) m + 15 * growK B E Q))) := by
      refine le_trans ccost (mul_le_mul_of_nonneg_left (add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (add_le_add ?_ (add_le_add hF3 le_rfl)) zero_le)) zero_le)
      unfold ctxBoundG
      exact add_le_add (add_le_add hS3 (mul_le_mul_of_nonneg_left hF3 zero_le)) le_rfl
    refine le_trans hcost ?_
    rw [hdlen_leaf, hsplit]
    unfold topBound''
    calc setLen LAct Γ₄ + 1 + (costSum N E Γ₀ (rootSteps x) + (costSum N E Γ₁ P +
          (costSum N E Γ₂ L₁ + costSum N E Γ₃ (closeSteps χ k ρ js tN tblL tblM))))
        = (setLen LAct Γ₄ + 1) + costSum N E Γ₀ (rootSteps x) + costSum N E Γ₁ P + costSum N E Γ₂ L₁ +
          costSum N E Γ₃ (closeSteps χ k ρ js tN tblL tblM) := by ring
      _ ≤ _ := add_le_add (add_le_add (add_le_add (add_le_add h_leaf h_root) h_pin) h_ver) h_close

theorem boundedInnerNec_of_kit''' (m : ℕ) (hm3 : 3 ≤ m) {N B N' B' N₂ B₂ N₃ B₃ Ck Cv : ℕ} {Cχ : Semisentence LAct 1 → ℕ}
    (hpkg : KitPackage''' N B N' B' N₂ B₂ N₃ B₃ Ck Cv Cχ m) : BoundedInnerNec (deg m) where
  nec χ := by
    -- `n = max m 1` is fixed BEFORE the witness: the constant mentions it and must have it in scope
    obtain ⟨n, hn_def⟩ : ∃ n : ℕ, n = max m 1 := ⟨_, rfl⟩
    have hn : 1 ≤ n := hn_def ▸ le_max_right m 1
    have hmn : m ≤ n := hn_def ▸ le_max_left m 1
    -- the constant is a NATURAL metavariable (`_`): the final `exact` assigns it by unification (a `?_` goal is
    -- synthetic-opaque and would not be)
    exact ⟨_, fun V _ _ k hk ↦ by
      obtain ⟨tbl, Wl, Wc, W₁, W₂, W, T, tblL, tblM, htbl, hT, hB, hPl, hPeq, hPle, htblN, htblL, htblM, hex, hkit, hpin⟩ := hpkg V
      obtain ⟨ρ, hρ, hlen⟩ := hk
      obtain ⟨A, L, hA, hL⟩ := hex ρ (Etop''' χ k (dlen TAct ρ) Ck (Cχ χ) Cv m) hρ.2
        (le_Etop'''_axm χ k (dlen TAct ρ) Ck (Cχ χ) Cv m)
      obtain ⟨e, Lr, he, hLr, hbound⟩ := top_main''' χ m htbl hT hB hPl hPeq hPle htblN htblL htblM hkit (hpin χ) hρ hlen hL hA
        (le_Etop'''_top χ k (dlen TAct ρ) Ck (Cχ χ) Cv m)
      refine ⟨e, ?_, he⟩
      -- the graded inputs (`G = gBudget k + 1`, `u = ‖k‖ + 1`)
      have hc := pbCtx_gBudget k
      have hlk : PB (gBudget k + 1) (‖k‖ + 1) 1 ‖k‖ 0 1 := (PB.u_ hc).of_le le_self_add
      have hone : PB (gBudget k + 1) (‖k‖ + 1) 1 (1 : V) 0 1 := PB.one'.mono hc (e' := 0) (f' := 1) le_rfl (by norm_num)
      have h1u : PB (gBudget k + 1) (‖k‖ + 1) 1 (1 : V) 1 0 := PB.one'.mono hc (e' := 1) (f' := 0) (by norm_num) le_rfl
      have h3u : PB (gBudget k + 1) (‖k‖ + 1) 3 (3 : V) 0 1 := PB.three.mono hc (e' := 0) (f' := 1) le_rfl (by norm_num)
      have hbk : PB (gBudget k + 1) (‖k‖ + 1) 7 (termLen LAct (bnum k)) 0 1 := by
        refine PB.of_le (termLen_bnum_le_V k) ?_
        have := (hlk.smul 6).add hone
        simpa using this
      have hg1 : PB (gBudget k + 1) (‖k‖ + 1) 1 (gBudget k) 1 0 := (PB.G_ hc).of_le le_self_add
      have hd1 : PB (gBudget k + 1) (‖k‖ + 1) 1 (dlen TAct ρ + 1) 1 0 := (PB.G_ hc).of_le (add_le_add hlen le_rfl)
      have hd0 : PB (gBudget k + 1) (‖k‖ + 1) 1 (dlen TAct ρ) 1 0 := hg1.of_le hlen
      have hCk : PB (gBudget k + 1) (‖k‖ + 1) Ck (Ck : V) 0 0 := PB.const Ck
      have hCχ : PB (gBudget k + 1) (‖k‖ + 1) (Cχ χ) (Cχ χ : V) 0 0 := PB.const _
      have hqN : PB (gBudget k + 1) (‖k‖ + 1) (2 * (⌜χ⌝ : ℕ) + 1) (termLen LAct (qNum χ : V)) 0 0 :=
        PB.natCast _ (termLen_qNum_le χ)
      -- `|x| ≤ |χ|·|bnum k|`
      have hx : PB (gBudget k + 1) (‖k‖ + 1) (flen (Rewriting.emb χ : Semiproposition LAct 1) * 7)
          (formulaLen LAct (instB (⌜χ⌝ : V) k)) 0 1 :=
        PB.of_le (by
          have := formulaLen_instB_le (Sentence.quote_isSemiformul₁ χ) k
          rwa [formulaLen_quote_semisentence_V'] at this) ((PB.const _).mul hbk)
      -- `E = Etop''`: each summand is `≲ G^n`, `n := max m 1`
      have hdm : PB (gBudget k + 1) (‖k‖ + 1) (1 ^ m) ((dlen TAct ρ + 1) ^ m) n 0 :=
        (hd1.pow m).mono hc (e' := n) (f' := 0) (by omega) (by omega)
      have h1n : PB (gBudget k + 1) (‖k‖ + 1) 1 (1 : V) n 0 := PB.one'.mono hc (e' := n) (f' := 0) (by omega) le_rfl
      have h3n : PB (gBudget k + 1) (‖k‖ + 1) 3 (3 : V) n 0 := PB.three.mono hc (e' := n) (f' := 0) (by omega) le_rfl
      have e1 := (PB.uG hc (((PB.two.mul hx).add ((PB.natCast (q := (8 : V)) 8 (by norm_num)).mono hc (e' := 0) (f' := 1)
        le_rfl (by norm_num))).mono hc (e' := 0) (f' := 1) le_rfl (by norm_num))).mono hc (e' := n) (f' := 0) (by omega) le_rfl
      have e2 := (PB.uG hc (((hCχ.mul (hlk.add (PB.one'.mono hc (e' := 0) (f' := 1) le_rfl (by norm_num)))).of_le
        (le_of_eq (by ring : (Cχ χ : V) * (‖k‖ + 0 + 1) = (Cχ χ : V) * (‖k‖ + 1)))).mono hc (e' := 0) (f' := 1)
        le_rfl (by norm_num))).mono hc (e' := n) (f' := 0) (by omega) le_rfl
      have hin := (PB.uG hc (((hCχ.mul (PB.u_ hc)).of_le (le_of_eq (zero_add ((Cχ χ : V) * (‖k‖ + 1))))).mono hc
        (e' := 0) (f' := 1) le_rfl (by norm_num))).mono hc (e' := n) (f' := 0) (by omega) le_rfl
      have e3 := (hCk.mul (hdm.add hin)).mono hc (e' := n) (f' := 0) (by omega) le_rfl
      have e4 := ((((PB.uG hc ((hCχ.mul (PB.u_ hc)).mono hc (e' := 0) (f' := 1) le_rfl (by norm_num))).mono hc (e' := n) (f' := 0) (by omega) le_rfl).add h1n).add
        ((hCk.mul hdm).mono hc (e' := n) (f' := 0) (by omega) le_rfl)).add
        ((PB.natCast (q := (4 : V)) 4 (by norm_num)).mono hc (e' := n) (f' := 0) (by omega) le_rfl)
      have e5 := hqN.mono hc (e' := n) (f' := 0) (by omega) le_rfl
      have e6 := (PB.uG hc hbk).mono hc (e' := n) (f' := 0) (by omega) le_rfl
      have e7 := (PB.uG hc (PB.of_le (termLen_bnum_le_V ‖k‖) (((hlk.of_le (length_le _)).smul 6).add hone))).mono hc (e' := n) (f' := 0) (by omega) le_rfl
      have e8 := (PB.reduce hc (PB.of_le (termLen_bnum_le_V (‖k‖ * ‖k‖))
        (((((hlk.mul hlk).of_le (length_le _)).smul 6).add (hone.mono hc (e' := 0) (f' := 2) le_rfl (by norm_num))).mono hc
          (e' := 0) (f' := 3) le_rfl (by norm_num)))).mono hc (e' := n) (f' := 0) (by omega) le_rfl
      have e9 := (PB.of_le (termLen_bnum_le_V (gBudget k)) (((hg1.of_le (length_le _)).smul 6).add h1u)).mono hc (e' := n) (f' := 0) (by omega) le_rfl
      have e10 := (PB.of_le (termLen_bnum_le_V (dlen TAct ρ)) (((hd0.of_le (length_le _)).smul 6).add h1u)).mono hc (e' := n) (f' := 0) (by omega) le_rfl
      have e11 := (PB.uG hc ((hlk.smul 12).add h3u)).mono hc (e' := n) (f' := 0) (by omega) le_rfl
      have hs1 := PB.of_le (length_le (‖k‖ * ‖k‖ + ‖k‖ + ‖k‖))
        (((hlk.mul hlk).add (hlk.mono hc (e' := 0) (f' := 2) le_rfl (by norm_num))).add
          (hlk.mono hc (e' := 0) (f' := 2) le_rfl (by norm_num)))
      have e12 := (PB.reduce hc (((hs1.smul 12).add (PB.three.mono hc (e' := 0) (f' := 2) le_rfl (by norm_num))).mono hc
        (e' := 0) (f' := 3) le_rfl (by norm_num))).mono hc (e' := n) (f' := 0) (by omega) le_rfl
      have hle2 : ‖k‖ * ‖k‖ * ‖k‖ + ‖k‖ * ‖k‖ + ‖k‖ ≤ gBudget k + gBudget k + gBudget k := by
        unfold gBudget; exact add_le_add (add_le_add le_rfl (sq_le_cube _)) (le_cube _)
      have hs2 := PB.of_le (length_le (‖k‖ * ‖k‖ * ‖k‖ + ‖k‖ * ‖k‖ + ‖k‖)) (PB.of_le hle2 ((hg1.add hg1).add hg1))
      have e13 := ((hs2.smul 12).add (PB.three.mono hc (e' := 1) (f' := 0) (by norm_num) le_rfl)).mono hc (e' := n) (f' := 0) (by omega) le_rfl
      have hCv : PB (gBudget k + 1) (‖k‖ + 1) Cv (Cv : V) 0 0 := PB.const Cv
      have e14a := (hCv.mul ((hd1.mul hd1).mul hd1)).mono hc (e' := n) (f' := 0) (by omega) le_rfl
      have e14b := ((hd0.smul 6).add h1u).mono hc (e' := n) (f' := 0) (by omega) le_rfl
      have e14 := e14a.add e14b
      have hE₀ := (((((((((((((e1.add e2).add e3).add e4).add e5).add e6).add e7).add e8).add e9).add e10).add e11).add e12).add e13).add e14)
      have hE := PB.of_le (q := Etop''' χ k (dlen TAct ρ) Ck (Cχ χ) Cv m) (le_of_eq (by
        unfold Etop''' Etop'' eWalk ePin eVer'' eJs'' eQ eK eL eB eG eD eN5 eN4a eN4b p3; push_cast; ring)) hE₀
      -- `S₀, F₀ ≤ |Pbox| · (2⌜χ⌝ + 6‖k‖ + 9)`
      have hq : IsSemiterm LAct (0 : V) (qNum χ) := isSemiterm_qNum χ
      have hbk' : IsSemiterm LAct (0 : V) (bnum k) := isSemiterm_bnum_LAct 0 k
      have hTf : IsFormula LAct (boxFact (qNum χ) (bnum k)) := isFormula_boxFact hq hbk'
      have hB' : formulaLen LAct (boxFact (qNum χ) (bnum k)) ≤
          formulaLen LAct (Pbox : V) * (((2 * (⌜χ⌝ : ℕ) + 1 : ℕ) : V) + (6 * ‖k‖ + 1)) :=
        formulaLen_boxFact_le (le_trans (by norm_num) le_add_self) hq hbk' (le_trans (termLen_qNum_le χ) le_self_add)
          (le_trans (termLen_bnum_le_V k) le_add_self)
      have hBp := PB.uG hc (((PB.const (2 * (⌜χ⌝ : ℕ) + 1)).mono hc (e' := 0) (f' := 1) le_rfl (by norm_num)).add
        ((hlk.smul 6).add hone))
      have hPb := PB.natCast (G := gBudget k + 1) (u := ‖k‖ + 1)
        (flen (Rewriting.emb (Semiformula.lMap emb (↑boxCoreS : ArithmeticSemisentence 2)) : Semiproposition LAct 2))
        (le_of_eq (formulaLen_quote_semisentence_V' _))
      have hTlen := PB.of_le hB' ((hPb.mul hBp).mono hc (e' := 1) (f' := 0) (by norm_num) le_rfl)
      have hS := PB.of_le (le_trans (setLen_insert_le (L := LAct) (boxFact (qNum χ) (bnum k)) (∅ : V))
        (by rw [setLen_empty', zero_add])) hTlen
      have hF := PB.of_le (le_trans (fvOccS_insert_le (L := LAct) (boxFact (qNum χ) (bnum k)) (∅ : V))
        (by rw [fvOccS_empty, zero_add]; exact fvOccF_le_formulaLen hTf.isUFormula)) hTlen
      -- `Lr ≤ 12|x| + 9`
      have h1 : Lr ≤ 12 * formulaLen LAct (instB (⌜χ⌝ : V) k) + 9 := by
        have : Lr + 4 ≤ 12 * formulaLen LAct (instB (⌜χ⌝ : V) k) + 9 + 4 := by
          refine le_trans hLr (le_of_eq ?_); ring
        exact le_of_add_le_add_right this
      have hL := PB.of_le h1 (((PB.natCast (q := (12 : V)) 12 (by norm_num)).mul hx).add
        ((PB.natCast (q := (9 : V)) 9 (by norm_num)).mono hc (e' := 0) (f' := 1) le_rfl (by norm_num)))
      have hD := topD_pb N' B' N₂ B₂ N₃ B₃ k (dlen TAct ρ) hlen
      have hmain := topBound''_pb hc m n hmn hn (PB.const N) (PB.const B) hE hCk hCχ (PB.u_ hc) hd1 hdm hS hF hL hD
      have hfin := PB.final_pow hc hmain
      rw [show deg m = 4 * n by rw [deg, hn_def]]
      exact le_trans hbound hfin⟩





/-! ## 8. THE THEOREM: `BoundedInnerNec 24` and Dupoc's self-cooperation, conditional on the two named oracles -/

section theorem24

/-- **The size oracle** at the package's tables (`VerifySizeOracle` for every `IndRec` table with its row-body
bound, at the canonical piece tables) — THE ONE remaining hypothesis of the theorem (`Verify4`'s
`verifyGraph''_ok_pow4` gives `ListOK`/`NoDrop'`/`shiftsV`/the goal fact, not `len`/`SizeOK`). -/
def SizeOracle (Cz : ℕ) : Prop :=
  ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (tbl B T : V), IndRecTable tbl →
    (∀ j < len tbl, formulaLen LAct (rowB tbl.[j]) ≤ B) →
    VerifySizeOracle tbl B layoutPieces certPieces frag1Pieces frag2Pieces proPieces T Cz

/-- The standard lengths of the three predicate codes the closing block needs below `B`. -/
noncomputable def cPlength : ℕ := flen (Rewriting.emb (Semiformula.lMap emb (↑lengthDef : ArithmeticSemisentence 2)) : Semiproposition LAct 2)
noncomputable def cPeq : ℕ := flen (Rewriting.emb eqS : Semiproposition LAct 2)
noncomputable def cPle : ℕ := flen (Rewriting.emb leS : Semiproposition LAct 2)

lemma formulaLen_Plength_eq : formulaLen LAct (Plength : V) = (cPlength : V) := by
  unfold Plength; rw [formulaLen_quote_semisentence_V']; rfl
lemma formulaLen_Peq_eq : formulaLen LAct (Peq : V) = (cPeq : V) := by
  unfold Peq; rw [formulaLen_quote_semisentence_V']; rfl
lemma formulaLen_Ple_eq : formulaLen LAct (Ple : V) = (cPle : V) := by
  unfold Ple; rw [formulaLen_quote_semisentence_V']; rfl

/-- **An `IndRec` table with its row-body bound exists in every model** (`Pin.exists_numIdTableB`'s proof at
`indRecRows`). -/
theorem exists_indRecTableB : ∃ N B : ℕ, ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁],
    ∃ tbl : V, TableOK tbl (N : V) ∧ IndRecTable tbl ∧ ∀ j < len tbl, formulaLen LAct (rowB tbl.[j]) ≤ (B : V) := by
  obtain ⟨N, hN⟩ := exists_rows indRecRows
  refine ⟨N, rowsB indRecRows, fun V _ _ ↦ ?_⟩
  obtain ⟨rows, hlen, hok, hidx⟩ := hN V
  refine ⟨vecOf rows, tableOK_vecOf rows hok, ⟨?_, ?_⟩, ?_⟩
  · rw [len_vecOf, hlen, indRecRows_length]
  · intro i h
    have h' : i < rows.length := by rw [hlen]; exact h
    rw [nth_vecOf rows i h']
    exact hidx i h h'
  · intro j hj
    rw [len_vecOf] at hj
    obtain ⟨i, rfl⟩ := eq_nat_of_lt_nat hj
    have h' : i < rows.length := by exact_mod_cast hj
    have h : i < indRecRows.length := by rw [← hlen]; exact h'
    rw [nth_vecOf rows i h', (hidx i h h').2, ← Sentence.coe_quote_eq_quote (V := V), flN_cast]
    exact_mod_cast flN_le_rowsB indRecRows i h

/-- **The package holds at `m = 4`, given the size oracle**: ONE table per model (`IndRecTable ⇒ ProAxmTable ⇒
NumIdTable ⇒ ProTable ⇒ TopTable`, `exists_indRecTableB`), the row-body bound `B` enlarged by the three predicate
lengths, the numeral tables, the graph's existence half from `verifyGraph''_exists_unconditional` (the `axm` case
UNCONDITIONAL: `IndRec`'s recognizer, `Cv = C`), the kit from `verifyKit'''_of`, the pins from `pinKit'_of`. -/
theorem kitPackage'''_of_size (Cz : ℕ) (hsz : SizeOracle Cz) :
    ∃ (N B N' B' N₂ B₂ N₃ B₃ Ck Cv : ℕ) (Cχ : Semisentence LAct 1 → ℕ),
      KitPackage''' N B N' B' N₂ B₂ N₃ B₃ Ck Cv Cχ 4 := by
  obtain ⟨N, B₀, hTab⟩ := exists_indRecTableB
  obtain ⟨N', B', hNum⟩ := exists_numTable
  obtain ⟨N₂, B₂, hLen⟩ := exists_lenTable
  obtain ⟨N₃, B₃, hMul⟩ := exists_mulTable
  obtain ⟨C, hex⟩ := verifyGraph''_exists_unconditional
  obtain ⟨Ck, hkit⟩ := verifyKit'''_of N' B' Cz C
  refine ⟨N, B₀ + cPlength + cPeq + cPle, N', B', N₂, B₂, N₃, B₃, Ck, C,
    fun χ ↦ Classical.choose (pinKit'_of χ N' B'), fun V _ _ ↦ ?_⟩
  obtain ⟨tbl, htbl, hPA, hB₀⟩ := hTab V
  obtain ⟨tblN, hN⟩ := hNum V
  obtain ⟨tblL, hL⟩ := hLen V
  obtain ⟨tblM, hM⟩ := hMul V
  have hB : ∀ j < len tbl, formulaLen LAct (rowB tbl.[j]) ≤ ((B₀ + cPlength + cPeq + cPle : ℕ) : V) := fun j hj ↦
    le_trans (hB₀ j hj) (by exact_mod_cast (by omega : B₀ ≤ B₀ + cPlength + cPeq + cPle))
  have hPl : formulaLen LAct (Plength : V) ≤ ((B₀ + cPlength + cPeq + cPle : ℕ) : V) := by
    rw [formulaLen_Plength_eq]; exact_mod_cast (by omega : cPlength ≤ B₀ + cPlength + cPeq + cPle)
  have hPeq : formulaLen LAct (Peq : V) ≤ ((B₀ + cPlength + cPeq + cPle : ℕ) : V) := by
    rw [formulaLen_Peq_eq]; exact_mod_cast (by omega : cPeq ≤ B₀ + cPlength + cPeq + cPle)
  have hPle : formulaLen LAct (Ple : V) ≤ ((B₀ + cPlength + cPeq + cPle : ℕ) : V) := by
    rw [formulaLen_Ple_eq]; exact_mod_cast (by omega : cPle ≤ B₀ + cPlength + cPeq + cPle)
  refine ⟨tbl, layoutPieces, certPieces, frag1Pieces, frag2Pieces, proPieces, tblN, tblL, tblM, htbl,
    hPA.proTable.topTable, hB, hPl, hPeq, hPle, hN, hL, hM, ?_, ?_, ?_⟩
  · intro ρ E hd hE
    exact hex V htbl hPA rfl rfl rfl hd hE
  · exact hkit V htbl hPA.proTable hB hPle hN rfl rfl rfl rfl rfl (hsz V tbl _ tblN hPA hB)
  · intro χ
    exact Classical.choose_spec (pinKit'_of χ N' B') V htbl hPA.numIdTable hB hN

lemma deg_four : deg 4 = 16 := rfl

/-- **`BoundedInnerNec 16`** (`deg 4 = 16`), conditional on the size oracle ONLY (the `axm` case is unconditional
since `Verify3`/`IndRec`). -/
theorem boundedInnerNec_sixteen_of_size (Cz : ℕ) (hsz : SizeOracle Cz) : BoundedInnerNec 16 := by
  obtain ⟨N, B, N', B', N₂, B₂, N₃, B₃, Ck, Cv, Cχ, hpkg⟩ := kitPackage'''_of_size Cz hsz
  exact boundedInnerNec_of_kit''' 4 (by norm_num) hpkg

/-- **Critch's Theorem 3.7 in PA-`S`, conditional on the size oracle**: for all large `k`, `Dupoc k` cooperates
with itself and `Cupod k` defects against itself (`Assembly/Cell.dupoc_self_coop` at `d = 16`). -/
theorem dupoc_self_coop_of_size (Cz : ℕ) (hsz : SizeOracle Cz) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 2 (Dupoc k) (Dupoc k) (Dupoc k) 0 ∧ EvalGraph 2 (Cupod k) (Cupod k) (Cupod k) 1 :=
  dupoc_self_coop (boundedInnerNec_sixteen_of_size Cz hsz)

end theorem24

end ArithS
