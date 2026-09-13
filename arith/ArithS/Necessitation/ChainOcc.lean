import ArithS.Necessitation.Chain

/-!
# ArithS.Necessitation.ChainOcc — the per-step bound with the additive shift term

`Chain.dlen_applyStep_le` charges the two shifting steps (tag 2 `introFactCode`, tag 3
`elimExistsCode` on a leaf) through `|setShift Γ| ≤ 2|Γ|`. `ShiftLen` proved the additive law
`|setShift Γ| ≤ |Γ| + fvOccS Γ`; `stepCostOcc` is `stepCost` with that term on tags 2 and 3
(`introCostOcc` replaces one `|Γ|` of `introCost` by `fvOccS Γ`) and `dlen_applyStep_le_occ` is
the sharpened per-step bound (`DESIGN_describe.md` §10: a walk of `n` shifting steps over a
context of `G` characters then costs `n·(G + fvOccS Γ)`, not `2ⁿ·G`).

`stepCostOcc` is a plain function (no `Σ₁` blueprint): the chain builder's PR cost sum stays
`stepCost`; the walk's cost analysis only needs the additive bound to EXIST per step.
-/

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

section perStepOcc

open LAct

/-- `introCost` with one `G` traded for the occurrence count `O` (`dlen_introFactCode_le_occ`):
`N + (m + 2j + 9)G + O + (m+11)BE + (m+1)²(BE + m) + B + mE + 2m + (2j+1)((j+2)BE + 1) + 12`. -/
noncomputable def introCostOcc (N E G O m j B : V) : V :=
  N + (m + 2 * j + 9) * G + O + (m + 11) * (B * E) + (m + 1) * (m + 1) * (B * E + m) + B + m * E + 2 * m
    + (2 * j + 1) * ((j + 2) * (B * E) + 1) + 12

/-- `stepCost` with the additive shift term on the two shifting tags:
tag 2 `introCostOcc`; tag 3 `5G + fvOccS Γ + 7|P| + 10`; every other tag `stepCost`. -/
noncomputable def stepCostOcc (N E Γ s : V) : V :=
  if sTag s = 2 then
    introCostOcc N E (setLen LAct Γ) (fvOccS LAct Γ) (len (sEv s)) (len (sAs s))
      (formulaLen LAct (impChainV LAct (sAs s) (^∃ (sC s))))
  else if sTag s = 3 then
    5 * setLen LAct Γ + fvOccS LAct Γ + 7 * formulaLen LAct (π₂ s) + 10
  else stepCost N E Γ s

lemma stepCostOcc_tag0 {N E Γ s : V} (h : sTag s = 0) : stepCostOcc N E Γ s = stepCost N E Γ s := by
  simp [stepCostOcc, h]
lemma stepCostOcc_tag1 {N E Γ s : V} (h : sTag s = 1) : stepCostOcc N E Γ s = stepCost N E Γ s := by
  simp [stepCostOcc, h]
lemma stepCostOcc_tag2 {N E Γ s : V} (h : sTag s = 2) :
    stepCostOcc N E Γ s = introCostOcc N E (setLen LAct Γ) (fvOccS LAct Γ) (len (sEv s)) (len (sAs s))
      (formulaLen LAct (impChainV LAct (sAs s) (^∃ (sC s)))) := by simp [stepCostOcc, h]
lemma stepCostOcc_tag3 {N E Γ s : V} (h : sTag s = 3) :
    stepCostOcc N E Γ s = 5 * setLen LAct Γ + fvOccS LAct Γ + 7 * formulaLen LAct (π₂ s) + 10 := by
  simp [stepCostOcc, h]
lemma stepCostOcc_tag4 {N E Γ s : V} (h : sTag s = 4) : stepCostOcc N E Γ s = stepCost N E Γ s := by
  simp [stepCostOcc, h]
lemma stepCostOcc_tag5 {N E Γ s : V} (h : sTag s = 5) : stepCostOcc N E Γ s = stepCost N E Γ s := by
  simp [stepCostOcc, h]

lemma introCostOcc_bound {a N d G O m j B E : V} (h : a ≤ N) :
    a + d + (m + 2 * j + 9) * G + O + (m + 11) * (B * E) + (m + 1) * (m + 1) * (B * E + m) + B + m * E + 2 * m
        + (2 * j + 1) * ((j + 2) * (B * E) + 1) + 12
      ≤ d + introCostOcc N E G O m j B := by
  unfold introCostOcc
  calc a + d + (m + 2 * j + 9) * G + O + (m + 11) * (B * E) + (m + 1) * (m + 1) * (B * E + m) + B + m * E
          + 2 * m + (2 * j + 1) * ((j + 2) * (B * E) + 1) + 12
      = a + (d + (m + 2 * j + 9) * G + O + (m + 11) * (B * E) + (m + 1) * (m + 1) * (B * E + m) + B + m * E
          + 2 * m + (2 * j + 1) * ((j + 2) * (B * E) + 1) + 12) := by ring
    _ ≤ N + (d + (m + 2 * j + 9) * G + O + (m + 11) * (B * E) + (m + 1) * (m + 1) * (B * E + m) + B + m * E
          + 2 * m + (2 * j + 1) * ((j + 2) * (B * E) + 1) + 12) := add_le_add h le_rfl
    _ = _ := by ring

/-- The sharpening is one: `introCostOcc ≤ introCost` once `O ≤ G` (`fvOccS_le_setLen`). -/
lemma introCostOcc_le_introCost {N E G O m j B : V} (hO : O ≤ G) :
    introCostOcc N E G O m j B ≤ introCost N E G m j B := by
  unfold introCostOcc introCost
  calc N + (m + 2 * j + 9) * G + O + (m + 11) * (B * E) + (m + 1) * (m + 1) * (B * E + m) + B + m * E + 2 * m
        + (2 * j + 1) * ((j + 2) * (B * E) + 1) + 12
      ≤ N + (m + 2 * j + 9) * G + G + (m + 11) * (B * E) + (m + 1) * (m + 1) * (B * E + m) + B + m * E + 2 * m
        + (2 * j + 1) * ((j + 2) * (B * E) + 1) + 12 := by gcongr
    _ = _ := by ring

/-- **One step costs at most `stepCostOcc`** — `dlen_applyStep_le` with the additive shift term on
tags 2 and 3 (`dlen_introFactCode_le_occ`, `setLen_setShift_le_occ`); the other tags are
`dlen_applyStep_le` verbatim. -/
theorem dlen_applyStep_le_occ (M : ℕ) {tbl N E Γ s e : V} (hE : 1 ≤ E) (htbl : TableOK tbl N)
    (hok : StepOK tbl E (M : V) Γ s) (he : DerivationOf TAct e (ctxAfter Γ s)) :
    dlen TAct (applyStep tbl Γ s e) ≤ dlen TAct e + stepCostOcc N E Γ s := by
  have hΓ := hok.1
  rcases hok.2 with ⟨ht, hh, hB⟩ | ⟨ht, hh, hB⟩ | ⟨ht, hh, hB⟩ | ⟨ht, hP, hmem⟩ | ⟨ht, hp, hq, hmem⟩ | ⟨ht, hsub⟩
  · rw [stepCostOcc_tag0 ht]; exact dlen_applyStep_le M hE htbl hok he
  · rw [stepCostOcc_tag1 ht]; exact dlen_applyStep_le M hE htbl hok he
  · obtain ⟨es, l, hes_eq, hl_eq, hm, hes', hneg'⟩ := hh.lists M
    have hes : ∀ e ∈ es, IsTerm LAct e := fun e he ↦ (hes' e he).1
    have hrow := htbl _ hh.1
    rw [hm, hB, hl_eq, impChainV_vecOf] at hrow
    obtain ⟨has, hc⟩ := isSemiformula_of_impChain hrow.1
    have hR : IsSemiformula LAct ((es.length : V) + 1) (sC s) := IsSemiformula.exs.mp hc
    have hΛ := hrow.2.1
    rw [qqAlls_natCast] at hΛ
    have hneg : ∀ a ∈ l, neg LAct (instOuter LAct es a) ∈ Γ := fun a ha ↦ by
      have := hneg' a ha
      rwa [subst_revV_vecOf es (has a ha) hes] at this
    rw [ctxAfter_tag2 ht, hes_eq, subst_qVec_revV_vecOf es hR hes] at he
    rw [applyStep_tag2 ht, stepCostOcc_tag2 ht, hes_eq, hl_eq, len_vecOf, len_vecOf, impChainV_vecOf,
      introFactV_vecOf Γ es l has hR hes]
    exact le_trans (dlen_introFactCode_le_occ hE has hR hes' hΓ hneg hΛ he le_rfl) (introCostOcc_bound hrow.2.2)
  · rw [stepCostOcc_tag3 ht]
    have h := dlen_applyStep_le M hE htbl hok he
    rw [stepCost_tag3 ht] at h
    refine le_trans h ?_
    have hsh := setLen_setShift_le_occ hΓ
    calc dlen TAct e + (4 * setLen LAct Γ + setLen LAct (setShift LAct Γ) + 7 * formulaLen LAct (π₂ s) + 10)
        ≤ dlen TAct e + (4 * setLen LAct Γ + (setLen LAct Γ + fvOccS LAct Γ) + 7 * formulaLen LAct (π₂ s) + 10) := by
          gcongr
      _ = _ := by ring
  · rw [stepCostOcc_tag4 ht]; exact dlen_applyStep_le M hE htbl hok he
  · rw [stepCostOcc_tag5 ht]; exact dlen_applyStep_le M hE htbl hok he

end perStepOcc

end ArithS
