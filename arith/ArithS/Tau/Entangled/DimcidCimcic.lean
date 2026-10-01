import ArithS.Tau.Entangled.Dimcid

/-!
# ArithS.Tau.Entangled.DimcidCimcic — the `dimcid × cimcic` systems: two bits D (one FLIP)

`inst dimcid cimcic = .sys [dim 1, cim 0] 0`: the DIMCID member defects (`found_Di`) — `D`, the FLIP of the
engine's `C`. `inst cimcic dimcid = .sys [cim 1, dim 0] 0`: the CIMCIC member's guard "if I cooperate with the
DIMCID member, it cooperates with me" is SELF-REFUTING (`cimcic_defect_not_found`'s argument): a proof of it would
make the CIMCIC member cooperate with the DIMCID member (the guard is the same code in every opp-frame,
`q_congr_opp_impl`), so by soundness the DIMCID member would cooperate back — but it defects against the CIMCIC
member (its own guard is found in that frame). Never found: `D`.
-/

namespace ArithS.Tau

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1
open LAct
open PD PD.Tau

/-! ### 1. `dimcid × cimcic` -/

noncomputable def SDiCi : Sys2 := ⟨SM.ofSearch (entDimG 1) .D, SM.ofSearch (entCimG 0) .C⟩

theorem found_DiCi_engine : ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
    LenBox TAct k (guardCode (templateCode (.impl (.plays .self (.bot (.sys (sys2 (dim 1 k) (cim 0 k)) 1)) .C)
      (.plays (.bot (.sys (sys2 (dim 1 k) (cim 0 k)) 1)) .self .D)))
      (progCode (sysFrame (dim 1 k) (cim 0 k))) (progCode (sysFrame (dim 1 k) (cim 0 k)))) := by
  obtain ⟨k₀, h⟩ := Sys2.found_Di SDiCi 0 1 (by decide) (by decide) rfl rfl
  refine ⟨k₀, fun k hk ↦ ?_⟩
  obtain ⟨hK, b₁, -⟩ := h k hk
  have := Sys2.box_guard_nat hK 0 0 0 rfl b₁
  rw [show SDiCi = Sys2.mk (SM.ofSearch (entDimG 1) .D) (SM.ofSearch (entCimG 0) .C) from rfl] at this
  rw [Sys2.guardCodeB_sysClose_nat (entDimG 1) (entCimG 0) .D .C k (entDimG 1) rfl rfl, Sys2.code_nat (entDimG 1) (entCimG 0) .D .C] at this
  exact this

/-- `dimcid × cimcic`: D — the FLIP (the engine reads this bit `C`). -/
theorem ent_dimcid_cimcic : bitEventually .dimcid .cimcic .D := by
  obtain ⟨k₀, h⟩ := found_DiCi_engine
  exact ⟨k₀, fun k hk ↦ bit_D_of_dim_then (inst_dimcid_cimcic k) (h k hk)⟩

/-! ### 2. `cimcic × dimcid`: the self-refuting guard -/

noncomputable def SCiDi : Sys2 := ⟨SM.ofSearch (entCimG 1) .C, SM.ofSearch (entDimG 0) .D⟩

/-- The engine frame of the bit, on the system's codes. -/
lemma SCiDi_frame (k : ℕ) : progCode (sysFrame (cim 1 k) (dim 0 k)) = pBot (SCiDi.code 0 k) := by
  rw [show SCiDi = Sys2.mk (SM.ofSearch (entCimG 1) .C) (SM.ofSearch (entDimG 0) .D) from rfl, Sys2.code_nat (entCimG 1) (entDimG 0) .C .D]; rfl

lemma SCiDi_partner (k : ℕ) : progCode (.bot (.sys (sys2 (cim 1 k) (dim 0 k)) 1)) = pBot (SCiDi.code 1 k) := by
  rw [show SCiDi = Sys2.mk (SM.ofSearch (entCimG 1) .C) (SM.ofSearch (entDimG 0) .D) from rfl, Sys2.code_nat (entCimG 1) (entDimG 0) .C .D]; rfl

/-- **The CIMCIC member's guard about the DIMCID member is never found** (for all large `k`). -/
theorem cimcic_guard_dimcid_not_found : ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
    ¬ LenBox TAct k (guardCode (templateCode (.impl (.plays .self (.bot (.sys (sys2 (cim 1 k) (dim 0 k)) 1)) .C)
      (.plays (.bot (.sys (sys2 (cim 1 k) (dim 0 k)) 1)) .self .C)))
      (progCode (sysFrame (cim 1 k) (dim 0 k))) (progCode (sysFrame (cim 1 k) (dim 0 k)))) := by
  obtain ⟨k₀, h⟩ := Sys2.found_Di SCiDi 1 0 (by decide) (by decide) rfl rfl
  refine ⟨k₀, fun k hk hf ↦ ?_⟩
  obtain ⟨hK, -, b₂⟩ := h k hk
  -- the DIMCID member defects against the CIMCIC member
  have hD := Sys2.plays_of_box_nat hK 1 (by decide) 1 0 b₂
  -- the found box, as a box of the instance, hence (same code in every opp-frame) in the frame `(0, 1)`
  have hf' : LenBox TAct k (instB (⌜SCiDi.q 0 0 0⌝ : ℕ) k) := by
    refine Sys2.box_instB_of_guard_nat hK 0 0 0 rfl ?_
    rw [show SCiDi = Sys2.mk (SM.ofSearch (entCimG 1) .C) (SM.ofSearch (entDimG 0) .D) from rfl,
      Sys2.guardCodeB_sysClose_nat (entCimG 1) (entDimG 0) .C .D k (entCimG 1) rfl rfl, Sys2.code_nat (entCimG 1) (entDimG 0) .C .D]
    exact hf
  rw [Sys2.q_congr_opp_impl SCiDi (pa := .self) (pb := .bot (.selfIdx 1)) (pa' := .bot (.selfIdx 1)) (pb' := .self)
    (by simp) (by simp) (by simp) (by simp) rfl 0 0 1] at hf'
  -- so the CIMCIC member cooperates with the DIMCID member
  have hC := Sys2.plays_of_box_nat hK 0 (by decide) 0 1 hf'
  -- by soundness the guard is true: the DIMCID member cooperates back
  have hT := models_sentenceAt_of_lenBox (φ := .impl (.plays .self (.bot (.sys (sys2 (cim 1 k) (dim 0 k)) 1)) .C)
    (.plays (.bot (.sys (sys2 (cim 1 k) (dim 0 k)) 1)) .self .C)) hf
  rw [models_sentenceAt_impl, models_plays_self_closed _ _ _ (by simp) (by simp),
    models_plays_closed_self _ _ _ (by simp) (by simp), SCiDi_frame, SCiDi_partner] at hT
  obtain ⟨N, hN⟩ := hT ⟨4, hC⟩
  exact absurd (EvalGraph.unique' hN hD) (by decide)

/-- `cimcic × dimcid`: D. -/
theorem ent_cimcic_dimcid : bitEventually .cimcic .dimcid .D := by
  obtain ⟨k₀, h⟩ := cimcic_guard_dimcid_not_found
  exact ⟨k₀, fun k hk ↦ bit_D_of_cim_else (inst_cimcic_dimcid k) (h k hk)⟩

end ArithS.Tau
