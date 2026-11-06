import ArithS.Tau.Entangled.Dimcid

/-!
# ArithS.Tau.Entangled.DimcidCupod — the `dimcid × cupod` systems: two bits D

`inst dimcid cupod = .sys [dim 1, cm 0] 0`: the DIMCID member defects (`found_Di`). `inst cupod dimcid =
.sys [cm 1, dim 0] 0`: the Cupod member's punish-probe "the DIMCID member defects against itself" is TRUE and
PROVABLE within the budget — a box consequence of the DIMCID member's Löb family (`found_of_box_conseq`, as the
base `guardian_finds_DIMCID`), so the Cupod member punishes: `D`.
-/

namespace ArithS.Tau

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1
open LAct
open PD PD.Tau

/-! ### 1. `dimcid × cupod` -/

noncomputable def SDiC : Sys2 := ⟨SM.ofSearch (entDimG 1) .D, SM.ofSearch (entCmG 0) .D⟩

theorem found_DiC_engine : ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
    LenBox TAct k (guardCode (templateCode (.impl (.plays .self (.bot (.sys (sys2 (dim 1 k) (cm 0 k)) 1)) .C)
      (.plays (.bot (.sys (sys2 (dim 1 k) (cm 0 k)) 1)) .self .D)))
      (progCode (sysFrame (dim 1 k) (cm 0 k))) (progCode (sysFrame (dim 1 k) (cm 0 k)))) := by
  obtain ⟨k₀, h⟩ := Sys2.found_Di SDiC 0 1 (by decide) (by decide) rfl rfl
  refine ⟨k₀, fun k hk ↦ ?_⟩
  obtain ⟨hK, b₁, -⟩ := h k hk
  have := Sys2.box_guard_nat hK 0 0 0 rfl b₁
  rw [show SDiC = Sys2.mk (SM.ofSearch (entDimG 1) .D) (SM.ofSearch (entCmG 0) .D) from rfl] at this
  rw [Sys2.guardCodeB_sysClose_nat (entDimG 1) (entCmG 0) .D .D k (entDimG 1) rfl rfl, Sys2.code_nat (entDimG 1) (entCmG 0) .D .D] at this
  exact this

/-- `dimcid × cupod`: D. -/
theorem ent_dimcid_cupod : bitEventually .dimcid .cupod .D := by
  obtain ⟨k₀, h⟩ := found_DiC_engine
  exact ⟨k₀, fun k hk ↦ bit_D_of_dim_then (inst_dimcid_cupod k) (h k hk)⟩

/-! ### 2. `cupod × dimcid`: the punish-probe is a box consequence of DIMCID's family -/

noncomputable def SCDi : Sys2 := ⟨SM.ofSearch (entCmG 1) .D, SM.ofSearch (entDimG 0) .D⟩

/-- A box of the DIMCID member's family makes it defect against itself, in both systems. -/
theorem boxConseq_CDi : BoxConseq (pQ (SCDi.q 1 1 1 ⋏ SCDi.q 1 1 0)) (SCDi.q 0 0 0) (14 + SCDi.K) 16 := by
  refine boxConseq_pQ₂_above _ _ _ SCDi.K fun V _ _ k hk b₁ b₂ b₃ b₄ ↦ ?_
  have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
  rw [← stdReadingV_eq_stdReading]
  refine ⟨?_, ?_⟩
  · exact (Sys2.eval_q_partner hk (j := 0) (j' := 1) (by decide) rfl 0 0).mpr
      ⟨4, Sys2.plays_of_box hk 1 (by decide) 1 1 b₁⟩
  · exact (Sys2.eval_q_partner_swap hk (j := 0) (j' := 1) (by decide) rfl 0 0).mpr
      ⟨4, Sys2.tr_plays_of_box hk 1 (by decide) 1 1 b₃⟩

/-- **The Cupod member finds its punish-probe for all large `k`.** -/
theorem found_CDi : ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k → LenBox TAct k (instB (⌜SCDi.q 0 0 0⌝ : ℕ) k) :=
  found_of_box_conseq _ boundedInnerNec_sixteen (Sys2.loebSound_Di SCDi 1 0 (by decide) (by decide) rfl rfl) _
    boxConseq_CDi (fun k ↦ instB (⌜SCDi.q 0 0 0⌝ : ℕ) k) (fun _ ↦ rfl)

theorem found_CDi_engine : ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
    LenBox TAct k (guardCode (templateCode (.plays (.bot (.sys (sys2 (cm 1 k) (dim 0 k)) 1)) (.bot (.sys (sys2 (cm 1 k) (dim 0 k)) 1)) .D))
      (progCode (sysFrame (cm 1 k) (dim 0 k))) (progCode (sysFrame (cm 1 k) (dim 0 k)))) := by
  obtain ⟨k₀, h⟩ := found_CDi
  refine ⟨k₀ + SCDi.K, fun k hk ↦ ?_⟩
  have := Sys2.box_guard_nat (S := SCDi) (by omega) 0 0 0 rfl (h k (by omega))
  rw [show SCDi = Sys2.mk (SM.ofSearch (entCmG 1) .D) (SM.ofSearch (entDimG 0) .D) from rfl] at this
  rw [Sys2.guardCodeB_sysClose_nat (entCmG 1) (entDimG 0) .D .D k (entCmG 1) rfl rfl, Sys2.code_nat (entCmG 1) (entDimG 0) .D .D] at this
  exact this

/-- `cupod × dimcid`: D. -/
theorem ent_cupod_dimcid : bitEventually .cupod .dimcid .D := by
  obtain ⟨k₀, h⟩ := found_CDi_engine
  exact ⟨k₀, fun k hk ↦ bit_D_of_cm_then (inst_cupod_dimcid k) (h k hk)⟩

end ArithS.Tau
