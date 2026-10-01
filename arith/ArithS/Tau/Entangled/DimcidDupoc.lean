import ArithS.Tau.Entangled.Dimcid

/-!
# ArithS.Tau.Entangled.DimcidDupoc — the `dimcid × dupoc` systems: six bits D (three FLIPS)

`inst dimcid dupoc = .sys [dim 1, dm 0] 0` and `inst dupoc dimcid = .sys [dm 1, dim 0] 0`; the natives are the
same two systems. In `S'` the DIMCID member DEFECTS (its guard is self-fulfilling, `found_Di`), so
`dimcid × dupoc` is `D` — the FLIP of the engine's `C` (`outcome_DIMCID_vs_DupocBot = (C, D)`, `dimcid_vs_closed`
in the base) — and the Dupoc member's probe "the DIMCID member cooperates with itself" is FALSE, hence never
found (soundness): `dupoc × dimcid` is `D`, as in the engine.
-/

namespace ArithS.Tau

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1
open LAct
open PD PD.Tau

/-! ### 1. DIMCID at the head: `dimcid × {dupoc, maxconfidence, minconfidence}` -/

/-- `.sys [dim 1, dm 0]`. -/
noncomputable def SDiD : Sys2 := ⟨SM.ofSearch (entDimG 1) .D, SM.ofSearch (entDmG 0) .C⟩

/-- The DIMCID member finds its guard in the bit's frame, on the engine's codes. -/
theorem found_DiD_engine : ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
    LenBox TAct k (guardCode (templateCode (.impl (.plays .self (.bot (.sys (sys2 (dim 1 k) (dm 0 k)) 1)) .C)
      (.plays (.bot (.sys (sys2 (dim 1 k) (dm 0 k)) 1)) .self .D)))
      (progCode (sysFrame (dim 1 k) (dm 0 k))) (progCode (sysFrame (dim 1 k) (dm 0 k)))) := by
  obtain ⟨k₀, h⟩ := Sys2.found_Di SDiD 0 1 (by decide) (by decide) rfl rfl
  refine ⟨k₀, fun k hk ↦ ?_⟩
  obtain ⟨hK, b₁, -⟩ := h k hk
  have := Sys2.box_guard_nat hK 0 0 0 rfl b₁
  rw [show SDiD = Sys2.mk (SM.ofSearch (entDimG 1) .D) (SM.ofSearch (entDmG 0) .C) from rfl] at this
  rw [Sys2.guardCodeB_sysClose_nat (entDimG 1) (entDmG 0) .D .C k (entDimG 1) rfl rfl, Sys2.code_nat (entDimG 1) (entDmG 0) .D .C] at this
  exact this

/-- `dimcid × dupoc`: D — the FLIP (the engine reads this bit `C`). -/
theorem ent_dimcid_dupoc : bitEventually .dimcid .dupoc .D := by
  obtain ⟨k₀, h⟩ := found_DiD_engine
  exact ⟨k₀, fun k hk ↦ bit_D_of_dim_then (inst_dimcid_dupoc k) (h k hk)⟩

theorem ent_dimcid_maxconfidence : bitEventually .dimcid .maxconfidence .D := by
  obtain ⟨k₀, h⟩ := found_DiD_engine
  exact ⟨k₀, fun k hk ↦ bit_D_of_dim_then (inst_dimcid_maxconfidence k) (h k hk)⟩

theorem ent_dimcid_minconfidence : bitEventually .dimcid .minconfidence .D := by
  obtain ⟨k₀, h⟩ := found_DiD_engine
  exact ⟨k₀, fun k hk ↦ bit_D_of_dim_then (inst_dimcid_minconfidence k) (h k hk)⟩

/-! ### 2. Dupoc at the head: `{dupoc, maxconfidence, minconfidence} × dimcid` -/

/-- `.sys [dm 1, dim 0]`. -/
noncomputable def SDDi : Sys2 := ⟨SM.ofSearch (entDmG 1) .C, SM.ofSearch (entDimG 0) .D⟩

/-- **The Dupoc member's probe is never found**: the DIMCID member defects against itself (its guard is found in
its self-play frame), so "it cooperates with itself" is false in ℕ. -/
theorem dupoc_probe_dimcid_not_found : ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
    ¬ LenBox TAct k (guardCode (templateCode (.plays (.bot (.sys (sys2 (dm 1 k) (dim 0 k)) 1)) (.bot (.sys (sys2 (dm 1 k) (dim 0 k)) 1)) .C))
      (progCode (sysFrame (dm 1 k) (dim 0 k))) (progCode (sysFrame (dm 1 k) (dim 0 k)))) := by
  obtain ⟨k₀, h⟩ := Sys2.found_Di SDDi 1 0 (by decide) (by decide) rfl rfl
  refine ⟨k₀, fun k hk ↦ ?_⟩
  obtain ⟨hK, b₁, -⟩ := h k hk
  have hD := Sys2.plays_of_box_nat hK 1 (by decide) 1 1 b₁
  rw [show SDDi = Sys2.mk (SM.ofSearch (entDmG 1) .C) (SM.ofSearch (entDimG 0) .D) from rfl, Sys2.code_nat (entDmG 1) (entDimG 0) .C .D] at hD
  refine closed_not_found rfl ?_ k
  rw [models_partner_probe]
  exact not_exists_evalGraph_of_ne (a := .C) (b := .D) (by decide) hD

/-- `dupoc × dimcid`: D. -/
theorem ent_dupoc_dimcid : bitEventually .dupoc .dimcid .D := by
  obtain ⟨k₀, h⟩ := dupoc_probe_dimcid_not_found
  exact ⟨k₀, fun k hk ↦ bit_D_of_dm_else (inst_dupoc_dimcid k) (h k hk)⟩

theorem ent_maxconfidence_dimcid : bitEventually .maxconfidence .dimcid .D := by
  obtain ⟨k₀, h⟩ := dupoc_probe_dimcid_not_found
  exact ⟨k₀, fun k hk ↦ bit_D_of_dm_else (inst_maxconfidence_dimcid k) (h k hk)⟩

theorem ent_minconfidence_dimcid : bitEventually .minconfidence .dimcid .D := by
  obtain ⟨k₀, h⟩ := dupoc_probe_dimcid_not_found
  exact ⟨k₀, fun k hk ↦ bit_D_of_dm_else (inst_minconfidence_dimcid k) (h k hk)⟩

end ArithS.Tau
