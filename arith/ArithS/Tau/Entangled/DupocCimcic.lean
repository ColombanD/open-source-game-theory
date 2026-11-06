import ArithS.Tau.Entangled.Dimcid

/-!
# ArithS.Tau.Entangled.DupocCimcic — the `dupoc × cimcic` systems: mutual Löb, six bits C

`inst dupoc cimcic = .sys [dm 1, cim 0] 0` and `inst cimcic dupoc = .sys [cim 1, dm 0] 0` (the natives are the
same two systems). The Dupoc member probes "the CIMCIC member cooperates with itself"; the CIMCIC member's guard
is "if I cooperate with the Dupoc member, it cooperates with me". A box of both makes the Dupoc member cooperate
in every frame (its guard is closed: `q_congr_opp_plays`) and the CIMCIC member cooperate with itself — so the
probe is true and the implication's consequent holds: the engine's `dupoc_cimcic_mutual`
(`Tau/Theorems/TauCIMCIC/Helpers.lean`), on the member slots in `S'`.
-/

namespace ArithS.Tau

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1
open LAct
open PD PD.Tau

namespace Sys2

/-- **The mutual Löb premise of a Dupoc/CIMCIC system**: member `d` is Dupoc probing `c`, member `c` is CIMCIC
probing `d`. -/
theorem loebSound_DCi (S : Sys2) (d c : ℕ) (hd : d ≤ 1) (hc : c ≤ 1)
    (hgd : (S.mem d).g = template13 (entDmG c)) (had : (S.mem d).a = 0)
    (hgc : (S.mem c).g = template13 (entCimG d)) (hac : (S.mem c).a = 0) :
    LoebSound (pQ (S.q d d d ⋏ S.q c c c)) (14 + S.K) 16 := by
  refine loebSound_pQ₂_above _ _ S.K fun V _ _ k hk b₁ b₂ b₃ b₄ ↦ ?_
  have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
  rw [← stdReadingV_eq_stdReading]
  have hcongr : S.q d d d = S.q d d c :=
    q_congr_opp_plays S (pa := .bot (.selfIdx c)) (pb := .bot (.selfIdx c)) (by simp) (by simp) hgd d d c
  -- Dupoc cooperates in the frame `(d, c)`, CIMCIC cooperates with itself
  have hDc : EvalGraph 4 (pBot (S.code d k)) (pBot (S.code c k)) (pBot (S.code d k)) (actCode .C : V) := by
    have := plays_of_box hk d hd d c (by rw [← hcongr]; exact b₁)
    rwa [had, Nat.cast_zero, ← actCode_C_cast] at this
  have hCc : EvalGraph 4 (pBot (S.code c k)) (pBot (S.code c k)) (pBot (S.code c k)) (actCode .C : V) := by
    have := plays_of_box hk c hc c c b₂
    rwa [hac, Nat.cast_zero, ← actCode_C_cast] at this
  have hDcT : EvalGraph 4 (pBot (S.tr.code d k)) (pBot (S.tr.code c k)) (pBot (S.tr.code d k)) (actCode Action.C.swap : V) := by
    have := tr_plays_of_box hk d hd d c (by rw [show Semiformula.lMap swap (S.q d d c) = Semiformula.lMap swap (S.q d d d) by rw [hcongr]]; exact b₃)
    rw [tr_mem S d hd, SM.tr_a, had, Nat.sub_zero, Nat.cast_one, ← actCode_D_cast] at this
    exact this
  have hCcT : EvalGraph 4 (pBot (S.tr.code c k)) (pBot (S.tr.code c k)) (pBot (S.tr.code c k)) (actCode Action.C.swap : V) := by
    have := tr_plays_of_box hk c hc c c b₄
    rw [tr_mem S c hc, SM.tr_a, hac, Nat.sub_zero, Nat.cast_one, ← actCode_D_cast] at this
    exact this
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (eval_q_partner hk (j := d) (j' := c) hc hgd d d).mpr ⟨4, hCc⟩
  · exact (eval_q_impl hk (j := c) (j' := d) hd hgc c c).mpr fun _ ↦ ⟨4, hDc⟩
  · exact (eval_q_partner_swap hk (j := d) (j' := c) hc hgd d d).mpr ⟨4, hCcT⟩
  · exact (eval_q_impl_swap hk (j := c) (j' := d) hd hgc c c).mpr fun _ ↦ ⟨4, hDcT⟩

/-- **Both members find their guards for all large `k`.** -/
theorem found_DCi (S : Sys2) (d c : ℕ) (hd : d ≤ 1) (hc : c ≤ 1)
    (hgd : (S.mem d).g = template13 (entDmG c)) (had : (S.mem d).a = 0)
    (hgc : (S.mem c).g = template13 (entCimG d)) (hac : (S.mem c).a = 0) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k → S.K ≤ k ∧
      LenBox TAct k (instB (⌜S.q d d d⌝ : ℕ) k) ∧ LenBox TAct k (instB (⌜S.q c c c⌝ : ℕ) k) := by
  obtain ⟨k₀, h⟩ := family_found (pQ (S.q d d d ⋏ S.q c c c)) boundedInnerNec_sixteen
    (loebSound_DCi S d c hd hc hgd had hgc hac)
  refine ⟨k₀ + S.K, fun k hk ↦ ?_⟩
  obtain ⟨a, ha', hbox⟩ := h k (by omega)
  obtain ⟨b₁, b₂, -, -⟩ := boxes_pQ₂_nat _ _ S.K k a ha' hbox
  exact ⟨by omega, b₁, b₂⟩

end Sys2

/-! ### 1. Dupoc at the head: `{dupoc, maxconfidence, minconfidence} × cimcic` -/

noncomputable def SDCi : Sys2 := ⟨SM.ofSearch (entDmG 1) .C, SM.ofSearch (entCimG 0) .C⟩

theorem found_DCi_engine : ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
    LenBox TAct k (guardCode (templateCode (.plays (.bot (.sys (sys2 (dm 1 k) (cim 0 k)) 1)) (.bot (.sys (sys2 (dm 1 k) (cim 0 k)) 1)) .C))
      (progCode (sysFrame (dm 1 k) (cim 0 k))) (progCode (sysFrame (dm 1 k) (cim 0 k)))) := by
  obtain ⟨k₀, h⟩ := Sys2.found_DCi SDCi 0 1 (by decide) (by decide) rfl rfl rfl rfl
  refine ⟨k₀, fun k hk ↦ ?_⟩
  obtain ⟨hK, b₁, -⟩ := h k hk
  have := Sys2.box_guard_nat hK 0 0 0 rfl b₁
  rw [show SDCi = Sys2.mk (SM.ofSearch (entDmG 1) .C) (SM.ofSearch (entCimG 0) .C) from rfl] at this
  rw [Sys2.guardCodeB_sysClose_nat (entDmG 1) (entCimG 0) .C .C k (entDmG 1) rfl rfl, Sys2.code_nat (entDmG 1) (entCimG 0) .C .C] at this
  exact this

/-- `dupoc × cimcic`: C. -/
theorem ent_dupoc_cimcic : bitEventually .dupoc .cimcic .C := by
  obtain ⟨k₀, h⟩ := found_DCi_engine
  exact ⟨k₀, fun k hk ↦ bit_C_of_dm_then (inst_dupoc_cimcic k) (h k hk)⟩

theorem ent_maxconfidence_cimcic : bitEventually .maxconfidence .cimcic .C := by
  obtain ⟨k₀, h⟩ := found_DCi_engine
  exact ⟨k₀, fun k hk ↦ bit_C_of_dm_then (inst_maxconfidence_cimcic k) (h k hk)⟩

theorem ent_minconfidence_cimcic : bitEventually .minconfidence .cimcic .C := by
  obtain ⟨k₀, h⟩ := found_DCi_engine
  exact ⟨k₀, fun k hk ↦ bit_C_of_dm_then (inst_minconfidence_cimcic k) (h k hk)⟩

/-! ### 2. CIMCIC at the head: `cimcic × {dupoc, maxconfidence, minconfidence}` -/

noncomputable def SCiD : Sys2 := ⟨SM.ofSearch (entCimG 1) .C, SM.ofSearch (entDmG 0) .C⟩

theorem found_CiD_engine : ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
    LenBox TAct k (guardCode (templateCode (.impl (.plays .self (.bot (.sys (sys2 (cim 1 k) (dm 0 k)) 1)) .C)
      (.plays (.bot (.sys (sys2 (cim 1 k) (dm 0 k)) 1)) .self .C)))
      (progCode (sysFrame (cim 1 k) (dm 0 k))) (progCode (sysFrame (cim 1 k) (dm 0 k)))) := by
  obtain ⟨k₀, h⟩ := Sys2.found_DCi SCiD 1 0 (by decide) (by decide) rfl rfl rfl rfl
  refine ⟨k₀, fun k hk ↦ ?_⟩
  obtain ⟨hK, -, b₂⟩ := h k hk
  have := Sys2.box_guard_nat hK 0 0 0 rfl b₂
  rw [show SCiD = Sys2.mk (SM.ofSearch (entCimG 1) .C) (SM.ofSearch (entDmG 0) .C) from rfl] at this
  rw [Sys2.guardCodeB_sysClose_nat (entCimG 1) (entDmG 0) .C .C k (entCimG 1) rfl rfl, Sys2.code_nat (entCimG 1) (entDmG 0) .C .C] at this
  exact this

/-- `cimcic × dupoc`: C. -/
theorem ent_cimcic_dupoc : bitEventually .cimcic .dupoc .C := by
  obtain ⟨k₀, h⟩ := found_CiD_engine
  exact ⟨k₀, fun k hk ↦ bit_C_of_cim_then (inst_cimcic_dupoc k) (h k hk)⟩

theorem ent_cimcic_maxconfidence : bitEventually .cimcic .maxconfidence .C := by
  obtain ⟨k₀, h⟩ := found_CiD_engine
  exact ⟨k₀, fun k hk ↦ bit_C_of_cim_then (inst_cimcic_maxconfidence k) (h k hk)⟩

theorem ent_cimcic_minconfidence : bitEventually .cimcic .minconfidence .C := by
  obtain ⟨k₀, h⟩ := found_CiD_engine
  exact ⟨k₀, fun k hk ↦ bit_C_of_cim_then (inst_cimcic_minconfidence k) (h k hk)⟩

end ArithS.Tau
