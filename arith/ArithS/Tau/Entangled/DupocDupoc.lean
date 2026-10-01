import ArithS.Tau.Entangled.Dimcid

/-!
# ArithS.Tau.Entangled.DupocDupoc — the symmetric Dupoc-spec system `cfdSys`: mutual Löb, six bits C

The natives `maxconfidence`/`minconfidence` carry Dupoc's spec, so every pair among `{dupoc, maxconfidence,
minconfidence}` compiles to the SAME system `.sys [dm 1, dm 0] 0` (`Base.lean`, `inst_dupoc_maxconfidence`, …;
the engine's `cfdSys`, `Tau/Theorems/TauMaxConfidence/Helpers.lean`). Member `0` probes "the bot-wrapped member
`1` cooperates with itself", member `1` the converse; a box of BOTH probes makes both members cooperate, which
makes both probes true — the mutual Löb family `pQ (q₀ ⋏ q₁)` (`loebSound_DD`), found for all large `k`
(`family_found`), so member `0` finds its probe in the bit's frame and cooperates.
-/

namespace ArithS.Tau

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1
open LAct
open PD PD.Tau

/-- The symmetric system: member `0` is `dm 1`, member `1` is `dm 0`. -/
noncomputable def SDD : Sys2 := ⟨SM.ofSearch (entDmG 1) .C, SM.ofSearch (entDmG 0) .C⟩

lemma SDD_g0 : (SDD.mem 0).g = template13 (entDmG 1) := rfl
lemma SDD_g1 : (SDD.mem 1).g = template13 (entDmG 0) := rfl

/-- **The mutual Löb premise**: boxes of both probes (and of their transpositions) make both members (and both
transposed members) play their then-actions, which is what the four probes say. -/
theorem loebSound_DD : LoebSound (pQ (SDD.q 0 0 0 ⋏ SDD.q 1 1 1)) (14 + SDD.K) 16 := by
  refine loebSound_pQ₂_above _ _ SDD.K fun V _ _ k hk b₁ b₂ b₃ b₄ ↦ ?_
  have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
  rw [← stdReadingV_eq_stdReading]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (Sys2.eval_q_partner hk (j := 0) (j' := 1) (by decide) SDD_g0 0 0).mpr
      ⟨4, Sys2.plays_of_box hk 1 (by decide) 1 1 b₂⟩
  · exact (Sys2.eval_q_partner hk (j := 1) (j' := 0) (by decide) SDD_g1 1 1).mpr
      ⟨4, Sys2.plays_of_box hk 0 (by decide) 0 0 b₁⟩
  · exact (Sys2.eval_q_partner_swap hk (j := 0) (j' := 1) (by decide) SDD_g0 0 0).mpr
      ⟨4, Sys2.tr_plays_of_box hk 1 (by decide) 1 1 b₄⟩
  · exact (Sys2.eval_q_partner_swap hk (j := 1) (j' := 0) (by decide) SDD_g1 1 1).mpr
      ⟨4, Sys2.tr_plays_of_box hk 0 (by decide) 0 0 b₃⟩

/-- **Member `0` finds its probe in the bit's frame for all large `k`.** -/
theorem found_DD : ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
    LenBox TAct k (guardCodeB (sysCloseTemplate (SDD.D k) (⌜template13 (entDmG 1)⌝ : ℕ))
      (pBot (SDD.code 0 k)) (pBot (SDD.code 0 k)) k) := by
  obtain ⟨k₀, h⟩ := family_found (pQ (SDD.q 0 0 0 ⋏ SDD.q 1 1 1)) boundedInnerNec_sixteen loebSound_DD
  refine ⟨k₀ + SDD.K, fun k hk ↦ ?_⟩
  obtain ⟨a, ha, hbox⟩ := h k (by omega)
  obtain ⟨b₁, -, -, -⟩ := boxes_pQ₂_nat _ _ SDD.K k a ha hbox
  have e := Sys2.guard_eq_instB (V := ℕ) (S := SDD) (k := k) (le_def.mpr (Or.inr (by rw [natCast_nat]; omega))) 0 0 0
  rw [natCast_nat] at e
  rw [show (⌜template13 (entDmG 1)⌝ : ℕ) = ⌜(SDD.mem 0).g⌝ from rfl, e]
  exact b₁

/-- The found box, in the engine's frame and on the engine's closed guard. -/
theorem found_DD_engine : ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
    LenBox TAct k (guardCode (templateCode (.plays (.bot (.sys (sys2 (dm 1 k) (dm 0 k)) 1)) (.bot (.sys (sys2 (dm 1 k) (dm 0 k)) 1)) .C))
      (progCode (sysFrame (dm 1 k) (dm 0 k))) (progCode (sysFrame (dm 1 k) (dm 0 k)))) := by
  obtain ⟨k₀, h⟩ := found_DD
  refine ⟨k₀, fun k hk ↦ ?_⟩
  have := h k hk
  rw [show SDD = Sys2.mk (SM.ofSearch (entDmG 1) .C) (SM.ofSearch (entDmG 0) .C) from rfl] at this
  rw [Sys2.guardCodeB_sysClose_nat (entDmG 1) (entDmG 0) .C .C k (entDmG 1) rfl rfl, Sys2.code_nat] at this
  exact this

/-- `dupoc × maxconfidence`: C. -/
theorem ent_dupoc_maxconfidence : bitEventually .dupoc .maxconfidence .C := by
  obtain ⟨k₀, h⟩ := found_DD_engine
  exact ⟨k₀, fun k hk ↦ bit_C_of_dm_then (inst_dupoc_maxconfidence k) (h k hk)⟩

/-- `maxconfidence × dupoc`: C (the engine's `maxconfidence_dupoc_plays_C`). -/
theorem ent_maxconfidence_dupoc : bitEventually .maxconfidence .dupoc .C := by
  obtain ⟨k₀, h⟩ := found_DD_engine
  exact ⟨k₀, fun k hk ↦ bit_C_of_dm_then (inst_maxconfidence_dupoc k) (h k hk)⟩

theorem ent_dupoc_minconfidence : bitEventually .dupoc .minconfidence .C := by
  obtain ⟨k₀, h⟩ := found_DD_engine
  exact ⟨k₀, fun k hk ↦ bit_C_of_dm_then (inst_dupoc_minconfidence k) (h k hk)⟩

theorem ent_minconfidence_dupoc : bitEventually .minconfidence .dupoc .C := by
  obtain ⟨k₀, h⟩ := found_DD_engine
  exact ⟨k₀, fun k hk ↦ bit_C_of_dm_then (inst_minconfidence_dupoc k) (h k hk)⟩

theorem ent_maxconfidence_minconfidence : bitEventually .maxconfidence .minconfidence .C := by
  obtain ⟨k₀, h⟩ := found_DD_engine
  exact ⟨k₀, fun k hk ↦ bit_C_of_dm_then (inst_maxconfidence_minconfidence k) (h k hk)⟩

theorem ent_minconfidence_maxconfidence : bitEventually .minconfidence .maxconfidence .C := by
  obtain ⟨k₀, h⟩ := found_DD_engine
  exact ⟨k₀, fun k hk ↦ bit_C_of_dm_then (inst_minconfidence_maxconfidence k) (h k hk)⟩

end ArithS.Tau
