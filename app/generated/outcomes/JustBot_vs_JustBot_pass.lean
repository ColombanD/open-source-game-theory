import PrisonersDilemma.Bots.LlmGenerations.JustBot
import PrisonersDilemma.Bots.DupocBot
import PrisonersDilemma.Axioms
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.SizeLemmas
import PrisonersDilemma.Theorems.Helpers
import PrisonersDilemma.Theorems.LlmGenerations.JustBot

open PD
open PD.Axioms
open PD.BaseTheorems
open PD.Bots

namespace PD.Theorems

/-- Inversion: a `.bot DupocBot` self-play cooperation forces its guard to fire. -/
theorem ps_k_of_play_botDupoc_self (k N : Nat)
    (h : play N (.bot (DupocBot k)) (.bot (DupocBot k)) = some .C) :
    proofSearch k (.plays (.bot (DupocBot k)) (.bot (DupocBot k)) .C) = true := by
  cases hps : proofSearch k (.plays (.bot (DupocBot k)) (.bot (DupocBot k)) .C) with
  | true => rfl
  | false =>
    exfalso
    have hD : play (N + 3) (.bot (DupocBot k)) (.bot (DupocBot k)) = some .D := by
      show eval (N + 3) (.bot (DupocBot k)) (.bot (DupocBot k)) (.bot (DupocBot k)) = some .D
      unfold DupocBot at hps ⊢
      simp [eval, Prog.subst, Formula.subst, hps]
    have hC : play (N + 3) (.bot (DupocBot k)) (.bot (DupocBot k)) = some .C := by
      unfold play at h ⊢
      exact eval_mono_le h (N + 3) (by omega)
    rw [hC] at hD
    cases hD

/-- Löb premise for `.bot DupocBot` self-play, via `botSearchStep`. -/
theorem botdupoc_loeb_premise :
    ∃ K₀ : Nat, ∀ k : Nat, k ≥ K₀ →
      Provable k (.impl (.box k (.plays (.bot (DupocBot k)) (.bot (DupocBot k)) .C))
                        (.plays (.bot (DupocBot k)) (.bot (DupocBot k)) .C)) := by
  obtain ⟨K₀, hK₀⟩ := linear_log2_add_le 5 37
  refine ⟨K₀, fun k hk => ?_⟩
  apply Provable.struct
  refine ⟨.botSearchStep k (.plays .opp .self .C) .C .D (.bot (DupocBot k)) (.bot (DupocBot k)) rfl, ?_⟩
  simp only [Derivation.size, Formula.size, Prog.size, DupocBot]
  have := hK₀ k hk
  omega

/-- For large `k`, `.bot DupocBot` self-play cooperates (its guard provably fires). -/
theorem botDupoc_self_coop :
    ∃ k₂, ∀ k, k₂ < k →
      proofSearch k (.plays (.bot (DupocBot k)) (.bot (DupocBot k)) .C) = true := by
  let φ : Nat → Formula := fun k => .plays (.bot (DupocBot k)) (.bot (DupocBot k)) .C
  have hMono : ∀ a b : Nat, a ≤ b → id a ≤ id b := fun _ _ h => h
  have hLog : ∃ c kHat, c > 0 ∧ ∀ k, k > kHat → id k > c * Nat.log2 k := by
    refine ⟨1, 0, Nat.zero_lt_one, ?_⟩
    intro k hk
    have hlog : Nat.log2 k < k := by
      rw [Nat.log2_lt (Nat.pos_iff_ne_zero.mp hk)]
      exact Nat.lt_two_pow_self
    simpa using hlog
  obtain ⟨K₀, hK₀⟩ := botdupoc_loeb_premise
  have hLoeb : ∀ k, k > K₀ → ∃ m, Provable m (.impl (.box (id k) (φ k)) (φ k)) := by
    intro k hk
    exact ⟨k, hK₀ k (Nat.le_of_lt hk)⟩
  obtain ⟨k₂, hk₂⟩ := PBLT φ id K₀ hMono hLog hLoeb
  refine ⟨k₂, fun k hk => ?_⟩
  obtain ⟨m, hm⟩ := hk₂ k hk
  have hInterp : (φ k).interp := Provable_sound m (φ k) hm
  obtain ⟨n, hn⟩ := hInterp
  exact ps_k_of_play_botDupoc_self k n hn

/-- JustBot vs JustBot: mutual cooperation for sufficiently large `k`. -/
theorem llm_outcome_JustBot_vs_JustBot :
    ∃ k₂, ∀ k, k₂ < k →
      ∃ fuel, outcome fuel (JustBot k) (JustBot k) = some (.C, .C) := by
  obtain ⟨k₂, hk₂⟩ := botDupoc_self_coop
  refine ⟨max k₂ (atom_cost 2), fun k hk => ?_⟩
  have hk2 : k₂ < k := lt_of_le_of_lt (le_max_left _ _) hk
  have hac2 : atom_cost 2 ≤ k := le_of_lt (lt_of_le_of_lt (le_max_right _ _) hk)
  have hdd : proofSearch k (.plays (.bot (DupocBot k)) (.bot (DupocBot k)) .C) = true := hk₂ k hk2
  have hJd : ∀ f, play (f + 2) (JustBot k) (.bot (DupocBot k)) = some .C := by
    intro f
    refine JustBot_eval_step k f (.bot (DupocBot k)) .C ?_
    simpa using hdd
  have hd' : proofSearch k (.plays (JustBot k) (.bot (DupocBot k)) .C) = true := by
    refine proofSearch_monotone (atom_cost 2) k _ hac2 ?_
    exact (proofSearch_spec _ _).2 (Provable.atom
      (atom_complete (JustBot k) (.bot (DupocBot k)) .C 2 (by simpa using hJd 0)))
  have hJJ : ∀ f, play (f + 2) (JustBot k) (JustBot k) = some .C := by
    intro f
    refine JustBot_eval_step k f (JustBot k) .C ?_
    simpa using hd'
  exact ⟨2, outcome_of_plays _ _ _ _ _ (by simpa using hJJ 0) (by simpa using hJJ 0)⟩

end PD.Theorems
