import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Axioms
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Bots.LlmGenerations.PrudentBot
import PrisonersDilemma.Theorems.LlmGenerations.PrudentBot
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.SizeLemmas

open PD
open PD.Axioms
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

/-- Prudence atom for PrudentBot self-play: PrudentBot plays D vs `.bot DefectBot`. -/
theorem prudence_self_prudent :
    ∃ k₀, ∀ k, k₀ ≤ k →
      Provable k (Formula.plays (PrudentBot k) (.bot DefectBot) Action.D) := by
  refine ⟨atom_cost 2, fun k hk => ?_⟩
  have hPlay : play 2 (PrudentBot k) (.bot DefectBot) = some .D := by
    simpa using PrudentBot_plays_D_vs_bot_DB k 0
  exact Provable.atom (atom_monotone (atom_cost 2) k _ hk
    (atom_complete (PrudentBot k) (.bot DefectBot) Action.D 2 hPlay))

/-- The closed Löb premise for PrudentBot self-play, directly from
    `searchThenSearch_t` (self-play: opponent = me = PrudentBot k). -/
theorem prudent_self_loeb_premise :
    ∃ K₀ : Nat, ∀ k : Nat, k ≥ K₀ →
      Provable k (.impl (.box k (Formula.plays (PrudentBot k) (PrudentBot k) Action.C))
                        (Formula.plays (PrudentBot k) (PrudentBot k) Action.C)) := by
  obtain ⟨kPrud, hkPrud⟩ := prudence_self_prudent
  obtain ⟨Ksz, hKsz⟩ := linear_log2_add_le 20 200
  refine ⟨max kPrud Ksz, fun k hk => ?_⟩
  have hkP : kPrud ≤ k := le_trans (le_max_left _ _) hk
  have hkS : Ksz ≤ k := le_trans (le_max_right _ _) hk
  have hprud : Provable k (Formula.plays (PrudentBot k) (.bot DefectBot) Action.D) := hkPrud k hkP
  refine Provable.searchThenSearch_t k k
    (Formula.plays .opp .self Action.C)
    (Formula.plays .opp (.bot DefectBot) Action.D)
    Action.C Action.D (.const Action.D) (PrudentBot k) (PrudentBot k) rfl hprud ?_
  simp only [Formula.subst, Prog.subst, Formula.size, Prog.size, PrudentBot, DefectBot]
  have := hKsz k hkS
  omega

/-- **PrudentBot vs PrudentBot → (C, C)** for all large enough `k`. -/
theorem llm_outcome_PrudentBot_vs_PrudentBot :
    ∃ k₂, ∀ k, k₂ < k →
      ∃ fuel, outcome fuel (PrudentBot k) (PrudentBot k) = some (.C, .C) := by
  let φ : Nat → Formula := fun k => Formula.plays (PrudentBot k) (PrudentBot k) Action.C
  have hMono : ∀ a b : Nat, a ≤ b → id a ≤ id b := fun _ _ h => h
  have hLog : ∃ c kHat, c > 0 ∧ ∀ k, k > kHat → id k > c * Nat.log2 k := by
    refine ⟨1, 0, Nat.zero_lt_one, ?_⟩
    intro k hk
    have hlog : Nat.log2 k < k := by
      rw [Nat.log2_lt (Nat.pos_iff_ne_zero.mp hk)]
      exact Nat.lt_two_pow_self
    simpa using hlog
  obtain ⟨kPrud, hkPrud⟩ := prudence_self_prudent
  obtain ⟨K₀, hK₀⟩ := prudent_self_loeb_premise
  have hLoeb : ∀ k, k > K₀ → ∃ m, Provable m (.impl (.box (id k) (φ k)) (φ k)) :=
    fun k hk => ⟨k, hK₀ k (Nat.le_of_lt hk)⟩
  obtain ⟨k₂, hk₂⟩ := PBLT φ id K₀ hMono hLog hLoeb
  refine ⟨max k₂ kPrud, fun k hk => ?_⟩
  have hk2 : k > k₂ := lt_of_le_of_lt (le_max_left _ _) hk
  have hkP : kPrud ≤ k := le_of_lt (lt_of_le_of_lt (le_max_right _ _) hk)
  obtain ⟨m, hm⟩ := hk₂ k hk2
  obtain ⟨n, hplay⟩ := Provable_sound m (φ k) hm
  have hpsOuter : proofSearch k (Formula.plays (PrudentBot k) (PrudentBot k) Action.C) = true :=
    prudent_outer_true_of_play_C k n (PrudentBot k) hplay
  have hprud : proofSearch k (Formula.plays (PrudentBot k) (.bot DefectBot) Action.D) = true :=
    (proofSearch_spec _ _).2 (hkPrud k hkP)
  refine ⟨3, ?_⟩
  have hA : play 3 (PrudentBot k) (PrudentBot k) = some .C := by
    simpa using prudent_eval_both_true k 0 (PrudentBot k) hpsOuter hprud
  exact outcome_of_plays _ _ _ _ _ hA hA

end PD.Theorems
