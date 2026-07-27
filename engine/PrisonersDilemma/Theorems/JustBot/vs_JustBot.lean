import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Bots.DupocBot
import PrisonersDilemma.Bots.LlmGenerations.JustBot
import PrisonersDilemma.Theorems.DupocBot.Helpers
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Base.Asymptotics
import PrisonersDilemma.Theorems.JustBot.Helpers

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

-- JustBot --

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
theorem botdupoc_loeb_premise (k : Nat) :
    Pf (20 * Nat.log2 k + 150)
      (.impl (.box k (.plays (.bot (DupocBot k)) (.bot (DupocBot k)) .C))
             (.plays (.bot (DupocBot k)) (.bot (DupocBot k)) .C)) := by
  -- transcript-tight: a single `botSearchStep` leaf, O(log k) — unconditionally.
  refine Pf.botSearchStep k (.plays .opp .self .C) .C .D (.bot (DupocBot k)) (.bot (DupocBot k)) rfl ?_
  simp only [Formula.subst, Prog.subst, numCost, Formula.size, Prog.size, DupocBot]
  omega

/-- For large `k`, `.bot DupocBot` self-play cooperates (its guard provably fires). -/
theorem botDupoc_self_coop :
    ∃ k₂, ∀ k, k₂ < k →
      proofSearch k (.plays (.bot (DupocBot k)) (.bot (DupocBot k)) .C) = true := by
  let φ : Nat → Formula := fun k => .plays (.bot (DupocBot k)) (.bot (DupocBot k)) .C
  have hLoeb : ∀ k, k > 0 →
      Pf (20 * Nat.log2 k + 150) (.impl (.box k (φ k)) (φ k)) := by
    intro k _
    exact botdupoc_loeb_premise k
  have hφsz : ∀ k, (φ k).size ≤ 100 * Nat.log2 k + 1000 := by
    intro k
    show (Formula.plays (.bot (DupocBot k)) (.bot (DupocBot k)) .C).size ≤ _
    simp only [numCost, Formula.size, Prog.size, DupocBot]
    omega
  have hpm : ∀ k, 20 * Nat.log2 k + 150 ≤ 100 * Nat.log2 k + 1000 := fun k => by omega
  obtain ⟨k₂, hk₂⟩ := pblt_engine_id φ (fun k => 20 * Nat.log2 k + 150) 0 hφsz hpm hLoeb
  refine ⟨k₂, fun k hk => ?_⟩
  obtain ⟨m, hm⟩ := hk₂ k hk
  have hInterp : (φ k).interp := Pf_sound m (φ k) hm
  obtain ⟨n, hn⟩ := hInterp
  exact ps_k_of_play_botDupoc_self k n hn

/-- JustBot vs JustBot: mutual cooperation for sufficiently large `k`. -/
theorem outcome_JustBot_vs_JustBot :
    ∃ k₂, ∀ k, k₂ < k →
      ∃ fuel, outcome fuel (JustBot k) (JustBot k) = some (.C, .C) := by
  obtain ⟨k₂, hk₂⟩ := botDupoc_self_coop
  obtain ⟨KL, hKL⟩ := linear_log2_add_le 1 3
  refine ⟨max k₂ KL, fun k hk => ?_⟩
  have hk2 : k₂ < k := lt_of_le_of_lt (le_max_left _ _) hk
  have hKLk : Nat.log2 k + 3 ≤ k := by
    have := hKL k (le_of_lt (lt_of_le_of_lt (le_max_right _ _) hk))
    omega
  have hdd : proofSearch k (.plays (.bot (DupocBot k)) (.bot (DupocBot k)) .C) = true := hk₂ k hk2
  have hd' : proofSearch k (.plays (JustBot k) (.bot (DupocBot k)) .C) = true := by
    -- hand certificate: JustBot's own search FIRED (hdd) — search_t ∘ const, log2 k + 3 chars
    refine (proofSearch_spec _ _).2 (Pf.atom
      (⟨PlaysProof.search_t ((proofSearch_spec _ _).1 hdd) PlaysProof.const, ?_⟩ :
        AtomProvable k (.plays (JustBot k) (.bot (DupocBot k)) .C)))
    show c_leaf + c_guard k + c_node ≤ k
    simp only [numCost, c_leaf, c_guard, c_node]
    omega
  have hJJ : ∀ f, play (f + 2) (JustBot k) (JustBot k) = some .C := by
    intro f
    refine JustBot_eval_step k f (JustBot k) .C ?_
    simpa using hd'
  exact ⟨2, outcome_of_plays _ _ _ _ _ (by simpa using hJJ 0) (by simpa using hJJ 0)⟩
end PD.Theorems
