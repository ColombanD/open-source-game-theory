import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Bots.DupocBot
import PrisonersDilemma.Bots.MirrorBot
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Base.Asymptotics
import PrisonersDilemma.Theorems.DupocBot.Helpers
import PrisonersDilemma.Outcome

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems
/-- DupocBot vs MirrorBot cooperates, for `k` large enough. Direct application
    of PBLT with `φ k = .plays MirrorBot (DupocBot k) .C`, `f = id`, `k₁ = 0`.
    Mirrors `outcome_DupocBot_vs_DupocBot`; the play witness lives on the MirrorBot leg
    and is lifted to the DupocBot leg via the `.sim` swap. -/
@[outcome]
theorem outcome_DupocBot_vs_MirrorBot :
    OutcomeSpec .eventual 3
      DupocBot (fun _ => MirrorBot) (some (.C, .C)) := by
  let φ : Nat → Formula := fun k => .plays MirrorBot (DupocBot k) .C
  have hLoeb :
      ∀ k, k > 0 →
        Pf (20 * Nat.log2 k + 150) (.impl (.box k (φ k)) (φ k)) := by
    intro k _
    exact dupoc_mirror_loeb_premise k
  have hφsz : ∀ k, (φ k).size ≤ 100 * Nat.log2 k + 1000 := by
    intro k
    show (Formula.plays MirrorBot (DupocBot k) .C).size ≤ _
    simp only [numCost, Formula.size, Prog.size, DupocBot, MirrorBot]
    omega
  have hpm : ∀ k, 20 * Nat.log2 k + 150 ≤ 100 * Nat.log2 k + 1000 := fun k => by omega
  obtain ⟨k₂, hk₂⟩ := pblt_engine_id φ (fun k => 20 * Nat.log2 k + 150) 0 hφsz hpm hLoeb
  refine ⟨k₂, fun k hk fuel => outcome_at_of_ex ?_ ?_ fuel⟩
  -- The old existential-fuel argument, verbatim: some fuel determines the outcome…
  · obtain ⟨m, hm⟩ := hk₂ k hk
    have hInterp : (φ k).interp := Pf_sound m (φ k) hm
    obtain ⟨n, hMirror⟩ := hInterp
    have hPS : proofSearch k (.plays MirrorBot (DupocBot k) .C) = true :=
      proofSearch_k_of_play_MirrorBot_dupoc k n hMirror
    refine ⟨3, ?_⟩
    have hA : play 3 (DupocBot k) MirrorBot = some .C := by
      simpa using DupocBot_plays_C_against_MirrorBot k 1 hPS
    have hB : play 3 MirrorBot (DupocBot k) = some .C := by
      simpa using MirrorBot_plays_C_against_DupocBot k 0 hPS
    exact outcome_of_plays _ _ _ _ _ hA hB
  -- …and the match is determined at fuel 3 whatever the oracle says, so
  -- determinism (`play_unique`) pins the value there and monotonicity does the rest.
  · exact outcome_total_of_plays (play_search_const_total _ _ _ _ _ 1) (play_sim_opp_self_total (play_search_const_total _ _ _ _ _ 0))
end PD.Theorems
