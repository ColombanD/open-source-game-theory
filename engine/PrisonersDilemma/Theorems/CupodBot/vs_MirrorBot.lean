import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Bots.CupodBot
import PrisonersDilemma.Bots.MirrorBot
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Base.Asymptotics
import PrisonersDilemma.Theorems.CupodBot.Helpers

open PD
open PD.Bots
open PD.BaseTheorems
namespace PD.Theorems
/-- CupodBot vs MirrorBot defects, for `k` large enough. Direct application of
    PBLT with `φ k = .plays MirrorBot (CupodBot k) .D`, `f = id`, `k₁ = 0`.
    Mirrors `outcome_CupodBot_vs_CupodBot`; the play witness lives on the MirrorBot
    leg and is lifted to the CupodBot leg via the `.sim` swap. -/
theorem outcome_CupodBot_vs_MirrorBot :
    ∃ k₂, ∀ k, k₂ < k →
      ∃ fuel, outcome fuel (CupodBot k) MirrorBot = some (.D, .D) := by
  let φ : Nat → Formula := fun k => .plays MirrorBot (CupodBot k) .D
  have hLoeb :
      ∀ k, k > 0 →
        Pf (20 * Nat.log2 k + 150) (.impl (.box k (φ k)) (φ k)) := by
    intro k _
    exact cupod_mirror_loeb_premise k
  have hφsz : ∀ k, (φ k).size ≤ 100 * Nat.log2 k + 1000 := by
    intro k
    show (Formula.plays MirrorBot (CupodBot k) .D).size ≤ _
    simp only [numCost, Formula.size, Prog.size, CupodBot, MirrorBot]
    omega
  have hpm : ∀ k, 20 * Nat.log2 k + 150 ≤ 100 * Nat.log2 k + 1000 := fun k => by omega
  obtain ⟨k₂, hk₂⟩ := pblt_engine_id φ (fun k => 20 * Nat.log2 k + 150) 0 hφsz hpm hLoeb
  refine ⟨k₂, ?_⟩
  intro k hk
  obtain ⟨m, hm⟩ := hk₂ k hk
  have hInterp : (φ k).interp := Pf_sound m (φ k) hm
  obtain ⟨n, hMirror⟩ := hInterp
  have hPS : proofSearch k (.plays MirrorBot (CupodBot k) .D) = true :=
    proofSearch_k_of_play_MirrorBot k n hMirror
  refine ⟨3, ?_⟩
  have hA : play 3 (CupodBot k) MirrorBot = some .D := by
    simpa using CupodBot_plays_D_against_MirrorBot k 1 hPS
  have hB : play 3 MirrorBot (CupodBot k) = some .D := by
    simpa using MirrorBot_plays_D_against_CupodBot k 0 hPS
  exact outcome_of_plays _ _ _ _ _ hA hB

end PD.Theorems
