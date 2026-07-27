import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Bots.CupodBot
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Base.Asymptotics
import PrisonersDilemma.Theorems.CupodBot.Helpers

open PD
open PD.Bots
open PD.BaseTheorems
namespace PD.Theorems
/-- CUPOD self-play defects, for `k` large enough — critch22 Theorem 3.4.
    Direct application of PBLT with `φ k = .plays (CupodBot k) (CupodBot k) .D`,
    `f = id`, `k₁ = 0`. The Löb premise comes from `cupod_loeb_premise`,
    soundness collapses bounded provability to a `play` witness, and self-play
    symmetry makes the same `play` discharge both legs of `outcome`. -/
theorem outcome_CupodBot_vs_CupodBot :
    ∃ k₂, ∀ k, k₂ < k →
      ∃ fuel, outcome fuel (CupodBot k) (CupodBot k) = some (.D, .D) := by
  let φ : Nat → Formula := fun k => .plays (CupodBot k) (CupodBot k) .D
  -- `cupod_loeb_premise` proves the premise at its HONEST transcript `5·log2 k + 33` —
  -- exactly `pblt_engine_id`'s premise shape (the Löb chain needs `pm ≪ k`).
  have hLoeb :
      ∀ k, k > 0 →
        Pf (5 * Nat.log2 k + 33) (.impl (.box k (φ k)) (φ k)) := by
    intro k _
    exact cupod_loeb_premise k
  have hφsz : ∀ k, (φ k).size ≤ 100 * Nat.log2 k + 1000 := by
    intro k
    show (Formula.plays (CupodBot k) (CupodBot k) .D).size ≤ _
    simp only [numCost, Formula.size, Prog.size, CupodBot]
    omega
  have hpm : ∀ k, 5 * Nat.log2 k + 33 ≤ 100 * Nat.log2 k + 1000 := fun k => by omega
  obtain ⟨k₂, hk₂⟩ := pblt_engine_id φ (fun k => 5 * Nat.log2 k + 33) 0 hφsz hpm hLoeb
  refine ⟨k₂, ?_⟩
  intro k hk
  obtain ⟨m, hm⟩ := hk₂ k hk
  have hInterp : (φ k).interp := Pf_sound m (φ k) hm
  obtain ⟨n, hn⟩ := hInterp
  refine ⟨n, ?_⟩
  simp [outcome, hn]

end PD.Theorems
