import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Bots.DupocBot
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Base.Asymptotics
import PrisonersDilemma.Theorems.DupocBot.Helpers
import PrisonersDilemma.Outcome

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems
/-- DUPOC self-play cooperates, for `k` large enough — critch22 Theorem 3.7.
    Direct application of PBLT with `φ k = .plays (DupocBot k) (DupocBot k) .C`,
    `f = id`, `k₁ = 0`. The Löb premise comes from `dupoc_loeb_premise`,
    soundness collapses bounded provability to a `play` witness, and self-play
    symmetry makes the same `play` discharge both legs of `outcome`. -/
@[outcome]
theorem outcome_DupocBot_vs_DupocBot :
    OutcomeSpec .eventual 2 DupocBot DupocBot (some (.C, .C)) := by
  let φ : Nat → Formula := fun k => .plays (DupocBot k) (DupocBot k) .C
  -- `dupoc_loeb_premise` proves the premise at its HONEST transcript `5·log2 k + 33` —
  -- exactly `pblt_engine_id`'s premise shape (the Löb chain needs `pm ≪ k`).
  have hLoeb :
      ∀ k, k > 0 →
        Pf (5 * Nat.log2 k + 33) (.impl (.box k (φ k)) (φ k)) := by
    intro k _
    exact dupoc_loeb_premise k
  have hφsz : ∀ k, (φ k).size ≤ 100 * Nat.log2 k + 1000 := by
    intro k
    show (Formula.plays (DupocBot k) (DupocBot k) .C).size ≤ _
    simp only [numCost, Formula.size, Prog.size, DupocBot]
    omega
  have hpm : ∀ k, 5 * Nat.log2 k + 33 ≤ 100 * Nat.log2 k + 1000 := fun k => by omega
  obtain ⟨k₂, hk₂⟩ := pblt_engine_id φ (fun k => 5 * Nat.log2 k + 33) 0 hφsz hpm hLoeb
  refine ⟨k₂, fun k hk fuel => ?_⟩
  obtain ⟨m, hm⟩ := hk₂ k hk
  -- Soundness yields the play at SOME fuel; the match is determined at fuel 2 whatever
  -- the oracle says, so determinism pins the value there and monotonicity does the rest.
  have hex : ∃ n, play n (DupocBot k) (DupocBot k) = some .C := Pf_sound m (φ k) hm
  have htot : ∃ b, play 2 (DupocBot k) (DupocBot k) = some b :=
    play_search_const_total k _ _ _ _ 0
  have hC : play (fuel + 2) (DupocBot k) (DupocBot k) = some .C := play_at_of_ex hex htot fuel
  exact outcome_of_plays _ _ _ _ _ hC hC

end PD.Theorems
