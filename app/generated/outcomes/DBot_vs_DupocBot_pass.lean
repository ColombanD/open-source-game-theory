import PrisonersDilemma.Bots.DBot
import PrisonersDilemma.Bots.DupocBot
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Theorems.Helpers
import PrisonersDilemma.Theorems.ProofSearch
import PrisonersDilemma.Axioms

open PD
open PD.Axioms
open PD.Bots
namespace PD.Theorems

-- DupocBot monotonicity: lift a proof-search success from index n to a larger index k.
theorem DupocBot_monotonicity_local (n k : Nat) (Bot : Prog) (a : Action) :
    n ≤ k →
    proofSearch k (.plays Bot (DupocBot n) a) = true →
    proofSearch k (.plays Bot (DupocBot k) a) = true := by
  intro hle hnk
  let Φ : Nat → Formula := fun i => Formula.plays Bot (DupocBot i) a
  obtain ⟨w, hw, hwk⟩ := (proofSearch_spec k (Φ n)).1 hnk
  obtain ⟨w', hw', hwk'⟩ := witness_transport_family Φ n k hle w hw hwk
  exact (proofSearch_spec k (Φ k)).2 ⟨w', hw', hwk'⟩

-- `.bot DefectBot` always plays D against any opponent (with enough fuel).
theorem play_bot_DefectBot_against_DupocBot (k n : Nat) :
    play (n+2) (.bot DefectBot) (DupocBot k) = some .D := by
  show eval (n+2) (.bot DefectBot) (DupocBot k) (.bot DefectBot) = some .D
  simp [eval, DefectBot]

theorem interp_bot_DefectBot_plays_C_DupocBot_false (k : Nat) :
    ¬ (Formula.plays (.bot DefectBot) (DupocBot k) .C).interp := by
  rintro ⟨n, hn⟩
  cases n with
  | zero => simp [play, eval] at hn
  | succ m =>
    cases m with
    | zero => simp [play, eval] at hn
    | succ j =>
      have hd : play (j + 2) (.bot DefectBot) (DupocBot k) = some .D :=
        play_bot_DefectBot_against_DupocBot k j
      rw [hd] at hn
      cases hn

theorem proofSearch_false_bot_DefectBot_DupocBot (k : Nat) :
    proofSearch k (.plays (.bot DefectBot) (DupocBot k) .C) = false := by
  cases h : proofSearch k (.plays (.bot DefectBot) (DupocBot k) .C) with
  | true =>
      exact absurd (proofSearch_sound _ _ h)
                   (interp_bot_DefectBot_plays_C_DupocBot_false k)
  | false => rfl

-- DupocBot k plays D against .bot DefectBot because its proof search fails.
theorem DupocBot_plays_D_against_bot_DefectBot (k fuel : Nat) :
    play (fuel + 2) (DupocBot k) (.bot DefectBot) = some .D := by
  have hg := proofSearch_false_bot_DefectBot_DupocBot k
  show eval (fuel + 2) (DupocBot k) (.bot DefectBot) (DupocBot k) = some .D
  unfold DupocBot at hg ⊢
  simp [eval, Prog.subst, Formula.subst, hg]

-- DBot plays C against DupocBot k because its probe (DupocBot k vs DefectBot) returns D.
theorem DBot_plays_C_against_DupocBot (k fuel : Nat) :
    play (fuel + 4) DBot (DupocBot k) = some .C := by
  have hDupoc : play (fuel + 2) (DupocBot k) (.bot DefectBot) = some .D :=
    DupocBot_plays_D_against_bot_DefectBot k fuel
  have hGuard :
      eval (fuel + 3) DBot (DupocBot k) (.sim .opp (.bot DefectBot)) = some .D := by
    simpa [Nat.add_assoc] using
      (eval_sim_opp_bot_of_play (fuel + 2) DBot (DupocBot k) DefectBot Action.D hDupoc)
  have hPlay := play_ite_from_guard
    fuel 3 DBot (DupocBot k) (.sim .opp (.bot DefectBot))
    (.const Action.D) (.const Action.C)
    Action.C Action.D
    (by rfl) hGuard
  simpa [eval] using hPlay

-- There exists k such that the proof search for `.plays DBot (DupocBot k) .C` succeeds.
theorem proofSearch_true_DBot_DupocBot :
    ∃ k, proofSearch k (.plays DBot (DupocBot k) .C) = true := by
  have hex : ∃ m, play m DBot (DupocBot 0) = some .C :=
    ⟨_, DBot_plays_C_against_DupocBot 0 0⟩
  obtain ⟨k, hk⟩ := proofSearch_complete_plays DBot (DupocBot 0) .C hex
  refine ⟨k, ?_⟩
  exact DupocBot_monotonicity_local 0 k DBot .C (Nat.zero_le k) hk

-- DupocBot k plays C against DBot when its proof-search guard succeeds.
theorem DupocBot_plays_C_against_DBot (k fuel : Nat)
    (hk : proofSearch k (.plays DBot (DupocBot k) .C) = true) :
    play (fuel + 2) (DupocBot k) DBot = some .C := by
  show eval (fuel + 2) (DupocBot k) DBot (DupocBot k) = some .C
  unfold DupocBot at hk ⊢
  simp [eval, Prog.subst, Formula.subst, hk]

-- Main theorem: DBot vs DupocBot k yields mutual cooperation for some k.
theorem llm_outcome_DBot_vs_DupocBot (n : Nat) :
    ∃ k, outcome (n + 4) DBot (DupocBot k) = some (.C, .C) := by
  obtain ⟨k, hk⟩ := proofSearch_true_DBot_DupocBot
  refine ⟨k, ?_⟩
  have hA : play (n + 4) DBot (DupocBot k) = some .C :=
    DBot_plays_C_against_DupocBot k n
  have hB : play (n + 4) (DupocBot k) DBot = some .C := by
    simpa [Nat.add_assoc] using DupocBot_plays_C_against_DBot k (n + 2) hk
  exact outcome_of_plays _ _ _ _ _ hA hB

end PD.Theorems
