import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Axioms
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Bots.CupodBot
import PrisonersDilemma.Theorems.CooperateBot
import PrisonersDilemma.Theorems.DefectBot
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Theorems.ProofSearch
import PrisonersDilemma.Theorems.Helpers
import PrisonersDilemma.Theorems.TitForTatBot
import PrisonersDilemma.Theorems.DBot

open PDNew
open PDNew.Axioms
open PDNew.Bots
namespace PDNew.Theorems

/-- Monotonicity of CupodBot: If the proof search succeeds with less fuel, it also succeeds with more fuel -/
theorem CupodBot_monotonicity (n k : Nat) :
    n ≤ k →
    proofSearch k (.plays DefectBot (CupodBot n) .D) = true →
    proofSearch k (.plays DefectBot (CupodBot k) .D) = true := by
  intro hle hnk
  let Φ : Nat → Formula := fun i => Formula.plays DefectBot (CupodBot i) .D
  obtain ⟨w, hw, hwk⟩ := (proofSearch_spec k (Φ n)).1 hnk
  obtain ⟨w', hw', hwk'⟩ := witness_transport_family Φ n k hle w hw hwk
  exact (proofSearch_spec k (Φ k)).2 ⟨w', hw', hwk'⟩


/-- Proof search is false for CooperateBot -/
theorem proofSearch_false_for_CooperateBot (k : Nat) :
    proofSearch k (.plays CooperateBot (CupodBot k) .D) = false := by
  cases h : proofSearch k (.plays CooperateBot (CupodBot k) .D) with
  | true  => exact absurd (proofSearch_sound _ _ h)
                          (interp_CooperateBot_plays_D_false _)
  | false => rfl

theorem proofSearch_true_for_DefectBot_different_k (n: Nat) :
    ∃ k, proofSearch k (.plays DefectBot (CupodBot n) .D) = true := by
  -- Show that there exists n such that play n DefectBot (CupodBot n) = some .D
  have hex : ∃ m, play m DefectBot (CupodBot n) = some .D := by
    -- Use the fact that DefectBot always plays .D
    exists 1
  -- Now apply the restricted completeness theorem
  have h := proofSearch_complete_plays DefectBot (CupodBot n) .D hex
  obtain ⟨k, hk⟩ := h
  exact ⟨k, hk⟩

/-- Proof search k is true for DefectBot vs Cupod k -/
theorem proofSearch_true_for_DefectBot :
    ∃ k, proofSearch k (.plays DefectBot (CupodBot k) .D) = true := by
  have h := proofSearch_true_for_DefectBot_different_k
  obtain ⟨k, hk⟩ := h 0 -- we can pick any n, so we pick 0 for simplicity; k is the corresponding k from the lemma.
  refine ⟨k, ?_⟩ -- use the same k for the conclusion
  exact CupodBot_monotonicity 0 k (Nat.zero_le k) hk

theorem CupodBot_plays_C_against_CooperateBot (k fuel : Nat) :
    play (fuel + 2) (CupodBot k) CooperateBot = some .C := by
  -- `guard_false` tells us the proof search for “CooperateBot plays D” fails.
  -- Once we unfold the bot, the remaining `simp` can simplify the search node
  -- and the constant branch all the way down to `.C`.
  have hg := proofSearch_false_for_CooperateBot k
  show eval (fuel + 2) (CupodBot k) CooperateBot (CupodBot k) = some .C
  unfold CupodBot at hg ⊢
  simp [eval, Prog.subst, Formula.subst, hg]

theorem CupodBot_plays_D_against_DefectBot (k fuel : Nat)
    (hk : proofSearch k (.plays DefectBot (CupodBot k) .D) = true) :
    play (fuel + 2) (CupodBot k) DefectBot = some .D := by
  show eval (fuel + 2) (CupodBot k) DefectBot (CupodBot k) = some .D
  unfold CupodBot at hk ⊢
  simp [eval, Prog.subst, Formula.subst, hk]


/-- CupodBot vs CooperateBot: uses proof search being false -/
theorem CupodBot_vs_CooperateBot (k fuel : Nat):
    outcome (fuel + 2) (CupodBot k) CooperateBot = some (.C, .C) := by
  -- Left side: CUPOD executes its `.search` guard. The guard is false by the
  -- lemma above, so the `search` falls through to the final `.const .C` branch.
  have hA : play (fuel + 2) (CupodBot k) CooperateBot = some .C := CupodBot_plays_C_against_CooperateBot k fuel
  -- Right side: CooperateBot is definitionally the constant `.C` bot.
  have hB : play (fuel + 2) CooperateBot (CupodBot k) = some .C := rfl
  -- Finally, `outcome` just packages the two `play` results together.
  simp [outcome, hA, hB]

/-- CupodBot vs DefectBot: uses proof search being true -/
theorem CupodBot_vs_DefectBot (fuel : Nat):
    ∃ k, outcome (fuel + 2) (CupodBot k) DefectBot = some (.D, .D) := by
  obtain ⟨k, hk⟩ := proofSearch_true_for_DefectBot
  refine ⟨k, ?_⟩

  have hA : play (fuel + 2) (CupodBot k) DefectBot = some .D :=
    CupodBot_plays_D_against_DefectBot k fuel hk

  have hB : play (fuel + 2) DefectBot (CupodBot k) = some .D := by
    simpa [Nat.add_assoc] using (play_DefectBot (fuel + 1) (CupodBot k))

  simp [outcome, hA, hB]



theorem TitForTatBot_plays_C_against_CupodBot (k fuel : Nat) :
    play (fuel + 4) TitForTatBot (CupodBot k) = some .C := by
  have hCupod : play (fuel + 2) (CupodBot k) CooperateBot = some .C := CupodBot_plays_C_against_CooperateBot k fuel
  have hGuard :
      eval (fuel + 3) TitForTatBot (CupodBot k) (.sim .opp CooperateBot) = some .C := by
    simpa [eval, Prog.subst, play, CooperateBot] using hCupod
  have hPlay := play_ite_from_guard
    fuel 3 TitForTatBot (CupodBot k) (.sim .opp CooperateBot)
    (.const Action.C) (.const Action.D)
    Action.C Action.C
    (by rfl) hGuard
  simpa [eval] using hPlay

theorem interp_TitForTatBot_plays_D_false (k : Nat) :
    ¬ (Formula.plays TitForTatBot (CupodBot k) .D).interp := by
  -- `interp` for a `.plays` formula means: there exists some evaluation fuel
  -- `n` at which the play returns the claimed action.  To refute the formula,
  -- assume such an `n` exists and show that this run cannot produce `.D`.
  rintro ⟨n, hn⟩
  -- The first few fuel values do not give TitForTat enough steps to complete
  -- the simulation of its opponent against `CooperateBot`.  We split them out
  -- explicitly and let `simp` compute the exhausted/incomplete evaluations.
  cases n with
  | zero   => simp only [play, eval, reduceCtorEq] at hn
  | succ m =>
      cases m with
      | zero => simp [play, eval, TitForTatBot] at hn
      | succ m =>
          cases m with
          | zero =>
              simp [play, eval, TitForTatBot] at hn
          | succ fuel =>
              cases fuel with
              | zero =>
                  -- At exactly three steps, the guard reaches CUPOD against
                  -- `CooperateBot`; CUPOD cooperates, so TitForTat's result is
                  -- still not `.D`.
                  simp [play, eval, TitForTatBot, CupodBot, Prog.subst, Formula.subst, CooperateBot] at hn
              | succ fuel =>
                  -- From four steps onward, use the parametric play theorem:
                  -- TitForTat always cooperates against `CupodBot k`.
                  have hC : play (fuel + 1 + 1 + 1 + 1) TitForTatBot (CupodBot k) = some .C := by
                    simpa [Nat.add_assoc] using TitForTatBot_plays_C_against_CupodBot k fuel
                  -- Rewriting the assumed `.D` run with the proven `.C` run
                  -- leaves `some .C = some .D`, which is contradictory.
                  rw [hC] at hn
                  cases hn

theorem proofSearch_false_for_TitForTatBot (k : Nat) :
    proofSearch k (.plays TitForTatBot (CupodBot k) .D) = false := by
  cases h : proofSearch k (.plays TitForTatBot (CupodBot k) .D) with
  | true  => exact absurd (proofSearch_sound _ _ h)
                          (interp_TitForTatBot_plays_D_false _)
  | false => rfl

theorem CupodBot_vs_TitForTatBot (fuel : Nat):
    ∃ k, outcome (fuel + 4) (CupodBot k) TitForTatBot = some (.C, .C) := by
  let k := 0
  refine ⟨k, ?_⟩
  have hA : play (fuel + 4) (CupodBot k) TitForTatBot = some .C := by
    have hg := proofSearch_false_for_TitForTatBot k
    show eval (fuel + 4) (CupodBot k) TitForTatBot (CupodBot k) = some .C
    unfold CupodBot at hg ⊢
    simp [eval, Prog.subst, Formula.subst, hg]
  have hB : play (fuel + 4) TitForTatBot (CupodBot k) = some .C := by
    exact TitForTatBot_plays_C_against_CupodBot k fuel
  simp [outcome, hA, hB]


theorem DBot_plays_C_against_CupodBot (k fuel : Nat)
    (hk : proofSearch k (.plays DefectBot (CupodBot k) .D) = true) :
    play (fuel + 4) DBot (CupodBot k) = some .C := by
  have hCupod : play (fuel + 2) (CupodBot k) DefectBot = some .D :=
    CupodBot_plays_D_against_DefectBot k fuel hk
  have hGuard :
      eval (fuel + 3) DBot (CupodBot k) (.sim .opp DefectBot) = some .D := by
    simpa [eval, Prog.subst, play, DefectBot] using hCupod
  have hPlay := play_ite_from_guard
    fuel 3 DBot (CupodBot k) (.sim .opp DefectBot)
    (.const Action.D) (.const Action.C)
    Action.C Action.D
    (by rfl) hGuard
  simpa [eval] using hPlay

theorem interp_DBot_plays_D_false (k : Nat)
    (hk : proofSearch k (.plays DefectBot (CupodBot k) .D) = true) :
    ¬ (Formula.plays DBot (CupodBot k) .D).interp := by
  -- `interp` for a `.plays` formula means: there exists some evaluation fuel
  -- `n` at which the play returns the claimed action.  To refute the formula,
  -- assume such an `n` exists and show that this run cannot produce `.D`.
  rintro ⟨n, hn⟩
  -- The first few fuel values do not give DBot enough steps to complete
  -- the simulation of its opponent against `DefectBot`.  We split them out
  -- explicitly and let `simp` compute the exhausted/incomplete evaluations.
  cases n with
  | zero   => simp only [play, eval, reduceCtorEq] at hn
  | succ m =>
      cases m with
      | zero => simp [play, eval, DBot] at hn
      | succ m =>
          cases m with
          | zero =>
              simp [play, eval, DBot] at hn
          | succ fuel =>
              cases fuel with
              | zero =>
                  -- At exactly three steps, the guard reaches CUPOD against
                  -- `DefectBot`, but there is not enough evaluation fuel left
                  -- to finish CUPOD's branch, so DBot still cannot return `.D`.
                  simp [play, eval, DBot, CupodBot, Prog.subst, Formula.subst, DefectBot] at hn
              | succ fuel =>
                  -- From four steps onward, use the parametric play theorem:
                  -- DBot always cooperates against `CupodBot k`.
                  have hC : play (fuel + 1 + 1 + 1 + 1) DBot (CupodBot k) = some .C := by
                    simpa [Nat.add_assoc] using DBot_plays_C_against_CupodBot k fuel hk
                  -- Rewriting the assumed `.D` run with the proven `.C` run
                  -- leaves `some .C = some .D`, which is contradictory.
                  rw [hC] at hn
                  cases hn

theorem proofSearch_false_for_DBot (k : Nat)
    (hk : proofSearch k (.plays DefectBot (CupodBot k) .D) = true) :
    proofSearch k (.plays DBot (CupodBot k) .D) = false := by
  cases h : proofSearch k (.plays DBot (CupodBot k) .D) with
  | true  => exact absurd (proofSearch_sound _ _ h)
                          (interp_DBot_plays_D_false _ hk)
  | false => rfl

theorem CupodBot_vs_DBot (fuel : Nat):
    ∃ k, outcome (fuel + 4) (CupodBot k) DBot = some (.C, .C) := by
  obtain ⟨k, hk⟩ := proofSearch_true_for_DefectBot
  refine ⟨k, ?_⟩
  have hA : play (fuel + 4) (CupodBot k) DBot = some .C := by
    have hg := proofSearch_false_for_DBot k hk
    show eval (fuel + 4) (CupodBot k) DBot (CupodBot k) = some .C
    unfold CupodBot at hg ⊢
    simp [eval, Prog.subst, Formula.subst, hg]
  have hB : play (fuel + 4) DBot (CupodBot k) = some .C := by
    exact DBot_plays_C_against_CupodBot k fuel hk
  simp [outcome, hA, hB]

end PDNew.Theorems
