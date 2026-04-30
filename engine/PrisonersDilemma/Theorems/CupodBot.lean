import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Axioms
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Bots.CupodBot
import PrisonersDilemma.Bots.MirrorBot
import PrisonersDilemma.Theorems.CooperateBot
import PrisonersDilemma.Theorems.DefectBot
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Theorems.ProofSearch
import PrisonersDilemma.Theorems.Helpers
import PrisonersDilemma.Theorems.TitForTatBot
import PrisonersDilemma.Theorems.DBot
import PrisonersDilemma.Bots.OBot
import PrisonersDilemma.Bots.EBot

open PDNew
open PDNew.Axioms
open PDNew.Bots
namespace PDNew.Theorems


/-- Monotonicity of CupodBot: If the proof search succeeds with less fuel, it also succeeds with more fuel -/
theorem CupodBot_monotonicity (n k : Nat) (Bot : Prog) (a : Action) :
    n ≤ k →
    proofSearch k (.plays Bot (CupodBot n) a) = true →
    proofSearch k (.plays Bot (CupodBot k) a) = true := by
  intro hle hnk
  let Φ : Nat → Formula := fun i => Formula.plays Bot (CupodBot i) a
  obtain ⟨w, hw, hwk⟩ := (proofSearch_spec k (Φ n)).1 hnk
  obtain ⟨w', hw', hwk'⟩ := witness_transport_family Φ n k hle w hw hwk
  exact (proofSearch_spec k (Φ k)).2 ⟨w', hw', hwk'⟩


-- CooperateBot --

/-- Proof search is false for CooperateBot -/
theorem proofSearch_false_for_CooperateBot (k : Nat) :
    proofSearch k (.plays CooperateBot (CupodBot k) .D) = false := by
  cases h : proofSearch k (.plays CooperateBot (CupodBot k) .D) with
  | true  => exact absurd (proofSearch_sound _ _ h)
                          (interp_CooperateBot_plays_D_false _)
  | false => rfl

theorem play_bot_CooperateBot (n : Nat) (opponent : Prog) :
    play (n + 2) (.bot CooperateBot) opponent = some .C := by
  simp [play, eval, CooperateBot]

theorem interp_bot_CooperateBot_plays_D_false (q : Prog) :
    ¬ (Formula.plays (.bot CooperateBot) q .D).interp := by
  rintro ⟨n, hn⟩
  cases n with
  | zero => simp only [play, eval, reduceCtorEq] at hn
  | succ m =>
      cases m with
      | zero => simp [play, eval] at hn
      | succ fuel =>
          rw [play_bot_CooperateBot] at hn
          cases hn

theorem proofSearch_false_for_bot_CooperateBot (k : Nat) :
    proofSearch k (.plays (.bot CooperateBot) (CupodBot k) .D) = false := by
  cases h : proofSearch k (.plays (.bot CooperateBot) (CupodBot k) .D) with
  | true  => exact absurd (proofSearch_sound _ _ h)
                          (interp_bot_CooperateBot_plays_D_false _)
  | false => rfl

theorem CupodBot_plays_C_against_CooperateBot (k fuel : Nat) :
    play (fuel + 2) (CupodBot k) CooperateBot = some .C := by
  -- `guard_false` tells us the proof search for “CooperateBot plays D” fails.
  -- Once we unfold the bot, the remaining `simp` can simplify the search node
  -- and the constant branch all the way down to `.C`.
  have hg := proofSearch_false_for_CooperateBot k
  show eval (fuel + 2) (CupodBot k) CooperateBot (CupodBot k) = some .C
  unfold CupodBot at hg ⊢
  simp [eval, Prog.subst, Formula.subst, hg]

theorem CupodBot_plays_C_against_bot_CooperateBot (k fuel : Nat) :
    play (fuel + 2) (CupodBot k) (.bot CooperateBot) = some .C := by
  have hg := proofSearch_false_for_bot_CooperateBot k
  show eval (fuel + 2) (CupodBot k) (.bot CooperateBot) (CupodBot k) = some .C
  unfold CupodBot at hg ⊢
  simp [eval, Prog.subst, Formula.subst, hg]

/-- CupodBot vs CooperateBot: uses proof search being false -/
theorem CupodBot_vs_CooperateBot (k fuel : Nat):
    outcome (fuel + 2) (CupodBot k) CooperateBot = some (.C, .C) := by
  -- Left side: CUPOD executes its `.search` guard. The guard is false by the
  -- lemma above, so the `search` falls through to the final `.const .C` branch.
  have hA : play (fuel + 2) (CupodBot k) CooperateBot = some .C := CupodBot_plays_C_against_CooperateBot k fuel
  -- Right side: CooperateBot is definitionally the constant `.C` bot.
  have hB : play (fuel + 2) CooperateBot (CupodBot k) = some .C := rfl
  -- Finally, `outcome` just packages the two `play` results together.
  exact outcome_of_plays _ _ _ _ _ hA hB


-- DefectBot --

/-- We first show that proof search is true for DefectBot, for any k not necessary equal to n -/
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
  exact CupodBot_monotonicity 0 k DefectBot .D (Nat.zero_le k) hk

theorem proofSearch_true_for_bot_DefectBot_different_k (n: Nat) :
    ∃ k, proofSearch k (.plays (.bot DefectBot) (CupodBot n) .D) = true := by
  have hex : ∃ m, play m (.bot DefectBot) (CupodBot n) = some .D := by
    exists 2
  exact proofSearch_complete_plays (.bot DefectBot) (CupodBot n) .D hex

theorem proofSearch_true_for_bot_DefectBot :
    ∃ k, proofSearch k (.plays (.bot DefectBot) (CupodBot k) .D) = true := by
  obtain ⟨k, hk⟩ := proofSearch_true_for_bot_DefectBot_different_k 0
  refine ⟨k, ?_⟩
  exact CupodBot_monotonicity 0 k (.bot DefectBot) .D (Nat.zero_le k) hk

theorem CupodBot_plays_D_against_DefectBot (k fuel : Nat)
    (hk : proofSearch k (.plays DefectBot (CupodBot k) .D) = true) :
    play (fuel + 2) (CupodBot k) DefectBot = some .D := by
  show eval (fuel + 2) (CupodBot k) DefectBot (CupodBot k) = some .D
  unfold CupodBot at hk ⊢
  simp [eval, Prog.subst, Formula.subst, hk]

theorem CupodBot_plays_D_against_bot_DefectBot (k fuel : Nat)
    (hk : proofSearch k (.plays (.bot DefectBot) (CupodBot k) .D) = true) :
    play (fuel + 2) (CupodBot k) (.bot DefectBot) = some .D := by
  show eval (fuel + 2) (CupodBot k) (.bot DefectBot) (CupodBot k) = some .D
  unfold CupodBot at hk ⊢
  simp [eval, Prog.subst, Formula.subst, hk]

/-- CupodBot vs DefectBot: uses proof search being true -/
theorem CupodBot_vs_DefectBot (fuel : Nat):
    ∃ k, outcome (fuel + 2) (CupodBot k) DefectBot = some (.D, .D) := by
  obtain ⟨k, hk⟩ := proofSearch_true_for_DefectBot
  refine ⟨k, ?_⟩

  have hA : play (fuel + 2) (CupodBot k) DefectBot = some .D :=
    CupodBot_plays_D_against_DefectBot k fuel hk

  have hB : play (fuel + 2) DefectBot (CupodBot k) = some .D := by
    simpa [Nat.add_assoc] using (play_DefectBot (fuel + 1) (CupodBot k))

  exact outcome_of_plays _ _ _ _ _ hA hB


-- TitForTatBot --

theorem TitForTatBot_plays_C_against_CupodBot (k fuel : Nat) :
    play (fuel + 4) TitForTatBot (CupodBot k) = some .C := by
  have hCupod : play (fuel + 2) (CupodBot k) (.bot CooperateBot) = some .C :=
    CupodBot_plays_C_against_bot_CooperateBot k fuel
  have hGuard :
      eval (fuel + 3) TitForTatBot (CupodBot k) (.sim .opp (.bot CooperateBot)) = some .C := by
    simpa [Nat.add_assoc] using
      (eval_sim_opp_bot_of_play (fuel + 2) TitForTatBot (CupodBot k) CooperateBot Action.C hCupod)
  have hPlay := play_ite_from_guard
    fuel 3 TitForTatBot (CupodBot k) (.sim .opp (.bot CooperateBot))
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
  exact outcome_of_plays _ _ _ _ _ hA hB


-- DBot --

theorem DBot_plays_C_against_CupodBot (k fuel : Nat)
    (hk : proofSearch k (.plays (.bot DefectBot) (CupodBot k) .D) = true) :
    play (fuel + 4) DBot (CupodBot k) = some .C := by
  have hCupod : play (fuel + 2) (CupodBot k) (.bot DefectBot) = some .D :=
    CupodBot_plays_D_against_bot_DefectBot k fuel hk
  have hGuard :
      eval (fuel + 3) DBot (CupodBot k) (.sim .opp (.bot DefectBot)) = some .D := by
    simpa [Nat.add_assoc] using
      (eval_sim_opp_bot_of_play (fuel + 2) DBot (CupodBot k) DefectBot Action.D hCupod)
  have hPlay := play_ite_from_guard
    fuel 3 DBot (CupodBot k) (.sim .opp (.bot DefectBot))
    (.const Action.D) (.const Action.C)
    Action.C Action.D
    (by rfl) hGuard
  simpa [eval] using hPlay

theorem interp_DBot_plays_D_false (k : Nat)
    (hk : proofSearch k (.plays (.bot DefectBot) (CupodBot k) .D) = true) :
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
    (hk : proofSearch k (.plays (.bot DefectBot) (CupodBot k) .D) = true) :
    proofSearch k (.plays DBot (CupodBot k) .D) = false := by
  cases h : proofSearch k (.plays DBot (CupodBot k) .D) with
  | true  => exact absurd (proofSearch_sound _ _ h)
                          (interp_DBot_plays_D_false _ hk)
  | false => rfl

theorem CupodBot_vs_DBot (fuel : Nat):
    ∃ k, outcome (fuel + 4) (CupodBot k) DBot = some (.C, .C) := by
  obtain ⟨k, hk⟩ := proofSearch_true_for_bot_DefectBot
  refine ⟨k, ?_⟩
  have hA : play (fuel + 4) (CupodBot k) DBot = some .C := by
    have hg := proofSearch_false_for_DBot k hk
    show eval (fuel + 4) (CupodBot k) DBot (CupodBot k) = some .C
    unfold CupodBot at hg ⊢
    simp [eval, Prog.subst, Formula.subst, hg]
  have hB : play (fuel + 4) DBot (CupodBot k) = some .C := by
    exact DBot_plays_C_against_CupodBot k fuel hk
  exact outcome_of_plays _ _ _ _ _ hA hB


-- OBot --

theorem OBot_plays_D_against_CupodBot (k fuel : Nat)
    (hk : proofSearch k (.plays (.bot DefectBot) (CupodBot k) .D) = true) :
    play (fuel + 5) OBot (CupodBot k) = some .D := by
  have hGuard1 :
      eval (fuel + 4) OBot (CupodBot k) (.sim .opp (.bot CooperateBot)) = some .C := by
    have hProbe : play (fuel + 3) (CupodBot k) (.bot CooperateBot) = some .C := by
      simpa [Nat.add_assoc] using CupodBot_plays_C_against_bot_CooperateBot k (fuel + 1)
    simpa [Nat.add_assoc] using
      (eval_sim_opp_bot_of_play (fuel + 3) OBot (CupodBot k) CooperateBot Action.C hProbe)
  have hGuard2 :
      eval (fuel + 3) OBot (CupodBot k) (.sim .opp (.bot DefectBot)) = some .D := by
    have hProbe : play (fuel + 2) (CupodBot k) (.bot DefectBot) = some .D :=
      CupodBot_plays_D_against_bot_DefectBot k fuel hk
    simpa [Nat.add_assoc] using
      (eval_sim_opp_bot_of_play (fuel + 2) OBot (CupodBot k) DefectBot Action.D hProbe)
  have hPlay := play_ite_from_guard
    fuel 4 OBot (CupodBot k) (.sim .opp (.bot CooperateBot))
    (.ite (.sim .opp (.bot DefectBot)) Action.C (.const Action.C) (.const Action.D))
    (.const Action.D)
    Action.C Action.C
    (by rfl) hGuard1
  have hInner :
      eval (fuel + 4) OBot (CupodBot k)
        (.ite (.sim .opp (.bot DefectBot)) Action.C (.const Action.C) (.const Action.D)) =
          some .D := by
    simpa [Nat.add_assoc] using
      (eval_ite_from_guard (fuel + 3) OBot (CupodBot k)
        (.sim .opp (.bot DefectBot)) (.const Action.C) (.const Action.D)
        Action.C Action.D hGuard2)
  simpa [hInner] using hPlay

theorem proofSearch_true_for_OBot_different_k:
    ∃ k n, proofSearch k (.plays OBot (CupodBot n) .D) = true := by
  have hex : ∃ m n, play m OBot (CupodBot n) = some .D := by
    -- We want to use OBot plays D against CupodBot n, but we need to have hk
    have hk := proofSearch_true_for_bot_DefectBot
    obtain ⟨d, hd⟩ := hk
    have hOBotPlayD := OBot_plays_D_against_CupodBot d 0 hd
    exists 5, d
  rcases hex with ⟨m, n, h⟩
  have hn : ∃ m, play m OBot (CupodBot n) = some Action.D := ⟨m, h⟩
  have h := proofSearch_complete_plays OBot (CupodBot n) .D hn
  obtain ⟨k, hk⟩ := h
  exact ⟨k, n, hk⟩

theorem proofSearch_true_for_OBot :
    ∃ k, proofSearch k (.plays OBot (CupodBot k) .D) = true := by
  have h := proofSearch_true_for_OBot_different_k
  obtain ⟨k, n, hk⟩ := h
  by_cases hnk : n ≤ k
  · refine ⟨k, ?_⟩
    -- If the Cupod index `n` is at most the proof-search fuel `k`, keep `k`
    -- as the final witness and transport the formula from `CupodBot n` to
    -- `CupodBot k`.
    exact CupodBot_monotonicity n k OBot .D hnk hk
  · refine ⟨n, ?_⟩
    -- Otherwise `k < n`. We cannot transport `CupodBot n` down to `CupodBot k`,
    -- so choose `n` as the final witness and only increase the proof-search
    -- fuel from `k` to `n`, leaving the formula itself unchanged.
    exact proofSearch_monotone k n (.plays OBot (CupodBot n) .D)
      (Nat.le_of_lt (Nat.lt_of_not_ge hnk)) hk

theorem CupodBot_plays_D_against_OBot (fuel : Nat) (k : Nat)
    (hk: proofSearch k (.plays OBot (CupodBot k) .D) = true) :
    play (fuel + 5) (CupodBot k) OBot = some .D := by
    show eval (fuel + 5) (CupodBot k) OBot (CupodBot k)= some .D
    unfold CupodBot at hk ⊢
    simp [eval, Prog.subst, Formula.subst, hk]

theorem CupodBot_vs_OBot (fuel : Nat) :
    ∃ k, outcome (fuel + 5) (CupodBot k) OBot = some (.D, .D) := by
  -- First get possibly different proof-search witnesses:
  -- `o` makes CUPOD defect against OBot, while `d` makes OBot defect against
  -- CUPOD via the DefectBot probe used inside `OBot_plays_D_against_CupodBot`.
  obtain ⟨o, ho⟩ := proofSearch_true_for_OBot
  obtain ⟨d, hd⟩ := proofSearch_true_for_bot_DefectBot

  -- Choose one final index large enough for both witnesses. From there,
  -- monotonicity lets us reuse both proof-search successes at the same `k`.
  let k := o + d
  have hok : o ≤ k := by
    exact Nat.le_add_right o d
  have hdk : d ≤ k := by
    exact Nat.le_add_left d o

  -- Lift OBot's proof-search success from fuel/index `o` to the shared `k`.
  have hkOBot : proofSearch k (.plays OBot (CupodBot k) .D) = true :=
    CupodBot_monotonicity o k OBot .D hok
      (proofSearch_monotone o k (.plays OBot (CupodBot o) .D) hok ho)

  -- Lift DefectBot's proof-search success from fuel/index `d` to the same `k`.
  -- This is what OBot needs in order to defect against `CupodBot k`.
  have hkDefect : proofSearch k (.plays (.bot DefectBot) (CupodBot k) .D) = true :=
    CupodBot_monotonicity d k (.bot DefectBot) .D hdk
      (proofSearch_monotone d k (.plays (.bot DefectBot) (CupodBot d) .D) hdk hd)
  refine ⟨k, ?_⟩

  -- CUPOD defects against OBot because `hkOBot` makes its search guard true.
  have hA : play (fuel + 5) (CupodBot k) OBot = some .D :=
    CupodBot_plays_D_against_OBot fuel k hkOBot

  -- OBot defects against CUPOD because `hkDefect` makes CUPOD defect against
  -- DefectBot, so OBot's inner probe follows its defect branch.
  have hB : play (fuel + 5) OBot (CupodBot k) = some .D := by
    exact OBot_plays_D_against_CupodBot k fuel hkDefect
  exact outcome_of_plays _ _ _ _ _ hA hB


--EBot --

theorem EBot_plays_C_against_CupodBot (k fuel : Nat)
    (hk : proofSearch k (.plays (.bot DefectBot) (CupodBot k) .D) = true) :
    play (fuel + 5) EBot (CupodBot k) = some .C := by
  have hCupodD : play (fuel + 3) (CupodBot k) (.bot DefectBot) = some .D := by
    simpa [Nat.add_assoc] using CupodBot_plays_D_against_bot_DefectBot k (fuel + 1) hk
  have hGuard1 :
      eval (fuel + 4) EBot (CupodBot k) (.sim .opp (.bot DefectBot)) = some .D := by
    simpa [Nat.add_assoc] using
      (eval_sim_opp_bot_of_play (fuel + 3) EBot (CupodBot k) DefectBot Action.D hCupodD)
  have hCupodC : play (fuel + 2) (CupodBot k) (.bot CooperateBot) = some .C :=
    CupodBot_plays_C_against_bot_CooperateBot k fuel
  have hGuard2 :
      eval (fuel + 3) EBot (CupodBot k) (.sim .opp (.bot CooperateBot)) = some .C := by
    simpa [Nat.add_assoc] using
      (eval_sim_opp_bot_of_play (fuel + 2) EBot (CupodBot k) CooperateBot Action.C hCupodC)
  have hInner :
      eval (fuel + 4) EBot (CupodBot k)
        (.ite (.sim .opp (.bot CooperateBot)) Action.C (.const Action.C)
          (.ite (.sim .opp (.bot MirrorBot)) Action.C (.const Action.C) (.const Action.D))) =
        some .C := by
    simpa [Nat.add_assoc] using
      (eval_ite_from_guard (fuel + 3) EBot (CupodBot k)
        (.sim .opp (.bot CooperateBot)) (.const Action.C)
        (.ite (.sim .opp (.bot MirrorBot)) Action.C (.const Action.C) (.const Action.D))
        Action.C Action.C hGuard2)
  have hPlay := play_ite_from_guard
    fuel 4 EBot (CupodBot k) (.sim .opp (.bot DefectBot))
    (.const Action.D)
    (.ite (.sim .opp (.bot CooperateBot)) Action.C (.const Action.C)
      (.ite (.sim .opp (.bot MirrorBot)) Action.C (.const Action.C) (.const Action.D)))
    Action.C Action.D
    (by rfl) hGuard1
  simpa [Nat.add_assoc, hInner] using hPlay

theorem interp_EBot_plays_D_false (k : Nat)
    (hk : proofSearch k (.plays (.bot DefectBot) (CupodBot k) .D) = true) :
    ¬ (Formula.plays EBot (CupodBot k) .D).interp := by
  rintro ⟨n, hn⟩
  cases n with
  | zero   => simp only [play, eval, reduceCtorEq] at hn
  | succ m =>
      cases m with
      | zero => simp [play, eval, EBot] at hn
      | succ m =>
          cases m with
          | zero => simp [play, eval, EBot] at hn
          | succ fuel =>
              cases fuel with
              | zero =>
                  simp [play, eval, EBot, CupodBot, Prog.subst, Formula.subst] at hn
              | succ fuel =>
                  cases fuel with
                  | zero =>
                      have hk' := hk
                      unfold CupodBot at hk'
                      simp [play, eval, EBot, CupodBot, Prog.subst, Formula.subst, hk'] at hn
                      have hDC : (Action.D == Action.C) = false := by decide
                      rw [hDC] at hn
                      cases hn
                  | succ fuel =>
                      have hC :
                          play (fuel + 1 + 1 + 1 + 1 + 1) EBot (CupodBot k) = some .C := by
                        simpa [Nat.add_assoc] using EBot_plays_C_against_CupodBot k fuel hk
                      rw [hC] at hn
                      cases hn

theorem proofSearch_false_for_EBot (k : Nat)
    (hk : proofSearch k (.plays (.bot DefectBot) (CupodBot k) .D) = true) :
    proofSearch k (.plays EBot (CupodBot k) .D) = false := by
  cases h : proofSearch k (.plays EBot (CupodBot k) .D) with
  | true  => exact absurd (proofSearch_sound _ _ h)
                          (interp_EBot_plays_D_false _ hk)
  | false => rfl

theorem CupodBot_vs_EBot (fuel : Nat):
    ∃ k, outcome (fuel + 5) (CupodBot k) EBot = some (.C, .C) := by
  obtain ⟨k, hk⟩ := proofSearch_true_for_bot_DefectBot
  refine ⟨k, ?_⟩
  have hA : play (fuel + 5) (CupodBot k) EBot = some .C := by
    have hg := proofSearch_false_for_EBot k hk
    show eval (fuel + 5) (CupodBot k) EBot (CupodBot k) = some .C
    unfold CupodBot at hg ⊢
    simp [eval, Prog.subst, Formula.subst, hg]
  have hB : play (fuel + 5) EBot (CupodBot k) = some .C := by
    exact EBot_plays_C_against_CupodBot k fuel hk
  exact outcome_of_plays _ _ _ _ _ hA hB

-- CupodBot --

theorem linear_function_growth :
  ∃ c kHat, c > 0 ∧ ∀ k, k > kHat → k > c * Nat.log2 k := by
  -- We only need one positive constant and one threshold.  Taking `c = 1`
  -- reduces the goal to showing that, eventually, `k > log2 k`.
  refine ⟨1, 1, by decide, ?_⟩
  intro k hk
  -- Since `k > 1`, in particular `k` is nonzero.  This lets us use the
  -- standard characterization `Nat.log2_lt`: `log2 k < k` iff `k < 2^k`.
  have hk_ne_zero : k ≠ 0 := by
    exact Nat.ne_of_gt (Nat.lt_trans (by decide : 0 < 1) hk)
  -- The exponential bound `k < 2^k` is true because the base `2` is bigger
  -- than `1`.  Rewriting through `Nat.log2_lt` gives `log2 k < k`.
  have hlog_lt : Nat.log2 k < k := by
    exact (Nat.log2_lt hk_ne_zero).2 (Nat.lt_pow_self (by decide : 1 < 2))
  -- The PBLT growth hypothesis is written as `k > 1 * log2 k`; `simpa`
  -- removes the harmless multiplication by `1`.
  simpa using hlog_lt

theorem formula_self_fulfilling :
  let φ := fun k : Nat => Formula.plays (CupodBot k) (CupodBot k) Action.D
  (∀ k, k > 0 → ∃ m, proofSearch m (.impl (.box (k) (φ k)) (φ k)) = true) := by
  dsimp
  intro k _hk
  let ψ := Formula.plays (CupodBot k) (CupodBot k) Action.D

  -- First prove the semantic version of the self-fulfilling implication.
  -- Semantically, `.box k ψ` means exactly `proofSearch k ψ = true`.
  -- By proof-search soundness, any such proof-search success implies `ψ.interp`.
  have hSemantic : (Formula.impl (Formula.box k ψ) ψ).interp := by
    intro hBox
    exact proofSearch_sound k ψ hBox

  -- Blocking step: to finish the PBLT hypothesis, we need this semantic
  -- implication to be provable in the abstract proof system `S`.
  --
  -- The existing completeness theorem only applies when the outer formula is
  -- `.plays`.  Here the outer formula is `.impl`, so this step needs either a
  -- concrete proof system for `S` or an additional axiom/completeness principle
  -- for this kind of implication.
  have hProvable :
      ∃ m, proofSearch m (Formula.impl (Formula.box k ψ) ψ) = true := proofSearch_CupodBot_self_fulfilling k

  -- Unfold the local abbreviation `ψ` so the result matches the statement.
  simpa [ψ] using hProvable


theorem CupodBot_vs_CupodBot (fuel : Nat) :
    ∃ k, outcome (fuel + 2) (CupodBot k) (CupodBot k) = some (.D, .D) := by
    -- We instantiate PBLT with the formula saying that `CupodBot k` defects
    -- against itself.  The function `f k = k` matches CUPOD's proof-search
    -- budget, because `CupodBot k` searches with exactly fuel `k`.
    let φ := fun k : Nat => Formula.plays (CupodBot k) (CupodBot k) Action.D
    let f := fun x : Nat => x
    let k₁ := 0

    -- `f` is monotone since it is just the identity function.
    have hf_mono : ∀ a b : Nat, a ≤ b → f a ≤ f b := by
      intro a b hab
      exact hab

    -- These are the remaining PBLT hypotheses: enough growth for `f`, and
    -- derivability of Löb-style implications for all sufficiently large `k`.
    have hf_growth :
      ∃ c kHat, c > 0 ∧ ∀ k, k > kHat → f k > c * Nat.log2 k := linear_function_growth
    have hproofSearch :
      (∀ k, k > k₁ → ∃ m, proofSearch m (.impl (.box (f k) (φ k)) (φ k)) = true) := formula_self_fulfilling

    -- PBLT gives a threshold `k₂`: every `k` above it has some proof-search
    -- fuel `m` proving `φ k`.
    have pblt := PBLT φ f k₁ hf_mono hf_growth hproofSearch
    obtain ⟨k₂, hk⟩ := pblt

    -- Start with any index above the PBLT threshold.  This `k₀` is only a
    -- temporary index used to extract an initial proof-search witness.
    let k₀ := Nat.succ k₂
    have hk₀_gt : k₀ > k₂ := by
      exact Nat.lt_succ_self k₂

    -- Specializing `hk` at `k₀` gives a proof-search success for `φ k₀`, but
    -- with an unknown fuel `m`.
    obtain ⟨m, hm⟩ := hk k₀ hk₀_gt

    -- CUPOD's own search budget must equal its index.  Since `hm` only proves
    -- success at fuel `m`, choose the final CUPOD index `k` large enough for
    -- both the original index `k₀` and the fuel `m`.
    let k := k₀ + m
    have hk₀_le_k : k₀ ≤ k := by
      exact Nat.le_add_right k₀ m
    have hm_le_k : m ≤ k := by
      exact Nat.le_add_left m k₀

    -- Lift the proof-search success from `proofSearch m (φ k₀)` to
    -- `proofSearch k (φ k)`.  This happens in two steps:
    -- first increase the proof-search fuel from `m` to `k`, then transport the
    -- indexed formula from `k₀` to the larger index `k`.
    have hSearchK : proofSearch k (φ k) = true := by
      let Φ : Nat → Formula := fun i => φ i
      have hmK : proofSearch k (Φ k₀) = true :=
        proofSearch_monotone m k (Φ k₀) hm_le_k hm
      obtain ⟨w, hw, hwk⟩ := (proofSearch_spec k (Φ k₀)).1 hmK
      obtain ⟨w', hw', hwk'⟩ := witness_transport_family Φ k₀ k hk₀_le_k w hw hwk
      exact (proofSearch_spec k (Φ k)).2 ⟨w', hw', hwk'⟩

    -- Use this final `k` as the witness for the theorem.
    refine ⟨k, ?_⟩

    -- With `hSearchK`, both CUPOD bots see their search guard succeed, so the
    -- evaluated action is `.D`.
    have hA : play (fuel + 2) (CupodBot k) (CupodBot k) = some .D := by
      show eval (fuel + 2) (CupodBot k) (CupodBot k) (CupodBot k) = some .D
      unfold φ at hSearchK
      unfold CupodBot at hSearchK ⊢
      simp [eval, Prog.subst, Formula.subst, hSearchK]

    -- The two sides of the outcome are identical plays, so `hA` resolves both.
    exact outcome_of_plays _ _ _ _ _ hA hA


end PDNew.Theorems
