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

theorem CupodBot_plays_C_against_CooperateBot (k fuel : Nat) :
    play (fuel + 2) (CupodBot k) CooperateBot = some .C := by
  -- `guard_false` tells us the proof search for “CooperateBot plays D” fails.
  -- Once we unfold the bot, the remaining `simp` can simplify the search node
  -- and the constant branch all the way down to `.C`.
  have hg := proofSearch_false_for_CooperateBot k
  show eval (fuel + 2) (CupodBot k) CooperateBot (CupodBot k) = some .C
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
  simp [outcome, hA, hB]


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

theorem CupodBot_plays_D_against_DefectBot (k fuel : Nat)
    (hk : proofSearch k (.plays DefectBot (CupodBot k) .D) = true) :
    play (fuel + 2) (CupodBot k) DefectBot = some .D := by
  show eval (fuel + 2) (CupodBot k) DefectBot (CupodBot k) = some .D
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

  simp [outcome, hA, hB]


-- TitForTatBot --

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


-- DBot --

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


-- OBot --

theorem OBot_plays_D_against_CupodBot (k fuel : Nat)
    (hk : proofSearch k (.plays DefectBot (CupodBot k) .D) = true) :
    play (fuel + 5) OBot (CupodBot k) = some .D := by
  have hGuard1 :
      eval (fuel + 4) OBot (CupodBot k) (.sim .opp CooperateBot) = some .C := by
    have hProbe : play (fuel + 3) (CupodBot k) CooperateBot = some .C := by
      simpa [Nat.add_assoc] using CupodBot_plays_C_against_CooperateBot k (fuel + 1)
    simpa [eval, Prog.subst, play, CooperateBot] using hProbe
  have hGuard2 :
      eval (fuel + 3) OBot (CupodBot k) (.sim .opp DefectBot) = some .D := by
    have hProbe : play (fuel + 2) (CupodBot k) DefectBot = some .D :=
      CupodBot_plays_D_against_DefectBot k fuel hk
    simpa [eval, Prog.subst, play, DefectBot] using hProbe
  have hPlay := play_ite_from_guard
    fuel 4 OBot (CupodBot k) (.sim .opp CooperateBot)
    (.ite (.sim .opp DefectBot) Action.C (.const Action.C) (.const Action.D))
    (.const Action.D)
    Action.C Action.C
    (by rfl) hGuard1
  have hInner :
      eval (fuel + 4) OBot (CupodBot k)
        (.ite (.sim .opp DefectBot) Action.C (.const Action.C) (.const Action.D)) =
          some .D := by
    have hGuard2' :
        eval (fuel + 3)
          (.ite (.sim .opp DefectBot) Action.C (.const Action.C) (.const Action.D))
          (CupodBot k) (.sim .opp DefectBot) = some .D := by
      simpa [eval, Prog.subst, play, DefectBot] using hGuard2
    have hPlay := play_ite_from_guard
      fuel 3
      (.ite (.sim .opp DefectBot) Action.C (.const Action.C) (.const Action.D))
      (CupodBot k) (.sim .opp DefectBot)
      (.const Action.C) (.const Action.D)
      Action.C Action.D
      (by rfl) hGuard2'
    simpa [play, eval, Prog.subst] using hPlay
  simpa [hInner] using hPlay

theorem proofSearch_true_for_OBot_different_k:
    ∃ k n, proofSearch k (.plays OBot (CupodBot n) .D) = true := by
  have hex : ∃ m n, play m OBot (CupodBot n) = some .D := by
    -- We want to use OBot plays D against CupodBot n, but we need to have hk
    have hk := proofSearch_true_for_DefectBot
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
  obtain ⟨d, hd⟩ := proofSearch_true_for_DefectBot

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
  have hkDefect : proofSearch k (.plays DefectBot (CupodBot k) .D) = true :=
    CupodBot_monotonicity d k DefectBot .D hdk
      (proofSearch_monotone d k (.plays DefectBot (CupodBot d) .D) hdk hd)
  refine ⟨k, ?_⟩

  -- CUPOD defects against OBot because `hkOBot` makes its search guard true.
  have hA : play (fuel + 5) (CupodBot k) OBot = some .D :=
    CupodBot_plays_D_against_OBot fuel k hkOBot

  -- OBot defects against CUPOD because `hkDefect` makes CUPOD defect against
  -- DefectBot, so OBot's inner probe follows its defect branch.
  have hB : play (fuel + 5) OBot (CupodBot k) = some .D := by
    exact OBot_plays_D_against_CupodBot k fuel hkDefect
  simp [outcome, hA, hB]


-- CupodBot --



end PDNew.Theorems
