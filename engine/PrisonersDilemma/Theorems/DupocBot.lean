import PrisonersDilemma.Program
import PrisonersDilemma.Derivation
import PrisonersDilemma.Axioms
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Bots.DupocBot
import PrisonersDilemma.Bots.DBot
import PrisonersDilemma.Bots.OBot
import PrisonersDilemma.Bots.TitForTatBot
import PrisonersDilemma.Bots.EBot
import PrisonersDilemma.Bots.MirrorBot
import PrisonersDilemma.Theorems.CooperateBot
import PrisonersDilemma.Theorems.DefectBot
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Theorems.Helpers
import PrisonersDilemma.Theorems.ProofSearch

open PD
open PD.Axioms
open PD.Bots
namespace PD.Theorems

/-- Monotonicity of Dupoc bot: If the proof search succeeds with less fuel, it also succeeds with more fuel -/
theorem DupocBot_monotonicity (n k : Nat) (Bot : Prog) (a : Action) :
    n ≤ k →
    proofSearch k (.plays Bot (DupocBot n) a) = true →
    proofSearch k (.plays Bot (DupocBot k) a) = true := by
  intro hle hnk
  let Φ : Nat → Formula := fun i => Formula.plays Bot (DupocBot i) a
  have hn : Provable k (Φ n) := (proofSearch_spec k (Φ n)).1 hnk
  exact (proofSearch_spec k (Φ k)).2 (Provable_transport_family Φ n k hle hn)


/-- Proof search is false for DefectBot -/
theorem proofSearch_false_for_DefectBot (k : Nat) :
    proofSearch k (.plays DefectBot (DupocBot k) .C) = false := by
  cases h : proofSearch k (.plays DefectBot (DupocBot k) .C) with
  | true  => exact absurd (proofSearch_sound _ _ h)
                          (interp_DefectBot_plays_C_false _)
  | false => rfl

/-- Proof search k is true for CooperateBot vs Dupoc n, but n ≠ k -/
theorem proofSearch_true_for_CooperateBot_different_k (n: Nat) :
    ∃ k, proofSearch k (.plays CooperateBot (DupocBot n) .C) = true := by
  -- Show that there exists n such that play n CooperateBot (DupocBot n) = some .C
  have hex : ∃ m, play m CooperateBot (DupocBot n) = some .C := by
    -- Use the fact that CooperateBot always plays .C
    exists 1
  -- Now apply the restricted completeness theorem
  have h := proofSearch_complete_plays CooperateBot (DupocBot n) .C hex
  obtain ⟨k, hk⟩ := h
  exact ⟨k, hk⟩

/-- Proof search k is true for CooperateBot vs Dupoc k -/
theorem proofSearch_true_for_CooperateBot :
    ∃ k, proofSearch k (.plays CooperateBot (DupocBot k) .C) = true := by
  have h := proofSearch_true_for_CooperateBot_different_k
  obtain ⟨k, hk⟩ := h 0 -- we can pick any n, so we pick 0 for simplicity; k is the corresponding k from the lemma.
  refine ⟨k, ?_⟩ -- use the same k for the conclusion
  exact DupocBot_monotonicity 0 k CooperateBot .C (Nat.zero_le k) hk


/-- DupocBot vs DefectBot: uses proof search being false -/
theorem DupocBot_vs_DefectBot (k fuel : Nat):
    outcome (fuel + 2) (DupocBot k) DefectBot = some (.D, .D) := by
  -- Left side: Dupoc executes its `.search` guard. The guard is false by the
  -- lemma above, so the `search` falls through to the final `.const .D` branch.
  have hA : play (fuel + 2) (DupocBot k) DefectBot = some .D := by
    show eval (fuel + 2) (DupocBot k) DefectBot (DupocBot k) = some .D
    -- `guard_false` tells us the proof search for “DefectBot plays C” fails.
    -- Once we unfold the bot, the remaining `simp` can simplify the search node
    -- and the constant branch all the way down to `.D`.
    have hg := proofSearch_false_for_DefectBot k
    unfold DupocBot at hg ⊢
    simp [eval, Prog.subst, Formula.subst, hg]
  -- Right side: DefectBot is definitionally the constant `.D` bot.
  have hB : play (fuel + 2) DefectBot (DupocBot k) = some .D := rfl
  -- Finally, `outcome` just packages the two `play` results together.
  simp [outcome, hA, hB]

/-- DupocBot vs CooperateBot: uses proof search being true -/
theorem DupocBot_vs_CooperateBot (fuel : Nat):
    ∃ k, outcome (fuel + 2) (DupocBot k) CooperateBot = some (.C, .C) := by
  obtain ⟨k, hk⟩ := proofSearch_true_for_CooperateBot
  refine ⟨k, ?_⟩

  have hA : play (fuel + 2) (DupocBot k) CooperateBot = some .C := by
    show eval (fuel + 2) (DupocBot k) CooperateBot (DupocBot k) = some .C
    unfold DupocBot at hk ⊢
    simp [eval, Prog.subst, Formula.subst, hk]

  have hB : play (fuel + 2) CooperateBot (DupocBot k) = some .C := by
    simpa [Nat.add_assoc] using (play_CooperateBot (fuel + 1) (DupocBot k))

  simp [outcome, hA, hB]


-- DBot --

/-- Proof search is false for `.bot DefectBot` against DupocBot: `.bot DefectBot`
    can never play C, so the proof search must fail. -/
theorem proofSearch_false_for_bot_DefectBot (k : Nat) :
    proofSearch k (.plays (.bot DefectBot) (DupocBot k) .C) = false := by
  cases h : proofSearch k (.plays (.bot DefectBot) (DupocBot k) .C) with
  | true  => exact absurd (proofSearch_sound _ _ h)
                          (interp_bot_DefectBot_plays_C_false _)
  | false => rfl

/-- DupocBot defects against `.bot DefectBot` because the search guard fails. -/
theorem DupocBot_plays_D_against_bot_DefectBot (k fuel : Nat) :
    play (fuel + 2) (DupocBot k) (.bot DefectBot) = some .D := by
  have hg := proofSearch_false_for_bot_DefectBot k
  show eval (fuel + 2) (DupocBot k) (.bot DefectBot) (DupocBot k) = some .D
  unfold DupocBot at hg ⊢
  simp [eval, Prog.subst, Formula.subst, hg]

/-- DBot probes its opponent against `.bot DefectBot`; DupocBot defects on that
    probe, so DBot's `ite` selects the cooperate branch. -/
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

/-- Proof search is true for DBot vs DupocBot n, for some k (n ≠ k in general). -/
theorem proofSearch_true_for_DBot_different_k (n : Nat) :
    ∃ k, proofSearch k (.plays DBot (DupocBot n) .C) = true := by
  have hex : ∃ m, play m DBot (DupocBot n) = some .C :=
    ⟨4, by simpa using DBot_plays_C_against_DupocBot n 0⟩
  exact proofSearch_complete_plays DBot (DupocBot n) .C hex

/-- Proof search k is true for DBot vs Dupoc k. -/
theorem proofSearch_true_for_DBot :
    ∃ k, proofSearch k (.plays DBot (DupocBot k) .C) = true := by
  obtain ⟨k, hk⟩ := proofSearch_true_for_DBot_different_k 0
  refine ⟨k, ?_⟩
  exact DupocBot_monotonicity 0 k DBot .C (Nat.zero_le k) hk

/-- DupocBot vs DBot: mutual cooperation. DupocBot's search succeeds (DBot does
    cooperate against it), and DBot's probe sees DupocBot defect against
    DefectBot, so DBot cooperates. -/
theorem DupocBot_vs_DBot (fuel : Nat) :
    ∃ k, outcome (fuel + 4) (DupocBot k) DBot = some (.C, .C) := by
  obtain ⟨k, hk⟩ := proofSearch_true_for_DBot
  refine ⟨k, ?_⟩
  have hA : play (fuel + 4) (DupocBot k) DBot = some .C := by
    show eval (fuel + 4) (DupocBot k) DBot (DupocBot k) = some .C
    unfold DupocBot at hk ⊢
    simp [eval, Prog.subst, Formula.subst, hk]
  have hB : play (fuel + 4) DBot (DupocBot k) = some .C :=
    DBot_plays_C_against_DupocBot k fuel
  exact outcome_of_plays _ _ _ _ _ hA hB


-- OBot --

/-- DupocBot cooperates with `.bot CooperateBot` once its search guard succeeds. -/
theorem DupocBot_plays_C_against_bot_CooperateBot (k fuel : Nat)
    (hk : proofSearch k (.plays (.bot CooperateBot) (DupocBot k) .C) = true) :
    play (fuel + 2) (DupocBot k) (.bot CooperateBot) = some .C := by
  show eval (fuel + 2) (DupocBot k) (.bot CooperateBot) (DupocBot k) = some .C
  unfold DupocBot at hk ⊢
  simp [eval, Prog.subst, Formula.subst, hk]

/-- OBot defects against DupocBot: outer probe sees DupocBot cooperate against
    `.bot CooperateBot` (search succeeds), so OBot descends into the inner ite.
    The inner probe sees DupocBot defect against `.bot DefectBot` (search fails),
    so OBot takes the defect branch. -/
theorem OBot_plays_D_against_DupocBot (k fuel : Nat)
    (hCB : proofSearch k (.plays (.bot CooperateBot) (DupocBot k) .C) = true) :
    play (fuel + 5) OBot (DupocBot k) = some .D := by
  have hDupocC : play (fuel + 3) (DupocBot k) (.bot CooperateBot) = some .C := by
    simpa [Nat.add_assoc] using DupocBot_plays_C_against_bot_CooperateBot k (fuel + 1) hCB
  have hOuterGuard :
      eval (fuel + 4) OBot (DupocBot k) (.sim .opp (.bot CooperateBot)) = some .C := by
    simpa [Nat.add_assoc] using
      (eval_sim_opp_bot_of_play (fuel + 3) OBot (DupocBot k) CooperateBot Action.C hDupocC)
  have hDupocD : play (fuel + 2) (DupocBot k) (.bot DefectBot) = some .D :=
    DupocBot_plays_D_against_bot_DefectBot k fuel
  have hInnerGuard :
      eval (fuel + 3) OBot (DupocBot k) (.sim .opp (.bot DefectBot)) = some .D := by
    simpa [Nat.add_assoc] using
      (eval_sim_opp_bot_of_play (fuel + 2) OBot (DupocBot k) DefectBot Action.D hDupocD)
  have hPlay := play_ite_from_guard
    fuel 4 OBot (DupocBot k) (.sim .opp (.bot CooperateBot))
    (.ite (.sim .opp (.bot DefectBot)) Action.C (.const Action.C) (.const Action.D))
    (.const Action.D)
    Action.C Action.C
    (by rfl) hOuterGuard
  have hInner :
      eval (fuel + 4) OBot (DupocBot k)
        (.ite (.sim .opp (.bot DefectBot)) Action.C (.const Action.C) (.const Action.D)) =
          some .D := by
    simpa [Nat.add_assoc] using
      (eval_ite_from_guard (fuel + 3) OBot (DupocBot k)
        (.sim .opp (.bot DefectBot)) (.const Action.C) (.const Action.D)
        Action.C Action.D hInnerGuard)
  simpa [hInner] using hPlay

/-- Semantically, OBot never plays C against DupocBot (given the `.bot CB`
    proof-search succeeds). -/
theorem interp_OBot_plays_C_false (k : Nat)
    (hCB : proofSearch k (.plays (.bot CooperateBot) (DupocBot k) .C) = true) :
    ¬ (Formula.plays OBot (DupocBot k) .C).interp := by
  rintro ⟨n, hn⟩
  have hDB : proofSearch k (.plays (.bot DefectBot) (DupocBot k) .C) = false :=
    proofSearch_false_for_bot_DefectBot k
  cases n with
  | zero => simp only [play, eval, reduceCtorEq] at hn
  | succ m =>
      cases m with
      | zero => simp [play, eval, OBot] at hn
      | succ m =>
          cases m with
          | zero => simp [play, eval, OBot] at hn
          | succ m =>
              cases m with
              | zero =>
                  simp [play, eval, OBot, DupocBot, Prog.subst, Formula.subst] at hn
              | succ fuel =>
                  cases fuel with
                  | zero =>
                      unfold DupocBot at hCB hDB
                      simp [play, eval, OBot, DupocBot, Prog.subst, Formula.subst, hCB, hDB] at hn
                  | succ fuel =>
                      have hD : play (fuel + 5) OBot (DupocBot k) = some .D := by
                        simpa [Nat.add_assoc] using OBot_plays_D_against_DupocBot k fuel hCB
                      rw [hD] at hn
                      cases hn

/-- Proof search is false for OBot vs DupocBot k, given the `.bot CB` search succeeds. -/
theorem proofSearch_false_for_OBot (k : Nat)
    (hCB : proofSearch k (.plays (.bot CooperateBot) (DupocBot k) .C) = true) :
    proofSearch k (.plays OBot (DupocBot k) .C) = false := by
  cases h : proofSearch k (.plays OBot (DupocBot k) .C) with
  | true => exact absurd (proofSearch_sound _ _ h) (interp_OBot_plays_C_false k hCB)
  | false => rfl

/-- DupocBot defects against OBot: its search for "OBot plays C" fails, so it
    falls through to the defect branch. -/
theorem DupocBot_plays_D_against_OBot (k fuel : Nat)
    (hCB : proofSearch k (.plays (.bot CooperateBot) (DupocBot k) .C) = true) :
    play (fuel + 2) (DupocBot k) OBot = some .D := by
  have hOBot : proofSearch k (.plays OBot (DupocBot k) .C) = false :=
    proofSearch_false_for_OBot k hCB
  show eval (fuel + 2) (DupocBot k) OBot (DupocBot k) = some .D
  unfold DupocBot at hOBot ⊢
  simp [eval, Prog.subst, Formula.subst, hOBot]

/-- Proof search is true for `.bot CooperateBot` vs DupocBot n, but n ≠ k. -/
theorem proofSearch_true_for_bot_CooperateBot_different_k (n : Nat) :
    ∃ k, proofSearch k (.plays (.bot CooperateBot) (DupocBot n) .C) = true := by
  have hex : ∃ m, play m (.bot CooperateBot) (DupocBot n) = some .C :=
    ⟨2, by simpa using play_bot_CooperateBot 0 (DupocBot n)⟩
  exact proofSearch_complete_plays (.bot CooperateBot) (DupocBot n) .C hex

/-- Proof search k is true for `.bot CooperateBot` vs DupocBot k. -/
theorem proofSearch_true_for_bot_CooperateBot :
    ∃ k, proofSearch k (.plays (.bot CooperateBot) (DupocBot k) .C) = true := by
  obtain ⟨k, hk⟩ := proofSearch_true_for_bot_CooperateBot_different_k 0
  refine ⟨k, ?_⟩
  exact DupocBot_monotonicity 0 k (.bot CooperateBot) .C (Nat.zero_le k) hk

/-- DupocBot vs OBot: mutual defection. -/
theorem DupocBot_vs_OBot (fuel : Nat) :
    ∃ k, outcome (fuel + 5) (DupocBot k) OBot = some (.D, .D) := by
  obtain ⟨k, hk⟩ := proofSearch_true_for_bot_CooperateBot
  refine ⟨k, ?_⟩
  have hA : play (fuel + 5) (DupocBot k) OBot = some .D := by
    simpa [Nat.add_assoc] using DupocBot_plays_D_against_OBot k (fuel + 3) hk
  have hB : play (fuel + 5) OBot (DupocBot k) = some .D :=
    OBot_plays_D_against_DupocBot k fuel hk
  exact outcome_of_plays _ _ _ _ _ hA hB


-- TitForTatBot --

/-- TitForTatBot cooperates with DupocBot: its probe sees DupocBot cooperate
    against `.bot CooperateBot` (search succeeds), so the `ite` selects the
    cooperate branch. -/
theorem TitForTatBot_plays_C_against_DupocBot (k fuel : Nat)
    (hCB : proofSearch k (.plays (.bot CooperateBot) (DupocBot k) .C) = true) :
    play (fuel + 4) TitForTatBot (DupocBot k) = some .C := by
  have hDupocC : play (fuel + 2) (DupocBot k) (.bot CooperateBot) = some .C :=
    DupocBot_plays_C_against_bot_CooperateBot k fuel hCB
  have hGuard :
      eval (fuel + 3) TitForTatBot (DupocBot k) (.sim .opp (.bot CooperateBot)) = some .C := by
    simpa [Nat.add_assoc] using
      (eval_sim_opp_bot_of_play (fuel + 2) TitForTatBot (DupocBot k) CooperateBot Action.C hDupocC)
  have hPlay := play_ite_from_guard
    fuel 3 TitForTatBot (DupocBot k) (.sim .opp (.bot CooperateBot))
    (.const Action.C) (.const Action.D)
    Action.C Action.C
    (by rfl) hGuard
  simpa [eval] using hPlay

/-- Existence of a `(k, n)` for which proof search verifies "TFT plays C vs
    DupocBot n". The Dupoc index `n` is the witness from
    `proofSearch_true_for_bot_CooperateBot` so that TFT's probe fires. -/
theorem proofSearch_true_for_TitForTatBot_different_k :
    ∃ k n, proofSearch k (.plays TitForTatBot (DupocBot n) .C) = true := by
  obtain ⟨c, hc⟩ := proofSearch_true_for_bot_CooperateBot
  have hPlay : play 4 TitForTatBot (DupocBot c) = some .C := by
    simpa using TitForTatBot_plays_C_against_DupocBot c 0 hc
  obtain ⟨k, hk⟩ :=
    proofSearch_complete_plays TitForTatBot (DupocBot c) .C ⟨4, hPlay⟩
  exact ⟨k, c, hk⟩

/-- Proof search k is true for TFT vs DupocBot k. Aligns the indices via
    monotonicity (Dupoc-side or proof-search-side, depending on which is
    larger). -/
theorem proofSearch_true_for_TitForTatBot :
    ∃ k, proofSearch k (.plays TitForTatBot (DupocBot k) .C) = true := by
  obtain ⟨k, n, hk⟩ := proofSearch_true_for_TitForTatBot_different_k
  by_cases hnk : n ≤ k
  · refine ⟨k, ?_⟩
    exact DupocBot_monotonicity n k TitForTatBot .C hnk hk
  · refine ⟨n, ?_⟩
    exact proofSearch_monotone k n (.plays TitForTatBot (DupocBot n) .C)
      (Nat.le_of_lt (Nat.lt_of_not_ge hnk)) hk

/-- DupocBot cooperates with TFT once its search for "TFT plays C" succeeds. -/
theorem DupocBot_plays_C_against_TitForTatBot (k fuel : Nat)
    (hk : proofSearch k (.plays TitForTatBot (DupocBot k) .C) = true) :
    play (fuel + 2) (DupocBot k) TitForTatBot = some .C := by
  show eval (fuel + 2) (DupocBot k) TitForTatBot (DupocBot k) = some .C
  unfold DupocBot at hk ⊢
  simp [eval, Prog.subst, Formula.subst, hk]

/-- DupocBot vs TitForTatBot: mutual cooperation. Combine two proof-search
    witnesses (one for `.bot CB`, one for TFT) at a common `k = t + c`. -/
theorem DupocBot_vs_TitForTatBot (fuel : Nat) :
    ∃ k, outcome (fuel + 4) (DupocBot k) TitForTatBot = some (.C, .C) := by
  obtain ⟨t, ht⟩ := proofSearch_true_for_TitForTatBot
  obtain ⟨c, hc⟩ := proofSearch_true_for_bot_CooperateBot
  let k := t + c
  have htk : t ≤ k := Nat.le_add_right t c
  have hck : c ≤ k := Nat.le_add_left c t
  have hkTFT : proofSearch k (.plays TitForTatBot (DupocBot k) .C) = true :=
    DupocBot_monotonicity t k TitForTatBot .C htk
      (proofSearch_monotone t k (.plays TitForTatBot (DupocBot t) .C) htk ht)
  have hkCB : proofSearch k (.plays (.bot CooperateBot) (DupocBot k) .C) = true :=
    DupocBot_monotonicity c k (.bot CooperateBot) .C hck
      (proofSearch_monotone c k (.plays (.bot CooperateBot) (DupocBot c) .C) hck hc)
  refine ⟨k, ?_⟩
  have hA : play (fuel + 4) (DupocBot k) TitForTatBot = some .C := by
    simpa [Nat.add_assoc] using DupocBot_plays_C_against_TitForTatBot k (fuel + 2) hkTFT
  have hB : play (fuel + 4) TitForTatBot (DupocBot k) = some .C :=
    TitForTatBot_plays_C_against_DupocBot k fuel hkCB
  exact outcome_of_plays _ _ _ _ _ hA hB


-- EBot --

/-- EBot cooperates with DupocBot: outer probe (`.bot DefectBot`) sees DupocBot
    defect (always), so EBot descends into the inner ite. The next probe
    (`.bot CooperateBot`) sees DupocBot cooperate (search succeeds), so EBot
    cooperates. -/
theorem EBot_plays_C_against_DupocBot (k fuel : Nat)
    (hCB : proofSearch k (.plays (.bot CooperateBot) (DupocBot k) .C) = true) :
    play (fuel + 5) EBot (DupocBot k) = some .C := by
  have hDupocD : play (fuel + 3) (DupocBot k) (.bot DefectBot) = some .D := by
    simpa [Nat.add_assoc] using DupocBot_plays_D_against_bot_DefectBot k (fuel + 1)
  have hGuard1 :
      eval (fuel + 4) EBot (DupocBot k) (.sim .opp (.bot DefectBot)) = some .D := by
    simpa [Nat.add_assoc] using
      (eval_sim_opp_bot_of_play (fuel + 3) EBot (DupocBot k) DefectBot Action.D hDupocD)
  have hDupocC : play (fuel + 2) (DupocBot k) (.bot CooperateBot) = some .C :=
    DupocBot_plays_C_against_bot_CooperateBot k fuel hCB
  have hGuard2 :
      eval (fuel + 3) EBot (DupocBot k) (.sim .opp (.bot CooperateBot)) = some .C := by
    simpa [Nat.add_assoc] using
      (eval_sim_opp_bot_of_play (fuel + 2) EBot (DupocBot k) CooperateBot Action.C hDupocC)
  have hInner :
      eval (fuel + 4) EBot (DupocBot k)
        (.ite (.sim .opp (.bot CooperateBot)) Action.C (.const Action.C)
          (.ite (.sim .opp (.bot MirrorBot)) Action.C (.const Action.C) (.const Action.D))) =
        some .C := by
    simpa [Nat.add_assoc] using
      (eval_ite_from_guard (fuel + 3) EBot (DupocBot k)
        (.sim .opp (.bot CooperateBot)) (.const Action.C)
        (.ite (.sim .opp (.bot MirrorBot)) Action.C (.const Action.C) (.const Action.D))
        Action.C Action.C hGuard2)
  have hPlay := play_ite_from_guard
    fuel 4 EBot (DupocBot k) (.sim .opp (.bot DefectBot))
    (.const Action.D)
    (.ite (.sim .opp (.bot CooperateBot)) Action.C (.const Action.C)
      (.ite (.sim .opp (.bot MirrorBot)) Action.C (.const Action.C) (.const Action.D)))
    Action.C Action.D
    (by rfl) hGuard1
  simpa [Nat.add_assoc, hInner] using hPlay

/-- Existence of `(k, n)` for which proof search verifies "EBot plays C vs
    DupocBot n". The Dupoc index is the witness from
    `proofSearch_true_for_bot_CooperateBot` so EBot's inner probe fires. -/
theorem proofSearch_true_for_EBot_different_k :
    ∃ k n, proofSearch k (.plays EBot (DupocBot n) .C) = true := by
  obtain ⟨c, hc⟩ := proofSearch_true_for_bot_CooperateBot
  have hPlay : play 5 EBot (DupocBot c) = some .C := by
    simpa using EBot_plays_C_against_DupocBot c 0 hc
  obtain ⟨k, hk⟩ :=
    proofSearch_complete_plays EBot (DupocBot c) .C ⟨5, hPlay⟩
  exact ⟨k, c, hk⟩

/-- Proof search k is true for EBot vs DupocBot k. Aligns indices via
    monotonicity. -/
theorem proofSearch_true_for_EBot :
    ∃ k, proofSearch k (.plays EBot (DupocBot k) .C) = true := by
  obtain ⟨k, n, hk⟩ := proofSearch_true_for_EBot_different_k
  by_cases hnk : n ≤ k
  · refine ⟨k, ?_⟩
    exact DupocBot_monotonicity n k EBot .C hnk hk
  · refine ⟨n, ?_⟩
    exact proofSearch_monotone k n (.plays EBot (DupocBot n) .C)
      (Nat.le_of_lt (Nat.lt_of_not_ge hnk)) hk

/-- DupocBot cooperates with EBot once its search for "EBot plays C" succeeds. -/
theorem DupocBot_plays_C_against_EBot (k fuel : Nat)
    (hk : proofSearch k (.plays EBot (DupocBot k) .C) = true) :
    play (fuel + 2) (DupocBot k) EBot = some .C := by
  show eval (fuel + 2) (DupocBot k) EBot (DupocBot k) = some .C
  unfold DupocBot at hk ⊢
  simp [eval, Prog.subst, Formula.subst, hk]

/-- DupocBot vs EBot: mutual cooperation. Combine two proof-search witnesses
    (one for `.bot CB`, one for EBot) at a common `k = e + c`. -/
theorem DupocBot_vs_EBot (fuel : Nat) :
    ∃ k, outcome (fuel + 5) (DupocBot k) EBot = some (.C, .C) := by
  obtain ⟨e, he⟩ := proofSearch_true_for_EBot
  obtain ⟨c, hc⟩ := proofSearch_true_for_bot_CooperateBot
  let k := e + c
  have hek : e ≤ k := Nat.le_add_right e c
  have hck : c ≤ k := Nat.le_add_left c e
  have hkEBot : proofSearch k (.plays EBot (DupocBot k) .C) = true :=
    DupocBot_monotonicity e k EBot .C hek
      (proofSearch_monotone e k (.plays EBot (DupocBot e) .C) hek he)
  have hkCB : proofSearch k (.plays (.bot CooperateBot) (DupocBot k) .C) = true :=
    DupocBot_monotonicity c k (.bot CooperateBot) .C hck
      (proofSearch_monotone c k (.plays (.bot CooperateBot) (DupocBot c) .C) hck hc)
  refine ⟨k, ?_⟩
  have hA : play (fuel + 5) (DupocBot k) EBot = some .C := by
    simpa [Nat.add_assoc] using DupocBot_plays_C_against_EBot k (fuel + 3) hkEBot
  have hB : play (fuel + 5) EBot (DupocBot k) = some .C :=
    EBot_plays_C_against_DupocBot k fuel hkCB
  exact outcome_of_plays _ _ _ _ _ hA hB


-- DupocBot --

/-- DUPOC-specific Löb premise (critch22 Theorem 3.7 substitution into PBLT).
    Instantiates `proof_system_verifies_search_branch` with
    ψ = "opp(self.source) == C", a = .C, b = .D, me = opp = DupocBot k.
    The closed guard `ψ.subst (DupocBot k) (DupocBot k)` reduces to
    `.plays (DupocBot k) (DupocBot k) .C`. -/
theorem dupoc_loeb_premise (k : Nat) :
    ∃ m, proofSearch m
      (.impl (.box k (.plays (DupocBot k) (DupocBot k) .C))
             (.plays (DupocBot k) (DupocBot k) .C)) = true := by
  have h := proof_system_verifies_search_branch
              k (.plays .opp .self .C) .C .D
              (DupocBot k) (DupocBot k) rfl
  simpa [Formula.subst, Prog.subst] using h

/-- DUPOC self-play cooperates, for `k` large enough — critch22 Theorem 3.7.
    Direct application of PBLT with `φ k = .plays (DupocBot k) (DupocBot k) .C`,
    `f = id`, `k₁ = 0`. The Löb premise comes from `dupoc_loeb_premise`,
    soundness collapses bounded provability to a `play` witness, and self-play
    symmetry makes the same `play` discharge both legs of `outcome`. -/
theorem DupocBot_vs_DupocBot :
    ∃ k₂, ∀ k, k₂ < k →
      ∃ fuel, outcome fuel (DupocBot k) (DupocBot k) = some (.C, .C) := by
  let φ : Nat → Formula := fun k => .plays (DupocBot k) (DupocBot k) .C
  have hMono : ∀ a b : Nat, a ≤ b → id a ≤ id b := fun _ _ h => h
  have hLog : ∃ c kHat, c > 0 ∧ ∀ k, k > kHat → id k > c * Nat.log2 k := by
    refine ⟨1, 0, Nat.zero_lt_one, ?_⟩
    intro k hk
    have hlog : Nat.log2 k < k := by
      rw [Nat.log2_lt (Nat.pos_iff_ne_zero.mp hk)]
      exact Nat.lt_two_pow_self
    simpa using hlog
  have hLoeb :
      ∀ k, k > 0 →
        ∃ m, proofSearch m (.impl (.box (id k) (φ k)) (φ k)) = true := by
    intro k _
    simpa using dupoc_loeb_premise k
  obtain ⟨k₂, hk₂⟩ := PBLT φ id 0 hMono hLog hLoeb
  refine ⟨k₂, ?_⟩
  intro k hk
  obtain ⟨m, hm⟩ := hk₂ k hk
  have hInterp : (φ k).interp := proofSearch_sound m (φ k) hm
  obtain ⟨n, hn⟩ := hInterp
  refine ⟨n, ?_⟩
  simp [outcome, hn]


-- MirrorBot --

/-- Löb premise for DupocBot vs MirrorBot. Combines source-code transparency
    of DupocBot's `.search` body (`□_k φ_A → φ_B`) with `.sim` source
    transparency for MirrorBot (`φ_B → φ_A`), chained by `Derivation.hypSyll`
    into the closed `□_k φ → φ` that PBLT requires. (Symmetric to
    `cupod_mirror_loeb_premise`.) -/
theorem dupoc_mirror_loeb_premise (k : Nat) :
    ∃ m, proofSearch m
      (.impl (.box k (.plays MirrorBot (DupocBot k) .C))
             (.plays MirrorBot (DupocBot k) .C)) = true := by
  let dS : Derivation (.impl (.box k (.plays MirrorBot (DupocBot k) .C))
                             (.plays (DupocBot k) MirrorBot .C)) := by
    have := Derivation.searchBranch k (.plays .opp .self .C) .C .D (DupocBot k) MirrorBot rfl
    simpa [Formula.subst, Prog.subst, DupocBot] using this
  let dM : Derivation (.impl (.plays (DupocBot k) MirrorBot .C)
                             (.plays MirrorBot (DupocBot k) .C)) := by
    have := Derivation.simStep MirrorBot .opp .self (DupocBot k) .C rfl
    simpa [Prog.subst, MirrorBot] using this
  exact derives (.hypSyll _ _ _ dS dM)

/-- Once `proofSearch k = true`, DupocBot's eval against MirrorBot takes the
    cooperate branch. -/
theorem DupocBot_plays_C_against_MirrorBot (k fuel : Nat)
    (hk : proofSearch k (.plays MirrorBot (DupocBot k) .C) = true) :
    play (fuel + 2) (DupocBot k) MirrorBot = some .C := by
  show eval (fuel + 2) (DupocBot k) MirrorBot (DupocBot k) = some .C
  unfold DupocBot at hk ⊢
  simp [eval, Prog.subst, Formula.subst, hk]

/-- MirrorBot mirrors DupocBot's cooperate via the `.sim .opp .self` swap. -/
theorem MirrorBot_plays_C_against_DupocBot (k fuel : Nat)
    (hk : proofSearch k (.plays MirrorBot (DupocBot k) .C) = true) :
    play (fuel + 3) MirrorBot (DupocBot k) = some .C := by
  have hDupoc : play (fuel + 2) (DupocBot k) MirrorBot = some .C :=
    DupocBot_plays_C_against_MirrorBot k fuel hk
  simpa [play, eval, Prog.subst, MirrorBot] using hDupoc

/-- Dual of `DupocBot_plays_C_against_MirrorBot`: when proofSearch fails,
    DupocBot falls through to its `.const .D` defect branch. -/
theorem DupocBot_plays_D_against_MirrorBot (k fuel : Nat)
    (hk : proofSearch k (.plays MirrorBot (DupocBot k) .C) = false) :
    play (fuel + 2) (DupocBot k) MirrorBot = some .D := by
  show eval (fuel + 2) (DupocBot k) MirrorBot (DupocBot k) = some .D
  unfold DupocBot at hk ⊢
  simp [eval, Prog.subst, Formula.subst, hk]

/-- Dual of `MirrorBot_plays_C_against_DupocBot`: MirrorBot mirrors the defect
    branch via the `.sim .opp .self` swap. -/
theorem MirrorBot_plays_D_against_DupocBot (k fuel : Nat)
    (hk : proofSearch k (.plays MirrorBot (DupocBot k) .C) = false) :
    play (fuel + 3) MirrorBot (DupocBot k) = some .D := by
  have hDupoc : play (fuel + 2) (DupocBot k) MirrorBot = some .D :=
    DupocBot_plays_D_against_MirrorBot k fuel hk
  simpa [play, eval, Prog.subst, MirrorBot] using hDupoc

/-- Inversion: from a `play` witness on MirrorBot's leg, recover that DupocBot's
    proof-search guard at parameter `k` must have fired. The play can only be
    `some .C` if DupocBot's `.search` took the `.const .C` branch, which requires
    `proofSearch k = true`. -/
theorem proofSearch_k_of_play_MirrorBot_dupoc
    (k n : Nat) (h : play n MirrorBot (DupocBot k) = some .C) :
    proofSearch k (.plays MirrorBot (DupocBot k) .C) = true := by
  cases hps : proofSearch k (.plays MirrorBot (DupocBot k) .C) with
  | true  => rfl
  | false =>
    exfalso
    rcases n with _ | _ | _ | n
    · simp [play, eval] at h
    · simp [play, eval, MirrorBot] at h
    · have hev : play 2 MirrorBot (DupocBot k) = none := by
        unfold DupocBot
        simp [play, eval, Prog.subst, MirrorBot, Formula.subst]
      rw [hev] at h
      cases h
    · have hev : play (n + 3) MirrorBot (DupocBot k) = some .D := by
        simpa using MirrorBot_plays_D_against_DupocBot k n hps
      rw [hev] at h
      cases h

/-- DupocBot vs MirrorBot cooperates, for `k` large enough. Direct application
    of PBLT with `φ k = .plays MirrorBot (DupocBot k) .C`, `f = id`, `k₁ = 0`.
    Mirrors `DupocBot_vs_DupocBot`; the play witness lives on the MirrorBot leg
    and is lifted to the DupocBot leg via the `.sim` swap. -/
theorem DupocBot_vs_MirrorBot :
    ∃ k₂, ∀ k, k₂ < k →
      ∃ fuel, outcome fuel (DupocBot k) MirrorBot = some (.C, .C) := by
  let φ : Nat → Formula := fun k => .plays MirrorBot (DupocBot k) .C
  have hMono : ∀ a b : Nat, a ≤ b → id a ≤ id b := fun _ _ h => h
  have hLog : ∃ c kHat, c > 0 ∧ ∀ k, k > kHat → id k > c * Nat.log2 k := by
    refine ⟨1, 0, Nat.zero_lt_one, ?_⟩
    intro k hk
    have hlog : Nat.log2 k < k := by
      rw [Nat.log2_lt (Nat.pos_iff_ne_zero.mp hk)]
      exact Nat.lt_two_pow_self
    simpa using hlog
  have hLoeb :
      ∀ k, k > 0 →
        ∃ m, proofSearch m (.impl (.box (id k) (φ k)) (φ k)) = true := by
    intro k _
    simpa using dupoc_mirror_loeb_premise k
  obtain ⟨k₂, hk₂⟩ := PBLT φ id 0 hMono hLog hLoeb
  refine ⟨k₂, ?_⟩
  intro k hk
  obtain ⟨m, hm⟩ := hk₂ k hk
  have hInterp : (φ k).interp := proofSearch_sound m (φ k) hm
  obtain ⟨n, hMirror⟩ := hInterp
  have hPS : proofSearch k (.plays MirrorBot (DupocBot k) .C) = true :=
    proofSearch_k_of_play_MirrorBot_dupoc k n hMirror
  refine ⟨3, ?_⟩
  have hA : play 3 (DupocBot k) MirrorBot = some .C := by
    simpa using DupocBot_plays_C_against_MirrorBot k 1 hPS
  have hB : play 3 MirrorBot (DupocBot k) = some .C := by
    simpa using MirrorBot_plays_C_against_DupocBot k 0 hPS
  exact outcome_of_plays _ _ _ _ _ hA hB


end PD.Theorems
