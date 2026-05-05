import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Axioms
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Bots.CupodBot
import PrisonersDilemma.Bots.TitForTatBot
import PrisonersDilemma.Bots.DBot
import PrisonersDilemma.Bots.OBot
import PrisonersDilemma.Theorems.CooperateBot
import PrisonersDilemma.Theorems.DefectBot
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Theorems.Helpers
import PrisonersDilemma.Theorems.ProofSearch

open PDNew
open PDNew.Axioms
open PDNew.Bots
namespace PDNew.Theorems


-- Monotonicity --

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

/-- CupodBot vs CooperateBot: uses proof search being false -/
theorem CupodBot_vs_CooperateBot (k fuel : Nat):
    outcome (fuel + 2) (CupodBot k) CooperateBot = some (.C, .C) := by
  -- Left side: CUPOD executes its `.search` guard. The guard is false by the
  -- lemma above, so the `search` falls through to the final `.const .C` branch.
  have hA : play (fuel + 2) (CupodBot k) CooperateBot = some .C := by
    show eval (fuel + 2) (CupodBot k) CooperateBot (CupodBot k) = some .C
    -- `guard_false` tells us the proof search for “CooperateBot plays D” fails.
    -- Once we unfold the bot, the remaining `simp` can simplify the search node
    -- and the constant branch all the way down to `.C`.
    have hg := proofSearch_false_for_CooperateBot k
    unfold CupodBot at hg ⊢
    simp [eval, Prog.subst, Formula.subst, hg]
  -- Right side: CooperateBot is definitionally the constant `.C` bot.
  have hB : play (fuel + 2) CooperateBot (CupodBot k) = some .C := rfl
  -- Finally, `outcome` just packages the two `play` results together.
  simp [outcome, hA, hB]


-- DefectBot --

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

/-- CupodBot vs DefectBot: uses proof search being true -/
theorem CupodBot_vs_DefectBot (fuel : Nat):
    ∃ k, outcome (fuel + 2) (CupodBot k) DefectBot = some (.D, .D) := by
  obtain ⟨k, hk⟩ := proofSearch_true_for_DefectBot
  refine ⟨k, ?_⟩

  have hA : play (fuel + 2) (CupodBot k) DefectBot = some .D := by
    show eval (fuel + 2) (CupodBot k) DefectBot (CupodBot k) = some .D
    unfold CupodBot at hk ⊢
    simp [eval, Prog.subst, Formula.subst, hk]

  have hB : play (fuel + 2) DefectBot (CupodBot k) = some .D := by
    simpa [Nat.add_assoc] using (play_DefectBot (fuel + 1) (CupodBot k))

  simp [outcome, hA, hB]


-- CupodBot --

/-- CUPOD-specific Löb premise (critch22 Theorem 3.4 substitution into PBLT).
    Instantiates `proof_system_verifies_search_branch` with
    ψ = "opp(self.source) == D", a = .D, b = .C, me = opp = CupodBot k.
    The closed guard `ψ.subst (CupodBot k) (CupodBot k)` reduces to
    `.plays (CupodBot k) (CupodBot k) .D`. -/
theorem cupod_loeb_premise (k : Nat) :
    ∃ m, proofSearch m
      (.impl (.box k (.plays (CupodBot k) (CupodBot k) .D))
             (.plays (CupodBot k) (CupodBot k) .D)) = true := by
  have h := proof_system_verifies_search_branch
              k (.plays .opp .self .D) .D .C
              (CupodBot k) (CupodBot k) rfl
  simpa [Formula.subst, Prog.subst] using h

/-- CUPOD self-play defects, for `k` large enough — critch22 Theorem 3.4.
    Direct application of PBLT with `φ k = .plays (CupodBot k) (CupodBot k) .D`,
    `f = id`, `k₁ = 0`. The Löb premise comes from `cupod_loeb_premise`,
    soundness collapses bounded provability to a `play` witness, and self-play
    symmetry makes the same `play` discharge both legs of `outcome`. -/
theorem CupodBot_vs_CupodBot :
    ∃ k₂, ∀ k, k₂ < k →
      ∃ fuel, outcome fuel (CupodBot k) (CupodBot k) = some (.D, .D) := by
  let φ : Nat → Formula := fun k => .plays (CupodBot k) (CupodBot k) .D
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
    simpa using cupod_loeb_premise k
  obtain ⟨k₂, hk₂⟩ := PBLT φ id 0 hMono hLog hLoeb
  refine ⟨k₂, ?_⟩
  intro k hk
  obtain ⟨m, hm⟩ := hk₂ k hk
  have hInterp : (φ k).interp := proofSearch_sound m (φ k) hm
  obtain ⟨n, hn⟩ := hInterp
  refine ⟨n, ?_⟩
  simp [outcome, hn]


-- TitForTatBot --

/-- Proof search is false for `.bot CooperateBot`. -/
theorem proofSearch_false_for_bot_CooperateBot (k : Nat) :
    proofSearch k (.plays (.bot CooperateBot) (CupodBot k) .D) = false := by
  cases h : proofSearch k (.plays (.bot CooperateBot) (CupodBot k) .D) with
  | true  => exact absurd (proofSearch_sound _ _ h)
                          (interp_bot_CooperateBot_plays_D_false _)
  | false => rfl

/-- CUPOD cooperates against `.bot CooperateBot` because the search guard fails. -/
theorem CupodBot_plays_C_against_bot_CooperateBot (k fuel : Nat) :
    play (fuel + 2) (CupodBot k) (.bot CooperateBot) = some .C := by
  have hg := proofSearch_false_for_bot_CooperateBot k
  show eval (fuel + 2) (CupodBot k) (.bot CooperateBot) (CupodBot k) = some .C
  unfold CupodBot at hg ⊢
  simp [eval, Prog.subst, Formula.subst, hg]

/-- TitForTat cooperates with CUPOD: its `.sim .opp (.bot CooperateBot)` probe
    sees CUPOD cooperate, so the `ite` selects the cooperate branch. -/
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

/-- Semantically, TitForTat never plays D against CUPOD. -/
theorem interp_TitForTatBot_plays_D_false (k : Nat) :
    ¬ (Formula.plays TitForTatBot (CupodBot k) .D).interp := by
  rintro ⟨n, hn⟩
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
                  simp [play, eval, TitForTatBot, CupodBot, Prog.subst, Formula.subst, CooperateBot] at hn
              | succ fuel =>
                  have hC : play (fuel + 1 + 1 + 1 + 1) TitForTatBot (CupodBot k) = some .C := by
                    simpa [Nat.add_assoc] using TitForTatBot_plays_C_against_CupodBot k fuel
                  rw [hC] at hn
                  cases hn

/-- Proof search is false for `.plays TitForTatBot (CupodBot k) .D`. -/
theorem proofSearch_false_for_TitForTatBot (k : Nat) :
    proofSearch k (.plays TitForTatBot (CupodBot k) .D) = false := by
  cases h : proofSearch k (.plays TitForTatBot (CupodBot k) .D) with
  | true  => exact absurd (proofSearch_sound _ _ h)
                          (interp_TitForTatBot_plays_D_false _)
  | false => rfl

/-- CupodBot vs TitForTatBot: mutual cooperation. -/
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

theorem proofSearch_true_for_bot_DefectBot_different_k (n : Nat) :
    ∃ k, proofSearch k (.plays (.bot DefectBot) (CupodBot n) .D) = true := by
  have hex : ∃ m, play m (.bot DefectBot) (CupodBot n) = some .D := by
    exists 2
  exact proofSearch_complete_plays (.bot DefectBot) (CupodBot n) .D hex

theorem proofSearch_true_for_bot_DefectBot :
    ∃ k, proofSearch k (.plays (.bot DefectBot) (CupodBot k) .D) = true := by
  obtain ⟨k, hk⟩ := proofSearch_true_for_bot_DefectBot_different_k 0
  refine ⟨k, ?_⟩
  exact CupodBot_monotonicity 0 k (.bot DefectBot) .D (Nat.zero_le k) hk

/-- CUPOD defects against `.bot DefectBot` once its search guard succeeds. -/
theorem CupodBot_plays_D_against_bot_DefectBot (k fuel : Nat)
    (hk : proofSearch k (.plays (.bot DefectBot) (CupodBot k) .D) = true) :
    play (fuel + 2) (CupodBot k) (.bot DefectBot) = some .D := by
  show eval (fuel + 2) (CupodBot k) (.bot DefectBot) (CupodBot k) = some .D
  unfold CupodBot at hk ⊢
  simp [eval, Prog.subst, Formula.subst, hk]

/-- DBot probes its opponent against `.bot DefectBot`; once CUPOD defects on
    that probe, DBot's `ite` selects the cooperate branch. -/
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

/-- Semantically, DBot never plays D against CUPOD (given the DefectBot probe
    succeeds). -/
theorem interp_DBot_plays_D_false (k : Nat)
    (hk : proofSearch k (.plays (.bot DefectBot) (CupodBot k) .D) = true) :
    ¬ (Formula.plays DBot (CupodBot k) .D).interp := by
  rintro ⟨n, hn⟩
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
                  simp [play, eval, DBot, CupodBot, Prog.subst, Formula.subst, DefectBot] at hn
              | succ fuel =>
                  have hC : play (fuel + 1 + 1 + 1 + 1) DBot (CupodBot k) = some .C := by
                    simpa [Nat.add_assoc] using DBot_plays_C_against_CupodBot k fuel hk
                  rw [hC] at hn
                  cases hn

theorem proofSearch_false_for_DBot (k : Nat)
    (hk : proofSearch k (.plays (.bot DefectBot) (CupodBot k) .D) = true) :
    proofSearch k (.plays DBot (CupodBot k) .D) = false := by
  cases h : proofSearch k (.plays DBot (CupodBot k) .D) with
  | true  => exact absurd (proofSearch_sound _ _ h)
                          (interp_DBot_plays_D_false _ hk)
  | false => rfl

/-- CupodBot vs DBot: mutual cooperation. -/
theorem CupodBot_vs_DBot (fuel : Nat) :
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

/-- OBot defects against CUPOD: its first probe (`.bot CooperateBot`) sees CUPOD
    cooperate, so it descends into the inner `ite`; that inner probe
    (`.bot DefectBot`) sees CUPOD defect, sending OBot to the defect branch. -/
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

theorem proofSearch_true_for_OBot_different_k :
    ∃ k n, proofSearch k (.plays OBot (CupodBot n) .D) = true := by
  have hex : ∃ m n, play m OBot (CupodBot n) = some .D := by
    have hk := proofSearch_true_for_bot_DefectBot
    obtain ⟨d, hd⟩ := hk
    have _ := OBot_plays_D_against_CupodBot d 0 hd
    exists 5, d
  rcases hex with ⟨m, n, h⟩
  have hn : ∃ m, play m OBot (CupodBot n) = some Action.D := ⟨m, h⟩
  have h := proofSearch_complete_plays OBot (CupodBot n) .D hn
  obtain ⟨k, hk⟩ := h
  exact ⟨k, n, hk⟩

theorem proofSearch_true_for_OBot :
    ∃ k, proofSearch k (.plays OBot (CupodBot k) .D) = true := by
  obtain ⟨k, n, hk⟩ := proofSearch_true_for_OBot_different_k
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
    (hk : proofSearch k (.plays OBot (CupodBot k) .D) = true) :
    play (fuel + 5) (CupodBot k) OBot = some .D := by
  show eval (fuel + 5) (CupodBot k) OBot (CupodBot k) = some .D
  unfold CupodBot at hk ⊢
  simp [eval, Prog.subst, Formula.subst, hk]

/-- CupodBot vs OBot: mutual defection. -/
theorem CupodBot_vs_OBot (fuel : Nat) :
    ∃ k, outcome (fuel + 5) (CupodBot k) OBot = some (.D, .D) := by
  -- Two proof-search witnesses: `o` makes CUPOD defect against OBot, `d` makes
  -- OBot defect against CUPOD via the DefectBot probe.
  obtain ⟨o, ho⟩ := proofSearch_true_for_OBot
  obtain ⟨d, hd⟩ := proofSearch_true_for_bot_DefectBot

  -- Pick a final index large enough for both witnesses; monotonicity reuses
  -- both proof-search successes at the same `k`.
  let k := o + d
  have hok : o ≤ k := Nat.le_add_right o d
  have hdk : d ≤ k := Nat.le_add_left d o

  have hkOBot : proofSearch k (.plays OBot (CupodBot k) .D) = true :=
    CupodBot_monotonicity o k OBot .D hok
      (proofSearch_monotone o k (.plays OBot (CupodBot o) .D) hok ho)

  have hkDefect : proofSearch k (.plays (.bot DefectBot) (CupodBot k) .D) = true :=
    CupodBot_monotonicity d k (.bot DefectBot) .D hdk
      (proofSearch_monotone d k (.plays (.bot DefectBot) (CupodBot d) .D) hdk hd)

  refine ⟨k, ?_⟩

  have hA : play (fuel + 5) (CupodBot k) OBot = some .D :=
    CupodBot_plays_D_against_OBot fuel k hkOBot

  have hB : play (fuel + 5) OBot (CupodBot k) = some .D :=
    OBot_plays_D_against_CupodBot k fuel hkDefect

  exact outcome_of_plays _ _ _ _ _ hA hB

end PDNew.Theorems
