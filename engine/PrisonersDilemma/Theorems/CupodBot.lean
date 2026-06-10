import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Axioms
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Bots.CupodBot
import PrisonersDilemma.Bots.TitForTatBot
import PrisonersDilemma.Bots.DBot
import PrisonersDilemma.Bots.OBot
import PrisonersDilemma.Bots.EBot
import PrisonersDilemma.Bots.MirrorBot
import PrisonersDilemma.Theorems.CooperateBot
import PrisonersDilemma.Theorems.DefectBot
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Theorems.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.SizeLemmas

open PD
open PD.Axioms
open PD.Bots
open PD.BaseTheorems
namespace PD.Theorems




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

/-- Proof search is true for DefectBot vs CupodBot k at budget/index
    `atom_cost 1`. DefectBot ignores its opponent
    so the play holds for any CupodBot index. -/
theorem proofSearch_true_for_DefectBot :
    ∃ k, proofSearch k (.plays DefectBot (CupodBot k) .D) = true :=
  let k := atom_cost 1
  ⟨k, (proofSearch_spec _ _).2 (Provable.atom (atom_complete DefectBot (CupodBot k) .D 1 rfl))⟩

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

/-- CUPOD-specific Löb premise (critch22 Theorem 3.4 substitution into PBLT),
    **character-faithful**. The `searchBranch` derivation concluding
    `□_k (CUPOD plays D vs CUPOD) → (CUPOD plays D vs CUPOD)` has size exactly
    `5 * log2 k + 33` characters (the guard `ψ.subst (CupodBot k) (CupodBot k)`
    reduces to `.plays (CupodBot k) (CupodBot k) .D`; each `CupodBot k` costs
    `log2 k + 7`). By `linear_log2_add_le 5 33` this fits within budget `k` for
    all `k ≥ K₀`, so the implication is `Provable k` outright — exactly the
    PBLT-shaped hypothesis (no looser `∃ m` budget).

    The conclusion formula is *definitionally* the `searchBranch` conclusion: the
    guard `(.plays .opp .self .D).subst (CupodBot k) (CupodBot k)` unfolds to
    `.plays (CupodBot k) (CupodBot k) .D`, so the derivation lands in the target
    type with no rewriting. -/
theorem cupod_loeb_premise :
    ∃ K₀ : Nat, ∀ k : Nat, k ≥ K₀ →
      Provable k (.impl (.box k (.plays (CupodBot k) (CupodBot k) .D))
                        (.plays (CupodBot k) (CupodBot k) .D)) := by
  obtain ⟨K₀, hK₀⟩ := linear_log2_add_le 5 33
  refine ⟨K₀, fun k hk => ?_⟩
  apply Provable.struct
  refine ⟨.searchBranch k (.plays .opp .self .D) .D .C (CupodBot k) (CupodBot k) rfl, ?_⟩
  -- d.size = conclusion.size = 5 * log2 k + 33 ≤ k for k ≥ K₀.
  simp only [Derivation.size, Formula.size, Prog.size, CupodBot]
  have := hK₀ k hk
  omega

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
  obtain ⟨K₀, hK₀⟩ := cupod_loeb_premise
  -- `cupod_loeb_premise` proves the *tight* bound `Provable k (…)` (size ≤ k,
  -- keeping `Derivation.size` load-bearing); PBLT only needs the existential
  -- `∃ m, Provable m (…)`, so we weaken.
  have hLoeb :
      ∀ k, k > K₀ →
        ∃ m, Provable m (.impl (.box (id k) (φ k)) (φ k)) := by
    intro k hk
    exact ⟨k, hK₀ k (Nat.le_of_lt hk)⟩
  obtain ⟨k₂, hk₂⟩ := PBLT φ id K₀ hMono hLog hLoeb
  refine ⟨k₂, ?_⟩
  intro k hk
  obtain ⟨m, hm⟩ := hk₂ k hk
  have hInterp : (φ k).interp := Provable_sound m (φ k) hm
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

theorem proofSearch_true_for_bot_DefectBot :
    ∃ k, proofSearch k (.plays (.bot DefectBot) (CupodBot k) .D) = true :=
  let k := atom_cost 2
  ⟨k, (proofSearch_spec _ _).2 (Provable.atom (atom_complete (.bot DefectBot) (CupodBot k) .D 2 rfl))⟩

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

theorem proofSearch_true_for_OBot :
    ∃ k, proofSearch k (.plays OBot (CupodBot k) .D) = true := by
  -- Working budget/index k = atom_cost 5.
  refine ⟨atom_cost 5, ?_⟩
  -- Step 1: lift the .bot DefectBot atom from fuel-2 budget to working budget.
  have hkDefect : proofSearch (atom_cost 5)
      (.plays (.bot DefectBot) (CupodBot (atom_cost 5)) .D) = true :=
    proofSearch_monotone (atom_cost 2) _ _
      (atom_cost_mono (by omega))
      ((proofSearch_spec _ _).2 (Provable.atom
        (atom_complete (.bot DefectBot) (CupodBot (atom_cost 5)) .D 2 rfl)))
  -- Step 2: OBot defects vs CupodBot k at fuel 5.
  have hobot : play 5 OBot (CupodBot (atom_cost 5)) = some .D := by
    simpa using OBot_plays_D_against_CupodBot (atom_cost 5) 0 hkDefect
  -- Step 3: atom_complete at fuel 5 gives the working budget exactly.
  exact (proofSearch_spec _ _).2 (Provable.atom
    (atom_complete OBot (CupodBot (atom_cost 5)) .D 5 hobot))

theorem CupodBot_plays_D_against_OBot (fuel : Nat) (k : Nat)
    (hk : proofSearch k (.plays OBot (CupodBot k) .D) = true) :
    play (fuel + 5) (CupodBot k) OBot = some .D := by
  show eval (fuel + 5) (CupodBot k) OBot (CupodBot k) = some .D
  unfold CupodBot at hk ⊢
  simp [eval, Prog.subst, Formula.subst, hk]

/-- CupodBot vs OBot: mutual defection. -/
theorem CupodBot_vs_OBot (fuel : Nat) :
    ∃ k, outcome (fuel + 5) (CupodBot k) OBot = some (.D, .D) := by
  -- Working budget/index k = atom_cost 5.
  let k := atom_cost 5
  have hkDefect : proofSearch k (.plays (.bot DefectBot) (CupodBot k) .D) = true :=
    proofSearch_monotone (atom_cost 2) k _
      (atom_cost_mono (by omega))
      ((proofSearch_spec _ _).2 (Provable.atom (atom_complete (.bot DefectBot) (CupodBot k) .D 2 rfl)))
  have hkOBot : proofSearch k (.plays OBot (CupodBot k) .D) = true := by
    have hobot : play 5 OBot (CupodBot k) = some .D := by
      simpa using OBot_plays_D_against_CupodBot k 0 hkDefect
    exact (proofSearch_spec _ _).2 (Provable.atom (atom_complete OBot (CupodBot k) .D 5 hobot))

  refine ⟨k, ?_⟩

  have hA : play (fuel + 5) (CupodBot k) OBot = some .D :=
    CupodBot_plays_D_against_OBot fuel k hkOBot

  have hB : play (fuel + 5) OBot (CupodBot k) = some .D :=
    OBot_plays_D_against_CupodBot k fuel hkDefect

  exact outcome_of_plays _ _ _ _ _ hA hB


-- EBot --

/-- EBot cooperates with CUPOD: its outer probe (`.bot DefectBot`) sees CUPOD
    defect, so EBot descends into the inner `ite`; the next probe
    (`.bot CooperateBot`) sees CUPOD cooperate, so EBot cooperates. -/
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

/-- Semantically, EBot never plays D against CUPOD (given the DefectBot probe
    succeeds). -/
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

/-- CupodBot vs EBot: mutual cooperation. -/
theorem CupodBot_vs_EBot (fuel : Nat) :
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


-- MirrorBot --

/-- Specialization of `proof_system_verifies_sim` to `MirrorBot = .sim .opp .self`
    against an arbitrary opponent: S derives "opp plays a vs Mirror → Mirror plays a vs opp". -/
theorem mirror_swap_provable (q : Prog) (a : Action) :
    ∃ m, proofSearch m
      (.impl (.plays q MirrorBot a) (.plays MirrorBot q a)) = true := by
  have h := proof_system_verifies_sim MirrorBot .opp .self q a rfl
  simpa [Prog.subst, MirrorBot] using h

/-- Löb premise for CupodBot vs MirrorBot. Combines source-code transparency
    of CupodBot's `.search` body (`□_k φ_A → φ_B`) with `.sim` source
    transparency for MirrorBot (`φ_B → φ_A`), chained by `Dynamics.hypSyll`
    into the closed `□_k φ → φ` that PBLT requires. (Was an `proofSearch`-level
    chain via the deleted `proofSearch_impl_trans`; now one explicit
    Dynamics.) -/
theorem cupod_mirror_loeb_premise :
    ∃ K₀ : Nat, ∀ k : Nat, k ≥ K₀ →
      Provable k (.impl (.box k (.plays MirrorBot (CupodBot k) .D))
                        (.plays MirrorBot (CupodBot k) .D)) := by
  -- The `hypSyll` chain concludes `□_k (Mirror plays D vs Cupod) → (Mirror plays
  -- D vs Cupod)`, of size exactly `3 * log2 k + 25` characters (MirrorBot costs
  -- 3, each `CupodBot k` costs `log2 k + 7`). `linear_log2_add_le 3 25` fits this
  -- within budget `k` for `k ≥ K₀`.
  obtain ⟨K₀, hK₀⟩ := linear_log2_add_le 3 25
  refine ⟨K₀, fun k hk => ?_⟩
  -- `□_k (Mirror plays D vs Cupod) → Cupod plays D vs Mirror`, from Cupod's `.search` body.
  -- The guard `(.plays .opp .self .D).subst (CupodBot k) MirrorBot` reduces
  -- definitionally to `.plays MirrorBot (CupodBot k) .D`, so this lands in type.
  let dS : Derivation (.impl (.box k (.plays MirrorBot (CupodBot k) .D))
                             (.plays (CupodBot k) MirrorBot .D)) :=
    Derivation.searchBranch k (.plays .opp .self .D) .D .C (CupodBot k) MirrorBot rfl
  -- `Cupod plays D vs Mirror → Mirror plays D vs Cupod`, from Mirror's `.sim` swap.
  let dM : Derivation (.impl (.plays (CupodBot k) MirrorBot .D)
                             (.plays MirrorBot (CupodBot k) .D)) :=
    Derivation.simStep MirrorBot .opp .self (CupodBot k) .D rfl
  apply Provable.struct
  refine ⟨.hypSyll _ _ _ dS dM, ?_⟩
  simp only [Derivation.size, Formula.size, Prog.size, CupodBot, MirrorBot]
  have := hK₀ k hk
  omega

/-- Once `proofSearch k = true`, CupodBot's eval against MirrorBot is fully
    determined. Pattern from `CupodBot_plays_D_against_bot_DefectBot:247`. -/
theorem CupodBot_plays_D_against_MirrorBot (k fuel : Nat)
    (hk : proofSearch k (.plays MirrorBot (CupodBot k) .D) = true) :
    play (fuel + 2) (CupodBot k) MirrorBot = some .D := by
  show eval (fuel + 2) (CupodBot k) MirrorBot (CupodBot k) = some .D
  unfold CupodBot at hk ⊢
  simp [eval, Prog.subst, Formula.subst, hk]

/-- `.sim .opp .self` swap idiom from `MirrorBot_plays_C_against_DBot:54`. -/
theorem MirrorBot_plays_D_against_CupodBot (k fuel : Nat)
    (hk : proofSearch k (.plays MirrorBot (CupodBot k) .D) = true) :
    play (fuel + 3) MirrorBot (CupodBot k) = some .D := by
  have hCupod : play (fuel + 2) (CupodBot k) MirrorBot = some .D :=
    CupodBot_plays_D_against_MirrorBot k fuel hk
  simpa [play, eval, Prog.subst, MirrorBot] using hCupod

/-- Dual of `CupodBot_plays_D_against_MirrorBot`: when proofSearch fails,
    CupodBot falls through to its `.const .C` cooperate branch. -/
theorem CupodBot_plays_C_against_MirrorBot (k fuel : Nat)
    (hk : proofSearch k (.plays MirrorBot (CupodBot k) .D) = false) :
    play (fuel + 2) (CupodBot k) MirrorBot = some .C := by
  show eval (fuel + 2) (CupodBot k) MirrorBot (CupodBot k) = some .C
  unfold CupodBot at hk ⊢
  simp [eval, Prog.subst, Formula.subst, hk]

/-- Dual of `MirrorBot_plays_D_against_CupodBot`: MirrorBot mirrors the
    cooperate branch via the `.sim .opp .self` swap. -/
theorem MirrorBot_plays_C_against_CupodBot (k fuel : Nat)
    (hk : proofSearch k (.plays MirrorBot (CupodBot k) .D) = false) :
    play (fuel + 3) MirrorBot (CupodBot k) = some .C := by
  have hCupod : play (fuel + 2) (CupodBot k) MirrorBot = some .C :=
    CupodBot_plays_C_against_MirrorBot k fuel hk
  simpa [play, eval, Prog.subst, MirrorBot] using hCupod

/-- Inversion: from a `play` witness on MirrorBot's leg, recover that
    CupodBot's proof-search guard at parameter `k` must have fired. The play
    can only be `some .D` if CupodBot's `.search` took the `.const .D` branch,
    which requires `proofSearch k = true`. -/
theorem proofSearch_k_of_play_MirrorBot
    (k n : Nat) (h : play n MirrorBot (CupodBot k) = some .D) :
    proofSearch k (.plays MirrorBot (CupodBot k) .D) = true := by
  cases hps : proofSearch k (.plays MirrorBot (CupodBot k) .D) with
  | true  => rfl
  | false =>
    -- `play _ MirrorBot (CupodBot k)` is either `none` (small fuel) or `some .C`
    -- (proofSearch returned false). Neither equals `some .D`, contradicting `h`.
    exfalso
    rcases n with _ | _ | _ | n
    · simp [play, eval] at h
    · simp [play, eval, MirrorBot] at h
    · have hev : play 2 MirrorBot (CupodBot k) = none := by
        unfold CupodBot
        simp [play, eval, Prog.subst, MirrorBot, Formula.subst]
      rw [hev] at h
      cases h
    · have hev : play (n + 3) MirrorBot (CupodBot k) = some .C := by
        simpa using MirrorBot_plays_C_against_CupodBot k n hps
      rw [hev] at h
      cases h

/-- CupodBot vs MirrorBot defects, for `k` large enough. Direct application of
    PBLT with `φ k = .plays MirrorBot (CupodBot k) .D`, `f = id`, `k₁ = 0`.
    Mirrors `CupodBot_vs_CupodBot`; the play witness lives on the MirrorBot
    leg and is lifted to the CupodBot leg via the `.sim` swap. -/
theorem CupodBot_vs_MirrorBot :
    ∃ k₂, ∀ k, k₂ < k →
      ∃ fuel, outcome fuel (CupodBot k) MirrorBot = some (.D, .D) := by
  let φ : Nat → Formula := fun k => .plays MirrorBot (CupodBot k) .D
  have hMono : ∀ a b : Nat, a ≤ b → id a ≤ id b := fun _ _ h => h
  have hLog : ∃ c kHat, c > 0 ∧ ∀ k, k > kHat → id k > c * Nat.log2 k := by
    refine ⟨1, 0, Nat.zero_lt_one, ?_⟩
    intro k hk
    have hlog : Nat.log2 k < k := by
      rw [Nat.log2_lt (Nat.pos_iff_ne_zero.mp hk)]
      exact Nat.lt_two_pow_self
    simpa using hlog
  obtain ⟨K₀, hK₀⟩ := cupod_mirror_loeb_premise
  have hLoeb :
      ∀ k, k > K₀ →
        ∃ m, Provable m (.impl (.box (id k) (φ k)) (φ k)) := by
    intro k hk
    exact ⟨k, hK₀ k (Nat.le_of_lt hk)⟩
  obtain ⟨k₂, hk₂⟩ := PBLT φ id K₀ hMono hLog hLoeb
  refine ⟨k₂, ?_⟩
  intro k hk
  obtain ⟨m, hm⟩ := hk₂ k hk
  have hInterp : (φ k).interp := Provable_sound m (φ k) hm
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
