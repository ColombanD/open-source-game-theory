import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Axioms
import PrisonersDilemma.Bots.DupocBot
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Bots.MirrorBot
import PrisonersDilemma.Bots.TitForTatBot
import PrisonersDilemma.Bots.LlmGenerations.JustBot
import PrisonersDilemma.Theorems.CooperateBot
import PrisonersDilemma.Theorems.DefectBot
import PrisonersDilemma.Theorems.DupocBot
import PrisonersDilemma.Theorems.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.SizeLemmas

open PD
open PD.Axioms
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems



/-- One evaluation step of JustBot: it consults its guard `proofSearch` and takes
    the corresponding constant branch (cooperate iff the guard fires). -/
theorem JustBot_eval_step (k fuel : Nat) (X : Prog) (a : Action)
    (hg : proofSearch k (Formula.plays X (.bot (DupocBot k)) Action.C)
            = (a == Action.C)) :
    play (fuel + 2) (JustBot k) X = some a := by
  -- The guard `proofSearch` argument is definitionally `.plays X (.bot (DupocBot k)) .C`.
  show (if proofSearch k (Formula.plays X (.bot (DupocBot k)) Action.C)
          then eval (fuel + 1) (JustBot k) X (.const Action.C)
          else eval (fuel + 1) (JustBot k) X (.const Action.D)) = some a
  rw [hg]
  cases a with
  | C => simp [eval]; rfl
  | D => simp [eval]; rfl

-- DefectBot --

/-- JustBot's substituted guard against DefectBot is false: DefectBot never plays C
    (against DupocBot or anything), so the guard search fails. -/
theorem proofSearch_false_for_JustBot_vs_DefectBot (k : Nat) :
    proofSearch k (Formula.plays DefectBot (.bot (DupocBot k)) Action.C) = false := by
  cases h : proofSearch k (Formula.plays DefectBot (.bot (DupocBot k)) Action.C) with
  | true  => exact absurd (proofSearch_sound _ _ h) (interp_DefectBot_plays_C_false _)
  | false => rfl

/-- JustBot defects against DefectBot: its guard fails. -/
theorem JustBot_plays_D_against_DefectBot (k fuel : Nat) :
    play (fuel + 2) (JustBot k) DefectBot = some .D := by
  refine JustBot_eval_step k fuel DefectBot .D ?_
  simpa using proofSearch_false_for_JustBot_vs_DefectBot k

/-- JustBot vs DefectBot: mutual defection. -/
theorem JustBot_vs_DefectBot (k fuel : Nat) :
    outcome (fuel + 2) (JustBot k) DefectBot = some (.D, .D) := by
  have hA : play (fuel + 2) (JustBot k) DefectBot = some .D :=
    JustBot_plays_D_against_DefectBot k fuel
  have hB : play (fuel + 2) DefectBot (JustBot k) = some .D := by
    simpa [Nat.add_comm] using play_DefectBot (fuel + 1) (JustBot k)
  exact outcome_of_plays _ _ _ _ _ hA hB

-- CooperateBot --

/-- JustBot's substituted guard against CooperateBot is true: CooperateBot
    cooperates against DupocBot (it cooperates against everything). -/
theorem proofSearch_true_for_JustBot_vs_CooperateBot :
    ∃ k, proofSearch k (Formula.plays CooperateBot (.bot (DupocBot k)) Action.C) = true := by
  refine ⟨atom_cost 1, ?_⟩
  refine (proofSearch_spec _ _).2 (Provable.atom (atom_complete CooperateBot _ .C 1 ?_))
  simpa using play_CooperateBot 0 (.bot (DupocBot (atom_cost 1)))

/-- JustBot cooperates against CooperateBot: its guard succeeds. -/
theorem JustBot_plays_C_against_CooperateBot (k fuel : Nat)
    (hk : proofSearch k (Formula.plays CooperateBot (.bot (DupocBot k)) Action.C) = true) :
    play (fuel + 2) (JustBot k) CooperateBot = some .C := by
  refine JustBot_eval_step k fuel CooperateBot .C ?_
  simpa using hk

/-- JustBot vs CooperateBot: mutual cooperation. -/
theorem JustBot_vs_CooperateBot (fuel : Nat) :
    ∃ k, outcome (fuel + 2) (JustBot k) CooperateBot = some (.C, .C) := by
  obtain ⟨k, hk⟩ := proofSearch_true_for_JustBot_vs_CooperateBot
  refine ⟨k, ?_⟩
  have hA : play (fuel + 2) (JustBot k) CooperateBot = some .C :=
    JustBot_plays_C_against_CooperateBot k fuel hk
  have hB : play (fuel + 2) CooperateBot (JustBot k) = some .C := by
    simpa [Nat.add_comm] using play_CooperateBot (fuel + 1) (JustBot k)
  exact outcome_of_plays _ _ _ _ _ hA hB

-- TitForTatBot --

/-- The shared guard: `(.bot CooperateBot)` cooperates against `(.bot (DupocBot k))`.
    Provable at budget `atom_cost 2` (a `.bot`-wrapped constant cooperates in two
    steps); we lift it to any `k ≥ atom_cost 2` via monotonicity. -/
theorem proofSearch_botCB_vs_botDupoc (k : Nat) (hk : k ≥ atom_cost 2) :
    proofSearch k (Formula.plays (.bot CooperateBot) (.bot (DupocBot k)) Action.C) = true := by
  refine proofSearch_monotone (atom_cost 2) k _ hk ?_
  exact (proofSearch_spec _ _).2 (Provable.atom
    (atom_complete (.bot CooperateBot) (.bot (DupocBot k)) .C 2
      (by simpa using play_bot_CooperateBot 0 (.bot (DupocBot k)))))

/-- DupocBot (`.bot`-wrapped) cooperates against `.bot CooperateBot`: once the
    shared guard fires, its `.search` takes the `.const .C` branch (after one extra
    fuel step to unwrap the `.bot`). -/
theorem botDupocBot_plays_C_against_bot_CooperateBot (k fuel : Nat)
    (hk : proofSearch k (Formula.plays (.bot CooperateBot) (.bot (DupocBot k)) Action.C) = true) :
    play (fuel + 3) (.bot (DupocBot k)) (.bot CooperateBot) = some .C := by
  show eval (fuel + 3) (.bot (DupocBot k)) (.bot CooperateBot) (.bot (DupocBot k)) = some .C
  rw [eval]   -- unwrap the `.bot` body, exposing DupocBot's `.search`
  show (if proofSearch k (Formula.plays (.bot CooperateBot) (.bot (DupocBot k)) Action.C)
          then eval (fuel + 1) (.bot (DupocBot k)) (.bot CooperateBot) (.const Action.C)
          else eval (fuel + 1) (.bot (DupocBot k)) (.bot CooperateBot) (.const Action.D)) = some .C
  rw [hk]; simp [eval]

/-- TitForTatBot cooperates against `.bot (DupocBot k)`: its probe sees DupocBot
    cooperate against `.bot CooperateBot`, so the `ite` selects the cooperate
    branch. -/
theorem TitForTatBot_plays_C_against_bot_DupocBot (k fuel : Nat)
    (hk : proofSearch k (Formula.plays (.bot CooperateBot) (.bot (DupocBot k)) Action.C) = true) :
    play (fuel + 5) TitForTatBot (.bot (DupocBot k)) = some .C := by
  have hDupoc : play (fuel + 3) (.bot (DupocBot k)) (.bot CooperateBot) = some .C :=
    botDupocBot_plays_C_against_bot_CooperateBot k fuel hk
  have hGuard :
      eval (fuel + 4) TitForTatBot (.bot (DupocBot k)) (.sim .opp (.bot CooperateBot)) = some .C := by
    simpa [Nat.add_assoc] using
      (eval_sim_opp_bot_of_play (fuel + 3) TitForTatBot (.bot (DupocBot k)) CooperateBot Action.C hDupoc)
  have hPlay := play_ite_from_guard
    fuel 4 TitForTatBot (.bot (DupocBot k)) (.sim .opp (.bot CooperateBot))
    (.const Action.C) (.const Action.D)
    Action.C Action.C
    (by rfl) hGuard
  simpa [eval] using hPlay

/-- JustBot's guard against `.bot CooperateBot` is the *same* shared formula
    `.plays (.bot CooperateBot) (.bot (DupocBot k)) .C`, so JustBot cooperates
    against `.bot CooperateBot` whenever the shared guard fires. This is what makes
    TFT (which probes its opponent against `.bot CooperateBot`) cooperate with
    JustBot. -/
theorem JustBot_plays_C_against_bot_CooperateBot (k fuel : Nat)
    (hk : proofSearch k (Formula.plays (.bot CooperateBot) (.bot (DupocBot k)) Action.C) = true) :
    play (fuel + 2) (JustBot k) (.bot CooperateBot) = some .C := by
  refine JustBot_eval_step k fuel (.bot CooperateBot) .C ?_
  simpa using hk

/-- TitForTatBot cooperates against JustBot: its probe sees JustBot cooperate
    against `.bot CooperateBot` (same shared guard), so the `ite` cooperates. -/
theorem TitForTatBot_plays_C_against_JustBot (k fuel : Nat)
    (hk : proofSearch k (Formula.plays (.bot CooperateBot) (.bot (DupocBot k)) Action.C) = true) :
    play (fuel + 4) TitForTatBot (JustBot k) = some .C := by
  have hJust : play (fuel + 2) (JustBot k) (.bot CooperateBot) = some .C :=
    JustBot_plays_C_against_bot_CooperateBot k fuel hk
  have hGuard :
      eval (fuel + 3) TitForTatBot (JustBot k) (.sim .opp (.bot CooperateBot)) = some .C := by
    simpa [Nat.add_assoc] using
      (eval_sim_opp_bot_of_play (fuel + 2) TitForTatBot (JustBot k) CooperateBot Action.C hJust)
  have hPlay := play_ite_from_guard
    fuel 3 TitForTatBot (JustBot k) (.sim .opp (.bot CooperateBot))
    (.const Action.C) (.const Action.D)
    Action.C Action.C
    (by rfl) hGuard
  simpa [eval] using hPlay

/-- JustBot cooperates against TitForTatBot: its guard fires. -/
theorem JustBot_plays_C_against_TitForTatBot (k fuel : Nat)
    (hk : proofSearch k (Formula.plays TitForTatBot (.bot (DupocBot k)) Action.C) = true) :
    play (fuel + 2) (JustBot k) TitForTatBot = some .C := by
  refine JustBot_eval_step k fuel TitForTatBot .C ?_
  simpa using hk

/-- JustBot vs TitForTatBot: mutual cooperation. Both legs ride the shared guard at
    budget `atom_cost 5`. -/
theorem JustBot_vs_TitForTatBot :
    ∃ k, ∀ fuel, outcome (fuel + 5) (JustBot k) TitForTatBot = some (.C, .C) := by
  let k := atom_cost 5
  have hk : proofSearch k (Formula.plays (.bot CooperateBot) (.bot (DupocBot k)) Action.C) = true :=
    proofSearch_botCB_vs_botDupoc k (atom_cost_mono (by omega))
  have hGuardTFT : proofSearch k (Formula.plays TitForTatBot (.bot (DupocBot k)) Action.C) = true := by
    have hPlay : play 5 TitForTatBot (.bot (DupocBot k)) = some .C := by
      simpa using TitForTatBot_plays_C_against_bot_DupocBot k 0 hk
    exact (proofSearch_spec _ _).2 (Provable.atom
      (atom_complete TitForTatBot (.bot (DupocBot k)) .C 5 hPlay))
  refine ⟨k, fun fuel => ?_⟩
  have hA : play (fuel + 5) (JustBot k) TitForTatBot = some .C := by
    simpa [Nat.add_assoc] using JustBot_plays_C_against_TitForTatBot k (fuel + 3) hGuardTFT
  have hB : play (fuel + 5) TitForTatBot (JustBot k) = some .C := by
    simpa [Nat.add_assoc] using TitForTatBot_plays_C_against_JustBot k (fuel + 1) hk
  exact outcome_of_plays _ _ _ _ _ hA hB

end PD.Theorems
