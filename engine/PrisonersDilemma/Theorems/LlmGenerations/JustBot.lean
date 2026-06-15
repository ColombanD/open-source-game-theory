import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Axioms
import PrisonersDilemma.Bots.DupocBot
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Bots.MirrorBot
import PrisonersDilemma.Bots.TitForTatBot
import PrisonersDilemma.Bots.LlmGenerations.JustBot
import PrisonersDilemma.Bots.LlmGenerations.PrudentBot
import PrisonersDilemma.Bots.CupodTrollBot
import PrisonersDilemma.Theorems.CooperateBot
import PrisonersDilemma.Theorems.DefectBot
import PrisonersDilemma.Theorems.DupocBot
import PrisonersDilemma.Theorems.Helpers
import PrisonersDilemma.Theorems.CupodTrollBot
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


--- DBot ---

-- .bot DefectBot cannot play C against anything
theorem ps_false_bot_DefectBot_vs_bot_DupocBot_JB (k : Nat) :
    proofSearch k (.plays (.bot DefectBot) (.bot (DupocBot k)) .C) = false := by
  cases h : proofSearch k (.plays (.bot DefectBot) (.bot (DupocBot k)) .C) with
  | true =>
    exact absurd (proofSearch_sound _ _ h) (by
      rintro ⟨n, hn⟩
      rcases n with _ | _ | n
      · simp [play, eval] at hn
      · simp [play, eval] at hn
      · simp [play, eval, DefectBot] at hn)
  | false => rfl

-- .bot (DupocBot k) defects against .bot DefectBot: its guard fails (DefectBot plays D)
theorem bot_DupocBot_plays_D_against_bot_DefectBot_JB (k fuel : Nat) :
    play (fuel + 3) (.bot (DupocBot k)) (.bot DefectBot) = some .D := by
  have hg := ps_false_bot_DefectBot_vs_bot_DupocBot_JB k
  show eval (fuel + 3) (.bot (DupocBot k)) (.bot DefectBot) (.bot (DupocBot k)) = some .D
  unfold DupocBot at hg ⊢
  simp [eval, Prog.subst, Formula.subst, hg]

-- DBot cooperates against .bot (DupocBot k): its sim probe sees D, so takes .const .C
theorem DBot_plays_C_against_bot_DupocBot_JB (k fuel : Nat) :
    play (fuel + 5) DBot (.bot (DupocBot k)) = some .C := by
  have hInner : play (fuel + 3) (.bot (DupocBot k)) (.bot DefectBot) = some .D :=
    bot_DupocBot_plays_D_against_bot_DefectBot_JB k fuel
  have hGuard : eval (fuel + 4) DBot (.bot (DupocBot k)) (.sim .opp (.bot DefectBot)) = some .D := by
    simpa [Nat.add_assoc] using
      eval_sim_opp_bot_of_play (fuel + 3) DBot (.bot (DupocBot k)) DefectBot .D hInner
  have hPlay := play_ite_from_guard
    fuel 4 DBot (.bot (DupocBot k)) (.sim .opp (.bot DefectBot))
    (.const Action.D) (.const Action.C) Action.C Action.D
    (by rfl) hGuard
  simpa [eval] using hPlay

-- JustBot k defects against .bot DefectBot: its guard (.plays .bot DefectBot ...) fails
theorem JustBot_plays_D_against_bot_DefectBot_JB (k fuel : Nat) :
    play (fuel + 2) (JustBot k) (.bot DefectBot) = some .D := by
  have hg := ps_false_bot_DefectBot_vs_bot_DupocBot_JB k
  show eval (fuel + 2) (JustBot k) (.bot DefectBot) (JustBot k) = some .D
  unfold JustBot
  simp [eval, Prog.subst, Formula.subst, hg]

-- DBot cooperates against JustBot k: sim probe sees JustBot defects → DBot cooperates
theorem DBot_plays_C_against_JustBot_JB (k fuel : Nat) :
    play (fuel + 4) DBot (JustBot k) = some .C := by
  have hInner : play (fuel + 2) (JustBot k) (.bot DefectBot) = some .D :=
    JustBot_plays_D_against_bot_DefectBot_JB k fuel
  have hGuard : eval (fuel + 3) DBot (JustBot k) (.sim .opp (.bot DefectBot)) = some .D := by
    simpa [Nat.add_assoc] using
      eval_sim_opp_bot_of_play (fuel + 2) DBot (JustBot k) DefectBot .D hInner
  have hPlay := play_ite_from_guard
    fuel 3 DBot (JustBot k) (.sim .opp (.bot DefectBot))
    (.const Action.D) (.const Action.C) Action.C Action.D
    (by rfl) hGuard
  simpa [eval] using hPlay

-- JustBot cooperates against DBot when proof search fires
theorem JustBot_plays_C_against_DBot_JB (k fuel : Nat)
    (hk : proofSearch k (.plays DBot (.bot (DupocBot k)) .C) = true) :
    play (fuel + 2) (JustBot k) DBot = some .C := by
  show eval (fuel + 2) (JustBot k) DBot (JustBot k) = some .C
  unfold JustBot
  simp [eval, Prog.subst, Formula.subst, hk]

theorem outcome_JustBot_vs_DBot (n : Nat) :
    ∃ k, outcome (n + 4) (JustBot k) DBot = some (.C, .C) := by
  let k := atom_cost 5
  refine ⟨k, ?_⟩
  have hPlay : play 5 DBot (.bot (DupocBot k)) = some .C := by
    simpa using DBot_plays_C_against_bot_DupocBot_JB k 0
  have hk : proofSearch k (.plays DBot (.bot (DupocBot k)) .C) = true :=
    (proofSearch_spec _ _).2 (Provable.atom (atom_complete DBot (.bot (DupocBot k)) .C 5 hPlay))
  have hA : play (n + 4) (JustBot k) DBot = some .C := by
    have h := JustBot_plays_C_against_DBot_JB k (n + 2) hk
    simpa [Nat.add_assoc] using h
  have hB : play (n + 4) DBot (JustBot k) = some .C :=
    DBot_plays_C_against_JustBot_JB k n
  exact outcome_of_plays _ _ _ _ _ hA hB

--- OBot ---

theorem outcome_JustBot_vs_OBot :
    ∃ k, ∀ n, outcome (n + 6) (JustBot k) OBot = some (.D, .D) := by
  let k := atom_cost 5
  refine ⟨k, fun n => ?_⟩

  have hPSCB : proofSearch k (.plays (.bot CooperateBot) (.bot (DupocBot k)) .C) = true := by
    have hPlay : play 2 (.bot CooperateBot) (.bot (DupocBot k)) = some .C :=
      play_bot_CooperateBot 0 (.bot (DupocBot k))
    exact proofSearch_monotone (atom_cost 2) k _
      (atom_cost_mono (by show 2 ≤ 5; omega))
      ((proofSearch_spec _ _).2 (Provable.atom
        (atom_complete (.bot CooperateBot) (.bot (DupocBot k)) .C 2 hPlay)))

  have hPSDB : proofSearch k (.plays (.bot DefectBot) (.bot (DupocBot k)) .C) = false := by
    cases h : proofSearch k (.plays (.bot DefectBot) (.bot (DupocBot k)) .C) with
    | true  => exact absurd (proofSearch_sound _ _ h) (interp_bot_DefectBot_plays_C_false _)
    | false => rfl

  have hPlay_botDupoc_botCB : ∀ N, play (N + 3) (.bot (DupocBot k)) (.bot CooperateBot) = some .C := by
    intro N
    show eval (N + 3) (.bot (DupocBot k)) (.bot CooperateBot) (.bot (DupocBot k)) = some .C
    show eval (N + 2) (.bot (DupocBot k)) (.bot CooperateBot) (DupocBot k) = some .C
    unfold DupocBot at hPSCB ⊢
    simp [eval, Prog.subst, Formula.subst, hPSCB]

  have hPlay_botDupoc_botDB : ∀ N, play (N + 3) (.bot (DupocBot k)) (.bot DefectBot) = some .D := by
    intro N
    show eval (N + 3) (.bot (DupocBot k)) (.bot DefectBot) (.bot (DupocBot k)) = some .D
    show eval (N + 2) (.bot (DupocBot k)) (.bot DefectBot) (DupocBot k) = some .D
    unfold DupocBot at hPSDB ⊢
    simp [eval, Prog.subst, Formula.subst, hPSDB]

  have hObotD : ∀ N, play (N + 6) OBot (.bot (DupocBot k)) = some .D := by
    intro N
    have hOuter : eval (N + 5) OBot (.bot (DupocBot k)) (.sim .opp (.bot CooperateBot)) = some .C :=
      eval_sim_opp_bot_of_play (N + 4) OBot (.bot (DupocBot k)) CooperateBot .C
        (by simpa [Nat.add_assoc] using hPlay_botDupoc_botCB (N + 1))
    have hInner : eval (N + 4) OBot (.bot (DupocBot k)) (.sim .opp (.bot DefectBot)) = some .D :=
      eval_sim_opp_bot_of_play (N + 3) OBot (.bot (DupocBot k)) DefectBot .D
        (hPlay_botDupoc_botDB N)
    have hPlay := play_ite_from_guard
      N 5 OBot (.bot (DupocBot k)) (.sim .opp (.bot CooperateBot))
      (.ite (.sim .opp (.bot DefectBot)) Action.C (.const Action.C) (.const Action.D))
      (.const Action.D)
      Action.C Action.C
      (by rfl) hOuter
    have hInnerIte :
        eval (N + 5) OBot (.bot (DupocBot k))
          (.ite (.sim .opp (.bot DefectBot)) Action.C (.const Action.C) (.const Action.D)) =
            some .D := by
      simpa [Nat.add_assoc] using
        (eval_ite_from_guard (N + 4) OBot (.bot (DupocBot k))
          (.sim .opp (.bot DefectBot)) (.const Action.C) (.const Action.D)
          Action.C Action.D hInner)
    simpa [Nat.add_assoc, hInnerIte] using hPlay

  have hPSObot : proofSearch k (.plays OBot (.bot (DupocBot k)) .C) = false := by
    cases h : proofSearch k (.plays OBot (.bot (DupocBot k)) .C) with
    | true =>
        exfalso
        obtain ⟨N, hC⟩ := proofSearch_sound _ _ h
        have hD : play 6 OBot (.bot (DupocBot k)) = some .D := hObotD 0
        have hC' : play (max N 6) OBot (.bot (DupocBot k)) = some .C := by
          unfold play
          exact eval_mono_le hC (max N 6) (Nat.le_max_left _ _)
        have hD' : play (max N 6) OBot (.bot (DupocBot k)) = some .D := by
          unfold play
          exact eval_mono_le hD (max N 6) (Nat.le_max_right _ _)
        rw [hC'] at hD'
        cases hD'
    | false => rfl

  have hA : play (n + 6) (JustBot k) OBot = some .D := by
    show eval (n + 6) (JustBot k) OBot (JustBot k) = some .D
    unfold JustBot
    simp [eval, Prog.subst, Formula.subst, hPSObot]

  have hJustC_botCB : ∀ N, play (N + 2) (JustBot k) (.bot CooperateBot) = some .C := by
    intro N
    show eval (N + 2) (JustBot k) (.bot CooperateBot) (JustBot k) = some .C
    unfold JustBot
    simp [eval, Prog.subst, Formula.subst, hPSCB]

  have hJustD_botDB : ∀ N, play (N + 2) (JustBot k) (.bot DefectBot) = some .D := by
    intro N
    show eval (N + 2) (JustBot k) (.bot DefectBot) (JustBot k) = some .D
    unfold JustBot
    simp [eval, Prog.subst, Formula.subst, hPSDB]

  have hB : play (n + 6) OBot (JustBot k) = some .D := by
    have hOuter : eval (n + 5) OBot (JustBot k) (.sim .opp (.bot CooperateBot)) = some .C :=
      eval_sim_opp_bot_of_play (n + 4) OBot (JustBot k) CooperateBot .C
        (by simpa [Nat.add_assoc] using hJustC_botCB (n + 2))
    have hInner : eval (n + 4) OBot (JustBot k) (.sim .opp (.bot DefectBot)) = some .D :=
      eval_sim_opp_bot_of_play (n + 3) OBot (JustBot k) DefectBot .D
        (by simpa [Nat.add_assoc] using hJustD_botDB (n + 1))
    have hPlay := play_ite_from_guard
      n 5 OBot (JustBot k) (.sim .opp (.bot CooperateBot))
      (.ite (.sim .opp (.bot DefectBot)) Action.C (.const Action.C) (.const Action.D))
      (.const Action.D)
      Action.C Action.C
      (by rfl) hOuter
    have hInnerIte :
        eval (n + 5) OBot (JustBot k)
          (.ite (.sim .opp (.bot DefectBot)) Action.C (.const Action.C) (.const Action.D)) =
            some .D := by
      simpa [Nat.add_assoc] using
        (eval_ite_from_guard (n + 4) OBot (JustBot k)
          (.sim .opp (.bot DefectBot)) (.const Action.C) (.const Action.D)
          Action.C Action.D hInner)
    simpa [Nat.add_assoc, hInnerIte] using hPlay

  exact outcome_of_plays _ _ _ _ _ hA hB


/-- CupodTrollBot --

-- JustBot cooperates against CupodTrollBot for large budget: its guard asks
    "does CupodTrollBot play C against (bot DupocBot)?" which is true, so once the
    budget covers the atom the guard fires. -/
theorem JustBot_plays_C_against_CupodTrollBot (k fuel : Nat)
    (hbudget : atom_cost (fuel + 2) ≤ k) :
    play (fuel + 2) (JustBot k) (CupodTrollBot k) = some .C := by
  -- CupodTrollBot cooperates against `.bot (DupocBot k)`.
  have hC : play (fuel + 2) (CupodTrollBot k) (.bot (DupocBot k)) = some .C :=
    CupodTrollBot_cooperates_against_bot k fuel (DupocBot k)
  have hatom : proofSearch (atom_cost (fuel + 2))
      (.plays (CupodTrollBot k) (.bot (DupocBot k)) .C) = true :=
    (proofSearch_spec _ _).2
      (Provable.atom (atom_complete (CupodTrollBot k) (.bot (DupocBot k)) .C (fuel + 2) hC))
  have hg : proofSearch k (.plays (CupodTrollBot k) (.bot (DupocBot k)) .C) = true :=
    proofSearch_monotone _ _ _ hbudget hatom
  show eval (fuel + 2) (JustBot k) (CupodTrollBot k) (JustBot k) = some .C
  unfold JustBot at hg ⊢
  simp [eval, Prog.subst, Formula.subst, hg]

theorem outcome_JustBot_vs_CupodTrollBot :
    ∃ k₂, ∀ k, k₂ < k →
      ∃ fuel, outcome fuel (JustBot k) (CupodTrollBot k) = some (.C, .C) := by
  refine ⟨atom_cost 2, fun k hk => ⟨2, ?_⟩⟩
  have hbudget : atom_cost (0 + 2) ≤ k := by simpa using Nat.le_of_lt hk
  -- Direction A: JustBot cooperates.
  have hA : play 2 (JustBot k) (CupodTrollBot k) = some .C := by
    simpa using JustBot_plays_C_against_CupodTrollBot k 0 hbudget
  -- Direction B: CupodTrollBot cooperates (JustBot ≠ CupodBot).
  have hB : play 2 (CupodTrollBot k) (JustBot k) = some .C := by
    have := CupodTrollBot_cooperates_if_opp_not_CupodBot k 0 (JustBot k)
      (by simp [JustBot, CupodBot])
    simpa using this
  exact outcome_of_plays _ _ _ _ _ hA hB


-- EBot --

theorem outcome_JustBot_vs_EBot :
    ∃ k₂, ∀ k, k₂ < k →
      ∃ fuel, outcome fuel (JustBot k) EBot = some (.C, .C) := by
  refine ⟨atom_cost 6, ?_⟩
  intro k hk
  have h26 : atom_cost 2 ≤ atom_cost 6 := atom_cost_mono (by omega)
  have hb2 : atom_cost 2 ≤ k := by omega
  have hb6 : atom_cost 6 ≤ k := by omega
  -- proof-search facts
  have hPSf : proofSearch k (.plays (.bot DefectBot) (.bot (DupocBot k)) .C) = false := by
    cases h : proofSearch k (.plays (.bot DefectBot) (.bot (DupocBot k)) .C) with
    | true => exact absurd (proofSearch_sound _ _ h) (interp_bot_DefectBot_plays_C_false _)
    | false => rfl
  have hPS1 : proofSearch k (.plays (.bot CooperateBot) (.bot (DupocBot k)) .C) = true :=
    proofSearch_monotone (atom_cost 2) k _ hb2
      ((proofSearch_spec _ _).2 (Provable.atom
        (atom_complete (.bot CooperateBot) (.bot (DupocBot k)) .C 2
          (by simpa using play_bot_CooperateBot 0 (.bot (DupocBot k))))))
  -- DupocBot (wrapped) defects vs .bot DefectBot, cooperates vs .bot CooperateBot
  have lemA : ∀ j, play (j+3) (.bot (DupocBot k)) (.bot DefectBot) = some .D := by
    intro j
    show eval (j+3) (.bot (DupocBot k)) (.bot DefectBot) (.bot (DupocBot k)) = some .D
    unfold DupocBot at hPSf ⊢
    simp [eval, Prog.subst, Formula.subst, hPSf]
  have lemB : ∀ j, play (j+3) (.bot (DupocBot k)) (.bot CooperateBot) = some .C := by
    intro j
    show eval (j+3) (.bot (DupocBot k)) (.bot CooperateBot) (.bot (DupocBot k)) = some .C
    unfold DupocBot at hPS1 ⊢
    simp [eval, Prog.subst, Formula.subst, hPS1]
  -- EBot cooperates whenever the opponent defects vs DefectBot and cooperates vs CooperateBot
  have ebot_C : ∀ (op : Prog),
      (∀ j, play (j+3) op (.bot DefectBot) = some .D) →
      (∀ j, play (j+3) op (.bot CooperateBot) = some .C) →
      play 6 EBot op = some .C := by
    intro op hD hC
    have hG1 : eval 5 EBot op (.sim .opp (.bot DefectBot)) = some .D :=
      eval_sim_opp_bot_of_play 4 EBot op DefectBot Action.D (hD 1)
    have hG2 : eval 4 EBot op (.sim .opp (.bot CooperateBot)) = some .C :=
      eval_sim_opp_bot_of_play 3 EBot op CooperateBot Action.C (hC 0)
    have hInner : eval 5 EBot op
        (.ite (.sim .opp (.bot CooperateBot)) Action.C (.const Action.C)
          (.ite (.sim .opp (.bot MirrorBot)) Action.C (.const Action.C) (.const Action.D))) = some .C := by
      simpa using (eval_ite_from_guard 4 EBot op (.sim .opp (.bot CooperateBot)) (.const Action.C)
        (.ite (.sim .opp (.bot MirrorBot)) Action.C (.const Action.C) (.const Action.D))
        Action.C Action.C hG2)
    have hPlay := play_ite_from_guard 0 5 EBot op (.sim .opp (.bot DefectBot))
      (.const Action.D)
      (.ite (.sim .opp (.bot CooperateBot)) Action.C (.const Action.C)
        (.ite (.sim .opp (.bot MirrorBot)) Action.C (.const Action.C) (.const Action.D)))
      Action.C Action.D
      (by rfl) hG1
    simpa [hInner] using hPlay
  have hEO : play 6 EBot (.bot (DupocBot k)) = some .C := ebot_C (.bot (DupocBot k)) lemA lemB
  have hPS3 : proofSearch k (.plays EBot (.bot (DupocBot k)) .C) = true :=
    proofSearch_monotone (atom_cost 6) k _ hb6
      ((proofSearch_spec _ _).2 (Provable.atom
        (atom_complete EBot (.bot (DupocBot k)) .C 6 hEO)))
  -- JustBot vs EBot: cooperates
  have hJ : ∀ j, play (j+2) (JustBot k) EBot = some .C := by
    intro j
    show eval (j+2) (JustBot k) EBot (JustBot k) = some .C
    unfold JustBot
    unfold DupocBot at hPS3 ⊢
    simp [eval, Prog.subst, Formula.subst, hPS3]
  -- JustBot vs .bot DefectBot defects, vs .bot CooperateBot cooperates
  have lemC : ∀ j, play (j+2) (JustBot k) (.bot DefectBot) = some .D := by
    intro j
    show eval (j+2) (JustBot k) (.bot DefectBot) (JustBot k) = some .D
    unfold JustBot
    unfold DupocBot at hPSf ⊢
    simp [eval, Prog.subst, Formula.subst, hPSf]
  have lemD : ∀ j, play (j+2) (JustBot k) (.bot CooperateBot) = some .C := by
    intro j
    show eval (j+2) (JustBot k) (.bot CooperateBot) (JustBot k) = some .C
    unfold JustBot
    unfold DupocBot at hPS1 ⊢
    simp [eval, Prog.subst, Formula.subst, hPS1]
  have hEJ6 : play 6 EBot (JustBot k) = some .C :=
    ebot_C (JustBot k) (fun j => lemC (j+1)) (fun j => lemD (j+1))
  exact ⟨6, outcome_of_plays 6 (JustBot k) EBot .C .C (hJ 4) hEJ6⟩

end PD.Theorems
