import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Axioms
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Bots.DBot
import PrisonersDilemma.Bots.OBot
import PrisonersDilemma.Bots.TitForTatBot
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Bots.LlmGenerations.PrudentBot
import PrisonersDilemma.Theorems.CooperateBot
import PrisonersDilemma.Theorems.DefectBot
import PrisonersDilemma.Theorems.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.SizeLemmas

open PD
open PD.Axioms
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

/-- PrudentBot's head, unfolded once. The cooperation `.search` is at the root;
    the prudence (`opp defects vs DefectBot`) search is folded into its THEN
    branch. -/
theorem PrudentBot_eq (k : Nat) :
    PrudentBot k = .search k (Formula.plays .opp .self Action.C)
      (.search k (Formula.plays .opp (.bot DefectBot) Action.D)
        (.const Action.C) (.const Action.D))
      (.const Action.D) := rfl


/-- Core lemma for every matchup in which PrudentBot defects: if the opponent
    `opp` does **not** cooperate with PrudentBot (the outer cooperation search is
    false), PrudentBot lands in the root `.search`'s else-branch and defects. The
    inner prudence search is never reached. -/
theorem PrudentBot_plays_D_of_search_false (k fuel : Nat) (opponent : Prog)
    (hf : proofSearch k (Formula.plays opponent (PrudentBot k) Action.C) = false) :
    play (fuel + 2) (PrudentBot k) opponent = some .D := by
  show eval (fuel + 2) (PrudentBot k) opponent (PrudentBot k) = some .D
  rw [PrudentBot_eq]
  show (if proofSearch k ((Formula.plays .opp .self Action.C).subst (PrudentBot k) opponent)
          then eval (fuel + 1) (PrudentBot k) opponent
                (.search k (Formula.plays .opp (.bot DefectBot) Action.D)
                  (.const Action.C) (.const Action.D))
          else eval (fuel + 1) (PrudentBot k) opponent (.const Action.D)) = some .D
  rw [show (Formula.plays Prog.opp Prog.self Action.C).subst (PrudentBot k) opponent
        = Formula.plays opponent (PrudentBot k) Action.C from rfl, hf]
  rfl

-- DefectBot --

/-- The outer cooperation search "DefectBot cooperates with PrudentBot" is false:
    DefectBot never plays C. -/
theorem proofSearch_false_DefectBot_vs_PrudentBot (k : Nat) :
    proofSearch k (Formula.plays DefectBot (PrudentBot k) Action.C) = false := by
  cases h : proofSearch k (Formula.plays DefectBot (PrudentBot k) Action.C) with
  | true  => exact absurd (proofSearch_sound _ _ h) (interp_DefectBot_plays_C_false _)
  | false => rfl

/-- PrudentBot defects against DefectBot (outer cooperation search fails). -/
theorem PrudentBot_plays_D_against_DefectBot (k fuel : Nat) :
    play (fuel + 2) (PrudentBot k) DefectBot = some .D :=
  PrudentBot_plays_D_of_search_false k fuel DefectBot
    (proofSearch_false_DefectBot_vs_PrudentBot k)

/-- PrudentBot vs DefectBot: mutual defection, (D, D). -/
theorem PrudentBot_vs_DefectBot (k fuel : Nat) :
    outcome (fuel + 2) (PrudentBot k) DefectBot = some (.D, .D) := by
  have hA : play (fuel + 2) (PrudentBot k) DefectBot = some .D :=
    PrudentBot_plays_D_against_DefectBot k fuel
  have hB : play (fuel + 2) DefectBot (PrudentBot k) = some .D := by
    simpa [Nat.add_comm] using play_DefectBot (fuel + 1) (PrudentBot k)
  exact outcome_of_plays _ _ _ _ _ hA hB

-- CooperateBot --

/-- The inner prudence search "CooperateBot defects vs DefectBot" is false:
    CooperateBot cooperates against everything, so it never plays D. -/
theorem proofSearch_false_CooperateBot_prudence (k : Nat) :
    proofSearch k (Formula.plays CooperateBot (.bot DefectBot) Action.D) = false := by
  cases h : proofSearch k (Formula.plays CooperateBot (.bot DefectBot) Action.D) with
  | true  =>
    exfalso
    obtain ⟨n, hn⟩ := proofSearch_sound _ _ h
    cases n with
    | zero   => simp [play, eval] at hn
    | succ m =>
        rw [show play (m+1) CooperateBot (.bot DefectBot) = some .C from by
              simpa [Nat.add_comm] using play_CooperateBot m (.bot DefectBot)] at hn
        cases hn
  | false => rfl

/-- PrudentBot defects against CooperateBot. The outer cooperation search may
    succeed (CooperateBot does cooperate), but then the inner *prudence* search
    fails (CooperateBot is a sucker — it cooperates vs DefectBot), so PrudentBot
    defects via the inner else-branch. Either way: defect. -/
theorem PrudentBot_plays_D_against_CooperateBot (k fuel : Nat) :
    play (fuel + 3) (PrudentBot k) CooperateBot = some .D := by
  show eval (fuel + 3) (PrudentBot k) CooperateBot (PrudentBot k) = some .D
  rw [PrudentBot_eq]
  show (if proofSearch k ((Formula.plays .opp .self Action.C).subst (PrudentBot k) CooperateBot)
          then eval (fuel + 2) (PrudentBot k) CooperateBot
                (.search k (Formula.plays .opp (.bot DefectBot) Action.D)
                  (.const Action.C) (.const Action.D))
          else eval (fuel + 2) (PrudentBot k) CooperateBot (.const Action.D)) = some .D
  have hinner := proofSearch_false_CooperateBot_prudence k
  by_cases hc : proofSearch k ((Formula.plays Prog.opp Prog.self Action.C).subst (PrudentBot k) CooperateBot) = true
  · rw [if_pos hc]
    show (if proofSearch k ((Formula.plays .opp (.bot DefectBot) Action.D).subst (PrudentBot k) CooperateBot)
            then eval (fuel + 1) (PrudentBot k) CooperateBot (.const Action.C)
            else eval (fuel + 1) (PrudentBot k) CooperateBot (.const Action.D)) = some .D
    rw [show (Formula.plays Prog.opp (.bot DefectBot) Action.D).subst (PrudentBot k) CooperateBot
          = Formula.plays CooperateBot (.bot DefectBot) Action.D from rfl, hinner]
    rfl
  · rw [if_neg hc]; rfl

/-- PrudentBot vs CooperateBot: PrudentBot exploits the sucker, (D, C). -/
theorem PrudentBot_vs_CooperateBot (k fuel : Nat) :
    outcome (fuel + 3) (PrudentBot k) CooperateBot = some (.D, .C) := by
  have hA : play (fuel + 3) (PrudentBot k) CooperateBot = some .D :=
    PrudentBot_plays_D_against_CooperateBot k fuel
  have hB : play (fuel + 3) CooperateBot (PrudentBot k) = some .C := by
    simpa [Nat.add_comm] using play_CooperateBot (fuel + 2) (PrudentBot k)
  exact outcome_of_plays _ _ _ _ _ hA hB

-- Probe lemmas: how PrudentBot responds to the canonical probe bots that
-- DBot/OBot/TFT simulate it against.

/-- PrudentBot defects against `.bot DefectBot`: the outer cooperation search
    "DefectBot cooperates with PrudentBot" is false. -/
theorem PrudentBot_plays_D_vs_bot_DB (k fuel : Nat) :
    play (fuel + 2) (PrudentBot k) (.bot DefectBot) = some .D := by
  apply PrudentBot_plays_D_of_search_false
  cases h : proofSearch k (Formula.plays (.bot DefectBot) (PrudentBot k) Action.C) with
  | true  => exact absurd (proofSearch_sound _ _ h) (interp_bot_DefectBot_plays_C_false _)
  | false => rfl

/-- PrudentBot defects against `.bot CooperateBot`: outer cooperation search may
    succeed, but the inner prudence search ("CooperateBot defects vs DefectBot")
    fails, so PrudentBot defects. -/
theorem PrudentBot_plays_D_vs_bot_CB (k fuel : Nat) :
    play (fuel + 3) (PrudentBot k) (.bot CooperateBot) = some .D := by
  show eval (fuel + 3) (PrudentBot k) (.bot CooperateBot) (PrudentBot k) = some .D
  rw [PrudentBot_eq]
  show (if proofSearch k ((Formula.plays .opp .self Action.C).subst (PrudentBot k) (.bot CooperateBot))
          then eval (fuel + 2) (PrudentBot k) (.bot CooperateBot)
                (.search k (Formula.plays .opp (.bot DefectBot) Action.D)
                  (.const Action.C) (.const Action.D))
          else eval (fuel + 2) (PrudentBot k) (.bot CooperateBot) (.const Action.D)) = some .D
  have hinner : proofSearch k (Formula.plays (.bot CooperateBot) (.bot DefectBot) Action.D) = false := by
    cases h : proofSearch k (Formula.plays (.bot CooperateBot) (.bot DefectBot) Action.D) with
    | true  =>
      exfalso
      obtain ⟨n, hn⟩ := proofSearch_sound _ _ h
      cases n with
      | zero   => simp [play, eval] at hn
      | succ m =>
          cases m with
          | zero => simp [play, eval] at hn
          | succ j =>
              rw [show play (j+2) (.bot CooperateBot) (.bot DefectBot) = some .C from by
                    simp [play, eval, CooperateBot]] at hn
              cases hn
    | false => rfl
  by_cases hc : proofSearch k ((Formula.plays Prog.opp Prog.self Action.C).subst (PrudentBot k) (.bot CooperateBot)) = true
  · rw [if_pos hc]
    show (if proofSearch k ((Formula.plays .opp (.bot DefectBot) Action.D).subst (PrudentBot k) (.bot CooperateBot))
            then eval (fuel + 1) (PrudentBot k) (.bot CooperateBot) (.const Action.C)
            else eval (fuel + 1) (PrudentBot k) (.bot CooperateBot) (.const Action.D)) = some .D
    rw [show (Formula.plays Prog.opp (.bot DefectBot) Action.D).subst (PrudentBot k) (.bot CooperateBot)
          = Formula.plays (.bot CooperateBot) (.bot DefectBot) Action.D from rfl, hinner]
    rfl
  · rw [if_neg hc]; rfl

-- DBot --

/-- DBot cooperates with PrudentBot: DBot probes PrudentBot against `.bot DefectBot`,
    sees it defect (guard value D ≠ test C), and takes its else-branch (cooperate). -/
theorem DBot_plays_C_vs_PrudentBot (k fuel : Nat) :
    play (fuel + 4) DBot (PrudentBot k) = some .C := by
  have hProbe : play (fuel + 2) (PrudentBot k) (.bot DefectBot) = some .D :=
    PrudentBot_plays_D_vs_bot_DB k fuel
  have hGuard : eval (fuel + 3) DBot (PrudentBot k) (.sim .opp (.bot DefectBot)) = some .D :=
    eval_sim_opp_bot_of_play (fuel + 2) DBot (PrudentBot k) DefectBot Action.D hProbe
  have hPlay := eval_ite_from_guard
    (fuel + 3) DBot (PrudentBot k) (.sim .opp (.bot DefectBot))
    (.const Action.D) (.const Action.C)
    Action.C Action.D
    hGuard
  show eval (fuel + 4) DBot (PrudentBot k) DBot = some .C
  rw [show DBot = .ite (.sim .opp (.bot DefectBot)) Action.C (.const Action.D) (.const Action.C) from rfl] at *
  rw [hPlay]; rfl

/-- The inner prudence search "DBot defects vs DefectBot" is false: DBot probes
    DefectBot (which defects), so DBot takes its else-branch and *cooperates*
    against DefectBot. Hence it is a sucker and the prudence atom is false. -/
theorem proofSearch_false_DBot_prudence (k : Nat) :
    proofSearch k (Formula.plays DBot (.bot DefectBot) Action.D) = false := by
  cases h : proofSearch k (Formula.plays DBot (.bot DefectBot) Action.D) with
  | true  =>
    exfalso
    obtain ⟨n, hn⟩ := proofSearch_sound _ _ h
    -- DBot cooperates vs `.bot DefectBot`, so it never plays D there.
    have hC : ∀ m, play (m + 4) DBot (.bot DefectBot) = some .C := by
      intro m
      have hProbe : play (m + 2) (.bot DefectBot) (.bot DefectBot) = some .D := by
        simpa [Nat.add_comm] using play_bot_DefectBot m (.bot DefectBot)
      have hGuard : eval (m + 3) DBot (.bot DefectBot) (.sim .opp (.bot DefectBot)) = some .D :=
        eval_sim_opp_bot_of_play (m + 2) DBot (.bot DefectBot) DefectBot Action.D hProbe
      have hPlay := eval_ite_from_guard
        (m + 3) DBot (.bot DefectBot) (.sim .opp (.bot DefectBot))
        (.const Action.D) (.const Action.C) Action.C Action.D hGuard
      show eval (m + 4) DBot (.bot DefectBot) DBot = some .C
      rw [show DBot = .ite (.sim .opp (.bot DefectBot)) Action.C (.const Action.D) (.const Action.C) from rfl] at *
      rw [hPlay]; rfl
    have hmono : play (n + 4) DBot (.bot DefectBot) = some .D := by
      unfold play at hn ⊢; exact eval_mono_le hn (n + 4) (by omega)
    rw [hC n] at hmono; cases hmono
  | false => rfl

/-- PrudentBot defects against DBot. Like CooperateBot, DBot cooperates with
    PrudentBot, but DBot is a sucker against DefectBot, so the inner prudence
    search fails and PrudentBot defects. -/
theorem PrudentBot_plays_D_against_DBot (k fuel : Nat) :
    play (fuel + 3) (PrudentBot k) DBot = some .D := by
  show eval (fuel + 3) (PrudentBot k) DBot (PrudentBot k) = some .D
  rw [PrudentBot_eq]
  show (if proofSearch k ((Formula.plays .opp .self Action.C).subst (PrudentBot k) DBot)
          then eval (fuel + 2) (PrudentBot k) DBot
                (.search k (Formula.plays .opp (.bot DefectBot) Action.D)
                  (.const Action.C) (.const Action.D))
          else eval (fuel + 2) (PrudentBot k) DBot (.const Action.D)) = some .D
  have hinner := proofSearch_false_DBot_prudence k
  by_cases hc : proofSearch k ((Formula.plays Prog.opp Prog.self Action.C).subst (PrudentBot k) DBot) = true
  · rw [if_pos hc]
    show (if proofSearch k ((Formula.plays .opp (.bot DefectBot) Action.D).subst (PrudentBot k) DBot)
            then eval (fuel + 1) (PrudentBot k) DBot (.const Action.C)
            else eval (fuel + 1) (PrudentBot k) DBot (.const Action.D)) = some .D
    rw [show (Formula.plays Prog.opp (.bot DefectBot) Action.D).subst (PrudentBot k) DBot
          = Formula.plays DBot (.bot DefectBot) Action.D from rfl, hinner]
    rfl
  · rw [if_neg hc]; rfl

/-- PrudentBot vs DBot: PrudentBot exploits, (D, C). -/
theorem outcome_PrudentBot_vs_DBot :
    ∃ k₂, ∀ k, k₂ < k →
      ∃ fuel, outcome fuel (PrudentBot k) DBot = some (.D, .C) := by
  refine ⟨0, fun k _ => ⟨7, ?_⟩⟩
  have hA : play 7 (PrudentBot k) DBot = some .D := by
    simpa using PrudentBot_plays_D_against_DBot k 4
  have hB : play 7 DBot (PrudentBot k) = some .C := by
    simpa using DBot_plays_C_vs_PrudentBot k 3
  exact outcome_of_plays _ _ _ _ _ hA hB

-- TitForTatBot --

/-- TFT defects against PrudentBot: TFT probes PrudentBot against `.bot CooperateBot`,
    sees it defect (guard D ≠ test C), takes its else-branch and defects. -/
theorem TFT_plays_D_vs_PrudentBot (k fuel : Nat) :
    play (fuel + 5) TitForTatBot (PrudentBot k) = some .D := by
  have hProbe : play (fuel + 3) (PrudentBot k) (.bot CooperateBot) = some .D :=
    PrudentBot_plays_D_vs_bot_CB k fuel
  have hGuard : eval (fuel + 4) TitForTatBot (PrudentBot k)
      (.sim .opp (.bot CooperateBot)) = some .D :=
    eval_sim_opp_bot_of_play (fuel + 3) TitForTatBot (PrudentBot k) CooperateBot Action.D hProbe
  have hPlay := eval_ite_from_guard
    (fuel + 4) TitForTatBot (PrudentBot k) (.sim .opp (.bot CooperateBot))
    (.const Action.C) (.const Action.D) Action.C Action.D hGuard
  show eval (fuel + 5) TitForTatBot (PrudentBot k) TitForTatBot = some .D
  rw [show TitForTatBot = .ite (.sim .opp (.bot CooperateBot)) Action.C
        (.const Action.C) (.const Action.D) from rfl] at *
  rw [hPlay]; rfl

theorem interp_TFT_plays_C_vs_PrudentBot_false (k : Nat) :
    ¬ (Formula.plays TitForTatBot (PrudentBot k) .C).interp := by
  rintro ⟨n, hn⟩
  have hD : play (n + 6) TitForTatBot (PrudentBot k) = some .D := by
    simpa [Nat.add_assoc] using TFT_plays_D_vs_PrudentBot k (n + 1)
  have hC : play (n + 6) TitForTatBot (PrudentBot k) = some .C := by
    unfold play at hn ⊢; exact eval_mono_le hn (n + 6) (by omega)
  rw [hC] at hD; cases hD

theorem proofSearch_false_TFT_vs_PrudentBot (k : Nat) :
    proofSearch k (Formula.plays TitForTatBot (PrudentBot k) Action.C) = false := by
  cases h : proofSearch k (Formula.plays TitForTatBot (PrudentBot k) Action.C) with
  | true  => exact absurd (proofSearch_sound _ _ h) (interp_TFT_plays_C_vs_PrudentBot_false k)
  | false => rfl

theorem PrudentBot_plays_D_against_TFT (k fuel : Nat) :
    play (fuel + 2) (PrudentBot k) TitForTatBot = some .D :=
  PrudentBot_plays_D_of_search_false k fuel TitForTatBot
    (proofSearch_false_TFT_vs_PrudentBot k)

/-- PrudentBot vs TitForTatBot: mutual defection, (D, D). -/
theorem outcome_PrudentBot_vs_TitForTatBot :
    ∃ k₂, ∀ k, k₂ < k →
      ∃ fuel, outcome fuel (PrudentBot k) TitForTatBot = some (.D, .D) := by
  refine ⟨0, fun k _ => ⟨6, ?_⟩⟩
  have hA : play 6 (PrudentBot k) TitForTatBot = some .D := by
    simpa using PrudentBot_plays_D_against_TFT k 4
  have hB : play 6 TitForTatBot (PrudentBot k) = some .D := by
    simpa using TFT_plays_D_vs_PrudentBot k 1
  exact outcome_of_plays _ _ _ _ _ hA hB

-- OBot --

/-- OBot defects against PrudentBot: OBot's first probe is the opponent against
    `.bot CooperateBot`; PrudentBot defects there (D ≠ test C), so OBot takes its
    outermost else-branch and defects. -/
theorem OBot_plays_D_vs_PrudentBot (k fuel : Nat) :
    play (fuel + 5) OBot (PrudentBot k) = some .D := by
  have hProbe : play (fuel + 3) (PrudentBot k) (.bot CooperateBot) = some .D :=
    PrudentBot_plays_D_vs_bot_CB k fuel
  have hGuard : eval (fuel + 4) OBot (PrudentBot k)
      (.sim .opp (.bot CooperateBot)) = some .D :=
    eval_sim_opp_bot_of_play (fuel + 3) OBot (PrudentBot k) CooperateBot Action.D hProbe
  have hPlay := eval_ite_from_guard
    (fuel + 4) OBot (PrudentBot k) (.sim .opp (.bot CooperateBot))
    (.ite (.sim .opp (.bot DefectBot)) Action.C (.const Action.C) (.const Action.D))
    (.const Action.D) Action.C Action.D hGuard
  show eval (fuel + 5) OBot (PrudentBot k) OBot = some .D
  rw [show OBot = .ite (.sim .opp (.bot CooperateBot)) Action.C
        (.ite (.sim .opp (.bot DefectBot)) Action.C (.const Action.C) (.const Action.D))
        (.const Action.D) from rfl] at *
  rw [hPlay]; rfl

theorem interp_OBot_plays_C_vs_PrudentBot_false (k : Nat) :
    ¬ (Formula.plays OBot (PrudentBot k) .C).interp := by
  rintro ⟨n, hn⟩
  have hD : play (n + 6) OBot (PrudentBot k) = some .D := by
    simpa [Nat.add_assoc] using OBot_plays_D_vs_PrudentBot k (n + 1)
  have hC : play (n + 6) OBot (PrudentBot k) = some .C := by
    unfold play at hn ⊢; exact eval_mono_le hn (n + 6) (by omega)
  rw [hC] at hD; cases hD

theorem proofSearch_false_OBot_vs_PrudentBot (k : Nat) :
    proofSearch k (Formula.plays OBot (PrudentBot k) Action.C) = false := by
  cases h : proofSearch k (Formula.plays OBot (PrudentBot k) Action.C) with
  | true  => exact absurd (proofSearch_sound _ _ h) (interp_OBot_plays_C_vs_PrudentBot_false k)
  | false => rfl

theorem PrudentBot_plays_D_against_OBot (k fuel : Nat) :
    play (fuel + 2) (PrudentBot k) OBot = some .D :=
  PrudentBot_plays_D_of_search_false k fuel OBot
    (proofSearch_false_OBot_vs_PrudentBot k)

/-- PrudentBot vs OBot: mutual defection, (D, D). -/
theorem outcome_PrudentBot_vs_OBot :
    ∃ k₂, ∀ k, k₂ < k →
      ∃ fuel, outcome fuel (PrudentBot k) OBot = some (.D, .D) := by
  refine ⟨0, fun k _ => ⟨6, ?_⟩⟩
  have hA : play 6 (PrudentBot k) OBot = some .D := by
    simpa using PrudentBot_plays_D_against_OBot k 4
  have hB : play 6 OBot (PrudentBot k) = some .D := by
    simpa using OBot_plays_D_vs_PrudentBot k 1
  exact outcome_of_plays _ _ _ _ _ hA hB

end PD.Theorems
