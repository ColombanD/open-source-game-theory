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


/-- PrudentBot's head, unfolded once. -/
theorem PrudentBot_eq (k : Nat) :
    PrudentBot k = .ite (.sim .opp (.bot DefectBot)) Action.D
      (.search k (Formula.plays .opp .self Action.C) (.const Action.C) (.const Action.D))
      (.const Action.D) := rfl

-- CooperateBot --

/-- PrudentBot defects against CooperateBot: CooperateBot cooperates against
    `.bot DefectBot` (it cooperates against everything), so the probe yields C ≠ D,
    PrudentBot takes the else-branch and defects. -/
theorem PrudentBot_plays_D_against_CooperateBot (k fuel : Nat) :
    play (fuel + 4) (PrudentBot k) CooperateBot = some .D := by
  -- probe: CooperateBot vs `.bot DefectBot` plays C.
  have hCoop : play (fuel + 2) CooperateBot (.bot DefectBot) = some .C := by
    simpa [Nat.add_comm] using play_CooperateBot (fuel + 1) (.bot DefectBot)
  have hGuard :
      eval (fuel + 3) (PrudentBot k) CooperateBot (.sim .opp (.bot DefectBot)) = some .C := by
    simpa [Nat.add_assoc] using
      (eval_sim_opp_bot_of_play (fuel + 2) (PrudentBot k) CooperateBot DefectBot Action.C hCoop)
  have hPlay := play_ite_from_guard
    fuel 3 (PrudentBot k) CooperateBot (.sim .opp (.bot DefectBot))
    (.search k (Formula.plays .opp .self Action.C) (.const Action.C) (.const Action.D))
    (.const Action.D)
    Action.D Action.C
    (PrudentBot_eq k) hGuard
  -- guard value C ≠ test D, so the else-branch `.const .D` runs.
  simpa [eval] using hPlay

/-- PrudentBot vs CooperateBot: PrudentBot exploits, (D, C). -/
theorem PrudentBot_vs_CooperateBot (k fuel : Nat) :
    outcome (fuel + 4) (PrudentBot k) CooperateBot = some (.D, .C) := by
  have hA : play (fuel + 4) (PrudentBot k) CooperateBot = some .D :=
    PrudentBot_plays_D_against_CooperateBot k fuel
  have hB : play (fuel + 4) CooperateBot (PrudentBot k) = some .C := by
    simpa [Nat.add_comm] using play_CooperateBot (fuel + 3) (PrudentBot k)
  exact outcome_of_plays _ _ _ _ _ hA hB

-- DefectBot --

/-- The inner search guard substituted against DefectBot is false: the guard asks
    "does DefectBot cooperate against PrudentBot?", and DefectBot never plays C. -/
theorem proofSearch_false_for_PrudentBot_inner_DefectBot (k : Nat) :
    proofSearch k (Formula.plays DefectBot (PrudentBot k) Action.C) = false := by
  cases h : proofSearch k (Formula.plays DefectBot (PrudentBot k) Action.C) with
  | true  => exact absurd (proofSearch_sound _ _ h) (interp_DefectBot_plays_C_false _)
  | false => rfl

/-- PrudentBot defects against DefectBot: DefectBot defects against `.bot DefectBot`
    (guard == D), so PrudentBot descends into its search; that search ("does
    DefectBot cooperate against me?") fails, so PrudentBot defects. -/
theorem PrudentBot_plays_D_against_DefectBot (k fuel : Nat) :
    play (fuel + 4) (PrudentBot k) DefectBot = some .D := by
  -- probe: DefectBot vs `.bot DefectBot` plays D.
  have hDef : play (fuel + 2) DefectBot (.bot DefectBot) = some .D := by
    simpa [Nat.add_comm] using play_DefectBot (fuel + 1) (.bot DefectBot)
  have hGuard :
      eval (fuel + 3) (PrudentBot k) DefectBot (.sim .opp (.bot DefectBot)) = some .D := by
    simpa [Nat.add_assoc] using
      (eval_sim_opp_bot_of_play (fuel + 2) (PrudentBot k) DefectBot DefectBot Action.D hDef)
  have hPlay := play_ite_from_guard
    fuel 3 (PrudentBot k) DefectBot (.sim .opp (.bot DefectBot))
    (.search k (Formula.plays .opp .self Action.C) (.const Action.C) (.const Action.D))
    (.const Action.D)
    Action.D Action.D
    (PrudentBot_eq k) hGuard
  -- guard value D == test D, so the then-branch (`.search …`) runs.
  rw [if_pos (by rfl)] at hPlay
  -- the search guard is `.plays DefectBot (PrudentBot k) .C`, which is false.
  have hg := proofSearch_false_for_PrudentBot_inner_DefectBot k
  rw [hPlay]
  show eval (fuel + 3) (PrudentBot k) DefectBot
        (.search k (Formula.plays .opp .self Action.C) (.const Action.C) (.const Action.D)) = some .D
  rw [eval]
  -- the guard's subst form is defeq to `.plays DefectBot (PrudentBot k) .C`.
  show (if proofSearch k (Formula.plays DefectBot (PrudentBot k) Action.C)
          then eval (fuel + 2) (PrudentBot k) DefectBot (.const Action.C)
          else eval (fuel + 2) (PrudentBot k) DefectBot (.const Action.D)) = some .D
  rw [hg]
  simp [eval]

/-- PrudentBot vs DefectBot: mutual defection, (D, D). -/
theorem PrudentBot_vs_DefectBot (k fuel : Nat) :
    outcome (fuel + 4) (PrudentBot k) DefectBot = some (.D, .D) := by
  have hA : play (fuel + 4) (PrudentBot k) DefectBot = some .D :=
    PrudentBot_plays_D_against_DefectBot k fuel
  have hB : play (fuel + 4) DefectBot (PrudentBot k) = some .D := by
    simpa [Nat.add_comm] using play_DefectBot (fuel + 3) (PrudentBot k)
  exact outcome_of_plays _ _ _ _ _ hA hB


-- DBot --

theorem ps_false_bot_DB_plays_C (k : Nat) (q : Prog) :
    proofSearch k (.plays (.bot DefectBot) q .C) = false := by
  cases h : proofSearch k (.plays (.bot DefectBot) q .C) with
  | true =>
    exfalso
    obtain ⟨n, hn⟩ := proofSearch_sound _ _ h
    rcases n with _ | _ | n
    · simp [play, eval] at hn
    · simp [play, eval] at hn
    · simp [play, eval, DefectBot] at hn
  | false => rfl

/-- PrudentBot vs DBot at the concrete fuel `6`: PrudentBot defects, DBot
    cooperates, (D, C). -/
theorem outcome_PrudentBot_vs_DBot_fuel (k : Nat) :
    outcome 6 (PrudentBot k) DBot = some (.D, .C) := by
  have hfalse := ps_false_bot_DB_plays_C k
    ((Prog.opp.sim (Prog.const Action.D).bot).ite Action.D
      (Prog.search k (Formula.plays Prog.opp Prog.self Action.C) (Prog.const Action.C)
        (Prog.const Action.D))
      (Prog.const Action.D))
  simp only [DefectBot] at hfalse
  simp [outcome, play, eval, PrudentBot, DBot, DefectBot, Prog.subst, Formula.subst,
        show (Action.D == Action.C) = false from rfl,
        show (Action.C == Action.D) = false from rfl,
        hfalse]

theorem outcome_PrudentBot_vs_DBot :
    ∃ k₂, ∀ k, k₂ < k →
      ∃ fuel, outcome fuel (PrudentBot k) DBot = some (.D, .C) :=
  ⟨0, fun k _ => ⟨6, outcome_PrudentBot_vs_DBot_fuel k⟩⟩


-- OBot --

theorem PrudentBot_plays_D_vs_bot_CB (k fuel : Nat) :
    play (fuel + 4) (PrudentBot k) (.bot CooperateBot) = some .D := by
  have hProbe : play (fuel + 2) (.bot CooperateBot) (.bot DefectBot) = some .C := by
    show eval (fuel + 2) (.bot CooperateBot) (.bot DefectBot) (.bot CooperateBot) = some .C
    simp [eval, CooperateBot]
  have hGuard : eval (fuel + 3) (PrudentBot k) (.bot CooperateBot)
                  (.sim .opp (.bot DefectBot)) = some .C := by
    simpa [Nat.add_assoc] using
      (eval_sim_opp_bot_of_play (fuel + 2) (PrudentBot k) (.bot CooperateBot)
        DefectBot Action.C hProbe)
  have hPlay := play_ite_from_guard
    fuel 3 (PrudentBot k) (.bot CooperateBot) (.sim .opp (.bot DefectBot))
    (.search k (.plays .opp .self Action.C) (.const Action.C) (.const Action.D))
    (.const Action.D)
    Action.D Action.C
    (by rfl) hGuard
  simpa [eval] using hPlay

theorem proofSearch_false_botDB_vs_PrudentBot (k : Nat) :
    proofSearch k (.plays (.bot DefectBot) (PrudentBot k) .C) = false := by
  cases h : proofSearch k (.plays (.bot DefectBot) (PrudentBot k) .C) with
  | true  => exact absurd (proofSearch_sound _ _ h)
                          (interp_bot_DefectBot_plays_C_false _)
  | false => rfl

theorem OBot_plays_D_vs_PrudentBot (k fuel : Nat) :
    play (fuel + 6) OBot (PrudentBot k) = some .D := by
  have hPrudCB : play (fuel + 4) (PrudentBot k) (.bot CooperateBot) = some .D :=
    PrudentBot_plays_D_vs_bot_CB k fuel
  have hGuard : eval (fuel + 5) OBot (PrudentBot k)
                  (.sim .opp (.bot CooperateBot)) = some .D := by
    simpa [Nat.add_assoc] using
      (eval_sim_opp_bot_of_play (fuel + 4) OBot (PrudentBot k)
        CooperateBot Action.D hPrudCB)
  have hPlay := play_ite_from_guard
    fuel 5 OBot (PrudentBot k) (.sim .opp (.bot CooperateBot))
    (.ite (.sim .opp (.bot DefectBot)) Action.C (.const Action.C) (.const Action.D))
    (.const Action.D)
    Action.C Action.D
    (by rfl) hGuard
  simpa [eval] using hPlay

theorem interp_OBot_plays_C_vs_PrudentBot_false (k : Nat) :
    ¬ (Formula.plays OBot (PrudentBot k) .C).interp := by
  rintro ⟨n, hn⟩
  have hD : play (n + 6) OBot (PrudentBot k) = some .D :=
    OBot_plays_D_vs_PrudentBot k n
  have hC : play (n + 6) OBot (PrudentBot k) = some .C := by
    unfold play at hn ⊢
    exact eval_mono_le hn (n + 6) (by omega)
  rw [hC] at hD
  cases hD

theorem proofSearch_false_OBot_vs_PrudentBot (k : Nat) :
    proofSearch k (.plays OBot (PrudentBot k) .C) = false := by
  cases h : proofSearch k (.plays OBot (PrudentBot k) .C) with
  | true  => exact absurd (proofSearch_sound _ _ h)
                          (interp_OBot_plays_C_vs_PrudentBot_false k)
  | false => rfl

theorem OBot_plays_D_vs_bot_DB (fuel : Nat) :
    play (fuel + 4) OBot (.bot DefectBot) = some .D := by
  have hGuard : eval (fuel + 3) OBot (.bot DefectBot)
                  (.sim .opp (.bot CooperateBot)) = some .D := by
    simp [eval, Prog.subst, DefectBot]
  have hPlay := play_ite_from_guard
    fuel 3 OBot (.bot DefectBot) (.sim .opp (.bot CooperateBot))
    (.ite (.sim .opp (.bot DefectBot)) Action.C (.const Action.C) (.const Action.D))
    (.const Action.D)
    Action.C Action.D
    (by rfl) hGuard
  simpa [eval] using hPlay

theorem PrudentBot_plays_D_vs_OBot (k fuel : Nat) :
    play (fuel + 6) (PrudentBot k) OBot = some .D := by
  have hOBotDB : play (fuel + 4) OBot (.bot DefectBot) = some .D :=
    OBot_plays_D_vs_bot_DB fuel
  have hGuard : eval (fuel + 5) (PrudentBot k) OBot
                  (.sim .opp (.bot DefectBot)) = some .D := by
    simpa [Nat.add_assoc] using
      (eval_sim_opp_bot_of_play (fuel + 4) (PrudentBot k) OBot
        DefectBot Action.D hOBotDB)
  have hgsearch := proofSearch_false_OBot_vs_PrudentBot k
  have hPlay := play_ite_from_guard
    fuel 5 (PrudentBot k) OBot (.sim .opp (.bot DefectBot))
    (.search k (.plays .opp .self Action.C) (.const Action.C) (.const Action.D))
    (.const Action.D)
    Action.D Action.D
    (by rfl) hGuard
  simp [eval, Prog.subst, Formula.subst, hgsearch] at hPlay
  exact hPlay

theorem outcome_PrudentBot_vs_OBot :
    ∃ k₂, ∀ k, k₂ < k →
      ∃ fuel, outcome fuel (PrudentBot k) OBot = some (.D, .D) := by
  refine ⟨0, fun k _ => ⟨6, ?_⟩⟩
  have hA : play 6 (PrudentBot k) OBot = some .D := by
    simpa using PrudentBot_plays_D_vs_OBot k 0
  have hB : play 6 OBot (PrudentBot k) = some .D := by
    simpa using OBot_plays_D_vs_PrudentBot k 0
  exact outcome_of_plays _ _ _ _ _ hA hB


-- TitForTatBot --

theorem PrudentBot_plays_D_against_bot_CB (k fuel : Nat) :
    play (fuel + 4) (PrudentBot k) (.bot CooperateBot) = some .D := by
  show eval (fuel + 4) (PrudentBot k) (.bot CooperateBot) (PrudentBot k) = some .D
  have hCD : (Action.C == Action.D) = false := rfl
  simp [PrudentBot, CooperateBot, eval, Prog.subst, Formula.subst, hCD]

theorem TFT_plays_D_against_PrudentBot (k fuel : Nat) :
    play (fuel + 6) TitForTatBot (PrudentBot k) = some .D := by
  have hProbe : play (fuel + 4) (PrudentBot k) (.bot CooperateBot) = some .D :=
    PrudentBot_plays_D_against_bot_CB k fuel
  have hGuard :
      eval (fuel + 5) TitForTatBot (PrudentBot k) (.sim .opp (.bot CooperateBot)) = some .D := by
    simpa [Nat.add_assoc] using
      (eval_sim_opp_bot_of_play (fuel + 4) TitForTatBot (PrudentBot k) CooperateBot Action.D hProbe)
  have hPlay := play_ite_from_guard
    fuel 5 TitForTatBot (PrudentBot k) (.sim .opp (.bot CooperateBot))
    (.const Action.C) (.const Action.D)
    Action.C Action.D
    (by rfl) hGuard
  simpa [eval] using hPlay

theorem interp_TitForTatBot_plays_C_against_PrudentBot_false (k : Nat) :
    ¬ (Formula.plays TitForTatBot (PrudentBot k) .C).interp := by
  rintro ⟨n, hn⟩
  cases n with
  | zero => simp [play, eval] at hn
  | succ n0 =>
  cases n0 with
  | zero => simp [play, eval, TitForTatBot] at hn
  | succ n1 =>
  cases n1 with
  | zero => simp [play, eval, TitForTatBot] at hn
  | succ n2 =>
  cases n2 with
  | zero => simp [play, eval, TitForTatBot, PrudentBot, Prog.subst, CooperateBot] at hn
  | succ n3 =>
  cases n3 with
  | zero => simp [play, eval, TitForTatBot, PrudentBot, Prog.subst, CooperateBot, DefectBot, Formula.subst] at hn
  | succ n4 =>
  cases n4 with
  | zero => simp [play, eval, TitForTatBot, PrudentBot, Prog.subst, CooperateBot, DefectBot, Formula.subst] at hn
  | succ fuel =>
    have hD : play (fuel + 6) TitForTatBot (PrudentBot k) = some .D :=
      TFT_plays_D_against_PrudentBot k fuel
    have heq : fuel + 1 + 1 + 1 + 1 + 1 + 1 = fuel + 6 := by omega
    rw [heq] at hn
    rw [hD] at hn
    cases hn

theorem proofSearch_false_for_TitForTatBot_vs_PrudentBot (k : Nat) :
    proofSearch k (.plays TitForTatBot (PrudentBot k) .C) = false := by
  cases h : proofSearch k (.plays TitForTatBot (PrudentBot k) .C) with
  | true => exact absurd (proofSearch_sound _ _ h)
                         (interp_TitForTatBot_plays_C_against_PrudentBot_false k)
  | false => rfl

theorem PrudentBot_plays_D_against_TFT (k fuel : Nat) :
    play (fuel + 6) (PrudentBot k) TitForTatBot = some .D := by
  have hps := proofSearch_false_for_TitForTatBot_vs_PrudentBot k
  simp only [TitForTatBot, PrudentBot, CooperateBot, DefectBot] at hps
  show eval (fuel + 6) (PrudentBot k) TitForTatBot (PrudentBot k) = some .D
  have hDC : (Action.D == Action.C) = false := rfl
  simp [PrudentBot, TitForTatBot, CooperateBot, DefectBot, eval, Prog.subst, Formula.subst,
        hps, hDC]

theorem outcome_PrudentBot_vs_TitForTatBot :
    ∃ k₂, ∀ k, k₂ < k →
      ∃ fuel, outcome fuel (PrudentBot k) TitForTatBot = some (.D, .D) := by
  refine ⟨0, fun k _ => ⟨6, ?_⟩⟩
  have hA : play 6 (PrudentBot k) TitForTatBot = some .D :=
    PrudentBot_plays_D_against_TFT k 0
  have hB : play 6 TitForTatBot (PrudentBot k) = some .D :=
    TFT_plays_D_against_PrudentBot k 0
  simp [outcome, hA, hB]

end PD.Theorems
