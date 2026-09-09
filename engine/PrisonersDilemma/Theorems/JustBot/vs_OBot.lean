import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Bots.DupocBot
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Bots.LlmGenerations.JustBot
import PrisonersDilemma.Theorems.CooperateBot.Helpers
import PrisonersDilemma.Theorems.DefectBot.Helpers
import PrisonersDilemma.Theorems.DupocBot.Helpers
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Base.Asymptotics
import PrisonersDilemma.Theorems.JustBot.Helpers
import PrisonersDilemma.Outcome

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

-- Generalized from the single witness `k = atom_cost 5`: the only certificate here is a
-- `Pf.atom` with a CONSTANT cost (`.bot .const`, no `c_guard k` term), so it is afforded
-- at every budget above that floor, and the rest of the proof treats `k` abstractly.
@[outcome]
theorem outcome_JustBot_vs_OBot :
    OutcomeSpec .eventual 6
      JustBot (fun _ => OBot) (some (.D, .D)) := by
  refine ⟨atom_cost 5, fun k hlt n => ?_⟩

  have hPSCB : proofSearch k (.plays (.bot CooperateBot) (.bot (DupocBot k)) .C) = true :=
    (proofSearch_spec _ _).2
      (Pf.atom ⟨PlaysProof.bot PlaysProof.const, by simp [atom_cost] at hlt ⊢; omega⟩)

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
      simpa [Nat.add_assoc] using!
        (eval_ite_from_guard (N + 4) OBot (.bot (DupocBot k))
          (.sim .opp (.bot DefectBot)) (.const Action.C) (.const Action.D)
          Action.C Action.D hInner)
    simpa [Nat.add_assoc, hInnerIte] using! hPlay

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
      simpa [Nat.add_assoc] using!
        (eval_ite_from_guard (n + 4) OBot (JustBot k)
          (.sim .opp (.bot DefectBot)) (.const Action.C) (.const Action.D)
          Action.C Action.D hInner)
    simpa [Nat.add_assoc, hInnerIte] using! hPlay

  exact outcome_of_plays _ _ _ _ _ hA hB
end PD.Theorems
