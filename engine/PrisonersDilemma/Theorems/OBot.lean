import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Bots.TitForTatBot
import PrisonersDilemma.Bots.OBot
import PrisonersDilemma.Theorems.DBot
import PrisonersDilemma.Theorems.TitForTatBot
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Theorems.Helpers


open PDNew.Bots
namespace PDNew.Theorems


theorem OBot_plays_C_against_CB(fuel : Nat) :
    play (fuel + 5) OBot CooperateBot = some .C := by
    apply play_from_eval
    unfold OBot CooperateBot
    simp [eval, Prog.subst]
    decide

theorem OBot_vs_CB (fuel : Nat):
    outcome (fuel + 5) OBot CooperateBot = some (.C, .C) := by
    have hA : play (fuel + 5) OBot CooperateBot = some .C := OBot_plays_C_against_CB (fuel)
    have hB : play (fuel + 5) CooperateBot OBot = some .C := rfl
    simp [outcome, hA, hB]

theorem OBot_plays_D_against_DB (fuel : Nat) :
    play (fuel + 3) OBot DefectBot = some .D := by
    have hGuard : eval (fuel + 2) OBot DefectBot (.sim .opp (.bot CooperateBot)) = some .D := by
        unfold OBot DefectBot CooperateBot
        simp [eval, Prog.subst]
    have hPlay := play_ite_from_guard
        fuel 2 OBot DefectBot (.sim .opp (.bot CooperateBot))
        (.ite (.sim .opp (.bot DefectBot)) Action.C (.const Action.C) (.const Action.D))
        (.const Action.D)
        Action.C Action.D
        (by rfl) hGuard
    simpa [eval] using hPlay

theorem OBot_vs_DB (fuel : Nat):
    outcome (fuel + 3) OBot DefectBot = some (.D, .D) := by
    have hA : play (fuel + 3) OBot DefectBot = some .D := OBot_plays_D_against_DB (fuel)
    have hB : play (fuel + 3) DefectBot OBot = some .D := rfl
    simp [outcome, hA, hB]


theorem OBot_vs_TitForTatBot (fuel : Nat):
    outcome (fuel + 7) OBot TitForTatBot = some (.D, .C) := by
    have hGuard1 : eval (fuel + 6) OBot TitForTatBot (.sim .opp (.bot CooperateBot)) = some .C := by
      simp [eval, Prog.subst, TitForTatBot, CooperateBot]; decide
    have hGuard2 : eval (fuel + 6) OBot TitForTatBot (.sim .opp (.bot DefectBot)) = some .D := by
      simp [eval, Prog.subst, TitForTatBot, CooperateBot, DefectBot]; decide
    have hA : play (fuel + 7) OBot TitForTatBot = some .D := by
        have hPlay := play_ite_from_guard
            fuel 6 OBot TitForTatBot (.sim .opp (.bot CooperateBot))
            (.ite (.sim .opp (.bot DefectBot)) Action.C (.const Action.C) (.const Action.D))
            (.const Action.D)
            Action.C Action.C
            (by rfl) hGuard1
        simpa [eval, hGuard2] using hPlay
    have hB : play (fuel + 7) TitForTatBot OBot = some .C := by
        -- TitForTatBot's guard reduces to OBot vs (.bot CooperateBot). We trace
        -- OBot's outer ite (guard = C → take then-branch which is inner ite,
        -- inner guard = C → take const C).
        have hOuter : eval (fuel + 4) OBot (.bot CooperateBot) (.sim .opp (.bot CooperateBot)) = some .C := by
          simp [eval, Prog.subst, CooperateBot]
        have hInner : eval (fuel + 4) OBot (.bot CooperateBot) (.sim .opp (.bot DefectBot)) = some .C := by
          simp [eval, Prog.subst, CooperateBot]
        have hOBot : play (fuel + 5) OBot (.bot CooperateBot) = some .C := by
          have hPlay := play_ite_from_guard
            fuel 4 OBot (.bot CooperateBot) (.sim .opp (.bot CooperateBot))
            (.ite (.sim .opp (.bot DefectBot)) Action.C (.const Action.C) (.const Action.D))
            (.const Action.D)
            Action.C Action.C
            (by unfold OBot; rfl) hOuter
          simpa [eval, hInner] using hPlay
        have hGuard : eval (fuel + 6) TitForTatBot OBot (.sim .opp (.bot CooperateBot)) = some .C := by
          rw [show eval (fuel + 6) TitForTatBot OBot (.sim .opp (.bot CooperateBot)) =
                  eval (fuel + 5) OBot (.bot CooperateBot) OBot by rfl]
          simpa [play] using hOBot
        have hPlay := play_ite_from_guard
            fuel 6 TitForTatBot OBot (.sim .opp (.bot CooperateBot))
            (.const Action.C) (.const Action.D)
            Action.C Action.C
            (by rfl) hGuard
        exact hPlay ▸ rfl
    unfold outcome
    rw [hA, hB]
    rfl

theorem OBot_vs_DBot (fuel : Nat):
    outcome (fuel + 6) OBot DBot = some (.D, .C) := by
    -- hGuard1: simulates DBot vs (.bot CooperateBot). DBot's inner guard
    -- returns C, so DBot takes its const-D branch.
    have hGuard1 : eval (fuel + 5) OBot DBot (.sim .opp (.bot CooperateBot)) = some .D := by
      simp [eval, Prog.subst, DBot, CooperateBot, DefectBot]; decide
    -- hGuard2: simulates OBot vs (.bot DefectBot). OBot's outer guard returns
    -- D, so OBot takes its const-D else-branch.
    have hG2Outer : eval (fuel + 3) OBot (.bot DefectBot) (.sim .opp (.bot CooperateBot)) = some .D := by
      simp [eval, Prog.subst, DefectBot]
    have hOBotvsBotDefect : play (fuel + 4) OBot (.bot DefectBot) = some .D := by
      have hPlay := play_ite_from_guard
        fuel 3 OBot (.bot DefectBot) (.sim .opp (.bot CooperateBot))
        (.ite (.sim .opp (.bot DefectBot)) Action.C (.const Action.C) (.const Action.D))
        (.const Action.D)
        Action.C Action.D
        (by unfold OBot; rfl) hG2Outer
      simpa [eval] using hPlay
    have hGuard2 : eval (fuel + 5) DBot OBot (.sim .opp (.bot DefectBot)) = some .D := by
      rw [show eval (fuel + 5) DBot OBot (.sim .opp (.bot DefectBot)) =
              eval (fuel + 4) OBot (.bot DefectBot) OBot by rfl]
      simpa [play] using hOBotvsBotDefect

    have hA : play (fuel + 6) OBot DBot = some .D := by
        have hPlay := play_ite_from_guard
            fuel 5 OBot DBot (.sim .opp (.bot CooperateBot))
            (.ite (.sim .opp (.bot DefectBot)) Action.C (.const Action.C) (.const Action.D))
            (.const Action.D)
            Action.C Action.D
            (by rfl) hGuard1
        simpa [eval] using hPlay

    have hB : play (fuel + 6) DBot OBot = some .C := by
        have hPlay := play_ite_from_guard
            fuel 5 DBot OBot (.sim .opp (.bot DefectBot))
            (.const Action.D) (.const Action.C)
            Action.C Action.D
            (by rfl) hGuard2
        simpa [eval] using hPlay

    simp [outcome, hA, hB]


theorem OBot_vs_OBot (fuel : Nat):
    outcome (fuel + 7) OBot OBot = some (.D, .D) := by
    -- After substitution, OBot's outer guard simulates OBot vs (.bot CooperateBot).
    -- Trace OBot's outer ite (guard = C, take then-branch = inner ite, inner
    -- guard = C, take const C) → some C.
    have hOuter : eval (fuel + 4) OBot (.bot CooperateBot) (.sim .opp (.bot CooperateBot)) = some .C := by
      simp [eval, Prog.subst, CooperateBot]
    have hInner : eval (fuel + 4) OBot (.bot CooperateBot) (.sim .opp (.bot DefectBot)) = some .C := by
      simp [eval, Prog.subst, CooperateBot]
    have hOBotvsBotCB : play (fuel + 5) OBot (.bot CooperateBot) = some .C := by
      have hPlay := play_ite_from_guard
        fuel 4 OBot (.bot CooperateBot) (.sim .opp (.bot CooperateBot))
        (.ite (.sim .opp (.bot DefectBot)) Action.C (.const Action.C) (.const Action.D))
        (.const Action.D)
        Action.C Action.C
        (by unfold OBot; rfl) hOuter
      simpa [eval, hInner] using hPlay
    have hGuard1 : eval (fuel + 6) OBot OBot (.sim .opp (.bot CooperateBot)) = some .C := by
      rw [show eval (fuel + 6) OBot OBot (.sim .opp (.bot CooperateBot)) =
              eval (fuel + 5) OBot (.bot CooperateBot) OBot by rfl]
      simpa [play] using hOBotvsBotCB

    -- Same idea for the inner guard: simulates OBot vs (.bot DefectBot),
    -- where OBot's outer guard returns D, so falls to const D.
    have hOuterD : eval (fuel + 3) OBot (.bot DefectBot) (.sim .opp (.bot CooperateBot)) = some .D := by
      simp [eval, Prog.subst, DefectBot]
    have hOBotvsBotDB : play (fuel + 4) OBot (.bot DefectBot) = some .D := by
      have hPlay := play_ite_from_guard
        fuel 3 OBot (.bot DefectBot) (.sim .opp (.bot CooperateBot))
        (.ite (.sim .opp (.bot DefectBot)) Action.C (.const Action.C) (.const Action.D))
        (.const Action.D)
        Action.C Action.D
        (by unfold OBot; rfl) hOuterD
      simpa [eval] using hPlay
    have hGuard2 : eval (fuel + 6) OBot OBot (.sim .opp (.bot DefectBot)) = some .D := by
      rw [show eval (fuel + 6) OBot OBot (.sim .opp (.bot DefectBot)) =
              eval (fuel + 5) OBot (.bot DefectBot) OBot by rfl]
      simpa [play] using hOBotvsBotDB

    have hA : play (fuel + 7) OBot OBot = some .D := by
        have hPlay := play_ite_from_guard
            fuel 6 OBot OBot (.sim .opp (.bot CooperateBot))
            (.ite (.sim .opp (.bot DefectBot)) Action.C (.const Action.C) (.const Action.D))
            (.const Action.D)
            Action.C Action.C
            (by rfl) hGuard1
        simpa [eval, hGuard2] using hPlay

    simp [outcome, hA]

end PDNew.Theorems
