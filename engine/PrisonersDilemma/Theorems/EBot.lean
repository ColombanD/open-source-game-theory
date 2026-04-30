import PrisonersDilemma.Bots.EBot
import PrisonersDilemma.Bots.OBot
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Bots.DBot
import PrisonersDilemma.Theorems.Helpers
import PrisonersDilemma.Theorems.DBot
import PrisonersDilemma.Theorems.OBot
import PrisonersDilemma.Theorems.TitForTatBot
import PrisonersDilemma.Theorems.MirrorBot


open PDNew.Bots
namespace PDNew.Theorems

theorem EBot_plays_D_against_CooperateBot (fuel : Nat) :
    play (fuel + 3) EBot CooperateBot = some .D := by
    apply play_from_eval
    unfold EBot CooperateBot
    simp [eval, Prog.subst]
    intro h
    have : (Action.C == Action.C) = true := by decide
    simp [this] at h

theorem EBot_vs_CooperateBot (fuel : Nat):
    outcome (fuel + 3) EBot CooperateBot = some (.D, .C) := by
    have hA : play (fuel + 3) EBot CooperateBot = some .D := EBot_plays_D_against_CooperateBot (fuel)
    have hB : play (fuel + 3) CooperateBot EBot = some .C := rfl
    simp [outcome, hA, hB]

theorem EBot_plays_D_against_DefectBot (fuel : Nat) :
    play (fuel + 5) EBot DefectBot = some .D := by
    apply play_from_eval
    unfold EBot DefectBot
    simp [eval, Prog.subst]
    intro h
    simp [h]

theorem EBot_vs_DefectBot (fuel : Nat):
    outcome (fuel + 5) EBot DefectBot = some (.D, .D) := by
    have hA : play (fuel + 5) EBot DefectBot = some .D := EBot_plays_D_against_DefectBot (fuel)
    have hB : play (fuel + 5) DefectBot EBot = some .D := rfl
    simp [outcome, hA, hB]

theorem EBot_vs_Dbot (fuel : Nat):
    outcome (fuel + 8) EBot DBot = some (.D, .C) := by
    have hGuard1 : eval (fuel + 7) EBot DBot (.sim .opp (.bot DefectBot)) = some .C := by
      simp [eval, Prog.subst, DBot, DefectBot]; decide
    have hA : play (fuel + 8) EBot DBot = some .D := by
        have hPlay := play_ite_from_guard
            fuel 7 EBot DBot (.sim .opp (.bot DefectBot))
            (.const Action.D)
            (.ite (.sim .opp (.bot CooperateBot)) Action.C (.const Action.C) (.ite (.sim .opp (.bot MirrorBot)) Action.C (.const Action.C) (.const Action.D)))
            Action.C Action.C
            (by rfl) hGuard1
        simpa [eval] using hPlay
    have hGuard2 : eval (fuel + 7) DBot EBot (.sim .opp (.bot DefectBot)) = some .D := by
      simp [eval, Prog.subst, EBot, DefectBot, CooperateBot, MirrorBot]; decide
    have hB : play (fuel + 8) DBot EBot = some .C := by
        have hPlay := play_ite_from_guard
            fuel 7 DBot EBot (.sim .opp (.bot DefectBot))
            (.const Action.D)
            (.const Action.C)
            Action.C Action.D
            (by rfl) hGuard2
        simpa [eval] using hPlay
    simp [outcome, hA, hB]


theorem EBot_vs_TitForTatBot (fuel : Nat):
    outcome (fuel + 7) EBot TitForTatBot = some (.C, .D) := by
    have hGuard1 : eval (fuel + 6) EBot TitForTatBot (.sim .opp (.bot DefectBot)) = some .D := by
      simp [eval, Prog.subst, TitForTatBot, DefectBot, CooperateBot]; decide
    have hGuard2 : eval (fuel + 6) EBot TitForTatBot (.sim .opp (.bot CooperateBot)) = some .C := by
      simp [eval, Prog.subst, TitForTatBot, CooperateBot]; decide
    have hA : play (fuel + 7) EBot TitForTatBot = some .C := by
        have hPlay := play_ite_from_guard
            fuel 6 EBot TitForTatBot (.sim .opp (.bot DefectBot))
            (.const Action.D)
            (.ite (.sim .opp (.bot CooperateBot)) Action.C (.const Action.C) (.ite (.sim .opp (.bot MirrorBot)) Action.C (.const Action.C) (.const Action.D)))
            Action.C Action.D
            (by rfl) hGuard1
        simpa [eval, hGuard2] using hPlay
    -- hGuard3 reduces to "EBot vs (.bot CooperateBot)". EBot's outer guard
    -- sees (.bot CooperateBot) cooperate against DefectBot, so it defects.
    have hOuterCB : eval (fuel + 4) EBot (.bot CooperateBot) (.sim .opp (.bot DefectBot)) = some .C := by
      simp [eval, Prog.subst, CooperateBot]
    have hEBotBotCB : play (fuel + 5) EBot (.bot CooperateBot) = some .D := by
      have hPlay := play_ite_from_guard
        fuel 4 EBot (.bot CooperateBot) (.sim .opp (.bot DefectBot))
        (.const Action.D)
        (.ite (.sim .opp (.bot CooperateBot)) Action.C (.const Action.C) (.ite (.sim .opp (.bot MirrorBot)) Action.C (.const Action.C) (.const Action.D)))
        Action.C Action.C
        (by unfold EBot; rfl) hOuterCB
      simpa [eval] using hPlay
    have hGuard3 : eval (fuel + 6) TitForTatBot EBot (.sim .opp (.bot CooperateBot)) = some .D := by
      rw [show eval (fuel + 6) TitForTatBot EBot (.sim .opp (.bot CooperateBot)) =
              eval (fuel + 5) EBot (.bot CooperateBot) EBot by rfl]
      simpa [play] using hEBotBotCB
    have hB : play (fuel + 7) TitForTatBot EBot = some .D := by
        have hPlay := play_ite_from_guard
            fuel 6 TitForTatBot EBot (.sim .opp (.bot CooperateBot))
            (.const Action.C)
            (.const Action.D)
            Action.C Action.D
            (by rfl) hGuard3
        simpa [eval] using hPlay
    simp [outcome, hA, hB]


theorem EBot_vs_OBot (fuel : Nat):
    outcome (fuel + 8) EBot OBot = some (.C, .D) := by
    -- For hGuard1 we directly trace OBot vs (.bot DefectBot): OBot's outer
    -- guard returns D (since (.bot DefectBot) defects against CooperateBot),
    -- so OBot defects.
    have hOBotvsBotD_outer : eval (fuel + 5) OBot (.bot DefectBot) (.sim .opp (.bot CooperateBot)) = some .D := by
      simp [eval, Prog.subst, DefectBot]
    have hOBotvsBotD : play (fuel + 6) OBot (.bot DefectBot) = some .D := by
      have hPlay := play_ite_from_guard
        fuel 5 OBot (.bot DefectBot) (.sim .opp (.bot CooperateBot))
        (.ite (.sim .opp (.bot DefectBot)) Action.C (.const Action.C) (.const Action.D))
        (.const Action.D)
        Action.C Action.D
        (by unfold OBot; rfl) hOBotvsBotD_outer
      simpa [eval] using hPlay
    have hGuard1 : eval (fuel + 7) EBot OBot (.sim .opp (.bot DefectBot)) = some .D := by
      rw [show eval (fuel + 7) EBot OBot (.sim .opp (.bot DefectBot)) =
              eval (fuel + 6) OBot (.bot DefectBot) OBot by rfl]
      simpa [play] using hOBotvsBotD
    -- hGuard2 traces OBot vs (.bot CooperateBot): outer guard C, take inner ite
    -- whose guard is also C, take const C.
    have hOBotvsBotC_outer : eval (fuel + 5) OBot (.bot CooperateBot) (.sim .opp (.bot CooperateBot)) = some .C := by
      simp [eval, Prog.subst, CooperateBot]
    have hOBotvsBotC_inner : eval (fuel + 5) OBot (.bot CooperateBot) (.sim .opp (.bot DefectBot)) = some .C := by
      simp [eval, Prog.subst, CooperateBot]
    have hOBotvsBotC : play (fuel + 6) OBot (.bot CooperateBot) = some .C := by
      have hPlay := play_ite_from_guard
        fuel 5 OBot (.bot CooperateBot) (.sim .opp (.bot CooperateBot))
        (.ite (.sim .opp (.bot DefectBot)) Action.C (.const Action.C) (.const Action.D))
        (.const Action.D)
        Action.C Action.C
        (by unfold OBot; rfl) hOBotvsBotC_outer
      simpa [eval, hOBotvsBotC_inner] using hPlay
    have hGuard2 : eval (fuel + 7) EBot OBot (.sim .opp (.bot CooperateBot)) = some .C := by
      rw [show eval (fuel + 7) EBot OBot (.sim .opp (.bot CooperateBot)) =
              eval (fuel + 6) OBot (.bot CooperateBot) OBot by rfl]
      simpa [play] using hOBotvsBotC
    have hA : play (fuel + 8) EBot OBot = some .C := by
        have hPlay := play_ite_from_guard
            fuel 7 EBot OBot (.sim .opp (.bot DefectBot))
            (.const Action.D)
            (.ite (.sim .opp (.bot CooperateBot)) Action.C (.const Action.C) (.ite (.sim .opp (.bot MirrorBot)) Action.C (.const Action.C) (.const Action.D)))
            Action.C Action.D
            (by rfl) hGuard1
        simpa [eval, hGuard2] using hPlay
    -- For hGuard3: EBot vs (.bot CooperateBot) — outer guard returns C, defect.
    have hEBotBotCB_outer : eval (fuel + 5) EBot (.bot CooperateBot) (.sim .opp (.bot DefectBot)) = some .C := by
      simp [eval, Prog.subst, CooperateBot]
    have hEBotBotCB : play (fuel + 6) EBot (.bot CooperateBot) = some .D := by
      have hPlay := play_ite_from_guard
        fuel 5 EBot (.bot CooperateBot) (.sim .opp (.bot DefectBot))
        (.const Action.D)
        (.ite (.sim .opp (.bot CooperateBot)) Action.C (.const Action.C) (.ite (.sim .opp (.bot MirrorBot)) Action.C (.const Action.C) (.const Action.D)))
        Action.C Action.C
        (by unfold EBot; rfl) hEBotBotCB_outer
      simpa [eval] using hPlay
    have hGuard3 : eval (fuel + 7) OBot EBot (.sim .opp (.bot CooperateBot)) = some .D := by
      rw [show eval (fuel + 7) OBot EBot (.sim .opp (.bot CooperateBot)) =
              eval (fuel + 6) EBot (.bot CooperateBot) EBot by rfl]
      simpa [play] using hEBotBotCB
    have hB : play (fuel + 8) OBot EBot = some .D := by
        have hPlay := play_ite_from_guard
            fuel 7 OBot EBot (.sim .opp (.bot CooperateBot))
            (.ite (.sim .opp (.bot DefectBot)) Action.C (.const Action.C) (.const Action.D))
            (.const Action.D)
            Action.C Action.D
            (by rfl) hGuard3
        simpa [eval] using hPlay
    simp [outcome, hA, hB]

theorem EBot_plays_C_against_MirrorBot (fuel : Nat) :
    play (fuel + 7) EBot MirrorBot = some .C := by
    have hGuard1 : eval (fuel + 6) EBot MirrorBot (.sim .opp (.bot DefectBot)) = some .D := by
      simp [eval, Prog.subst, MirrorBot, DefectBot]
    have hGuard2 : eval (fuel + 6) EBot MirrorBot (.sim .opp (.bot CooperateBot)) = some .C := by
      simp [eval, Prog.subst, MirrorBot, CooperateBot]
    have hPlay := play_ite_from_guard
        fuel 6 EBot MirrorBot (.sim .opp (.bot DefectBot))
        (.const Action.D)
        (.ite (.sim .opp (.bot CooperateBot)) Action.C (.const Action.C) (.ite (.sim .opp (.bot MirrorBot)) Action.C (.const Action.C) (.const Action.D)))
        Action.C Action.D
        (by rfl) hGuard1
    simpa [eval, hGuard2] using hPlay

theorem EBot_vs_MirrorBot (fuel : Nat):
    outcome (fuel + 8) EBot MirrorBot = some (.C, .C) := by
    have hA : play (fuel + 8) EBot MirrorBot = some .C := EBot_plays_C_against_MirrorBot (fuel + 1)
    have hB : play (fuel + 8) MirrorBot EBot = some .C := by
        have hEBotPlays : play (fuel + 7) EBot MirrorBot = some .C :=
            EBot_plays_C_against_MirrorBot fuel
        show eval (fuel + 7) EBot MirrorBot EBot = some .C
        exact hEBotPlays
    simp [outcome, hA, hB]

/--
With `.bot`-wrapped bot references, EBot's third guard `(.sim .opp (.bot MirrorBot))`
is now an independent probe of "opp vs MirrorBot": substitution does not descend
into `.bot`, so `MirrorBot`'s placeholders bind to MirrorBot's own frame at unwrap
time rather than being captured by the outer EBot/EBot frame. In self-play this
makes the third guard cleanly evaluate to `C` (EBot mirrors itself against
MirrorBot, MirrorBot cooperates), so EBot cooperates with itself.
-/
theorem EBot_vs_EBot (fuel : Nat):
    outcome (fuel + 11) EBot EBot = some (.C, .C) := by
  -- Helpers: EBot's behaviour against `.bot`-wrapped probes.
  have hEBotBotD : ∀ k, eval (k + 6) EBot (.bot DefectBot) EBot = some .D := by
    intro k
    have hOuterG : eval (k + 5) EBot (.bot DefectBot) (.sim .opp (.bot DefectBot)) = some .D := by
      simp only [eval, Prog.subst, DefectBot]
    have hInnerG : eval (k + 4) EBot (.bot DefectBot) (.sim .opp (.bot CooperateBot)) = some .D := by
      simp only [eval, Prog.subst, DefectBot]
    have hInnerInnerG : eval (k + 3) EBot (.bot DefectBot) (.sim .opp (.bot MirrorBot)) = some .D := by
      simp only [eval, Prog.subst, DefectBot]
    have hInnerInnerIte : eval (k + 4) EBot (.bot DefectBot) (Prog.ite (.sim .opp (.bot MirrorBot)) Action.C (.const Action.C) (.const Action.D)) = some .D := by
      change (do let r ← eval (k + 3) EBot (.bot DefectBot) (.sim .opp (.bot MirrorBot)); if r == Action.C then eval (k + 3) EBot (.bot DefectBot) (.const Action.C) else eval (k + 3) EBot (.bot DefectBot) (.const Action.D)) = some Action.D
      rw [hInnerInnerG]; rfl
    have hInnerIte : eval (k + 5) EBot (.bot DefectBot) (Prog.ite (.sim .opp (.bot CooperateBot)) Action.C (.const Action.C) (Prog.ite (.sim .opp (.bot MirrorBot)) Action.C (.const Action.C) (.const Action.D))) = some .D := by
      change (do let r ← eval (k + 4) EBot (.bot DefectBot) (.sim .opp (.bot CooperateBot)); if r == Action.C then eval (k + 4) EBot (.bot DefectBot) (.const Action.C) else eval (k + 4) EBot (.bot DefectBot) (Prog.ite (.sim .opp (.bot MirrorBot)) Action.C (.const Action.C) (.const Action.D))) = some Action.D
      rw [hInnerG, hInnerInnerIte]; rfl
    change (do let r ← eval (k + 5) EBot (.bot DefectBot) (.sim .opp (.bot DefectBot)); if r == Action.C then eval (k + 5) EBot (.bot DefectBot) (.const Action.D) else eval (k + 5) EBot (.bot DefectBot) (Prog.ite (.sim .opp (.bot CooperateBot)) Action.C (.const Action.C) (Prog.ite (.sim .opp (.bot MirrorBot)) Action.C (.const Action.C) (.const Action.D)))) = some Action.D
    rw [hOuterG, hInnerIte]; rfl
  have hEBotBotC : ∀ k, eval (k + 4) EBot (.bot CooperateBot) EBot = some .D := by
    intro k
    have hOuterG : eval (k + 3) EBot (.bot CooperateBot) (.sim .opp (.bot DefectBot)) = some .C := by
      simp only [eval, Prog.subst, CooperateBot]
    change (do let r ← eval (k + 3) EBot (.bot CooperateBot) (.sim .opp (.bot DefectBot)); if r == Action.C then eval (k + 3) EBot (.bot CooperateBot) (.const Action.D) else eval (k + 3) EBot (.bot CooperateBot) (Prog.ite (.sim .opp (.bot CooperateBot)) Action.C (.const Action.C) (Prog.ite (.sim .opp (.bot MirrorBot)) Action.C (.const Action.C) (.const Action.D)))) = some Action.D
    rw [hOuterG]; rfl
  have hEBotBotM : ∀ k, eval (k + 7) EBot (.bot MirrorBot) EBot = some .C := by
    intro k
    have hOuterG : eval (k + 6) EBot (.bot MirrorBot) (.sim .opp (.bot DefectBot)) = some .D := by
      simp only [eval, Prog.subst, MirrorBot, DefectBot]
    have hInnerG : eval (k + 5) EBot (.bot MirrorBot) (.sim .opp (.bot CooperateBot)) = some .C := by
      simp only [eval, Prog.subst, MirrorBot, CooperateBot]
    have hInnerIte : eval (k + 6) EBot (.bot MirrorBot)
        (Prog.ite (.sim .opp (.bot CooperateBot)) Action.C (.const Action.C)
              (Prog.ite (.sim .opp (.bot MirrorBot)) Action.C (.const Action.C) (.const Action.D)))
        = some .C := by
      change (do let r ← eval (k + 5) EBot (.bot MirrorBot) (.sim .opp (.bot CooperateBot)); if r == Action.C then eval (k + 5) EBot (.bot MirrorBot) (.const Action.C) else eval (k + 5) EBot (.bot MirrorBot) (Prog.ite (.sim .opp (.bot MirrorBot)) Action.C (.const Action.C) (.const Action.D))) = some Action.C
      rw [hInnerG]
      rfl
    change (do let r ← eval (k + 6) EBot (.bot MirrorBot) (.sim .opp (.bot DefectBot)); if r == Action.C then eval (k + 6) EBot (.bot MirrorBot) (.const Action.D) else eval (k + 6) EBot (.bot MirrorBot) (Prog.ite (.sim .opp (.bot CooperateBot)) Action.C (.const Action.C) (Prog.ite (.sim .opp (.bot MirrorBot)) Action.C (.const Action.C) (.const Action.D)))) = some Action.C
    rw [hOuterG, hInnerIte]
    rfl

  -- Self-play guards: each reduces to EBot vs (.bot Z) via the .sim rule.
  have hG1 : eval (fuel + 10) EBot EBot (.sim .opp (.bot DefectBot)) = some .D := by
    rw [show eval (fuel + 10) EBot EBot (.sim .opp (.bot DefectBot)) =
            eval (fuel + 9) EBot (.bot DefectBot) EBot by rfl]
    exact hEBotBotD (fuel + 3)
  have hG2 : eval (fuel + 9) EBot EBot (.sim .opp (.bot CooperateBot)) = some .D := by
    rw [show eval (fuel + 9) EBot EBot (.sim .opp (.bot CooperateBot)) =
            eval (fuel + 8) EBot (.bot CooperateBot) EBot by rfl]
    exact hEBotBotC (fuel + 4)
  have hG3 : eval (fuel + 8) EBot EBot (.sim .opp (.bot MirrorBot)) = some .C := by
    rw [show eval (fuel + 8) EBot EBot (.sim .opp (.bot MirrorBot)) =
            eval (fuel + 7) EBot (.bot MirrorBot) EBot by rfl]
    exact hEBotBotM fuel

  have hInnerInnerIte : eval (fuel + 9) EBot EBot (Prog.ite (.sim .opp (.bot MirrorBot)) Action.C (.const Action.C) (.const Action.D)) = some .C := by
    change (do let r ← eval (fuel + 8) EBot EBot (.sim .opp (.bot MirrorBot)); if r == Action.C then eval (fuel + 8) EBot EBot (.const Action.C) else eval (fuel + 8) EBot EBot (.const Action.D)) = some Action.C
    rw [hG3]; rfl
  have hInnerIte : eval (fuel + 10) EBot EBot (Prog.ite (.sim .opp (.bot CooperateBot)) Action.C (.const Action.C) (Prog.ite (.sim .opp (.bot MirrorBot)) Action.C (.const Action.C) (.const Action.D))) = some .C := by
    change (do let r ← eval (fuel + 9) EBot EBot (.sim .opp (.bot CooperateBot)); if r == Action.C then eval (fuel + 9) EBot EBot (.const Action.C) else eval (fuel + 9) EBot EBot (Prog.ite (.sim .opp (.bot MirrorBot)) Action.C (.const Action.C) (.const Action.D))) = some Action.C
    rw [hG2, hInnerInnerIte]; rfl
  have hA : play (fuel + 11) EBot EBot = some .C := by
    show eval (fuel + 11) EBot EBot EBot = some .C
    change (do let r ← eval (fuel + 10) EBot EBot (.sim .opp (.bot DefectBot)); if r == Action.C then eval (fuel + 10) EBot EBot (.const Action.D) else eval (fuel + 10) EBot EBot (Prog.ite (.sim .opp (.bot CooperateBot)) Action.C (.const Action.C) (Prog.ite (.sim .opp (.bot MirrorBot)) Action.C (.const Action.C) (.const Action.D)))) = some Action.C
    rw [hG1, hInnerIte]; rfl
  simp [outcome, hA]

end PDNew.Theorems
