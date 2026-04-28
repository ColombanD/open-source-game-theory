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
    outcome (fuel + 7) EBot DBot = some (.D, .C) := by
    have hGuard1 : eval (fuel + 6) EBot DBot (.sim .opp DefectBot) = some .C := by
        have hProbe : play (fuel + 5) DBot DefectBot = some .C :=
            (DBot_plays_C_against_DefectBot (fuel + 2)) ▸ rfl
        rw [show eval (fuel + 6) EBot DBot (.sim .opp DefectBot) =
                eval (fuel + 5) DBot DefectBot DBot by rfl]
        rw [show eval (fuel + 5) DBot DefectBot DBot =
                play (fuel + 5) DBot DefectBot by rfl]
        exact hProbe
    have hA : play (fuel + 7) EBot DBot = some .D := by
        have hPlay := play_ite_from_guard
            fuel 6 EBot DBot (.sim .opp DefectBot)
            (.const Action.D)
            (.ite (.sim .opp CooperateBot) Action.C (.const Action.C) (.ite (.sim .opp MirrorBot) Action.C (.const Action.C) (.const Action.D)))
            Action.C Action.C
            (by rfl) hGuard1
        simpa [eval] using hPlay
    have hGuard2 : eval (fuel + 6) DBot EBot (.sim .opp DefectBot) = some .D := by
        have hProbe : play (fuel + 5) EBot DefectBot = some .D :=
            EBot_plays_D_against_DefectBot (fuel + 2) ▸ rfl
        rw [show eval (fuel + 6) DBot EBot (.sim .opp DefectBot) =
                eval (fuel + 5) EBot DefectBot EBot by rfl]
        rw [show eval (fuel + 5) EBot DefectBot EBot =
                play (fuel + 5) EBot DefectBot by rfl]
        exact hProbe
    have hB : play (fuel + 7) DBot EBot = some .C := by
        have hPlay := play_ite_from_guard
            fuel 6 DBot EBot (.sim .opp DefectBot)
            (.const Action.D)
            (.const Action.C)
            Action.C Action.D
            (by rfl) hGuard2
        simpa [eval] using hPlay
    simp [outcome, hA, hB]


theorem EBot_vs_TitForTatBot (fuel : Nat):
    outcome (fuel + 7) EBot TitForTatBot = some (.C, .D) := by
    have hGuard1 : eval (fuel + 6) EBot TitForTatBot (.sim .opp DefectBot) = some .D := by
        have hProbe : play (fuel + 5) TitForTatBot DefectBot = some .D :=
            (TitForTatBot_plays_D_against_DB (fuel + 2)) ▸ rfl
        rw [show eval (fuel + 6) EBot TitForTatBot (.sim .opp DefectBot) =
                eval (fuel + 5) TitForTatBot DefectBot TitForTatBot by rfl]
        rw [show eval (fuel + 5) TitForTatBot DefectBot TitForTatBot =
                        play (fuel + 5) TitForTatBot DefectBot by rfl]
        exact hProbe
    have hGuard2 : eval (fuel + 6) EBot TitForTatBot (.sim .opp CooperateBot) = some .C := by
        have hProbe : play (fuel + 5) TitForTatBot CooperateBot = some .C :=
            (TitForTatBot_plays_C_against_CB (fuel + 2)) ▸ rfl
        show eval (fuel + 6) EBot TitForTatBot (.sim .opp CooperateBot) = some .C
        rw [show eval (fuel + 6) EBot TitForTatBot (.sim .opp CooperateBot) =
                eval (fuel + 5) TitForTatBot CooperateBot TitForTatBot by rfl]
        rw [show eval (fuel + 5) TitForTatBot CooperateBot TitForTatBot =
                        play (fuel + 5) TitForTatBot CooperateBot by rfl]
        exact hProbe
    have hA : play (fuel + 7) EBot TitForTatBot = some .C := by
        have hPlay := play_ite_from_guard
            fuel 6 EBot TitForTatBot (.sim .opp DefectBot)
            (.const Action.D)
            (.ite (.sim .opp CooperateBot) Action.C (.const Action.C) (.ite (.sim .opp MirrorBot) Action.C (.const Action.C) (.const Action.D)))
            Action.C Action.D
            (by rfl) hGuard1
        simpa [eval, hGuard2] using hPlay
    have hGuard3 : eval (fuel + 6) TitForTatBot EBot (.sim .opp CooperateBot) = some .D := by
        have hProbe : play (fuel + 5) EBot CooperateBot = some .D :=
            EBot_plays_D_against_CooperateBot (fuel + 2) ▸ rfl
        rw [show eval (fuel + 6) TitForTatBot EBot (.sim .opp CooperateBot) =
                eval (fuel + 5) EBot CooperateBot EBot by rfl]
        rw [show eval (fuel + 5) EBot CooperateBot EBot =
                play (fuel + 5) EBot CooperateBot by rfl]
        exact hProbe
    have hB : play (fuel + 7) TitForTatBot EBot = some .D := by
        have hPlay := play_ite_from_guard
            fuel 6 TitForTatBot EBot (.sim .opp CooperateBot)
            (.const Action.C)
            (.const Action.D)
            Action.C Action.D
            (by rfl) hGuard3
        simpa [eval] using hPlay
    simp [outcome, hA, hB]


theorem EBot_vs_OBot (fuel : Nat):
    outcome (fuel + 7) EBot OBot = some (.C, .D) := by
    have hGuard1 : eval (fuel + 6) EBot OBot (.sim .opp DefectBot) = some .D := by
        have hProbe : play (fuel + 5) OBot DefectBot = some .D := OBot_plays_D_against_DB (fuel + 2)
        rw [show eval (fuel + 6) EBot OBot (.sim .opp DefectBot) =
                eval (fuel + 5) OBot DefectBot OBot by rfl]
        rw [show eval (fuel + 5) OBot DefectBot OBot =
                play (fuel + 5) OBot DefectBot by rfl]
        exact hProbe
    have hGuard2 : eval (fuel + 6) EBot OBot (.sim .opp CooperateBot) = some .C := by
        have hProbe : play (fuel + 5) OBot CooperateBot = some .C := OBot_plays_C_against_CB (fuel)
        rw [show eval (fuel + 6) EBot OBot (.sim .opp CooperateBot) =
                eval (fuel + 5) OBot CooperateBot OBot by rfl]
        rw [show eval (fuel + 5) OBot CooperateBot OBot =
                play (fuel + 5) OBot CooperateBot by rfl]
        exact hProbe
    have hA : play (fuel + 7) EBot OBot = some .C := by
        have hPlay := play_ite_from_guard
            fuel 6 EBot OBot (.sim .opp DefectBot)
            (.const Action.D)
            (.ite (.sim .opp CooperateBot) Action.C (.const Action.C) (.ite (.sim .opp MirrorBot) Action.C (.const Action.C) (.const Action.D)))
            Action.C Action.D
            (by rfl) hGuard1
        simpa [eval, hGuard2] using hPlay
    have hGuard3 : eval (fuel + 6) OBot EBot (.sim .opp CooperateBot) = some .D := by
        have hProbe : play (fuel + 5) EBot CooperateBot = some .D := EBot_plays_D_against_CooperateBot (fuel + 2)
        rw [show eval (fuel + 6) OBot EBot (.sim .opp CooperateBot) =
                eval (fuel + 5) EBot CooperateBot EBot by rfl]
        rw [show eval (fuel + 5) EBot CooperateBot EBot =
                play (fuel + 5) EBot CooperateBot by rfl]
        exact hProbe
    have hB : play (fuel + 7) OBot EBot = some .D := by
        have hPlay := play_ite_from_guard
            fuel 6 OBot EBot (.sim .opp CooperateBot)
            (.ite (.sim .opp DefectBot) Action.C (.const Action.C) (.const Action.D))
            (.const Action.D)
            Action.C Action.D
            (by rfl) hGuard3
        simpa [eval] using hPlay
    simp [outcome, hA, hB]

theorem EBot_plays_C_against_MirrorBot (fuel : Nat) :
    play (fuel + 7) EBot MirrorBot = some .C := by
    have hGuard1 : eval (fuel + 6) EBot MirrorBot (.sim .opp DefectBot) = some .D := by
        have hProbe : play (fuel + 5) MirrorBot DefectBot = some .D :=
            (MirrorBot_plays_D_against_DefectBot (fuel + 2)) ▸ rfl
        rw [show eval (fuel + 6) EBot MirrorBot (.sim .opp DefectBot) =
                eval (fuel + 5) MirrorBot DefectBot MirrorBot by rfl]
        rw [show eval (fuel + 5) MirrorBot DefectBot MirrorBot =
                play (fuel + 5) MirrorBot DefectBot by rfl]
        exact hProbe
    have hGuard2 : eval (fuel + 6) EBot MirrorBot (.sim .opp CooperateBot) = some .C := by
        have hProbe : play (fuel + 5) MirrorBot CooperateBot = some .C :=
            (MirrorBot_plays_C_against_CooperateBot (fuel + 2)) ▸ rfl
        rw [show eval (fuel + 6) EBot MirrorBot (.sim .opp CooperateBot) =
                eval (fuel + 5) MirrorBot CooperateBot MirrorBot by rfl]
        rw [show eval (fuel + 5) MirrorBot CooperateBot MirrorBot =
                play (fuel + 5) MirrorBot CooperateBot by rfl]
        exact hProbe
    have hPlay := play_ite_from_guard
        fuel 6 EBot MirrorBot (.sim .opp DefectBot)
        (.const Action.D)
        (.ite (.sim .opp CooperateBot) Action.C (.const Action.C) (.ite (.sim .opp MirrorBot) Action.C (.const Action.C) (.const Action.D)))
        Action.C Action.D
        (by rfl) hGuard1
    simpa [eval, hGuard2] using hPlay

theorem EBot_vs_MirrorBot (fuel : Nat):
    outcome (fuel + 7) EBot MirrorBot = some (.C, .C) := by
    have hA : play (fuel + 7) EBot MirrorBot = some .C := EBot_plays_C_against_MirrorBot (fuel)
    have hB : play (fuel + 7) MirrorBot EBot = some .C := by
        have hEBotPlays : play (fuel + 6) EBot MirrorBot = some .C :=
            EBot_plays_C_against_MirrorBot (fuel + 1)
        simpa [play, eval, Prog.subst, MirrorBot] using hEBotPlays
    simp [outcome, hA, hB]

/--
Why this theorem is subtle:

At first glance, self-play seems to reach EBot's third check
"what does opponent do against MirrorBot?", and we already know
`EBot` vs `MirrorBot` yields `C`.

However, under this evaluator, `.sim` first substitutes placeholders.
So in self-play, the guard
`eval ... EBot EBot (.sim .opp MirrorBot)` does not become a plain
`EBot` vs `MirrorBot` query. Instead, `.opp` is replaced by the current
opponent (`EBot`), so the simulated opponent is `MirrorBot.subst EBot EBot`,
which unfolds to a self-simulation shape (`.sim EBot EBot`).

That transformed program can recurse much more deeply than the plain
mirror matchup, and with finite fuel this may hit `none` before producing
`some C`/`some D`. So the theorem is not an immediate consequence of
`EBot_vs_MirrorBot`; it needs reasoning in the substituted self-play context.
-/
theorem EBot_vs_EBot (fuel : Nat):
    outcome (fuel + 7) EBot EBot = some (.C, .C) := sorry

end PDNew.Theorems
