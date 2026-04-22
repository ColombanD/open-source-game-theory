import PrisonersDilemmaNew.Bots.CooperateBot
import PrisonersDilemmaNew.Bots.DefectBot
import PrisonersDilemmaNew.Bots.TitForTatBot
import PrisonersDilemmaNew.Bots.OBot
import PrisonersDilemmaNew.Theorems.DBot
import PrisonersDilemmaNew.Theorems.TitForTatBot
import PrisonersDilemmaNew.Dynamics
import PrisonersDilemmaNew.Theorems.Helpers


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
    have hGuard : eval (fuel + 2) OBot DefectBot (.sim .opp CooperateBot) = some .D := by
        unfold OBot DefectBot CooperateBot
        simp [eval, Prog.subst]
    have hPlay := play_ite_from_guard
        fuel 2 OBot DefectBot (.sim .opp CooperateBot)
        (.ite (.sim .opp DefectBot) Action.C (.const Action.C) (.const Action.D))
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
    outcome (fuel + 9) OBot TitForTatBot = some (.D, .C) := by
    -- OBot is an outer `ite` whose guard asks:
    -- "What does the opponent do against CooperateBot?"
    -- Here the opponent is TitForTatBot, and TitForTatBot cooperates vs CooperateBot.
    -- So this guard must evaluate to `some .C`.
    have hGuard1 : eval (fuel + 8) OBot TitForTatBot (.sim .opp CooperateBot) = some .C := by
        -- Reuse the already-proven behavior of TitForTatBot against CooperateBot.
        have hProbe : play (fuel + 7) TitForTatBot CooperateBot = some .C :=
            (TitForTatBot_plays_C_against_CB (fuel + 4)) ▸ rfl
        -- Convert the simulated guard expression into exactly that `play` statement.
        show eval (fuel + 8) OBot TitForTatBot (.sim .opp CooperateBot) = some .C
        rw [show eval (fuel + 8) OBot TitForTatBot (.sim .opp CooperateBot) =
                eval (fuel + 7) TitForTatBot CooperateBot TitForTatBot by rfl]
        simp only [show eval (fuel + 7) TitForTatBot CooperateBot TitForTatBot =
                        play (fuel + 7) TitForTatBot CooperateBot by rfl]
        exact hProbe
    -- This is the inner guard used once the outer guard is `C`.
    -- It asks what TitForTatBot does against DefectBot.
    -- TitForTatBot defects there, so this guard evaluates to `some .D`.
    have hGuard2 : eval (fuel + 8) OBot TitForTatBot (.sim .opp DefectBot) = some .D := by
        -- Reuse the theorem for TitForTatBot vs DefectBot.
        have hProbe : play (fuel + 7) TitForTatBot DefectBot = some .D :=
            (TitForTatBot_plays_D_against_DB (fuel + 4)) ▸ rfl
        -- Same conversion pattern: simulated eval -> concrete `play` fact.
        show eval (fuel + 8) OBot TitForTatBot (.sim .opp DefectBot) = some .D
        rw [show eval (fuel + 8) OBot TitForTatBot (.sim .opp DefectBot) =
                eval (fuel + 7) TitForTatBot DefectBot TitForTatBot by rfl]
        simp only [show eval (fuel + 7) TitForTatBot DefectBot TitForTatBot =
                        play (fuel + 7) TitForTatBot DefectBot by rfl]
        exact hProbe
    -- Compute OBot's action against TitForTatBot.
    -- `play_ite_from_guard` unfolds one outer `ite` step using `hGuard1`.
    -- Since the outer guard result is `C` (the test action), we move into the then-branch,
    -- which is the inner `ite`.
    -- `hGuard2` then forces that inner `ite` to choose its else-branch (`const D`).
    have hA : play (fuel + 9) OBot TitForTatBot = some .D := by
        have hPlay := play_ite_from_guard
            fuel 8 OBot TitForTatBot (.sim .opp CooperateBot)
            (.ite (.sim .opp DefectBot) Action.C (.const Action.C) (.const Action.D))
            (.const Action.D)
            Action.C Action.C
            (by rfl) hGuard1
        simpa [eval, hGuard2] using hPlay
    -- Now compute TitForTatBot's action against OBot.
    -- TitForTatBot also checks what the opponent does against CooperateBot.
    -- We first show OBot cooperates against CooperateBot, then feed that into the guard.
    have hB : play (fuel + 9) TitForTatBot OBot = some .C := by
        -- OBot cooperates when facing CooperateBot.
        have hProbe : play (fuel + 7) OBot CooperateBot = some .C :=
            (OBot_plays_C_against_CB (fuel + 2)) ▸ rfl
        -- Rewrite TitForTatBot's guard simulation into the corresponding `play` fact.
        have hGuard : eval (fuel + 8) TitForTatBot OBot (.sim .opp CooperateBot) = some .C := by
            show eval (fuel + 8) TitForTatBot OBot (.sim .opp CooperateBot) = some .C
            rw [show eval (fuel + 8) TitForTatBot OBot (.sim .opp CooperateBot) =
                    eval (fuel + 7) OBot CooperateBot OBot by rfl]
            simp only [show eval (fuel + 7) OBot CooperateBot OBot =
                            play (fuel + 7) OBot CooperateBot by rfl]
            exact hProbe
        -- One `ite` step for TitForTatBot: guard is `C`, so it takes `const C`.
        have hPlay := play_ite_from_guard
            fuel 8 TitForTatBot OBot (.sim .opp CooperateBot)
            (.const Action.C) (.const Action.D)
            Action.C Action.C
            (by rfl) hGuard
        exact hPlay ▸ rfl
    -- Finish: outcome is just the pair of both `play` results.
    unfold outcome
    rw [hA, hB]
    rfl

theorem OBot_vs_DBot (fuel : Nat):
    outcome (fuel + 5) OBot DBot = some (.D, .C) := by
    -- Probe facts reused to evaluate simulation guards.
    -- 1) OBot defects against DefectBot.
    have hProbe1 : play (fuel + 3) OBot DefectBot = some .D := OBot_plays_D_against_DB fuel
    -- 2) DBot defects against CooperateBot.
    have hProbe2 : play (fuel + 3) DBot CooperateBot = some .D := DBot_plays_D_against_CB fuel

    -- OBot's outer guard against DBot is `.sim .opp CooperateBot`.
    -- In this development, after unfolding/simplifying `eval`, `Prog.subst`, and `play`,
    -- this guard goal reduces to the already-known probe fact `hProbe1`.
    have hGuard1 : eval (fuel + 4) OBot DBot (.sim .opp CooperateBot) = some .D := by
        simpa [eval, Prog.subst, play] using hProbe1

    -- DBot's guard against OBot is `.sim .opp DefectBot`.
    -- With the same unfolding/simplification pattern, this guard goal reduces
    -- to the probe fact `hProbe2`.
    have hGuard2 : eval (fuel + 4) DBot OBot (.sim .opp DefectBot) = some .D := by
        simpa [eval, Prog.subst, play] using hProbe2

    -- Compute OBot's move against DBot.
    -- `play_ite_from_guard` unfolds one outer `ite` step of OBot.
    -- The test action is `C`, but the guard result is `D`, so OBot takes else-branch `const D`.
    have hA : play (fuel + 5) OBot DBot = some .D := by
        have hPlay := play_ite_from_guard
            fuel 4 OBot DBot (.sim .opp CooperateBot)
            (.ite (.sim .opp DefectBot) Action.C (.const Action.C) (.const Action.D))
            (.const Action.D)
            Action.C Action.D
            (by rfl) hGuard1
        simpa [eval] using hPlay

    -- Compute DBot's move against OBot.
    -- DBot is `ite (.sim .opp DefectBot) C (const D) (const C)`.
    -- Here guard result is `D`, not equal to test `C`, so DBot takes else-branch `const C`.
    have hB : play (fuel + 5) DBot OBot = some .C := by
        have hPlay := play_ite_from_guard
            fuel 4 DBot OBot (.sim .opp DefectBot)
            (.const Action.D) (.const Action.C)
            Action.C Action.D
            (by rfl) hGuard2
        simpa [eval] using hPlay

    -- Finish by unfolding `outcome` and substituting both computed plays.
    simp [outcome, hA, hB]


theorem OBot_vs_OBot (fuel : Nat):
    outcome (fuel + 9) OBot OBot = some (.D, .D) := by
    -- Outer guard for OBot (against OBot): `.sim .opp CooperateBot`.
    -- We reduce it to a known probe: OBot cooperates against CooperateBot.
    have hGuard1 : eval (fuel + 8) OBot OBot (.sim .opp CooperateBot) = some .C := by
        -- Existing theorem gives `play (fuel + 7) OBot CooperateBot = some .C`.
        have hProbe : play (fuel + 7) OBot CooperateBot = some .C :=
            (OBot_plays_C_against_CB (fuel + 2)) ▸ rfl
        -- Convert simulated guard evaluation into that `play` statement.
        show eval (fuel + 8) OBot OBot (.sim .opp CooperateBot) = some .C
        rw [show eval (fuel + 8) OBot OBot (.sim .opp CooperateBot) =
                eval (fuel + 7) OBot CooperateBot OBot by rfl]
        simp only [show eval (fuel + 7) OBot CooperateBot OBot =
                        play (fuel + 7) OBot CooperateBot by rfl]
        exact hProbe

    -- Inner guard for OBot's then-branch: `.sim .opp DefectBot`.
    -- This reduces to the known probe that OBot defects against DefectBot.
    have hGuard2 : eval (fuel + 8) OBot OBot (.sim .opp DefectBot) = some .D := by
        -- Existing theorem gives `play (fuel + 7) OBot DefectBot = some .D`.
        have hProbe : play (fuel + 7) OBot DefectBot = some .D :=
            (OBot_plays_D_against_DB (fuel + 4)) ▸ rfl
        -- Convert simulated guard evaluation into that `play` statement.
        show eval (fuel + 8) OBot OBot (.sim .opp DefectBot) = some .D
        rw [show eval (fuel + 8) OBot OBot (.sim .opp DefectBot) =
                eval (fuel + 7) OBot DefectBot OBot by rfl]
        simp only [show eval (fuel + 7) OBot DefectBot OBot =
                        play (fuel + 7) OBot DefectBot by rfl]
        exact hProbe

    -- Compute OBot's action against OBot.
    -- `play_ite_from_guard` unfolds one outer `ite` step using `hGuard1`.
    -- Since the outer guard is `C` (the test), we enter the inner `ite`.
    -- `hGuard2` then forces the inner `ite` to choose `const D`.
    have hA : play (fuel + 9) OBot OBot = some .D := by
        have hPlay := play_ite_from_guard
            fuel 8 OBot OBot (.sim .opp CooperateBot)
            (.ite (.sim .opp DefectBot) Action.C (.const Action.C) (.const Action.D))
            (.const Action.D)
            Action.C Action.C
            (by rfl) hGuard1
        simpa [eval, hGuard2] using hPlay

    -- Finish by unfolding outcome and substituting both computed plays.
    simp [outcome, hA]

end PDNew.Theorems
