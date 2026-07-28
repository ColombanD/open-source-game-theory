import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Base.Asymptotics
import PrisonersDilemma.Base.Helpers

import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Bots.LlmGenerations.CIMCIC
import PrisonersDilemma.Theorems.CooperateBot.Helpers
import PrisonersDilemma.Theorems.DefectBot.Helpers

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

/-- The substituted CIMCIC guard against DefectBot. -/
abbrev cimcic_guard (k : Nat) : Formula :=
  .impl (.plays (CIMCIC k) DefectBot Action.C) (.plays DefectBot (CIMCIC k) Action.C)

/-- The consequent atom `DefectBot plays C vs CIMCIC` is genuinely UNPROVABLE: DefectBot plays D,
    so its `interp` is false, refuted by `Pf_sound`. -/
theorem cimcic_consequent_not_provable (k m : Nat) :
    ¬ Pf m (.plays DefectBot (CIMCIC k) Action.C) := by
  intro h
  obtain ⟨n, hn⟩ := Pf_sound m _ h
  have : play n DefectBot (CIMCIC k) = some Action.D ∨ play n DefectBot (CIMCIC k) = none := by
    cases n with
    | zero => right; rfl
    | succ n => left; simp [play, eval, DefectBot]
  rcases this with hD | hNone
  · rw [hD] at hn; exact absurd hn (by decide)
  · rw [hNone] at hn; exact absurd hn (by decide)

/-- **No `Pf` concludes anything guarded-tailed at the forbidden consequent** — an
    instance of the shared census `no_provable_tailTo_unreadable` (Base/Exclusion):
    the consequent atom has no certificate at any budget, and the target player is
    bridge-unreadable. (Formerly a hand-rolled 22-arm `Pf.induct`; the shared census
    runs on the Guarded `TailTo` invariant — see Base/Exclusion's header.) -/
theorem cimcic_no_provable_forbidden (k : Nat) :
    ∀ {m : Nat} {φ : Formula}, Pf m φ →
      ¬ TailTo (.plays DefectBot (CIMCIC k) Action.C) φ :=
  no_provable_tailTo_unreadable _ _ _
    (fun n hA => cimcic_consequent_not_provable k n (.atom hA))
    (by rintro (⟨_, _, _, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, _, _, h⟩ |
          ⟨_, _, _, _, _, _, _, h⟩ | ⟨_, _, _, _, _, _, _, h⟩) <;> simp [DefectBot] at h)
    (by intro L h
        cases L with
        | nil => simp [searchPlug, DefectBot] at h
        | cons hd tl =>
            obtain ⟨g, ψ, e⟩ := hd
            simp [searchPlug, DefectBot] at h)
    (by intro hd L h
        cases hd with
        | searchL g' ψ' e' => simp [ctxPlug, DefectBot] at h
        | iteL z' aT' other' => simp [ctxPlug, DefectBot] at h)

/-- CIMCIC's guard against DefectBot is **not provable** within any budget `k`. -/
theorem cimcic_guard_not_provable (k : Nat) : ¬ Pf k (cimcic_guard k) := by
  intro h
  refine cimcic_no_provable_forbidden k h ?_
  exact ⟨rfl, by simp [CIMCIC, DefectBot]⟩

/-- `proofSearch k guard = false` — from `cimcic_guard_not_provable`. -/
theorem proofSearch_false_for_CIMCIC_vs_DefectBot (k : Nat) :
    proofSearch k
      ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.C)).subst
        (CIMCIC k) DefectBot) = false := by
  show proofSearch k (cimcic_guard k) = false
  cases hps : proofSearch k (cimcic_guard k) with
  | false => rfl
  | true => exact absurd ((proofSearch_spec k (cimcic_guard k)).1 hps) (cimcic_guard_not_provable k)

/-- CIMCIC defects against DefectBot: its guard fails, so it takes the `.const .D` branch. -/
theorem CIMCIC_plays_D_against_DefectBot (k fuel : Nat) :
    play (fuel + 2) (CIMCIC k) DefectBot = some .D := by
  show (if proofSearch k
            ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.C)).subst
              (CIMCIC k) DefectBot)
          then eval (fuel + 1) (CIMCIC k) DefectBot (.const Action.C)
          else eval (fuel + 1) (CIMCIC k) DefectBot (.const Action.D)) = some .D
  rw [proofSearch_false_for_CIMCIC_vs_DefectBot k]; simp [eval]

/-- **CIMCIC vs DefectBot: mutual defection (D, D)** — formerly the deliberately-omitted theorem,
    now PROVED with NO `atom_complete_false_guard` axiom. -/
theorem outcome_CIMCIC_vs_DefectBot :
    ∃ k, ∀ fuel, outcome (fuel + 2) (CIMCIC k) DefectBot = some (.D, .D) := by
  refine ⟨0, fun fuel => ?_⟩
  have hA : play (fuel + 2) (CIMCIC 0) DefectBot = some .D := CIMCIC_plays_D_against_DefectBot 0 fuel
  have hB : play (fuel + 2) DefectBot (CIMCIC 0) = some .D := by
    simpa using play_DefectBot (fuel + 1) (CIMCIC 0)
  exact outcome_of_plays _ _ _ _ _ hA hB

end PD.Theorems
