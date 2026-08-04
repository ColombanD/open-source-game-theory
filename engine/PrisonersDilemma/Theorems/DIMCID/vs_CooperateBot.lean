import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Bots.LlmGenerations.DIMCID
import PrisonersDilemma.Theorems.CooperateBot.Helpers
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Base.Asymptotics

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

/-- The substituted DIMCID guard against CooperateBot. -/
abbrev dimcid_guard (k : Nat) : Formula :=
  .impl (.plays (DIMCID k) CooperateBot Action.C) (.plays CooperateBot (DIMCID k) Action.D)

/-- The consequent atom `CooperateBot plays D vs DIMCID` is UNPROVABLE: CooperateBot plays C. -/
theorem dimcid_consequent_not_provable (k m : Nat) :
    ¬ Pf m (.plays CooperateBot (DIMCID k) Action.D) := by
  intro h
  obtain ⟨n, hn⟩ := Pf_sound m _ h
  have : play n CooperateBot (DIMCID k) = some Action.C ∨ play n CooperateBot (DIMCID k) = none := by
    cases n with
    | zero => right; rfl
    | succ n => left; exact play_CooperateBot n (DIMCID k)
  rcases this with hC | hNone
  · rw [hC] at hn; exact absurd hn (by decide)
  · rw [hNone] at hn; exact absurd hn (by decide)

/-- **No `Pf` concludes anything guarded-tailed at the forbidden consequent** — an
    instance of the shared census `no_provable_tailTo_unreadable` (Base/Exclusion):
    the consequent atom has no certificate at any budget, and the target player is
    bridge-unreadable. (Formerly a hand-rolled 22-arm `Pf.induct`; the shared census
    runs on the Guarded `TailTo` invariant — see Base/Exclusion's header.) -/
theorem dimcid_no_provable_forbidden (k : Nat) :
    ∀ {m : Nat} {φ : Formula}, Pf m φ →
      ¬ TailTo (.plays CooperateBot (DIMCID k) Action.D) φ :=
  no_provable_tailTo_unreadable _ _ _
    (fun n hA => dimcid_consequent_not_provable k n (.atom hA))
    (by rintro (⟨_, _, _, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, _, _, h⟩ |
          ⟨_, _, _, _, _, _, _, h⟩ | ⟨_, _, _, _, _, _, _, h⟩) <;> simp [CooperateBot] at h)
    (by intro L h
        cases L with
        | nil => simp [searchPlug, CooperateBot] at h
        | cons hd tl =>
            obtain ⟨g, ψ, e⟩ := hd
            simp [searchPlug, CooperateBot] at h)
    (by intro hd L h
        cases hd with
        | searchL g' ψ' e' => simp [ctxPlug, CooperateBot] at h
        | iteL z' aT' other' => simp [ctxPlug, CooperateBot] at h)
    (by intro hd L h
        cases hd <;> simp [plug2, CooperateBot] at h)

theorem dimcid_guard_not_provable (k : Nat) : ¬ Pf k (dimcid_guard k) := by
  intro h
  refine dimcid_no_provable_forbidden k h ?_
  exact ⟨rfl, by simp [DIMCID, CooperateBot]⟩

theorem proofSearch_false_for_DIMCID_vs_CooperateBot (k : Nat) :
    proofSearch k
      ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.D)).subst
        (DIMCID k) CooperateBot) = false := by
  show proofSearch k (dimcid_guard k) = false
  cases hps : proofSearch k (dimcid_guard k) with
  | false => rfl
  | true => exact absurd ((proofSearch_spec k (dimcid_guard k)).1 hps) (dimcid_guard_not_provable k)

/-- DIMCID cooperates against CooperateBot: its guard fails, so it takes the `.const .C` branch. -/
theorem DIMCID_plays_C_against_CooperateBot (k fuel : Nat) :
    play (fuel + 2) (DIMCID k) CooperateBot = some .C := by
  show (if proofSearch k
            ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.D)).subst
              (DIMCID k) CooperateBot)
          then eval (fuel + 1) (DIMCID k) CooperateBot (.const Action.D)
          else eval (fuel + 1) (DIMCID k) CooperateBot (.const Action.C)) = some .C
  rw [proofSearch_false_for_DIMCID_vs_CooperateBot k]; simp [eval]

/-- **DIMCID vs CooperateBot: mutual cooperation (C, C)** — formerly deliberately-omitted, now
    PROVED with NO `atom_complete_false_guard` axiom. -/
theorem outcome_DIMCID_vs_CooperateBot :
    ∃ k, ∀ fuel, outcome (fuel + 2) (DIMCID k) CooperateBot = some (.C, .C) := by
  refine ⟨0, fun fuel => ?_⟩
  have hA : play (fuel + 2) (DIMCID 0) CooperateBot = some .C := DIMCID_plays_C_against_CooperateBot 0 fuel
  have hB : play (fuel + 2) CooperateBot (DIMCID 0) = some .C := by
    simpa using play_CooperateBot (fuel + 1) (DIMCID 0)
  exact outcome_of_plays _ _ _ _ _ hA hB

end PD.Theorems
