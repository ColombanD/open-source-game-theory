import PrisonersDilemma.Bots.LlmGenerations.CIMCIC
import PrisonersDilemma.Bots.DBot
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Theorems.DefectBot.Helpers
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Base.Asymptotics

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

/-!
# CIMCIC vs DBot — the honest `(D, C)` outcome

CIMCIC's guard against DBot is
`.impl (CIMCIC plays C vs DBot) (DBot plays C vs CIMCIC)`.
The consequent — DBot plays C vs CIMCIC — is TRUE but structurally UNCERTIFIABLE:
DBot cooperates only because its probe sees CIMCIC play D against `.bot DefectBot`,
and CIMCIC's D there is itself an unprovable-guard (Gödelian) fall-through, so no
`Pf` certificate for DBot's cooperation exists. Hence CIMCIC's guard is unprovable
and CIMCIC defects; DBot, run at simulation price, cooperates. Outcome `(D, C)`.
-/

/-! ## Part 1: CIMCIC plays D against `.bot DefectBot` -/

abbrev cimcic_guard_botDefect (k : Nat) : Formula :=
  .impl (.plays (CIMCIC k) (.bot DefectBot) Action.C)
        (.plays (.bot DefectBot) (CIMCIC k) Action.C)

theorem cimcic_botDefect_consequent_not_provable (k m : Nat) :
    ¬ Pf m (.plays (.bot DefectBot) (CIMCIC k) Action.C) := by
  intro h
  exact interp_bot_DefectBot_plays_C_false (CIMCIC k) (Pf_sound m _ h)

/-- **No `Pf` concludes anything guarded-tailed at the forbidden consequent** — an
    instance of the shared census `no_provable_tailTo_unreadable` (Base/Exclusion):
    the consequent atom has no certificate at any budget, and the target player is
    bridge-unreadable. (Formerly a hand-rolled 22-arm `Pf.induct`; the shared census
    runs on the Guarded `TailTo` invariant — see Base/Exclusion's header.) -/
theorem cimcic_bot_no_provable_forbidden (k : Nat) :
    ∀ {m : Nat} {φ : Formula}, Pf m φ →
      ¬ TailTo (.plays (.bot DefectBot) (CIMCIC k) Action.C) φ :=
  no_provable_tailTo_unreadable _ _ _
    (fun n hA => cimcic_botDefect_consequent_not_provable k n (.atom hA))
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

theorem cimcic_botDefect_guard_not_provable (k : Nat) :
    ¬ Pf k (cimcic_guard_botDefect k) := by
  intro h
  refine cimcic_bot_no_provable_forbidden k h ?_
  exact ⟨rfl, by simp [CIMCIC]⟩

theorem proofSearch_false_CIMCIC_vs_botDefect (k : Nat) :
    proofSearch k
      ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.C)).subst
        (CIMCIC k) (.bot DefectBot)) = false := by
  show proofSearch k (cimcic_guard_botDefect k) = false
  cases hps : proofSearch k (cimcic_guard_botDefect k) with
  | false => rfl
  | true => exact absurd ((proofSearch_spec k _).1 hps) (cimcic_botDefect_guard_not_provable k)

theorem CIMCIC_plays_D_against_botDefect (k fuel : Nat) :
    play (fuel + 2) (CIMCIC k) (.bot DefectBot) = some .D := by
  show (if proofSearch k
            ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.C)).subst
              (CIMCIC k) (.bot DefectBot))
          then eval (fuel + 1) (CIMCIC k) (.bot DefectBot) (.const Action.C)
          else eval (fuel + 1) (CIMCIC k) (.bot DefectBot) (.const Action.D)) = some .D
  rw [proofSearch_false_CIMCIC_vs_botDefect k]; simp [eval]

/-! ## Part 2: the guard's semantic content (used in Part 3) -/

theorem cimcic_antecedent_false (k : Nat) :
    ¬ (Formula.plays (CIMCIC k) (.bot DefectBot) Action.C).interp := by
  rintro ⟨n, hn⟩
  cases n with
  | zero => simp [play, eval] at hn
  | succ m =>
    cases m with
    | zero => simp [play, eval, CIMCIC] at hn
    | succ fuel =>
      have hD : play (fuel + 2) (CIMCIC k) (.bot DefectBot) = some .D :=
        CIMCIC_plays_D_against_botDefect k fuel
      rw [hD] at hn
      cases hn

theorem cimcic_guard_botDefect_interp (k : Nat) :
    (cimcic_guard_botDefect k).interp := by
  show (Formula.plays (CIMCIC k) (.bot DefectBot) Action.C).interp →
       (Formula.plays (.bot DefectBot) (CIMCIC k) Action.C).interp
  intro h
  exact absurd h (cimcic_antecedent_false k)

/-! ## Part 3: DBot plays C against CIMCIC, but this is uncertifiable -/

theorem DBot_plays_C_against_CIMCIC (k fuel : Nat) :
    play (fuel + 4) DBot (CIMCIC k) = some .C := by
  have hProbe : play (fuel + 2) (CIMCIC k) (.bot DefectBot) = some .D :=
    CIMCIC_plays_D_against_botDefect k fuel
  have hGuard :
      eval (fuel + 3) DBot (CIMCIC k) (.sim .opp (.bot DefectBot)) = some .D := by
    simpa [Nat.add_assoc] using
      (eval_sim_opp_bot_of_play (fuel + 2) DBot (CIMCIC k) DefectBot Action.D hProbe)
  have hPlay := play_ite_from_guard
    fuel 3 DBot (CIMCIC k) (.sim .opp (.bot DefectBot))
    (.const Action.D) (.const Action.C)
    Action.C Action.D
    (by rfl) hGuard
  simpa [eval] using hPlay

/-- No certificate exists for DBot playing C vs CIMCIC: it would route through
    CIMCIC's search-false play vs `.bot DefectBot`, a refutation of the TRUE guard. -/
theorem dbot_C_cert_impossible (k n : Nat) :
    ¬ PlaysProof DBot (CIMCIC k) DBot Action.C n := by
  intro cert
  cases cert with
  | ite_t hb hr hp => cases hp
  | ite_f hb hr hq =>
      cases hb with
      | sim hin =>
          cases hin with
          | search_t hg hp2 => cases hp2; exact absurd hr (by decide)
          | search_f hneg hq2 =>
              exact (Pf_sound _ _ hneg) (cimcic_guard_botDefect_interp k)

/-! ## Part 4: CIMCIC's guard against DBot is unprovable, so CIMCIC defects -/

/-- **No `Pf` concludes anything guarded-tailed at the forbidden consequent** — an
    instance of the shared census `no_provable_tailTo_unreadable` (Base/Exclusion):
    the consequent atom has no certificate at any budget, and the target player is
    bridge-unreadable. (Formerly a hand-rolled 22-arm `Pf.induct`; the shared census
    runs on the Guarded `TailTo` invariant — see Base/Exclusion's header.) -/
theorem dbot_no_provable_forbidden (k : Nat) :
    ∀ {m : Nat} {φ : Formula}, Pf m φ →
      ¬ TailTo (.plays DBot (CIMCIC k) Action.C) φ :=
  no_provable_tailTo_unreadable _ _ _
    (fun n hA => by cases hA with | mk cert hle => exact dbot_C_cert_impossible k _ cert)
    (by rintro (⟨_, _, _, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, _, _, h⟩ |
          ⟨_, _, _, _, _, _, _, h⟩ | ⟨_, _, _, _, _, _, _, h⟩) <;> simp [DBot] at h)
    (by intro L h
        cases L with
        | nil => simp [searchPlug, DBot] at h
        | cons hd tl =>
            obtain ⟨g, ψ, e⟩ := hd
            simp [searchPlug, DBot] at h)
    (by intro hd L h
        cases hd with
        | searchL g' ψ' e' => simp [ctxPlug, DBot] at h
        | iteL z' aT' other' =>
            simp only [ctxPlug, DBot, Prog.ite.injEq] at h
            exact const_ne_ctxPlug (by decide) L h.2.2.1)

abbrev cimcic_guard_DBot (k : Nat) : Formula :=
  .impl (.plays (CIMCIC k) DBot Action.C) (.plays DBot (CIMCIC k) Action.C)

theorem cimcic_DBot_guard_not_provable (k : Nat) :
    ¬ Pf k (cimcic_guard_DBot k) := by
  intro h
  refine dbot_no_provable_forbidden k h ?_
  exact ⟨rfl, by simp [CIMCIC, DBot]⟩

theorem proofSearch_false_CIMCIC_vs_DBot (k : Nat) :
    proofSearch k
      ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.C)).subst
        (CIMCIC k) DBot) = false := by
  show proofSearch k (cimcic_guard_DBot k) = false
  cases hps : proofSearch k (cimcic_guard_DBot k) with
  | false => rfl
  | true => exact absurd ((proofSearch_spec k _).1 hps) (cimcic_DBot_guard_not_provable k)

theorem CIMCIC_plays_D_against_DBot (k fuel : Nat) :
    play (fuel + 2) (CIMCIC k) DBot = some .D := by
  show (if proofSearch k
            ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.C)).subst
              (CIMCIC k) DBot)
          then eval (fuel + 1) (CIMCIC k) DBot (.const Action.C)
          else eval (fuel + 1) (CIMCIC k) DBot (.const Action.D)) = some .D
  rw [proofSearch_false_CIMCIC_vs_DBot k]; simp [eval]

/-! ## Part 5: the outcome -/

theorem llm_outcome_CIMCIC_vs_DBot :
    ∃ k₂, ∀ k, k₂ < k →
      ∃ fuel, outcome fuel (CIMCIC k) DBot = some (.D, .C) := by
  refine ⟨0, fun k _ => ⟨4, ?_⟩⟩
  have hA : play 4 (CIMCIC k) DBot = some .D := by
    simpa using CIMCIC_plays_D_against_DBot k 2
  have hB : play 4 DBot (CIMCIC k) = some .C := by
    simpa using DBot_plays_C_against_CIMCIC k 0
  exact outcome_of_plays _ _ _ _ _ hA hB

end PD.Theorems
