import PrisonersDilemma.Bots.LlmGenerations.CIMCIC
import PrisonersDilemma.Bots.OBot
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Base.Asymptotics
import PrisonersDilemma.Theorems.CIMCIC.vs_EBot
import PrisonersDilemma.Outcome

/-!
# CIMCIC vs OBot — `(D, D)` past the weakenImpl threshold

The last base pair the Def-3 comparison consulted without a theorem (stipulated
`(D, D)`); the value the tau layer's obot column predicted.

* OBot watches "does my opponent cooperate with BOTH the cooperator and the
  defector?" — CIMCIC cooperates with `.bot CooperateBot` (its consequent is a
  cheap constant certificate, `proofSearch_true_CIMCIC_vs_botCoop`) but DEFECTS
  against `.bot DefectBot` (`CIMCIC_plays_D_against_botDef`), so OBot's second
  watch falls to its defection branch: OBot plays D.
* CIMCIC's guard "I cooperate with OBot → OBot cooperates with me" is refuted by
  SOUNDNESS alone: were it provable, CIMCIC's search would fire (antecedent
  true), so the consequent — OBot cooperating with CIMCIC — would be true; but
  OBot REALLY defects against CIMCIC, and `eval` is deterministic. No census
  needed: the consequent is false in every world where the guard fires.

The gate is inherited from `proofSearch_true_CIMCIC_vs_botCoop` (the implication's
size must fit the budget), hence the `∃ k₂` form.
-/

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

/-- OBot defects against CIMCIC: watch 1 (vs the cooperator) passes, watch 2 (vs
    the defector) catches the conditional cooperator defecting. -/
theorem co_OBot_plays_D (k fuel : Nat)
    (hbc : proofSearch k
        ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.C)).subst
          (CIMCIC k) (.bot CooperateBot)) = true) :
    play (fuel + 5) OBot (CIMCIC k) = some .D := by
  have hCimC : play (fuel + 3) (CIMCIC k) (.bot CooperateBot) = some .C := by
    simpa [Nat.add_assoc] using CIMCIC_plays_C_against_botCoop k (fuel + 1) hbc
  have hGuard1 :
      eval (fuel + 4) OBot (CIMCIC k) (.sim .opp (.bot CooperateBot)) = some .C := by
    simpa [Nat.add_assoc] using
      (eval_sim_opp_bot_of_play (fuel + 3) OBot (CIMCIC k) CooperateBot Action.C hCimC)
  have hCimD : play (fuel + 2) (CIMCIC k) (.bot DefectBot) = some .D :=
    CIMCIC_plays_D_against_botDef k fuel
  have hGuard2 :
      eval (fuel + 3) OBot (CIMCIC k) (.sim .opp (.bot DefectBot)) = some .D := by
    simpa [Nat.add_assoc] using
      (eval_sim_opp_bot_of_play (fuel + 2) OBot (CIMCIC k) DefectBot Action.D hCimD)
  have hInner :
      eval (fuel + 4) OBot (CIMCIC k)
        (.ite (.sim .opp (.bot DefectBot)) Action.C (.const Action.C)
          (.const Action.D)) = some .D := by
    simpa [Nat.add_assoc] using
      (eval_ite_from_guard (fuel + 3) OBot (CIMCIC k)
        (.sim .opp (.bot DefectBot)) (.const Action.C) (.const Action.D)
        Action.C Action.D hGuard2)
  have hPlay := play_ite_from_guard
    fuel 4 OBot (CIMCIC k) (.sim .opp (.bot CooperateBot))
    (.ite (.sim .opp (.bot DefectBot)) Action.C (.const Action.C) (.const Action.D))
    (.const Action.D)
    Action.C Action.C
    (by rfl) hGuard1
  simpa [Nat.add_assoc, hInner] using hPlay

/-- CIMCIC's guard against OBot is unprovable — by soundness and determinism:
    a provable guard fires CIMCIC's own search, making the antecedent true, so
    the consequent would make OBot cooperate; but OBot defects. -/
theorem co_cimcic_guard_not_provable (k : Nat)
    (hOD : ∃ n, play n OBot (CIMCIC k) = some .D) :
    ¬ Pf k (.impl (.plays (CIMCIC k) OBot Action.C)
                  (.plays OBot (CIMCIC k) Action.C)) := by
  intro h
  have hps : proofSearch k
      ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.C)).subst
        (CIMCIC k) OBot) = true :=
    (proofSearch_spec _ _).2 h
  have hant : (Formula.plays (CIMCIC k) OBot Action.C).interp := by
    refine ⟨2, ?_⟩
    show (if proofSearch k
              ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.C)).subst
                (CIMCIC k) OBot)
            then eval 1 (CIMCIC k) OBot (.const Action.C)
            else eval 1 (CIMCIC k) OBot (.const Action.D)) = some .C
    rw [hps]; simp [eval]
  have hcons : (Formula.plays OBot (CIMCIC k) Action.C).interp :=
    (Pf_sound k _ h) hant
  obtain ⟨n1, hn1⟩ := hcons
  obtain ⟨n2, hn2⟩ := hOD
  have h1 : eval (max n1 n2) OBot (CIMCIC k) OBot = some Action.C :=
    eval_mono_le hn1 (max n1 n2) (Nat.le_max_left _ _)
  have h2 : eval (max n1 n2) OBot (CIMCIC k) OBot = some Action.D :=
    eval_mono_le hn2 (max n1 n2) (Nat.le_max_right _ _)
  rw [h1] at h2
  exact absurd (Option.some.inj h2) (by decide)

theorem co_proofSearch_false_cimcic (k : Nat)
    (hOD : ∃ n, play n OBot (CIMCIC k) = some .D) :
    proofSearch k
      ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.C)).subst
        (CIMCIC k) OBot) = false := by
  show proofSearch k
      (.impl (.plays (CIMCIC k) OBot Action.C)
             (.plays OBot (CIMCIC k) Action.C)) = false
  cases hps : proofSearch k
      (.impl (.plays (CIMCIC k) OBot Action.C)
             (.plays OBot (CIMCIC k) Action.C)) with
  | false => rfl
  | true =>
      exact absurd ((proofSearch_spec k _).1 hps)
        (co_cimcic_guard_not_provable k hOD)

theorem co_CIMCIC_plays_D (k fuel : Nat)
    (hOD : ∃ n, play n OBot (CIMCIC k) = some .D) :
    play (fuel + 2) (CIMCIC k) OBot = some .D := by
  have hg := co_proofSearch_false_cimcic k hOD
  show (if proofSearch k
            ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.C)).subst
              (CIMCIC k) OBot)
          then eval (fuel + 1) (CIMCIC k) OBot (.const Action.C)
          else eval (fuel + 1) (CIMCIC k) OBot (.const Action.D)) = some .D
  rw [hg]; simp [eval]

/-- **CIMCIC vs OBot → (D, D)** past the weakenImpl threshold: the tester
    convicts the conditional cooperator, and the conditional cooperator — unable
    to certify a cooperation that does not exist — returns the favor. -/
@[outcome]
theorem outcome_CIMCIC_vs_OBot :
    OutcomeSpec .eventual 5
      CIMCIC (fun _ => OBot) (some (.D, .D)) := by
  obtain ⟨K, hK⟩ := proofSearch_true_CIMCIC_vs_botCoop
  refine ⟨K, fun k hk fuel => ?_⟩
  have hbc := hK k (Nat.le_of_lt hk)
  refine outcome_mono_le (N := 5) ?_ (fuel + 5) (by omega)
  have hB : play 5 OBot (CIMCIC k) = some .D := by
    simpa using co_OBot_plays_D k 0 hbc
  have hA : play 5 (CIMCIC k) OBot = some .D := by
    simpa using co_CIMCIC_plays_D k 3 ⟨5, hB⟩
  exact outcome_of_plays _ _ _ _ _ hA hB

end PD.Theorems
