import PrisonersDilemma.Bots.LlmGenerations.DIMCID
import PrisonersDilemma.Bots.OBot
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Base.Asymptotics

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

/-! ## Threshold and DIMCID's defection-detection facts -/

abbrev dimcidObThresh (k : Nat) : Prop :=
  2 + (Formula.impl (.plays (DIMCID k) (.bot DefectBot) Action.C)
        (.plays (.bot DefectBot) (DIMCID k) Action.D)).size ≤ k

theorem dimcidOb_guard_bot_def_provable (k : Nat) :
    Pf (2 + (Formula.impl (.plays (DIMCID k) (.bot DefectBot) Action.C)
              (.plays (.bot DefectBot) (DIMCID k) Action.D)).size)
      (.impl (.plays (DIMCID k) (.bot DefectBot) Action.C)
             (.plays (.bot DefectBot) (DIMCID k) Action.D)) := by
  have hcons : Pf 2 (.plays (.bot DefectBot) (DIMCID k) Action.D) :=
    Pf.atom ⟨PlaysProof.bot PlaysProof.const, by decide⟩
  exact Pf.weakenImpl _ _ 2 hcons (by omega)

theorem dimcidOb_proofSearch_true_bot_def (k : Nat) (hk : dimcidObThresh k) :
    proofSearch k
      ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.D)).subst
        (DIMCID k) (.bot DefectBot)) = true := by
  show proofSearch k
      (.impl (.plays (DIMCID k) (.bot DefectBot) Action.C)
             (.plays (.bot DefectBot) (DIMCID k) Action.D)) = true
  exact (proofSearch_spec k _).2 (Pf_mono (dimcidOb_guard_bot_def_provable k) hk)

theorem dimcidOb_DIMCID_plays_D_bot_def (k fuel : Nat) (hk : dimcidObThresh k) :
    play (fuel + 2) (DIMCID k) (.bot DefectBot) = some .D := by
  have hg := dimcidOb_proofSearch_true_bot_def k hk
  show (if proofSearch k
            ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.D)).subst
              (DIMCID k) (.bot DefectBot))
          then eval (fuel + 1) (DIMCID k) (.bot DefectBot) (.const Action.D)
          else eval (fuel + 1) (DIMCID k) (.bot DefectBot) (.const Action.C)) = some .D
  rw [hg]; simp [eval]

/-! ## DIMCID cooperates vs `.bot CooperateBot` (guard unprovable) -/

theorem dimcidOb_botCB_D_not_provable (k m : Nat) :
    ¬ Pf m (.plays (.bot CooperateBot) (DIMCID k) Action.D) := by
  intro h
  obtain ⟨n, hn⟩ := Pf_sound m _ h
  cases n with
  | zero => simp [play, eval] at hn
  | succ n' =>
    cases n' with
    | zero => simp [play, eval] at hn
    | succ n'' =>
      have : play (n'' + 2) (.bot CooperateBot) (DIMCID k) = some .C := by
        show eval (n'' + 2) (.bot CooperateBot) (DIMCID k) (.bot CooperateBot) = some .C
        simp [eval, CooperateBot]
      rw [this] at hn
      exact absurd hn (by decide)

theorem dimcidOb_dimcid_botCB_guard_not_provable (k : Nat) :
    ¬ Pf k (.impl (.plays (DIMCID k) (.bot CooperateBot) Action.C)
                  (.plays (.bot CooperateBot) (DIMCID k) Action.D)) := by
  intro h
  refine no_provable_tailTo_unreadable (.bot CooperateBot) (DIMCID k) Action.D
    (fun n hA => dimcidOb_botCB_D_not_provable k n (.atom hA))
    (by rintro (⟨_, _, _, _, hh⟩ | ⟨_, _, hh⟩ | ⟨_, _, hh⟩ | ⟨_, _, _, _, hh⟩ |
          ⟨_, _, _, _, _, _, _, hh⟩ | ⟨_, _, _, _, _, _, _, hh⟩) <;>
          simp [CooperateBot] at hh)
    (by intro L hh
        cases L with
        | nil => simp [searchPlug, CooperateBot] at hh
        | cons hd tl =>
            obtain ⟨g, ψ, e⟩ := hd
            simp [searchPlug, CooperateBot] at hh)
    (by intro hd L hh
        cases hd with
        | searchL g' ψ' e' => simp [ctxPlug, CooperateBot] at hh
        | iteL z' aT' other' => simp [ctxPlug, CooperateBot] at hh)
    h ?_
  exact ⟨rfl, by simp [DIMCID, CooperateBot]⟩

theorem dimcidOb_proofSearch_false_botCB (k : Nat) :
    proofSearch k
      ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.D)).subst
        (DIMCID k) (.bot CooperateBot)) = false := by
  cases hps : proofSearch k
      ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.D)).subst
        (DIMCID k) (.bot CooperateBot)) with
  | false => rfl
  | true =>
      exact absurd ((proofSearch_spec k _).1 hps) (dimcidOb_dimcid_botCB_guard_not_provable k)

theorem dimcidOb_DIMCID_plays_C_botCB (k fuel : Nat) :
    play (fuel + 2) (DIMCID k) (.bot CooperateBot) = some .C := by
  show (if proofSearch k
            ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.D)).subst
              (DIMCID k) (.bot CooperateBot))
          then eval (fuel + 1) (DIMCID k) (.bot CooperateBot) (.const Action.D)
          else eval (fuel + 1) (DIMCID k) (.bot CooperateBot) (.const Action.C)) = some .C
  rw [dimcidOb_proofSearch_false_botCB k]; simp [eval]

/-! ## OBot plays D vs DIMCID -/

theorem dimcidOb_OBot_plays_D (k fuel : Nat) (hk : dimcidObThresh k) :
    play (fuel + 5) OBot (DIMCID k) = some .D := by
  have hGuard1 :
      eval (fuel + 4) OBot (DIMCID k) (.sim .opp (.bot CooperateBot)) = some .C := by
    have hProbe : play (fuel + 3) (DIMCID k) (.bot CooperateBot) = some .C := by
      simpa [Nat.add_assoc] using dimcidOb_DIMCID_plays_C_botCB k (fuel + 1)
    simpa [Nat.add_assoc] using
      (eval_sim_opp_bot_of_play (fuel + 3) OBot (DIMCID k) CooperateBot Action.C hProbe)
  have hGuard2 :
      eval (fuel + 3) OBot (DIMCID k) (.sim .opp (.bot DefectBot)) = some .D := by
    have hProbe : play (fuel + 2) (DIMCID k) (.bot DefectBot) = some .D :=
      dimcidOb_DIMCID_plays_D_bot_def k fuel hk
    simpa [Nat.add_assoc] using
      (eval_sim_opp_bot_of_play (fuel + 2) OBot (DIMCID k) DefectBot Action.D hProbe)
  have hPlay := play_ite_from_guard
    fuel 4 OBot (DIMCID k) (.sim .opp (.bot CooperateBot))
    (.ite (.sim .opp (.bot DefectBot)) Action.C (.const Action.C) (.const Action.D))
    (.const Action.D)
    Action.C Action.C
    (by rfl) hGuard1
  have hInner :
      eval (fuel + 4) OBot (DIMCID k)
        (.ite (.sim .opp (.bot DefectBot)) Action.C (.const Action.C) (.const Action.D)) =
          some .D := by
    simpa [Nat.add_assoc] using
      (eval_ite_from_guard (fuel + 3) OBot (DIMCID k)
        (.sim .opp (.bot DefectBot)) (.const Action.C) (.const Action.D)
        Action.C Action.D hGuard2)
  simpa [hInner] using hPlay

/-! ## DIMCID's guard vs OBot is FALSE-interp; floor kills it -/

theorem dimcidOb_guard_botCB_false (k : Nat) :
    ¬ ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.D)).subst
        (DIMCID k) (.bot CooperateBot)).interp := by
  show ¬ (Formula.impl (.plays (DIMCID k) (.bot CooperateBot) Action.C)
              (.plays (.bot CooperateBot) (DIMCID k) Action.D)).interp
  intro himpl
  have hante : (Formula.plays (DIMCID k) (.bot CooperateBot) Action.C).interp :=
    ⟨2, dimcidOb_DIMCID_plays_C_botCB k 0⟩
  obtain ⟨n, hn⟩ := himpl hante
  cases n with
  | zero => simp [play, eval] at hn
  | succ n' =>
    cases n' with
    | zero => simp [play, eval] at hn
    | succ n'' =>
      have : play (n'' + 2) (.bot CooperateBot) (DIMCID k) = some .C := by
        show eval (n'' + 2) (.bot CooperateBot) (DIMCID k) (.bot CooperateBot) = some .C
        simp [eval, CooperateBot]
      rw [this] at hn
      exact absurd hn (by decide)

theorem dimcidOb_no_provable_OBot_D_tail (k : Nat) :
    ∀ K φ, Pf K φ → K ≤ k →
      TailTo (.plays OBot (DIMCID k) .D) φ → False := by
  intro K φ hp hK ht
  refine no_provable_probeFirst_tail k CooperateBot
      (.ite (.sim .opp (.bot DefectBot)) .C (.const .C) (.const .D))
      (.const .D) .C .D
      (.impl (.plays .self .opp Action.C) (.plays .opp .self Action.D))
      (.const .D) (.const .C) ?_ ?_ ?_ K φ hp hK ?_
  · exact dimcidOb_guard_botCB_false k
  · intro k' ψ c0 c1 h; simp at h
  · intro L h
    cases L with
    | nil => simp [ctxPlug] at h
    | cons hd tl =>
        cases hd with
        | searchL g' ψ' e' => simp [ctxPlug] at h
        | iteL z' aT' other' =>
            simp only [ctxPlug, Prog.ite.injEq] at h
            exact const_ne_ctxPlug (by decide) tl h.2.2.1
  · simpa [OBot, DIMCID] using ht

/-! ## DIMCID's guard vs OBot is unprovable → DIMCID cooperates -/

theorem dimcidOb_dimcid_OBot_guard_not_provable (k : Nat) :
    ¬ Pf k (.impl (.plays (DIMCID k) OBot Action.C)
                  (.plays OBot (DIMCID k) Action.D)) := by
  intro h
  refine dimcidOb_no_provable_OBot_D_tail k k _ h le_rfl ?_
  refine ⟨rfl, ?_⟩
  intro hA
  simp only [TailTo] at hA
  exact absurd hA (by simp [OBot, DIMCID])

theorem dimcidOb_proofSearch_false_OBot (k : Nat) :
    proofSearch k
      ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.D)).subst
        (DIMCID k) OBot) = false := by
  show proofSearch k
      (.impl (.plays (DIMCID k) OBot Action.C) (.plays OBot (DIMCID k) Action.D)) = false
  cases hps : proofSearch k
      (.impl (.plays (DIMCID k) OBot Action.C) (.plays OBot (DIMCID k) Action.D)) with
  | false => rfl
  | true =>
      exact absurd ((proofSearch_spec k _).1 hps) (dimcidOb_dimcid_OBot_guard_not_provable k)

theorem dimcidOb_DIMCID_plays_C_against_OBot (k fuel : Nat) :
    play (fuel + 2) (DIMCID k) OBot = some .C := by
  have hg := dimcidOb_proofSearch_false_OBot k
  show (if proofSearch k
            ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.D)).subst
              (DIMCID k) OBot)
          then eval (fuel + 1) (DIMCID k) OBot (.const Action.D)
          else eval (fuel + 1) (DIMCID k) OBot (.const Action.C)) = some .C
  rw [hg]; simp [eval]

/-! ## Final theorem -/

theorem llm_outcome_DIMCID_vs_OBot :
    ∃ k₂, ∀ k, k₂ < k →
      ∃ fuel, outcome fuel (DIMCID k) OBot = some (.C, .D) := by
  obtain ⟨K, hK⟩ := linear_log2_add_le 4 100
  refine ⟨K, fun k hk => ⟨7, ?_⟩⟩
  have hthresh : dimcidObThresh k := by
    have hsz : 2 + (Formula.impl (.plays (DIMCID k) (.bot DefectBot) Action.C)
                (.plays (.bot DefectBot) (DIMCID k) Action.D)).size
              ≤ 4 * Nat.log2 k + 100 := by
      simp only [DIMCID, DefectBot, Formula.size, Prog.size, numCost]; omega
    have hkK : 4 * Nat.log2 k + 100 ≤ k := hK k (by omega)
    show 2 + _ ≤ k
    omega
  have hA : play 7 (DIMCID k) OBot = some .C := by
    simpa using dimcidOb_DIMCID_plays_C_against_OBot k 5
  have hB : play 7 OBot (DIMCID k) = some .D := by
    simpa using dimcidOb_OBot_plays_D k 2 hthresh
  exact outcome_of_plays _ _ _ _ _ hA hB

end PD.Theorems
