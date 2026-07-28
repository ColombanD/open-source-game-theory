import PrisonersDilemma.Bots.LlmGenerations.CIMCIC
import PrisonersDilemma.Bots.EBot
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Bots.MirrorBot
import PrisonersDilemma.Theorems.CooperateBot.Helpers
import PrisonersDilemma.Theorems.DefectBot.Helpers
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Base.Asymptotics

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

/-!
# CIMCIC vs EBot — the honest `(D, C)` outcome

EBot cooperates with CIMCIC (its probes see CIMCIC defect vs `.bot DefectBot`,
then cooperate vs `.bot CooperateBot`, so EBot's second guard fires → C). But
CIMCIC DEFECTS against EBot: its guard `(CIMCIC plays C vs EBot) → (EBot plays C
vs CIMCIC)` is structurally unprovable — the consequent `EBot plays C vs CIMCIC`
is TRUE but UNCERTIFIABLE, because EBot's play crosses CIMCIC's failed search vs
`.bot DefectBot`, whose failure is IRREFUTABLE (the guard's interp is vacuously
true, so its negation cannot be proven). Hence no `search_f` certificate exists,
no play certificate for EBot exists, and the consequent — and therefore the
whole guard — is unprovable. CIMCIC falls through to `.const .D`.
-/

/-! ## CIMCIC vs `.bot DefectBot` : defects (guard consequent false, unprovable) -/

abbrev cimcic_guard_botDef (k : Nat) : Formula :=
  .impl (.plays (CIMCIC k) (.bot DefectBot) Action.C)
        (.plays (.bot DefectBot) (CIMCIC k) Action.C)

theorem cimcic_botDef_consequent_not_provable (k m : Nat) :
    ¬ Pf m (.plays (.bot DefectBot) (CIMCIC k) Action.C) := by
  intro h
  exact interp_bot_DefectBot_plays_C_false (CIMCIC k) (Pf_sound m _ h)

/-- **No `Pf` concludes anything guarded-tailed at the forbidden consequent** — an
    instance of the shared census `no_provable_tailTo_unreadable` (Base/Exclusion):
    the consequent atom has no certificate at any budget, and the target player is
    bridge-unreadable. (Formerly a hand-rolled 22-arm `Pf.induct`; the shared census
    runs on the Guarded `TailTo` invariant — see Base/Exclusion's header.) -/
theorem cimcic_botDef_no_provable_forbidden (k : Nat) :
    ∀ {m : Nat} {φ : Formula}, Pf m φ →
      ¬ TailTo (.plays (.bot DefectBot) (CIMCIC k) Action.C) φ :=
  no_provable_tailTo_unreadable _ _ _
    (fun n hA => cimcic_botDef_consequent_not_provable k n (.atom hA))
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

theorem cimcic_botDef_guard_not_provable (k : Nat) : ¬ Pf k (cimcic_guard_botDef k) := by
  intro h
  refine cimcic_botDef_no_provable_forbidden k h ?_
  exact ⟨rfl, by simp [CIMCIC]⟩

theorem proofSearch_false_CIMCIC_vs_botDef (k : Nat) :
    proofSearch k
      ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.C)).subst
        (CIMCIC k) (.bot DefectBot)) = false := by
  show proofSearch k (cimcic_guard_botDef k) = false
  cases hps : proofSearch k (cimcic_guard_botDef k) with
  | false => rfl
  | true => exact absurd ((proofSearch_spec k _).1 hps) (cimcic_botDef_guard_not_provable k)

/-- CIMCIC defects against `.bot DefectBot`. -/
theorem CIMCIC_plays_D_against_botDef (k fuel : Nat) :
    play (fuel + 2) (CIMCIC k) (.bot DefectBot) = some .D := by
  have hg := proofSearch_false_CIMCIC_vs_botDef k
  show (if proofSearch k
            ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.C)).subst
              (CIMCIC k) (.bot DefectBot))
          then eval (fuel + 1) (CIMCIC k) (.bot DefectBot) (.const Action.C)
          else eval (fuel + 1) (CIMCIC k) (.bot DefectBot) (.const Action.D)) = some .D
  rw [hg]; simp [eval]

/-- CIMCIC never plays C against `.bot DefectBot` (needed for the guard's interp). -/
theorem interp_CIMCIC_plays_C_vs_botDef_false (k : Nat) :
    ¬ (Formula.plays (CIMCIC k) (.bot DefectBot) Action.C).interp := by
  rintro ⟨n, hn⟩
  have hg := proofSearch_false_CIMCIC_vs_botDef k
  cases n with
  | zero => simp [play, eval] at hn
  | succ m =>
      cases m with
      | zero =>
          have : play 1 (CIMCIC k) (.bot DefectBot) = none := by
            show (if proofSearch k _ then eval 0 (CIMCIC k) (.bot DefectBot) (.const Action.C)
                  else eval 0 (CIMCIC k) (.bot DefectBot) (.const Action.D)) = none
            rw [hg]; simp [eval]
          rw [this] at hn; cases hn
      | succ m2 =>
          have : play (m2+2) (CIMCIC k) (.bot DefectBot) = some .D := by
            show (if proofSearch k _ then eval (m2+1) (CIMCIC k) (.bot DefectBot) (.const Action.C)
                  else eval (m2+1) (CIMCIC k) (.bot DefectBot) (.const Action.D)) = some .D
            rw [hg]; simp [eval]
          rw [this] at hn; cases hn

/-- CIMCIC's guard against `.bot DefectBot` is TRUE (vacuously — antecedent false). -/
theorem interp_cimcic_guard_botDef_true (k : Nat) :
    (cimcic_guard_botDef k).interp := by
  show (Formula.plays (CIMCIC k) (.bot DefectBot) Action.C).interp →
       (Formula.plays (.bot DefectBot) (CIMCIC k) Action.C).interp
  intro hA
  exact absurd hA (interp_CIMCIC_plays_C_vs_botDef_false k)

/-! ## CIMCIC vs `.bot CooperateBot` : cooperates (guard consequent provable) -/

theorem cimcic_botCoop_consequent (k : Nat) :
    Pf (atom_cost 2) (Formula.plays (.bot CooperateBot) (CIMCIC k) Action.C) :=
  Pf.atom ⟨PlaysProof.bot PlaysProof.const, by decide⟩

theorem proofSearch_true_CIMCIC_vs_botCoop :
    ∃ K, ∀ k, k ≥ K →
      proofSearch k
        ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.C)).subst
          (CIMCIC k) (.bot CooperateBot)) = true := by
  obtain ⟨K, hK⟩ := linear_log2_add_le 10 100
  refine ⟨K, fun k hk => ?_⟩
  refine (proofSearch_spec _ _).2 ?_
  show Pf k
    (Formula.impl (.plays (CIMCIC k) (.bot CooperateBot) Action.C)
                  (.plays (.bot CooperateBot) (CIMCIC k) Action.C))
  refine Pf.weakenImpl _ _ (atom_cost 2) (cimcic_botCoop_consequent k) ?_
  have hb := hK k hk
  have h1 : atom_cost 2 = 7 := by decide
  simp only [numCost, Formula.size, Prog.size, CIMCIC, CooperateBot]
  omega

theorem CIMCIC_plays_C_against_botCoop (k fuel : Nat)
    (hk : proofSearch k
        ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.C)).subst
          (CIMCIC k) (.bot CooperateBot)) = true) :
    play (fuel + 2) (CIMCIC k) (.bot CooperateBot) = some .C := by
  show (if proofSearch k
            ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.C)).subst
              (CIMCIC k) (.bot CooperateBot))
          then eval (fuel + 1) (CIMCIC k) (.bot CooperateBot) (.const Action.C)
          else eval (fuel + 1) (CIMCIC k) (.bot CooperateBot) (.const Action.D)) = some .C
  rw [hk]; simp [eval]

/-! ## EBot plays C against CIMCIC -/

theorem EBot_plays_C_against_CIMCIC (k fuel : Nat)
    (hk : proofSearch k
        ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.C)).subst
          (CIMCIC k) (.bot CooperateBot)) = true) :
    play (fuel + 5) EBot (CIMCIC k) = some .C := by
  have hCimD : play (fuel + 3) (CIMCIC k) (.bot DefectBot) = some .D := by
    simpa [Nat.add_assoc] using CIMCIC_plays_D_against_botDef k (fuel + 1)
  have hGuard1 :
      eval (fuel + 4) EBot (CIMCIC k) (.sim .opp (.bot DefectBot)) = some .D := by
    simpa [Nat.add_assoc] using
      (eval_sim_opp_bot_of_play (fuel + 3) EBot (CIMCIC k) DefectBot Action.D hCimD)
  have hCimC : play (fuel + 2) (CIMCIC k) (.bot CooperateBot) = some .C :=
    CIMCIC_plays_C_against_botCoop k fuel hk
  have hGuard2 :
      eval (fuel + 3) EBot (CIMCIC k) (.sim .opp (.bot CooperateBot)) = some .C := by
    simpa [Nat.add_assoc] using
      (eval_sim_opp_bot_of_play (fuel + 2) EBot (CIMCIC k) CooperateBot Action.C hCimC)
  have hInner :
      eval (fuel + 4) EBot (CIMCIC k)
        (.ite (.sim .opp (.bot CooperateBot)) Action.C (.const Action.C)
          (.ite (.sim .opp (.bot MirrorBot)) Action.C (.const Action.C) (.const Action.D))) =
        some .C := by
    simpa [Nat.add_assoc] using
      (eval_ite_from_guard (fuel + 3) EBot (CIMCIC k)
        (.sim .opp (.bot CooperateBot)) (.const Action.C)
        (.ite (.sim .opp (.bot MirrorBot)) Action.C (.const Action.C) (.const Action.D))
        Action.C Action.C hGuard2)
  have hPlay := play_ite_from_guard
    fuel 4 EBot (CIMCIC k) (.sim .opp (.bot DefectBot))
    (.const Action.D)
    (.ite (.sim .opp (.bot CooperateBot)) Action.C (.const Action.C)
      (.ite (.sim .opp (.bot MirrorBot)) Action.C (.const Action.C) (.const Action.D)))
    Action.C Action.D
    (by rfl) hGuard1
  simpa [Nat.add_assoc, hInner] using hPlay

/-! ## CIMCIC's guard against EBot is unprovable → CIMCIC defects -/

theorem guard_subst_eq (k : Nat) :
    ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.C)).subst
      (CIMCIC k) (.bot DefectBot)) = cimcic_guard_botDef k := by
  rfl

theorem no_cert_CIMCIC_vs_botDef (k : Nat) (r : Action) (n : Nat) :
    ¬ PlaysProof (CIMCIC k) (.bot DefectBot) (CIMCIC k) r n := by
  intro h
  unfold CIMCIC at h
  cases h with
  | search_t hprov hbr =>
      have hprov' : Pf k (cimcic_guard_botDef k) := hprov
      exact cimcic_botDef_guard_not_provable k hprov'
  | search_f hneg hbr =>
      have hneg' : Pf _ (.neg (cimcic_guard_botDef k)) := hneg
      exact (Pf_sound _ _ hneg') (interp_cimcic_guard_botDef_true k)

theorem no_cert_EBot_guard1_vs_CIMCIC (k : Nat) (r : Action) (n : Nat) :
    ¬ PlaysProof EBot (CIMCIC k) (.sim .opp (.bot DefectBot)) r n := by
  intro h
  cases h with
  | sim hin =>
      simp only [Prog.subst] at hin
      exact no_cert_CIMCIC_vs_botDef k r _ hin

theorem no_cert_EBot_vs_CIMCIC (k : Nat) (a : Action) (n : Nat) :
    ¬ PlaysProof EBot (CIMCIC k) EBot a n := by
  intro h
  unfold EBot at h
  cases h with
  | ite_t hg hr hbr => exact no_cert_EBot_guard1_vs_CIMCIC k _ _ hg
  | ite_f hg hr hbr => exact no_cert_EBot_guard1_vs_CIMCIC k _ _ hg

/-- **No `Pf` concludes anything guarded-tailed at the forbidden consequent** — an
    instance of the shared census `no_provable_tailTo_unreadable` (Base/Exclusion):
    the consequent atom has no certificate at any budget, and the target player is
    bridge-unreadable. (Formerly a hand-rolled 22-arm `Pf.induct`; the shared census
    runs on the Guarded `TailTo` invariant — see Base/Exclusion's header.) -/
theorem ebot_no_provable_forbidden (k : Nat) :
    ∀ {m : Nat} {φ : Formula}, Pf m φ →
      ¬ TailTo (.plays EBot (CIMCIC k) Action.C) φ :=
  no_provable_tailTo_unreadable _ _ _
    (fun n hA => by cases hA with | mk cert hle => exact no_cert_EBot_vs_CIMCIC k _ _ cert)
    (by rintro (⟨_, _, _, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, _, _, h⟩ |
          ⟨_, _, _, _, _, _, _, h⟩ | ⟨_, _, _, _, _, _, _, h⟩) <;> simp [EBot] at h)
    (by intro L h
        cases L with
        | nil => simp [searchPlug, EBot] at h
        | cons hd tl =>
            obtain ⟨g, ψ, e⟩ := hd
            simp [searchPlug, EBot] at h)
    (by intro hd L h
        cases hd with
        | searchL g' ψ' e' => simp [ctxPlug, EBot] at h
        | iteL z' aT' other' =>
            simp only [ctxPlug, EBot, Prog.ite.injEq] at h
            exact const_ne_ctxPlug (by decide) L h.2.2.1)

abbrev cimcic_guard_EBot (k : Nat) : Formula :=
  .impl (.plays (CIMCIC k) EBot Action.C) (.plays EBot (CIMCIC k) Action.C)

theorem cimcic_guard_EBot_not_provable (k : Nat) : ¬ Pf k (cimcic_guard_EBot k) := by
  intro h
  refine ebot_no_provable_forbidden k h ?_
  exact ⟨rfl, by simp [CIMCIC, EBot]⟩

theorem proofSearch_false_CIMCIC_vs_EBot (k : Nat) :
    proofSearch k
      ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.C)).subst
        (CIMCIC k) EBot) = false := by
  show proofSearch k (cimcic_guard_EBot k) = false
  cases hps : proofSearch k (cimcic_guard_EBot k) with
  | false => rfl
  | true => exact absurd ((proofSearch_spec k _).1 hps) (cimcic_guard_EBot_not_provable k)

theorem CIMCIC_plays_D_against_EBot (k fuel : Nat) :
    play (fuel + 2) (CIMCIC k) EBot = some .D := by
  have hg := proofSearch_false_CIMCIC_vs_EBot k
  show (if proofSearch k
            ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.C)).subst
              (CIMCIC k) EBot)
          then eval (fuel + 1) (CIMCIC k) EBot (.const Action.C)
          else eval (fuel + 1) (CIMCIC k) EBot (.const Action.D)) = some .D
  rw [hg]; simp [eval]

/-! ## The outcome -/

theorem llm_outcome_CIMCIC_vs_EBot :
    ∃ k₂, ∀ k, k₂ < k →
      ∃ fuel, outcome fuel (CIMCIC k) EBot = some (.D, .C) := by
  obtain ⟨K, hK⟩ := proofSearch_true_CIMCIC_vs_botCoop
  refine ⟨K, fun k hk => ?_⟩
  have hk' : k ≥ K := Nat.le_of_lt hk
  have hbc := hK k hk'
  refine ⟨7, ?_⟩
  have hA : play 7 (CIMCIC k) EBot = some .D := by
    simpa using CIMCIC_plays_D_against_EBot k 5
  have hB : play 7 EBot (CIMCIC k) = some .C := by
    simpa using EBot_plays_C_against_CIMCIC k 2 hbc
  exact outcome_of_plays _ _ _ _ _ hA hB

end PD.Theorems
