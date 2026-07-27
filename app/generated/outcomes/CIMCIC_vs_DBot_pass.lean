import PrisonersDilemma.Bots.LlmGenerations.CIMCIC
import PrisonersDilemma.Bots.DBot
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Theorems.DefectBot
import PrisonersDilemma.Theorems.Helpers
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

def CimcicBotForbiddenC (k : Nat) : Formula → Prop
  | .plays p q a => p = .bot DefectBot ∧ q = CIMCIC k ∧ a = Action.C
  | .impl _ ψ    => CimcicBotForbiddenC k ψ
  | _            => False

theorem cimcic_bot_no_provable_forbidden (k : Nat) :
    ∀ {m : Nat} {φ : Formula}, Pf m φ → ¬ CimcicBotForbiddenC k φ := by
  intro m φ h
  induction h using Pf.induct with
  | atom k' φ' hatom =>
      intro hF
      cases hatom with
      | mk cert hle =>
          simp only [CimcicBotForbiddenC] at hF
          obtain ⟨hp, hq, ha⟩ := hF
          subst hp; subst hq; subst ha
          exact cimcic_botDefect_consequent_not_provable k _ (Pf.atom (.mk cert hle))
  | searchBranch k' g ψ a b me opponent hme hle =>
      intro hF; subst hme; simp only [CimcicBotForbiddenC] at hF
      obtain ⟨hm, _, _⟩ := hF; simp [DefectBot] at hm
  | simStep k' me p q opponent a hme hle =>
      intro hF; subst hme; simp only [CimcicBotForbiddenC] at hF
      obtain ⟨hm, _, _⟩ := hF; simp [DefectBot] at hm
  | botSimStep k' me p q opponent a hme hle =>
      intro hF; subst hme; simp only [CimcicBotForbiddenC] at hF
      obtain ⟨hm, _, _⟩ := hF; simp [DefectBot] at hm
  | botSearchStep k' g ψ a b me opponent hme hle =>
      intro hF; subst hme; simp only [CimcicBotForbiddenC] at hF
      obtain ⟨hm, _, _⟩ := hF; simp [DefectBot] at hm
  | iteBranchSearch_t k' g z a' c0 c1 ψ q me opponent hme hle =>
      intro hF; subst hme; simp only [CimcicBotForbiddenC] at hF
      obtain ⟨hm, _, _⟩ := hF; simp [DefectBot] at hm
  | searchThenSearch_t k' k₁ k₂ m' ψ₁ ψ₂ c0 c1 q me opponent hme hprud hmk hle _ih =>
      intro hF; subst hme; simp only [CimcicBotForbiddenC] at hF
      obtain ⟨hm, _, _⟩ := hF; simp [DefectBot] at hm
  | mp k' m₁ m₂ φ' α h1 h2 hle ih1 _ih2 => intro hF; exact ih1 hF
  | implTrans k' φ' ψ χ a b h1 h2 hle _ih1 ih2 => intro hF; exact ih2 hF
  | weakenImpl k' φ' ψ m' hψ hle ih => intro hF; exact ih hF
  | impS2 φ' ψ χ m₁ m₂ K h1 h2 hle ih1 _ih2 => intro hF; exact ih1 hF
  | diagF pm fb g K tgt hgate hle ih => intro hF; exact ih hF
  | eqRefl k' p hle => intro hF; simp only [CimcicBotForbiddenC] at hF
  | eqNeg k' p q hne hle => intro hF; simp only [CimcicBotForbiddenC] at hF
  | atomNeg k' p q b aN m' hatom hne hle => intro hF; simp only [CimcicBotForbiddenC] at hF
  | atomBoxImpl k' kBox p q a hatom hle => intro hF; simp only [CimcicBotForbiddenC] at hF
  | boxIntro kIn K φ' hprem hle _ih => intro hF; simp only [CimcicBotForbiddenC] at hF
  | axK a b c m' K φ' α hprem hgate hle _ih => intro hF; simp only [CimcicBotForbiddenC] at hF
  | box4 a b K φ' hgate hsz => intro hF; simp only [CimcicBotForbiddenC] at hF
  | diagB pm fb g K tgt hgate hle _ih => intro hF; simp only [CimcicBotForbiddenC] at hF
  | axKf a b c K φ' α hgate hsz => intro hF; simp only [CimcicBotForbiddenC] at hF
  | boxMono a b K φ' hab hsz => intro hF; simp only [CimcicBotForbiddenC] at hF

theorem cimcic_botDefect_guard_not_provable (k : Nat) :
    ¬ Pf k (cimcic_guard_botDefect k) := by
  intro h
  refine cimcic_bot_no_provable_forbidden k h ?_
  show CimcicBotForbiddenC k (cimcic_guard_botDefect k)
  unfold cimcic_guard_botDefect CimcicBotForbiddenC CimcicBotForbiddenC
  exact ⟨rfl, rfl, rfl⟩

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

def DBotForbiddenC (k : Nat) : Formula → Prop
  | .plays p q a => p = DBot ∧ q = CIMCIC k ∧ a = Action.C
  | .impl _ ψ    => DBotForbiddenC k ψ
  | _            => False

theorem dbot_no_provable_forbidden (k : Nat) :
    ∀ {m : Nat} {φ : Formula}, Pf m φ → ¬ DBotForbiddenC k φ := by
  intro m φ h
  induction h using Pf.induct with
  | atom k' φ' hatom =>
      intro hF
      cases hatom with
      | mk cert hle =>
          simp only [DBotForbiddenC] at hF
          obtain ⟨hp, hq, ha⟩ := hF
          subst hp; subst hq; subst ha
          exact dbot_C_cert_impossible k _ cert
  | searchBranch k' g ψ a b me opponent hme hle =>
      intro hF; subst hme; simp only [DBotForbiddenC] at hF
      obtain ⟨hm, _, _⟩ := hF; simp [DBot] at hm
  | simStep k' me p q opponent a hme hle =>
      intro hF; subst hme; simp only [DBotForbiddenC] at hF
      obtain ⟨hm, _, _⟩ := hF; simp [DBot] at hm
  | botSimStep k' me p q opponent a hme hle =>
      intro hF; subst hme; simp only [DBotForbiddenC] at hF
      obtain ⟨hm, _, _⟩ := hF; simp [DBot] at hm
  | botSearchStep k' g ψ a b me opponent hme hle =>
      intro hF; subst hme; simp only [DBotForbiddenC] at hF
      obtain ⟨hm, _, _⟩ := hF; simp [DBot] at hm
  | iteBranchSearch_t k' g z a' c0 c1 ψ q me opponent hme hle =>
      intro hF; subst hme; simp only [DBotForbiddenC] at hF
      obtain ⟨hm, _, _⟩ := hF; simp [DBot] at hm
  | searchThenSearch_t k' k₁ k₂ m' ψ₁ ψ₂ c0 c1 q me opponent hme hprud hmk hle _ih =>
      intro hF; subst hme; simp only [DBotForbiddenC] at hF
      obtain ⟨hm, _, _⟩ := hF; simp [DBot] at hm
  | mp k' m₁ m₂ φ' α h1 h2 hle ih1 _ih2 => intro hF; exact ih1 hF
  | implTrans k' φ' ψ χ a b h1 h2 hle _ih1 ih2 => intro hF; exact ih2 hF
  | weakenImpl k' φ' ψ m' hψ hle ih => intro hF; exact ih hF
  | impS2 φ' ψ χ m₁ m₂ K h1 h2 hle ih1 _ih2 => intro hF; exact ih1 hF
  | diagF pm fb g K tgt hgate hle ih => intro hF; exact ih hF
  | eqRefl k' p hle => intro hF; simp only [DBotForbiddenC] at hF
  | eqNeg k' p q hne hle => intro hF; simp only [DBotForbiddenC] at hF
  | atomNeg k' p q b aN m' hatom hne hle => intro hF; simp only [DBotForbiddenC] at hF
  | atomBoxImpl k' kBox p q a hatom hle => intro hF; simp only [DBotForbiddenC] at hF
  | boxIntro kIn K φ' hprem hle _ih => intro hF; simp only [DBotForbiddenC] at hF
  | axK a b c m' K φ' α hprem hgate hle _ih => intro hF; simp only [DBotForbiddenC] at hF
  | box4 a b K φ' hgate hsz => intro hF; simp only [DBotForbiddenC] at hF
  | diagB pm fb g K tgt hgate hle _ih => intro hF; simp only [DBotForbiddenC] at hF
  | axKf a b c K φ' α hgate hsz => intro hF; simp only [DBotForbiddenC] at hF
  | boxMono a b K φ' hab hsz => intro hF; simp only [DBotForbiddenC] at hF

abbrev cimcic_guard_DBot (k : Nat) : Formula :=
  .impl (.plays (CIMCIC k) DBot Action.C) (.plays DBot (CIMCIC k) Action.C)

theorem cimcic_DBot_guard_not_provable (k : Nat) :
    ¬ Pf k (cimcic_guard_DBot k) := by
  intro h
  refine dbot_no_provable_forbidden k h ?_
  show DBotForbiddenC k (cimcic_guard_DBot k)
  unfold cimcic_guard_DBot DBotForbiddenC DBotForbiddenC
  exact ⟨rfl, rfl, rfl⟩

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
