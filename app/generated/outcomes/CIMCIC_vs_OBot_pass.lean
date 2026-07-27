import PrisonersDilemma.Bots.LlmGenerations.CIMCIC
import PrisonersDilemma.Bots.OBot
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Theorems.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Base.Asymptotics

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

/-! # CIMCIC vs OBot — the honest `(D, D)` outcome.

CIMCIC's first probe target `.bot CooperateBot` has a TRUE consequent, so CIMCIC cooperates
against it; its second probe target `.bot DefectBot` has a FALSE consequent, so CIMCIC
defects against it. OBot therefore descends past its first `ite` guard and defects on the
second. Since OBot defects vs CIMCIC, CIMCIC's own guard consequent ("OBot plays C vs
CIMCIC") is FALSE and structurally unprovable, so CIMCIC also defects. Result: `(D, D)`. -/

-- ── CIMCIC vs .bot CooperateBot: cooperate (true consequent) ──

theorem CIMCIC_consequent_bot_CooperateBot (k : Nat) :
    Pf 2 (Formula.plays (.bot CooperateBot) (CIMCIC k) Action.C) :=
  Pf.atom ⟨PlaysProof.bot PlaysProof.const, by simp [c_leaf, c_node]⟩

theorem proofSearch_true_for_CIMCIC_vs_bot_CooperateBot :
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
  refine Pf.weakenImpl _ _ 2 (CIMCIC_consequent_bot_CooperateBot k) ?_
  have hb := hK k hk
  simp only [numCost, Formula.size, Prog.size, CIMCIC, CooperateBot]
  omega

theorem CIMCIC_plays_C_against_bot_CooperateBot (k fuel : Nat)
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

-- ── CIMCIC vs .bot DefectBot: defect (false consequent, unprovable guard) ──

theorem cimcic_bot_DefectBot_consequent_not_provable (k m : Nat) :
    ¬ Pf m (.plays (.bot DefectBot) (CIMCIC k) Action.C) := by
  intro h
  obtain ⟨n, hn⟩ := Pf_sound m _ h
  have : play n (.bot DefectBot) (CIMCIC k) = some Action.D ∨
         play n (.bot DefectBot) (CIMCIC k) = none := by
    cases n with
    | zero => right; rfl
    | succ n =>
      cases n with
      | zero => right; rfl
      | succ n => left; simp [play, eval, DefectBot]
  rcases this with hD | hNone
  · rw [hD] at hn; exact absurd hn (by decide)
  · rw [hNone] at hn; exact absurd hn (by decide)

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
          exact cimcic_bot_DefectBot_consequent_not_provable k _ (Pf.atom (.mk cert hle))
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

abbrev cimcic_bot_guard (k : Nat) : Formula :=
  .impl (.plays (CIMCIC k) (.bot DefectBot) Action.C)
        (.plays (.bot DefectBot) (CIMCIC k) Action.C)

theorem cimcic_bot_guard_not_provable (k : Nat) : ¬ Pf k (cimcic_bot_guard k) := by
  intro h
  refine cimcic_bot_no_provable_forbidden k h ?_
  show CimcicBotForbiddenC k (cimcic_bot_guard k)
  unfold cimcic_bot_guard CimcicBotForbiddenC CimcicBotForbiddenC
  exact ⟨rfl, rfl, rfl⟩

theorem proofSearch_false_for_CIMCIC_vs_bot_DefectBot (k : Nat) :
    proofSearch k
      ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.C)).subst
        (CIMCIC k) (.bot DefectBot)) = false := by
  show proofSearch k (cimcic_bot_guard k) = false
  cases hps : proofSearch k (cimcic_bot_guard k) with
  | false => rfl
  | true =>
      exact absurd ((proofSearch_spec k (cimcic_bot_guard k)).1 hps)
        (cimcic_bot_guard_not_provable k)

theorem CIMCIC_plays_D_against_bot_DefectBot (k fuel : Nat) :
    play (fuel + 2) (CIMCIC k) (.bot DefectBot) = some .D := by
  show (if proofSearch k
            ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.C)).subst
              (CIMCIC k) (.bot DefectBot))
          then eval (fuel + 1) (CIMCIC k) (.bot DefectBot) (.const Action.C)
          else eval (fuel + 1) (CIMCIC k) (.bot DefectBot) (.const Action.D)) = some .D
  rw [proofSearch_false_for_CIMCIC_vs_bot_DefectBot k]; simp [eval]

-- ── OBot defects against CIMCIC ──

theorem OBot_plays_D_against_CIMCIC (k fuel : Nat)
    (hC : ∀ f, play (f + 2) (CIMCIC k) (.bot CooperateBot) = some .C) :
    play (fuel + 5) OBot (CIMCIC k) = some .D := by
  have hGuard1 :
      eval (fuel + 4) OBot (CIMCIC k) (.sim .opp (.bot CooperateBot)) = some .C := by
    have hProbe : play (fuel + 3) (CIMCIC k) (.bot CooperateBot) = some .C := by
      simpa [Nat.add_assoc] using hC (fuel + 1)
    simpa [Nat.add_assoc] using
      (eval_sim_opp_bot_of_play (fuel + 3) OBot (CIMCIC k) CooperateBot Action.C hProbe)
  have hGuard2 :
      eval (fuel + 3) OBot (CIMCIC k) (.sim .opp (.bot DefectBot)) = some .D := by
    have hProbe : play (fuel + 2) (CIMCIC k) (.bot DefectBot) = some .D :=
      CIMCIC_plays_D_against_bot_DefectBot k fuel
    simpa [Nat.add_assoc] using
      (eval_sim_opp_bot_of_play (fuel + 2) OBot (CIMCIC k) DefectBot Action.D hProbe)
  have hPlay := play_ite_from_guard
    fuel 4 OBot (CIMCIC k) (.sim .opp (.bot CooperateBot))
    (.ite (.sim .opp (.bot DefectBot)) Action.C (.const Action.C) (.const Action.D))
    (.const Action.D)
    Action.C Action.C
    (by rfl) hGuard1
  have hInner :
      eval (fuel + 4) OBot (CIMCIC k)
        (.ite (.sim .opp (.bot DefectBot)) Action.C (.const Action.C) (.const Action.D)) =
          some .D := by
    simpa [Nat.add_assoc] using
      (eval_ite_from_guard (fuel + 3) OBot (CIMCIC k)
        (.sim .opp (.bot DefectBot)) (.const Action.C) (.const Action.D)
        Action.C Action.D hGuard2)
  simpa [hInner] using hPlay

-- ── CIMCIC defects against OBot (false consequent) ──

theorem interp_OBot_plays_C_false (k : Nat)
    (hOBotD : ∀ fuel, play (fuel + 5) OBot (CIMCIC k) = some .D) :
    ¬ (Formula.plays OBot (CIMCIC k) .C).interp := by
  rintro ⟨n, hn⟩
  have h1 : play (n + 5) OBot (CIMCIC k) = some .C := by
    have := eval_mono_le (show eval n OBot (CIMCIC k) OBot = some .C from hn) (n + 5) (by omega)
    simpa [play] using this
  have h2 : play (n + 5) OBot (CIMCIC k) = some .D := hOBotD n
  rw [h1] at h2
  exact absurd h2 (by decide)

def CimcicObotForbiddenC (k : Nat) : Formula → Prop
  | .plays p q a => p = OBot ∧ q = CIMCIC k ∧ a = Action.C
  | .impl _ ψ    => CimcicObotForbiddenC k ψ
  | _            => False

theorem cimcic_obot_no_provable_forbidden (k : Nat)
    (hcons : ∀ m, ¬ Pf m (.plays OBot (CIMCIC k) Action.C)) :
    ∀ {m : Nat} {φ : Formula}, Pf m φ → ¬ CimcicObotForbiddenC k φ := by
  intro m φ h
  induction h using Pf.induct with
  | atom k' φ' hatom =>
      intro hF
      cases hatom with
      | mk cert hle =>
          simp only [CimcicObotForbiddenC] at hF
          obtain ⟨hp, hq, ha⟩ := hF
          subst hp; subst hq; subst ha
          exact hcons _ (Pf.atom (.mk cert hle))
  | searchBranch k' g ψ a b me opponent hme hle =>
      intro hF; subst hme; simp only [CimcicObotForbiddenC] at hF
      obtain ⟨hm, _, _⟩ := hF; simp [OBot] at hm
  | simStep k' me p q opponent a hme hle =>
      intro hF; subst hme; simp only [CimcicObotForbiddenC] at hF
      obtain ⟨hm, _, _⟩ := hF; simp [OBot] at hm
  | botSimStep k' me p q opponent a hme hle =>
      intro hF; subst hme; simp only [CimcicObotForbiddenC] at hF
      obtain ⟨hm, _, _⟩ := hF; simp [OBot] at hm
  | botSearchStep k' g ψ a b me opponent hme hle =>
      intro hF; subst hme; simp only [CimcicObotForbiddenC] at hF
      obtain ⟨hm, _, _⟩ := hF; simp [OBot] at hm
  | iteBranchSearch_t k' g z a' c0 c1 ψ q me opponent hme hle =>
      intro hF; subst hme; simp only [CimcicObotForbiddenC] at hF
      obtain ⟨hm, _, _⟩ := hF; simp [OBot] at hm
  | searchThenSearch_t k' k₁ k₂ m' ψ₁ ψ₂ c0 c1 q me opponent hme hprud hmk hle _ih =>
      intro hF; subst hme; simp only [CimcicObotForbiddenC] at hF
      obtain ⟨hm, _, _⟩ := hF; simp [OBot] at hm
  | mp k' m₁ m₂ φ' α h1 h2 hle ih1 _ih2 => intro hF; exact ih1 hF
  | implTrans k' φ' ψ χ a b h1 h2 hle _ih1 ih2 => intro hF; exact ih2 hF
  | weakenImpl k' φ' ψ m' hψ hle ih => intro hF; exact ih hF
  | impS2 φ' ψ χ m₁ m₂ K h1 h2 hle ih1 _ih2 => intro hF; exact ih1 hF
  | diagF pm fb g K tgt hgate hle ih => intro hF; exact ih hF
  | eqRefl k' p hle => intro hF; simp only [CimcicObotForbiddenC] at hF
  | eqNeg k' p q hne hle => intro hF; simp only [CimcicObotForbiddenC] at hF
  | atomNeg k' p q b aN m' hatom hne hle => intro hF; simp only [CimcicObotForbiddenC] at hF
  | atomBoxImpl k' kBox p q a hatom hle => intro hF; simp only [CimcicObotForbiddenC] at hF
  | boxIntro kIn K φ' hprem hle _ih => intro hF; simp only [CimcicObotForbiddenC] at hF
  | axK a b c m' K φ' α hprem hgate hle _ih => intro hF; simp only [CimcicObotForbiddenC] at hF
  | box4 a b K φ' hgate hsz => intro hF; simp only [CimcicObotForbiddenC] at hF
  | diagB pm fb g K tgt hgate hle _ih => intro hF; simp only [CimcicObotForbiddenC] at hF
  | axKf a b c K φ' α hgate hsz => intro hF; simp only [CimcicObotForbiddenC] at hF
  | boxMono a b K φ' hab hsz => intro hF; simp only [CimcicObotForbiddenC] at hF

abbrev cimcic_obot_guard (k : Nat) : Formula :=
  .impl (.plays (CIMCIC k) OBot Action.C) (.plays OBot (CIMCIC k) Action.C)

theorem cimcic_obot_guard_not_provable (k : Nat)
    (hcons : ∀ m, ¬ Pf m (.plays OBot (CIMCIC k) Action.C)) :
    ¬ Pf k (cimcic_obot_guard k) := by
  intro h
  refine cimcic_obot_no_provable_forbidden k hcons h ?_
  show CimcicObotForbiddenC k (cimcic_obot_guard k)
  unfold cimcic_obot_guard CimcicObotForbiddenC CimcicObotForbiddenC
  exact ⟨rfl, rfl, rfl⟩

theorem proofSearch_false_for_CIMCIC_vs_OBot (k : Nat)
    (hcons : ∀ m, ¬ Pf m (.plays OBot (CIMCIC k) Action.C)) :
    proofSearch k
      ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.C)).subst
        (CIMCIC k) OBot) = false := by
  show proofSearch k (cimcic_obot_guard k) = false
  cases hps : proofSearch k (cimcic_obot_guard k) with
  | false => rfl
  | true =>
      exact absurd ((proofSearch_spec k (cimcic_obot_guard k)).1 hps)
        (cimcic_obot_guard_not_provable k hcons)

theorem CIMCIC_plays_D_against_OBot (k fuel : Nat)
    (hcons : ∀ m, ¬ Pf m (.plays OBot (CIMCIC k) Action.C)) :
    play (fuel + 2) (CIMCIC k) OBot = some .D := by
  show (if proofSearch k
            ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.C)).subst
              (CIMCIC k) OBot)
          then eval (fuel + 1) (CIMCIC k) OBot (.const Action.C)
          else eval (fuel + 1) (CIMCIC k) OBot (.const Action.D)) = some .D
  rw [proofSearch_false_for_CIMCIC_vs_OBot k hcons]; simp [eval]

-- ── The final outcome ──

theorem llm_outcome_CIMCIC_vs_OBot :
    ∃ k₂, ∀ k, k₂ < k →
      ∃ fuel, outcome fuel (CIMCIC k) OBot = some (.D, .D) := by
  obtain ⟨K, hK⟩ := proofSearch_true_for_CIMCIC_vs_bot_CooperateBot
  refine ⟨K, fun k hk => ?_⟩
  have hkK : k ≥ K := Nat.le_of_lt hk
  have hpsC := hK k hkK
  have hC : ∀ f, play (f + 2) (CIMCIC k) (.bot CooperateBot) = some .C :=
    fun f => CIMCIC_plays_C_against_bot_CooperateBot k f hpsC
  have hOBotD : ∀ fuel, play (fuel + 5) OBot (CIMCIC k) = some .D :=
    fun fuel => OBot_plays_D_against_CIMCIC k fuel hC
  have hcons : ∀ m, ¬ Pf m (.plays OBot (CIMCIC k) Action.C) := by
    intro m h
    exact interp_OBot_plays_C_false k hOBotD (Pf_sound m _ h)
  refine ⟨5, ?_⟩
  have hA : play 5 (CIMCIC k) OBot = some .D := by
    simpa using CIMCIC_plays_D_against_OBot k 3 hcons
  have hB : play 5 OBot (CIMCIC k) = some .D := by
    simpa using hOBotD 0
  exact outcome_of_plays _ _ _ _ _ hA hB

end PD.Theorems
