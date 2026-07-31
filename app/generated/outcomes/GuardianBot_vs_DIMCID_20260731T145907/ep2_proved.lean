import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Base.ValuationSoundness
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.Bots.LlmGenerations.GuardianBot
import PrisonersDilemma.Bots.LlmGenerations.DIMCID
import PrisonersDilemma.Bots.CooperateBot

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

/-! ## GuardianBot's side: guard "DIMCID plays D vs bot CB" is false → Guardian trusts DIMCID -/

theorem gd_botCB_D_not_provable (k m : Nat) :
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

theorem gd_dimcid_botCB_guard_not_provable (k : Nat) :
    ¬ Pf k (.impl (.plays (DIMCID k) (.bot CooperateBot) Action.C)
                  (.plays (.bot CooperateBot) (DIMCID k) Action.D)) := by
  intro h
  refine no_provable_tailTo_unreadable (.bot CooperateBot) (DIMCID k) Action.D
    (fun n hA => gd_botCB_D_not_provable k n (.atom hA))
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

theorem gd_proofSearch_false_dimcid_botCB (k : Nat) :
    proofSearch k
      ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.D)).subst
        (DIMCID k) (.bot CooperateBot)) = false := by
  cases hps : proofSearch k
      ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.D)).subst
        (DIMCID k) (.bot CooperateBot)) with
  | false => rfl
  | true =>
      exact absurd ((proofSearch_spec k _).1 hps) (gd_dimcid_botCB_guard_not_provable k)

theorem gd_DIMCID_plays_C_vs_botCB (k fuel : Nat) :
    play (fuel + 2) (DIMCID k) (.bot CooperateBot) = some .C := by
  show (if proofSearch k
            ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.D)).subst
              (DIMCID k) (.bot CooperateBot))
          then eval (fuel + 1) (DIMCID k) (.bot CooperateBot) (.const Action.D)
          else eval (fuel + 1) (DIMCID k) (.bot CooperateBot) (.const Action.C))
        = some Action.C
  rw [gd_proofSearch_false_dimcid_botCB k]; simp [eval]

theorem gd_guardian_guard_false_vs_DIMCID (k : Nat) :
    proofSearch k (.plays (DIMCID k) (.bot CooperateBot) .D) = false := by
  cases hps : proofSearch k (.plays (DIMCID k) (.bot CooperateBot) .D) with
  | true  =>
      exfalso
      obtain ⟨n, hn⟩ := proofSearch_sound _ _ hps
      have hC : play (n + 2) (DIMCID k) (.bot CooperateBot) = some .C :=
        gd_DIMCID_plays_C_vs_botCB k n
      have hD : play (n + 2) (DIMCID k) (.bot CooperateBot) = some .D :=
        eval_mono_le hn (n + 2) (by omega)
      rw [hC] at hD; simp at hD
  | false => rfl

theorem gd_GuardianBot_cooperates_vs_DIMCID (k fuel : Nat) :
    play (fuel + 2) (GuardianBot k) (DIMCID k) = some .C := by
  have hg := gd_guardian_guard_false_vs_DIMCID k
  show eval (fuel + 2) (GuardianBot k) (DIMCID k) (GuardianBot k) = some .C
  unfold GuardianBot
  simp [eval, Prog.subst, Formula.subst, hg]

theorem gd_Guardian_plays_D_vs_DIMCID_false (k : Nat) :
    ¬ (Formula.plays (GuardianBot k) (DIMCID k) Action.D).interp := by
  rintro ⟨n, hn⟩
  have hC : play (n + 2) (GuardianBot k) (DIMCID k) = some .C :=
    gd_GuardianBot_cooperates_vs_DIMCID k n
  have hD : play (n + 2) (GuardianBot k) (DIMCID k) = some .D :=
    eval_mono_le hn (n + 2) (by omega)
  rw [hC] at hD; simp at hD

/-! ## DIMCID's side: guard is WV-false → DIMCID cooperates -/

theorem gd_no_opp_image {x me o : Prog}
    (hme : (∃ p₂ q₂, me = .sim p₂ q₂) ∨ (∃ p₂ q₂, me = .bot (.sim p₂ q₂)))
    (ho : o ≠ .opp) (h : x.subst me o = Prog.opp) : False := by
  cases x with
  | const a => simp [Prog.subst] at h
  | self => rcases hme with ⟨_,_,rfl⟩ | ⟨_,_,rfl⟩ <;> simp [Prog.subst] at h
  | opp => simp only [Prog.subst] at h; exact ho h
  | bot p => simp [Prog.subst] at h
  | sim p q => simp [Prog.subst] at h
  | ite b a p q => simp [Prog.subst] at h
  | search K g p q => simp [Prog.subst] at h

theorem gd_no_self_image {x me o : Prog}
    (hme : (∃ p₂ q₂, me = .sim p₂ q₂) ∨ (∃ p₂ q₂, me = .bot (.sim p₂ q₂)))
    (ho : o ≠ .self) (h : x.subst me o = Prog.self) : False := by
  cases x with
  | const a => simp [Prog.subst] at h
  | self => rcases hme with ⟨_,_,rfl⟩ | ⟨_,_,rfl⟩ <;> simp [Prog.subst] at h
  | opp => simp only [Prog.subst] at h; exact ho h
  | bot p => simp [Prog.subst] at h
  | sim p q => simp [Prog.subst] at h
  | ite b a p q => simp [Prog.subst] at h
  | search K g p q => simp [Prog.subst] at h

theorem gd_subst_dimcid_forces {k : Nat} {p me o : Prog}
    (hme : (∃ p₂ q₂, me = .sim p₂ q₂) ∨ (∃ p₂ q₂, me = .bot (.sim p₂ q₂)))
    (h : p.subst me o = DIMCID k) : o = DIMCID k := by
  cases p with
  | const a => simp [Prog.subst, DIMCID] at h
  | self => rcases hme with ⟨_,_,rfl⟩ | ⟨_,_,rfl⟩ <;> simp [Prog.subst, DIMCID] at h
  | opp => simpa [Prog.subst] using h
  | bot pp => simp [Prog.subst, DIMCID] at h
  | sim pp qq => simp [Prog.subst, DIMCID] at h
  | ite b a pp qq => simp [Prog.subst, DIMCID] at h
  | search K g pp qq =>
      exfalso
      simp only [DIMCID, Prog.subst, Prog.search.injEq] at h
      obtain ⟨hK, hg, hp, hq⟩ := h
      cases g with
      | plays a b c => simp [Formula.subst] at hg
      | neg f => simp [Formula.subst] at hg
      | box n f => simp [Formula.subst] at hg
      | eq a b => simp [Formula.subst] at hg
      | diag gg f => simp [Formula.subst] at hg
      | impl f1 f2 =>
          simp only [Formula.subst, Formula.impl.injEq] at hg
          obtain ⟨hf1, hf2⟩ := hg
          cases f1 with
          | impl _ _ => simp [Formula.subst] at hf1
          | neg _ => simp [Formula.subst] at hf1
          | box _ _ => simp [Formula.subst] at hf1
          | eq _ _ => simp [Formula.subst] at hf1
          | diag _ _ => simp [Formula.subst] at hf1
          | plays x y a =>
              simp only [Formula.subst, Formula.plays.injEq] at hf1
              obtain ⟨hx, hy, -⟩ := hf1
              by_cases hoself : o = Prog.self
              · subst hoself; exact gd_no_opp_image hme (by simp) hy
              · exact gd_no_self_image hme hoself hx

theorem gd_subst_ne_guardian {k : Nat} {q me o : Prog}
    (hme : (∃ p₂ q₂, me = .sim p₂ q₂) ∨ (∃ p₂ q₂, me = .bot (.sim p₂ q₂)))
    (ho : o ≠ .opp) (hoG : o ≠ GuardianBot k) (h : q.subst me o = GuardianBot k) : False := by
  cases q with
  | const a => simp [Prog.subst, GuardianBot] at h
  | self => rcases hme with ⟨_,_,rfl⟩ | ⟨_,_,rfl⟩ <;> simp [Prog.subst, GuardianBot] at h
  | opp => simp only [Prog.subst] at h; exact hoG h
  | bot pp => simp [Prog.subst, GuardianBot] at h
  | sim pp qq => simp [Prog.subst, GuardianBot] at h
  | ite b a pp qq => simp [Prog.subst, GuardianBot] at h
  | search K g pp qq =>
      simp only [GuardianBot, Prog.subst, Prog.search.injEq] at h
      obtain ⟨hK, hg, hp, hq⟩ := h
      cases g with
      | impl _ _ => simp [Formula.subst] at hg
      | neg f => simp [Formula.subst] at hg
      | box n f => simp [Formula.subst] at hg
      | eq a b => simp [Formula.subst] at hg
      | diag gg f => simp [Formula.subst] at hg
      | plays x y a =>
          simp only [Formula.subst, Formula.plays.injEq] at hg
          obtain ⟨hx, hy, -⟩ := hg
          exact gd_no_opp_image hme ho hx

theorem gd_simS_impossible {k : Nat} {p q me o : Prog}
    (hme : (∃ p₂ q₂, me = .sim p₂ q₂) ∨ (∃ p₂ q₂, me = .bot (.sim p₂ q₂)))
    (hp : p.subst me o = DIMCID k) (hq : q.subst me o = GuardianBot k) : False := by
  have hoD : o = DIMCID k := gd_subst_dimcid_forces hme hp
  have hoopp : o ≠ Prog.opp := by rw [hoD]; simp [DIMCID]
  have hoG : o ≠ GuardianBot k := by rw [hoD]; simp [DIMCID, GuardianBot]
  exact gd_subst_ne_guardian hme hoopp hoG hq

def gdS (k : Nat) : Prog → Prog → Prop :=
  fun p q => p = DIMCID k ∧ q = GuardianBot k

theorem gd_pf_WV (k : Nat) : ∀ {K : Nat} {φ : Formula},
    Pf K φ → WV (gdS k) φ := by
  intro K φ h
  refine ((wv_sound_upto (gdS k) (fun _ _ => False)
    ?nb ?const ?opp ?ite ?botbot ?botsearch ?sim_inv ?botsim_inv ?search_t ?search_f
    ?simS ?botsimS K).2 K φ h).2 Pf_sound
  case nb =>
    rintro oppo z ⟨h1, h2⟩; simp [GuardianBot] at h2
  case const =>
    rintro me oppo a (⟨h1, h2⟩ | hF) hgate
    · subst h1; rcases hgate with hb | hb <;> simp [DIMCID] at hb
    · exact hF.elim
  case opp =>
    rintro me oppo (⟨h1, h2⟩ | hF) hgate
    · subst h1; rcases hgate with hb | hb <;> simp [DIMCID] at hb
    · exact hF.elim
  case ite =>
    rintro me oppo b a' p q (⟨h1, h2⟩ | hF) hgate
    · subst h1; rcases hgate with hb | hb <;> simp [DIMCID] at hb
    · exact hF.elim
  case botbot =>
    rintro me oppo p (⟨h1, h2⟩ | hF) hb
    · subst h1; simp [DIMCID] at hb
    · exact hF.elim
  case botsearch =>
    rintro me oppo g ψ P Q (⟨h1, h2⟩ | hF) hb
    · subst h1; simp [DIMCID] at hb
    · exact hF.elim
  case sim_inv =>
    rintro p q oppo (⟨h1, h2⟩ | hF)
    · simp [DIMCID] at h1
    · exact hF.elim
  case botsim_inv =>
    rintro p q oppo (⟨h1, h2⟩ | hF)
    · simp [DIMCID] at h1
    · exact hF.elim
  case search_t =>
    rintro oppo g ψ P Q a n (⟨hp, hq⟩ | hF) hWV hcert
    · exfalso
      subst hq
      unfold DIMCID at hp
      injection hp with h1 h2 h3 h4
      subst h1; subst h2; subst h3; subst h4
      rw [show Prog.search g
            ((Formula.plays Prog.self Prog.opp Action.C).impl (.plays Prog.opp Prog.self Action.D))
            (.const Action.D) (.const Action.C) = DIMCID g from rfl] at hWV
      have hred : ((Formula.plays .self .opp Action.C).impl
                  (.plays .opp .self Action.D)).subst (DIMCID g) (GuardianBot g)
          = .impl (.plays (DIMCID g) (GuardianBot g) Action.C)
                  (.plays (GuardianBot g) (DIMCID g) Action.D) := by
        simp [Formula.subst, Prog.subst, DIMCID]
      rw [hred, WV_impl] at hWV
      have hante : WV (gdS g) (.plays (DIMCID g) (GuardianBot g) Action.C) := by
        rw [WV_plays]; exact Or.inl ⟨rfl, ⟨rfl, rfl⟩⟩
      have hcons := hWV hante
      rw [WV_plays] at hcons
      rcases hcons with ⟨hCeqD, _⟩ | hint
      · exact Action.noConfusion hCeqD
      · exact gd_Guardian_plays_D_vs_DIMCID_false g hint
    · exact hF.elim
  case search_f =>
    rintro oppo g ψ P Q a n (⟨hp, hq⟩ | hF) hcert
    · unfold DIMCID at hp
      injection hp with h1 h2 h3 h4
      subst h4
      cases hcert
      rfl
    · exact hF.elim
  case simS =>
    rintro p q oppo ⟨hp, hq⟩
    exact (gd_simS_impossible (Or.inl ⟨p, q, rfl⟩) hp hq).elim
  case botsimS =>
    rintro p q oppo ⟨hp, hq⟩
    exact (gd_simS_impossible (Or.inr ⟨p, q, rfl⟩) hp hq).elim

theorem gd_dimcid_guard_not_provable (k : Nat) :
    ¬ Pf k (.impl (.plays (DIMCID k) (GuardianBot k) Action.C)
                  (.plays (GuardianBot k) (DIMCID k) Action.D)) := by
  intro h
  have hWV := gd_pf_WV k h
  rw [WV_impl] at hWV
  have hante : WV (gdS k) (.plays (DIMCID k) (GuardianBot k) Action.C) := by
    rw [WV_plays]; exact Or.inl ⟨rfl, ⟨rfl, rfl⟩⟩
  have hcons := hWV hante
  rw [WV_plays] at hcons
  rcases hcons with ⟨hCeqD, _⟩ | hint
  · exact Action.noConfusion hCeqD
  · exact gd_Guardian_plays_D_vs_DIMCID_false k hint

theorem gd_proofSearch_false_dimcid_guard (k : Nat) :
    proofSearch k
      ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.D)).subst
        (DIMCID k) (GuardianBot k)) = false := by
  cases hps : proofSearch k
      ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.D)).subst
        (DIMCID k) (GuardianBot k)) with
  | false => rfl
  | true =>
      exact absurd ((proofSearch_spec k _).1 hps) (gd_dimcid_guard_not_provable k)

theorem gd_DIMCID_plays_C_vs_GuardianBot (k fuel : Nat) :
    play (fuel + 2) (DIMCID k) (GuardianBot k) = some .C := by
  show (if proofSearch k
            ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.D)).subst
              (DIMCID k) (GuardianBot k))
          then eval (fuel + 1) (DIMCID k) (GuardianBot k) (.const Action.D)
          else eval (fuel + 1) (DIMCID k) (GuardianBot k) (.const Action.C))
        = some Action.C
  rw [gd_proofSearch_false_dimcid_guard k]; simp [eval]

/-- **GuardianBot vs DIMCID → (C, C)** for all sufficiently large `k`. -/
theorem llm_outcome_GuardianBot_vs_DIMCID :
    ∃ k₂, ∀ k, k₂ < k →
      ∃ fuel, outcome fuel (GuardianBot k) (DIMCID k) = some (.C, .C) := by
  refine ⟨0, fun k _ => ⟨2, ?_⟩⟩
  have hA : play 2 (GuardianBot k) (DIMCID k) = some .C :=
    gd_GuardianBot_cooperates_vs_DIMCID k 0
  have hB : play 2 (DIMCID k) (GuardianBot k) = some .C :=
    gd_DIMCID_plays_C_vs_GuardianBot k 0
  exact outcome_of_plays _ _ _ _ _ hA hB

end PD.Theorems
