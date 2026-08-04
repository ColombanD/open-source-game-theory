import PrisonersDilemma.Bots.LlmGenerations.DIMCID
import PrisonersDilemma.Bots.CupodTrollBot
import PrisonersDilemma.Bots.CupodBot
import PrisonersDilemma.Dynamics
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.Base.ValuationSoundness
import PrisonersDilemma.Theorems.CupodTrollBot.Helpers

open PD
open PD.Bots
open PD.BaseTheorems
namespace PD.Theorems

namespace DimcidCtbCensus

inductive SP (k : Nat) : Prog → Prog → Prop where
  | base : SP k (DIMCID k) (CupodTrollBot k)
  | simL (p q o : Prog) :
      SP k (p.subst (.sim p q) o) (q.subst (.sim p q) o) →
      SP k (.sim p q) o
  | botSimL (p q o : Prog) :
      SP k (p.subst (.bot (.sim p q)) o) (q.subst (.bot (.sim p q)) o) →
      SP k (.bot (.sim p q)) o

theorem SP_me {k : Nat} {me oppo : Prog} (h : SP k me oppo) :
    me = DIMCID k ∨ (∃ p q, me = .sim p q) ∨ (∃ p q, me = .bot (.sim p q)) := by
  cases h with
  | base => exact Or.inl rfl
  | simL p q o _ => exact Or.inr (Or.inl ⟨p, q, rfl⟩)
  | botSimL p q o _ => exact Or.inr (Or.inr ⟨p, q, rfl⟩)

theorem subst_eq_ctb {k : Nat} {q me o : Prog}
    (hme : (∃ p₂ q₂, me = .sim p₂ q₂) ∨ (∃ p₂ q₂, me = .bot (.sim p₂ q₂)))
    (h : q.subst me o = CupodTrollBot k) : o = CupodTrollBot k ∨ o = Prog.opp := by
  cases q with
  | const a => simp [Prog.subst, CupodTrollBot] at h
  | self =>
      rcases hme with ⟨p₂, q₂, rfl⟩ | ⟨p₂, q₂, rfl⟩ <;>
        simp [Prog.subst, CupodTrollBot] at h
  | opp => left; simpa [Prog.subst] using h
  | bot p => simp [Prog.subst, CupodTrollBot] at h
  | sim p q => simp [Prog.subst, CupodTrollBot] at h
  | ite b a p q => simp [Prog.subst, CupodTrollBot] at h
  | search K φg pp qq =>
      simp only [CupodTrollBot, Prog.subst, Prog.search.injEq] at h
      obtain ⟨hK, hg, hp, hq⟩ := h
      cases φg with
      | plays x y a => simp [Formula.subst] at hg
      | impl f1 f2 => simp [Formula.subst] at hg
      | box n' f1 => simp [Formula.subst] at hg
      | neg f1 => simp [Formula.subst] at hg
      | diag g' f1 => simp [Formula.subst] at hg
      | eq p' q' =>
          simp only [Formula.subst, Formula.eq.injEq] at hg
          obtain ⟨hlhs, hrhs⟩ := hg
          cases p' with
          | const a' => simp [Prog.subst] at hlhs
          | bot p'' => simp [Prog.subst] at hlhs
          | sim p'' q'' => simp [Prog.subst] at hlhs
          | ite b' a' p'' q'' => simp [Prog.subst] at hlhs
          | search K' g' p'' q'' => simp [Prog.subst] at hlhs
          | self =>
              rcases hme with ⟨p₂, q₂, rfl⟩ | ⟨p₂, q₂, rfl⟩ <;>
                simp [Prog.subst] at hlhs
          | opp =>
              simp only [Prog.subst] at hlhs
              right; exact hlhs

theorem subst_eq_opp {q me o : Prog}
    (hme : (∃ p₂ q₂, me = .sim p₂ q₂) ∨ (∃ p₂ q₂, me = .bot (.sim p₂ q₂)))
    (h : q.subst me o = Prog.opp) : o = Prog.opp := by
  cases q with
  | const a => simp [Prog.subst] at h
  | self =>
      rcases hme with ⟨p₂, q₂, rfl⟩ | ⟨p₂, q₂, rfl⟩ <;>
        simp [Prog.subst] at h
  | opp => simpa [Prog.subst] using h
  | bot p => simp [Prog.subst] at h
  | sim p q => simp [Prog.subst] at h
  | ite b a p q => simp [Prog.subst] at h
  | search K φg pp qq => simp [Prog.subst] at h

theorem SP_opp {k : Nat} {me oppo : Prog} (h : SP k me oppo) :
    oppo = CupodTrollBot k ∨ oppo = Prog.opp := by
  induction h with
  | base => exact Or.inl rfl
  | simL p q o hprem ih =>
      rcases ih with hc | ho
      · exact subst_eq_ctb (Or.inl ⟨p, q, rfl⟩) hc
      · exact Or.inr (subst_eq_opp (Or.inl ⟨p, q, rfl⟩) ho)
  | botSimL p q o hprem ih =>
      rcases ih with hc | ho
      · exact subst_eq_ctb (Or.inr ⟨p, q, rfl⟩) hc
      · exact Or.inr (subst_eq_opp (Or.inr ⟨p, q, rfl⟩) ho)

theorem SP_not_bot (k : Nat) : ∀ oppo z, ¬ SP k oppo (.bot z) := by
  intro oppo z h
  rcases SP_opp h with hc | ho
  · simp [CupodTrollBot] at hc
  · simp at ho

theorem SP_sim_inv {k : Nat} {p q oppo : Prog}
    (h : SP k (.sim p q) oppo) :
    SP k (p.subst (.sim p q) oppo) (q.subst (.sim p q) oppo) := by
  cases h with
  | simL _ _ _ hprem => exact hprem

theorem SP_botSim_inv {k : Nat} {p q oppo : Prog}
    (h : SP k (.bot (.sim p q)) oppo) :
    SP k (p.subst (.bot (.sim p q)) oppo) (q.subst (.bot (.sim p q)) oppo) := by
  cases h with
  | botSimL _ _ _ hprem => exact hprem

/-- CTB never plays D vs DIMCID (DIMCID ≠ CupodBot, so CTB cooperates). -/
theorem ctb_not_D_vs_dimcid (k : Nat) :
    ¬ (Formula.plays (CupodTrollBot k) (DIMCID k) Action.D).interp := by
  rintro ⟨n, hn⟩
  have hC : play (n + 2) (CupodTrollBot k) (DIMCID k) = some Action.C :=
    CupodTrollBot_cooperates_if_opp_not_CupodBot k n (DIMCID k) (by simp [DIMCID, CupodBot])
  have hD : play (n + 2) (CupodTrollBot k) (DIMCID k) = some Action.D :=
    eval_mono_le hn (n + 2) (by omega)
  rw [hC] at hD; simp at hD

theorem pf_WV (k : Nat) : ∀ {K : Nat} {φ : Formula},
    Pf K φ → WV (SP k) φ := by
  intro K φ h
  refine ((wv_sound_upto (SP k) (fun _ _ => False)
    (SP_not_bot k) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ K).2 K φ h).2 Pf_sound
  · intro me oppo a hT hgate
    rcases hT with hS | hF
    · rcases SP_me hS with rfl | ⟨p', q', rfl⟩ | ⟨p', q', rfl⟩ <;>
        rcases hgate with hb | hb <;> exact absurd hb (by simp [DIMCID])
    · exact hF.elim
  · intro me oppo hT hgate
    rcases hT with hS | hF
    · rcases SP_me hS with rfl | ⟨p', q', rfl⟩ | ⟨p', q', rfl⟩ <;>
        rcases hgate with hb | hb <;> exact absurd hb (by simp [DIMCID])
    · exact hF.elim
  · intro me oppo b a' p q hT hgate
    rcases hT with hS | hF
    · rcases SP_me hS with rfl | ⟨p', q', rfl⟩ | ⟨p', q', rfl⟩ <;>
        rcases hgate with hb | hb <;> exact absurd hb (by simp [DIMCID])
    · exact hF.elim
  · intro me oppo p hT hb
    rcases hT with hS | hF
    · rcases SP_me hS with rfl | ⟨p', q', rfl⟩ | ⟨p', q', rfl⟩ <;>
        exact absurd hb (by simp [DIMCID])
    · exact hF.elim
  · intro me oppo g ψ P Q hT hb
    rcases hT with hS | hF
    · rcases SP_me hS with rfl | ⟨p', q', rfl⟩ | ⟨p', q', rfl⟩ <;>
        exact absurd hb (by simp [DIMCID])
    · exact hF.elim
  · intro p q oppo hT
    rcases hT with hS | hF
    · exact Or.inl (SP_sim_inv hS)
    · exact hF.elim
  · intro p q oppo hT
    rcases hT with hS | hF
    · exact Or.inl (SP_botSim_inv hS)
    · exact hF.elim
  · -- h_search_t : the base kill
    intro oppo g ψ P Q a n hT hWV hcert
    rcases hT with hS | hF
    · rcases SP_me hS with hme | ⟨p', q', hme⟩ | ⟨p', q', hme⟩
      · unfold DIMCID at hme
        injection hme with h1 h2 h3 h4
        subst h2; subst h3; subst h4
        rw [h1] at hWV hcert hS
        rcases SP_opp hS with hopp | hopp
        · subst hopp
          simp only [Formula.subst, Prog.subst] at hWV
          rw [WV_impl] at hWV
          exfalso
          have hA : WV (SP k) (.plays (DIMCID k) (CupodTrollBot k) Action.C) := by
            rw [WV_plays]; exact Or.inl ⟨rfl, SP.base⟩
          have hcons := hWV hA
          rw [WV_plays] at hcons
          rcases hcons with ⟨hbad, _⟩ | hint
          · exact absurd hbad (by decide)
          · exact absurd hint (ctb_not_D_vs_dimcid k)
        · exfalso
          rw [hopp] at hS
          cases hS
      · simp at hme
      · simp at hme
    · exact hF.elim
  · -- h_search_f : the base else = .const C
    intro oppo g ψ P Q a n hT hcert
    rcases hT with hS | hF
    · rcases SP_me hS with hme | ⟨p', q', hme⟩ | ⟨p', q', hme⟩
      · unfold DIMCID at hme
        injection hme with h1 h2 h3 h4
        subst h4
        cases hcert
        rfl
      · simp at hme
      · simp at hme
    · exact hF.elim
  · exact fun p q oppo h => SP.simL p q oppo h
  · exact fun p q oppo h => SP.botSimL p q oppo h

/-- The DIMCID guard against CupodTrollBot is unprovable at every budget. -/
theorem dimcid_ctb_guard_not_provable (k K : Nat) :
    ¬ Pf K (.impl (.plays (DIMCID k) (CupodTrollBot k) Action.C)
                  (.plays (CupodTrollBot k) (DIMCID k) Action.D)) := by
  intro h
  have hWV := pf_WV k h
  rw [WV_impl] at hWV
  have hA : WV (SP k) (.plays (DIMCID k) (CupodTrollBot k) Action.C) := by
    rw [WV_plays]; exact Or.inl ⟨rfl, SP.base⟩
  have hcons := hWV hA
  rw [WV_plays] at hcons
  rcases hcons with ⟨hbad, _⟩ | hint
  · exact absurd hbad (by decide)
  · exact absurd hint (ctb_not_D_vs_dimcid k)

end DimcidCtbCensus

/-- DIMCID's guard search fails against CupodTrollBot. -/
theorem proofSearch_false_dimcid_vs_ctb (k : Nat) :
    proofSearch k
      ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.D)).subst
        (DIMCID k) (CupodTrollBot k)) = false := by
  cases hps : proofSearch k
      ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.D)).subst
        (DIMCID k) (CupodTrollBot k)) with
  | false => rfl
  | true =>
      have h := (proofSearch_spec k _).1 hps
      simp only [Formula.subst, Prog.subst] at h
      exact absurd h (DimcidCtbCensus.dimcid_ctb_guard_not_provable k k)

/-- DIMCID cooperates against CupodTrollBot (guard unprovable). -/
theorem DIMCID_plays_C_against_CupodTrollBot (k fuel : Nat) :
    play (fuel + 2) (DIMCID k) (CupodTrollBot k) = some .C := by
  show (if proofSearch k
            ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.D)).subst
              (DIMCID k) (CupodTrollBot k))
          then eval (fuel + 1) (DIMCID k) (CupodTrollBot k) (.const Action.D)
          else eval (fuel + 1) (DIMCID k) (CupodTrollBot k) (.const Action.C)) = some .C
  rw [proofSearch_false_dimcid_vs_ctb k]; simp [eval]

theorem llm_outcome_DIMCID_vs_CupodTrollBot :
    ∃ k₂, ∀ k, k₂ < k →
      ∃ fuel, outcome fuel (DIMCID k) (CupodTrollBot k) = some (.C, .C) := by
  refine ⟨0, fun k _ => ⟨2, ?_⟩⟩
  have hA : play 2 (DIMCID k) (CupodTrollBot k) = some .C :=
    DIMCID_plays_C_against_CupodTrollBot k 0
  have hB : play 2 (CupodTrollBot k) (DIMCID k) = some .C :=
    CupodTrollBot_cooperates_if_opp_not_CupodBot k 0 (DIMCID k) (by simp [DIMCID, CupodBot])
  exact outcome_of_plays _ _ _ _ _ hA hB

end PD.Theorems
