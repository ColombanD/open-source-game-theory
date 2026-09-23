import PrisonersDilemma.Bots.LlmGenerations.WaryBot
import PrisonersDilemma.Bots.CupodBot
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Base.ValuationSoundness

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

namespace WaryCupodCensus

theorem wc_subst_eq_wary {k : Nat} {q me o : Prog}
    (hme : (∃ p₂ q₂, me = .sim p₂ q₂) ∨ (∃ p₂ q₂, me = .bot (.sim p₂ q₂)))
    (h : q.subst me o = WaryBot k) : o = WaryBot k := by
  cases q with
  | const a => simp [Prog.subst, WaryBot] at h
  | self =>
      rcases hme with ⟨p₂, q₂, rfl⟩ | ⟨p₂, q₂, rfl⟩ <;>
        simp [Prog.subst, WaryBot] at h
  | opp => simpa [Prog.subst] using h
  | bot p => simp [Prog.subst, WaryBot] at h
  | sim p q => simp [Prog.subst, WaryBot] at h
  | ite b a p q => simp [Prog.subst, WaryBot] at h
  | search K φg pp qq =>
      simp only [WaryBot, Prog.subst, Prog.search.injEq] at h
      obtain ⟨hK, hg, hp, hq⟩ := h
      cases φg with
      | plays x y a => simp [Formula.subst] at hg
      | impl f1 f2 => simp [Formula.subst] at hg
      | box n' f1 => simp [Formula.subst] at hg
      | eq p' q' => simp [Formula.subst] at hg
      | diag g' f1 => simp [Formula.subst] at hg
      | neg f1 =>
          simp only [Formula.subst, Formula.neg.injEq] at hg
          cases f1 with
          | impl f2 f3 => simp [Formula.subst] at hg
          | neg f2 => simp [Formula.subst] at hg
          | box n' f2 => simp [Formula.subst] at hg
          | eq p' q' => simp [Formula.subst] at hg
          | diag g' f2 => simp [Formula.subst] at hg
          | plays x y a =>
              simp only [Formula.subst, Formula.plays.injEq] at hg
              obtain ⟨hx, hy, -⟩ := hg
              cases x with
              | const a' => simp [Prog.subst] at hx
              | bot p' => simp [Prog.subst] at hx
              | sim p' q' => simp [Prog.subst] at hx
              | ite b' a' p' q' => simp [Prog.subst] at hx
              | search K' g' p' q' => simp [Prog.subst] at hx
              | self =>
                  rcases hme with ⟨p₂, q₂, rfl⟩ | ⟨p₂, q₂, rfl⟩ <;>
                    simp [Prog.subst] at hx
              | opp =>
                  simp only [Prog.subst] at hx
                  cases y with
                  | const a' => simp [Prog.subst] at hy
                  | bot p' => simp [Prog.subst] at hy
                  | sim p' q' => simp [Prog.subst] at hy
                  | ite b' a' p' q' => simp [Prog.subst] at hy
                  | search K' g' p' q' => simp [Prog.subst] at hy
                  | self =>
                      rcases hme with ⟨p₂, q₂, rfl⟩ | ⟨p₂, q₂, rfl⟩ <;>
                        simp [Prog.subst] at hy
                  | opp =>
                      simp only [Prog.subst] at hy
                      rw [hx] at hy
                      exact absurd hy (by simp)

theorem wc_subst_eq_cupod {k : Nat} {q me o : Prog}
    (hme : (∃ p₂ q₂, me = .sim p₂ q₂) ∨ (∃ p₂ q₂, me = .bot (.sim p₂ q₂)))
    (h : q.subst me o = CupodBot k) : o = CupodBot k := by
  cases q with
  | const a => simp [Prog.subst, CupodBot] at h
  | self =>
      rcases hme with ⟨p₂, q₂, rfl⟩ | ⟨p₂, q₂, rfl⟩ <;>
        simp [Prog.subst, CupodBot] at h
  | opp => simpa [Prog.subst] using h
  | bot p => simp [Prog.subst, CupodBot] at h
  | sim p q => simp [Prog.subst, CupodBot] at h
  | ite b a p q => simp [Prog.subst, CupodBot] at h
  | search K φg pp qq =>
      simp only [CupodBot, Prog.subst, Prog.search.injEq] at h
      obtain ⟨hK, hg, hp, hq⟩ := h
      cases φg with
      | impl f1 f2 => simp [Formula.subst] at hg
      | box n' f1 => simp [Formula.subst] at hg
      | eq p' q' => simp [Formula.subst] at hg
      | diag g' f1 => simp [Formula.subst] at hg
      | neg f1 => simp [Formula.subst] at hg
      | plays x y a =>
          simp only [Formula.subst, Formula.plays.injEq] at hg
          obtain ⟨hx, hy, -⟩ := hg
          cases x with
          | const a' => simp [Prog.subst] at hx
          | bot p' => simp [Prog.subst] at hx
          | sim p' q' => simp [Prog.subst] at hx
          | ite b' a' p' q' => simp [Prog.subst] at hx
          | search K' g' p' q' => simp [Prog.subst] at hx
          | self =>
              rcases hme with ⟨p₂, q₂, rfl⟩ | ⟨p₂, q₂, rfl⟩ <;>
                simp [Prog.subst] at hx
          | opp =>
              simp only [Prog.subst] at hx
              cases y with
              | const a' => simp [Prog.subst] at hy
              | bot p' => simp [Prog.subst] at hy
              | sim p' q' => simp [Prog.subst] at hy
              | ite b' a' p' q' => simp [Prog.subst] at hy
              | search K' g' p' q' => simp [Prog.subst] at hy
              | self =>
                  rcases hme with ⟨p₂, q₂, rfl⟩ | ⟨p₂, q₂, rfl⟩ <;>
                    simp [Prog.subst] at hy
              | opp =>
                  simp only [Prog.subst] at hy
                  rw [hx] at hy
                  exact absurd hy (by simp)

/-- Entangled cooperation atoms. -/
inductive SP (k : Nat) : Prog → Prog → Prop where
  | baseCW : SP k (CupodBot k) (WaryBot k)
  | baseWC : SP k (WaryBot k) (CupodBot k)
  | simL (p q o : Prog) :
      SP k (p.subst (.sim p q) o) (q.subst (.sim p q) o) →
      SP k (.sim p q) o
  | botSimL (p q o : Prog) :
      SP k (p.subst (.bot (.sim p q)) o) (q.subst (.bot (.sim p q)) o) →
      SP k (.bot (.sim p q)) o

theorem SP_me {k : Nat} {me oppo : Prog} (h : SP k me oppo) :
    me = CupodBot k ∨ me = WaryBot k ∨
    (∃ p q, me = .sim p q) ∨ (∃ p q, me = .bot (.sim p q)) := by
  cases h with
  | baseCW => exact Or.inl rfl
  | baseWC => exact Or.inr (Or.inl rfl)
  | simL p q o _ => exact Or.inr (Or.inr (Or.inl ⟨p, q, rfl⟩))
  | botSimL p q o _ => exact Or.inr (Or.inr (Or.inr ⟨p, q, rfl⟩))

theorem SP_opp {k : Nat} {me oppo : Prog} (h : SP k me oppo) :
    oppo = WaryBot k ∨ oppo = CupodBot k := by
  induction h with
  | baseCW => exact Or.inl rfl
  | baseWC => exact Or.inr rfl
  | simL p q o hprem ih =>
      rcases ih with hw | hc
      · exact Or.inl (wc_subst_eq_wary (Or.inl ⟨p, q, rfl⟩) hw)
      · exact Or.inr (wc_subst_eq_cupod (Or.inl ⟨p, q, rfl⟩) hc)
  | botSimL p q o hprem ih =>
      rcases ih with hw | hc
      · exact Or.inl (wc_subst_eq_wary (Or.inr ⟨p, q, rfl⟩) hw)
      · exact Or.inr (wc_subst_eq_cupod (Or.inr ⟨p, q, rfl⟩) hc)

theorem SP_not_bot (k : Nat) : ∀ oppo z, ¬ SP k oppo (.bot z) := by
  intro oppo z h
  rcases SP_opp h with hw | hc
  · simp [WaryBot] at hw
  · simp [CupodBot] at hc

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

end WaryCupodCensus

end PD.Theorems

