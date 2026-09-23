import PrisonersDilemma.Bots.LlmGenerations.DIMCID
import PrisonersDilemma.Bots.CupodTrollBot
import PrisonersDilemma.Bots.CupodBot
import PrisonersDilemma.Dynamics
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.Base.ValuationSoundness
import PrisonersDilemma.Theorems.CupodTrollBot.Helpers

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

theorem dctb_CupodTrollBot_plays_C (k fuel : Nat) :
    play (fuel + 2) (CupodTrollBot k) (DIMCID k) = some .C :=
  CupodTrollBot_cooperates_if_opp_not_CupodBot k fuel (DIMCID k)
    (by simp [DIMCID, CupodBot])

theorem dctb_B_false (k : Nat) :
    ¬ (Formula.plays (CupodTrollBot k) (DIMCID k) Action.D).interp := by
  rintro ⟨n, hn⟩
  have hC : play (n + 2) (CupodTrollBot k) (DIMCID k) = some .C :=
    dctb_CupodTrollBot_plays_C k n
  have hn' : eval n (CupodTrollBot k) (DIMCID k) (CupodTrollBot k) = some .D := hn
  have hD : play (n + 2) (CupodTrollBot k) (DIMCID k) = some .D :=
    eval_mono_le hn' (n + 2) (by omega)
  rw [hC] at hD; simp at hD

theorem dctb_subst_DIMCID_imp {k : Nat} {p me o : Prog}
    (h : p.subst me o = DIMCID k) :
    me = DIMCID k ∨ o = DIMCID k ∨ me = .self ∨ o = .self := by
  cases p with
  | const a => simp [Prog.subst, DIMCID] at h
  | self => exact Or.inl (by simpa [Prog.subst] using h)
  | opp => exact Or.inr (Or.inl (by simpa [Prog.subst] using h))
  | bot w => simp [Prog.subst, DIMCID] at h
  | sim a b => simp [Prog.subst, DIMCID] at h
  | ite b a p q => simp [Prog.subst, DIMCID] at h
  | search K φg pp qq =>
      simp only [DIMCID, Prog.subst, Prog.search.injEq] at h
      obtain ⟨hK, hg, hp, hq⟩ := h
      cases φg with
      | plays x y a => simp [Formula.subst] at hg
      | neg f => simp [Formula.subst] at hg
      | box n f => simp [Formula.subst] at hg
      | eq x y => simp [Formula.subst] at hg
      | diag gg f => simp [Formula.subst] at hg
      | impl f1 f2 =>
          simp only [Formula.subst, Formula.impl.injEq] at hg
          obtain ⟨hf1, hf2⟩ := hg
          cases f1 with
          | plays x y a =>
              simp only [Formula.subst, Formula.plays.injEq] at hf1
              obtain ⟨hx, hy, ha⟩ := hf1
              cases x with
              | self => exact Or.inr (Or.inr (Or.inl (by simpa [Prog.subst] using hx)))
              | opp => exact Or.inr (Or.inr (Or.inr (by simpa [Prog.subst] using hx)))
              | const a' => simp [Prog.subst] at hx
              | bot p' => simp [Prog.subst] at hx
              | sim p' q' => simp [Prog.subst] at hx
              | ite b' a' p' q' => simp [Prog.subst] at hx
              | search K' g' p' q' => simp [Prog.subst] at hx
          | _ => simp [Formula.subst] at hf1

theorem dctb_subst_opp_val {k : Nat} {q me o : Prog}
    (hme : (∃ p₂ q₂, me = .sim p₂ q₂) ∨ (∃ p₂ q₂, me = .bot (.sim p₂ q₂)))
    (h : q.subst me o = CupodTrollBot k) : o = CupodTrollBot k ∨ o = .opp := by
  cases q with
  | const a => simp [Prog.subst, CupodTrollBot] at h
  | self =>
      rcases hme with ⟨p₂, q₂, rfl⟩ | ⟨p₂, q₂, rfl⟩ <;>
        simp [Prog.subst, CupodTrollBot] at h
  | opp => exact Or.inl (by simpa [Prog.subst] using h)
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
      | eq x y =>
          simp only [Formula.subst, Formula.eq.injEq] at hg
          obtain ⟨hx, -⟩ := hg
          cases x with
          | const a' => simp [Prog.subst] at hx
          | bot p' => simp [Prog.subst] at hx
          | sim p' q' => simp [Prog.subst] at hx
          | ite b' a' p' q' => simp [Prog.subst] at hx
          | search K' g' p' q' => simp [Prog.subst] at hx
          | self =>
              rcases hme with ⟨p₂, q₂, rfl⟩ | ⟨p₂, q₂, rfl⟩ <;>
                simp [Prog.subst] at hx
          | opp => exact Or.inr (by simpa [Prog.subst] using hx)

namespace DctbCensus

inductive SD (k : Nat) : Prog → Prog → Prop where
  | base : SD k (DIMCID k) (CupodTrollBot k)
  | simL (p q o : Prog) :
      SD k (p.subst (.sim p q) o) (q.subst (.sim p q) o) →
      SD k (.sim p q) o
  | botSimL (p q o : Prog) :
      SD k (p.subst (.bot (.sim p q)) o) (q.subst (.bot (.sim p q)) o) →
      SD k (.bot (.sim p q)) o

theorem SD_base_only {k : Nat} {me oppo : Prog} (h : SD k me oppo) :
    me = DIMCID k ∧ oppo = CupodTrollBot k := by
  induction h with
  | base => exact ⟨rfl, rfl⟩
  | simL p q o hp ih =>
      exfalso
      obtain ⟨ih1, ih2⟩ := ih
      have hd := dctb_subst_DIMCID_imp ih1
      have hc := dctb_subst_opp_val (Or.inl ⟨p, q, rfl⟩) ih2
      rcases hd with h1 | h1 | h1 | h1
      · simp [DIMCID] at h1
      · rcases hc with hcc | hcc <;> rw [h1] at hcc <;> simp [DIMCID, CupodTrollBot] at hcc
      · simp at h1
      · rcases hc with hcc | hcc <;> rw [h1] at hcc <;> simp [CupodTrollBot] at hcc
  | botSimL p q o hp ih =>
      exfalso
      obtain ⟨ih1, ih2⟩ := ih
      have hd := dctb_subst_DIMCID_imp ih1
      have hc := dctb_subst_opp_val (Or.inr ⟨p, q, rfl⟩) ih2
      rcases hd with h1 | h1 | h1 | h1
      · simp [DIMCID] at h1
      · rcases hc with hcc | hcc <;> rw [h1] at hcc <;> simp [DIMCID, CupodTrollBot] at hcc
      · simp at h1
      · rcases hc with hcc | hcc <;> rw [h1] at hcc <;> simp [CupodTrollBot] at hcc

theorem pf_WV_dctb (k : Nat) : ∀ {K : Nat} {φ : Formula},
    Pf K φ → WV (SD k) φ := by
  intro K φ h
  refine ((wv_sound_upto (SD k) (fun _ _ => False)
    (fun oppo z hb => by
      have h2 := (SD_base_only hb).2
      simp [CupodTrollBot] at h2)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ K).2 K φ h).2 Pf_sound
  · intro me oppo a hT hgate
    rcases hT with hS | hF
    · have hme := (SD_base_only hS).1; subst hme
      rcases hgate with hb | hb <;> simp [DIMCID] at hb
    · exact hF.elim
  · intro me oppo hT hgate
    rcases hT with hS | hF
    · have hme := (SD_base_only hS).1; subst hme
      rcases hgate with hb | hb <;> simp [DIMCID] at hb
    · exact hF.elim
  · intro me oppo b a' p q hT hgate
    rcases hT with hS | hF
    · have hme := (SD_base_only hS).1; subst hme
      rcases hgate with hb | hb <;> simp [DIMCID] at hb
    · exact hF.elim
  · intro me oppo p hT hb
    rcases hT with hS | hF
    · have hme := (SD_base_only hS).1; subst hme; simp [DIMCID] at hb
    · exact hF.elim
  · intro me oppo g ψ P Q hT hb
    rcases hT with hS | hF
    · have hme := (SD_base_only hS).1; subst hme; simp [DIMCID] at hb
    · exact hF.elim
  · intro p q oppo hT
    rcases hT with hS | hF
    · have hme := (SD_base_only hS).1; simp [DIMCID] at hme
    · exact hF.elim
  · intro p q oppo hT
    rcases hT with hS | hF
    · have hme := (SD_base_only hS).1; simp [DIMCID] at hme
    · exact hF.elim
  · -- h_search_t : the base kill
    intro oppo g ψ P Q a n hT hWV hcert
    rcases hT with hS | hF
    · cases hS with
      | base =>
          simp only [Formula.subst, Prog.subst] at hWV
          rw [WV_impl] at hWV
          have hA : WV (SD k) (.plays (DIMCID k) (CupodTrollBot k) Action.C) := by
            rw [WV_plays]; exact Or.inl ⟨rfl, SD.base⟩
          have hB := hWV hA
          rw [WV_plays] at hB
          rcases hB with ⟨hcc, -⟩ | hint
          · exact absurd hcc (by decide)
          · exact absurd hint (dctb_B_false k)
    · exact hF.elim
  · -- h_search_f
    intro oppo g ψ P Q a n hT hcert
    rcases hT with hS | hF
    · cases hS with
      | base =>
          cases hcert
          rfl
    · exact hF.elim
  · exact fun p q oppo h => SD.simL p q oppo h
  · exact fun p q oppo h => SD.botSimL p q oppo h

/-- The DIMCID guard against CupodTrollBot is not WV-true, hence not provable. -/
theorem dctb_guard_not_provable (k : Nat) :
    ¬ Pf k (.impl (.plays (DIMCID k) (CupodTrollBot k) Action.C)
                  (.plays (CupodTrollBot k) (DIMCID k) Action.D)) := by
  intro h
  have hWV := pf_WV_dctb k h
  rw [WV_impl] at hWV
  have hA : WV (SD k) (.plays (DIMCID k) (CupodTrollBot k) Action.C) := by
    rw [WV_plays]; exact Or.inl ⟨rfl, SD.base⟩
  have hB := hWV hA
  rw [WV_plays] at hB
  rcases hB with ⟨hcc, -⟩ | hint
  · exact absurd hcc (by decide)
  · exact absurd hint (dctb_B_false k)

end DctbCensus

/-- The DIMCID guard search fails against CupodTrollBot. -/
theorem proofSearch_false_dctb (k : Nat) :
    proofSearch k
      ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.D)).subst
        (DIMCID k) (CupodTrollBot k)) = false := by
  cases hps : proofSearch k
      ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.D)).subst
        (DIMCID k) (CupodTrollBot k)) with
  | false => rfl
  | true =>
      have := (proofSearch_spec k _).1 hps
      simp only [Formula.subst, Prog.subst] at this
      exact absurd this (DctbCensus.dctb_guard_not_provable k)

/-- DIMCID cooperates against CupodTrollBot (guard unprovable → else-branch). -/
theorem DIMCID_plays_C_against_CupodTrollBot (k fuel : Nat) :
    play (fuel + 2) (DIMCID k) (CupodTrollBot k) = some .C := by
  show (if proofSearch k
            ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.D)).subst
              (DIMCID k) (CupodTrollBot k))
          then eval (fuel + 1) (DIMCID k) (CupodTrollBot k) (.const Action.D)
          else eval (fuel + 1) (DIMCID k) (CupodTrollBot k) (.const Action.C)) = some .C
  rw [proofSearch_false_dctb k]; simp [eval]

theorem llm_outcome_DIMCID_vs_CupodTrollBot :
    ∃ k₂, ∀ k, k₂ < k →
      ∃ fuel, outcome fuel (DIMCID k) (CupodTrollBot k) = some (.C, .C) := by
  refine ⟨0, fun k _ => ⟨2, ?_⟩⟩
  have hA : play 2 (DIMCID k) (CupodTrollBot k) = some .C :=
    DIMCID_plays_C_against_CupodTrollBot k 0
  have hB : play 2 (CupodTrollBot k) (DIMCID k) = some .C :=
    dctb_CupodTrollBot_plays_C k 0
  exact outcome_of_plays _ _ _ _ _ hA hB

end PD.Theorems

