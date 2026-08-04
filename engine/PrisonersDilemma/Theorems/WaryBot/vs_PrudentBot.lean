import PrisonersDilemma.Bots.LlmGenerations.WaryBot
import PrisonersDilemma.Bots.LlmGenerations.PrudentBot
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Theorems.LlmGenerations.LlmLemmas
import PrisonersDilemma.Theorems.WaryBot.Helpers
import PrisonersDilemma.Theorems.PrudentBot.Helpers

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

/-! ## Census 1 — WaryBot cooperates: it cannot refute PrudentBot's cooperation. -/

inductive WaryPrudentCensus (k : Nat) : Prog → Prog → Prop where
  | base : WaryPrudentCensus k (PrudentBot k) (WaryBot k)
  | simL (p q o : Prog) :
      WaryPrudentCensus k (p.subst (.sim p q) o) (q.subst (.sim p q) o) →
      WaryPrudentCensus k (.sim p q) o
  | botSimL (p q o : Prog) :
      WaryPrudentCensus k (p.subst (.bot (.sim p q)) o) (q.subst (.bot (.sim p q)) o) →
      WaryPrudentCensus k (.bot (.sim p q)) o

theorem WaryPrudentCensus_opp {k : Nat} {me oppo : Prog} (h : WaryPrudentCensus k me oppo) :
    oppo = WaryBot k := by
  induction h with
  | base => rfl
  | simL p q o hprem ih => exact WaryCensus.subst_eq_wary (Or.inl ⟨p, q, rfl⟩) ih
  | botSimL p q o hprem ih => exact WaryCensus.subst_eq_wary (Or.inr ⟨p, q, rfl⟩) ih

theorem waryPrudent_prudent_noD_floor (k : Nat) :
    ∀ n, PlaysProof (PrudentBot k) (WaryBot k) (PrudentBot k) .D n → k < n := by
  intro n hpp
  unfold PrudentBot at hpp
  cases hpp with
  | search_t hProv hbr =>
      cases hbr with
      | search_t hProv2 hbr2 => cases hbr2
      | search_f hneg2 hbr2 => simp only [c_node, c_guard, numCost]; omega
  | search_f hneg hbr => simp only [c_node]; omega

theorem waryPrudentCensus_noD_floor (k : Nat) :
    ∀ p q, WaryPrudentCensus k p q → ∀ n, PlaysProof p q p .D n → k < n := by
  intro p q h
  induction h with
  | base => exact waryPrudent_prudent_noD_floor k
  | simL p q o hprem ih =>
      intro n hpp
      cases hpp with
      | sim hsub => simp only [c_node]; have := ih _ hsub; omega
  | botSimL p q o hprem ih =>
      intro n hpp
      cases hpp with
      | bot hsub =>
          cases hsub with
          | sim hsub2 => simp only [c_node]; have := ih _ hsub2; omega

theorem waryPrudentCensus_not_bot (k : Nat) : ∀ oppo z, ¬ WaryPrudentCensus k oppo (.bot z) := by
  intro oppo z h
  have hw := WaryPrudentCensus_opp h
  simp [WaryBot] at hw

theorem no_Pf_neg_wary_prudent (k K : Nat) (hK : K ≤ k) :
    ¬ Pf K (.neg (.plays (PrudentBot k) (WaryBot k) .C)) := by
  intro h
  have hWV : WV (WaryPrudentCensus k) (.neg (.plays (PrudentBot k) (WaryBot k) .C)) :=
    PD.LlmLemmas.wv_budget_census k (WaryPrudentCensus k)
      (waryPrudentCensus_not_bot k)
      (fun p q o hh => WaryPrudentCensus.simL p q o hh)
      (fun p q o hh => WaryPrudentCensus.botSimL p q o hh)
      (waryPrudentCensus_noD_floor k)
      K _ h hK
  rw [WV_neg] at hWV
  refine hWV ?_
  rw [WV_plays]
  exact Or.inl ⟨rfl, WaryPrudentCensus.base⟩

/-- WaryBot cannot refute PrudentBot's cooperation within its own budget. -/
theorem proofSearch_false_wary_prudent (k : Nat) :
    proofSearch k (.neg (.plays (PrudentBot k) (WaryBot k) .C)) = false := by
  cases h : proofSearch k (.neg (.plays (PrudentBot k) (WaryBot k) .C)) with
  | true => exact absurd ((proofSearch_spec _ _).1 h) (no_Pf_neg_wary_prudent k k le_rfl)
  | false => rfl

/-- WaryBot cooperates with PrudentBot. -/
theorem WaryBot_cooperates_vs_PrudentBot (k fuel : Nat) :
    play (fuel + 2) (WaryBot k) (PrudentBot k) = some .C := by
  have hg := proofSearch_false_wary_prudent k
  show eval (fuel + 2) (WaryBot k) (PrudentBot k) (WaryBot k) = some .C
  unfold WaryBot at hg ⊢
  simp [eval, Prog.subst, Formula.subst, hg]

/-! ## Census 2 — PrudentBot defects: it cannot prove WaryBot cooperates. -/

theorem waryPrudent_no_provable_C_tail (k : Nat) :
    ∀ K φ, Pf K φ → K ≤ k →
      TailTo (.plays (WaryBot k) (PrudentBot k) .C) φ → False := by
  intro K φ hp hK htail
  refine no_provable_tailToS_floor k (· = .plays (WaryBot k) (PrudentBot k) .C)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ K φ hp hK ((TailToS_singleton _ φ).2 htail)
  · rintro φ rfl; exact ⟨_, _, _, rfl⟩
  · rintro K hK φ rfl hA
    cases hA with
    | mk hpp hn =>
      show False
      unfold WaryBot at hpp
      cases hpp with
      | search_t hProv hbr => cases hbr
      | search_f hneg hbr => simp only [c_node] at hn; omega
  · intro me oppo c hS g ψ b hme
    injection hS with h1 h2 h3; subst h1
    unfold WaryBot at hme
    simp only [Prog.search.injEq] at hme
    obtain ⟨-, -, hthen, -⟩ := hme
    subst h3
    exact absurd hthen (by simp)
  · intro me oppo c hS p q hme; injection hS with h1 h2 h3; subst h1
    unfold WaryBot at hme; simp at hme
  · intro me oppo c hS p q hme; injection hS with h1 h2 h3; subst h1
    unfold WaryBot at hme; simp at hme
  · intro me oppo c hS g ψ b hme; injection hS with h1 h2 h3; subst h1
    unfold WaryBot at hme; simp at hme
  · rintro z a' g ψ c0 c1 q oppo hS
    injection hS with h1 h2 h3
    unfold WaryBot at h1; simp at h1
  · intro me oppo c hS k₁ ψ₁ k₂ ψ₂ c1 q hme; injection hS with h1 h2 h3; subst h1
    unfold WaryBot at hme; simp at hme
  · intro me oppo c hS L hme; injection hS with h1 h2 h3; subst h1; subst h3
    cases L with
    | nil => unfold WaryBot at hme; simp [searchPlug] at hme
    | cons hd tl =>
        obtain ⟨g, ψ, e⟩ := hd
        unfold WaryBot at hme; simp only [searchPlug, Prog.search.injEq] at hme
        obtain ⟨-, -, hthen, -⟩ := hme
        cases tl with
        | nil => simp [searchPlug] at hthen
        | cons hd2 tl2 => obtain ⟨g2, ψ2, e2⟩ := hd2; simp [searchPlug] at hthen
  · intro me oppo c hS hd L hme; injection hS with h1 h2 h3; subst h1; subst h3
    exfalso
    cases hd with
    | searchL g ψ e =>
        unfold WaryBot at hme; simp only [ctxPlug, Prog.search.injEq] at hme
        obtain ⟨-, -, hthen, -⟩ := hme
        cases L with
        | nil => simp [ctxPlug] at hthen
        | cons hd2 tl2 =>
            cases hd2 with
            | searchL g2 ψ2 e2 => simp [ctxPlug] at hthen
            | iteL z2 aT2 o2 => simp [ctxPlug] at hthen
    | iteL z aT o => unfold WaryBot at hme; simp [ctxPlug] at hme
  · -- polarity plug: WaryBot's `.neg` guard blocks every `elseL` layer, and its
    -- then-slot `.const .D ≠` any C-plug
    intro me oppo c hS hd L hme
    injection hS with h1 h2 h3; subst h1; subst h3
    exfalso
    cases hd with
    | thenL g ψ e =>
        simp only [plug2, WaryBot, Prog.search.injEq] at hme
        obtain ⟨-, -, hplug, -⟩ := hme
        cases L with
        | nil => simp [plug2] at hplug
        | cons hd2 tl2 => cases hd2 <;> simp [plug2] at hplug
    | elseL g P' Q' c' q =>
        simp only [plug2, WaryBot, Prog.search.injEq] at hme
        exact absurd hme.2.1 (by simp)

theorem proofSearch_false_prudent_wary (k : Nat) :
    proofSearch k (.plays (WaryBot k) (PrudentBot k) .C) = false := by
  cases h : proofSearch k (.plays (WaryBot k) (PrudentBot k) .C) with
  | true =>
      exact absurd ((proofSearch_spec _ _).1 h)
        (fun hp => waryPrudent_no_provable_C_tail k k _ hp le_rfl (by simp))
  | false => rfl

/-- PrudentBot defects against WaryBot: its outer cooperation search fails. -/
theorem PrudentBot_defects_vs_WaryBot (k fuel : Nat) :
    play (fuel + 2) (PrudentBot k) (WaryBot k) = some .D :=
  PrudentBot_plays_D_of_search_false k fuel (WaryBot k)
    (proofSearch_false_prudent_wary k)

/-! ## The outcome -/

theorem llm_outcome_WaryBot_vs_PrudentBot :
    ∃ k₂, ∀ k, k₂ < k →
      ∃ fuel, outcome fuel (WaryBot k) (PrudentBot k) = some (.C, .D) := by
  refine ⟨0, fun k _ => ⟨2, ?_⟩⟩
  have hA : play 2 (WaryBot k) (PrudentBot k) = some .C :=
    WaryBot_cooperates_vs_PrudentBot k 0
  have hB : play 2 (PrudentBot k) (WaryBot k) = some .D :=
    PrudentBot_defects_vs_WaryBot k 0
  exact outcome_of_plays _ _ _ _ _ hA hB

end PD.Theorems

