import PrisonersDilemma.Bots.LlmGenerations.WaryBot
import PrisonersDilemma.Bots.LlmGenerations.JustBot
import PrisonersDilemma.Bots.DupocBot
import PrisonersDilemma.Dynamics
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.Theorems.WaryBot.Helpers
import PrisonersDilemma.Theorems.JustBot.Helpers
import PrisonersDilemma.Theorems.LlmGenerations.LlmLemmas

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

/-! # WaryBot vs JustBot = (C, D)

WaryBot cooperates (cannot refute JustBot's cooperation — JustBot's defection is itself
uncertifiable), JustBot defects (cannot certify WaryBot's cooperation — WaryBot's C is an
else-play, floor-priced). Determined at every budget `k`. -/

-- (A): JustBot defects — its guard "WaryBot plays C vs .bot(DupocBot k)" is unprovable
--      (WaryBot's C is an else-play; every cert pays the search_f floor > k).
theorem wj_no_provable_A_tail (k : Nat) :
    ∀ K φ, Pf K φ → K ≤ k →
      TailTo (.plays (WaryBot k) (.bot (DupocBot k)) .C) φ → False := by
  intro K φ hp hK htail
  refine no_provable_tailToS_floor k (· = .plays (WaryBot k) (.bot (DupocBot k)) .C)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ K φ hp hK ((TailToS_singleton _ φ).2 htail)
  · rintro φ' rfl; exact ⟨_, _, _, rfl⟩
  · intro K' hK' φ' hφ' hA
    cases hφ'
    cases hA with
    | mk hpp hn =>
        unfold WaryBot at hpp
        cases hpp with
        | search_t hProv hbr => cases hbr
        | search_f hneg hbr => simp only [c_node] at hn; omega
  · intro me oppo c hS g ψ b hme
    injection hS with h1 h2 h3; subst h1; subst h2; subst h3
    unfold WaryBot at hme; simp only [Prog.search.injEq] at hme
    obtain ⟨-, -, hthen, -⟩ := hme; injection hthen with hd; exact Action.noConfusion hd
  · intro me oppo c hS p q hme
    injection hS with h1 h2 h3; subst h1; simp [WaryBot] at hme
  · intro me oppo c hS p q hme
    injection hS with h1 h2 h3; subst h1; simp [WaryBot] at hme
  · intro me oppo c hS g ψ b hme
    injection hS with h1 h2 h3; subst h1; simp [WaryBot] at hme
  · intro z a' g ψ c0 c1 q oppo hS
    injection hS with h1 h2 h3; simp [WaryBot] at h1
  · intro me oppo c hS k₁ ψ₁ k₂ ψ₂ c1 q hme
    injection hS with h1 h2 h3; subst h1
    unfold WaryBot at hme; simp only [Prog.search.injEq] at hme
    obtain ⟨-, -, hthen, -⟩ := hme; simp at hthen
  · intro me oppo c hS L hme
    injection hS with h1 h2 h3; subst h1; subst h3
    cases L with
    | nil => simp [searchPlug, WaryBot] at hme
    | cons hd tl =>
        obtain ⟨g, ψ, e⟩ := hd
        unfold WaryBot at hme; simp only [searchPlug, Prog.search.injEq] at hme
        obtain ⟨-, -, hthen, -⟩ := hme
        cases tl with
        | nil => simp [searchPlug] at hthen
        | cons hd2 tl2 => obtain ⟨g2, ψ2, e2⟩ := hd2; simp [searchPlug] at hthen
  · intro me oppo c hS hd L hme
    injection hS with h1 h2 h3; subst h1; subst h3
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
  · -- polarity plug: WaryBot's guard is a `.neg` — no `elseL` layer can match it,
    -- and the then-slot holds `.const D ≠` any C-plug
    rintro me oppo c hS hd L hme
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

theorem wj_proofSearch_false_A (k : Nat) :
    proofSearch k (.plays (WaryBot k) (.bot (DupocBot k)) .C) = false := by
  cases h : proofSearch k (.plays (WaryBot k) (.bot (DupocBot k)) .C) with
  | true =>
      exact absurd ((proofSearch_spec k _).mp h)
        (fun hp => wj_no_provable_A_tail k k _ hp le_rfl (by simp))
  | false => rfl

-- (B): WaryBot cooperates — it cannot refute JustBot's cooperation, since JustBot's
--      D-play cert is a search_f floor > k, so (JustBot k, WaryBot k) survives in a
--      play-C-forced WV census (h_noD holds).
inductive SPJust (k : Nat) : Prog → Prog → Prop where
  | base : SPJust k (JustBot k) (WaryBot k)
  | simL (p q o : Prog) :
      SPJust k (p.subst (.sim p q) o) (q.subst (.sim p q) o) →
      SPJust k (.sim p q) o
  | botSimL (p q o : Prog) :
      SPJust k (p.subst (.bot (.sim p q)) o) (q.subst (.bot (.sim p q)) o) →
      SPJust k (.bot (.sim p q)) o

theorem SPJust_opp {k : Nat} {me oppo : Prog} (h : SPJust k me oppo) :
    oppo = WaryBot k := by
  induction h with
  | base => rfl
  | simL p q o hprem ih => exact WaryCensus.subst_eq_wary (Or.inl ⟨p, q, rfl⟩) ih
  | botSimL p q o hprem ih => exact WaryCensus.subst_eq_wary (Or.inr ⟨p, q, rfl⟩) ih

theorem SPJust_nb (k : Nat) : ∀ oppo z, ¬ SPJust k oppo (.bot z) := by
  intro oppo z h; have := SPJust_opp h; simp [WaryBot] at this

theorem SPJust_no_D_cert (k : Nat) :
    ∀ (P O : Prog), SPJust k P O → ∀ n, PlaysProof P O P .D n → k < n := by
  intro P O hmem
  induction hmem with
  | base =>
      intro n hpp; unfold JustBot at hpp
      cases hpp with
      | search_t hProv hbr => cases hbr
      | search_f hneg hbr => simp only [c_node]; omega
  | simL p q o hprem ih =>
      intro n hpp
      cases hpp with
      | sim hin => rename_i n'; have := ih n' hin; simp only [c_node]; omega
  | botSimL p q o hprem ih =>
      intro n hpp
      cases hpp with
      | bot hin => cases hin with
        | sim hin2 => rename_i n'; have := ih n' hin2; simp only [c_node]; omega

theorem wj_no_Pf_neg_B (k K : Nat) (hK : K ≤ k) :
    ¬ Pf K (.neg (.plays (JustBot k) (WaryBot k) .C)) := by
  intro h
  have hWV := PD.LlmLemmas.wv_budget_census k (SPJust k)
    (SPJust_nb k)
    (fun p q o hh => SPJust.simL p q o hh)
    (fun p q o hh => SPJust.botSimL p q o hh)
    (SPJust_no_D_cert k) K _ h hK
  rw [WV_neg] at hWV
  refine hWV ?_
  rw [WV_plays]
  exact Or.inl ⟨rfl, SPJust.base⟩

theorem wj_proofSearch_false_negB (k : Nat) :
    proofSearch k (.neg (.plays (JustBot k) (WaryBot k) .C)) = false := by
  cases h : proofSearch k (.neg (.plays (JustBot k) (WaryBot k) .C)) with
  | true => exact absurd ((proofSearch_spec k _).mp h) (wj_no_Pf_neg_B k k le_rfl)
  | false => rfl

/-- WaryBot cooperates with JustBot (guard `.neg B` unprovable ⇒ else `.const .C`). -/
theorem WaryBot_plays_C_vs_JustBot (k fuel : Nat) :
    play (fuel + 2) (WaryBot k) (JustBot k) = some .C := by
  have hg := wj_proofSearch_false_negB k
  show eval (fuel + 2) (WaryBot k) (JustBot k) (WaryBot k) = some .C
  unfold WaryBot at hg ⊢
  simp [eval, Prog.subst, Formula.subst, hg]

/-- JustBot defects against WaryBot (guard `A` unprovable ⇒ else `.const .D`). -/
theorem JustBot_plays_D_vs_WaryBot (k fuel : Nat) :
    play (fuel + 2) (JustBot k) (WaryBot k) = some .D := by
  have hg := wj_proofSearch_false_A k
  show eval (fuel + 2) (JustBot k) (WaryBot k) (JustBot k) = some .D
  unfold JustBot
  simp [eval, Prog.subst, Formula.subst, hg]

/-- **WaryBot vs JustBot = (C, D)** at every sufficiently large budget (indeed every `k`). -/
theorem llm_outcome_WaryBot_vs_JustBot :
    ∃ k₂, ∀ k, k₂ < k →
      ∃ fuel, outcome fuel (WaryBot k) (JustBot k) = some (.C, .D) := by
  refine ⟨0, fun k _ => ⟨2, ?_⟩⟩
  exact outcome_of_plays 2 _ _ _ _
    (WaryBot_plays_C_vs_JustBot k 0) (JustBot_plays_D_vs_WaryBot k 0)

end PD.Theorems
