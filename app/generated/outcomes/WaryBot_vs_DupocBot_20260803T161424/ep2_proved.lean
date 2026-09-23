import PrisonersDilemma.Bots.LlmGenerations.WaryBot
import PrisonersDilemma.Bots.DupocBot
import PrisonersDilemma.Dynamics
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.Theorems.WaryBot.Helpers
import PrisonersDilemma.Theorems.LlmGenerations.LlmLemmas

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

/-! ### WaryBot vs DupocBot — the determined `(C, D)` outcome.

Both bots are searchers with a DEFECTING "wrong" branch, so neither can sit in the master
`wv_sound_upto`'s `S` (its unconditional `h_search_f` demands the else-branch play `.C`). The
resolution is budget-aware: (1) DupocBot cannot prove `A = "WaryBot plays C"` — `A` is WaryBot's
ELSE play, so its certificate pays the `search_f` floor `> k` (`wd_no_provable_A_tail`, an instance
of the set-valued floor kernel with the searchBranch kill ACTION-refined: WaryBot's THEN action is
`.D`, never `.C`), hence DupocBot defects; (2) WaryBot cannot prove `.neg B` where `B = "DupocBot
plays C"` — `B` is DupocBot's THEN play needing `Pf A` (impossible), and refuting it needs a
`.D`-certificate of DupocBot whose `search_f` floor `> k`. (2) is the budget-gated WV census
`PD.LlmLemmas.wv_budget_census` at the sim-closure `SPDupoc` of `(DupocBot, WaryBot)`. -/

/-- The sim-closure of the entangled base pair `(DupocBot k, WaryBot k)`. -/
inductive SPDupoc (k : Nat) : Prog → Prog → Prop where
  | base : SPDupoc k (DupocBot k) (WaryBot k)
  | simL (p q o : Prog) :
      SPDupoc k (p.subst (.sim p q) o) (q.subst (.sim p q) o) →
      SPDupoc k (.sim p q) o
  | botSimL (p q o : Prog) :
      SPDupoc k (p.subst (.bot (.sim p q)) o) (q.subst (.bot (.sim p q)) o) →
      SPDupoc k (.bot (.sim p q)) o

theorem SPDupoc_opp {k : Nat} {me oppo : Prog} (h : SPDupoc k me oppo) :
    oppo = WaryBot k := by
  induction h with
  | base => rfl
  | simL p q o hprem ih => exact WaryCensus.subst_eq_wary (Or.inl ⟨p, q, rfl⟩) ih
  | botSimL p q o hprem ih => exact WaryCensus.subst_eq_wary (Or.inr ⟨p, q, rfl⟩) ih

theorem SPDupoc_nb (k : Nat) : ∀ oppo z, ¬ SPDupoc k oppo (.bot z) := by
  intro oppo z h; have := SPDupoc_opp h; simp [WaryBot] at this

/-- Every `SPDupoc`-member's `.D`-play costs strictly more than `k`: the base is DupocBot's
    else-play (`search_f` floor), and each sim-lift adds a `c_node`. -/
theorem SPDupoc_no_D_cert (k : Nat) :
    ∀ (P O : Prog), SPDupoc k P O → ∀ n, PlaysProof P O P .D n → k < n := by
  intro P O hmem
  induction hmem with
  | base =>
      intro n hpp; unfold DupocBot at hpp
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

/-- **Obligation 1**: `A = "WaryBot plays C vs DupocBot"` is unprovable at every budget `≤ k`.
    `A` is WaryBot's ELSE play (target `.C`, but WaryBot's THEN action is `.D`), so `searchBranch`
    reads the wrong action and any `.C`-certificate pays the `search_f` floor `> k`. Instance of
    the set-valued floor kernel, `hsb` discharged by ACTION mismatch (`.const .D ≠ .const .C`). -/
theorem wd_no_provable_A_tail (k : Nat) :
    ∀ K φ, Pf K φ → K ≤ k →
      TailTo (.plays (WaryBot k) (DupocBot k) .C) φ → False := by
  intro K φ hp hK htail
  refine no_provable_tailToS_floor k (· = .plays (WaryBot k) (DupocBot k) .C)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ K φ hp hK ((TailToS_singleton _ φ).2 htail)
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

/-- DupocBot's guard `A` fails at every budget, so DupocBot defects. -/
theorem wd_proofSearch_false_A (k : Nat) :
    proofSearch k (.plays (WaryBot k) (DupocBot k) .C) = false := by
  cases h : proofSearch k (.plays (WaryBot k) (DupocBot k) .C) with
  | true =>
      exact absurd ((proofSearch_spec k _).mp h)
        (fun hp => wd_no_provable_A_tail k k _ hp le_rfl (by simp))
  | false => rfl

/-- **Obligation 2** (WV census): WaryBot's refutation guard `.neg B` is unprovable at every
    budget `≤ k`. Instantiate `wv_budget_census` at `SPDupoc k`; `.neg B` is `WV`-false since
    `B = "DupocBot plays C"` is a base member (WV-forced true). -/
theorem wd_no_Pf_neg_B (k K : Nat) (hK : K ≤ k) :
    ¬ Pf K (.neg (.plays (DupocBot k) (WaryBot k) .C)) := by
  intro h
  have hWV := PD.LlmLemmas.wv_budget_census k (SPDupoc k)
    (SPDupoc_nb k)
    (fun p q o hh => SPDupoc.simL p q o hh)
    (fun p q o hh => SPDupoc.botSimL p q o hh)
    (SPDupoc_no_D_cert k) K _ h hK
  rw [WV_neg] at hWV
  refine hWV ?_
  rw [WV_plays]
  exact Or.inl ⟨rfl, SPDupoc.base⟩

/-- WaryBot's guard `.neg B` fails at every budget, so WaryBot cooperates. -/
theorem wd_proofSearch_false_negB (k : Nat) :
    proofSearch k (.neg (.plays (DupocBot k) (WaryBot k) .C)) = false := by
  cases h : proofSearch k (.neg (.plays (DupocBot k) (WaryBot k) .C)) with
  | true => exact absurd ((proofSearch_spec k _).mp h) (wd_no_Pf_neg_B k k le_rfl)
  | false => rfl

/-- WaryBot cooperates with DupocBot (guard `.neg B` unprovable ⇒ else `.const .C`). -/
theorem WaryBot_plays_C_vs_DupocBot (k fuel : Nat) :
    play (fuel + 2) (WaryBot k) (DupocBot k) = some .C := by
  have hg := wd_proofSearch_false_negB k
  show eval (fuel + 2) (WaryBot k) (DupocBot k) (WaryBot k) = some .C
  unfold WaryBot at hg ⊢
  simp [eval, Prog.subst, Formula.subst, hg]

/-- DupocBot defects against WaryBot (guard `A` unprovable ⇒ else `.const .D`). -/
theorem DupocBot_plays_D_vs_WaryBot (k fuel : Nat) :
    play (fuel + 2) (DupocBot k) (WaryBot k) = some .D := by
  have hg := wd_proofSearch_false_A k
  show eval (fuel + 2) (DupocBot k) (WaryBot k) (DupocBot k) = some .D
  unfold DupocBot at hg ⊢
  simp [eval, Prog.subst, Formula.subst, hg]

/-- **WaryBot vs DupocBot = (C, D)** at every sufficiently large budget (indeed every `k`). -/
theorem llm_outcome_WaryBot_vs_DupocBot :
    ∃ k₂, ∀ k, k₂ < k →
      ∃ fuel, outcome fuel (WaryBot k) (DupocBot k) = some (.C, .D) := by
  refine ⟨0, fun k _ => ⟨2, ?_⟩⟩
  exact outcome_of_plays 2 _ _ _ _
    (WaryBot_plays_C_vs_DupocBot k 0) (DupocBot_plays_D_vs_WaryBot k 0)

end PD.Theorems
