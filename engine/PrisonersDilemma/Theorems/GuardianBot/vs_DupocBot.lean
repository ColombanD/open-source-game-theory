import PrisonersDilemma.Bots.LlmGenerations.GuardianBot
import PrisonersDilemma.Bots.DupocBot
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Dynamics
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.Theorems.CooperateBot.Helpers
import PrisonersDilemma.Theorems.DupocBot.Helpers
import PrisonersDilemma.Theorems.GuardianBot.Helpers

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

-- === GuardianBot side: cooperates (guard refuted) ===

theorem gd_dupoc_C_vs_botCB (k fuel : Nat) (hk : 2 ≤ k) :
    play (fuel + 2) (DupocBot k) (.bot CooperateBot) = some .C := by
  have hCB : proofSearch k (.plays (.bot CooperateBot) (DupocBot k) .C) = true :=
    (proofSearch_spec _ _).2 (Pf.atom
      ⟨PlaysProof.bot PlaysProof.const, by simp only [c_leaf, c_node]; omega⟩)
  exact DupocBot_plays_C_against_bot_CooperateBot k fuel hCB

theorem gd_interp_dupoc_D_vs_botCB_false (k : Nat) (hk : 2 ≤ k) :
    ¬ (Formula.plays (DupocBot k) (.bot CooperateBot) .D).interp := by
  rintro ⟨n, hn⟩
  have hC : play (n + 2) (DupocBot k) (.bot CooperateBot) = some .C :=
    gd_dupoc_C_vs_botCB k n hk
  have hD : play (n + 2) (DupocBot k) (.bot CooperateBot) = some .D :=
    eval_mono_le hn (n + 2) (by omega)
  rw [hC] at hD; simp at hD

theorem gd_guardian_guard_false (k : Nat) (hk : 2 ≤ k) :
    proofSearch k (.plays (DupocBot k) (.bot CooperateBot) .D) = false := by
  cases hps : proofSearch k (.plays (DupocBot k) (.bot CooperateBot) .D) with
  | true  => exact absurd (proofSearch_sound _ _ hps) (gd_interp_dupoc_D_vs_botCB_false k hk)
  | false => rfl

theorem gd_GuardianBot_C_vs_DupocBot (k fuel : Nat) (hk : 2 ≤ k) :
    play (fuel + 2) (GuardianBot k) (DupocBot k) = some .C := by
  have hg := gd_guardian_guard_false k hk
  show eval (fuel + 2) (GuardianBot k) (DupocBot k) (GuardianBot k) = some .C
  unfold GuardianBot
  simp [eval, Prog.subst, Formula.subst, hg]

-- === DupocBot side: defects (floor kills its guard) ===

theorem gd_no_provable_C_tail (k : Nat) :
    ∀ K φ, Pf K φ → K ≤ k →
      TailTo (.plays (GuardianBot k) (DupocBot k) .C) φ → False := by
  intro K φ hp hK ht
  refine no_provable_tailToS_floor k (· = .plays (GuardianBot k) (DupocBot k) .C)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ K φ hp hK ((TailToS_singleton _ φ).2 ht)
  · rintro φ' rfl; exact ⟨_, _, _, rfl⟩
  · intro K' hK' φ' hφ'
    cases hφ'
    intro hA
    cases hA with
    | mk hpp hn =>
      unfold GuardianBot at hpp
      cases hpp with
      | search_t hProv hbr => cases hbr
      | search_f hneg hbr => simp only [c_node] at hn; omega
  · intro me oppo c hS g ψ b hme
    injection hS with h1 h2 h3
    subst h1; subst h3
    unfold GuardianBot at hme
    injection hme with e1 e2 e3 e4
    simp at e3
  · intro me oppo c hS p q hme
    injection hS with h1 h2 h3
    subst h1
    unfold GuardianBot at hme; simp at hme
  · intro me oppo c hS p q hme
    injection hS with h1 h2 h3
    subst h1
    unfold GuardianBot at hme; simp at hme
  · intro me oppo c hS g ψ b hme
    injection hS with h1 h2 h3
    subst h1
    unfold GuardianBot at hme; simp at hme
  · intro z a' g ψ c0 c1 q oppo hS
    injection hS with h1 h2 h3
    unfold GuardianBot at h1; simp at h1
  · intro me oppo c hS k₁ ψ₁ k₂ ψ₂ c1 q hme
    injection hS with h1 h2 h3
    subst h1
    unfold GuardianBot at hme; simp at hme
  · intro me oppo c hS L hme
    injection hS with h1 h2 h3
    subst h1; subst h3
    cases L with
    | nil => unfold GuardianBot at hme; simp [searchPlug] at hme
    | cons hd tl =>
        obtain ⟨g, ψ, e⟩ := hd
        unfold GuardianBot at hme
        simp only [searchPlug, Prog.search.injEq] at hme
        have hcontra := hme.2.2.1
        rw [searchPlug_eq_ctxPlug tl (.const .C)] at hcontra
        exact const_ne_ctxPlug (by decide) _ hcontra
  · intro me oppo c hS hd L hme
    injection hS with h1 h2 h3
    subst h1; subst h3
    exfalso
    cases hd with
    | searchL g ψ e =>
        unfold GuardianBot at hme
        simp only [ctxPlug, Prog.search.injEq] at hme
        have hcontra := hme.2.2.1
        exact const_ne_ctxPlug (by decide) L hcontra
    | iteL z aT other => unfold GuardianBot at hme; simp [ctxPlug] at hme
  · -- polarity plug: GuardianBot's C IS its else-slot — the matching `elseL`
    -- decomposition pays GuardianBot's own floor `k`; the `thenL` route dead-ends
    -- at the then-slot `.const .D ≠` any C-plug
    intro me oppo c hS hd L hme
    injection hS with h1 h2 h3; subst h1; subst h3
    cases hd with
    | thenL g ψ e =>
        simp only [plug2, GuardianBot, Prog.search.injEq] at hme
        obtain ⟨-, -, hplug, -⟩ := hme
        exfalso
        cases L with
        | nil => simp [plug2] at hplug
        | cons hd2 tl2 => cases hd2 <;> simp [plug2] at hplug
    | elseL g P' Q' c' q =>
        simp only [plug2, GuardianBot, Prog.search.injEq] at hme
        obtain ⟨rfl, -, -, -⟩ := hme
        simp only [layersCost, layerCost, c_node]
        omega

theorem gd_dupoc_guard_false (k : Nat) :
    proofSearch k (.plays (GuardianBot k) (DupocBot k) .C) = false := by
  cases h : proofSearch k (.plays (GuardianBot k) (DupocBot k) .C) with
  | true =>
      exact absurd ((proofSearch_spec k _).mp h)
        (fun hp => gd_no_provable_C_tail k k _ hp le_rfl (by simp))
  | false => rfl

theorem gd_DupocBot_D_vs_GuardianBot (k fuel : Nat) :
    play (fuel + 2) (DupocBot k) (GuardianBot k) = some .D := by
  have hg := gd_dupoc_guard_false k
  show eval (fuel + 2) (DupocBot k) (GuardianBot k) (DupocBot k) = some .D
  unfold DupocBot at hg ⊢
  simp [eval, Prog.subst, Formula.subst, hg]

-- === The outcome ===

theorem llm_outcome_GuardianBot_vs_DupocBot :
    ∃ k₂, ∀ k, k₂ < k →
      ∃ fuel, outcome fuel (GuardianBot k) (DupocBot k) = some (.C, .D) := by
  refine ⟨2, fun k hk => ⟨2, ?_⟩⟩
  have hA : play 2 (GuardianBot k) (DupocBot k) = some .C :=
    gd_GuardianBot_C_vs_DupocBot k 0 (by omega)
  have hB : play 2 (DupocBot k) (GuardianBot k) = some .D :=
    gd_DupocBot_D_vs_GuardianBot k 0
  exact outcome_of_plays _ _ _ _ _ hA hB

end PD.Theorems

