import PrisonersDilemma.Bots.LlmGenerations.GuardianBot
import PrisonersDilemma.Bots.LlmGenerations.PrudentBot
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Dynamics
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.Base.Exclusion
import PrisonersDilemma.Theorems.PrudentBot.Helpers
import PrisonersDilemma.Theorems.GuardianBot.Helpers

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

/-! # GuardianBot vs PrudentBot — the mutual FLOOR case.

Both guards are TRUE but unprovable at budget k (certificates pay the `search_f`
floor `≥ k`), so each bot falls to its else-branch:
* GuardianBot's guard "PrudentBot bullies CooperateBot" is true (PrudentBot plays D
  vs `.bot CooperateBot`) but the certificate costs ≥ k → GuardianBot COOPERATES.
* PrudentBot's outer guard "GuardianBot cooperates with me" is true (GuardianBot
  cooperates) but that C is GuardianBot's else-play, cost ≥ k → PrudentBot DEFECTS.
Outcome: (C, D). -/

-- ══ Obligation 1: GuardianBot's guard is unprovable at budget k ══

theorem gvp_prudent_atom_kill (k K : Nat) (hK : K ≤ k) :
    ¬ AtomProvable K (.plays (PrudentBot k) (.bot CooperateBot) .D) := by
  intro hA
  unfold PrudentBot at hA
  cases hA with
  | mk hpp hn =>
    cases hpp with
    | search_t hProv hbr =>
        cases hbr with
        | search_t hP2 hbr2 => cases hbr2
        | search_f hneg2 hbr2 => simp only [c_node, c_guard, numCost] at hn; omega
    | search_f hneg hbr => simp only [c_node] at hn; omega

theorem gvp_no_Pf_prudent_D (k K : Nat) (φ : Formula) (hp : Pf K φ) (hK : K ≤ k)
    (ht : TailTo (.plays (PrudentBot k) (.bot CooperateBot) .D) φ) : False := by
  refine no_provable_tailToS_floor k (· = .plays (PrudentBot k) (.bot CooperateBot) .D)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ K φ hp hK ((TailToS_singleton _ φ).2 ht)
  · rintro φ' rfl; exact ⟨_, _, _, rfl⟩
  · rintro K' hK' φ' rfl; exact gvp_prudent_atom_kill k K' hK'
  · rintro me oppo c heq g ψ b hme
    injection heq with h1 h2 h3; subst h1; subst h2; subst h3
    simp [PrudentBot] at hme
  · rintro me oppo c heq p q hme
    injection heq with h1 h2 h3; subst h1
    simp [PrudentBot] at hme
  · rintro me oppo c heq p q hme
    injection heq with h1 h2 h3; subst h1
    simp [PrudentBot] at hme
  · rintro me oppo c heq g ψ b hme
    injection heq with h1 h2 h3; subst h1
    simp [PrudentBot] at hme
  · rintro z a' g ψ c0 c1 q oppo heq
    injection heq with h1 h2 h3
    simp [PrudentBot] at h1
  · rintro me oppo c heq k₁ ψ₁ k₂ ψ₂ c1 q hme
    injection heq with h1 h2 h3; subst h1; subst h3
    unfold PrudentBot at hme
    injection hme with e1 e2 e3 e4
    injection e3 with f1 f2 f3 f4
    exact absurd f3 (by decide)
  · rintro me oppo c heq L hme
    injection heq with h1 h2 h3; subst h1; subst h3
    unfold PrudentBot at hme
    cases L with
    | nil => simp [searchPlug] at hme
    | cons hd tl =>
      obtain ⟨g, ψ, e⟩ := hd
      simp only [searchPlug, Prog.search.injEq] at hme
      cases tl with
      | nil => simp [searchPlug] at hme
      | cons hd2 tl2 =>
        obtain ⟨g2, ψ2, e2⟩ := hd2
        simp only [searchPlug, Prog.search.injEq] at hme
        cases tl2 with
        | nil => simp [searchPlug] at hme
        | cons hd3 tl3 => obtain ⟨g3, ψ3, e3⟩ := hd3; simp [searchPlug] at hme
  · rintro me oppo c heq hd L hme
    injection heq with h1 h2 h3; subst h1; subst h3
    unfold PrudentBot at hme
    cases hd with
    | searchL g ψ e =>
      simp only [ctxPlug, Prog.search.injEq] at hme
      cases L with
      | nil => simp [ctxPlug] at hme
      | cons hd2 tl2 =>
        cases hd2 with
        | searchL g2 ψ2 e2 =>
          simp only [ctxPlug, Prog.search.injEq] at hme
          cases tl2 with
          | nil => simp [ctxPlug] at hme
          | cons hd3 tl3 =>
            cases hd3 with
            | searchL g3 ψ3 e3 => simp [ctxPlug] at hme
            | iteL z3 aT3 o3 => simp [ctxPlug] at hme
        | iteL z2 aT2 o2 => simp [ctxPlug] at hme
    | iteL z aT other => simp [ctxPlug] at hme
  · -- polarity plug: PrudentBot's D-plays ARE else-slots — every matching
    -- decomposition routes through an `elseL` layer carrying PrudentBot's own
    -- floor `k`; the all-`thenL` route dead-ends at the inner then-slot `.const .C`
    rintro me oppo c heq hd L hme
    injection heq with h1 h2 h3; subst h1; subst h3
    cases hd with
    | thenL g ψ e =>
        simp only [plug2, PrudentBot, Prog.search.injEq] at hme
        obtain ⟨rfl, rfl, hplug, rfl⟩ := hme
        cases L with
        | nil => simp [plug2] at hplug
        | cons hd2 tl2 =>
            cases hd2 with
            | thenL g2 ψ2 e2 =>
                exfalso
                simp only [plug2, Prog.search.injEq] at hplug
                obtain ⟨-, -, hplug2, -⟩ := hplug
                cases tl2 with
                | nil => simp [plug2] at hplug2
                | cons hd3 tl3 => cases hd3 <;> simp [plug2] at hplug2
            | elseL g2 P2 Q2 c2 q2 =>
                simp only [plug2, Prog.search.injEq] at hplug
                obtain ⟨rfl, -, -, -⟩ := hplug
                simp only [layersCost, layerCost, c_node]
                omega
    | elseL g P' Q' c' q =>
        simp only [plug2, PrudentBot, Prog.search.injEq] at hme
        obtain ⟨rfl, -, -, -⟩ := hme
        simp only [layersCost, layerCost, c_node]
        omega

theorem gvp_guardian_guard_false (k : Nat) :
    proofSearch k (.plays (PrudentBot k) (.bot CooperateBot) .D) = false := by
  cases h : proofSearch k (.plays (PrudentBot k) (.bot CooperateBot) .D) with
  | true =>
      exact absurd ((proofSearch_spec _ _).1 h)
        (fun hp => gvp_no_Pf_prudent_D k k _ hp le_rfl rfl)
  | false => rfl

-- ══ Obligation 2: PrudentBot's outer guard is unprovable at budget k ══

theorem pvg_guardian_atom_kill (k K : Nat) (hK : K ≤ k) :
    ¬ AtomProvable K (.plays (GuardianBot k) (PrudentBot k) .C) := by
  intro hA
  unfold GuardianBot at hA
  cases hA with
  | mk hpp hn =>
    cases hpp with
    | search_t hProv hbr => cases hbr
    | search_f hneg hbr => simp only [c_node] at hn; omega

theorem pvg_no_Pf_guardian_C (k K : Nat) (φ : Formula) (hp : Pf K φ) (hK : K ≤ k)
    (ht : TailTo (.plays (GuardianBot k) (PrudentBot k) .C) φ) : False := by
  refine no_provable_tailToS_floor k (· = .plays (GuardianBot k) (PrudentBot k) .C)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ K φ hp hK ((TailToS_singleton _ φ).2 ht)
  · rintro φ' rfl; exact ⟨_, _, _, rfl⟩
  · rintro K' hK' φ' rfl; exact pvg_guardian_atom_kill k K' hK'
  · rintro me oppo c heq g ψ b hme
    injection heq with h1 h2 h3; subst h1; subst h2; subst h3
    unfold GuardianBot at hme
    injection hme with e1 e2 e3 e4
    exact absurd e3 (by decide)
  · rintro me oppo c heq p q hme
    injection heq with h1 h2 h3; subst h1
    simp [GuardianBot] at hme
  · rintro me oppo c heq p q hme
    injection heq with h1 h2 h3; subst h1
    simp [GuardianBot] at hme
  · rintro me oppo c heq g ψ b hme
    injection heq with h1 h2 h3; subst h1
    simp [GuardianBot] at hme
  · rintro z a' g ψ c0 c1 q oppo heq
    injection heq with h1 h2 h3
    simp [GuardianBot] at h1
  · rintro me oppo c heq k₁ ψ₁ k₂ ψ₂ c1 q hme
    injection heq with h1 h2 h3; subst h1
    simp [GuardianBot] at hme
  · rintro me oppo c heq L hme
    injection heq with h1 h2 h3; subst h1; subst h3
    unfold GuardianBot at hme
    cases L with
    | nil => simp [searchPlug] at hme
    | cons hd tl =>
      obtain ⟨g, ψ, e⟩ := hd
      simp only [searchPlug, Prog.search.injEq] at hme
      cases tl with
      | nil => simp [searchPlug] at hme
      | cons hd2 tl2 => obtain ⟨g2, ψ2, e2⟩ := hd2; simp [searchPlug] at hme
  · rintro me oppo c heq hd L hme
    injection heq with h1 h2 h3; subst h1; subst h3
    unfold GuardianBot at hme
    cases hd with
    | searchL g ψ e =>
      simp only [ctxPlug, Prog.search.injEq] at hme
      cases L with
      | nil => simp [ctxPlug] at hme
      | cons hd2 tl2 =>
        cases hd2 with
        | searchL g2 ψ2 e2 => simp [ctxPlug] at hme
        | iteL z2 aT2 o2 => simp [ctxPlug] at hme
    | iteL z aT other => simp [ctxPlug] at hme
  · -- polarity plug: GuardianBot's C IS its else-slot — the matching `elseL`
    -- decomposition pays GuardianBot's own floor `k`; the `thenL` route dead-ends
    -- at the then-slot `.const .D ≠` any C-plug
    rintro me oppo c heq hd L hme
    injection heq with h1 h2 h3; subst h1; subst h3
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

theorem pvg_prudent_guard_false (k : Nat) :
    proofSearch k (.plays (GuardianBot k) (PrudentBot k) .C) = false := by
  cases h : proofSearch k (.plays (GuardianBot k) (PrudentBot k) .C) with
  | true =>
      exact absurd ((proofSearch_spec _ _).1 h)
        (fun hp => pvg_no_Pf_guardian_C k k _ hp le_rfl rfl)
  | false => rfl

-- ══ Assemble the plays and outcome ══

theorem gvp_guardian_plays_C (k fuel : Nat) :
    play (fuel + 2) (GuardianBot k) (PrudentBot k) = some .C := by
  have hg := gvp_guardian_guard_false k
  show eval (fuel + 2) (GuardianBot k) (PrudentBot k) (GuardianBot k) = some .C
  unfold GuardianBot
  simp [eval, Prog.subst, Formula.subst, hg]

theorem gvp_prudent_plays_D (k fuel : Nat) :
    play (fuel + 2) (PrudentBot k) (GuardianBot k) = some .D :=
  PrudentBot_plays_D_of_search_false k fuel (GuardianBot k) (pvg_prudent_guard_false k)

theorem llm_outcome_GuardianBot_vs_PrudentBot :
    ∃ k₂, ∀ k, k₂ < k →
      ∃ fuel, outcome fuel (GuardianBot k) (PrudentBot k) = some (.C, .D) := by
  refine ⟨0, fun k _ => ⟨2, ?_⟩⟩
  have hA : play 2 (GuardianBot k) (PrudentBot k) = some .C := gvp_guardian_plays_C k 0
  have hB : play 2 (PrudentBot k) (GuardianBot k) = some .D := gvp_prudent_plays_D k 0
  exact outcome_of_plays _ _ _ _ _ hA hB

end PD.Theorems
