import PrisonersDilemma.Bots.LlmGenerations.CIMCIC
import PrisonersDilemma.Bots.LlmGenerations.DIMCID
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Base.Asymptotics

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

/-- α = DIMCID plays C vs CIMCIC (DIMCID's else-play). Unprovable-tailed at budget k,
    via the SET kernel with a singleton set (DIMCID has const branches, so the simple
    `no_provable_tailTo_floor` wrapper does not apply — we need the action-refined kill). -/
theorem cd_no_provable_alpha (k : Nat) :
    ∀ K φ, Pf K φ → K ≤ k →
      TailTo (.plays (DIMCID k) (CIMCIC k) Action.C) φ → False := by
  intro K φ hp hK htail
  refine no_provable_tailToS_floor k (· = .plays (DIMCID k) (CIMCIC k) Action.C)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ K φ hp hK ((TailToS_singleton _ φ).2 htail)
  · rintro φ' rfl; exact ⟨_, _, _, rfl⟩
  · -- atom killer: DIMCID plays C is its else-branch; cert must be search_f → floor
    rintro K' hK' φ' rfl hA
    cases hA with
    | mk hpp hn =>
      unfold DIMCID at hpp
      cases hpp with
      | search_t hg hbr => cases hbr
      | search_f hneg hbr => simp only [c_node] at hn; omega
  · rintro me oppo c hS g ψ b hme
    injection hS with h1 h2 h3; subst h1; subst h3
    unfold DIMCID at hme; simp only [Prog.search.injEq] at hme
    exact absurd hme.2.2.1 (by decide)
  · rintro me oppo c hS p q hme
    injection hS with h1 h2 h3; subst h1; simp [DIMCID] at hme
  · rintro me oppo c hS p q hme
    injection hS with h1 h2 h3; subst h1; simp [DIMCID] at hme
  · rintro me oppo c hS g ψ b hme
    injection hS with h1 h2 h3; subst h1; simp [DIMCID] at hme
  · rintro z a' g ψ c0 c1 q oppo hS
    injection hS with h1 h2 h3; simp [DIMCID] at h1
  · rintro me oppo c hS k₁ ψ₁ k₂ ψ₂ c1 q hme
    injection hS with h1 h2 h3; subst h1; subst h3
    unfold DIMCID at hme; simp only [Prog.search.injEq] at hme
    exact absurd hme.2.2.1 (by simp)
  · rintro me oppo c hS L hme
    injection hS with h1 h2 h3; subst h1; subst h3
    cases L with
    | nil => simp [searchPlug, DIMCID] at hme
    | cons hd tl =>
        obtain ⟨g, ψ, e⟩ := hd
        simp only [searchPlug, DIMCID, Prog.search.injEq] at hme
        cases tl with
        | nil => simp [searchPlug] at hme
        | cons hd2 tl2 => obtain ⟨g2, ψ2, e2⟩ := hd2; simp [searchPlug] at hme
  · rintro me oppo c hS hd L hme
    injection hS with h1 h2 h3; subst h1; subst h3
    cases hd with
    | searchL g ψ e =>
        simp only [ctxPlug, DIMCID, Prog.search.injEq] at hme
        obtain ⟨rfl, rfl, hplug, rfl⟩ := hme
        cases L with
        | nil => simp [ctxPlug] at hplug
        | cons hd2 tl2 => cases hd2 <;> simp [ctxPlug] at hplug
    | iteL z aT other => simp [ctxPlug, DIMCID] at hme
  · -- polarity plug: DIMCID's guard is an `.impl` — no `elseL` layer can match it
    rintro me oppo c hS hd L hme
    injection hS with h1 h2 h3; subst h1; subst h3
    exfalso
    cases hd with
    | thenL g ψ e =>
        simp only [plug2, DIMCID, Prog.search.injEq] at hme
        obtain ⟨-, -, hplug, -⟩ := hme
        cases L with
        | nil => simp [plug2] at hplug
        | cons hd2 tl2 => cases hd2 <;> simp [plug2] at hplug
    | elseL g P' Q' c' q =>
        simp only [plug2, DIMCID, Prog.search.injEq] at hme
        exact absurd hme.2.1 (by simp)

/-- β = CIMCIC plays D vs DIMCID (CIMCIC's else-play). Unprovable-tailed at budget k. -/
theorem cd_no_provable_beta (k : Nat) :
    ∀ K φ, Pf K φ → K ≤ k →
      TailTo (.plays (CIMCIC k) (DIMCID k) Action.D) φ → False := by
  intro K φ hp hK htail
  refine no_provable_tailToS_floor k (· = .plays (CIMCIC k) (DIMCID k) Action.D)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ K φ hp hK ((TailToS_singleton _ φ).2 htail)
  · rintro φ' rfl; exact ⟨_, _, _, rfl⟩
  · rintro K' hK' φ' rfl hA
    cases hA with
    | mk hpp hn =>
      unfold CIMCIC at hpp
      cases hpp with
      | search_t hg hbr => cases hbr
      | search_f hneg hbr => simp only [c_node] at hn; omega
  · rintro me oppo c hS g ψ b hme
    injection hS with h1 h2 h3; subst h1; subst h3
    unfold CIMCIC at hme; simp only [Prog.search.injEq] at hme
    exact absurd hme.2.2.1 (by decide)
  · rintro me oppo c hS p q hme
    injection hS with h1 h2 h3; subst h1; simp [CIMCIC] at hme
  · rintro me oppo c hS p q hme
    injection hS with h1 h2 h3; subst h1; simp [CIMCIC] at hme
  · rintro me oppo c hS g ψ b hme
    injection hS with h1 h2 h3; subst h1; simp [CIMCIC] at hme
  · rintro z a' g ψ c0 c1 q oppo hS
    injection hS with h1 h2 h3; simp [CIMCIC] at h1
  · rintro me oppo c hS k₁ ψ₁ k₂ ψ₂ c1 q hme
    injection hS with h1 h2 h3; subst h1; subst h3
    unfold CIMCIC at hme; simp only [Prog.search.injEq] at hme
    exact absurd hme.2.2.1 (by simp)
  · rintro me oppo c hS L hme
    injection hS with h1 h2 h3; subst h1; subst h3
    cases L with
    | nil => simp [searchPlug, CIMCIC] at hme
    | cons hd tl =>
        obtain ⟨g, ψ, e⟩ := hd
        simp only [searchPlug, CIMCIC, Prog.search.injEq] at hme
        cases tl with
        | nil => simp [searchPlug] at hme
        | cons hd2 tl2 => obtain ⟨g2, ψ2, e2⟩ := hd2; simp [searchPlug] at hme
  · rintro me oppo c hS hd L hme
    injection hS with h1 h2 h3; subst h1; subst h3
    cases hd with
    | searchL g ψ e =>
        simp only [ctxPlug, CIMCIC, Prog.search.injEq] at hme
        obtain ⟨rfl, rfl, hplug, rfl⟩ := hme
        cases L with
        | nil => simp [ctxPlug] at hplug
        | cons hd2 tl2 => cases hd2 <;> simp [ctxPlug] at hplug
    | iteL z aT other => simp [ctxPlug, CIMCIC] at hme
  · -- polarity plug: CIMCIC's guard is an `.impl` — no `elseL` layer can match it
    rintro me oppo c hS hd L hme
    injection hS with h1 h2 h3; subst h1; subst h3
    exfalso
    cases hd with
    | thenL g ψ e =>
        simp only [plug2, CIMCIC, Prog.search.injEq] at hme
        obtain ⟨-, -, hplug, -⟩ := hme
        cases L with
        | nil => simp [plug2] at hplug
        | cons hd2 tl2 => cases hd2 <;> simp [plug2] at hplug
    | elseL g P' Q' c' q =>
        simp only [plug2, CIMCIC, Prog.search.injEq] at hme
        exact absurd hme.2.1 (by simp)

theorem cd_cimcic_guard_not_provable (k : Nat) :
    ¬ Pf k (.impl (.plays (CIMCIC k) (DIMCID k) Action.C)
                  (.plays (DIMCID k) (CIMCIC k) Action.C)) := by
  intro h
  refine cd_no_provable_alpha k k _ h le_rfl ?_
  refine ⟨rfl, ?_⟩
  intro hA
  simp only [TailTo] at hA
  exact absurd hA (by simp [CIMCIC, DIMCID])

theorem cd_dimcid_guard_not_provable (k : Nat) :
    ¬ Pf k (.impl (.plays (DIMCID k) (CIMCIC k) Action.C)
                  (.plays (CIMCIC k) (DIMCID k) Action.D)) := by
  intro h
  refine cd_no_provable_beta k k _ h le_rfl ?_
  refine ⟨rfl, ?_⟩
  intro hA
  simp only [TailTo] at hA
  exact absurd hA (by simp [CIMCIC, DIMCID])

theorem proofSearch_false_cimcic (k : Nat) :
    proofSearch k
      ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.C)).subst
        (CIMCIC k) (DIMCID k)) = false := by
  cases hps : proofSearch k
      ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.C)).subst
        (CIMCIC k) (DIMCID k)) with
  | false => rfl
  | true =>
      exact absurd ((proofSearch_spec k _).1 hps) (cd_cimcic_guard_not_provable k)

theorem proofSearch_false_dimcid (k : Nat) :
    proofSearch k
      ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.D)).subst
        (DIMCID k) (CIMCIC k)) = false := by
  cases hps : proofSearch k
      ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.D)).subst
        (DIMCID k) (CIMCIC k)) with
  | false => rfl
  | true =>
      exact absurd ((proofSearch_spec k _).1 hps) (cd_dimcid_guard_not_provable k)

theorem CIMCIC_plays_D_against_DIMCID (k fuel : Nat) :
    play (fuel + 2) (CIMCIC k) (DIMCID k) = some .D := by
  show (if proofSearch k
            ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.C)).subst
              (CIMCIC k) (DIMCID k))
          then eval (fuel + 1) (CIMCIC k) (DIMCID k) (.const Action.C)
          else eval (fuel + 1) (CIMCIC k) (DIMCID k) (.const Action.D)) = some .D
  rw [proofSearch_false_cimcic k]; simp [eval]

theorem DIMCID_plays_C_against_CIMCIC (k fuel : Nat) :
    play (fuel + 2) (DIMCID k) (CIMCIC k) = some .C := by
  show (if proofSearch k
            ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.D)).subst
              (DIMCID k) (CIMCIC k))
          then eval (fuel + 1) (DIMCID k) (CIMCIC k) (.const Action.D)
          else eval (fuel + 1) (DIMCID k) (CIMCIC k) (.const Action.C)) = some .C
  rw [proofSearch_false_dimcid k]; simp [eval]

theorem llm_outcome_CIMCIC_vs_DIMCID :
    ∃ k₂, ∀ k, k₂ < k →
      ∃ fuel, outcome fuel (CIMCIC k) (DIMCID k) = some (.D, .C) := by
  refine ⟨0, fun k _ => ⟨2, ?_⟩⟩
  have hA : play 2 (CIMCIC k) (DIMCID k) = some .D :=
    CIMCIC_plays_D_against_DIMCID k 0
  have hB : play 2 (DIMCID k) (CIMCIC k) = some .C :=
    DIMCID_plays_C_against_CIMCIC k 0
  exact outcome_of_plays _ _ _ _ _ hA hB

end PD.Theorems
