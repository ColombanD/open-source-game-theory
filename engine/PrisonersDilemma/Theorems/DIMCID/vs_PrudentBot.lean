import PrisonersDilemma.Bots.LlmGenerations.DIMCID
import PrisonersDilemma.Bots.LlmGenerations.PrudentBot
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Base.Asymptotics
import PrisonersDilemma.Theorems.PrudentBot.Helpers

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

/-! # DIMCID vs PrudentBot → (C, D)

DIMCID's guard vs PrudentBot is `A_C → D_PB`
  (A_C = "DIMCID plays C vs PB", D_PB = "PB plays D vs DIMCID").
Both `A_C` (DIMCID's else-play) and `D_PB` (PB's else-play) are certifiable only
through a `search_f` else-branch, which pays the full FLOOR `k` — so neither is
provable at budget ≤ k. Hence:
  * DIMCID's guard is unprovable (its consequent `D_PB` is floor-blocked) → DIMCID
    takes its `.const C` else-branch → cooperates.
  * PrudentBot's outer guard "DIMCID plays C vs PB" (= `A_C`) is floor-blocked → PB
    takes its `.const D` else-branch → defects.
DIMCID cooperates unconditionally (no threshold flip); PB defects because DIMCID's
cooperation is Gödelian-unprovable. Outcome `(C, D)`.  -/

-- === Census 1: "PrudentBot plays D vs DIMCID" is unprovable at budget k. ===
theorem dp_no_provable_pbD (k : Nat) :
    ∀ K φ, Pf K φ → K ≤ k →
      TailTo (.plays (PrudentBot k) (DIMCID k) Action.D) φ → False := by
  intro K φ hp hK htail
  refine no_provable_tailToS_floor k (· = .plays (PrudentBot k) (DIMCID k) Action.D)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ K φ hp hK ((TailToS_singleton _ φ).2 htail)
  · rintro φ' rfl; exact ⟨_, _, _, rfl⟩
  · rintro K' hK' φ' rfl hA
    cases hA with
    | mk hpp hn =>
      unfold PrudentBot at hpp
      cases hpp with
      | search_t hg hbr =>
          cases hbr with
          | search_t hg2 hbr2 => cases hbr2
          | search_f hneg2 hbr2 => simp only [c_node, c_guard] at hn; omega
      | search_f hneg hbr => simp only [c_node] at hn; omega
  · rintro me oppo c hS g ψ b hme
    injection hS with h1 h2 h3; subst h1; subst h3
    unfold PrudentBot at hme; simp only [Prog.search.injEq] at hme
    exact absurd hme.2.2.1 (by simp)
  · rintro me oppo c hS p q hme
    injection hS with h1 h2 h3; subst h1; simp [PrudentBot] at hme
  · rintro me oppo c hS p q hme
    injection hS with h1 h2 h3; subst h1; simp [PrudentBot] at hme
  · rintro me oppo c hS g ψ b hme
    injection hS with h1 h2 h3; subst h1; simp [PrudentBot] at hme
  · rintro z a' g ψ c0 c1 q oppo hS
    injection hS with h1 h2 h3; simp [PrudentBot] at h1
  · rintro me oppo c hS k₁ ψ₁ k₂ ψ₂ c1 q hme
    injection hS with h1 h2 h3; subst h1; subst h3
    unfold PrudentBot at hme; simp only [Prog.search.injEq] at hme
    exact absurd hme.2.2.1 (by simp [DefectBot])
  · rintro me oppo c hS L hme
    injection hS with h1 h2 h3; subst h1; subst h3
    cases L with
    | nil => simp [searchPlug, PrudentBot] at hme
    | cons hd tl =>
        obtain ⟨g, ψ, e⟩ := hd
        simp only [searchPlug, PrudentBot, Prog.search.injEq] at hme
        obtain ⟨-, -, hinner, -⟩ := hme
        cases tl with
        | nil => simp [searchPlug] at hinner
        | cons hd2 tl2 =>
            obtain ⟨g2, ψ2, e2⟩ := hd2
            simp only [searchPlug, Prog.search.injEq] at hinner
            obtain ⟨-, -, hinner2, -⟩ := hinner
            exact absurd hinner2
              (by rw [searchPlug_eq_ctxPlug]; exact const_ne_ctxPlug (by decide) _)
  · rintro me oppo c hS hd L hme
    injection hS with h1 h2 h3; subst h1; subst h3
    cases hd with
    | searchL g ψ e =>
        simp only [ctxPlug, PrudentBot, Prog.search.injEq] at hme
        obtain ⟨rfl, rfl, hplug, rfl⟩ := hme
        exfalso
        cases L with
        | nil => simp [ctxPlug] at hplug
        | cons hd2 tl2 =>
            cases hd2 with
            | searchL g2 ψ2 e2 =>
                simp only [ctxPlug, Prog.search.injEq] at hplug
                obtain ⟨-, -, hinner, -⟩ := hplug
                exact absurd hinner (const_ne_ctxPlug (by decide) tl2)
            | iteL z2 aT2 other2 => simp [ctxPlug] at hplug
    | iteL z aT other => simp [ctxPlug, PrudentBot] at hme
  · -- polarity plug: PrudentBot's D-plays ARE else-slots — every matching
    -- decomposition routes through an `elseL` layer carrying PrudentBot's own
    -- floor `k`, so `layersCost > k`; the all-`thenL` route dead-ends at the
    -- inner then-slot `.const C ≠` any D-plug
    rintro me oppo c hS hd L hme
    injection hS with h1 h2 h3; subst h1; subst h3
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

-- === Census 2: "DIMCID plays C vs PrudentBot" is unprovable at budget k. ===
theorem dp_no_provable_dimcidC (k : Nat) :
    ∀ K φ, Pf K φ → K ≤ k →
      TailTo (.plays (DIMCID k) (PrudentBot k) Action.C) φ → False := by
  intro K φ hp hK htail
  refine no_provable_tailToS_floor k (· = .plays (DIMCID k) (PrudentBot k) Action.C)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ K φ hp hK ((TailToS_singleton _ φ).2 htail)
  · rintro φ' rfl; exact ⟨_, _, _, rfl⟩
  · rintro K' hK' φ' rfl hA
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
  · -- polarity plug: DIMCID's guard is an `.impl` — no `elseL` layer can match it,
    -- and the then-slot holds `.const D ≠` any C-plug
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

-- === DIMCID cooperates against PrudentBot ===
theorem dp_dimcid_guard_not_provable (k : Nat) :
    ¬ Pf k (.impl (.plays (DIMCID k) (PrudentBot k) Action.C)
                  (.plays (PrudentBot k) (DIMCID k) Action.D)) := by
  intro h
  refine dp_no_provable_pbD k k _ h le_rfl ?_
  refine ⟨rfl, ?_⟩
  intro hA
  simp only [TailTo] at hA
  exact absurd hA (by simp [PrudentBot, DIMCID])

theorem dp_proofSearch_false_dimcid (k : Nat) :
    proofSearch k
      ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.D)).subst
        (DIMCID k) (PrudentBot k)) = false := by
  show proofSearch k
      (.impl (.plays (DIMCID k) (PrudentBot k) Action.C)
             (.plays (PrudentBot k) (DIMCID k) Action.D)) = false
  cases hps : proofSearch k
      (.impl (.plays (DIMCID k) (PrudentBot k) Action.C)
             (.plays (PrudentBot k) (DIMCID k) Action.D)) with
  | false => rfl
  | true => exact absurd ((proofSearch_spec k _).1 hps) (dp_dimcid_guard_not_provable k)

theorem DIMCID_plays_C_against_PrudentBot (k fuel : Nat) :
    play (fuel + 2) (DIMCID k) (PrudentBot k) = some .C := by
  have hg := dp_proofSearch_false_dimcid k
  show (if proofSearch k
            ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.D)).subst
              (DIMCID k) (PrudentBot k))
          then eval (fuel + 1) (DIMCID k) (PrudentBot k) (.const Action.D)
          else eval (fuel + 1) (DIMCID k) (PrudentBot k) (.const Action.C)) = some .C
  rw [hg]; simp [eval]

-- === PrudentBot defects against DIMCID ===
theorem dp_pb_outer_not_provable (k : Nat) :
    ¬ Pf k (.plays (DIMCID k) (PrudentBot k) Action.C) := by
  intro h
  exact dp_no_provable_dimcidC k k _ h le_rfl (by simp [TailTo])

theorem dp_proofSearch_false_pb_outer (k : Nat) :
    proofSearch k (.plays (DIMCID k) (PrudentBot k) Action.C) = false := by
  cases hps : proofSearch k (.plays (DIMCID k) (PrudentBot k) Action.C) with
  | false => rfl
  | true => exact absurd ((proofSearch_spec k _).1 hps) (dp_pb_outer_not_provable k)

theorem PrudentBot_plays_D_against_DIMCID (k fuel : Nat) :
    play (fuel + 2) (PrudentBot k) (DIMCID k) = some .D :=
  PrudentBot_plays_D_of_search_false k fuel (DIMCID k)
    (dp_proofSearch_false_pb_outer k)

-- === Final theorem ===
theorem llm_outcome_DIMCID_vs_PrudentBot :
    ∃ k₂, ∀ k, k₂ < k →
      ∃ fuel, outcome fuel (DIMCID k) (PrudentBot k) = some (.C, .D) := by
  refine ⟨0, fun k _ => ⟨2, ?_⟩⟩
  have hA : play 2 (DIMCID k) (PrudentBot k) = some .C :=
    DIMCID_plays_C_against_PrudentBot k 0
  have hB : play 2 (PrudentBot k) (DIMCID k) = some .D :=
    PrudentBot_plays_D_against_DIMCID k 0
  exact outcome_of_plays _ _ _ _ _ hA hB

end PD.Theorems
