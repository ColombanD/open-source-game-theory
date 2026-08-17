import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Base.Asymptotics
import PrisonersDilemma.Base.Helpers

import PrisonersDilemma.Bots.LlmGenerations.CIMCIC
import PrisonersDilemma.Bots.LlmGenerations.OptimBot

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

/-!
# CIMCIC vs OptimBot — the honest `(D, C)` outcome

CIMCIC's guard against OptimBot is `(CIMCIC plays C vs OptimBot) → (OptimBot plays C
vs CIMCIC)`.  The consequent `B = OptimBot plays C vs CIMCIC` is reached only through
OptimBot's fallback, i.e. through `search_f` else-branches — so every certificate for
`B` pays the `search_f` floor (`> k`), making `B` unprovable at budget `k`.  Hence
CIMCIC's guard (whose spine tail is `B`) is unprovable, and CIMCIC defects.  With
CIMCIC defecting, OptimBot's rung guards `CIMCIC plays C vs OptimBot` and `CIMCIC
plays D vs OptimBot` both fail (the first is semantically false; the second is a true
but floor-uncertifiable else-play), so OptimBot falls through to its fallback and
cooperates.  Outcome `(D, C)`.
-/

/-- Any certificate for `OptimBot plays C vs CIMCIC` costs more than `k`: every path
    to a `C`-constant in OptimBot passes a `search_f` else-branch, which pays the
    full failed budget `k`. -/
theorem optim_C_cert_cost (k : Nat) (O : Prog) :
    ∀ n, PlaysProof (OptimBot k k) O (OptimBot k k) Action.C n → k < n := by
  intro n cert
  unfold OptimBot at cert
  cases cert with
  | search_t hg hp =>
      cases hp with
      | search_t hg2 hp2 => cases hp2
      | search_f hneg2 hp2 => simp only [c_node] at *; omega
  | search_f hneg hp => simp only [c_node] at *; omega

/-- No `Pf` at budget `≤ k` concludes anything guarded-tailed at `B = OptimBot plays C
    vs CIMCIC` — the floor census over the singleton `{B}`. -/
theorem cimcic_optim_guard_B_unprov (k : Nat) :
    ∀ K φ, Pf K φ → K ≤ k →
      TailTo (.plays (OptimBot k k) (CIMCIC k) Action.C) φ → False := by
  intro K φ hp hK htail
  refine no_provable_tailToS_floor k (· = .plays (OptimBot k k) (CIMCIC k) Action.C)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ K φ hp hK ((TailToS_singleton _ φ).2 htail)
  · rintro φ' rfl; exact ⟨_, _, _, rfl⟩
  · rintro K' hK' φ' rfl hA
    cases hA with
    | mk hpp hn => have := optim_C_cert_cost k (CIMCIC k) _ hpp; omega
  · rintro me oppo c hS g ψ b hme
    injection hS with h1 h2 h3; subst h1; simp [OptimBot] at hme
  · rintro me oppo c hS p q hme
    injection hS with h1 h2 h3; subst h1; simp [OptimBot] at hme
  · rintro me oppo c hS p q hme
    injection hS with h1 h2 h3; subst h1; simp [OptimBot] at hme
  · rintro me oppo c hS g ψ b hme
    injection hS with h1 h2 h3; subst h1; simp [OptimBot] at hme
  · rintro z a' g ψ c0 c1 q oppo hS
    injection hS with h1 h2 h3; simp [OptimBot] at h1
  · rintro me oppo c hS k₁ ψ₁ k₂ ψ₂ c1 q hme
    injection hS with h1 h2 h3; subst h1; subst h3
    unfold OptimBot at hme; simp only [Prog.search.injEq] at hme
    exact absurd hme.2.2.1 (by simp)
  · rintro me oppo c hS L hme
    injection hS with h1 h2 h3; subst h1; subst h3
    cases L with
    | nil => simp [searchPlug, OptimBot] at hme
    | cons hd tl =>
        obtain ⟨g, ψ, e⟩ := hd
        simp only [searchPlug, OptimBot, Prog.search.injEq] at hme
        obtain ⟨_, _, hthen, _⟩ := hme
        cases tl with
        | nil => simp [searchPlug] at hthen
        | cons hd2 tl2 =>
            obtain ⟨g2, ψ2, e2⟩ := hd2
            simp only [searchPlug, Prog.search.injEq] at hthen
            obtain ⟨_, _, hthen2, _⟩ := hthen
            cases tl2 with
            | nil => simp [searchPlug] at hthen2
            | cons hd3 tl3 => obtain ⟨g3, ψ3, e3⟩ := hd3; simp [searchPlug] at hthen2
  · rintro me oppo c hS hd L hme
    injection hS with h1 h2 h3; subst h1; subst h3
    exfalso
    cases hd with
    | iteL z aT other => simp [ctxPlug, OptimBot] at hme
    | searchL g ψ e =>
        simp only [ctxPlug, OptimBot, Prog.search.injEq] at hme
        obtain ⟨_, _, hthen, _⟩ := hme
        cases L with
        | nil => simp [ctxPlug] at hthen
        | cons hd2 tl2 =>
            cases hd2 with
            | iteL z2 aT2 other2 => simp [ctxPlug] at hthen
            | searchL g2 ψ2 e2 =>
                simp only [ctxPlug, Prog.search.injEq] at hthen
                obtain ⟨_, _, hthen2, _⟩ := hthen
                cases tl2 with
                | nil => simp [ctxPlug] at hthen2
                | cons hd3 tl3 => cases hd3 <;> simp [ctxPlug] at hthen2
  · -- polarity plug: every else-crossing decomposition of OptimBot pays a full rung
    -- budget `k + c_node > k`; all-thenL decompositions dead-end in `.const D`
    rintro me oppo c hS hd L hme
    injection hS with h1 h2 h3; subst h1; subst h3
    cases hd with
    | elseL g P' Q' c' q =>
        simp only [plug2, OptimBot, Prog.search.injEq] at hme
        obtain ⟨rfl, -, -, -⟩ := hme
        simp only [layersCost, layerCost, c_node]
        omega
    | thenL g ψ e =>
        simp only [plug2, OptimBot, Prog.search.injEq] at hme
        obtain ⟨-, -, hplug, -⟩ := hme
        cases L with
        | nil => simp [plug2] at hplug
        | cons hd2 tl2 =>
            cases hd2 with
            | elseL g2 P2 Q2 c2 q2 =>
                simp only [plug2, Prog.search.injEq] at hplug
                obtain ⟨rfl, -, -, -⟩ := hplug
                simp only [layersCost, layerCost, c_node]
                omega
            | thenL g2 ψ2 e2 =>
                simp only [plug2, Prog.search.injEq] at hplug
                obtain ⟨-, -, hplug2, -⟩ := hplug
                exfalso
                cases tl2 with
                | nil => simp [plug2] at hplug2
                | cons hd3 tl3 => cases hd3 <;> simp [plug2] at hplug2

/-- `G3 = CIMCIC plays D vs OptimBot` — the true-but-uncertifiable else-play — is
    unprovable at budget `k`, via the `search_f` floor census. -/
theorem cimcic_optim_G3_unprov (k : Nat) :
    ∀ K φ, Pf K φ → K ≤ k →
      TailTo (.plays (CIMCIC k) (OptimBot k k) Action.D) φ → False := by
  intro K φ hp hK htail
  refine no_provable_tailToS_floor k (· = .plays (CIMCIC k) (OptimBot k k) Action.D)
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
        obtain ⟨_, _, hthen, _⟩ := hme
        cases tl with
        | nil => simp [searchPlug] at hthen
        | cons hd2 tl2 => obtain ⟨g2, ψ2, e2⟩ := hd2; simp [searchPlug] at hthen
  · rintro me oppo c hS hd L hme
    injection hS with h1 h2 h3; subst h1; subst h3
    exfalso
    cases hd with
    | iteL z aT other => simp [ctxPlug, CIMCIC] at hme
    | searchL g ψ e =>
        simp only [ctxPlug, CIMCIC, Prog.search.injEq] at hme
        obtain ⟨_, _, hthen, _⟩ := hme
        cases L with
        | nil => simp [ctxPlug] at hthen
        | cons hd2 tl2 => cases hd2 <;> simp [ctxPlug] at hthen
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

/-- CIMCIC's guard against OptimBot (`A → B`) is unprovable at budget `k`: its spine
    tail `B` is floor-unprovable. -/
theorem cimcic_optim_guard_unprov (k : Nat) :
    ¬ Pf k (.impl (.plays (CIMCIC k) (OptimBot k k) Action.C)
                  (.plays (OptimBot k k) (CIMCIC k) Action.C)) := by
  intro h
  refine cimcic_optim_guard_B_unprov k k _ h le_rfl ?_
  refine ⟨rfl, ?_⟩
  intro hA
  simp only [TailTo] at hA
  exact absurd hA (by simp [CIMCIC, OptimBot])

theorem cimcic_optim_proofSearch_false_guard (k : Nat) :
    proofSearch k
      ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.C)).subst
        (CIMCIC k) (OptimBot k k)) = false := by
  cases hps : proofSearch k
      ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.C)).subst
        (CIMCIC k) (OptimBot k k)) with
  | false => rfl
  | true =>
      have hpf : Pf k (.impl (.plays (CIMCIC k) (OptimBot k k) Action.C)
                             (.plays (OptimBot k k) (CIMCIC k) Action.C)) := by
        have := (proofSearch_spec _ _).1 hps
        simpa [Formula.subst] using this
      exact absurd hpf (cimcic_optim_guard_unprov k)

/-- CIMCIC defects against OptimBot: its guard is unprovable, so it takes the
    `.const .D` branch. -/
theorem CIMCIC_plays_D_against_OptimBot (k fuel : Nat) :
    play (fuel + 2) (CIMCIC k) (OptimBot k k) = some .D := by
  show (if proofSearch k
            ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.C)).subst
              (CIMCIC k) (OptimBot k k))
          then eval (fuel + 1) (CIMCIC k) (OptimBot k k) (.const Action.C)
          else eval (fuel + 1) (CIMCIC k) (OptimBot k k) (.const Action.D)) = some .D
  rw [cimcic_optim_proofSearch_false_guard k]; simp [eval]

/-- `CIMCIC plays C vs OptimBot` is semantically false (CIMCIC defects), hence
    unprovable. -/
theorem cimcic_optim_proofSearch_false_A (k : Nat) :
    proofSearch k (Formula.plays (CIMCIC k) (OptimBot k k) Action.C) = false := by
  cases hps : proofSearch k (Formula.plays (CIMCIC k) (OptimBot k k) Action.C) with
  | false => rfl
  | true =>
      exfalso
      obtain ⟨n, hn⟩ := Pf_sound _ _ ((proofSearch_spec _ _).1 hps)
      have hD : play (n + 2) (CIMCIC k) (OptimBot k k) = some .D :=
        CIMCIC_plays_D_against_OptimBot k n
      have hC : play (n + 2) (CIMCIC k) (OptimBot k k) = some .C :=
        eval_mono_le hn (n + 2) (by omega)
      rw [hD] at hC; cases hC

theorem cimcic_optim_proofSearch_false_G3 (k : Nat) :
    proofSearch k (Formula.plays (CIMCIC k) (OptimBot k k) Action.D) = false := by
  cases hps : proofSearch k (Formula.plays (CIMCIC k) (OptimBot k k) Action.D) with
  | false => rfl
  | true =>
      exact absurd (cimcic_optim_G3_unprov k k _ ((proofSearch_spec _ _).1 hps) le_rfl rfl) id

/-- OptimBot cooperates against CIMCIC: both rung guards (`CIMCIC plays C` and `CIMCIC
    plays D`) are unprovable, so OptimBot falls through every rung to its fallback. -/
theorem OptimBot_plays_C_against_CIMCIC (k fuel : Nat) :
    play (fuel + 5) (OptimBot k k) (CIMCIC k) = some .C := by
  show eval (fuel + 5) (OptimBot k k) (CIMCIC k) (OptimBot k k) = some .C
  have hG1 := cimcic_optim_proofSearch_false_A k
  have hG3 := cimcic_optim_proofSearch_false_G3 k
  conv_lhs => rw [OptimBot]
  simp only [eval, Prog.subst, Formula.subst]
  simp only [OptimBot] at hG1 hG3
  simp only [hG1, hG3, if_false, Bool.false_eq_true]

/-- **CIMCIC vs OptimBot: `(D, C)`** — CIMCIC defects (guard floor-unprovable),
    OptimBot cooperates (falls through to fallback). -/
theorem llm_outcome_CIMCIC_vs_OptimBot :
    ∃ k₂, ∀ k, k₂ < k →
      ∃ fuel, outcome fuel (CIMCIC k) (OptimBot k k) = some (.D, .C) := by
  refine ⟨0, fun k _ => ⟨5, ?_⟩⟩
  have hA : play 5 (CIMCIC k) (OptimBot k k) = some .D := by
    simpa using CIMCIC_plays_D_against_OptimBot k 3
  have hB : play 5 (OptimBot k k) (CIMCIC k) = some .C := by
    simpa using OptimBot_plays_C_against_CIMCIC k 0
  exact outcome_of_plays _ _ _ _ _ hA hB

end PD.Theorems
