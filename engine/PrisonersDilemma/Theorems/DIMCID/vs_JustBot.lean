import PrisonersDilemma.Bots.LlmGenerations.DIMCID
import PrisonersDilemma.Bots.LlmGenerations.JustBot
import PrisonersDilemma.Bots.DupocBot
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.BaseTheorems

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

/-! # DIMCID vs JustBot → (C, D)

JustBot's guard vs DIMCID is "DIMCID plays C vs `.bot (DupocBot k)`" — but DIMCID's
C-play is its ELSE-branch, certifiable only through `search_f`, which pays the full
floor `k`. So JustBot can never afford the certificate and defects.

DIMCID's guard vs JustBot is `A_C → J_D`
  (A_C = "DIMCID plays C vs JustBot", J_D = "JustBot plays D vs DIMCID").
`J_D` is JustBot's ELSE-play, again `search_f`-floor-blocked at budget ≤ k, so the
implication is unprovable and DIMCID takes its `.const C` else-branch.

DIMCID cooperates while its cooperation is Gödelian-invisible to JustBot's guard:
outcome `(C, D)` at every budget — the same floor shape as DIMCID vs PrudentBot. -/

-- === Census 1: "JustBot plays D vs DIMCID" is unprovable at budget k. ===
theorem dj_no_provable_justbotD (k : Nat) :
    ∀ K φ, Pf K φ → K ≤ k →
      TailTo (.plays (JustBot k) (DIMCID k) Action.D) φ → False := by
  intro K φ hp hK htail
  refine no_provable_tailToS_floor k (· = .plays (JustBot k) (DIMCID k) Action.D)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ K φ hp hK ((TailToS_singleton _ φ).2 htail)
  · rintro φ' rfl; exact ⟨_, _, _, rfl⟩
  · rintro K' hK' φ' rfl hA
    cases hA with
    | mk hpp hn =>
      unfold JustBot at hpp
      cases hpp with
      | search_t hg hbr => cases hbr
      | search_f hneg hbr => simp only [c_node] at hn; omega
  · rintro me oppo c hS g ψ b hme
    injection hS with h1 h2 h3; subst h1; subst h3
    unfold JustBot at hme; simp only [Prog.search.injEq] at hme
    exact absurd hme.2.2.1 (by decide)
  · rintro me oppo c hS p q hme
    injection hS with h1 h2 h3; subst h1; simp [JustBot] at hme
  · rintro me oppo c hS p q hme
    injection hS with h1 h2 h3; subst h1; simp [JustBot] at hme
  · rintro me oppo c hS g ψ b hme
    injection hS with h1 h2 h3; subst h1; simp [JustBot] at hme
  · rintro z a' g ψ c0 c1 q oppo hS
    injection hS with h1 h2 h3; simp [JustBot] at h1
  · rintro me oppo c hS k₁ ψ₁ k₂ ψ₂ c1 q hme
    injection hS with h1 h2 h3; subst h1; subst h3
    unfold JustBot at hme; simp only [Prog.search.injEq] at hme
    exact absurd hme.2.2.1 (by simp)
  · rintro me oppo c hS L hme
    injection hS with h1 h2 h3; subst h1; subst h3
    cases L with
    | nil => simp [searchPlug, JustBot] at hme
    | cons hd tl =>
        obtain ⟨g, ψ, e⟩ := hd
        simp only [searchPlug, JustBot, Prog.search.injEq] at hme
        cases tl with
        | nil => simp [searchPlug] at hme
        | cons hd2 tl2 => obtain ⟨g2, ψ2, e2⟩ := hd2; simp [searchPlug] at hme
  · rintro me oppo c hS hd L hme
    injection hS with h1 h2 h3; subst h1; subst h3
    cases hd with
    | searchL g ψ e =>
        simp only [ctxPlug, JustBot, Prog.search.injEq] at hme
        obtain ⟨rfl, rfl, hplug, rfl⟩ := hme
        cases L with
        | nil => simp [ctxPlug] at hplug
        | cons hd2 tl2 => cases hd2 <;> simp [ctxPlug] at hplug
    | iteL z aT other => simp [ctxPlug, JustBot] at hme

-- === Census 2: "DIMCID plays C vs .bot (DupocBot k)" is unprovable at budget k. ===
theorem dj_no_provable_dimcidC (k : Nat) :
    ∀ K φ, Pf K φ → K ≤ k →
      TailTo (.plays (DIMCID k) (.bot (DupocBot k)) Action.C) φ → False := by
  intro K φ hp hK htail
  refine no_provable_tailToS_floor k (· = .plays (DIMCID k) (.bot (DupocBot k)) Action.C)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ K φ hp hK ((TailToS_singleton _ φ).2 htail)
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

-- === DIMCID cooperates against JustBot ===
theorem dj_dimcid_guard_not_provable (k : Nat) :
    ¬ Pf k (.impl (.plays (DIMCID k) (JustBot k) Action.C)
                  (.plays (JustBot k) (DIMCID k) Action.D)) := by
  intro h
  refine dj_no_provable_justbotD k k _ h le_rfl ?_
  refine ⟨rfl, ?_⟩
  intro hA
  simp only [TailTo] at hA
  exact absurd hA (by simp [JustBot, DIMCID])

theorem dj_proofSearch_false_dimcid (k : Nat) :
    proofSearch k
      ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.D)).subst
        (DIMCID k) (JustBot k)) = false := by
  show proofSearch k
      (.impl (.plays (DIMCID k) (JustBot k) Action.C)
             (.plays (JustBot k) (DIMCID k) Action.D)) = false
  cases hps : proofSearch k
      (.impl (.plays (DIMCID k) (JustBot k) Action.C)
             (.plays (JustBot k) (DIMCID k) Action.D)) with
  | false => rfl
  | true => exact absurd ((proofSearch_spec k _).1 hps) (dj_dimcid_guard_not_provable k)

theorem DIMCID_plays_C_against_JustBot (k fuel : Nat) :
    play (fuel + 2) (DIMCID k) (JustBot k) = some .C := by
  have hg := dj_proofSearch_false_dimcid k
  show (if proofSearch k
            ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.D)).subst
              (DIMCID k) (JustBot k))
          then eval (fuel + 1) (DIMCID k) (JustBot k) (.const Action.D)
          else eval (fuel + 1) (DIMCID k) (JustBot k) (.const Action.C)) = some .C
  rw [hg]; simp [eval]

-- === JustBot defects against DIMCID ===
theorem dj_justbot_guard_not_provable (k : Nat) :
    ¬ Pf k (.plays (DIMCID k) (.bot (DupocBot k)) Action.C) := by
  intro h
  exact dj_no_provable_dimcidC k k _ h le_rfl (by simp [TailTo])

theorem dj_proofSearch_false_justbot (k : Nat) :
    proofSearch k (.plays (DIMCID k) (.bot (DupocBot k)) Action.C) = false := by
  cases hps : proofSearch k (.plays (DIMCID k) (.bot (DupocBot k)) Action.C) with
  | false => rfl
  | true => exact absurd ((proofSearch_spec k _).1 hps) (dj_justbot_guard_not_provable k)

theorem JustBot_plays_D_against_DIMCID (k fuel : Nat) :
    play (fuel + 2) (JustBot k) (DIMCID k) = some .D := by
  have hg := dj_proofSearch_false_justbot k
  show eval (fuel + 2) (JustBot k) (DIMCID k) (JustBot k) = some .D
  unfold JustBot
  simp [eval, Prog.subst, Formula.subst, hg]

-- === Final theorem ===
theorem llm_outcome_DIMCID_vs_JustBot :
    ∃ k₂, ∀ k, k₂ < k →
      ∃ fuel, outcome fuel (DIMCID k) (JustBot k) = some (.C, .D) := by
  refine ⟨0, fun k _ => ⟨2, ?_⟩⟩
  have hA : play 2 (DIMCID k) (JustBot k) = some .C :=
    DIMCID_plays_C_against_JustBot k 0
  have hB : play 2 (JustBot k) (DIMCID k) = some .D :=
    JustBot_plays_D_against_DIMCID k 0
  exact outcome_of_plays _ _ _ _ _ hA hB

end PD.Theorems
