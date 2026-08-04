import PrisonersDilemma.Bots.LlmGenerations.GuardianBot
import PrisonersDilemma.Bots.LlmGenerations.JustBot
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Bots.DupocBot
import PrisonersDilemma.Dynamics
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.Base.Asymptotics
import PrisonersDilemma.Theorems.JustBot.Helpers
import PrisonersDilemma.Theorems.CooperateBot.Helpers

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

/-! # GuardianBot vs JustBot — outcome (C, D).

GuardianBot cooperates by default and JustBot never bullies CooperateBot, so
GuardianBot's punishment guard is refuted: GuardianBot cooperates (C).
JustBot demands a proof that GuardianBot cooperates vs `.bot (DupocBot k)`. That IS
true, but it is an ELSE-play of GuardianBot's own budget-`k` search (GuardianBot does
not prove DupocBot bullies CooperateBot), so its certificate pays the `search_f`
floor `> k` — JustBot at the same budget can never see it and defects (D). -/

/-! ## DupocBot side (feeds GuardianBot's guard against `.bot (DupocBot k)`). -/

theorem gjb_DupocBot_plays_C_vs_botCB (k : Nat) (hk : 2 ≤ k) :
    ∃ n, play n (DupocBot k) (.bot CooperateBot) = some .C := by
  have hg : proofSearch k (.plays (.bot CooperateBot) (DupocBot k) .C) = true := by
    refine (proofSearch_spec _ _).2 (Pf.atom ⟨PlaysProof.bot PlaysProof.const, ?_⟩)
    unfold c_leaf c_node; omega
  refine ⟨2, ?_⟩
  show eval 2 (DupocBot k) (.bot CooperateBot) (DupocBot k) = some .C
  unfold DupocBot
  show (if proofSearch k ((Formula.plays .opp .self Action.C).subst
          (.search k (Formula.plays .opp .self Action.C) (.const .C) (.const .D))
          (.bot CooperateBot))
        then eval 1 _ _ (.const Action.C) else eval 1 _ _ (.const Action.D)) = some .C
  rw [show (Formula.plays Prog.opp Prog.self Action.C).subst
        (.search k (Formula.plays Prog.opp Prog.self Action.C) (.const .C) (.const .D))
        (.bot CooperateBot)
      = Formula.plays (.bot CooperateBot)
          (.search k (Formula.plays Prog.opp Prog.self Action.C) (.const .C) (.const .D)) .C
      from rfl]
  rw [show (Prog.search k (Formula.plays Prog.opp Prog.self Action.C) (.const .C) (.const .D))
        = DupocBot k from rfl] at *
  rw [hg]; rfl

/-! ## The floor census: JustBot's guard against GuardianBot is unprovable at ≤ k. -/

theorem gjb_no_provable_Guardian_C_vs_botDupoc (k : Nat) :
    ∀ K φ, Pf K φ → K ≤ k →
      TailTo (.plays (GuardianBot k) (.bot (DupocBot k)) .C) φ → False := by
  intro K φ hp hK ht
  refine no_provable_tailToS_floor k (· = .plays (GuardianBot k) (.bot (DupocBot k)) .C)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ K φ hp hK ((TailToS_singleton _ φ).2 ht)
  · rintro φ' rfl; exact ⟨_, _, _, rfl⟩
  · intro K' hK' φ' rfl
    rintro ⟨hpp, hn⟩
    unfold GuardianBot at hpp
    cases hpp with
    | search_t hProv hbr => cases hbr
    | search_f hneg hbr => simp only [c_node] at hn; omega
  · intro me oppo c hS g ψ b hme
    injection hS with h1 h2 h3; subst h1; subst h3
    unfold GuardianBot at hme
    simp only [Prog.search.injEq] at hme
    obtain ⟨_, _, hthen, _⟩ := hme
    exact absurd hthen (by decide)
  · intro me oppo c hS p q hme
    injection hS with h1 h2 h3; subst h1
    unfold GuardianBot at hme; simp at hme
  · intro me oppo c hS p q hme
    injection hS with h1 h2 h3; subst h1
    unfold GuardianBot at hme; simp at hme
  · intro me oppo c hS g ψ b hme
    injection hS with h1 h2 h3; subst h1
    unfold GuardianBot at hme; simp at hme
  · intro z a' g ψ c0 c1 q oppo hS
    injection hS with h1 h2 h3
    unfold GuardianBot at h1; simp at h1
  · intro me oppo c hS k₁ ψ₁ k₂ ψ₂ c1 q hme
    injection hS with h1 h2 h3; subst h1
    unfold GuardianBot at hme; simp at hme
  · intro me oppo c hS L hme
    injection hS with h1 h2 h3; subst h1; subst h3
    cases L with
    | nil => unfold GuardianBot at hme; simp [searchPlug] at hme
    | cons hd tl =>
        obtain ⟨g, ψ, e⟩ := hd
        unfold GuardianBot at hme
        simp only [searchPlug, Prog.search.injEq] at hme
        obtain ⟨_, _, hthen, _⟩ := hme
        cases tl with
        | nil => simp [searchPlug] at hthen
        | cons hd2 tl2 => obtain ⟨g2, ψ2, e2⟩ := hd2; simp [searchPlug] at hthen
  · intro me oppo c hS hd L hme
    injection hS with h1 h2 h3; subst h1; subst h3
    exfalso
    cases hd with
    | searchL g ψ e =>
        unfold GuardianBot at hme
        simp only [ctxPlug, Prog.search.injEq] at hme
        obtain ⟨_, _, hthen, _⟩ := hme
        cases L with
        | nil => simp [ctxPlug] at hthen
        | cons hd2 tl2 =>
            cases hd2 with
            | searchL g2 ψ2 e2 => simp [ctxPlug] at hthen
            | iteL z2 a2 o2 => simp [ctxPlug] at hthen
    | iteL z a' o =>
        unfold GuardianBot at hme; simp [ctxPlug] at hme
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

/-- JustBot's guard against GuardianBot fails at budget k. -/
theorem gjb_JustBot_guard_vs_Guardian_false (k : Nat) :
    proofSearch k (.plays (GuardianBot k) (.bot (DupocBot k)) .C) = false := by
  cases h : proofSearch k (.plays (GuardianBot k) (.bot (DupocBot k)) .C) with
  | true =>
      exact absurd ((proofSearch_spec k _).mp h)
        (fun hp => gjb_no_provable_Guardian_C_vs_botDupoc k k _ hp le_rfl (by simp))
  | false => rfl

/-- JustBot defects against GuardianBot (guard starved by the floor). -/
theorem gjb_JustBot_plays_D_vs_Guardian (k fuel : Nat) :
    play (fuel + 2) (JustBot k) (GuardianBot k) = some .D := by
  have hg := gjb_JustBot_guard_vs_Guardian_false k
  show eval (fuel + 2) (JustBot k) (GuardianBot k) (JustBot k) = some .D
  unfold JustBot
  simp [eval, Prog.subst, Formula.subst, hg]

/-! ## LEFT: GuardianBot cooperates vs JustBot. -/

theorem gjb_JustBot_plays_C_vs_botCB (k fuel : Nat) (hk : 2 ≤ k) :
    play (fuel + 2) (JustBot k) (.bot CooperateBot) = some .C := by
  have hg : proofSearch k
      (.plays (.bot CooperateBot) (.bot (DupocBot k)) .C) = true := by
    refine (proofSearch_spec _ _).2 (Pf.atom ⟨PlaysProof.bot PlaysProof.const, ?_⟩)
    unfold c_leaf c_node; omega
  exact JustBot_plays_C_against_bot_CooperateBot k fuel hg

theorem gjb_JustBot_D_vs_botCB_false (k : Nat) (hk : 2 ≤ k) :
    ¬ (Formula.plays (JustBot k) (.bot CooperateBot) .D).interp := by
  rintro ⟨n, hn⟩
  have hC : play (n + 2) (JustBot k) (.bot CooperateBot) = some .C :=
    gjb_JustBot_plays_C_vs_botCB k n hk
  have hD : play (n + 2) (JustBot k) (.bot CooperateBot) = some .D :=
    eval_mono_le hn (n + 2) (by omega)
  rw [hC] at hD; simp at hD

theorem gjb_guardian_guard_vs_JustBot_false (k : Nat) (hk : 2 ≤ k) :
    proofSearch k (.plays (JustBot k) (.bot CooperateBot) .D) = false := by
  cases h : proofSearch k (.plays (JustBot k) (.bot CooperateBot) .D) with
  | true => exact absurd (proofSearch_sound _ _ h) (gjb_JustBot_D_vs_botCB_false k hk)
  | false => rfl

theorem gjb_GuardianBot_plays_C_vs_JustBot (k fuel : Nat) (hk : 2 ≤ k) :
    play (fuel + 2) (GuardianBot k) (JustBot k) = some .C := by
  have hg := gjb_guardian_guard_vs_JustBot_false k hk
  show eval (fuel + 2) (GuardianBot k) (JustBot k) (GuardianBot k) = some .C
  unfold GuardianBot
  simp [eval, Prog.subst, Formula.subst, hg]

/-! ## The outcome. -/

theorem llm_outcome_GuardianBot_vs_JustBot :
    ∃ k₂, ∀ k, k₂ < k →
      ∃ fuel, outcome fuel (GuardianBot k) (JustBot k) = some (.C, .D) := by
  refine ⟨2, fun k hk => ⟨2, ?_⟩⟩
  have hk2 : 2 ≤ k := by omega
  have hA : play 2 (GuardianBot k) (JustBot k) = some .C :=
    gjb_GuardianBot_plays_C_vs_JustBot k 0 hk2
  have hB : play 2 (JustBot k) (GuardianBot k) = some .D :=
    gjb_JustBot_plays_D_vs_Guardian k 0
  exact outcome_of_plays _ _ _ _ _ hA hB

end PD.Theorems
