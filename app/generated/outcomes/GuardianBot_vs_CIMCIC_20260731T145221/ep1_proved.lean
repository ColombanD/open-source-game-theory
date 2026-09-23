import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Base.Asymptotics
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.Bots.LlmGenerations.GuardianBot
import PrisonersDilemma.Bots.LlmGenerations.CIMCIC
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Theorems.CooperateBot.Helpers

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

/-! ## GuardianBot's side: refute its guard against CIMCIC (CIMCIC doesn't bully CB). -/

theorem gc_CIMCIC_consequent_botCB (k : Nat) :
    Pf (atom_cost 2) (Formula.plays (.bot CooperateBot) (CIMCIC k) Action.C) :=
  Pf.atom ⟨PlaysProof.bot PlaysProof.const, by decide⟩

theorem gc_proofSearch_true_CIMCIC_vs_botCB :
    ∃ K, ∀ k, k ≥ K →
      proofSearch k
        ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.C)).subst
          (CIMCIC k) (.bot CooperateBot)) = true := by
  obtain ⟨K, hK⟩ := linear_log2_add_le 10 100
  refine ⟨K, fun k hk => ?_⟩
  refine (proofSearch_spec _ _).2 ?_
  show Pf k
    (Formula.impl (.plays (CIMCIC k) (.bot CooperateBot) Action.C)
                  (.plays (.bot CooperateBot) (CIMCIC k) Action.C))
  refine Pf.weakenImpl _ _ (atom_cost 2) (gc_CIMCIC_consequent_botCB k) ?_
  have hb := hK k hk
  have h1 : atom_cost 2 = 7 := by decide
  simp only [numCost, Formula.size, Prog.size, CIMCIC, CooperateBot]
  omega

theorem gc_CIMCIC_plays_C_vs_botCB (k fuel : Nat)
    (hk : proofSearch k
        ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.C)).subst
          (CIMCIC k) (.bot CooperateBot)) = true) :
    play (fuel + 2) (CIMCIC k) (.bot CooperateBot) = some .C := by
  show (if proofSearch k
            ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.C)).subst
              (CIMCIC k) (.bot CooperateBot))
          then eval (fuel + 1) (CIMCIC k) (.bot CooperateBot) (.const Action.C)
          else eval (fuel + 1) (CIMCIC k) (.bot CooperateBot) (.const Action.D)) = some .C
  rw [hk]; simp [eval]

theorem gc_guardian_guard_false (K : Nat)
    (hK : ∀ k, k ≥ K →
      proofSearch k
        ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.C)).subst
          (CIMCIC k) (.bot CooperateBot)) = true) :
    ∀ k, k ≥ K → proofSearch k (.plays (CIMCIC k) (.bot CooperateBot) .D) = false := by
  intro k hk
  cases hps : proofSearch k (.plays (CIMCIC k) (.bot CooperateBot) .D) with
  | true  =>
      exfalso
      obtain ⟨n, hn⟩ := proofSearch_sound _ _ hps
      have hC : play (n + 2) (CIMCIC k) (.bot CooperateBot) = some .C :=
        gc_CIMCIC_plays_C_vs_botCB k n (hK k hk)
      have hD : play (n + 2) (CIMCIC k) (.bot CooperateBot) = some .D :=
        eval_mono_le hn (n + 2) (by omega)
      rw [hC] at hD; simp at hD
  | false => rfl

theorem gc_GuardianBot_cooperates_vs_CIMCIC (k fuel : Nat)
    (hg : proofSearch k (.plays (CIMCIC k) (.bot CooperateBot) .D) = false) :
    play (fuel + 2) (GuardianBot k) (CIMCIC k) = some .C := by
  show eval (fuel + 2) (GuardianBot k) (CIMCIC k) (GuardianBot k) = some .C
  unfold GuardianBot
  simp [eval, Prog.subst, Formula.subst, hg]

/-! ## CIMCIC's side: its guard is floor-killed → CIMCIC defects. -/

theorem gc_no_provable_tail (k : Nat) :
    ∀ K φ, Pf K φ → K ≤ k →
      TailTo (.plays (GuardianBot k) (CIMCIC k) Action.C) φ → False := by
  intro K φ hp hK htail
  refine no_provable_tailToS_floor k
    (· = .plays (GuardianBot k) (CIMCIC k) Action.C)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ K φ hp hK ((TailToS_singleton _ φ).2 htail)
  · rintro φ' rfl; exact ⟨_, _, _, rfl⟩
  · rintro K' hK' φ' rfl hA
    cases hA with
    | mk hpp hn =>
      unfold GuardianBot at hpp
      cases hpp with
      | search_t hg hbr => cases hbr
      | search_f hneg hbr => cases hbr; simp only [c_leaf, c_node] at hn; omega
  · rintro me oppo c hS g ψ b hme
    injection hS with h1 h2 h3; subst h1; subst h3
    unfold GuardianBot at hme; simp only [Prog.search.injEq] at hme
    exact absurd hme.2.2.1 (by decide)
  · rintro me oppo c hS p q hme
    injection hS with h1 h2 h3; subst h1; simp [GuardianBot] at hme
  · rintro me oppo c hS p q hme
    injection hS with h1 h2 h3; subst h1; simp [GuardianBot] at hme
  · rintro me oppo c hS g ψ b hme
    injection hS with h1 h2 h3; subst h1; simp [GuardianBot] at hme
  · rintro z a' g ψ c0 c1 q oppo hS
    injection hS with h1 h2 h3; simp [GuardianBot] at h1
  · rintro me oppo c hS k₁ ψ₁ k₂ ψ₂ c1 q hme
    injection hS with h1 h2 h3; subst h1; subst h3
    unfold GuardianBot at hme; simp only [Prog.search.injEq] at hme
    exact absurd hme.2.2.1 (by simp)
  · rintro me oppo c hS L hme
    injection hS with h1 h2 h3; subst h1; subst h3
    cases L with
    | nil => simp [searchPlug, GuardianBot] at hme
    | cons hd tl =>
        obtain ⟨g, ψ, e⟩ := hd
        simp only [searchPlug, GuardianBot, Prog.search.injEq] at hme
        cases tl with
        | nil => simp [searchPlug] at hme
        | cons hd2 tl2 => obtain ⟨g2, ψ2, e2⟩ := hd2; simp [searchPlug] at hme
  · rintro me oppo c hS hd L hme
    injection hS with h1 h2 h3; subst h1; subst h3
    cases hd with
    | searchL g ψ e =>
        simp only [ctxPlug, GuardianBot, Prog.search.injEq] at hme
        obtain ⟨rfl, rfl, hplug, rfl⟩ := hme
        cases L with
        | nil => simp [ctxPlug] at hplug
        | cons hd2 tl2 => cases hd2 <;> simp [ctxPlug] at hplug
    | iteL z aT other => simp [ctxPlug, GuardianBot] at hme

/-- CIMCIC's guard vs GuardianBot is unprovable at budget k (spine tail is the
    floor-killed C-play; the antecedent is a different atom). -/
theorem gc_cimcic_guard_not_provable (k : Nat) :
    ¬ Pf k (.impl (.plays (CIMCIC k) (GuardianBot k) Action.C)
                  (.plays (GuardianBot k) (CIMCIC k) Action.C)) := by
  intro h
  refine gc_no_provable_tail k k _ h le_rfl ?_
  refine ⟨rfl, ?_⟩
  intro hA
  simp only [TailTo] at hA
  exact absurd hA (by simp [GuardianBot, CIMCIC])

theorem gc_proofSearch_false_cimcic_guard (k : Nat) :
    proofSearch k
      ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.C)).subst
        (CIMCIC k) (GuardianBot k)) = false := by
  cases hps : proofSearch k
      ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.C)).subst
        (CIMCIC k) (GuardianBot k)) with
  | false => rfl
  | true =>
      exact absurd ((proofSearch_spec k _).1 hps) (gc_cimcic_guard_not_provable k)

theorem gc_CIMCIC_plays_D_vs_GuardianBot (k fuel : Nat) :
    play (fuel + 2) (CIMCIC k) (GuardianBot k) = some .D := by
  show (if proofSearch k
            ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.C)).subst
              (CIMCIC k) (GuardianBot k))
          then eval (fuel + 1) (CIMCIC k) (GuardianBot k) (.const Action.C)
          else eval (fuel + 1) (CIMCIC k) (GuardianBot k) (.const Action.D))
        = some Action.D
  rw [gc_proofSearch_false_cimcic_guard k]; simp [eval]

/-- **GuardianBot vs CIMCIC → (C, D)** for all sufficiently large `k`: GuardianBot
    trusts CIMCIC (it doesn't bully CooperateBot), but CIMCIC cannot prove
    GuardianBot's (floor-priced else-play) cooperation and defects. -/
theorem llm_outcome_GuardianBot_vs_CIMCIC :
    ∃ k₂, ∀ k, k₂ < k →
      ∃ fuel, outcome fuel (GuardianBot k) (CIMCIC k) = some (.C, .D) := by
  obtain ⟨K, hK⟩ := gc_proofSearch_true_CIMCIC_vs_botCB
  refine ⟨K, fun k hk => ⟨2, ?_⟩⟩
  have hgf := gc_guardian_guard_false K hK k (Nat.le_of_lt hk)
  have hA : play (0 + 2) (GuardianBot k) (CIMCIC k) = some .C :=
    gc_GuardianBot_cooperates_vs_CIMCIC k 0 hgf
  have hB : play (0 + 2) (CIMCIC k) (GuardianBot k) = some .D :=
    gc_CIMCIC_plays_D_vs_GuardianBot k 0
  exact outcome_of_plays _ _ _ _ _ hA hB

end PD.Theorems

