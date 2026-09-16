import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Bots.DupocBot
import PrisonersDilemma.Bots.LlmGenerations.JustBot
import PrisonersDilemma.Bots.CupodTrollBot
import PrisonersDilemma.Theorems.DupocBot.Helpers
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.Theorems.CupodTrollBot.Helpers
import PrisonersDilemma.Theorems.CupodTrollBot.vs_DupocBot
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Base.Asymptotics
import PrisonersDilemma.Theorems.JustBot.Helpers
import PrisonersDilemma.Base.Exclusion
import PrisonersDilemma.Theorems.DupocBot.vs_CupodTrollBot
import PrisonersDilemma.Outcome

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

-- CupodTrollBot --

/-! ### JustBot × CupodTrollBot — RETIRED (2026-07-02, the false-guard repair).

CupodTrollBot's cooperation against `.bot (DupocBot k)` is an ELSE-play of its own `.eq`
search (the opponent is not literally `CupodBot k`), so its certificate pays the `search_f`
floor — JustBot's guard at the same `k` can never afford it. Staggered-budget restatement
(Troll at `j`, JustBot at `k ≥ j + O(log)`) is T3.2b; cf. the staggered
`outcome_CupodTrollBot_vs_DupocBot` in `Theorems/CupodTrollBot.lean`. -/

/-! ### JustBot × CupodTrollBot — RECOVERED with STAGGERED budgets (T3.2b, 2026-07-03).

`JustBot (4j+100)` vs `CupodTrollBot j`: JustBot's bigger budget affords Troll's
`search_f`-floored else-certificate (Troll cooperates because its `.eq` recognition guard
FAILS against `.bot (DupocBot (4j+100))`, refuted by `Pf.eqNeg`). Holds for EVERY
`j` — no eventuality. -/

/-- `4·log2 k ≤ k + 12` (file-private twin of the PrudentBot files' lemma; needed since the
    2026-09-16 re-cost charges the atom's size on top of the stagger). -/
private theorem four_mul_log2_le (k : Nat) : 4 * Nat.log2 k ≤ k + 12 := by
  have haux : ∀ n : Nat, 4 * (n + 4) ≤ 2 ^ (n + 4) := by
    intro n
    induction n with
    | zero => decide
    | succ n ih =>
        have h : 2 ^ (n + 1 + 4) = 2 ^ (n + 4) * 2 := by
          rw [show n + 1 + 4 = (n + 4) + 1 by omega, Nat.pow_succ]
        omega
  have h4 : ∀ n : Nat, 4 * n ≤ 2 ^ n + 12 := by
    intro n
    rcases Nat.lt_or_ge n 4 with h | h
    · have := Nat.one_le_two_pow (n := n); omega
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' h
      have := haux m
      omega
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · have hpow : 2 ^ Nat.log2 k ≤ k := by
      rw [Nat.log2_eq_log_two]; exact Nat.pow_log_le_self 2 (by omega)
    have := h4 (Nat.log2 k)
    omega

-- The staggered companion (not the cell — see `outcome_JustBot_vs_CupodTrollBot` below).
@[outcome_companion]
theorem outcome_JustBot_vs_CupodTrollBot_staggered :
    OutcomeSpec .universal 2
      (fun j => JustBot (4*j+100)) CupodTrollBot (some (.C, .C)) := by
  intro j fuel
  have hlj := log2_le_self j
  have hlgj := log2_stagger4_le j
  have hne : Prog.bot (DupocBot (4*j+100)) ≠ CupodBot j := by simp [CupodBot]
  -- the eqNeg refutation of Troll's recognition guard, at its own size
  have hneg : Pf ((Formula.neg (.eq (.bot (DupocBot (4*j+100))) (CupodBot j))).size)
      (.neg (.eq (.bot (DupocBot (4*j+100))) (CupodBot j))) :=
    Pf.eqNeg _ _ hne (Nat.le_refl _)
  -- Troll's floored else-certificate, affordable in JustBot's 4j+100 budget
  have hguard : proofSearch (4*j+100)
      (.plays (CupodTrollBot j) (.bot (DupocBot (4*j+100))) .C) = true := by
    refine (proofSearch_spec _ _).2 (Pf.atom (atom_monotone _ (4*j+100) _ ?_
      (⟨PlaysProof.search_f hneg PlaysProof.const, Nat.le_refl _⟩ :
        AtomProvable
          (c_leaf + (Formula.neg (.eq (.bot (DupocBot (4*j+100))) (CupodBot j))).size
            + j + c_node
            + (Formula.plays (CupodTrollBot j) (.bot (DupocBot (4*j+100))) .C).size)
          (.plays (CupodTrollBot j) (.bot (DupocBot (4*j+100))) .C))))
    -- `4·log2 j ≤ j + 12` (`log2 j ≤ j` alone is too weak once the atom's size is charged)
    have h4 := four_mul_log2_le j
    simp only [numCost, c_leaf, c_node, Formula.size, Prog.size, DupocBot, CupodBot,
      CupodTrollBot]
    omega
  have hA : play (fuel + 2) (JustBot (4*j+100)) (CupodTrollBot j) = some .C := by
    refine JustBot_eval_step (4*j+100) fuel (CupodTrollBot j) .C ?_
    simpa using! hguard
  have hB : play (fuel + 2) (CupodTrollBot j) (JustBot (4*j+100)) = some .C :=
    CupodTrollBot_cooperates_if_opp_not_CupodBot j fuel (JustBot (4*j+100))
      (by simp [JustBot, CupodBot])
  exact outcome_of_plays _ _ _ _ _ hA hB

/-! ### The SAME-budget regime — the tau layer's value, proven in base (2026-08-25)

The strict `outcome_{L}_vs_{R}` theorem above is stated at a budget STAGGER: that is
what buys the cooperative cell, by paying a partner's `search_f` floor. At one shared
budget the floor is unpayable and the honest outcome is what the tau lift (`tauZoo k`,
one `k` for everyone) reads. These `_samek` theorems certify that value in base, so the
tau/base divergence on this pair is a matter of budget regime alone — both regimes are
theorems. (The `_samek` suffix keeps them out of the strict matrix scan.) -/

theorem JustBot_plays_D_against_CupodTrollBot_samek (k fuel : Nat) :
    play (fuel + 2) (JustBot k) (CupodTrollBot k) = some .D :=
  JustBot_eval_step k fuel (CupodTrollBot k) .D
    (by rw [proofSearch_false_CupodTrollBot_C]; rfl)

theorem CupodTrollBot_plays_C_against_JustBot_samek (k fuel : Nat) :
    play (fuel + 2) (CupodTrollBot k) (JustBot k) = some .C :=
  CupodTrollBot_cooperates_if_opp_not_CupodBot k fuel (JustBot k) (by simp [JustBot, CupodBot])

/-- **THE CELL — JustBot vs CupodTrollBot at ONE shared budget = (D, C)**: Troll's C is
    its floor-priced else-play, which JustBot's probe cannot afford at the same `k`.
    Cooperation needs `JustBot (4j+100)` — `outcome_JustBot_vs_CupodTrollBot_staggered`.
    (Until 2026-08-27 the staggered result filled the cell and this was `_samek`.) -/
@[outcome]
theorem outcome_JustBot_vs_CupodTrollBot :
    OutcomeSpec .universal 2 JustBot CupodTrollBot (some (.D, .C)) := fun k fuel =>
  outcome_of_plays _ _ _ _ _ (JustBot_plays_D_against_CupodTrollBot_samek k fuel)
    (CupodTrollBot_plays_C_against_JustBot_samek k fuel)

end PD.Theorems
