import PrisonersDilemma.Bots.CupodTrollBot
import PrisonersDilemma.Bots.CupodBot
import PrisonersDilemma.Bots.DupocBot


import PrisonersDilemma.Dynamics
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.Theorems.CupodTrollBot.Helpers
import PrisonersDilemma.Outcome

open PD
open PD.Bots
open PD.BaseTheorems
namespace PD.Theorems
/-- **The general fact**: CupodTrollBot `j` and DupocBot `k` cooperate as soon as `k`
    affords Troll's else-certificate — the refutation of its `.eq` guard plus Troll's whole
    failed budget `j` (the `search_f` floor). Not a matrix cell (no cell-shaped name): the
    cell below is its conventional staggered instance. -/
theorem CupodTrollBot_vs_DupocBot_above_floor (j k fuel : Nat)
    (hjk : (Formula.neg (.eq (DupocBot k) (CupodBot j))).size + j + 2 ≤ k) :
    outcome (fuel + 2) (CupodTrollBot j) (DupocBot k) = some (.C, .C) := by
  -- CupodTrollBot cooperates against `DupocBot` (direction A).
  have hA : play (fuel + 2) (CupodTrollBot j) (DupocBot k) = some .C :=
    CupodTrollBot_cooperates_if_opp_not_CupodBot j fuel (DupocBot k)
      (by simp [DupocBot, CupodBot])
  -- `DupocBot` cooperates with CupodTrollBot once its guard affords the floor (direction B).
  have hB : play (fuel + 2) (DupocBot k) (CupodTrollBot j) = some .C :=
    DupocBot_plays_C_against_CupodTrollBot j k fuel hjk
  exact outcome_of_plays _ _ _ _ _ hA hB

/-- **The staggered companion**: CupodTrollBot `k` vs DupocBot `(2k+64)` = (C, C) at every
    large `k` — the zoo's conventional budget stagger (cf.
    `outcome_PrudentBot_vs_DupocBot_staggered`). Not the matrix cell: that is the
    shared-budget `outcome_DupocBot_vs_CupodTrollBot = (D, C)`
    (`Theorems/DupocBot/vs_CupodTrollBot.lean`). The floor `size + k + 2 ≤ 2k+64` is
    logarithmic-plus-`k` against `2k`, hence `.eventual`. (Until 2026-08-27 this was the
    sole user of a guarded `OutcomeSpecIf` template, and filled the cell.) -/
@[outcome_companion]
theorem outcome_CupodTrollBot_vs_DupocBot_staggered :
    OutcomeSpec .eventual 2 CupodTrollBot (fun k => DupocBot (2*k+64)) (some (.C, .C)) := by
  have hsz : ∀ k, (Formula.neg (.eq (DupocBot (2*k+64)) (CupodBot k))).size
      ≤ 100 * Nat.log2 k + 1000 := by
    intro k
    have := log2_stagger_le k
    simp only [Formula.size, Prog.size, numCost, DupocBot, CupodBot]
    omega
  obtain ⟨K, hK⟩ := linear_log2_add_le 100 1000
  refine ⟨K, fun k hk fuel => ?_⟩
  have hfloor : (Formula.neg (.eq (DupocBot (2*k+64)) (CupodBot k))).size + k + 2 ≤ 2*k+64 := by
    have := hsz k
    have := hK k (by omega)
    omega
  exact CupodTrollBot_vs_DupocBot_above_floor k (2*k+64) fuel hfloor

end PD.Theorems
