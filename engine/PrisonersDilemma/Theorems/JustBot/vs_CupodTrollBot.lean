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

theorem outcome_JustBot_vs_CupodTrollBot (j fuel : Nat) :
    outcome (fuel + 2) (JustBot (4*j+100)) (CupodTrollBot j) = some (.C, .C) := by
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
            + j + c_node)
          (.plays (CupodTrollBot j) (.bot (DupocBot (4*j+100))) .C))))
    simp only [numCost, c_leaf, c_node, Formula.size, Prog.size, DupocBot, CupodBot]
    omega
  have hA : play (fuel + 2) (JustBot (4*j+100)) (CupodTrollBot j) = some .C := by
    refine JustBot_eval_step (4*j+100) fuel (CupodTrollBot j) .C ?_
    simpa using hguard
  have hB : play (fuel + 2) (CupodTrollBot j) (JustBot (4*j+100)) = some .C :=
    CupodTrollBot_cooperates_if_opp_not_CupodBot j fuel (JustBot (4*j+100))
      (by simp [JustBot, CupodBot])
  exact outcome_of_plays _ _ _ _ _ hA hB
end PD.Theorems
