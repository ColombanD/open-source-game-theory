import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Bots.LlmGenerations.LegibleBot
import PrisonersDilemma.Bots.LlmGenerations.CIMCIC
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Theorems.LegibleBot.Helpers

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

/-- LegibleBot vs CIMCIC, the whole FLOOR regime (same budget both sides):
    both guards outgrow the budget and both else-branches defect — mutual
    defection. Large-`k` is RESOLVED (2026-07-30) at staggered dials: see the theorem below. -/
theorem outcome_LegibleBot_vs_CIMCIC_floor (k fuel : Nat)
    (hszL : k < (Formula.box k
      (.plays (LegibleBot k k) (CIMCIC k) .C)).size)
    (hszI : k < (Formula.impl (.plays (CIMCIC k) (LegibleBot k k) .C)
      (.plays (LegibleBot k k) (CIMCIC k) .C)).size) :
    outcome (fuel + 2) (LegibleBot k k) (CIMCIC k) = some (.D, .D) :=
  outcome_of_plays _ _ _ _ _ (LegibleBot_defects_floor k k fuel _ hszL)
    (CIMCIC_plays_D_against_LegibleBot_floor k fuel hszI)

/-- The concrete `k = 2` instance. -/
theorem outcome_LegibleBot_vs_CIMCIC_floor2 (fuel : Nat) :
    outcome (fuel + 2) (LegibleBot 2 2) (CIMCIC 2) = some (.D, .D) :=
  outcome_LegibleBot_vs_CIMCIC_floor 2 fuel (by decide) (by decide)

/-- **LegibleBot (staggered) vs CIMCIC (same inner dial `k`): `(C, C)`** for all
    sufficiently large `k`. CIMCIC's guard vs L is `(CIMCIC plays C) → (L plays
    C)`; the consequent has a CHEAP certificate: L's C-play means its own guard
    fired (`LegibleBot_playC_gives_box` recovers `Pf (2k+64) (□_k ψ)`), and
    `PlaysProof.search_t` cites that fired guard at only
    `c_guard (2k+64) = O(log k)` transcript characters — NOT the `Pf k ψ`
    budget. `weakenImpl` then proves CIMCIC's implication within its own budget
    `k`, the guard fires, and CIMCIC cooperates. Staggered complement of
    `outcome_LegibleBot_vs_CIMCIC_floor`. -/
theorem outcome_LegibleBot_vs_CIMCIC :
    ∃ k₂, ∀ k, k > k₂ →
      ∃ fuel, outcome fuel (LegibleBot (2*k+64) k) (CIMCIC k) = some (.C, .C) := by
  obtain ⟨kA, hA⟩ := LegibleBot_cooperates_large (fun k => CIMCIC k) 100
    (fun k => by simp only [CIMCIC, Prog.size, Formula.size, numCost]; omega)
  obtain ⟨K, hK⟩ := linear_log2_add_le 20 500
  refine ⟨max kA K, fun k hk => ?_⟩
  obtain ⟨n, hn⟩ := hA k (lt_of_le_of_lt (Nat.le_max_left _ _) hk)
  -- L's fired guard, recovered as a bounded box certificate
  have hbox : Pf (2*k+64) (.box k (.plays (LegibleBot (2*k+64) k) (CIMCIC k) .C)) :=
    LegibleBot_playC_gives_box k n (CIMCIC k) hn
  -- the O(log k) atom certificate: search_t citing the fired guard
  have hatom : AtomProvable (c_leaf + c_guard (2*k+64) + c_node)
      (.plays (LegibleBot (2*k+64) k) (CIMCIC k) .C) :=
    ⟨PlaysProof.search_t hbox PlaysProof.const, Nat.le_refl _⟩
  -- CIMCIC's guard is provable at its own budget k
  have hguardC : Pf k (.impl (.plays (CIMCIC k) (LegibleBot (2*k+64) k) .C)
                             (.plays (LegibleBot (2*k+64) k) (CIMCIC k) .C)) := by
    refine Pf.weakenImpl _ _ _ (Pf.atom hatom) ?_
    have hKk := hK k (Nat.le_of_lt (lt_of_le_of_lt (Nat.le_max_right _ _) hk))
    have hst := log2_stagger_le k
    simp only [c_leaf, c_node, c_guard, numCost, Formula.size, Prog.size, LegibleBot, CIMCIC]
    omega
  have hps : proofSearch k
      ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.C)).subst
        (CIMCIC k) (LegibleBot (2*k+64) k)) = true :=
    (proofSearch_spec _ _).2 hguardC
  have hCplay : play (n + 2) (CIMCIC k) (LegibleBot (2*k+64) k) = some .C := by
    show (if proofSearch k
              ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.C)).subst
                (CIMCIC k) (LegibleBot (2*k+64) k))
            then eval (n + 1) (CIMCIC k) (LegibleBot (2*k+64) k) (.const Action.C)
            else eval (n + 1) (CIMCIC k) (LegibleBot (2*k+64) k) (.const Action.D))
          = some Action.C
    rw [hps]; simp [eval]
  have hn' : eval n (LegibleBot (2*k+64) k) (CIMCIC k) (LegibleBot (2*k+64) k)
      = some .C := hn
  have hLplay : play (n + 2) (LegibleBot (2*k+64) k) (CIMCIC k) = some .C :=
    eval_mono_le hn' _ (Nat.le_add_right _ 2)
  exact ⟨n + 2, outcome_of_plays _ _ _ _ _ hLplay hCplay⟩

end PD.Theorems
