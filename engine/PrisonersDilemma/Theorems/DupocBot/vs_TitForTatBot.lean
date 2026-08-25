import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Bots.DupocBot
import PrisonersDilemma.Bots.TitForTatBot
import PrisonersDilemma.Theorems.CooperateBot.Helpers
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Base.Asymptotics
import PrisonersDilemma.Theorems.DupocBot.Helpers
import PrisonersDilemma.Outcome

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems
/-- DupocBot vs TitForTatBot: mutual cooperation. Both witnesses at a common
    budget `atom_cost 4`. -/
-- Generalized from the single witness `kTFT = atom_cost 4`. An earlier attempt read the
-- failing `omega` as a hard obstruction ("c_guard grows with k"); that was too coarse.
-- `c_guard k = numCost k = log2 k + 1` is LOGARITHMIC, so `log2 k + 6 ≤ k` holds for all
-- large `k` by `linear_log2_add_le` — the same route as JustBot × TitForTatBot.
@[outcome]
theorem outcome_DupocBot_vs_TitForTatBot :
    OutcomeSpecEx .eventual
      DupocBot (fun _ => TitForTatBot) (some (.C, .C)) := by
  obtain ⟨K, hK⟩ := linear_log2_add_le 1 6
  refine ⟨max K (atom_cost 4), fun k hlt => ?_⟩
  have hKk : K ≤ k := le_of_lt (lt_of_le_of_lt (le_max_left _ _) hlt)
  have hfloor : atom_cost 4 ≤ k := le_of_lt (lt_of_le_of_lt (le_max_right K _) hlt)
  have hcost : Nat.log2 k + 6 ≤ k := by have := hK k hKk; omega
  have hCBprov : Pf k (.plays (.bot CooperateBot) (DupocBot k) .C) :=
    Pf.atom ⟨PlaysProof.bot PlaysProof.const, by
      simp [atom_cost, numCost, c_leaf, c_node] at hfloor ⊢; omega⟩
  have hkCB : proofSearch k (.plays (.bot CooperateBot) (DupocBot k) .C) = true :=
    (proofSearch_spec _ _).2 hCBprov
  have hkTFT : proofSearch k (.plays TitForTatBot (DupocBot k) .C) = true := by
    refine (proofSearch_spec _ _).2 (Pf.atom
      (⟨PlaysProof.ite_t (PlaysProof.sim (PlaysProof.search_t hCBprov PlaysProof.const))
        rfl PlaysProof.const, ?_⟩ :
        AtomProvable k (.plays TitForTatBot (DupocBot k) .C)))
    show c_leaf + c_guard k + c_node + c_node + c_leaf + c_node ≤ k
    simp [c_leaf, c_node, c_guard, numCost] at hcost ⊢
    omega
  refine ⟨4, ?_⟩
  have hA : play 4 (DupocBot k) TitForTatBot = some .C := by
    simpa using DupocBot_plays_C_against_TitForTatBot k 2 hkTFT
  have hB : play 4 TitForTatBot (DupocBot k) = some .C :=
    TitForTatBot_plays_C_against_DupocBot k 0 hkCB
  exact outcome_of_plays _ _ _ _ _ hA hB
end PD.Theorems
