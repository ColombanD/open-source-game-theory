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

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems
/-- DupocBot vs TitForTatBot: mutual cooperation. Both witnesses at a common
    budget `atom_cost 4`. -/
theorem outcome_DupocBot_vs_TitForTatBot (fuel : Nat) :
    ∃ k, outcome (fuel + 4) (DupocBot k) TitForTatBot = some (.C, .C) := by
  let kTFT := atom_cost 4
  have hCBprov : Pf kTFT (.plays (.bot CooperateBot) (DupocBot kTFT) .C) :=
    Pf.atom ⟨PlaysProof.bot PlaysProof.const, by decide⟩
  have hkCB : proofSearch kTFT (.plays (.bot CooperateBot) (DupocBot kTFT) .C) = true :=
    (proofSearch_spec _ _).2 hCBprov
  have hkTFT : proofSearch kTFT (.plays TitForTatBot (DupocBot kTFT) .C) = true := by
    refine (proofSearch_spec _ _).2 (Pf.atom
      (⟨PlaysProof.ite_t (PlaysProof.sim (PlaysProof.search_t hCBprov PlaysProof.const))
        rfl PlaysProof.const, ?_⟩ :
        AtomProvable kTFT (.plays TitForTatBot (DupocBot kTFT) .C)))
    show c_leaf + c_guard kTFT + c_node + c_node + c_leaf + c_node ≤ kTFT
    decide
  refine ⟨kTFT, ?_⟩
  have hA : play (fuel + 4) (DupocBot kTFT) TitForTatBot = some .C := by
    simpa [Nat.add_assoc] using DupocBot_plays_C_against_TitForTatBot kTFT (fuel + 2) hkTFT
  have hB : play (fuel + 4) TitForTatBot (DupocBot kTFT) = some .C :=
    TitForTatBot_plays_C_against_DupocBot kTFT fuel hkCB
  exact outcome_of_plays _ _ _ _ _ hA hB

end PD.Theorems
