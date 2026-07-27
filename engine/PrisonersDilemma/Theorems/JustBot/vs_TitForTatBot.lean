import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Bots.DupocBot
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Bots.MirrorBot
import PrisonersDilemma.Bots.TitForTatBot
import PrisonersDilemma.Bots.LlmGenerations.JustBot
import PrisonersDilemma.Bots.LlmGenerations.PrudentBot
import PrisonersDilemma.Bots.CupodTrollBot
import PrisonersDilemma.Theorems.CooperateBot
import PrisonersDilemma.Theorems.DefectBot
import PrisonersDilemma.Theorems.DupocBot
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.Theorems.CupodTrollBot
import PrisonersDilemma.Theorems.PrudentBot.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Base.Asymptotics
import PrisonersDilemma.Theorems.JustBot.Helpers

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

-- TitForTatBot --

/-- The shared guard: `(.bot CooperateBot)` cooperates against `(.bot (DupocBot k))`.
    Pf at budget `atom_cost 2` (a `.bot`-wrapped constant cooperates in two
    steps); we lift it to any `k ≥ atom_cost 2` via monotonicity. -/
theorem proofSearch_botCB_vs_botDupoc (k : Nat) (hk : k ≥ atom_cost 2) :
    proofSearch k (Formula.plays (.bot CooperateBot) (.bot (DupocBot k)) Action.C) = true := by
  refine (proofSearch_spec _ _).2 (Pf.atom ⟨PlaysProof.bot PlaysProof.const, ?_⟩)
  have h7 : atom_cost 2 = 7 := by decide
  show c_leaf + c_node ≤ k
  simp only [c_leaf, c_node]
  omega

/-- DupocBot (`.bot`-wrapped) cooperates against `.bot CooperateBot`: once the
    shared guard fires, its `.search` takes the `.const .C` branch (after one extra
    fuel step to unwrap the `.bot`). -/
theorem botDupocBot_plays_C_against_bot_CooperateBot (k fuel : Nat)
    (hk : proofSearch k (Formula.plays (.bot CooperateBot) (.bot (DupocBot k)) Action.C) = true) :
    play (fuel + 3) (.bot (DupocBot k)) (.bot CooperateBot) = some .C := by
  show eval (fuel + 3) (.bot (DupocBot k)) (.bot CooperateBot) (.bot (DupocBot k)) = some .C
  rw [eval]   -- unwrap the `.bot` body, exposing DupocBot's `.search`
  show (if proofSearch k (Formula.plays (.bot CooperateBot) (.bot (DupocBot k)) Action.C)
          then eval (fuel + 1) (.bot (DupocBot k)) (.bot CooperateBot) (.const Action.C)
          else eval (fuel + 1) (.bot (DupocBot k)) (.bot CooperateBot) (.const Action.D)) = some .C
  rw [hk]; simp [eval]

/-- TitForTatBot cooperates against `.bot (DupocBot k)`: its probe sees DupocBot
    cooperate against `.bot CooperateBot`, so the `ite` selects the cooperate
    branch. -/
theorem TitForTatBot_plays_C_against_bot_DupocBot (k fuel : Nat)
    (hk : proofSearch k (Formula.plays (.bot CooperateBot) (.bot (DupocBot k)) Action.C) = true) :
    play (fuel + 5) TitForTatBot (.bot (DupocBot k)) = some .C := by
  have hDupoc : play (fuel + 3) (.bot (DupocBot k)) (.bot CooperateBot) = some .C :=
    botDupocBot_plays_C_against_bot_CooperateBot k fuel hk
  have hGuard :
      eval (fuel + 4) TitForTatBot (.bot (DupocBot k)) (.sim .opp (.bot CooperateBot)) = some .C := by
    simpa [Nat.add_assoc] using
      (eval_sim_opp_bot_of_play (fuel + 3) TitForTatBot (.bot (DupocBot k)) CooperateBot Action.C hDupoc)
  have hPlay := play_ite_from_guard
    fuel 4 TitForTatBot (.bot (DupocBot k)) (.sim .opp (.bot CooperateBot))
    (.const Action.C) (.const Action.D)
    Action.C Action.C
    (by rfl) hGuard
  simpa [eval] using hPlay
/-- TitForTatBot cooperates against JustBot: its probe sees JustBot cooperate
    against `.bot CooperateBot` (same shared guard), so the `ite` cooperates. -/
theorem TitForTatBot_plays_C_against_JustBot (k fuel : Nat)
    (hk : proofSearch k (Formula.plays (.bot CooperateBot) (.bot (DupocBot k)) Action.C) = true) :
    play (fuel + 4) TitForTatBot (JustBot k) = some .C := by
  have hJust : play (fuel + 2) (JustBot k) (.bot CooperateBot) = some .C :=
    JustBot_plays_C_against_bot_CooperateBot k fuel hk
  have hGuard :
      eval (fuel + 3) TitForTatBot (JustBot k) (.sim .opp (.bot CooperateBot)) = some .C := by
    simpa [Nat.add_assoc] using
      (eval_sim_opp_bot_of_play (fuel + 2) TitForTatBot (JustBot k) CooperateBot Action.C hJust)
  have hPlay := play_ite_from_guard
    fuel 3 TitForTatBot (JustBot k) (.sim .opp (.bot CooperateBot))
    (.const Action.C) (.const Action.D)
    Action.C Action.C
    (by rfl) hGuard
  simpa [eval] using hPlay

/-- JustBot cooperates against TitForTatBot: its guard fires. -/
theorem JustBot_plays_C_against_TitForTatBot (k fuel : Nat)
    (hk : proofSearch k (Formula.plays TitForTatBot (.bot (DupocBot k)) Action.C) = true) :
    play (fuel + 2) (JustBot k) TitForTatBot = some .C := by
  refine JustBot_eval_step k fuel TitForTatBot .C ?_
  simpa using hk

/-- JustBot vs TitForTatBot: mutual cooperation. Both legs ride the shared guard at
    budget `atom_cost 5`. -/
theorem outcome_JustBot_vs_TitForTatBot :
    ∃ k, ∀ fuel, outcome (fuel + 5) (JustBot k) TitForTatBot = some (.C, .C) := by
  let k := atom_cost 5
  have hk : proofSearch k (Formula.plays (.bot CooperateBot) (.bot (DupocBot k)) Action.C) = true :=
    proofSearch_botCB_vs_botDupoc k (atom_cost_mono (by omega))
  have hGuardTFT : proofSearch k (Formula.plays TitForTatBot (.bot (DupocBot k)) Action.C) = true := by
    -- hand certificate: TFT's probe runs `.bot (DupocBot k)`'s FIRED search (hk), so
    -- ite_t ∘ sim ∘ bot ∘ search_t ∘ const; cost = log2 k + 7 ≤ k (k = atom_cost 5 = 21).
    refine (proofSearch_spec _ _).2 (Pf.atom
      (⟨PlaysProof.ite_t (PlaysProof.sim (PlaysProof.bot
          (PlaysProof.search_t ((proofSearch_spec _ _).1 hk) PlaysProof.const)))
        rfl PlaysProof.const, ?_⟩ :
        AtomProvable k (.plays TitForTatBot (.bot (DupocBot k)) .C)))
    show c_leaf + c_guard k + c_node + c_node + c_node + c_leaf + c_node ≤ k
    decide
  refine ⟨k, fun fuel => ?_⟩
  have hA : play (fuel + 5) (JustBot k) TitForTatBot = some .C := by
    simpa [Nat.add_assoc] using JustBot_plays_C_against_TitForTatBot k (fuel + 3) hGuardTFT
  have hB : play (fuel + 5) TitForTatBot (JustBot k) = some .C := by
    simpa [Nat.add_assoc] using TitForTatBot_plays_C_against_JustBot k (fuel + 1) hk
  exact outcome_of_plays _ _ _ _ _ hA hB
end PD.Theorems
