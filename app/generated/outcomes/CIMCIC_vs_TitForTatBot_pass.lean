import PrisonersDilemma.Bots.LlmGenerations.CIMCIC
import PrisonersDilemma.Bots.TitForTatBot
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Theorems.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Base.Asymptotics

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

/-- CIMCIC's guard against `.bot CooperateBot` is provable at budget `k` (large `k`):
    the consequent "`.bot CooperateBot` plays C vs CIMCIC" is provable, so `weakenImpl`
    builds the implication. -/
theorem CIMCIC_guard_bot_CooperateBot_provable :
    ∃ K, ∀ k, k ≥ K →
      Pf k
        (Formula.impl (.plays (CIMCIC k) (.bot CooperateBot) Action.C)
                      (.plays (.bot CooperateBot) (CIMCIC k) Action.C)) := by
  obtain ⟨K, hK⟩ := linear_log2_add_le 10 100
  refine ⟨K, fun k hk => ?_⟩
  refine Pf.weakenImpl _ _ (atom_cost 2)
    (Pf.atom ⟨PlaysProof.bot PlaysProof.const, by decide⟩) ?_
  have hb := hK k hk
  have h1 : atom_cost 2 = 7 := by decide
  simp only [numCost, Formula.size, Prog.size, CIMCIC, CooperateBot]
  omega

/-- CIMCIC's guard vs `.bot CooperateBot` fires, so `proofSearch = true`. -/
theorem proofSearch_true_CIMCIC_vs_bot_CooperateBot :
    ∃ K, ∀ k, k ≥ K →
      proofSearch k
        ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.C)).subst
          (CIMCIC k) (.bot CooperateBot)) = true := by
  obtain ⟨K, hK⟩ := CIMCIC_guard_bot_CooperateBot_provable
  refine ⟨K, fun k hk => ?_⟩
  simp only [Formula.subst, Prog.subst]
  exact (proofSearch_spec _ _).2 (hK k hk)

/-- CIMCIC plays C vs `.bot CooperateBot` once its guard fires. -/
theorem CIMCIC_plays_C_against_bot_CooperateBot (k fuel : Nat)
    (hk : proofSearch k
        ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.C)).subst
          (CIMCIC k) (.bot CooperateBot)) = true) :
    play (fuel + 2) (CIMCIC k) (.bot CooperateBot) = some .C := by
  show eval (fuel + 2) (CIMCIC k) (.bot CooperateBot) (CIMCIC k) = some .C
  simp only [Formula.subst, Prog.subst] at hk
  unfold CIMCIC at hk ⊢
  simp [eval, Prog.subst, Formula.subst, hk]

/-- TitForTat cooperates with CIMCIC: its `.sim .opp (.bot CooperateBot)` probe sees
    CIMCIC cooperate, so the `ite` selects the cooperate branch. -/
theorem TitForTatBot_plays_C_against_CIMCIC (k fuel : Nat)
    (hk : proofSearch k
        ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.C)).subst
          (CIMCIC k) (.bot CooperateBot)) = true) :
    play (fuel + 4) TitForTatBot (CIMCIC k) = some .C := by
  have hCimcic : play (fuel + 2) (CIMCIC k) (.bot CooperateBot) = some .C :=
    CIMCIC_plays_C_against_bot_CooperateBot k fuel hk
  have hGuard :
      eval (fuel + 3) TitForTatBot (CIMCIC k) (.sim .opp (.bot CooperateBot)) = some .C := by
    simpa [Nat.add_assoc] using
      (eval_sim_opp_bot_of_play (fuel + 2) TitForTatBot (CIMCIC k) CooperateBot Action.C hCimcic)
  have hPlay := play_ite_from_guard
    fuel 3 TitForTatBot (CIMCIC k) (.sim .opp (.bot CooperateBot))
    (.const Action.C) (.const Action.D)
    Action.C Action.C
    (by rfl) hGuard
  simpa [eval] using hPlay

/-- The consequent atom "TFT plays C vs CIMCIC k" is provable at an `O(log k)`-budget
    certificate: `ite_t` over the `.sim` probe (`search_t` on the guard proof, then
    the `.const .C` leaf). -/
theorem TFT_plays_C_vs_CIMCIC_provable :
    ∃ K, ∀ k, k ≥ K →
      Pf ((((c_leaf + c_guard k + c_node) + c_node) + c_leaf) + c_node)
        (Formula.plays TitForTatBot (CIMCIC k) Action.C) := by
  obtain ⟨K, hK⟩ := CIMCIC_guard_bot_CooperateBot_provable
  refine ⟨K, fun k hk => ?_⟩
  have hguard := hK k hk
  have cert : PlaysProof TitForTatBot (CIMCIC k) TitForTatBot Action.C
      ((((c_leaf + c_guard k + c_node) + c_node) + c_leaf) + c_node) := by
    unfold TitForTatBot
    refine PlaysProof.ite_t (r := Action.C) ?_ (by rfl) PlaysProof.const
    refine PlaysProof.sim ?_
    simp only [Prog.subst]
    unfold CIMCIC
    refine PlaysProof.search_t ?_ PlaysProof.const
    simp only [Formula.subst, Prog.subst]
    unfold CIMCIC at hguard
    exact hguard
  exact Pf.atom ⟨cert, Nat.le_refl _⟩

/-- CIMCIC's guard against TitForTatBot is provable at budget `k` (large `k`):
    the consequent "TFT plays C vs CIMCIC" is provable (via the certificate above),
    so `weakenImpl` builds the implication guard. -/
theorem proofSearch_true_CIMCIC_vs_TitForTatBot :
    ∃ K, ∀ k, k ≥ K →
      proofSearch k
        ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.C)).subst
          (CIMCIC k) TitForTatBot) = true := by
  obtain ⟨K₀, hK₀⟩ := TFT_plays_C_vs_CIMCIC_provable
  obtain ⟨K₁, hK₁⟩ := linear_log2_add_le 20 200
  refine ⟨max K₀ K₁, fun k hk => ?_⟩
  have hk0 : k ≥ K₀ := le_trans (le_max_left _ _) hk
  have hk1 : k ≥ K₁ := le_trans (le_max_right _ _) hk
  simp only [Formula.subst, Prog.subst]
  refine (proofSearch_spec _ _).2 ?_
  refine Pf.weakenImpl _ _ _ (hK₀ k hk0) ?_
  -- transcript: consequent certificate size (O(log k)) + implication size ≤ k
  have hb := hK₁ k hk1
  simp only [c_leaf, c_guard, c_node, numCost, Formula.size, Prog.size, CIMCIC, TitForTatBot,
    CooperateBot]
  omega

/-- CIMCIC cooperates against TitForTatBot: its guard fires. -/
theorem CIMCIC_plays_C_against_TitForTatBot (k fuel : Nat)
    (hk : proofSearch k
        ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.C)).subst
          (CIMCIC k) TitForTatBot) = true) :
    play (fuel + 2) (CIMCIC k) TitForTatBot = some .C := by
  show eval (fuel + 2) (CIMCIC k) TitForTatBot (CIMCIC k) = some .C
  simp only [Formula.subst, Prog.subst] at hk
  unfold CIMCIC at hk ⊢
  simp [eval, Prog.subst, Formula.subst, hk]

/-- **CIMCIC vs TitForTatBot: mutual cooperation (C, C)** for all sufficiently large `k`. -/
theorem llm_outcome_CIMCIC_vs_TitForTatBot :
    ∃ k₂, ∀ k, k₂ < k →
      ∃ fuel, outcome fuel (CIMCIC k) TitForTatBot = some (.C, .C) := by
  obtain ⟨Ka, hKa⟩ := proofSearch_true_CIMCIC_vs_TitForTatBot
  obtain ⟨Kb, hKb⟩ := proofSearch_true_CIMCIC_vs_bot_CooperateBot
  refine ⟨max Ka Kb, fun k hk => ?_⟩
  have hka : k ≥ Ka := le_of_lt (lt_of_le_of_lt (le_max_left _ _) hk)
  have hkb : k ≥ Kb := le_of_lt (lt_of_le_of_lt (le_max_right _ _) hk)
  refine ⟨6, ?_⟩
  have hA : play 6 (CIMCIC k) TitForTatBot = some .C := by
    simpa using CIMCIC_plays_C_against_TitForTatBot k 4 (hKa k hka)
  have hB : play 6 TitForTatBot (CIMCIC k) = some .C := by
    simpa using TitForTatBot_plays_C_against_CIMCIC k 2 (hKb k hkb)
  exact outcome_of_plays _ _ _ _ _ hA hB

end PD.Theorems
