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
import PrisonersDilemma.Theorems.CooperateBot.Helpers
import PrisonersDilemma.Theorems.CooperateBot.vs_CooperateBot
import PrisonersDilemma.Theorems.CooperateBot.vs_DefectBot
import PrisonersDilemma.Theorems.DefectBot.Helpers
import PrisonersDilemma.Theorems.DefectBot.vs_DefectBot
import PrisonersDilemma.Theorems.DupocBot.Helpers
import PrisonersDilemma.Theorems.DupocBot.vs_CooperateBot
import PrisonersDilemma.Theorems.DupocBot.vs_DBot
import PrisonersDilemma.Theorems.DupocBot.vs_DefectBot
import PrisonersDilemma.Theorems.DupocBot.vs_DupocBot
import PrisonersDilemma.Theorems.DupocBot.vs_EBot
import PrisonersDilemma.Theorems.DupocBot.vs_MirrorBot
import PrisonersDilemma.Theorems.DupocBot.vs_OBot
import PrisonersDilemma.Theorems.DupocBot.vs_TitForTatBot
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.Theorems.CupodTrollBot.Helpers
import PrisonersDilemma.Theorems.CupodTrollBot.vs_CooperateBot
import PrisonersDilemma.Theorems.CupodTrollBot.vs_CupodBot
import PrisonersDilemma.Theorems.CupodTrollBot.vs_CupodTrollBot
import PrisonersDilemma.Theorems.CupodTrollBot.vs_DBot
import PrisonersDilemma.Theorems.CupodTrollBot.vs_DefectBot
import PrisonersDilemma.Theorems.CupodTrollBot.vs_DupocBot
import PrisonersDilemma.Theorems.CupodTrollBot.vs_EBot
import PrisonersDilemma.Theorems.CupodTrollBot.vs_MirrorBot
import PrisonersDilemma.Theorems.CupodTrollBot.vs_OBot
import PrisonersDilemma.Theorems.CupodTrollBot.vs_TitForTatBot
import PrisonersDilemma.Theorems.PrudentBot.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Base.Asymptotics
import PrisonersDilemma.Theorems.JustBot.Helpers

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

/-! ### JustBot vs EBot — the honest `(D, C)` outcome (floor formalized 2026-07-09).

HISTORY: `outcome_JustBot_vs_EBot` was RETIRED 2026-07-02 as an axiom artifact: EBot's
C-play against `.bot (DupocBot k)` crosses Dupoc's FAILED outer-probe search (vs
`.bot DefectBot`) — the `search_f` floor, unaffordable within the shared budget.

RESOLVED (2026-07-09): `no_provable_EBot_C_vs_botDupoc_tail` (the `.bot`-wrapped
variant, as for DBot above). JustBot defects at every budget; EBot's probes watch
JustBot defect vs `.bot DefectBot` and cooperate vs `.bot CooperateBot` (both
run-priced), so EBot cooperates: `outcome_JustBot_vs_EBot = (D, C)` for every
`k ≥ 2` (the Σ₁ price of the `.bot CooperateBot` probe certificate). -/

/-- The floor for the EBot pair: no ≤ k certificate concludes any formula whose spine
    tail is "EBot plays C against `.bot (DupocBot k)`" (JustBot's guard instance). -/
theorem no_provable_EBot_C_vs_botDupoc_tail (k : Nat) :
    ∀ K φ, Pf K φ → K ≤ k →
      rightTail φ = .plays EBot (.bot (DupocBot k)) .C → False := by
  intro K φ hp hK ht
  refine no_provable_probeFirst_tail_botOpp k DefectBot (.const .D)
      (.ite (.sim .opp (.bot CooperateBot)) .C (.const .C)
        (.ite (.sim .opp (.bot MirrorBot)) .C (.const .C) (.const .D)))
      .C .C (.plays .opp .self .C) (.const .C) (.const .D) ?_ ?_ K φ hp hK ?_
  · simpa [Formula.subst, Prog.subst, DupocBot] using
      interp_bot_DefectBot_plays_C_false (.bot (DupocBot k))
  · intro k' ψ c0 c1 h; simp at h
  · simpa [EBot, DupocBot] using ht

/-- JustBot's guard fails against EBot at every budget — the floor's bite. -/
theorem proofSearch_false_for_EBot_vs_botDupoc (k : Nat) :
    proofSearch k (.plays EBot (.bot (DupocBot k)) .C) = false := by
  cases h : proofSearch k (.plays EBot (.bot (DupocBot k)) .C) with
  | true =>
      exact absurd ((proofSearch_spec k _).mp h)
        (fun hp => no_provable_EBot_C_vs_botDupoc_tail k k _ hp le_rfl (by simp))
  | false => rfl

/-- JustBot defects against EBot: it can never afford the certificate of EBot's
    (true!) cooperation with `.bot DupocBot`. -/
theorem JustBot_plays_D_against_EBot (k fuel : Nat) :
    play (fuel + 2) (JustBot k) EBot = some .D := by
  have hg := proofSearch_false_for_EBot_vs_botDupoc k
  show eval (fuel + 2) (JustBot k) EBot (JustBot k) = some .D
  unfold JustBot
  simp [eval, Prog.subst, Formula.subst, hg]

/-- The `.bot CooperateBot` probe guard vs `.bot DupocBot` is Σ₁-certifiable at run
    price, feeding `JustBot_plays_C_against_bot_CooperateBot` at every `k ≥ 2`. -/
theorem proofSearch_true_bot_CooperateBot_vs_botDupoc (k : Nat) (hk : 2 ≤ k) :
    proofSearch k (.plays (.bot CooperateBot) (.bot (DupocBot k)) .C) = true :=
  (proofSearch_spec _ _).2 (Pf.atom
    ⟨PlaysProof.bot PlaysProof.const, by simp only [c_leaf, c_node]; omega⟩)

/-- EBot cooperates with JustBot: probe 1 watches JustBot defect vs `.bot DefectBot`
    (descend), probe 2 watches it cooperate vs `.bot CooperateBot` (the shared guard
    fires Σ₁-cheaply) — EBot takes the cooperate branch. Pure simulation, no floor. -/
theorem EBot_plays_C_against_JustBot (k fuel : Nat) (hk : 2 ≤ k) :
    play (fuel + 5) EBot (JustBot k) = some .C := by
  have hP1 : play (fuel + 3) (JustBot k) (.bot DefectBot) = some .D := by
    simpa [Nat.add_assoc] using JustBot_plays_D_against_bot_DefectBot_JB k (fuel + 1)
  have hG1 : eval (fuel + 4) EBot (JustBot k) (.sim .opp (.bot DefectBot)) = some .D := by
    simpa [Nat.add_assoc] using
      eval_sim_opp_bot_of_play (fuel + 3) EBot (JustBot k) DefectBot .D hP1
  have hP2 : play (fuel + 2) (JustBot k) (.bot CooperateBot) = some .C :=
    JustBot_plays_C_against_bot_CooperateBot k fuel
      (proofSearch_true_bot_CooperateBot_vs_botDupoc k hk)
  have hG2 : eval (fuel + 3) EBot (JustBot k) (.sim .opp (.bot CooperateBot)) = some .C := by
    simpa [Nat.add_assoc] using
      eval_sim_opp_bot_of_play (fuel + 2) EBot (JustBot k) CooperateBot .C hP2
  have hInner : eval (fuel + 4) EBot (JustBot k)
      (.ite (.sim .opp (.bot CooperateBot)) .C (.const .C)
        (.ite (.sim .opp (.bot MirrorBot)) .C (.const .C) (.const .D))) = some .C := by
    rw [eval_ite_from_guard _ _ _ _ _ _ _ _ hG2]; rfl
  show eval (fuel + 5) EBot (JustBot k)
      (.ite (.sim .opp (.bot DefectBot)) .C (.const .D)
        (.ite (.sim .opp (.bot CooperateBot)) .C (.const .C)
          (.ite (.sim .opp (.bot MirrorBot)) .C (.const .C) (.const .D)))) = some .C
  rw [eval_ite_from_guard _ _ _ _ _ _ _ _ hG1]
  exact hInner

/-- **The honest JustBot×EBot outcome — `(D, C)` for every `k ≥ 2`.** -/
theorem outcome_JustBot_vs_EBot (k fuel : Nat) (hk : 2 ≤ k) :
    outcome (fuel + 5) (JustBot k) EBot = some (.D, .C) := by
  have hA : play (fuel + 5) (JustBot k) EBot = some .D := by
    simpa [Nat.add_assoc] using JustBot_plays_D_against_EBot k (fuel + 3)
  have hB := EBot_plays_C_against_JustBot k fuel hk
  simp [outcome, hA, hB]
end PD.Theorems
