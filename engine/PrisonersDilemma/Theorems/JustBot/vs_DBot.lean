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

--- DBot ---
-- .bot (DupocBot k) defects against .bot DefectBot: its guard fails (DefectBot plays D)
theorem bot_DupocBot_plays_D_against_bot_DefectBot_JB (k fuel : Nat) :
    play (fuel + 3) (.bot (DupocBot k)) (.bot DefectBot) = some .D := by
  have hg := ps_false_bot_DefectBot_vs_bot_DupocBot_JB k
  show eval (fuel + 3) (.bot (DupocBot k)) (.bot DefectBot) (.bot (DupocBot k)) = some .D
  unfold DupocBot at hg ⊢
  simp [eval, Prog.subst, Formula.subst, hg]

-- DBot cooperates against .bot (DupocBot k): its sim probe sees D, so takes .const .C
theorem DBot_plays_C_against_bot_DupocBot_JB (k fuel : Nat) :
    play (fuel + 5) DBot (.bot (DupocBot k)) = some .C := by
  have hInner : play (fuel + 3) (.bot (DupocBot k)) (.bot DefectBot) = some .D :=
    bot_DupocBot_plays_D_against_bot_DefectBot_JB k fuel
  have hGuard : eval (fuel + 4) DBot (.bot (DupocBot k)) (.sim .opp (.bot DefectBot)) = some .D := by
    simpa [Nat.add_assoc] using
      eval_sim_opp_bot_of_play (fuel + 3) DBot (.bot (DupocBot k)) DefectBot .D hInner
  have hPlay := play_ite_from_guard
    fuel 4 DBot (.bot (DupocBot k)) (.sim .opp (.bot DefectBot))
    (.const Action.D) (.const Action.C) Action.C Action.D
    (by rfl) hGuard
  simpa [eval] using hPlay
-- DBot cooperates against JustBot k: sim probe sees JustBot defects → DBot cooperates
theorem DBot_plays_C_against_JustBot_JB (k fuel : Nat) :
    play (fuel + 4) DBot (JustBot k) = some .C := by
  have hInner : play (fuel + 2) (JustBot k) (.bot DefectBot) = some .D :=
    JustBot_plays_D_against_bot_DefectBot_JB k fuel
  have hGuard : eval (fuel + 3) DBot (JustBot k) (.sim .opp (.bot DefectBot)) = some .D := by
    simpa [Nat.add_assoc] using
      eval_sim_opp_bot_of_play (fuel + 2) DBot (JustBot k) DefectBot .D hInner
  have hPlay := play_ite_from_guard
    fuel 3 DBot (JustBot k) (.sim .opp (.bot DefectBot))
    (.const Action.D) (.const Action.C) Action.C Action.D
    (by rfl) hGuard
  simpa [eval] using hPlay

/-! ### JustBot vs DBot — the honest `(D, C)` outcome (floor formalized 2026-07-09).

HISTORY: `outcome_JustBot_vs_DBot` was RETIRED 2026-07-02 as an axiom artifact: DBot's
C-play against `.bot (DupocBot k)` (JustBot's frozen guard target) crosses Dupoc's
FAILED probe search (vs `.bot DefectBot`), so its certificate pays the `search_f`
floor — cost > k for every k — and JustBot's guard can never see "DBot plays C vs
`.bot DupocBot`" within the shared budget `k`.

RESOLVED (2026-07-09): the floor is a THEOREM — `no_provable_DBot_C_vs_botDupoc_tail`,
an instance of `no_provable_probeFirst_tail_botOpp` (Base/Exclusion.lean; the
`.bot`-wrapped-searcher variant, since JustBot's guard target is the FROZEN
`.bot (DupocBot k)`). JustBot's guard fails at every budget, so JustBot defects while
DBot — whose probe already watched JustBot defect vs `.bot DefectBot` — cooperates:
`outcome_JustBot_vs_DBot = (D, C)` at every budget. -/

/-- The floor for the DBot pair: no ≤ k certificate concludes any formula whose spine
    tail is "DBot plays C against `.bot (DupocBot k)`" (JustBot's guard instance). -/
theorem no_provable_DBot_C_vs_botDupoc_tail (k : Nat) :
    ∀ K φ, Pf K φ → K ≤ k →
      rightTail φ = .plays DBot (.bot (DupocBot k)) .C → False := by
  intro K φ hp hK ht
  refine no_provable_probeFirst_tail_botOpp k DefectBot (.const .D) (.const .C) .C .C
      (.plays .opp .self .C) (.const .C) (.const .D) ?_ ?_ K φ hp hK ?_
  · simpa [Formula.subst, Prog.subst, DupocBot] using
      interp_bot_DefectBot_plays_C_false (.bot (DupocBot k))
  · intro k' ψ c0 c1 h; simp at h
  · simpa [DBot, DupocBot] using ht

/-- JustBot's guard fails against DBot at every budget — the floor's bite. -/
theorem proofSearch_false_for_DBot_vs_botDupoc (k : Nat) :
    proofSearch k (.plays DBot (.bot (DupocBot k)) .C) = false := by
  cases h : proofSearch k (.plays DBot (.bot (DupocBot k)) .C) with
  | true =>
      exact absurd ((proofSearch_spec k _).mp h)
        (fun hp => no_provable_DBot_C_vs_botDupoc_tail k k _ hp le_rfl (by simp))
  | false => rfl

/-- JustBot defects against DBot: it can never afford the certificate of DBot's
    (true!) cooperation with `.bot DupocBot`. -/
theorem JustBot_plays_D_against_DBot (k fuel : Nat) :
    play (fuel + 2) (JustBot k) DBot = some .D := by
  have hg := proofSearch_false_for_DBot_vs_botDupoc k
  show eval (fuel + 2) (JustBot k) DBot (JustBot k) = some .D
  unfold JustBot
  simp [eval, Prog.subst, Formula.subst, hg]

/-- **The honest JustBot×DBot outcome — `(D, C)` at every budget.** -/
theorem outcome_JustBot_vs_DBot (k fuel : Nat) :
    outcome (fuel + 4) (JustBot k) DBot = some (.D, .C) := by
  have hA : play (fuel + 4) (JustBot k) DBot = some .D := by
    simpa [Nat.add_assoc] using JustBot_plays_D_against_DBot k (fuel + 2)
  have hB : play (fuel + 4) DBot (JustBot k) = some .C :=
    DBot_plays_C_against_JustBot_JB k fuel
  simp [outcome, hA, hB]

/-! ### JustBot2 — the FREEZE TRICK: cooperation with DBot recovered (2026-07-09).

`outcome_JustBot_vs_DBot = (D, C)` above is an artifact of BUDGET-TYING, not of the
matchup: JustBot's guard fact "DBot plays C vs `.bot (DupocBot k)`" costs exactly
`k + log₂ k + 26` (the snapshot's `search_f` floor `k`, plus the `atomNeg` refutation
and the replay overhead) — one floor above JustBot's own budget `k`. `JustBot2 K k`
decouples the dials: at `K ≥ k + log₂ k + 26` the certificate fits, the guard fires,
and the FairBot×DBot handshake returns at staggered internal budgets. Constructive
companion to the floor impossibilities: the `(D, C)` outcomes are about budget-TIED
bots, not about the pairs. -/

/-- **The staggered certificate**: DBot's cooperation with the frozen snapshot IS
    affordable one floor up — the honest price of the fact JustBot's guard requests.
    Structure: replay DBot's `ite` (else-branch C), whose guard simulates the snapshot
    against `.bot DefectBot`; the snapshot's probe search fails, certified by
    `search_f` over the `atomNeg` refutation (DefectBot's actual D-play refutes the
    C-claim) — paying the floor `k`. Total: `k + log₂ k + 26`. -/
theorem provable_DBot_C_vs_botDupoc (k K : Nat) (hK : k + Nat.log2 k + 26 ≤ K) :
    Pf K (.plays DBot (.bot (DupocBot k)) .C) := by
  have hneg : Pf (Nat.log2 k + 20)
      (.neg (.plays (.bot DefectBot) (.bot (DupocBot k)) .C)) := by
    refine Pf.atomNeg (.bot DefectBot) (.bot (DupocBot k)) .D .C 2
      ⟨PlaysProof.bot PlaysProof.const, by decide⟩ (by decide) ?_
    simp only [Formula.size, Prog.size, DupocBot, DefectBot, numCost]
    omega
  refine Pf.atom
    ⟨PlaysProof.ite_f
      (PlaysProof.sim (PlaysProof.bot (PlaysProof.search_f hneg PlaysProof.const)))
      (by decide) PlaysProof.const, ?_⟩
  simp only [c_leaf, c_node]
  omega

/-- JustBot2's guard fires against DBot once `K` clears the staggered price. -/
theorem proofSearch_true_DBot_vs_botDupoc (k K : Nat)
    (hK : k + Nat.log2 k + 26 ≤ K) :
    proofSearch K (.plays DBot (.bot (DupocBot k)) .C) = true :=
  (proofSearch_spec _ _).2 (provable_DBot_C_vs_botDupoc k K hK)

/-- JustBot2 cooperates with DBot: the staggered budget affords the certificate the
    single-parameter JustBot could never see. -/
theorem JustBot2_plays_C_against_DBot (k K fuel : Nat)
    (hK : k + Nat.log2 k + 26 ≤ K) :
    play (fuel + 2) (JustBot2 K k) DBot = some .C := by
  have hg := proofSearch_true_DBot_vs_botDupoc k K hK
  show eval (fuel + 2) (JustBot2 K k) DBot (JustBot2 K k) = some .C
  unfold JustBot2
  simp [eval, Prog.subst, Formula.subst, hg]

/-- JustBot2's guard fails against `.bot DefectBot` at every budget (the formula is
    false — DefectBot never cooperates with the snapshot). -/
theorem ps_false_bot_DefectBot_vs_botDupoc_J2 (k K : Nat) :
    proofSearch K (.plays (.bot DefectBot) (.bot (DupocBot k)) .C) = false := by
  cases h : proofSearch K (.plays (.bot DefectBot) (.bot (DupocBot k)) .C) with
  | true => exact absurd (proofSearch_sound _ _ h) (interp_bot_DefectBot_plays_C_false _)
  | false => rfl

theorem JustBot2_plays_D_against_bot_DefectBot (k K fuel : Nat) :
    play (fuel + 2) (JustBot2 K k) (.bot DefectBot) = some .D := by
  have hg := ps_false_bot_DefectBot_vs_botDupoc_J2 k K
  show eval (fuel + 2) (JustBot2 K k) (.bot DefectBot) (JustBot2 K k) = some .D
  unfold JustBot2
  simp [eval, Prog.subst, Formula.subst, hg]

/-- DBot cooperates with JustBot2: its probe watches JustBot2 defect vs
    `.bot DefectBot`. -/
theorem DBot_plays_C_against_JustBot2 (k K fuel : Nat) :
    play (fuel + 4) DBot (JustBot2 K k) = some .C := by
  have hInner : play (fuel + 2) (JustBot2 K k) (.bot DefectBot) = some .D :=
    JustBot2_plays_D_against_bot_DefectBot k K fuel
  have hGuard : eval (fuel + 3) DBot (JustBot2 K k) (.sim .opp (.bot DefectBot)) = some .D := by
    simpa [Nat.add_assoc] using
      eval_sim_opp_bot_of_play (fuel + 2) DBot (JustBot2 K k) DefectBot .D hInner
  have hPlay := play_ite_from_guard
    fuel 3 DBot (JustBot2 K k) (.sim .opp (.bot DefectBot))
    (.const Action.D) (.const Action.C) Action.C Action.D
    (by rfl) hGuard
  simpa [eval] using hPlay

/-- **The recovered handshake — `(C, C)` at staggered internal budgets, every `k`.**
    The freeze trick in action: `JustBot2 (2k+64) k` affords the certificate of DBot's
    cooperation with its frozen snapshot (floor `k` < budget `2k+64`), while DBot's
    run-priced probe needs no proofs at all. Compare `outcome_JustBot_vs_DBot =
    (D, C)`: same matchup, budgets tied, guard starved by its own floor. -/
theorem outcome_JustBot2_vs_DBot (k fuel : Nat) :
    outcome (fuel + 4) (JustBot2 (2*k + 64) k) DBot = some (.C, .C) := by
  have hK : k + Nat.log2 k + 26 ≤ 2*k + 64 := by
    have := log2_le_self k
    omega
  have hA : play (fuel + 4) (JustBot2 (2*k + 64) k) DBot = some .C := by
    simpa [Nat.add_assoc] using JustBot2_plays_C_against_DBot k (2*k + 64) (fuel + 2) hK
  have hB : play (fuel + 4) DBot (JustBot2 (2*k + 64) k) = some .C :=
    DBot_plays_C_against_JustBot2 k (2*k + 64) fuel
  simp [outcome, hA, hB]
end PD.Theorems
