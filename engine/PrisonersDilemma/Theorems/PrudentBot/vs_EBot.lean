import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Bots.DBot
import PrisonersDilemma.Bots.OBot
import PrisonersDilemma.Bots.TitForTatBot
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Bots.LlmGenerations.PrudentBot
import PrisonersDilemma.Theorems.CooperateBot
import PrisonersDilemma.Theorems.DefectBot
import PrisonersDilemma.Theorems.CupodTrollBot
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Base.Asymptotics
import PrisonersDilemma.Bots.EBot
import PrisonersDilemma.Bots.CupodTrollBot
import PrisonersDilemma.Theorems.PrudentBot.Helpers

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

/-- Prudence atom for `.bot MirrorBot`: it mirrors `.bot DefectBot`'s defection. -/
theorem bot_MirrorBot_plays_D_vs_bot_DefectBot (fuel : Nat) :
    play (fuel + 4) (.bot MirrorBot) (.bot DefectBot) = some .D := by
  show eval (fuel + 4) (.bot MirrorBot) (.bot DefectBot) (.bot MirrorBot) = some .D
  simp [eval, Prog.subst, MirrorBot, DefectBot]

theorem prudence_provable_bot :
    Pf 81 (Formula.plays (.bot MirrorBot) (.bot DefectBot) Action.D) := by
  have hPlay : play 4 (.bot MirrorBot) (.bot DefectBot) = some .D := by
    simpa using bot_MirrorBot_plays_D_vs_bot_DefectBot 0
  exact Pf.atom (atom_monotone (3 ^ 4) 81 _ (by norm_num)
    (atom_complete_searchfree (.bot MirrorBot) (.bot DefectBot) Action.D 4 rfl rfl hPlay))

/-- **Löb premise for PrudentBot vs `.bot MirrorBot`.** Identical assembly to the
    bare-MirrorBot premise, but the mirror leg uses `botSimStep` (reading
    `.bot MirrorBot = .bot (.sim .opp .self)`) instead of `simStep`. -/
theorem prudent_bot_mirror_loeb_premise (k : Nat) (hk : 81 ≤ k) :
    Pf (50 * Nat.log2 k + 500)
      (.impl (.box k (Formula.plays (.bot MirrorBot) (PrudentBot k) Action.C))
             (Formula.plays (.bot MirrorBot) (PrudentBot k) Action.C)) := by
  -- TRANSCRIPT-TIGHT (see `prudent_mirror_loeb_premise`); the search-free prudence
  -- certificate costs ≤ 81 chars, whence `81 ≤ k`.
  have leg1 : Pf (20 * Nat.log2 k + 200)
      (.impl (.box k (Formula.plays (.bot MirrorBot) (PrudentBot k) Action.C))
             (Formula.plays (PrudentBot k) (.bot MirrorBot) Action.C)) := by
    refine Pf.searchThenSearch_t k k 81
      (Formula.plays .opp .self Action.C)
      (Formula.plays .opp (.bot DefectBot) Action.D)
      Action.C Action.D (.const Action.D) (PrudentBot k) (.bot MirrorBot) rfl
      prudence_provable_bot (by omega) ?_
    simp only [numCost, Formula.subst, Prog.subst, Formula.size, Prog.size, PrudentBot, MirrorBot,
      DefectBot, c_guard]
    omega
  have leg2 : Pf (20 * Nat.log2 k + 200)
      (.impl (Formula.plays (PrudentBot k) (.bot MirrorBot) Action.C)
             (Formula.plays (.bot MirrorBot) (PrudentBot k) Action.C)) := by
    refine Pf.botSimStep (.bot MirrorBot) .opp .self (PrudentBot k) Action.C rfl ?_
    simp only [Formula.subst, Prog.subst, numCost, Formula.size, Prog.size, PrudentBot, MirrorBot, DefectBot]
    omega
  refine Pf.implTrans _ _ _ (20 * Nat.log2 k + 200) (20 * Nat.log2 k + 200) leg1 leg2 ?_
  simp only [numCost, Formula.size, Prog.size, PrudentBot, MirrorBot, DefectBot]
  omega

/-- Once both searches fire, PrudentBot cooperates with `.bot MirrorBot`. -/
theorem PrudentBot_plays_C_against_bot_MirrorBot (k fuel : Nat)
    (hCoop : proofSearch k (Formula.plays (.bot MirrorBot) (PrudentBot k) Action.C) = true)
    (hPrud : proofSearch k (Formula.plays (.bot MirrorBot) (.bot DefectBot) Action.D) = true) :
    play (fuel + 3) (PrudentBot k) (.bot MirrorBot) = some .C := by
  show eval (fuel + 3) (PrudentBot k) (.bot MirrorBot) (PrudentBot k) = some .C
  unfold PrudentBot at hCoop ⊢
  simp [eval, Prog.subst, Formula.subst, hCoop, hPrud]

/-- When PrudentBot's cooperation search fails, it defects against `.bot MirrorBot`. -/
theorem PrudentBot_plays_D_against_bot_MirrorBot (k fuel : Nat)
    (hf : proofSearch k (Formula.plays (.bot MirrorBot) (PrudentBot k) Action.C) = false) :
    play (fuel + 2) (PrudentBot k) (.bot MirrorBot) = some .D := by
  show eval (fuel + 2) (PrudentBot k) (.bot MirrorBot) (PrudentBot k) = some .D
  unfold PrudentBot at hf ⊢
  simp [eval, Prog.subst, Formula.subst, hf]

/-- Inversion for the `.bot MirrorBot` leg. -/
theorem proofSearch_k_of_play_bot_MirrorBot_prudent
    (k n : Nat) (h : play n (.bot MirrorBot) (PrudentBot k) = some .C) :
    proofSearch k (Formula.plays (.bot MirrorBot) (PrudentBot k) Action.C) = true := by
  cases hps : proofSearch k (Formula.plays (.bot MirrorBot) (PrudentBot k) Action.C) with
  | true  => rfl
  | false =>
    exfalso
    have hPrudD : ∀ f, play (f + 2) (PrudentBot k) (.bot MirrorBot) = some .D :=
      fun f => PrudentBot_plays_D_against_bot_MirrorBot k f hps
    have hMirD : play (n + 4) (.bot MirrorBot) (PrudentBot k) = some .D := by
      have hP : play (n + 2) (PrudentBot k) (.bot MirrorBot) = some .D := hPrudD n
      show eval (n + 4) (.bot MirrorBot) (PrudentBot k) (.bot MirrorBot) = some .D
      simpa [play, eval, Prog.subst, MirrorBot] using hP
    have hMonoC : play (n + 4) (.bot MirrorBot) (PrudentBot k) = some .C := by
      unfold play at h ⊢
      exact eval_mono_le h (n + 4) (by omega)
    rw [hMonoC] at hMirD
    cases hMirD

/-- **PrudentBot cooperates with `.bot MirrorBot`**, for all large enough `k`.
    Discharges the former `PrudentBot_plays_C_vs_bot_MirrorBot` axiom. -/
theorem PrudentBot_plays_C_vs_bot_MirrorBot :
    ∃ k₂, ∀ k, k₂ < k →
      ∃ fuel, play fuel (PrudentBot k) (.bot MirrorBot) = some .C := by
  let φ : Nat → Formula := fun k => Formula.plays (.bot MirrorBot) (PrudentBot k) Action.C
  have hLoeb : ∀ k, k > 81 →
      Pf (50 * Nat.log2 k + 500) (.impl (.box k (φ k)) (φ k)) :=
    fun k hk => prudent_bot_mirror_loeb_premise k (by omega)
  have hφsz : ∀ k, (φ k).size ≤ 100 * Nat.log2 k + 1000 := by
    intro k
    show (Formula.plays (.bot MirrorBot) (PrudentBot k) Action.C).size ≤ _
    simp only [numCost, Formula.size, Prog.size, PrudentBot, MirrorBot, DefectBot]
    omega
  have hpm : ∀ k, 50 * Nat.log2 k + 500 ≤ 100 * Nat.log2 k + 1000 := fun k => by omega
  obtain ⟨k₂, hk₂⟩ := pblt_engine_id φ (fun k => 50 * Nat.log2 k + 500) 81 hφsz hpm hLoeb
  refine ⟨max k₂ 81, fun k hk => ⟨3, ?_⟩⟩
  have hk2 : k > k₂ := lt_of_le_of_lt (le_max_left _ _) hk
  have hkP : (81 : Nat) ≤ k :=
    le_of_lt (lt_of_le_of_lt (le_max_right _ _) hk)
  obtain ⟨m, hm⟩ := hk₂ k hk2
  obtain ⟨n, hMir⟩ := Pf_sound m (φ k) hm
  have hCoopPS : proofSearch k (Formula.plays (.bot MirrorBot) (PrudentBot k) Action.C) = true :=
    proofSearch_k_of_play_bot_MirrorBot_prudent k n hMir
  have hPrudPS : proofSearch k (Formula.plays (.bot MirrorBot) (.bot DefectBot) Action.D) = true :=
    (proofSearch_spec _ _).2 (Pf_mono prudence_provable_bot hkP)
  simpa using PrudentBot_plays_C_against_bot_MirrorBot k 0 hCoopPS hPrudPS
-- EBot --
/-- EBot defects against `.bot DefectBot`. -/
theorem EBot_plays_D_vs_bot_DefectBot (k : Nat) :
    play (k + 6) EBot (.bot DefectBot) = some .D := by
  show eval (k + 6) EBot (.bot DefectBot) EBot = some .D
  have hOuterG : eval (k + 5) EBot (.bot DefectBot) (.sim .opp (.bot DefectBot)) = some .D := by
    simp only [eval, Prog.subst, DefectBot]
  have hInnerG : eval (k + 4) EBot (.bot DefectBot) (.sim .opp (.bot CooperateBot)) = some .D := by
    simp only [eval, Prog.subst, DefectBot]
  have hInnerInnerG : eval (k + 3) EBot (.bot DefectBot) (.sim .opp (.bot MirrorBot)) = some .D := by
    simp only [eval, Prog.subst, DefectBot]
  have hInnerInnerIte : eval (k + 4) EBot (.bot DefectBot)
      (.ite (.sim .opp (.bot MirrorBot)) .C (.const .C) (.const .D)) = some .D := by
    rw [eval_ite_from_guard _ _ _ _ _ _ _ _ hInnerInnerG]; rfl
  have hInnerIte : eval (k + 5) EBot (.bot DefectBot)
      (.ite (.sim .opp (.bot CooperateBot)) .C (.const .C)
        (.ite (.sim .opp (.bot MirrorBot)) .C (.const .C) (.const .D))) = some .D := by
    rw [eval_ite_from_guard _ _ _ _ _ _ _ _ hInnerG]
    exact hInnerInnerIte
  show eval (k + 6) EBot (.bot DefectBot)
      (.ite (.sim .opp (.bot DefectBot)) .C (.const .D)
        (.ite (.sim .opp (.bot CooperateBot)) .C (.const .C)
          (.ite (.sim .opp (.bot MirrorBot)) .C (.const .C) (.const .D)))) = some .D
  rw [eval_ite_from_guard _ _ _ _ _ _ _ _ hOuterG]
  exact hInnerIte

/-- Löb premise for PrudentBot cooperating with `.bot MirrorBot`. -/
theorem prudent_botmirror_loeb_premise (k : Nat) (hk : 81 ≤ k) :
    Pf (50 * Nat.log2 k + 500)
      (.impl (.box k (.plays (.bot MirrorBot) (PrudentBot k) .C))
             (.plays (.bot MirrorBot) (PrudentBot k) .C)) :=
  prudent_bot_mirror_loeb_premise k hk

/-- PrudentBot's outer guard against `.bot MirrorBot` is provable for large k. -/
theorem prudent_botmirror_coop :
    ∃ k₂, ∀ k, k₂ < k →
      proofSearch k (.plays (.bot MirrorBot) (PrudentBot k) .C) = true := by
  let φ : Nat → Formula := fun k => .plays (.bot MirrorBot) (PrudentBot k) .C
  have hLoeb :
      ∀ k, k > 81 → Pf (50 * Nat.log2 k + 500) (.impl (.box k (φ k)) (φ k)) := by
    intro k hk
    exact prudent_botmirror_loeb_premise k (by omega)
  have hφsz : ∀ k, (φ k).size ≤ 100 * Nat.log2 k + 1000 := by
    intro k
    show (Formula.plays (.bot MirrorBot) (PrudentBot k) Action.C).size ≤ _
    simp only [numCost, Formula.size, Prog.size, PrudentBot, MirrorBot, DefectBot]
    omega
  have hpm : ∀ k, 50 * Nat.log2 k + 500 ≤ 100 * Nat.log2 k + 1000 := fun k => by omega
  obtain ⟨k₂, hk₂⟩ := pblt_engine_id φ (fun k => 50 * Nat.log2 k + 500) 81 hφsz hpm hLoeb
  refine ⟨k₂, fun k hk => ?_⟩
  obtain ⟨m, hm⟩ := hk₂ k hk
  have hInterp : (φ k).interp := Pf_sound m (φ k) hm
  obtain ⟨n, hplay⟩ := hInterp
  rcases n with _ | _ | n
  · simp [play, eval] at hplay
  · simp [play, eval] at hplay
  · have heq : play (n + 2) (.bot MirrorBot) (PrudentBot k)
             = play n (PrudentBot k) (.bot MirrorBot) := by
      simp [play, eval, Prog.subst, MirrorBot]
    rw [heq] at hplay
    exact prudent_outer_true_of_play_C k n (.bot MirrorBot) hplay

/-! ### PrudentBot vs EBot — the honest `(D, C)` outcome (floor formalized 2026-07-09).

HISTORY: `outcome_PrudentBot_vs_EBot` (mutual cooperation at a common budget) was
RETIRED 2026-07-02 as an axiom artifact: EBot's C-play against `PrudentBot k` crosses
PrudentBot's own FAILED outer search (the probe vs `.bot DefectBot`), so its certificate
pays the `search_f` floor — cost > k for every k — and PrudentBot's outer guard can
never see "EBot plays C vs me" within its own budget. See `DECIDABILITY_ROADMAP.md`.

RESOLVED (2026-07-09): the floor is a THEOREM — `no_provable_EBot_C_vs_Prudent_tail`,
an instance of `no_provable_probeFirst_C_tail` (Base/Exclusion.lean; PrudentBot matches
the budget-`k` searcher shape with its prudence search as the then-branch). PrudentBot
defects at every budget. EBot's own play is pure run-priced simulation: its probes
watch PrudentBot defect vs `.bot DefectBot` (outer guard refuted by soundness) and vs
`.bot CooperateBot` (outer guard may or may not fire, but the prudence guard is refuted
— CooperateBot never defects — so both branches defect), then watch PrudentBot
COOPERATE vs `.bot MirrorBot` (the Löb fixpoint, `prudent_botmirror_coop`) — so EBot
cooperates for k past the Löb threshold: `outcome_PrudentBot_vs_EBot = (D, C)`. -/

/-- The floor for the EBot pair: no ≤ k certificate concludes any formula whose spine
    tail is "EBot plays C against `PrudentBot k`". -/
theorem no_provable_EBot_C_vs_Prudent_tail (k : Nat) :
    ∀ K φ, Pf K φ → K ≤ k →
      rightTail φ = .plays EBot (PrudentBot k) .C → False := by
  intro K φ hp hK ht
  refine no_provable_probeFirst_tail k DefectBot (.const .D)
      (.ite (.sim .opp (.bot CooperateBot)) .C (.const .C)
        (.ite (.sim .opp (.bot MirrorBot)) .C (.const .C) (.const .D)))
      .C .C (.plays .opp .self .C)
      (.search k (.plays .opp (.bot DefectBot) .D) (.const .C) (.const .D))
      (.const .D) ?_ ?_ K φ hp hK ?_
  · simpa [Formula.subst, Prog.subst, PrudentBot] using
      interp_bot_DefectBot_plays_C_false (PrudentBot k)
  · intro k' ψ c0 c1 h; simp at h
  · simpa [EBot, PrudentBot] using ht

/-- PrudentBot's outer guard fails against EBot at every budget — the floor's bite. -/
theorem proofSearch_false_for_EBot_vs_Prudent (k : Nat) :
    proofSearch k (.plays EBot (PrudentBot k) .C) = false := by
  cases h : proofSearch k (.plays EBot (PrudentBot k) .C) with
  | true =>
      exact absurd ((proofSearch_spec k _).mp h)
        (fun hp => no_provable_EBot_C_vs_Prudent_tail k k _ hp le_rfl (by simp))
  | false => rfl

/-- PrudentBot defects against EBot: it can never afford the certificate of EBot's
    (true!) cooperation. -/
theorem PrudentBot_plays_D_against_EBot (k fuel : Nat) :
    play (fuel + 2) (PrudentBot k) EBot = some .D :=
  PrudentBot_plays_D_of_search_false k fuel EBot (proofSearch_false_for_EBot_vs_Prudent k)

/-- Probe 1: `.bot DefectBot` never cooperates, so PrudentBot's outer guard is refuted
    by soundness and PrudentBot defects on EBot's first probe. -/
theorem proofSearch_false_bot_DefectBot_vs_Prudent (k : Nat) :
    proofSearch k (.plays (.bot DefectBot) (PrudentBot k) .C) = false := by
  cases h : proofSearch k (.plays (.bot DefectBot) (PrudentBot k) .C) with
  | true => exact absurd (proofSearch_sound _ _ h) (interp_bot_DefectBot_plays_C_false _)
  | false => rfl

theorem PrudentBot_plays_D_vs_bot_DefectBot (k fuel : Nat) :
    play (fuel + 2) (PrudentBot k) (.bot DefectBot) = some .D :=
  PrudentBot_plays_D_of_search_false k fuel _ (proofSearch_false_bot_DefectBot_vs_Prudent k)

/-- Probe 2, prudence side: `.bot CooperateBot` never defects, so PrudentBot's inner
    (prudence) guard is refuted by soundness. -/
theorem proofSearch_false_prudence_bot_CooperateBot (k : Nat) :
    proofSearch k (.plays (.bot CooperateBot) (.bot DefectBot) .D) = false := by
  cases h : proofSearch k (.plays (.bot CooperateBot) (.bot DefectBot) .D) with
  | true => exact absurd (proofSearch_sound _ _ h) (interp_bot_CooperateBot_plays_D_false _)
  | false => rfl

/-- Probe 2: PrudentBot defects against `.bot CooperateBot` REGARDLESS of whether its
    outer guard fires — if it fails, the else-branch defects; if it fires, the prudence
    guard is refuted (CooperateBot is a sucker) and the inner else defects. -/
theorem PrudentBot_plays_D_vs_bot_CooperateBot (k fuel : Nat) :
    play (fuel + 3) (PrudentBot k) (.bot CooperateBot) = some .D := by
  cases h1 : proofSearch k (.plays (.bot CooperateBot) (PrudentBot k) .C) with
  | false =>
      simpa [Nat.add_assoc] using
        PrudentBot_plays_D_of_search_false k (fuel + 1) (.bot CooperateBot) h1
  | true =>
      exact prudent_eval_inner_false k fuel (.bot CooperateBot) h1
        (proofSearch_false_prudence_bot_CooperateBot k)

/-- Probe 3, at arbitrary fuel: past the Löb threshold, PrudentBot cooperates with
    `.bot MirrorBot` (outer guard by `prudent_botmirror_coop`, prudence by
    `prudence_provable_bot`). Strengthens `PrudentBot_plays_C_vs_bot_MirrorBot`
    (which fixes `fuel = 3`) to every fuel offset, as the EBot assembly needs. -/
theorem PrudentBot_plays_C_vs_bot_MirrorBot_fuel :
    ∃ k₂, ∀ k, k₂ < k → ∀ fuel,
      play (fuel + 3) (PrudentBot k) (.bot MirrorBot) = some .C := by
  obtain ⟨k₂, hOuter⟩ := prudent_botmirror_coop
  refine ⟨max k₂ 81, fun k hk fuel => ?_⟩
  have h1 := hOuter k (lt_of_le_of_lt (le_max_left _ _) hk)
  have h2 : proofSearch k (.plays (.bot MirrorBot) (.bot DefectBot) .D) = true :=
    (proofSearch_spec _ _).2 (Pf_mono prudence_provable_bot
      (le_of_lt (lt_of_le_of_lt (le_max_right _ _) hk)))
  exact prudent_eval_both_true k fuel _ h1 h2

/-- EBot cooperates with PrudentBot past the Löb threshold: probes 1 and 2 watch
    PrudentBot defect (descend), probe 3 watches it cooperate with `.bot MirrorBot`
    (the Löb fixpoint) — EBot takes the cooperate branch. Pure simulation, no floor. -/
theorem EBot_plays_C_against_PrudentBot :
    ∃ k₂, ∀ k, k₂ < k → ∀ fuel,
      play (fuel + 7) EBot (PrudentBot k) = some .C := by
  obtain ⟨k₂, hMir⟩ := PrudentBot_plays_C_vs_bot_MirrorBot_fuel
  refine ⟨k₂, fun k hk fuel => ?_⟩
  have hP1 : play (fuel + 5) (PrudentBot k) (.bot DefectBot) = some .D := by
    simpa [Nat.add_assoc] using PrudentBot_plays_D_vs_bot_DefectBot k (fuel + 3)
  have hP2 : play (fuel + 4) (PrudentBot k) (.bot CooperateBot) = some .D := by
    simpa [Nat.add_assoc] using PrudentBot_plays_D_vs_bot_CooperateBot k (fuel + 1)
  have hP3 : play (fuel + 3) (PrudentBot k) (.bot MirrorBot) = some .C := hMir k hk fuel
  have hG1 : eval (fuel + 6) EBot (PrudentBot k) (.sim .opp (.bot DefectBot)) = some .D := by
    simpa [Nat.add_assoc] using
      eval_sim_opp_bot_of_play (fuel + 5) EBot (PrudentBot k) DefectBot .D hP1
  have hG2 : eval (fuel + 5) EBot (PrudentBot k) (.sim .opp (.bot CooperateBot)) = some .D := by
    simpa [Nat.add_assoc] using
      eval_sim_opp_bot_of_play (fuel + 4) EBot (PrudentBot k) CooperateBot .D hP2
  have hG3 : eval (fuel + 4) EBot (PrudentBot k) (.sim .opp (.bot MirrorBot)) = some .C := by
    simpa [Nat.add_assoc] using
      eval_sim_opp_bot_of_play (fuel + 3) EBot (PrudentBot k) MirrorBot .C hP3
  have hIte3 : eval (fuel + 5) EBot (PrudentBot k)
      (.ite (.sim .opp (.bot MirrorBot)) .C (.const .C) (.const .D)) = some .C := by
    rw [eval_ite_from_guard _ _ _ _ _ _ _ _ hG3]; rfl
  have hIte2 : eval (fuel + 6) EBot (PrudentBot k)
      (.ite (.sim .opp (.bot CooperateBot)) .C (.const .C)
        (.ite (.sim .opp (.bot MirrorBot)) .C (.const .C) (.const .D))) = some .C := by
    rw [eval_ite_from_guard _ _ _ _ _ _ _ _ hG2]
    exact hIte3
  show eval (fuel + 7) EBot (PrudentBot k)
      (.ite (.sim .opp (.bot DefectBot)) .C (.const .D)
        (.ite (.sim .opp (.bot CooperateBot)) .C (.const .C)
          (.ite (.sim .opp (.bot MirrorBot)) .C (.const .C) (.const .D)))) = some .C
  rw [eval_ite_from_guard _ _ _ _ _ _ _ _ hG1]
  exact hIte2

/-- **The honest PrudentBot×EBot outcome — `(D, C)` past the Löb threshold.** The
    simulator cooperates (its third probe watched the PrudentBot↔MirrorBot Löb
    cooperation), the searcher defects (the floor: EBot's cooperation certificate
    crosses PrudentBot's own failed probe search). -/
theorem outcome_PrudentBot_vs_EBot :
    ∃ k₂, ∀ k, k₂ < k → ∀ fuel,
      outcome (fuel + 7) (PrudentBot k) EBot = some (.D, .C) := by
  obtain ⟨k₂, hE⟩ := EBot_plays_C_against_PrudentBot
  refine ⟨k₂, fun k hk fuel => ?_⟩
  have hA : play (fuel + 7) (PrudentBot k) EBot = some .D := by
    simpa [Nat.add_assoc] using PrudentBot_plays_D_against_EBot k (fuel + 5)
  have hB := hE k hk fuel
  simp [outcome, hA, hB]
end PD.Theorems
