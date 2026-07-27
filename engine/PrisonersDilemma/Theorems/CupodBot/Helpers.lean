import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Bots.CupodBot
import PrisonersDilemma.Bots.TitForTatBot
import PrisonersDilemma.Bots.DBot
import PrisonersDilemma.Bots.OBot
import PrisonersDilemma.Bots.EBot
import PrisonersDilemma.Bots.MirrorBot
import PrisonersDilemma.Theorems.CooperateBot.Helpers
import PrisonersDilemma.Theorems.CooperateBot.vs_CooperateBot
import PrisonersDilemma.Theorems.CooperateBot.vs_DefectBot
import PrisonersDilemma.Theorems.DefectBot.Helpers
import PrisonersDilemma.Theorems.DefectBot.vs_DefectBot
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Base.Asymptotics

open PD
open PD.Bots
open PD.BaseTheorems
namespace PD.Theorems
-- CooperateBot --

/-- Proof search is false for CooperateBot -/
theorem proofSearch_false_for_CooperateBot (k : Nat) :
    proofSearch k (.plays CooperateBot (CupodBot k) .D) = false := by
  cases h : proofSearch k (.plays CooperateBot (CupodBot k) .D) with
  | true  => exact absurd (proofSearch_sound _ _ h)
                          (interp_CooperateBot_plays_D_false _)
  | false => rfl


-- DefectBot --

/-- Proof search is true for DefectBot vs CupodBot k at budget/index
    `atom_cost 1`. DefectBot ignores its opponent
    so the play holds for any CupodBot index. -/
theorem proofSearch_true_for_DefectBot :
    ∃ k, proofSearch k (.plays DefectBot (CupodBot k) .D) = true :=
  let k := atom_cost 1
  ⟨k, (proofSearch_spec _ _).2 (Pf.atom ⟨PlaysProof.const, by decide⟩)⟩


-- CupodBot --

/-- CUPOD-specific Löb premise (critch22 Theorem 3.4 substitution into PBLT),
    **character-faithful**. The `searchBranch` derivation concluding
    `□_k (CUPOD plays D vs CUPOD) → (CUPOD plays D vs CUPOD)` has size exactly
    `5 * log2 k + 33` characters (the guard `ψ.subst (CupodBot k) (CupodBot k)`
    reduces to `.plays (CupodBot k) (CupodBot k) .D`; each `CupodBot k` costs
    `log2 k + 7`). By `linear_log2_add_le 5 33` this fits within budget `k` for
    all `k ≥ K₀`, so the implication is `Pf k` outright — exactly the
    PBLT-shaped hypothesis (no looser `∃ m` budget).

    The conclusion formula is *definitionally* the `searchBranch` conclusion: the
    guard `(.plays .opp .self .D).subst (CupodBot k) (CupodBot k)` unfolds to
    `.plays (CupodBot k) (CupodBot k) .D`, so the derivation lands in the target
    type with no rewriting. -/
theorem cupod_loeb_premise (k : Nat) :
    Pf (5 * Nat.log2 k + 33)
      (.impl (.box k (.plays (CupodBot k) (CupodBot k) .D))
             (.plays (CupodBot k) (CupodBot k) .D)) := by
  refine Pf.searchBranch k (.plays .opp .self .D) .D .C (CupodBot k) (CupodBot k) rfl ?_
  -- transcript = the single leaf's conclusion: 5 * log2 k + 33 — unconditionally.
  simp only [Formula.subst, Prog.subst, numCost, Formula.size, Prog.size, CupodBot]
  omega


-- TitForTatBot --

/-- Proof search is false for `.bot CooperateBot`. -/
theorem proofSearch_false_for_bot_CooperateBot (k : Nat) :
    proofSearch k (.plays (.bot CooperateBot) (CupodBot k) .D) = false := by
  cases h : proofSearch k (.plays (.bot CooperateBot) (CupodBot k) .D) with
  | true  => exact absurd (proofSearch_sound _ _ h)
                          (interp_bot_CooperateBot_plays_D_false _)
  | false => rfl

/-- CUPOD cooperates against `.bot CooperateBot` because the search guard fails. -/
theorem CupodBot_plays_C_against_bot_CooperateBot (k fuel : Nat) :
    play (fuel + 2) (CupodBot k) (.bot CooperateBot) = some .C := by
  have hg := proofSearch_false_for_bot_CooperateBot k
  show eval (fuel + 2) (CupodBot k) (.bot CooperateBot) (CupodBot k) = some .C
  unfold CupodBot at hg ⊢
  simp [eval, Prog.subst, Formula.subst, hg]

/-- TitForTat cooperates with CUPOD: its `.sim .opp (.bot CooperateBot)` probe
    sees CUPOD cooperate, so the `ite` selects the cooperate branch. -/
theorem TitForTatBot_plays_C_against_CupodBot (k fuel : Nat) :
    play (fuel + 4) TitForTatBot (CupodBot k) = some .C := by
  have hCupod : play (fuel + 2) (CupodBot k) (.bot CooperateBot) = some .C :=
    CupodBot_plays_C_against_bot_CooperateBot k fuel
  have hGuard :
      eval (fuel + 3) TitForTatBot (CupodBot k) (.sim .opp (.bot CooperateBot)) = some .C := by
    simpa [Nat.add_assoc] using
      (eval_sim_opp_bot_of_play (fuel + 2) TitForTatBot (CupodBot k) CooperateBot Action.C hCupod)
  have hPlay := play_ite_from_guard
    fuel 3 TitForTatBot (CupodBot k) (.sim .opp (.bot CooperateBot))
    (.const Action.C) (.const Action.D)
    Action.C Action.C
    (by rfl) hGuard
  simpa [eval] using hPlay

/-- Semantically, TitForTat never plays D against CUPOD. -/
theorem interp_TitForTatBot_plays_D_false (k : Nat) :
    ¬ (Formula.plays TitForTatBot (CupodBot k) .D).interp := by
  rintro ⟨n, hn⟩
  cases n with
  | zero   => simp only [play, eval, reduceCtorEq] at hn
  | succ m =>
      cases m with
      | zero => simp [play, eval, TitForTatBot] at hn
      | succ m =>
          cases m with
          | zero =>
              simp [play, eval, TitForTatBot] at hn
          | succ fuel =>
              cases fuel with
              | zero =>
                  simp [play, eval, TitForTatBot, CupodBot, Prog.subst, Formula.subst, CooperateBot] at hn
              | succ fuel =>
                  have hC : play (fuel + 1 + 1 + 1 + 1) TitForTatBot (CupodBot k) = some .C := by
                    simpa [Nat.add_assoc] using TitForTatBot_plays_C_against_CupodBot k fuel
                  rw [hC] at hn
                  cases hn

/-- Proof search is false for `.plays TitForTatBot (CupodBot k) .D`. -/
theorem proofSearch_false_for_TitForTatBot (k : Nat) :
    proofSearch k (.plays TitForTatBot (CupodBot k) .D) = false := by
  cases h : proofSearch k (.plays TitForTatBot (CupodBot k) .D) with
  | true  => exact absurd (proofSearch_sound _ _ h)
                          (interp_TitForTatBot_plays_D_false _)
  | false => rfl


-- DBot --

theorem proofSearch_true_for_bot_DefectBot :
    ∃ k, proofSearch k (.plays (.bot DefectBot) (CupodBot k) .D) = true :=
  let k := atom_cost 2
  ⟨k, (proofSearch_spec _ _).2 (Pf.atom ⟨PlaysProof.bot PlaysProof.const, by decide⟩)⟩

/-- CUPOD defects against `.bot DefectBot` once its search guard succeeds. -/
theorem CupodBot_plays_D_against_bot_DefectBot (k fuel : Nat)
    (hk : proofSearch k (.plays (.bot DefectBot) (CupodBot k) .D) = true) :
    play (fuel + 2) (CupodBot k) (.bot DefectBot) = some .D := by
  show eval (fuel + 2) (CupodBot k) (.bot DefectBot) (CupodBot k) = some .D
  unfold CupodBot at hk ⊢
  simp [eval, Prog.subst, Formula.subst, hk]

/-- DBot probes its opponent against `.bot DefectBot`; once CUPOD defects on
    that probe, DBot's `ite` selects the cooperate branch. -/
theorem DBot_plays_C_against_CupodBot (k fuel : Nat)
    (hk : proofSearch k (.plays (.bot DefectBot) (CupodBot k) .D) = true) :
    play (fuel + 4) DBot (CupodBot k) = some .C := by
  have hCupod : play (fuel + 2) (CupodBot k) (.bot DefectBot) = some .D :=
    CupodBot_plays_D_against_bot_DefectBot k fuel hk
  have hGuard :
      eval (fuel + 3) DBot (CupodBot k) (.sim .opp (.bot DefectBot)) = some .D := by
    simpa [Nat.add_assoc] using
      (eval_sim_opp_bot_of_play (fuel + 2) DBot (CupodBot k) DefectBot Action.D hCupod)
  have hPlay := play_ite_from_guard
    fuel 3 DBot (CupodBot k) (.sim .opp (.bot DefectBot))
    (.const Action.D) (.const Action.C)
    Action.C Action.D
    (by rfl) hGuard
  simpa [eval] using hPlay

/-- Semantically, DBot never plays D against CUPOD (given the DefectBot probe
    succeeds). -/
theorem interp_DBot_plays_D_false (k : Nat)
    (hk : proofSearch k (.plays (.bot DefectBot) (CupodBot k) .D) = true) :
    ¬ (Formula.plays DBot (CupodBot k) .D).interp := by
  rintro ⟨n, hn⟩
  cases n with
  | zero   => simp only [play, eval, reduceCtorEq] at hn
  | succ m =>
      cases m with
      | zero => simp [play, eval, DBot] at hn
      | succ m =>
          cases m with
          | zero =>
              simp [play, eval, DBot] at hn
          | succ fuel =>
              cases fuel with
              | zero =>
                  simp [play, eval, DBot, CupodBot, Prog.subst, Formula.subst, DefectBot] at hn
              | succ fuel =>
                  have hC : play (fuel + 1 + 1 + 1 + 1) DBot (CupodBot k) = some .C := by
                    simpa [Nat.add_assoc] using DBot_plays_C_against_CupodBot k fuel hk
                  rw [hC] at hn
                  cases hn

theorem proofSearch_false_for_DBot (k : Nat)
    (hk : proofSearch k (.plays (.bot DefectBot) (CupodBot k) .D) = true) :
    proofSearch k (.plays DBot (CupodBot k) .D) = false := by
  cases h : proofSearch k (.plays DBot (CupodBot k) .D) with
  | true  => exact absurd (proofSearch_sound _ _ h)
                          (interp_DBot_plays_D_false _ hk)
  | false => rfl


-- OBot --

/-- OBot defects against CUPOD: its first probe (`.bot CooperateBot`) sees CUPOD
    cooperate, so it descends into the inner `ite`; that inner probe
    (`.bot DefectBot`) sees CUPOD defect, sending OBot to the defect branch. -/
theorem OBot_plays_D_against_CupodBot (k fuel : Nat)
    (hk : proofSearch k (.plays (.bot DefectBot) (CupodBot k) .D) = true) :
    play (fuel + 5) OBot (CupodBot k) = some .D := by
  have hGuard1 :
      eval (fuel + 4) OBot (CupodBot k) (.sim .opp (.bot CooperateBot)) = some .C := by
    have hProbe : play (fuel + 3) (CupodBot k) (.bot CooperateBot) = some .C := by
      simpa [Nat.add_assoc] using CupodBot_plays_C_against_bot_CooperateBot k (fuel + 1)
    simpa [Nat.add_assoc] using
      (eval_sim_opp_bot_of_play (fuel + 3) OBot (CupodBot k) CooperateBot Action.C hProbe)
  have hGuard2 :
      eval (fuel + 3) OBot (CupodBot k) (.sim .opp (.bot DefectBot)) = some .D := by
    have hProbe : play (fuel + 2) (CupodBot k) (.bot DefectBot) = some .D :=
      CupodBot_plays_D_against_bot_DefectBot k fuel hk
    simpa [Nat.add_assoc] using
      (eval_sim_opp_bot_of_play (fuel + 2) OBot (CupodBot k) DefectBot Action.D hProbe)
  have hPlay := play_ite_from_guard
    fuel 4 OBot (CupodBot k) (.sim .opp (.bot CooperateBot))
    (.ite (.sim .opp (.bot DefectBot)) Action.C (.const Action.C) (.const Action.D))
    (.const Action.D)
    Action.C Action.C
    (by rfl) hGuard1
  have hInner :
      eval (fuel + 4) OBot (CupodBot k)
        (.ite (.sim .opp (.bot DefectBot)) Action.C (.const Action.C) (.const Action.D)) =
          some .D := by
    simpa [Nat.add_assoc] using
      (eval_ite_from_guard (fuel + 3) OBot (CupodBot k)
        (.sim .opp (.bot DefectBot)) (.const Action.C) (.const Action.D)
        Action.C Action.D hGuard2)
  simpa [hInner] using hPlay

/-! ### CupodBot vs OBot — the honest `(C, D)` outcome (floor formalized 2026-07-09).

HISTORY: `proofSearch_true_for_OBot`/`CupodBot_vs_OBot` (mutual defection detected at a
common budget) were RETIRED 2026-07-02 as axiom artifacts: OBot's D-play against
`CupodBot k` crosses Cupod's FAILED first-probe search (vs `.bot CooperateBot` —
"botCoop plays D vs me" is false), so its certificate pays the `search_f` floor —
cost > k for every k.

RESOLVED (2026-07-09): the floor is a THEOREM — `no_provable_OBot_D_tail`, an instance
of `no_provable_probeFirst_tail` (Base/Exclusion.lean; note the fully general shape:
OBot's THEN-branch is its inner probe `ite` and the target action is D — the kill
happens at the guard certificate, which both `ite` polarities carry). Cupod's search
for "OBot plays D vs me" fails at every budget, so Cupod falls through to its
cooperate else-branch while OBot — pure run-priced simulation — defects:
`outcome_CupodBot_vs_OBot = (C, D)` for every `k ≥ 2`. Critch-faithful and grimly
honest: the defection-detector gets exploited by exactly the opponent whose defection
is real but whose certificate crosses the detector's own failed probe. -/

/-- The floor for the OBot pair: no ≤ k certificate concludes any formula whose spine
    tail is "OBot plays D against `CupodBot k`". -/
theorem no_provable_OBot_D_tail (k : Nat) :
    ∀ K φ, Pf K φ → K ≤ k →
      rightTail φ = .plays OBot (CupodBot k) .D → False := by
  intro K φ hp hK ht
  refine no_provable_probeFirst_tail k CooperateBot
      (.ite (.sim .opp (.bot DefectBot)) .C (.const .C) (.const .D))
      (.const .D) .C .D (.plays .opp .self .D) (.const .D) (.const .C) ?_ ?_ K φ hp hK ?_
  · simpa [Formula.subst, Prog.subst, CupodBot] using
      interp_bot_CooperateBot_plays_D_false (CupodBot k)
  · intro k' ψ c0 c1 h; simp at h
  · simpa [OBot, CupodBot] using ht

/-- Cupod's defection search fails against OBot at every budget — the floor's bite:
    OBot really does defect, but every certificate costs more than `k`. -/
theorem proofSearch_false_for_OBot_vs_Cupod (k : Nat) :
    proofSearch k (.plays OBot (CupodBot k) .D) = false := by
  cases h : proofSearch k (.plays OBot (CupodBot k) .D) with
  | true =>
      exact absurd ((proofSearch_spec k _).mp h)
        (fun hp => no_provable_OBot_D_tail k k _ hp le_rfl (by simp))
  | false => rfl

/-- CupodBot cooperates with OBot: it can never afford the certificate of OBot's
    (real!) defection, so it falls through to the trusting else-branch. -/
theorem CupodBot_plays_C_against_OBot (k fuel : Nat) :
    play (fuel + 2) (CupodBot k) OBot = some .C := by
  have hg := proofSearch_false_for_OBot_vs_Cupod k
  show eval (fuel + 2) (CupodBot k) OBot (CupodBot k) = some .C
  unfold CupodBot at hg ⊢
  simp [eval, Prog.subst, Formula.subst, hg]

/-- The `.bot DefectBot` probe guard is Σ₁-certifiable at run price, discharging
    `OBot_plays_D_against_CupodBot`'s hypothesis at every `k ≥ 2`. -/
theorem proofSearch_true_for_bot_DefectBot_vs_Cupod (k : Nat) (hk : 2 ≤ k) :
    proofSearch k (.plays (.bot DefectBot) (CupodBot k) .D) = true :=
  (proofSearch_spec _ _).2 (Pf.atom
    ⟨PlaysProof.bot PlaysProof.const, by simp only [c_leaf, c_node]; omega⟩)

theorem CupodBot_plays_D_against_OBot (fuel : Nat) (k : Nat)
    (hk : proofSearch k (.plays OBot (CupodBot k) .D) = true) :
    play (fuel + 5) (CupodBot k) OBot = some .D := by
  show eval (fuel + 5) (CupodBot k) OBot (CupodBot k) = some .D
  unfold CupodBot at hk ⊢
  simp [eval, Prog.subst, Formula.subst, hk]


-- EBot --

/-- EBot cooperates with CUPOD: its outer probe (`.bot DefectBot`) sees CUPOD
    defect, so EBot descends into the inner `ite`; the next probe
    (`.bot CooperateBot`) sees CUPOD cooperate, so EBot cooperates. -/
theorem EBot_plays_C_against_CupodBot (k fuel : Nat)
    (hk : proofSearch k (.plays (.bot DefectBot) (CupodBot k) .D) = true) :
    play (fuel + 5) EBot (CupodBot k) = some .C := by
  have hCupodD : play (fuel + 3) (CupodBot k) (.bot DefectBot) = some .D := by
    simpa [Nat.add_assoc] using CupodBot_plays_D_against_bot_DefectBot k (fuel + 1) hk
  have hGuard1 :
      eval (fuel + 4) EBot (CupodBot k) (.sim .opp (.bot DefectBot)) = some .D := by
    simpa [Nat.add_assoc] using
      (eval_sim_opp_bot_of_play (fuel + 3) EBot (CupodBot k) DefectBot Action.D hCupodD)
  have hCupodC : play (fuel + 2) (CupodBot k) (.bot CooperateBot) = some .C :=
    CupodBot_plays_C_against_bot_CooperateBot k fuel
  have hGuard2 :
      eval (fuel + 3) EBot (CupodBot k) (.sim .opp (.bot CooperateBot)) = some .C := by
    simpa [Nat.add_assoc] using
      (eval_sim_opp_bot_of_play (fuel + 2) EBot (CupodBot k) CooperateBot Action.C hCupodC)
  have hInner :
      eval (fuel + 4) EBot (CupodBot k)
        (.ite (.sim .opp (.bot CooperateBot)) Action.C (.const Action.C)
          (.ite (.sim .opp (.bot MirrorBot)) Action.C (.const Action.C) (.const Action.D))) =
        some .C := by
    simpa [Nat.add_assoc] using
      (eval_ite_from_guard (fuel + 3) EBot (CupodBot k)
        (.sim .opp (.bot CooperateBot)) (.const Action.C)
        (.ite (.sim .opp (.bot MirrorBot)) Action.C (.const Action.C) (.const Action.D))
        Action.C Action.C hGuard2)
  have hPlay := play_ite_from_guard
    fuel 4 EBot (CupodBot k) (.sim .opp (.bot DefectBot))
    (.const Action.D)
    (.ite (.sim .opp (.bot CooperateBot)) Action.C (.const Action.C)
      (.ite (.sim .opp (.bot MirrorBot)) Action.C (.const Action.C) (.const Action.D)))
    Action.C Action.D
    (by rfl) hGuard1
  simpa [Nat.add_assoc, hInner] using hPlay

/-- Semantically, EBot never plays D against CUPOD (given the DefectBot probe
    succeeds). -/
theorem interp_EBot_plays_D_false (k : Nat)
    (hk : proofSearch k (.plays (.bot DefectBot) (CupodBot k) .D) = true) :
    ¬ (Formula.plays EBot (CupodBot k) .D).interp := by
  rintro ⟨n, hn⟩
  cases n with
  | zero   => simp only [play, eval, reduceCtorEq] at hn
  | succ m =>
      cases m with
      | zero => simp [play, eval, EBot] at hn
      | succ m =>
          cases m with
          | zero => simp [play, eval, EBot] at hn
          | succ fuel =>
              cases fuel with
              | zero =>
                  simp [play, eval, EBot, CupodBot, Prog.subst, Formula.subst] at hn
              | succ fuel =>
                  cases fuel with
                  | zero =>
                      have hk' := hk
                      unfold CupodBot at hk'
                      simp [play, eval, EBot, CupodBot, Prog.subst, Formula.subst, hk'] at hn
                      have hDC : (Action.D == Action.C) = false := by decide
                      rw [hDC] at hn
                      cases hn
                  | succ fuel =>
                      have hC :
                          play (fuel + 1 + 1 + 1 + 1 + 1) EBot (CupodBot k) = some .C := by
                        simpa [Nat.add_assoc] using EBot_plays_C_against_CupodBot k fuel hk
                      rw [hC] at hn
                      cases hn

theorem proofSearch_false_for_EBot (k : Nat)
    (hk : proofSearch k (.plays (.bot DefectBot) (CupodBot k) .D) = true) :
    proofSearch k (.plays EBot (CupodBot k) .D) = false := by
  cases h : proofSearch k (.plays EBot (CupodBot k) .D) with
  | true  => exact absurd (proofSearch_sound _ _ h)
                          (interp_EBot_plays_D_false _ hk)
  | false => rfl


-- MirrorBot --

/-- Specialization of `proof_system_verifies_sim` to `MirrorBot = .sim .opp .self`
    against an arbitrary opponent: S derives "opp plays a vs Mirror → Mirror plays a vs opp". -/
theorem mirror_swap_provable (q : Prog) (a : Action) :
    ∃ m, proofSearch m
      (.impl (.plays q MirrorBot a) (.plays MirrorBot q a)) = true := by
  have h := proof_system_verifies_sim MirrorBot .opp .self q a rfl
  simpa [Prog.subst, MirrorBot] using h

/-- Löb premise for CupodBot vs MirrorBot. Combines source-code transparency
    of CupodBot's `.search` body (`□_k φ_A → φ_B`) with `.sim` source
    transparency for MirrorBot (`φ_B → φ_A`), chained by `Dynamics.hypSyll`
    into the closed `□_k φ → φ` that PBLT requires. (Was an `proofSearch`-level
    chain via the deleted `proofSearch_impl_trans`; now one explicit
    Dynamics.) -/
theorem cupod_mirror_loeb_premise (k : Nat) :
    Pf (20 * Nat.log2 k + 150)
      (.impl (.box k (.plays MirrorBot (CupodBot k) .D))
             (.plays MirrorBot (CupodBot k) .D)) := by
  -- The `hypSyll` TRANSCRIPT pays both leaves plus its conclusion (transcript cost
  -- model): searchBranch leaf + simStep leaf + the `□_k … → …` conclusion — all
  -- `O(log k)`; `20·log2 k + 150` is a generous uniform bound, valid for ALL `k`.
  -- Pf-only: a `hypSyll` TREE smuggled through `struct` becomes a FLAT `implTrans`
  -- of two bare leaves — same two transparency steps, same total budget.
  refine Pf.implTrans _ _ _ (5 * Nat.log2 k + 50) (5 * Nat.log2 k + 50)
    (Pf.searchBranch k (.plays .opp .self .D) .D .C (CupodBot k) MirrorBot rfl ?_)
    (Pf.simStep MirrorBot .opp .self (CupodBot k) .D rfl ?_) ?_ <;>
  · simp only [Formula.subst, Prog.subst, numCost, Formula.size, Prog.size, CupodBot, MirrorBot]
    omega

/-- Once `proofSearch k = true`, CupodBot's eval against MirrorBot is fully
    determined. Pattern from `CupodBot_plays_D_against_bot_DefectBot:247`. -/
theorem CupodBot_plays_D_against_MirrorBot (k fuel : Nat)
    (hk : proofSearch k (.plays MirrorBot (CupodBot k) .D) = true) :
    play (fuel + 2) (CupodBot k) MirrorBot = some .D := by
  show eval (fuel + 2) (CupodBot k) MirrorBot (CupodBot k) = some .D
  unfold CupodBot at hk ⊢
  simp [eval, Prog.subst, Formula.subst, hk]

/-- `.sim .opp .self` swap idiom from `MirrorBot_plays_C_against_DBot:54`. -/
theorem MirrorBot_plays_D_against_CupodBot (k fuel : Nat)
    (hk : proofSearch k (.plays MirrorBot (CupodBot k) .D) = true) :
    play (fuel + 3) MirrorBot (CupodBot k) = some .D := by
  have hCupod : play (fuel + 2) (CupodBot k) MirrorBot = some .D :=
    CupodBot_plays_D_against_MirrorBot k fuel hk
  simpa [play, eval, Prog.subst, MirrorBot] using hCupod

/-- Dual of `CupodBot_plays_D_against_MirrorBot`: when proofSearch fails,
    CupodBot falls through to its `.const .C` cooperate branch. -/
theorem CupodBot_plays_C_against_MirrorBot (k fuel : Nat)
    (hk : proofSearch k (.plays MirrorBot (CupodBot k) .D) = false) :
    play (fuel + 2) (CupodBot k) MirrorBot = some .C := by
  show eval (fuel + 2) (CupodBot k) MirrorBot (CupodBot k) = some .C
  unfold CupodBot at hk ⊢
  simp [eval, Prog.subst, Formula.subst, hk]

/-- Dual of `MirrorBot_plays_D_against_CupodBot`: MirrorBot mirrors the
    cooperate branch via the `.sim .opp .self` swap. -/
theorem MirrorBot_plays_C_against_CupodBot (k fuel : Nat)
    (hk : proofSearch k (.plays MirrorBot (CupodBot k) .D) = false) :
    play (fuel + 3) MirrorBot (CupodBot k) = some .C := by
  have hCupod : play (fuel + 2) (CupodBot k) MirrorBot = some .C :=
    CupodBot_plays_C_against_MirrorBot k fuel hk
  simpa [play, eval, Prog.subst, MirrorBot] using hCupod

/-- Inversion: from a `play` witness on MirrorBot's leg, recover that
    CupodBot's proof-search guard at parameter `k` must have fired. The play
    can only be `some .D` if CupodBot's `.search` took the `.const .D` branch,
    which requires `proofSearch k = true`. -/
theorem proofSearch_k_of_play_MirrorBot
    (k n : Nat) (h : play n MirrorBot (CupodBot k) = some .D) :
    proofSearch k (.plays MirrorBot (CupodBot k) .D) = true := by
  cases hps : proofSearch k (.plays MirrorBot (CupodBot k) .D) with
  | true  => rfl
  | false =>
    -- `play _ MirrorBot (CupodBot k)` is either `none` (small fuel) or `some .C`
    -- (proofSearch returned false). Neither equals `some .D`, contradicting `h`.
    exfalso
    rcases n with _ | _ | _ | n
    · simp [play, eval] at h
    · simp [play, eval, MirrorBot] at h
    · have hev : play 2 MirrorBot (CupodBot k) = none := by
        unfold CupodBot
        simp [play, eval, Prog.subst, MirrorBot, Formula.subst]
      rw [hev] at h
      cases h
    · have hev : play (n + 3) MirrorBot (CupodBot k) = some .C := by
        simpa using MirrorBot_plays_C_against_CupodBot k n hps
      rw [hev] at h
      cases h

end PD.Theorems
