import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Bots.MirrorBot
import PrisonersDilemma.Bots.TitForTatBot
import PrisonersDilemma.Bots.OBot
import PrisonersDilemma.Bots.DBot
import PrisonersDilemma.Bots.EBot
import PrisonersDilemma.Bots.LlmGenerations.WaryBot
import PrisonersDilemma.Bots.LlmGenerations.CIMCIC
import PrisonersDilemma.Bots.LlmGenerations.DIMCID
import PrisonersDilemma.Theorems.CooperateBot.Helpers
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.BaseTheorems

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

/-! # WaryBot matchup helpers

WaryBot's guard is the REFUTATION `.neg (.plays .opp .self .C)`; its substituted
form mentions WaryBot's own source, so the guard size chases the budget and at
small `k` the SIZE FLOOR (`proofSearch_false_neg_undersized`) forces the trusting
else-branch — the certified "budget phase transition" of 2026-07-29: suckered by
DefectBot at `k ≤ 4`, defended (`Pf.atomNeg` fits) from `k = 16`. All statements
verified against the deterministic pre-pass. -/

/-- **The floor**: at any budget below the substituted guard's size, WaryBot's
    refutation search cannot fire and it cooperates. The size hypothesis is
    discharged per-opponent `by decide`. -/
theorem WaryBot_cooperates_floor (k fuel : Nat) (opponent : Prog)
    (hsz : k < (Formula.neg (.plays opponent (WaryBot k) .C)).size) :
    play (fuel + 2) (WaryBot k) opponent = some .C := by
  have hg := proofSearch_false_neg_undersized hsz
  show eval (fuel + 2) (WaryBot k) opponent (WaryBot k) = some .C
  unfold WaryBot at hg ⊢
  simp [eval, Prog.subst, Formula.subst, hg]

/-- Against CooperateBot the guard is refuted at EVERY budget (not just below the
    floor): "¬(CooperateBot plays C)" is semantically false, so soundness blocks
    the search outright. -/
theorem proofSearch_false_wary_CooperateBot (k : Nat) :
    proofSearch k (.neg (.plays CooperateBot (WaryBot k) .C)) = false := by
  cases h : proofSearch k (.neg (.plays CooperateBot (WaryBot k) .C)) with
  | true  => exact absurd (interp_CooperateBot_plays_C_true _) (proofSearch_sound _ _ h)
  | false => rfl

/-- WaryBot trusts CooperateBot at every budget. -/
theorem WaryBot_cooperates_vs_CooperateBot (k fuel : Nat) :
    play (fuel + 2) (WaryBot k) CooperateBot = some .C := by
  have hg := proofSearch_false_wary_CooperateBot k
  show eval (fuel + 2) (WaryBot k) CooperateBot (WaryBot k) = some .C
  unfold WaryBot at hg ⊢
  simp [eval, Prog.subst, Formula.subst, hg]

/-- **The defended side of the phase transition**: at `k = 16` the `Pf.atomNeg`
    transcript (DefectBot's D-certificate at `c_leaf`, plus the negated atom's
    size 15) exactly fits the budget, and the refutation fires. -/
theorem proofSearch_true_wary16_DefectBot :
    proofSearch 16 (.neg (.plays DefectBot (WaryBot 16) .C)) = true :=
  (proofSearch_spec _ _).2
    (Pf.atomNeg DefectBot (WaryBot 16) .D .C c_leaf ⟨PlaysProof.const, le_rfl⟩
      (by decide) (by decide))

/-- WaryBot 16 defends itself against DefectBot. -/
theorem WaryBot16_defects_vs_DefectBot (fuel : Nat) :
    play (fuel + 2) (WaryBot 16) DefectBot = some .D := by
  have hg := proofSearch_true_wary16_DefectBot
  show eval (fuel + 2) (WaryBot 16) DefectBot (WaryBot 16) = some .D
  unfold WaryBot at hg ⊢
  simp [eval, Prog.subst, Formula.subst, hg]

/-- WaryBot trusts the CooperateBot probe at EVERY budget: refuting the probe's
    cooperation is semantically impossible. -/
theorem proofSearch_false_wary_botCooperateBot (k : Nat) :
    proofSearch k (.neg (.plays (.bot CooperateBot) (WaryBot k) .C)) = false := by
  cases h : proofSearch k (.neg (.plays (.bot CooperateBot) (WaryBot k) .C)) with
  | true =>
      have hI : (Formula.plays (.bot CooperateBot) (WaryBot k) .C).interp := by
        unfold Formula.interp
        exact ⟨2, play_bot_CooperateBot 0 _⟩
      exact absurd hI (proofSearch_sound _ _ h)
  | false => rfl

/-- WaryBot cooperates with the CooperateBot probe at every budget. -/
theorem WaryBot_cooperates_vs_botCooperateBot (k fuel : Nat) :
    play (fuel + 2) (WaryBot k) (.bot CooperateBot) = some .C := by
  have hg := proofSearch_false_wary_botCooperateBot k
  show eval (fuel + 2) (WaryBot k) (.bot CooperateBot) (WaryBot k) = some .C
  unfold WaryBot at hg ⊢
  simp [eval, Prog.subst, Formula.subst, hg]

/-! ## How the rest of the zoo plays against WaryBot in the FLOOR regime -/

/-- MirrorBot cooperates back at every FLOOR budget: simulating WaryBot against
    itself reaches the floor-forced trusting branch. -/
theorem MirrorBot_plays_C_against_WaryBot_floor (k fuel : Nat)
    (hsz : k < (Formula.neg (.plays MirrorBot (WaryBot k) .C)).size) :
    play (fuel + 3) MirrorBot (WaryBot k) = some .C := by
  have h := WaryBot_cooperates_floor k fuel MirrorBot hsz
  show eval (fuel + 3) MirrorBot (WaryBot k) MirrorBot = some .C
  simpa [eval, MirrorBot, Prog.subst] using h

/-- DBot's DefectBot probe sees WaryBot cooperate at every FLOOR budget (it
    cannot afford the refutation even of a pure defector), so DBot EXPLOITS it. -/
theorem DBot_plays_D_against_WaryBot_floor (k fuel : Nat)
    (hszDB : k < (Formula.neg (.plays (.bot DefectBot) (WaryBot k) .C)).size) :
    play (fuel + 4) DBot (WaryBot k) = some .D := by
  have hW : play (fuel + 2) (WaryBot k) (.bot DefectBot) = some .C :=
    WaryBot_cooperates_floor k fuel _ hszDB
  have hGuard : eval (fuel + 3) DBot (WaryBot k)
      (.sim .opp (.bot DefectBot)) = some .C := by
    simpa [Nat.add_assoc] using
      (eval_sim_opp_bot_of_play (fuel + 2) DBot (WaryBot k) DefectBot .C hW)
  have hPlay := play_ite_from_guard fuel 3 DBot (WaryBot k)
    (.sim .opp (.bot DefectBot)) (.const .D) (.const .C) .C .C (by rfl) hGuard
  simpa [eval] using hPlay

/-- EBot's first probe (vs DefectBot) sees WaryBot's floor-trust, so EBot defects
    immediately. -/
theorem EBot_plays_D_against_WaryBot_floor (k fuel : Nat)
    (hszDB : k < (Formula.neg (.plays (.bot DefectBot) (WaryBot k) .C)).size) :
    play (fuel + 4) EBot (WaryBot k) = some .D := by
  have hW : play (fuel + 2) (WaryBot k) (.bot DefectBot) = some .C :=
    WaryBot_cooperates_floor k fuel _ hszDB
  have hGuard : eval (fuel + 3) EBot (WaryBot k)
      (.sim .opp (.bot DefectBot)) = some .C := by
    simpa [Nat.add_assoc] using
      (eval_sim_opp_bot_of_play (fuel + 2) EBot (WaryBot k) DefectBot .C hW)
  have hPlay := play_ite_from_guard fuel 3 EBot (WaryBot k)
    (.sim .opp (.bot DefectBot)) (.const .D)
    (.ite (.sim .opp (.bot CooperateBot)) .C (.const .C)
      (.ite (.sim .opp (.bot MirrorBot)) .C (.const .C) (.const .D)))
    .C .C (by rfl) hGuard
  simpa [eval] using hPlay

/-- OBot clears WaryBot on both probes at every FLOOR budget (the CooperateBot
    probe clears at EVERY budget by soundness; the DefectBot probe needs the
    floor) and cooperates. -/
theorem OBot_plays_C_against_WaryBot_floor (k fuel : Nat)
    (hszDB : k < (Formula.neg (.plays (.bot DefectBot) (WaryBot k) .C)).size) :
    play (fuel + 5) OBot (WaryBot k) = some .C := by
  have hW1 : play (fuel + 3) (WaryBot k) (.bot CooperateBot) = some .C :=
    WaryBot_cooperates_vs_botCooperateBot k (fuel + 1)
  have hW2 : play (fuel + 2) (WaryBot k) (.bot DefectBot) = some .C :=
    WaryBot_cooperates_floor k fuel _ hszDB
  have hG1 : eval (fuel + 4) OBot (WaryBot k)
      (.sim .opp (.bot CooperateBot)) = some .C := by
    simpa [Nat.add_assoc] using
      (eval_sim_opp_bot_of_play (fuel + 3) OBot (WaryBot k) CooperateBot .C hW1)
  have hG2 : eval (fuel + 3) OBot (WaryBot k)
      (.sim .opp (.bot DefectBot)) = some .C := by
    simpa [Nat.add_assoc] using
      (eval_sim_opp_bot_of_play (fuel + 2) OBot (WaryBot k) DefectBot .C hW2)
  have hInner : eval (fuel + 4) OBot (WaryBot k)
      (.ite (.sim .opp (.bot DefectBot)) .C (.const .C) (.const .D)) = some .C := by
    have h := eval_ite_from_guard (fuel + 3) OBot (WaryBot k)
      (.sim .opp (.bot DefectBot)) (.const .C) (.const .D) .C .C hG2
    simpa [Nat.add_assoc, eval] using h
  have hPlay := play_ite_from_guard fuel 4 OBot (WaryBot k)
    (.sim .opp (.bot CooperateBot))
    (.ite (.sim .opp (.bot DefectBot)) .C (.const .C) (.const .D)) (.const .D)
    .C .C (by rfl) hG1
  simpa [hInner] using hPlay

/-- CIMCIC's implication guard outgrows its budget at every FLOOR budget (the
    size floor for `.impl`), so it falls to its defecting else-branch. -/
theorem CIMCIC_plays_D_against_WaryBot_floor (k fuel : Nat)
    (hszI : k < (Formula.impl (.plays (CIMCIC k) (WaryBot k) .C)
      (.plays (WaryBot k) (CIMCIC k) .C)).size) :
    play (fuel + 2) (CIMCIC k) (WaryBot k) = some .D := by
  have hg := proofSearch_false_impl_undersized hszI
  show eval (fuel + 2) (CIMCIC k) (WaryBot k) (CIMCIC k) = some .D
  unfold CIMCIC at hg ⊢
  simp [eval, Prog.subst, Formula.subst, hg]

/-- DIMCID's implication guard also hits the size floor, so it falls to its
    cooperating else-branch. -/
theorem DIMCID_plays_C_against_WaryBot_floor (k fuel : Nat)
    (hszI : k < (Formula.impl (.plays (DIMCID k) (WaryBot k) .C)
      (.plays (WaryBot k) (DIMCID k) .D)).size) :
    play (fuel + 2) (DIMCID k) (WaryBot k) = some .C := by
  have hg := proofSearch_false_impl_undersized hszI
  show eval (fuel + 2) (DIMCID k) (WaryBot k) (DIMCID k) = some .C
  unfold DIMCID at hg ⊢
  simp [eval, Prog.subst, Formula.subst, hg]

/-! ## The LARGE-`k` regime — where WaryBot's refutation power actually engages

The substituted guard `.neg (.plays opp (WaryBot k) .C)` has size `log₂ k + O(1)`
(the only `k`-dependence is the numeral in WaryBot's own source), so for every
constant-play opponent fact the `Pf.atomNeg` transcript is EVENTUALLY affordable
(`linear_log2_add_le`). Large-`k` cells that remain OPEN, for the proof agent:
MirrorBot and self-play (the refutation-guard Löb fixpoint — no `diag` analogue
for `.neg` guards yet), OBot (needs `¬Pf` of a TRUE probe formula — a floor
census for `.neg` spines), and the impl/eq/box-guard opponents. -/

/-- Large-`k` defended guard vs DefectBot: the refutation transcript costs
    `log₂ k + 12`, affordable once `k` dominates it. -/
theorem proofSearch_true_wary_DefectBot_large (k : Nat)
    (hk : Nat.log2 k + 12 ≤ k) :
    proofSearch k (.neg (.plays DefectBot (WaryBot k) .C)) = true := by
  refine (proofSearch_spec _ _).2
    (Pf.atomNeg DefectBot (WaryBot k) .D .C c_leaf ⟨PlaysProof.const, le_rfl⟩
      (by decide) ?_)
  show c_leaf + (Formula.neg (.plays DefectBot (WaryBot k) .C)).size ≤ k
  simp [WaryBot, Formula.size, Prog.size, numCost, c_leaf, DefectBot]
  omega

/-- WaryBot defends itself against DefectBot at every sufficiently large budget. -/
theorem WaryBot_defects_vs_DefectBot_large (k fuel : Nat)
    (hk : Nat.log2 k + 12 ≤ k) :
    play (fuel + 2) (WaryBot k) DefectBot = some .D := by
  have hg := proofSearch_true_wary_DefectBot_large k hk
  show eval (fuel + 2) (WaryBot k) DefectBot (WaryBot k) = some .D
  unfold WaryBot at hg ⊢
  simp [eval, Prog.subst, Formula.subst, hg]

/-- Large-`k` defended guard vs the FROZEN DefectBot probe (`.bot DefectBot`):
    one extra `c_node` for the `.bot` hop, transcript `log₂ k + 14`. -/
theorem proofSearch_true_wary_botDefectBot_large (k : Nat)
    (hk : Nat.log2 k + 14 ≤ k) :
    proofSearch k (.neg (.plays (.bot DefectBot) (WaryBot k) .C)) = true := by
  refine (proofSearch_spec _ _).2
    (Pf.atomNeg (.bot DefectBot) (WaryBot k) .D .C (c_leaf + c_node)
      ⟨PlaysProof.bot PlaysProof.const, le_rfl⟩ (by decide) ?_)
  show (c_leaf + c_node) +
      (Formula.neg (.plays (.bot DefectBot) (WaryBot k) .C)).size ≤ k
  simp [WaryBot, Formula.size, Prog.size, numCost, c_leaf, c_node, DefectBot]
  omega

/-- WaryBot defends on the DefectBot PROBE at large `k` — this is what flips the
    simulators' assessment of it. -/
theorem WaryBot_defects_vs_botDefectBot_large (k fuel : Nat)
    (hk : Nat.log2 k + 14 ≤ k) :
    play (fuel + 2) (WaryBot k) (.bot DefectBot) = some .D := by
  have hg := proofSearch_true_wary_botDefectBot_large k hk
  show eval (fuel + 2) (WaryBot k) (.bot DefectBot) (WaryBot k) = some .D
  unfold WaryBot at hg ⊢
  simp [eval, Prog.subst, Formula.subst, hg]

/-- TitForTatBot cooperates with WaryBot at EVERY budget (its probe clears at
    every budget, by soundness — no floor involved). -/
theorem TitForTatBot_plays_C_against_WaryBot (k fuel : Nat) :
    play (fuel + 4) TitForTatBot (WaryBot k) = some .C := by
  have hW : play (fuel + 2) (WaryBot k) (.bot CooperateBot) = some .C :=
    WaryBot_cooperates_vs_botCooperateBot k fuel
  have hGuard : eval (fuel + 3) TitForTatBot (WaryBot k)
      (.sim .opp (.bot CooperateBot)) = some .C := by
    simpa [Nat.add_assoc] using
      (eval_sim_opp_bot_of_play (fuel + 2) TitForTatBot (WaryBot k) CooperateBot .C hW)
  have hPlay := play_ite_from_guard fuel 3 TitForTatBot (WaryBot k)
    (.sim .opp (.bot CooperateBot)) (.const .C) (.const .D) .C .C (by rfl) hGuard
  simpa [eval] using hPlay

/-- WaryBot cannot refute TitForTatBot's cooperation (it is semantically true at
    every budget), so it trusts back. -/
theorem proofSearch_false_wary_TitForTatBot (k : Nat) :
    proofSearch k (.neg (.plays TitForTatBot (WaryBot k) .C)) = false := by
  cases h : proofSearch k (.neg (.plays TitForTatBot (WaryBot k) .C)) with
  | true =>
      have hI : (Formula.plays TitForTatBot (WaryBot k) .C).interp := by
        unfold Formula.interp
        exact ⟨4, TitForTatBot_plays_C_against_WaryBot k 0⟩
      exact absurd hI (proofSearch_sound _ _ h)
  | false => rfl

/-- WaryBot cooperates with TitForTatBot at every budget. -/
theorem WaryBot_cooperates_vs_TitForTatBot (k fuel : Nat) :
    play (fuel + 2) (WaryBot k) TitForTatBot = some .C := by
  have hg := proofSearch_false_wary_TitForTatBot k
  show eval (fuel + 2) (WaryBot k) TitForTatBot (WaryBot k) = some .C
  unfold WaryBot at hg ⊢
  simp [eval, Prog.subst, Formula.subst, hg]

/-- At large `k` DBot's probe sees WaryBot DEFEND against DefectBot, so DBot has
    no sucker to exploit and cooperates — the opposite of the floor regime. -/
theorem DBot_plays_C_against_WaryBot_large (k fuel : Nat)
    (hk : Nat.log2 k + 14 ≤ k) :
    play (fuel + 4) DBot (WaryBot k) = some .C := by
  have hW : play (fuel + 2) (WaryBot k) (.bot DefectBot) = some .D :=
    WaryBot_defects_vs_botDefectBot_large k fuel hk
  have hGuard : eval (fuel + 3) DBot (WaryBot k)
      (.sim .opp (.bot DefectBot)) = some .D := by
    simpa [Nat.add_assoc] using
      (eval_sim_opp_bot_of_play (fuel + 2) DBot (WaryBot k) DefectBot .D hW)
  have hPlay := play_ite_from_guard fuel 3 DBot (WaryBot k)
    (.sim .opp (.bot DefectBot)) (.const .D) (.const .C) .C .D (by rfl) hGuard
  simpa [eval] using hPlay

/-- At large `k` WaryBot cannot refute DBot's (true) cooperation, so it trusts. -/
theorem proofSearch_false_wary_DBot_large (k : Nat)
    (hk : Nat.log2 k + 14 ≤ k) :
    proofSearch k (.neg (.plays DBot (WaryBot k) .C)) = false := by
  cases h : proofSearch k (.neg (.plays DBot (WaryBot k) .C)) with
  | true =>
      have hI : (Formula.plays DBot (WaryBot k) .C).interp := by
        unfold Formula.interp
        exact ⟨4, DBot_plays_C_against_WaryBot_large k 0 hk⟩
      exact absurd hI (proofSearch_sound _ _ h)
  | false => rfl

/-- WaryBot cooperates with DBot at large `k`. -/
theorem WaryBot_cooperates_vs_DBot_large (k fuel : Nat)
    (hk : Nat.log2 k + 14 ≤ k) :
    play (fuel + 2) (WaryBot k) DBot = some .C := by
  have hg := proofSearch_false_wary_DBot_large k hk
  show eval (fuel + 2) (WaryBot k) DBot (WaryBot k) = some .C
  unfold WaryBot at hg ⊢
  simp [eval, Prog.subst, Formula.subst, hg]

/-- At large `k` EBot walks its probes — WaryBot defends vs DefectBot (first
    probe fails EBot's exploit test) then cooperates with CooperateBot — and
    EBot cooperates. -/
theorem EBot_plays_C_against_WaryBot_large (k fuel : Nat)
    (hk : Nat.log2 k + 14 ≤ k) :
    play (fuel + 5) EBot (WaryBot k) = some .C := by
  have hW1 : play (fuel + 3) (WaryBot k) (.bot DefectBot) = some .D :=
    WaryBot_defects_vs_botDefectBot_large k (fuel + 1) hk
  have hW2 : play (fuel + 2) (WaryBot k) (.bot CooperateBot) = some .C :=
    WaryBot_cooperates_vs_botCooperateBot k fuel
  have hG1 : eval (fuel + 4) EBot (WaryBot k)
      (.sim .opp (.bot DefectBot)) = some .D := by
    simpa [Nat.add_assoc] using
      (eval_sim_opp_bot_of_play (fuel + 3) EBot (WaryBot k) DefectBot .D hW1)
  have hG2 : eval (fuel + 3) EBot (WaryBot k)
      (.sim .opp (.bot CooperateBot)) = some .C := by
    simpa [Nat.add_assoc] using
      (eval_sim_opp_bot_of_play (fuel + 2) EBot (WaryBot k) CooperateBot .C hW2)
  have hInner : eval (fuel + 4) EBot (WaryBot k)
      (.ite (.sim .opp (.bot CooperateBot)) .C (.const .C)
        (.ite (.sim .opp (.bot MirrorBot)) .C (.const .C) (.const .D))) = some .C := by
    have h := eval_ite_from_guard (fuel + 3) EBot (WaryBot k)
      (.sim .opp (.bot CooperateBot)) (.const .C)
      (.ite (.sim .opp (.bot MirrorBot)) .C (.const .C) (.const .D)) .C .C hG2
    simpa [Nat.add_assoc, eval] using h
  have hPlay := play_ite_from_guard fuel 4 EBot (WaryBot k)
    (.sim .opp (.bot DefectBot)) (.const .D)
    (.ite (.sim .opp (.bot CooperateBot)) .C (.const .C)
      (.ite (.sim .opp (.bot MirrorBot)) .C (.const .C) (.const .D)))
    .C .D (by rfl) hG1
  simpa [hInner] using hPlay

/-- At large `k` WaryBot cannot refute EBot's (true) cooperation, so it trusts. -/
theorem proofSearch_false_wary_EBot_large (k : Nat)
    (hk : Nat.log2 k + 14 ≤ k) :
    proofSearch k (.neg (.plays EBot (WaryBot k) .C)) = false := by
  cases h : proofSearch k (.neg (.plays EBot (WaryBot k) .C)) with
  | true =>
      have hI : (Formula.plays EBot (WaryBot k) .C).interp := by
        unfold Formula.interp
        exact ⟨5, EBot_plays_C_against_WaryBot_large k 0 hk⟩
      exact absurd hI (proofSearch_sound _ _ h)
  | false => rfl

/-- WaryBot cooperates with EBot at large `k`. -/
theorem WaryBot_cooperates_vs_EBot_large (k fuel : Nat)
    (hk : Nat.log2 k + 14 ≤ k) :
    play (fuel + 2) (WaryBot k) EBot = some .C := by
  have hg := proofSearch_false_wary_EBot_large k hk
  show eval (fuel + 2) (WaryBot k) EBot (WaryBot k) = some .C
  unfold WaryBot at hg ⊢
  simp [eval, Prog.subst, Formula.subst, hg]

end PD.Theorems
