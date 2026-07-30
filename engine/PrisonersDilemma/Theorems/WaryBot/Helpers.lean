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


namespace WaryCensus

/-- The subst-preimage analysis shared by both censuses: under a
    `.sim`/`.bot (.sim …)` frame, a substitution image can be the literal
    `WaryBot k` only via `q = .opp` with `o = WaryBot k` — the guard formula's
    bare `.opp`/`.self` atoms are not producible under a non-atom frame. -/
theorem subst_eq_wary {k : Nat} {q me o : Prog}
    (hme : (∃ p₂ q₂, me = .sim p₂ q₂) ∨ (∃ p₂ q₂, me = .bot (.sim p₂ q₂)))
    (h : q.subst me o = WaryBot k) : o = WaryBot k := by
  cases q with
  | const a => simp [Prog.subst, WaryBot] at h
  | self =>
      rcases hme with ⟨p₂, q₂, rfl⟩ | ⟨p₂, q₂, rfl⟩ <;>
        simp [Prog.subst, WaryBot] at h
  | opp => simpa [Prog.subst] using h
  | bot p => simp [Prog.subst, WaryBot] at h
  | sim p q => simp [Prog.subst, WaryBot] at h
  | ite b a p q => simp [Prog.subst, WaryBot] at h
  | search K φg pp qq =>
      simp only [WaryBot, Prog.subst, Prog.search.injEq] at h
      obtain ⟨hK, hg, hp, hq⟩ := h
      cases φg with
      | plays x y a => simp [Formula.subst] at hg
      | impl f1 f2 => simp [Formula.subst] at hg
      | box n' f1 => simp [Formula.subst] at hg
      | eq p' q' => simp [Formula.subst] at hg
      | diag g' f1 => simp [Formula.subst] at hg
      | neg f1 =>
          simp only [Formula.subst, Formula.neg.injEq] at hg
          cases f1 with
          | impl f2 f3 => simp [Formula.subst] at hg
          | neg f2 => simp [Formula.subst] at hg
          | box n' f2 => simp [Formula.subst] at hg
          | eq p' q' => simp [Formula.subst] at hg
          | diag g' f2 => simp [Formula.subst] at hg
          | plays x y a =>
              simp only [Formula.subst, Formula.plays.injEq] at hg
              obtain ⟨hx, hy, -⟩ := hg
              cases x with
              | const a' => simp [Prog.subst] at hx
              | bot p' => simp [Prog.subst] at hx
              | sim p' q' => simp [Prog.subst] at hx
              | ite b' a' p' q' => simp [Prog.subst] at hx
              | search K' g' p' q' => simp [Prog.subst] at hx
              | self =>
                  rcases hme with ⟨p₂, q₂, rfl⟩ | ⟨p₂, q₂, rfl⟩ <;>
                    simp [Prog.subst] at hx
              | opp =>
                  simp only [Prog.subst] at hx
                  cases y with
                  | const a' => simp [Prog.subst] at hy
                  | bot p' => simp [Prog.subst] at hy
                  | sim p' q' => simp [Prog.subst] at hy
                  | ite b' a' p' q' => simp [Prog.subst] at hy
                  | search K' g' p' q' => simp [Prog.subst] at hy
                  | self =>
                      rcases hme with ⟨p₂, q₂, rfl⟩ | ⟨p₂, q₂, rfl⟩ <;>
                        simp [Prog.subst] at hy
                  | opp =>
                      simp only [Prog.subst] at hy
                      rw [hx] at hy
                      exact absurd hy (by simp)

/-! #### The modified valuation, PARAMETRIC over the entangled-atom relation

`WV S` is `Formula.interp` with one change: a plays-atom is additionally true
when its action is `.C` and its player pair is in `S`. Boxes stay RAW `Pf` —
that is what keeps the modal tier and the transparency leaves sound without
touching the Löb machinery. -/

def WV (S : Prog → Prog → Prop) : Formula → Prop
  | .plays p q a => (a = .C ∧ S p q) ∨ (Formula.plays p q a).interp
  | .impl α β => WV S α → WV S β
  | .neg φ => ¬ WV S φ
  | .box n φ => Pf n φ
  | .eq p q => p = q
  | .diag g φ => Pf g (.diag g φ) → WV S φ

theorem WV_plays {S : Prog → Prog → Prop} {p q : Prog} {a : Action} :
    WV S (.plays p q a) = ((a = .C ∧ S p q) ∨ (Formula.plays p q a).interp) := rfl
theorem WV_impl {S : Prog → Prog → Prop} {α β : Formula} :
    WV S (.impl α β) = (WV S α → WV S β) := rfl
theorem WV_neg {S : Prog → Prog → Prop} {φ : Formula} :
    WV S (.neg φ) = ¬ WV S φ := rfl
theorem WV_box {S : Prog → Prog → Prop} {n : Nat} {φ : Formula} :
    WV S (.box n φ) = Pf n φ := rfl
theorem WV_eq {S : Prog → Prog → Prop} {p q : Prog} :
    WV S (.eq p q) = (p = q) := rfl
theorem WV_diag {S : Prog → Prog → Prop} {g : Nat} {φ : Formula} :
    WV S (.diag g φ) = (Pf g (.diag g φ) → WV S φ) := rfl

/-- Probe atoms (`.bot`-frozen opponent) fall out of any `S` that avoids `.bot`
    opponents, so their WV is their interp. -/
theorem interp_of_WV_probe {S : Prog → Prog → Prop}
    (hnb : ∀ oppo z, ¬ S oppo (.bot z)) {oppo z : Prog} {aT : Action}
    (h : WV S (.plays oppo (.bot z) aT)) :
    (Formula.plays oppo (.bot z) aT).interp := by
  rw [WV_plays] at h
  rcases h with ⟨-, hSP⟩ | h
  · exact absurd hSP (hnb oppo z)
  · exact h

/-- Interp-to-WV bridge along a search-guard chain (box antecedents: WV = interp;
    the plays tail embeds by `Or.inr`). -/
theorem WV_of_interp_searchChain {S : Prog → Prog → Prop} (me oppo : Prog)
    (a : Action) :
    ∀ L : List (Nat × Formula × Prog),
      (implChain (searchGuards me oppo L) (.plays me oppo a)).interp →
      WV S (implChain (searchGuards me oppo L) (.plays me oppo a))
  | [] => fun h => Or.inr h
  | (g, ψ, e) :: L => by
      intro h
      show WV S (.impl (.box g (ψ.subst me oppo))
        (implChain (searchGuards me oppo L) (.plays me oppo a)))
      rw [WV_impl]
      intro hbox
      rw [WV_box] at hbox
      exact WV_of_interp_searchChain me oppo a L (h hbox)

/-- Interp-to-WV bridge along a mixed-telescope guard chain. -/
theorem WV_of_interp_ctxChain {S : Prog → Prog → Prop}
    (hnb : ∀ oppo z, ¬ S oppo (.bot z)) (me oppo : Prog) (a : Action) :
    ∀ L : List CtxLayer,
      (implChain (ctxGuards me oppo L) (.plays me oppo a)).interp →
      WV S (implChain (ctxGuards me oppo L) (.plays me oppo a))
  | [] => fun h => Or.inr h
  | .searchL g ψ e :: L => by
      intro h
      show WV S (.impl (.box g (ψ.subst me oppo))
        (implChain (ctxGuards me oppo L) (.plays me oppo a)))
      rw [WV_impl]
      intro hbox
      rw [WV_box] at hbox
      exact WV_of_interp_ctxChain hnb me oppo a L (h hbox)
  | .iteL z aT other :: L => by
      intro h
      show WV S (.impl (.plays oppo (.bot z) aT)
        (implChain (ctxGuards me oppo L) (.plays me oppo a)))
      rw [WV_impl]
      intro hprobe
      exact WV_of_interp_ctxChain hnb me oppo a L (h (interp_of_WV_probe hnb hprobe))

/-! #### The MirrorBot census: `SPMirror` -/

/-- Atoms entangled with the WaryBot k ↔ MirrorBot fixpoint: base "MirrorBot
    plays C vs WaryBot k" (raw constructor form, for clean `cases` unification),
    closed under the two sim-transparency lifts. -/
inductive SPMirror (k : Nat) : Prog → Prog → Prop where
  | base : SPMirror k (.sim .opp .self)
      (.search k (.neg (.plays .opp .self .C)) (.const .D) (.const .C))
  | simL (p q o : Prog) :
      SPMirror k (p.subst (.sim p q) o) (q.subst (.sim p q) o) →
      SPMirror k (.sim p q) o
  | botSimL (p q o : Prog) :
      SPMirror k (p.subst (.bot (.sim p q)) o) (q.subst (.bot (.sim p q)) o) →
      SPMirror k (.bot (.sim p q)) o

theorem SPMirror_me {k : Nat} {me oppo : Prog} (h : SPMirror k me oppo) :
    (∃ p q, me = .sim p q) ∨ (∃ p q, me = .bot (.sim p q)) := by
  cases h with
  | base => exact Or.inl ⟨_, _, rfl⟩
  | simL p q o _ => exact Or.inl ⟨p, q, rfl⟩
  | botSimL p q o _ => exact Or.inr ⟨p, q, rfl⟩

/-- The invariant: the opponent slot is always the literal `WaryBot k`. -/
theorem SPMirror_opp {k : Nat} {me oppo : Prog} (h : SPMirror k me oppo) :
    oppo = WaryBot k := by
  induction h with
  | base => rfl
  | simL p q o hprem ih => exact subst_eq_wary (Or.inl ⟨p, q, rfl⟩) ih
  | botSimL p q o hprem ih => exact subst_eq_wary (Or.inr ⟨p, q, rfl⟩) ih

theorem SPMirror_not_bot (k : Nat) : ∀ oppo z, ¬ SPMirror k oppo (.bot z) := by
  intro oppo z h
  have hw := SPMirror_opp h
  simp [WaryBot] at hw

theorem SPMirror_sim_inv {k : Nat} {p q oppo : Prog}
    (h : SPMirror k (.sim p q) oppo) :
    (p = .opp ∧ q = .self ∧ oppo = WaryBot k) ∨
    SPMirror k (p.subst (.sim p q) oppo) (q.subst (.sim p q) oppo) := by
  cases h with
  | base => exact Or.inl ⟨rfl, rfl, rfl⟩
  | simL _ _ _ hprem => exact Or.inr hprem

theorem SPMirror_botSim_inv {k : Nat} {p q oppo : Prog}
    (h : SPMirror k (.bot (.sim p q)) oppo) :
    SPMirror k (p.subst (.bot (.sim p q)) oppo)
      (q.subst (.bot (.sim p q)) oppo) := by
  cases h with
  | botSimL _ _ _ hprem => exact hprem

/- **PROJECT-CONVENTION NOTE (raw mutual recursor).** The codebase rule is
"never use the raw mutual recursors outside ProofSystem.lean §4 and
`sound_upto`". The two `pf_WV_*` inductions below are the THIRD legitimate
site, for the same reason as `sound_upto`: the proof needs the cross-IH through
the `PlaysProof.search_t` guard back-edge (a `Pf`-motive fact about the guard
proof INSIDE a play certificate), which neither `Pf.induct` nor
`PlaysProof.induct` can supply — the named eliminators hand the mutual premises
over as data, not as induction hypotheses. Budget induction is no substitute
(the guard budget does not descend), so the raw recursor is forced. -/

set_option maxHeartbeats 1000000 in
/-- **WV-soundness for the MirrorBot census**: every `Pf`-provable formula is
    `WV (SPMirror k)`-true. Mutual structural induction (`Pf.rec`); motives:
    play-exclusion (an SP player — or WaryBot itself vs MirrorBot — never
    certifiably plays anything but C), no D-certificate for SP-atoms, and WV. -/
theorem pf_WV_mirror (k : Nat) : ∀ {K : Nat} {φ : Formula},
    Pf K φ → WV (SPMirror k) φ := by
  intro K φ h
  refine Pf.rec (motive_1 := fun me oppo body a n _ =>
      (SPMirror k me oppo → (body = me ∨ me = .bot body) → a = .C) ∧
      (me = WaryBot k → oppo = MirrorBot → body = WaryBot k → a = .C))
    (motive_2 := fun m ψ _ => ∀ p q, SPMirror k p q → ψ ≠ .plays p q .D)
    (motive_3 := fun _ ψ _ => WV (SPMirror k) ψ)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    h
  -- ═══ PlaysProof arms (9) ═══
  · -- const
    intro me oppo a
    constructor
    · intro hSP hgate
      rcases SPMirror_me hSP with ⟨p', q', rfl⟩ | ⟨p', q', rfl⟩ <;>
        rcases hgate with hb | hb <;> simp_all
    · intro _ _ h3
      simp [WaryBot] at h3
  · -- self
    intro me oppo a n hpl ih
    constructor
    · intro hSP hgate
      rcases SPMirror_me hSP with ⟨p', q', rfl⟩ | ⟨p', q', rfl⟩ <;>
        rcases hgate with hb | hb <;> simp_all
    · intro _ _ h3
      simp [WaryBot] at h3
  · -- opp
    intro me oppo a n hpl ih
    constructor
    · intro hSP hgate
      rcases SPMirror_me hSP with ⟨p', q', rfl⟩ | ⟨p', q', rfl⟩ <;>
        rcases hgate with hb | hb <;> simp_all
    · intro _ _ h3
      simp [WaryBot] at h3
  · -- bot
    intro me oppo p a n hpl ih
    constructor
    · intro hSP hgate
      rcases hgate with hb | hb
      · exact ih.1 hSP (Or.inr hb.symm)
      · rcases SPMirror_me hSP with ⟨p', q', rfl⟩ | ⟨p', q', rfl⟩ <;> simp_all
    · intro _ _ h3
      simp [WaryBot] at h3
  · -- sim
    intro a n me oppo p q hpl ih
    constructor
    · intro hSP hgate
      rcases hgate with hb | hb
      · subst hb
        rcases SPMirror_sim_inv hSP with ⟨rfl, rfl, rfl⟩ | hprem
        · exact ih.2 (by simp [Prog.subst]) (by simp [Prog.subst, MirrorBot])
            (by simp [Prog.subst])
        · exact ih.1 hprem (Or.inl rfl)
      · subst hb
        exact ih.1 (SPMirror_botSim_inv hSP) (Or.inl rfl)
    · intro _ _ h3
      simp [WaryBot] at h3
  · -- ite_t
    intro me oppo b r m a' p a n q hb hr hp ihb ihp
    constructor
    · intro hSP hgate
      rcases SPMirror_me hSP with ⟨p', q', rfl⟩ | ⟨p', q', rfl⟩ <;>
        rcases hgate with hg | hg <;> simp_all
    · intro _ _ h3
      simp [WaryBot] at h3
  · -- ite_f
    intro me oppo b r m a' q a n p hb hr hq ihb ihq
    constructor
    · intro hSP hgate
      rcases SPMirror_me hSP with ⟨p', q', rfl⟩ | ⟨p', q', rfl⟩ <;>
        rcases hgate with hg | hg <;> simp_all
    · intro _ _ h3
      simp [WaryBot] at h3
  · -- search_t : the back-edge. The second clause is the heart of the argument.
    intro K' me oppo p a n φg q hg hp ihg ihp
    constructor
    · intro hSP hgate
      rcases SPMirror_me hSP with ⟨p', q', rfl⟩ | ⟨p', q', rfl⟩ <;>
        rcases hgate with hb | hb <;> simp_all
    · intro h1 h2 h3
      unfold WaryBot at h3
      injection h3 with hK hφ hpp hqq
      subst hK; subst hφ; subst h1; subst h2
      simp only [Formula.subst, Prog.subst] at ihg
      rw [WV_neg] at ihg
      refine absurd ?_ ihg
      rw [WV_plays]
      exact Or.inl ⟨rfl, SPMirror.base⟩
  · -- search_f : the else-branch plays C, killed by inversion.
    intro m me oppo q a n K' φg p hg hq ihg ihq
    constructor
    · intro hSP hgate
      rcases SPMirror_me hSP with ⟨p', q', rfl⟩ | ⟨p', q', rfl⟩ <;>
        rcases hgate with hb | hb <;> simp_all
    · intro h1 h2 h3
      unfold WaryBot at h3
      injection h3 with hK hφ hpp hqq
      subst hqq
      cases hq
      rfl
  -- ═══ AtomProvable arm (1) ═══
  · -- mk
    intro me oppo a n K hpp hn ih p q hSP heq
    injection heq with h1 h2 h3
    subst h1; subst h2; subst h3
    exact Action.noConfusion (ih.1 hSP (Or.inl rfl))
  -- ═══ Pf arms (29) ═══
  · -- atom
    intro K ψ hatom ih
    cases hatom with
    | mk hpp hn =>
        rw [WV_plays]
        exact Or.inr (Pf_sound _ _ (Pf.atom ⟨hpp, hn⟩))
  · -- atomNeg
    intro K p q b aN m hatom hne hle ih
    rw [WV_neg, WV_plays]
    rintro (⟨rfl, hSP⟩ | hint)
    · cases b with
      | C => exact hne rfl
      | D => exact ih p q hSP rfl
    · have hs := Pf_sound _ _ (Pf.atomNeg p q b aN m hatom hne hle)
      simp only [Formula.interp] at hs
      exact hs hint
  · -- searchBranch
    intro K g ψ a b me oppo hme hle
    rw [WV_impl, WV_box]
    intro hbox
    rw [WV_plays]
    exact Or.inr ((Pf_sound _ _ (Pf.searchBranch g ψ a b me oppo hme hle)) hbox)
  · -- simStep : the SP closure in action
    intro K me p q oppo a hme hle
    rw [WV_impl, WV_plays, WV_plays]
    rintro (⟨rfl, hSP⟩ | hint)
    · subst hme
      exact Or.inl ⟨rfl, SPMirror.simL p q oppo hSP⟩
    · exact Or.inr ((Pf_sound _ _ (Pf.simStep me p q oppo a hme hle)) hint)
  · -- botSimStep
    intro K me p q oppo a hme hle
    rw [WV_impl, WV_plays, WV_plays]
    rintro (⟨rfl, hSP⟩ | hint)
    · subst hme
      exact Or.inl ⟨rfl, SPMirror.botSimL p q oppo hSP⟩
    · exact Or.inr ((Pf_sound _ _ (Pf.botSimStep me p q oppo a hme hle)) hint)
  · -- botSearchStep
    intro K g ψ a b me oppo hme hle
    rw [WV_impl, WV_box]
    intro hbox
    rw [WV_plays]
    exact Or.inr ((Pf_sound _ _ (Pf.botSearchStep g ψ a b me oppo hme hle)) hbox)
  · -- iteBranchSearch_t : probe antecedent is never SP (SPMirror_not_bot)
    intro K g z a' c0 c1 ψ q me oppo hme hle
    rw [WV_impl, WV_impl, WV_box]
    intro hprobe hbox
    rw [WV_plays]
    exact Or.inr ((Pf_sound _ _
      (Pf.iteBranchSearch_t g z a' c0 c1 ψ q me oppo hme hle))
      (interp_of_WV_probe (SPMirror_not_bot k) hprobe) hbox)
  · -- searchThenSearch_t
    intro K k₁ k₂ m ψ₁ ψ₂ c0 c1 q me oppo hme hprud hmk hle ih
    rw [WV_impl, WV_box]
    intro hbox
    rw [WV_plays]
    exact Or.inr ((Pf_sound _ _
      (Pf.searchThenSearch_t k₁ k₂ m ψ₁ ψ₂ c0 c1 q me oppo hme hprud hmk hle)) hbox)
  · -- searchChain
    intro K g₁ ψ₁ e₁ L a me oppo hme hle
    rw [WV_impl, WV_box]
    intro hbox
    exact WV_of_interp_searchChain me oppo a L
      ((Pf_sound _ _ (Pf.searchChain g₁ ψ₁ e₁ L a me oppo hme hle)) hbox)
  · -- ctxChain
    intro K hd L a me oppo hme hle
    have hs := Pf_sound _ _ (Pf.ctxChain hd L a me oppo hme hle)
    cases hd with
    | searchL g ψ e =>
        simp only [ctxGuard] at hs ⊢
        rw [WV_impl, WV_box]
        intro hbox
        exact WV_of_interp_ctxChain (SPMirror_not_bot k) me oppo a L (hs hbox)
    | iteL z aT other =>
        simp only [ctxGuard] at hs ⊢
        rw [WV_impl]
        intro hprobe
        exact WV_of_interp_ctxChain (SPMirror_not_bot k) me oppo a L
          (hs (interp_of_WV_probe (SPMirror_not_bot k) hprobe))
  · -- eqRefl
    intro K p hle
    rw [WV_eq]
  · -- eqNeg
    intro K p q hne hle
    rw [WV_neg, WV_eq]
    exact hne
  · -- mp
    intro K m₁ m₂ φ' α h1 h2 hle ih1 ih2
    rw [WV_impl] at ih1
    exact ih1 ih2
  · -- implTrans
    intro K φ' ψ χ a b h1 h2 hle ih1 ih2
    rw [WV_impl] at ih1 ih2 ⊢
    exact fun hφ => ih2 (ih1 hφ)
  · -- weakenImpl
    intro K φ' ψ m hψ hle ih
    rw [WV_impl]
    exact fun _ => ih
  · -- impS2
    intro φ' ψ χ m₁ m₂ K h1 h2 hle ih1 ih2
    rw [WV_impl] at ih1 ih2 ⊢
    intro hφ
    have hi := ih1 hφ
    rw [WV_impl] at hi
    exact hi (ih2 hφ)
  · -- implRefl
    intro K φ' hle
    rw [WV_impl]
    exact id
  · -- implK
    intro K φ' ψ hle
    rw [WV_impl]
    intro hφ
    rw [WV_impl]
    exact fun _ => hφ
  · -- implS
    intro K φ' ψ χ hle
    rw [WV_impl]
    intro hf
    rw [WV_impl]
    intro hg
    rw [WV_impl]
    intro hx
    rw [WV_impl] at hf hg
    have h1 := hf hx
    rw [WV_impl] at h1
    exact h1 (hg hx)
  · -- contrapose : trivially WV-sound (this rule falsifies the TailTo census)
    intro K φ' ψ m hp hle ih
    rw [WV_impl] at ih
    rw [WV_impl, WV_neg, WV_neg]
    exact fun hnψ hφ => hnψ (ih hφ)
  · -- negElim
    intro K φ' ψ m₁ m₂ h1 h2 hle ih1 ih2
    rw [WV_neg] at ih1
    exact absurd ih2 ih1
  · -- boxIntro
    intro kIn K φ' hprem hle ih
    rw [WV_box]
    exact hprem
  · -- atomBoxImpl
    intro K kBox p q a hatom hle _ihA
    show WV (SPMirror k) (.impl (.plays p q a) (.box kBox (.plays p q a)))
    rw [WV_impl, WV_box]
    exact fun _ => Pf.atom hatom
  · -- axK
    intro a b c m K φ' α hprem hgate hle ih
    rw [WV_box] at ih
    rw [WV_impl, WV_box, WV_box]
    exact fun hb => Pf.mp a b φ' α ih hb hgate
  · -- axKf
    intro a b c K φ' α hgate hsz
    rw [WV_impl, WV_box, WV_impl, WV_box, WV_box]
    exact fun h1 hb => Pf.mp a b φ' α h1 hb hgate
  · -- box4
    intro a b K φ' hgate hsz
    rw [WV_impl, WV_box, WV_box]
    exact fun hp => Pf.boxIntro a b φ' hp hgate
  · -- boxMono
    intro a b K φ' hab hsz
    rw [WV_impl, WV_box, WV_box]
    exact fun hp => Pf_mono hp hab
  · -- diagF
    intro pm fb g K tgt hgate hle ih
    rw [WV_impl, WV_diag, WV_impl, WV_box]
    exact fun hd => hd
  · -- diagB
    intro pm fb g K tgt hgate hle ih
    rw [WV_impl, WV_impl, WV_box, WV_diag]
    exact fun hd => hd

/-! #### The self-play census: `SPSelf`

Same closure with base "WaryBot k plays C vs itself" — a SEARCH-headed player,
so the base kill lives in `motive_1`'s `search_t` arm (the guard IS the excluded
refutation) instead of the `sim` arm, and `motive_1` needs only one clause. -/

inductive SPSelf (k : Nat) : Prog → Prog → Prop where
  | base : SPSelf k
      (.search k (.neg (.plays .opp .self .C)) (.const .D) (.const .C))
      (.search k (.neg (.plays .opp .self .C)) (.const .D) (.const .C))
  | simL (p q o : Prog) :
      SPSelf k (p.subst (.sim p q) o) (q.subst (.sim p q) o) →
      SPSelf k (.sim p q) o
  | botSimL (p q o : Prog) :
      SPSelf k (p.subst (.bot (.sim p q)) o) (q.subst (.bot (.sim p q)) o) →
      SPSelf k (.bot (.sim p q)) o

theorem SPSelf_me {k : Nat} {me oppo : Prog} (h : SPSelf k me oppo) :
    me = WaryBot k ∨ (∃ p q, me = .sim p q) ∨ (∃ p q, me = .bot (.sim p q)) := by
  cases h with
  | base => exact Or.inl rfl
  | simL p q o _ => exact Or.inr (Or.inl ⟨p, q, rfl⟩)
  | botSimL p q o _ => exact Or.inr (Or.inr ⟨p, q, rfl⟩)

theorem SPSelf_opp {k : Nat} {me oppo : Prog} (h : SPSelf k me oppo) :
    oppo = WaryBot k := by
  induction h with
  | base => rfl
  | simL p q o hprem ih => exact subst_eq_wary (Or.inl ⟨p, q, rfl⟩) ih
  | botSimL p q o hprem ih => exact subst_eq_wary (Or.inr ⟨p, q, rfl⟩) ih

theorem SPSelf_not_bot (k : Nat) : ∀ oppo z, ¬ SPSelf k oppo (.bot z) := by
  intro oppo z h
  have hw := SPSelf_opp h
  simp [WaryBot] at hw

/-- Inversion at a `.sim` player (the base is `.search`-headed: only the lift). -/
theorem SPSelf_sim_inv {k : Nat} {p q oppo : Prog}
    (h : SPSelf k (.sim p q) oppo) :
    SPSelf k (p.subst (.sim p q) oppo) (q.subst (.sim p q) oppo) := by
  cases h with
  | simL _ _ _ hprem => exact hprem

theorem SPSelf_botSim_inv {k : Nat} {p q oppo : Prog}
    (h : SPSelf k (.bot (.sim p q)) oppo) :
    SPSelf k (p.subst (.bot (.sim p q)) oppo)
      (q.subst (.bot (.sim p q)) oppo) := by
  cases h with
  | botSimL _ _ _ hprem => exact hprem

set_option maxHeartbeats 1000000 in
/-- **WV-soundness for the self-play census** (see the convention note above
    `pf_WV_mirror` for why the raw recursor is deliberate here). -/
theorem pf_WV_self (k : Nat) : ∀ {K : Nat} {φ : Formula},
    Pf K φ → WV (SPSelf k) φ := by
  intro K φ h
  refine Pf.rec (motive_1 := fun me oppo body a n _ =>
      SPSelf k me oppo → (body = me ∨ me = .bot body) → a = .C)
    (motive_2 := fun m ψ _ => ∀ p q, SPSelf k p q → ψ ≠ .plays p q .D)
    (motive_3 := fun _ ψ _ => WV (SPSelf k) ψ)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    h
  -- ═══ PlaysProof arms (9) ═══
  · -- const
    intro me oppo a hSP hgate
    rcases SPSelf_me hSP with rfl | ⟨p', q', rfl⟩ | ⟨p', q', rfl⟩ <;>
      rcases hgate with hb | hb <;> exact absurd hb (by simp [WaryBot])
  · -- self
    intro me oppo a n hpl ih hSP hgate
    rcases SPSelf_me hSP with rfl | ⟨p', q', rfl⟩ | ⟨p', q', rfl⟩ <;>
      rcases hgate with hb | hb <;> exact absurd hb (by simp [WaryBot])
  · -- opp
    intro me oppo a n hpl ih hSP hgate
    rcases SPSelf_me hSP with rfl | ⟨p', q', rfl⟩ | ⟨p', q', rfl⟩ <;>
      rcases hgate with hb | hb <;> exact absurd hb (by simp [WaryBot])
  · -- bot
    intro me oppo p a n hpl ih hSP hgate
    rcases hgate with hb | hb
    · exact ih hSP (Or.inr hb.symm)
    · rcases SPSelf_me hSP with rfl | ⟨p', q', rfl⟩ | ⟨p', q', rfl⟩ <;>
        exact absurd hb (by simp [WaryBot])
  · -- sim : both gate shapes route through the SP lift inversions
    intro a n me oppo p q hpl ih hSP hgate
    rcases hgate with hb | hb
    · subst hb
      exact ih (SPSelf_sim_inv hSP) (Or.inl rfl)
    · subst hb
      exact ih (SPSelf_botSim_inv hSP) (Or.inl rfl)
  · -- ite_t
    intro me oppo b r m a' p a n q hb' hr hp ihb ihp hSP hgate
    rcases SPSelf_me hSP with rfl | ⟨p', q', rfl⟩ | ⟨p', q', rfl⟩ <;>
      rcases hgate with hg | hg <;> exact absurd hg (by simp [WaryBot])
  · -- ite_f
    intro me oppo b r m a' q a n p hb' hr hq ihb ihq hSP hgate
    rcases SPSelf_me hSP with rfl | ⟨p', q', rfl⟩ | ⟨p', q', rfl⟩ <;>
      rcases hgate with hg | hg <;> exact absurd hg (by simp [WaryBot])
  · -- search_t : THE base kill — the guard is the excluded refutation itself
    intro K' me oppo p a n φg q hg hp ihg ihp hSP hgate
    rcases hgate with hb | hb
    · subst hb
      cases hSP with
      | base =>
          simp only [Formula.subst, Prog.subst] at ihg
          rw [WV_neg] at ihg
          refine absurd ?_ ihg
          rw [WV_plays]
          exact Or.inl ⟨rfl, SPSelf.base⟩
    · rcases SPSelf_me hSP with rfl | ⟨p', q', rfl⟩ | ⟨p', q', rfl⟩ <;>
        exact absurd hb (by simp [WaryBot])
  · -- search_f : the else-branch is `.const .C`
    intro m me oppo q a n K' φg p hg hq ihg ihq hSP hgate
    rcases hgate with hb | hb
    · subst hb
      cases hSP with
      | base =>
          cases hq
          rfl
    · rcases SPSelf_me hSP with rfl | ⟨p', q', rfl⟩ | ⟨p', q', rfl⟩ <;>
        exact absurd hb (by simp [WaryBot])
  -- ═══ AtomProvable arm (1) ═══
  · -- mk
    intro me oppo a n K hpp hn ih p q hSP heq
    injection heq with h1 h2 h3
    subst h1; subst h2; subst h3
    exact Action.noConfusion (ih hSP (Or.inl rfl))
  -- ═══ Pf arms (29) ═══
  · -- atom
    intro K ψ hatom ih
    cases hatom with
    | mk hpp hn =>
        rw [WV_plays]
        exact Or.inr (Pf_sound _ _ (Pf.atom ⟨hpp, hn⟩))
  · -- atomNeg
    intro K p q b aN m hatom hne hle ih
    rw [WV_neg, WV_plays]
    rintro (⟨rfl, hSP⟩ | hint)
    · cases b with
      | C => exact hne rfl
      | D => exact ih p q hSP rfl
    · have hs := Pf_sound _ _ (Pf.atomNeg p q b aN m hatom hne hle)
      simp only [Formula.interp] at hs
      exact hs hint
  · -- searchBranch : sound even when reading the SP player's own source —
    -- under the raw box hypothesis the searcher REALLY plays its then-branch
    intro K g ψ a b me oppo hme hle
    rw [WV_impl, WV_box]
    intro hbox
    rw [WV_plays]
    exact Or.inr ((Pf_sound _ _ (Pf.searchBranch g ψ a b me oppo hme hle)) hbox)
  · -- simStep
    intro K me p q oppo a hme hle
    rw [WV_impl, WV_plays, WV_plays]
    rintro (⟨rfl, hSP⟩ | hint)
    · subst hme
      exact Or.inl ⟨rfl, SPSelf.simL p q oppo hSP⟩
    · exact Or.inr ((Pf_sound _ _ (Pf.simStep me p q oppo a hme hle)) hint)
  · -- botSimStep
    intro K me p q oppo a hme hle
    rw [WV_impl, WV_plays, WV_plays]
    rintro (⟨rfl, hSP⟩ | hint)
    · subst hme
      exact Or.inl ⟨rfl, SPSelf.botSimL p q oppo hSP⟩
    · exact Or.inr ((Pf_sound _ _ (Pf.botSimStep me p q oppo a hme hle)) hint)
  · -- botSearchStep
    intro K g ψ a b me oppo hme hle
    rw [WV_impl, WV_box]
    intro hbox
    rw [WV_plays]
    exact Or.inr ((Pf_sound _ _ (Pf.botSearchStep g ψ a b me oppo hme hle)) hbox)
  · -- iteBranchSearch_t
    intro K g z a' c0 c1 ψ q me oppo hme hle
    rw [WV_impl, WV_impl, WV_box]
    intro hprobe hbox
    rw [WV_plays]
    exact Or.inr ((Pf_sound _ _
      (Pf.iteBranchSearch_t g z a' c0 c1 ψ q me oppo hme hle))
      (interp_of_WV_probe (SPSelf_not_bot k) hprobe) hbox)
  · -- searchThenSearch_t
    intro K k₁ k₂ m ψ₁ ψ₂ c0 c1 q me oppo hme hprud hmk hle ih
    rw [WV_impl, WV_box]
    intro hbox
    rw [WV_plays]
    exact Or.inr ((Pf_sound _ _
      (Pf.searchThenSearch_t k₁ k₂ m ψ₁ ψ₂ c0 c1 q me oppo hme hprud hmk hle)) hbox)
  · -- searchChain
    intro K g₁ ψ₁ e₁ L a me oppo hme hle
    rw [WV_impl, WV_box]
    intro hbox
    exact WV_of_interp_searchChain me oppo a L
      ((Pf_sound _ _ (Pf.searchChain g₁ ψ₁ e₁ L a me oppo hme hle)) hbox)
  · -- ctxChain
    intro K hd L a me oppo hme hle
    have hs := Pf_sound _ _ (Pf.ctxChain hd L a me oppo hme hle)
    cases hd with
    | searchL g ψ e =>
        simp only [ctxGuard] at hs ⊢
        rw [WV_impl, WV_box]
        intro hbox
        exact WV_of_interp_ctxChain (SPSelf_not_bot k) me oppo a L (hs hbox)
    | iteL z aT other =>
        simp only [ctxGuard] at hs ⊢
        rw [WV_impl]
        intro hprobe
        exact WV_of_interp_ctxChain (SPSelf_not_bot k) me oppo a L
          (hs (interp_of_WV_probe (SPSelf_not_bot k) hprobe))
  · -- eqRefl
    intro K p hle
    rw [WV_eq]
  · -- eqNeg
    intro K p q hne hle
    rw [WV_neg, WV_eq]
    exact hne
  · -- mp
    intro K m₁ m₂ φ' α h1 h2 hle ih1 ih2
    rw [WV_impl] at ih1
    exact ih1 ih2
  · -- implTrans
    intro K φ' ψ χ a b h1 h2 hle ih1 ih2
    rw [WV_impl] at ih1 ih2 ⊢
    exact fun hφ => ih2 (ih1 hφ)
  · -- weakenImpl
    intro K φ' ψ m hψ hle ih
    rw [WV_impl]
    exact fun _ => ih
  · -- impS2
    intro φ' ψ χ m₁ m₂ K h1 h2 hle ih1 ih2
    rw [WV_impl] at ih1 ih2 ⊢
    intro hφ
    have hi := ih1 hφ
    rw [WV_impl] at hi
    exact hi (ih2 hφ)
  · -- implRefl
    intro K φ' hle
    rw [WV_impl]
    exact id
  · -- implK
    intro K φ' ψ hle
    rw [WV_impl]
    intro hφ
    rw [WV_impl]
    exact fun _ => hφ
  · -- implS
    intro K φ' ψ χ hle
    rw [WV_impl]
    intro hf
    rw [WV_impl]
    intro hg
    rw [WV_impl]
    intro hx
    rw [WV_impl] at hf hg
    have h1 := hf hx
    rw [WV_impl] at h1
    exact h1 (hg hx)
  · -- contrapose
    intro K φ' ψ m hp hle ih
    rw [WV_impl] at ih
    rw [WV_impl, WV_neg, WV_neg]
    exact fun hnψ hφ => hnψ (ih hφ)
  · -- negElim
    intro K φ' ψ m₁ m₂ h1 h2 hle ih1 ih2
    rw [WV_neg] at ih1
    exact absurd ih2 ih1
  · -- boxIntro
    intro kIn K φ' hprem hle ih
    rw [WV_box]
    exact hprem
  · -- atomBoxImpl
    intro K kBox p q a hatom hle _ihA
    show WV (SPSelf k) (.impl (.plays p q a) (.box kBox (.plays p q a)))
    rw [WV_impl, WV_box]
    exact fun _ => Pf.atom hatom
  · -- axK
    intro a b c m K φ' α hprem hgate hle ih
    rw [WV_box] at ih
    rw [WV_impl, WV_box, WV_box]
    exact fun hb => Pf.mp a b φ' α ih hb hgate
  · -- axKf
    intro a b c K φ' α hgate hsz
    rw [WV_impl, WV_box, WV_impl, WV_box, WV_box]
    exact fun h1 hb => Pf.mp a b φ' α h1 hb hgate
  · -- box4
    intro a b K φ' hgate hsz
    rw [WV_impl, WV_box, WV_box]
    exact fun hp => Pf.boxIntro a b φ' hp hgate
  · -- boxMono
    intro a b K φ' hab hsz
    rw [WV_impl, WV_box, WV_box]
    exact fun hp => Pf_mono hp hab
  · -- diagF
    intro pm fb g K tgt hgate hle ih
    rw [WV_impl, WV_diag, WV_impl, WV_box]
    exact fun hd => hd
  · -- diagB
    intro pm fb g K tgt hgate hle ih
    rw [WV_impl, WV_impl, WV_box, WV_diag]
    exact fun hd => hd

end WaryCensus

/-! #### Per-matchup facts (still HELPERS — same destination) -/

/-- WaryBot k's refutation guard against MirrorBot is underivable at EVERY
    budget (both fixpoints are semantically consistent; this is the syntactic
    exclusion, via `pf_WV_mirror` at the base atom). -/
theorem no_Pf_neg_mirror_wary (k K : Nat) :
    ¬ Pf K (.neg (.plays MirrorBot (WaryBot k) .C)) := by
  intro h
  have hWV := WaryCensus.pf_WV_mirror k h
  rw [WaryCensus.WV_neg] at hWV
  refine hWV ?_
  rw [WaryCensus.WV_plays]
  exact Or.inl ⟨rfl, WaryCensus.SPMirror.base⟩

theorem proofSearch_false_wary_MirrorBot (k : Nat) :
    proofSearch k (.neg (.plays MirrorBot (WaryBot k) .C)) = false := by
  cases h : proofSearch k (.neg (.plays MirrorBot (WaryBot k) .C)) with
  | true => exact absurd ((proofSearch_spec _ _).1 h) (no_Pf_neg_mirror_wary k k)
  | false => rfl

/-- WaryBot trusts MirrorBot at EVERY budget k (not just below the size floor). -/
theorem WaryBot_cooperates_vs_MirrorBot (k fuel : Nat) :
    play (fuel + 2) (WaryBot k) MirrorBot = some .C := by
  have hg := proofSearch_false_wary_MirrorBot k
  show eval (fuel + 2) (WaryBot k) MirrorBot (WaryBot k) = some .C
  unfold WaryBot at hg ⊢
  simp [eval, Prog.subst, Formula.subst, hg]

/-- MirrorBot replays the trust, at every budget. -/
theorem MirrorBot_plays_C_against_WaryBot (k fuel : Nat) :
    play (fuel + 3) MirrorBot (WaryBot k) = some .C := by
  have h := WaryBot_cooperates_vs_MirrorBot k fuel
  show eval (fuel + 3) MirrorBot (WaryBot k) MirrorBot = some .C
  simpa [eval, MirrorBot, Prog.subst] using h

/-- WaryBot k's self-refutation guard is underivable at EVERY budget. -/
theorem no_Pf_neg_wary_self (k K : Nat) :
    ¬ Pf K (.neg (.plays (WaryBot k) (WaryBot k) .C)) := by
  intro h
  have hWV := WaryCensus.pf_WV_self k h
  rw [WaryCensus.WV_neg] at hWV
  refine hWV ?_
  rw [WaryCensus.WV_plays]
  exact Or.inl ⟨rfl, WaryCensus.SPSelf.base⟩

theorem proofSearch_false_wary_self (k : Nat) :
    proofSearch k (.neg (.plays (WaryBot k) (WaryBot k) .C)) = false := by
  cases h : proofSearch k (.neg (.plays (WaryBot k) (WaryBot k) .C)) with
  | true => exact absurd ((proofSearch_spec _ _).1 h) (no_Pf_neg_wary_self k k)
  | false => rfl

/-- WaryBot trusts itself at EVERY budget k. -/
theorem WaryBot_cooperates_vs_WaryBot (k fuel : Nat) :
    play (fuel + 2) (WaryBot k) (WaryBot k) = some .C := by
  have hg := proofSearch_false_wary_self k
  show eval (fuel + 2) (WaryBot k) (WaryBot k) (WaryBot k) = some .C
  unfold WaryBot at hg ⊢
  simp [eval, Prog.subst, Formula.subst, hg]

end PD.Theorems
