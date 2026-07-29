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

/-! ## How the rest of the zoo plays against `WaryBot 2` (the floor regime) -/

/-- MirrorBot cooperates back: simulating WaryBot 2 against itself reaches the
    floor-forced trusting branch. -/
theorem MirrorBot_plays_C_against_WaryBot2 (fuel : Nat) :
    play (fuel + 3) MirrorBot (WaryBot 2) = some .C := by
  have h := WaryBot_cooperates_floor 2 fuel MirrorBot (by decide)
  show eval (fuel + 3) MirrorBot (WaryBot 2) MirrorBot = some .C
  simpa [eval, MirrorBot, Prog.subst] using h

/-- TitForTatBot's CooperateBot probe sees WaryBot 2 cooperate (floor), so it
    cooperates. -/
theorem TitForTatBot_plays_C_against_WaryBot2 (fuel : Nat) :
    play (fuel + 4) TitForTatBot (WaryBot 2) = some .C := by
  have hW : play (fuel + 2) (WaryBot 2) (.bot CooperateBot) = some .C :=
    WaryBot_cooperates_floor 2 fuel _ (by decide)
  have hGuard : eval (fuel + 3) TitForTatBot (WaryBot 2)
      (.sim .opp (.bot CooperateBot)) = some .C := by
    simpa [Nat.add_assoc] using
      (eval_sim_opp_bot_of_play (fuel + 2) TitForTatBot (WaryBot 2) CooperateBot .C hW)
  have hPlay := play_ite_from_guard fuel 3 TitForTatBot (WaryBot 2)
    (.sim .opp (.bot CooperateBot)) (.const .C) (.const .D) .C .C (by rfl) hGuard
  simpa [eval] using hPlay

/-- DBot's DefectBot probe sees WaryBot 2 cooperate (floor: it cannot afford the
    refutation even of a pure defector), so DBot EXPLOITS it. -/
theorem DBot_plays_D_against_WaryBot2 (fuel : Nat) :
    play (fuel + 4) DBot (WaryBot 2) = some .D := by
  have hW : play (fuel + 2) (WaryBot 2) (.bot DefectBot) = some .C :=
    WaryBot_cooperates_floor 2 fuel _ (by decide)
  have hGuard : eval (fuel + 3) DBot (WaryBot 2)
      (.sim .opp (.bot DefectBot)) = some .C := by
    simpa [Nat.add_assoc] using
      (eval_sim_opp_bot_of_play (fuel + 2) DBot (WaryBot 2) DefectBot .C hW)
  have hPlay := play_ite_from_guard fuel 3 DBot (WaryBot 2)
    (.sim .opp (.bot DefectBot)) (.const .D) (.const .C) .C .C (by rfl) hGuard
  simpa [eval] using hPlay

/-- EBot's first probe (vs DefectBot) sees WaryBot 2 cooperate, so EBot defects
    immediately. -/
theorem EBot_plays_D_against_WaryBot2 (fuel : Nat) :
    play (fuel + 4) EBot (WaryBot 2) = some .D := by
  have hW : play (fuel + 2) (WaryBot 2) (.bot DefectBot) = some .C :=
    WaryBot_cooperates_floor 2 fuel _ (by decide)
  have hGuard : eval (fuel + 3) EBot (WaryBot 2)
      (.sim .opp (.bot DefectBot)) = some .C := by
    simpa [Nat.add_assoc] using
      (eval_sim_opp_bot_of_play (fuel + 2) EBot (WaryBot 2) DefectBot .C hW)
  have hPlay := play_ite_from_guard fuel 3 EBot (WaryBot 2)
    (.sim .opp (.bot DefectBot)) (.const .D)
    (.ite (.sim .opp (.bot CooperateBot)) .C (.const .C)
      (.ite (.sim .opp (.bot MirrorBot)) .C (.const .C) (.const .D)))
    .C .C (by rfl) hGuard
  simpa [eval] using hPlay

/-- OBot clears WaryBot 2 on both probes (floor cooperation both times) and
    cooperates. -/
theorem OBot_plays_C_against_WaryBot2 (fuel : Nat) :
    play (fuel + 5) OBot (WaryBot 2) = some .C := by
  have hW1 : play (fuel + 3) (WaryBot 2) (.bot CooperateBot) = some .C :=
    WaryBot_cooperates_floor 2 (fuel + 1) _ (by decide)
  have hW2 : play (fuel + 2) (WaryBot 2) (.bot DefectBot) = some .C :=
    WaryBot_cooperates_floor 2 fuel _ (by decide)
  have hG1 : eval (fuel + 4) OBot (WaryBot 2)
      (.sim .opp (.bot CooperateBot)) = some .C := by
    simpa [Nat.add_assoc] using
      (eval_sim_opp_bot_of_play (fuel + 3) OBot (WaryBot 2) CooperateBot .C hW1)
  have hG2 : eval (fuel + 3) OBot (WaryBot 2)
      (.sim .opp (.bot DefectBot)) = some .C := by
    simpa [Nat.add_assoc] using
      (eval_sim_opp_bot_of_play (fuel + 2) OBot (WaryBot 2) DefectBot .C hW2)
  have hInner : eval (fuel + 4) OBot (WaryBot 2)
      (.ite (.sim .opp (.bot DefectBot)) .C (.const .C) (.const .D)) = some .C := by
    have h := eval_ite_from_guard (fuel + 3) OBot (WaryBot 2)
      (.sim .opp (.bot DefectBot)) (.const .C) (.const .D) .C .C hG2
    simpa [Nat.add_assoc, eval] using h
  have hPlay := play_ite_from_guard fuel 4 OBot (WaryBot 2)
    (.sim .opp (.bot CooperateBot))
    (.ite (.sim .opp (.bot DefectBot)) .C (.const .C) (.const .D)) (.const .D)
    .C .C (by rfl) hG1
  simpa [hInner] using hPlay

/-- CIMCIC 2's implication guard outgrows its budget against WaryBot 2 (the size
    floor for `.impl`), so it falls to its defecting else-branch. -/
theorem CIMCIC2_plays_D_against_WaryBot2 (fuel : Nat) :
    play (fuel + 2) (CIMCIC 2) (WaryBot 2) = some .D := by
  have hg : proofSearch 2 (.impl (.plays (CIMCIC 2) (WaryBot 2) .C)
      (.plays (WaryBot 2) (CIMCIC 2) .C)) = false :=
    proofSearch_false_impl_undersized (by decide)
  show eval (fuel + 2) (CIMCIC 2) (WaryBot 2) (CIMCIC 2) = some .D
  unfold CIMCIC at hg ⊢
  simp [eval, Prog.subst, Formula.subst, hg]

/-- DIMCID 2's implication guard also hits the size floor, so it falls to its
    cooperating else-branch. -/
theorem DIMCID2_plays_C_against_WaryBot2 (fuel : Nat) :
    play (fuel + 2) (DIMCID 2) (WaryBot 2) = some .C := by
  have hg : proofSearch 2 (.impl (.plays (DIMCID 2) (WaryBot 2) .C)
      (.plays (WaryBot 2) (DIMCID 2) .D)) = false :=
    proofSearch_false_impl_undersized (by decide)
  show eval (fuel + 2) (DIMCID 2) (WaryBot 2) (DIMCID 2) = some .C
  unfold DIMCID at hg ⊢
  simp [eval, Prog.subst, Formula.subst, hg]

end PD.Theorems
