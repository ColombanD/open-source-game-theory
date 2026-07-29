import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Bots.MirrorBot
import PrisonersDilemma.Bots.TitForTatBot
import PrisonersDilemma.Bots.OBot
import PrisonersDilemma.Bots.DBot
import PrisonersDilemma.Bots.EBot
import PrisonersDilemma.Bots.LlmGenerations.LegibleBot
import PrisonersDilemma.Bots.LlmGenerations.CIMCIC
import PrisonersDilemma.Bots.LlmGenerations.DIMCID
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.BaseTheorems

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

/-! # LegibleBot matchup helpers — the floor-dominated regime

LegibleBot's guard `□_kIn (I play C)` contains its own substituted source, so at
budgets below the guard's size the SIZE FLOOR (`proofSearch_false_box_undersized`)
forces the illegible else-branch: it defects against EVERYONE, including
CooperateBot. Every lemma is stated for the WHOLE floor regime (size hypotheses,
discharged `by decide` at concrete budgets). The non-degenerate regime — where the
guard fits and a `.box` prover could fire it (bounded Löb through two boxes) — is
OPEN, and is the LegibleBot slice of the prover-agent benchmark. Verified against
the deterministic pre-pass (2026-07-29). -/

/-- **The floor**: below the substituted box-guard's size, LegibleBot cannot
    certify its own legibility and defects. -/
theorem LegibleBot_defects_floor (kOut kIn fuel : Nat) (opponent : Prog)
    (hsz : kOut < (Formula.box kIn (.plays (LegibleBot kOut kIn) opponent .C)).size) :
    play (fuel + 2) (LegibleBot kOut kIn) opponent = some .D := by
  have hg := proofSearch_false_box_undersized hsz
  show eval (fuel + 2) (LegibleBot kOut kIn) opponent (LegibleBot kOut kIn) = some .D
  unfold LegibleBot at hg ⊢
  simp [eval, Prog.subst, Formula.subst, hg]

/-! ## How the rest of the zoo plays against a floor-regime LegibleBot -/

/-- MirrorBot mirrors the floor-defection back. -/
theorem MirrorBot_plays_D_against_LegibleBot_floor (kOut kIn fuel : Nat)
    (hszM : kOut < (Formula.box kIn
      (.plays (LegibleBot kOut kIn) MirrorBot .C)).size) :
    play (fuel + 3) MirrorBot (LegibleBot kOut kIn) = some .D := by
  have h := LegibleBot_defects_floor kOut kIn fuel MirrorBot hszM
  show eval (fuel + 3) MirrorBot (LegibleBot kOut kIn) MirrorBot = some .D
  simpa [eval, MirrorBot, Prog.subst] using h

/-- TitForTatBot's CooperateBot probe sees the floor-defection and punishes. -/
theorem TitForTatBot_plays_D_against_LegibleBot_floor (kOut kIn fuel : Nat)
    (hszCB : kOut < (Formula.box kIn
      (.plays (LegibleBot kOut kIn) (.bot CooperateBot) .C)).size) :
    play (fuel + 4) TitForTatBot (LegibleBot kOut kIn) = some .D := by
  have hL : play (fuel + 2) (LegibleBot kOut kIn) (.bot CooperateBot) = some .D :=
    LegibleBot_defects_floor kOut kIn fuel _ hszCB
  have hGuard : eval (fuel + 3) TitForTatBot (LegibleBot kOut kIn)
      (.sim .opp (.bot CooperateBot)) = some .D := by
    simpa [Nat.add_assoc] using
      (eval_sim_opp_bot_of_play (fuel + 2) TitForTatBot (LegibleBot kOut kIn)
        CooperateBot .D hL)
  have hPlay := play_ite_from_guard fuel 3 TitForTatBot (LegibleBot kOut kIn)
    (.sim .opp (.bot CooperateBot)) (.const .C) (.const .D) .C .D (by rfl) hGuard
  simpa [eval] using hPlay

/-- DBot's DefectBot probe sees the floor-defection, so DBot cooperates (it only
    exploits bots that cooperate with defectors). -/
theorem DBot_plays_C_against_LegibleBot_floor (kOut kIn fuel : Nat)
    (hszDB : kOut < (Formula.box kIn
      (.plays (LegibleBot kOut kIn) (.bot DefectBot) .C)).size) :
    play (fuel + 4) DBot (LegibleBot kOut kIn) = some .C := by
  have hL : play (fuel + 2) (LegibleBot kOut kIn) (.bot DefectBot) = some .D :=
    LegibleBot_defects_floor kOut kIn fuel _ hszDB
  have hGuard : eval (fuel + 3) DBot (LegibleBot kOut kIn)
      (.sim .opp (.bot DefectBot)) = some .D := by
    simpa [Nat.add_assoc] using
      (eval_sim_opp_bot_of_play (fuel + 2) DBot (LegibleBot kOut kIn)
        DefectBot .D hL)
  have hPlay := play_ite_from_guard fuel 3 DBot (LegibleBot kOut kIn)
    (.sim .opp (.bot DefectBot)) (.const .D) (.const .C) .C .D (by rfl) hGuard
  simpa [eval] using hPlay

/-- OBot's first probe (vs CooperateBot) already sees the floor-defection and
    OBot defects. -/
theorem OBot_plays_D_against_LegibleBot_floor (kOut kIn fuel : Nat)
    (hszCB : kOut < (Formula.box kIn
      (.plays (LegibleBot kOut kIn) (.bot CooperateBot) .C)).size) :
    play (fuel + 4) OBot (LegibleBot kOut kIn) = some .D := by
  have hL : play (fuel + 2) (LegibleBot kOut kIn) (.bot CooperateBot) = some .D :=
    LegibleBot_defects_floor kOut kIn fuel _ hszCB
  have hGuard : eval (fuel + 3) OBot (LegibleBot kOut kIn)
      (.sim .opp (.bot CooperateBot)) = some .D := by
    simpa [Nat.add_assoc] using
      (eval_sim_opp_bot_of_play (fuel + 2) OBot (LegibleBot kOut kIn)
        CooperateBot .D hL)
  have hPlay := play_ite_from_guard fuel 3 OBot (LegibleBot kOut kIn)
    (.sim .opp (.bot CooperateBot))
    (.ite (.sim .opp (.bot DefectBot)) .C (.const .C) (.const .D)) (.const .D)
    .C .D (by rfl) hGuard
  simpa [eval] using hPlay

/-- EBot walks all three probes (DefectBot, CooperateBot, MirrorBot), sees the
    floor-defection each time, and defects. -/
theorem EBot_plays_D_against_LegibleBot_floor (kOut kIn fuel : Nat)
    (hszDB : kOut < (Formula.box kIn
      (.plays (LegibleBot kOut kIn) (.bot DefectBot) .C)).size)
    (hszCB : kOut < (Formula.box kIn
      (.plays (LegibleBot kOut kIn) (.bot CooperateBot) .C)).size)
    (hszM : kOut < (Formula.box kIn
      (.plays (LegibleBot kOut kIn) (.bot MirrorBot) .C)).size) :
    play (fuel + 6) EBot (LegibleBot kOut kIn) = some .D := by
  have hL1 : play (fuel + 4) (LegibleBot kOut kIn) (.bot DefectBot) = some .D :=
    LegibleBot_defects_floor kOut kIn (fuel + 2) _ hszDB
  have hL2 : play (fuel + 3) (LegibleBot kOut kIn) (.bot CooperateBot) = some .D :=
    LegibleBot_defects_floor kOut kIn (fuel + 1) _ hszCB
  have hL3 : play (fuel + 2) (LegibleBot kOut kIn) (.bot MirrorBot) = some .D :=
    LegibleBot_defects_floor kOut kIn fuel _ hszM
  have hG1 : eval (fuel + 5) EBot (LegibleBot kOut kIn)
      (.sim .opp (.bot DefectBot)) = some .D := by
    simpa [Nat.add_assoc] using
      (eval_sim_opp_bot_of_play (fuel + 4) EBot (LegibleBot kOut kIn)
        DefectBot .D hL1)
  have hG2 : eval (fuel + 4) EBot (LegibleBot kOut kIn)
      (.sim .opp (.bot CooperateBot)) = some .D := by
    simpa [Nat.add_assoc] using
      (eval_sim_opp_bot_of_play (fuel + 3) EBot (LegibleBot kOut kIn)
        CooperateBot .D hL2)
  have hG3 : eval (fuel + 3) EBot (LegibleBot kOut kIn)
      (.sim .opp (.bot MirrorBot)) = some .D := by
    simpa [Nat.add_assoc] using
      (eval_sim_opp_bot_of_play (fuel + 2) EBot (LegibleBot kOut kIn)
        MirrorBot .D hL3)
  have hInner3 : eval (fuel + 4) EBot (LegibleBot kOut kIn)
      (.ite (.sim .opp (.bot MirrorBot)) .C (.const .C) (.const .D)) = some .D := by
    have h := eval_ite_from_guard (fuel + 3) EBot (LegibleBot kOut kIn)
      (.sim .opp (.bot MirrorBot)) (.const .C) (.const .D) .C .D hG3
    simpa [Nat.add_assoc, eval] using h
  have hInner2 : eval (fuel + 5) EBot (LegibleBot kOut kIn)
      (.ite (.sim .opp (.bot CooperateBot)) .C (.const .C)
        (.ite (.sim .opp (.bot MirrorBot)) .C (.const .C) (.const .D))) = some .D := by
    have h := eval_ite_from_guard (fuel + 4) EBot (LegibleBot kOut kIn)
      (.sim .opp (.bot CooperateBot)) (.const .C)
      (.ite (.sim .opp (.bot MirrorBot)) .C (.const .C) (.const .D)) .C .D hG2
    rw [show fuel + 4 + 1 = fuel + 5 by omega] at h
    simpa [hInner3] using h
  have hPlay := play_ite_from_guard fuel 5 EBot (LegibleBot kOut kIn)
    (.sim .opp (.bot DefectBot)) (.const .D)
    (.ite (.sim .opp (.bot CooperateBot)) .C (.const .C)
      (.ite (.sim .opp (.bot MirrorBot)) .C (.const .C) (.const .D)))
    .C .D (by rfl) hG1
  simpa [hInner2] using hPlay

/-- CIMCIC's implication guard hits the size floor against a same-budget
    LegibleBot. -/
theorem CIMCIC_plays_D_against_LegibleBot_floor (k fuel : Nat)
    (hszI : k < (Formula.impl (.plays (CIMCIC k) (LegibleBot k k) .C)
      (.plays (LegibleBot k k) (CIMCIC k) .C)).size) :
    play (fuel + 2) (CIMCIC k) (LegibleBot k k) = some .D := by
  have hg := proofSearch_false_impl_undersized hszI
  show eval (fuel + 2) (CIMCIC k) (LegibleBot k k) (CIMCIC k) = some .D
  unfold CIMCIC at hg ⊢
  simp [eval, Prog.subst, Formula.subst, hg]

/-- DIMCID's implication guard hits the size floor; it cooperates by default. -/
theorem DIMCID_plays_C_against_LegibleBot_floor (k fuel : Nat)
    (hszI : k < (Formula.impl (.plays (DIMCID k) (LegibleBot k k) .C)
      (.plays (LegibleBot k k) (DIMCID k) .D)).size) :
    play (fuel + 2) (DIMCID k) (LegibleBot k k) = some .C := by
  have hg := proofSearch_false_impl_undersized hszI
  show eval (fuel + 2) (DIMCID k) (LegibleBot k k) (DIMCID k) = some .C
  unfold DIMCID at hg ⊢
  simp [eval, Prog.subst, Formula.subst, hg]

end PD.Theorems
