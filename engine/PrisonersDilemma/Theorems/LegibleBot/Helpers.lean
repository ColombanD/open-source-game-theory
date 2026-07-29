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
small budgets the guard size strictly exceeds `kOut` and the SIZE FLOOR
(`proofSearch_false_box_undersized`) forces the illegible else-branch: it defects
against EVERYONE, including CooperateBot. Its non-degenerate regime (kOut ≳ 30)
needs a `.box` prover and is left to the proof agent. Verified against the
deterministic pre-pass (2026-07-29). -/

/-- **The floor**: below the substituted box-guard's size, LegibleBot cannot
    certify its own legibility and defects. Size hypothesis per-opponent
    `by decide`. -/
theorem LegibleBot_defects_floor (kOut kIn fuel : Nat) (opponent : Prog)
    (hsz : kOut < (Formula.box kIn (.plays (LegibleBot kOut kIn) opponent .C)).size) :
    play (fuel + 2) (LegibleBot kOut kIn) opponent = some .D := by
  have hg := proofSearch_false_box_undersized hsz
  show eval (fuel + 2) (LegibleBot kOut kIn) opponent (LegibleBot kOut kIn) = some .D
  unfold LegibleBot at hg ⊢
  simp [eval, Prog.subst, Formula.subst, hg]

/-! ## How the rest of the zoo plays against `LegibleBot 2 2` -/

/-- MirrorBot mirrors the floor-defection back. -/
theorem MirrorBot_plays_D_against_LegibleBot22 (fuel : Nat) :
    play (fuel + 3) MirrorBot (LegibleBot 2 2) = some .D := by
  have h := LegibleBot_defects_floor 2 2 fuel MirrorBot (by decide)
  show eval (fuel + 3) MirrorBot (LegibleBot 2 2) MirrorBot = some .D
  simpa [eval, MirrorBot, Prog.subst] using h

/-- TitForTatBot's CooperateBot probe sees the floor-defection and punishes. -/
theorem TitForTatBot_plays_D_against_LegibleBot22 (fuel : Nat) :
    play (fuel + 4) TitForTatBot (LegibleBot 2 2) = some .D := by
  have hL : play (fuel + 2) (LegibleBot 2 2) (.bot CooperateBot) = some .D :=
    LegibleBot_defects_floor 2 2 fuel _ (by decide)
  have hGuard : eval (fuel + 3) TitForTatBot (LegibleBot 2 2)
      (.sim .opp (.bot CooperateBot)) = some .D := by
    simpa [Nat.add_assoc] using
      (eval_sim_opp_bot_of_play (fuel + 2) TitForTatBot (LegibleBot 2 2) CooperateBot .D hL)
  have hPlay := play_ite_from_guard fuel 3 TitForTatBot (LegibleBot 2 2)
    (.sim .opp (.bot CooperateBot)) (.const .C) (.const .D) .C .D (by rfl) hGuard
  simpa [eval] using hPlay

/-- DBot's DefectBot probe sees the floor-defection, so DBot cooperates (it only
    exploits bots that cooperate with defectors). -/
theorem DBot_plays_C_against_LegibleBot22 (fuel : Nat) :
    play (fuel + 4) DBot (LegibleBot 2 2) = some .C := by
  have hL : play (fuel + 2) (LegibleBot 2 2) (.bot DefectBot) = some .D :=
    LegibleBot_defects_floor 2 2 fuel _ (by decide)
  have hGuard : eval (fuel + 3) DBot (LegibleBot 2 2)
      (.sim .opp (.bot DefectBot)) = some .D := by
    simpa [Nat.add_assoc] using
      (eval_sim_opp_bot_of_play (fuel + 2) DBot (LegibleBot 2 2) DefectBot .D hL)
  have hPlay := play_ite_from_guard fuel 3 DBot (LegibleBot 2 2)
    (.sim .opp (.bot DefectBot)) (.const .D) (.const .C) .C .D (by rfl) hGuard
  simpa [eval] using hPlay

/-- OBot's first probe (vs CooperateBot) already sees the floor-defection and
    OBot defects. -/
theorem OBot_plays_D_against_LegibleBot22 (fuel : Nat) :
    play (fuel + 4) OBot (LegibleBot 2 2) = some .D := by
  have hL : play (fuel + 2) (LegibleBot 2 2) (.bot CooperateBot) = some .D :=
    LegibleBot_defects_floor 2 2 fuel _ (by decide)
  have hGuard : eval (fuel + 3) OBot (LegibleBot 2 2)
      (.sim .opp (.bot CooperateBot)) = some .D := by
    simpa [Nat.add_assoc] using
      (eval_sim_opp_bot_of_play (fuel + 2) OBot (LegibleBot 2 2) CooperateBot .D hL)
  have hPlay := play_ite_from_guard fuel 3 OBot (LegibleBot 2 2)
    (.sim .opp (.bot CooperateBot))
    (.ite (.sim .opp (.bot DefectBot)) .C (.const .C) (.const .D)) (.const .D)
    .C .D (by rfl) hGuard
  simpa [eval] using hPlay

/-- EBot walks all three probes (DefectBot, CooperateBot, MirrorBot), sees the
    floor-defection each time, and defects. -/
theorem EBot_plays_D_against_LegibleBot22 (fuel : Nat) :
    play (fuel + 6) EBot (LegibleBot 2 2) = some .D := by
  have hL1 : play (fuel + 4) (LegibleBot 2 2) (.bot DefectBot) = some .D :=
    LegibleBot_defects_floor 2 2 (fuel + 2) _ (by decide)
  have hL2 : play (fuel + 3) (LegibleBot 2 2) (.bot CooperateBot) = some .D :=
    LegibleBot_defects_floor 2 2 (fuel + 1) _ (by decide)
  have hL3 : play (fuel + 2) (LegibleBot 2 2) (.bot MirrorBot) = some .D :=
    LegibleBot_defects_floor 2 2 fuel _ (by decide)
  have hG1 : eval (fuel + 5) EBot (LegibleBot 2 2)
      (.sim .opp (.bot DefectBot)) = some .D := by
    simpa [Nat.add_assoc] using
      (eval_sim_opp_bot_of_play (fuel + 4) EBot (LegibleBot 2 2) DefectBot .D hL1)
  have hG2 : eval (fuel + 4) EBot (LegibleBot 2 2)
      (.sim .opp (.bot CooperateBot)) = some .D := by
    simpa [Nat.add_assoc] using
      (eval_sim_opp_bot_of_play (fuel + 3) EBot (LegibleBot 2 2) CooperateBot .D hL2)
  have hG3 : eval (fuel + 3) EBot (LegibleBot 2 2)
      (.sim .opp (.bot MirrorBot)) = some .D := by
    simpa [Nat.add_assoc] using
      (eval_sim_opp_bot_of_play (fuel + 2) EBot (LegibleBot 2 2) MirrorBot .D hL3)
  have hInner3 : eval (fuel + 4) EBot (LegibleBot 2 2)
      (.ite (.sim .opp (.bot MirrorBot)) .C (.const .C) (.const .D)) = some .D := by
    have h := eval_ite_from_guard (fuel + 3) EBot (LegibleBot 2 2)
      (.sim .opp (.bot MirrorBot)) (.const .C) (.const .D) .C .D hG3
    simpa [Nat.add_assoc, eval] using h
  have hInner2 : eval (fuel + 5) EBot (LegibleBot 2 2)
      (.ite (.sim .opp (.bot CooperateBot)) .C (.const .C)
        (.ite (.sim .opp (.bot MirrorBot)) .C (.const .C) (.const .D))) = some .D := by
    have h := eval_ite_from_guard (fuel + 4) EBot (LegibleBot 2 2)
      (.sim .opp (.bot CooperateBot)) (.const .C)
      (.ite (.sim .opp (.bot MirrorBot)) .C (.const .C) (.const .D)) .C .D hG2
    rw [show fuel + 4 + 1 = fuel + 5 by omega] at h
    simpa [hInner3] using h
  have hPlay := play_ite_from_guard fuel 5 EBot (LegibleBot 2 2)
    (.sim .opp (.bot DefectBot)) (.const .D)
    (.ite (.sim .opp (.bot CooperateBot)) .C (.const .C)
      (.ite (.sim .opp (.bot MirrorBot)) .C (.const .C) (.const .D)))
    .C .D (by rfl) hG1
  simpa [hInner2] using hPlay

/-- CIMCIC 2's implication guard hits the size floor against LegibleBot 2 2. -/
theorem CIMCIC2_plays_D_against_LegibleBot22 (fuel : Nat) :
    play (fuel + 2) (CIMCIC 2) (LegibleBot 2 2) = some .D := by
  have hg : proofSearch 2 (.impl (.plays (CIMCIC 2) (LegibleBot 2 2) .C)
      (.plays (LegibleBot 2 2) (CIMCIC 2) .C)) = false :=
    proofSearch_false_impl_undersized (by decide)
  show eval (fuel + 2) (CIMCIC 2) (LegibleBot 2 2) (CIMCIC 2) = some .D
  unfold CIMCIC at hg ⊢
  simp [eval, Prog.subst, Formula.subst, hg]

/-- DIMCID 2's implication guard hits the size floor; it cooperates by default. -/
theorem DIMCID2_plays_C_against_LegibleBot22 (fuel : Nat) :
    play (fuel + 2) (DIMCID 2) (LegibleBot 2 2) = some .C := by
  have hg : proofSearch 2 (.impl (.plays (DIMCID 2) (LegibleBot 2 2) .C)
      (.plays (LegibleBot 2 2) (DIMCID 2) .D)) = false :=
    proofSearch_false_impl_undersized (by decide)
  show eval (fuel + 2) (DIMCID 2) (LegibleBot 2 2) (DIMCID 2) = some .C
  unfold DIMCID at hg ⊢
  simp [eval, Prog.subst, Formula.subst, hg]

end PD.Theorems
