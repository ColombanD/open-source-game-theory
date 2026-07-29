import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Bots.MirrorBot
import PrisonersDilemma.Bots.LlmGenerations.GuardianBot
import PrisonersDilemma.Theorems.CooperateBot.Helpers
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.BaseTheorems

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

/-! # GuardianBot matchup helpers

GuardianBot's guard `.plays .opp (.bot CooperateBot) .D` ("the opponent bullies
CooperateBot") substitutes to a formula mentioning ONLY the opponent and the frozen
probe — never GuardianBot itself. So its guard verdicts are self-reference-free:
positive certificates for constant bullies, soundness refutations for everyone the
probe clears. Statements verified against the deterministic pre-pass (2026-07-29). -/

/-- DefectBot provably bullies the probe: a bare `.const` certificate at cost
    `c_leaf`, so the guard fires at every budget `k ≥ 1`. -/
theorem proofSearch_true_guardian_DefectBot (k : Nat) :
    proofSearch (k + 1) (.plays DefectBot (.bot CooperateBot) .D) = true :=
  (proofSearch_spec _ _).2 (Pf.atom ⟨PlaysProof.const, by unfold c_leaf; omega⟩)

/-- CooperateBot never bullies the probe (it cannot play D at all), so the guard
    is refuted by soundness at EVERY budget. -/
theorem proofSearch_false_guardian_CooperateBot (k : Nat) :
    proofSearch k (.plays CooperateBot (.bot CooperateBot) .D) = false := by
  cases h : proofSearch k (.plays CooperateBot (.bot CooperateBot) .D) with
  | true  => exact absurd (proofSearch_sound _ _ h)
                          (interp_CooperateBot_plays_D_false _)
  | false => rfl

/-- MirrorBot cooperates with the frozen CooperateBot probe: the `.sim .opp .self`
    body substitutes to running `.bot CooperateBot` (against MirrorBot), which is
    CooperateBot's constant C two `.bot`/`.sim` steps down. -/
theorem play_MirrorBot_vs_botCB (n : Nat) :
    play (n + 3) MirrorBot (.bot CooperateBot) = some .C := by
  simp [play, eval, MirrorBot, Prog.subst, CooperateBot]

/-- The semantic refutation feeding soundness: "MirrorBot plays D against the
    probe" is false at every fuel. -/
theorem interp_MirrorBot_vs_botCB_D_false :
    ¬ (Formula.plays MirrorBot (.bot CooperateBot) .D).interp := by
  rintro ⟨n, hn⟩
  cases n with
  | zero => simp [play, eval] at hn
  | succ m =>
      cases m with
      | zero => simp [play, eval, MirrorBot] at hn
      | succ l =>
          cases l with
          | zero => simp [play, eval, MirrorBot, Prog.subst, CooperateBot] at hn
          | succ i =>
              rw [play_MirrorBot_vs_botCB] at hn
              cases hn

/-- MirrorBot never provably bullies the probe. -/
theorem proofSearch_false_guardian_MirrorBot (k : Nat) :
    proofSearch k (.plays MirrorBot (.bot CooperateBot) .D) = false := by
  cases h : proofSearch k (.plays MirrorBot (.bot CooperateBot) .D) with
  | true  => exact absurd (proofSearch_sound _ _ h) interp_MirrorBot_vs_botCB_D_false
  | false => rfl

/-- GuardianBot punishes DefectBot: the bully certificate fires the guard. -/
theorem GuardianBot_defects_vs_DefectBot (k fuel : Nat) :
    play (fuel + 2) (GuardianBot (k + 1)) DefectBot = some .D := by
  have hg := proofSearch_true_guardian_DefectBot k
  show eval (fuel + 2) (GuardianBot (k + 1)) DefectBot (GuardianBot (k + 1)) = some .D
  unfold GuardianBot
  simp [eval, Prog.subst, Formula.subst, hg]

/-- GuardianBot trusts CooperateBot: the guard is refuted, the else-branch trusts. -/
theorem GuardianBot_cooperates_vs_CooperateBot (k fuel : Nat) :
    play (fuel + 2) (GuardianBot k) CooperateBot = some .C := by
  have hg := proofSearch_false_guardian_CooperateBot k
  show eval (fuel + 2) (GuardianBot k) CooperateBot (GuardianBot k) = some .C
  unfold GuardianBot
  simp [eval, Prog.subst, Formula.subst, hg]

/-- GuardianBot trusts MirrorBot (the probe clears it). -/
theorem GuardianBot_cooperates_vs_MirrorBot (k fuel : Nat) :
    play (fuel + 2) (GuardianBot k) MirrorBot = some .C := by
  have hg := proofSearch_false_guardian_MirrorBot k
  show eval (fuel + 2) (GuardianBot k) MirrorBot (GuardianBot k) = some .C
  unfold GuardianBot
  simp [eval, Prog.subst, Formula.subst, hg]

/-- MirrorBot cooperates back: simulating GuardianBot against itself reaches
    GuardianBot's (guard-refuted) trusting else-branch. -/
theorem MirrorBot_plays_C_against_GuardianBot (k fuel : Nat) :
    play (fuel + 3) MirrorBot (GuardianBot k) = some .C := by
  have h := GuardianBot_cooperates_vs_MirrorBot k fuel
  show eval (fuel + 3) MirrorBot (GuardianBot k) MirrorBot = some .C
  simpa [eval, MirrorBot, Prog.subst] using h

end PD.Theorems
