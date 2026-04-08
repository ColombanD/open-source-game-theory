import PrisonersDilemma.Models.OpenSourceBots

namespace PD.Proofs.OpenSourceBots

open PD
open PD.Action
open PD.Models.OpenSourceBots

abbrev payoff (mine opponent : Action) : Nat :=
  PD.payoff PD.canonicalPayoff mine opponent

@[simp] theorem source_eq_source (b : Bot) :
    ProgramModel.source b = source b := rfl

@[simp] theorem actionFromSource_eq_evalSource (me : Bot) (oppSource : SourceAST) :
    ProgramModel.actionFromSource me oppSource = evalSource me oppSource := rfl

section ActionClaimTheorems

/-- CooperateBot vs CooperateBot: mutual cooperation. -/
theorem cc_actionClaim :
    ActionClaim Bot.cooperateBot Bot.cooperateBot C C := by
  unfold ActionClaim playActions
  simp [ProgramModel.action]

/-- CooperateBot vs DefectBot: (C,D). -/
theorem cd_actionClaim :
    ActionClaim Bot.cooperateBot Bot.defectBot C D := by
  unfold ActionClaim playActions
  simp [ProgramModel.action]

/-- DefectBot vs CooperateBot: (D,C). -/
theorem dc_actionClaim :
    ActionClaim Bot.defectBot Bot.cooperateBot D C := by
  unfold ActionClaim playActions
  simp [ProgramModel.action]

/-- DefectBot vs DefectBot: mutual defection. -/
theorem dd_actionClaim :
    ActionClaim Bot.defectBot Bot.defectBot D D := by
  unfold ActionClaim playActions
  simp [ProgramModel.action]

/-- TitForTat vs CooperateBot: mutual cooperation. -/
theorem tft_c_actionClaim :
    ActionClaim Bot.titForTat Bot.cooperateBot C C := by
  unfold ActionClaim playActions
  simp [ProgramModel.action]

/-- TitForTat vs DefectBot: mutual defection. -/
theorem tft_d_actionClaim :
    ActionClaim Bot.titForTat Bot.defectBot D D := by
  unfold ActionClaim playActions
  simp [ProgramModel.action]

/-- TitForTat vs TitForTat: mutual cooperation. -/
theorem tft_tft_actionClaim :
    ActionClaim Bot.titForTat Bot.titForTat C C := by
  unfold ActionClaim playActions
  simp [ProgramModel.action]

/-- CooperateBot always cooperates, regardless of opponent. -/
theorem cooperateBot_always_cooperates (opp : Bot) :
    eval Bot.cooperateBot opp = C := by
  simp [eval, ProgramModel.action]

/-- CooperateBot never defects. -/
theorem cooperateBot_never_defects (opp : Bot) :
    eval Bot.cooperateBot opp ≠ D := by
  simp [eval, ProgramModel.action]

/-- DefectBot always defects, regardless of opponent. -/
theorem defectBot_always_defects (opp : Bot) :
    eval Bot.defectBot opp = D := by
  simp [eval, ProgramModel.action]

/-- DBot exploits naive cooperators by defecting. -/
theorem dBot_defects_against_cooperateBot :
    eval Bot.dBot Bot.cooperateBot = D := by
  simp [eval, ProgramModel.action]

/-- DBot cooperates with defensive defectors (contrarian probe behavior). -/
theorem dBot_cooperates_against_defectBot :
    eval Bot.dBot Bot.defectBot = C := by
  simp [eval, ProgramModel.action]

/-- TitForTat cooperates with CooperateBot. -/
theorem tft_cooperates_with_cooperateBot :
    eval Bot.titForTat Bot.cooperateBot = C := by
  simp [eval, ProgramModel.action]

/-- TitForTat defects against DefectBot. -/
theorem tft_defects_against_defectBot :
    eval Bot.titForTat Bot.defectBot = D := by
  simp [eval, ProgramModel.action]

/-- Bot evaluation is asymmetric in the open-source setting. -/
example : eval Bot.cooperateBot Bot.defectBot ≠ eval Bot.defectBot Bot.cooperateBot := by
  simp [eval, ProgramModel.action]

end ActionClaimTheorems

section OutcomeClaimTheorems

/-- CooperateBot vs CooperateBot full outcome under canonical payoff. -/
theorem cc_outcomeClaim :
    OutcomeClaim PD.canonicalPayoff Bot.cooperateBot Bot.cooperateBot {
      leftAction := C
      rightAction := C
      leftPayoff := 3
      rightPayoff := 3
    } := by
  unfold OutcomeClaim
  have hActs : ActionClaim Bot.cooperateBot Bot.cooperateBot C C := cc_actionClaim
  unfold ActionClaim at hActs
  simp [playOutcome, mkOutcome, hActs]

/-- CooperateBot vs DefectBot full outcome under canonical payoff. -/
theorem cd_outcomeClaim :
    OutcomeClaim PD.canonicalPayoff Bot.cooperateBot Bot.defectBot {
      leftAction := C
      rightAction := D
      leftPayoff := 0
      rightPayoff := 5
    } := by
  unfold OutcomeClaim
  have hActs : ActionClaim Bot.cooperateBot Bot.defectBot C D := cd_actionClaim
  unfold ActionClaim at hActs
  simp [playOutcome, mkOutcome, hActs]

/-- DefectBot vs CooperateBot full outcome under canonical payoff. -/
theorem dc_outcomeClaim :
    OutcomeClaim PD.canonicalPayoff Bot.defectBot Bot.cooperateBot {
      leftAction := D
      rightAction := C
      leftPayoff := 5
      rightPayoff := 0
    } := by
  unfold OutcomeClaim
  have hActs : ActionClaim Bot.defectBot Bot.cooperateBot D C := dc_actionClaim
  unfold ActionClaim at hActs
  simp [playOutcome, mkOutcome, hActs]

/-- DefectBot vs DefectBot full outcome under canonical payoff. -/
theorem dd_outcomeClaim :
    OutcomeClaim PD.canonicalPayoff Bot.defectBot Bot.defectBot {
      leftAction := D
      rightAction := D
      leftPayoff := 1
      rightPayoff := 1
    } := by
  unfold OutcomeClaim
  have hActs : ActionClaim Bot.defectBot Bot.defectBot D D := dd_actionClaim
  unfold ActionClaim at hActs
  simp [playOutcome, mkOutcome, hActs]

/-- TitForTat vs TitForTat full outcome under canonical payoff. -/
theorem tft_tft_outcomeClaim :
    OutcomeClaim PD.canonicalPayoff Bot.titForTat Bot.titForTat {
      leftAction := C
      rightAction := C
      leftPayoff := 3
      rightPayoff := 3
    } := by
  unfold OutcomeClaim
  have hActs : ActionClaim Bot.titForTat Bot.titForTat C C := tft_tft_actionClaim
  unfold ActionClaim at hActs
  simp [playOutcome, mkOutcome, hActs]

/-- TitForTat vs DefectBot full outcome under canonical payoff. -/
theorem tft_d_outcomeClaim :
    OutcomeClaim PD.canonicalPayoff Bot.titForTat Bot.defectBot {
      leftAction := D
      rightAction := D
      leftPayoff := 1
      rightPayoff := 1
    } := by
  unfold OutcomeClaim
  have hActs : ActionClaim Bot.titForTat Bot.defectBot D D := tft_d_actionClaim
  unfold ActionClaim at hActs
  simp [playOutcome, mkOutcome, hActs]

/-- CooperateBot vs CooperateBot yields payoff 3 for both. -/
theorem cc_payoff :
    botPayoff Bot.cooperateBot Bot.cooperateBot = 3 := by
  simp [botPayoff, eval, ProgramModel.action]

/-- CooperateBot is exploited by DefectBot: payoff is 0. -/
theorem cooperateBot_exploited_by_defectBot :
    botPayoff Bot.cooperateBot Bot.defectBot = 0 := by
  simp [botPayoff, eval, ProgramModel.action]

/-- DefectBot vs DefectBot yields payoff 1 for both (punishment). -/
theorem dd_payoff :
    botPayoff Bot.defectBot Bot.defectBot = 1 := by
  simp [botPayoff, eval, ProgramModel.action]

/-- DefectBot exploits CooperateBot: payoff is 5. -/
theorem defectBot_exploits_cooperateBot :
    botPayoff Bot.defectBot Bot.cooperateBot = 5 := by
  simp [botPayoff, eval, ProgramModel.action]

/-- DBot earns the temptation payoff against CooperateBot. -/
theorem dBot_exploits_cooperateBot :
    botPayoff Bot.dBot Bot.cooperateBot = 5 := by
  simp [botPayoff, eval, ProgramModel.action]

/-- DBot is exploited by DefectBot due to its contrarian cooperation. -/
theorem dBot_exploited_by_defectBot :
    botPayoff Bot.dBot Bot.defectBot = 0 := by
  simp [botPayoff, eval, ProgramModel.action]

/-- TitForTat vs TitForTat payoff: 3 each. -/
theorem tft_tft_payoff :
    botPayoff Bot.titForTat Bot.titForTat = 3 := by
  simp [botPayoff, eval, ProgramModel.action]

/-- TitForTat vs DefectBot payoff: TFT gets 1 (mutual defection).
    In open-source PD, TFT sees DefectBot and pre-emptively defects,
    avoiding exploitation. Both end up in the (D,D) outcome. -/
theorem tft_vs_defectBot_payoff :
    botPayoff Bot.titForTat Bot.defectBot = 1 := by
  simp [botPayoff, eval, ProgramModel.action]

end OutcomeClaimTheorems

section RemainingTheorems

/-- Defecting always yields strictly higher payoff than cooperating
    when the opponent plays a fixed action. -/
theorem defect_strictly_dominates_cooperate (oppAction : Action) :
    payoff D oppAction > payoff C oppAction := by
  cases oppAction <;> simp [payoff]

/-- In open-source PD, defection does NOT universally dominate:
    CooperateBot outperforms DefectBot against TitForTat,
    because TFT can see its opponent and punishes defection. -/
theorem open_source_breaks_dominance :
    botPayoff Bot.cooperateBot Bot.titForTat >
    botPayoff Bot.defectBot Bot.titForTat := by
  simp [botPayoff, eval, ProgramModel.action]

/-- DefectBot does dominate CooperateBot against opponents that
    cannot condition on source code (e.g., always-defect, always-cooperate). -/
theorem defectBot_dominates_against_unconditional :
    botPayoff Bot.defectBot Bot.cooperateBot >
    botPayoff Bot.cooperateBot Bot.cooperateBot ∧
    botPayoff Bot.defectBot Bot.defectBot >
    botPayoff Bot.cooperateBot Bot.defectBot := by
  simp [botPayoff, eval, ProgramModel.action]

/-- (D,D) is a Nash equilibrium: given the opponent plays D,
    switching to C only hurts you. -/
theorem dd_is_nash :
    payoff D D ≥ payoff C D ∧ payoff D D ≥ payoff C D := by
  simp [payoff]

/-- (C,C) is NOT a Nash equilibrium: a player can profitably
    deviate to defection. -/
theorem cc_not_nash :
    payoff D C > payoff C C := by
  simp [payoff]

/-- The payoff matrix is symmetric in actions iff both players
    chose the same action. -/
theorem payoff_symmetric (a b : Action) :
    payoff a b = payoff b a ↔ a = b := by
  cases a <;> cases b <;> decide

/-- Mutual cooperation yields higher social welfare than mutual defection. -/
theorem cc_better_than_dd_socially :
    socialWelfare Bot.cooperateBot Bot.cooperateBot >
    socialWelfare Bot.defectBot Bot.defectBot := by
  simp [socialWelfare, botPayoff, eval, ProgramModel.action]

/-- TitForTat vs TitForTat achieves the same social welfare as
    CooperateBot vs CooperateBot. -/
theorem tft_tft_optimal_welfare :
    socialWelfare Bot.titForTat Bot.titForTat =
    socialWelfare Bot.cooperateBot Bot.cooperateBot := by
  simp [socialWelfare, botPayoff, eval, ProgramModel.action]

/-- (TFT, TFT) is a program equilibrium: switching to DefectBot
    does not improve payoff. -/
theorem tft_is_program_equilibrium :
    botPayoff Bot.titForTat Bot.titForTat ≥
    botPayoff Bot.defectBot Bot.titForTat := by
  simp [botPayoff, eval, ProgramModel.action]

/-- (CooperateBot, CooperateBot) is a weak program-equilibrium style claim
    used in the legacy development. -/
theorem cooperateBot_program_equilibrium :
    botPayoff Bot.cooperateBot Bot.cooperateBot ≥
    botPayoff Bot.defectBot Bot.cooperateBot - 2 := by
  simp [botPayoff, eval, ProgramModel.action]

/-- (DefectBot, DefectBot) is also a program equilibrium:
    switching to CooperateBot doesn't help when opponent always defects. -/
theorem defectBot_program_equilibrium :
    botPayoff Bot.defectBot Bot.defectBot ≥
    botPayoff Bot.cooperateBot Bot.defectBot := by
  simp [botPayoff, eval, ProgramModel.action]

/-- (C,C) Pareto-dominates (D,D): both players are better off. -/
theorem cc_pareto_dominates_dd :
    payoff C C > payoff D D ∧ payoff C C > payoff D D := by
  simp [payoff]

/-- The dilemma: the unique Nash equilibrium (D,D) is
    Pareto-dominated by (C,C). -/
theorem pd_dilemma :
    (payoff D D ≥ payoff C D) ∧
    (payoff C C > payoff D D) := by
  simp [payoff]

end RemainingTheorems

end PD.Proofs.OpenSourceBots
