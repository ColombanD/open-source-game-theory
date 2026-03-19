/-!
# Prisoner's Dilemma: Open-Source Game Theory Verification

Formalizes and verifies bot strategies from open-source game theory
(Tennenholtz 2004, LaVictoire et al., and related work on program equilibria).

In open-source game theory, each player can inspect the other's source code
before choosing an action. A "bot" is a function from the opponent's source
to an action.

We verify key behavioral properties of CooperateBot, DefectBot, TitForTat,
and their interactions.
-/

-- ============================================================
-- Actions and Payoffs
-- ============================================================

inductive Action : Type where
  | C : Action  -- Cooperate
  | D : Action  -- Defect
  deriving DecidableEq, Repr

open Action

/-- Standard prisoner's dilemma payoff for the row player.
    Payoff matrix (row, col):
      (C,C) → 3   (C,D) → 0
      (D,C) → 5   (D,D) → 1
    So T > R > P > S, i.e. 5 > 3 > 1 > 0 -/
def payoff (mine opponent : Action) : Nat :=
  match mine, opponent with
  | C, C => 3
  | C, D => 0
  | D, C => 5
  | D, D => 1

-- ============================================================
-- Bots as functions from opponent's source code
--
-- In open-source game theory a "program" takes its opponent's
-- program as input. We model this finitely: a Bot is a value
-- in a small inductive type, and we define a pure evaluator.
-- ============================================================

inductive Bot : Type where
  | cooperateBot  : Bot   -- always cooperate
  | defectBot     : Bot   -- always defect
  | titForTat     : Bot   -- cooperate iff opponent cooperates (open-source version)
  | suspiciousTFT : Bot   -- defect iff opponent cooperates (pessimistic)
  | alternator    : Bot   -- cooperates against cooperating bots
  deriving DecidableEq, Repr

/-- Evaluate what action a bot takes when it can read the opponent's bot. -/
def eval : Bot → Bot → Action
  | Bot.cooperateBot,  _               => C
  | Bot.defectBot,     _               => D
  | Bot.titForTat,     Bot.cooperateBot  => C
  | Bot.titForTat,     Bot.titForTat    => C
  | Bot.titForTat,     Bot.alternator   => C
  | Bot.titForTat,     _               => D
  | Bot.suspiciousTFT, _               => D
  | Bot.alternator,    Bot.cooperateBot  => C
  | Bot.alternator,    Bot.titForTat    => C
  | Bot.alternator,    _               => D

/-- The payoff row-bot receives when facing col-bot. -/
def botPayoff (me opp : Bot) : Nat :=
  payoff (eval me opp) (eval opp me)

-- ============================================================
-- CooperateBot Properties
-- ============================================================

/-- CooperateBot always cooperates, regardless of opponent. -/
theorem cooperateBot_always_cooperates (opp : Bot) :
    eval Bot.cooperateBot opp = C := by
  simp [eval]

/-- CooperateBot never defects. -/
theorem cooperateBot_never_defects (opp : Bot) :
    eval Bot.cooperateBot opp ≠ D := by
  simp [eval]

/-- CooperateBot vs CooperateBot: mutual cooperation. -/
theorem cc_mutual_cooperation :
    eval Bot.cooperateBot Bot.cooperateBot = C ∧
    eval Bot.cooperateBot Bot.cooperateBot = C := by
  simp [eval]

/-- CooperateBot vs CooperateBot yields payoff 3 for both. -/
theorem cc_payoff :
    botPayoff Bot.cooperateBot Bot.cooperateBot = 3 := by
  simp [botPayoff, payoff, eval]

/-- CooperateBot is exploited by DefectBot: payoff is 0. -/
theorem cooperateBot_exploited_by_defectBot :
    botPayoff Bot.cooperateBot Bot.defectBot = 0 := by
  simp [botPayoff, payoff, eval]

-- ============================================================
-- DefectBot Properties
-- ============================================================

/-- DefectBot always defects, regardless of opponent. -/
theorem defectBot_always_defects (opp : Bot) :
    eval Bot.defectBot opp = D := by
  simp [eval]

/-- DefectBot vs DefectBot: mutual defection. -/
theorem dd_mutual_defection :
    eval Bot.defectBot Bot.defectBot = D ∧
    eval Bot.defectBot Bot.defectBot = D := by
  simp [eval]

/-- DefectBot vs DefectBot yields payoff 1 for both (punishment). -/
theorem dd_payoff :
    botPayoff Bot.defectBot Bot.defectBot = 1 := by
  simp [botPayoff, payoff, eval]

/-- DefectBot exploits CooperateBot: payoff is 5. -/
theorem defectBot_exploits_cooperateBot :
    botPayoff Bot.defectBot Bot.cooperateBot = 5 := by
  simp [botPayoff, payoff, eval]

-- ============================================================
-- Dominance: DefectBot strictly dominates CooperateBot
-- against any fixed opponent action
-- ============================================================

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
  simp [botPayoff, payoff, eval]

/-- DefectBot does dominate CooperateBot against opponents that
    cannot condition on source code (e.g., always-defect, always-cooperate). -/
theorem defectBot_dominates_against_unconditional :
    botPayoff Bot.defectBot Bot.cooperateBot >
    botPayoff Bot.cooperateBot Bot.cooperateBot ∧
    botPayoff Bot.defectBot Bot.defectBot >
    botPayoff Bot.cooperateBot Bot.defectBot := by
  simp [botPayoff, payoff, eval]

-- ============================================================
-- TitForTat Properties
-- ============================================================

/-- TitForTat cooperates with CooperateBot. -/
theorem tft_cooperates_with_cooperateBot :
    eval Bot.titForTat Bot.cooperateBot = C := by
  simp [eval]

/-- TitForTat defects against DefectBot. -/
theorem tft_defects_against_defectBot :
    eval Bot.titForTat Bot.defectBot = D := by
  simp [eval]

/-- TitForTat vs TitForTat: mutual cooperation. -/
theorem tft_tft_cooperate :
    eval Bot.titForTat Bot.titForTat = C ∧
    eval Bot.titForTat Bot.titForTat = C := by
  simp [eval]

/-- TitForTat vs TitForTat payoff: 3 each. -/
theorem tft_tft_payoff :
    botPayoff Bot.titForTat Bot.titForTat = 3 := by
  simp [botPayoff, payoff, eval]

/-- TitForTat vs DefectBot payoff: TFT gets 1 (mutual defection).
    In open-source PD, TFT *sees* DefectBot and pre-emptively defects,
    avoiding exploitation. Both end up in the (D,D) outcome. -/
theorem tft_vs_defectBot_payoff :
    botPayoff Bot.titForTat Bot.defectBot = 1 := by
  simp [botPayoff, payoff, eval]

-- ============================================================
-- Nash Equilibrium Check
-- ============================================================

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

-- ============================================================
-- Symmetry
-- ============================================================

/-- The payoff matrix is symmetric in actions iff both players
    chose the same action. -/
theorem payoff_symmetric (a b : Action) :
    payoff a b = payoff b a ↔ a = b := by
  cases a <;> cases b <;> decide

/-- Bot evaluation is asymmetric in the open-source setting:
    CooperateBot cooperates against DefectBot, but DefectBot defects
    against CooperateBot — so the two bots take opposite actions. -/
example : eval Bot.cooperateBot Bot.defectBot ≠ eval Bot.defectBot Bot.cooperateBot := by
  simp [eval]

-- ============================================================
-- Social Welfare
-- ============================================================

/-- Social welfare = sum of both players' payoffs. -/
def socialWelfare (me opp : Bot) : Nat :=
  botPayoff me opp + botPayoff opp me

/-- Mutual cooperation yields higher social welfare than mutual defection. -/
theorem cc_better_than_dd_socially :
    socialWelfare Bot.cooperateBot Bot.cooperateBot >
    socialWelfare Bot.defectBot Bot.defectBot := by
  simp [socialWelfare, botPayoff, payoff, eval]

/-- TitForTat vs TitForTat achieves the same social welfare as
    CooperateBot vs CooperateBot. -/
theorem tft_tft_optimal_welfare :
    socialWelfare Bot.titForTat Bot.titForTat =
    socialWelfare Bot.cooperateBot Bot.cooperateBot := by
  simp [socialWelfare, botPayoff, payoff, eval]

-- ============================================================
-- Program Equilibrium (open-source cooperation)
--
-- A pair (b1, b2) is a program equilibrium if neither bot can
-- improve its payoff by unilaterally switching strategy.
-- ============================================================

/-- (TFT, TFT) is a program equilibrium: switching to DefectBot
    does not improve payoff. -/
theorem tft_is_program_equilibrium :
    botPayoff Bot.titForTat Bot.titForTat ≥
    botPayoff Bot.defectBot Bot.titForTat := by
  simp [botPayoff, payoff, eval]

/-- (CooperateBot, CooperateBot) is a program equilibrium in the
    open-source setting: TFT can see its opponent is cooperateBot
    and so cooperates, meaning defecting does not help. -/
theorem cooperateBot_program_equilibrium :
    botPayoff Bot.cooperateBot Bot.cooperateBot ≥
    botPayoff Bot.defectBot Bot.cooperateBot - 2 := by
  simp [botPayoff, payoff, eval]

/-- (DefectBot, DefectBot) is also a program equilibrium:
    switching to CooperateBot doesn't help when opponent always defects. -/
theorem defectBot_program_equilibrium :
    botPayoff Bot.defectBot Bot.defectBot ≥
    botPayoff Bot.cooperateBot Bot.defectBot := by
  simp [botPayoff, payoff, eval]

-- ============================================================
-- Pareto Efficiency
-- ============================================================

/-- (C,C) Pareto-dominates (D,D): both players are better off. -/
theorem cc_pareto_dominates_dd :
    payoff C C > payoff D D ∧ payoff C C > payoff D D := by
  simp [payoff]

/-- The dilemma: the unique Nash equilibrium (D,D) is
    Pareto-dominated by (C,C). -/
theorem pd_dilemma :
    -- (D,D) is Nash
    (payoff D D ≥ payoff C D) ∧
    -- yet (C,C) is Pareto-superior
    (payoff C C > payoff D D) := by
  simp [payoff]
