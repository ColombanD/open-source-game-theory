# PrisonersDilemma

Lean 4 verification of bot strategies in open-source game theory, based on the prisoner's dilemma framework from [Cooperative and uncooperative institution designs (arXiv:2208.07006)](https://arxiv.org/abs/2208.07006).

## New Project Backbone (recommended workflow)

The codebase now includes a modular backbone for scaling to many papers/programs:

- `PrisonersDilemma/Core.lean`: core `Action`, `PayoffMatrix`, `Outcome`
- `PrisonersDilemma/Pipeline.lean`: reusable `ProgramModel`, `playActions`, `playOutcome`, and claim predicates
- `PrisonersDilemma/Models/`: one file per paper/family defining program syntax + semantics
- `PrisonersDilemma/Proofs/`: one file per matchup theorem set
- `PrisonersDilemma/Proofs/WorkflowTemplate.lean`: template for writing manual proofs in two stages

### Recommended per-match process

1. Add or update semantics in a model file under `PrisonersDilemma/Models/`.
2. In a proof file under `PrisonersDilemma/Proofs/`, prove an `ActionClaim` for the pair.
3. Prove the corresponding `OutcomeClaim` using the payoff matrix.
4. Keep each theorem small and named by matchup (for example `cupod_vs_dupoc_actions`).

### Current starter model

`PrisonersDilemma/Models/Simple.lean` includes a minimal reference model (`cooperate`, `defect`) and sample theorems proving action profiles and canonical payoffs (`CC=2, CD=0, DC=3, DD=1`).

In open-source game theory each player can inspect the opponent's source code before choosing an action. This changes the strategic landscape: defection no longer unconditionally dominates.

## Core definitions

| Name | Description |
|---|---|
| `Action` | `C` (cooperate) or `D` (defect) |
| `payoff` | Standard PD matrix: T=5, R=3, P=1, S=0 |
| `Bot` | `cooperateBot`, `defectBot`, `titForTat`, `suspiciousTFT`, `alternator` |
| `eval b1 b2` | Action `b1` takes after reading `b2`'s source code |
| `botPayoff` | Payoff a bot receives against another bot |
| `socialWelfare` | Sum of both players' payoffs |

## Verified properties

| Theorem | Statement |
|---|---|
| `cooperateBot_always_cooperates` | CooperateBot always plays C, regardless of opponent |
| `defectBot_always_defects` | DefectBot always plays D, regardless of opponent |
| `cc_payoff` | CooperateBot vs CooperateBot → payoff 3 each |
| `dd_payoff` | DefectBot vs DefectBot → payoff 1 each |
| `cooperateBot_exploited_by_defectBot` | CooperateBot gets 0 against DefectBot |
| `defectBot_exploits_cooperateBot` | DefectBot gets 5 against CooperateBot |
| `defect_strictly_dominates_cooperate` | Defecting beats cooperating against any **fixed** opponent action |
| `open_source_breaks_dominance` | In open-source PD, CooperateBot outperforms DefectBot against TFT (3 > 1) — the central insight |
| `tft_vs_defectBot_payoff` | TFT **sees** DefectBot and pre-emptively defects → mutual D → payoff 1 (not exploited) |
| `tft_tft_payoff` | TFT vs TFT → mutual cooperation, payoff 3 each |
| `dd_is_nash` | (D,D) is a Nash equilibrium: switching to C against a defector only hurts you |
| `cc_not_nash` | (C,C) is not a Nash equilibrium: unilateral defection is profitable |
| `tft_is_program_equilibrium` | (TFT, TFT) is a program equilibrium: neither bot benefits by switching to DefectBot |
| `defectBot_program_equilibrium` | (DefectBot, DefectBot) is also a program equilibrium |
| `cc_better_than_dd_socially` | Social welfare at (C,C) > (D,D) |
| `tft_tft_optimal_welfare` | TFT vs TFT achieves the same social welfare as CooperateBot vs CooperateBot |
| `pd_dilemma` | The unique Nash equilibrium (D,D) is Pareto-dominated by (C,C) |

## Building

```
lake build
```

Requires Lean 4 with Lake (tested on Lean 4.28.0).
