# PrisonersDilemma

Lean 4 formalization of Prisoner's Dilemma models and proofs.

This project provides a modular architecture to:

1. Define reusable game semantics,
2. Encode program families (bots),
3. Prove action/outcome claims and game-theoretic properties.

## Overview

The codebase is organized around a pipeline-native semantics layer:

- Core game objects and payoff logic in `Core.lean`,
- Strategy expression language and evaluators in `StrategyDSL.lean`,
- Program interaction semantics in `Pipeline.lean`,
- Concrete bot definitions in `Models/`,
- Theorem developments in `Proofs/`.

The default proving strategy is action-first:

1. Prove the action profile (`ActionClaim`),
2. Add outcome/payoff theorems (`OutcomeClaim`) only when needed.

## Folder Map

### Library entrypoint

- `PrisonersDilemma.lean`
	- Root import hub for all build targets in this package.

### Core semantics

- `PrisonersDilemma/Core.lean`
	- Defines `Action`, `PayoffMatrix`, `Outcome`, `mkOutcome`.
	- Defines canonical one-shot PD payoff matrix:
		- `CC = 3`, `CD = 0`, `DC = 5`, `DD = 1`.

- `PrisonersDilemma/Pipeline.lean`
	- Defines `ProgramModel` abstraction.
	- Defines reusable simulation combinators:
		- `playActions`
		- `playOutcome`
		- `ActionClaim`
		- `OutcomeClaim`

### Models

- `PrisonersDilemma/Models/CooperateBot.lean`
	- Strategy/source/action definitions for an always-cooperate bot.

- `PrisonersDilemma/Models/DefectBot.lean`
	- Strategy/source/action definitions for an always-defect bot.

- `PrisonersDilemma/Models/DBot.lean`
	- Strategy/source/action definitions for a conditional bot that defects against cooperate-tagged source and cooperates otherwise.

- `PrisonersDilemma/Models/BotUniverse.lean`
	- Shared `Bot` type (`cooperateBot`, `defectBot`, `dBot`).
	- `ProgramModel` instance via:
		- `botSource`
		- `botEvalSource`
		- `botEval`

### Proofs

- `PrisonersDilemma/Proofs/CooperateBot.lean`
	- Proves `CooperateBot.action` is always `C`.

- `PrisonersDilemma/Proofs/DefectBot.lean`
	- Proves `DefectBot.action` is always `D`.

- `PrisonersDilemma/Proofs/DBot.lean`
	- Proves pipeline-level `ActionClaim` results for key matchups in the shared bot universe.

### Research material (non-code)

- `PrisonersDilemma/Research/Notes/`
	- Markdown notes and summaries.
- `PrisonersDilemma/Research/Readings/`
	- Papers and extracted text files.
- `PrisonersDilemma/Research/Data/`
	- Raw tournament/program data artifacts.
	- Includes `prisoners_dilemma_tournament_results.scm`.

These files are intentionally separated from Lean modules to reduce clutter in
the main code path.

## Core Concepts

### ActionClaim: The Heart of the Project

**ActionClaim** is the foundational concept: it captures the semantic fact "when program X plays program Y, what actions do they choose?"

```lean
def ActionClaim (left right : Prog) (leftAction rightAction : Action) : Prop :=
  playActions left right = (leftAction, rightAction)
```

**Why ActionClaim is central:**
- It is the minimal semantic unit: what each program does in a matchup.
- It is independent of payoffs: action behavior can be proved without matrix details.
- It is reusable: payoff and higher-level theorems build on these action facts.

### ActionClaim Proof Flow

Example with the shared bot universe:

```lean
theorem dbot_vs_cooperate_actionClaim :
    ActionClaim Bot.dBot Bot.cooperateBot D C := by
  unfold ActionClaim playActions
  change (botEvalSource Bot.dBot (botSource Bot.cooperateBot),
    botEvalSource Bot.cooperateBot (botSource Bot.dBot)) = (D, C)
  simp [botEvalSource, botSource, action, strategy, actionFor, evalActionExpr,
    PD.Models.CooperateBot.action, PD.Models.CooperateBot.strategy]
```

**Key insight:** ActionClaim is your **stopping point** if you only care about what programs do. Payoffs and outcomes are optional layers on top.

| Name | Meaning |
|---|---|
| `Action` | `C` (cooperate) or `D` (defect) |
| `ActionClaim` | proposition that a matchup yields a specific action pair |
| `playActions` | computes both players' chosen actions |
| `canonicalPayoff` | one-shot PD matrix `CC=3, CD=0, DC=5, DD=1` |
| `OutcomeClaim` | proposition that a matchup yields a specific outcome record (actions + payoffs) |
| `playOutcome` | lifts action profile into payoff outcome record |
| `ProgramModel` | how a program chooses an action given opponent source |

## How To Extend

Recommended process for a new paper/program family:

1. Create `PrisonersDilemma/Models/<Family>.lean`.
2. Define program syntax and implement `ProgramModel`.
3. Create `PrisonersDilemma/Proofs/<Family>.lean`.
4. Prove key `ActionClaim` theorems first.
5. Add optional `OutcomeClaim`/payoff theorems only if needed.
6. Add the new model/proof imports to `PrisonersDilemma.lean`.

## Build

From `engine/`:

```bash
lake build
```

Toolchain: Lean `v4.28.0` (see `lean-toolchain`).
