# PrisonersDilemma

Lean 4 formalization of Prisoner's Dilemma models and proofs.

This project provides a modular architecture to:

1. define reusable game semantics,
2. encode program families (bots),
3. prove action/outcome claims and game-theoretic properties.

## What Changed In This Refactor

The project was reorganized around a clean module pipeline and a stronger action-first theorem style:

### Module reorganization
- `Basic.lean` was removed.
- core semantics are centralized in `Core.lean`.
- strategy definitions live in `Models/`.
- theorem developments live in `Proofs/`.
- non-code reading and dataset files were moved under `PrisonersDilemma/Research/`.

This removes duplicated definitions and keeps code, proofs, and references separated.

### Proof style reorganization
The refactor prioritizes proving action behavior first, with optional payoff/outcome layers on top.

## Folder Map

### Library entrypoint

- `PrisonersDilemma.lean`
	- root import hub for all build targets in this package.

### Core semantics

- `PrisonersDilemma/Core.lean`
	- defines `Action`, `PayoffMatrix`, `Outcome`, `mkOutcome`.
	- defines canonical one-shot PD payoff matrix:
		- `CC = 3`, `CD = 0`, `DC = 5`, `DD = 1`.

- `PrisonersDilemma/Pipeline.lean`
	- defines `ProgramModel` abstraction.
	- defines reusable simulation combinators:
		- `playActions`
		- `playOutcome`
		- `ActionClaim`
		- `OutcomeClaim`

### Models

- `PrisonersDilemma/Models/CooperateBot.lean`
	- strategy/source/action definitions for an always-cooperate bot.

- `PrisonersDilemma/Models/DefectBot.lean`
	- strategy/source/action definitions for an always-defect bot.

- `PrisonersDilemma/Models/DBot.lean`
	- strategy/source/action definitions for a conditional bot that defects against cooperate-tagged source and cooperates otherwise.

- `PrisonersDilemma/Models/BotUniverse.lean`
	- shared `Bot` type (`cooperateBot`, `defectBot`, `dBot`).
	- `ProgramModel` instance via:
		- `botSource`
		- `botEvalSource`
		- `botEval`

### Proofs

- `PrisonersDilemma/Proofs/CooperateBot.lean`
	- proves `CooperateBot.action` is always `C`.

- `PrisonersDilemma/Proofs/DefectBot.lean`
	- proves `DefectBot.action` is always `D`.

- `PrisonersDilemma/Proofs/DBot.lean`
	- proves pipeline-level `ActionClaim` results for key matchups in the shared bot universe.

### Research material (non-code)

- `PrisonersDilemma/Research/Notes/`
	- markdown notes and summaries.
- `PrisonersDilemma/Research/Readings/`
	- papers and extracted text files.
- `PrisonersDilemma/Research/Data/`
	- raw tournament/program data artifacts.
	- includes `prisoners_dilemma_tournament_results.scm`.

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
- It is the **minimal semantic unit** — just "what did each program do?"
- It is **independent of payoffs** — you can prove and reason about actions without touching the payoff matrix.
- It is **reusable** — subsequent proofs (payoffs, outcomes, equilibria) all build on ActionClaim facts.

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

## Core Concepts (Extended Reference)

For backward compatibility, this table covers all semantic layers:

---

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
