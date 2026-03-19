# PrisonersDilemma

Lean 4 formalization of open-source Prisoner's Dilemma models and proofs.

In open-source game theory, each player can inspect the opponent's source code
before choosing an action. This project provides a modular architecture to:

1. define reusable game semantics,
2. encode program families (bots),
3. prove action/outcome claims and game-theoretic properties.

## What Changed In This Refactor

The project was reorganized around a clean module pipeline:

- `Basic.lean` was removed.
- core semantics are centralized in `Core.lean`.
- strategy definitions live in `Models/`.
- theorem developments live in `Proofs/`.
- non-code reading and dataset files were moved under `PrisonersDilemma/Research/`.

This removes duplicated definitions and keeps code, proofs, and references
separated.

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

- `PrisonersDilemma/Models/Simple.lean`
	- minimal two-strategy toy model (`cooperate`, `defect`).
	- small sanity-check theorems over action profiles and canonical outcomes.

- `PrisonersDilemma/Models/OpenSourceBots.lean`
	- main bot family used in this repository:
		- `cooperateBot`, `defectBot`, `titForTat`, `suspiciousTFT`, `alternator`.
	- provides `ProgramModel` semantics for these bots.
	- provides convenience definitions:
		- `eval`
		- `botPayoff`
		- `socialWelfare`

### Proofs

- `PrisonersDilemma/Proofs/WorkflowTemplate.lean`
	- generic template showing the intended 2-stage proof pattern:
		1. prove action profile,
		2. derive outcome/payoff claim.

- `PrisonersDilemma/Proofs/OpenSourceBots.lean`
	- theorem set for the `OpenSourceBots` model.
	- includes behavior, dominance, equilibrium, and welfare results.

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

| Name | Meaning |
|---|---|
| `Action` | `C` (cooperate) or `D` (defect) |
| `canonicalPayoff` | one-shot PD matrix `CC=3, CD=0, DC=5, DD=1` |
| `ProgramModel` | how a program chooses an action given opponent source |
| `playActions` | computes both players' chosen actions |
| `playOutcome` | lifts action profile into payoff outcome record |
| `ActionClaim` | proposition that a matchup yields a specific action pair |
| `OutcomeClaim` | proposition that a matchup yields a specific outcome record |

## Theorem Coverage (OpenSourceBots)

Main theorem families in `Proofs/OpenSourceBots.lean`:

- behavior:
	- always-cooperate / always-defect lemmas,
	- matchup action and payoff lemmas.
- strategic relations:
	- fixed-action dominance,
	- open-source dominance break results.
- equilibrium-style statements:
	- Nash-style checks,
	- program-equilibrium style inequalities.
- welfare and dilemma statements:
	- social welfare comparisons,
	- Pareto-vs-equilibrium tension (`pd_dilemma`).

## How To Extend

Recommended process for a new paper/program family:

1. Create `PrisonersDilemma/Models/<Family>.lean`.
2. Define program syntax and implement `ProgramModel`.
3. Create `PrisonersDilemma/Proofs/<Family>.lean`.
4. First prove action claims (`ActionClaim`).
5. Then prove outcome/payoff claims (`OutcomeClaim`).
6. Add the new model/proof imports to `PrisonersDilemma.lean`.

## Build

From `code/`:

```bash
lake build
```

Toolchain: Lean `v4.28.0` (see `lean-toolchain`).
