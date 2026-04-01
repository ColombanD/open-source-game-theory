# PrisonersDilemma

Lean 4 formalization of open-source Prisoner's Dilemma models and proofs.

In open-source game theory, each player can inspect the opponent's source code
before choosing an action. This project provides a modular architecture to:

1. define reusable game semantics,
2. encode program families (bots),
3. prove action/outcome claims and game-theoretic properties.

## What Changed In This Refactor

The project was reorganized around a clean module pipeline and a new **action-first proof workflow**:

### Module reorganization
- `Basic.lean` was removed.
- core semantics are centralized in `Core.lean`.
- strategy definitions live in `Models/`.
- theorem developments live in `Proofs/`.
- non-code reading and dataset files were moved under `PrisonersDilemma/Research/`.

This removes duplicated definitions and keeps code, proofs, and references separated.

### Proof workflow reorganization
All theorem files now follow a **three-section structure**:

1. **ActionClaim theorems** — prove what actions each program chose.
2. **OutcomeClaim theorems** — (optional) prove full outcomes with payoffs, built on ActionClaim.
3. **Remaining theorems** — game-theoretic analysis (dominance, equilibrium, welfare).

This pattern prioritizes action-level reasoning and makes payoff/outcome proofs optional.

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

**Stage 1: Prove the action profile**
```lean
theorem cc_actionClaim :
    ActionClaim Bot.cooperateBot Bot.cooperateBot C C := by
  unfold ActionClaim playActions
  simp [ProgramModel.action]  -- Unfold bot semantics and verify actions match
```

**Stage 2a (optional): Derive full outcome**
```lean
theorem cc_outcomeClaim :
    OutcomeClaim PD.canonicalPayoff Bot.cooperateBot Bot.cooperateBot {
      leftAction := C, rightAction := C, leftPayoff := 3, rightPayoff := 3
    } := by
  have hActs : ActionClaim Bot.cooperateBot Bot.cooperateBot C C := cc_actionClaim
  -- Now unfold outcome computation using the known actions
  simp [playOutcome, mkOutcome, hActs]
```

**Stage 2b (optional): Extract individual action facts**
```lean
theorem cooperateBot_always_cooperates (opp : Bot) :
    eval Bot.cooperateBot opp = C := by
  simp [eval, ProgramModel.action]
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

## Theorem Coverage (OpenSourceBots)

Theorems in `Proofs/OpenSourceBots.lean` are organized into three sections:

### ActionClaim theorems
Proofs of what actions each program chooses in key matchups:
- behavior:
	- always-cooperate / always-defect lemmas,
	- matchup action lemmas.

### OutcomeClaim theorems
Full outcome records and payoff facts built from ActionClaim proofs:
- matchup outcome and payoff lemmas.

### Remaining theorems
Game-theoretic analysis and strategic properties:
- dominance:
	- fixed-action dominance,
	- open-source dominance break results.
- equilibrium-style statements:
	- Nash-style checks,
	- program-equilibrium style inequalities.
- welfare and dilemma statements:
	- social welfare comparisons,
	- Pareto-vs-equilibrium tension (`pd_dilemma`).

---

## How To Extend

Recommended process for a new paper/program family:

1. Create `PrisonersDilemma/Models/<Family>.lean`.
2. Define program syntax and implement `ProgramModel`.
3. Create `PrisonersDilemma/Proofs/<Family>.lean`.
4. **Organize into three sections:**
   - **Stage A (default):** prove `ActionClaim` theorems for key matchups.
   - **Stage B (optional):** prove `OutcomeClaim` theorems if you need payoffs.
   - **Stage C (optional):** add remaining game-theoretic theorems.
5. Add the new model/proof imports to `PrisonersDilemma.lean`.

## Build

From `code/`:

```bash
lake build
```

Toolchain: Lean `v4.28.0` (see `lean-toolchain`).
