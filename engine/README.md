# PrisonersDilemma

Lean 4 formalization of Prisoner's Dilemma using fuel-bounded program evaluation.

This project provides a modular architecture to:

1. Define executable game programs using inductive syntax,
2. Evaluate programs under fuel constraints (to ensure termination),
3. Encode bot strategies with simulation, branching, and oracle reasoning,
4. Prove action and outcome claims via mechanized verification.

## Overview

The codebase is organized around a **fuel-bounded evaluator** for game programs:

- Program syntax and substitution in `PrisonersDilemma/Program.lean`,
- Fuelled evaluation semantics in `PrisonersDilemma/Dynamics.lean`,
- Bot strategy definitions in `PrisonersDilemma/Bots/`,
- Theorem developments and helpers in `PrisonersDilemma/Theorems/`.

The proving strategy focuses on outcome proofs:

1. Define bot strategies as `Prog` terms,
2. Establish guard evaluations and simulations,
3. Prove `play` (single action) and `outcome` (action pair) claims.

## Folder Map

### Library entrypoint

- `PrisonersDilemma.lean`
	- Root import hub for all build targets in the new package.

### Core semantics

- `PrisonersDilemma/Program.lean`
	- Defines `Action` (C or D), `Outcome` (action pair), and `Prog` inductive type.
	- `Prog` variants: `.const`, `.self`, `.opp`, `.sim`, `.ite`, `.search`.
	- Defines `Formula` for oracle-decidable propositions about programs.
	- Implements `Prog.subst` and `Formula.subst` for variable capture.

- `PrisonersDilemma/Dynamics.lean`
	- Defines fuel-bounded evaluator `eval : Nat → Prog → Prog → Prog → Option Action`.
	- Axiomatizes `proofSearch : Nat → Formula → Bool` (oracle).
	- Defines `play : Nat → Prog → Prog → Option Action` (single agent's move).
	- Defines `outcome : Nat → Prog → Prog → Option Outcome` (both agents' moves).
	- Defines `Formula.interp` (semantic interpretation of formulas).

### Bots

- `PrisonersDilemma/Bots/CooperateBot.lean`
	- Always-cooperate strategy as `.const Action.C`.

- `PrisonersDilemma/Bots/DefectBot.lean`
	- Always-defect strategy as `.const Action.D`.

- `PrisonersDilemma/Bots/DBot.lean`
	- Defector bot: probes opponent against CooperateBot, responds to probe result.

- `PrisonersDilemma/Bots/TitForTatBot.lean`
	- Tit-for-tat bot: probes opponent against CooperateBot, cooperates if probe yields C.

- `PrisonersDilemma/Bots/OBot.lean`
	- Opportunistic bot: nested probes (CooperateBot, then DefectBot based on first result).

- `PrisonersDilemma/Bots/CupodBot.lean`
	- Cupod (Cooperative Until Provably Opportunistic Defector) strategy with fuel parameter.

- `PrisonersDilemma/Bots/DupocBot.lean`
	- Dupoc (Defector Unless Provably Opportunistic Cooperator) strategy.

### Theorems

- `PrisonersDilemma/Theorems/Helpers.lean`
	- Reusable proof helpers:
		- `play_from_eval`: Lifting eval results to play claims.
		- `play_ite_from_guard(fuel n)`: Generic helper for if-then-else programs with parametric fuel offset.

- `PrisonersDilemma/Theorems/CooperateBot.lean`
	- Proves action claims for CooperateBot (always plays C).

- `PrisonersDilemma/Theorems/DefectBot.lean`
	- Proves action claims for DefectBot (always plays D).

- `PrisonersDilemma/Theorems/DBot.lean`
	- Proves outcome claims for DBot vs key opponents.

- `PrisonersDilemma/Theorems/TitForTatBot.lean`
	- Proves outcome claims for TitForTatBot vs key opponents.

- `PrisonersDilemma/Theorems/OBot.lean`
	- Proves outcome claims for OBot (handles nested simulation structure).

- `PrisonersDilemma/Theorems/CupodBot.lean`
	- Proves outcome claims for CupodBot with parametrized fuel.

- `PrisonersDilemma/Theorems/Axioms.lean`
	- Axioms and additional assumptions used across theorem development.

## Core Concepts

### Program Semantics: The Foundation

**Programs** are defined inductively in `Prog`:
- `.const a`: Always play action `a`.
- `.self`: Evaluate the current program (self-reference).
- `.opp`: Evaluate the opponent program.
- `.sim p q`: Simulate program `p` against `q`, then evaluate the result.
- `.ite b a p q`: If guard `b` evaluates to action `a`, run `p`, else run `q`.
- `.search k φ p q`: If oracle proves formula `φ`, run `p`, else run `q`.

### Evaluation: Fuel-Bounded Execution

The evaluator `eval : Nat → Prog → Prog → Prog → Option Action` takes:
- `fuel`: A natural number limiting recursion depth (ensures termination).
- `me` and `opponent`: The two programs in the matchup.
- `body`: The program to evaluate (usually `me` itself via `play`).

Returns `Option Action`: `some a` if evaluation succeeds, `none` if fuel exhausted.

**Key insight:** Fuel parametrization allows reasoning about "how deep" a proof can dig. Higher fuel enables more complex nested simulations.

### Action and Outcome Claims

| Term | Meaning |
|---|---|
| `play fuel me opp` | Single program `me`'s action when facing `opp` with given `fuel`. |
| `outcome fuel p q` | Pair `(play fuel p q, play fuel q p)` of both programs' actions. |
| Theorem proving `play`/`outcome` | Establishes what programs provably do at specific fuel levels. |

### Substitution and Capture Avoidance

`Prog.subst` replaces `.self` and `.opp` references:
- In bot definitions, we write `.opp` abstractly.
- During evaluation, `.opp` is substituted with the actual opponent program.
- This avoids explicit lambda abstractions while enabling higher-order reasoning.

### Nested Simulation and Proof Structuring

Complex bots (e.g., OBot) involve nested `.ite` and `.sim` constructs:
- **Guard evaluation**: Prove `eval (fuel + n) me opp guard_expr = some guardAct`.
- **Branch instantiation**: Use `play_ite_from_guard` helper to connect guard result to branch outcome.
- **Nested structures**: For nested ites, apply the helper recursively at different fuel levels.

## How To Extend

Recommended process for adding a new bot strategy:

1. **Define the bot** in `PrisonersDilemma/Bots/<BotName>.lean`.
   - Create a `def <botName> : Prog` using the inductive syntax.
   - Document the strategy in comments.

2. **Create theorems** in `PrisonersDilemma/Theorems/<BotName>.lean`.
   - Import the bot definition and helper theorems.
   - Prove `play` (single action) claims at specific fuel levels.
   - Prove `outcome` (pair action) claims by combining two `play` results.

3. **Reuse helpers** from `PrisonersDilemma/Theorems/Helpers.lean`.
   - `play_from_eval`: Lift `eval` results to `play` goals.
   - `play_ite_from_guard(fuel n)`: Handle if-then-else structure with fuel offset `n`.

4. **Manage fuel tracking** carefully.
   - Each simulation step consumes 1 fuel.
   - Document fuel requirements as comments in proofs.
   - Use parametric helpers to avoid repeating similar proofs at different fuel levels.

## Build

From `engine/`:

```bash
# Build the entire package
lake build

# Build only PrisonersDilemma
lake build PrisonersDilemma

# Build a specific theorem module
lake build PrisonersDilemma.Theorems.OBot
```

**Toolchain:** Lean `v4.28.0` (see `lean-toolchain`).

**Note:** The deprecated `PrisonersDilemma` folder is kept for historical reference but is not actively maintained. Use `PrisonersDilemma` for all new work.
