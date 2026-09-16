# ArithS — Open-Source Game Theory in Peano Arithmetic with a length-bounded provability predicate

This package is the arithmetized side of the OSGT mechanization. The engine (`../engine`)
formalizes Critch's bounded proof-searching agents against a rule-based proof system `S` and
proves a 155-cell outcome matrix. This package builds the system Critch actually describes —
**PA with a provability predicate bounded by proof length in characters** — on the
[Foundation](https://github.com/FormalizedFormalLogic/Foundation) library, and proves his
central results in it. Everything rests on Lean's three standard axioms; there is no `axiom`,
`sorry`, or `native_decide` in the package (`ArithS/Audit.lean` prints the census).

## The three results

| Theorem | Statement | File |
|---|---|---|
| `ArithS.red_cell` | Dupoc k vs Cupod k = (D, C) at **every** budget k — the cell Critch et al. leave open | `ArithS/RedCell.lean` |
| `ArithS.dupoc_self_coop_unconditional` | Dupoc k cooperates with itself (and Cupod k defects against itself) at every sufficiently large k — Critch's Theorem 3.7 | `ArithS/Necessitation/Package.lean` |
| `ArithS.pblt_unconditional` | the parametric bounded Löb theorem, uniform in the budget — Critch's Lemma 3.6 | `ArithS/Necessitation/Package.lean` |

The last two rest on `ArithS.boundedInnerNec_sixteen` (same file): Critch's assumption (d),
bounded inner necessitation with polynomial expansion (degree 16), **proved** rather than
assumed. Its proof is the `Necessitation/` directory: a verification proof built as a derivation
code inside every model of IΣ₁, never writing a code as a numeral.

## What a reader must accept by eye (the trusted base)

Eight definitions, under 300 lines in total: the theory `TAct` (PA plus two action constants,
distinct and equal to 0/1 in some order — `TheoryAct.lean`), the length measure `dlen`
(`DerivationLength.lean`), the bounded box `LenProvableV` (`BewV.lean`), the program codes
(`Prog.lean`), the guard template and program descriptions (`Template.lean`, `Guard.lean`), and
the evaluator `EvalGraph` (`Eval.lean`). Everything else is a theorem about these. Why each is
what it is, the alternative, and what breaks without it:
`../engine/PrisonersDilemma/Research/Notes/SPRIME_DESIGN_RATIONALE.md`.

## How to check that the definitions mean what we claim

`../engine/PrisonersDilemma/Research/Notes/RED_CELL_AUDIT.md`, with its executable companions:
`ArithS/RedCellAudit.lean` (negative controls, determinism, fuel-independence, the truth
equation, non-vacuity), `ArithS/RedCellUnsound.lean` (the "drop soundness" mutation as a
theorem: an inconsistent theory flips the cell to (C, D)), and
`../engine/PrisonersDilemma/Base/RedCellFramework.lean` (the red cell proved once, axiom-free,
against an abstract hypothesis package, then instantiated with the engine's `S` in
`../engine/PrisonersDilemma/Theorems/DupocBot/RedCellInstance.lean` and with this package in
`ArithS/RedCellInstance.lean`).

## Relation to the engine's rule system

The engine's `S` is this system plus one rule: a free citation of an existing proof (its box
rules are additive; PA's verification is polynomial). No matrix result depends on that rule
(`../engine/PrisonersDilemma/Research/Notes/BOXCOST_SPIKE.md`); how the two systems should be
related in the paper is the open decision in `MERGE_CROSSROAD.md` in the same directory.

## Building

Lean toolchain as pinned in `lean-toolchain`; Foundation and the engine are resolved by `lake`.

```
cd arith
lake build --try-cache ArithS     # first time: downloads Foundation's prebuilt artifacts
lake env lean ArithS/Audit.lean    # prints the axiom census
```

A full incremental build is about 3300 jobs; a single file check needs ~5 GB of imports.

## Reading order

1. `../engine/PrisonersDilemma/Research/Notes/ARITHMETIZED_S_RESULTS.md` — what is proved.
2. `SPRIME_DESIGN_RATIONALE.md` — why the definitions are what they are.
3. `RED_CELL_AUDIT.md` — how the meaning is pinned; then the three audit files above.
4. `MERGE_CROSSROAD.md`, `BOXCOST_SPIKE.md` — the engine/PA relation and the open decision.
5. `ARITHMETIZED_S_ROADMAP.md` — the full construction log (M1 → U10), for the details.
