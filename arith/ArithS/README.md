# `ArithS` — reading guide

PA-`S'`: the engine's proof system `S` replaced by Peano Arithmetic with a length-bounded provability
predicate, and the matrix re-proved cell by cell. 134k lines; a reader needs ~5 %. This says which.

Design: `Research/Notes/SPRIME_DESIGN_RATIONALE.md`. Results: `ARITHMETIZED_S_RESULTS.md`. Ledger: `ROUTE_B_CENSUS.md`.

## 1. Tiers

| tier | where | lines | verdict |
|---|---|---:|---|
| trusted base (definitions you accept by eye) | `Theory/ Length/ Box/ Agents/ Eval/` | 13k | read §2 |
| results | `Outcome/` `Cells/` `Assembly/` `Loeb/` `Necessitation/Package.lean` | 19k | read §3 |
| U10 construction (PA verifies its own proofs within budget) | `Necessitation/` minus `Package` | 96k | do not open |
| frozen bridge, estimates, census | `Bridge/` `Length/Proper` `Box/ProperV` `Agents/Fit*` `Audit/` | 6k | skip |

Files marked `GENERATED` are never edited by hand (`scripts/README.md`).

## 2. Trusted base — nine definitions, in order

1. `LAct = ℒₒᵣ + {c_C, c_D}`, `swap` (τ) — [`Theory/LangAct.lean`](Theory/LangAct.lean)
2. `TAct = PA + {c_C ≠ c_D, c_D ≠ c_C, axAct, axAct'}` (closed under `swap`; ℕ is a model) — [`Theory/TheoryAct.lean`](Theory/TheoryAct.lean)
3. `dlen`, symbol count of a proof code (symbol-blind ⇒ τ-invariant) — [`Length/DerivationLength.lean`](Length/DerivationLength.lean), `dlen ⌜d⌝ = mlen d` in `MetaLength`
4. `□[k] φ := ∃ d < fbound k, Proof TAct d φ ∧ dlen d ≤ k` (`LenProvableV`) — [`Box/BewV.lean`](Box/BewV.lean)
5. program codes `pConst pSelf pOpp pBot pSim pIte pSearch` on `ppair`, `swapcode` — [`Agents/Prog.lean`](Agents/Prog.lean)
6. descriptions as binary-numeral terms (`progT`, `dnum dU dW`) — [`Agents/ProgT.lean`](Agents/ProgT.lean)
7. `guardTemplate a` ("opp plays `a` against me"), `tmpl : PD.Formula → sentence`, `guardCode`/`guardCodeB` (runtime guard, budget slot) — [`Agents/Template.lean`](Agents/Template.lean), [`Agents/Code.lean`](Agents/Code.lean), [`Agents/Guard.lean`](Agents/Guard.lean)
8. `psubst`/`gsubst`, the engine's `Prog.subst` on codes — [`Agents/Subst.lean`](Agents/Subst.lean)
9. `EvalGraph n me opp p a`, the evaluator as a Σ₁ fixpoint; `search` consults the box — [`Eval/Eval.lean`](Eval/Eval.lean)

Engine bridge: `pcode : PD.Prog → ℕ`, `tcode : PD.Formula → ℕ` (`Agents/Code.lean`).

## 3. Results — start here

`Outcome/`: the matrix in the engine's words. [`Spec.lean`](Outcome/Spec.lean) defines `plays`,
`OutcomeSpecA`, `bot`/`const`, `□[k]`; `Matrix/<L>.lean` has one theorem per cell:

```lean
theorem outcome_DupocBot_vs_CupodBot :
    OutcomeSpecA .universal (bot DupocBot) (bot CupodBot) (some (.D, .C))
```

Then, in order:
1. red cell — [`Cells/RedCellEngine.lean`](Cells/RedCellEngine.lean) (60 lines: τ-symmetry + soundness + determinism)
2. a soundness cell — `Cells/SoundnessCells.lean`, `snd_else_of_false`
3. PBLT statements — `Assembly/Family.lean`, `Necessitation/Package.lean`
4. a Löb cell — `Cells/CIMCIC.lean`
5. the flips — `Cells/FlipCells.lean`, `Cells/DimcidFlips.lean` (`dimcid_vs_closed`)
6. the floors — `Cells/FloorDichotomy.lean`

## 4. Dictionary

| engine | `ArithS` |
|---|---|
| `Prog` | `ℕ` code, `pcode p`; `bot P`, `const P` |
| `Action` | `actCode .C = 0`, `actCode .D = 1` |
| guard `Formula` | `tmpl φ`, code `tcode φ` |
| `eval` | `EvalGraph n me opp p a` |
| `play`, `outcome`, `OutcomeSpec` | `plays`, `OutcomeAtA`, `OutcomeSpecA` |
| `Pf k φ` | `□[k] ⌜φ⌝` |
| `Pf.transpose` | `transpose_exists` (free: τ is a language hom) |
| `sound_upto` | `models_TAct` + truth equations |
| `pblt_engine` | `pblt_unconditional` |
| `outcome_L_vs_R` | `outcome_L_vs_R`, proved from `sf_/snd_/pos_/loeb_/khat_L_vs_R` |

Cell theorem heads = proof method: `sf` search-free · `snd` soundness/else branch · `pos` found without Löb ·
`loeb` bounded Löb · `khat` the `k̂`-chain · `floor` settled half · `dich` floor dichotomy.

**Twins.** `Dupoc`, `Cupod`, `Just`, `Just7`, `CupodTroll7` are hand-template codes, NOT the engine's `pcode`
(same meaning, different sentence; not interchangeable at a fixed `k`). Thirteen cells are stated on them and
keep the twin's name (`outcome_Dupoc_vs_Dupoc`). `Cimcic`, `Dimcid`, `Prudent`, `Mirror` are the engine's codes.

## 5. Folders

- `Theory/` — language, theory, τ-transport of proofs, τ-closure at every length
- `Length/` — symbol counts; `Proper` = code below a tower (estimate)
- `Box/` — `□[k]`; bounded modus ponens; properness in every model
- `Agents/` — codes, descriptions, templates, guards, substitution, `pcode`; `Fit*` = why LegibleBot is out
- `Eval/` — the evaluator, its determinism and monotonicity
- `Loeb/`, `Assembly/` — diagonal lemma, the family-parametric PBLT
- `Necessitation/` — U10; read only `Package.lean`
- `Cells/` — the proofs by method; `Common/` shared bots and templates; `Names` = old names
- `Outcome/` — the cells in the engine's words
- `Bridge/` — frozen T2 bridge (impossible at polynomial budgets)
- `Audit/` — every `#print axioms` the build runs

## 6. Build

```
cd arith && lake build ArithS --try-cache       # never compile Foundation/mathlib
timeout 900 lake env lean ArithS/<file>.lean    # single file; check the exit code
scripts/regen_all.sh                            # generated tables in sync
```

Census: all `[propext, Classical.choice, Quot.sound]` but four known subsets. Traps: `ARITH_TRAPS.md`.

## 7. Not here

LegibleBot/OptimBot/WaryBot floors (22 cells, need a third U10 kit); the 26 genuine floors are dichotomies on
a hinge = bounded consistency at `k` (never an axiom); tau constructors.
