# ARITHMETIZED_S_RESULTS — what PA-`S'` proves

*Every statement is a Lean theorem in `arith/ArithS/` on `[propext, Classical.choice, Quot.sound]`.
Design: `SPRIME_DESIGN_RATIONALE.md`. Cell ledger: `ROUTE_B_CENSUS.md`. Code guide: `arith/ArithS/README.md`.
The chronological long form (addenda by date, commit hashes, superseded tallies) is in git before `c0aa163`.*

## 1. The object

PA on Foundation, with: a symbol-blind length `proofLen` on proof codes; the box
`□_k φ := ∃ d < codeBound k, Proof TAct d φ ∧ proofLen d ≤ k` (Δ₁, properness makes the code bound invisible);
actions as constants, `TAct = PA + {c_C ≠ c_D, actionAxiom}` closed under the swap τ, with
`TAct ⊢_k φ ↔ TAct ⊢_k τφ` at EVERY length; programs as codes with binary-numeral descriptions (length
`O(log)`); the evaluator `EvalGraph` whose `search` clause consults the box.

## 2. Headline theorems

```
red_cell (k)                : Dupoc k defects against Cupod k, Cupod k cooperates — EVERY k
                              (τ-symmetry + soundness in ℕ + determinism; no Löb, no census, no threshold)
snd_DupocBot_vs_CupodBot (k): the same on the engine's codes progCode (DupocBot k) / progCode (CupodBot k)
boundedInnerNec_sixteen     : BoundedInnerNec 16 — Critch's assumption (d), a THEOREM: PA verifies a proof
                              of length ≤ ‖k‖³ within a polynomial (degree 16) budget, in every model
closedInnerNec_sixteen      : the same for a closed sentence at an arbitrary budget
pblt          : the parametric bounded Löb theorem (Critch 2019's uniform proof), family-parametric
dupoc_self_coop : ∃ k₀, ∀ k > k₀, Dupoc k cooperates with itself ∧ Cupod k defects against itself
dimcid_vs_closed (P)        : ∃ k₀, ∀ k > k₀, DIMCID k defects against the closed code P and FINDS its guard
```

**Paper sentence.** *In Peano Arithmetic with a length-bounded provability predicate, Dupoc cooperates with
itself at every sufficiently large budget, and the bounded inner necessitation principle this rests on is
itself a theorem of the system, with polynomial expansion.* On the degree: 16 rather than the design's 3,
every loss traceable to unary variable indices in `proofLen`; the results are parametric in the degree.

## 3. The matrix in `S'` (the ledger, cell-exact)

155 engine cells: **107 stated in `S'`** (`Outcome/Matrix/<L>.lean`, `outcome_<L>_vs_<R>`), of which
**94 agree with the engine and 13 disagree**; **26 genuine floors** (dichotomies, no side taken);
**22 excluded** (LegibleBot 16, OptimBot 4, WaryBot's two floor cells).

| class | cells | how |
|---|---|---|
| SF | 28 | search-free: transfer at the engine's fuel (`eval`/`EvalGraph` in lockstep) |
| SND | 39 | guard FALSE in ℕ ⇒ never found (soundness) ⇒ else branch; every `k` or all large `k` |
| POS | 13 | guard `TAct`-provable by completeness; its `k`-instance fits for large `k` (`found_of_all`, the `k̂`-chain) |
| LOEB | 14 | bounded Löb via `family_found` (single, mutual as one conjunction family, nested searches, frozen `.bot`) |
| FLIP | 13 | stated, value CONTRADICTS the engine (§4) |
| GENUINE-FLOOR | 26 | `dich_<L>_vs_<R>` (§5) |
| EXCLUDED | 22 | boxes inside guards (`box_guard_never_fits`), WaryBot's floor cells |

Seven stated cells are on the hand-template twins `Just`/`Just7`/`CupodTroll7` (a budget-carrying frozen
snapshot inside the guard is describable only through the seven-variable slot templates, `ROUTE_B_SCOPE.md` §7),
not the engine's `progCode`; the former Dupoc/Cupod twins are retired since 2026-09-30 — `Cells/{DupocEngine,
CimcicEngine, DimcidEngine}.lean` prove Dupoc × Dupoc, Cupod × Cupod, Dupoc/Cupod × Mirror, CIMCIC × Dupoc and
DIMCID × Cupod on `progCode (DupocBot k)`/`progCode (CupodBot k)` (`arith/ArithS/README.md` §4).

## 4. The finding: where `S'` contradicts `S`

The engine closes these cells by censuses that rest on a player being UNREADABLE by `S`'s rules; PA reads
every source (Σ₁-completeness), and a negative Löb guard ("I will not cooperate") is self-fulfilling under
a real proof predicate: it gets FOUND.

| cell | engine | `S'` | theorem |
|---|---|---|---|
| DIMCID × CooperateBot | (C, C) | (D, C) | `loeb_DIMCID_vs_CooperateBot` |
| DIMCID × TitForTatBot | (C, C) | (D, D) | `loeb_DIMCID_vs_TitForTatBot` |
| DIMCID × CupodTrollBot | (C, C) | (D, C) | `loeb_DIMCID_vs_CupodTrollBot` |
| DIMCID × DBot | (C, C) | (D, C) | `loeb_DIMCID_vs_DBot` |
| DIMCID × EBot | (C, C) | (D, D) | `loeb_DIMCID_vs_EBot` |
| DIMCID × OBot | (C, D) | (D, D) | `loeb_DIMCID_vs_OBot` |
| DIMCID × DupocBot | **(C, D) at EVERY k** | (D, D) all large k | `loeb_DIMCID_vs_DupocBot` |
| DIMCID × JustBot | (C, D) | (D, D) | `loeb_DIMCID_vs_JustBot` |
| DIMCID × PrudentBot | (C, D) | (D, D) | `loeb_DIMCID_vs_PrudentBot` |
| CIMCIC × DIMCID | (D, C) | (D, D) | `loeb_CIMCIC_vs_DIMCID` |
| GuardianBot × DIMCID | (C, C) | (D, D) | `loeb_GuardianBot_vs_DIMCID` |
| WaryBot × MirrorBot | (C, C) | (D, D) | `loeb_WaryBot_vs_MirrorBot` |
| WaryBot × WaryBot | (C, C) | (D, D) | `loeb_WaryBot_vs_WaryBot` |

DIMCID cooperates NOWHERE in `S'` (`dimcid_vs_closed`: "my cooperating implies X" is found because finding
it refutes the antecedent, whatever `X`). The Dupoc row is the sharpest case: a UNIVERSAL engine theorem
contradicted for all large `k`. Two CIMCIC cells (× DefectBot, × OBot) keep the engine's value but by
soundness (self-refuting guard), not by the engine's census.

**Paper sentence.** *The engine's `S` is PA plus free citation, MINUS the reading of sources its rules do not
cover, plus a stipulated answer to an open proof-complexity question; the second departure changes outcomes.*

## 5. The floors: dichotomies, no side taken

In each of the 26 cells the floor guard is a TRUE Σ₁ sentence whose only witness runs through the ELSE branch
of a search on a guard σ FALSE in ℕ, so "found within `k`" is inter-derivable (additive overhead) with the
bounded consistency `Con_TAct(k ± c)` — Pudlák's question (lower bound `k^ε`, linear regime open). The engine's
`search_f` stipulates `+k`, the negative side. `S'` proves the dependence:

```
dich_<L>_vs_<R> : ∃ k₀, ∀ k > k₀, (¬A_k → ⟨engine value⟩) ∧ (A_k → ⟨found-branch value⟩)
A_k := LenBox TAct k (guardCodeB (templateCode φ) (progCode me) (progCode opp) k)   -- written inline
```

nested over two or three hinges for the bistable pairs (Wary × Dupoc/Just/Prudent, Cupod × Prudent both ways,
Just × Cupod, CIMCIC × Cupod). Settled halves and true guards are unconditional (`floor_*_left/_right/_true`).
The reduction, for the simplest cell (`Cells/FloorDichotomy.lean`):

```
hinge_reduces_to_bounded_consistency_DupocBot_vs_DBot : ∃ C₀ C₁, ∀ k,
    A_k → LenBox TAct (k + C₀ + C₁ * size k) ⌜¬□_k σ_k ∨ ¬□_k τσ_k⌝
bounded_consistency_reduces_to_hinge_DupocBot_vs_DBot : the converse from the conjunction
```

The ∨/∧ gap is the τ-invariance of `□_k` that `TAct` does not internalize. The prudence hinge is discharged
where the opponent's defection against `.bot DefectBot` is its then-branch (Guardian, Wary, Cupod:
`prudence_found_vs_*`); not dischargeable for Just and CIMCIC (their guards are else-branches: the residue
itself). Prudent × EBot is closed in both worlds (`dich_PrudentBot_vs_EBot_full`, via Prudent × `.bot
MirrorBot` by Löb).

**Paper sentence.** *The engine's floor rule stipulates the negative side of the linear-regime
finite-consistency question; `S'` proves the dependence and takes no side.*

## 6. The bridge `S → S'` (T2, frozen)

Three theorems settle what a rule-by-rule bridge can be:
* **T2-CORE** (`Pf_core_sound`): the engine's Löbian core (`boxIntro/axK/box4/diagF/…`) is a fragment of GL over
  PA's real provability predicate; every budget question lives in the leaves.
* **T2-AGENT** (`playsProof_evalGraph`, `eval_iff_evalGraph`): given agreement on the consulted `□_k` facts
  (`GuardAgree` = bounded D1 and its converse, a hypothesis never assumed by route B), every evaluation
  certificate of `S` is a run of `EvalGraph` at the same budgets, and conversely.
* **The obstruction**: citation composes doubly-exponentially through nested boxes while `search_t` cites at
  `log k`, so no budget-keeping rule bridge exists at polynomial budgets (`MERGE_CROSSROAD.md`). Route B
  re-proves cells directly instead. The engine's atom re-cost (2026-09-16, `pf_size : Pf k φ → φ.size ≤ k`)
  removed the other departure from a character count; every outcome value survived it.

## 7. Boundaries

* `.box` is not compositional under LENGTH-bounded provability (a box names its body's code; provable
  equivalence does not preserve `□_k`) — the code equations are on the box-free fragment.
* Encoding: `‖⌜φ⌝‖` is exponential in syntax depth; every statement is "for all large `k`".
* LegibleBot: fixable in length within route (c) (inner budget `gBudget #6`, polylog; a linear stagger is
  impossible in `S'`), blocked on necessitation for a frame-computed box body — a third U10-kit instance.
