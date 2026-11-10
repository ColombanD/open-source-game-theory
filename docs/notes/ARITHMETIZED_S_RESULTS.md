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

155 engine cells: **108 stated in `S'`** (`Outcome/Matrix/<L>.lean`, `outcome_<L>_vs_<R>`), of which
**94 agree with the engine and 14 disagree**; **25 genuine floors** (dichotomies, no side taken);
**22 excluded** (LegibleBot 16, OptimBot 4, WaryBot's two floor cells). *(107 / 13 / 26 until 2026-11-05, when
Cupod × OBot left the floors — §5.1.)*

Beyond the engine's ledger, **12 `S'`-only cells** (2026-10-13): `DupocTrollBot k` ("defect iff the opponent IS
`DupocBot k`", an engine definition with no engine theorem) against the ten `body` bots, CIMCIC and itself —
9 SND, 1 POS (× DupocBot `(D, D)`), 1 LOEB (× DIMCID `(C, D)`), 1 genuine floor (× CIMCIC, engine side `(C, D)`).
`Cells/DupocTrollBot.lean`; ledger section "`S'`-only cells" of `ROUTE_B_CENSUS.md`. Export totals: 118 cells, 27 floors.

And **13 more `S'`-only cells** (2026-10-13): `DIMDID k` ("defect iff my defection provably implies yours",
`Bots/DIMDID.lean`, the C/D TRANSPOSITION of CIMCIC — `(CIMCIC k).transpose = DIMDID k` by `rfl`) against the ten
`body` bots, CIMCIC, PrudentBot and itself — 3 SND, 2 POS, 2 LOEB (× OBot, × DIMCID, both `(D, D)`), 3 by the
general transposition theorem from CIMCIC's cells (× DefectBot, × CupodBot, × itself), 3 genuine two-hinge floors
(× DupocBot, × CIMCIC, × PrudentBot; engine side `(C, D)`, hinge side `(D, D)`). The new argument is the
SELF-DEFEATING guard (soundness pointing the other way: a found "I defect ⇒ you defect" forces the opponent's
defection, so against a cooperator it is never found). `Cells/Dimdid.lean`. Export totals: 128 cells, 30 floors.

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

### 5.1 2026-11-05 — one floor was not a floor; a second reduction

**The claim "the only witness runs through an else-branch, so the hinge is bounded consistency" is an ARGUMENT
about the evaluation, and a proof need not follow the evaluation.** Checked cell by cell on the paper's base zoo
(`body8`: Dupoc × DBot, Dupoc × EBot, Cupod × OBot), it holds for two and FAILS for the third.

* **Cupod × OBot is `(D, D)`, a theorem** (`Cells/CupodOBot.lean`, `outcome_CupodBot_vs_OBot`; the engine says
  `(C, D)`). OBot cooperates only with an opponent that cooperates with BOTH `.bot CooperateBot` and
  `.bot DefectBot`. Cupod defects against `.bot DefectBot` through its THEN-branch, found in every model above a
  threshold (`cupod_botDB_V`). So OBot's defection is over-determined: whatever Cupod plays against
  `.bot CooperateBot` — and a search is decided in every model — OBot ends on a D. `TAct` proves
  `∀ k ≥ k̂, "OBot plays D against CupodBot k"` by that case split (`tact_rOB_above`), with no consistency statement
  in it; the instance is found by the `k̂`-chain (`hinge_found_CupodBot_vs_OBot`), Cupod plays its then-branch.
  The tau images follow: `cupod × obot = D` (`Tau/ClosedWatchCu.cupod_obot_D`, the argument of
  `ClosedWatchDd.WoDd_plays_D` on the Cupod members) and `obot × cupod = D` are row slots; **199 row slots + 57
  floor bits = 256**. The value agrees with the standalone repo's hand table (`CRITCH8_TRANSCRIPTION_DIFFS`), which
  had `(D, D)` all along.
* **Dupoc × EBot is inter-reducible with the SAME bounded-consistency instance as Dupoc × DBot**
  (`Cells/FloorReductions.lean`): `hinge_reduces_to_bounded_consistency_DupocBot_vs_EBot` (cost `k + C₀ + C₁·size k`,
  verbatim DBot's: EBot's cooperation passes its first rung) and `bounded_consistency_reduces_to_hinge_DupocBot_vs_EBot`
  (for `k > k̂`, cost `m + C₀ + C₁·size k + C₂·(size k)²`: the second rung needs Dupoc's then-branch C against
  `.bot CooperateBot`, true above a threshold, so the uniform theorem is conditional and its threshold costs one
  more cut).

So on `body8` the ledger is **two floors, both proved inter-reducible with one sentence `σ_k`, and one flip**. For the
floors outside `body8` the reduction is NOT mechanized: they are cells `S'` determines only up to their hinge, and
"genuine" is the structural argument, to be checked per cell for over-determination before it is claimed.

### 5.2 2026-11-05 (later) — the eight remaining floors of the 12-bot ladder, one by one

After §5.1 the paper's top rung (`body8+trolls+provers`) had ten floor pairs, two of them reduced. The other eight:

| pair | result | where |
|---|---|---|
| DIMDID × CIMCIC | **DECIDED: `(C, D)` at every `k`** — the red cell's argument. The pair is self-dual, so the two guards are τ-images, found together (`guard_DIMDID_iff_guard_CIMCIC`); together they contradict each other; neither is found | `Cells/SelfDual.snd_DIMDID_vs_CIMCIC`, `outcome_DIMDID_vs_CIMCIC` |
| Dupoc × CupodTroll | **two-way reduction**, no threshold, overhead `C₀ + C₁·size k` each way: the troll is ONE search node, so it cooperates iff its `.eq` guard `ε_k` (false) is not found | `Cells/TrollReduction` |
| CIMCIC × DBot, × EBot | **one-way**: hinge within `k` ⇒ `Con_TAct(k − C₀ − C₁·size k)` within `k + O((log k)²)` | `Cells/ConReduction` |
| CIMCIC × CupodTroll, × DupocTroll | **one-way**, same statement | `Cells/ConReduction` |
| CIMCIC × Cupod | **one-way, both hinges**; NOT decided (three outcomes consistent) | `Cells/ConReduction`, `Cells/NestedReduction` |
| DIMDID × Dupoc | **the SAME floor as CIMCIC × Cupod** (its transposition: hinges coincide pairwise, outcomes are transposes at every `k`); both hinges one-way | `Cells/SelfDual`, `Cells/NestedReduction` |

**The generic one-way reduction** (`Cells/ConReduction.hinge_con_reduction`). If a hinge formula `r`, when TRUE in a
model at `x`, forbids that all of a finite list of guard boxes hold at budget `x` (evaluator determinism: a play
that differs from a then-constant is a guard not found), then `TAct ⊢ ∀ k ≥ k̂, r(k) → conBelow C₀ C₁ (k)`, where
`conBelow` says "`⊥` has no proof within `k − C₀ − C₁·‖k‖`" — because a proof of `⊥` within `j` gives a proof of any
fixed guard instance within `j + E₀ + E₁·‖k‖` IN EVERY MODEL (`exFalso_V`, ex falso with length accounting). `⊥` is
τ-invariant, so no twin disjunction. This is the paper's "bounded consistency" VERBATIM, for every remaining hinge.
For CIMCIC the list is {its own hinge, the guard its opponent's cooperation needs to fail}: CIMCIC's guard is an
implication about its own play, `φ ↔ (□φ → q)`, and `q` needs a box to fail.

**Literal form for all nine** (2026-11-05, evening). The three Dupoc floors also have the literal one-way statement
through the generic lemma: `hinge_reduces_to_literal_consistency_DupocBot_vs_{DBot, EBot}` (`Cells/ConReduction` §6)
and `…_DupocBot_vs_CupodTrollBot` (`Cells/NestedReduction` §3). So the paper's main thread — *if the hinge holds,
`S` proves within about `k` symbols that it has no contradiction of length about `k`* — is a theorem for EVERY hinge
of the nine floors of the 12-bot ladder, in the SAME form (`conBelow`).

**No converse for the one-way ones**, and on paper none at additive overhead: from consistency one must first PROVE the
guard boxes as theorems (inner necessitation, polynomial), so the converse starts from `Con_TAct(poly(k))`. In GL
terms CIMCIC's guard against these opponents is the fixed point `p ↔ (□p → Con)`, i.e. `Con` itself.

**Ledger after §5.2.** 134 cells / 28 floors. On the 12-bot rung: **nine floor pairs, eight independent questions**
(Dupoc × DBot, × EBot, × CupodTroll two-way; four CIMCIC single-hinge one-way; one nested one-way), every hinge of
every one of them tied to bounded consistency BY THEOREM in at least one direction. The tau bits `dimdid × cimcic` and
back stay floor bits (no τ-symmetry inside one `.sys`): two more RECORDED provenance divergences (eight in all).
The hinge-side table carried `(D, D)` for DIMDID × CIMCIC, a value now proved impossible.

**Consequences downstream.** The export is 134 cells / 28 floors (133 / 29 after §5.1 alone); `body8` has 2 hinge pairs and 1 flip; every EGT
run made before this date used `(C, D)` for Cupod × OBot on the engine side and must be re-run (the hinge-side runs
had `(D, D)` for this cell but also move the two real floors).

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
  equivalence does not preserve `□_k`) — the SUBSTITUTION code equations are on the box-free fragment. The
  τ equations hold through boxes since 2026-11-09: a box names its body by `boxQuote`, a term τ re-values
  (`Agents/CodeTranspose`), and the transposition theorem of outcomes and its corollary (a program and its
  transpose play opposite actions) hold on every program without a tau constructor, at every budget
  (`outcomeAtA_transpose_of_transposableP`, `opposite_of_plays_transpose_of_transposableP`; LegibleBot is
  in that fragment). Not done: the truth equation of a box sentence under the two readings, and τ through
  `.sys` (the 8 recorded tau provenance divergences).
* Encoding: `‖⌜φ⌝‖` is exponential in syntax depth; every statement is "for all large `k`".
* LegibleBot: fixable in length within route (c) (inner budget `gBudget #6`, polylog; a linear stagger is
  impossible in `S'`), blocked on necessitation for a frame-computed box body — a third U10-kit instance.
