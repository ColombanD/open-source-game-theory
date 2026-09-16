# The red cell in PA-`S'`: what is trusted, what is checked, how to break it (2026-09-16)

Purpose: answer "is what we defined and proved what we wanted?" for ONE result, `ArithS.red_cell`
(Cupod vs Dupoc = (D, C) at every budget), by separating the **trusted base** — definitions a
reader must accept by eye — from the **checked part**, and by pinning the meaning of the trusted
base with sanity theorems (`arith/ArithS/RedCellAudit.lean`) and deliberate-break tests. The
method is meant to be repeated for every headline result.

## 1. The statement, in words

> With fuel 2, the program `Dupoc k`, run by itself against `Cupod k`, returns 1 (= D);
> `Cupod k` against `Dupoc k` returns 0 (= C). For every `k : ℕ`.

Lean: `EvalGraph 2 (Dupoc k) (Cupod k) (Dupoc k) 1 ∧ EvalGraph 2 (Cupod k) (Dupoc k) (Cupod k) 0`.
Axioms: `[propext, Classical.choice, Quot.sound]`.

## 2. The trusted base (read these; nothing else needs to be believed)

| # | Object | Lean | Where | Meaning in one sentence |
|---|---|---|---|---|
| T1 | Program codes | `pConst a`, `pSelf`, `pOpp`, `pBot`, `pSim`, `pIte`, `pSearch k g p q` | `Prog.lean` §137–169 | a program is a number: a tag paired (`ppair`) with its children; `pSearch k g p q` = "search for a proof of length ≤ k of the guard template `g` instantiated at (me, opp); if found run `p`, else `q`" |
| T2 | The two bots | `Dupoc k := pSearch k ⌜GtmplA 0⌝ (pConst 0) (pConst 1)`, `Cupod k` with `1`/`0` | `RedCell.lean` §31–35 | Dupoc: cooperate iff "opp plays C against me" is provable in ≤ k; Cupod: defect iff "opp plays D against me" is |
| T3 | The guard template | `gtmpl` (7 free variables), `GtmplA a` (action fixed) | `Template.lean` §37, §83 | "the program described by (x₂,u₂,w₂) plays `t` against the one described by (x₁,u₁,w₁)": `∃ me opp, me = relabel u₁ w₁ x₁ ∧ opp = relabel u₂ w₂ x₂ ∧ ∃ n, EvalGraph n opp me opp t` |
| T4 | Descriptions | `dnumT`, `dUT`, `dWT`, `descVec`, `guardCode g me opp := subst (descVec me opp) g` | `Template.lean` §60–72, `Guard.lean` §153–157 | how a program is named INSIDE a sentence: its canonical code as a structural term of binary numerals, plus two constants saying which of the two C/D orientations it is; the guard is the template with the six descriptions substituted |
| T5 | The evaluator | `EvalGraph n me opp p a` = Δ₁ fixed point of the seven clauses in `Eval.lean` §35–49 | `Eval.lean` | fuel-`n` big-step semantics; the `search` clause: `LenProvableV TAct k (guardCode g me opp)` → run `p`, `¬…` → run `q` |
| T6 | Bounded provability | `LenProvableV T k φ := ∃ d < fbound k, Proof T d φ ∧ dlen T d ≤ k` | `BewV.lean` §23 | "φ has a proof code of length ≤ k" (`dlen` = character count of the derivation, M1; `fbound` = the code bound making it Δ₁) |
| T7 | The theory | `TAct := {axAct, axAct', axNe, axNe'} ∪ emb 𝗣𝗔` | `TheoryAct.lean` §65–114 | PA plus two constants `c_C`, `c_D` that are distinct and are `0`/`1` in some order |
| T8 | Foundation | `Proof`, `Semiformula`, `subst`, `⌜·⌝`, IΣ₁ | external | the arithmetization of syntax and proofs; trusted as a library |

Sizes: T1–T7 together are under 300 lines of definitions. Everything else in the package is
theorems about them.

## 3. What is checked (theorems, three standard axioms)

* **The proof itself** (`red_cell`, 30 lines): symmetry `guard_Dupoc_iff_guard_Cupod` (a `TAct`
  proof transports along the C/D swap at the same length — `Transpose.lean`; and
  `swapcode (Dupoc k) = Cupod k`), the truth equation (§4 below), determinism of `EvalGraph`.
* **Sanity theorems** (`RedCellAudit.lean`), each a one-liner from the package:
  1. *Negative controls*: `dupoc_not_coop`, `cupod_not_defect` — the opposite outcomes are
     REFUTED, at every fuel. A vacuous or under-determined evaluator could not refute them.
  2. *Determinism*: `red_cell_deterministic` — at most one action per run.
  3. *Fuel-independence*: `red_cell_any_fuel` — the answer is stable above fuel 2.
  4. *Truth equation*: `guard_is_about_the_run` — a provable guard is a true statement about the
     run (`models_guardSentenceA_iff` + soundness of `TAct`). This is the link between T3–T4
     (a sentence) and T5 (a run): if the template were misread, this would not compile.
  5. *Why both guards fail*: `guards_both_fail` — the argument's core, isolated.
  6. *Non-vacuity*: `search_is_real` (`guard_fits`) — from some budget on, the guard sentence is
     shorter than `k`, so "unprovable at `k`" is not "too long to state". (Only for large `k`;
     at small `k` the cell still holds, trivially — both searches fail for lack of room.)

## 4. How to break it (the deliberate-mutation protocol)

A definition that is wrong in the usual ways must make something FAIL. Each mutation below is
applied in a scratch copy and the named theorem must stop compiling; if it still compiles, the
definition is not load-bearing and the audit has found a hole.

| Mutate | Must fail |
|---|---|
| swap the continuations of `Dupoc` (`pConst 1`, `pConst 0`) | EXECUTED 2026-09-16: `swapcode_Dupoc` (line 42, the mutated Dupoc is no longer Cupod's mirror) and `red_cell` (lines 112–123) fail; `red_cell_unique` cannot elaborate |
| give `Cupod` the template `GtmplA 0` (same as Dupoc) | `guard_Dupoc_iff_guard_Cupod` (`swapcode_Cupod`) |
| in `gtmpl`, run `me` instead of `opp` (`EvalGraph n me opp me t`) | `models_guardSentenceA_iff`, hence `guard_is_about_the_run` |
| in the evaluator's `search` clause, swap the `p`/`q` branches | `red_cell` via `EvalGraph.search_iff` |
| drop `axAct` from `TAct` | the M4 vacuity found 2026-09-12 returns: models where the constants read as 5/7 (`tact_complete'` fails) — `red_cell` itself is EXPECTED to survive (it only needs soundness in ℕ + symmetry), i.e. the red cell should not depend on the action axiom; untested (the mutation rebuilds the whole package) |
| **drop soundness**: add `c_C = c_D` (and its swap) to the theory (`TBad`) | EXECUTED 2026-09-16 as a THEOREM, `arith/ArithS/RedCellUnsound.lean`: `TBad` is inconsistent, every sentence has a 3-node proof of length `3·|σ| + c`, both guards become provable for large `k`, and the cell FLIPS to `(C, D)` — `red_cell_flips_when_unsound`, with `red_cell_flip` showing `(D, C)` under `TAct` and `(C, D)` under `TBad` at the same budgets. The evaluator is copied with the theory swapped (`EvalGraphBad`; not yet parametric). This is the paper note's Proposition 6.1 (soundness cannot be dropped), mechanized. |

## 4b. The theorem, stated once, instantiated twice (2026-09-16)

`engine/PrisonersDilemma/Base/RedCellFramework.lean` states the hypothesis package (the paper
note's (H0)–(H6), abstracted: bounded derivability `Prov`, an involutive transposition `τ` with
`prov_swap : Prov k φ → Prov k (τ φ)`, the two guard sentences with `mirror : τ (ρ₁ k) = ρ₂ k`,
the fire/else clauses of the two searchers, soundness at the ONE instance `sound₂ : Prov k (ρ₂ k) →
playA k D`, determinism of both plays) and proves, with NO axioms at all:
`search_symmetry`, `guards_fail`, `red_cell : ∀ k, playA k D ∧ playB k C`, and the §6.1 table —
`not_CC` and `not_DD` from symmetry alone, `not_CD` from soundness. (Finding: the split needs
determinism of BOTH plays, which the note folds into (H0).) Two instances, both at the three
standard axioms and sharing no code:
* `PD.Theorems.red_cell_engine` (`Theorems/DupocBot/RedCellInstance.lean`): `Prov := Pf`,
  `τ := Formula.transpose`, `prov_swap := Pf.transpose`, plays via `play`;
* `ArithS.red_cell_via_framework` (`arith/ArithS/RedCellInstance.lean`): `Prov k φ :=
  LenProvableV TAct k ⌜φ⌝`, `τ := lMap swap`, `prov_swap` from the same-length swap transport,
  plays via `EvalGraph`.
Each instance file also identifies the framework's conclusion with the hand-proven cell
(`outcome_DupocBot_vs_CupodBot` at its pad; `red_cell` at fuel 2).
| replace `dlen` by `0` in `LenProvableV` | `guard_fits` becomes trivial and `lower_bound_dlen_proof_lenGödel_fbound` (M1 gate) fails |

## 5. What this audit does NOT establish

* That `Dupoc k` (a number) is the engine's `DupocBot k`. That is a separate theorem family
  (T2-AGENT: `playsProof_evalGraph`, `AgentConverse`), conditional on the two box notions
  agreeing; the red cell does not use it and does not need it. The reader compares T2 with
  `Bots/DupocBot.lean` by eye: `.search k (.plays .opp .self C) (.const C) (.const D)`.
* That the evaluator (T5) matches Critch's prose. It is a definition; §3.4 (truth equation) and
  the negative controls are the evidence it does what its clauses say.
* Anything about budgets beyond "every `k`": the cell needs no Löb argument, no expansion
  function, no U10. This is why it is the anchor result.

## 6. Repeat for the next results

Same table for `dupoc_self_coop_unconditional` (adds T9 `BoundedInnerNec`/U10 — no longer
trusted, a theorem — and the fixed-point family `psi`) and for `pblt_unconditional`. Their
negative controls: `¬ EvalGraph n (Dupoc k) (Dupoc k) (Dupoc k) 1` for large `k`.
