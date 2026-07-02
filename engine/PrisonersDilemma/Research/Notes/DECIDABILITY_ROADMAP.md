# Decidability Roadmap — decidable `Provable`, computable `eval`, ZERO axioms

**Goal.** Make `Provable k φ` decidable by a computable `D` with `D k φ = true ↔ Provable k φ`.
Payoffs (all from this ONE lever): `proofSearch := D` ⇒ **`eval` computable** (the project crux);
`search_f` with the positive premise `D k guard = false` becomes typeable AND sound (both walls of
`atom_complete_false_guard` fall) ⇒ **ZERO project axioms**; concrete outcomes become `by decide`;
`evalC` scaffolding retires. Precondition established 2026-07-01: PBLT is already a theorem
(`INTERNALIZATION_ROADMAP.md`), so the Löb side is constructor-backed — the only remaining blockers
to decidability are the cost model (unpaid cuts) and the one axiom (which this project removes).

---

## The two routes, honestly compared

### Route A — cut-elimination / analytic calculus (keep the current cost model)

Add a sequent-style analytic calculus for the bounded-GL-with-`.diag` fragment, prove it equivalent
to `Provable` (= cut admissibility), get decidability from terminating proof search over the finite
Fischer–Ladner closure.

- **Pro:** the existing engine is untouched — purely additive; all current proofs stand verbatim.
- **Pro:** the Löb rule is known NOT to block it (GL is decidable; Sambin–Valentini cut-free calculus;
  controversy resolved by Goré–Ramanayake; a mechanization of pure-GL cut-elimination exists in
  Rocq/Coq — and is itself a multi-thousand-line project for PURE GL).
- **Con (decisive):** our system is NOT pure GL. Completeness must cover ~20 rules including the
  bespoke engine-transparency rules (`searchBranch`, `searchThenSearch_t`, `botSearchStep`,
  `iteBranchSearch_t`, `weakenImpl`, …) and the eval-tied atom layer — every one needs cut-permutation
  cases with NO literature coverage. This is genuine open-ended proof-theory research; realistic risk
  of stalling on a single bespoke rule's permutation case months in.
- **Con (readability):** you end with TWO proof systems (declarative + analytic) plus a large
  equivalence proof, kept in sync forever. The engine's semantics gets HARDER to explain, not easier.
- **Con (doesn't finish the job alone):** even with the calculus, wiring `D` into `search_f`, the
  eval↔D stratification, and the axiom deletion is still ahead — i.e., most of Route B's endgame work
  ON TOP of the calculus.

### Route B — transcript-length accounting (make the cost model literal) ★ RECOMMENDED

Change `Provable`'s budget semantics from conclusion-size gates to CUMULATIVE (transcript) cost:
each rule ADDS its premises' costs plus its own conclusion's character size. Then `{proofs of cost
≤ k}` is genuinely FINITE (engine formulas of bounded size are finitely many — every numeral pays
`log2`, the constructor alphabet is finite; the toy counterexample in `MN1_decidable.lean` does NOT
apply to the engine: its atoms cost 1 with unbounded codes, ours pay). Decidability = bounded search,
no cut-elimination theorem needed — the research wall dissolves into (large) engineering.

- **Pro (kills the research risk):** enumeration is honestly finite; the only *theory* work is
  re-balancing the Löb chain (sketched below — it closes; T0 verifies).
- **Pro (readability & faithfulness — the user's stated priority):** ONE system, ONE cost model, and
  it is CRITCH'S model — "`k` means characters of proof transcript" becomes literally true. The paper
  story simplifies; a reviewer's mental model finally matches the code. The current model's honest
  awkwardness ("budget gates line widths, not the transcript") disappears.
- **Pro (the engine is already half-way there):** the atom layer is ALREADY transcript-style —
  `PlaysProof` carries cumulative per-step costs and `atom_cost fuel = c_leaf + (c_node + c_guard
  fuel)·fuel`. Only `Derivation.size := conclusion.size` and the `Provable` gates are conclusion-cost.
  Route B makes the engine INTERNALLY CONSISTENT, not alien.
- **Pro (working template for the hardest part):** the decider `D` is `decGuard`/`evalC` extended
  from the certificate fragment to all rules, with the SAME fuel-stratified eval↔D mutual recursion
  already proven sound in `ComputableEval/`.
- **Con (the grind):** every size side-condition and omega block is re-derived. Measured blast:
  ~100 `.size ≤` sites (BaseTheorems 30, Derivation 14, JustBot 22, PrudentBot 18, Dupoc/Cupod/Troll
  12, ComputableEval 5) and ~100 omega blocks across ~10 files. Mechanical, compiler-enumerated,
  but weeks of it. `bloeb_engine`'s side-conditions get re-done (its STRUCTURE survives).
- **Con (one real design risk, front-loaded):** the Löb chain's subscript balancing changes — see T0.

**RECOMMENDATION: Route B.** It converts an open research problem into a charted refactor, it
IMPROVES readability and Critch-faithfulness (Route A degrades both), the engine's atom layer already
uses this accounting, and Route A would still require most of Route B's endgame anyway. Route A is
right only if "never touch existing proofs" is paramount — explicitly not the constraint here.

---

## Route B — frozen design sketch (to validate in T0)

1. **`Provable` stays a `Prop`-inductive** (no Type-level proof terms needed for the DEFINITION):
   rules change from `(conclusion).size ≤ k` gates to ADDITIVE budgets, e.g.
   `app : Provable m₁ (.impl φ α) → Provable m₂ φ → m₁ + m₂ + (α.size + 1) ≤ k → Provable k α`.
   Every rule pays: (sum of premise budgets) + (its conclusion's character size). `Derivation.size`
   becomes tree/transcript cost (or `Derivation` collapses into `Provable` — decide in T0).
   The decider is a SEPARATE computable search function (decGuard pattern), proven `↔ Provable` after.
2. **Two new sound rules the re-balanced Löb chain needs:**
   - `boxMono` (upward): `□_a φ → □_b φ` for `a ≤ b` — sound (a ≤a-cost proof is a ≤b-cost proof).
   - additive `axKf`: `□_a(φ→α) → (□_b φ → □_{a+b+c} α)` — Critch's Implication Distribution.
3. **The re-balanced chain (Critch §5 proper, now WITH the g ≺ f dance):** diag subscript `g(k)`
   STRICTLY BELOW `f k`, because under transcript cost the fixpoint ψ's proof CONTAINS the premise's
   proof, so `□`-ing ψ needs subscript ≥ ψ's proof cost. THE SAVING FACT (why this closes for us):
   the consumers' tight Löb premises have O(log k) TRANSCRIPTS — `dupoc_loeb_premise` is ONE
   `searchBranch` leaf (≈ 5·log2 k + 33 chars); the `mutual_loeb` premises are a handful of steps,
   each O(log k). So ψ's proof cost is O(log k), `g, h := c·log k` work, the box on the target grows
   to `g + h + O(log k) ≤ f k` via upward `boxMono`, and the premise composes. All conditions stay
   `A·log2 k + B ≤ k` — same `linear_log2_add_le`/omega discharge style as today, more conditions.
4. **The decider `D`:** extend `decGuard` from {plays, impl-weaken} to all rules — bounded search
   over the (finite) formulas of size ≤ k and rule applications within the remaining budget; mutual
   with computable `eval` on decreasing FUEL (the evalC stratification). Prove `D k φ = true ↔
   Provable k φ`: soundness easy (search only applies real rules); completeness = the enumeration
   bound (every ≤k-cost proof is found — this is where cumulative cost pays off: the search space IS
   finite). The fuel↔budget bridge for plays-atoms is `atom_cost` (already linear, invertible enough).
5. **Endgame:** `proofSearch := D` (eval computable); `search_f` constructor with premise
   `D k guard = false` (positive, sound by D's completeness — Wall 2 dead); prove
   `atom_complete_false_guard` as a THEOREM; delete it. **ZERO project axioms.** Retire `evalC` to
   historical; add `by decide`/`#eval` outcome demos.

## Milestones (kill-criteria first, as with the internalization)

- **T0 — design freeze + kill spike (1–2 sessions).** Mini-engine (I0Design pattern) with additive
  budgets: re-run the bloeb chain with `boxMono`-up + additive `axKf` + `g ≺ f` balancing; verify the
  consumer-premise-O(log k)-transcript assumption suffices. Also freeze: Derivation-vs-Provable merge
  question; exact cost constants. **KILL if the subscript dance cannot close** (then Route A or stop).
- **T1 — accounting refactor (the grind, ~2–3 weeks).** Additive budgets through
  `Derivation`/`Provable`; re-prove BaseTheorems (`Provable_sound`, `proofSearch_monotone` — now
  genuine budget-monotonicity, `mutual_loeb`, `bloeb_engine`/`pblt_engine` with T0's arithmetic).
  Gate: build green; PBLT-as-theorem re-established; outcome theorems' footprints unchanged.
- **T2 — consumer re-derivations (~1 week).** The ~100 omega blocks across bot theorem files.
  Compiler-enumerated; new constants, same shapes.
- **T3 — the decider `D` (~2–3 weeks, the second hard chunk).** decGuard→full-rule bounded search,
  fuel-stratified with computable eval; `D ↔ Provable` (completeness is THE proof of the project).
- **T4 — the endgame (~1 week).** `proofSearch := D`; `search_f`; `atom_complete_false_guard`
  theorem + DELETE. Sweep: all outcome theorems on the 3 Lean-standard axioms. `#eval` demos.
- **T5 — aftermath.** Retire evalC scaffolding; docs (CLAUDE.md crux → RESOLVED); paper notes.

**Total: ~7–10 weeks focused.** Risks ranked: (1) T0 subscript re-balance (killed cheaply if fatal);
(2) T3 completeness of `D` (fuel↔budget bridge; template exists but the full-rule version is new);
(3) T1/T2 grind volume (mechanical but large — the compiler enumerates every site).

## What it buys

**Zero axioms. Computable `eval`. Literal Critch cost semantics. `by decide` outcome theorems.**
The full "explicit S" endgame — with the readability IMPROVING at each step (one system, one honest
cost model, no analytic/declarative split).
