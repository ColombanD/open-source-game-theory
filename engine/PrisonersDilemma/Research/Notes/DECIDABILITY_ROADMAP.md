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

- **T0 — design freeze + kill spike. ✅ PASSED (2026-07-02).** Spike:
  `Research/Spikes/transcript/T0Transcript.lean`. Mini-engine with fully ADDITIVE budgets (every rule
  pays premise transcripts + its conclusion's size); `Prov_mono` (genuine budget monotonicity) +
  `Prov_sound` + `consistency` all **axiom-free**; `bloeb_transcript` (the full Löb chain, 21 explicit
  side-conditions) **axiom-free**; `pblt_transcript` (kill-criterion: `f = id`, premise transcript
  `≤ P·log2 k + Q`, target size `≤ A·log2 k + B` ⇒ `∃K₀,∀k≥K₀,∃m, Prov m (tgt k)`) closes on the
  3 Lean-standard axioms only. **The subscript dance closes** — Route B is GO.

  **T0 freeze decisions (binding for T1):**
  1. **All budgets are multiples of one O(log k) unit** `W := pm + |tgt| + log2 k + 8`. Working
     assignment (generous, omega-verified): diag subscript `g := 1024·W`; box stages
     `n₁, n₃, n₄, n₅ := 32W, 2048W, 2048W, 8192W`; ψ's whole proof transcript `c₁₃ = 768·W ≤ g`
     (THE crux condition — g absorbs the fixpoint's own proof); final transcript `m = 2048·W`. The
     ONLY headroom condition is `8192·W ≤ k`, discharged by `linear_log2_add_le
     (8192·(P+A+1)) (8192·(Q+B+8))` — same consumer-facing shape as today's `pblt_engine_id`.
  2. **`diagF`/`diagB` keep the tight-Löb gate AND charge its transcript** (`pm + |concl| ≤ k`).
     Conservative (preserves the CIMCIC/DIMCID/Exclusion invariants the same way as now) and the
     chain still closes because consumer premises have O(log k) transcripts. ONE signature change vs.
     the current engine rules: the gate premise's box subscript is the FREE `fb` (= f k, the
     consumer's premise subscript), not `g` — under transcript cost `g ≺ f` strictly, so the gate
     can no longer be stated at `g`. Sound arms stay identity.
  3. **`boxMono` is an OBJECT-formula rule** `⊢ □_a φ → □_b φ` (a ≤ b), sound via `Prov_mono` —
     upward subscript weakening, the piece the conclusion-cost model never needed.
  4. **`axKf` goes additive**: gate `a + b + |α| ≤ c` for conclusion `□_a(φ→α) → (□_b φ → □_c α)`;
     its soundness arm is EXACTLY `Prov.app` (Critch's Implication Distribution, now honest).
  5. **`boxIntro`** pays the inner transcript: premises `Prov m φ`, `m ≤ g`, `m + |□_g φ| ≤ k`
     (subscript = inner budget; linear E). **`four`** gate: `a + |□_a φ| ≤ b`.
  6. **Derivation/Provable merge: DON'T.** The atom layer (`Derivation`/`PlaysProof` with cumulative
     `atom_cost`) is already transcript-style — keep it; T1 only converts `Provable`'s gates from
     conclusion-size to additive and re-balances `bloeb_engine` with T0's arithmetic.
- **T1 — accounting refactor. ✅ DONE (2026-07-02), T2 absorbed.** Build green (3144 jobs);
  outcome-theorem axiom footprints UNCHANGED (Dupoc/Cupod on 3 Lean-standard only;
  Prudent/JustBot + `atom_complete_false_guard`). What shipped:
  - `Derivation.size` is now STRUCTURAL (leaves = conclusion; `modusPonens`/`hypSyll` pay both
    subtrees + conclusion — the paid-cut property at the `Derivation` level).
  - Every `Provable` rule additive: `weakenImpl`/`atomBoxImpl`/`boxIntro`/`implTrans` (cut-size
    gate DROPPED — premises pay it)/`app` (split `m₁ m₂`)/`impS2`; `axK`+`axKf` in the
    three-subscript form `□_a(φ→α) → (□_b φ → □_c α)` gated `a+b+|α| ≤ c` (sound arm = `app`);
    `box4` as `□_a φ → □_b (□_a φ)` gated `a + |□_a φ| ≤ b`; `diagF`/`diagB` gate at the FREE
    `fb` and charged; NEW `boxMono` (appended LAST — positional-rec prefix stable);
    `searchThenSearch_t` premise at its OWN transcript `m ≤ k₂` (NOT the inner source literal —
    charging `k₂` would sink the chain; soundness lifts via `Provable_mono`).
  - BaseTheorems: NEW `Provable_mono` (genuine budget monotonicity, by `cases` — every rule
    self-weakens); `proofSearch_monotone` = 1-line corollary; `bloeb_engine` = T0's 21-condition
    transcript chain; `pblt_engine` takes the premise at its honest `pm k` (do NOT weaken to k!)
    + ONE headroom bound `8192·W ≤ f k`; `pblt_engine_id` (uniform `100·log2 k + 1000` bounds);
    `mutual_loeb` = the LOWERED-fb two-leg premise (T0 §6); NEW `mutual_pblt_engine_id` (the
    cross-bot closer — consumers pass the two O(log k) transparency legs directly).
  - Consumers: all `*_loeb_premise` lemmas are now TRANSCRIPT-TIGHT (`Provable (c·log2 k + C)`,
    unconditional — no `K₀` eventuality; `searchThenSearch` premises need `atom_cost ≤ k`, e.g.
    `atom_cost 2 = 7`, `atom_cost 3 = 10`, `atom_cost 4 = 17`); PrudentBot×Dupoc and JustBot's
    two mutual sites now go through `mutual_pblt_engine_id` at SAME-k bots (old `loeb_premise_provable`
    same-subscript assemblies deleted); `decGuard`'s `.impl` case consults the consequent at the
    REDUCED budget `k − |φ'→ψ|`.
  - NOT touched: atom layer (`PlaysProof`/`AtomProvable`/`atom_cost`, incl. `search_t`'s
    `c_guard`-only charge), `proofSearch := decide`, `Formula.interp`. Reflection/* (historical,
    not root-imported) not rebuilt.
- **T3 — the decider `D` (~2–3 weeks, the second hard chunk).** decGuard→full-rule bounded search,
  fuel-stratified with computable eval; `D ↔ Provable` (completeness is THE proof of the project).
  - **T3.0 — decidability kill-spike. ✅ PASSED (2026-07-02).**
    `Research/Spikes/transcript/T3DeciderMini.lean`: `Prov` is DECIDABLE for the full mini
    additive rule set — Löb rules INCLUDED — on the 3 Lean-standard axioms. `decP` (computable
    backward search) + `decP_sound` + `decP_complete` ⇒ `instance : Decidable (Prov k φ)`;
    `#eval`-computed consistency. Validated method (binding for T3.1+):
    1. **fuel = budget suffices**: every rule's premise budgets are STRICTLY below the
       conclusion's (additive gates + `size_pos`), so the search recurses structurally on fuel
       with `fuel := k` — no well-founded-recursion gymnastics.
    2. **`prov_size` (paid conclusions) bounds the space**: cut formulas (`app`/`implTrans`/
       `impS2`) range over `enumF k` (finite, since every numeral — atom codes included —
       pays `log2`); the `diagF`/`diagB` gate's free `fb` is paid by the gate formula, so
       `fb < 2^(k+2)` — the Löb rules do NOT break decidability (bounded-GL analogue).
    3. **Maximal-budget instantiation**: per rule, check premises at the largest admissible
       budget (justified by `Prov_mono`) — kills the budget-split blowup except one linear
       split point for two-premise rules.
    4. Lean plumbing that worked: one NAMED checker per rule (small match equations; `split at`
       clean), recursive checkers take the smaller-fuel search as an explicit callback;
       completeness by induction on `Prov` in the form `∀ fuel K, m ≤ K → K ≤ fuel → decP…`.
  - **T3.1 — engine decider, atom-oracle-relative. ✅ PASSED (2026-07-02).**
    `Research/Spikes/transcript/T31EngineDecider.lean` (3 Lean-standard axioms; notably NOT
    `atom_complete_false_guard`): `decProv O` — backward search over ALL 15 `Provable`
    constructors, incl. `struct` via its own `Derivation` search `decDeriv` (8 rules; leaves =
    syntactic shape-matching against the transparency conclusions, `DecidableEq`-checked) —
    sound and complete relative to an atom oracle `O` (`OracleSound`/`OracleComplete` for
    `AtomProvable`). Headline: `provableRelDecidable` — ANY correct atom decision procedure
    makes the engine's full `Provable` decidable. New ingredients over T3.0:
    * mutual `enumProg`/`enumFormula` + joint completeness (actions finite, numerals pay log2);
    * **atoms are NOT size-paid** — `Provable.atom`'s budget bounds eval-steps, not characters.
      Sharp replacement: `provable_size_or_atom` (size-paid OR an atom certificate) and
      `provable_impl_size` (`AtomProvable` never concludes an `.impl`), which re-bounds every
      cut formula THROUGH its impl-premise — cuts still range over `enumFormula k`;
    * `axK`'s inner subscript searched over `range (c+1)` (gate `a+b+|α| ≤ c` bounds it);
      `searchThenSearch_t`'s inner premise at `min k₂ (k − |concl|)`; `atomProvable_pos`
      (certificates cost ≥ 1) keeps budget-0 empty.
  - **T3.2 (the remaining hard part)**: decide `AtomProvable` — `search_t`'s guard premise
    sits at a SOURCE-LITERAL budget (up to 2^k, not < k), so plays-atoms need the
    fuel-stratified evalC-style evaluator, now with `decProv` available for guards; all
    `PlaysProof`/`Provable` rules are POSITIVE (no `search_f` — the deleted axiom's direction),
    so a least-fixpoint computation over the finite query universe
    `{(m, ψ) : ψ.size ≤ m ≤ 2^…}` is the fallback shape. Then T4 wires
    `proofSearch := decProv O` and deletes the last axiom.
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
