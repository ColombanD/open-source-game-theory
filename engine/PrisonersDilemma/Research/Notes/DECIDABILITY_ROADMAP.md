# Decidability Roadmap — decidable `Provable`, computable `eval`, ZERO axioms

---

## ⚑ STATUS (2026-07-03, end of the T3/T4 arc) — read this first

Everything below T4.1b is DONE, on Lean's 3 standard axioms, no sorries:

| Result | Where |
|---|---|
| ZERO project axioms (the last one was proven INCONSISTENT and repaired) | `Derivation.lean`, `T32Inconsistency.lean`, `BaseTheorems.sound_upto` |
| Transcript-cumulative costs (Critch's literal model), staggered-budget outcome recoveries, `PrudentBot2` (bounded PA+1) | T1/T2, T3.2b |
| `Provable k φ ↔ ∃ fuel, decFull fuel k φ = true` — ABSOLUTE semidecidability, verified computable enumerator | `Decidability/T31EngineDecider.lean` §7–8 |
| `evalG` — computable evaluation of search bots, sound commits in BOTH guard polarities; `#eval` demos run | `Decidability/T31EngineDecider.lean` §9 |
| `ProvableG G` gate-parametric strata; `Provable ↔ ∃N, ProvableB N`; `CutRelevance` stated | `Decidability/T42ProvableB.lean` |
| MODESTY: the whole zoo's substitution dynamics live in a finite universe (each bot `by rfl`) | `Decidability/T43ModestUniverse.lean` |
| `decB` — the modest-bounded decider, SOUND and ∃-fuel COMPLETE for the stratum | `Decidability/T44BoundedDecider.lean` |
| The certificate layer's read interface (`CertRead`, congruence, finite read-set) | `Decidability/T45CertReads.lean` |
| The global query universe (non-circular budget ceiling `R = max k₀ (max L₀ N)`) | `Decidability/T46LogicSpace.lean` |
| **`Decidable (ProvableG (modestGate N) k φ)`** — fuel bound `\|SL\|`, countP stabilization | `Decidability/T47Stabilization.lean` |

**T5 consolidation (2026-07-03): PROMOTED.** The chain above moved from
`Research/Spikes/transcript/` to `PrisonersDilemma/Decidability/` (milestone names and
namespaces kept — historical entries below cite the old paths), is wired into the default
`lake build` via the umbrella `PrisonersDilemma/Decidability.lean` (which re-exports the
headline API under `PD.Decidability`), and `ComputableEval/Computable.lean`'s header now
marks `evalC` HISTORICAL/superseded-by-`evalG`. Deferred to a future session: rewiring
`proofSearch` (its right form depends on the conjecture below) and `by decide` outcome demos.

**T4.1b attack — the full 2026-07-03 arc: `Research/Notes/CUT_RELEVANCE.md`** (§5b has the
milestone ledger; read §5c–§5g before touching anything). Executive summary:

* **The judgment-local program is CLOSED by three kernel-checked refutations**
  (`T48CutRelevance.lean` §9–§11): the tame trichotomy was vacuous (retracted); linked
  variants are FALSE at box contents, guarded tails, and unguarded heads (`deadJ`, the
  dead-implication generator). No pairwise judgment invariant can carry the conjecture.
* **The conjecture REDUCES to atom modesty**: C0's literal bound + the compression
  ceiling (`T49 §8`: budget-`k` boxes have subscripts `< 2^k`) + backward-tameness leave
  ONE escalation channel — cite budgets fueled by cut atoms' fresh programs. The literal
  half is free at `N₀ := 2^max(k, maxLitF φ) + maxLitF φ`.
* **The TREE SUBSTRATE + EXTRACTION MACHINE** (`T49TreeSubstrate.lean`): `ProvT` mirror
  triple with `Provable k φ ↔ Nonempty (ProvT k φ)`; `gateOK` (one tree's cut diet);
  `tree_cutRelevance : TreeCutRelevance N₀ → CutRelevance N₀` — the official reduction.
  `boxInvGo`: a fueled stack machine extracting box/diag contents, CORRECT BY
  CONSTRUCTION, `#eval`-running (incl. through Löb fixpoint pairs). Kernel-checked:
  extraction is weight-conserving, diet-preserving (unconditionally — `litGate` and
  `modestGate` are box-content-closed), depth-conserving, and TOTAL with closed-form
  fuel on the contraction-free fragment (`boxInv_total_of_freeS2`).
* **THE NORMALIZATION THEOREM — PROVEN (2026-07-03, `boxInv_total`, T49 §19–21)**:
  the extraction machine weakly normalizes on every well-typed box judgment,
  UNCONDITIONALLY (no contraction-freedom hypothesis) — boundedness defuses the
  Löb/Y-combinator (`.diag` is a NEGATIVE recursive type; the budget-pinned guard is
  Nakano's ▷). Proof: Tait computability `Good` on lex `(k, μ, phase)` with
  `μ(box) = 0` + the fundamental lemma (contraction free by hypothesis reuse; Löb case
  by fuel monotonicity; modal leaves by cumulative determinism). Plausibly the first
  normalization theorem for a bounded provability logic —
  `Research/Notes/BOUNDED_LOB_NORMALIZATION.md` is the paper-grade record. The total
  computable extractor `boxInvT` + `box_inversion_diet` (diet-controlled constructive
  box inversion) are the assembly interface. REMAINING to CutRelevance (assembly, no
  open math): the excisor/crossing over general cores, `TreeModestRelevance` for zoo
  roots, plug into T47.

**The ONE remaining open item** is the T4.1b conjecture (`CutRelevance`,
`T42ProvableB.lean`): a computable `N₀` with `Provable k φ → ProvableG (modestGate (N₀ k φ))
k φ`. Given it, `proofSearch` is decidable ⇒ `eval` computable ⇒ outcomes `by decide`. If it
fails, `Provable` is a candidate undecidable bounded-provability predicate. Either resolution
is thesis-grade. (Optional consolidation, T5: promote the spike chain into the engine tree,
wire `proofSearch` to the decided fragment, retire `evalC`.)

---

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
  - **T3.2 — ⚠️ CRITICAL FINDING (2026-07-02): `atom_complete_false_guard` is INCONSISTENT.**
    `Research/Spikes/transcript/T32Inconsistency.lean`: `engine_inconsistent : False` on
    [3 std axioms + atom_complete_false_guard]. Witness = the ANTI-DIAGONAL bot
    `G := .search 100 (.plays .self .self .D) (.const .C) (.const .D)`: guard true ⇒ soundness
    yields a D-play but eval cooperates (contradiction); guard false ⇒ the axiom injects the
    else-certificate at `atom_cost 2 = 7 ≤ 100`, monotonicity lifts it above the guard budget,
    flipping the guard (contradiction). Predates the transcript refactor (all ingredients are
    from the original engine). Everything downstream of the axiom (all of `atom_complete`'s
    users, incl. PrudentBot/JustBot outcomes) is vacuous until repaired.
    The T3.2 decidability analysis had independently arrived at the SAME structural point:
    * UNCHARGED `search_t` (cost = `c_guard` only) leaves the guard-nesting rank of
      certificates uncomputable (no fuel bound for a complete atom decider), AND permits the
      inconsistency (else-facts fit under the budgets they refute).
    * The **CHARGED atom model** is both the repair and the decidability enabler:
      then-certificates pay the guard PROOF's transcript (Critch-faithful — PA proofs embed
      their sub-proofs; only possible post-PBLT-internalization, since the Löb-fixpoint guards
      now have finite O(log k) non-atomic proofs); else-certificates must EXCEED the guard
      budget they refute (so monotonicity can never lift them back under it).
    * The `search_f` endgame needs a stratified decider (`search_f`'s premise = a Bool fact
      about an ALREADY-DEFINED total decider, keeping positivity); the naive "one D deciding
      the system containing D-facts" is a non-monotone fixpoint (more provable ⇒ fewer
      else-certs) — the anti-diagonal bot is exactly its paradox.
    REVISED PLAN: T3.2a — redesign the atom layer on the charged model (search_t pays the
    guard proof transcript m' with m' ≤ kg; delete the axiom, whose role is taken by a
    consistent charged `search_f`/eval-completeness story); T3.2b — re-prove atom_complete
    (cost now program-dependent) + consumer sweep (T1-style); T3.2c — the atom decider
    (budget now strictly decreases through search_t: the T3.0/T3.1 method applies directly).
    Then T4 as planned.
  - **T3.2a STEP 1 — ✅ SHIPPED (2026-07-02, build green).** `PlaysProof.search_f` (refutation
    premise `Provable m (.neg guard)` + the cost FLOOR: pays the full failed budget `k`) and
    `Provable.atomNeg` (refute a play-atom from a certificate of the actual play — eval
    determinism) are IN; soundness restructured as `BaseTheorems.sound_upto` (joint, by STRONG
    INDUCTION ON THE BUDGET — the floor makes the hypothetical guard proof strictly smaller,
    which is what lets `search_f` be sounded at all); `Exclusion.no_pp_else` /
    `no_provable_forbidden` cost-qualified (the exclusion holds exactly WITHIN the guard's own
    budget — the unqualified forms were the inconsistent axiom's shape). Public soundness API
    unchanged. The axiom still present (still inconsistent) — deletion is STEP 2.
  - **T3.2a STEP 2 — ⚠️ NOT MECHANICAL: outcome theorems CHANGE SEMANTICALLY.** Deleting the
    axiom requires restating `atom_complete` per-site (certificates constructed with
    `search_t`/`search_f`), and the FLOOR forces honest game-theory changes wherever a bot
    consumes ANOTHER bot's else-play within the same budget: the else-certificate costs
    > that bot's guard budget. Concretely (analysis 2026-07-02):
    * `DupocBot_vs_DBot` (and OBot/EBot probes): DBot's play crosses Dupoc's FAILED search
      (probe vs `.bot DefectBot`), so "DBot plays C vs Dupoc_k" is certifiable only ABOVE k —
      Dupoc_k's guard at k cannot see it ⇒ same-k (C,C) does NOT survive; needs staggered
      budgets or a NEW refutation-transparency rule (an `iteBranchNeg` reading the probe's
      refutation at Derivation level — design open).
    * `outcome_PrudentBot_vs_DupocBot` / JustBot×{Prudent,Dupoc}: prudence facts are
      else-plays of the partner — same-k cooperation needs restating (e.g. PrudentBot_{f k}
      vs DupocBot_k with f k ≥ k + O(log k)); this matches Critch (his PrudentBot/FairBot
      pairs carry budget-function conditions; the same-k theorems were artifacts of the
      unsound axiom).
    * Search-free-probe results (PrudentBot×MirrorBot, Dupoc/Cupod self-play & vs
      const/sim bots) survive as-is (their prudence/probe facts have ordinary certificates).
    DECISION (Colomban, 2026-07-02): staggered budgets (recommendation).
  - **T3.2a STEP 2 — ✅ SHIPPED (2026-07-03, build green): THE AXIOM IS DELETED — ZERO
    PROJECT AXIOMS.** Every surviving theorem (`#print axioms`) rests on `[propext,
    Classical.choice, Quot.sound]` only. What shipped:
    * `Axioms.lean` declares NOTHING (historical record); `T32Inconsistency.lean` restated
      hypothesis-relative (the machine-checked reason the axiom had to go).
    * NEW `Derivation.eqNeg` (refute structural identity of distinct programs — feeds
      `search_f` for failed `.eq` guards).
    * `atom_complete` DELETED; replaced by the constructive toolkit
      (`atom_complete_searchfree` at `3^fuel`; `atom_search_t_top`/`_bot_top` at
      `log2 k + 3/4`; `atom_search_f_top`/`_bot_top` at the floor `m + k + 2/3`);
      `proofSearch_complete_plays` search-free-qualified; `atom_box_provable_impl_sound`
      takes the certificate; `decGuard`'s plays-true case restricted to the search-free
      fragment at `3^(n+1)` (search-crossing commits await the full decider, T3.2c).
    * SURVIVING (re-certified by hand where needed): Dupoc/Cupod self-play & vs
      const/sim bots, Dupoc×TitForTat (hand `ite_t∘sim∘search_t` certificate!),
      Dupoc×OBot (D,D), PrudentBot×MirrorBot & ×botMirror (search-free prudence, new
      constants 27/81), CupodTroll×Cupod (fired `.eq`), **CupodTroll×Dupoc STAGGERED**
      (`j`/`k` with `|neg(eq)| + j + 2 ≤ k` — the first staggered-budget theorem, via an
      `eqNeg`+`search_f` certificate), JustBot self-play & ×TitForTat & ×Dupoc & ×OBot
      (hand `search_t` certificates, `log2 k + 3 ≤ k` thresholds).
    * RETIRED with tombstones (axiom artifacts, honestly unprovable at same-`k` — the
      self-referential floor): Dupoc×{DBot, EBot}, Cupod×OBot, PrudentBot×{EBot, Dupoc,
      SELF}, JustBot×{DBot, CupodTroll, EBot, PrudentBot}. PrudentBot's same-`k` prudence
      is self-referentially impossible — rediscovering why MIRI's PrudentBot checks
      prudence in PA+1. T3.2b = staggered restatements (two-budget mutual wrapper;
      two-tier PrudentBot).
  - **T3.2b — ✅ CORE SHIPPED (2026-07-03, build green): the headline cross-bot cooperations
    are RECOVERED with staggered budgets.**
    * `searchThenSearch_t` now CITES its inner search (`c_guard k₂`) instead of charging the
      premise transcript — Critch-faithful (like `search_t`; positive premise, no floor
      needed), and what keeps the staggered legs' transcripts O(log k). The staggering
      constraint still bites through `m ≤ k₂` (same-`k` remains honestly dead).
    * NEW `BaseTheorems.mutual_pblt_engine_staggered` (leg 1's box at `kP k ≥ k`, leg 2's at
      `k`; same internal chain) + `log2_le_self` / `log2_stagger_le` helpers.
    * **`outcome_PrudentBot_vs_DupocBot`**: `PrudentBot (2k+64)` vs `DupocBot k` → (C,C) —
      `prudence_dupoc` = the floored `search_f`-over-`atomNeg` certificate
      (`k + log2 k + 15`), affordable in the bigger inner literal.
    * **`outcome_JustBot_vs_PrudentBot`**: `JustBot k` vs `PrudentBot (2k+64)` → (C,C) —
      `prudence_botdupoc` (bot-wrapped floor, `k + log2 k + 17`) + `justbot_prudence`
      (JustBot's own floored defection, `k + log2 k + 16`, consumed by PrudentBot's outer
      budget).
    All on the 3 Lean-standard axioms. T3.2b TAIL also SHIPPED (2026-07-03): `PrudentBot2`
    (two-tier, the bounded PA+1) + `outcome_PrudentBot2_self` (k, 4k+100); staggered
    `outcome_JustBot_vs_CupodTrollBot` (∀j, no eventuality); docs refreshed. Remaining:
    honest (D,·)-type outcomes for the retired probe pairs (need the ¬Provable side).
  - **T3.2c PART 1 — ✅ SHIPPED (2026-07-03): `Provable` is SEMIDECIDABLE relative to the
    atom layer, by a computable enumerator.** `Research/Spikes/transcript/T31EngineDecider.lean`
    (green, 3 std axioms): the full backward-search `decProv O` now covers ALL 16 `Provable`
    rules (incl. `atomNeg` via the oracle, `eqNeg` in `decDeriv`, and the CITE-model
    `searchThenSearch_t`) with
    * `decProv_sound` — every hit at every fuel is a real derivation;
    * `decProv_mono` — fuel monotonicity;
    * `decProv_complete` — every derivation is FOUND at some fuel (∃-fuel form: the
      `∀ fuel ≥ K` discipline is impossible under the CITE model, since inner premises live
      at source literals unbounded by the conclusion's budget — this is the precise residual
      of the decidability question);
    * **`decProv_iff`**: `OracleSound O → OracleComplete O →
      (Provable k φ ↔ ∃ fuel, decProv O fuel k φ = true)`.
  - **T3.2c PART 2 — ✅ SHIPPED (2026-07-03): `Provable` is ABSOLUTELY SEMIDECIDABLE — no
    oracle, no hypothesis.** Same spike file, §7–8 (green, 3 std axioms). The knot untied by
    fuel stratification, plain structural recursion:
    * `decCertG D fuel b me oppo body a` — cost-tracking cert search over the program body
      (guards consult `D`: the true-guard CITEs `D kg guard`, the false-guard sweeps
      refutation budgets `m ∈ range (b+1)` and pays the `m + kg` floor — exactly `search_f`);
    * `certOG D fuel` — the plays-atom oracle from it; and the tie-off
      **`decFull : Nat → Nat → Formula → Bool`**, `decFull (fuel+1) = decProv (certOG
      (decFull fuel) fuel) (fuel+1)` — each fuel level feeds the previous level in as the
      atom oracle. Fully computable, total.
    * `decFull_sound` — every hit is a real derivation (via `decProv_sound` + `certOG_sound`);
    * `decCertG_mono2`/`certOG_mono2`/`decFull_mono`/`decFull_le_inner` — the monotonicity
      lattice (oracle-pointwise + fuel) that lets sub-derivations found at different fuels be
      lifted to a common level;
    * `decFull_complete` — joint `Provable.rec` over all three layers (9 `PlaysProof` arms +
      `mk` + 16 `Provable` arms; motives `∃ F, decCertG (decFull F) F … = true` etc.);
    * **`Provable_iff_decFull : Provable k φ ↔ ∃ fuel, decFull fuel k φ = true`** — the
      engine's bounded provability, Löb fixpoints and floored else-certificates included, is
      r.e. with a verified enumerator, on `[propext, Classical.choice, Quot.sound]` only.
    REMAINING (T4): the OPEN question — a computable fuel bound as a function of `(k, φ)`
    (query-universe finiteness across guard hops; the ∃-fuel cannot currently be bounded
    because cited premises live at source literals) — full decidability, `proofSearch := D`,
    computable `eval`, `by decide` outcomes.
- **T4 — the endgame: from r.e. to decidable.** Remaining open item: a computable fuel bound
  `f(k, φ)` with `Provable k φ ↔ decFull (f k φ) k φ = true`. Then `proofSearch := decFull ∘ f`
  is computable, `eval` computable, outcomes `by decide`.
  - **T4.0 — ✅ SHIPPED (2026-07-03): `evalG` — computable evaluation, both guard polarities,
    search bots RUN.** Spike §9. A 3-valued guard is sound in BOTH directions with no axiom:
    `some true` from `decFull` (soundness), `some false` from a DERIVABLE refutation
    `Provable m (.neg φ)` — soundness + consistency exclude `Provable k φ` at EVERY budget
    (the honest replacement for what the deleted axiom faked). `evalG G` = `eval`'s recursion
    with the 3-valued guard, parametric in `G`; `GuardSound G → evalG` commits are `eval`'s
    answers AT THE SAME FUEL (`evalG_sound`, sharper than `evalC`'s `∃N`). Instances:
    `guardFull` (decFull both sides; `guardFull_converges_pos/_neg` = `none` escapable on the
    whole r.e. fragment) and `guardFast` (goal-directed cert search, `Provable.atomNeg`-style
    refutations; what makes `#eval` practical). Demos (printed, certified by
    `outcomeG_sound`): Mirror-style search bot vs CooperateBot `some (C,C)`, vs DefectBot
    `some (D,D)`, self-play `none` — the Löb boundary, computably. This SUPERSEDES `evalC`'s
    role (search-crossing commits both sides vs. evalC's search-free true-commits).
  - **T4.1a — ✅ SHIPPED (2026-07-03): the bounded-literal world is DECIDABLE — least-fixpoint
    stabilization beats budget jumps.** `Research/Spikes/transcript/T4QueryBound.lean`
    (self-contained mini, no engine imports, 3 std axioms). The minimal system exhibiting the
    engine's residual: mutual `Good`/`Bad` (≈ `Provable`/refutation layer) over programs with
    `sr kg g p q` nodes whose guard is CITED at its own literal budget `kg` — legal with
    `kg ≫ k` (only `log2 kg + 2` paid), so T3.0's fuel=budget method is UNAVAILABLE. Yet:
    `Good k p ↔ decN (Qs p k).length k p true = true` (`Good_iff_decN`), hence
    `Decidable (Good k p)` (`decideGood`). Method (the template for the engine's `ProvableB`):
    step operator `stepF` over approximations + soundness + chain monotonicity + ∃-fuel
    completeness + finite query space `Qs` = (budgets ≤ max(k, source literals)) × subterm
    closure × polarity + closure lemmas (`stepF` at an in-space query reads only in-space
    queries — the false side pays its floor LINEARLY, so only source literals are ever
    jumped to) + `countP` pigeonhole (the monotone chain on the finite Bool-lattice must
    stabilize within `|Qs|` steps) + agreement propagation. The fuel bound is `|Qs|` —
    computable from the query alone.
  - **T4.1b — the fuel-bound analysis (the remaining open mathematics).** Offender census: budgets along
    a backward search DECREASE at every rule except exactly TWO CITE-model hops, both paying
    only `c_guard = log2+1` for a premise at a SOURCE-LITERAL budget: `search_t`'s guard
    (`decCertG`'s `D kg` slot) and `searchThenSearch_t`'s inner premise (at `k₂`). (`boxIntro`
    and `atomBoxImpl` pay their subscripts LINEARLY — not offenders.) Source literals of the
    original query are a fixed finite set — the danger is exclusively CUT FORMULAS
    (`app`/`implTrans`/`impS2` enumerate any `B` with `size ≤ K`), which can mention fresh
    `.search` programs with literals up to `2^K`; a guard hop into one raises the budget to
    `2^K`, whose cuts reach `2^2^K` — the TOWER. So full decidability reduces to a
    **cut-relevance theorem**: minimal derivations only need cut formulas from a computable
    universe (substitution instances of source syntax + `.diag` sentences + source-bounded
    box subscripts — cf. `bloeb_engine`'s actual cut diet). Given that: budgets range over a
    finite set; cert queries about substitution-grown programs depend only on their
    budget-depth SLICE (finitely many classes); minimal derivations never repeat a query on a
    branch ⇒ depth ≤ |query universe| ⇒ `f(k, φ)`. Fallback if cut-relevance resists: the
    positive-rule least-fixpoint over the sliced universe (all `Provable` rules are positive).
  - **T4.2 — ✅ SHIPPED (2026-07-03): `ProvableB N`, the literal-bounded stratification — the
    conjecture is now a precise engine statement.** `Research/Spikes/transcript/T42ProvableB.lean`
    (green, no sorry; transfer theorems on `[propext, Quot.sound]` only). `maxLitP`/`maxLitF`
    (the literal vocabulary); the mutual triple `PlaysProofB/AtomProvableB/ProvableB N`
    mirroring the engine EXACTLY except six gates on the rules whose premises carry material
    absent from their conclusions: `implTrans`/`app`/`impS2` cut formulas (`maxLitF ≤ N`),
    `axK`'s inner subscript and `diagF`/`diagB`'s Löb budget (`≤ N`). (`struct` ungated:
    `Derivation` is size-paid ⇒ literals `< 2^k` automatically.) Shipped: `ProvableB_sound`
    (erase gates), `PlaysProofB_monoN`/`ProvableB_monoN`, and
    **`Provable_iff_exists_ProvableB : Provable k φ ↔ ∃ N, ProvableB N k φ`** (every
    derivation is finitely-cut — max over its own cut diet). `CutRelevance N₀ :=
    ∀ k φ, Provable k φ → ProvableB (N₀ k φ) k φ` is THE T4.1b conjecture;
    `Provable_iff_ProvableB_of_cutRelevance` reduces deciding `Provable` to deciding the
    stratum. Remaining pipeline: (i) the T4.1a stabilization port to `ProvableB` (finite
    query space needs the subst-closure/slice treatment of programs — finite outright for
    "modest" bots whose guards mention `.self`/`.opp` only atomically, i.e. the whole zoo);
    (ii) the conjecture itself.
  - **T4.3 — ✅ SHIPPED (2026-07-03): the MODEST universe — the query space is finite and
    closed under the evaluation dynamics.** `Research/Spikes/transcript/T43ModestUniverse.lean`
    (green, no sorry; step lemmas on `[propext, Quot.sound]`). `closedP/closedF`
    (subst-invariance; `.bot`/`.diag`/`.eq`-RHS frozen by `subst` itself) with
    `substP_id/substF_id`; **`modestP/modestF`** — every substitution-reachable position
    (`.sim` args, `.plays`-atom args in guards) is `.self`/`.opp`/frozen — computable and
    `rfl`-checkable; `subsP/subsF` subterm closure (through guard formulas) with
    transitivity and modesty-inheritance; `playsArgsF` + `playsArgsF_subst` (substituted
    modest atoms resolve to the players or frozen originals). The universe: `certU`
    (bodies) / `players` (roots + frozen subterms) / `guardU` (guards × player pairs), all
    finite lists, with the STEP LEMMAS `step_sim` (new players stay players), `step_search`
    (hops land in `guardU`), `guardU_args` (hop formulas' `.plays` args are players) —
    the `T4QueryBound` in-space closure for real engine programs. THE WHOLE ZOO IS MODEST
    (`MirrorBot`/`DupocBot`/`CupodBot`/`TitForTat`/`PrudentBot`/`PrudentBot2`/`JustBot`,
    each `by rfl`). Remaining for (i), now assembly: the two-sided step operator for
    `ProvableB` over `(budgets ≤ max k N) × (gated enumFormula ∪ guardU-subformulas) ×
    (players² × certU)` + the T4.1a lfp-stabilization verbatim.
  - **T4.4a — ✅ SHIPPED (2026-07-03): `decB`, the modest-bounded step decider, SOUND.**
    `Research/Spikes/transcript/T44BoundedDecider.lean` (green, no sorry; imports the T3.1,
    T4.2, T4.3 spikes — spike oleans build via `lake build <module>`). T4.2 REFACTORED to the
    gate-parametric `ProvableG (G : Formula → Prop)` (gates on the six conclusion-absent
    premise FORMULAS — `axK`/`diag` gate the whole premise, subsuming the subscript);
    `ProvableB N := ProvableG (litGate N)` keeps every T4.2 statement. The DECIDABLE gate is
    `modestGate N B := maxLitF B ≤ N ∧ modestF B` (literal-bounded ⇒ finite hop budgets;
    modest ⇒ cut atoms' cert queries stay in the T4.3 universe). Shipped: `cutOKb` + six
    gated checker variants (`chkITransB`/`chkAppEB`/`chkAxKB`/`chkDiagFEB`/`chkDiagBEB`/
    `chkImpS2EB`) — T3.1's other ten checkers reused VERBATIM; **`stepB N`** (one
    rule-firing pass over an approximation; the atom side runs T3.1's `decCertG` with the
    approximation as guard oracle at fuel `k+1` — cert budgets strictly decrease, so the
    cert layer needs no stabilization of its own); `decB N fuel := stepB N ^[fuel] ⊥`;
    `decCertG_soundG`/`certOG_soundG` (T3.1 cert soundness re-targeted at the gated triple);
    **`decB_sound`**: every hit is a real `ProvableG (modestGate N)` derivation (hence
    `Provable`).
  - **T4.4b — ✅ SHIPPED (2026-07-03): `decB` is COMPLETE — the modest stratum has its own
    verified enumerator.** Same spike, §6–8: `stepB_mono`/`decB_mono` (per-checker, the
    T3.1 `decProv_mono` idiom; the lagged-`certOG` oracle slots lift via `certOG_mono2`);
    `decB_complete` — the 26-arm joint `ProvableG.rec` (cert motive at FIXED fuel `b+1` —
    cert budgets strictly decrease so only the guard-oracle slot grows; SIMPLER than
    `decFull_complete`: checkers consume the approximation at the SAME level, no lagged
    bridge); payoff **`ProvableG_modest_iff_decB`**:
    `ProvableG (modestGate N) k φ ↔ ∃ fuel, decB N fuel k φ = true`.
    Remaining (T4.4c, the LAST assembly step): the formula-side space (gated `enumFormula`
    ∪ `guardU`-subformula closure), the in-space/congruence lemmas (consuming T4.3), and
    the T4.1a countP stabilization converting ∃-fuel into the computable bound
    `|query space|` ⇒ `Decidable (ProvableG (modestGate N) k φ)` for in-space queries —
    unconditional decidability over the zoo's query universe.
  - **T4.4c part 1 — ✅ SHIPPED (2026-07-03): the certificate layer's READ INTERFACE.**
    `Research/Spikes/transcript/T45CertReads.lean` (green, no sorry; on
    `[propext, Quot.sound]`). Every logic-side read of `stepB` strictly decreases the
    budget or lands in a finite family — except the reads hidden inside the imported
    `decCertG`. Now first-class: **`CertRead b me oppo body m ψ`** (budget-indexed
    reachability of oracle consultations — one constructor per consultation site: guard
    cite `(kg, g.subst me oppo)`, refutation sweep `(m ≤ b, .neg (g.subst me oppo))` — and
    per recursion site, overapproximating swept budgets); **`decCertG_congr`** — oracles
    agreeing on the `CertRead`-set produce the SAME Bool at every fuel (induction on fuel,
    `anyCongr` through the sweeps; `certOG_congr` wrapper); **`certRead_mem_guardU`** —
    over the T4.3 modest universe every read formula is a `guardU` member or the `.neg`
    of one (induction on `CertRead` consuming `step_search`/`step_sim`/subterm lemmas).
    The atom layer's read-set is FINITE and the atom side of `stepB` is congruent past it.
    Remaining (part 2): the logic-side space (stratified size bound `Z(b)` over the gated
    base + `guardU` family + its `.neg`s), the 16-checker in-space closure + `stepB`
    congruence, and the countP stabilization ⇒ the fuel bound ⇒ `Decidable`.
  - **T4.4c part 2a — ✅ SHIPPED (2026-07-03): the GLOBAL query universe.**
    `Research/Spikes/transcript/T46LogicSpace.lean` (green, no sorry; on
    `[propext, Quot.sound]`). KEY: the budget ceiling is NON-CIRCULAR — every read either
    strictly decreases the budget or jumps to a guard cite at a LITERAL, and literals come
    from the roots (`≤ L₀`) or `modestGate`-gated cut material (`≤ N`): `LU := max L₀ N`
    bounds every jump, `R := max k₀ LU` every reachable budget. Shipped: the `maxLit` kit
    (subterm + substitution monotonicity, mutual pairs, omega-driven — omega handles
    `Nat.max` natively); **`allowedProgs`** (subterm closure of roots + `.self`/`.opp` +
    every closed modest literal-gated program of size ≤ R — the cut-atom arguments) with
    subterm-closure/modesty/literal lemmas; **`GF`** — the pair-indexed guard family
    (T4.3's `guardU u v` glued over `allowedProgs²`), with `GF_args` (members' `.plays`
    args are universe programs — so cert queries re-enter the space) and `GF_lit`;
    globalized read interface: `certRead_budget` (every consultation at `≤ max b LU`) and
    `certRead_mem_GF` (every consulted formula ∈ `GF` or its `.neg`).
  - **T4.4c part 2b — ✅ SHIPPED (2026-07-03): PIPELINE (i) COMPLETE — the modest stratum
    is DECIDABLE, with the computable fuel bound `|SL|`.**
    `Research/Spikes/transcript/T47Stabilization.lean` (~990 lines, green, no sorry, 3 std
    axioms). The space: fold-based enum size ceilings (`EB b := foldMax size (enumFormula
    b)` — no structural enumeration bound needed), subterm-size lemmas, the ceilings
    `LL`/`RR`/`EBR`/`SB`, the stratification `ZS b := Z₀ + (RR−b)·(EBR+RR+3)` (each
    strictly-descending read gets one composite's headroom; the pair-glued guard family
    `GFall` fits at EVERY budget), the invariant `InvP` (atom args ∈ `allowedProgs`,
    literals ≤ `LL`), and the space list `SL` with intro/elim. **`stepB_congr`** — the
    16-checker in-space congruence: descending reads by `ZS_step` arithmetic; cut sweeps
    case on `cutOKb` (false ⇒ both sides false; true ⇒ `enumArg_mem` re-entry);
    `chkDiagFEB/BEB` case on their duplicated-pattern `beq`s first (false ⇒ trivial;
    true ⇒ subst); jumps (`chkSTS`, cert cites/refutations) land in `GFall` via T4.5/T4.6.
    Then the T4.1a countP stabilization verbatim (`Agree`/`agree_succ` via the congruence/
    `agree_ge`/`exists_agree`/`decB_bound`) and THE PAYOFF:
    **`ProvableG_iff_decB_bound : ProvableG (modestGate N) k₀ φ₀ ↔
    decB N |SL| k₀ φ₀ = true`** + **`decideProvableG : Decidable (…)`** — hypotheses just:
    modest roots (the whole zoo, T4.3) and root atom-args in the universe (automatic for
    every bot-guard instance via `GF_args`). Bounded provability over the zoo's query
    universe is decided by a terminating computation. What remains of T4 is ONLY the
    T4.1b conjecture (cut relevance) separating `ProvableG (modestGate N)` from full
    `Provable` — plus optional consolidation (promote the spike chain into the engine
    tree, wire `proofSearch` to the decided fragment).
- **T5 — aftermath.** Retire evalC scaffolding; docs (CLAUDE.md crux → RESOLVED); paper notes.

**Total: ~7–10 weeks focused.** Risks ranked: (1) T0 subscript re-balance (killed cheaply if fatal);
(2) T3 completeness of `D` (fuel↔budget bridge; template exists but the full-rule version is new);
(3) T1/T2 grind volume (mechanical but large — the compiler enumerates every site).

## What it buys

**Zero axioms. Computable `eval`. Literal Critch cost semantics. `by decide` outcome theorems.**
The full "explicit S" endgame — with the readability IMPROVING at each step (one system, one honest
cost model, no analytic/declarative split).
