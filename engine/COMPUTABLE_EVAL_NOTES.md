# Computable-`eval` investigation — findings log

_Context: the project was reviewed; one criticism was that the central evaluator
`eval` is `noncomputable`. This logs the attempt to make it computable, what landed,
and the decisive mathematical obstruction found._

Date: 2026-06 (Lean engine, `engine/PrisonersDilemma`).

---

## TL;DR

- **Goal**: make `eval`/`play`/`outcome` computable by replacing the classical oracle
  `proofSearch k φ := decide (Provable k φ)` (noncomputable, via `open Classical`) with
  a computable decision of `Provable k φ`.
- **CORRECTED conclusion (supersedes the earlier "undecidable wall" claim in the
  obstruction section below)**: computable `eval` **is reachable**. The Π₁/Gödel wall
  applies to *unbounded* provability ("a proof of *any* size exists"), which is
  RE-not-recursive. But `proofSearch k φ` asks about **bounded** provability ("a proof
  of size ≤ k"), which is a **finite, decidable** search — *provided every
  constructor's premises are bounded by `k`*. The right object is
  `instance : Decidable (Provable k φ)` by enumeration over size-≤-k terms, NOT a
  fuel-tangled `derivable`. Then `proofSearch k φ := decide (Provable k φ)` is computable
  and `proofSearch_spec` is *definitional* (`decide_eq_true_iff`) — no separate
  completeness proof, no monotonicity, no Π₁ issue.
- **Why the earlier `derivable` attempt thrashed (self-inflicted)**: `derivable` used a
  *separate search-gas* `fuel`, distinct from and possibly smaller than the logical
  budget `k`. A guard provable-within-`k` but not-found-within-`fuel` read `false` → the
  bot took its else-branch → "not found yet" conflated with "unprovable". THAT
  conflation (not bounded provability) is the non-monotone/undecidable-looking part.
  Deciding `Provable k` directly by k-bounded enumeration removes it.
- **The one genuine remaining gap (see Feasibility below)**: the `Derivation`-level cut
  rules `modusPonens`/`hypSyll` still carry **unbounded** cut formulas `ψ` (Step 2 only
  bounded the `Provable`-level cuts). Since `Derivation.size = conclusion.size`, a
  derivation of a size-≤k conclusion can have arbitrarily large premises →
  `Nonempty (Derivation φ)` not obviously finite. **Fix: bound the cut in
  `modusPonens`/`hypSyll` too.** After that the search is finite and
  `Decidable (Provable k φ)` is constructible.
- **`atom_complete_false_guard` should be DELETED, not axiomatized** (user call,
  correct): the false-guard play certificate has cost `≤ atom_cost fuel` (bounded), so
  its existence is a *finite* fact — provable by enumeration, subsumed by the
  `Decidable` instance. Its axiom status was an artifact of the `decide`-based opaque
  oracle.
- **What did land (all green, kept)**: concrete costs, one fewer axiom
  (`c_guard_mono`), a `Provable`-level cut-bounded calculus, an enumerator, and a sound
  (partial) computable checker. Details below.

> The section "## The obstruction, precisely" below was written under the earlier
> (mistaken) belief the wall was fundamental. It correctly describes the *gas*
> non-monotonicity but its conclusion is SUPERSEDED: the gas was the wrong design, not a
> real barrier. Bounded provability is decidable.

---

## What landed and is GREEN (3141 jobs, kept in the build)

These are real improvements independent of the computability goal:

1. **Concrete cost constants** (`Derivation.lean`): `c_leaf = 1`, `c_node = 1`,
   `c_guard k = Nat.log2 k + 1` (were `opaque`). `atom_cost` dropped `noncomputable`.
2. **`deriving DecidableEq for Prog, Formula`** (`Program.lean`) — worked on the nested
   mutual block, no hand-written instance needed.
3. **`c_guard_mono` demoted axiom → theorem** (`Axioms.lean`, via
   `Nat.log2_eq_log_two` + `Nat.log_mono_right`). **Axiom count 5 → 4.** Directly
   answers the reviewer's *other* criticism (too many axioms).
4. **Cut-bounded `Provable`** (`Derivation.lean`): `weakenImpl` carries `m ≤ k`;
   `searchThenSearch_t` carries `k₂ ≤ k`; `implTrans` carries `a ≤ k, b ≤ k,
   ψ.size ≤ k`. ~20 call sites updated; `proofSearch_monotone` rethreaded. This makes
   the calculus subformula/budget-bounded (a cleaner, more defensible `S`).
5. **Bounded `box_provable`** (`Axioms.lean`): now `∃ K, K ≤ (□φ).size ∧ Provable K …`
   (honest bounded-GL-4); `atom_box_provable_impl_sound` re-verified.
6. **`Enumerate.lean`** (new, proven): `progsOfSizeLE` / `formulasOfSizeLE` +
   completeness lemmas (`_.size ≤ n → _ ∈ _ofSizeLE n`); `natsOfLog2CostLE` for the
   numeral indices in `.search`/`.box`.
7. **`Checker.lean`** (new, compiles): `playsCheck` (cost-tracking fuel-bounded eval
   with guard `derivable fuel kg`) and `derivable fuel k φ` (a sound, computable,
   *partial* checker). `derivLeaf` recognises ALL `Derivation` leaf rules
   (searchBranch / simStep / botSimStep / botSearchStep / iteBranchSearch_t / eqRefl)
   by size-bounded enumeration; cut rules by enumerating cut formulas.

## What is PARKED (sorries, NOT wired into the build)

- `CheckerSound.lean` — soundness scaffold (`derivable → Provable`).
- `CheckerComplete.lean` — completeness scaffold; `monoStep_all` documents the
  non-monotonicity / undecidability obstruction.
- `BaseTheorems.lean : proofSearch_spec` — currently `sorry` (Step-6′ reshuffle made
  `proofSearch := derivable (k+1) k`; the `←` direction is the uncomputable one). The
  library's outcome theorems compile *through* this sorry; they are otherwise
  unchanged and remain provable once the bridge is restored (see Decisions).

---

## The obstruction, precisely

`eval` at a `.search kg ψ p q` node:
```
if proofSearch kg (ψ.subst …) then run p else run q
```
- **then-branch** (guard provable): fine — a provable guard has a witness
  (`PlaysProof.search_t` requires `Provable kg guard`); fully constructive.
- **else-branch** (guard *not* provable): fires on `¬ Provable kg (ψ.subst …)`. There
  is deliberately **no `search_f` constructor** — certifying "no proof of size ≤ k
  exists" is Π₁ (non-positive, kernel-rejected). Real bots' plays routinely take this
  branch (a failed proof-search falling through, e.g. defect-on-failure).

A computably **complete** `derivable`/`proofSearch` would have to return the correct
Boolean on the else-branch too, i.e. **decide non-provability** — undecidable.

### Why every proof attempt failed (all the same root cause)
`derivable`/`playsCheck` are **not fuel(gas)-monotone**:
- Counterexample: `me = .search kg ψ (.const C) (.const D)`, `ψ` provable but not yet
  found at small gas. Small gas → guard `false` → plays `D`; large gas → guard `true`
  → plays `C`. **Different action.** So `some r`-monotonicity is false, and via the
  atom branch (`a' == a`) `derivable`-truth-monotonicity is false too.
- Completeness needs *some* monotonicity to combine premises at a common gas (max).
  Restricting to `PlaysProof`-witnessed plays (then-branches only) does **not** rescue
  it: a witnessed play of `me` can still *traverse* `.search` nodes whose guards are
  false en route (those are the `atom_complete_false_guard` / axiom plays), and those
  are exactly the non-monotone ones.
- Conclusion: the non-monotonicity is the *symptom* of the else-branch undecidability.
  Separating gas (search depth) from the logical budget `k` does not help — the flip
  is in gas.

### This matches the existing design
The original authors hit this exact wall: `atom_complete`'s false-guard direction is
the axiom `atom_complete_false_guard` (`Axioms.lean`), and `proofSearch` was a classical
`decide`. The undecidability is *why* `eval` was `noncomputable` in the first place.

---

## ★ FEASIBILITY: constructing `Decidable (Provable k φ)` — the corrected plan ★

This is the right path (supersedes the "Decisions" list further down). Verdict:
**feasible**, with one constructor change + a standard (tedious) well-founded
decidability proof.

### The decreasing measure (decidability is by strong recursion on `k`)

Decide the four mutually-defined predicates at budget `k` with measure
**`(k, judgment-tag, formula-or-cost-size)`**, lexicographic:

- `Provable k φ`:
  - `struct`: `∃ d : Derivation φ, d.size ≤ k`. Since `Derivation.size = φ.size`, this
    is `φ.size ≤ k ∧ Nonempty (Derivation φ)`. Deciding `Nonempty (Derivation φ)`
    recurses into `Derivation`'s rules — **needs the cut bound (below)** to be finite.
  - `atom`: `AtomProvable k φ` — decide `∃ n ≤ k, PlaysProof me opp me a n`.
  - `weakenImpl`/`searchThenSearch_t`/`implTrans`: premises at budgets `m,k₂,a,b ≤ k`
    (Step 2 bounds) and cut `ψ.size ≤ k` — all strictly within the size-≤k universe;
    enumerate cut formulas from `formulasOfSizeLE k` (already built, with completeness).
- `Derivation φ` (for `struct`): leaf rules decided by `derivLeaf` (already written,
  enumerates size-≤k params). Cut rules `modusPonens`/`hypSyll`: **THE GAP** — cut `ψ`
  unbounded. With a `ψ.size ≤ k` bound added, enumerate ψ from `formulasOfSizeLE k`;
  premises have size ≤ k, so they're decided at a strictly smaller measure (same `k`,
  but the cut-search is a finite fold over `formulasOfSizeLE k`, terminating by a
  saturation/round count — standard "decide provability in a finite logic by forward
  closure").
- `PlaysProof me opp body a n`: decide by recursion on the **cost `n`** (each rule adds
  `≥ 1`: `c_leaf=c_node=1`, `c_guard k = log2 k +1 ≥ 1`). `search_t`'s premise
  `Provable kg (guard)` is at budget `kg` — a SEPARATE finite decision (the guard's own
  bounded provability), decided at measure `(kg, …)`. Note `kg` may be > the play's `n`,
  so `PlaysProof`-decidability is NOT a sub-recursion of the play cost alone; it bottoms
  out because the guard's `Provable kg` is itself decidable (by the same instance at
  budget `kg`), and bots are *finite terms* so only finitely many distinct `kg` occur.
  ⇒ the clean measure is on the **logical budget `k`/`kg` plus a structural term size**,
  NOT a separate eval-gas. THIS is the fix for the gas mess.

### Required change (one constructor edit + 3 call sites)

Add a cut-size bound to the `Derivation` cut rules, e.g.:
```
| modusPonens (φ ψ : Formula) :
    Derivation (.impl φ ψ) → Derivation φ → ψ.size ≤ φ.size + 1 → Derivation ψ   -- or carry an explicit k
| hypSyll (φ ψ χ : Formula) :
    Derivation (.impl φ ψ) → Derivation (.impl ψ χ) → ψ.size ≤ … → Derivation (.impl φ χ)
```
Caveat: `Derivation` has **no `k` parameter** (`Derivation.size = conclusion size`).
Two options:
  (i) bound the cut by the *conclusion/premise* sizes intrinsic to the rule (e.g. for
      `modusPonens`, `ψ` is the consequent of premise `impl φ ψ`, so `ψ.size <
      (impl φ ψ).size` already — but the PREMISE `impl φ ψ` can still be large; need to
      bound *it* by the conclusion, which fails since mp grows). So intrinsic bounding
      is insufficient — `modusPonens` genuinely enlarges.
  (ii) **index `Derivation` by a budget `k`** (`Derivation k φ` with `d.size ≤ k`
      threaded), bounding every premise by `k`. Cleanest but touches all `Derivation`
      constructors + ~15 call sites.
  OR (iii) **decide `Provable` WITHOUT `Nonempty (Derivation φ)` as a black box**:
      replace the `struct` disjunct's existential with a *budget-bounded derivability
      predicate* `DerivableAt k φ` (Prop or Bool) that has the bounds built in, prove
      `DerivableAt k φ ↔ (φ.size ≤ k ∧ Nonempty (Derivation φ))` for the fragment used.
      This is the forward-saturation route from the original plan (Step 7 "cut layer").

Recommended: **(ii)** — index `Derivation` by `k`. It is the honest "bounded `S`" and
makes the measure trivial. Cost: re-thread `k` through `Derivation`'s 8 constructors
and the ~15 `Provable.struct ⟨d, …⟩` / `Derivation.sound` sites. Mechanical.
The 3 cut call sites (`K_provable`, cupod/dupoc `hypSyll`) already prove a
conclusion-size-≤-k bound by `omega`+`linear_log2_add_le`; the cut `ψ` there is a
`.plays` atom strictly smaller than the conclusion, so the new bound discharges the
same way. **Verified safe** (grep: only those 3 sites use the cut rules).

### `atom_complete_false_guard` → theorem/deleted

With `Decidable (Provable k φ)` available, `atom_complete` no longer needs the axiom:
the false-guard play's certificate cost is `≤ atom_cost fuel` (finite), so
`AtomProvable (atom_cost fuel) (.plays p q a)` is decided by the same instance. Delete
the axiom; re-prove `atom_complete` directly (or fold it into the `Decidable` instance).
**Axiom count 4 → 3** (then only `PBLT` + `box_provable` + `atom_box_provable_impl`
remain; cf. Path-A discussion — the two DupocBot reflection axioms are a separate
matter, NOT about computability).

### Net effort estimate
- Index `Derivation` by `k` (or do route iii): ~1 file + ~15 mechanical call sites.
- `instance : Decidable (Provable k φ)` by WF recursion on `(k, tag, size)`: the real
  work — a few hundred lines, standard shape, reuses `formulasOfSizeLE` + `derivLeaf`.
- Delete `atom_complete_false_guard`; re-prove `atom_complete`.
- `proofSearch k φ := decide (Provable k φ)` computable; `proofSearch_spec` becomes
  `decide_eq_true_iff` again (definitional!); drop `noncomputable` from
  `eval`/`play`/`outcome`. **Library theorems unchanged** (proofSearch_spec statement
  identical). The `derivable`/`playsCheck`/`CheckerSound`/`CheckerComplete` files become
  obsolete (the `decide`-instance route replaces them) — delete or keep as a fast
  evaluator.
- Risk: `#eval` performance (the size-≤k enumeration is ~`2^k` for numerals) — fine for
  small budgets / the demo, intractable for large `k`. A hand-written *fast* checker
  (the salvageable core of `derivable`, but consulting the decidable `Provable kg` at
  fixed budget — no separate gas) can be added for speed, proven equal to `decide`.

---

## Decisions / options going forward (SUPERSEDED by Feasibility above)

_These were written under the mistaken "undecidable" conclusion. (D)/(C) remain valid
*fallbacks* if the `Decidable` instance proves too costly, but the feasibility section
is the recommended direction._

The plan's premise ("redefine `proofSearch := derivable`, prove byte-identical
`proofSearch_spec`, library untouched") **can** be realized — but via
`Decidable (Provable k φ)` (definitional `proofSearch_spec`), not the `derivable`
checker (whose separate gas was the mistake).

- **(D) Sound-only demo `evalC`** *(recommended)*: restore the classical
  `eval`/`proofSearch` (remove the `proofSearch_spec` sorry → library fully green,
  0 sorry, outcome theorems intact). Add a standalone fuel-capped computable `evalC`,
  proven **sound** and equal to `eval` on the demonstrable const/atom-guard matchups
  (where guards bottom out → monotone & terminating there). Paper: "`#eval evalC 100 …`
  runs; `eval` is proven equal to a runnable evaluator on these cases; full
  computability is precluded by the undecidability of negative provability — the
  `atom_complete_false_guard` boundary." Turns the reviewer's jab into a precise
  theorem about the domain.
- **(C) Reframe + bank wins**: restore classical `eval`; KEEP items 1–6 above
  (concrete costs, one fewer axiom, cut-bounded calculus, enumerator). Frame
  noncomputability honestly in the paper; spend remaining effort on the E1–E4
  experiments.
- **(1-cap) WF checker with explicit depth cap**: SHOWN NOT TO CLOSE — the gas cap
  resurfaces the same flip/undecidability. Do not pursue.

### To restore the library to green + sorry-free (either D or C)
Revert the Step-6′ change in `Dynamics.lean` (`proofSearch := derivable (k+1) k` and
the `eval`/`play`/`outcome` `noncomputable` drops) and restore
`proofSearch_spec` in `BaseTheorems.lean` to `unfold proofSearch; exact
decide_eq_true_iff`. `Checker.lean` / `Enumerate.lean` can stay (sound, harmless) or be
demoted to the demo path.

---

## Files touched
- Modified: `Program.lean`, `Derivation.lean`, `Axioms.lean`, `Dynamics.lean`,
  `BaseTheorems.lean`, and ~20 theorem call sites (CIMCIC, DIMCID, PrudentBot, JustBot,
  Cupod/Dupoc) for the cut-bound arities.
- New: `Enumerate.lean` (proven), `Checker.lean` (compiles), `CheckerSound.lean`
  (parked), `CheckerComplete.lean` (parked), `AxiomBaseline.lean` (regression scratch),
  this file.
- Plan / scratch: `~/.claude/plans/i-want-to-go-abstract-wand.md` (full step log),
  `/tmp/axiom_baseline.txt` (axiom regression snapshot).
