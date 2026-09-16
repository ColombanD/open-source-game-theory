# The merge crossroad (2026-09-16)

Where the `S` → `S'` merge stands after one day of work, and the decision it needs.
Authoritative detail: `ARITHMETIZED_S_ROADMAP.md` §3 "M6"; results: `ARITHMETIZED_S_RESULTS.md` §5.

## The goal we set this morning

`S'` (PA + length-bounded `□_k`) is the formal system. The engine's 33 rules should be
derived rules of `S'`, budget-keeping, so the 155 outcome theorems transfer untouched by one
induction over `Pf`. Trusted definitions: the translation `tr` and the budget function `f`.

## What is done

* **Atom re-cost** (branch `colomban-recost`, commit `70134d8`): `AtomProvable.mk` pays the
  whole conclusion atom. Engine green (3278 jobs), export byte-identical (155 cells, 4
  companions, 18 tau rows: values, regimes, pads unchanged). T2-NEG retired; every engine theorem
  now fits its budget (`ArithS.pf_size`). Keep this whatever route is chosen.
* **Step-2 check**: cut and instantiation are at explicit budgets; the diagonal lemma needs a
  wrapper; bounded D1 exists only in parametric form (`BoundedInnerNec 16` at `gBudget k`).

## The obstruction

The engine's box rules are **additive**: `□_a φ` costs `a + |□_a φ|`. This is a free
**citation** ("see the proof above"). Any real system, PA-`S'` included, pays a verification:
polynomial (degree 16 here), and even Critch's own assumption (d) is `e*·k` with `e* > 1`.
Nested boxes compose: additive gaps in the engine vs multiplicative gaps in `S'` force the
budget function to be doubly exponential, and `search_t`'s `log k` citation defeats even that.
Conclusion: **the engine's `S` is Critch's `S` plus free citation (and, via `search_f`, free
bounded reflection); PA has neither.** Abbreviations and O(n) numberings (Critch §4.2) would
make `e` linear, not additive — they shrink U10's degree, they do not rescue a uniform bridge.

Independent fact: the red cell `red_cell` (Cupod vs Dupoc = (D, C), every k) and M5
(`dupoc_self_coop_unconditional`, `pblt_unconditional`, all large k) are already theorems of
`S'` on three standard axioms; no route below changes them.

## The routes

| | What | Gives | Costs / caveats |
|---|---|---|---|
| **A** | Uniform rule bridge with doubly-exponential `f` + `search_t` re-cost | Literal "rules are theorems of `S'`" | Budgets meaningless; sparse budget sets; staggers destroyed; `search_t` re-cost may flip same-`k` values; dominated by M5 on Löbian cells |
| **B** | No rule bridge; direct `S'` proofs per Löbian family (M5 pattern) + erased core for the logic | Strongest statements (all large `k`); engine untouched | Engine–`S'` relation stated in prose, not as rule theorems; one `S'` proof per family |
| **C** | `S''` = PA + a `cite` node (Critch's (c)/(d) as a rule); engine rules derived at the same budgets; U10 = conservativity of `cite` over PA | Formal rule-level relation; budgets intact | 5–8 weeks new construction; box means `S''`-provability; floors need a second rule (bounded reflection), whose polynomial conservativity is Pudlák-grade and unscheduled |
| **D** | Re-cost the engine's box rules to Critch's `e(k)` (polynomial, matching U10) + `search_t` at `k` | Engine literally satisfies (a)–(d) as rules; a polynomial bridge is no longer blocked by composition | Needs verifying that the Löb chains close under polynomial box costs (they should: they expand only `O(lg k)` proofs — Critch Thm 4.2's condition); still needs the node-data box coding fix, reflection for floors, and the sparse-budget argument unless `f = id` |

## Recommendation

1. **B now**: mutual-Löb (Prudent/Just × Dupoc) and staggered families in `S'`.
2. **D spike (one day)**: restate `bloeb_engine`'s size hypotheses with a polynomial box cost;
   if the Löb cells still close, the engine obeys (d) with the polynomial U10 proves.
3. **C only if time remains**, positive fragment first; it reuses B's proofs.
4. Never A.

Paper sentence either way: *the engine's `S` is a sound self-referential bounded proof system
with a citation rule; PA-`S'` is its arithmetic counterpart; the Löbian cells and the red cell
are re-proved in PA-`S'`; citation is polynomially eliminable (U10); no polynomial
budget-preserving embedding of the citation rule exists.*

## Open questions for Colomban

* Must the box mean *PA* provability (→ B, D), or is "a system over PA satisfying (a)–(d),
  reducible to PA" acceptable (→ C)?
* Is the floor (`search_f`) to be claimed in `S'` at all, or left as the engine's result with
  the reflection assumption stated?
