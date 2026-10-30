# The box-cost spike: does any outcome depend on free citation? (2026-09-16, branch `colomban-boxcost`)

**Question.** The engine's box rules charged a box ADDITIVELY (`□_a φ` at `a + |□_a φ|`), i.e. a
free citation of the proof above — stronger than Critch's assumption (d) (`e*·k`, `e* > 1`) and
unavailable in PA-`S'`, where the verification is polynomial (U10, degree 16). Which outcome
theorems depend on that extra strength? (`MERGE_CROSSROAD.md`, route D.)

**Method.** Replace the gates of `boxIntro`, `box4`, `atomBoxImpl` by
`boxCost a φ := (a + |□_a φ|) ^ boxDeg`, `boxDeg = 2` (one constant; the argument is about growth
rates, so degree 2 answers the question for degree 16). Repair the base layer, repair the Löb chain
so that the four consumer-facing theorems keep their statements byte for byte, then build
everything and read the failures. No outcome statement was edited by hand.

## Result

| Layer | Outcome |
|---|---|
| Base (`Transpose`, `Soundness`, `Closure`, `Exclusion`, `TowerCensus`, `BoundedGL`) | repaired; `pf_size_or_atom` still holds (`le_boxCost`); the interface's four `rfl` bridges to the engine still close |
| Löb chain (`Base/Loeb.lean`) | `pblt_engine_id`, `pblt_engine_id_bounded`, `mutual_pblt_engine_id`, `mutual_pblt_engine_staggered` **byte-identical**; master bounds now polynomial in the unit `W ≈ log k` (see degrees) |
| 155 cells, 4 staggered companions, 18 tau rows | **ALL compile unchanged** except the three OptimBot staggered cells (out of scope) |
| Direct users of the chain's internals | 8 files needed mechanical restatement of internal helper budgets (DIMCID ×2, TauDIMCID helpers, LegibleBot helpers, OptimBot ×4); no cell statement changed |
| Metatheory target | not measured — pre-broken independently (`Decidability.lean` docstring-before-imports); its mirror `PfG` has 164 box-rule sites to adapt if this lands |

**Degrees observed** (the price of composition): single Löb `2³⁴·W⁴ ≤ k`; mutual Löb (a `box4` at
the Löb subscript) `2¹⁷³·W¹⁶ ≤ k`; the two-stage vector engine of the tau `.sys` bots
`2⁴⁰²⁹·W¹²⁸ ≤ k`. All polylog, so every "for all large `k`" survives; the thresholds behind
"large" are astronomically far from any budget one would run. This is exactly Critch's Theorem 4.2
condition `f(k) ≻ e(O(lg k))` in engine form, and the doubly-exponential composition predicted for
a uniform bridge shows up here as `16^depth` in the degree.

## Findings

1. **No cell in the Löbian core, no floor, no tau row depends on the additive rule.** The engine's
   Löb proofs are parametric — they expand only `O(lg k)`-sized proofs — so Critch's (d) at any
   polynomial degree suffices. The paper can say the engine satisfies (a)–(d) as rules with the
   polynomial expansion U10 proves, and that the additive rule was never load-bearing for the
   matrix.
2. **Cooperation across a floor needs a POLYNOMIAL stagger.** The three OptimBot staggered cells
   (`OptimBot k (65536·k)` vs TFT/DefectBot, `OptimBot k (10⁸·k)` vs DBot) fail at EVERY threshold:
   their Löb premise pays two `search_f` floors (`pm ≥ 2k`, forced by consistency), the fixpoint
   subscript must absorb it (`g ≥ 2·pm`), and boxing the fixpoint costs `g²`, so the outer budget
   must be `≥ 4k²` — no linear stagger can hold it. OptimBot is out of the merge's scope, but the
   mechanism is general: under Critch's (d) at polynomial degree, a prover that pays a partner's
   floor needs a budget polynomial in the partner's, not `2k + 64`.
3. **Why the four `_staggered` companions (Prudent/Just/CupodTroll vs Dupoc/Just) nevertheless
   survive at their LINEAR staggers:** their legs are `searchThenSearch_t` implications, whose
   inner floor-paying premise is CITED at `c_guard` cost, not charged (recorded dead end:
   "charging `searchThenSearch_t`'s inner premise sinks the staggered Löb chains"). That is the
   same cheap-citation idealization as `search_t`, one level up. So the honest reading is: the
   linear staggers hold in the engine because of a second citation rule; under full character
   accounting they would need polynomial staggers like OptimBot's. This is the `search_t` half of
   the M3 finding, now with a concrete consequence.
4. **LegibleBot's inner-dial necessitation is dead under the gate** (`box4 k (2k+64)` needs
   `(k + |□_k ψ|)² ≤ 2k + 64`); every LegibleBot theorem survives by moving the fixpoint to a
   polylog subscript and bridging with `box4`/`axK`. Out of scope, recorded because it shows the
   pattern: what a linear stagger buys is a polylog fixpoint, never a fixpoint at the inner dial.

## What landing this would mean (not decided)

* The engine's cost model would state Critch's (d) with the polynomial U10 proves; `boxDeg` would
  become 16 (or whatever U10's degree is after the deferred refinements), and the thresholds would
  be honest but enormous.
* `search_t` and `searchThenSearch_t` would still cite at `c_guard`; charging them is the second
  half (§3 above) and would move the four companions to polynomial staggers.
* `Decidability/` (164 sites), the arith `Core/Sound.lean` induct arms, and the app's prepass
  evaluator would need the same gate.

## Files

`engine/PrisonersDilemma/ProofSystem.lean` (`boxDeg`, `boxCost`, `le_boxCost`, three gates, the
eliminator), `Base/{Transpose,Soundness,Closure,Exclusion,TowerCensus,Loeb,Asymptotics,BoundedGL}`,
`Theorems/{DIMCID,LegibleBot,OptimBot}/…`, `Tau/Theorems/TauDIMCID/Helpers.lean`. New helpers:
`bloeb_std`, `mutual_loeb_std`, `boxCost_le_of_le`, `poly_log2_add_le`, `poly_envelope_le`,
`quartic_log2_add_le`, `pow_le_two_pow_eventually`. Three OptimBot theorems left RED on purpose,
each with a doc comment recording the obstruction.
