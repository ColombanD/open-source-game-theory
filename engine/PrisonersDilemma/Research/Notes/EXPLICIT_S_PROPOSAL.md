# Making S explicit — status & the one remaining axiom (`PBLT`)

This note tracked the "make provability concrete proof-data" program. Most of it is now **done**:
two of the four reflection axioms were eliminated by adding sound constructors to `Provable`. What
remains is `PBLT` (the Löb core) — the last reflection axiom, removable only by a faithful (route-A)
mechanization. Companion: `WALLS_AND_EXTENSIONS.md`.

## Done — `box_provable` and `boxInternalize` eliminated (2026-06-29, 4 → 2 axioms)

Both fell to **sound, kernel-positive constructors** on `Provable` — no new axiom; `Provable_sound`
still depends on only the 3 Lean-standard axioms (propext / Classical.choice / Quot.sound):

- **`boxIntro`** (`Provable k φ → □_k φ`, bare necessitation) — discharged `box_provable`.
- **`app` / `axK` / `box4`** (object modus ponens / GL axiom-K with a proof-TERM premise / object
  GL-4 `□φ→□□φ`) — discharged `boxInternalize`. `mutual_loeb` was rewritten to **Route 2**: from the
  two object transparency legs (`legPD : □φP→φD`, `legDP : □φD→φP`) it builds `□φP→φP` via
  `boxIntro → axK → box4 → implTrans×2` — no proof *transformer*, so no non-positive premise.

The key insight (faithful spike `FaithfulSubstrateSpike.lean`): proof-data only works once it's
**applicable** — the missing piece was the object modus-ponens rule `app`, which the abstract `Prop`
engine had only inside `Derivation`/`struct`. The per-leg budget reconciliation (the "Horn B" budget
threshold) is carried by each leg's own source-transparency `Derivation` — which already existed.
All 3 cross-bot legs converted (PrudentBot via `searchThenSearch_t` + prudence atom; JustBot ×2 via
`searchThenSearch_t` and `botSearchStep`). `mutual_loeb` now depends on NO axioms.

Bonus: `no_pp_else` / `no_provable_forbidden` (`Exclusion.lean`) had to be PROVEN (were doc-only)
because `app` could otherwise route a proof to the false else-play; they show it cannot.

## Remaining — `PBLT` (route A only)

`PBLT` (Critch's parametric bounded Löb) is the last reflection axiom. A faithful mechanization is a
classical diagonal argument that needs a concrete encoding of provability to even state.

- **Stays classical/existential.** Route A cleans the axiom surface (2 → 1) but does NOT make `eval`
  computable at the fixpoints (the constructive route is closed — see Wall 1).
- **Floor = 1 axiom.** `atom_complete_false_guard` is irreducible even under explicit S (Wall 2,
  empty else-cert) — it does not fall to this lever.

### Phase-0 spike — VERDICT: route A does NOT close over the concrete engine (2026-06-29)

`Research/Spikes/pblt/PbltInterfaceSpike.lean` states Critch's PBLT proof (`PBLT_proof.tex` §5) as an
abstract `structure BPS` (the named properties: Implication/Quantifier Distribution, Bounded /
Bounded-Inner Necessitation, Parametric Diagonal Lemma) and probes whether the engine's `Provable`
can discharge each field. The five split:

- **Bounded Necessitation** — `boxIntro` (the rule exists; only budget bookkeeping). ✓
- **Bounded Inner Necessitation** — `box4` (object GL-4, size-gated). ✓
- **Implication Distribution** `□_a(p→q) → (□_b p → □_{a+b+c} q)** — `axK` generalized to ADDITIVE
  budgets; a budget-arithmetic variant of an existing sound constructor. Plausible new constructor. ~
- **Quantifier Distribution** — **BLOCKED.** Needs `∀` over the parameter `k`; `Formula` has NO
  quantifier constructor (only `plays/impl/neg/box/eq`).
- **Parametric Diagonal Lemma** — **BLOCKED.** Needs a Gödel encoding / self-reference; `Formula` has
  no encoding of its own codes.

**So three of Critch's five ingredients are essentially ALREADY PRESENT** — the box rules built during
the `boxInternalize` elimination (`boxIntro`/`axK`/`box4`) ARE the bounded HBL derivability conditions,
a real head start. But **two require machinery `Formula` fundamentally lacks: a `∀` quantifier and a
Gödel-encoding layer.** Route A over the *concrete* `Provable` therefore does NOT close locally — it
requires extending `Formula` with `∀` + an encoding and building `Bew`/the diagonal lemma from zero
(the weeks–months effort; Mathlib `ModelTheory` gives ~15–20% syntax scaffolding, no `Bew`, no bounded
GL).

### Option 1b ATTEMPTED — the interface does NOT cleanly refactor PBLT (CORRECTED 2026-06-29)

I built the budget-tracking interface `BPSb` and transcribed the §5 chain producing the EXACT engine
`PBLT` signature — `bloeb_of_bpsb` / `pblt_of_bpsb` are **sorry-free** (real, reusable artifacts). BUT
discharging the interface FIELDS for the engine's `Provable` mostly FAILS — only `mp` (object MP via
`Provable.app`) closes. The blockers:

- **`nec` / `K` / `four`** — the box SUBSCRIPT is coupled to proof cost: `Provable` is monotone UP in
  budget, not down, so boxing `φ` at a chosen subscript `a` needs `Provable a φ`, which fails when
  φ's cheapest proof exceeds `a`. The "box rules = HBL conditions" intuition holds only at the
  formula's own cost budget, not an arbitrary one.
- **`boxMono`** (relax a box subscript) — no engine rule weakens a box subscript (proof-budget
  monotonicity ≠ box-subscript monotonicity).
- **`impI`** (deduction theorem) — the engine `Derivation` DELIBERATELY has no
  implication-introduction (only `weakenImpl` = impl from a *proved* consequent, and `hypSyll`/
  `implTrans` = chaining). No hypothesis-discharging deduction. Structural.
- **`diag`** — Gödel encoding / self-reference, as before.

So landing `PBLT := pblt_of_bpsb engineBPSb` would need FIVE fields as axioms — strictly **worse** than
the single `PBLT`. The blockers are load-bearing design choices: the engine's `Provable` is a
deliberately *bounded, deduction-free* object, while Critch's proof lives in an *unbounded first-order
`S` with a deduction theorem and a Gödel `Bew`*. The mismatch is fundamental, not bookkeeping.

**Revised options:**
1. ~~Refactor PBLT into the interface to shrink the axiom surface~~ — **does not work** (above).
2. **Full route A** — extend `Formula` with `∀` + Gödel encoding + a deduction-carrying proof layer,
   build `Bew` + the diagonal, prove `PBLT` outright → 1 axiom. A genuine separate development (NOT a
   refactor of the current engine), `atom_complete_false_guard` remains the floor.
3. **Stop at 2 axioms (recommended).** Both remaining are faithfully stated and well-understood: PBLT
   = Critch's metatheorem with a complete paper proof (`PBLT_proof.tex` §5), and the false-guard axiom
   is machine-proven irreducible. The `bloeb_of_bpsb` chain stands as the abstract justification (PBLT
   mechanized over an interface) even though the engine can't instantiate the interface.

**Recommendation: option 3.** Option 1 is refuted; option 2 is a from-scratch research project, not a
follow-on. The current 2-axiom state is clean and defensible. (Spike: `Research/Spikes/pblt/`.)

## Note on the `Derivation` cost model (settled)

A `Derivation`'s "size" is the **conclusion's character count** (`Derivation.size := φ.size`), NOT a
proof-tree size. `mutual_loeb` and the box rules discharge all their budget side-conditions through
`Formula.size`. So the box-introduction work needed **no** structural size-index on `Derivation` and
**no** ~500-ref refactor — the constructors are local. (An early Phase-0 attempt to add a structural
size / decidable `Provable_k` was a dead end and has been removed.)
