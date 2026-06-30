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
- **Cost.** Mathlib gives only ~15–20% scaffolding (`ModelTheory`); no bounded GL, no arithmetized
  provability, no derivability conditions — the hard core is built from zero. Large, foundational,
  separate research effort. The `PBLT` proof itself is in `PBLT_proof.tex` (Critch §5, complete).

## Note on the `Derivation` cost model (settled)

A `Derivation`'s "size" is the **conclusion's character count** (`Derivation.size := φ.size`), NOT a
proof-tree size. `mutual_loeb` and the box rules discharge all their budget side-conditions through
`Formula.size`. So the box-introduction work needed **no** structural size-index on `Derivation` and
**no** ~500-ref refactor — the constructors are local. (An early Phase-0 attempt to add a structural
size / decidable `Provable_k` was a dead end and has been removed.)
