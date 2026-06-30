# Walls and Extensions — the axiom & computability boundaries

A short map of the engine's two remaining axioms and the one computability boundary. Deeper
write-ups: `COMPUTABLE_EVAL_NOTES.md`, `CONSTRUCTIVE_BOUNDED_LOB.md`, `EXPLICIT_S_PROPOSAL.md`.

The unifying theme is a **proof-vs-witness gap**: a fact can be *true in the `interp` model* yet have
*no finite proof TERM*.

## History (4 → 2 axioms)

The engine started with 4 reflection axioms; two were eliminated (2026-06-29) by adding **sound
constructors** to `Provable` — no new axiom, `Provable_sound` still depends on only the 3 Lean-standard
axioms (propext / Classical.choice / Quot.sound):

- **`box_provable`** (bounded GL-4 necessitation) — killed by the `boxIntro` constructor
  (`Provable k φ → □_k φ`).
- **`boxInternalize`** (box-internalization at the cross-bot Löb fixpoints) — killed by the
  `app` / `axK` / `box4` constructors (object modus ponens / GL axiom-K / object GL-4), which let
  `mutual_loeb` build `□φP → φP` from the two object transparency legs directly, with no proof
  *transformer*. (`atomBoxImpl`, for the witnessed atom, was already a constructor.)

The two that REMAIN are below: the Löb core (`PBLT`) and the Π₁ false-guard residue
(`atom_complete_false_guard`).

---

## The 2 axioms

| Axiom | Role | Removable? |
|---|---|---|
| `PBLT` | Parametric Bounded Löb (Critch 3.6); closes the `∀k` cooperation families | **Only by fully-explicit S.** A faithful mechanization (route A) stays classical/existential — it cleans the axiom surface but does NOT make `eval` computable. NOT removable locally. |
| `atom_complete_false_guard` | Π₁ residue: a play branching on a *failed* guard still has an `AtomProvable` cert | **NO — proven irreducible** (Wall 2 below). Load-bearing (~5 false-guard else-plays). |

---

## Wall 1 — Computable `eval`: blocked ONLY at the genuine Löb fixpoints

`eval` is `noncomputable` because its `.search` guard consults
`proofSearch k φ := decide (Provable k φ)`, and `Provable` is a `Prop` with axiom-injected
(term-free) members ⇒ `decide` needs `Classical`.

- **Off the fixpoints:** effectively computable. A finite proof term exists. Shipped: `evalC`
  (`ComputableEval/Computable.lean`) — a sound, total, computable *partial* evaluator that commits a
  real action wherever a finite witness exists.
- **AT the genuine fixpoints** (FairBot↔FairBot, CUPOD↔CUPOD): **proven impossible**
  (`BoundedLobSpike` S3′, machine-checked). The constructive bounded-Löb lever is dead because
  **search budget = box budget coincide**: `eval` consults `proofSearch k` at the bot's OWN `k`, the
  sound premise is `□_k φ → φ` at the *same* `k`, and the `c_guard k` cost is internal proof-length
  bookkeeping paid *on top of* the atom, never subtracted from the antecedent box. No strictly-smaller
  budget ⇒ budget-recursion has no foothold ⇒ the fixpoint certificate would need *itself* as a
  `search_t` premise (forbidden: `PlaysProof` is a *least* fixed point).

**Net:** `eval` is computable everywhere a finite witness exists and **provably non-computable
exactly at the Löb fixpoints** — which is precisely where `evalC` returns `none`. The boundary is
located, not a failure. (Note: fully-explicit `S` / `PBLT` would clean the axiom surface but does NOT
move this boundary — the constructive-Löb route stays closed.)

---

## Wall 2 — `atom_complete_false_guard`: irreducible

A *negative* / *empty-certificate* fact, distinct from Wall 1's positive fixpoint.

- **The fact is DECIDABLE** — `ppSize` / `Provable_fin` (`ComputableEval/PlaysCheck.lean`) compute
  "no size-≤-k `PlaysProof` of the guard exists" by a terminating procedure.
- **But it cannot be carried as a term.** Removing the axiom needs a `PlaysProof` rule producing the
  search-bot's ELSE-action. The honest premise is `¬ Provable k guard` — a Π₁ negation,
  kernel-non-positive in the mutual block.
- **Exclusion lemmas (machine-checked, `[propext]`, root-imported in `ComputableEval/Exclusion.lean`):**
  `no_deriv_else` / `no_pp_else` / `provable_else_isAtom` / `no_provable_forbidden` prove the else-play's
  **certificate type is provably empty** — no `Derivation`, no `PlaysProof`, and no `Provable` (even via
  the object modus-ponens `app` rule) concludes it. So the axiom inhabits a true `interp` consequence
  that has *no proof term at all*.

**Net:** irreducible even under fully-explicit S — the wall is an empty certificate type, not the
abstractness of proofs. (`no_provable_forbidden`/`no_pp_else` are what keep this result valid now that
`app` exists: `app` could otherwise route a proof to the else-play; they prove it cannot.)

**Concrete win banked:** the `.impl`-guard false fragment IS dischargeable without the axiom when the
consequent is a false *atom* (refuted by `Provable_sound`): `CIMCIC vs DefectBot`,
`DIMCID vs CooperateBot` are real outcome theorems with NO reflection axiom. *Play*-atom false guards
(DupocBot/JustBot/CupodTrollBot) still route through the axiom — no false-consequent handle.

---

## Shipped artifacts at the boundaries (all root-imported)

- `evalC` (`ComputableEval/Computable.lean`) — sound, total, computable *partial* evaluator; `none`
  exactly at the Löb fixpoints.
- `ppSize` / `Provable_fin` / `instDecProvableFin` (`ComputableEval/PlaysCheck.lean`) — computable,
  sound decider for the bounded play-certificate (the "decidable, but uncarriable" witness for Wall 2).
- `no_deriv_else` / `no_pp_else` / `provable_else_isAtom` / `no_provable_forbidden`
  (`ComputableEval/Exclusion.lean`, `[propext]`) — the irreducibility proof for
  `atom_complete_false_guard` (else-play certificate type provably empty).

## The one remaining lever

**Fully-explicit S** — make proofs concrete, sized data and mechanize `PBLT` faithfully (route A). It
would clean the last reflection axiom (`PBLT`) toward the Lean-standard floor. It does NOT make `eval`
computable at the fixpoints (Wall 1, closed) and does NOT touch `atom_complete_false_guard` (Wall 2,
irreducible). Large, foundational; see `EXPLICIT_S_PROPOSAL.md`.
