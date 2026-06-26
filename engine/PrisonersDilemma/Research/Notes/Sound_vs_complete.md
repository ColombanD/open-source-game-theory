# Soundness vs completeness

These are the two halves of "the proof system S matches reality (`eval`)." Reality is: bot p plays action a against q. `S` is: there's a bounded proof that p plays a.

Soundness = `S` never lies. If S proves it, it's true.

```text
Provable k (p plays a) ⟹ play fuel p q = some a
```

This is `Derivation.sound / proofSearch_spec.1` (BaseTheorems.lean:53). It's the one you must never break — an unsound `S` would certify false cooperations, and your whole "compilation == correctness" guarantee dies. This is why you ripped out `atom_box_provable_impl`: it was unsound.

Completeness = `S` misses nothing. If it's true, S can prove it.

```text
play fuel p q = some a ⟹ Provable (atom_cost fuel) (p plays a)
```

This is `atom_complete` (BaseTheorems.lean:32). Every real play has a bounded certificate. This is the direction the false-guard axiom lives in.

The asymmetry is the whole game:

- Soundness is "downhill" — you have a proof tree, you read off the play. Always constructive.
- Completeness is "uphill" — you have a play, you must manufacture a proof tree. Sometimes the play happened because a search failed ("I cooperate because I couldn't prove you'd defect"). To certify that play, S must certify the absence of a proof — `¬ Provable k (guard)`. That negative is the Π₁ residue.

---

# Removing `atom_complete_false_guard` (the Π₁ residue) — the plan

The false-guard axiom is removable **because boundedness makes the negated guard
decidable-by-enumeration, and the guard carries no Löb fixpoint** (the self-reference
in e.g. CUPOD's guard is to a *sibling* atom — `CUPOD plays D` — not to the
cooperation `CUPOD plays C` being certified, so there is no same-budget cycle; the
budget-coincidence `k'=k` that closes route (B) in `CONSTRUCTIVE_BOUNDED_LOB.md` S3′
is simply absent here). Contrast: the Löb *defection* fixpoint (true branch) stays an
axiom (`PBLT`); the *cooperation* false branch is the eliminable one.

## The four changes

1. **`DecidablePred` for the bounded play-certificate** — decide whether a guard
   play-atom has a bounded `PlaysProof`, by a real terminating enumeration (not
   `Classical.dec`). **Spiked & PASSED:** `Research/Spikes/DecidableFiniteSpike.lean`.
2. **`search_f` constructor** — the positive dual of `search_t`, carrying
   `decide (Provable_finite k guard) = false` (a `Bool` eq, kernel-positive — NOT a
   bare `¬ Provable`). Plus the `botSearchStep`/`iteBranchSearch` analogues. Cost
   identical to `search_t` (`+ c_guard k + c_node`).
3. **Re-prove `atom_complete`'s else-branch** constructively — replace
   `BaseTheorems.lean:38`'s `exact atom_complete_false_guard …` with a `by_cases` on
   `decide (Provable_finite k guard)`: `true` → `search_t`, `false` → `search_f`. The
   `by_cases` is total because Change 1 made the guard decidable.
4. **Extend `Derivation.sound`/`playsProof_sound`** to `search_f` — needs the bridge
   `¬ Provable_finite k guard ↔ proofSearch k guard = false` on guard atoms (holds
   because the guard has no axiom-injected members — no fixpoint).

Effort: 1 is the real work (moderate, de-risked below); 2 easy; 3 moderate; 4 the
soundness one to watch (the guard-bridge lemma).

## Change 1 — SPIKE RESULT (PASSED)

`Research/Spikes/DecidableFiniteSpike.lean` (not imported by root; build alone with
`lake env lean …`). **No `sorry`, no `Classical`, no `axiom`** in the proofs.

- `playsCheck` — total, fuel-decreasing `Bool` checker for the `PlaysProof`
  (play-atom) fragment, parameterised by a guard oracle `gd`.
- `playsCheck_sound` (`check=true → ∃n, PlaysProof`), `playsCheck_complete`
  (`PlaysProof n → ∃N, check N=true`, via `PlaysProof.rec` — mutual block),
  `playsCheck_mono`/`_mono_le`. `decidableAtBudget` = the computing `Decidable`.

**Confirmed:** the predicate `search_f` negates is genuinely decidable (sound +
complete + monotone), so a `decide(…)=false` premise is honest.

**Residual, by design:** `gd` is abstract (spec `gd k φ = true ↔ Provable k φ`).
Closing it = deciding the *guard's* `Provable`, one `PlaysProof` level down (a strictly
smaller, fixpoint-free sub-program) — tie off by recursion on a *guard-nesting depth
fuel* `d` (NOT budget `k`: S3′ showed budget can't descend at the fixpoint; depth can,
off it). That tie-off is `§6`/`gdRec` below; the machinery it recurses through is proven
sound/complete here.

## §6 — first tie-off `gdRec` (SUPERSEDED — budget reuse fails)

`gdRec d k (.plays p q a) = playsCheck (gdRec d) k p q p a` reuses box budget `k` as
STRUCTURAL fuel. `gdRec_sound` proved only MODULO a named `gd_budget` hypothesis — which
is FALSE as set up. **Cost-bound finding:** a play accepted at checker-fuel `F` has a
`PlaysProof` of cost `~2^F` (`.ite` branches both children at the same fuel; `.search`
adds `c_guard k` uncounted in fuel). So reusing `k` as fuel can't enforce
`atom_cost(witness) ≤ k`; `gd_budget` is undischargeable for `gdRec`. → §7 fixes it.

## §7 — FIX: cost-tracking `playsCheckC` + budget-gated `gdRecB` (CLOSED ✅)

Thread the ACTUAL cost; accept a `.search` guard only when the inner cert cost fits the
box budget `k` (the `Provable_finite`-by-enumeration route).

- `playsCheckC : Nat → Prog³ → Action → Option Nat` — returns cert cost (`some n`)/`none`.
- `playsCheckC_sound` — `some n → PlaysProof … n` of cost EXACTLY `n`. Sorry-free.
- `gdRecB d k (.plays p q a)` = run `playsCheckC`, then `decide (n ≤ k)`. Total, structural.
- **`gdRecB_sound` — UNCONDITIONAL, sorry-free: `gdRecB d k φ = true → Provable k φ`.**
  `n ≤ k` gate + `AtomProvable.mk` → `Provable k` at the guard's OWN budget. `gd_budget`
  DISCHARGED, not assumed.
- **`#print axioms`: both depend on `[propext, Quot.sound]` ONLY** — no `sorryAx`, no
  `Classical.choice`, NONE of the project reflection axioms. Budget-match genuinely closed.

## §8 — cost-aware COMPLETENESS (CLOSED ✅)

Three lemmas bottom-up, all sorry-free:
- `plays_det` — play DETERMINISM (engine lacked it): from `playsProof_sound` + `eval_mono_le`.
- `playsCheckC_no_false` — checker never reports a non-existent play (soundness+determinism);
  TAMES the `.ite` tie-break (else-branch witness ⇒ then-guard `b a'` provably fails).
- `playsCheckC_mono_lift` — fuel-lift `F≤F'`, cost `≤`; `.ite` non-monotonicity killed by
  `no_false` (the earlier naive `playsCheckC_step` failed precisely for LACK of determinism).
- `playsCheckC_complete` — every `PlaysProof … n` found at some fuel, cost ≤ n (via `.rec`).
- `gdRecB_accepts` (payoff) — cert of cost ≤ k ⇒ `gdRecB (d+1)` accepts (given inner oracle
  sound+complete). With `gdRecB_sound`, `gdRecB` is a genuine DECISION on the play-atom fragment.

`#print axioms`: completeness lemmas = `[propext, Classical.choice, Quot.sound]` (the
`Classical.choice` only transitively from the engine's classical meta-theory). Still the
three standard axioms; no `sorryAx`, no project reflection axioms.

## §9 — depth recursion: `inner_bwd` IS the fixpoint boundary (finding)

`hfuel` now DISCHARGED (`playsCheckC_complete` proves `F ≤ n+1 ≤ k+1`). `gdRecB_accepts` keeps
only `inner_fwd` (= `gdRecB_sound`, unconditional) + `inner_bwd`. `gdRecB_complete` = per-level
reduction to `inner_bwd`.

**`inner_bwd` does NOT vanish — and WHY is the result, not a gap.** Depth induction bottoms out
iff the certificate's guard-nesting is FINITE: off the Löb fixpoint, yes (dischargeable); AT the
fixpoint CUPOD self-play references itself at the same budget (S3′), nesting INFINITE, no finite
`d` bottoms out, `gdRecB` = false (correct, = evalC none). So `inner_bwd`-as-hypothesis is EXACTLY
"certificate has finite guard-depth" = the precise off-fixpoint condition. A concrete
`searchDepth ≤ d` side-condition carries the same finiteness content, NOT new math. **The depth
recursion closes iff off the fixpoint — exactly where gdRecB is meant to decide.** Boundary
LOCATED inside the completeness machinery.

**Status (final):**
- SOUNDNESS (budget-match) of `gdRecB` — CLOSED, unconditional, sorry-free, `[propext, Quot.sound]`.
- COMPLETENESS (cost-aware) of `playsCheckC` — CLOSED, sorry-free (incl. `F ≤ n+1`).
- `gdRecB_accepts`/`gdRecB_complete` — per-level CLOSED; sole residual `inner_bwd` = the fixpoint
  boundary itself (finite guard-depth = off-fixpoint), NOT a mechanical gap.
- Two hard math pieces (budget-match soundness; determinism-based completeness) DONE.

**Scope caveat:** covers `Provable`-via-`AtomProvable`/`PlaysProof` only (the
false-guard case = exactly this). The reflection rules (`weakenImpl`,
`searchThenSearch_t`, `atomBoxImpl`) and `.struct`/`Derivation` members are NOT
finitely enumerable and out of scope — correctly, since a failed guard is a play-atom
with no certificate.

So: completeness is where Π₁ shows up, because completeness is the direction that has to account for plays caused by failed searches.