# Proof Length: making budgets character-faithful (roadmap)

## Why

`□_k φ` is meant (critch22) as "φ has a proof of **≤ k characters**". Two places
treat "length" loosely:

1. **`Derivation.size`** counted *rule applications* (`searchBranch = 1`
   regardless of how big its conclusion `□_k(ψ.subst me opp) → plays me opp a`
   is). Not a character count.
2. **`atom_complete`** ties proof budget to eval `fuel` *exactly*
   (`play fuel → AtomProvable fuel`). The honest σ₁ bound is `O(fuel)` — a proof
   that "p plays a in `fuel` steps" is the `fuel`-step trace, length `c·fuel + d`
   (Critch's proof-expansion constant `e*`, Appendix B(d)) — not exactly `fuel`.

These didn't matter while `Derivation.size`'s value was never compared to a
concrete number (it's used only existentially in `derives`/`proofSearch_monotone`
or additively in `K_provable`). But once we want the budget to mean characters,
and `atom_complete` to be faithful, both must be made concrete.

## Done (committed, green)

`Prog.size` / `Formula.size` in [Program.lean](engine/PrisonersDilemma/Program.lean):
character counts, numerals costing `Nat.log2 k + 1` (Appendix B(b)), every node
`(Σ children) + 1`.

**Steps 1–3** in [SizeLemmas.lean](engine/PrisonersDilemma/SizeLemmas.lean) +
[Derivation.lean](engine/PrisonersDilemma/Derivation.lean) +
[BaseTheorems.lean](engine/PrisonersDilemma/BaseTheorems.lean):

1. `log2_add_le` — `∀ c, ∃ K, ∀ k ≥ K, Nat.log2 k + c ≤ k`. Threshold `2*c`;
   uses `Nat.lt_two_pow_self` + `Nat.log2_lt` + `omega`. Mathlib-free. ✅
2. `subst_size_le` — `(p.subst me opp).size ≤ p.size * (me.size + opp.size + 1)`
   and likewise for `Formula`. Proved via joint `Prog.rec` / `Formula.rec`;
   constants handled by `le_self_mul`; linear combination via `Nat.add_mul` + `omega`. ✅
3. `Derivation.size` redefined as **conclusion's `Formula.size`** (was rule count).
   `K_provable` updated: `ψ.size ≤ (φ→ψ).size ≤ n`; `_hF` parameter now vestigial
   but kept for API stability. Full `lake build` green (29/29). ✅

## The key insight (why this is worth it)

Making `Derivation.size` faithful **explains PBLT's otherwise-mysterious
hypothesis `f(k) ≻ O(lg k)`**:

- The `searchBranch` derivation for CUPOD self-play concludes a formula
  containing `me = opp = CupodBot k` *literally*. `|CupodBot k| ≈ log2 k + c`
  (it embeds the numeral `k`). So the derivation's **character size is
  `~ log2 k + const`**.
- Critch's `□_{f(k)}` requires that proof to fit in `f(k)` characters:
  `log2 k + c ≤ f(k)`.
- That holds **iff `f(k) ≻ O(lg k)`** — exactly PBLT's hypothesis.

So the faithful model turns `f(k) ≻ O(lg k)` from an opaque side-condition into
a *derived requirement*: "the source-transparency proof fits in CUPOD's search
budget." Likewise the "for k large enough" in CUPOD's theorem becomes "k past
the point where `log2 k + c ≤ k`."

## Remaining steps (each with its proof obligation)

1. ~~**Arithmetic lemma** `log2_add_le`~~ ✅ done — see `SizeLemmas.lean`.
2. ~~**`subst` size bound**~~ ✅ done — `subst_size_le` in `SizeLemmas.lean`.
3. ~~**Redefine `Derivation.size`**~~ ✅ done — conclusion `Formula.size` in
   `Derivation.lean`; `K_provable` updated in `BaseTheorems.lean`.
4. ~~**Per-rule size-bound lemmas**~~ ✅ done — `searchBranch_size_le`,
   `simStep_size_le`, `eqRefl_size`, `hypSyll_size_le`, `modusPonens_size_le`
   in `SizeLemmas.lean`.
5. ~~**`atom_complete` with expansion constant**~~ ✅ done — abstract
   `proof_expansion_c` / `proof_expansion_d` (Critch's `e*`, `e₀`) in
   `Axioms.lean`; `atom_complete` now gives budget `proof_expansion_c * fuel +
   proof_expansion_d`. `atom_monotone` added (was automatic before). All bot
   proofs updated to lift via `atom_monotone` / `proofSearch_monotone`.
6. ~~**Tighten the Löb chain** so `size` is *load-bearing*~~ ✅ done —
   - **PBLT stays faithful to Critch**: the OUTER proof (of the implication
     `□_{f k} φ → φ`) is left *unbudgeted* — `∃ m, Provable m (…)` — matching
     Critch's turnstile `⊢`, which puts no size annotation on the implication's
     proof. (A prior iteration pinned the outer proof to budget `f k`; that is a
     sound *strengthening* of the hypothesis but a distortion of Critch, so it
     was reverted. The inner box budget `f k` is of course still present and
     load-bearing — `f ≻ O(lg k)` is what makes `□_{f k} φ` a non-vacuous claim
     about `φ`, whose proof is `Θ(lg k)`.)
   - **`Derivation.size` is kept load-bearing in the *library*, not the axiom.**
     All four Löb premises (`cupod_loeb_premise`, `cupod_mirror_loeb_premise`,
     `dupoc_loeb_premise`, `dupoc_mirror_loeb_premise`) return the *tight*
     `∃ K₀, ∀ k ≥ K₀, Provable k (□_k φ → φ)`. They **exhibit the explicit
     derivation** (`searchBranch`, or `hypSyll(searchBranch, simStep)` for the
     MirrorBot legs) and **prove its size ≤ k**:
       - self-play size = `5 * log2 k + 33` (each bot costs `log2 k + 7`);
       - MirrorBot legs size = `3 * log2 k + 25` (MirrorBot costs 3);
     discharged by `linear_log2_add_le 5 33` / `linear_log2_add_le 3 25`. This
     is where `Derivation.size` does real work. The four `*_vs_*` callers pass
     `K₀` as PBLT's `k₁` and *weaken* `Provable k (…)` to `∃ m, Provable m (…)`
     when feeding the (unbudgeted) PBLT hypothesis.

   **Key simplification found:** the `searchBranch`/`simStep` derivations land in
   their target formula types *definitionally* (the `ψ.subst me opp` guard
   unfolds by `Formula.subst`/`Prog.subst` reduction), so no `simpa`/cast is
   needed — `Derivation.searchBranch … rfl` typechecks directly at the closed
   formula, and the size is read off by `simp only [Derivation.size,
   Formula.size, Prog.size, <Bot>, MirrorBot]; omega`.

7. ~~**Fallout**~~ ✅ done — `lake build` green (3129 jobs). `#print axioms` on
   all four `*_vs_*` theorems: `[propext, Classical.choice, Quot.sound,
   AtomProvable_sound, PBLT]` — the `searchBranch` size bound is now discharged
   *constructively* (via `linear_log2_add_le`, Mathlib-backed, no axiom), and
   the `proof_expansion_*` axioms aren't even in the Löb-chain dependency closure
   (only on the atom-completeness paths for non-Löb opponents).

## Status: COMPLETE ✅

All 7 steps done. `□_k φ` now means "φ has a proof of ≤ k characters" faithfully:
`Derivation.size` is the conclusion's character count, `atom_complete` is linear
in fuel (Critch's `e*`), and PBLT's `f(k) ≻ O(lg k)` hypothesis is now a *derived
requirement* — the source-transparency proof (size `~ log2 k + const`) must fit
in the search budget `f(k)`, proved via `linear_log2_add_le`.

## Follow-up (separate reform)

`atom_complete` is still an **axiom** — the bulk of the library's proof-length
accounting (all `.search`-free opponents) routes through it. `AtomProvableReform.md`
scopes making it a *theorem* via a constructive play-certificate inductive
(`PlaysProof`); a probe confirms the apparent self-reference obstruction is an
artifact of the `opaque AtomProvable` layering, not a real one. Not yet integrated.
