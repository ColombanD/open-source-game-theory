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

1. **Arithmetic lemma** `log2_add_le : ∀ c, ∃ K, ∀ k ≥ K, Nat.log2 k + c ≤ k`.
   Provable from `Nat.log2_lt` + `Nat.lt_two_pow_self` (as in the existing
   `hLog` proofs), but **needs a careful core-Lean proof — no Mathlib**
   (`lt_of_lt_of_le`, `norm_num` unavailable). Likely via `2^(c+1)` threshold.
2. **`subst` size bound** `(φ.subst me opp).size ≤ φ.size * (me.size + opp.size + 1)`
   (or a tighter/cleaner bound — TBD). Structural induction over the mutual
   `Prog`/`Formula`. `subst` replaces `.self`/`.opp` (size 1) by `me`/`opp`, so
   size grows; find the exact provable bound.
3. **Redefine `Derivation.size`** to be character-faithful (e.g. via the
   conclusion's `Formula.size`, or per-rule sums that bound it), in
   [Derivation.lean](engine/PrisonersDilemma/Derivation.lean) + the `sound`
   case in BaseTheorems still valid.
4. **Per-rule size-bound lemmas**: `(searchBranch …).size ≤ <explicit>`,
   similarly `simStep`/`hypSyll`/`modusPonens`. The searchBranch one is the
   crux (uses steps 1–2).
5. **`atom_complete` with expansion constant**: introduce abstract
   `axiom proof_expansion_c : Nat` (Critch's `e*`) and state
   `play fuel p q = some a → AtomProvable (proof_expansion_c * fuel + …) (…)`.
   Propagate through `proofSearch_complete_plays` and the bot proofs (their
   chosen budgets `1,2,5` become `c*… + …`; the `decide` budget-monotone
   bounds become symbolic `Nat` inequalities — provable but not by `decide`).
6. **Tighten the Löb chain** so `size` is *load-bearing*:
   - PBLT premise: `Provable (f k) (□_{f k} φ_k → φ_k)` instead of
     `∃ m, Provable m (…)`.
   - `cupod/dupoc_loeb_premise`: exhibit the `hypSyll(searchBranch, simStep)`
     derivation **and** prove `its size ≤ f k`, adding a `k ≥ K₀` side-condition
     (from step 1). This is where `Derivation.size` finally *matters*.
7. **Fallout**: every `proofSearch_true_for_*` / `*_vs_*` budget constant, and
   the monotone steps, re-expressed with the constants. Full `lake build` green;
   confirm via `#print axioms` and that `size` appears in the Löb chain.

## Scoping note

Steps 1–2 are self-contained arithmetic/induction grinds (Mathlib-free).
Steps 3–6 reshape the trust base and both Löb premises. Step 7 ripples through
all bot proofs. Treat as a dedicated multi-session effort; steps 1–2 can be
done and committed independently as pure lemmas before touching the engine.
