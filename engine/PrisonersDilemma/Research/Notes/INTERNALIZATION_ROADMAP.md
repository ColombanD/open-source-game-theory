# Internalization Roadmap — making the engine's own S Löb-capable (deleting `PBLT` for real)

**Why this route (context).** The B-series (`CONSTRUCTED_BEW_SCOPE.md`) finished the Löb mathematics in
the side reflection layer: diagonal DERIVED (`selfApply := betaA`, B4), soundness outcome-free (B3),
chain sorry-free. What it PROVED CANNOT work is the *transfer*: an object proof beside the engine cannot
be reflected into `Provable` (BWD hits the mp-cut; a bridge constructor is unsound; `Formula` can't
express the diagonal). And conceptually it must fail: `eval`'s oracle is `decide (Provable k φ)` — only
`Provable` itself proving the Löb chain discharges PBLT. **So: internalize the (now fully blueprinted)
reflection machinery into `Formula`/`Provable` themselves.** Then the chain concludes
`∃m, Provable m (φ k)` directly — PBLT verbatim, no bridge, no BWD, no extraction.

---

## Blast radius (measured against the code, 2026-07-01)

### MUST change — total recursion / total matches on `Formula` (each needs new cases)

| Site | File | Nature of change | Risk |
|---|---|---|---|
| `Formula` inductive + `deriving DecidableEq` | `Program.lean` | add diagonal constructors | design-heavy, see I0 |
| `Formula.subst` (mutual w/ `Prog.subst`) | `Program.lean` | new cases (diagonal atoms: subst does NOT descend — frozen, like `.eq` RHS) | low |
| `Formula.size` (mutual w/ `Prog.size`) | `Program.lean` | new cases (numerals cost `log2`, as `.box`) | low |
| `Formula.interp` | `Dynamics.lean` | new clauses = the FIXED `Gw`-style denotations (B3/B4 patterns) | **medium — the design core** |
| `Provable` inductive | `Derivation.lean` | add `gammaAx`/`betaGamma`/`ctxUnfold` rules + size side-conditions | medium |
| `Provable_sound` (via `Provable.rec`, positional arms) | `BaseTheorems.lean` | add the 3 new arms (B3/B4 soundness proofs, at the fixed interp) | medium |
| `proofSearch_spec`/`_monotone` + size lemmas | `BaseTheorems.lean`/`SizeLemmas.lean` | re-check; new rules must be monotone (size-gated like existing) | low-med |
| `decGuard` | `ComputableEval/Computable.lean` | new atoms → `none` (partial evaluator stays sound) | low |
| `Forbidden` | `ComputableEval/Exclusion.lean` | benign new cases | low |
| `Formula.searchDepth` | `ComputableEval/DecMeasure.lean` | new cases → 0 | low |
| `Provable_fin` | `ComputableEval/PlaysCheck.lean` | scope note or benign cases (off-core decider) | low |
| `CimcicForbiddenC`-style total matches | `Theorems/LlmGenerations/CIMCIC.lean`, `DIMCID.lean` | catch-all `_ => False` cases | low |
| `encodeF` + `formulaCode` (+ injectivity) | `Reflection/Bridge.lean` | new cases + extend `formulaCode_inj` | low (mechanical, same pattern) |

### Does NOT change

- `Prog`, `Prog.subst/size`, **`eval`** (matches `Prog` only; guard just passes φ to `proofSearch`).
- `Derivation` and `PlaysProof` (indexed by `Formula`, constructors are shape-specific — no totality).
- `atom_complete` / `atom_complete_false_guard` (play-atom layer untouched; the 1-axiom floor stays).
- The **22 bot/theorem files**: they consume `PBLT`'s *signature*, which is preserved verbatim
  (`PBLT` becomes a theorem with the same statement). Only the 4 PBLT consumers get a one-line
  `Axioms.PBLT` → `BaseTheorems.PBLT` repoint.
- Hidden breakage reserve: proofs doing `simp [Formula.size]`/exhaustive `cases` may surface at build —
  the compiler finds them all; budget ~1 session of whack-a-mole.

---

## ✅ I0 DESIGN FREEZE — DONE (2026-07-01, validated end-to-end in `Research/Spikes/pblt/I0Design.lean`)

The spike is a faithful mini-engine (engine-exact `boxIntro`/`axK`/`box4`/`app`/`implTrans` signatures,
size-gated) and it validates the ENTIRE design: `bloeb_mini` (the full internal Löb chain) and
`Prov_sound` (all arms) close with **NO axioms at all**; `sizes_ok` (kill-criterion) on 3 std. The
frozen design is SIMPLER than this roadmap's draft — no `gamma`, no `gApp`, no Formula-level
encode/decode, `interp` stays a plain (computable-shape) def:

1. **ONE new `Formula` constructor:** `.diag (g : Nat) (tgt : Formula)` — the Löb fixpoint sentence for
   target `tgt` at box budget `g`. Its `interp` is SELF-REFERENTIAL BY DESIGN:
       `| .diag g t => Provable g (.diag g t) → t.interp`
   Legal (recursion descends only into `t`; `Provable` does not recurse through `interp`). This is B4
   internalized: the fixpoint is DEFINITIONAL, so the diagonal legs are sound by `id`. Same design
   pattern as `.box n φ ↦ Provable n φ`; the meta-justification that such a sentence exists in a
   faithful arithmetization is the (kept) Reflection layer's DERIVED diagonal (B4 `repr_object`).
   - `subst`: FROZEN (`.diag g t ↦ .diag g t`, like `.bot`/`.eq`-RHS — the diagonal is a closed
     meta-construction; it never appears in bot source, only in the meta Löb chain).
   - `size`: `(log2 g + 1) + t.size + 1` (numeral cost, like `.box`).
2. **FOUR new `Provable` rules** (all size-gated like existing constructors; soundness arms trivial):
   - `diagF`/`diagB` — the fixpoint legs `ψ → (□_g ψ → t)` and `(□_g ψ → t) → ψ` for `ψ := .diag g t`;
     sound = `id` (the interp IS the fixpoint).
   - `axKf` — object-FORMULA K `□_k(φ→α) → (□_k φ → □_k α)`; sound = `app`. NEEDED because the engine's
     `axK` is RULE-form and Löb's step h3 requires the formula (rule-K provably insufficient there).
   - `impS2` — closed composition rule `⊢ φ→(ψ→χ) ⟹ ⊢ φ→ψ ⟹ ⊢ φ→χ`; sound = application. Replaces the
     side layer's deduction theorem (both premises closed, so rule form suffices).
3. **TIGHT premise, unified subscript:** `bloeb_engine` takes `∀k>k₁, Provable (f k) (□_{f k} φk → φk)`
   and runs everything at subscript AND budget `u := f k` — no `boxMono`, no deduction theorem, no
   E-expansion (the engine's cost model is conclusion-size, killing Critch's `E` entirely). The
   consumers ALREADY produce the tight premise (`dupoc_loeb_premise : Provable k (□_k … → …)`); they
   currently LOOSEN it to feed the ∃m axiom — the repoint just drops that loosening (4 call sites).
   The ∃m-loose signature is NOT derivable from tight in general; the replacement theorem is tight.
4. **KILL-CRITERION PASSED** (`sizes_ok`): the largest chain formula has size exactly
   `9·log2 k + 6·(φ k).size + 23`; with consumers' `φ k` of size `A·log2 k + B` (DupocBot ≈ `2·log2 k +
   15`) every side-condition is `A'·log2 k + B' ≤ k`, closed by `linear_log2_add_le` beyond `K₀` —
   absorbed by the `∃k₂` conclusion. The chain needs 13 such conditions (hs1–hs13 in the spike), all
   smaller or equal.

BLAST-TABLE SIMPLIFICATION vs the draft: the `encodeF`/`formulaCode` rows stay (one `.diag` case each,
trivial); the `gamma`/`gApp`/Formula-encode/noncomputable-interp complexity is GONE.

## Milestones

- **I0 — design freeze (≈1 session).** The four decisions above, written down with exact constructor
  signatures and the budget plan. Gate: signatures typecheck in a scratch file.
- **I1 — syntax blast (≈1–2 sessions, mechanical).** Add constructors; fix ALL table-1 total matches;
  `encodeF`/`formulaCode` extension + injectivity. Gate: **full `lake build` green with zero behavior
  change** (no new rules yet — old theorems untouched by construction).
- **I2 — semantics (≈1 session).** New `interp` clauses (fixed `Gw`-style denotations); `e`/`e_graph`
  at `Formula` level. Gate: `Formula.interp` compiles; old clauses definitionally unchanged.
- **I3 — proof rules + soundness (≈2–3 sessions).** Add `gammaAx`/`betaGamma`/`ctxUnfold` to `Provable`
  (size-gated, monotone); extend `Provable_sound` (the B3/B4 arms — ctxUnfold outcome-free at the fixed
  denotation, betaGamma via `e_graph`); re-verify `proofSearch_spec`/`_monotone`. Gate: build green,
  `#print axioms Provable_sound` = 3 std + `atom_complete_false_guard` only.
- **I4 — the internal Löb chain (≈3–5 sessions, THE hard chunk).** `diagFix_engine` derived (B4
  pattern); `bloeb_engine : (∀k>k₁, ∃m, Provable m (□_{f k} φk → φk)) → ∃k₂,∀k>k₂,∃m, Provable m (φ k)`
  — the §5 chain INSIDE `Provable`, with real budget bookkeeping (Critch's `g ≺ h ≺ f` arithmetic; the
  `∃m`-unbudgeted premise shape and `∃k₂` threshold give slack; `mutual_loeb` already demonstrates the
  size-side-condition style). Gate: `bloeb_engine` sorry-free, no PBLT in its axiom footprint.
- **I5 — delete the axiom (≈1 session).** `theorem PBLT := bloeb_engine`-wrapper with the EXACT current
  signature; repoint the 4 consumers (DupocBot, CupodBot, PrudentBot, JustBot — signature-identical);
  delete `axiom PBLT`; full `#print axioms` sweep of all outcome theorems → **1 axiom**
  (`atom_complete_false_guard`). Docs: Axioms.lean header, CLAUDE.md, EXPLICIT_S_PROPOSAL, README.
- **I6 — aftermath (≈1 session).** Update COMPUTABLE_EVAL_NOTES (after internalization every `Provable`
  member has a real derivation tree — no witness-free members; whether that makes `proofSearch`
  decidable is a SEPARATE question, do NOT promise it); retire superseded Reflection modules
  (`ProvesC`/`ProvesN`/`Native`/`Engine` become historical); memory updates.

**Total estimate: ~9–13 focused sessions (2–4 weeks of thesis time).**

## Risk register (ranked)

1. **Budget threading in I4 (HIGH).** The B-series kept the object box budget-free; the engine box is
   budgeted, so the diagonal chain must do Critch's §5 `g/h/f` arithmetic with character sizes of the
   diagonal formulas (which contain numerals of their own codes → `log2` growth — exactly what
   abbreviations/`E` handle in the paper). Mitigation: the paper proof is line-by-line explicit; the
   engine already does this style of bookkeeping (`mutual_loeb`, `dupoc_loeb_premise`); the `∃m`/`∃k₂`
   slack means bounds only need to be ACHIEVABLE, not tight. Kill-criterion: if a diagonal formula's
   size cannot be bounded `≺ f(k)` for the consumers' `f = id`, the thresholds fail — check EARLY in I0
   with a size estimate.
2. **New `Provable` rules vs existing meta-theorems (MED).** `proofSearch_monotone`, `Provable.rec`
   consumers, `ComputableEval` soundness. Mitigation: all new rules size-gated exactly like `boxIntro`;
   `decGuard → none` keeps evalC sound; the compiler enumerates every breakage.
3. **Soundness of target-carrying atoms (MED-LOW).** B3/B4 proved the patterns, but at a parametric
   valuation; here the denotation is FIXED in `interp` — actually SIMPLER (no `Gw` disjointness
   side-conditions: the atom carries its target, no code-collision with play-atoms possible). Verify in
   I2 gate.
4. **Hidden exhaustive matches (LOW).** Compiler-found; budgeted in I1.

## What this buys / does not buy

- **Buys:** `PBLT` deleted → **1 axiom** (`atom_complete_false_guard`, machine-proven irreducible).
  "S made explicit, bounded Löb proven inside it" — the headline the thesis wants.
- **Does NOT automatically buy:** computable `eval`. Decidability of the enriched `Provable` is a
  separate question (mp-cut enumeration) — do not conflate (route B, closed for now).
