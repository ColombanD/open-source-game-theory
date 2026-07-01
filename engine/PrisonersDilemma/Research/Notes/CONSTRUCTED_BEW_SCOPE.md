# Scope — constructed `Bew`/context predicate: making `ContextRepr` DERIVED (route A)

**Goal.** Discharge the one real gap in PBLT-removal: `ContextRepr p ψ : ⊢ gApp(⌜ψ⌝) ↔ (□ψ → p)`,
currently asserted via the outcome-relative `Gctx` valuation trick (`ProvesC`/`ProvesN`). Replace it
with a DERIVATION from a representability rule — exactly the pattern the layer already uses for
`Γ_e`/`gammaAx`/`betaGamma`. Then `bloeb_object` (sorry-free) + `bridge_BWD_plays` (sorry-free) close
the engine PBLT with NO `provesN_play_extract`.

## The precise diagnosis (why `ctxUnfold` is the ONLY opaque piece)

The layer is ALREADY faithful for the `β`/`Γ_e` half:
- `Representability.lean`: `PrAr` DERIVES `gammaAx`/`betaGamma`/`repr` from `atomTrue`
  (Σ₁-completeness) + `leibniz` (equality elim) — both SOUND rules mirroring PA theorems. `gApp y = G(y)`
  is representability-based there, not opaque.
- The OPAQUE piece is `ctxUnfold : gApp(⌜ψ⌝) ↔ (□ψ → p)` (Diagonal.lean). It is asserted as a `ProvesC`
  rule, sound ONLY via `Gctx` (which reads `interp G0 p` — the outcome). That outcome-dependence is what
  propagates to `provesN_play_extract`. It is the LAST asserted, non-representability-derived rule.

## Critch's actual mechanism (§5) — `G` is a computable-function representability, NOT structural decode

Critch's diagonal predicate: `G(n,k) := (∃m: Bew(m, Eval₁(n,k), g(k))) → p(k)`. Crucially:
- `gApp(⌜ψ⌝) = G(⌜ψ⌝) = □_{g}ψ → p` holds because `Eval₁(⌜ψ⌝,k) = ⌜ψ(k)⌝` is REPRESENTABLE (Cori-Lascar
  6.8, the same theorem `Γ_e` uses), NOT because `gApp` structurally decodes its argument.
- So `ctxUnfold` should be DERIVED from a representability rule for the computable "wrap" function
  `wrap(n) := #(□(decode n) → p)`, exactly as `betaGamma` is derived from `Γ_e`'s representability.

**This means the fix does NOT require a structural `decode : Nat → OFml` inside formulas** (which is
impossible — a formula is a fixed tree). It requires ONE more representability rule + its graph atom,
mirroring `gammaAx`/`betaGamma`.

## The concrete change (mirrors the existing `Γ_e` pattern exactly)

1. **A second graph atom + computable function** (like `gamma`/`e`):
   - `wrap (p : OFml) (n : Nat) : Nat := encode (.imp (.box (decode n)) p)` where `decode` is the
     choice-fibre partial inverse of `encode` (total via the same `if ∃φ, encode φ = n` trick as `e`).
     `decode` need NOT be a formula constructor — it is a meta `Nat → OFml`, used only to DEFINE `wrap`.
   - `wrap_graph : wrap p (encode ψ) = encode (.imp (.box ψ) p)` — PROVEN from `encode_inj` (twin of
     `e_graph`). This is the arithmetic heart, and it is `rfl`-ish / injectivity, no open content.

2. **A representability rule** `ctxRepr` (twin of `betaGamma`/`leibniz`), added to the `PrAr`-style
   derived layer, NOT asserted opaquely:
   - `ctxRepr (p : OFml) (n y : Nat) : ⊢ Γ_wrap(n, y) → (gApp n ↔ gAppTarget y)` where `gAppTarget y`
     is the atom denoting "the formula coded by `y` holds". Equivalently, collapse directly:
   - `gAppUnfold (p ψ : OFml) : ⊢ gApp(encode ψ) ↔ (□ψ → p)`, DERIVED by: `Γ_wrap`-representability at
     `encode ψ` (gives `wrap p (encode ψ) = encode(□ψ→p)` via `wrap_graph`) + Leibniz, SOUND because
     `gApp c` denotes "formula coded c holds" and `wrap` maps `⌜ψ⌝ ↦ ⌜□ψ→p⌝`. KEY: this soundness is
     UNCONDITIONAL (holds for every valuation once `gApp c := (formula coded c is true)`), NOT
     `Gctx`/outcome-relative — because it is pure representability of a computable function, exactly like
     `betaGamma`.

3. **Re-denote `gApp`** in `interp` so the derivation is sound: `gApp c := (the formula coded by c is
   true under interp)`, i.e. `gApp (encode φ) := interp (decode (encode φ)) = interp φ`. Then
   `gAppUnfold` is sound by `wrap_graph` — no free-valuation problem, no `Gctx`. (This is the substantive
   re-denotation: `gApp` stops being a free `G c` atom and becomes "truth of the coded formula".)

4. **Drop `ProvesC`/`ProvesN`/`Gctx`** and the `provesN_play_extract` obligation: `ctxUnfold` becomes
   `gAppUnfold` (derived, unconditional), so `contextRepr_provesC` is replaced by a base-`Proves`
   theorem, and `bloeb_object` runs over base `Proves` directly.

## Risk assessment

- **The `wrap`/`decode`/`wrap_graph` arithmetic** — LOW risk, twin of `e`/`e_graph` (already done). The
  `decode` choice-fibre + injectivity is mechanical.
- **Re-denoting `gApp` := "coded formula is true"** — MEDIUM. This is the substantive move. Must check:
  (a) `betaGamma`/`repr` still sound under the new `gApp` denotation (they should — `betaA`/`gApp`
  denotations stay consistent via `e`); (b) `Proves_sound` still holds. The soundness interp changes,
  so all `_sound` lemmas over `interp` need re-checking. This is the real work.
- **`gAppUnfold` soundness UNCONDITIONAL** — the payoff to verify: unlike `ctxUnfold_sound` (needs `hp`),
  `gAppUnfold` must be sound for ALL valuations. If it is, `provesN_play_extract` is GONE. If it secretly
  still needs the outcome, the diagnosis is wrong and we escalate. **This is the make-or-break check —
  do it FIRST as a spike before the full re-denotation.**
- **No `∀`-quantifier needed** — the meta-∀k fibre (`φ : Nat → Formula`) already handles Critch's `∀k`;
  `gAppUnfold` is per-`ψ`, no object quantifier.

## Milestones

- **B1 (make-or-break spike) — ✅ DONE, PASSED (`Research/Spikes/pblt/BewB1.lean`, sorry-free).**
  Defined `decode`/`wrap`/`wrap_graph`, re-denoted `gApp`, and proved `gAppUnfold_sound :
  gApp(⌜ψ⌝) ↔ (□ψ→p)` UNCONDITIONALLY (no `hp`/outcome, any `Prov`/valuation) — depends on NO axioms
  (`Iff.rfl` after the `GappOK` rewrite). `gappCanonical_OK` shows the denotation is realizable
  (non-vacuous) for the `gApp`-free PBLT target. **Diagnosis CONFIRMED: re-denoting `gApp` dissolves the
  outcome-dependence** (old `ctxUnfold_sound` needed `hp`; new `gAppUnfold_sound` needs nothing).
  CORRECTION from B1: the right denotation is `gApp c := truth of ⌜□(decode c)→p⌝` (Critch's
  `G(n):=□(decode n)→p`), NOT "coded-formula-true" (`decode c`) — the naive version gives `interp ψ` not
  `interp(□ψ→p)`. The `wrap` function carries the `□·→p` wrapping.
- **B2:** port the re-denotation into `Proves.lean`'s `interp` (`gApp c := interp (□(decode c)→p)` via
  `wrap`); re-verify `Proves_sound`, `repr_object`, `PrAr_sound` under it. THE MEDIUM-RISK STEP (the
  soundness interp changes). Care: `gApp`'s denotation now recurses through `wrap`/`decode` — keep it on
  the `gApp`-free fragment (PBLT target) so it stays well-founded, as B1's `gappCanonical` does.
- **B3:** replace `ctxUnfold`/`ProvesC` with derived `gAppUnfold`; rebuild `diag_object'`/`bloeb_object`
  over base `Proves` (no `ProvesN`, no `Gctx`).
- **B4:** wire to engine — `bloeb_object` + `bridge_BWD_plays` → engine PBLT with no
  `provesN_play_extract`; delete `axiom PBLT`; repoint the 4 consumers → 1 axiom.

## Immediate next action
B1 PASSED → the route is open. Next: **B2** — port the re-denoted `gApp` into `Proves.lean`'s `interp`
and re-verify the `_sound` lemmas. This is the medium-risk step (changing the soundness model).
