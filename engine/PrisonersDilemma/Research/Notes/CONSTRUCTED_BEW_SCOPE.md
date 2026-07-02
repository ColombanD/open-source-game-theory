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
- **B2 — ✅ DONE, VALIDATES over the REAL layer (`Research/Spikes/pblt/BewB2.lean`, sorry-free, 3 std).**
  KEY REFINEMENT: do NOT change base `interp`/`Proves_sound` (they stay `G`-parametric). Instead replace
  the soundness VALUATION `Gctx` with `Gw` — `Gw p G0 c := interp G0 (□(decode c)→p)` at `betaA` codes,
  else `G0`. Then `interp (Gw) (gApp ⌜ψ⌝) = interp G0 (□ψ→p)` by `decode_encode`, and `ctxUnfold_Gw` is
  sound with NO outcome hypothesis — only `hn` (play-atom index ≠ a `betaA` code; structural
  disjointness, tag 0 vs 5). This is much MORE surgical than "change base interp": base `Proves`,
  `interp`, `Proves_sound`, `repr_object` are UNTOUCHED; only the diagonal soundness valuation changes.
  Remaining: `diagFix` at `Gw` (reduces to the same `e_graph`/`selfApply` identity as `diagFix_sound`,
  minus the hp0 that entered only via the shared `Gctx` target-read).
- **B3 — ✅ DONE (`Research/Spikes/pblt/BewB3.lean`, sorry-free, 3 std). PARTIAL WIN + a KEY LIMIT found.**
  Built the UNIFIED system `ProvesU` (plumbing + HBL + repr + ctxUnfold + diagFix + engineLeaf), box :=
  `ProvesU` uniform (`interpU`), diagonal atoms wrapped by `Gw` (now wrapping with the ProvesU-box
  context). `provesU_sound` closes. RESULT:
    • `ctxUnfold` (context representability) — DISSOLVED: closes with only STRUCTURAL conditions
      (`hpp`/`hpb`, `p` gApp/box-free), NO outcome. This is the real constructed-`Bew` payoff.
    • `diagFix` (the diagonal FIXPOINT self-reference) — STILL needs `hp0 : interp G0 p` (the outcome).
      Machine-exposed reason: its two sides denote `ProvesU p (.atom 0)→interp p` (LHS via
      selfApply=.atom 0) vs `ProvesU p (betaA (.atom 0))→interp p` (RHS); antecedents DIFFER, so the iff
      holds only when `interp p` makes both consequents True. Same `hp0` the old `diagFix_sound` used.
  ⇒ **CORRECTED SCOPE: constructed-`Bew` fixes the CONTEXT, not the FIXPOINT.** `provesN_play_extract`
  is REDUCED (ctxUnfold no longer contributes the outcome-read) but NOT fully dissolved — the residual
  `hp0` moved into `diagFix` (the self-reference). This is an honest partial result, not the full
  dissolution B1/B2 suggested.
- **B3-followup — ✅ DONE (`Research/Spikes/pblt/BewB3f.lean`, sorry-free). VERDICT: diagFix's hp0 IS
  removable, but ONLY by rebuilding the diagonal at the PREDICATE level (not by re-denotation).**
  Machine-traced:
    • The genuine diagonal IS outcome-free — `DiagonalLemmaSpike.parametric_diagonal` derives
      `ψ ↔ G(⌜ψ⌝)` from `repr` ALONE (`exact hrepr`, no hp0). So the fixpoint is not intrinsically
      outcome-dependent.
    • WHY it closes there: PREDICATE-level. `ψ := selfApply β`; `selfApply θ := ⟨fun _ k => θ.app (code
      θ) k⟩` DISCARDS the plugged code, so `ψ.app (code ψ)` reduces DEFINITIONALLY to `β.app (code β) =
      ψ`, matching repr's LHS — the self-reference closes by defeq.
    • WHY B3's diagFix needs hp0: the OFml diagonal is SUBSTITUTION-level. `selfApply θ = plug (encode
      θ) θ` genuinely substitutes (plug is HEAD-PRESERVING: `plug_head_preserving`, proven by rfl). So
      `selfApply θ ≠ betaA θ`, the self-code fixpoint `ψ ↔ gApp(⌜ψ⌝)` that `diag_object'` needs is
      unreachable, and `diagFix` bridges the gap by ASSERTING it — sound only via hp0.
  ⇒ FULL route to drop diagFix's hp0: rebuild the OFml diagonal at the predicate level (betaA/selfApply
  discarding the plugged code, à la parametric_diagonal), port `repr_object` (= `repr`, the one
  representability input) to it, feed `diag_object'` the DEFEQ fixpoint. Then ctxUnfold (B3, Gw) +
  diagFix (predicate-level defeq) are BOTH outcome-free ⇒ `provesN_play_extract` FULLY dissolved.
  De-risked: parametric_diagonal PROVES the predicate-level fixpoint outcome-free. The work is porting
  betaA/plug → predicate encoding (touches Syntax/Proves/Diagonal — mechanical but non-trivial).
- **B4-impl — ✅ DONE, LANDED IN THE REAL LAYER (`Syntax.lean` changed; `BewB4`/`BewB4port` spikes,
  sorry-free, 3 std).** The predicate-level diagonal is ONE definitional change:
  `Syntax.selfApply θ := .betaA θ` (was `plug (encode θ) θ`). Then `e ⌜θ⌝ = ⌜betaA θ⌝`, so the REAL
  `repr_object` (unchanged, from `gammaAx`/`betaGamma`) yields the SELF-CODE fixpoint `betaA θ ↔
  gApp(⌜betaA θ⌝)` DIRECTLY — `diagFix_real` (a THEOREM, outcome-free, NO asserted rule).
  `object_pblt_real` then derives object PBLT (`Proves p`) from the Löb premise + `ContextRepr` via the
  base-Proves `object_pblt_of_repr`/`bloeb_object` — 3 std axioms, NO `hp0`, NO PBLT. Verified: real
  `Proves_sound`/`consistency`/`repr_object` STILL hold with the new `selfApply` (soundness preserved);
  FULL engine `lake build` green. `plug` remains defined but is no longer used by the diagonal.
  `Representability.lean` was already broken pre-change (stale `betaA : Nat` signature; superseded module,
  not root-imported) — NOT a regression.
- **B4-wire (next, the finish):** supply `ContextRepr p (betaA θ)` as a base-`Proves` theorem via the
  B3 `Gw`-soundness (outcome-free ctxUnfold), so `object_pblt_real` needs only the Löb premise. Then
  chain FWD (engine `Provable m (□φ→φ)` → `Proves (□p→p)`) + `bridge_BWD_plays` → the engine PBLT
  conclusion with NO `provesN_play_extract`; delete `axiom PBLT`; repoint the 4 consumers → 1 axiom.

- **B4-wire — ✅ CORE DONE (`Research/Spikes/pblt/BewB4wire.lean`; core sorry-free, 3 std). The `hp0`/
  diagonal obstruction is FULLY DISSOLVED, machine-checked.** Built the unified `ProvesU` with `diagFix`
  DERIVED (not a rule): `provesU_sound` is now OUTCOME-FREE (diagFix is no longer a soundness arm; the
  only diagonal arm, `ctxUnfold`, is Gw-outcome-free from B3). Plus `bloebU` (full Löb chain in ProvesU)
  and `extract_atom`/`extract_play` (the extraction STRUCTURE, `ProvesU (encodeF φ) (encodeF φ) → play`,
  side-conditions structural — the play-atom index is not a betaA code, machine-checked). `provesU_sound`/
  `bloebU`/`extract_atom` are all sorry-free on 3 std axioms. **So the outcome-dependence that made
  `provesN_play_extract` axiom-strength is GONE.**
- **REMAINING RESIDUE (`hEL`, one `sorry` in `extract_play`) — NOT the diagonal/hp0 obstruction.** It is
  the FWD-FAITHFULNESS of `engineLeaf` at `interpU`: `provesU_sound` needs each `engineLeaf` leaf
  `interpU`-true; in the pipeline the only such leaf is the engine Löb premise `Provable m (□φ→φ)`, whose
  `interpU` reads `box` as `ProvesU` (not engine `Provable`) — the interpU-box vs engine-box mismatch
  (the same residue the layer's FWD side always carried; `engineLeaf_sound_plays` covers the play-atom
  leaf, the impl/box Löb-premise leaf needs the analogous BWD-faithfulness). This is a SEPARATE, standard
  piece (engine-provable ⟹ true), and it does NOT reintroduce `hp0`. It IS required to actually delete
  `PBLT` end-to-end.

## Immediate next action
The B-series achieved its goal: the diagonal `hp0` obstruction (the reason `provesN_play_extract` was
axiom-strength) is DISSOLVED — machine-checked, sorry-free core. To DELETE the axiom end-to-end, close
the one remaining residue: **B4-hEL** — FWD-faithfulness of the `engineLeaf` Löb-premise leaf at
`interpU` (relate `ProvesU p (encodeF φ)` to engine `Provable`; the box-mismatch/BWD piece). This is a
different obligation from the one the B-series removed; standard in content (engine soundness), but real.
