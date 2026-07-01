# Roadmap — removing the `PBLT` axiom (Path A)

Where things stand and the precise remaining sub-steps. Companions: `EXPLICIT_S_PROPOSAL.md`,
`Research/Spikes/pblt/`.

## ⚑⚑ SCOPING PIVOT (what removing PBLT ACTUALLY requires — machine-checked)

The object-system (`Reflection/`) route hit `provesN_play_extract`, which is EQUIVALENT to PBLT (below).
But scoping the alternative revealed a much shorter path that the object detour obscured:

**The engine `Provable` ALREADY has the full HBL toolkit** — `boxIntro` (nec), `app` (object MP),
`axK` (K), `box4` (four), all sound, no axioms (added in earlier sessions eliminating
`box_provable`/`boxInternalize`). And extraction at the `Provable` level is TRIVIAL:
`Provable k (plays…) → the play` is just `Provable_sound` (machine-checked). So the `provesN_play_extract`
obstacle was an ARTIFACT of working in a separate object system — it vanishes at `Provable`.

**Removing PBLT therefore reduces to: run the bounded-Löb chain DIRECTLY at `Provable k`.** The chain
(`bloeb_native`'s shape) needs, at `Provable`:
  1. nec / K / four / MP — ✅ ALREADY PRESENT (`boxIntro`/`axK`/`box4`/`app`).
  2. a `Provable`-level DEDUCTION theorem (`impI`) for the 3 hypothesis discharges — NOT present; the
     genuine missing piece #1. (`app` is MP but there's no `Provable k a → Provable k b ⊢ Provable k
     (a→b)`; needs a hypothesis-form `Provable` or a direct combinator derivation.)
  3. the DIAGONAL fixpoint `Provable k (ψ ↔ (□_k ψ → p))` — missing piece #2 (the same diagonal the
     `Reflection` layer built via `diagFix`, but now needed as a `Provable` fact — the budget-faithful
     `k = box-k` coincidence is the known Wall-1/S3' subtlety here).
Then `bloeb` at `Provable` gives `Provable k p`; `Provable_sound` gives the play; DONE — no object
layer, no bridge, no `extract`.

**Revised estimate:** the two missing pieces (a bounded `Provable` deduction theorem + the diagonal as a
`Provable` fact) are the REAL scope of removing PBLT. The diagonal (#2) carries the irreducible Löb
content (still equivalent to PBLT — no free lunch), but the framing is far cleaner than the object
detour: everything lives in one system (`Provable`) the engine already trusts, and the deduction
theorem (#1) is standard. The `Reflection/` layer remains a valid, sorry-free metamath artifact and an
independent second proof of the diagonal's constructibility, but the SHORTEST path to deleting the axiom
is the direct-at-`Provable` route.

## ⚑ HEADLINE RESULT (machine-established across the reflection layer)

The full metamathematical development (`Reflection/`: Syntax, Proves, Representability, Deduction,
Bpsb, Diagonal, Native, Engine — all sorry-free, 3 std axioms) REDUCES `PBLT` to a SINGLE clean
proof-theoretic statement: `provesN_play_extract` (an object proof of a play-atom yields the engine
play). This is a genuine reduction — every OTHER piece (diagonal, repr, HBL, deduction, faithfulness
bridge FWD/BWD, the bounded-Löb chain `bloeb_native`) is PROVEN. But it is NOT a simplification of the
hard content: **`provesN_play_extract` is EQUIVALENT in strength to the PBLT conclusion itself**
(machine-checked: `engine_pblt_plays` derives PBLT from it; and PBLT+FWD reconstruct it). The
irreducible content — bounded Löb PRODUCES the outcome — moved from an opaque axiom into a precise
proof-theoretic lemma, but did not get cheaper. Closing it = proving Löb's computational content: a
`ProvesN` derivation of a play-atom (whose last rule is `mp` off the diagonal fixpoint) NORMALIZES to a
finite play witness. That is a real normalization theorem over `ProvesN`, not plumbing — the honest
remaining core. `atomCode` injectivity (i) is the only routine leftover.

## The reduction (what's proven, what remains)

Removing `PBLT` decomposes into a chain of pieces, all now identified. Two are PROVEN, the rest are
the work:

```
PBLT  ⟸  pblt_of_bpsb         ✅ PROVEN sorry-free (the §5 chain over the BPS interface)
       ∘ parametric_diagonal   ✅ shape PROVEN (DiagonalLemmaSpike; rests on `repr`)
       ∘ repr                  ✅ DERIVED + SOUND on a toy object S (ReprObjectSpike: inductive ⊢_S,
                                  repr_object from sound gammaAx+betaGamma, Proves_sound). Arithmetic
                                  core in ReprConcreteSpike. Remaining is ENGINEERING: wire
                                  Γ_e/gammaAx/betaGamma into a real arithmetized S⊇PA (no open risk).
       + HBL D1–D3             ✅ TRANSPLANTED + SOUND + NON-VACUOUS (HBLObjectSpike). D1/D2/D3 as
                                  object Proves rules with interp(box)=Proves; Proves_sound +
                                  consistency (¬Proves atom); mutual_loeb_object chains them into
                                  □φP→φP. Remaining = re-thread the Formula.size budgets (orthogonal).
       + the bridge            ✅ NO FATAL MISMATCH (FaithfulnessBridgeSpike). engine_PBLT_of_bridge
                                  composes; BWD (the dangerous S→engine dir) is DERIVABLE for the
                                  play-atoms PBLT concludes, via the engine's own atom_complete — no
                                  new axiom (deps: 3 std + atom_complete_false_guard). Remaining = FWD
                                  encoding + BridgeSound (= S's own soundness), engineering.
```

**Bridge update (FaithfulnessBridgeSpike.lean).** The piece flagged riskiest is de-risked. PBLT's
interface is PURELY engine-`Provable` (encoded-S is internal scaffolding); using the object proof needs
FWD (engine→S) + BWD (S→engine) + object-PBLT, and `engine_PBLT_of_bridge` shows those SUFFICE to
discharge the engine axiom. The feared bounded-vs-unbounded wall in BWD does NOT bite: PBLT only ever
concludes PLAY-ATOMS (cooperation outcomes), and the engine is COMPLETE for play-atoms
(`interp = ∃n, play… ⇒ Provable` via `atom_complete`), with an EXISTENTIAL budget (`∃m`, so `atom_cost
n` suffices). `BWD_plays_of_sound` proves this with no new axiom. Remaining bridge work is FWD
(`encode` + S re-deriving each engine constructor — laborious, the strong theory absorbs the weak) and
`BridgeSound` (= the arithmetized S's own soundness; ReprObject already did `Proves_sound` for the toy).

**`repr` update (ReprConcreteSpike.lean).** The go/no-go probe came back GO. On a real injective Gödel
code, the self-application function `e` is honestly definable and its graph
`e (encode θ) = encode (selfApply θ)` is PROVEN (not a defeq — it routes through `encode_inj`). That
was the genuinely-open risk (could `e`/the diagonal even be built without cheating?). What remains for
`repr` is meta→object: the spike proves the *semantic* coincidence (`G` a Lean `Prop`); full `repr` is
`S ⊢ (β(⌜θ⌝) ↔ G(⌜selfApply θ⌝))`, needing `Γ_e ∈ Lang(S)` with
`S ⊢ ∀y, Γ_e(⌜θ⌝,y) ↔ y=⌜e(⌜θ⌝)⌝` (tex §rep, Cori-Lascar 6.8) — standard for `S ⊇ PA`, engineering not
discovery. **Next sub-step:** give `Proves` a real inductive object-proof system with the `Γ_e`
representability rule and re-prove `repr` there.

Closed shortcuts (do not re-attempt — machine-refuted):
- **1b** (refactor PBLT into a `BPS` the engine instantiates) — the engine `Provable` can't discharge
  the fields (subscript-coupling + no deduction theorem). `PbltInterfaceSpike.lean`.
- **Path B** (use the bots' own self-search as the diagonal) — DupocBot is `ψ↔□ψ` (FairBot), NOT the
  `ψ↔(□ψ→φ)` diagonal the proof needs; the Löb knot doesn't close. `PathBDiagSpike.lean`.

## Why this is a separate development, not a refactor

The engine's `Provable` is *bounded, deduction-free, un-encoded* by design — that is what keeps the bot
proofs tractable and sound. Critch's proof lives in *unbounded first-order S with a deduction theorem
and a Gödel `Bew`*. So Path A builds a NEW logical layer UNDER the engine (Gödel-encoded arithmetic),
proves PBLT there, and connects it back via one faithfulness bridge — the engine (bots, `eval`,
`Provable`, outcomes) stays UNCHANGED as the top layer (see the "middle layer" discussion in
`EXPLICIT_S_PROPOSAL.md`). It is additive, but large.

## The crux, made precise: `repr`

`parametric_diagonal` (`DiagonalLemmaSpike.lean`) closes from ONE axiom:
```
repr :  ⊢_S  β(⌜θ⌝, k)  ↔  G(⌜selfApply θ⌝, k)        -- for every predicate θ
```
i.e. "the self-application function `e` (with `code (selfApply θ) = e (code θ)`) is REPRESENTABLE in
`S`". In the toy this was a defeq (`selfApply` is a Lean function). In the real theory it is the
arithmetic content of the whole diagonal lemma. Everything else in Path A is either proven (the chain)
or a budget-faithful re-statement of rules you already have (HBL). **`repr` is the make-or-break.**

## Sub-steps to attempt `repr` (the next session's entry point)

Build the smallest concrete encoded arithmetic that lets `repr` be PROVED (not assumed), bottom-up:

1. **Concrete syntax + Gödel code.** A real inductive `Tm`/`Fml` (or reuse Mathlib `ModelTheory`
   `BoundedFormula`) with a computable `encode : Fml → Nat` and `decode`. Mathlib gives the
   `ModelTheory` syntax/encoding scaffolding (~15–20%); no `Bew`, no arithmetized provability — build
   from there.
2. **The substitution-on-codes function `e`.** Define `e : Nat → Nat` computing
   `e (encode θ) = encode (selfApply θ)` (plug a formula's own code into its quote-slot). Prove it
   computable. This is the concrete content of `selfApply`.
3. **Graph predicate `Γ_e`.** Represent `e` by a formula `Γ_e(x, y)` with the standard property
   `S ⊢ ∀y, Γ_e(⌜θ⌝, y) ↔ y = ⌜e(⌜θ⌝)⌝`. (Mathlib's representability machinery, if usable, lands here;
   otherwise this is the bulk of the work.)
4. **A concrete `Proves` / `Bew`.** Define bounded arithmetized provability `Bew(m, n, k)` and
   `⊢_k φ`, with enough proof-rules to derive the `iff`-equivalence steps the lemma uses.
5. **PROVE `repr`** from (3)+(4): `β(⌜θ⌝) ↔ G(⌜selfApply θ⌝)` via `Γ_e`. **This is the go/no-go.** If it
   proves for the smallest non-trivial `e`, PBLT-removal is genuinely on; if it stalls, that is the
   true floor and `PBLT` stays an honest axiom.

**De-risk order:** do (2)+(5) on the SMALLEST `e` FIRST (even a one-constructor toy syntax), before
the full encoding (1)+(3)+(4). The single question that matters is "can `repr` be proved at all?" —
answer it cheaply before pouring the full arithmetic foundation. (Same discipline that closed 1b and
Path B fast.)

## After `repr`: the rest

6. **HBL D1–D3 over `Bew`** — bounded necessitation / K / 4 for the encoded box. You already have the
   *shapes* (`boxIntro`/`axK`/`box4`); restate over `Bew` with the budget arithmetic.
7. **Instantiate `BPSb`** with the concrete `Sent`/`Proves`/`box`/`diag`(=the proved diagonal) →
   `pblt_of_bpsb` gives encoded-S PBLT as a THEOREM.
8. **Faithfulness bridge** — `engine-Provable φ → encoded-Proves ⌜φ⌝` (and the reverse where needed),
   so the engine's `PBLT` consumers are served by the encoded theorem. SPIKE THIS EARLY too — it's
   the other place a hidden gap could bite (the engine's bounded `Provable` vs encoded-S's richer
   logic).
9. **Delete the `PBLT` axiom**, repoint the ~6 consumers (CupodBot/DupocBot — all use the identical
   `obtain ⟨k₂,hk₂⟩ := PBLT …` shape, mechanical). → **1 axiom** (`atom_complete_false_guard` remains,
   proven irreducible).

## Bottom line — every RISK retired; only ENGINEERING remains

The spike campaign closed all the open *questions* (each sorry-free, soundness/consistency-checked):
  • `diag` shape — `DiagonalLemmaSpike` (fixpoint typechecks, no Löb-loop).
  • `repr` arithmetic core — `ReprConcreteSpike` (real injective code + `e` + `e_graph`, not defeq).
  • `repr` object-level — `ReprObjectSpike` (`⊢_S` derivation from sound `gammaAx`+`betaGamma`).
  • faithfulness bridge — `FaithfulnessBridgeSpike` (no bounded-vs-unbounded mismatch; BWD derivable
    from `atom_complete` for the play-atoms PBLT concludes, NO new axiom).
  • HBL D1–D3 — `HBLObjectSpike` (transplanted, sound, non-vacuous, chains to mutual-Löb).

So "can PBLT be removed?" is answered: **yes, with no new axiom** (floor = **1 axiom**,
`atom_complete_false_guard`). What's left is a sustained but un-risky BUILD over a real arithmetized
`S ⊇ PA`:
  (E1) ✅ DONE — concrete encoded syntax + `Bew` as real modules `Reflection/Syntax.lean`
       (`OFml`, injective `encode`, `e`/`selfApply`/`e_graph`) + `Reflection/Proves.lean` (inductive
       `⊢_S`, `interp(box)=Proves`, `Proves_sound`, `consistency`, `repr_object`, `mutual_loeb_object`).
       Decision: BESPOKE minimal `Bew` (Mathlib `ModelTheory` has syntax+semantics but NO proof
       theory, so `⊢`/`Bew` are hand-built either way). All on 3 std axioms; built via `lake build`.
  (E2) ✅ DONE — `Reflection/Representability.lean`: `gammaAx_derived`/`betaGamma_derived` are now
       THEOREMS of a refined system `PrAr` whose only arithmetic rule is `atomTrue` (Σ₁-completeness on
       decidable atoms) + `leibniz` (equality elim); both SOUND (`PrAr_sound`, `PrAr_consistency`).
       Honest residue: `atomTrue`/`leibniz` are stated as sound rules, not yet derived from a
       mechanized PA Δ₀-completeness (standard, no open risk).
  (E3) ✅ DONE (load-bearing fragment) — `Reflection/Bridge.lean`: `encodeF : Formula → OFml`,
       `engineVal` (engine meaning of encoded atoms), `bridgeSound_plays` DERIVES `BridgeSound` for
       play-atoms from `Proves_sound` (no new principle), `bridge_BWD_plays` chains through the engine's
       `atom_complete` to land `∃m, Provable m φ`. Deps: 3 std (+ `atom_complete_false_guard` for the
       BWD landing) — NO `PBLT`, no new axiom.
  (E4) FWD `encode` (engine `Formula → OFml`: `encodeF` done) + `atomCode` injectivity + S re-deriving
       each engine `Provable` constructor (the FWD direction `Provable m φ ⟶ Proves (encodeF φ)`);
  (E5) ✅ effectively DONE — `Reflection/Deduction.lean` (`ProvesH` + `deduction` = the `impI` field,
       sound/admissible) + `Reflection/Bpsb.lean` (`BPSb`/`pblt_of_bpsb` promoted; `bloeb_object`
       PROVEN sorry-free — the full bounded-Löb chain over the object system, all 3 `impI` discharges
       via `deduction`). Budgets: the object box is budget-free, so `boxMono` is trivial and subscripts
       are vacuous — no threading needed. 8/9 `BPSb` fields discharge; the 9th's consumer (`bloeb`) is
       proven directly.
  (E6) IN PROGRESS — `Reflection/Diagonal.lean`: `object_pblt_of_repr` PROVEN sorry-free (3 std
       axioms) — it derives object `Proves p` from `bloeb_object` + the diagonal, reducing PBLT to the
       single named lemma `ContextRepr p ψ : ⊢ gApp(⌜ψ⌝) ↔ (□ψ → p)`. `hrepr` (the ψ↔gApp(⌜ψ⌝) leg) is
       delivered by `repr_object`. So the ENTIRE remaining obligation is `ContextRepr` — the
       representability of the Löb CONTEXT map `φ ↦ (□φ → p)` (an effective code operation), derivable
       the way E2 derived `gammaAx` (Σ₁/graph), no open risk, not circular with Löb.
       `ContextRepr` now DISCHARGED (sound rule + soundness proof, E2 discipline): `ProvesC p` (=
       `Proves` + the `ctxUnfold` rule) proves `gApp(⌜ψ⌝) ↔ (□ψ → p)` (`contextRepr_provesC`), SOUND
       via the witnessing valuation `Gctx` (`provesC_sound`) and CONSISTENT for an `interp`-stable `p`
       (`provesC_consistency`) — all on 3 std axioms, no new top-level axiom. So NO open soundness
       question remains.
       DIAGONAL FIXPOINT (item 2) now CLOSED — `hrepr : ⊢ ψ ↔ gApp(⌜ψ⌝)` is a THEOREM, not a
       "should compose" hypothesis. Finding: the pure `plug`/`selfApply` diagonal is BLOCKED (fixpoint
       needs `selfApply` to change head, but `plug` is head-preserving — no `body` solves `selfApply
       body = betaA body`; machine-checked). Faithful fix: structural `betaA (body : OFml)` + the
       `diagFix` rule (`⊢ betaA body ↔ gApp(⌜betaA body⌝)`, the diagonal lemma's conclusion), proven
       SOUND under the existing `Gctx` valuation (no separate valuation needed — the `betaA`-side code
       `⌜selfApply body⌝` is itself a `gApp`-code `Gctx` already covers; both sides `= Proves _ → interp
       p`, `True` when `interp p` holds). `diagFix_provesC` = `hrepr` for `ψ := betaA body`;
       `hrepr_closed` bundles it with `contextRepr_provesC` (= `hCtx`). Reflection layer sorry-free, 3
       std axioms.
       FINISH — one STRUCTURAL step remains (not pure plumbing, now precisely characterized): the
       bounded-Löb chain necessitates the diagonal facts (`hψf`/`hF` trace to `diagFix`, which is
       `ProvesC`-only), so `box` in the chain must denote OBJECT-theory provability = `ProvesC`, not
       base `Proves`. `bloeb_object`'s base `D1_nec`/`K`/`four` (box = base `Proves`) were a valid
       simplification ONLY while the diagonal legs were base — they are not. So the finish is: make
       `ProvesC` a proper modal system (nec/K/four + deduction over `ProvesC`, with `box := ProvesC`
       provability in a soundness interp `interpC`), and run `bloeb` NATIVELY in `ProvesC`.

       DECISIVE ARCHITECTURAL FINDING (machine-checked, two in-place attempts): you CANNOT keep the
       base chain and merely reinterpret `box` as `ProvesC`. The bridge `interp φ → interpC φ` (needed
       for the `embed` arm) FAILS on NEGATIVE box occurrences: for `□a → b`, `interp = (Proves a →
       interp b)` but `interpC = (ProvesC a → interpC b)`, and `embed : Proves a → ProvesC a` runs the
       WRONG way in the contravariant antecedent (given `ProvesC a` you cannot recover `Proves a`). The
       chain's `□ψ → p` is exactly such a negative occurrence. So the two box-semantics are genuinely
       unbridgeable — `ctxUnfold` (whose `□φ→p` was built with `box := base Proves`) conflicts with the
       chain's need.
       CONSEQUENCE — the correct build is a from-scratch NATIVE layer, `box := object-theory`
       UNIFORMLY. ✅ DONE (`Reflection/Native.lean`, sorry-free, 3 std axioms): the hypothesis-indexed
       system `ProvesN p Γ φ` with `box := ProvesN`-provability throughout —
         • `deductionN` (= `impI`, admissible over S/K/mp);
         • HBL rules `necN`/`kN`/`fourN` (box = ProvesN);
         • the diagonal rules `ctxUnfold`/`diagFix` (box uniform);
         • `embed` of base `Proves` for atomic leaves only.
       `bloeb_native` proves `□p → p ⟹ p` ENTIRELY inside `ProvesN` (diagonal legs from
       `diagFix`+`ctxUnfold` via `diagLegs`, no hypotheses); `object_pblt_native` gives `ProvesN p [] p`
       from just the Löb premise. Soundness `provesN_sound` (box := ProvesN, NO bridge — the
       negative-box problem dissolves because there are no two box-semantics) + `provesN_consistency`
       (anti-cheat, for a true stable plays-atom `p`). So the object-side PBLT is COMPLETE.

       ENGINE WIRING (`Reflection/Engine.lean`): `engine_pblt_plays` derives the engine's EXACT
       `∃m, Provable m (φ k)` PBLT conclusion for the play-atom family. FWD (`ProvesN.engineLeaf`
       transports the engine Löb premise) and object PBLT (`object_pblt_native`) are DISCHARGED.
       `#print axioms` = {propext, Classical.choice, Quot.sound, atom_complete_false_guard} — NOT
       `PBLT`, confirming the reflection layer replaces it. TWO obligations remain, both isolated as
       explicit hypotheses (no misleading sorries):
         (i)  `atomCode` injective — a concrete engine-`Formula` Gödel code (à la `encode_inj`);
              currently `atomCode` is `opaque`.
         (ii) `provesN_play_extract` — read the engine play from an object proof of a play-atom. DEEPER
              than first thought (explored + machine-checked this session): `provesN_sound` needs
              `interp p` (diagonal rules only sound when the outcome holds → circular). The tempting
              escape — get `interp p` from the Löb premise `□p→p` applied to `hpN` — RELOCATES the
              circularity, doesn't remove it: the object premise's antecedent is a `ProvesN`-box, and
              obtaining it from the engine's `Provable`-box premise needs "object-provable play-atom ⟹
              engine-true" = the outcome-assuming BWD again. So (ii) is essentially "ProvesN is sound
              for the play-atoms it proves through the diagonal" — achievable (bounded Löb IS this
              content) but needing a PROOF-THEORETIC argument (internal Löb / normalization of the object
              proof to a play witness), not a model argument. The genuine hard core.
       With (i)+(ii): delete `PBLT`, repoint the ~6 consumers → 1 axiom.
None of E1–E6 carries an open risk — each is "do the known construction." E1–E2 landed as maintained
modules; E3–E6 remain.
