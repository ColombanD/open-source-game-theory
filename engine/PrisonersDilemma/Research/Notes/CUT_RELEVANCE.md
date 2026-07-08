# Cut Relevance (T4.1b) — the analysis and the attack plan

**The conjecture** (`CutRelevance`, `Decidability/T42ProvableB.lean`): a computable `N₀` with

```
Provable k φ  →  ProvableG (modestGate (N₀ k φ)) k φ
```

i.e. minimal derivations never need cut material (the `implTrans`/`app`/`impS2` cut formulas
and the enumerated `axK`/`diagF`/`diagB` premises) that is exotic — literals beyond `N₀`, or
non-modest program syntax. Given it, `T47Stabilization`'s decision procedure decides full
`Provable`; `proofSearch` becomes computable; `eval` computable; outcomes `by decide`. If it
fails, `Provable` is a candidate undecidable bounded-provability predicate.

Status 2026-07-03: analysis below; mechanical foundations in
`Research/Spikes/transcript/T48CutRelevance.lean` (C0 ✅).

---

## 1. Sharpening: the LITERAL half is locally free (T48, proven)

Every gated premise is **size-paid at its own judgment**:

* cut formulas occur inside a premise `Provable a (.impl A ψ)`; impls are non-atoms, so
  `provable_impl_size` gives `|impl A ψ| ≤ a` — hence (`T48.cut_lit_bound`)
  `maxLitF ψ < 2^a` and `maxLitF A < 2^a`;
* `axK`'s premise `.box a (.impl ψ α)` and `diagF/B`'s premise `.impl (.box fb t) t` are
  likewise size-paid: `a < 2^m`, `fb < 2^m` (`T48.box_lit_bound`, `T48.diag_lit_bound`).

So **at each judgment of budget `m`, all cut literals are `< 2^m`**. This does NOT yet give
the uniform stratum bound: a single derivation contains judgments at budgets far above the
root's `k` — `search_t` cites guards at source literals `kg` written in PROGRAMS of the
derivation's formulas, and a cut atom (atoms are size-EXEMPT) can smuggle in a program with
a literal `~2^k`; the guard subderivation then lives at budget `~2^k`, its cuts reach
`~2^2^k`, and the tower climbs — *inside one derivation*. The tower is fed exclusively by
cut ATOMS (and atoms inside cut formulas); everything else is size-chained to the root.

## 2. The key structural observation: antecedents are never free

For a cut `B` to be useful, BOTH `Provable m₂ B` and `Provable m₁ (.impl B C)` must hold.
Census of every rule that can conclude an implication `.impl B C`:

| producer | antecedent `B` | provenance |
|---|---|---|
| `weakenImpl` | arbitrary | **degenerate**: `C` provable outright at `< m₁` |
| `implTrans` | from premise `.impl B D` | **chain**: recurse (same `B`, smaller budget) |
| `impS2` | from premise `.impl B (.impl E C)` | **chain**: recurse |
| `app` (α an impl) | from premise `.impl D (.impl B C)` | **nested**: recurse into positive positions |
| `struct`: `searchBranch`/`botSearchStep` | `.box k (ψ.subst me oppo)` | conclusion-determined (`me`, `oppo` in `C`) |
| `struct`: `simStep`/`botSimStep` | `.plays (p.subst me oppo) (q.subst me oppo) a` | conclusion-determined (subst instances) |
| `struct`: `iteBranchSearch_t` | `.plays opponent (.bot z) a'` (and nested `.box`) | conclusion-determined |
| `struct`: `modusPonens`/`hypSyll` | Derivation-internal | recurse INSIDE `Derivation` — whose own producers are all conclusion-determined (no free choice in the Type layer; its mp-cuts are size-paid structurally) |
| `searchThenSearch_t` | `.box k₁ (ψ₁.subst me opnt)` | conclusion-determined |
| `atomBoxImpl` | `.plays p q a` | appears in consequent |
| `boxIntro` | — (not an impl) | — |
| `axK` | `.box b ψ` | `ψ` in consequent; `b` size-paid in conclusion |
| `axKf` | `.box a (.impl ψ α)` | `ψ, α` in consequent; `a` size-paid |
| `box4` | `.box a ψ` | in consequent |
| `boxMono` | `.box a ψ` | `ψ` in consequent; `a` size-paid |
| `diagF` | `.diag g tgt` | in consequent |
| `diagB` | `.impl (.box g (.diag g tgt)) tgt` | in consequent |

**Every antecedent is conclusion-determined, weakening-degenerate, or chain-recursive.**
There is no rule that manufactures a genuinely free antecedent non-degenerately. (This is
the bounded analogue of the subformula property, and much weaker than cut-elimination — we
never eliminate non-degenerate cuts, we only characterize their CONTENT.)

Define the **antecedent closure** `AntCl(φ)`: the least set containing the subformulas of
`φ`, closed under (i) substitution instances `g.subst u v` of guard formulas of programs
occurring in members, by programs occurring in members; (ii) `.box j ψ` and `.diag j ψ` for
member `ψ` and size-paid `j`; (iii) `.neg` of members (refutation premises); (iv) the
`subst`-instances the transparency shapes generate. For MODEST `φ` (all zoo material) the
program part of `AntCl` is the T4.3 finite universe: `AntCl` is modest-preserving and its
literals are bounded by `max(source literals, 2^(local budget))`.

## 3. The reduction

**Lemma A (impl-inversion dichotomy, conjectured):** if `Provable m (.impl B C)` then
either (a) `∃ m' , Provable m' C` with `m' + |impl B C| ≤ m` (degenerate), or (b) every
formula in negative position of `.impl B C` — in particular `B` and its atoms — lies in
`AntCl(C)`-style provenance. Proof plan: well-founded induction on the budget (chains
recurse at strictly smaller budgets — transcript accounting pays the premises), with the
`app`-nesting handled by stating the invariant for ALL positive-position implications of a
derivable formula simultaneously.

**Lemma B (degeneracy elimination, conjectured):** every `app`/`implTrans`/`impS2` instance
whose impl-premise is degenerate can be rewritten away with a NON-INCREASED transcript
(e.g. `app(weaken(hC), hB) ⇒ hC` lifted by `Provable_mono` — strictly cheaper; the chain
cases turn one chain step into one `app` + one `weaken`, arithmetic to check). Rewrites
strictly decrease total transcript ⇒ terminate; the normal form has only provenance-(b)
cuts.

**Theorem (CutRelevance, target):** normal-form derivations of a modest root have all cut
material in `AntCl(root)` ∪ (size-paid boxes/diags) ⇒ modest and literal-bounded by
`N₀ k φ := 2^(max k L(AntCl φ) + 2)` — computable. ∎ (plan)

## 4. Risks / kill-criteria

1. **Budget bookkeeping of Lemma B** (the real risk): a degeneracy rewrite must fit the
   ORIGINAL budgets. The `app(weaken)` case is strictly cheaper ✓; the `implTrans(weaken(hD), hDC)`
   case turns `a + b + |impl B C|` into `(m_D + b + |C|) + |impl B C|` — fits iff
   `m_D + |C| ≤ a + ...`; since `m_D + |impl B D| ≤ a` this needs `|C| ≤ |impl B D| + (a − m_D − |impl B D|) + b`-slack —
   check case-by-case; if some case needs budget slack that isn't there, the conjecture may
   need the weaker form `Provable k φ → ProvableG (modestGate N₀) (c·k) φ` (budget
   inflation) — STILL sufficient for decidability of `Provable k φ` (decide the inflated
   stratum, soundness unchanged)! Keep this fallback in mind: the decision procedure only
   needs `Provable k φ ↔ ProvableG (modestGate N₀) (f k) φ` for computable `f`.
2. **`app`-nesting invariant** (Lemma A's generalization): the statement must cover
   positive-position impls at all depths; risk of invariant-wrangling, not of falsity.
3. **The Derivation layer**: needs its own "no free antecedents" lemma (C1) — expected
   mechanical (every rule carries `hme :`-equations tying formulas to conclusions).
4. **If Lemma B genuinely fails** even with budget inflation: attempt the ENCODING —
   a root whose provability requires an unbounded cite-escalation (halting-style); that
   would make `Provable` undecidable, also a publishable resolution.

## 5. The C3 master-induction architecture (designed 2026-07-03; open contract question)

The tree-invariant and the transformation MERGE into one structural induction (`Provable.rec`),
because the degeneracy-rewrites produce derivations that neither budget- nor structural
induction covers separately — so the dichotomy's degenerate disjunct must CARRY its
transformed witness:

```
motive₃ (m, φ) :=  (Inv φ → ProvableG GATE m φ)
                ∧ (∀ B C, PosImpl φ B C → PAnt' B C
                     ∨ ∃ m' ≤ m, Provable m' C ∧ (Inv C → ProvableG GATE m' C))
```

Key facts making it close:

* **Cites are structural.** Budget induction dies at `search_t`/STS jumps; `Provable.rec`
  doesn't — the cited guard judgment is a premise, its IH available.
* **Degenerate witnesses come with transforms.** `weakenImpl`'s degenerate witness IS its
  premise (IH attached ✓); `implTrans`'s propagation reassembles via `Provable.app` within
  budget (C2 verified the arithmetic ✓).
* **Boxes are never opened** (no reflection rule; `Derivation` cannot conclude a box —
  T48 §6 `derivation_shape`/`derivation_no_box`). So box CONTENTS never become judgments;
  their material matters only through the GATES (`modestF` of a recorded cut sees the whole
  formula). Box-judgment provenance is a two-case inversion (T48 §6 `box_inversion`):
  `boxIntro` (content was a judgment — IH reaches it) or `app` (spine — IH reaches the
  impl-premise).
* **Sibling-sourcing resolves the census holes.** `axkPair`/`box4`-style pairs (`B = .box b ψ`
  with `ψ` pairwise-invisible) are consumed only at `app` sites where the SIBLING judgment
  `Provable m₂ B` is present — its IH supplies `B`'s transform; `B`'s `Inv` comes from the
  sibling's own provenance (box-inversion → `boxIntro`-content judgment or deeper spine).

**The open design question (start here next session):** the `Inv`-contract. `Inv` cannot be
purely an INPUT (consumer-supplied downward): at `app`, the cut `B`'s `Inv` is needed for
IH₂ but is not conclusion-visible; sourcing it from the sibling's structure makes it an
OUTPUT. Candidate resolution: split the motive's first component into
`ProvableG GATE m φ ∧ SelfInv m φ` where `SelfInv` asserts the judgment's own
non-conclusion-sourced material (cut formulas it used, box contents it introduced) is
GATE-tame — produced bottom-up, no input needed; then `app` reads `B`'s tameness from IH₂'s
`SelfInv` and only the ROOT's conclusion-material needs the (modest-root) hypothesis. The
GATE's `N₀` then aggregates: root material + `2^(local budgets along the spine)` — the
budget-relativity of deep judgments is the part to nail down (deep cites at budget `kg`
have local cuts `< 2^kg`; `kg` itself is source-material of an Inv-tame formula, so the
aggregation should ground out at `N₀ = 2^(max k L(root closure) + c)` — verify).

### 5a. C3b design refinements (2026-07-03, second pass — read before attempting)

Working the master induction to the brink of formalization surfaced three load-bearing
facts that fix the design:

1. **The budget invariant.** If every judgment's FORMULA satisfies `maxLitF ≤ L`
   (tameness), then every cite targets a literal `≤ L`, so EVERY budget in the derivation
   is `≤ M := max k L` — and all size-paid material is `< 2^M`, giving the FIXED stratum
   bound `N₀ := 2^(M+2)` with no aggregation subtleties. Tameness must thread as an INPUT
   (downward): each rule's premise formulas are conclusion-material (`≤ L` ✓),
   cite-substs (`maxLitF_subst`, `≤ L` ✓), census antecedents (nonincreasing ✓), or CUTS —
   which the dichotomy resolves (census ⇒ `≤ L`; degenerate ⇒ rewritten away).

2. **The literal half still needs the census.** Tempting shortcut — "all cuts are
   size-paid locally, so `< 2^M` suffices" — FAILS: a `2^M`-literal cut formula's programs
   contain `2^M`-literal `.search` nodes; the cut's own cert obligations cite THOSE guards
   at budget `~2^M`, breaking the budget invariant and restarting the tower. Only
   tame-bounded (`≤ L`) cut formulas keep cites at `≤ L`. So the dichotomy/census is
   load-bearing even for the literal-only statement.

3. **The holes do not compose through `trans`.** `PAnt.trans` chains
   `B ≤ D-material ≤ C-material` — if `D` is an `axkPair` hole, `B` is bounded by an
   unbounded intermediate. A generic `PAnt_lit` lemma is therefore false-ish; the hole
   information must be carried, which the MERGED MOTIVE does naturally. Final motive shape
   (three components, all parameterized by the tameness bound `L`):

   ```
   motive₃ (m, φ) :=
        (Tame L φ → m ≤ M → ProvableB N₀ m φ)                                -- transform
      ∧ (∀ B C, PosImpl φ B C → censusTame B C ∨                            -- pair dichotomy
           ∃ m' ≤ m, Provable m' C ∧ (Tame L C → m' ≤ M → ProvableB N₀ m' C))  --  w/ transform
      ∧ (∀ b ψ, PosBox φ b ψ → contentTame ψ ∨                              -- box contents
           ∃ mb ≤ b, Provable mb ψ ∧ (Tame L ψ → … → ProvableB N₀ mb ψ))       --  w/ transform
   ```

   The third component is what resolves the `axkPair`/`box4` holes WITHOUT box_inversion's
   opaque witnesses breaking the induction: box contents' transforms are carried
   structurally from `boxIntro`/spine arms, exactly as degenerate witnesses are. The cert
   layer's motives carry the program-side tameness (the T4.3 universe hypotheses) for the
   guard-subst premises.

   Modesty rides the same induction: `Tame L φ` becomes `maxLitF φ ≤ L ∧ argsIn U φ` with
   `U` the T4.3/T4.6 universe, and the same threading arguments apply (census antecedents
   are subst-instances of consequent programs — `T43.step_*`; cut-args re-enter via the
   gate — `T47.enumArg_mem`-style).

4. **Expected failure points to watch**: the axK arm's degenerate-content case (rewrite
   arithmetic — first candidate for the budget-inflation fallback, which would change
   `ProvableB N₀ m φ` to `ProvableB N₀ (F m) φ` for a fixed computable `F`, harmless for
   decidability); and `diagF/B`'s Löb-premise pairs at deep positions (covered by the
   premise IH — verify the budget side-conditions).

### 5a′. C3b final specification (2026-07-03, third pass — THE implementable design)

Pushing §5a to full case analysis produced the decisive refinement and closed every gap:

**The measure split (the breakthrough).** Cite targets are ONLY `.search` literals of
programs (`search_t`'s `kg`, STS's `k₂`); box/diag SUBSCRIPTS never become budgets — boxes
are never opened (T48 §6). So the tameness invariant must track `maxSLitF` — the
search-literals-in-programs measure that IGNORES `.box`/`.diag` subscripts — while
subscripts stay size-paid (`< 2^M` locally) and are covered by the GATE, not the invariant.
With `Tame φ := maxSLitF φ ≤ L`:
  * the budget invariant `M := max k L` holds (cites ≤ L);
  * `diagFInner`, `boxMono`, `axkf`-HEAD, `axK`-HEAD (via its premise's box-content pair)
    all become genuine D1 — the subscripts that blocked them don't count;
  * the gate needs `maxLitF cut ≤ N`: from `Tame` + size-payment,
    `maxLitF ψ ≤ maxSLitF ψ + 2^|ψ|` (the split lemma, T48 §7) gives
    `≤ L + 2^M ≤ N := 2^(M+2)`.

**The trichotomy.** Component (B) over `PPair` (positive pairs at box-depth ≤ 1 — impl
tails, plus ONE box-content descent, which is all `axK`-premise sourcing needs; deeper
box-interiors are never consumed):
  * **D1**: `Tame C → Tame B` — an IMPLICATION, which is what makes it compose through
    `implTrans`/`impS2` heads (absolute tameness does not);
  * **D2**: `∃ m' ≤ m, Provable m' C ∧ (Tame C → m' ≤ M → ProvableB N m' C)` —
    degenerate-with-transform;
  * **D3**: `∃ b c ψ₀ α₀, B = .box b ψ₀ ∧ C = .box c α₀` — shape only. The ONLY D3 source
    is `axKf`'s tail pair (premise-free rule, box-box pair, contents unlinked at birth);
    `box4`/`boxMono`/`diagF` export none (trivial or subscript-only), `axK`'s head is D1
    via its premise.

**The patch theorem (peel order).** An `axKf` conclusion `.impl A (.impl (.box b ψ₀)
(.box c α₀))` (A = `.box a (.impl ψ₀ α₀)`) is consumed by first discharging A — and THAT
`app`'s sibling is exactly `A`, whose box-content pair `(ψ₀, α₀)` supplies the link
`Tame α₀ → Tame ψ₀` (via IH₂'s `PPair` boxT-head + D1). The app arm therefore patches every
received D3 whose shapes match its sibling's content — and peel order guarantees the
matching app comes BEFORE the hole can be exposed as a judgment head. Non-matching D3s pass
through (they meet their own discharge apps later); compositions preserve head antecedents,
so the right sibling always arrives. Nested holes resolve level-by-level the same way.

**Wildness is confined.** Wild material (non-tame programs) IS derivable (wild-atom certs
evaluate without visiting junk; `atomBoxImpl`+`boxIntro`+`axK` lift it into boxes) — but
census steps are `maxSLit`-NONINCREASING, so wild antecedents force wild consequents:
wildness can never flow into a Tame conclusion non-degenerately; the degenerate branch
(D2, with carried transform) bypasses it. This is why the theorem is true.

**Assembly**: motive := (A) `Tame φ → m ≤ M → ProvableB N m φ` ∧ (B) the trichotomy over
`PPair φ`. One `Provable.rec`; composition arms (implTrans/impS2 heads) do 3×3 subcases —
all verified on paper (D2 absorbs, D1 composes, D3 passes). Target instantiation:
`L := maxSLitF φ₀ (⊔ k)`, `M := max k L`, `N := 2^(M+2)`:
**`Provable k φ → ProvableB (2^(max k (maxSLitF φ) + 2)) k φ`** — the literal half of
CutRelevance. Modesty then rides the same induction (enrich Tame with the T4.3 universe).

### 5c. The retraction and the corrected course (2026-07-03, post-review)

**What went wrong.** To make the trichotomy's 26 arms compose, the two "recorded
obstruction" disjuncts were UNLINKED from the analyzed pair `(B, C)`. Unlinked existentials
over an inhabited domain are `True`: one fixed `box4` instance witnesses them for every
input (kernel-checked, T48 §9 `Tri_always`), so the theorem carries no information. The
composition pressure that forced the unlinking was the honest signal that a pairwise,
judgment-local statement CANNOT carry that information — the correct response was never to
drop the links. (`PAnt.axkPair` in C2 has the same disease in milder form: `PAnt` is
trivial on box-box pairs, and `trans` leaks this to any path routing through boxes —
C2's value is likewise confined to its non-box-mediated content.)

**C3b-i′ — the corrected plan, two steps:**

1. **The LINKED trichotomy diagnostic.** Re-run the 26-arm induction against the tight
   target with NO escape hatches:
   `TriL := (Tame C → Tame B) ∨ (∃ b ψ₀, B = .box b ψ₀) ∨ (∃ m' ≤ m, Provable m' C)`
   (keep `DboxAnt` — it IS linked via `B`, and its consumers hold the sibling). Do not
   expect it to close; the point is the exact list of arms that break. Predicted breakage:
   `implTrans`/`impS2` head-compositions where the MIDDLE is a box (`X₂ = DboxAnt`), and
   the boxT-content pairs of the premise-free rules (`axKf`/`box4`/`boxMono`
   consequent-contents). Each breakage is a REAL lemma obligation, not a formalization
   artifact.
2. **The box-chain grounding lemma** (the predicted missing mathematics, from the
   producer census): for `Provable b (.impl (.box bb ψ₀) χ)` with `χ` NOT a box, the
   only non-degenerate producers of box-antecedent/non-box-consequent implications are
   the `searchBranch` family (⇒ `ψ₀` is a guard-subst of the consequent's programs —
   TAME relative to `χ`) and chains whose middles recurse; box-middles pass rightward
   until the consequent is non-box. So conjecture: `χ` non-box ⇒ `(Tame χ → Tame ψ₀)`
   ∨ degenerate — provable by induction with the box-DEPTH of the consequent as the
   auxiliary measure for the all-box chains (`axK`-land), which must eventually be
   consumed toward a non-box conclusion. If THIS grounding fails, the failure is a
   genuine candidate for the undecidability encoding (§4.4).

### 5d. The diagnostic's RESULTS (2026-07-03, T48 §10) — two falsity theorems, one foundation

Running §5c step 1 on paper settled the arms before the induction was worth writing: the
linked forms are not hard — at two precisely-located position classes they are **FALSE**,
and both counterexamples are kernel-checked (`ppair_linked_false`,
`spine_boxlinked_false`, via the soundness-based unprovability helpers
`eq_const_unprovable`/`box_eq_unprovable`).

1. **Box-content pairs are unfixable** (`ppair_linked_false`). `axKf` is a PREMISE-FREE
   axiom schema, so its consequent-box content `α` is arbitrary: `α := .impl wildF eqCD`
   plants a wild-antecedent/unprovable-consequent pair inside a positive box of a
   derivable judgment, defeating `D1 ∨ Dbox ∨ D2` outright. So `PPair`'s boxT descent
   must GO from any judgment-local lemma; box contents are sourced only at consumption
   (box judgments via `box_inversion`) — the §5 consumer-side design, now FORCED rather
   than chosen. (Retro-explains C3b-i: DboxPos could never have been linked.)
2. **Guarded tail positions are unfixable pairwise** (`spine_boxlinked_false`). Even
   spine-only and even GRANTING the box escape its content-link
   (`B = □ψ₀ ∧ (Tame C → Tame ψ₀)`), the dichotomy fails at tail positions behind an
   undischarged antecedent: the same `axKf` instance's tail pair `(□b wildF, □c eqCD)`
   has no link and no degeneracy — before the antecedent `□a(wildF → eqCD)` is
   discharged (it can't be), the judgment alone carries no information about the pair.
   Guard CONTEXT is necessary information. (§5's discharge-site architecture, likewise
   now forced.)

**The corrected foundation (C3b-ii′).** Three components, each checked on paper against
the failure modes above:

- **Motive: pairs with guard context.** `PosImplCtx φ Γ B C` — spine descent collecting
  into `Γ` every antecedent passed on the way to the pair; the dichotomy takes
  `∀ X ∈ Γ, ∃ mX, Provable mX X` as a hypothesis. Both counterexamples dissolve: the
  `axKf` tail pair's guard is `□a(wildF → eqCD)`, and its provability (the discharge
  sibling at the consuming `app`) is exactly the constraint whose absence made the pair
  wild.
- **Induction: budget-strong-induction with inversion, NOT structural `rec`.** Legal
  because **pair-queries never cross cites** — checked rule-by-rule: the cited premises
  of `search_t`/`searchThenSearch_t`/`search_f` and the STS premise (at `m' ≤ k₂`)
  contribute NO pairs to their conclusions' spines (plays-ended conclusions); `diagF`'s
  tail-tail pairs come from its premise at `pm < K`. Every pair-relevant premise sits at
  a strictly smaller budget — and, the decisive advantage over the merged-motive design,
  the D2 wall vanishes: opaque degenerate WITNESSES are just judgments at smaller
  budgets, re-analyzable by the same strong IH. No transform-carrying inside the
  dichotomy.
- **Kernel: `HBoxHead` — box-chain grounding at HEAD positions only.**
  `Provable m (.impl (.box b₀ ψ₀) C) → (Tame C → Tame ψ₀) ∨ (∃ m' ≤ m, Provable m' C)`.
  Heads dodge both falsity findings (unguarded by construction), and the §5c-2 producer
  census applies: head box-antecedents come from the `searchBranch` family (guard-subst
  contents — tame), chains (recurse), `axK` (premise-constrained: `□a(ψ₀ → α)` is a real
  judgment), or post-discharge `axKf` (the discharge sibling constrains the content).
  On paper the guard-context dichotomy closes ALL arms given `HBoxHead`: box-B heads
  discharge by `HBoxHead`-at-self; box-middle compositions consume the strong IH's
  binary answer at the middle judgment; `impS2`'s tail-query carries guard `A`,
  discharged at its consumption sites.

The conjecture's residue after the diagnostic is `HBoxHead` — one head-level, guard-free
statement, plausible by census, the natural home for §5c-2's box-depth auxiliary
induction. If IT fails, §4.4's undecidability encoding starts there.

### 5e. The third refutation (2026-07-03, T48 §11) — `HBoxHead` is FALSE; the judgment-local program is CLOSED

Probing §5d's kernel before building on it (the lesson of §5c, applied) produced a third
kernel-checked counterexample, and this one closes the whole program. `deadJ` is a
**dead implication**: `Provable 10000 (.impl (.box 300 ψ₀) (.box 1000 eqCD))` with `ψ₀`
wild, the consequent tame and unprovable — refuting `HBoxHead` (`hboxhead_false`) and the
head-level linked dichotomy itself (`head_dichotomy_false`) at an UNGUARDED HEAD pair.
The recipe combines four engine facts, each individually innocent:
provable formulas carry arbitrary search literals (`eqRefl` on any program);
`weakenImpl` admits arbitrary antecedents; `boxIntro`+`axK` box and distribute the
degenerate implication, planting the wild content in antecedent position; `impS2`
against a free `axKf` composes away the middle. Both sides of `deadJ` are unprovable
(`box_psi0_unprovable`, `box_eq_unprovable`) — it can never fire via `app`.

**Why no pairwise repair exists.** Conditioning on liveness doesn't save it: with a
budget-BOUNDED degeneracy disjunct (`∃ m' ≤ m, Provable m' C`) the live variant still
fails — box subscripts are BUDGET COMPRESSORS (`.box c χ` has size `~log c` but asserts
budget-`c` provability, so a judgment can cheaply mention provability far above its own
budget; replace `eqCD` by a tame `χ` provable only at `N ≫ m` and choose the `axKf`
subscript `c ≥ N`). With budget-UNBOUNDED degeneracy the live variant is trivially true
(apply `app`) and carries no information. Every informative judgment-local statement is
false; every true one is empty. With §9 (vacuity), §10 (content pairs, guarded tails),
and §11 (unguarded heads), the program is closed, not paused.

**What survives.** The conjecture. All three counterexamples have unprovable right
sides — dead weight that no derivation of a provable goal consumes through `app`, and
that minimality should excise. The information CutRelevance needs lives in minimal
derivation TREES of provable roots, not in judgments.

**The fork (pick one next session):**

- **(A) Tree-level minimality / excision** — Lemma B's true home. Formalize weighted
  derivation trees; define LIVE sub-judgments (consequent-side contributes to the root);
  prove the excision lemma (dead sub-derivations removable, budget non-increasing); then
  re-run the literal analysis over live judgments only — where every `app` site has its
  discharge sibling present in the tree, which is exactly the guard context §5d wanted,
  now with real witnesses instead of hypotheses.
- **(B) Specialize to the actual consumer.** `decB`/T47 need CutRelevance only for
  zoo-universe roots (modest, plays-shaped goals in `SL`). Run (A)'s tree analysis
  specialized to those roots: their derivations are census-dominated (the whole theorem
  library's cut diet is modest), and the wild-injection machinery may be provably
  excisable there even if the general statement stays open.
- **(C) The undecidability route, now with a weapon.** Budget compression is encoding
  material: `maxLitF` counts box subscripts, so □-compressed cuts are exotic by
  definition; if some tame provable family can be FORCED to route through
  `.box c`-cuts whose minimal `c` grows non-computably in `k`, CutRelevance FAILS and
  `Provable` is undecidable. The §11 injection recipe (weaken-plant + `axK`-distribute)
  is the tool for building such forcings — the open question is making the wild route
  NECESSARY, i.e. defeating excision, which is exactly the negation of (A)'s lemma.
  (A) and (C) are the two faces of one question: is excision always possible?

### 5f. The excision design (2026-07-03, D2 planning — read before attempting D2b)

Working the crossing analysis on paper (per the §5c policy: probe before building)
produced two load-bearing observations, one wall with its fix, and the master statement.

**Observation 1 — subscripts are backward-tame through gates.** Every rule that consumes
or produces a box subscript CHAINS it arithmetically to its conclusion's content:
`axK`/`axKf` force `a + b + |α| ≤ c` (premise and antecedent subscripts bounded by the
consequent's), `boxMono` forces `a ≤ b`, `box4` forces `a + |□aφ| ≤ b`, and the
search-interface rules (`searchBranch`, `searchThenSearch_t`) pin the subscript to the
goal's own program literal. So budget-compression wildness (§5e's weapon) CANNOT cross a
tame interface: a tame consumption site arithmetically bounds every subscript feeding it.
`deadJ`-style wildness is content-wildness, handled by Observation 2.

**Observation 2 — content is backward-tame through shapes.** At a crossing
`⟨t1 : ProvT m₁ (.impl B α), t2 : ProvT m₂ B⟩` with `B` wild and `α` tame, most arms of
`t1` are VACUOUS because the constructor's shape puts `B`'s content inside `α`:
`atomBoxImpl` (α contains the same atom), `axKf` (α = `.impl (□bφ) (□cα')` contains both
components of B's content), the censuses (B = box of a guard-subst OF α's own programs,
tame by `maxLitF_subst`), `box4`/`boxMono` (same φ both sides). The arms that survive:
`weakenImpl` (the excisable entry — `cross_weaken`, now proven), and the recursive ones
(`implTrans`/`impS2`/`app`/`struct`-chains), which is where the induction lives.

**The wall and its fix — budget discipline.** Naive β-style rewriting
(`app(implTrans(tA,tB), targ) ⇒ app(tB, app(tA, targ))`) EXCEEDS the original budget:
materializing the intermediate judgment pays the cut formula's size `|ψ|`, which the
original tree paid only once inside `tA`'s budget. Strict-budget cut-ELIMINATION is
impossible (cuts compress — that is their point), but excision doesn't eliminate tame
cuts, and for wild ones the fix is: the crossing lemma NEVER materializes intermediates —
it carries implication/argument pairs abstractly and returns budget `≤ m₁ + m₂`, the
consumer paying the target's size exactly once (`impl_size_le` supplies the arithmetic:
every impl node already paid its conclusion).

**The master statement (D2b).** Mutual with the main induction
(`t : ProvT k φ` with `φ` tame ⇒ ∃ same-budget tame-cut tree):
`spineCross : (t1 : ProvT m₁ ξ) → ξ an impl-spine over segments [B₁,…,Bₙ] with final
target α tame → (discharge trees tᵢ : ProvT mᵢ Bᵢ for each segment) → ∃ tame-cut tree of
α at budget ≤ m₁ + Σmᵢ + |α|` — structural induction on `t1`, wild segments consumed via
Observation 2's vacuities and `cross_weaken`, tame segments re-gated directly (`G Bᵢ`
holds), subscript arithmetic via Observation 1. The discharge trees are the guard context
§5d wanted — now real objects, which is why this formulation dodges all three §5e
refutations (they are statements about JUDGMENTS; `spineCross` holds trees).
Open sub-questions for D2b: `diagF/B`'s premise budget `fb` is conclusion-free (but the
premise formula is gated, so the gate absorbs it); the atom layer's guard cites recurse
through the main induction at guard budgets (guard formulas are substitution instances of
the conclusion's programs — `maxLitF_subst` keeps them tame); `struct`-embedded
`modusPonens`/`hypSyll` chains need the Derivation-level census (C1's `DAnt`, which
stands).

### 5g. The D2b probe (2026-07-03) — the reduction to ATOM MODESTY, and the Gentzen wall

Designing `spineCross` arm-by-arm before writing it (standing policy) produced one
strategic simplification, one hard wall, and two failed forcing attempts worth keeping.

**The reduction: the conjecture IS atom modesty.** Assembling what already stands:
(i) C0's `cut_lit_bound` — every gated cut formula has `maxLitF < 2^(local budget)`, and
logic-layer node budgets DESCEND from the root (`k`); (ii) the compression ceiling
(T49 §8, `box_subscript_lt`) — box subscripts reachable at budget `k` are `< 2^k`, since
every box-concluding node pays its conclusion (`boxIntro`/`app` by gate; the Type layer
concludes no box; atoms none); (iii) so within any single cite stratum, EVERYTHING is
`< 2^k`-bounded automatically, and the only escalation channel is a CITE (a
`search_t`/`search_f` guard, at a budget equal to a program's search subscript) whose
program comes from a cut ATOM's fresh material — root-pool programs keep cite budgets
≤ the root's own literals at every depth (substitution instances, `maxLitF_subst`).
Hence: **if some budget-`k` tree keeps its cut atoms' programs in the root's subterm
pool, then `N₀ (k, φ) := 2^(max k (maxLitF φ)) + maxLitF φ` tames it uniformly, at every
cite depth**. The literal half of CutRelevance is FREE; the entire conjecture reduces to:
*some minimal tree's cut atoms stay in the pool* — exactly the property the modest gate
polices, and exactly what T43's universe closure already gives for zoo dynamics. Fork
(B)'s specialization is now the MAIN road, not a shortcut.

**The Gentzen wall.** `spineCross`'s recursion is structural on `t1` for every arm
EXCEPT the discharge-diving bases (`axK`/`axKf`/`box4` chase their segments' box
CONTENTS — through `box_inv` — and `diagF/B` chase the Löb premise), which recurse into
discharge-internals; and `impS2`'s arm DUPLICATES its head discharge (it feeds both
premise spines — contraction). Consequences, checked arithmetically: (a) every
total-size termination measure fails (the impS2 arm grows it by one discharge's size);
(b) strict same-`k` budget preservation fails the same way (the transcript cost model
charges re-derivations honestly — a tame rewrite may genuinely not fit `k`). The
standard resolutions: Gentzen rank-lexicographic measures (dives strip a constructor
off the segment formula; duplications preserve rank), or shared-discharge environments
(de Bruijn-style, so duplication is reference-copying, free in both size and budget).
Both are heavyweight; the environment route also REPAIRS strict-`k` (sharing is how a
real transcript would cite a lemma twice)... but NOTE: the engine's cost model has no
sharing — `impS2` pays `m₁ + m₂` with the discharge inside both — so if the original
wild tree could afford duplication, the budget for it EXISTS in `k`; the question is
whether the tame REPLACEMENT of each copy fits the copy's own budget — it does if
excision is budget-non-increasing PER SUBTREE (it is: `cross_weaken` shrinks;
re-gating preserves). So strict-`k` is NOT yet dead — the wall is termination
bookkeeping, not budgets, PROVIDED excision is stated per-subtree-budget-preserving.

**Failed forcings (fork (C) attempts, kept as evidence FOR the conjecture).**
(1) Nested compression (`□c₁(□c₂ χ)` roots): the inner subscript lives in the ROOT's own
syntax, so `N₀`'s dependence on `maxLitF φ` absorbs it. (2) Fresh-provable-middle
forcing (the `deadJ` recipe as a needed cut): the `axKf`-segment pairing forces the
middle `X` to satisfy `ψ₀ = X → eqCD` with `ψ₀` fixed by the root — the root carries its
own wildness or the route dies; no tame-rooted variant found. Both die on Observations
1&2 (backward-tame subscripts and content). The conjecture keeps surviving adversarial
probes; its expected resolution remains TRUE-via-excision, with the risk concentrated in
the termination formalization.

**D2b, re-aimed (the executable plan):**
1. `box_inv` on trees (`ProvT m (.box c ψ) → Σ' m' ≤ c, ProvT m' ψ`) — mutual with the
   spine machinery; the axK-dive pays its gate (`a + b + |α| ≤ c` — Observation 1 IS the
   budget proof).
2. `spineCross` over MODEST-POOL segments only (fork (B)): segments and discharges
   restricted to the T43 universe make the diving arms' formulas pool-bounded, the
   rank-lex measure collapses to (pool-formula rank, tree size) — finitely many ranks —
   and termination becomes provable without full Gentzen machinery.
3. Assemble `TreeModestRelevance` for zoo roots; plug into `tree_modestRelevance` +
   T47's decider: `Provable` decidable on the zoo universe.

## 5b. Milestones

- **C0 ✅ (2026-07-03)**: this analysis; T48 foundations (literal bounds at own judgments).
- **C1 ✅ (2026-07-03, T48 §3–4)**: Derivation-layer antecedent determinacy. KEY DESIGN
  (reusable for C3): state the invariant over the POSITIVE IMPLICATION SPINE
  (`PosImpl φ B C`) — then `modusPonens` needs NO cut analysis (the conclusion's spine
  embeds in the impl-premise's spine: `ih₁ (.tail hp)`) and `hypSyll` is exactly
  `DAnt.trans`. `DAnt` = the census as an inductive (six transparency constructors +
  transitivity); `derivation_posImpl_ant`/`derivation_impl_ant` prove it; payoff
  `DAnt_lit` — Derivation antecedents NEVER increase literals (each census step is built
  from the consequent's own programs, via `maxLitF_subst`) — and `struct_ant_lit`: every
  positive antecedent of a `struct`-entry at budget `k` is `< 2^k`-literal-bounded. The
  Type layer is fully tame; the residue is the `Provable` layer.
- **C2 ✅ (2026-07-03, T48 §5)**: the FULL `Provable`-layer spine dichotomy — not just the
  chain-free fragment (the `PosImpl` formulation absorbed the chains):
  `provable_posImpl_ant` / `provable_impl_ant`:
  `Provable m (.impl B C) → PAnt B C ∨ ∃ m' ≤ m, Provable m' C`.
  `PAnt` = the census inductive (C1's `DAnt` embedded; one constructor per modal
  producer). HONESTY POINTS for C3: (i) `imps2Ant` RECORDS its producing judgment (budget
  strictly smaller — the tree-invariant unfolds it); (ii) `axkPair` is SHAPE-ONLY — at a
  box-box pair the antecedent content (`ψ` of `.box b ψ`) is carried by the SIBLING
  judgment `.box a (.impl ψ α)` at the consuming `app`, invisible pairwise; C3 must use
  both premises. Degeneracy propagation verified to FIT budgets: `implTrans`'s mixed case
  reassembles with `Provable.app` at `b + m₁' + |χ| < k` (the arithmetic closes because
  the conclusion gate pays `|impl A χ| > |χ|`) — first evidence AGAINST the Lemma-B budget
  risk.
  Remaining C3 content: the TREE-invariant (every judgment in a degeneracy-normalized
  derivation has its formula in `Cl(root)`), consuming the dichotomy at `app` sites with
  both premises visible (resolves `axkPair`), unfolding `imps2Ant`'s records, and the
  box-content positions (extend `PosImpl` through `.box` if needed). (no implTrans/impS2/app-produced
  impls) — the census above, formalized.
- **C3a ✅ (2026-07-03, T48 §6)**: the sibling-sourcing tools. `derivation_shape` (the Type
  layer concludes only plays-ended impl chains and equality shapes) ⇒ `derivation_no_box`;
  `provable_pos`; **`box_inversion`** — a derivable box comes from `boxIntro` (its content
  WAS a judgment, at budget = the subscript) or an `app` spine, nothing else. These are the
  master induction's tools for resolving the census holes from sibling judgments.
- **C3b-i ✗ RETRACTED (2026-07-03, same day — external review + kernel check, T48 §9)**:
  the "tame trichotomy" below is TRUE BUT VACUOUS — its `DboxMid`/`DboxPos` disjuncts
  don't mention the analyzed pair and are unconditionally inhabited by one fixed `box4`
  witness (`Tri_always`); the whole theorem follows in one line (`tame_trichotomy_vacuous`).
  Withdrawn claim, kept for the record: `tame_impl_trichotomy`:
  `Provable m (.impl B C) → Tri L m B C` where `Tri` = D1 (`maxSLitF C ≤ L → maxSLitF B ≤
  L` — implicational, composes) ∨ DboxAnt (`B` is a box — sibling-resolvable at its
  discharge `app`) ∨ DboxMid (a box-antecedent pair recorded in a judgment — the
  `implTrans`-through-box-middle kernel) ∨ DboxPos (a box-interior pair of a judgment —
  content-judgment-resolvable) ∨ D2 (degenerate within budget). Over the full `PPair`
  (spines + one box-content descent). The obstruction disjuncts are SELF-CONTAINED so all
  compositions pass verbatim; the census cases needed only `DAnt_slit` (search literals
  never increase — the subscript-blocked cases of the old census are D1 now or honestly
  Dbox*). The conjecture's residue is now EXACTLY the three box obstructions.
- **C3b-i′ ✅ (2026-07-03, T48 §10 — the diagnostic, resolved by REFUTATION; see §5d)**:
  the linked trichotomy is FALSE, twice over — `ppair_linked_false` (box-content pairs of
  premise-free axioms are arbitrary; boxT descent must go) and `spine_boxlinked_false`
  (guarded tail pairs carry no pairwise information; guard context is necessary). Output:
  the corrected foundation — guard-context motive `PosImplCtx`, budget-strong-induction
  (pair-queries never cross cites), and the single kernel `HBoxHead`. Supersedes the
  retracted C3b-i and the old C3b-ii plan below.
- **C3b-ii′ ✗ KERNEL REFUTED (2026-07-03, T48 §11 — see §5e)**: probing `HBoxHead` before
  building on it found it FALSE (`hboxhead_false`), along with the head-level linked
  dichotomy itself (`head_dichotomy_false`), via the dead implication `deadJ`
  (wild boxed antecedent, tame unprovable consequent — never fires via `app`). Third and
  closing refutation: the judgment-local program is DEAD at every position class. The
  conjecture survives (all counterexamples are excisable dead weight).
- **D0+D1 ✅ (2026-07-03, `T49TreeSubstrate.lean`) — the tree substrate, fork (A)'s
  foundation**: the `Type`-valued mirror triple `PlaysT`/`AtomT`/`ProvT` (constructor for
  constructor; `struct` carries its `Derivation` witness), `sound` + `complete` —
  **`Provable k φ ↔ Nonempty (ProvT k φ)`** (`Provable_iff_nonempty_ProvT`); `gateOK G t`
  (the cut DIET of one specific tree, through the six T42 gate positions AND the atom
  layer's guard cites); `toG` (a tree with passing residue lands in `ProvableG G`); and
  the official reduction **`tree_cutRelevance : TreeCutRelevance N₀ → CutRelevance N₀`**
  (plus the modest variant `tree_modestRelevance`). The conjecture is now a statement
  about trees — `∃ t, gateOK … t` — which dead implications cannot refute: excision may
  REPLACE the tree, not just describe it.
- **D2a ✅ (2026-07-03, T49 §7) — the excision toolkit's first layer**: `ProvT.mono`
  (budget monotonicity by root re-gating — structure untouched), `ProvT.mono_gateOK`
  (re-gating preserves the cut diet), `ProvT.impl_size_le` (every impl node pays its
  conclusion's size — the crossing arithmetic's backbone; atoms cannot conclude impls),
  and `cross_weaken`/`cross_weaken_gateOK` (the first excision: `weakenImpl`-headed
  `app`s drop their argument, same diet, within budget — the entry through which every
  §5e counterexample dies). Design record: §5f (backward-tame subscripts, backward-tame
  content, the budget discipline, the `spineCross` master statement).
- **D2b-probe ✅ (2026-07-03, T49 §8 + §5g) — the reduction + the wall**: the
  compression ceiling is kernel-checked (`ProvT.box_size_le`, `ProvT.box_subscript_lt`:
  budget-`k` boxes have subscripts `< 2^k` — only `boxIntro`/`app` conclude boxes, both
  pay). With C0 and the backward-tameness observations this REDUCES the conjecture to
  ATOM MODESTY (§5g): the literal half is free at
  `N₀ (k,φ) := 2^(max k (maxLitF φ)) + maxLitF φ`; what remains is that some minimal
  tree's cut atoms stay in the root's program pool. Also found: the GENTZEN WALL
  (`impS2` duplicates a discharge — kills total-size termination; strict-`k` budgets
  survive IF excision is stated per-subtree-budget-preserving); two fork-(C) forcing
  attempts died on Observations 1&2 (recorded — evidence FOR the conjecture).
- **D2c ✅ (2026-07-03, T49 §9–10) — `boxInvGo`, the fueled extraction machine, RUNS**:
  the spine machinery collapsed to a STACK MACHINE over a dependent discharge stack
  (`DStack ξ core`) — push at `app`, drop at `weakenImpl` (excision), compose at
  `implTrans`, duplicate at `impS2` (fuel absorbs the Gentzen contraction), apply-self
  at `diagF`, consume at the modal leaves where each gate pays its own extraction
  (`axK`/`axKf` at `a+b+|α| ≤ c`, `box4` re-boxes the mono-lifted content at
  `a+|□aφ| ≤ b`, `boxMono` passes `a ≤ b`). Result type computed from the core
  (`BoxContent`) ⇒ every `some` is CORRECT BY CONSTRUCTION: **box contents are
  derivable within their own subscripts** (box honesty). `#eval` demos extract through
  real trees (direct and behind app/weaken detours), returning at exactly the
  subscript. LEAN NOTE: dependent matches over `DStack` generalize away the core's
  box-structure — computing the return type from the core (`BoxContent core`) fixes it
  with zero casts; shape-excluded arms return `none` (sound; unreachability belongs to
  totality).
- **D2d ✅ (2026-07-03, T49 §9–10 revised) — the totality audit caught a LOOP; the Löb
  pair is now a second core**: the original `diagF` arm (apply-self, keep peeling)
  returns to its own state two steps later — sound (fuel runs out) but totality-fatal.
  Fix: `CoreContent` also makes `.diag` extractable (a diag's content is the implication
  it abbreviates, budget-free); `diagB` + non-empty stack is the diag base case (its
  discharge IS the content), and `diagF` extracts its diag discharge's content and
  applies it — strictly decreasing. New `#eval`: extraction through a full
  `diagF`/`diagB` fixpoint pair down to a real box, at exactly the subscript.
  TOTALITY LEDGER (audited arm-by-arm, measure `W = |t| + Σ|stack|`): app −1, weaken
  −1−|d|, implTrans 0 with |t| strictly down (lex), diagF strictly down (extracted
  content ⊊ consumed discharge), dives fresh-smaller, leaves terminal; the SOLE
  obstruction is `impS2` (+|d| — Gentzen contraction, as §5g predicted). All `none`
  arms have UNINHABITED state types for box/diag cores (DStack index chasing +
  `derivation_shape`).
- **D2e-1 ✅ (2026-07-03, T49 §11) — the totality toolkit**: `ProvT.wt`/`DStack.wt`
  (walkable weight — atom certs and Derivations are terminal), `freeS2`
  (contraction-freedom), `mono_wt`/`mono_freeS2` (re-gating preserves both), and the
  substantive joint lemma **`boxInvGo_wt_le`**: on contraction-free states, extraction's
  result weighs no more than the state consumed AND is itself contraction-free (both
  halves fail on `impS2` — the hypotheses are exact). LEAN NOTE: the machine had to be
  restructured (tree matched first, stacks in small nested per-arm matches) because the
  combined deep dependent match defeats the equational-theorem generator — without
  equations, `simp only [boxInvGo]` is dead and every proof fights whnf by hand.
- **D2e-2 ✅ (2026-07-03, T49 §12) — THE MASTER TOTALITY THEOREM**:
  `boxInvGo_total` — on contraction-free states with a box/diag core the machine ALWAYS
  halts with `some`, and the corollary **`boxInv_total_of_freeS2`** gives box honesty
  TOTAL with closed-form fuel `(wt t + 1)² + wt t + 1`. Induction on FUEL alone (each
  call burns one unit; the lex measure lives in the threshold arithmetic:
  `thr_step`/`thr_same`, with `(P+1)²` as an omega-opaque atom via `Nat.mul_le_mul` +
  one expansion identity). Every `none` arm closes by `IsCore` reduction, `DStack`
  index chasing, or `derivation_shape` (`EndsInPlays.no_core_stack`). LEAN NOTES:
  pin `thr_step`'s `P'` explicitly (metavariables in omega goals otherwise); get the
  dive results via `Option.isSome_iff_exists` + `rw` rather than `cases hd :` (cases
  substitutes the scrutinee in the goal, breaking the later rewrite);
  `Nat.le_of_succ_le_succ` aligns the `+1+1 ≤ F+1` threshold shapes.
- **D2f-a ✅ (2026-07-03, T49 §13) — cut-diet bookkeeping: extraction PRESERVES the
  gate**: `boxInvGo_gateOK` — if the input tree and stack pass `G`, the stack's segment
  formulas pass `G`, and `G` is box-content-closed (`G (.box b ψ) → G ψ` — true of
  `litGate` and the modest gate), then the extracted tree passes `G`. The arms align
  EXACTLY: every materialized `app`'s gated argument is a stack segment whose
  obligation is supplied by the very node that pushed it (`app`'s own `G φ`,
  `implTrans`'s/`impS2`'s `G ψ`), except the `axK`/`axKf` leaves which need the one
  closure hypothesis. NOTE: holds for ALL trees including `impS2` — only TOTALITY
  needs contraction-freedom; the diet is safe unconditionally. Dives never leak exotic
  cuts.
- **D2f-a′ ✅ (2026-07-03, T49 §14)**: the gate instances — `litGate_box_closed`,
  `modestGate_box_closed` (both gates are box-content-closed, so §13 applies to them);
  the §12 closed-form fuel validated live by `#eval`.
- **D2f-b groundwork ✅ (2026-07-03, T49 §15 + machine rev)**: the `diagF` continuation
  INLINED (`(x, d2::S'')` directly — semantically identical, one step cheaper, and the
  materialized `app`-node charge that polluted every measure candidate is gone from the
  design space); all three conservation theorems updated (their `diagF` arms
  simplified). Plus `ProvT.s2d` (`impS2`-nesting depth), `mono_s2d`, and
  **`boxInvGo_s2d_le`** — extraction never increases contraction depth,
  unconditionally: navigation moves subtrees, extraction assembles only `app`/`boxIntro`
  nodes, never an `impS2`. This is the conservation input the stratified measure needs
  (the depth-indexed `Ψ_d` family is well-defined on machine runs only because depth
  cannot resurge).
- **D2f-b status upgrade (2026-07-03, post-inlining re-check)**: the linear potential's
  failure is DEEPER than diagF-promotion — even Φ-CONSERVATION breaks at the `axKf`
  leaf: its result `app(r1, r2)` multiplies two STACK potentials (`Φd1·(Φd2+2)`), and a
  premise-free leaf has only a constant node-charge to pay with. Stack×stack products
  are intrinsic to the Löb/K-distribution patterns (`axKf` leaves and `diagF`
  continuations). CONCLUSION: **every local-charge scheme is provably insufficient** —
  contraction cost depends on discharged material unknown at the node. Remaining routes:
  (i) Tait-style computability predicates over `ProvT` (the honest SN proof;
  heavyweight); (ii) a Gentzen rank development on segment formulas; (iii) PER-INSTANCE
  fuel — the machine already semidecides, and concrete zoo trees can be excised by
  `#eval` with per-theorem certificates (E-grade thesis content without the SN proof).
- **D2f-c ✅ (2026-07-03, T49 §16) — executable diet certificates**: `gateOKb` (the
  Boolean mirror of the cut-diet check, over the full mutual triple),
  `gateOKb_sound`, and **`certify`** — a concrete tree whose checker returns `true`
  lands in `ProvableG (modestGate N)` via `toG`. The route-(iii) pipeline runs live:
  `#eval` extracts a box content and CHECKS its diet (`true` at `modestGate 2`).
  Per-instance CutRelevance is now: build/synthesize the tree, run the excisor, run
  the checker, `certify`. Missing for zoo-scale instances: a tree SYNTHESIZER
  (`decFullT`-style, or hand-built trees for the flagship theorems).
### The D2f-b route-map (2026-07-03, deep-dive) — why this is a THEOREM-SIZED problem

Seven standard normalization techniques, each pushed to its exact failure point against
this machine (do not re-derive):

1. **Local-charge potentials** — provably insufficient: contraction cost depends on
   discharged material unknown at the node; stack×stack products at `axKf`/`diagF`
   (details in the milestone entries below).
2. **Tait on formula structure** — breaks at `.diag`: a RECURSIVE type
   (`diag g tgt` unfolds to `impl (box g (diag g tgt)) tgt`, which CONTAINS it), so
   formula-size recursion is ill-founded. The Löb fixpoint doing exactly what it does
   in GL: defeating naive formula induction.
3. **Type-order (arrow-depth) ranks** — same failure: `order(diag) = ∞`.
4. **Step-indexed logical relations** — the index breaks the diag circle but
   step-indexing proves SAFETY, not termination; useless for totality.
5. **Budget-indexed Tait** — promising (KEY FACT: the diag formula PINS its unfolding
   budget — every `□g(diag g tgt)`-content lives at budget `≤ g`, the SAME `g`, forever;
   Löb unfold-chains are budget-capped, which is WHY this calculus should normalize) —
   but breaks at arrow-quantification: `Good(impl B C)` must quantify over arguments of
   arbitrary budget/weight, so no `(budget, |ξ|)` or `(weight, |ξ|)` lex founds the
   definition.
6. **Counting/tower measures** (`#impS2`-weighted, `W^N`, towers) — close UNNESTED
   contraction but break on nested: a fired `impS2` duplicates a discharge whose own
   count/depth is arbitrary (stack material).
7. **Syntactic fragments** (stack-monotone, `s2depth ≤ 1`) — violated by the most
   common REAL pattern: `app(axKf-leaf, huge-Löb-argument)`.

**What a correct proof needs** (the positive residue): Tait with the arrow case
quantifying over MACHINE-REACHABLE arguments only (biorthogonality over reachable
stacks — the machine is closed, and weight strictly decreases at every extraction
along a run), the diag circle broken by the pinned budget `g` (fact 5), outer induction
on run-closure material. This is normalization for a **bounded-Löb modal proof
calculus** — plausibly novel (GL lacks ordinary cut-elimination; boundedness is exactly
what restores it) and plausibly a stand-alone paper. It needs offline mathematical
iteration. Meanwhile the thesis does not wait: `boxInv_total_of_freeS2` covers the
contraction-free fragment, and the executable instance route (synthesize → excise →
check → `certify`) delivers zoo-scale certificates without the SN theorem.

- **D2f-b ✅✅ THE NORMALIZATION THEOREM (2026-07-03, T49 §19–23)**: `boxInv_total` —
  UNCONDITIONAL, kernel-checked, zero sorries; full machine form `machine_total`
  (every well-typed state with a box/diag core halts); total computable extractor
  `boxInvT` + `box_inversion_diet` (diet-controlled constructive box inversion);
  `diagInv_total`. See `BOUNDED_LOB_NORMALIZATION.md` (paper-grade record: the
  Y-diagnosis, the nine-route failure map, the `Good` design on lex `(k, μ(box)=0,
  phase)`, the fundamental lemma).
- **D2g (NEXT — the assembly; the ONE remaining design task): the general-core
  crossing.** The excisor must β-reduce wild cuts whose spine ends at ARBITRARY
  formulas, not just box/diag cores. Design spec:
  1. Extend `CoreContent` to all formulas: for non-box/diag cores,
     `CoreContent φ := Σ' m', ProvT m' φ` — the crossing simply returns a tree of the
     spine-end judgment.
  2. New machine base cases at plays/eq cores: `atom`-nodes return themselves;
     `struct`-nodes require the DERIVATION-LEVEL crossing — walk `modusPonens`/`hypSyll`
     chains with the stack, and at census leaves (`searchBranch` etc.) RECONSTRUCT the
     atom certificate: extract the discharged guard box (via `boxInvT` — total now!),
     lift to `Provable` by soundness + budget-mono, and build the `PlaysT.search_t`
     cert (trivial for `.const` branches — the zoo shape; recursive for nested
     branches — bounded by the same `Good` machinery). THIS is the remaining
     sub-problem with content: atom-cert reconstruction at census leaves.
  3. Totality/diet for the extended machine: rerun the §19–21 pattern (the `Good`
     framework is core-shape-agnostic except at the base cases — new bases are
     terminal, so the measure arguments carry over verbatim).
  4. The excisor: walk any tree of a modest root; gated cuts with `cutOKb`-failures
     are β-reduced via the extended crossing (their consumers hold the discharges);
     KEY simplification from §5g + N₀'s self-calibration: with
     `N₀ := 2^max(k, maxLitF φ) + maxLitF φ`, ALL logic-layer literal-gates pass
     automatically (C0), `axK`/`diagF/B` premise-gates are conclusion-tied (auto-tame
     for pool roots) — the ONLY genuinely wild cuts are fresh-ATOM middles in
     `implTrans`/`app`/`impS2`, and cite-strata escalation through them. Excising
     those with the crossing + T43 pool-closure for everything ungated yields
     `TreeModestRelevance` for zoo roots.
  5. Plug into `tree_modestRelevance` + T47 ⇒ `Provable` decidable on the zoo
     universe ⇒ `proofSearch` computable ⇒ `eval` computable ⇒ outcomes `by decide`.

  **D2g build-spec (2026-07-03, census inventory done — ready to execute):**

  * Extended cores: `CoreContent (.plays p q c) := Σ' k', AtomT k' (.plays p q c)`;
    `.eq`/`.neg`/`.impl` cores ↦ `Σ' m', ProvT m' core` (tree of the judgment). Nil-base
    at general cores: return the walker (`some ⟨m, t⟩` — @-pattern). NOTE: this breaks
    `boxInvGo_wt_lt`'s strictness at general cores — restate it with an `IsCore`
    hypothesis (box/diag only); all other conservation lemmas gain trivial arms.
  * `derivCross`: the Derivation-level walker (mutual with the machine), reusing
    `DStack`. Arms: `hypSyll(d1, d2)` composes like `implTrans` (its middles are
    C1-tame, size-paid — no gate obligations!); `modusPonens(d1, d2)` walks `d1` with
    `.struct d2 (le_refl)` pushed; `eqRefl`/`eqNeg` are nil-base leaves. Census leaves
    with their reconstructions (all branches `.const` — certs are TRIVIAL):
    - `searchBranch`/`botSearchStep` (+ discharge `u : □k ψ'-tree`):
      `tc := boxInvT u` (TOTAL now) — and T49's `PlaysT.search_t` takes the `ProvT`
      guard DIRECTLY (`tc.mono : ProvT k ψ'` — no Prop round-trip, diet preserved by
      `box_inversion_diet`); branch cert `PlaysT.const`; assemble
      `.atom (.mk (search_t …) le_refl)` at cost `c_leaf + c_guard k + c_node` — tiny,
      budget-mono lifts to the site's budget.
    - `simStep`/`botSimStep` (+ discharge `u : plays-tree`): extract `u`'s `AtomT` via
      the plays-core machine (mutual recursion — `.atom` base, app-chains walk,
      `struct` re-enters `derivCross`); its `PlaysT` is exactly the `.sim`-premise
      shape; wrap with `PlaysT.sim`/`.bot`.
    - `iteBranchSearch_t` (two segments: guard-atom + box): rebuild via
      `PlaysT.ite_t(sim-wrapped guard cert, ==-check, search_t branch cert)`; needs
      `closedP z` (so `z.subst = z` aligns the frames — free for modest material via
      `substP_id`).
  * Totality/diet for the extension: rerun the §19–21 `Good` pattern — general-core
    nil-bases are terminal (measure arguments verbatim); `derivCross` recursions are
    structural on the Derivation (its middles carry no gates) plus dives already
    covered by `machine_total`.
  * Then the excisor (walk + `cutOKb`-check + β-reduce via the extended crossing) and
    `TreeModestRelevance` for zoo roots. Structural insight: every duplication of a discharge happens under a
  strictly SHALLOWER `impS2`-walker, so tower-bounded fuel (`~wt · 2^(2^D)` at nesting
  depth `D`) EXISTS; the fight is the invariant. **Measure attempts, with exact failure
  points:**
  * Linear-stack potential `Ψ := Φ(t)·(1 + ΣΦ(dᵢ))` with `Φ(impS2 tf tx) := Φtf·(Φtx+2)`
    — handles `impS2` STRICTLY (the multiplicative node-charge pre-pays the duplicate),
    and `app`/`weaken`/`implTrans` close with `Φ(app f x) := Φf·(Φx+2)` etc. — but
    BREAKS on `diagF`: the continuation promotes the EXTRACTED tree to walker over the
    tail, turning stack-cost multiplicative (`Φx·(Φd2+2)·(1+S'')` vs the linear old
    `Φ(t)·(1+Φd1+Φd2+S'')` — triple products can't be dominated).
  * Fully multiplicative `Ψ := Φ(t)·Π(Φ(dᵢ)+2)` — handles `diagF` and the navigation
    arms (with `+1` paddings for strictness) — but BREAKS on `impS2`: the duplicate
    makes the new `Ψ` QUADRATIC in `ΦdB`, which no `dB`-independent node-charge
    `Φ(impS2)` can pre-pay.
  * Semi-multiplicative (`SP(d::s) := (Φd+1)·SP(s)+1`) — same quadratic failure.
  So the resolution must STRATIFY BY `s2depth`: below the walker's depth the potential
  may be multiplicative (duplicates only ever re-duplicated by shallower walkers),
  at-or-above it must stay linear; i.e. a depth-indexed family `Ψ_d` with the outer
  induction on `d` (the depth-0 case IS the proven `boxInvGo_total`). Alternatively the
  shared-environment/mix formulation. A full fresh session for the design, then one for
  the Lean. Then: `spineCross` on the same machine; `TreeModestRelevance` for zoo roots
  into T47's decider.
- **C3b-ii (superseded as stated)**: the master transform — thread the carried-transform payloads through `Tri`
  (D2 gains its `ProvableB`-transform; Dbox* resolved by the sibling machinery per §5/§5a′:
  DboxAnt at discharge-apps, DboxPos via box-content judgments (`box_inversion`), DboxMid
  is the open kernel — attack via a side induction on the middle's box-structure, or show
  its wild instances are D2-absorbed as in the confinement argument). Target unchanged:
  `Provable k φ → ProvableB (2^(max k (maxSLitF φ) + 2)) k φ`.
- **C4**: Lemma B rewrites + budget arithmetic (or the budget-inflated fallback).
- **C5**: assembly — `CutRelevance` (possibly budget-inflated) for modest roots; plug into
  T47 ⇒ `Provable` decidable on the zoo universe; `proofSearch := D`.

---

## §6 — HANDOVER BRIEF: the assembly theorem (for the next session/model)

**Target.** For modest roots `(k₀, φ₀)`: iterated excision yields a tree passing
`modestGate N₀`, `N₀ := 2^max(k₀, maxLitF φ₀) + maxLitF φ₀`. Literal half is FREE (C0 +
compression ceiling, §5g). Only the POOL half (atom modesty) needs proof.

**The invariant (design candidate).** Pool `P` := T43/T46 closure of `φ₀`'s programs
(`allowedProgs` exists in T46). `PoolF ψ` := every atom of `ψ` has programs in `P`.
Claim: in an excise-FIXPOINT tree of a pool-good root, every gated formula is PoolF.
Argument sketch: a surviving wild gate must be an `app`-cut (axK/diag premises are
conclusion-tied; implTrans/impS2 middles — see O4); an `app`-cut has its discharge in
hand, so the excisor would have crossed it — contradiction with fixpoint — UNLESS the
crossing fell back (O2/O3).

**Status 2026-07-08: O1 ✓ O2 ✓ O3 ✓ (T49 §25–§28). O4/O5 remain.**
- **O1 DONE** — `exciseFix`/`certifyExcised` (T49 §26); demo certifies the wild app.
- **O2 DONE, stronger than planned** — instead of weakening the fixpoint theorem, the
  MACHINE was totalized: the two partial-application gaps (`diagF@cons-nil` extracts the
  diag content — its tree IS the impl core; `axKf@cons-nil` repackages as an `axK` node
  with the discharge as premise field, gate paid by the stack's `segsOK` segment, weight
  exactly `d1.wt+1 ≤ 1+d1.wt`) were closed and all five conservation packages extended.
  Then the WIDE goodness family (`GoodW`/`GoodStackW`-nil := True/`ContentGoodW` with
  ATOMIZABLE plays-contents — the enrichment dissolving the fundamental↔atomize
  circularity), DUPLICATED not modified (zero ripples into §20–§23), hypothesized on
  `dbFree` (no `iteBranchSearch_t` — the one unreconstructible census):
  `GoodW_app` → `atomizeW_halts` → `GoodW_mono` (transport WITHOUT core-typed regate —
  this is why box4's inner content needs no `IsCore`) → `GoodD` (struct-crossing by
  Derivation-induction; mp-nil proves atomizability inline via the d1-IH at the
  (struct d2)::nil stack) → `fundamentalW` (16 arms) → **`crossTotalW`**: at EVERY
  wild-app state `(f, x::nil)`, any result formula, the machine halts with wide-good
  content. The excisor's beta-step is total on dbFree trees.
- **O3 DONE (by inspection)** — axK/diagF/diagB gates are conclusion-tied (+ subscripts
  size-paid); diag-cuts never need excision.

**Obligations remaining:**
- **O4 WARNING (new counter-scenario, 2026-07-08):** option (a) as stated is too
  strong: an `implTrans`/`impS2` node that is NEVER applied (e.g. the ROOT itself is
  impl-shaped and ends in `implTrans`) has no upstream app to convert its middle. For
  such middles the pool argument must go through the IH directly: the middle is the
  CONCLUSION of the subtree `tA` (premise formulas are budget-bounded by transcript
  costs — the size half; the pool half of a conclusion formula follows from the
  subtree's own pool-invariant). So O4 folds INTO O5's induction: gated-formula
  pool-goodness needs a simultaneous "conclusion-formula pool-goodness" strand, not an
  app-conversion detour. For applied middles the machine's implTrans-arm
  materialization story stands.
- **O1 (excise-until-fixpoint) — original text.** Current `excise` is one pass. Iterate: crossing
  outputs can carry NEW wild gates at the `axK`/`axKf` assembly apps (gate = segment-box
  CONTENT, subformula of a wild segment). Termination of iteration: strict consumption
  (`crossWtLt`) — each successful cross strictly reduces `wt`; iterate on `wt` or fuel.
- **O2 (general-core crossing totality).** `machine_total` covers box/diag cores only
  (`IsCore` in `GoodStack`-nil). Extend the `Good` framework: `GoodStack`-nil := True at
  ALL cores; general-core `ContentGood` := True. Re-run §21's fundamental (the
  identity/census bases are terminal — measure arguments carry; the struct-cons arms
  now recurse through `structCross`, whose dives are covered by the same `∀k`-motive at
  the SAME fuel-style composition as diagF). If it fights, weaken the fixpoint-theorem
  to "wild gates only at cores where crossing returned none" and handle those instance-wise.
- **O3 (diag fallback).** `contentToTree` punts diag cores. Either thread the Löb
  premise (a diag-cut's consumer context has it) or accept diag-cuts as
  conclusion-tied (they ARE: `.diag g tgt` gates are `G (.impl (.box fb tgt) tgt)` —
  tgt conclusion-tied, fb size-paid — CHECK: these never need excision at all).
- **O4 (implTrans/impS2 middles).** v1 excisor only crosses `app`s. Wild MIDDLES in
  chains have no local discharge. Two options: (a) show fixpoint trees of pool roots
  have no wild middles because chains are consumed at apps upstream (the middle becomes
  an app-cut after the outer crossing — likely TRUE via the machine's implTrans-arm
  materialization); (b) extend excise to rotate chains into apps. Try (a) first.
- **O5 DESIGN (2026-07-08, the middle-elimination route — read this first).**
  The pool argument's ONLY remaining gap is never-applied `implTrans`/`impS2` middles
  (applied middles LAUNDER: the machine's implTrans-arm materializes `app(tA, dB)` as
  a segment; the middle formula disappears from the result tree — the result is
  assembled from subtree INTERNALS + censuses, so its pool-status comes from the
  subtrees by IH, not from the middle). For never-applied middles, three facts found
  2026-07-08:
  1. **The calculus contains the combinatory basis**: `weakenImpl` IS rule-K
     (`⊢ψ ⟹ ⊢φ→ψ`), `impS2` IS rule-S (`⊢φ→(ψ→χ) ⟹ ⊢φ→ψ ⟹ ⊢φ→χ`), `implTrans` is
     rule-B. So BRACKET ABSTRACTION over a virtual discharge is definable on the
     APPLICATIVE fragment: run the machine on the never-applied node with a virtual
     hypothesis leaf `x̂ : φ'`, then abstract `[x̂]r` — K-steps for x̂-free subtrees,
     S-steps at apps. The abstraction's new cuts are subformulas of the path types —
     pool-tied. Budget inflates polynomially (the C4 budget-inflated fallback covers
     this).
  2. **Wall 1 — bare returns**: `[x̂]x̂` needs object-I (`⊢ A→A`), which rule-K/S
     CANNOT derive (object-K `A→(B→A)` is not an axiom here; `I = SKK` needs it).
     Check whether bare-x̂ returns actually occur: the machine returns the discharge
     verbatim only at `diagB@cons-nil` (diag content := the discharge) — conjecture:
     for virtual middles this case is conclusion-tied (diag shapes).
  3. **Wall 2 — modal embeddings**: x̂ can end up UNDER a `boxIntro` (via the box4 arm
     re-boxing extracted content that contains x̂). Abstraction cannot cross a box
     without axK-distribution over a BOXED hypothesis — the GL/necessitation boundary
     (same wall the normalization theorem dodged with μ(box)=0). Conjecture: x̂ enters
     box-content only through box-EXTRACTION of x̂-containing discharges, whose sites
     are census/box-consumption — exactly the CONCLUSION-TIED link shapes (searchBranch
     antecedent = the link's own guard box, etc.). So the dichotomy to prove:
     **every x̂-occurrence in a virtual run's result is either applicative (bracket
     abstraction applies) or at a census/box/diag consumption site (the middle is then
     conclusion-tied to a primitive link and pool-good directly)**.
  Plan: (i) formalize the virtual-hypothesis leaf as a ProvT EXTENSION (Type-layer
  normalization device only — never enters Provable); (ii) prove the dichotomy by the
  conservation-package induction pattern; (iii) bracket-abstract the applicative side;
  (iv) fold into the crossPool induction below. Alternatively, if the dichotomy fights:
  scope CutRelevance to the T47 query universe's actual root shapes and characterize
  impl-guard bots' chains directly (the zoo's impl guards are few and shallow).
  **Zoo audit (2026-07-08): the scoped route wins.** Every guard formula in the entire
  zoo is a PLAYS ATOM (`plays .opp .self C`, `plays .opp (.bot DefectBot) D`, …) except
  CIMCIC/DIMCID, whose guards are the single shape `impl (plays a b c) (plays d e f)`
  — depth-1, atoms on both sides. So the recursion closure of T47 root shapes contains
  exactly ONE impl-shape. CutRelevance-over-the-zoo (which is how T4 is already scoped
  — the modest universe IS zoo-derived) needs the middle analysis only for
  `impl atom atom` roots, where the known derivation forms are `weakenImpl(atom-cert)`
  and the Löb chain `atomBoxImpl → axK/boxMono links → guard-box` — all middles
  box-shaped and conclusion-tied. The general dichotomy/bracket-abstraction machinery
  is NOT needed for the thesis-grade zoo statement; keep it as the route for full
  generality.
- **O5 SITE INVENTORY (2026-07-08, verified against the actual defs — supersedes the
  sketch below).** The assembly = proving `certifyExcised rounds fuel N₀ t = some _`
  for modest roots. The final check is `gateOKb (cutOKb N₀)` on the survivor; the
  obligation decomposes over the gate sites of `ProvT.gateOK`/`derivGateOK`:
  1. **`app` cuts `G φ`** — by the FIXPOINT (needs the progress lemma: each wild fire
     strictly reduces wt via `crossWtLt` + halts via `crossTotalW`, so wt-many rounds
     suffice; excision of subtrees with their own wild cuts iterates outside-in).
  2. **`axK` premise `G (.box a (.impl φ α))`** — DONE: `modestGate_axK_tied` (T49,
     kernel-checked): fully conclusion-tied, `maxLitF` counts box subscripts and
     `hg1 : a+b+α.size ≤ c` bounds the premise subscript.
  3. **`diagF/diagB` gates `G (.impl (.box fb tgt) tgt)`** — `modestGate_diag_tied`
     (T49, kernel-checked): tied modulo `fb ≤ N` — the ONE literal-half consumer at
     the ProvT level (fb = the stored Löb premise's subscript, bounded by its budget
     via compression-ceiling/C0).
  4. **`implTrans`/`impS2` middles `G ψ`** — the zoo-scoped middle argument (one
     impl-shape; see the middle-elimination design above).
  5. **`derivGateOK` sites — CLOSED 2026-07-08** (`DAnt_gate`, T49, kernel-checked):
     `modestP_subst`/`modestF_subst` (modesty survives substitution by modest argOK
     players) → `DAnt_modest` → with `T48.DAnt_lit`, every census antecedent passes
     the gate whenever its consequent does. mp cuts are antecedents of the
     impl-premise (`derivation_impl_ant`), hypSyll middles are `DAnt.trans` legs —
     both covered. The feared **eqNeg cuts are IMPOSSIBLE** at the Derivation level:
     `DAnt` has no eq-shaped antecedent constructor, and every Derivation-level
     impl-antecedent is DAnt-census-legitimate. What remains for this site in the
     big induction: the node's CONCLUSION gate (the induction's own invariant).
  6. **`searchThenSearch_t`'s stored premise tree + all recursive `t.gateOK`** —
     recurse into the same inventory.
  Plus the LITERAL HALF — **already kernel-checked (found 2026-07-08)**: T48
  `cut_lit_bound`/`box_lit_bound`/`maxLitF_lt_two_pow_size` — `Formula.size` charges
  `log2+1` per numeral, so every rule's `hle` pays literal digits; NO new induction
  needed, only glue: (a) budgets descend node-by-node (each constructor's `hle`),
  (b) the ProvT mirror transports the Provable-level bounds to stored subtrees
  (`Provable_iff_nonempty_ProvT`). This also answers the weakenImpl worry: antecedents
  ARE size-charged. Item 3's `fb ≤ N₀` = `cut_lit_bound` at the stored premise.
  **BUT (arm-level check, 2026-07-08): a STANDALONE tree-wide literal lemma is
  impossible** — `PlaysT.gateOK` recurses into `search_t` cites whose budgets are
  program search-SUBSCRIPTS (§5g's escalation channel), not sub-budgets of the root;
  so `∀ t : ProvT m φ, t.gateOK (litGate 2^m)` fails at every atom boundary. The
  literal and pool halves interlock at exactly the cites: cite budgets ≤ maxLitP ≤
  the ATOM's program literals, which only the POOL premise bounds (then N₀ :=
  2^max(k, maxLitF φ₀) covers every stratum). Consequence: ONE simultaneous
  induction — `t.gateOK (modestGate N₀)` with the cut-atoms-in-pool hypothesis —
  is the irreducible shape of the assembly theorem; do not attempt split halves.
  (This is `local_lit_bound`'s docstring caveat, now confirmed at the arm level.)
  ALSO FOUND: **fixpoint progress needs no strict-decrease package ON THE
  CONTRACTION-FREE FRAGMENT** — a β-reduced wild app strictly shrinks by the app
  node's own +1 (`excise_wt_freeS2`, kernel-checked 2026-07-08: excision never
  gains weight and preserves freeS2, so wt-many rounds suffice). CAVEAT (correcting
  an earlier over-claim): `crossWt` is freeS2-CONDITIONED — impS2 crossings have NO
  weight bound (the Gentzen wall, §5g) — and Löb-bearing zoo trees DO contain impS2
  (bloeb uses it). So progress for Löb trees still needs the s2depth-stratified
  potential; only the contraction-free fragment's progress is closed. Remaining for
  progress: excise-walk bookkeeping (each pass fires ≥1 wild app or the app-half
  of the check passes). dbFree-conservation of machine outputs: **DONE 2026-07-08**
  (`crossDbFree`, T49 — with `DStack.dbFree`/`CoreContent.dbFree`/`mono_dbFree`),
  and lifted through the excisor: `excise_dbFree`/`exciseFix_dbFree` — every
  round's output satisfies `fundamentalW`'s hypothesis (the iteration license,
  end to end).
- **THE TIE-DOWN DESIGN (2026-07-08, the centerpiece's final shape — derived to the
  arm, supersedes all earlier sketches of the interlocked induction).**
  KEY REALIZATION: atoms' plays-formulas are NEVER gate-checked (`gateOK` gates only
  the six premise-formula sites and recurses); atom conclusions are conclusion-tied.
  So the assembly does NOT need atom-pool membership as such — it needs exactly:

  **`gateOK_of_cutsOK`** (the tie-down): for `t : ProvT m ξ`,
  `modestGate N ξ` (root conclusion gated) + `t.cutsOK (modestGate N)` (ONLY the
  app/implTrans/impS2 CUT sites pass — everything the excisor + middle analysis
  deliver) + `t.citesLE M` (every `search_t` cite budget ≤ M, hereditarily) +
  `m ≤ M` + `2^M ≤ N`  ⟹  `t.gateOK (modestGate N)`.
  Proof: one induction threading THE NODE'S CONCLUSION GATE downward:
  * app/implTrans/impS2: children's conclusions = parent conclusion pieces + the
    HYPOTHESIZED cut/middle gates. weakenImpl/boxIntro: subformulas.
  * axK: `modestGate_axK_tied` (no budget needed — hg1). diagF/diagB:
    `modestGate_diag_tied` + `fb < 2^pm ≤ 2^M ≤ N` (T48 `diag_lit_bound`/
    `cut_lit_bound` via ProvT.sound; budgets descend node-by-node through `hle`
    EXCEPT at cites, where `citesLE` caps them — THIS is where the interlock
    was, now an explicit hypothesis).
  * struct: `DAnt_gate` (mp cuts + hypSyll middles conclusion-tied; eq cuts
    impossible). sTS: tw's conclusion `ψ₂.subst me opnt` gated via
    `modestF_subst` + inner-guard extraction from `modestP me` (the DAnt_modest
    searchBr pattern) + literals ≤ maxLitP me ≤ N.
  * atom: recursion into cites: the cite's conclusion `φg.subst me' opnt'` gated
    by `modestF_subst` from the ATOM's conclusion-gate; its budget ≤ M by citesLE;
    recurse with the same (M, N).

  **Consumers must then supply**: (i) cutsOK of the excise-fixpoint tree = app-half
  by construction (the cutOKb check drives the fire) + middles (zoo case);
  (ii) citesLE conservation through crossing/excision (a crossCites package —
  census cites have budgets = guard subscripts of CONCLUSION programs ≤ maxLitP ≤
  M; mechanical, the crossDbFree pattern); (iii) citesLE of the ORIGINAL tree —
  the conjecture's irreducible residue: for zoo roots, cite budgets are guard
  subscripts of pool programs (≤ maxLitF φ₀); for ARBITRARY minimal trees this is
  exactly the open core (a gate-passing-but-fresh cut with a huge-subscript
  search program inside would escalate — the pathology CutRelevance must exclude
  or excise). N₀ := 2^max(k₀, maxLitF φ₀) + maxLitF φ₀ with M := max k₀ (maxLitF φ₀).

- **O5 (the pool lemma proper — original sketch).** Census outputs: programs are subst-instances of
  conclusion programs (T43 `subsP/substF` lemmas + `playsArgsF_subst`); contents:
  subformulas of segments — pool-good if the SEGMENT-BOX's judgment formula is (the
  discharge's conclusion, which is a formula of the pre-excised tree — IH). Package as
  a crossPool induction in the crossWt/crossGateOK style (the transformation recipe is
  in memory: extract old succ-body, ascribe the `.1`-projection, part-2/3/4 fresh).

**Traps already paid for (do not rediscover):** tactic-mode dispatcher bodies for
index refinement; flipped equations (`Formula.impl B rest = ξ`) so `cases heq`
substitutes; census helpers term-mode over concrete programs (rfl-reduction); bare
And-projections need type ascriptions; 12-space inner nil-arms contain the 8-space
pattern as a substring; `simp [X]` may close goals leaving `omega` stranded — use
`simp only`. Full list in the project memory file.

**Also queued:** ~~iteBranchSearch census~~ **DONE 2026-07-08** (`censusITE`, T49 —
and the `closedP z` side-condition DISSOLVED: the `.opp`/`.bot z` substs reduce on the
nose; machine + all five packages extended). REMAINING ite gap: the ONE-discharge
partial application `(u1 :: nil)` stays `none` — no ProvT constructor concludes the
ite-me Löb premise `impl (box k (ψ.subst me opnt)) (plays me opnt c0)` for ite-shaped
`me` (unlike axKf→axK there is no repackage target). So `dbFree` still guards
GoodD/fundamentalW. Options when it matters: (i) add a partial-ite ProvT constructor
(premise = the plays fact as a field — sound, mirrors the rule; touches every
`cases t`), or (ii) a saturation PRE-PASS replacing `app(app(struct(iteBranch),u1),u2)`
patterns by their census before excision (real zoo proofs use the rule saturated via
mp). Strict-k budget
conservation of excise (per-arm arithmetic, `crossWtLt`-style); `decFullT` tree
synthesis (mirror T31's enumerator with `Option ProvT` returns).
