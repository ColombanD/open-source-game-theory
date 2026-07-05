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
- **C3b**: the master induction per §5a′ (the FINAL spec — supersedes §5a's sketch).
  Foundations (maxSLit measure, subst lemma, split lemma) in T48 §7 ✅ (2026-07-03).
  Remaining: `PPair` + the master `Provable.rec` (~26 arms, 3×3 composition subcases).
- **C4**: Lemma B rewrites + budget arithmetic (or the budget-inflated fallback).
- **C5**: assembly — `CutRelevance` (possibly budget-inflated) for modest roots; plug into
  T47 ⇒ `Provable` decidable on the zoo universe; `proofSearch := D`.
