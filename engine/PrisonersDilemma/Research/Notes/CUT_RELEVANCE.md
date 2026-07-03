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

## 5. Milestones

- **C0 ✅ (2026-07-03)**: this analysis; T48 foundations (literal bounds at own judgments).
- **C1**: Derivation-layer antecedent determinacy (`Derivation (.impl B C)` ⇒ B
  conclusion-determined — incl. mp/hypSyll recursion).
- **C2**: impl-inversion dichotomy for the chain-free fragment (no implTrans/impS2/app-produced
  impls) — the census above, formalized.
- **C3**: the full Lemma A (chains + app-nesting; the positive-position invariant).
- **C4**: Lemma B rewrites + budget arithmetic (or the budget-inflated fallback).
- **C5**: assembly — `CutRelevance` (possibly budget-inflated) for modest roots; plug into
  T47 ⇒ `Provable` decidable on the zoo universe; `proofSearch := D`.
