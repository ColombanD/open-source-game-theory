# M4 design brief — PBLT in PA-`S` (written 2026-09-11, after the three reader reports)

*Companion to `READ_engine_pblt_critch.md` (engine `BoundedGL`/`bloeb`/`pblt`, the Löbian cells,
Critch 2022 verbatim), `READ_foundation_calculus.md` (Foundation's calculus, coded derivations,
`ProvabilityAbstraction`, fixed points, Σ₁-completeness) and `READ_arith_for_m4.md` (what the
package has). Critch 2019 (JSL, "A parametric, resource-bounded generalization of Löb's theorem")
§4–5 was extracted separately (`pypdf` over the arXiv PDF) and is quoted below where used.*

**Goal restated (Colomban, 2026-09-11).** A working `S'` = PA (Foundation) + the length-bounded
`□_k`, in which the PARAMETRIC bounded Löb theorem (PBLT) is a theorem, the red cell holds (done,
T1), and the zoo programs run. The bridge to the rule-based `Pf` (T2) is DEFERRED; nothing in this
brief extends it. FACT / ANALYSIS marking as in the M3 brief.

## 1. The theorem we are after, in Critch's own form

FACT (Critch 2019, §5, Theorem 3 "Parametric Bounded Löb", verbatim modulo notation): for a formula
`p(k)` with one free variable and a computable `f` with `f(k) ≻ E(O(lg k))`,
`⊢ ∀k (□_{f(k)} p(k) → p(k))` implies `∃k̂, ⊢ ∀k > k̂, p(k)`. The proof (pp. 10–11) uses exactly:

* **Property 1 (Implication Distribution)** — internal bounded D2:
  `⊢ ∀a b, □_a(φ → ψ) → □_b φ → □_{a+b+c} ψ` (`c` constant with abbreviations; for us
  `c·(|φ|+|ψ|)+c₀`, `Cut.lean` at the meta level).
* **Property 2 (Quantifier Distribution)** — instantiation with length:
  `⊢ □_N(∀k φ(k)) ⇒ ⊢ ∀k □_{C+2N+lg k} φ(k)`.
* **Property 3 (Bounded Necessitation)** `⊢_k φ ⇒ ⊢_{E k} □_k φ` — BUT in the proof it is applied
  only to two proofs of CONSTANT length (the fixed-point equivalence, the final `∀k>k₂ ψ(k)`), and
  only in the form `⊢_n φ ⇒ ⊢ □_n φ` (unbounded on the right). That is ordinary Σ₁-completeness of
  a true Δ₁ sentence — FREE in Foundation (`sigma_one_completeness`, `models_iff_provable_of_Delta1`).
* **Property 4 (Bounded Inner Necessitation)** — internal bounded D3:
  `⊢ ∀k ∀a, □_a ψ(k) → □_{E a} □_a ψ(k)`.
* The **parametric diagonal lemma** (`⊢ ∀k, ψ(k) ↔ G(⌜ψ⌝, k)`) — FACT: Foundation has it,
  `parameterizedFixedpoint`/`parameterized_diagonal₁` (`FixedPoint.lean:204-231`), proved via
  `complete` (no proof object — fine, its length is a constant we never need).
* `g(k)` with `lg k ≺ g(k)` and `E(g(k)) ≺ h(k) ≺ f(k)`; the fixed point is `ψ(k) ↔ (□_{g(k)} ψ(k) → p(k))`.

ANALYSIS. The whole argument is ONE uniform PA proof with `k` a variable, followed by ONE meta
instantiation at `k̄` of cost `O(lg k)`. Therefore:

1. **No proof-producing bounded D1 is needed.** The engine's `bloeb` (14 pointwise steps with
   `boxIntro` twice) is NOT the shape to reproduce; Critch's uniform shape is. This removes what
   the handover listed as the largest M4 item.
2. **The single hard item is Property 4** with a SUBEXPONENTIAL `E`. Constraint: `g ≥ lg k + c`
   (Property 2 on the fixed point) and `E(g(k)) ≺ f(k) = k` force `E(a) = 2^{o(a)}`; polynomial is
   the target. Under Foundation's Cantor-free but square-growing pairing a derivation of length `a`
   has a code of ≈ `2^a` bits, so the verification proof `E(ρ)` must NEVER write a code as a
   numeral: it must follow the tree of `ρ` with eigenvariables and cuts against constant-size
   lemmas. FACT: Foundation's internal Σ₁-completeness (`bold_sigma_one_complete`, `D3.lean:76`)
   constructs internal derivation codes with the internal cut `⨀` but tracks no length; naive
   Σ₁-completeness on the Δ₀ matrix of `Proof` is exponential in code size and useless here.
3. **Everything else is V-generic Lean, not PA-internal sentences.** The uniform argument can be
   run as reasoning "in every model `V ⊧ TAct`", using V-generic lemmas about codes (bounded cut
   with `dlen` accounting, instantiation with `dlen` accounting, inner necessitation), plus the
   diagonal lemma transferred to `V` by soundness; `complete` then yields the uniform TAct theorem
   (`Det.lean`'s pattern, `READ_arith_for_m4.md` §3). Only its EXISTENCE with some length `N` is
   used, by the meta instantiation (`Cut.lean`-style bridges).

## 2. The guard mismatch, and the coding decision

FACT. Dupoc's runtime guard is `guardCode ⌜GtmplA 0⌝ (Dupoc k) (Dupoc k) = subst (descVec …) ⌜GtmplA 0⌝`
with `descVec` built (before 2026-09-12) from `bnum (dnum (Dupoc k))` — the binary numeral of the WHOLE program code
(`Guard.lean`, now `progT (dnum (Dupoc k))`). PBLT's fixed point and Property 1 produce boxes of `k`-INSTANCES of
formulas, `subst (numeral k) ⌜p⌝`. The numeral of `⟪6, k, cP⟫ + 1` is not the numeral of `k`
inside any fixed term, because Foundation's `pair` is `if a < b then b*b + a else a*a + a + b`
(`IOpen/Basic.lean:511`) — no ℒₒᵣ term denotes it. So the guard is the `k`-instance of NO formula,
and `□_k` is not invariant under provable equivalence: the hypothesis of PBLT cannot be stated
for Dupoc under the present coding.

ANALYSIS — options considered.
(a) STRUCTURAL descriptions as FORMULAS (`∃x₁ x₂, Desc_me(x₁) ∧ Desc_opp(x₂) ∧ g[x₁,x₂]`): no
    language change, but the template interface changes from 6-variable term substitution to
    formula-code assembly; every bridge module (`Code`…`FitBox`, ~200 KB) re-shapes.
(b) Keep numeral descriptions, index the Löb family by the CODE `y = dnum (Dupoc k)`: the guard is
    then `subst (bnum y ∷ 0) ⌜q⌝` exactly — but the final instantiation must discharge
    `IsDupoc (bnum y₀) ∧ budget(bnum y₀) > k̂` by a SHORT PA proof about a numeral (pair-decoding
    and, worse, `y₀ ≤ swapcode y₀` — evaluating a Σ₁ fixpoint on a numeral), which is the very
    cost we are trying to avoid.
(c) A `pair` function symbol in `LAct` with a defining axiom in `TAct`: faithful (no term
    duplication) but touches the M1/M2 foundation layer and kills the `inst : LAct →ᵥ ℒₒᵣ` hom
    (`Inst`/`Det`, bridge-deferred but in the census).
(d) **CHOSEN: polynomial pairing for PROGRAM CODES**, `ppair x y := (x+y)·(x+y) + y` (injective,
    Δ₀-decodable, monotone, TERM-expressible), `pSearch k g p q := ppair 6 (ppair k (ppair g (ppair p q))) + 1`,
    and the description of a program is the TERM `progT x` built from `ppair` and the binary
    numerals of its leaves. Then `progT (Dupoc k) = T_D[bnum k]` for a FIXED term `T_D` with one
    variable, so the guard is literally `subst (bnum k ∷ 0) ⌜q_D⌝` for a fixed formula `q_D` —
    Critch's "source with `k` written in binary". Contained in `Prog.lean` (+ the few files that
    look into the pairing: `Neg`, `FitBox`, `Fit`), no language change, `Inst`/`Det` survive,
    `dnum/dU/dW`/τ untouched. Cost: term duplication (`ppair` copies `x` twice, `y` three times —
    a constant factor per nesting level; the zoo has constant depth). Guard length stays
    `O(size k)`. Note `FitBox`'s negative finding survives (the template CODE is still a numeral).

## 3. Objects and obligations (the M4 ladder)

Notation: `V` ranges over models of `TAct` (equivalently `V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁` plus the two action
axioms); `L a x := LenProvableV TAct a x` on codes.

| # | object / lemma | kind | status |
|---|---|---|---|
| U0 | `ppair`, program codes on it, `progT` (Σ₁ term-code function), `descVec` via `progT ∘ dnum`, `guard_fits` re-proved, code equation `guardCode ⌜GtmplA 0⌝ (Dupoc k) (Dupoc k) = subst (bnum k ∷ 0) ⌜q_D⌝` (existentially packaged `q_D`) | refactor | **DONE 2026-09-12** (`ProgT`, `Instance`, `InstanceV`): `exists_dupoc_instance` (meta), `exists_dupoc_instance_code` (ℕ) and `exists_dupoc_instance_code_V` (every `V`, every `k : V` — the guard code is `instB cq k`) |
| U1 | `bewB a n k := ∃ g, g = subst (bnum k ∷ 0) n ∧ L a g` — the parametric box on codes; its Δ₁ graph | def | — |
| U2 | Property 1 in `V`: `L a (imp φ ψ) → L b φ → L (a + b + c₁(‖φ‖+‖ψ‖) + c₀) ψ` (`CutV.lean`) | V-generic lemma | agent launched 2026-09-11 |
| U3 | Property 2 in `V`: from a code of `∀k χ(k)` with `dlen ≤ N`, a code of `subst (bnum k ∷ 0) ⌜χ⌝` with `dlen ≤ N + c·len(bnum k) + c'` (internal `∀`-elimination = one cut) | V-generic lemma | — |
| U4 | Property 3′: `LenProvable n σ → TAct ⊢ □_n σ` (Σ₁-completeness of a true Δ₁ sentence; the `lenProvableV_nat` reading) | free | check name |
| U5 | Property 4 in `V`: `L a x → L (E a) ⌜lenProvableV a x⌝` with `E` polynomial | V-generic lemma | **THE CRUX**; state first as a named hypothesis `BoundedInnerNec E` |
| U6 | parametric diagonal lemma for the `bnum`-instance operator (Foundation's `parameterized_diagonal₁` uses unary `numeral`; either reuse it — the numeral of `k` inside the fixed point may be unary, its length is `O(k)`… NO: that breaks `g ≥ lg k`; so re-do the construction with `bnum`, or prove `TAct ⊢ ∀k, ψ(k) ↔ …` where instances are `bnum`-instances) | theorem | design detail, decide at implementation |
| U7 | Dupoc transparency: `∀ V, ∀ k, L k (guard k) → EvalGraph 2 (Dupoc k) (Dupoc k) (Dupoc k) 0` and the truth equation in `V` (`READ_arith_for_m4.md` §4(iv) lists the ℕ-only lemmas needing `V` twins) | V-generic | — |
| U8 | `pblt_uniform`: assembling U1–U7 in `V`, then `complete`: `TAct ⊢ ∀k > k̂, q_D(k)` — and its meta instantiation: `∀ k > k̂, LenProvable (N + c·size k) (guard k)` | theorem, conditional on U5 | — |
| U9 | `dupoc_self_coop : ∃ k̂, ∀ k > k̂, EvalGraph 2 (Dupoc k) (Dupoc k) (Dupoc k) 0` (and the `(C, C)` outcome), conditional on U5 | theorem | — |
| U10 | discharge U5 (bounded inner necessitation with polynomial `E`) | research | months; Zulip question to Foundation |

Ordering: U0 ∥ U2 now; then U1/U3/U6/U7; then U8/U9 with U5 as a hypothesis (the honest,
`BoundedGL`-style form); then U10.

## 4. What the paper may say at each stage

* After U9: "PBLT holds in PA-`S` relative to ONE named condition, bounded inner necessitation with
  a subexponential expansion function — Critch's assumption (d) in its exact place; every other
  ingredient (bounded D2, instantiation, the parametric diagonal lemma, Σ₁-completeness) is a
  theorem, and under that condition Dupoc cooperates with itself in PA for all large `k`."
* After U10: the condition is a theorem for Foundation's calculus with an explicit polynomial `E`.
* Never: a numeric threshold `k̂` (Cantor-coded constants are astronomical; "for all large `k`").

## 5. Dangers specific to M4

1. U5's `E` may come out exponential if any step writes a code as a numeral; the construction
   must be checked for that BEFORE it is formalized (a paper-and-pencil cost table per node type).
2. `ppair` duplication: descriptions of deep programs grow as `c^depth`; fine for the zoo, and
   `T2-NEG`-style `bot^m` witnesses are bridge material.
3. Foundation's `numeral` is unary everywhere a Foundation lemma introduces one
   (`substNumeral`, `parameterizedFixedpoint`); every budget that enters a sentence must go
   through `bnum` (U6).
4. Properness inside `V` (`d < fbound k` from `dlen d ≤ k`) is proved at ℕ only (`Proper.lean`);
   U2/U3/U5 need it V-generically or must carry it as a hypothesis.
