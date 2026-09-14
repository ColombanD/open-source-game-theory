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
| U1 | `bewB a n k := ∃ g, g = subst (bnum k ∷ 0) n ∧ L a g` — the parametric box on codes; its Δ₁ graph | def | **DONE 2026-09-11** (`InstV.lean`, 47fa241): `instB`, `bewB a n k := LenDerivable TAct a (instB n k)` (Σ₁, NO `fbound` — `LenDerivable` is the box of the Löb argument), `bewBDef`, `quote_instB`, `formulaLen_instB_le` |
| U2 | Property 1 in `V`: `L a (imp φ ψ) → L b φ → L (a + b + c₁(‖φ‖+‖ψ‖) + c₀) ψ` (`CutV.lean`) | V-generic lemma | **DONE 2026-09-11** (`CutV.lean`, f4a1a0b): `lenDerivable_cut_V` unconditional (`5|φ|+10|ψ|+9`); `lenProvableV_cut_V` under `ProperV V T` — DISCHARGED for every model by `ProperV.lean` (5d9fc0a): `properV_TAct`, `lenDerivable_iff_lenProvableV`; `pa_proves_cutSentence`/`tact_proves_cutSentence` |
| U3 | Property 2 in `V`: from a code of `∀k χ(k)` with `dlen ≤ N`, a code of `subst (bnum k ∷ 0) ⌜χ⌝` with `dlen ≤ N + c·len(bnum k) + c'` (internal `∀`-elimination = one cut) | V-generic lemma | **DONE 2026-09-11** (`InstV.lean`): `lenDerivable_instB_V` (`+ 5|χ[t]| + 3|χ| + |t| + 7`), `bewB_of_all`, meta `lenProvable_inst_size` (`+ 6·size k + 8`) |
| U4 | Property 3′: `LenProvable n σ → TAct ⊢ □_n σ` (Σ₁-completeness of a true Δ₁ sentence; the `lenProvableV_nat` reading) | free | check name |
| U5 | Property 4 in `V`: `L a x → L (E a) ⌜lenProvableV a x⌝` with `E` polynomial | V-generic lemma | **RESTATED + used** (`Prep.lean`): `BoundedInnerNec d`, per-`χ` constant (the uniform-in-`flen` form was unsatisfiable) |
| U6 | parametric diagonal lemma for the `bnum`-instance operator (Foundation's `parameterized_diagonal₁` uses unary `numeral`; either reuse it — the numeral of `k` inside the fixed point may be unary, its length is `O(k)`… NO: that breaks `g ≥ lg k`; so re-do the construction with `bnum`, or prove `TAct ⊢ ∀k, ψ(k) ↔ …` where instances are `bnum`-instances) | theorem | **DONE 2026-09-12** (`Diag.lean`, 669704c): `tact_parametric_diagonal (θ : Semisentence LAct 2) : ∃ ψ, TAct ⊢ ∀¹ (ψ 🡘 θ ⇜ ![lMap emb ⌜ψ⌝, #0])` (Foundation's construction re-done over `LAct`: `substNumeralParamsA`, `tactFixedpoint`), instances at `bnumT k` (`tact_parametric_diagonal_inst`, model and `Provable`-code forms); reusable `tact_complete` (completeness for `TAct` on REAL-equality models) + `𝗘𝗤 LAct ⪯ TAct` |
| U7 | Dupoc transparency: `∀ V, ∀ k, L k (guard k) → EvalGraph 2 (Dupoc k) (Dupoc k) (Dupoc k) 0` and the truth equation in `V` (`READ_arith_for_m4.md` §4(iv) lists the ℕ-only lemmas needing `V` twins) | V-generic | **DONE 2026-09-12** (`Transparency.lean`, 54aee07): `eval_qDupoc_iff_V` (truth equation in `stdActV V`), `dupoc_search_V`, `dupoc_search_instB_V` (unconditional), `dupoc_loeb_premise_V` (under `ProperV`), ℕ forms unconditional, `pa_proves_dupocPremise`/`tact_proves_dupocPremise`. FINDING: truth equations hold only in the STANDARD readings `c_C ↦ 0, c_D ↦ 1` (and the swap) — `TAct` with only `c_C ≠ c_D` admits models where the guard is FALSE ⇒ `TAct ⊬ guard(k)` for all `k`: a VACUITY, fixed by the action axiom (U0b, agent launched) |
| U8 | `pblt_uniform`: assembling U1–U7 in `V`, then `complete`: `TAct ⊢ ∀k > k̂, q_D(k)` — and its meta instantiation: `∀ k > k̂, LenProvable (N + c·size k) (guard k)` | theorem, conditional on U5 | **DONE 2026-09-12** (`Assembly/Uniform.lean`, 91df6b9): `chain_V`, `chainBound_poly`, `psi_true_V`, `pblt_uniform` |
| U9 | `dupoc_self_coop : ∃ k̂, ∀ k > k̂, EvalGraph 2 (Dupoc k) (Dupoc k) (Dupoc k) 0` (and the `(C, C)` outcome), conditional on U5 | theorem | **DONE 2026-09-12** (`Assembly/Cell.lean`, 4c8ecc9): `dupoc_self_coop`, `dupoc_finds_guard` (conditional on `BoundedInnerNec d`) |
| U10 | discharge U5 (bounded inner necessitation with polynomial `E`) | research | designed (`DESIGN_inner_necessitation.md`): 2.5–4 months, E = O(a³); risk (1) checked OK — USER DECISION |

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

## 6. The assembly (U5 + U8 + U9), stated exactly (2026-09-12, after U0–U3, U6 landed)

Notation: `L a x := LenDerivable TAct a x` (Σ₁ box on codes, `CutV`); `instB n k`, `bewB`
(`InstV`); `qDupoc`, `DupocV k`, `guardCode_DupocV_eq_instB` (`InstanceV`); `tact_parametric_diagonal`,
`tact_complete` (`Diag`); `ProperV` (`CutV`/`ProperV`); transparency and the truth equation (U7).
Models `V`: `LAct`-structures with REAL equality whose reduct is a model of PA, satisfying the two
action axioms — exactly the class `tact_complete` quantifies over.

**The budget function.** `g k := ‖k‖ * ‖k‖` (`‖·‖` = bit length, Σ₁-definable in Foundation),
so that `C + c·‖k‖ ≤ g k` for all large `k` whatever the constants `C, c` (this breaks the
circularity between the fixed point's constants and the threshold: Critch's `lg k ≺ g(k)`).
`f k := k` (Dupoc's own budget). `h` is not needed separately: the master inequality is
`g k + N₁ + E (g k) + c·(|ψ| + |p| + ‖k‖) ≤ k`, true for all large `k` when `E` is polynomial.

**U5 — the ONE named hypothesis (bounded inner necessitation, family form).** For a one-variable
`χ : Semisentence LAct 1` let `Box_g χ : Semisentence LAct 1 := “∃ a, gGraph a #0 ∧ bewBDef a ⌜χ⌝ #0”`
(embedded along `emb`; `⌜χ⌝` a numeral constant, `#0` the free `k`). Then
```
structure BoundedInnerNec (E : ℕ → ℕ) : Prop where
  poly : ∃ d c, ∀ a, E a ≤ a ^ d + c
  nec  : ∀ (V) [real-eq model of TAct] (χ : Semisentence LAct 1) (k : V),
           L (g k) (instB ⌜χ⌝ k) → L (E (g k) + c₁ * (flen χ + ‖k‖) + c₀) (instB ⌜Box_g χ⌝ k)
```
(`E` applied inside `V` through its Σ₁ graph, or state `nec` with an explicit polynomial). This is
Critch's Property 4 = assumption (d); everything below is a theorem GIVEN it (U10 discharges it).

**U8 — the uniform argument, in `V`.** Fix `p := qDupoc`, `θ (n, k) := Box_g-with-code-n(k) 🡒 p(k)`
(a `Semisentence LAct 2`: `n` the code variable, `k` the budget variable), `ψ := tactFixedpoint θ`,
so `TAct ⊢ ∀¹ (ψ 🡘 θ ⇜ ![⌜ψ⌝, #0])`. Take META proofs of the two directions
`∀¹ (ψ 🡒 θ[⌜ψ⌝])` and `∀¹ (θ[⌜ψ⌝] 🡒 ψ)` with lengths `N₁, N₂ : ℕ` (constants; from `TAct ⊢` via
`Theory.Proof` + `mlen`), and transfer `L N₁ ⌜∀¹ (ψ 🡒 …)⌝` into every `V` by Σ₁-upward absoluteness
(`lenDerivableDef` is Σ₁). In `V`, for `k` with the master inequality:
1. (U3) `L (N₁ + …) (instB ⌜ψ 🡒 θ[⌜ψ⌝]⌝ k)`, i.e. of `imp (instB ⌜ψ⌝ k) (imp (instB ⌜Box_g ψ⌝ k) (instB ⌜p⌝ k))` (`instB` distributes over `🡒` — a code lemma).
2. Assume `A : L (g k) (instB ⌜ψ⌝ k)` (= `bewB (g k) ⌜ψ⌝ k`).
3. (U2 cut of 1 with 2) `L (…) (imp (instB ⌜Box_g ψ⌝ k) (instB ⌜p⌝ k))`.
4. (U5 on 2) `L (E (g k) + …) (instB ⌜Box_g ψ⌝ k)`.
5. (U2 cut of 3 with 4) `L (…) (instB ⌜p⌝ k)` = `L (…) (guardCode ⌜GtmplA 0⌝ (DupocV k) (DupocV k))`.
6. (master inequality + `lenDerivable_mono_V`) `L k (guard)`; (`properV_TAct`) `LenProvableV TAct k (guard)`;
   (U7 `dupoc_search_V`) `EvalGraph 2 (DupocV k) (DupocV k) (DupocV k) 0`; (U7 truth equation) `V ⊧ p[k]`.
7. Discharging 2: `V ⊧ (Box_g ψ)[k] ↔ L (g k) (instB ⌜ψ⌝ k)` (semantics of `bewBDef`/`gGraph`), so `V ⊧ θ[⌜ψ⌝][k]`, and by the fixed point (soundness of `TAct ⊢ ∀¹ (θ[⌜ψ⌝] 🡒 ψ)` in `V`) `V ⊧ ψ[k]`.
8. Hence, with `k̂ : ℕ` the threshold of the master inequality: every real-eq model of `TAct` satisfies `∀¹ (numeral k̂ ≤ #0 🡒 ψ)`; by `tact_complete`, `TAct ⊢ ∀¹ (numeral k̂ ≤ #0 🡒 ψ)`; let `N₃` be the length of one such proof.
   `pblt_uniform (hE : BoundedInnerNec E) : ∃ k̂ N₃, LenProvable fbound N₃ TAct ⌜∀¹ (numeral k̂ ≤ #0 🡒 ψ)⌝ ∧ (the chain 1–7 at every V, k ≥ k̂)`.

**U9 — the cell, at ℕ.** For `k ≥ k̂` (and a second threshold `k̂'` below):
1. (U3 meta, `lenProvable_inst_size`) `LenProvable (N₃ + c·‖k‖ + C) TAct ⌜numeral k̂ ≤ bnumT k 🡒 ψ ⇜ ![bnumT k]⌝`.
2. A SHORT proof of the antecedent: `LenProvable (c'·‖k‖ + C') TAct ⌜numeral k̂ ≤ bnumT k⌝` for `k ≥ k̂` — by bit recursion on `bnumT` (`x ≤ y → x ≤ 2y`, `x ≤ y → x ≤ 2y + 1` as PA lemmas cut in once per bit; base cases `k ∈ [k̂, 2k̂+1]` finitely many constant proofs by Σ₁-completeness, constants existential). NEW small library `NumeralFacts.lean`.
3. (`Cut.lean` meta cut) `LenProvable (N₄ k) TAct ⌜ψ ⇜ ![bnumT k]⌝` with `N₄ k = C'' + c''·‖k‖ ≤ g k` for `k ≥ k̂'`; by `quote_instB` + `properV_nat_TAct`: `L (g k) (instB ⌜ψ⌝ k)` at `V = ℕ` = step 2 of U8.
4. Run U8's chain at `V = ℕ`: `LenProvableV TAct k (guard)` and `EvalGraph 2 (Dupoc k) (Dupoc k) (Dupoc k) 0`.
   `dupoc_self_coop (hE : BoundedInnerNec E) : ∃ k₀, ∀ k ≥ k₀, EvalGraph 2 (Dupoc k) (Dupoc k) (Dupoc k) 0` — Critch's Theorem 3.7 in PA-`S`, conditional on (d).

Traps to expect: never `simp` a goal containing `⌜ψ⌝` (Diag's kernel-numeral trap); state every
length in `‖k‖`, `flen ψ`, `flen p` separately (InstV's trap); the fixed point's numeral `⌜ψ⌝` is
Foundation's UNARY numeral — an astronomical CONSTANT, harmless; `k̂`, `N₁…N₄` are all existential.

## 7. Correction to §6 (2026-09-12, after U7): the model class and the action axiom

`TAct = PA ∪ {c_C ≠ c_D, c_D ≠ c_C}` admits models reading the constants as ANY distinct pair; there
`relabel c_C c_D (dnum (Dupoc k))` is not a program (the relabelled template has a non-existent
symbol code), its search fails, and Dupoc's guard sentence is FALSE. So `TAct ⊬ guard(k)` for every
`k` and Dupoc never cooperates — the abstract-constant τ design (roadmap §2.4) was vacuous for the
Löbian cells (the M3 record's boundary 2 called the generic `TAct ⊢ trAt …` "needed by nothing
downstream"; it is needed by exactly these cells). FIX (U0b): add the τ-symmetric axiom
`axAct : (c_C = 0 ∧ c_D = 1) ∨ (c_C = 1 ∧ c_D = 0)` (and its swap image). Then every real-equality
model of `TAct` is `stdActV V` or its swap twin, `tact_complete` quantifies over exactly those two
readings, and §6's chain must be run in BOTH: in the swapped reading `qDupoc(k)` says "Cupod k plays
D vs Cupod k", obtained from `EvalGraph 2 (DupocV k) … 0` by the τ-equivariance of `EvalGraph`
(`swapcode`, `swapAct`) — a V-generic lemma to add to U8. Red cell, τ-closure and every `TAct ⊢`
result survive (a stronger theory); `no_budget_keeping_transfer` is a length argument.

**§7 addendum (after U0b landed, 7908336): the family is the CONJUNCTION.** `tact_complete'`
quantifies over `stdActS M` and `swapActS M`. In the swapped reading `qDupoc(k)` means "Cupod k plays
D vs Cupod k", and turning `EvalGraph 2 (DupocV k) … 0` into that needs τ-equivariance of `EvalGraph`
inside `V`, i.e. τ-closure of `LenProvableV` INTERNALLY — not available (`Symmetry.lean` is meta).
Critch's own move (2019 p. 21, PBLT on the conjunction) avoids it: take
`p := qDupoc ⋏ qCupod` with `qCupod := lMap swap qDupoc` (the one-variable formula whose `k`-instance
is CUPOD's guard: `guardCode ⌜GtmplA 1⌝ (CupodV k) (CupodV k) = instB ⌜qCupod⌝ k`, from
`swapcode_DupocV` + the template swap equations). Then from `L a (instB ⌜p⌝ k)` two cheap
∧-elimination cuts give `L (a + …) (instB ⌜qDupoc⌝ k)` AND `L (a + …) (instB ⌜qCupod⌝ k)`; each
searcher finds its own guard: `EvalGraph 2 (DupocV k) … 0` and `EvalGraph 2 (CupodV k) … 1`
(`search_iff` for `pSearch k _ (pConst 1) (pConst 0)`); and `p(k)` is TRUE in BOTH readings: in
`stdActS`, `qDupoc ↔ EvalGraph … Dupoc … 0` (U7) and `qCupod ↔ EvalGraph … Cupod … 1` (mirror);
in `swapActS`, `Eval (swapActS) φ = Eval (stdActS) (lMap swap φ)` swaps the two roles. So the ONLY new
truth equation is `eval_qCupod_iff_V` in `stdActS`, and U8's step 6 produces both `EvalGraph` facts.
The conclusion `dupoc_self_coop` is unchanged (and `cupod_self_defect` comes for free).

## 8. U10 design (2026-09-12, `DESIGN_inner_necessitation.md`) and a correction to §6

**Correction.** `BoundedInnerNec d c c₁ c₀` as first stated (§6, `Prep.lean` ec5a8b6) is
UNSATISFIABLE: the target `instB ⌜Box_g χ⌝ k` contains the UNARY numeral `⌜χ⌝`, so every proof of
it has `dlen ≥ encode χ` (exponential in `flen χ`) while the bound allowed `c₁ · flen χ` — a
theorem conditional on it would be vacuous. RESTATED (assembly agent instructed): the constant may
depend on `χ`: `∀ χ, ∃ C, ∀ V k, L (g k) (instB ⌜χ⌝ k) → ∃ e ≤ C·((g k)^d + 1), L e (instB ⌜Box_g χ⌝ k)`.
The argument uses one `χ` (= `psi`), so nothing is lost. General lesson: any sentence naming a
formula by a numeral costs at least that code's magnitude — bound constants per family, never
uniformly in `flen`.

**The construction (ANALYSIS, report §3).** `verifyCode ρ` follows `ρ`'s tree; every code
(sequent, formula, term, sub-derivation, length) enters the proof as an EIGENVARIABLE obtained by
∃-elimination from a constant-size universal lemma (pairing/insert/subst totality, the ten per-tag
intro clauses of the `derivation` fixpoint, the `DlenGraph` clauses — a finite library of ~40
`TAct`-sentences with existential lengths, each proved by `complete`); the fixpoint is never
unfolded; membership/subset/`IsFormulaSet` facts are constant consequences of the `insert`
construction; lengths flow as binary numerals. Foundation's own internal Σ₁-completeness is NOT
reusable (unary witnesses, bounded-∀ case analysis: `E ≥ 2^{2^a}`). Expected `E(a) = O(a³)`
(two extra factors: live-fact contexts per node, and UNARY free-variable indices in `Length.lean`
under `setShift`; `O(a²)` with binary indices) — polynomial suffices (`‖k‖⁹ ≺ k`); take `d = 3`.

**Risks.** (1) `axm` leaves: a PA proof that an eigenvariable-described formula is an induction
instance costs `O(|p|)` only if Foundation's `𝗣𝗔.Δ₁` recognizer (`Definability.lean:1070`) goes
through the code-level `subst`/`qqAll` graphs — CHECK FIRST. (2) `|derivation TAct|` as a
multiplicative constant; `simp` on quoted lemma sentences overflows the kernel numeral.

**Effort (report §5).** Lemma library 1000–1500 lines (5–8 days); the context-carrying recursion by
`Derivation.induction1` (existential form, `cutCode`-style fragment codes) 6000–7000 lines
(2.5–4 months); assembly ~400 lines. Cheap independent win: charge variable indices in BINARY in
`Length.lean` (one factor of `a` off `E`; touches the M1 constants). Alternatives (§6 of the
report): an abbreviation calculus (linear `E`, but re-does the M1–M3 length layers); accepting an
exponential `E` (kills `f(k) = k` — only a polynomial-budget agent language survives).

**Risk (1) checked (2026-09-12):** Foundation's `𝗣𝗔.Δ₁` instance is `Theory.Δ₁.add PeanoMinus.delta1
InductionScheme.delta1_univ` (`Incompleteness/Definability.lean:1070`) and the induction-instance
recognizer `indBodyVal` is "a chain of the `subst`/`imp`/`qqAll` graphs" (`:723-727`:
`substsGraph ℒₒᵣ … indSubstConst0/1 …`, then `imp`, then `qqAll`) — i.e. written through the code-level
graphs, so an `axm` leaf whose formula is an eigenvariable-described induction instance costs `O(|p|)`
lemma instantiations, as the eigenvariable construction requires. `PeanoMinus` is finite (a fixed
disjunction of numerals — constant). Risk (1) is not a blocker.

## 9. U10 execution (started 2026-09-12, branch `colomban-arith-u10` off `colomban-arith-m3` @ 15b015a)

Colomban's decision: push for the one obligation. Plan = `DESIGN_inner_necessitation.md` §5, cut into
agent-sized tasks under `arith/ArithS/Necessitation/`:
* `Primitives.lean` — the two moves of §3.1 as derivation-code constructors with `dlen` bounds:
  `useLemmaCode` (cut a stored `∀x̄ B` in at witnesses `ē`: `wk` + `m` `exsIntro`s + `cut`) and
  `elimExistsCode` (cut on `∃x P` against `allIntro` with the fresh `&0`); `wkDropCode`.
* `Lib/Basic.lean` — `Lib σ := ∃ N, ∀ V, LenDerivable TAct N ⌜lMap emb σ⌝`, `Lib.of_pa`;
  `Lib/Sets.lean`, `Lib/Formulas.lean`, `Lib/Lengths.lean` — the table rows totality/sets/formulas/lengths.
* NEXT: `Lib/Nodes.lean` — the ten `Intro_tag` + ten `Dlen_tag` sentences (with `(derivation TAct).sigma`
  and `dlenGraphDef`) and the `axm` recognizer items (§3.6); then `describeFormula` (the bottom-up
  syntax walk, a `UformulaRec`-style Σ₁ construction), `transportFacts`, the ten per-tag fragments
  (§3.3), the existential recursion by `Derivation.induction1` (§5(b), recommended over a
  `verifyCode` function), and the top (§4.3) closing `BoundedInnerNec 3`.
Conventions: two concurrent Lean agents, short tool calls, `wip` commits per green file, never
`simp` on quoted sentences, all constants existential; `-m3` stays frozen at the milestone.

**§9 status — Primitives DONE (204c012, census 179, general `L`/`T`, general arity `m`).**
`useLemmaCode Γ es B dΛ d` (cut a stored `∀^m B` in at the witness list `es`; `exsChainCode` =
`m` `exsIntro`s; `dlen ≤ dlen dΛ + dlen d + (m+3)|Γ| + (m+1)²(|B|·E + m) + |B| + mE + 2m + 3` with
`E` a bound on the witness term lengths — the `(m+1)²` is real: Foundation's `exsIntro` keeps the
principal formula, so the chain sequents accumulate), `elimExistsCode Γ P D d` (`dlen ≤ dlen D +
dlen d + 5|Γ| + 6|P| + 8`; the factor 2 on `setShift` is the unary free-variable charge),
`wkDropCode`; infrastructure `allsIter/exsIter`, `instOuter` (outermost-first instantiation) with
the LINEAR bound `|instOuter es B| ≤ |B|·E`. PROCESS TRAP: `pgrep -f 'lake build'` matches the
agent's own polling shell — use `pgrep -f 'bin/lake build'`. Mathlib: `add_le_add_left/right` have
swapped sides in this toolchain — use `add_le_add`/`gcongr`. IN FLIGHT: `Lib/{Basic,Sets,Formulas,
Lengths}` (rows A), `Lib/Nodes` (Intro/Dlen/axm).

**§9 status — Library rows A DONE (f6536fc): `Lib/Basic` (`Lib σ`, `Lib.of_pa`, `quote_alls`,
`Lib.univ_code`), `Lib/Sets` 26 rows, `Lib/Formulas` 84 rows (totality 18, formation 18,
commutation 32, shape inversion 16), `Lib/Lengths` 35 rows; ROW CONVENTION: body in index order,
Δ₁ hypotheses `.pi`, conclusions `.sigma`, bridges for both polarities. TRAP: a closed NUMERAL
inside a Δ₁ fixpoint blueprint (`!(isFormulaSet LAct).sigma 0`) explodes elaboration to 26 GB —
state rows over variables (`IsFormulaSet ∅` is the pair `isFormulaSetOfNoMem` + `notMemEmpty`);
a `timeout` upstream of `grep` exits 0 — check the exit code of `lake env lean` itself.
Library rows B DONE (d95ba66): `Lib/Nodes` — ten `Intro_tag`, ten node-code totality, ten
`Dlen_tag` rows (the length as a TERM in the conclusion), six polarity bridges, the axiom
recognizer: `lib_axiomRec σ (h : σ ∈ TAct)` (any axiom, at the price of its unary numeral) and
`lib_indRec` (induction instances through Foundation's `InductionR`: `qqAlls`, `IsUFormula ℒₒᵣ`,
`shift b = b`, `bv`, `fvarVec`, `substs`, `indBodyValGraph` — ℒₒᵣ-indexed graphs, hence the
`Lib/Bridge` task, agent launched). `derivation` is used ONLY as `!(derivation TAct).sigma`,
never unfolded. IN FLIGHT: `Steps.lean` (useHorn/introFact + the fragment protocol), `Lib/Bridge`.
NEXT: `describeFormula` (bottom-up walk), `transportFacts`, per-tag fragments, the recursion, the top.

## 10. U10 architecture refinement (2026-09-12): the STEP LIST, not CPS

`DESIGN` §5(b) leaves the recursion shape open ("a `Fixpoint` on `⟪d, ctx, e⟫`, or the existential
form by `induction1`"). Both hit the same wall: the natural construction is continuation-passing
(`describe (p ⋏ q) Γ d = describe p Γ (describe q Γ_p (step d))`) — the continuation CHANGES in
the recursive call, so it is neither a `PR`/`Fixpoint` construction with fixed parameters nor a
Π₁/Σ₁ statement (`∀ d, … → ∃ e, …` is Π₂; IΣ₁ has no Π₂ induction, and `ρ` may be nonstandard).
RESOLUTION: separate WHAT is done from HOW it is assembled.
* A **step** is a code `⟪tag, args⟫`: `introFact row ē`, `useHorn row ē`, `useHornAnd row ē`,
  `wkDrop Γ'`, `axLFact φ` (the `Steps.lean` constructors), rows referenced by their INDEX in a
  fixed table of library codes, witnesses as free-variable indices `&i`.
* `applyStep Γ s e` (Σ₁ function: the constructor of `Steps.lean` for the tag, applied to the
  continuation `e`), `ctxAfter Γ s` (the context after the step: the shifted `Γ` plus the negated
  new fact), `ctxVec Γ₀ steps` (PR over the list — the vector of contexts), and
  **`chainCode Γ₀ steps d`** (PR over the list length FROM THE END, with `(ctxVec, steps, d)` as
  FIXED parameters: `g 0 = d`, `g (j+1) = applyStep (ctxVec[n−j−1]) (steps[n−j−1]) (g j)`).
* `StepOK Γ s` (Δ₁: the row's antecedents are in `Γ` at the stated indices, the witnesses are
  terms, …); `chainCode_proof : (∀ i < n, StepOK (ctxVec[i]) (steps[i])) → DerivationOf d (ctxVec[n])
  → DerivationOf (chainCode Γ₀ steps d) Γ₀` and `dlen_chainCode_le` (sum of the per-step costs) —
  both by IΣ₁ induction on `j` with Π₁ predicates.
* Every producer is then a LIST-valued Σ₁ function: `describeSteps r` (by `UformulaRec`-style
  recursion, children's lists concatenated, with the index bookkeeping `descCount`), the per-tag
  fragments, and `verifySteps ρ` (a `DlenGraph`-style fixpoint on `⟪ρ, list⟫`); their theorems are
  `StepsOK` (Δ₁, bounded ∀ over the list) + the final-context facts + the length sum, all Π₁ in the
  input, provable by `IsUFormula`/`Derivation.induction1`.
* `verifyCode ρ := chainCode Γ₀ (verifySteps ρ) (top-closing code)`.

**§9 status — `Lib/Bridge` DONE (637df06, 49 rows, 31 V-lemmas):** ℒₒᵣ/LAct lifts (`IsUFormula/
IsSemiformula.LAct_of_LOR`, `bv` invariance), invariance of every `L`-indexed code operation on
ℒₒᵣ-codes (`neg/shift/subst/free/substs1/imp`, term ops; `subst` needs `IsUTermVec ℒₒᵣ` for the
`qVec` bump), the ℒₒᵣ formation rows, the `LAct → ℒₒᵣ` graph bridges, `indBodyIntro` (11 vars),
`.sigma → .pi` bridges at both languages, `axIsFormula`; the `axm`-leaf chain is written in the
file's closing docstring. NOT `rfl`: every operation is an `L`-indexed fixpoint recursion.
IN FLIGHT: `Steps.lean` (final), `Chain.lean` (§10). NEXT: `describeSteps`, fragments, `verifySteps`, top.

**§9 status — `Steps` DONE (511e5f1, census 251):** `useHornCode`/`useHornAndCode`/`introFactCode`/
`axLFactCode`/`wkToCode` with proofs and `dlen` bounds, `instOuterAt_subst` (one simultaneous
substitution makes fact matching SYNTACTIC), the canonical fact codes `subst ?[w] ⌜lMap emb P⌝`,
the shift bookkeeping (`subst ?[w] P` reappears as `subst ?[shift w] P`), and the worked
`describeAndCode` (introFact ∘ useHorn ∘ useHorn, cost `≤ dlen d + ΣNᵢ + 56|Γ| + O(|B|E)`); the
fragment protocol is the module docstring §1–10.
**RISK found 2026-09-12 (cost accounting):** `Primitives`' `setLen_setShift_le : |setShift Γ| ≤ 2|Γ|`
is the unary-index doubling bound; composed over `n` eigenvariable introductions it gives
`2ⁿ|Γ|` — EXPONENTIAL, unusable. The honest bound is additive: `|setShift Γ| ≤ |Γ| + occ(Γ)` with
`occ` the number of free-variable occurrences (each index grows by exactly 1), so `n` introductions
cost `≤ n · occ` extra — the factor-`g` index cost of DESIGN §3.7, not `2ⁿ`. The walk/fragment
implementations must use the additive lemma (to be proved in `Length.lean`/`SequentLength.lean`
terms: `termLen (termShift t) ≤ termLen t + fvarOcc t`, etc.) or the binary-index variant of
`Length.lean`. `DESIGN_describe.md` (agent launched) is asked to pin this down.

**§10 addendum — `DESIGN_describe.md` (2026-09-12, 720 lines): the formula walk, specified.**
Decisions it fixes: (1) `describeSteps` is a `Fixpoint` on `⟪n, r⟫` (arity changes under
quantifiers; `UformulaRec1` keeps the parameter fixed — `Formula/Basic.lean:507-514`); (2) leaf
values (symbol codes, bvar indices, ARITIES) are chain numerals `cT n` (`cT 0 = ⌜0⌝`,
`cT (n+1) = cT n ^+ ⌜1⌝`) because the rows write the body arity as the TERM `n + 1`, so the
child's fact matches syntactically; a bvar index `z` is a numeral witness (paid by `ρ`'s unary
`termLen ^#z = z + 1`), and `z < n` is DERIVED by `z + 1` Horn steps from two new `lt` rows;
(3) two extra step tags, `sElimExs` and `sSplit`, for rows concluding `∃x̄ (C₁ ∧ … ∧ C_j)`
(`negAndB`, `freeAllB`); (4) NO `sWkDrop` inside the walk (the steps are `Γ`-independent so the
theorem can quantify over `Γ`); (5) witness lists = the row's DSL variable list read right-to-left;
after `a` eliminations the last-listed variable is `&0`; the index rule for siblings:
`&0 ↦ &(c + 1)`; (6) `descCount ≤ |r|`, `stepCount ≤ 8|r|`, cost `dlen d + C₁|r|(N + |Γ|) +
C₂|r|²·fvOccS Γ + C₃|r|³`, witness bound `E ≤ 2(n₀ + |r|) + 18` independent of `Γ`; (7) all
hypotheses are memberships of codes built from witness TERMS — the values the eigenvariables
denote never appear (the derivation is valid under every valuation). LIBRARY GAPS (§10 of the
report): two `lt` rows (`0 < y+1`, `x < y → x+1 < y+1`), per-symbol closed rows `isRelConst`/
`isFuncConst` (8), `isUTermVecOfSemitermVecLAct`, `isSemitermVecQVec`, `substs1Substs`;
`instOuter_subst_bvN` (N ≤ 7), `freeIter_subst_listToVec`, `cT` lemmas; and for the fragments:
`formulaLenShift` + `fvOcc` rows (a SHIFTED atom's length cannot be bounded with the term vector
opaque). The `neg`/`shift`/`subst`/`free` shape facts are produced by separate `negSteps`/… (§9).

**§9 status — `ShiftLen` DONE (1eb099b, census +13):** occurrence counts `fvOcc`/`fvOccVec`/
`fvOccF`/`fvOccS` (Σ₁, by the `termLen`/`formulaLen`/`setLen` schemes), EXACT shift laws
`termLen (termShift t) = termLen t + fvOcc t`, `formulaLen (shift p) = formulaLen p + fvOccF p`,
`setLen (setShift s) ≤ setLen s + fvOccS s`, invariance of the counts under shift, and the LINEAR
iteration bound `setLen (setShiftIter n s) ≤ setLen s + n · fvOccS s`; sanity `fvOcc ≤ termLen` etc.;
`dlen_elimExistsCode_le_occ` (`… + 4|Γ| + fvOccS Γ + …`). The `free` bound `+ 1` was FALSE
(`free` frees every `#0` occurrence) — delivered `≤ fvOccF p + formulaLen p`; the sharp form needs
`bvOcc` (in the Walk task). TRAP: a `TermRec`/`UformulaRec1` blueprint clause written as the direct
graph `!listSumDef y v'` makes the `_defined` obligation loop forever — ∃-wrap it
(`∃ s, !listSumDef s v' ∧ y = s`, the `TermLen` shape). `Audit.lean` has its OWN import list.
IN FLIGHT: `Chain` (with `sElimExs`/`sSplit`), `Lib/Walk` + `WalkLemmas` (gaps, `cT`, `bvOcc`).

**§9 status — `Lib/Walk` + `WalkLemmas` DONE (45c8844, census 292):** the two `lt` rows, eight closed
symbol rows written with CHAIN numerals (`“!LAct.isRel (0+1+1) 0”`, verified `= isRel ⇜ ![cTT k, cTT R]`),
`isUTermVecOfSemitermVecLAct`, `isSemitermVecQVec`, `substs1Substs`; `cTV`/`cT`/`cTT` with
`quote_cTT`, `termLen (cT n) = 2n+1`, shift/subst/bshift invariance, `fvOcc = 0`; `bvOcc` family;
`fvOccF_subst_le : ≤ fvOccF p + bvOccF p · M` (entry bound `M`), `fvOccF_free_le' : ≤ fvOccF p +
bvOccF p`; `instOuterAt_subst_bvList` (+ `_bvN`, N ≤ 7), `freeIter`, `free_exsIter`,
`freeIter_subst_listToVec` (last-listed existential is `&0`, witnesses shifted `k` times).
Pending on `Chain` landing: the `Steps.lean` `dlen_introFactCode_le_occ` swap. IN FLIGHT: `Chain`
(resumed), `RowInst` (row-shape/instantiation lemmas + canonical context-fact codes).
NEXT: `describeSteps` (the walk itself, a `Fixpoint` on `⟪n, r⟫`) once `Chain` fixes the step codes.

**§9 status — 2026-09-13, takeover on the new account: `Chain.lean` diagnosed.** The wip draft
(Part A vector twins) did not finish type-checking in 30 min because of the BLUEPRINT TRAP: two
`PR`/`VecRec` clauses called a Σ₁ graph DIRECTLY (`!(qVecGraph L) y ih`, `!(impGraph L) y x ih`);
∃-wrapped (`∃ s, !(qVecGraph L) s ih ∧ y = s`) the file elaborates in 9 s (bisection by
truncation: prefix 130 OK, 150 stalled). It then shows 25 genuine errors (never checked end to
end before the rate-limit kill): a guessed API name `VecRec.Construction.result_defined_iff`
(lines 226, 262, 334 — find the real `VecRec` definability lemma), unsolved goals at 340, failed
rewrites in A.5 (`nth_qVecIter_single` at 493 and after). Part B (step language, `ctxVec`,
`chainCode`, `StepOK`, theorems) not started. Agent launched to repair Part A and write Part B.

**§9 status — `Chain` DONE (2026-09-13, census +9): Part A repaired, Part B landed.** Part A
(vector twins): the `VecRec` definability lemma is `eval_resultDef` (xs-first constructions use the
bare `resultDef`, parameter-first ones the `.rew` swap); `qVecIter` entry lemmas need the `len`
rewrite (`hv.lh`) BEFORE `nth_termBShiftVec`; the composition law
`termSubstVec_qVecIter_single` (`termSubstVec (n+k+1) (qVecIter k W) (qVecIter (n+k) (e∷0)) =
qVecIter k (concat W e)`, a `V`-cast on the length, never a `ℕ` ascription — it unifies `V := ℕ`);
`instOuterAt_eq_subst` (one simultaneous substitution) and the agreement theorems
`exsChainV/hornCloseV/useLemmaV/useHornV/useHornAndV/introFactV_vecOf`. Part B (§10): rows
`⟪dΛ, m, B⟫` with `TableOK tbl N`; six step codes — the Horn steps CARRY their decomposition
(`sUseHorn i ev as c`, `sUseHornAnd i ev as c₁ c₂`, `sIntroFact i ev as R`) and `StepOK` checks it
syntactically (`rowB = impChainV as c`), so no Σ₁ Horn-decomposition of a code exists;
`sElimExs P`, `sSplit p q` (via `splitAndCode`, the context already holds `neg (p ⋏ q)`,
`insert_eq_self_of_mem`), `sWkDrop Γ'`; `axLFactCode` is a LEAF, never a step (the chain's `d`).
`applyStep/ctxAfter/stepCost` are tag `if`-chains with explicit graph Defs (the `relabelSym`
pattern; `π₁` is a LOW-precedence prefix — parenthesize `(π₁ x) ^⋏ (π₂ x)`), `ctxAfter` needs no
table. `StepOK tbl E M Γ s` has an arity cap `M` (the STANDARDNESS bridge
`exists_list_of_len_le`: a vector of length `≤ (M : ℕ)` is `vecOf` of a Lean list, so the list
theorems apply — the theorems take `(M : ℕ)`); `ctxVec` (PR forward, stability + successor law),
`chainAux/chainCode` and `costAux/costSum` (PR from the end, fixed parameters);
`chainCode_proof`/`dlen_chainCode_le` by `pi1_succ_induction` on the position from the end;
`stepCost` reproduces the `dlen_…_le` bounds exactly (tag 3: `4G + |setShift Γ| + 7|P| + 10`,
the shifted length explicit). TRAPS: arity > 5 functions have no `Function₆` notation — state
`𝚺₁.DefinedFunction (fun v : Fin 6 → V ↦ …)`; `definability` does not compose 5-ary functions —
write the Def; `add_le_add_right` is swapped (use `add_le_add h le_rfl`); `zero_lt_one` is
ambiguous (`_root_.`); `tsub_add_cancel_of_le` for `n = (n - k) + k`. NEXT: `RowInst` (in flight),
then `describeSteps` producing step lists against this `StepOK`.

**§9 status — `Steps` `_occ` swap + `ChainOcc` DONE (c2cfd17, census 305):**
`dlen_introFactCode_horn_le` extracted, `dlen_introFactCode_le` byte-identical, new
`dlen_introFactCode_le_occ` (`(m + 2j + 9)·|Γ| + fvOccS Γ` instead of `(m + 2j + 10)·|Γ|`);
`ChainOcc.lean`: `introCostOcc`, `stepCostOcc` (tags 2/3 sharpened), `dlen_applyStep_le_occ`.
Limits: `stepCostOcc` has no Σ₁ blueprint (the PR `costSum` stays on `stepCost`); no
`stepCostOcc ≤ stepCost` on tag 3 (needs injectivity of `shift`, absent). IN FLIGHT: `RowInst`,
`Lib/Occ` (occurrence/shift-length rows). NEXT: `describeSteps`.

**§9 status — `RowInst` DONE (a40e816, census 334):** all 87 rows the walk and its companions use
(`quote_row_<row>` read off the DSL by one `simp only` + `rfl`; `inst_<row>` at arbitrary closed
witnesses, existential conclusions delivered as `freeIter a (instOuterAt a es body)` = the
conjunction of canonical facts about `&(a-1) … &0`, witnesses `termShift^[a]`; a third clause for
the nested existentials of `freeRel/NRel/All/Exs` via `freeIterAt`); 31 predicate codes, 28 new
fact codes with formula-ness/shift/length/`fvOccF` bounds. Generated from a row table (the
generator is in the session scratchpad, not the repo). Traps: `𝟎`/`𝟏` are `ℕ` codes — an unascribed
`bv i ^+ 𝟏` elaborates the WHOLE expression at `V := ℕ` and casts it (`↑(impChain …)`); a simp lemma
whose LHS contains `↑𝟎` is never used by `simp only` (use `rw`); `Fin`-literal casts `bv ↑2` close by
`rfl` only; `rw`'s trailing `rfl` and `simp only` can close a row goal early (guard with
`all_goals`). Flags: `isSemiformulaSubsts1B`/`isFormulaFreeB` write the arity `1` as `𝟏 ≠ cT 1`;
the length bound is multiplicative (`formulaLen P · B`), an additive one is false.

**§9 status — `Lib/Occ` DONE (18b6a91, 38 rows, census 347):** totality of `fvOcc/fvOccVec/fvOccF/
fvOccS/bvOccF`, per-constructor `fvOcc` rows, `termLenShift`/`formulaLenShift` (exact),
`setLenSetShiftLe`, `fvOccFShift`, sanity rows, `fvOccFFreeLe'` (Foundation has NO `free` graph:
`free p = substs1 &0 (shift p)` spelled out), `fvOccFSubstLe` (entry bound in the bounded `.pi`
shape `∀ i < n, ∀ e, nthDef e w i → ∀ x, fvOccGraph x e → x ≤ M`), and the §4.1 node
bookkeeping rows `dlenLeafLe/dlenUnaryLe/dlenBinaryLe` (one row use per node), `addLeAdd₃`,
`leOfEqLe`, `leAddLeAdd`, `leAddLeft`, `leRefl`. TRAP/FINDING: DSL `+`, `=`, `≤` are `rfl`-equal to
`Lengths.lean`'s `addO/eqO/leF`, but the DSL numeral `1` is NOT `rfl`-equal to `oneO`; `Nodes`'
`dlen` rows conclude in the DSL, the `bnum` bit laws use `oneO` — bridge row `dslSuccEqSuccO :
x + 1 = x + oneO` (+ `leOfLeEq`). `RowInst` generator checked in (`arith/scripts/`).
IN FLIGHT: `Describe` (the walk), a read-only design of the ten per-tag fragments (`DESIGN_fragments.md`).

**§9 status — chain-numeral arity rows DONE (6185743):** `isSemiformulaSubsts1C`, `isFormulaFreeC`
(arity written `0 + 1` in the DSL — `rfl`-equal to `cTTm m 1`, hence `cT 1` in the quote) and the
bridges `piArityOneToC`/`piArityCToOne`; `RowInst` §3.C hand-written (`cTTm`, `quote_cTTm`,
`cT_one : cT 1 = 𝟎 ^+ 𝟏`). DECISION: the walk uses `cT` for EVERY arity; the numeral-`1` rows stay
for the `axm`/`indRec` chain, converted by the bridges. TRAP: `cT 1` is not syntactically `cT (0+1)`
(`cT_succ` does not fire — use `cT_one`); the `“…”` DSL cannot splice a typed term (`!!(cTTm m k)`)
inside a variable-bearing row — write the literal and rewrite. IN FLIGHT: `Describe` (first wip
df3ffe3), `DESIGN_fragments.md`.

## 11. `DESIGN_fragments.md` (2026-09-13): the per-tag fragments and `verifySteps`, specified

Decisions: (1) a sub-chain step (`sSub`) is REJECTED — `chainAux` calls `applyStep`, so a chain
inside a step is a circular PR; instead two new FLAT tags: `sGoal e n s ū` (tag 6: `cutRule` on
the node's goal fact `∃ d n, derivation d ∧ fstIdx s d ∧ dlenGraph d n ∧ n ≤ ū`, left premise a
constant 10-node leaf from facts in context; the parent recovers `d, n` by `sElimExs`×2 +
`sSplit`×3) and `sLemma A dA` (tag 7: cut in a CLOSED numeral fact with its Γ-independent
derivation `dA` carried as data; `StepOK` = `DerivationOf dA {A}`, Δ₁). (2) `ū_ν = bnum (dlen ν)`
(a numeral); per node one `dlenBinaryLe` + one `sLemma` (`bnum a + bnum b + bnum c + 1 ≤
bnum (dlen ν)`, true by `DlenGraph.*_iff`) + `leTrans`; a Σ₁ prover `numSteps` over the
`Lengths.lean` term-level rows produces the closed facts. (3) No environment, no `sWkDrop`:
fragments assume a CANONICAL LAYOUT (member dossiers in walk order, insert-chain prefixes, `s =
&k`, `l_s = &0`); parents COPY inherited objects in (`eqTotal` + ~30 congruence rows); sequents
are chains over distinct members so `setLen` is exact by `sLemma` on V-truth (no `∉`); the row's
`insertDef cp p s` object is identified with the chain by `subsetAntisymm`. (4) Derived formulas
(`neg/shift/substs/free`) are RE-DESCRIBED bottom-up and CERTIFIED by new bottom-up rows (incl.
term-level `termShiftVec/termSubstVec` intro rows), replacing DESIGN_describe §9's opaque-vector
companions; an identification walk `eqSteps` (12 injectivity rows) handles duplicate inserts,
`shiftRule`, `axm`, and the top's `x_χ = ⌜χ⌝` pin. (5) FACT corrected: Foundation's `wk` clause is
`fstIdx d' ⊆ s` — only `cut` introduces arbitrary formulas. (6) `VerifyGraph W tbl ρ L`: a Δ₁
`Fixpoint` on `⟪ρ, L⟫` (`DlenGraph` pattern, `StrongFinite` via `ρ' < ρ`, `L' ≤ L` for
sub-vectors — new `le_appendV_mid`); existence by `Derivation.induction1 𝚺`, `verifySteps_ok`
(Π₁, `Layout Γ ρ → ListOK ∧ NoDrop ∧ goal fact ∧ shifted layout`) by `induction1 𝚷` +
`Fixpoint.case`. (7) COST: `O(g)` steps, contexts `O(B·g²)`, per step `O(|Γ|)`: `dlen ≤ dlen d +
C·(dlen ρ + 1)·(setLen Γ + N + (dlen ρ + 1)²)` — CUBIC; with `setLen Γ_top = C_χ·O(‖k‖)` and
`dlen ρ ≤ ‖k‖³` this is `BoundedInnerNec 3` exactly. (8) `M = 9`. (9) GAPS: ~150 new rows,
~100 `inst_` lemmas (generator), tags 6/7 in `Chain.lean` (~500 lines), producers
`memberList/copySteps/chainSteps/eqSteps/certX/lenSteps/numSteps/pinSteps/frag<Tag>` (~6–7k
lines), V-lemmas `setShift_insert`, `termLen_bnum_le`, `le_appendV_mid`. ORDER: tags 6/7 +
leaves → `numSteps` → `copySteps/chainSteps/eqSteps` → `certX/lenSteps` → the ten `frag<Tag>` +
`VerifyGraph` → `verifySteps_ok` → top. RISK: the ten per-tag LAYOUT theorems (index bookkeeping);
`axm`(ii)'s `bv`/`fvarVec` V-lemmas (Foundation status unverified). Note: `Occ.lean`'s `fvOcc`
rows are not needed by this design (shifted members are re-walked with exact lengths).

**§9 status — `Describe` (the walk) DONE, D1–D5 (df3ffe3 … a1f8b2b; 5616 lines, census +19, root
and `Audit` wired):** Part 0 vector/shift laws (`appendV`, `shiftsV`, `shiftIterV`, `ctxVec` append
laws, `ListOK`, `NoDrop` transport); Part 1 the walk's row table (D1: 40 rows in a FIXED order,
`rIdx_<row>` constants, `exists_walkTable : ∃ N, ∀ V, ∃ tbl, TableOK tbl N ∧ WalkTable tbl`, the
PIECE table `walkPieces` (`⟪tag, as, c⟫` per row, a closed V-generic term passed to every producer as
a PARAMETER — a closed quote must never enter a blueprint), `mkStep W i ev = ⟪tag, i, ev, as, c⟫`,
`walkTable_<row>`/`mkStep_<row>`); Part 2 the TERM walk (D2) as a `TermRec` construction with
parameters `(W, n)` (`vRef`, `ltSteps` = PR on `z`, `bvarNode/fvarNode/nilNode/adjNode/funcNode`,
`descVecAux` = PR from the END of the vector, `descT/describeT/descCountT/descTVec` + equations);
Part 3 D3 for terms (`stepOK_useHorn/introFact`, the 21 per-row `ok_<row>` lemmas from
`mkStep_<row>` + `walkTable_<row>` + `inst_<row>`, `ltAux_ok`, the node lemmas, `descVecAux_ok`
by PR on the number of entries folded with the entries' facts as a LEAN-level hypothesis, and
`termOK_of_isSemiterm` by `IsSemiterm.induction 𝚷` on the Π₁ invariant `TermOK tbl W n t := ∀ E,
2n + 2|t| + 8 ≤ E → TermFacts … ∧ descCountT + 1 ≤ 2|t|`: `describeT_ok`, `describeT_chain`);
Part 4 the FORMULA walk (D2) as a `Fixpoint` on `⟪n, r, y⟫` (`DescF`, `Finite` — NOT `StrongFinite`:
the quantifier clause references `⟪n+1, p, yp⟫`, bounded per clause by `⟪n+1, r, y⟫`; `DescFGraph`
Σ₁ via `fixpointDef`, `case_iff`, eight inversion lemmas, existence by `sigma1_structural_induction`,
uniqueness by `pi1_structural_induction`, `descFw` by `choose!`, `describeF/descCountF`, equations
`descFw_<c>`; four node emitters `constNode/binNode/quantNode/atomNode` taking their two row
indices as arguments); Part 5 D3/D4 for formulas (19 formula-row `ok_<row>`, node lemmas delivering
the root's SHAPE fact too, `formOK_of_isSemiformula` on `FormOK` (`E ≥ 2n + 2|r| + 8`, count
`descCountF + 1 ≤ 2|r|`), `describeF_ok`, `describeF_chain`, `describeF_shape_and/all/verum/rel`);
Part 6 sizes (`len (describeT/F) + 4 ≤ 12·|t|/|r|` — DESIGN's `8|r|` undercounts constants);
Part 7 D5 the cost: a HORN-ONLY list (tags 0/1/2, row bodies `≤ B`) costs `stepK N E B + 36·|Γᵢ|`
per step (`gcongr` monotonicity to the cap `m, j ≤ 8`, `hornCost_G/introCost_G` split off the `|Γ|`
coefficient), the contexts grow ADDITIVELY (`ctxAfter_len_le : |Γ'| ≤ |Γ| + fvOccS Γ + 4BE`,
`fvOccS Γ' ≤ fvOccS Γ + 4BE`; `ctxVec_len_le`), `costSum_le_of_hornOnly`, the walk is Horn-only
(`hornOnly_describeT/F` via 40 `tag_<row>` lemmas), and **`dlen_describeF_chain_le`**:
`dlen (chainCode tbl Γ (describeF n r) d) ≤ dlen d + 12|r|·(stepK N E B + 36·ctxBound E B Γ (12|r|))`,
`ctxBound E B Γ L = |Γ| + L·fvOccS Γ + (L² + L)·4BE` — DESIGN §6.3's polynomial, `B` a bound on
the table's row bodies (`∀ i < len tbl, |rowB tbl.[i]| ≤ B`, a table constant).
TRAPS: a DSL wrapper with a DUPLICATED variable (`“y W n z. !ltAuxDef y W n z z”`) runs away like
`setLenDef` — use `.rew (Rew.subst …)`; a PR/TermRec clause calling a Σ₁ Def DIRECTLY on `y`
(`!nilNodeDef y W n`) loops in `_defined` — ∃-wrap (`∃ s, !nilNodeDef s W n ∧ y = s`); `definability`
on a predicate mentioning `walkPieces` (or any def without an instance, e.g. `HornOnly`) times out
at `whnf` — keep `W` abstract with `hWp : W = walkPieces` and give every predicate an instance;
`ArithS.descF` was taken (`Code.lean`) — the walk's function is `descFw`; `rw [← hk]` with
`hk : ↑rIdx = 0` rewrites every `0` (the tag too) — rewrite the hypothesis instead; the
`descCount ≤ |r|` of DESIGN §4.3 is FALSE (vector nodes count), the true bound is
`descCount + 1 ≤ 2|r|`. NOT done: `negSteps/shiftSteps/substSteps/freeSteps` (DESIGN §9), the
D4 shape facts for `or/exs/falsum/nrel` (same proof as the four given), term-level shape facts.

**§11 status — `Chain` Part C DONE (6d4ebab):** `goalFact s ū := ^∃ ^∃ goalBody` (`d = #1`, `n = #0`;
conjuncts `derFact/fstIdxFact/dlenFact/leFact` as canonical codes over `Pderiv/PfstIdx/Pdlen/Ple`),
`goalInst`, `instOuter_goalBody`; the leaf `goalLeafCode` (2 `exsIntro` + `conj4Code` (3 `andIntro`
+ 4 `axL`) + 1 `wk`), `goalLeafCode_proof`, `dlen_goalLeafCode_le ≤ 10|Γ| + 27·|goalBody|·E + 2E + 41`
(MULTIPLICATIVE in `|G|·E` — the additive form is false when a variable repeats); tags `sGoal e n s ū`
(6; `ctxAfter = insert (neg goalFact) Γ`; `goalCost G Q E = 11G + 27QE + 2E + 42`) and `sLemma A dA`
(7; `StepOK = LemmaOK := IsFormula A ∧ DerivationOf dA {A}`, Δ₁ via `DerivationOf.definable'` — `derivation`
never unfolded; cost `dlen dA + 2|Γ| + 2|A| + 2`); `GoalOK` (12 conjuncts; one `definability` over
13 inline conjuncts hits aesop's 200-rule limit — split); `applyStep_proof`/`dlen_applyStep_le`/
`isFormulaSet_ctxAfter`/`ChainOcc` extended, all pre-existing names/statements byte-identical;
`mem_ctxAfter_of_noShift'` (tags 0/1/4/6/7). `Chain` now imports `RowInst`. Definability without
touching closed quotes: generic `fact1Def τ`/`fact2Def τ` blueprints proved for a VARIABLE `τ`.
NEXT (design order): `numSteps`, then `copySteps/chainSteps/eqSteps`, `certX/lenSteps`, `frag<Tag>`.

**§11 status — `Lib/Frag` + `RowInstB` DONE (3a3cad2; census 396):** the 196 rows of §8.1 (copy-in 40,
identification 12, functionality 37, sets 3, `fstIdx` per tag 10, top nodes 9, lengths 7, certification
46, numerals 6, `axm`(ii) 26) with `quote_row_/inst_` lemmas and the new predicate/fact codes, all
generated by `arith/scripts/gen_frag.py` from ONE row table (`Frag.lean.head`, `RowInstB.lean.head`).
SKIPPED: the per-`σ`/`χ` closed shape rows (a family produced by `pinSteps`, not rows) and the ~100
`inst_` lemmas for the EXISTING Nodes/Sets/Lengths/Occ rows (the generator's predicate table now
covers them — add as rows). TRAPS: a CLOSED row over a PR-blueprint graph at numerals hangs `simp`
(dummy binder); `Matrix.vecForall_iff` hangs at `m = 0`; NAME CLASH with `NumSteps` (`Peq/eqFact`,
`formulaLen_leFact_le`, `quote_closed_mul_m`, `termSubst_qqMul'`) — Frag's are suffixed `B`; unify
later. PROCESS: watcher shells whose own command line contains the polled pattern loop forever —
poll with `pgrep -f 'bin/lake build ArithS'`, never a pattern that matches the watcher.
IN FLIGHT: `NumSteps` (resumed), `Layout` (copySteps/chainSteps/eqSteps).

**§11 status — `NumSteps` DONE (ded402f; ≈3950 lines, census +14):** Σ₁ provers producing DERIVATION
CODES of closed binary-numeral facts, each with `DerivationOf`, a cubic `dlen` bound (`nodeCost N B E
= N + 800·B·E`) and `LemmaOK (sLemma A dA)` packaging: `succCode`, `addCode` (Fixpoint on `⟪a,b,d⟫`),
`leCode`/`ltCode`, `oneLe`, the node-bookkeeping facts `leafFact/bin2Fact/bin3Fact/sum2Fact`
(`bin3Fact : bnum a + bnum b + bnum c + 1 ≤ bnum n`, the `dlenBinaryLe` companion), `cTEqFact/cTLeFact`
(`cT z = bnum z`); a 19-row library, `exists_numTable`, combinators `goalLeaf/cut1/hornGoal/stepL`.
NOT delivered: N4 `mulEq`, N5 `lengthEq` (top only), the general-list N3. TRAPS: a full `simp` on the
instance proof of a Fixpoint-defined function explodes to 17 GB — rewrite explicitly, never unfold the
graph wrapper; `definability` dies on nested combinators — explicit blueprints; `zsh` `pipestatus` is
lowercase. NAME CLASH with Frag resolved by Frag's `B` suffixes (unify later).
IN FLIGHT: `Layout` (copy/chain/eq), `Cert` (certX + lenSteps).

**§11 status — 2026-09-14 morning (after the 02:10 rate-limit kills; both agents resumed 09:01):**
`Layout.lean` wip through Part 3 (71eb308, b4bee97; 4080 lines): `copySteps` (19 fact-tag kinds with
explicit blueprints, `copyAux` PR, `copySteps_ok`: Horn-only, one shift, `eqFactB &0 &(i+1)` + every
copied fact, `costSum_copySteps_le`) and `chainSteps` (`chainPre/chainA/chainBpre/chainB` PR,
innermost-first insert chain with interleaved formula-set facts, `subsetRefl/Insert/Trans`,
`memInsertSelf`, `subsetMem`, `setLenTotal`; `chainSteps_ok` — final layout `l_s = &0`, `s = &1`,
`s_i = &(i+1)`; `+ subsetReflC` row, Frag/RowInstB regenerated); Part 4 `eqSteps` pending.
`Cert.lean` wip Part 0 (1889d58: dossiers `DossF/DossT/DossV` = the walk's own final context from
the empty context shifted to an offset, `finalCtx` monotonicity, transport through `NoDrop` lists,
`shiftIterV` of every fact, per-constructor decomposition lemmas) + `CertRows` (56c29f7, generated by
`scripts/gen_cert.py`: the ten `Lib/Lengths` rows re-issued with `quote_row_/inst_` lemmas, the
certification table `certRows = walkRows ++ pad ++ 81 rows at 100+k`, `CertTable` (implies
`WalkTable`), `exists_certTable`, `certPieces` extending `walkPieces`); the producers pending.

**§11 status — `Layout` DONE (2026-09-13; Parts 1–4):** the three producers of §3.3–3.5 against the
step language. Part 1: `layoutRows := walkRows ++ 47 rows` (copy-in, identification, `subsetAntisymm`,
the new Frag group K `*C` — the `Sets`/`Lengths` rows re-issued WITH `inst_` lemmas, `IsFormulaSet 0`
reached as `0 ⊆ 0 → s ⊆ 0 → IsFormulaSet s`, never a closed `0` inside `isFormulaSet`), `LayoutTable`
(⇒ `WalkTable`), `layoutPieces` extending `walkPieces` entrywise (`mkStep_layoutPieces_lt`, so the
walk's `ok_` lemmas transfer), per row `lok_<row>` (generated). Part 2 `copySteps W i T`: FACT TAGS
`⟪kind, args⟫` (19 kinds: pi/and/or/all/exs/rel/nrel/verum/falsum/len/mem for formulas, tpi/func/bvar/
fvar/tlen for terms, adj/tvpi/utvpi for vectors) name one dossier fact and its other witnesses in the
PRE-copy frame; `eqTotal [^&i]` then per tag the congruence step (+ the walk's `.sigma→.pi` bridge for
the four formation kinds); `copySteps_ok`: `TagOK` for every tag ⇒ Horn-only, ONE shift, `≤ 2|T|+1`
steps, `eqFactB &0 &(i+1)` and every `tagFact` in the final context. Part 3 `chainSteps W xs`:
members inserted INNERMOST FIRST so `s_i = insert x_i s_{i+1}` ends at `&(i+1)` with NO index
arithmetic in the membership phase (only `k − (c+1)` in the intro loop, via `nthFromEnd`); the
formula-set facts interleaved into the intro loop; membership by `subsetRefl` + per member
`subsetInsert/subsetTrans/memInsertSelf/subsetMem` (`O(k)`); `setLenTotal` last. Final layout
(`k+1` shifts): `l_s = &0`, `s = &1`, `s_i = &(i+1)`, `insFact/fsetPiFact/memFact` per member,
`setLenFact &0 &1` (`chainSteps_ok`, `≤ 7k+6` steps). NOTE: this deviates from §3.2's `s = &k` (which
assumed a length object per prefix; the exact-length `sLemma` route is `NumSteps`'). Part 4
`eqSteps W i j r`: the walk's recursion shape replayed ONCE per code as a TEMPLATE `⟪count, facts,
steps⟫` with witnesses `tL/tR/tA` (left offset, right offset, closed term) — `TermRec` for terms, a
fold from the end for vectors, `UformulaRec1` (parameter unused) for formulas — then RELOCATED
(`relocS`/`relocD`, `VecRec` maps); `dossFacts P i r` = the relocated facts (`P := factPreds`, the
table of the twelve predicate codes, a PARAMETER), `DossierAt P Γ i r`; `eqSteps_ok` by the template
invariant `TOK` (top `vRef · k`, so the empty vector's `eqRefl [𝟎]` and the objects share one
statement), structural induction on terms/vectors/formulas. Costs: all three lists are Horn-only, so
`costSum_le_of_hornOnly` gives `len · (stepK + 36·ctxBound)`. DEBT: the bridge "the walk's final
context ⊇ `dossFacts factPreds 0 r`" and `eqCount r = descCountF W n r` are NOT proved here (the
`Cert` module's `DossF/DossT/DossV` dossiers are the natural home). TRAPS: `definability` on a
19-branch `ite` or on a bounded `∀ e < c + 1` (compound bound) times out / trips aesop — explicit
blueprints, a variable bound; `definability` unfolding a fact code whose predicate is an OPERATOR
sentence (`Pmem`) hangs — give every fact code a `_definable` instance (named `_definable'` here,
`Cert.lean` owns the plain names); `add_lt_add_left/right` are swapped like the `le` versions; a
`by_cases` branch must carry ALL previous case hypotheses into `simp`; `Function₅` exists only in the
`via` form; `ArithS.eqF` was taken (`TheoryAct`) — the formula template is `eqFT`; a `shiftTW` that
shifts every non-absolute tag made `relocV_shiftTV` FALSE for malformed tags (shift tags 0/1 only).

**§11 status — `Layout` DONE (0a076a4; 5299 lines; census standard):** `layoutRows` (47 = walk + copy-in
+ identification + `subsetAntisymm` + the Frag group K re-issues of Sets/Lengths rows WITH `inst_`),
`copySteps W i T` (19 fact kinds; index rule: one shift, source `&i ↦ &(i+1)`, copy `= &0`),
`chainSteps W xs` (innermost-first insert chain; LAYOUT `l_s = &0`, `s = &1`, `s_i = &(i+1)` —
deviates from §3.2's `s = &k`), `eqSteps W i j r` (the walk's recursion replayed once as a
template `⟪count, facts, steps⟫` and RELOCATED; `DossierAt P Γ i r`; `eqCount`), each with `_ok`
(`ListOK ∧ NoDrop ∧ HornOnly ∧ shiftsV = … ∧ len ≤ … ∧ facts ∈ finalCtx`) and `costSum_…_le`.
REMAINING bridges (stated, not proved): "the walk's final context holds `dossFacts factPreds 0 r`"
and `eqCount r = descCountF W n r` — the Cert agent's `DossF/DossT/DossV` are the natural home.
Name note: Layout's fact-code `_definable'` instances (Cert declares the plain names).
IN FLIGHT: `Cert` (producers), `Frag1` (the six fragments needing no re-description).

**§11 status — 2026-09-14 10:40, PAUSED (agents stopped for an account/model switch):** `Cert` and
`Frag1` in-progress edits + `Frag1Rows` (generated) committed UNVERIFIED as wip; see HANDOVER §8
for the resume procedure and the remaining ladder.

**§11 status — 2026-09-14 (Opus 5 takeover): the three unverified files triaged.** Baseline
re-verified: `lake build ArithS` green, 3240 jobs, census 417 lines (one pre-existing subset line
`substs_leF_imp`); none of `Cert`/`Frag1`/`Frag1Rows` was imported, so the baseline never depended
on them. Results: `Frag1Rows.lean` (2944 generated lines) GREEN as committed, 21 s.
`Frag1.lean` had exactly 2 errors, both the residual goal `2 ≤ 3·M + 11` left by
`mul_le_mul (by norm_num) …` in the tag-4 and tag-6 cost cases — `norm_num` cannot do
`V`-arithmetic with a CAST NATURAL; fixed by `le_trans (by norm_num) le_add_self` (i.e. `2 ≤ 11 ≤
3M + 11`); GREEN in 18 s (`ecd5559`). `Cert.lean` STALLED (exit 124 at 30 min, nothing flushed);
bisection by truncation (prefixes 1350/1500/1570/1597/1620/1670/1682, each ≤ 12 min) pinned it to
lines 1671–1682: **`passGraph_defined`'s blanket `simp [passGraphDef, eval_fixpointDef, PassGraph]`
over the FIVE-disjunct `PassT` blueprint** (the same one-liner is fine for `Describe`'s smaller
`DescF` at `Describe.lean:3309` — the trap is the blueprint's size, not the pattern). FIX
(`a140a68`): push the substitution through with a targeted
`simp only [passGraphDef, val_mkSigma, Semiformula.eval_substs, Matrix.comp_vecCons',
cons_val_zero, cons_val_one, head_cons, constant_eq_singleton]` and then `rw
[PassT.construction.eval_fixpointDef]; rfl` — the whole file now elaborates in 44 s. Remaining:
10 ordinary errors in lines 1809–1827 (`passTGraph_exists_bounded`'s `≤ B` associativity
bookkeeping: `rw [add_assoc]` against goals already right-nested, one stuck numeral) — agent on it.
GENERAL LESSON for every future `Fixpoint`: never let `simp` unfold a large blueprint in a
definability instance; rewrite with `eval_fixpointDef` explicitly after normalizing the
substitution. PROCESS: a truncation prefix that ends mid-declaration reports `unexpected end of
input` — that is an artifact, not a failure; only exit 124 with an empty log is a stall.

**§11 status — 2026-09-14 (Opus): `Cert` and `Frag1` GREEN AND WIRED (`ea5ce7e`, `d1bfb96`,
`8a5e5b1`).** `Cert.lean` 39.6 s (the 10 tail errors were one family: after `rw [hC] at hiB hjB`
and two `set`s the `≤ B` hypotheses are RIGHT-nested (`i + (cv + ct + 1) ≤ B`), so every
`rw [add_assoc …]` chain missed; replaced by explicit `le_trans`/`le_of_eq`/`add_le_add` terms —
statements byte-identical). `Frag1.lean` 18 s. Both wired into `ArithS.lean` and `Audit.lean`:
**build 3244 jobs green, census 428 lines**, one pre-existing subset line. TOOLCHAIN NOTES from the
tail fix: `gcongr` is NON-DETERMINISTIC here (on `i + c ≤ i + j + c` it sometimes closes the side
goal itself, leaving a following `exact le_self_add` with "No goals") — use explicit
`add_le_add h₁ h₂`; `le_rfl` after a rewrite produces a stuck `Preorder ?m` instance — use
`le_refl <explicit term>`. NOTE: `passTGraph_unique` does NOT exist yet (only `_exists`);
uniqueness is part of the remaining `Cert` work.

**§11 status — `Frag2` DONE (b0c0fe8): ALL TEN per-tag fragments now exist.** Build 3246 jobs,
census 437, all standard. `gen_frag2.py` + `Frag2Rows.lean` (24 new rows at `gIdx = 126+k`,
`frag2RowCount = 150`, `Frag2Table`/`frag2Pieces` extending `frag1Pieces` entrywise) and
`Frag2.lean` (1075 lines): `nodeShift`, `nodeAll`, `nodeExs` (cap `M = 9`, BINARY tail — the
witness term's length is charged), `nodeAxm` (leaf tail), each `node<Tag>Head` (4 steps, 1 shift:
totality → `fstIdx<Tag>` → `Intro<Tag>` → `Dlen<Tag>`) + a Frag1 tail, with `Head_ok`, `_ok`
(`len = 9`, `shiftsV = 1`, concluding `neg (goalFact (^&(is+1)) (bnum n)) ∈ finalCtx`), `sizeOK_`
and `costSum_…_le`. NEW predicate `Paxch`/`axchFact` (the `Δ₁ch TAct` recognizer had no code in
`RowInstB`). THE LAYOUT HYPOTHESES `Cert` MUST DISCHARGE (all stated as `neg … ∈ Γ`, the Frag1
discipline): `nodeShift` — `setShiftFact (^&is) (^&ic)` (pure producer work, every row needed is
already in the table) + `fstIdxFact`; `nodeAll` — `freeFact` (← `certFree`), `setShiftFact`,
`insFact`, `allFact`/`memFact`, `fstIdxFact`; `nodeExs` — `tPiFact`/`tlenFact` (← `describeT` +
term `lenSteps`), `leFact`, `substs1Fact` (← `certSubst` + `substsSubsts1`), `insFact`,
`exsFact`/`memFact`, `fstIdxFact`; **`nodeAxm` — the ONE deliberate weakening, flagged in the file
docstring and the census comment**: the whole recognizer chain of DESIGN §4.10 (case (i)
`pinSteps σ` + `axiomRec σ`, case (ii) `qqAlls`/`bv`/`fvarVec` + `indRec` + the `Lib/Bridge`
ℒₒᵣ↔LAct chain) is replaced by the single hypothesis `neg (axchFact (^&ip)) ∈ Γ`; when the
recognizer producer lands it discharges exactly that and nothing else changes (`axiomRec σ` is
PARAMETRIC in σ, so it needs one row per standard axiom). The fragments' PROLOGUES (§4.5(1)–(5),
§4.6(1)–(3), §4.8(1)–(3), §4.10) are not emitted here — `Frag1`/`Frag2` are the `node(ν)` part only.
TRAPS: (1) `Frag2.lean` must import `Frag1` as well as `Frag2Rows` (the symptom of the missing
import is "Function expected at …" from autobound implicits, NOT "unknown identifier");
(2) a generated row needs its predicate's `P…`/`…Fact` codes to exist already — registering a
`PREDS` entry is not enough, the code block must be hand-written (§0 of `Frag2Rows`);
(3) piece-table extension is FREE for the tails: every tail step reads an index `< frag1RowCount`,
so `goalTail*` at `frag2Pieces` is definitionally the Frag1 one after three
`mkStep_frag2Pieces_lt` rewrites (the same trick will serve any `Frag3`);
(4) `dlenExs` yields `binaryT` only if the term-length object is an EIGENVARIABLE `^&ilt` — the
numeral `bnum Lt` enters only through `leFact (^&ilt) (bnum Lt)` in the tail;
(5) `introExs`'s dummy ninth witness is the literal `𝟎`, forcing cap `M = 9` and `ok.mono h89` on
the `M = 8` siblings.

**§11 status — `Cert` Part 1–3 (23bf760, 1322ec8; 1836 → 3361 lines, census +14, all standard).**
DELIVERED: uniqueness of the term pass (`passTGraph_unique`, `passVGraph_unique`) and the functions
`passT`/`passV` with their definability and equations; the FORMULA pass as ONE parametric fixpoint
`PassF` on `⟪ν, n, r, i, j, y⟫` (`ν = 1` neg, `ν = 2` shift) with `passFGraph_exists`/`_unique`,
the function `passF` and its eight per-constructor equations, hence
`certNeg W n r i j := passF W 1 n r i j` and `certShift := passF W 2 …`; two of the four `_ok`
conjuncts (`certShift_noDrop_shifts`, `certNeg_noDrop_shifts`, `len_certShift_le`/`len_certNeg_le`:
`len + 4 ≤ 12|r|`); and the COUNT BRIDGE `Layout.lean:53` left open —
**`eqCount_eq_descCountF : eqCount r = descCountF W n r`** (`Cert` now imports `Layout`, no cycle).
NOT REACHED: the `ListOK` conjunct and the root-pair fact of `certShift_ok`/`certNeg_ok` (the
dossier-consumption argument reading the `dossF_*` decomposition lemmas), and
`costSum_certShift_le` (needs `ListOK` first); the DOSSIER bridge `DossF … → DossierAt …` (needs
`Layout`'s per-node `dossFacts_*` equations written first).
**TWO REPORTED BLOCKERS, BOTH SMALLER THAN REPORTED (checked 2026-09-14):**
(a) `lenSteps` was said to be blocked because `Describe.lean:432`'s `NoDrop` excludes tags 6/7 —
NOT A BLOCKER: `Frag1.lean:21` already defines **`NoDrop'`** (tags 0–4, 6, 7) with
`noDrop'_appendV`/`noDrop'_cons`/`mem_ctxVec_of_mem'`/`mem_finalCtx_of_mem'` and the coercion
`NoDrop.noDrop'`; `lenSteps_ok` simply states `NoDrop'`, as every `Frag1`/`Frag2` `_ok` already does.
(b) `certSubst`/`certFree` blocked because `tsvAdjCert` (9 witnesses) is absent from the
certification table under an `M = 8` cap — the ROW EXISTS and is proved (`Lib/Frag.lean:1604-1611`,
`lib_tsvAdjCert`); the cap is liftable exactly as `Frag2`'s `nodeExs` does it for the arity-9
`introExs`, via `Frag1.lean:101,114` `StepOK.mono`/`ListOK.mono`. Agent on it.
TRAPS (from the `Cert` agent, all worth keeping): (1) the fixpoint-`simp` hang RECURS at every new
fixpoint — and the targeted-`simp only` fix is NOT sufficient by itself: the fixpoint must ALSO be
wrapped in a separate `def <X>Packed (W pr : V) : Prop := construction.Fixpoint ![W] pr` before the
arity-`n` graph, or instance search unfolds through it and `definability` diverges (symptom: a goal
mentioning `construction.limSeq` with an aesop depth error); `PassGraph`/`PassTGraph` had this shape
by accident, `DescFGraph` gets away without it only because `DescF`'s blueprint is smaller.
(2) `definability` on a Π₁ motive must quantify over the GRAPH, never the `choose!` function
(`∀ i j y, PassTGraph … y → P y` works; `∀ i j, P (passT …)` gives "goal 9 was not normalised").
(3) `set_option … in` goes BEFORE the docstring. (4) Σ₁ motives forbid unbounded `∀`: every
`_exists` needs the `B`-parameter shape plus an unbounded corollary. (5) `le_of_eq (by ring)` fails
silently on inequalities — use `le_trans (le_of_eq (show _ = _ by ring)) h`. (6) `shiftsV_cons`
rewrites outermost-first: interleave each `if_neg` after its own `shiftsV_cons`. (7)
`IsUTermVec LAct m (takeLast v m)` has no standalone lemma — carry it in the induction's conjunction.
(8) `DefinedFunction` arity counts arguments, not the output. (9) a `¬(A ∧ B)` guard in a `choose!`
definability sentence must be written interpreted (`(!P → k < m) → y = 0`).

**§11 status — the `tsvAdjCert` blocker CLEARED (704fd2d; census 451, all standard).**
`cIdx_tsvAdjCert = 181`, APPENDED at the end of the table so every pre-existing `cIdx_` is
byte-stable (`certRowCount` 181 → 182 — the concurrent agents are writing consumers, so index
stability was the deciding consideration); full kit `certTable_/cpiece_/certPieces_/cmk_/ctag_`
(tag 0, `sUseHorn`) and `cok_tsvAdjCert` at **`M = 9`**. THE `M` CONVENTION (now documented in
`CertRows.lean`'s header, replacing the stale "not in the table" note): each `cok_` is stated at
its OWN minimal cap — 8 for the 81 older rows, 9 for `tsvAdjCert` — and a consumer that mixes them
runs at `M = 9` and lifts the siblings with `StepOK.mono`/`ListOK.mono` (`Frag1.lean:101,114`),
the idiom `Frag2`'s `nodeExs` already uses for the arity-9 `introExs`. `stepOK_useHorn` is
`M`-parametric, so no lemma anywhere had to change; in `gen_cert.py` the whole lift is one line
(`RM = 9 if name == 'tsvAdjCert' else 8`). METHOD NOTE worth keeping: the agent SENTINEL-TESTED its
own green result (deliberately breaking the new `cok_`'s `M` to 7 and confirming Lean fails at the
expected lines) before believing a fast `EXIT 0` on a 4000-line generated file — the right
discipline whenever "green" arrives suspiciously quickly. LESSON ON BLOCKERS: both blockers
reported against `Cert` dissolved on inspection (one was already solved by `NoDrop'`, one needed a
one-line cap lift with a worked precedent in the repository) — verify a reported blocker against
the tree before treating it as one.

**§11 status — `Layout` §4.8 + `Members` DONE (df045c4, 57bf1c4, 77bb65e; build 3248, census 464,
all standard; every check sentinel-tested).** `Layout.lean` §4.8 (5299 → 5483, additions only):
`dossFactsT/V`, `eqCountT/V`, `DossierAtT/V` (+ definability), the count equations
(`eqCountT_func = eqCountV k v k + 1`, `eqCountV_succ`, `eqCount_and = eqCount p + eqCount q + 1`,
…), the fact-list equations `dossFactsT_bvar/fvar/func`, `dossFactsV_zero/succ`,
`dossFacts_verum/falsum/and/or/all/exs/rel/nrel`, and the `DossierAt` DECOMPOSITIONS at
`factPreds` in Cert's fact order and offset spelling (`dossierAt_and : DossierAt factPreds Γ i
(p ^⋏ q) ↔ neg (andFact (^&i) (^&(i + eqCount q + 1)) (^&(i+1))) ∈ Γ ∧ DossierAt … (i+1) q ∧
DossierAt … (i + eqCount q + 1) p`, `dossierAtV_succ`, …). NOTE for the bridge: Layout's dossier
carries NO `piFact/tPiFact/tvPiFact/utvPiFact` (only the 12 shape kinds) — Cert's extra conjuncts
are dropped; hypotheses are `IsUFormula`/`IsUTermVec`. `Members.lean` (NEW, 338): `flenVec`
(VecRec map of `formulaLen`), `listSum_appendV`, `memberList` (PR on the set code: ascending,
`mem_memberList_iff`, `memberList_sorted/nodup`, `len_memberList_le_length : ≤ ‖s‖`),
**`setLen_eq_listSum_memberList : setLen LAct s = listSum (flenVec (memberList s))`** (THE
distinctness lemma, DESIGN §0 item 5) and `listSum_flenVec_memberList_le` (the `sLemma`'s true
closed sentence). §8.4 V-lemmas: nothing to write — `setShift_insert` (`Lib/Frag.lean:73`) and
`termLen_bnum_le` (`NumSteps.lean:1465`) exist. NOT started: N4 `mulEq`/N5 `lengthEq` — not a
small addition (`NumTableOK` has only the 19 `n*B` rows; each needs new rows + a bit-recursion
fixpoint on the `addCode` precedent, ~1000 lines); DESIGN NOTE: the FACT-level rows
`row_lengthZero/One/TwoMul/TwoMulOne` already exist in `RowInstB` (Frag table), so N5 can be a STEP
LIST over the Frag table instead of a `DerivationOf` sLemma. TRAPS: `add_lt_add_right hm 1` gives
`1 + m < 1 + len L` (the swap applies to `lt` too); `if … then` in a `PR.Construction` needs
`open Classical`; `lt_irrefl` is ambiguous — `_root_.lt_irrefl`; `one_le_formulaLen_V` needs
`(L := LAct) (n := 0)`; no `𝚺₁-Function₅` — state a 5-ary function as `𝚺₁.Definable (fun v :
Fin 6 → V ↦ f … = v 0)`; after appending to `Layout.lean`, `lake build
ArithS.Necessitation.Layout` (~70 s) before importers see the names.
IN FLIGHT: `Cert` (ok theorems, bridge row, certSubst/certFree, lenSteps); `Dossier` (the bridge) + N5.

**§11 status — `Dossier` (the bridge), `NumLength` (N5), `NumMul` (N4) DONE (1bbde1f, 124634c,
f1c2979; module builds green, census standard per scratch; full-build confirmation pending lake).**
`Dossier.lean` (imports `Cert`, `Members`; `DossF` is over `walkPieces`):
`dossierAtT_of_dossT`, `dossierAtV_of_dossV`, **`dossierAt_of_dossF : IsSemiformula LAct n r →
DossF W Γ n r i → DossierAt factPreds Γ i r`**, `dossierAt_of_walk : DossierAt factPreds
(finalCtx Γ (describeF W n r)) 0 r` (closes `Layout.lean:53`), the transported forms
`dossierAt_of_walk_transport`/`dossierAt_of_dossF_transport` (offset `i + shiftsV S` after a
`NoDrop` list), `dossierAtT_of_walk`; `eqCountT_eq_descCountT`. Cert's `piFact/…` conjuncts are
dropped. `NumLength.lean` (leaf, imports `NumSteps`, `RowInstB`): N5 by the `sLemma`/`DerivationOf`
ROUTE (not the step list — the Frag row `lengthTwoMul` concludes at `bnum ‖m‖ ^+ 𝟏` while the fact
needs `bnum (‖m‖+1)`, so two COMBINED rows `lenTwoMulSB “l' l x. !lengthDef l x → 0 < x → l + 1 = l'
→ !lengthDef l' (2*x)”`, `lenTwoMulOneSB` in their own 4-row `LenTableOK` table with
`exists_lenTable`): `lengthEqFact k := lengthFact (bnum ‖k‖) (bnum k)`, `LenGraph` fixpoint,
`lengthEqCode` (+ definability), `lengthEqCode_proof : DerivationOf TAct (lengthEqCode tblL tbl k)
(sing (lengthEqFact k))`, `dlen_lengthEqCode_le ≤ lengthEqBound N B N' B' k = (‖k‖+1)·nodeCap`,
`lemmaOK_lengthEq`, `stepCost_lemma_lengthEq`. `NumMul.lean` (leaf): `mulFact a b := eqFact (bnum a
^* bnum b) (bnum (a*b))`, `MulTableOK` (5 rows incl. `zeroMul` — `bnum (2·0) = 𝟎`, not `𝟐 ^* 𝟎`),
`MulGraph` on the bits of `b`, `mulEqCode`, `mulEqCode_proof`, `dlen_mulEqCode_le ≤ mulEqBound`,
`lemmaOK_mulEq`, `stepCost_lemma_mulEq`. Neither file touches `NumTableOK` (index-stable, no olean
invalidation under the concurrent `Cert` agent). FOR THE TOP: two extra tables in hand
(`exists_lenTable`, `exists_mulTable`), `mulEqCode` twice for `‖k‖³` plus `leCode`.
TRAPS: pass `factPreds` as a parameter `P` with `hP : P = factPreds` and `subst` per case, never
inside a `definability` goal; `dossF_of_walk` needs `(Γ := Γ)` in transported forms; no
`𝚺₁-Relation₅ … via` — 5-ary graphs are `𝚺₁.Defined (fun v : Fin 5 → V ↦ …)`; after `rcases … with
rfl | rfl | h` the name `a` is gone in the `rfl` branches — `by_cases ha0 : a = 0` instead; a
SENTINEL that replaces `_` by what it unifies to is a no-op — break a real argument;
`eqFactB = eqFact` is `rfl` (RowInstB's `PeqB` = NumSteps' `Peq`).
IN FLIGHT: `Cert` (ok theorems, bridge row, certSubst/certFree, lenSteps); `Top` (against a kit).

**§11 status — `Cert` Part 4 DONE: `certShift_ok`, `certNeg_ok`, costs (fdd6427 … 6c459d8; 3599 →
~5200 lines; build 3251 jobs, census 497, all standard).**
`certShift_ok {tbl N Wd W n r i j E Γ} (htbl) (hC : CertTable tbl) (hWd : Wd = walkPieces)
(hWp : W = certPieces) (hr : IsSemiformula LAct n r) (hE : 2n + 2|r| + 8 ≤ E) (hEi : i + 2|r| + 1
≤ E) (hEj) (hΓ) (hDi : DossF Wd Γ n r i) (hDj : DossF Wd Γ n (shift r) j) : ListOK tbl E 8 Γ
(certShift W n r i j) ∧ NoDrop ∧ HornOnly ∧ shiftsV = 0 ∧ neg (shiftFact (^&j) (^&i)) ∈ finalCtx`;
`certNeg_ok` identical with `neg`/`negFact`; `costSum_certShift_le/certNeg_le ≤ 12|r|·(stepK N E B
+ 36·ctxBound E B Γ (12|r|))` — the walk's polynomial. Structure §4.1–4.6 (`PassPre`/`PassPost`
packages, `TShiftOK`/`TEqOK`, `passTGraph_shift_ok`, `passTGraph_eq_ok` for any `ν ≠ 2`,
`passFGraph_shift_ok`, `passFGraph_neg_ok`). **A DESIGN BUG FOUND AND FIXED (fdd6427):** the old
`ν = 1` atom branch emitted `negRelCert` over the SOURCE vector, whose antecedent names `⟨v⟩ᵢ`, but
the image is walked afresh and its atom fact names `⟨v⟩ⱼ` — `certNeg_ok` was unprovable as
designed. Fix: the term pass's convention is now "`ν = 2` = shift, every other `ν` =
IDENTIFICATION", and `fAtomSteps` at `ν = 1` emits the identification pass + `eqRefl [&j]` +
`congRel/congNRel` before `negRelCert`; both branches also emit the closed `relRow R` step
(`isRelFact`); length bounds still fit `12|r|`. **THE `tvPiFact`/`utvPiFact` DESIGN FINDING
DISSOLVED:** the bridge already exists as WALK rows 38 (`isUTermVecOfSemitermVecLAct`) and 39, and
`vAdjSteps` already emits them on the source tail at every vector node — nothing added (the ℒₒᵣ
row `isUTermVecOfSemitermVecORB` is the wrong language). Third reported blocker dissolved on
inspection. NOT started, obstacles recorded in `Cert.lean` §4.7: `certSubst` — no `w` slot and
image offsets not in lock-step (`#z ↦ w.[z]` walked afresh) ⇒ a SIBLING fixpoint with parameters
`(W, wv, wt)`; the bvar leaf needs `termSubstBvarCert` at the original entry + identification +
`congAdj` (APPENDED to the certification table, `cIdx_congAdj = 182`, `M = 8`, sentinel-tested);
under quantifiers `qVec w` must be CONSTRUCTED by totality steps, so that pass is not shift-free.
`lenSteps` — the closed fact `bnum|p| ^+ bnum|q| ^+ 𝟏 = bnum(|p|+|q|+1)` needs an ADDITION
CONGRUENCE row (`x = x' → y = y' → x + y = x' + y'`; VERIFIED absent 2026-09-14 — no `congAdd`/
successor-congruence row anywhere) combined with `addFact`/`succFact` and `eqTrans`.
TRAPS: `definability` on an 8-conjunct inlined Π₁ motive times out at `whnf` though each conjunct
passes alone — package as defs with instances (the `GoalOK` lesson again); never hand `𝟎` to a
`cok_` witness (`isDefEq` on the closed constant times out) — name it `cTV 0` and `rw [← cTV_zero]`
first; `rw [a, b] at h₁ h₂` fails if `b` has no occurrence in one of them; `Σ` is not an identifier
character; `rw [termShiftIterV_cTV]` rewrites every instance of the first match; quantifier-child
offset bounds are `≤`, not `=`.
IN FLIGHT: `Cert` continuation (lenSteps with the congAdd row, then certSubst/certFree); `Top`.

**§11 status — 2026-09-14 late evening (Fable): `lenSteps` and the `Top` under way, both killed once
by the rate limit and resumed from on-disk state.** `Cert` Parts 5.0–5.7 (c6722dd … ebe4018, wip):
`congAdd` (cIdx 183), `congSucc` (184), `listSumAdjI` (185) APPENDED to the certification table
(447ed64; sentences + `lib_` proofs hand-written in `gen_cert.py`'s head §0); the eight length
builders `lnConst/Bin/Quant/Atom/Leaf/Func/Nil/AdjSteps`; the term/vector length fixpoint `LenT` on
`⟪tg, n, x, i, y⟫` (Blueprint 2: pieces `W` + the NumSteps table `T`) and the formula one `LenF` on
`⟪n, r, i, y⟫` (offsets move with `shiftsV` — the length lists are NOT shift-free: `shiftsV + 1 ≤
2|r|`, `len ≤ 14|r|`); the functions `lenT/lenV/lenSteps W T n r i` (Σ₁, equations,
`lenSteps_struct`); `lenTGraph_ok` (`tlenFact (bnum |t|) &(i + shifts)` in the final context, via
`LenPre/LenPreV/LenPost(V)` packages and fact transport through `NoDrop'` lists). PENDING:
`lenSteps_ok` at the formula level, `costSum_lenSteps_le`, then `certSubst`/`certFree`.
`Top.lean` (NEW, b1fc02c … 7376039, wip, ~1780 lines): the two new predicate codes
(`lenDerivableDef TAct`, `boxCore` via the Σ₁ symbol `boxCoreS`), the three closing rows
`gIntroNum/lenDerIntro/boxIntro` (Lib + pieces + `inst_`), the top table `topRows = frag2Rows ++ 5
rows at 150+k` (`TopTable`, `exists_topTable`, `topPieces`), the target's code shape for a VARIABLE
χ (`instB ⌜Box_g χ⌝ k = boxFact (numeral ⌜χ⌝) (bnum k)`, closedness/shift/length of the numeral);
§3 `RootLayout` (walk dossier + singleton chain) and the two KITS — `VerifyKit` (§6.3/§6.4/§5 for
the RELATION `VerifyGraph` at the root) and `PinKit χ` (§7.1 steps 1–4 / §7.2 pinning); §4
`rootSteps = describeF ++ chainSteps` with `rootSteps_ok`; §5 `closeSteps` (`goalElim` + the four
numeral `sLemma`s N5/N4/N4/N2 + `dlenDefIntro/proofIntro/leTrans/lenDerIntro/gIntroNum/boxIntro`)
with `closeSteps_ok` (cap 8, `NoDrop'`, 2 shifts, 15 steps, `boxFact (qNum χ) (bnum k)` in the
final context); §6 the assembly `top_main` (from `Proof ρ (instB ⌜χ⌝ k)`, `dlen ρ ≤ gBudget k`,
`VerifyGraph ρ L`, the two kits and the tables: a proof code of `instB ⌜Box_g χ⌝ k` of length
`≤ topBound`); §7 the graded polynomial-bound toolkit `PB/PBCtx` and `topD_pb` (the closing block's
four `sLemma` derivations are CUBIC in `gBudget k + 1`, using `‖gBudget k + 1‖ ≤ 3‖‖k‖‖ + 2` via
`Exp.exp`). PENDING: the final `boundedInnerNec_three_of_kit`, wiring, census.
