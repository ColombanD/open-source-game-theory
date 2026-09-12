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
