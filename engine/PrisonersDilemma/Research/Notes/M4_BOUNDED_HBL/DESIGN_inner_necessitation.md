# DESIGN: bounded inner necessitation (U5 / U10) by eigenvariables — Critch's Property 4 in Foundation's calculus

*Read-only design report, 2026-09-12. Companion to `BRIEF.md` §1/§3/§6/§7 and
`READ_foundation_calculus.md` §2/§5. FACT = verified in the sources cited (`file:line`);
ANALYSIS = paper-and-pencil reasoning by the author of this note. Foundation paths are relative
to `/Users/colomband/wt/arith-lake/packages/Foundation/Foundation/FirstOrder/`, package paths to
`arith/ArithS/`. Line numbers are those of the checked-out sources on the day of writing.*

## 0. Verdict in one paragraph

The obligation is dischargeable, and the shape of the proof is exactly the one the brief guesses:
a `TAct`-proof code `verifyCode ρ` that follows the tree of `ρ`, introduces every code it talks
about (sequents, formulas, terms, sub-derivations, lengths) as an EIGENVARIABLE obtained by
∃-elimination from a constant-size universal lemma, and cuts against a fixed library of
universal `TAct`-theorems (the per-tag introduction clause of Foundation's `Derivation`
fixpoint, the per-tag `DlenGraph` clause, totality of the Σ₁ graphs, a dozen set/formula
facts). The fixpoint predicate `derivation TAct` is NEVER unfolded inside the proof — it is a
black box that appears only in the statements of the library lemmas. With the package's
current `dlen` (every node charges its whole sequent, free-variable indices charged UNARY —
`Length.lean:16-19`, `termLen_fvar`), the honest bound is **`E(a) = O(a³)`** (safe), `O(a²)`
with a refresh discipline, and **NOT linear**: linear needs Critch's abbreviation rule. Any
polynomial suffices for PBLT with `gBudget k = ‖k‖²` and `f k = k` (`‖k‖⁶ ≺ k`). Two things
found on the way must be fixed BEFORE anything is formalized: (1) the hypothesis
`BoundedInnerNec` as written in `Assembly/Prep.lean:716-720` is FALSE for every choice of
`d c c₁ c₀` (§4.4 — the additive term must be `flen (Box_g χ)`, which contains the unary
numeral `⌜χ⌝`, not `flen χ`); (2) the `axm` nodes of `ρ` need a PA proof that an
eigenvariable-described formula is a PA axiom, which depends on the SHAPE of Foundation's
`𝗣𝗔.Δ₁` recognizer — the one library item whose cost is not obviously `O(|node|)` (§3.6).

## 1. The internal `Proof`/`Derivation` predicate, unfolded (FACT)

### 1.1 Node codes and the one-step operator

`Bootstrapping/Syntax/Proof/Basic.lean`:

* Node codes (:134-152): `axL s p = ⟪s, 0, p⟫ + 1`, `verumIntro s = ⟪s, 1, 0⟫ + 1`,
  `andIntro s p q dp dq = ⟪s, 2, p, q, dp, dq⟫ + 1`, `orIntro s p q d = ⟪s, 3, p, q, d⟫ + 1`,
  `allIntro s p d = ⟪s, 4, p, d⟫ + 1`, `exsIntro s p t d = ⟪s, 5, p, t, d⟫ + 1`,
  `wkRule s d = ⟪s, 6, d⟫ + 1`, `shiftRule s d = ⟪s, 7, d⟫ + 1`,
  `cutRule s p d₁ d₂ = ⟪s, 8, p, d₁, d₂⟫ + 1`, `axm s p = ⟪s, 9, p⟫ + 1`; each with a Σ₀ graph
  (`axLGraph` … `axmGraph`, :156-204) and `fstIdx (node s …) = s` (:267-276). `pair` is
  Foundation's `if a < b then b*b + a else a*a + a + b` (`Arithmetic/IOpen/Basic.lean:511`).
* `Derivation.Phi T C d` (:286-297) — quoted verbatim in `READ_foundation_calculus.md` §2.2:
  `IsFormulaSet L (fstIdx d) ∧ (axL-clause ∨ verum ∨ and ∨ or ∨ all ∨ exs ∨ wk ∨ shift ∨ cut ∨ axm)`,
  where the side conditions are: membership `p ∈ s`, `neg L p ∈ s`, `^⊤ ∈ s`, `p ^⋏ q ∈ s`,
  `^∀ p ∈ s`, `^∃ p ∈ s`; sequent equations `fstIdx dp = insert p s`,
  `fstIdx dpq = insert p (insert q s)`, `fstIdx dp = insert (free L p) (setShift L s)`,
  `fstIdx dp = insert (substs1 L t p) s`, `fstIdx d₁ = insert p s ∧ fstIdx d₂ = insert (neg L p) s`;
  `IsTerm L t`; `fstIdx d' ⊆ s` (wk); `s = setShift L (fstIdx d')` (shift); the axiom test
  `p ∈ T.Δ₁Class` (axm); and `dp ∈ C` for every premise.
* `IsFormulaSet L s := ∀ p ∈ s, IsFormula L p` (:19), Δ₁ via `isFormulaSet` (:20-22:
  `“s. ∀ p ∈' s, !(isSemiformula L).sigma 0 p”` / `.pi`); `insert_iff` (:40) is the
  constant-size insert law; `setShift` (:71) with Σ₁ graph `setShiftGraph` (:75-76),
  `mem_setShift_iff` (:82), `shift_mem_setShift` (:97), `IsFormulaSet.setShift_iff` (:106).
* The blueprint (`:351-410`), the Δ₁ formula of `Phi`: `.mkDelta (.mkSigma “d C. (∃ fst,
  !fstIdxDef fst d ∧ !(isFormulaSet L).sigma fst) ∧ ((∃ s < d, ∃ p < d, !axLGraph d s p ∧ p ∈ s
  ∧ ∃ np, !(negGraph L) np p ∧ np ∈ s) ∨ … ∨ (∃ s < d, ∃ p < d, !axmGraph d s p ∧ p ∈ s ∧
  !T.Δ₁ch.sigma p))”) (.mkPi …)`. Sub-formulas that appear inside it: `fstIdxDef`, `insertDef`,
  `bitSubsetDef`, `qqVerumDef/qqAndDef/qqOrDef/qqAllDef/qqExsDef` (Σ₀), `negGraph`,
  `substs1Graph`, `freeGraph`, `setShiftGraph`, `(isSemiterm L).sigma/.pi`,
  `(isFormulaSet L).sigma/.pi`, and `T.Δ₁ch.sigma/.pi` — for `T = TAct` the Δ₁ recognizer of
  `PA ∪ {axAct, axAct', axNe, axNe'}` (`TheoryAct.lean:25-48`, built from `𝗣𝗔.Δ₁`,
  `Incompleteness/Definability.lean:1070`, with `Theory.Δ₁.insert`).
* `construction T : Fixpoint.Construction V (blueprint T)` (:417), `monotone` (:420), and the
  `StrongFinite` instance (:437): every premise code is `< d` (`dp_lt_andIntro` etc.).

### 1.2 How the fixpoint is defined (`Arithmetic/HFS/Fixpoint.lean`)

```lean
structure Blueprint (k : ℕ) where core : 𝚫₁.Semisentence (k + 2)                       -- :25
def succDef : 𝚺₁.Semisentence (k + 3) := .mkSigma
  “u ih s. ∀ x < u + (s + 1), (x ∈ u → x ≤ s ∧ !φ.core.sigma x ih ⋯) ∧ (x ≤ s ∧ !φ.core.pi x ih ⋯ → x ∈ u)”   -- :34-35
def prBlueprint : PR.Blueprint k where zero := .mkSigma “x. x = 0”; succ := φ.succDef            -- :37-39
def limSeqDef : 𝚺₁.Semisentence (k + 2) := (φ.prBlueprint).resultDef                            -- :41 (PR.resultDef: HFS/Vec.lean:356)
def fixpointDefΔ₁ : 𝚫₁.Semisentence (k + 1) := .mkDelta
  (.mkSigma “x. ∃ L, !φ.limSeqDef L (x + 1) ⋯  ∧ x ∈ L”)
  (.mkPi    “x. ∀ L, !φ.limSeqDef L (x + 1) ⋯  → x ∈ L”)                                        -- :46-48
class Construction.StrongFinite … strong_finite : c.Φ v C x → c.Φ v {y ∈ C | y < x} x          -- :62-63
def Fixpoint (x : V) : Prop := ∃ s, x ∈ c.limSeq v s                                              -- :184
lemma fixpoint_iff [c.StrongFinite] : c.Fixpoint v x ↔ x ∈ c.limSeq v (x + 1)                     -- :188
theorem case [c.Finite] : c.Fixpoint v x ↔ c.Φ v {z | c.Fixpoint v z} x                          -- :222
theorem induction [c.StrongFinite] {P} (hP : Γ-[1]-Predicate P) (H : ∀ C, (∀ x ∈ C, Fixpoint x ∧ P x) → ∀ x, Φ C x → P x) : ∀ x, Fixpoint x → P x   -- :256
```

So `Derivation T d` (`Proof/Basic.lean:465`, `:= (construction T).Fixpoint ![]`) means: `d` is
in the stage set `limSeq (d+1)`, the `(d+1)`-th iterate of the primitive-recursive stage
operator `succ s ih := {x ≤ s | Φ {z ∈ ih} x}` (the whole set of derivation codes `≤ d`, coded
as ONE hereditarily-finite set). The Σ₁ form of `Derivation d` is therefore

`derivation.sigma d  ≡  ∃ L, limSeqDef L (d + 1) ∧ d ∈ L`

(with `limSeqDef` a PR-result formula: "there is a sequence `⟨L₀, …, L_{d+1}⟩` with `L₀ = ∅`,
each `L_{i+1} = succ i L_i`, and `L = L_{d+1}`"). The witness `L` is a set whose magnitude is at
least `exp d` — this is what makes naive Σ₁-completeness hopeless (§2), and it is why the design
below never unfolds `derivation` at all.

### 1.3 The predicates, and which form the package's box uses

```lean
def Derivation : V → Prop := (construction T).Fixpoint ![]                                        -- Proof/Basic.lean:465
def DerivationOf (d s : V) : Prop := fstIdx d = s ∧ Derivation T d                                -- :467
def Proof (d φ : V) : Prop := DerivationOf T d {φ}                                                 -- :471
noncomputable def derivation : 𝚫₁.Semisentence 1 := (blueprint T).fixpointDefΔ₁                   -- :475
noncomputable def derivationOf : 𝚫₁.Semisentence 2 := .mkDelta
  (.mkSigma “d s. !fstIdxDef s d ∧ !(derivation T).sigma d”) (.mkPi “d s. !fstIdxDef s d ∧ !(derivation T).pi d”)   -- :477-479
noncomputable def proof : 𝚫₁.Semisentence 2 := .mkDelta
  (.mkSigma “d φ. ∃ s, !insertDef s φ 0 ∧ !(derivationOf T).sigma d s”)
  (.mkPi “d φ. ∀ s, !insertDef s φ 0 → !(derivationOf T).pi d s”)                                  -- :484-486
```

The package (FACT):

* `LenDerivable T k φ := ∃ d, Proof T d φ ∧ dlen T d ≤ k` (`CutV.lean:158`);
  `lenDerivableDef := .mkSigma “k φ. ∃ d, !(proof T).sigma d φ ∧ ∃ n, !(dlenDef T) n d ∧ n ≤ k”`
  (`CutV.lean:383-384`) — the **`.sigma`** of `proof`.
* `dlenDef := .mkSigma “n d. (!(derivation T).pi d → !(dlenGraphDef L).sigma d n) ∧ (¬!(derivation T).sigma d → n = 0)”`
  (`DerivationLength.lean:404-405`) — mentions BOTH polarities of `derivation T`;
  `dlenGraphDef` is the Δ₁ fixpoint formula of the length graph (`:82`), whose per-tag inversion
  clauses are `DlenGraph.axL_iff` … `DlenGraph.cutRule_iff` (`:135-181`).
* `instB n k := subst LAct (bnum k ∷ 0) n` (`InstV.lean:85`), Σ₁ graph
  `instBGraph := “y n k. ∃ t, !bnumGraph t k ∧ ∃ v, !adjoinDef v t 0 ∧ !(substsGraph LAct) y v n”` (`:90-91`);
  `bewB a n k := LenDerivable TAct a (instB n k)` (`:148`),
  `bewBDef := “a n k. ∃ g, !instBGraph g n k ∧ !(lenDerivableDef TAct) a g”` (`:151-152`).
* `gBudget k := ‖k‖ * ‖k‖`, `gGraph := “y k. ∃ l, !lengthDef l k ∧ y = l * l”` (`Assembly/Prep.lean:554-557`);
  `boxCore := “n k. ∃ a, !gGraph a k ∧ !bewBDef a n k”` (`:567`), `boxCoreA := lMap emb boxCore` (`:570`),
  `Box_g χ := boxCoreA ⇜ ![Semiterm.lMap emb (⌜χ⌝ : ArithmeticSemiterm Empty 1), #0]` (`:575-579`),
  where `⌜χ⌝` is Foundation's `Semiterm.Operator.encode` = the UNARY numeral of `encode χ`
  (`Arithmetic/Basic/Misc.lean:103-113`, `Basic/Operator.lean:156-158`; the docstring at
  `Prep.lean:36` says so explicitly).

**The target sentence, fully unfolded.** `instB ⌜Box_g χ⌝ k` is the code of the `LAct`-sentence

```
∃ a ((∃ l, lengthDef l k̄ ∧ a = l·l)
  ∧ ∃ g' ((∃ t, bnumGraph t k̄ ∧ ∃ v, adjoinDef v t 0 ∧ substsGraph g' v ⌜χ⌝)                    -- instBGraph g' ⌜χ⌝ k̄
      ∧ ∃ d ((∃ s, insertDef s g' 0 ∧ fstIdxDef s d ∧ ∃ L, limSeqDef L (d+1) ∧ d ∈ L)              -- proof.sigma d g'
          ∧ ∃ n (((derivation.pi d → dlenGraphDef.sigma d n) ∧ (¬ derivation.sigma d → n = 0))     -- dlenDef n d
                 ∧ n ≤ a))))
```

with `k̄ = bnum k` (a binary numeral term, `O(‖k‖)` symbols) and `⌜χ⌝` the unary numeral of
`encode χ` (≈ `encode χ` symbols, i.e. at least exponential in `flen χ` since Cantor tuples
square at each nesting level). ANALYSIS: any proof of this sentence has
`dlen ≥ 1 + formulaLen(target) ≥ encode χ` — see §4.4.

### 1.4 Is there an internal `case` lemma provable as ONE sentence? (FACT + ANALYSIS)

`Derivation.case_iff` (`Proof/Basic.lean:543-558`) and the introduction lemmas
`Derivation.axL` (:603), `verumIntro` (:606), `andIntro` (:610), `orIntro` (:616),
`allIntro` (:622), `exsIntro` (:629), `wkRule` (:637), `shiftRule` (:643), `cutRule` (:649),
`axm` (:657) are Lean theorems about an arbitrary `V ⊧* 𝗜𝚺₁`. Each introduction lemma, read
as a sentence of ℒₒᵣ with `Derivation` written as `(derivation T).sigma`, e.g.

`Intro_and :≡ ∀ s p q dp dq, IsFormulaSet s → (∃ r, qqAndDef r p q ∧ r ∈ s) → (∃ c, fstIdxDef c dp ∧ insertDef c p s) → derivation.sigma dp → (∃ c, fstIdxDef c dq ∧ insertDef c q s) → derivation.sigma dq → ∃ e, andIntroGraph e s p q dp dq ∧ derivation.sigma e`

is TRUE in every model of `𝗜𝚺₁` (the lemma + `eval_fixpointDefΔ₁`, `Fixpoint.lean:251`), hence
`𝗜𝚺₁ ⊢ Intro_and` by `complete` (`Arithmetic/Basic/Model.lean:78`; for `TAct` over `LAct` by
`lMap emb` and `tact_complete`/`tact_complete'`, `Diag.lean:176/203`). Its PROOF is a
`Nonempty` from the completeness theorem: no derivation object, but SOME length `N_and : ℕ`
exists (`Prep.lean:685 lenDerivable_of_proof`, then Σ₁-upward transfer `lenDerivable_of_nat`
`:671`). The same holds for the full `∀ d, derivation.sigma d ↔ (clauses)` if wanted; the
construction only needs the ten intro directions. **So yes: one universal sentence per tag,
provable in `TAct`, with an existential constant length.**

Size of the sentence (ANALYSIS): it contains `derivation TAct` three times, and
`|derivation TAct| = |fixpointDefΔ₁| ≈ 2·|limSeqDef| ≈ 2·(|PR.resultDef| + 2·|succDef|)`, with
`succDef ⊃ core.sigma + core.pi` = the full ten-clause blueprint of `Proof/Basic.lean:351-410`,
which embeds `negGraph`, `substs1Graph`, `freeGraph`, `setShiftGraph` (each itself a fixpoint
`resultDef`) and `TAct.Δ₁ch` (PA's induction-schema recognizer). A fixed number, plausibly
`10⁴–10⁶` symbols; it enters `E` only as the multiplicative constant `e*` (Critch's), never as a
function of `a`. Comment at `Proof/Basic.lean:495` ("Proving this by `rfl` overflows memory")
is the warning that Lean-side manipulation of these formulas must stay symbolic.

## 2. Foundation's internal Σ₁-completeness — and why it cannot be reused (FACT, then ANALYSIS)

`DerivabilityCondition/D3.lean`:

* `term_complete` (:48-73): Lean structural recursion on the META term `t`; at `+`/`*` it glues
  two internal codes with `subst_add_eq_add … ⨀ ih₀ ⨀ ih₁` and `numeral_add T _ _`
  (`PeanoMinus.lean:60`, proved by `sigma1_pos_succ_induction` INSIDE `V`, i.e. an internal
  proof of `𝕹 n + 𝕹 m ≐ 𝕹 (n+m)` whose size is not tracked). Every value is written as the
  internal UNARY numeral `𝕹 (t.valb w)` (`numeral`, `Term/Functions.lean:744`).
* `bold_sigma_one_complete` (:76-167): `sigma₁_induction'` on the META formula `φ`; cases
  `hEQ/hNEQ/hLT/hNLT` = `term_complete` + `numeral_ne/lt/nlt` (`PeanoMinus.lean:131-171`);
  `hAnd` = `K_intro`; `hOr` = `A_intro_left/right`; `hBall` = `ball_intro` (`PeanoMinus.lean:231`)
  + `ball_replace`; `hExs` = `TProof.exs! (𝕹 i)` with `i` the TRUE witness in `V`, written as a
  unary numeral.
* `ball_intro φ n bs` (`PeanoMinus.lean:231-247`): `φ.ball (𝕹 n)` from `n` sub-proofs
  `φ[𝕹 i]`, `i < n`, via `lt_iff_substItrDisj` (`:190-229`): `t <' 𝕹 n ↔ (t ≐ 𝕹 0) ⋎ … ⋎ (t ≐ 𝕹 (n-1))`,
  a disjunction of `n` disjuncts built by `sigma1_pos_succ_induction` in `V`, then
  `substItrDisj_left_intro` case-splits it. `bexs_intro` (`:249`) = `exs! (𝕹 i)` + `numeral_lt`.

**Cost (ANALYSIS).** A bounded `∀ x < n̄` costs `n` sub-proofs plus a disjunction formula of size
`Θ(n · |𝕹 n|) = Θ(n²)` symbols — exponential in `‖n‖`; an `∃` writes its witness as a unary
numeral of the witness's MAGNITUDE. For our sentence (§1.3) the witnesses are
`d = ρ` (magnitude `≤ FV(12·dlen ρ)` by `ProperV.lean:731 derivation_le_FV_dlen`, and
`≥ exp(⌜g'⌝) ≥ 2^{2^{Ω(|g'|)}}` from `Sequent.quote = ∑ exp ⌜φ⌝`, `Proof/Coding.lean:21`, and the
squaring pairing), `L = limSeq(d+1)` (larger still), `s = {g'}`, and every sub-code down the
tree; the Δ₀ matrix contains bounded quantifiers `∀ x < u + (s+1)` (`succDef`) over ranges of
that magnitude. So `bold_sigma_one_complete` applied to `instB ⌜Box_g χ⌝ k` produces an internal
proof of length at least `exp(exp(g))`-scale, i.e. `E(a) ≥ 2^{2^a}`. It also tracks NO length
(`TDerivation.and/or/all/exs`, `Typed.lean:242-255`, go through `Derivable.toTDerivation` and
lose the code equation — `READ_foundation_calculus.md` §2.3). **Not reusable, by a doubly
exponential margin.** What IS reusable: its OUTPUT TYPE — it builds internal codes
`T.internalize V ⊢ …` (elements of `V`), which is exactly what `verifyCode ρ` must be; only the
method (eigenvariables instead of numerals, explicit `cutRule`/`allIntro` codes instead of the
untracked typed constructors) changes.

## 3. The eigenvariable construction, node by node (ANALYSIS, built on the FACTs above)

### 3.1 Vocabulary of the verification proof

All reasoning is one-sided LK on codes (Foundation's ten rules), inside `TAct`, on sequents that
are finite SETS (`insert` on bit-sets, `Exponential/Bit.lean:227-243`: `insert x s = s` when
`x ∈ s`). Two primitive moves:

* **Use a library lemma `Λ = ∀ x̄, B(x̄)`** at eigenvariables `ē` in context `Γ`: `cut` on `Λ`;
  premise (a) = the stored proof of `Λ` (length `N_Λ`, a constant) weakened to `Γ, Λ` by one
  `wkRule` (cost `N_Λ + |Γ| + |Λ|`); premise (b) = `Γ, ¬Λ` where `¬Λ = ∃ x̄ ¬B`, closed by
  `|x̄|` `exsIntro`s with witnesses `ē` down to the `axL` on `¬B(ē), B(ē)`, at cost
  `O(|x̄| · (|Γ| + |B| + Σ|eᵢ|))`. Net effect: `B(ē)` is added to the context. Per use:
  `O(N_Λ + |Γ| + |B|·|x̄|)` — a constant plus the current context size. (Alternative: cut `Λ`
  in ONCE at the root and keep `¬Λ` in every sequent, instantiating by `exsIntro` at each use —
  cheaper per use, but pays `|Λ| ≥ |derivation TAct|` in every sequent. Either is `O(1)` per
  use asymptotically; the first keeps subtrees self-contained, which `verifyCode` needs.)
* **∃-elimination** of a fact `∃ x, P(x)` derived by a subproof `D` (conclusion `Δ, ∃x P`):
  `cut` on `∃x P`; premise (a) = `D` weakened; premise (b) = `Γ, ∀x ¬P` closed by `allIntro`,
  whose premise is `setShift Γ, ¬P(&0)` — the fresh eigenvariable `&0`; EVERY free variable of
  `Γ` is shifted up by one (`allIntro`'s side condition `fstIdx dp = insert (free L p) (setShift L s)`).
  This shift is the source of the unary-index cost (§3.7).

Hypotheses live in the sequent as their NEGATIONS; the goal of the subtree for a `ρ`-node `ν` is

`G_ν :≡ ∃ d n, derivation.sigma d ∧ fstIdxDef s_ν d ∧ dlenGraphDef.sigma d n ∧ n ≤ ū_ν`

with `s_ν` an eigenvariable already in scope (the node's sequent) and `ū_ν = bnum(dlen ν)` a
BINARY numeral (`O(‖g‖)` symbols; §4). Context of that subtree = the negated LIVE FACTS about
`s_ν`: `IsFormulaSet s_ν`; for each formula `r` of `s_ν` that is principal somewhere in `ν`'s
subtree ("live"), `r ∈ s_ν` plus the SHAPE facts of `r` and of whichever of its subformulas are
decomposed below (`r = qqAnd r₁ r₂`, `r₁ = qqAll r₁₁`, …, down to atoms `r = qqRel k R v`); and
the length fact `∃ l, setLenDef l s_ν ∧ l ≤ bnum(setLen s_ν)` (§4). All of constant size, all
about VARIABLES; nothing about `s_ν` is ever written as a numeral.

**The library `Λ` (each a `TAct`-theorem via `complete`, from the cited V-lemma):**

| name | sentence | V-lemma |
|---|---|---|
| `Intro_tag` (10) | §1.4 | `Derivation.axL … axm`, `Proof/Basic.lean:603-660` |
| `Dlen_tag` (10) | `∀ s p q dp dq np nq l, dlenGraph dp np → dlenGraph dq nq → setLenDef l s → ∃ n, n = l+np+nq+1 ∧ dlenGraph (andIntro …) n` etc. | `DlenGraph.*_iff`, `DerivationLength.lean:135-181` |
| totality | `∀ x y ∃ z, insertDef z x y`; `∀ p q ∃ r, qqAndDef r p q` (and `qqOr/qqAll/qqExs/qqRel/qqNRel/qqVerum`); `∀ p ∃ y, negGraph y p`; `∀ t p ∃ y, substs1Graph y t p`; `∀ p ∃ y, freeGraph y p`; `∀ s ∃ y, setShiftGraph y s`; `∀ p ∃ y, shiftGraph y p`; `∀ k ∃ t, bnumGraph t k`; `∀ s ∃ l, setLenDef l s`; `∀ p ∃ l, formulaLenGraph l p`; `∀ s p q dp dq ∃ e, andIntroGraph e s p q dp dq` (10 node graphs); `∀ t v ∃ v', adjoinDef v' t v` | totality of Foundation's functions on `V` (all are `Classical.choose!`/`construction.result`, defined everywhere) |
| sets | `x ∈ insert x s`; `x ∈ s → x ∈ insert y s`; `s ⊆ insert x s`; `s ⊆ t → x ∈ t → insert x s ⊆ t`; `∅ ⊆ s`; `x ∈ s → insert x s = s`; `IsFormulaSet ∅`; `IsFormulaSet s → IsFormula p → IsFormulaSet (insert p s)`; `y ∈ s → shift y ∈ setShift s`; `y ∈ setShift s → ∃ x ∈ s, y = shift x`; `IsFormulaSet s ↔ IsFormulaSet (setShift s)` | `mem_bitInsert_iff` (`Bit.lean:241`), `HFS/Basic.lean:24`, `IsFormulaSet.insert_iff/empty` (`Proof/Basic.lean:30-40`), `mem_setShift_iff` (:82), `shift_mem_setShift` (:97), `setShift_iff` (:106) |
| formulas | `IsFormula p → IsFormula q → IsFormula (qqAnd p q)` (…all constructors); `neg (qqAnd p q) = qqOr (neg p) (neg q)` (…); `subst w (qqAnd p q) = qqAnd (subst w p) (subst w q)` (…); `shift (qqAnd p q) = qqAnd (shift p) (shift q)` (…); the same for `free`; `IsFormula p → IsTerm t → IsFormula (substs1 t p)`; injectivity/shape-inversion `shift r' = qqAnd p q → ∃ p' q', r' = qqAnd p' q' ∧ p = shift p' ∧ q = shift q'` (needs `IsFormula r'`) | `neg_and/neg_or` (`Formula/Functions.lean:88-91`), `substs_rel/and/or/all/ex` (:456-475), `shift_and` (:303), `IsSemiformula.case_iff` (`Formula/Basic.lean:1302`) |
| lengths | `setLen (insert x s) ≤ setLen s + formulaLen x`; `setLen ∅ = 0`; `formulaLen (qqAnd p q) = formulaLen p + formulaLen q + 1` (…); `termLen (qqFunc k f v) = …`; the binary-numeral laws `bnum a + bnum b = bnum (a+b)` as bit-recursion lemmas (`NumeralFacts.lean` pattern) | `setLen_insert_le` (`CutV.lean:130`), `setLen_empty/singleton` (:135-138), `formulaLen_*` (`Length.lean:206-235`), `termLen_*` (:96-104) |
| axioms | `p = ⌜ax⌝ → TAct.Δ₁ch.sigma p` for each of the finitely many non-schema axioms; for the induction schema see §3.6 | `Δ₁Class.mem_iff` (`Theory.lean:85`), `𝗣𝗔.Δ₁` (`Definability.lean:1070`) |

The library is FINITE and independent of `ρ`, `χ`, `k`. Every lemma is used `O(g)` times at
cost `O(1) + O(|context|)`.

### 3.2 Where formula codes come from (the one level down)

Every formula in every sequent of `ρ` is one of:

1. **A subformula-instance of the root formula** `g' = instB ⌜χ⌝ k = subst (t ∷ 0) ⌜χ⌝` (its
   `and`/`or`/`all`/`exs`-descendants along `ρ`'s decompositions, and their `free`/`substs1`
   instances). Describe these ABSOLUTELY, not by a chain: at the top of the proof, introduce once
   `t` (`bnumGraph t k̄`), `v = t ∷ 0`, and eigenvariables `c_i` for the `|χ|` subformula codes
   with the numeral facts `c_i = ⌜χ_i⌝` — then prove the SHAPE facts `c_i = qqAnd c_j c_l`,
   `c_i = qqAll c_j`, … ONCE (they are Δ₀ identities between unary numerals: cost `N_χ`, a
   constant of the family, at least `encode χ` — the same order as the target sentence itself,
   §4.4) and `wk` the numeral facts away. Downstream, `g'_i = subst v c_i` are introduced by the
   `substsGraph` totality lemma and their shapes follow from `substs_and` etc. (`Functions.lean:466-475`)
   and the shape facts of `c_i`; the substituted variable `#0` becomes `t`, whose shape is never
   needed (terms are only ever compared for `IsTerm`, never decomposed, §3.3 exs). Cost `O(1)`
   per decomposition step; no numeral is ever re-written.
2. **An arbitrary (possibly nonstandard) formula** entering by `cut` (the cut formula), `wk`
   (any formula of the bigger sequent), `axm` (an axiom instance), or `shift`. Describe it
   BOTTOM-UP by its syntax tree with one eigenvariable per node: `∃ z, qqRelDef z k̄ R̄ v̄`
   (symbol codes are small numerals — `SmallCodesV`, `ProperV.lean`: every `LAct` symbol code
   `≤ 8`), `∃ v', adjoinDef v' z v`, `∃ y, qqAndDef y a b`, … — ONE totality-lemma use per symbol
   of the formula (and per symbol of each term inside it), so `O(|r|)` uses for a formula of
   `formulaLen r`; `IsFormula r` comes for free from the same walk (`IsFormula` intro lemmas).
   The node of `ρ` that introduces `r` is charged `formulaLen r` by `dlen` (it is in its
   sequent), so this is `O(1)` per unit of `ρ`'s own length.

So the whole proof is a bottom-up description of `ρ`'s syntax with `O(1)` library uses per
symbol of `ρ` — the "same trick one level down" the brief asks about, confirmed.

### 3.3 The fragment per tag

Notation: `Γ_ν` = live context of `ν` (negated); the subtree derives `Γ_ν, G_ν`. "Get `x`" =
∃-eliminate a totality lemma. "Cut `Λ[ē]`" = §3.1 first move. Children's subtrees are cut in as
`∃ d₁ n₁ …` and eliminated. For each child `ν'` we must FIRST build the child's context
`Γ_{ν'}` (its sequent eigenvariable and live facts), THEN run the child's subtree, THEN
eliminate its conclusion.

* **`axL s p`** (leaf). Live facts: `p ∈ s`, `np ∈ s` with `negGraph np p` (the shape of `p` is
  not needed: `np` is obtained from the totality of `neg`, and `np ∈ s` is a live fact of the
  formula `neg p` — which, being a member of `s`, has been described at ITS introduction, and
  the identity "that member IS `neg p`" is one `neg_*` shape lemma at the top constructor:
  `neg (qqAnd a b) = qqOr (neg a) (neg b)` — recursive down `p` if the two descriptions differ
  in depth; `O(|p|)`, paid by `ρ` at this node). Cut `Intro_axL[s, p]` → get `e` with
  `axLGraph e s p ∧ derivation.sigma e`; cut `Dlen_axL[s, l]` with the length fact of `s` → `n`;
  `∃`-introduce. Cost `O(1)` uses.
* **`verumIntro s`**: `vrm ∈ s` with `qqVerumDef vrm` (a member described as `⊤` at its
  introduction). Same shape.
* **`andIntro s p q dp dq`**: live: `r ∈ s`, `r = qqAnd p q` (the shape fact of the principal —
  here the DECOMPOSITION happens: `p`, `q` are the eigenvariables of `r`'s shape fact, which is
  in `Γ_ν` because a descendant uses `p` or `q`; if neither is ever principal below, the shape
  fact is still needed for `Intro_and`, so it is live by definition). Get `s₁ = insert p s`,
  `s₂ = insert q s` (totality of `insertDef`). Build `Γ_{ν₁}`: `IsFormulaSet s₁` (lemma from
  `IsFormulaSet s` + `IsFormula p`, the latter from `p`'s shape or the `IsFormula`-part of
  `r`'s description); transport every live fact `x ∈ s` needed below `ν₁` to `x ∈ s₁`
  (`x ∈ s → x ∈ insert p s`), and `p ∈ s₁` (`x ∈ insert x s`); length: `setLen s₁ ≤ setLen s +
  formulaLen p` (`setLen_insert_le`) — with the numeral bookkeeping of §4. Run the `ν₁` subtree,
  eliminate `d₁ n₁`; same for `ν₂`. Cut `Intro_and[s, p, q, d₁, d₂]` (its hypotheses
  `∃ c, fstIdxDef c dp ∧ insertDef c p s` are exactly `fstIdxDef s₁ d₁` and the `s₁`-fact);
  cut `Dlen_and`; conclude. Uses: `O(1)` + `O(#live facts transported)`.
* **`orIntro s p q d`**: as `and` with `s' = insert p (insert q s)` (two `insert`s) and one
  child.
* **`allIntro s p d`**: live: `r ∈ s`, `r = qqAll p`. Get `fp` (`freeGraph fp p`), `ss`
  (`setShiftGraph ss s`), `s' = insert fp ss`. `Γ_{ν'}`: `IsFormulaSet ss` (`setShift_iff`),
  `IsFormulaSet s'`; every live fact `x ∈ s` becomes `x' ∈ ss` with `x' = shift x` (get `x'`
  by totality, membership by `shift_mem_setShift`), and the shape facts of `x` are transported to
  `x'` by `shift_and/…` (one lemma per shape fact — `O(Σ |live shapes|) ≤ O(setLen s)`); the
  shape of `fp` from `p`'s by the `free`-commutation lemmas (`free p = substs1 (&0) (shift p)`,
  `Formula/Typed.lean:240`). This is where the decomposed formula's syntax is REBUILT after a
  substitution — `O(|p|)`, paid by `ρ` (the child's sequent contains `fp`).
* **`exsIntro s p t d`**: live: `r ∈ s`, `r = qqExs p`, and the WITNESS TERM `t` must be
  introduced here: describe `t` bottom-up (§3.2(2), `O(termLen t)` — exactly `ρ`'s extra charge
  at this node, `DLen.Phi`'s `termLen L t` summand), which also yields `IsTerm t`. Get
  `pt` (`substs1Graph pt t p`), `s' = insert pt s`; shapes of `pt` from those of `p` via
  `substs_*` (atoms: `substs_rel` gives `qqRel k R (termSubstVec …)` — the term vector is a new
  eigenvariable from the `termSubstVec` graph's totality; its inside is never needed).
* **`wkRule s d'`**: `ρ`'s CHILD sequent `s'` is a SUBSET; the child's live facts are about `s'`
  and must hold there: describe `s'` by the exact insert-chain of its members (each member a
  formula eigenvariable already in scope, since `s' ⊆ s`), prove `s' ⊆ s` by `|s'|` uses of
  `s ⊆ t → x ∈ t → insert x s ⊆ t` from `∅ ⊆ s`. Members of `s` that are NOT in `s'` were
  described (§3.2(2)) when `s` was built — `wk` is the rule that INTRODUCES arbitrary formulas.
  Cost `O(|s'|)` uses, `≤ O(setLen s)`.
* **`shiftRule s d'`**: `s = setShift s'` where `s'` is the child's sequent. The live facts flow
  DOWN (from `ν`'s ancestors to its descendants), so we have `x ∈ s` and need `x' ∈ s'` with
  `x = shift x'`: `mem_setShift_iff` (backward direction) gives `x'`; the shape facts of `x`
  transfer to `x'` by the shape-INVERSION lemmas (`shift r' = qqAnd p q → …`, which need
  `IsFormula r'` — available from `IsFormulaSet s'`, itself from `IsFormulaSet s` by
  `setShift_iff`). `O(Σ |live shapes|)`.
* **`cutRule s p d₁ d₂`**: the cut formula `p` is NEW: describe it bottom-up (§3.2(2),
  `O(|p|)`); get `np` (`negGraph`), `s₁ = insert p s`, `s₂ = insert np s`; `np`'s shapes from
  `p`'s by `neg_*`. Two children as in `and`.
* **`axm s p`**: live: `p ∈ s`, and `TAct.Δ₁ch.sigma p` must be PROVED for the
  eigenvariable-described `p` — §3.6.

The **dlen output** of every fragment is `n ≤ ū_ν` with `ū_ν` binary, §4.

### 3.4 Membership and subset facts without writing codes — the transport discipline

Every side condition of `Intro_tag` is a Δ₀ fact about the specific eigenvariables. They are
NEVER established by evaluating anything; each is a constant-size consequence of how the
sequent was BUILT: `p ∈ insert p s`, `x ∈ s → x ∈ insert p s`, `s ⊆ insert p s`,
`IsFormulaSet (insert p s) ← IsFormulaSet s ∧ IsFormula p`, `shift x ∈ setShift s ← x ∈ s`. The
only question is WHICH facts are carried in which sequent, because `dlen` charges every
formula of every sequent (`DLen.Phi`, `DerivationLength.lean:31-46`: every node pays
`setLen s + 1`). The discipline:

* A fact is carried in a subtree iff it is used in that subtree (live). Dead facts are dropped
  by `wkRule` at the subtree root (one node, cost = the sequent once).
* Facts about the PARENT's sequent variable are transported to the CHILD's at the child's root
  (one library use per fact), so no sequent ever mentions two different sequent variables
  except during that transport. In particular the insert-CHAIN description `s_{i+1} = insert p_i s_i`
  of the ancestors is NOT carried down; only `x ∈ s_ν` facts are.
* Formula eigenvariables and their shape facts are long-lived (from the formula's introduction
  to its last decomposition).

With `L_ν` = number of live facts at `ν` (`≤` the number of formulas in `s_ν` plus their live
shape facts, so `L_ν ≤ setLen s_ν ≤ w_ν`, where `w_ν := 1 + setLen s_ν (+ termLen t)` is `ν`'s
own `dlen` charge), a fragment makes `O(w_ν)` library uses, each with a context of `O(L_ν)`
constant-size formulas: **`O(w_ν · L_ν) ≤ O(w_ν²)` symbols per node, before the index cost.**
Summed, `Σ_ν w_ν² ≤ (Σ_ν w_ν)² = g²`.

Why this is not linear (ANALYSIS): the `L_ν` transports are separate cuts and each cut node's
sequent carries all `L_ν` facts. A cut has both premises in the FULL context (Foundation's
`cutRule s p d₁ d₂`: `fstIdx d₁ = insert p s`, `fstIdx d₂ = insert (neg p) s`); contexts can
shrink going up (`wk`) but never grow, so a fact needed in a sub-proof must be present at the
sub-proof's root. Packing the `L_ν` facts into one conjunction of size `O(L_ν)` changes nothing
(`L_ν` ∧-eliminations, each with the `O(L_ν)`-size conjunction in context). A balanced binary
split of the facts (each cut premise keeps only the half it needs) brings the per-node cost to
`O(w_ν log w_ν)` but complicates `verifyCode` for a `log` factor; not worth it while the index
cost (§3.7) is a factor `g` anyway.

### 3.5 Formulas with `#0`, substitution, and the decomposition sites

`subst` is handled entirely through its Σ₁ graph and the commutation lemmas: a substituted
formula is a NEW eigenvariable `y` with `substsGraph y w p` (or `substs1Graph y t p`), and its
shape facts are derived from `p`'s by `substs_and` (`Functions.lean:466`), `substs_or`,
`substs_all/ex` (with the pushed vector `qVec w`, again by totality), `substs_rel/nrel` (:456-459).
The recursion stops at atoms; term vectors inside atoms are opaque eigenvariables. The same
pattern serves `neg` (`neg_and/neg_or`, :88-91; `neg (qqRel …) = qqNRel …`), `shift`
(`shift_and`, :303) and `free`. No formula code is ever compared symbol-by-symbol EXCEPT when
`ρ` inserts a formula that is already in the sequent (`insert p s = s`) and the dlen
bookkeeping needs `p ∈ s` (§4.2) — then the V-generic construction knows which member `x` of
`s` equals `p` and proves `p = x` by walking the two shape descriptions in parallel
(`qqAnd a b = qqAnd a' b' ← a = a' ∧ b = b'`, `O(|p|)`).

### 3.6 The `axm` leaf — the one library item with a non-obvious cost

`Intro_axm` needs `TAct.Δ₁ch.sigma p` for an eigenvariable `p`. `TAct.Δ₁` (`TheoryAct.lean:25-48`)
is `Theory.Δ₁.insert` four times over `(Theory.lMap emb 𝗣𝗔).Δ₁`, whose `ch` is PA's recognizer
conjoined with "is an ℒₒᵣ-formula" (`isFormulaOR`, `:8`). For the four action sentences and the
finitely many `𝗣𝗔⁻`/`𝗘𝗤` axioms, `p = ⌜ax⌝ → Δ₁ch.sigma p` are constant lemmas whose use costs
the unary numeral `⌜ax⌝` once per use — a constant per `axm` node, fine. For an INDUCTION
INSTANCE the recognizer (`Incompleteness/Definability.lean:1070` `𝗣𝗔.Δ₁`, built from the
`succInd`/`indScheme` formulas of `Arithmetic/…/PeanoMinus`-`ISigma` definability files) says
"`∃ φ < p, IsSemiformula 1 φ ∧ p = (the induction sentence of φ)`" with the sentence built by
`substs`/`qqAll`/`imp` constructions of `φ`. The verification proof must: exhibit `φ` (an
eigenvariable — it is a sub-syntax of `p`, hence already described), and prove
`p = indSentence(φ)` by the same commutation-lemma walk as §3.5 — `O(|φ|) ≤ O(|p|)` uses,
paid by `ρ` at the node. **Risk**: this presumes the recognizer is written through the graphs
of `subst`/`qqAll`/… on codes (so that its clauses have constant-size intro lemmas); if it goes
through `substNumeral`-style or `Semiformula`-typed detours, the walk needs extra bridging
lemmas. To be checked against `Definability.lean` before the library is written — it is the
only place where the SHAPE of a Foundation definition (rather than its truth) decides a cost.

### 3.7 The bound `E(g)`, and why it is not linear

Per node `ν` the fragment has `O(w_ν)` library uses; each use is `O(1)` nodes of the
verification proof, each node's sequent has `O(L_ν)` formulas, each formula has `O(1)` symbols
PLUS its variable occurrences, each charged `index + 1` (`Length.lean:100-102 termLen_bvar/fvar`,
docstring `:16-19`: "variable indices are charged unary … Critch's assumption (b) is therefore
NOT met by the raw ℒₒᵣ coding; a cost-faithfulness item"). An eigenvariable introduced `D`
∃-eliminations ago has index `D` (every `allIntro` shifts the whole sequent). Along a
root-to-leaf path of the verification proof, `D ≤ Σ_{ancestors α of ν} O(w_α) ≤ g`. Hence:

* per node: `O(w_ν · L_ν · (1 + D_ν)) ≤ O(w_ν² · g)`;
* total: **`E(g) ≤ C · g³`** in the worst case (a deep, wide `ρ`), `C` dominated by
  `|derivation TAct|` (every `derivation.sigma dᵢ` in a context costs that many symbols);
* `O(g²)` if variable indices were charged `‖index‖` (binary — a `Length.lean` decision the
  file already flags as a T3 item) OR if long-lived variables are periodically refreshed
  (`∃ x', x' = x`, then re-derive the live facts — `O(L_ν)` per refresh; keeps `D = O(w_ν)`);
* `O(g)` is NOT reachable in Foundation's calculus as coded: (i) `L_ν` facts × `L_ν`-size contexts
  (§3.4); (ii) unary indices under `setShift`; (iii) formula shape facts re-derived after every
  `shift`/`subst`. Critch's `e*·k` (2019 Property 4) presupposes an abbreviation mechanism, as
  the brief's own parenthetical on Property 1 ("`c` constant WITH abbreviations") records.

For PBLT any polynomial is enough (`BRIEF.md` §6 master inequality:
`g k + N₁ + E(g k) + c·(…) ≤ k` with `g k = ‖k‖²`, so `E(g) = ‖k‖⁶ ≺ k`). Recommended target:
**state `BoundedInnerNec` with `d = 3`** and prove it with the plain discipline; tighten later
if the paper wants `d = 2`.

## 4. The `dlen` clause and the final existential

### 4.1 The length of each node as a binary numeral

Every fragment concludes `dlenGraphDef.sigma d n ∧ n ≤ ū_ν` where `ū_ν := bnum (dlen ν)` is
the binary numeral (`Bnum.lean:320`, `bnumT`, `NumeralFacts.lean`) of the TRUE length of the
sub-derivation (a `V`-element `≤ g`, so `O(‖g‖)` symbols). Recurrence at an `and` node:
`Dlen_and[s, p, q, d₁, d₂, n₁, n₂, l]` gives `n = l + n₁ + n₂ + 1`; with the live facts
`n₁ ≤ ū₁`, `n₂ ≤ ū₂`, `l ≤ ū_l` and the bit-recursion lemmas
`bnum a + bnum b = bnum (a + b)` (`O(‖a‖ + ‖b‖)` uses of `∀ x y, …` laws on `2x`, `2x+1`;
`NumeralFacts.lean:21-26` is the existing pattern: `∀ x, c ≤ x → c ≤ 2x`, `… ≤ 2x + 1`,
instantiated bit by bit) we get `n ≤ bnum(dlen ν)`. Cost `O(‖g‖)` per node — negligible
(`O(g ‖g‖)` total).

### 4.2 `setLen` without deciding non-membership

`l` is obtained from the totality of `setLenDef` and BOUNDED, never computed: for the child's
sequent `s' = insert p s`, `setLen s' ≤ setLen s + formulaLen p` (`CutV.lean:130
setLen_insert_le`, unconditional) with `formulaLen p ≤ bnum |p|` from `p`'s shape facts
(`formulaLen_and` etc., `Length.lean:220-235`, plus `bnum`-addition) — exact when `p ∉ s`,
which is when `ρ`'s `dlen` really grows. When `p ∈ s` (so `insert p s = s` and `dlen` does NOT
grow), the V-generic construction proves `p ∈ s` instead (§3.5, positive membership only) and
uses `x ∈ s → insert x s = s`; the bound stays exact. So every `ū_ν` equals `bnum (dlen ν)` and
no `∉` proof is ever needed. (The alternative "preprocess `ρ` into a duplicate-free `ρ'` with
`dlen ρ' ≤ dlen ρ`" is unnecessary.) `formulaLen` of root-subformula instances
`subst v c_i` is bounded through the shape facts too, with the atom-level fact
`termLen t ≤ bnum(c·‖k‖)` re-derived where used (`O(‖k‖)` per use).

### 4.3 Closing the target (the top of the proof, `O(1)` nodes of size `O(|target|)`)

1. Get `t` (`bnumGraph t k̄`, totality), `v = t ∷ 0` (`adjoinDef`), `g'` (`substsGraph g' v ⌜χ⌝`,
   totality — **the numeral `⌜χ⌝` appears here, in `O(1)` sequents**), `s₀ = insert g' ∅`
   (`insertDef s₀ g' 0`); the `c_i`/shape facts of §3.2(1) (numerals appear `O(|χ|)` times, then
   are `wk`-dropped). Establish `Γ_root = {IsFormulaSet s₀, g' ∈ s₀, shapes, setLen s₀ ≤ bnum |g'|}`.
2. `wk` the target formula out of the context; run the root fragment; eliminate `d, n` with
   `derivation.sigma d ∧ fstIdxDef s₀ d ∧ dlenGraphDef.sigma d n ∧ n ≤ bnum (dlen ρ)`.
3. `dlenDef n d` (`DerivationLength.lean:404`): its first conjunct from `dlenGraphDef.sigma d n`
   by weakening under the implication; its second from `derivation.sigma d` (the antecedent is
   refuted) — two constant steps. `proof.sigma d g'` from `insertDef s₀ g' 0 ∧ fstIdxDef s₀ d ∧
   derivation.sigma d` by one `∃`-intro on `s₀`.
4. `a`: get `l_k` with `lengthDef l_k k̄` (totality) and prove `l_k = bnum ‖k‖` by `O(‖k‖)`
   bit-recursion uses (`‖2x‖ = ‖x‖ + 1`, `‖2x+1‖ = ‖x‖ + 1`); get `a = l_k · l_k`; prove
   `bnum (dlen ρ) ≤ a` from the V-fact `dlen ρ ≤ gBudget k` by binary-numeral comparison and
   multiplication lemmas (`O(‖k‖²)` uses — absorbed in `(gBudget k)^d`).
5. `∃`-intros in order `n`, `d`, `g'`, `a`, each an `exsIntro` with an eigenvariable as witness
   (cost `|target|` per intro, `O(1)` intros), then `andIntro`s for the conjunctions; cut the
   eliminations against these.

`gGraph a k̄` and `instBGraph g' ⌜χ⌝ k̄` are literally the defining facts of the eigenvariables
`a`, `g'` (step 1, 4); nothing is evaluated.

### 4.4 FINDING: `BoundedInnerNec` as stated is refutable; restate before use

`Assembly/Prep.lean:716-720` (FACT):

```lean
structure BoundedInnerNec (d c c₁ c₀ : ℕ) : Prop where
  nec : ∀ (V) …, ∀ (χ : Semisentence LAct 1) (k : V),
    LenDerivable TAct (gBudget k) (instB ⌜χ⌝ k) →
    ∃ e, e ≤ (gBudget k) ^ d + c + c₁ * (flen χ + ‖k‖) + c₀ ∧ LenDerivable TAct e (instB ⌜Box_g χ⌝ k)
```

ANALYSIS. `Box_g χ` contains the UNARY numeral `⌜χ⌝` (§1.3), so `formulaLen (instB ⌜Box_g χ⌝ k)
≥ 2·encode χ`, and `dlen d ≥ 1 + setLen {φ} = 1 + formulaLen φ` for any proof `d` of `φ`
(`DlenGraph.*_iff`, root node). Take `χ_m := ⊤ ⋎ (⊤ ⋎ (… ⋎ ⊤))` (`m` disjuncts, no `#0`):
`instB ⌜χ_m⌝ k = ⌜χ_m⌝`, and `orIntro` over a `verumIntro` leaf proves it with
`dlen ≈ 3·flen χ_m`; so the premise holds at every `k` with `‖k‖² ≥ 3m + 4`, e.g.
`‖k‖ = ⌈√(3m+4)⌉`, where the right-hand side is `poly(m)`; but `encode χ_m` grows at least
exponentially in `m` (nested Cantor pairs square at each level). So for every `d c c₁ c₀` there
is `(χ, k)` violating `nec`: the structure is uninhabited, and `pblt_uniform (hE : BoundedInnerNec …)`
would be vacuous. The construction of §3–4 delivers instead

`∀ χ, ∃ C : ℕ, ∀ V k, LenDerivable TAct (gBudget k) (instB ⌜χ⌝ k) → ∃ e ≤ C * ((gBudget k)^3 + 1), LenDerivable TAct e (instB ⌜Box_g χ⌝ k)`

(`C` absorbs `flen (Box_g χ)`, `N_χ`, `|derivation TAct|`, the `‖k‖²`-terms via `‖k‖² ≤ gBudget k`).
This is what U8 consumes (χ = `psi` is fixed), and it is the honest shape: the constant depends
on `χ` at least through `encode χ`. Recommended restatement (task 5(0)):
`structure BoundedInnerNec (d : ℕ) : Prop where nec : ∀ χ, ∃ C : ℕ, ∀ V k, … ≤ C * ((gBudget k)^d + 1) …`,
with `poly` no longer needed. (`BRIEF.md` §6 anticipates this: "the fixed point's numeral `⌜ψ⌝`
is Foundation's UNARY numeral — an astronomical CONSTANT, harmless" — harmless only if it is
allowed into the constant.)

## 5. Lean task list (ANALYSIS; sizes are estimates for one person familiar with the package)

**5(0). Restate `BoundedInnerNec`** as in §4.4 and re-thread U8/U9 (`pblt_uniform`,
`dupoc_self_coop`). ~50 lines, half a day. Do this first: it changes what (c) must produce.

**5(a). The library `Λ` as `TAct`-theorems with existential lengths.** ~40 sentences (§3.1
table). Each: write the ℒₒᵣ-sentence in the binder DSL using the SAME Δ₁/Σ₁ formula objects
that appear in the target (`!(derivation TAct).sigma`, `!insertDef`, `!(dlenGraphDef LAct).sigma`,
`!(setLenDef LAct)`, `!bnumGraph`, `!(substsGraph LAct)`, …); prove `Eval ↔` by `simp` with the
`*.defined.iff` instances; close by `complete`/`tact_complete'` + the cited V-lemma; package the
length by `lenDerivable_of_proof` (`Prep.lean:685`) + `lenDerivable_of_nat` (`:671`) into
`∃ N, ∀ V, LenDerivable TAct N ⌜Λ⌝`. 20–40 lines each (the `Intro_tag` ones longer: the
sentence must match the fixpoint blueprint's clause shape so that `Fixpoint.Construction.case`
+ `eval_fixpointDefΔ₁` discharge it) → **1000–1500 lines, 5–8 days.** Foundation lemmas needed:
`Derivation.axL…axm` (`Proof/Basic.lean:603-660`), `Fixpoint.Construction.case/eval_fixpointDefΔ₁`
(`Fixpoint.lean:222/251`), `DlenGraph.*_iff` (package), `mem_bitInsert_iff` (`Bit.lean:241`),
`IsFormulaSet.insert_iff/setShift_iff` (`Proof/Basic.lean:40/106`), `mem_setShift_iff` (:82),
`neg_and/or`, `substs_*`, `shift_and` (`Formula/Functions.lean:88-91,303,456-475`),
`IsSemiformula.case_iff` (`Formula/Basic.lean:1302`), `setLen_insert_le` (`CutV.lean:130`),
`formulaLen_*`/`termLen_*` (`Length.lean`), `bnum_two_mul*` (`Bnum.lean:345-368`), `𝗣𝗔.Δ₁`'s
`mem_iff` (`Definability.lean:1070`) for §3.6, `complete` (`Model.lean:78`),
`Theory.Proof.complete_on_eq_models` (via `tact_complete`). Risk: §3.6 (the induction-instance
recognizer's shape); the `simp` cost of `Eval` on sentences containing `derivation TAct`
(`Proof/Basic.lean:495` warning — keep everything at the `.defined.iff` level, never unfold).

**5(b). The fragments and `verifyCode`.** Two layers:

* *Fragment codes* (Lean-level `noncomputable def`s built from the node constructors, in the
  style of `cutCode` (`CutV.lean:176-260`, ~90 lines for a 5-node code with `Proof` + `dlen`
  lemmas) and `instCode` (`InstV.lean:335-420`)): `useLemma Γ Λ ē` (§3.1 first move, `O(|ē|)`
  nodes), `elimExists Γ D` (second move), `describeFormula` (bottom-up syntax walk — itself a
  recursion on the formula code: a `UformulaRec`-style Σ₁ construction like `relabelTemplate`,
  `RelabelTemplate.lean`, 562 lines), `transportFacts`, and the ten per-tag fragments. Each
  fragment needs its `DerivationOf` proof and its `dlen` bound. **~3000 lines, 4–6 weeks.**
* *`verifyCode`*: the recursion on `ρ` is NOT structural in the `DLen` sense — the fragment
  for `ν` depends on a CONTEXT (which facts are live, the eigenvariable indices, the numerals
  `ū`), so define `verify : V → V → V` on `(ctx, d)` pairs by a `Fixpoint` on `⟪d, ctx, e⟫`
  triples with `ctx` an HFS code of the live-fact list (the `DLen` pattern:
  `DerivationLength.lean` §`Phi`/`blueprint`, existence + uniqueness by
  `Derivation.induction1 𝚺` (`Proof/Basic.lean:560`) with a Σ₁ predicate
  `∃ e, VerifyGraph d ctx e ∧ Derivation TAct e ∧ fstIdx e = … ∧ dlen e ≤ C·dlen d + …`),
  or — simpler and recommended — prove only the EXISTENTIAL `∀ ctx, WellFormed ctx d → ∃ e, …`
  by `induction1` with the fragment codes as explicit witnesses (no function `verifyCode` at
  all; the statement of U5 is existential anyway). The blueprint of the ctx/live-fact
  bookkeeping is the ugliest part: every fragment's sequents are quoted lemma sentences
  `⌜Λ⌝` with `subst` at eigenvariables and `shift`s applied (`coe_quote_eq`,
  `typed_quote_substs`, `Formula/Coding.lean:105`; `shift_substs`), and `dlen` of them must be
  bounded (`formulaLen` of a `subst`ed quote — `formulaLen_instB_le`-style lemmas,
  `InstV.lean`). **~3000–4000 lines, 6–10 weeks.** Risks: `simp` blow-ups on quoted formulas
  (Diag's kernel-numeral trap, `HANDOVER §6`); getting `IsFormulaSet` for every constructed
  sequent (all contain free variables — fine, `IsFormula = IsSemiformula 0` allows `&x`); the
  locally-nameless `allIntro` (the eliminated formula must be presented as `^∀ (neg body)` with
  `free` computed — `free_quote`, `Formula/Coding.lean:119`).

**5(c). Top-level assembly** (§4.3): ~400 lines, 1 week, after (a)(b).

**Total: ~8000 lines, 3–4 months** — the largest single item of the package by far, comparable
to the whole of M1–M3. Everything else in M4 (U8, U9) is days.

## 6. Alternatives if §3 fails or is too expensive

**(i) Craig-style abbreviation calculus.** Add to the derivation predicate a `cite` rule (a
node `⟪s, 10, j⟫` whose premise is the `j`-th previously derived sequent, with sequents shared
by REFERENCE) or a `def` rule (introduce a fresh symbol abbreviating a formula). Then the
library lemmas are cited, not repeated; facts are cited, not carried; `E` becomes linear
(Critch's system). Cost: a NEW `Derivation'` predicate (a copy of `Proof/Basic.lean` +
`Fixpoint` blueprint, ~900 lines) with soundness "`Derivation' e → ∃ d, Derivation d`" by
unfolding (exponential blow-up allowed, it is a `Prop`), and then EVERY length-carrying layer
re-done for it: `dlen'`, `ProperV'` (the towers change), `CutV'`, `InstV'`, `Prep`'s
`andLCode`, and the box `bewBDef'` — i.e. most of M2–M3 (`~3000` lines) plus the §5 work on the
new calculus. Not recommended unless the paper needs "linear" rather than "polynomial".

**(ii) Accept an exponential `E`.** With `E(a) = 2^{c·a}` and the package's `gBudget k = ‖k‖²`
the master inequality `E(g k) ≤ k` is false for all `k`. With the minimal `g(k) = A·‖k‖`
(`A` above the KNOWN instantiation coefficient — `lenProvable_inst_size`'s `6·size k`,
`InstV.lean` — so that `C + 6‖k‖ ≤ A‖k‖` eventually; the circularity with the fixed point's
constants is only through the additive `C`, so this is legitimate) one gets
`E(g k) = k^{cA}`: PBLT then needs `f(k) ≻ k^{cA}`, i.e. a searcher whose BUDGET is a
polynomial `k^m` of the parameter `k` written in its source. Not meaningless for self-play —
but it is a change of the AGENT LANGUAGE (`Prog.lean`/`Eval`: the stored budget field `k` is
read as `k^m` by the evaluator, so that `progT` still writes `bnum k` and the guard is still
`instB ⌜q_D⌝ k`), and the engine's `Pf` side has no such family. The natural family
(`f(k) = k`) is dead under exponential `E`, exactly as the brief says.

**(iii) Prove Property 4 only for `χ = psi`.** Does not help: `ρ` is an arbitrary (nonstandard)
`TAct`-proof of `psi(k)`; nothing about its shape is known, and the construction of §3 never
uses anything about `χ` beyond its (constant) numeral. The only effect of fixing `χ` is that
the `χ`-dependence of the constant becomes invisible — which the restatement in §4.4 already
provides.

**(iv) Cheaper partial wins worth doing regardless.** (1) Charge free-variable indices in
binary in `Length.lean` (`termLen_fvar x = ‖x‖ + 1`): one factor `g` off `E`, and it is the
`T3` cost-faithfulness item the file's docstring already records; every `dlen`-lemma downstream
survives with adjusted constants. (2) Restate `BoundedInnerNec` (§4.4) now, so that U8/U9 are
not vacuous even before U10.
