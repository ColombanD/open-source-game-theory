# DESIGN: `describeSteps` — the bottom-up syntax walk as a STEP LIST (U10, 2026-09-12)

Specification of the list of steps that, from a context `Γ`, introduces one eigenvariable per
node of a formula code `r`'s syntax tree (terms included) and leaves, for the top node's
eigenvariable, its SHAPE fact and its FORMATION fact — the "`describeFormula`" of
`DESIGN_inner_necessitation.md` §3.2(2)/§5(b), in the step-list architecture of `BRIEF.md`
§10. Also specified: the top-down companions `negSteps`, `shiftSteps`, `substSteps`,
`freeSteps` (§9), the invariant `StepsOK` and its Π₁ proof (§7), and the cost (§6).

Every claim is marked **FACT** (`file:line`, read 2026-09-12 on `colomban-arith-u10`) or
**ANALYSIS** (design decisions and consequences; nothing has been compiled).

**Status of `Chain.lean` (FACT).** `arith/ArithS/Necessitation/Chain.lean` on disk (194 lines,
untracked) contains only Part A — `vecOf`, `revV`, `tailIter`, `qVecIterV`, `qqExss`
(`Chain.lean:33-185`). The step codes `sIntroFact`/`sUseHorn`/`sUseHornAnd`/`sWkDrop`,
`StepOK`, `ctxAfter`, `chainCode` do NOT exist yet. This design is written against
`BRIEF.md` §10's description of them (`BRIEF.md:306-326`), plus two NEW step tags (§2.3)
that §10 does not list and that the multi-existential library rows force.

---

## 0. Summary of the decisions

1. **One numeral scheme for every leaf value**: the chain term `cT n` (`cT 0 = ⌜0⌝`,
   `cT (n+1) = cT n ^+ ⌜1⌝`; `termLen (cT n) = 2n + 1`). Bound-variable indices `z`,
   free-variable indices `x`, symbol codes `k R f`, and ARITIES `n` are all written as `cT`.
   The unary cost `2z + 1` is paid by `ρ`'s own unary charge for that leaf
   (`termLen_bvar : termLen ^#z = z + 1`, `Length.lean:100`). Arities MUST be chain terms: the
   rows write the body's arity as the TERM `n + 1` (`isSemiformulaAllB`, `Formulas.lean:638`),
   and `cT (n+1) ≡ cT n ^+ ⌜1⌝` makes the child's fact match SYNTACTICALLY, for free.
2. **`z < n` is derived, not assumed**: `z + 1` Horn steps (`0 < y + 1`, then `z` times
   `x < y → x + 1 < y + 1`) — two NEW rows — cost `O(z)` per bvar leaf, `Σ_leaves (z+1) ≤ |r|`.
   The bvar index is NOT an eigenvariable: bottom-up there is nothing to invert (§3.3).
3. **`describeSteps` is a `Fixpoint` on `⟪n, r⟫`** (the `DlenGraph` pattern), NOT a
   `UformulaRec1` construction: the arity changes under quantifiers and `UformulaRec1`'s
   `param` is fixed through the recursion (`Formula/Basic.lean:507-514`, `all : Semisentence 4`
   — `y param p₁ y₁`, no new parameter). §4.1.
4. **Two new step tags**: `sElimExs` (eliminate an existential fact already in context) and
   `sSplit` (split a conjunctive fact already in context, ONE `orIntro` node). Every row
   with a conclusion `∃ x̄ (C₁ ∧ … ∧ C_j)` is used by the macro `useRowEx` = `sIntroFact`
   + `(a-1)·sElimExs` + `(j-1)·sSplit` (§2.3).
5. **No `sWkDrop` inside the walk**: steps must be `Γ`-independent (the walk is a Σ₁ function
   of `(n, r)` alone, the theorem quantifies over `Γ`), and keeping the dead `lt`-facts costs
   `O(|r|²)`, the order the walk already has (§6.3).
6. **The walk's theorem is purely about codes**: `r` enters only as the argument of the Σ₁
   function `describeSteps` and through the numerals `cT z`, … inside witness codes; no clause
   says "`&0 = r`" (§7.3).
7. **Cost**: `dlen (chainCode Γ (describeSteps 0 r) d) ≤ dlen d + C₁·|r|·(N + |Γ|) +
   C₂·|r|²·fvOccS Γ + C₃·|r|³` — using `ShiftLen.lean`'s ADDITIVE shift bound (§6). The naive
   doubling bound would give `2^{|r|}·|Γ|`.

---

## 1. Conventions (FACT unless marked)

### 1.1 Contexts, facts, rows, witnesses

* A context `Γ` is a bit-set of `LAct`-formula codes (`IsFormulaSet LAct Γ`); a fact `H` is
  *in context* iff `neg H ∈ Γ` (`Steps.lean:22-25`, protocol §1).
* A row is `∀^m B` with `B = impChain as c`; used at CLOSED witness codes `es = [e₁, …, e_m]`,
  OUTERMOST quantifier first, so `es` lists the row's variables in REVERSE index order:
  `e₁` fills `#(m-1)`, `e_m` fills `#0` (`Steps.lean:26-32`).
* Row bodies are written `“x₀ … x_{m-1}. B”` with `x₀ = #0` (`Sets.lean:16-19`). Hence
  **the witness list is the DSL variable list read RIGHT-TO-LEFT.** Check against the smoke
  test: `isSemiformulaAndB = “r q p n. …”` is used at
  `[termShift nc, termShift a, termShift b, ^&0]` = `[n, p, q, r]` (`Steps.lean:1223-1226`).
* Canonical fact codes: `subst (listToVec [w₀, …, w_{a-1}]) ⌜lMap emb P⌝` in the PREDICATE's
  own variable order (`piFact n a`, `sigmaFact n a`, `andFact z a b`, `Steps.lean:1041-1043`);
  `instOuterAt_subst` (`Steps.lean:882-900`) reduces every instantiated row piece to such a
  code (`instOuter_subst_bv2/_bv3`, `:1084-1142`).
* `introFactCode Γ es as R dΛ d` delivers to `d` the context
  `insert (neg (free (instOuterAt 1 es R))) (setShift Γ)` — every free variable of `Γ` shifted
  by one, the new eigenvariable is `&0` (`Steps.lean:560-566`, `introFactCode_proof`, `:596-606`);
  `shift` fixes quoted sentence codes (`shift_quote_sentence`, `:1019`) so a fact
  `subst ?[w] P` shifts to `subst ?[termShift w] P` (`shift_subst_listToVec`, `:970`) and
  `free (subst ?[#0, l] P) = subst ?[&0, termShift l] P` (`free_subst_listToVec`, `:979`).
  `termShift (^&i) = ^&(i+1)` (`Term/Functions.lean:169`); closed numerals are fixed by
  `termShift` (needed as a lemma for `cT`, §10).
* Polarity: a Δ₁ predicate appears `.pi` in antecedent position and `.sigma` in conclusion
  position; the bridges convert (`Sets.lean:21-23`; `isSemiformulaSigmaPiB “p n.”`,
  `Sets.lean:269-270`; `isSemitermSigmaPiLActB “t n.”`, `isSemitermVecSigmaPiLActB “v n k.”`,
  `isUTermVecSigmaPiLActB “v k.”`, `Bridge.lean:828-852`).

### 1.2 Fact-code names used below (ANALYSIS: naming; each is `subst ?[…] ⌜lMap emb Pred⌝`)

| name | predicate (variable order = the row's `!Pred …` order) |
|---|---|
| `piF n p`, `sigmaF n p` | `(isSemiformula LAct).pi/.sigma n p` (= `piFact`, `sigmaFact`) |
| `tPiF n t`, `tSigmaF n t` | `(isSemiterm LAct).pi/.sigma n t` |
| `tvPiF k n v`, `tvSigmaF k n v` | `(isSemitermVec LAct).pi/.sigma k n v` |
| `utvPiF k v`, `utvSigmaF k v` | `(isUTermVec LAct).pi/.sigma k v` |
| `relF p k R v`, `nrelF`, `verumF p`, `falsumF p`, `andF r p q` (= `andFact`), `orF`, `allF q p`, `exsF q p` | `qqRelDef p k R v`, …, `qqAndDef r p q`, …, `qqAllDef q p`, … |
| `funcF t k f v`, `bvarF t z`, `fvarF t x`, `adjF w t v` | `qqFuncDef t k f v`, `qqBvarDef t z`, `qqFvarDef t x`, `adjoinDef w t v` |
| `isRelF k R`, `isFuncF k f` | `LAct.isRel k R`, `LAct.isFunc k f` |
| `ltF a b` | the atom `a < b` (ℒₒᵣ primitive) |
| `negF y p`, `shiftF y p`, `substF y w p`, `substs1F y t p`, `freeF y p`, `qVecF u w`, `tsvF u k w v`, `tshvF u k v` | `(negGraph LAct) y p`, `(shiftGraph LAct) y p`, `(substsGraph LAct) y w p`, `(substs1Graph LAct) y t p`, `(freeGraph LAct) y p`, `(qVecGraph LAct) u w`, `(termSubstVecGraph LAct) u k w v`, `(termShiftVecGraph LAct) u k v` |

### 1.3 Eigenvariable indices

All indices are RELATIVE to the current context. Each `sIntroFact`/`sElimExs` shifts every
existing `&i` to `&(i+1)` and names the new eigenvariable `&0`. If a fact about `&i` was
created and `s` shifting steps followed, it is now a fact about `&(i+s)`. For a list of
steps `L`, `shifts L` := the number of `sIntroFact`/`sElimExs` in it. For the walk,
`shifts (describeSteps n r) = descCount r` (§4.3).

### 1.4 Numerals: the chain term `cT` (ANALYSIS, decision 1)

`cT : V → V`, Σ₁ (primitive recursion): `cT 0 := ⌜0⌝` (the code of the ℒₒᵣ constant term `0`,
`qqFunc 0 ⌜zero⌝ 0`), `cT (n+1) := cT n ^+ ⌜1⌝` (`qqAdd`, the same codes the DSL's `y + 1`
produces). Properties to prove (§10): `IsSemiterm LAct 0 (cT n)` (closed, any level; ℒₒᵣ-code
lifted by the `LAct_of_LOR` family, `Bridge.lean:103-108`); `termLen LAct (cT n) = 2n + 1`;
`termShift (cT n) = cT n`; `fvOcc (cT n) = 0`; `cT (n : ℕ) = ⌜0 + 1 + ⋯ + 1⌝` (the code of the
DSL term with `n` `+ 1`s) — so a row written with the literal `0 + 1 + 1` instantiates to
`cT 2`.

Why NOT `bnum` (binary, `Bnum.lean:320`) for `z, x`: `ρ` already pays unary for them and the
`z < n` derivation (§3.3) is `O(z)` steps ONLY if both sides are chain terms. Why NOT
Foundation's `numeral` for `k, R, f`: `numeral 1 = 1 ≠ 0 + 1`, so `numeral k` would not match
the `(k + 1)` produced by the `adjoin` formation chain (`isSemitermVecAdjoinB`,
`Formulas.lean:792`: conclusion `(isSemitermVec LAct).sigma (k + 1) n u`). Symbol codes are
`≤ 8` (`smallCodesV_LAct`, `ProperV.lean:250`; `SmallCodesV`, `:227-234`) and `LAct` arities are
`0` or `2` (`LAct = ℒₒᵣ + constant Act`, `Act = C | D`, `LangAct.lean:20-26`), so every
`cT k`, `cT R`, `cT f` has `≤ 17` symbols — constants.

---

## 2. The step language (against `BRIEF.md` §10; §2.3 is NEW)

### 2.1 Step codes and `applyStep`/`ctxAfter` (ANALYSIS)

A step is `⟪tag, ρ, ws⟫`: `ρ` the index of a row in a fixed table `ROWS` (each entry: the
stored proof code `dΛ_ρ`, the antecedent list `as_ρ`, the conclusion `c_ρ`, arity `m_ρ`,
`j_ρ = len as_ρ`, body length `|B_ρ|`, `N_ρ ≥ dlen dΛ_ρ` from `Lib.univ_code`,
`Basic.lean:96-101`); `ws` an HFS vector of `m_ρ` closed term codes — an eigenvariable
`^&i` or a numeral `cT v`. `instOuter es B = subst (vecOf es.reverse) B` (`Chain.lean:17-18`),
so with `w := revV ws` (`Chain.lean:72`) every instantiated piece is `subst w (·)`.

| tag | `applyStep Γ s d` | `ctxAfter Γ s` | shift |
|---|---|---|---|
| `sUseHorn ρ ws` | `useHornCode LAct Γ es as_ρ c_ρ dΛ_ρ d` | `insert (neg (subst w c_ρ)) Γ` | 0 |
| `sUseHornAnd ρ ws` (`c_ρ = c₁ ⋏ c₂`) | `useHornAndCode …` | `insert (neg (subst w c₁)) (insert (neg (subst w c₂)) Γ)` | 0 |
| `sIntroFact ρ ws` (`c_ρ = ^∃ R_ρ`) | `introFactCode LAct Γ es as_ρ R_ρ dΛ_ρ d` | `insert (neg (free (instOuterAt 1 es R_ρ))) (setShift Γ)` | 1 |
| `sElimExs Q` (NEW, `neg (^∃ Q) ∈ Γ`) | `elimExistsCode LAct Γ Q (axLFactCode Γ (^∃ Q)) d` | `insert (neg (free Q)) (setShift Γ)` | 1 |
| `sSplit A B` (NEW, `neg (A ⋏ B) ∈ Γ`) | `orIntro Γ (neg A) (neg B) d` | `insert (neg A) (insert (neg B) Γ)` | 0 |
| `sWkDrop F` | `wkDropCode Γ d` | `Γ ∖ F` | 0 |

FACT for the two new tags: `elimExistsCode Γ P D d` needs `D : insert (^∃ P) Δ`, `Δ ⊆ Γ`
(`Primitives.lean:634-637`) — `axLFactCode Γ (^∃ Q)` derives `insert (^∃ Q) Γ` from
`neg (^∃ Q) ∈ Γ` (`Steps.lean:669-672`); `neg (A ⋏ B) = neg A ⋎ neg B` (`neg_and`, used at
`Steps.lean:463`), and `Derivation.orIntro` needs `p ⋎ q ∈ s` and `d : insert p (insert q s)`
(`Steps.lean:474`, `splitAndCode_proof`) — so `sSplit` is ONE node of cost `|Γ| + 1`, no
weakening. `sWkDrop` is listed for completeness; the walk never emits it (decision 5); if a
fragment uses it, `F` must be a set of fact codes computable without `Γ` and `Γ ∖ F` needs a
Σ₁ bit-set difference (not located in Foundation's `HFS/Bit.lean` — check before use).

### 2.2 `StepOK` (Δ₁) — what the invariant checks per step

`StepOK Γ ⟪tag, ρ, ws⟫` := `IsFormulaSet Γ ∧ len ws = m_ρ ∧ (∀ i < m_ρ, IsSemiterm LAct 0 ws.[i])
∧ ∀ a ∈ as_ρ, neg (subst (revV ws) a) ∈ Γ`, plus for `sElimExs Q`: `IsSemiformula LAct 1 Q ∧
neg (^∃ Q) ∈ Γ`; for `sSplit A B`: `IsFormula A ∧ IsFormula B ∧ neg (A ⋏ B) ∈ Γ`. These are
exactly the hypotheses of `useHornCode_proof` (`Steps.lean:339-346`: `has`, `hc`, `hes`, `hΓ`,
`hneg`), `introFactCode_proof` (`:596-606`), `elimExistsCode_proof`. Δ₁: `subst` and `revV`
are Σ₁ functions with graphs, membership is Δ₀, the `∀ a ∈ as_ρ` is over a fixed finite list.

`StepsOK Γ L := ∀ i < len L, StepOK (ctxVec Γ L).[i] L.[i]` (Δ₁, bounded ∀ over the list;
`ctxVec` is PR over the list by `ctxAfter`). `chainCode_proof` and `dlen_chainCode_le` as in
`BRIEF.md:318-321`.

### 2.3 Rows with conclusions `∃ x₁ … x_a (C₁ ∧ … ∧ C_j)` — the macro `useRowEx` (NEW)

`introFactCode` handles ONE `∃` with a single body `R` (`Steps.lean:560`). The library's
commutation and inversion rows conclude with up to five existentials and six conjuncts
(`negAndB “… → ∃ np nq, !negGraph np p ∧ !negGraph nq q ∧ !qqOrDef y np nq”`,
`Formulas.lean:864`; `freeAllB` with `∃ fz w, … ∧ … ∧ ∃ u sp sp', … ∧ … ∧ … ∧ …`,
`:1234`). Definition (ANALYSIS):

`useRowEx ρ ws` := `[sIntroFact ρ ws]` (its `R_ρ` = the body under the OUTERMOST `∃`)
followed by the row's *script* `script_ρ`: read the conclusion left to right; at an `∃`
emit `sElimExs`, at a `∧` emit `sSplit`. For `∃ x₁ … x_a (C₁ ∧ … ∧ C_j)`: `(a-1)` `sElimExs`
then `(j-1)` `sSplit`; for `freeAll`'s shape `∃ fz w, (P ∧ Q ∧ ∃ u sp sp', (A ∧ B ∧ C ∧ D))`:
`sElimExs, sSplit, sSplit, sElimExs, sElimExs, sElimExs, sSplit, sSplit, sSplit`.

**Index bookkeeping of the existentials (ANALYSIS, from the FACTs below).** After
`sIntroFact` the OUTERMOST variable `x₁` is `&0`; after the `i`-th subsequent `sElimExs`,
`x_{i+1} = &0` and `x_1 … x_i` are `&i … &1`. So after all `a` eliminations: `x_i = &(a − i)`
— **the LAST-listed variable is `&0`**; witnesses `ws` of the row are at `&(i + a)` for an
original `&i`. FACT chain: `instOuterAt 1 es (^∃ q) = ^∃ (instOuterAt 2 es q)`
(`instOuterAt_exs`, `Steps.lean:214`); `instOuterAt k es (subst W P) = subst (W ∘ ?[#0, …,
#(k-1), e_m, …, e₁]) P` (`instOuterAt_subst`, `:882`), so the `k` innermost bound variables
are left in place (`#0` = the innermost = `x_a`); `free (^∃ q) = ^∃ (subst (qVec ?[^&0])
(shift q))` (`free_exs`, `Formulas.lean:69-71`) sends `#1 ↦ ^&0` and keeps `#0`; the next
`free` sends `#0 ↦ ^&0` and shifts the earlier `^&0` to `^&1`. Needed lemma:
`freeIter_subst_listToVec` — the `k`-fold `free` of `subst ?[#0, …, #(k-1), l] P` (closed
`l`, `shift P = P`) is `subst ?[^&(k-1), …, ^&0, termShift^k l] P` (§10).

The conjunction split: `impChain as (c₁ ⋏ (c₂ ⋏ c₃))` — `sSplit` on the fact
`neg (subst w (c₁ ⋏ (c₂ ⋏ c₃)))` needs `subst w (A ⋏ B) = subst w A ⋏ subst w B`
(`substs_and`, used at `Steps.lean:98`) so that `ctxAfter` is stated on the pieces.

### 2.4 The generic "one row use" cost (FACT: the bounds of `Steps.lean`)

With `m = m_ρ`, `j = j_ρ`, `G ≥ setLen Γ`, `E ≥ 1` a bound on every witness length (AFTER the
shift for `sIntroFact`: the smoke test takes `2|a| ≤ E`, `Steps.lean:1333-1339`),
`F := |B_ρ|·E`:

* `sUseHorn`: `dlen ≤ dlen dΛ + dlen d + (m+3)G + (m+1)²(F+m) + |B| + mE + 2m + 3 +
  (2j+1)(G + (j+1)F + 1)` (`dlen_useHornCode_le`, `Steps.lean:354-366`).
* `sUseHornAnd`: the same with `dlen d` replaced by `dlen d + 2G + 6F + 4`
  (`dlen_useHornAndCode_le`, `:505-517`).
* `sIntroFact`: `dlen ≤ dlen dΛ + dlen d + (m + 2j + 10)G + (m+11)F + (m+1)²(F+m) + |B| + mE
  + 2m + (2j+1)((j+2)F + 1) + 12` (`dlen_introFactCode_le`, `:608-619`) — this bound contains
  the DOUBLING `|setShift Γ| ≤ 2|Γ|` through `dlen_elimExistsCode_le'` (`Primitives.lean:717`).
  **Required (§10): `dlen_introFactCode_le_occ`**, the same proof through
  `dlen_elimExistsCode_le_occ` (`ShiftLen.lean:684-698`: `4·setLen Γ + fvOccS Γ` instead of
  `5·setLen Γ`), giving `(m + 2j + 9)G + fvOccS Γ + …`.
* `sElimExs Q`: `dlen ≤ dlen d + 5G + fvOccS Γ + 7|Q| + 9` (`dlen_elimExistsCode_le_occ` with
  `dlen (axLFactCode Γ (^∃ Q)) ≤ G + |^∃ Q| + 1`, `dlen_axLFactCode_le`, `Steps.lean:683`).
* `sSplit`: `dlen = setLen Γ + dlen d + 1` (`DlenGraph.orIntro_iff`, as `dlen_splitAndCode`,
  `Steps.lean:487-491`).

Since `m ≤ 7`, `j ≤ 4` over the whole library (`substsInvRelB` has 7 variables,
`Formulas.lean:1377`; `introAndB` has 9 but is not a walk row), every step costs
`≤ N_ρ + 25·G + fvOccS Γ + K·|B_ρ|·E + K'` with absolute `K, K'` (`(m+1)² ≤ 64`, `(2j+1)(j+2) ≤ 54`).

---

## 3. Leaves: what the walk knows and how the leaf values enter

### 3.1 What is assumed about `r`

Nothing beyond `IsSemiformula LAct n r` at the META level (the V-generic constructor knows the
V-element `r` and its arity `n`, and reads its syntax tree by `IsSemiformula.case_iff`,
`Formula/Basic.lean:1302`). The walk introduces every node from scratch by TOTALITY rows whose
witnesses are the children's eigenvariables (`qqAndTotalB “q p. ∃ r, !qqAndDef r p q”`,
`Formulas.lean:355`, …, `adjoinTotalB “v t. ∃ w, !adjoinDef w t v”`, `:453`).

DESIGN §3.2(1) vs §3.2(2) (`DESIGN_inner_necessitation.md:259-286`): for the WALK the two
cases are identical — `describeSteps` is invoked on a formula code and knows nothing about
where it came from. The difference is in the CALLER: a root-subformula instance
`subst v c_i` is better obtained by `substSteps` (§9.3) from the ONE description of `⌜χ⌝`
(cost `O(|c_i|)`, no re-description of the substituted numeral `t` at every `#0`), and the
identity `x_χ = ⌜χ⌝` is pinned at the top by the numeral once (`DESIGN §4.3` step 1) — the
only place a value is ever written into a sequent. An arbitrary formula (cut formula,
`wk`-member, `axm` instance, the `exsIntro` witness term) is described by `describeSteps 0 r`
(resp. `describeTerm 0 t`) — arity `0`: every such formula is a sequent member, hence
`IsFormula = IsSemiformula 0` (`IsFormulaSet` of the sequent).

### 3.2 Symbol codes `k, R, f`: constants, one closed row per symbol (ANALYSIS)

`isSemiformulaRelB` has the antecedent `!LAct.isRel k R` (`Formulas.lean:554`),
`isSemitermFuncB` has `!LAct.isFunc k f` (`:736`). These are Σ₀ atoms on the witnesses; no
row in `Lib/*` proves them for a given symbol (Bridge has only the `ℒₒᵣ ↔ LAct` transfers,
`Bridge.lean:408-441`). **NEW rows** (finite: relations `=`, `<`; functions `0, 1, +, *, c_C,
c_D`): `isRelConst_R : “!LAct.isRel (0+1+1) (0+1+⋯+1)”` (closed sentence, `R` `+1`s;
`Lib.of_models`), `isFuncConst_f` likewise with arity `0` or `0+1+1`. Used as `sUseHorn ρ []`
(`m = 0`, `j = 0`: `useLemmaCode` with `allsIter 0 B = B`, `Primitives.lean:60`). Their
instances are `isRelF (cT k) (cT R)` by `quote_lMap_emb_subst` (`Steps.lean:1005`) and
`cT (n : ℕ) = ⌜0 + 1 + ⋯ + 1⌝` (§1.4). Closed facts are `shift`-invariant, so they may be
established at any earlier point of the walk (the walk establishes each at the node that
needs it).

### 3.3 The bound-variable index `z` — THE RESOLUTION (ANALYSIS)

The question raised in the brief: `isSemitermBvarB “t z n. z < n → !qqBvarDef t z →
!(isSemiterm LAct).sigma n t”` (`Formulas.lean:749-750`) needs `z` as a WITNESS TERM and the
fact `z < n` in context; `z` (and `n`) may be nonstandard.

* "`z` as an eigenvariable obtained from `r`'s decomposition by the shape-inversion rows" —
  REJECTED for the walk. The inversion rows (`shiftInvRelB … substsInvExsB`,
  `Formulas.lean:1263-1476`) decompose a formula that is ALREADY an eigenvariable in context
  (the output of `shift`/`subst`), and they stop at atoms: `shiftInvRelB` yields the term
  vector `u` with `termShiftVecGraph v k u` — OPAQUE; there is no term-level inversion row
  (no `termShiftVecInv`, no `bvarInv`), so no eigenvariable for `z` ever arises top-down. And
  bottom-up (the walk's direction, the ONLY option for a cut formula or a `wk`-member, which
  no row outputs) there is nothing to invert: the leaf must be BUILT. Building `t = ^#z` needs
  a witness whose VALUE is `z`: a numeral.
* "`numeral z` is impossible for nonstandard `z`" — FALSE at the code level: `cT z` is a
  V-element for every `z : V` (Σ₁ primitive recursion, like `bnum`, `Bnum.lean:320-380`,
  `bnum_semiterm : IsSemiterm ℒₒᵣ k (bnum n)` by `pi1_order_induction`). Its length
  `2z + 1` is nonstandard when `z` is — and so is `ρ`'s charge `termLen ^#z = z + 1`
  (`Length.lean:100`) for the same leaf. Nothing is lost: a nonstandard proof `ρ` has
  nonstandard length and the verification proof is allowed `poly(g)`.
* `z < n` must be DERIVED in `TAct` as the atom `ltF (cT z) (cT n)`. With chain terms this is
  `z + 1` Horn steps — `ltSteps z n` (requires `z < n`, which the V-generic constructor has
  from `IsSemiterm.induction`'s `hbvar : ∀ z < n, P (^#z)`, `Term/Basic.lean:836-838`):
  1. `sUseHorn zeroLtSucc [cT (n − z − 1)]` — NEW row `zeroLtSuccB “y. 0 < y + 1”`; the
     instance is `ltF (cT 0) (cT (n − z))` because the row's `0` IS `cT 0` and `y + 1` at
     `y := cT (n−z−1)` IS `cT (n − z)` (§1.4).
  2. for `i = 0 … z − 1`: `sUseHorn succLtSucc [cT (n − z + i), cT i]` — NEW row
     `succLtSuccB “y x. x < y → x + 1 < y + 1”` (witnesses right-to-left `[x, y]` — NB the
     DSL order `“y x.”` puts `y = #0`, `x = #1`, so `es = [x, y]`); antecedent
     `ltF (cT i) (cT (n − z + i))` (in context from the previous step); delivers
     `ltF (cT (i+1)) (cT (n − z + i + 1))`.
  End: `ltF (cT z) (cT n)`. Witness bound `E = 2n + 1`; `z + 1` steps.
  Why this direction: `Σ_{bvar leaves of r} (z + 1) ≤ formulaLen r` (`formulaLen_rel = Σ termLen
  + 1`, `termLen_bvar`), so the lt-derivations cost `O(|r|)` steps IN TOTAL. The other direction
  (`z < z+1` then `n − z − 1` bumps `x < y → x < y + 1`) costs `Σ (n − z)`, which is
  `Θ(#leaves · depth)` — quadratic for a deep formula with many `#0`s. Rejected.
* The free-variable index `x` (`isSemitermFvarB “t x n.”`, `Formulas.lean:763-764`) has NO side
  condition: `cT x` as the witness, one `sIntroFact`.

### 3.4 Arities `n` (ANALYSIS)

The arity at a node is the quantifier depth from the formula the caller passed (depth `d` ⇒
arity value `n₀ + d`, term `cT (n₀ + d)`). The formation rows write the body's arity as the
TERM `n + 1` (`isSemiformulaAllB “q p n. !(isSemiformula LAct).pi (n + 1) p → …”`,
`Formulas.lean:637-638`), whose instance at `n := cT m` is the code `cT m ^+ ⌜1⌝ = cT (m+1)`
DEFINITIONALLY (§1.4) — so the child's `piF (cT (m+1)) x_p` matches the instantiated antecedent
`subst ?[cT m ^+ ⌜1⌝, x_p] Ppi` with `rfl`-level equality of the substituted term, no numeral
arithmetic. The same for vector lengths: `isSemitermVecAdjoinB` concludes at `(k + 1)`
(`Formulas.lean:792`), matching `cT (k+1)` for the next `adjoin`, and finally
`isSemiformulaRelB`'s `!(isSemitermVec LAct).pi k n v` at `k := cT k` (`:554`).

---

## 4. `describeSteps` — definition and per-constructor step tables

### 4.1 Definition shape (ANALYSIS, decision 3)

`describeSteps : V → V → V`, `(n, r) ↦` a list (HFS vector) of step codes, defined as a
`Fixpoint` construction on the key `⟪n, r⟫` in the `DlenGraph` style (`DerivationLength.lean`,
`Φ`/blueprint), Δ₁ graph, existence and uniqueness by `IsSemiformula.pi1_structural_induction`
(`Formula/Basic.lean:1379`; cases `hrel hnrel hverum hfalsum hand hor hall hexs`, the last
two at `n + 1` — exactly the recursion below) and, for the term part, `IsSemiterm.induction`
(`Term/Basic.lean:836`; `hbvar : ∀ z < n`, `hfvar`, `hfunc … (∀ i < k, P v.[i])`). Not
`UformulaRec1`: its `all` clause is `“y param p₁ y₁”` with the SAME `param`
(`Formula/Basic.lean:507-514`, `:1038`), so the arity cannot be incremented under a quantifier;
bumping the arity witnesses by post-processing the child's list fails at the bvar leaves,
whose `ltSteps z n` need `n` (§3.3). TRAP (`BRIEF.md:294-297`): no closed numeral as an argument
of a Δ₁ predicate inside the blueprint — row indices and `cT` must enter through graphs/
parameters, not literals.

Three mutually recursive producers (or one fixpoint on tagged keys):
`describeSteps n r`, `describeTerm n t`, `descVec n k v` (the vector `v` of length `k`;
includes the `nil` fact). Concatenation is `++` on HFS vectors; children's lists FIRST.

### 4.2 The tables

Notation: `cp := descCount p`, etc.; `n̄ := cT n`; `⟨w⟩` marks the reference to a vector
eigenvariable — `&i` when the vector is non-empty, the literal `cT 0` when it is the empty
vector `0` (the empty vector IS the number `0`, and `cT 0` denotes `0`; the row
`isSemitermVecNilB “n. !(isSemitermVec LAct).sigma 0 n 0”`, `Formulas.lean:777-778`, is
stated at that literal). "shifted" = `termShift` applied by the step (§1.1). Every line gives:
step, row (variable order), witnesses right-to-left, antecedents that must be in context
(with where they come from), what is delivered.

**Formulas — `describeSteps n r`**

*(F⊤) `r = ^⊤`* — `descCount = 1`, 3 steps:
1. `sIntroFact qqVerumTotal []` (`“∃ p, !qqVerumDef p”`, `m = 0`) → `x_r = &0`; fact `verumF &0`.
2. `sUseHorn isSemiformulaVerum [n̄, &0]` (`“p n.”` → `[n, p]`); antecedent `verumF &0` (1.);
   delivers `sigmaF n̄ &0`.
3. `sUseHorn isSemiformulaSigmaPi [n̄, &0]` (`“p n.”`); antecedent `sigmaF n̄ &0`; delivers
   `piF n̄ &0`.

*(F⊥)* the same with `qqFalsumTotal`, `isSemiformulaFalsum`.

*(F∧) `r = p ^⋏ q`* — `descCount = cp + cq + 1`, `3 + steps(p) + steps(q)`:
0. `describeSteps n p` (→ `x_p = &0`, `piF n̄ &0` in context); then `describeSteps n q`
   (→ `x_q = &0`; `x_p = &cq`, its fact now `piF n̄ &cq`).
1. `sIntroFact qqAndTotal [&cq, &0]` (`“q p. ∃ r, !qqAndDef r p q”`, `:355` → `[p, q]`) →
   `x_r = &0`, `x_p = &(cq+1)`, `x_q = &1`; fact `andF &0 &(cq+1) &1` (`free_inst_rowAndTotalR`,
   `Steps.lean:1143`: `andFact ^&0 (termShift a) (termShift b)`).
2. `sUseHorn isSemiformulaAnd [n̄, &(cq+1), &1, &0]` (`“r q p n.”`, `:609` → `[n, p, q, r]`);
   antecedents `piF n̄ &(cq+1)` (p's step 3, shifted `cq + 1` times), `piF n̄ &1` (q's step 3,
   shifted once), `andF &0 &(cq+1) &1` (1.); delivers `sigmaF n̄ &0`.
3. `sUseHorn isSemiformulaSigmaPi [n̄, &0]` → `piF n̄ &0`.

*(F∨)* identical with `qqOrTotal`, `isSemiformulaOr`, fact `orF`.

*(F∀) `r = ^∀ p`* — `descCount = cp + 1`:
0. `describeSteps (n+1) p` (→ `x_p = &0`, `piF (cT (n+1)) &0`).
1. `sIntroFact qqAllTotal [&0]` (`“p. ∃ q, !qqAllDef q p”`, `:383`) → `x_r = &0`, `x_p = &1`;
   fact `allF &0 &1`.
2. `sUseHorn isSemiformulaAll [n̄, &1, &0]` (`“q p n.”`, `:637` → `[n, p, q]`); antecedents
   `piF (n̄ ^+ ⌜1⌝) &1` — this IS `piF (cT (n+1)) &1` (§3.4) — and `allF &0 &1`; delivers
   `sigmaF n̄ &0`.
3. bridge → `piF n̄ &0`.

*(F∃)* identical with `qqExsTotal`, `isSemiformulaExs`, fact `exsF`.

*(Frel) `r = ^rel k R v`, `k = len v`* — `descCount = cv + 1`, `6 + steps(descVec)`:
0. `descVec n k v` (→ `⟨v⟩ = &0` if `k > 0`; `tvPiF (cT k) n̄ ⟨v⟩` in context).
1. `sUseHorn isRelConst_R []` → `isRelF (cT k) (cT R)` (closed; §3.2).
2. `sIntroFact qqRelTotal [cT k, cT R, ⟨v⟩]` (`“v R k. ∃ p, !qqRelDef p k R v”`, `:299` →
   `[k, R, v]`) → `x_r = &0`, `⟨v⟩` becomes `&1` (if non-empty); fact
   `relF &0 (cT k) (cT R) ⟨v⟩'`.
3. `sUseHorn isSemiformulaRel [n̄, cT k, cT R, ⟨v⟩', &0]` (`“p v R k n.”`, `:553` →
   `[n, k, R, v, p]`); antecedents `isRelF (cT k) (cT R)` (1.), `tvPiF (cT k) n̄ ⟨v⟩'` (0.,
   shifted once), `relF …` (2.); delivers `sigmaF n̄ &0`.
4. bridge → `piF n̄ &0`.
5. `sUseHorn isUTermVecOfSemitermVecLAct [cT k, n̄, ⟨v⟩']` — NEW row
   `“v n k. !(isSemitermVec LAct).pi k n v → !(isUTermVec LAct).sigma k v”` (§10; Bridge has
   only the ℒₒᵣ version, `Bridge.lean:628`) → `utvSigmaF (cT k) ⟨v⟩'`.
6. `sUseHorn isUTermVecSigmaPiLAct [cT k, ⟨v⟩']` (`“v k.”`, `Bridge.lean:848`) →
   `utvPiF (cT k) ⟨v⟩'` — the `(isUTermVec LAct).pi k v` antecedent of every commutation and
   length row at atoms (`negRelB`, `shiftRelB`, `substsRelB`, `freeRelB`, `formulaLenRelB`).

*(Fnrel)* identical with `qqNRelTotal`, `isSemiformulaNRel`, fact `nrelF`.

**Vectors — `descVec n k v`** (`v = t₁ ∷ (t₂ ∷ (… ∷ 0))`, described TAIL FIRST)

*(V0) `v = 0`* — `descCount = 0`, 2 steps: `sUseHorn isSemitermVecNil [n̄]` (`“n.”`, `:777`)
→ `tvSigmaF (cT 0) n̄ (cT 0)`; `sUseHorn isSemitermVecSigmaPiLAct [cT 0, n̄, cT 0]` (`“v n k.”`,
`Bridge.lean:838` → `[k, n, v]`) → `tvPiF (cT 0) n̄ (cT 0)`.

*(V∷) `v = t ∷ v'`, `len v' = k'`* — `descCount = cv' + ct + 1`, `3 + …`:
0. `descVec n k' v'` (→ `⟨v'⟩`, `tvPiF (cT k') n̄ ⟨v'⟩`); then `describeTerm n t` (→ `x_t = &0`,
   `tPiF n̄ &0`; `⟨v'⟩ = &ct` if non-empty).
1. `sIntroFact adjoinTotal [&0, ⟨v'⟩]` (`“v t. ∃ w, !adjoinDef w t v”`, `:453` → `[t, v]`) →
   `x_v = &0`, `x_t = &1`, `⟨v'⟩' = &(ct+1)`; fact `adjF &0 &1 ⟨v'⟩'`.
2. `sUseHorn isSemitermVecAdjoin [cT k', n̄, ⟨v'⟩', &1, &0]` (`“u t w n k.”`, `:791` →
   `[k, n, w, t, u]`); antecedents `tvPiF (cT k') n̄ ⟨v'⟩'` (0.), `tPiF n̄ &1` (t's bridge,
   shifted once), `adjF &0 &1 ⟨v'⟩'` (1.); delivers `tvSigmaF (cT k' ^+ ⌜1⌝) n̄ &0` =
   `tvSigmaF (cT k) n̄ &0`.
3. `sUseHorn isSemitermVecSigmaPiLAct [cT k, n̄, &0]` → `tvPiF (cT k) n̄ &0`.

**Terms — `describeTerm n t`**

*(T#) `t = ^#z`, `z < n`* — `descCount = 1`, `z + 4` steps:
1–(z+1). `ltSteps z n` (§3.3) → `ltF (cT z) n̄` (and the `z` intermediate `ltF`s, kept).
(z+2). `sIntroFact qqBvarTotal [cT z]` (`“z. ∃ t, !qqBvarDef t z”`, `:425`) → `x_t = &0`; fact
   `bvarF &0 (cT z)` (closed numerals are shift-invariant, so the `ltF`s are unchanged).
(z+3). `sUseHorn isSemitermBvar [n̄, cT z, &0]` (`“t z n.”`, `:749` → `[n, z, t]`); antecedents
   `ltF (cT z) n̄`, `bvarF &0 (cT z)`; delivers `tSigmaF n̄ &0`.
(z+4). `sUseHorn isSemitermSigmaPiLAct [n̄, &0]` (`“t n.”`, `Bridge.lean:828`) → `tPiF n̄ &0`.

*(T&) `t = ^&x`* — `descCount = 1`, 3 steps: `sIntroFact qqFvarTotal [cT x]` (`“x. ∃ t”`,
`:439`) → `fvarF &0 (cT x)`; `sUseHorn isSemitermFvar [n̄, cT x, &0]` (`“t x n.”`, `:763`) →
`tSigmaF n̄ &0`; bridge → `tPiF n̄ &0`.

*(Tf) `t = ^func k f v`* — `descCount = cv + 1`, `6 + steps(descVec)`:
0. `descVec n k v`. 1. `sUseHorn isFuncConst_f []` → `isFuncF (cT k) (cT f)`.
2. `sIntroFact qqFuncTotal [cT k, cT f, ⟨v⟩]` (`“v f k. ∃ t, !qqFuncDef t k f v”`, `:411`) →
   `x_t = &0`; fact `funcF &0 (cT k) (cT f) ⟨v⟩'`.
3. `sUseHorn isSemitermFunc [n̄, cT k, cT f, ⟨v⟩', &0]` (`“t v f k n.”`, `:735` →
   `[n, k, f, v, t]`); antecedents `isFuncF`, `tvPiF (cT k) n̄ ⟨v⟩'`, `funcF …`; delivers
   `tSigmaF n̄ &0`. 4. bridge → `tPiF n̄ &0`.
5–6. `utvSigmaF`/`utvPiF (cT k) ⟨v⟩'` as in (Frel) 5–6 (for `termLenFuncB`,
   `Lengths.lean:341-342`, and any future term-level commutation rows).

### 4.3 `descCount`, `stepCount`, and the index check (ANALYSIS)

```
descCount ^⊤ = descCount ^⊥ = 1          descCount (p ⋏ q) = descCount (p ⋎ q) = cp + cq + 1
descCount (∀ p) = descCount (∃ p) = cp + 1   descCount (rel/nrel k R v) = descCount v + 1
descCount 0 = 0                           descCount (t ∷ v) = descCount v + descCount t + 1
descCount ^#z = descCount ^&x = 1         descCount (func k f v) = descCount v + 1
```
= the number of syntax-tree nodes other than empty vectors; `descCount r ≤ formulaLen r`.
`shifts (describeSteps n r) = descCount r` (one `sIntroFact` per node, no `sElimExs`).

`stepCount`: formula connectives 3, atoms 6 (+ vector), vectors 2 (nil) + 3 per `∷`, terms
`z + 4` / 3 / 6 (+ vector). Since `formulaLen` counts every node once and every `^#z` as
`z + 1` (`formulaLen_rel/and/all`, `termLen_bvar/fvar/func`, `Length.lean:100-102, 206-235`):
**`stepCount r ≤ 8·formulaLen r`**.

Index check (the rule of §1.3, applied): a child's top fact is created about `&0`; a later
sibling walk of count `c` and the parent's `sIntroFact` shift it to `&(c + 1)`; the parent's
own fact is created at `&0` after that shift, so it refers to the children as `&(c+1)` and
`&1` (binary) or `&1` (unary) — exactly the witnesses written in (F∧)/(F∀)/(V∷). Every
witness index used by the walk is `≤ descCount r` (the walk never references an eigenvariable
of `Γ`), which is what makes the witness bound `E` (§6) independent of `Γ`.

### 4.4 Positions of descendants after the walk (for the top-down walks, §9)

`off(r, path)` := index of the node at `path` relative to `x_r` right after `describeSteps`:
`off(p ⋏ q, left) = cq + 1`, `off(p ⋏ q, right) = 1`, `off(∀ p, body) = 1`,
`off(rel k R v, vec) = 1`, `off(t ∷ v', head) = 1`, `off(t ∷ v', tail) = ct + 1`; composed
along paths. Every later step that shifts adds one to all of them. The top-down producers
carry the current absolute index of `x_r` and compute children's indices from `off`.

---

## 5. The final context (ANALYSIS; all codes canonical, §1.2)

After `describeSteps n r` from `Γ` (`x_r = &0`, `s := descCount r`):

* `setShiftIter s Γ ⊆ ctxAfter` — every fact of `Γ` about `&i` reappears about `&(i + s)`
  (`Steps.lean` protocol §4; `mem_setShift_insert`/`shift_mem_setShift` as in
  `describeAnd_row2_proof`, `:1285-1310`);
* for the top node: its SHAPE fact (`andF &0 &(cq+1) &1`, `allF &0 &1`, `relF &0 (cT k) (cT R)
  &1`, `verumF &0`, …), `sigmaF n̄ &0` (`.sigma`, dead after the bridge) and `piF n̄ &0`
  (`.pi` — what every row consumes);
* for every descendant formula node at index `i`: its shape fact, `sigmaF (cT n_i) &i`,
  `piF (cT n_i) &i` with `n_i = n + depth`; for every term node: `tSigmaF`/`tPiF (cT n_i) &i`;
  for every non-empty vector node: `tvSigmaF`/`tvPiF (cT k) (cT n_i) &i` and (atoms/functions)
  `utvSigmaF`/`utvPiF (cT k) &i`; the nil facts `tvPiF (cT 0) (cT n_i) (cT 0)` (closed);
* the closed symbol facts `isRelF (cT k) (cT R)`, `isFuncF (cT k) (cT f)`;
* the closed `ltF (cT i) (cT (n_i − z + i))`, `i ≤ z`, for every bvar leaf (dead; §6.3).

NOT produced by the walk (obtained later, §9): `neg`-shapes (`axL` needs `np ∈ s` with
`negGraph np p`, `introAxLB`, `Nodes.lean:43-47`), `shift`/`free`/`subst` commutation at the
decomposition sites (`introAllB` needs `freeGraph fp p`, `setShiftGraph ss s`, `Nodes.lean:124-128`;
`introExsB` needs `substs1Graph pt t p`, `:146-151`), and lengths (`formulaLenGraph`,
`DESIGN §4`).

---

## 6. Cost of the walk

### 6.1 The honest growth of the context (FACT + ANALYSIS)

Doubling per shift (`setLen_setShift_le : setLen (setShift s) ≤ 2·setLen s`,
`Primitives.lean:596`) chained through `descCount r` shifts gives `2^{|r|}·|Γ|` — useless.
`ShiftLen.lean` (untracked, 698 lines, read 2026-09-12) supplies the sharp statements:
`formulaLen_shift_eq : formulaLen (shift p) = formulaLen p + fvOccF p` (`:364`),
`fvOccF_shift : fvOccF (shift p) = fvOccF p` (`:394`),
`setLen_setShift_le_occ : setLen (setShift s) ≤ setLen s + fvOccS s` (`:605`),
`fvOccS_setShift_le` (`:624`), `setLen_setShiftIter_le : setLen (setShift^[n] s) ≤ setLen s +
n·fvOccS s` (`:662`), `fvOccS_le_setLen` (`:592`), `fvOccS_insert_le` (`:580`), and the
restated primitive bound `dlen_elimExistsCode_le_occ` (`:684`). This is exactly the "sharper
length lemma" the brief asks for; the walk needs, on top of it:

* `fvOccF_subst_le : fvOccF (subst w P) ≤ fvOccF P + formulaLen P · listMax (fvOccVec w)` —
  so a fact `subst ?[ws] P` with eigenvariable/numeral witnesses has `fvOccF ≤ |P|` (each
  `^&i` has `fvOcc = 1`, `fvOcc_fvar`, `ShiftLen.lean:132`; `cT` has `0`). NOT in
  `ShiftLen.lean` — the analogue of `formulaLen_subst_le` (`InstV.lean`, used at
  `ShiftLen.lean:437`).
* `dlen_introFactCode_le_occ` (§2.4).
* a V-indexed `setShiftIterV : V → V → V` (`ShiftLen.setShiftIter` is `ℕ`-indexed, `:640`;
  `descCount r` is a V-value).

Per step `i` with context `Γ_i`, `G_i := setLen Γ_i`, `O_i := fvOccS Γ_i`, new fact `f_i`:
* `sUseHorn`: `G_{i+1} ≤ G_i + |f_i|`, `O_{i+1} ≤ O_i + fvOccF f_i` (`setLen_insert_le`,
  `CutV.lean:130`; `fvOccS_insert_le`);
* `sIntroFact`/`sElimExs`: `G_{i+1} ≤ G_i + O_i + |f_i|`, `O_{i+1} ≤ O_i + fvOccF f_i`
  (`setLen_setShift_le_occ`, `fvOccS_setShift_le`);
* `|f_i| ≤ 2·|B_ρ|·E_i` (`formulaLen_instOuter_le : |instOuter es B| ≤ |B|·E`,
  `Primitives.lean:311`; `free` adds `≤ |R'|`, `formulaLen_free_le`,
  `Primitives.lean:587`), `fvOccF f_i ≤ |B_ρ|` (`fvOccF_subst_le`).

### 6.2 The witness bound (ANALYSIS)

At every step of `describeSteps n₀ r` the witnesses are `^&i` with `i ≤ descCount r ≤ |r|`
(§4.3) or `cT v` with `v ∈ {z, x, k, R, f, n₀ + depth, n − z + i}`, all `≤ n₀ + |r| + 8`. After
the step's own shift `^&i ↦ ^&(i+1)`. Hence
**`E_i ≤ 2(n₀ + |r|) + 18 =: E(r)`** for every step — independent of `Γ` and of `i`.

### 6.3 The bound (ANALYSIS; constants absolute, from §2.4 with `B := max_ρ |B_ρ|`,
`N := max_ρ N_ρ`, `S := stepCount r ≤ 8|r|`, `s := descCount r ≤ |r|`)

`O_i ≤ O_0 + i·B ≤ fvOccS Γ + S·B`;
`G_i ≤ setLen Γ + s·(fvOccS Γ + S·B) + S·2B·E(r)`;
per step `≤ N + 25·G_i + O_i + K·B·E(r) + K'`; summing over `S` steps:

`dlen (chainCode Γ (describeSteps n₀ r) d) ≤ dlen d + S·(N + K') + 25·S·setLen Γ +
(25·S·s + S)·fvOccS Γ + 25·S·s·S·B + 50·S²·B·E(r) + S·S·B + K·B·S·E(r)`

i.e. **`≤ dlen d + C₁·|r|·(N + setLen Γ) + C₂·|r|²·fvOccS Γ + C₃·(|r| + n₀)·|r|²`** with
`C₁ = 8·26`, `C₂ = 8·26`, `C₃ = O(B²)` (row-table constants). With `fvOccS Γ ≤ setLen Γ`
(`fvOccS_le_setLen`): `O(|r|²·|Γ| + |r|³)`. Per `ρ`-node `ν` with `|r| ≤ w_ν` and
`|Γ_ν| = O(L_ν·(1 + D_ν))`: `O(w_ν²·L_ν·D_ν + w_ν³) ≤ O(w_ν²·g)` — the `O(w_ν · L_ν · (1 + D_ν))`
of `DESIGN §3.7` times the walk's own `w_ν`, still `E(g) = O(g³)`. The `|r|³` term is the
walk's `S` steps × its `≤ S` own facts × their index drift `≤ s` — reducible to `|r|² log`
by refreshing, not needed for `d = 3`.

Keeping the dead `ltF` facts (decision 5) adds `Σ_{bvar} (z+1)·(2n_i + 3) ≤ |r|·(2(n₀ + |r|) + 3)`
to every `G_i` — inside the `C₃` term. Keeping the dead `sigmaF` facts adds `≤ S·B·E(r)` — same.

---

## 7. `StepsOK`, its proof, and what the theorem says

### 7.1 The theorem (ANALYSIS — the statement to prove, code-level)

```
theorem describeSteps_ok {n r : V} (hr : IsSemiformula LAct n r) :
  ∀ Γ, IsFormulaSet LAct Γ →
    StepsOK Γ (describeSteps n r) ∧
    IsFormulaSet LAct (ctxAfter* Γ (describeSteps n r)) ∧
    shifts (describeSteps n r) = descCount r ∧
    neg (piF (cT n) ^&0) ∈ ctxAfter* Γ (describeSteps n r) ∧
    neg (shapeF r) ∈ ctxAfter* Γ (describeSteps n r) ∧            -- the per-shape code of §4.2
    setShiftIterV (descCount r) Γ ⊆ ctxAfter* Γ (describeSteps n r) ∧
    setLen (ctxAfter* …) ≤ setLen Γ + descCount r · fvOccS Γ + c·(|r| + n)·|r| ∧
    fvOccS (ctxAfter* …) ≤ fvOccS Γ + c'·|r|
```
(`ctxAfter*` = the last entry of `ctxVec`), and `dlen_describeSteps_le` = §6.3 via
`dlen_chainCode_le`. `shapeF r` is defined by cases on `r` (`andF ^&0 ^&(cq+1) ^&1`, …) — a
Σ₁ function of `r`, so the clause is Δ₁ in `(r, Γ, y)`.

### 7.2 The proof (ANALYSIS)

By `IsSemiformula.pi1_structural_induction` (`Formula/Basic.lean:1379`) with
`P n r := ∀ Γ y, y = describeSteps n r → IsFormulaSet Γ → (Δ₁ clauses above in Γ, y, r, n)` —
Π₁ (unbounded `∀ Γ y`, Σ₁ graph in the antecedent, Δ₁ matrix; `descCount`, `shapeF`, `cT`,
`setShiftIterV` enter through their Σ₁ graphs). Case `hand`: unfold `describeSteps n (p ⋏ q) =
describeSteps n p ++ describeSteps n q ++ node`, apply IH(p) at `Γ`, IH(q) at the resulting
context, then three concrete `StepOK`s: each needs the antecedent facts at the indices of
§4.2, obtained from the IHs' membership clauses transported through `setShiftIterV` (the
`shift_piFact`/`shift_mem_setShift` pattern of `describeAnd_row2_proof`, `Steps.lean:1285-1310`,
iterated) and the identification lemmas `inst_row_ρ` (per row, the `inst_rowIsAnd` pattern,
`:1150`) — these need `instOuter_subst_bvN` for `N ≤ 7` (only `_bv2/_bv3` exist, `:1084-1142`;
§10). Case `hall`: IH at `n + 1`; the antecedent `piF (cT n ^+ ⌜1⌝) ^&1` is the IH's
`piF (cT (n+1)) ^&0` shifted once, equal by `cT_succ` and `shift_subst_listToVec` +
`termShift (cT _) = cT _`. Atoms: the term part by `IsSemiterm.induction 𝚷`
(`Term/Basic.lean:836`) — `hbvar` gives `z < n` for `ltSteps`; `hfunc` gives `∀ i < k, P v.[i]`,
composed along `∷` by a lemma `descVec_ok` proved by `IsUTermVec` induction on the vector.
The length clauses are the recurrences of §6.1 discharged per step.

### 7.3 What the theorem does NOT say — and the check against `useHornCode_proof` (FACT)

`useHornCode_proof` (`Steps.lean:339-346`) takes `hneg : ∀ a ∈ as, neg (instOuter es a) ∈ Γ` and
`hd : DerivationOf d (insert (neg (instOuter es c)) Γ₀)`: membership of CODES built from the
witness TERMS `es`; `introFactCode_proof` (`:596-606`) the same with `free (instOuterAt 1 es R)`.
No hypothesis relates a witness `^&i` to a V-element. Hence `describeSteps_ok` mentions `r`
only as (i) the argument of the Σ₁ function `describeSteps` and (ii) the source of the
numerals `cT z, cT x, cT k, cT R, cT f, cT n` inside witness codes and of `shapeF r`'s
constructor tag. The eigenvariable `^&0` is never asserted to denote `r`; the derivation
`chainCode Γ (describeSteps n r) d` is a valid `TAct`-derivation of `Γ` under EVERY valuation
of its free variables — which is exactly what makes it a proof. The identity "`x_r` denotes
`r`" is only what the V-generic CONSTRUCTOR uses to decide which steps to emit (the values of
`z`, `k`, … it writes as numerals are `r`'s), and, once, at the top, for `⌜χ⌝` (§3.1). The
single other place a value enters a sequent is DESIGN §3.5/§4.2's `p ∈ s` case (`insert p s
= s`), proved by a parallel injectivity walk on two DESCRIBED eigenvariables — still codes.

---

## 8. Leaves entering the fragment (recap of §3.1)

* Sequent members introduced by `ρ` (`cut` formula, `wk` members, `axm` instances, `shift`
  outputs when re-described): `describeSteps 0 r` from the node's live context.
* The `exsIntro` witness term `t`: `describeTerm 0 t` (arity `0`: `IsSemiterm LAct 0 t` is what
  `introExsB` needs, `Nodes.lean:149`: `!(isSemiterm LAct).pi 0 t`).
* Root-subformula instances (`DESIGN §3.2(1)`): the top describes `⌜χ⌝` once by
  `describeSteps 1 ⌜χ⌝`, pins `x_χ = ⌜χ⌝` with the numeral (`N_χ`), and every instance
  `subst v c_i` is obtained by `substSteps` from the node `c_i` of that ONE description.

---

## 9. The top-down companions (ANALYSIS)

Each is a `Fixpoint` on `⟪n, r, i_x, i_y⟫` (arity, the SOURCE code `r`, the current indices of
the source eigenvariable `x_r` and the output eigenvariable `y`), producing steps that
decompose the OUTPUT `y` along `r`'s tree using `r`'s description (§5) — the rows' hypotheses
are about the SOURCE (`!(isSemiformula LAct).pi n p`, `!qqAndDef r p q`, `Formulas.lean:864`),
which the description supplies; the output's sub-eigenvariables are the rows' existentials.
The caller introduces `y` by the totality row first (`negTotalB “p. ∃ y”`, `shiftTotalB`,
`substsTotalB “p w. ∃ y”` → `[w, p]`, `substs1TotalB “p t. ∃ y”` → `[t, p]`, `freeTotalB`;
`Formulas.lean:467-496`, `Sets.lean:400-412`) and the output's top formation by
`isSemiformulaNeg/Shift/Subst/Substs1B`, `isFormulaFreeB` (`Formulas.lean:665-722`; for
`subst`, the vector fact `tvPiF n m w` — for `w = ?[t]` from `isSemitermVecAdjoin` +
`describeTerm`).

### 9.1 `negSteps` — `negCount (rel/nrel/⊤/⊥) = 0`, `(p⋏q), (p⋎q) = negCount p + negCount q + 2`, `(∀p), (∃p) = negCount p + 1`

* atoms: `sUseHorn negRel [cT k, cT R, ⟨v⟩, x_r, y]` (`“y r v R k.”`, `:807` → `[k, R, v, r, y]`);
  antecedents `isRelF`, `utvPiF (cT k) ⟨v⟩` (§4.2 Frel 6), `relF x_r …`, `negF y x_r`; delivers
  `nrelF y (cT k) (cT R) ⟨v⟩` — no new eigenvariable. `negVerum/Falsum`: `[y, r]` order
  `“y r.”` → `[r, y]`.
* `p ⋏ q`: `useRowEx negAnd [n̄, x_p, x_q, x_r, y]` (`“y r q p n.”` → `[n, p, q, r, y]`;
  `x_p = &(i_x + off)`, …) → 2 shifts: `np = &1`, `nq = &0`; facts `negF &1 x_p'`,
  `negF &0 x_q'`, `orF y' &1 &0`. Recurse `negSteps (n, p, i_x+off_p+2, 1)`, then
  `negSteps (n, q, i_x+off_q+2+negCount p, negCount p)`.
* `∀ p`: `useRowEx negAll [n̄, x_p, x_r, y]` (`“y r p n.”`) → 1 shift: `np = &0`; facts
  `negF &0 x_p'`, `exsF y' &0`; recurse at `n + 1`.
Formation of the output's sub-nodes (needed if `ρ` later inserts them into a sequent): by
`isSemiformulaNeg [n̄, x_sub, y_sub]` from the SOURCE's `piF` — no inversion row needed.

### 9.2 `shiftSteps` — `shiftCount (atom) = 1` (the opaque vector `u`), `⊤/⊥ = 0`, binary `+2`, quantifier `+1`

`shiftRel [cT k, cT R, ⟨v⟩, x_r, y]` (`“y r v R k.”`, `:1035`) → `∃ u`: `tshvF &0 (cT k) ⟨v⟩'`,
`relF y' (cT k) (cT R) &0`; `shiftAnd` (`:1091`), `shiftAll` (`:1119`, at `n + 1`) as for `neg`.
Formation of sub-outputs by `isSemiformulaShift`. NB the term vector `u` stays opaque: the
LENGTH of a shifted atom is not derivable from these rows (`fvOcc` would be needed) — the
`dlen` bookkeeping at `allIntro`/`shiftRule` nodes (DESIGN §4) is NOT covered by the current
library; either add `formulaLenShift` rows with an `fvOcc` graph, or re-describe the shifted
formula bottom-up and identify it with `y` by a parallel injectivity walk, which at atoms needs
term-level `termShiftVec` commutation rows (none exist). Flagged, out of scope here.

### 9.3 `substSteps (n → m, w)` — key `⟪n, m, r, i_x, i_y, i_w⟫`

`substsRel [w, cT k, cT R, ⟨v⟩, x_r, y]` (`“y r v R k w.”`, `:921` → `[w, k, R, v, r, y]`) →
`∃ u`: `tsvF &0 (cT k) w' ⟨v⟩'`, `relF y' … &0`; `substsAnd [w, n̄, x_p, x_q, x_r, y]`
(`“y r q p n w.”`, `:977`) → `sp = &1, sq = &0`; `substsAll [w, n̄, x_p, x_r, y]` (`“y r p n w.”`,
`:1005`) → `∃ u sp`: `u = &1` (`qVecF &1 w'`), `sp = &0` (`substF &0 &1 x_p'`), `allF y' &0`;
recurse on `p` at `(n+1 → m+1)` with `w := &1`. Formation of `sp` needs `tvPiF (n̄+1) (m̄+1) u`:
**NEW row** `isSemitermVecQVecB “u w m n. !(isSemitermVec LAct).pi n m w → !(qVecGraph LAct) u w →
!(isSemitermVec LAct).sigma (n + 1) (m + 1) u”`. For `exsIntro` (`substs1Graph pt t p`):
**NEW bridge** `substs1SubstsB “y w t p. !adjoinDef w t 0 → !(substs1Graph LAct) y t p →
!(substsGraph LAct) y w p”` (V-fact: `substs1 t p = substs (t ∷ 0) p`, Foundation's definition, unfolded by `simp [free, substs1]` at `Formulas.lean:38-41`), so the decomposition runs on `substsGraph`.

### 9.4 `freeSteps` — top node only, then `shift` + `subst`

`free (∀ p) = ∀ (subst (qVec ?[&0]) (shift p))` (`free_all`, `Formulas.lean:65-67`;
`freeAllB`, `:1233-1234`): `useRowEx freeAll [n̄, x_p, x_r, y]` → 5 shifts
(`fz, w, u, sp, sp'` = `&4 … &0`), facts `fvarF &4 (cT 0)`, `adjF &3 &4 (cT 0)`, `qVecF &2 &3`,
`shiftF &1 x_p'`, `substF &0 &2 &1`, `allF y' &0`; then `shiftSteps` on `(x_p, sp = &1)` and
`substSteps (n+1 → 1)` on `(sp, sp' = &0)` with `w := &2` — hence `freeSteps` below a
quantifier IS `shiftSteps` followed by `substSteps`; `freeAnd/Or/Rel/…` serve only the top
node when `p` itself is a connective (`freeAndB`, `:1205`; `freeRelB`, `:1149` — 4 existentials).

---

## 10. Library additions and V-lemmas required (ANALYSIS — the implementation checklist)

New library rows (each ~25 lines on the `Sets.lean` template):
1. `zeroLtSuccB “y. 0 < y + 1”`, `succLtSuccB “y x. x < y → x + 1 < y + 1”` (§3.3).
2. `isRelConst_{=,<}`, `isFuncConst_{0,1,+,*,c_C,c_D}`: closed sentences (§3.2).
3. `isUTermVecOfSemitermVecLActB “v n k. (isSemitermVec LAct).pi k n v → (isUTermVec LAct).sigma k v”`.
4. `isSemitermVecQVecB` (§9.3).
5. `substs1SubstsB` (§9.3).

New step machinery (`Chain.lean` Part B): `sElimExs`, `sSplit` with `applyStep`/`ctxAfter`/
`StepOK`/cost (§2.1–2.4); `useRowEx` and the per-row scripts (§2.3).

New V-lemmas:
* `cT` (Σ₁ PR), `isSemiterm_cT`, `termLen_cT : = 2n + 1`, `termShift_cT`, `fvOcc_cT = 0`,
  `cT_natCast : cT (n : ℕ) = ⌜0 + 1 + ⋯ + 1⌝`, `cT_succ` (§1.4).
* `instOuter_subst_bvN` for `N ≤ 7` (or one general lemma over `bvarList`-indexed slot lists),
  `inst_row_ρ` per row (the `inst_rowIsAnd` pattern, `Steps.lean:1150`).
* `freeIter_subst_listToVec` (§2.3); `subst w (A ⋏ B)` distribution for `sSplit`'s `ctxAfter`.
* `fvOccF_subst_le`; `dlen_introFactCode_le_occ`; `setShiftIterV` (§6.1).
* `descCount`, `shapeF`, `stepCount` as Σ₁ functions with their equations; `describeSteps`
  (`Fixpoint` on `⟪n, r⟫`, §4.1) with `descVec_ok` (§7.2).

Traps carried over: never `simp` on quoted sentences (`BRIEF.md:270`); no closed numeral as a
Δ₁-predicate argument inside a fixpoint blueprint (`BRIEF.md:294-297`); `pgrep -f 'bin/lake
build'` (`:279`); `add_le_add`/`gcongr` not `add_le_add_left` (`:280`).
