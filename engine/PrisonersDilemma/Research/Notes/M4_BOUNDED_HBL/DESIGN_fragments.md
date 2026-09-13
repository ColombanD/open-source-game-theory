# DESIGN: `verifySteps ρ` — the ten per-tag fragments as STEP LISTS (U10, 2026-09-13)

Specification of the Σ₁ step-list producer `verifySteps ρ` that, for a derivation code `ρ`
(possibly nonstandard) of a sequent `s_root`, proves inside `TAct` the goal
`G_ν :≡ ∃ d n, derivation.sigma d ∧ fstIdxDef s_ν d ∧ dlenGraphDef.sigma d n ∧ n ≤ ū_ν`
for every node `ν` of `ρ` — one FRAGMENT per node tag, glued into ONE FLAT LIST (`BRIEF.md`
§10), so that `chainCode tbl Γ_root (verifySteps ρ) d_leaf` is the verification proof and
`chainCode_proof`/`dlen_chainCode_le` (`Chain.lean:1732/1762`) give its correctness and length.
Written read-only against the code as it stands on `colomban-arith-u10` (2026-09-13 12:05):
`Chain.lean` (1804 lines, Part B landed), `Describe.lean` (1832 lines, Parts 0–2 landed:
infrastructure, the walk's row table, the TERM walk; the formula walk in flight), `Lib/*`,
`RowInst.lean`. Every claim is **FACT** (`file:line`) or **ANALYSIS** (design; nothing compiled).

---

## 0. Summary of the decisions

1. **Flat list, no sub-chains, no `sWkDrop`.** A child's whole fragment is spliced into the
   parent's list; the child's goal is turned into a context fact by ONE new step tag
   `sGoal` (tag 6): a `cutRule` on `G_child` whose LEFT premise is a constant-shape LEAF
   (`2 exsIntro + 3 andIntro + 4 axL`, all from facts already in context) — so no nested
   `chainCode` inside `applyStep` (which would be a circular primitive recursion, §2.1) and the
   parent then `sElimExs`-es `d`, `n` and `sSplit`s the four conjuncts with the EXISTING tags.
   Nothing is ever dropped (`NoDrop`, `Describe.lean` §0.5): contexts only grow; with unary
   indices `|Γ| = O(g²)` and `O(g)` steps in all, `E(g) = O(g³)` — the same exponent
   DESIGN §3.7 obtains WITH dropping, so `sWkDrop` (Γ-dependent, breaks `mem_ctxVec_of_mem`)
   is never emitted. `d = 3` survives (§5).
2. **Closed numeral facts by ONE more tag `sLemma A dA`** (tag 7): `cutRule Γ A (wkRule (insert A Γ) dA) e`
   with `dA` a Γ-INDEPENDENT derivation of the singleton `{A}` supplied IN the step as data
   (`StepOK` = `DerivationOf TAct dA {A}`, Δ₁). Every arithmetic fact between binary numerals
   (`bnum a + bnum b + bnum c + 1 ≤ bnum(a+b+c+1)`, `Σ bnum|xᵢ| ≤ bnum(setLen s)`, `lengthDef
   (bnum ‖k‖) (bnum k)`, …) is proved in a context of size `O(‖g‖)` by a separate Σ₁ producer
   `numSteps` (bit recursion on the `Lengths.lean` term-level rows) and cut in at cost
   `2|Γ| + O(‖g‖³)`. Without it the per-node `O(‖g‖)` bit-law steps would run in the full
   `O(g²)` context and cost `O(g³‖g‖)` — a `d = 4`, not `d = 3`.
3. **`ū_ν` IS the binary numeral `bnum (dlen ν)`** (DESIGN §4.1), never the term
   `ū_l + ū₁ + ū₂ + 1` (the term tree would be `O(g‖g‖)` symbols and every `neg G_child` fact
   stays in every later context, §1.2 of `Steps` — total `O(g³‖g‖)`). The witness for `∃ n`
   is the TERM `l + n₁ + n₂ + 1` the `Dlen_tag` row produces (`Nodes.lean:358-361`); its bound
   is `dlenBinaryLe` (`Occ.lean:585`) + `leTrans` against the `sLemma` numeral fact.
4. **Canonical layout by copy-in (no environment).** `verifySteps ρ` must be a Σ₁ function of
   `ρ` alone (a `Fixpoint` graph on `⟪ρ, L⟫` with `StrongFinite`, §6.1 — a key `⟪ρ, env⟫`
   with the ancestors' eigenvariable positions is NOT `StrongFinite`: positions grow downward;
   FACT: `Fixpoint.induction` needs `StrongFinite`, `HFS/Fixpoint.lean:256`). So every fragment
   ASSUMES its live context in a CANONICAL LAYOUT (§3.2: the sequent object at `&k` (`k` members), the length
   object at `&0`, before them the insert-chain prefixes and, member by member, the full walk
   dossier of every member) and the PARENT establishes the child's layout by COPYING the
   inherited objects (`sIntroFact eqTotal [x]` + congruence rows, §3.3) right before splicing
   the child's list. The relabeling alternative (child written against abstract positions, a
   PR pass renaming `&i` inside every step) is blocked by the absence of a free-variable
   renaming on codes (only `shift`/`free`/`substs` exist).
5. **Sequents are insert-CHAINS over their DISTINCT members, rebuilt at every node**; the
   sequent object the `Intro_tag` row needs (`insertDef cp p s`, `Nodes.lean:80-84`) is a
   SEPARATE fresh object `t` (`insertTotal`) identified with the chain by set-extensionality
   (`subsetAntisymm`, §3.4). Lengths are then EXACT WITHOUT deciding non-membership: the chain
   gives `l ≤ Σ bnum|xᵢ|` (`setLenInsertLe`, `Lengths.lean:117`) and the closed inequality
   `Σ bnum|xᵢ| ≤ bnum(setLen s)` is TRUE (the `xᵢ` are distinct) hence `sLemma`-provable —
   DESIGN §4.2's `p ∈ s` case still needs an IDENTIFICATION walk `eqSteps` (§3.5) for the
   duplicate to enter the chain once; `shiftRule` needs it too.
6. **Derived formulas are RE-DESCRIBED bottom-up and CERTIFIED** (`neg`, `shift`, `substs`,
   `free` outputs): the walk `describeF 0 y` on the KNOWN code `y` gives the full term-level
   dossier and exact lengths; bottom-up INTRO rows (`shiftAndIntro`, `substsRelIntro`, the
   term-level `termSubstVec` intro rows — NEW, §8) then certify `shiftF y x`. This replaces
   DESIGN_describe §9's top-down `negSteps/shiftSteps/substSteps/freeSteps` (whose atom
   vectors are OPAQUE — no length, no identification, `DESIGN_describe.md` §9.2's own flag).
7. **Recursion**: `VerifyGraph` = a Δ₁ `Fixpoint` on the key `⟪ρ, L⟫` (the `DlenGraph`
   pattern, `DerivationLength.lean:55-135`; `StrongFinite` via `ρ' < ρ` and `L' ≤ L` for
   sub-vectors); existence by `Derivation.induction1 𝚺`, the invariant `verifySteps_ok`
   (`Layout Γ ρ → ListOK ∧ NoDrop ∧ goal in `finalCtx` ∧ length recurrences) by
   `Derivation.induction1 𝚷` (`Proof/Basic.lean:560`), using `Fixpoint.case` (`Finite`
   suffices) to unfold the graph.
8. **Cost**: `dlen (chainCode tbl Γ (verifySteps ρ) d) ≤ dlen d + C·(dlen ρ + 1)·(setLen Γ +
   (dlen ρ + 1)·(D_Γ + dlen ρ + 1) + N + B)` (§5) — `O(g³)` at the top; `BoundedInnerNec 3`
   (§7.3).

---

## 1. Interfaces this design is written against (FACT)

### 1.1 The step language (`Chain.lean` Part B)

Steps (`:975-980`): `sUseHorn i ev as c = ⟪0,i,ev,as,c⟫`, `sUseHornAnd i ev as c₁ c₂`,
`sIntroFact i ev as R = ⟪2,…⟫`, `sElimExs P = ⟪3,P⟫`, `sSplit p q = ⟪4,p,q⟫`, `sWkDrop Γ' = ⟪5,Γ'⟫`.
`applyStep tbl Γ s e` (`:1020-1027`), `ctxAfter Γ s` (`:1062-1071`; tag 0 `insert (neg (subst
(revV ev) c)) Γ`, tag 2 `insert (neg (free (subst (qVec (revV ev)) R))) (setShift Γ)`, tag 3
`insert (neg (free P)) (setShift Γ)`, tag 4 `insert (neg p) (insert (neg q) Γ)`, else `π₂ s`),
`stepCost N E Γ s` (`:1141-1154`), `HornOK tbl E M Γ s` / `StepOK tbl E M Γ s` (`:1193-1207`:
row index `< len tbl`, `rowM = len ev ≤ M`, `len as ≤ M`, witnesses `IsSemiterm 0` of length
`≤ E`, antecedents `neg (subst (revV ev) as.[k]) ∈ Γ`, and per tag the syntactic decomposition
`rowB tbl.[i] = impChainV as c`), `TableOK tbl N` (`:970`), `chainCode tbl Γ₀ S d` (`:1320`),
`chainCode_proof (M : ℕ)` (`:1732`), `dlen_chainCode_le` (`:1762`), `mem_ctxAfter_of_noShift`
(tags 0/1/4, `:1577`), `mem_ctxAfter_of_shift` (tags 2/3, `:1585`), the standardness bridge
`exists_list_of_len_le` (`:1401`). Unknown tags act as `wkDrop` (`:1027`) — the two new tags
of §2 must be inserted BEFORE the final `else` of `applyStep`/`ctxAfter`/`stepCost`, and
`StepOK` gets two more disjuncts.

### 1.2 The list infrastructure (`Describe.lean` Part 0, `:36-429`)

`appendV` (`:68`), `shiftsV S` (`:246`, tags 2/3 counted; `shiftsV_appendV` `:281`),
`shiftIterV x k` (`:157`), `finalCtx Γ₀ S = (ctxVec Γ₀ S).[len S]` (`:311`),
`finalCtx_appendV` (`:346`), `ListOK tbl E M Γ₀ S` (`:352`) with `listOK_appendV` (`:358`),
`NoDrop S` (`:385`, tags 0–4 only), `mem_ctxVec_of_mem` (`:410`): a fact `x ∈ Γ₀` reappears as
`shiftIterV x (shiftsAux S j) ∈ (ctxVec Γ₀ S).[j]` — the TRANSPORT lemma every fragment relies
on. `NoDrop` must admit tags 6 and 7 (both non-shifting).

### 1.3 The walk (`Describe.lean` Parts 1–2, and DESIGN_describe §4 for formulas)

Row table: `WRow`, `walkRows` (40 rows, `rIdx_<row>` `:512-551`), `WalkTable tbl` (`:602`),
`exists_walkTable` (`:608`), the piece table `walkPieces : V` (`:1096`) and `mkStep W i ev`
(`:1000`: the step for row `i` of piece table `W` at witnesses `ev`; tag and decomposition read
off `W.[i]`). `vRef c j` (`:1515`: `𝟎` for the empty vector, else `^&c`). Term walk: `ltSteps
W n z` (`:1550`), `describeT W n t` / `descCountT W n t` (`:1764/1766`, a `TermRec` construction
with fixed parameters `(W, n)`). The formula walk is assumed as DESIGN_describe §4.1–4.3:
`describeF W n r`, `descCountF n r`, `shiftsV (describeF W n r) = descCountF n r`, top object
`&0` with `shapeF r`, `sigmaF/piF (cT n) &0`, every descendant at the offsets `off` of
DESIGN_describe §4.4, and `describeF_ok` (§7.1 there). This design extends the piece table
with the rows of §8 (one table `W` for everything; `verifySteps` takes `W` and `tbl` as
parameters, like `describeT`).

### 1.4 Rows (bodies verbatim where a fragment depends on the variable order)

* Node rows (`Lib/Nodes.lean`): `introAxLB “e np p s. …”` (`:44`), `introVerumB “e v s.”`
  (`:62`), `introAndB “e cq cp r dq dp q p s. !andIntroGraph e s p q dp dq → !qqAndDef r p q → r ∈ s
  → !fstIdxDef cp dp → !insertDef cp p s → derivation.sigma dp → !fstIdxDef cq dq → !insertDef
  cq q s → derivation.sigma dq → derivation.sigma e”` (`:80-84`), `introOrB “e c c' r d q p s.”`
  (`:103`: `insertDef c' q s`, `insertDef c p c'`), `introAllB “e c ss fp r d p s.”` (`:125`:
  `freeGraph fp p`, `setShiftGraph ss s`, `insertDef c fp ss`), `introExsB “e c pt r d t p s.”`
  (`:148`: `(isSemiterm).pi 0 t`, `substs1Graph pt t p`, `insertDef c pt s`), `introWkB “e c d s.”`
  (`:170`: `bitSubsetDef c s`), `introShiftB “e ss c d.”` (`:188`: `setShiftGraph ss c`,
  conclusion for `e` with `shiftRuleGraph e ss d` — the node's sequent IS `ss`), `introCutB
  “e c₂ np c₁ d₂ d₁ p s.”` (`:207`), `introAxmB “e p s.”` (`:231`: `(Theory.Δ₁ch TAct).sigma p`).
  Totality `totAxLB “p s. ∃ e”` … `totAxmB` (`:249-324`). `dlenAxLB “l p s e. axLGraph e s p →
  setLenDef l s → dlenGraph.sigma e (l + 1)”` (`:334`), `dlenAndB “l nq np dq dp q p s e. … →
  dlenGraph.sigma e (l + np + nq + 1)”` (`:358`), `dlenExsB “lt l n d t p s e. … termLenGraph lt t
  → … e (l + lt + n + 1)”` (`:399`), the unary ones `(l + n + 1)`. Bridges `derivationSigmaPi`,
  `dlenGraphSigmaPi`, `axSigmaPi` (`:468-540`). `axiomRec σ` (`:554`), `indRecB “K s fv b m p.”`
  (`:617`), `totIndBody` (`:634`). NOTE: no row concludes `fstIdxDef s e` from a node graph —
  §8 adds the ten `fstIdx<Tag>` rows (V-facts `fstIdx_axL …`, `Proof/Basic.lean:267-276`).
* Sets (`Lib/Sets.lean`): `memInsertSelfB “t s x. insertDef t x s → x ∈ t”` (`:34`),
  `memInsertOfMemB “t y s x.”` (`:47`), `subsetInsertB` (`:62`), `insertSubsetB “u x t s. subset s
  t → x ∈ t → insertDef u x s → subset u t”` (`:77`), `emptySubsetB` (`:96`), `insertEqOfMemB
  “t s x. x ∈ s → insertDef t x s → t = s”` (`:108`), `subsetMemB` (`:123`), `subsetRefl/Trans`,
  `isFormulaSetOfNoMem` + `notMemEmpty` (`:167/181`), `isFormulaSetInsertB “t p s.”` (`:193`),
  `isFormulaSetMemB` (`:228`), the four polarity bridges (`:243-284`), `shiftMemSetShiftB “y t x
  s.”` (`:302`), `memSetShiftInvB “y t s. setShiftGraph t s → y ∈ t → ∃ x, x ∈ s ∧ shiftGraph y x”`
  (`:319`), `isFormulaSetSetShift/OfSetShift` (`:338/356`), `insertTotalB “s x. ∃ t”` (`:376`),
  `setShiftTotal/shiftTotal/freeTotal` (`:388-412`).
* Lengths (`Lib/Lengths.lean`): `setLenInsertLeB “lx ls l t s x. insertDef t x s → setLenDef l t
  → setLenDef ls s → formulaLenGraph lx x → l ≤ ls + lx”` (`:117`), `setLenEmptyB` (`:136`),
  `formulaLenRelB` (`:150`: `∃ M s, termLenVecGraph M k v ∧ listSumDef s M ∧ l = s + 1`),
  `formulaLenAndB “lr lq lp r q p n.”` (`:218`), `formulaLenAllB` (`:256`), `formulaLenNegB`
  (`:292`), `termLenBvar/Fvar/FuncB` (`:311-341`), `bnumEven/OddB` (`:362/381`), the term-level
  laws `twoMulAdd…`, `addLeAdd`, `leAddRight`, `leTrans`, `leOfEq`, `leOfLeEq`, `succLeSucc`,
  `addAssoc/Comm` (`:418-581`); totality `formulaLen/termLen/termLenVec/listSum/setLen/bnumTotal`
  (`:42-103`).
* Occ (`Lib/Occ.lean`): `dlenLeafLeB “a l n. n = l + 1 → l ≤ a → n ≤ a + 1”` (`:555`),
  `dlenUnaryLeB` (`:569`), `dlenBinaryLeB “c b a nq np l n. n = l + np + nq + 1 → l ≤ a → np ≤ b →
  nq ≤ c → n ≤ a + b + c + 1”` (`:585`), `addLeAdd₃`, `leOfEqLe`, `leAddLeAdd`, `leAddLeft`,
  `leRefl` (`:601-656`), `dslSuccEqSuccO` (`:671`). The `fvOcc*`/`setLenSetShiftLe` rows
  (`:353-540`) are NOT used by the fragments (decision 6 makes shifted lengths exact through the
  re-description).
* Walk rows (`Lib/Walk.lean`): `zeroLtSucc/succLtSucc` (`:52/65`), the eight closed symbol rows
  (`:80-171`), `isUTermVecOfSemitermVecLAct` (`:186`), `isSemitermVecQVec` (`:201`),
  `substs1SubstsB “y w t p. adjoinDef w t 0 → substs1Graph y t p → substsGraph y w p”` (`:217`),
  `isSemiformulaSubsts1C`/`isFormulaFreeC` (arity `0 + 1`, `:237/252`), `piArityOneToC/CToOne`.
* Formulas (`Lib/Formulas.lean`): totality (`:299-537`), formation (`:553-791`), the commutation
  rows `neg*/substs*/shift*/free*` (`:807-1247`, top-down: existential outputs) and inversion
  rows (`:1263-1475`). Of these the fragments use only `neg*` (both directions coincide for
  `neg`: `negAndB` `:863` concludes `∃ np nq, negGraph np p ∧ negGraph nq q ∧ qqOrDef y np nq` —
  usable bottom-up too once `np, nq` are described: see §3.6) and the FORMATION rows
  `isSemiformulaNeg/Shift/Subst/Substs1` (`:665-707`).
* Bridge (`Lib/Bridge.lean`): the `axm` chain in the closing docstring (`:884-924`), `axIsFormula`
  (`:876`), `indBodyIntro` (11 variables), the `LAct → ℒₒᵣ` graph bridges.
* RowInst (`RowInst.lean`): `quote_<row>B`, `inst_<row>` at arbitrary closed witnesses, the
  canonical fact codes (`:1-120` header, §2 there): `piFact/sigmaFact/tPiFact/…/andFact/…/
  negFact/shiftFact/substFact/substs1Fact/freeFact/qVecFact/tsvFact/tshvFact`, each with
  `IsFormula`-ness, the shift law and the multiplicative length bound. Only the 87 WALK rows are
  instantiated there; §8 lists the rows that still need `inst_` lemmas (Nodes, Sets, Lengths,
  Occ, and the new rows) — the generator `arith/scripts/gen_rowinst.py` produces them.

---

## 2. Two new step tags (ANALYSIS; the `sSub` question resolved)

### 2.1 Why not a sub-chain step

The brief's `sSub steps' G'` ("cut on `G'`, left premise = the child chain") would make
`applyStep` call `chainCode`, and `chainAux`'s `PR` succ clause calls `applyStep`
(`Chain.lean:1302-1306`) — a circular definition, not a `PR`/`Fixpoint` construction with fixed
parameters. A graph-fixpoint `ApplyGraph` over nested lists would need `StrongFinite` on
`⟪…, s', e'⟫` where the inner continuation `e'` is not smaller than `e`. Both rejected. The
resolution is to keep the list FLAT: the child's steps run BEFORE the parent's node steps in the
SAME chain, so when the parent needs `G_child` all four of its conjuncts are already facts in
the context (`derivation.sigma e`, `fstIdxDef s' e`, `dlenGraph.sigma e n`, `n ≤ ū`); the only
missing move is "package four facts into `∃ d n (…∧…)` and make it a hypothesis" — a cut whose
left premise is a LEAF of constant shape. That is `sGoal`.

### 2.2 `sGoal e n s ū` (tag 6) — the goal-closing cut

* Code: `sGoal e n s ū := ⟪6, e, n, s, ū⟫` — `e`, `s` eigenvariable terms `^&i`, `n` a closed
  term (`^&j`, or the `Dlen` row's sum `l + n₁ + n₂ + 1` with `&`-entries), `ū` a closed
  numeral code (`bnum v`).
* The goal predicate (one closed ℒₒᵣ-sentence, quoted once):
  `goalB : ArithmeticSemisentence 2 := “u s. ∃ d n, !(derivation TAct).sigma d ∧ !fstIdxDef s d ∧
  !(dlenGraphDef LAct).sigma d n ∧ n ≤ u”`, `PGoal := ⌜lMap emb goalB⌝`,
  `goalFact s u := subst ?[u, s] PGoal` (canonical fact code, `RowInst` §2 convention:
  `subst (listToVec [w₀, w₁]) P` in the predicate's own order — `u = #0`, `s = #1` as written).
  FACT to prove (the `inst_` lemma of the goal): `goalFact s u = ^∃ ^∃ (qBody)` with
  `instOuter [e, n] qBody = derFact e ⋏ (fstIdxFact s e ⋏ (dlenFact e n ⋏ leFact n u))`
  (`derFact e := subst ?[e] ⌜(derivation TAct).sigma⌝`, `fstIdxFact s e := subst ?[s, e]
  ⌜fstIdxDef⌝`, `dlenFact e n := subst ?[e, n] ⌜(dlenGraphDef LAct).sigma⌝`, `leFact n u :=
  subst ?[n, u] ⌜leF⌝`) — by `substs_ex` twice, `instOuterAt_subst`/`instOuter_subst_listToVec`
  (`RowInst.lean` §1) exactly as `inst_negAnd` (`:~1600`) reads a 2-existential body.
* `applyStep tbl Γ (sGoal e n s ū) d := cutRule Γ G (goalLeafCode Γ e n s ū) d` with
  `G := goalFact s ū` and
  `goalLeafCode Γ e n s ū := exsChainCode LAct [e, n] qBody (insert G Γ) (conj4Code (insert G Γ ∪ chain) A₁ A₂ A₃ A₄)`
  (`exsChainCode` `Primitives.lean:332`: `m` `exsIntro`s keeping the principal formulas, ending
  in `wkRule (insert (instOuter es q) Γ') d'`; `conj4Code S A₁ A₂ A₃ A₄ := andIntro S A₁ (A₂ ⋏ (A₃ ⋏ A₄))
  (axL (insert A₁ S) A₁) (andIntro (insert (A₂ ⋏ (A₃ ⋏ A₄)) S) A₂ (A₃ ⋏ A₄) (axL …) (andIntro … A₃ A₄
  (axL …) (axL …)))` — NEW constructor, `conj4Code_proof` from `Derivation.andIntro/axL`
  (`Proof/Basic.lean:603/610`) needing `neg Aᵢ ∈ S` for the four facts and `IsFormula`).
  Node count `2 + 1 + 3 + 4 = 10`.
* `ctxAfter Γ (sGoal e n s ū) := insert (neg (goalFact s ū)) Γ` — non-shifting; add tag 6 to
  `mem_ctxAfter_of_noShift` and to `NoDrop`.
* `StepOK` disjunct: `sTag s = 6 ∧ IsSemiterm LAct 0 e ∧ … ∧ termLen ≤ E (four times) ∧
  neg (derFact e) ∈ Γ ∧ neg (fstIdxFact s e) ∈ Γ ∧ neg (dlenFact e n) ∈ Γ ∧ neg (leFact n ū) ∈ Γ`
  — Δ₁ (memberships of Σ₁-computed codes).
* `stepCost` tag 6: `12·G + 40·|goalFact s ū| + 4·E + 16` (ANALYSIS: the cut node `G + |G| + 1`;
  the leaf's ten sequents each `≤ G + 3|G| + E` — `exsIntro`'s chain sequents carry the two
  level formulas `exsIter j (…)`, each `≤ |G|`, plus the instantiated matrix `≤ |G| + 2E`; the
  final `wkRule` one more. Read the exact constants off `dlen_exsChainCode_le`
  (`Primitives.lean`, the `(m+1)²` shape with `m = 2`) when implementing; any bound of the form
  `c₁ G + c₂ |G| + c₃ E + c₄` keeps §5.) `|goalFact s ū| ≤ |PGoal|·max(1, |ū|, |s|)` (the
  multiplicative bound of `RowInst` §2) with `|PGoal| ≥ |derivation TAct|` — the constant `C`.
* `dlen_applyStep_le` extension: `dlen (cutRule Γ G d₁ d) = setLen Γ + dlen d₁ + dlen d + 1`
  (`DlenGraph.cutRule_iff`); `dlen d₁ ≤ 10·(G + 3|G| + 2E) + …` as above.
* After the step the parent holds the HYPOTHESIS `G` (`neg G ∈ Γ`); it recovers the four facts
  with the existing tags: `sElimExs (^∃ qBody')` — `StepOK` tag 3 needs `neg (^∃ P) ∈ Γ` with
  `P := ^∃ qBody'` and `IsSemiformula 1 P` (`Chain.lean:1204`) ✓ — delivering `d = &0` and
  `neg (free P) = neg (^∃ (qBody at d := &0))` (`free_exs`, `Formulas.lean:65`); then
  `sElimExs (qBody at d := &1, n := #0)` → `n = &0`, `d = &1`; then `sSplit` three times on the
  right-nested conjunction (`Chain.lean:1205`: `neg (p ⋏ q) ∈ Γ` → `neg p`, `neg q`). Five steps,
  two shifts. Index rule: after these, an object at `&i` before `sGoal` is at `&(i + 2)`.

### 2.3 `sLemma A dA` (tag 7) — a closed lemma cut in

* Code: `sLemma A dA := ⟪7, A, dA⟫`, `A` a CLOSED `LAct`-sentence code (a numeral fact), `dA` a
  derivation code of the singleton sequent `insert A 0`.
* `applyStep tbl Γ (sLemma A dA) d := cutRule Γ A (wkRule (insert A Γ) dA) d`;
  `Derivation.wkRule` (`Proof/Basic.lean:637`) needs `IsFormulaSet (insert A Γ)` and
  `insert A 0 ⊆ insert A Γ` ✓; `Derivation.cutRule` (`:649`) needs `fstIdx d = insert (neg A) Γ`.
* `ctxAfter Γ (sLemma A dA) := insert (neg A) Γ` — non-shifting.
* `StepOK` disjunct: `sTag s = 7 ∧ IsFormula LAct A ∧ DerivationOf TAct dA (insert A 0)` — Δ₁
  (`derivationOf` is `𝚫₁`, `Proof/Basic.lean:477`; `insert A 0` is Σ₁-computed).
* `stepCost` tag 7: `2·G + 2·|A| + 2 + dlen TAct dA` — the blueprint uses `!(dlenDef TAct)`
  (Σ₁, `DerivationLength.lean:404`); `costSum` stays a `PR` over `stepCostDef` ✓.
* `dlen_applyStep_le` extension: `dlen (cutRule …) = G + (G + |A| + dlen dA + 1) + dlen d + 1`
  (`DlenGraph.cutRule_iff`, `wkRule_iff`).
* `verifySteps` fills `dA := numProof tbl A` where `numProof` (§2.4) is a Σ₁ function producing
  a derivation of `{A}` for the closed numeral sentences it supports; `verifySteps` may call
  `chainCode` (it is defined AFTER `Chain`), only `applyStep` may not.
* The same tag serves the top (§7) for the `χ`-dependent closed facts (`qqAndDef ⌜χ⌝ ⌜χ₁⌝ ⌜χ₂⌝`,
  …), where `dA` is a STANDARD constant supplied by `Lib.univ_code` — or, equivalently and
  simpler for those, a closed ROW (`m = 0`) used by `sUseHorn i 0 0 c` (`Describe.lean`'s
  closed symbol rows are the template, `rIdx_isRelConst_eq`).

### 2.4 `numProof` / `numSteps` — the closed binary-arithmetic prover (NEW producer)

A Σ₁ function of the numbers involved, producing a step list over the term-level rows of
`Lengths.lean` (`twoMulAdd`, `twoMulAddOne`, `twoMulOneAdd`, `twoMulOneAddOne`,
`twoMulOneSucc`, `addLeAdd`, `leAddRight`, `leTrans`, `leOfEq`, `leOfLeEq`, `succLeSucc`,
`addAssoc/Comm`, `:418-581`; `bnumEven/Odd` `:362/381`) plus the NEW rows of §8.5, run by
`chainCode tbl ?[A] (numSteps …) (axLFactCode Γ_final A)` — the context starts as the singleton
`{A}` (the goal, positive), the steps add closed facts, the last fact is `A` itself and the
leaf is `axLFactCode` (`Steps.lean:735`: `neg A ∈ Γ_final`). Required instances (all TRUE by
the V-level values the constructor holds; `sLemma` is sound whatever `dA` is — `StepOK` checks
it — so a false closed sentence can never be cut in):

| name | closed sentence `A` | bit-recursion | uses |
|---|---|---|---|
| N1 `addEq a b` | `bnum a + bnum b = bnum (a + b)` | on the bits of `a, b` with the four `twoMul…` rows and the carry `twoMulOneSucc` | `O(‖a‖+‖b‖)` |
| N2 `le a b` (`a ≤ b`) | `bnum a ≤ bnum b` | `bnum b = bnum a + bnum (b − a)` (N1) + `leAddRight` | `O(‖b‖)` |
| N3 `sumLe [a₁…a_k] c` (`Σ aᵢ ≤ c`) | `bnum a₁ + … + bnum a_k ≤ bnum c` | `k − 1` N1 + N2 + `leOfLeEq`, `addAssoc` | `O(k·‖c‖)` |
| N4 `mulEq a b` | `bnum a * bnum b = bnum (a·b)` | on bits of `b`: `x·(2y) = 2(xy)`, `x·(2y+1) = 2(xy) + x` (+ N1); NEW rows `twoMulMul`, `twoMulOneMul` | `O(‖b‖·‖ab‖)` — top only |
| N5 `lengthEq a` | `lengthDef (bnum ‖a‖) (bnum a)` | `‖2x‖ = ‖x‖+1`, `‖2x+1‖ = ‖x‖+1`, `‖0‖ = 0`, `‖1‖ = 1`: NEW rows `lengthTwoMul/TwoMulOne/Zero/One` (Foundation's `length` graph `lengthDef`) | `O(‖a‖)` — top only |
| N6 `cTLe z` / `cTSucc z` | `cT z + 1 = bnum (z + 1)`, `cT z ≤ bnum z` | `z` uses of `succLeSucc`/N1 on `cT` (`cT (z+1) = cT z ^+ 𝟏`, `WalkLemmas.lean:237`; `1 = bnum 1`, `bnum_one`) | `O(z)` steps of size `O(z + ‖z‖)` |
| N7 `oneLe a` (`1 ≤ a`) | `1 ≤ bnum a` | N2 with `bnum 1 = 𝟏` | `O(‖a‖)` |
| N8 `ltCT z n` | `cT z < cT n` | `ltSteps` already produces it inside the walk (`Describe.lean:1550`) — not needed here |

Cost of `dA`: `O(‖·‖)` steps in a context of `O(‖·‖)` closed facts of size `O(‖·‖)` — `O(‖g‖³)`;
for N6 `O(z²)` with `z ≤ w_ν` (paid by `ρ`'s unary charge for the leaf). The DSL numeral `1`
vs `oneO` mismatch (`Occ.lean:664-671`, `dslSuccEqSuccO`) is crossed ONCE inside N1/N6 when a
`Nodes`/`Occ` conclusion (`l + 1` in the DSL) meets the `Lengths` term-level rows.
Theorems: `numSteps_ok` (Δ₁ `ListOK`, final fact `A`) and `dlen_numProof_le ≤ C·(‖a‖ + ‖b‖ + …)³`;
`numProof` is ONE Σ₁ function by cases on a tag `⟪kind, args⟫` (a `PR` on the bit length with
the partial lists as state, or four separate `PR`s glued).

---

## 3. The canonical layout, the copy-in, and the companions (ANALYSIS)

### 3.1 Objects and dossiers

An OBJECT is an eigenvariable standing for a code the V-level constructor knows. Kinds:
formula node (with its arity `a`), term node, term vector, sequent, chain prefix, length.
The DOSSIER of a formula code `x` at arity `a` is the set of facts the walk leaves for it
(DESIGN_describe §5) PLUS exact lengths:

* formula node `y` (sub-node of `x`, arity `a_y`): its shape fact (`andF y y₁ y₂`, `allF y y₁`,
  `relF y (cT k) (cT R) v`, `verumF y`, …), `piF (cT a_y) y` (the `.pi` reading; `sigmaF` is
  dead after the bridge), and `lenF (bnum |y|) y` where `lenF l y := subst ?[l, y]
  ⌜(formulaLenGraph LAct)⌝` — the length with the NUMERAL in graph position (§3.6);
* term node `t`: `bvarF t (cT z)` / `fvarF t (cT i)` / `funcF t (cT k) (cT f) v`, `tPiF (cT a) t`,
  `tlenF (bnum |t|) t`;
* vector node `v` (non-empty; the empty vector is the literal `𝟎`, `vRef`): `adjF v t v'`,
  `tvPiF (cT k) (cT a) v`, `utvPiF (cT k) v` (atoms/functions), `tvlenF M v` is NOT carried —
  lengths are pushed through `listSum` at the atom only (§3.6);
* the closed symbol facts `isRelF/isFuncF` (closed, shift-invariant, re-derivable at cost 1 —
  NOT part of the layout: the walk emits them where needed, `DESIGN_describe.md` §3.2).

`objs(x)` := the objects of `x`'s dossier in the WALK ORDER (children before parents; the
top last), so that the top of `x` is at offset `0` and every descendant at the offsets `off`
(DESIGN_describe §4.4) — the SAME positions the walk produces, so a freshly walked formula
and a copied one look alike. `|objs(x)| = descCount x ≤ |x|`.

### 3.2 The layout of a node

For a node `ν` with sequent `s` (members `x₁ < x₂ < … < x_k` in ascending code order — a
Σ₁ list `memberList s` by a bounded loop over the bits of `s`, NEW V-function), the layout,
FROM THE OLDEST eigenvariable to the newest (so the last item is `&0`):

```
objs(x₁) … objs(x_k)                    -- member dossiers (arity 0), each with `memF xᵢ s` added below
s₁ = insert x₁ ∅, s₂ = insert x₂ s₁, …, s_k = insert x_k s_{k-1}      -- chain prefixes; s := s_k
l₁, …, l_k                               -- the length objects of the prefixes; l_s := l_k
```
so `l_s = &0`, `l_j = &(k − j)`, `s = &k`, `s_j = &(2k − j)`, the top of `x_k` at `&(2k+1)`, the top
of `x_j` at `&(2k+1) + Σ_{i>j} descCount xᵢ`. Facts present (as `neg · ∈ Γ`):
* every dossier fact of every `objs(xᵢ)`;
* `insF sᵢ xᵢ sᵢ₋₁` (`subst ?[t, x, s] ⌜insertDef⌝`; `s₀ := 𝟎` literal), `memF xᵢ s`
  (`subst ?[x, s] ⌜x ∈ s⌝`, the DSL atom), `piFS s` (`(isFormulaSet).pi`), `setLenF l_s s`,
  `leF l_s (bnum (setLen s))`, `setLenF lⱼ sⱼ` for the prefixes (dead after the chain, kept).
* NO `negF` pairs: an `axL` leaf certifies `negGraph np p` between its two member dossiers
  itself (§4.1), so nothing pair-wise is carried.
`layoutFacts ν : V` — the list of these fact codes (about `&i`s) — is a Σ₁ function of
`fstIdx ν` (and of the code tree of each member); `Layout Γ ν := ∀ f ∈ layoutFacts ν, neg f ∈ Γ
∧ IsFormulaSet Γ` (Δ₁). The goal index: at the END of `verifySteps ν`, with `σ_ν :=
shiftsV (verifySteps ν)`, the sequent object is `&(k + σ_ν)` and the fragment's last step has
left `neg (goalFact (^&(k+σ_ν)) (bnum (dlen ν))) ∈ finalCtx` — that is the statement
`verifySteps_goal` (§6.3).

Why `s` is REBUILT as a chain at every node rather than transported: (i) the `Intro` rows need
the child's sequent as `insertDef cp p s` — a fresh object anyway; (ii) the chain makes `setLen`
EXACT with no `∉` reasoning (decision 5); (iii) `IsFormulaSet` of a chain is `k` uses of
`isFormulaSetInsert` from `isFormulaSetOfNoMem`+`notMemEmpty`.

### 3.3 Copy-in (`copySteps`)

To copy an object `x` currently at `&i` into a fresh `&0`: `sIntroFact rIdx_eqTotal [^&i]`
with the NEW row `eqTotalB “x. ∃ y, y = x”` → fact `eqF &0 (^&(i+1))`; then, per fact of `x`'s
dossier, ONE congruence row transporting the fact to the new object, e.g.
`congPiB “y x n. y = x → !(isSemiformula LAct).pi n x → !(isSemiformula LAct).pi n y”`,
`congAndB “q' p' r' q p r. r' = r → p' = p → q' = q → !qqAndDef r p q → !qqAndDef r' p' q'”`
(the children have been copied FIRST, walk order), `congRelB “v' r' v R k r. r' = r → v' = v →
!qqRelDef r k R v → !qqRelDef r' k R v'”`, `congLenB “y x l. y = x → !(formulaLenGraph LAct) l x
→ …l y”`, `congMemB “s y x. y = x → x ∈ s → y ∈ s”`, and the term/vector kinds
(`congTPi/TLen/Func/Bvar/Fvar/Adj/TvPi/UtvPi`) — §8.1 lists all 18. Cost per object: `1` shift +
`≤ 3` Horn steps. `copySteps (x at &i)` := for each object of `objs(x)` bottom-up: the four
steps, with the running index bookkeeping (each copy shifts everything by one; the source
index of a later object is its original index plus the copies made so far; the target's
children are at the offsets `off` just produced). The output is `objs(x)` at `&0 … &(c−1)`
in walk order — the layout convention. `copySteps` is a Σ₁ function of the CODE `x` and the
source index `i` (a `Fixpoint` on `⟪x, i, L⟫` like the walk, or — simpler — a post-processing
of the walk's OWN list: the copy list has the same tree shape as `describeF 0 x` with every
`sIntroFact qqXTotal [children]` replaced by `sIntroFact eqTotal [src]` and every formation
step by the congruence steps; ANALYSIS: define `copySteps` by its own `Fixpoint`, reusing
`descCountF` for the offsets).

The eigenvariable-index cost of copy-in is what keeps the indices INSIDE a fragment `O(w_ν)`
for the objects the fragment uses (DESIGN §3.7's "refresh"); dead objects and facts keep
drifting upward but are never referenced (§5).

### 3.4 Chains and the extensional identification of a sequent

`chainSteps [x₁ … x_k]` (objects at known indices): `k` times `sIntroFact rIdx_insertTotal
[^&(prev), ^&(xⱼ)]` (`insertTotalB “s x. ∃ t”` → witnesses right-to-left `[x, s]`; for `j = 1`
the set witness is the literal `𝟎`) — delivering `insF sⱼ xⱼ sⱼ₋₁`; then `memInsertSelf`
(`“t s x.”` → `[x, s, t]`) for `xⱼ ∈ sⱼ` and `memInsertOfMem` (`“t y s x.”` → `[x, s, y, t]`)
`j − 1` times to lift the earlier memberships — `O(k²)` Horn steps naively; do it in ONE pass
at the end: `memF xⱼ s` needs `xⱼ ∈ sⱼ` lifted through `s_{j+1} … s_k`: `Σⱼ (k − j) = O(k²)`.
ANALYSIS: `k ≤ setLen s ≤ w_ν` so `O(k²) ≤ O(w_ν²)` steps per node — this would break the
`O(g)` step count (`Σ w_ν² ≤ g²`, times `|Γ| = O(g²)` gives `g⁴`). FIX: the NEW row
`memChainB “t s x. !bitSubsetDef s t → x ∈ s → x ∈ t”` is `subsetMem` (`Sets.lean:123`) — lift
by SUBSET instead: derive `sⱼ ⊆ s` once per `j` (`subsetInsert` `k − j` times is again
quadratic…). Use instead the k facts `sⱼ ⊆ s_{j+1}` (`subsetInsert`, 1 each) and
`subsetTrans` accumulated from the top: `s_{k-1} ⊆ s`, `s_{k-2} ⊆ s` (via `s_{k-2} ⊆ s_{k-1}`,
`subsetTrans`), … — `2k` steps; then `memF xⱼ s` = `subsetMem [sⱼ ⊆ s, xⱼ ∈ sⱼ]` — `k` steps.
Total `O(k)` ✓. `IsFormulaSet s`: `isFormulaSetOfNoMem`+`notMemEmpty` (2), then
`isFormulaSetInsert` (`“t p s.”` → `[s, p, t]`, needs `piF (cT 0) xⱼ` from the dossier) +
`isFormulaSetSigmaPi` per link: `2k` steps. Length: `setLenTotal [s]` → `l_s = &0`
(1 shift); for the chain `l_j ≤ l_{j-1} + bnum|xⱼ|` we need each prefix's length object —
`k` more `setLenTotal` shifts and `k` `setLenInsertLe` uses (`“lx ls l t s x.”` →
`[x, s, t, l, ls, lx]` with `lx := bnum|xⱼ|` a NUMERAL witness: the dossier holds
`lenF (bnum|xⱼ|) xⱼ` — exactly the antecedent `!(formulaLenGraph LAct) lx x` at `lx :=
bnum|xⱼ|` ✓), `setLenEmpty` for `l₀ = 0` (`“l. setLenDef l 0 → l = 0”`), then fold with
`leAddLeAdd` (`“b a z y x. x ≤ y + z → y ≤ a → z ≤ b → x ≤ a + b”`, `Occ.lean:629`) and
`leRefl` for the numeral summands: `l_s ≤ bnum|x₁| + … + bnum|x_k|` as a term; finally
`sLemma (N3: Σ bnum|xᵢ| ≤ bnum (setLen s))` and `leTrans` → `leF l_s (bnum (setLen s))`.
`O(k)` steps + one `sLemma`. (The `bnum (setLen s)` value: the constructor computes `setLen s`
at the V-level; the closed sentence is true because the `xᵢ` are exactly the distinct members.)

**Identifying the row's sequent object with the chain.** The `Intro` row for the child
needs `insertDef cp p s` where `s` is the PARENT's chain top and `cp` any object equal to
`insert p s`. Take `cp := t` from `sIntroFact insertTotal [^&s, ^&p]` (fact `insF t p s`).
The child's OWN layout is the chain `s'' = chain(members of insert p s)`; the child fragment
uses `s''`; the child's goal then says `fstIdxDef s'' d`, but the parent's `Intro_and` needs
`fstIdxDef cp dp` — so the parent must know `t = s''`: `subsetAntisymmB “t s. !bitSubsetDef s t
→ !bitSubsetDef t s → s = t”` (NEW; V: `mem_ext`) from (a) `s'' ⊆ t`: every member of `s''`
is in `t` (`memInsertSelf/OfMem` on `insF t p s` and the parent's `memF xᵢ s`: `k' ≤ k + 1`
steps) folded by `insertSubset` (`“u x t s. subset s t → x ∈ t → insertDef u x s → subset u t”`,
`k'` steps from `emptySubset`); (b) `t ⊆ s''`: `s ⊆ s''` by `insertSubset` along the PARENT's
chain (`k` steps from `emptySubset`, using the parent's `insF sⱼ xⱼ sⱼ₋₁` and `memF xⱼ s''`
established in (a)) and then `insert p s ⊆ s''` (one more `insertSubset` with `p ∈ s''`).
Then `congFstIdxB “t' t d. t' = t → !fstIdxDef t d → !fstIdxDef t' d”` (NEW) moves the child's
`fstIdxDef s'' d` to `fstIdxDef t d`. `O(k)` steps. The same pattern serves `orIntro`
(`insert p (insert q s)`), `allIntro` (`insert (free p) (setShift s)`, §4.5), `exsIntro`,
`cut` (both children), `wk` (`bitSubsetDef c s` for `c := s''`: direction (a) only), `shift`
(§4.8). When `p ∈ s` (duplicate; the constructor knows), `p ∈ s''` in (b) is obtained by
`eqSteps` (§3.5) and `congMem` instead of `memInsertSelf`, and the chain `s''` has `k` members,
not `k + 1` — the length bound is then exact automatically.

### 3.5 The identification walk `eqSteps x y`

Two objects with full term-level dossiers denoting the SAME code: derive `eqF x y` by the
NEW injectivity rows, bottom-up in parallel: `eqOfAndB “y q' p' q p x. !qqAndDef x p q →
!qqAndDef y p' q' → p = p' → q = q' → x = y”` (and `Or/All/Exs`), `eqOfRelB “y v' v R k x.
!qqRelDef x k R v → !qqRelDef y k R v' → v = v' → x = y”` (`NRel`; the symbol numerals are
syntactically identical on both sides since both were written as `cT k`, `cT R`), `eqOfVerumB
“y x. !qqVerumDef x → !qqVerumDef y → x = y”` (`Falsum`), `eqOfAdjB “w' v' t' w v t. !adjoinDef w
t v → !adjoinDef w' t' v' → t = t' → v = v' → w = w'”`, `eqOfFuncB`, `eqOfBvarB “t' t z. !qqBvarDef
t z → !qqBvarDef t' z → t = t'”`, `eqOfFvarB`; the empty vector is the literal `𝟎` on both sides
(`eqRefl` on `𝟎`, `leRefl`'s twin `eqReflB “x. x = x”` NEW). `O(|x|)` steps. Used at: duplicate
inserts (§3.4), `shiftRule` (§4.8: the member `yᵢ` vs the certified shift of the re-described
unshift), the `axm` induction chain (`shift b = b`, §4.10), and the top's `x_χ = ⌜χ⌝` pin
(§7.1). Since eqSteps only READS dossiers, both objects must have walk-style (term-level)
dossiers — which every object in this design has (decision 6).

### 3.6 Certified re-description (`certNeg/certShift/certSubst/certFree`) and lengths

For an output code `y = f(x)` (`f ∈ {neg, shift, substs w, substs1 t, free}`) with `x`'s
dossier in context at known offsets: (1) `describeF W a y` — the walk on the KNOWN code `y`
(fresh objects, full dossier, `descCountF y` shifts); (2) `sIntroFact rIdx_fTotal [x]`
(`negTotal/shiftTotal/substsTotal/substs1Total/freeTotal`) → `y' = &0` with `fF y' x`;
(3) certify `y' = y_top` by the CERTIFICATION walk over the two dossiers: NEW bottom-up rows
`negRelCertB “y r v R k. isRel k R → utvPi k v → qqRelDef r k R v → qqNRelDef y k R v → negGraph y r”`
(V: `neg_rel`), `negAndCertB “y nq np r q p n. pi n p → pi n q → qqAndDef r p q → negGraph np p →
negGraph nq q → qqOrDef y np nq → negGraph y r”` (V: `neg_and`, `Formula/Functions.lean:88`),
`negAllCertB`, …; `shiftAndCertB` (V: `shift_and` `:303`), `shiftRelCertB “y u r v R k. … →
qqRelDef r k R v → termShiftVecGraph u k v → qqRelDef y k R u → shiftGraph y r”` with the TERM
level `tshvNilCertB “k. termShiftVecGraph 𝟎 0 𝟎”`, `tshvAdjCertB “u' u t' t v' v k. termShiftGraph
t' t → termShiftVecGraph u k v → adjoinDef v' t v → adjoinDef u' t' u → termShiftVecGraph u' (k+1) v'”`,
`termShiftBvarCertB “t' t z. qqBvarDef t z → qqBvarDef t' z → termShiftGraph t' t”`,
`termShiftFvarCertB “t' t x. qqFvarDef t x → qqFvarDef t' (x + 1) → termShiftGraph t' t”` (the
walk wrote `cT (x+1)` for the output leaf — matches `x + 1` at `x := cT x` by `cT_succ` ✓),
`termShiftFuncCertB`; `substs*CertB` likewise with `termSubstVecGraph`, `termSubstBvarCertB
“e w z t. qqBvarDef t z → nthDef e w z → termSubstGraph e w t”`, `termSubstFvarCertB`,
`termSubstFuncCertB`, `substsAllCertB` (through `qVecGraph u w`: `qVecTotal` + the entries:
`qVecNthZeroB “u w. qVecGraph u w → nthDef ^&? …”` — Foundation's `qVec w = #0 ∷ termBShiftVec w`;
the entry rows `qVecNth0 “u w. qVecGraph u w → ∃ z, qqBvarDef z 0 ∧ nthDef z u 0”`, `qVecNthSucc
“e' e u w i. qVecGraph u w → nthDef e w i → termBShiftGraph e' e → nthDef e' u (i+1)”`, and the
`termBShift` cert rows — the `qVec` level is needed only under quantifiers of a SUBSTITUTED
formula, i.e. for `exsIntro` (`substs1 t p` with `p` a 1-formula: only `#0`, no `qVec` unless
`p` has inner quantifiers — it may) and the root's `subst (t ∷ 0) ⌜χ⌝`); `freeCertB “fp sp z p.
qqFvarDef z 0 → shiftGraph sp p → substs1Graph fp z sp → freeGraph fp p”` (V: `free p = substs1
&0 (shift p)`, `Formulas.lean:38-41` as `Occ.lean:497-503` records). Then `congF` moves the
graph fact `fF y' x` onto the walked top `y_top` via `eqF y' y_top` — or simpler: certify
DIRECTLY `fF y_top x` (the cert rows conclude the graph fact for the walked object) and never
introduce `y'` at all: the totality step (2) is unnecessary — DROP IT. So a certified
re-description is: the walk + `O(|y|)` cert steps; every atom's vector is a walked vector
(terms known) — no opaque vectors anywhere.

Lengths (`lenSteps x`): bottom-up over the dossier, one `sIntroFact rIdx_formulaLenTotal [y]`
per node → `m_y = &0` with `formulaLenF m_y y`; then the exact equation by the `Lengths` row
(`formulaLenAndB “lr lq lp r q p n.”` → `[n, p, q, r, lp, lq, lr]` with `lp := bnum|p|`,
`lq := bnum|q|` NUMERAL witnesses — matching the children's `lenF (bnum|p|) p` — delivering
`m_y = bnum|p| + bnum|q| + 1`; atoms: `formulaLenRelB` delivers `∃ M s, termLenVecGraph M k v ∧
listSumDef s M ∧ l = s + 1` — `useRowEx`-style (`sIntroFact` + `sElimExs` + `sSplit` ×2) with
the vector's term lengths: NEW rows `termLenVecNilB “k n. termLenVecGraph 𝟎 0 𝟎”`,
`termLenVecAdjB “M' M l t v' v k. termLenGraph l t → termLenVecGraph M k v → adjoinDef v' t v →
adjoinDef M' l M → termLenVecGraph M' (k+1) v'”`, `listSumNilB`, `listSumAdjB “s' s l M M'.
listSumDef s M → adjoinDef M' l M → listSumDef s' M' → s' = l + s”` — plus functionality
`termLenVecFunB`/`listSumFunB` to match the row's existential `M, s` with the ones built
bottom-up (or state `formulaLenRelB`'s cousin `formulaLenRelCertB` with `M, s` UNIVERSAL: `“l s M
p v R k. isRel k R → utvPi k v → qqRelDef p k R v → termLenVecGraph M k v → listSumDef s M →
formulaLenGraph l p → l = s + 1”` — NEW, preferred); terms: `termLenBvarB` (`l = z + 1` at
`z := cT z`), `termLenFvarB`, `termLenFuncB` (as `Rel`)); then `sLemma (N1/N6)` for the closed
sum (`bnum|p| + bnum|q| + 1 = bnum(|p|+|q|+1)`, `cT z + 1 = bnum(z+1)`, …) and `eqTransB “z y x.
x = y → y = z → x = z”` (NEW) → `m_y = bnum|y|`; finally `congLenNumB “l' l y. l = l' →
formulaLenGraph l y → formulaLenGraph l' y”` → `lenF (bnum|y|) y` ✓ (the numeral now sits in the
graph position, which is what `setLenInsertLe` and `dlenExs` consume). `O(|x|)` steps + `|x|`
`sLemma`s (each `O(‖x‖³)` inside, `2|Γ|` outside). ANALYSIS: fold `lenSteps` INTO the walk
(`describeF` emitting the length steps per node) or run it as a separate bottom-up producer over
the walk's offsets — separate is simpler for the walk's author; the design assumes SEPARATE
(`lenSteps W x` at the offsets of `describeF`), invoked right after every walk.

---

## 4. The ten fragments (ANALYSIS)

Notation. `Γ_ν` = the layout of §3.2 for `ν`'s sequent `s` (`k` members `x₁ … x_k`, `s = &k`,
`l_s = &0`); `ū_ν := bnum (dlen ν)`, `ū_l := bnum (setLen s)`; "at `x`" = the current index of
object `x` (statically computed by the producer: an object introduced when the shift count
was `c₀`, at current count `c`, is `&(c − c₀ − 1)`). Witness lists are the DSL variable list
RIGHT-TO-LEFT (DESIGN_describe §1.1). A row use is `mkStep W (rIdx_row) ev` (`Describe.lean:1000`;
tag from the piece table). All steps are `Γ`-independent (only `ρ` and static indices).

### 4.0 The common shape

```
verifySteps ν = prologue(ν)                                  -- child sequents, layouts (§3.3–3.6)
             ++ [ verifySteps ν₁ ++ recover(ν₁) ]            -- child 1 (if any), then G_{ν₁} → facts
             ++ rebuild/copy for child 2 ++ [ verifySteps ν₂ ++ recover(ν₂) ]
             ++ node(ν)                                       -- the Intro/Dlen rows, the bound, sGoal
```
* `recover(ν')` (5 steps, 2 shifts, §2.2): `sElimExs`, `sElimExs`, `sSplit` ×3 — leaves
  `d' = &1`, `n' = &0`, facts `derF d'`, `fstIdxF s'' d'`, `dlenF d' n'`, `leF n' ū_{ν'}` — where
  `s''` is the CHILD's chain top (now at `&(k' + σ_{ν'} + 2)`).
* `node(ν)` for a node with node graph `tot<Tag>` (witness order per `Nodes.lean:249-324`),
  children facts as above, the row-specific antecedents `A_tag` (below):
  1. `sIntroFact rIdx_tot<Tag> [witnesses]` → `e = &0`, fact `<tag>Graph e s …` (everything
     shifts by 1).
  2. `sUseHorn rIdx_fstIdx<Tag> [...]` → `fstIdxF s e` (NEW rows, §8.2).
  3. `sUseHorn rIdx_intro<Tag> [e, …, s]` (antecedents `A_tag` + the children's `derF dᵢ`,
     `fstIdxF cpᵢ dᵢ` moved onto the row's `cp` objects by `congFstIdx`, §3.4) → `derF e`.
  4. `sUseHorn rIdx_dlen<Tag> [...]` (antecedents `<tag>Graph e …`, `dlenF dᵢ nᵢ`, `setLenF l_s s`
     (+ `tlenF lt t` for `exs`)) → `dlenF e T` with `T` the row's sum term (`l_s + n₁ + n₂ + 1`,
     `l_s + 1`, `l_s + lt + n' + 1`).
  5. `sUseHorn rIdx_eqRefl [T]` → `eqF T T`; `sUseHorn rIdx_dlenBinaryLe [ū₂, ū₁, ū_l, n₂, n₁, l_s, T]`
     (`“c b a nq np l n.”`; leaf: `dlenLeafLe [ū_l, l_s, T]`; unary: `dlenUnaryLe [ū₁, ū_l, n₁, l_s, T]`;
     `exs`: `dlenBinaryLe` with `np := lt`, `b := bnum|t|`) → `leF T (ū_l + ū₁ + ū₂ + 1)`.
  6. `sLemma (bnum(setLen s) + bnum(dlen ν₁) + bnum(dlen ν₂) + 1 ≤ bnum(dlen ν))` (N3 — TRUE:
     `DlenGraph.<tag>_iff`, `DerivationLength.lean:283-…`) ; `sUseHorn rIdx_leTrans [ū_ν, ū_l+…+1, T]`
     → `leF T ū_ν`.
  7. `sGoal (^&e) T (^&s) ū_ν` → `neg (goalFact s ū_ν) ∈ Γ`. END.
  Steps `node(ν)`: 8 (+ the `sLemma`), shifts 1. Row arities: `introAnd` has `m = 9` → the
  standardness cap `M := 9` (`sGoal` has 4 witnesses; `dlenExs` 8).
* `prologue` and the per-tag antecedents `A_tag`:

### 4.1 `axL s p` (leaf)

Live: `x_i = p`, `x_j = neg p` members (the constructor knows `i, j`; `j = i` impossible).
`A_axL`: `p ∈ s`, `negGraph np p`, `np ∈ s`, `piFS s`. Steps: `certNeg xᵢ xⱼ` (§3.6: eqSteps on
the atom vectors of the two dossiers + `neg*Cert` bottom-up, `O(|p|)`) → `negF xⱼ xᵢ`; then
`node`: `totAxL [xᵢ, s]` (`“p s.”` → `[s, p]`), `fstIdxAxL`, `introAxL [e, xⱼ, xᵢ, s]`
(`“e np p s.”` → `[s, p, np, e]`), `dlenAxL [l_s, xᵢ, s, e]` (`“l p s e.”` → `[e, s, p, l]`),
`dlenLeafLe`, `sLemma (bnum(setLen s) + 1 ≤ bnum(dlen ν))`, `leTrans`, `sGoal`. Total
`O(|p|) + 9` steps, 1 shift. `dlen`: `dlen ν = setLen s + 1`, `w_ν = 1 + setLen s ≥ |p|` ✓.

### 4.2 `verumIntro s` (leaf)

Live: member `x_i = ^⊤` with `verumF xᵢ`. `A`: `piFS s`, `qqVerumDef v`, `v ∈ s`. `node` with
`totVerumIntro [s]`, `introVerum [e, xᵢ, s]` (`“e v s.”` → `[s, v, e]`), `dlenVerum`,
`dlenLeafLe`. 9 steps.

### 4.3 `andIntro s p q dp dq`

Live: member `r = xᵢ` with `andF r p q` (the objects `p`, `q` are inside `objs(r)` at offsets
`cq + 1`, `1` from `r`'s top, DESIGN_describe §4.2 (F∧)). `A_and`: `andIntroGraph e s p q dp dq`,
`qqAndDef r p q`, `r ∈ s`, `fstIdxDef cp dp`, `insertDef cp p s`, `derF dp`, same for `q`.
Prologue for child 1 (`s' = insert p s`, members `M' = sort(members s ∪ {p})`, `k' = k` or
`k + 1`):
1. `copySteps` for every `y ∈ M'` in ascending order (`p`'s block copied from `objs(r)`'s
   sub-block; inherited members from their blocks) — `Σ descCount` shifts.
2. `chainSteps M'` + `IsFormulaSet` + lengths (§3.4) → `s''`, `l_{s''}` with
   `leF l_{s''} (bnum(setLen s'))` (`sLemma` N3; if `p ∈ s` the chain omits the duplicate and the
   `p ∈ s''` fact comes from `eqSteps p xⱼ` + `congMem`).
3. `sIntroFact rIdx_insertTotal [^&s, ^&p]` → `cp = &0`, `insF cp p s` (`“s x. ∃ t”` → `[x, s]`).
4. Identification `eqF cp s''` (§3.4, `O(k)`), kept for step 3 of `node`.
   NOTE the order 3–4 vs 2: `cp` must be introduced BEFORE the chain's tail so that the child's
   layout ends with `[s₁''…s_{k'}'', l₁…l_{k'}]`; concretely: copies, `cp`, chain, lengths.
   `cp` then sits just above the chain block; its index inside the child is irrelevant.
Then `verifySteps dp ++ recover(dp)`; then `congFstIdx [d₁, s'', cp]` (`fstIdxF cp d₁`). Then the
SAME prologue for child 2 (`insert q s`; the copies are made again — the earlier copies have
drifted by `σ_{dp} + 2 + …`, but copying from the ORIGINAL blocks or from the first copies is
the same cost; copy from the parent's original layout at its current indices), `verifySteps dq
++ recover(dq)`, `congFstIdx`. Then `node`: `totAndIntro [dq, dp, q, p, s]` (`“dq dp q p s.”` →
`[s, p, q, dp, dq]`), `fstIdxAnd`, `introAnd [e, cq, cp, r, dq, dp, q, p, s]` (`“e cq cp r dq dp q p
s.”` → `[s, p, q, dp, dq, r, cp, cq, e]`), `dlenAnd [l_s, n₂, n₁, dq, dp, q, p, s, e]`
(`“l nq np dq dp q p s e.”` → `[e, s, p, q, dp, dq, np, nq, l]`), `dlenBinaryLe`, `sLemma`,
`leTrans`, `sGoal`. Prologue cost: `O(setLen s')` steps and shifts per child.

### 4.4 `orIntro s p q d`

As 4.3 with ONE child, `s' = insert p (insert q s)`: `c' := insertTotal [s, q]`, `c :=
insertTotal [c', p]`; the chain over `members s ∪ {p, q}`; identification `c = s''` (two
insert levels in (b)). `introOr [e, c, c', r, d, q, p, s]` (`“e c c' r d q p s.”`), `dlenOr
[l_s, n', d, q, p, s, e]` (`“l n d q p s e.”`), `dlenUnaryLe`.

### 4.5 `allIntro s p d`

Live: member `r = xᵢ` with `allF r p`, `p` at offset `1`, arity `1` (`piF (cT 1) p`). Child
sequent `insert (free p) (setShift s)`, members `{shift xⱼ} ∪ {free p}` — ALL FRESH:
1. for each member `xⱼ`: `describeF W 0 (shift xⱼ)` + `lenSteps` + `certShift xⱼ →` `shiftF yⱼ xⱼ`
   (§3.6; `O(|xⱼ| + fvOccF xⱼ)` steps — `|shift x| = |x| + fvOccF x`, `ShiftLen.lean:364`, paid
   by `ρ` at the child: `setLen s' ≥ Σ|shift xⱼ|`);
2. `free p`: `describeF W 0 (shift p)` + `certShift` (arity 1), `qqFvarTotal [cT 0]` → `fz`,
   `adjoinTotal [fz, 𝟎]` → `w` (`adjF w fz 𝟎`), `describeF W 0 (free p)` + `lenSteps` +
   `certSubst (w, shift p)` → `substF fp w sp`; `substsSubsts1 [fp, w, fz, sp]` (NEW converse of
   `substs1Substs`) → `substs1F fp fz sp`; `freeCert [fp, sp, fz, p]` → `freeF fp p`;
3. `sIntroFact rIdx_setShiftTotal [^&s]` → `ss`, `setShiftF ss s`; `insertTotal [ss, fp]` → `c`;
4. `chainSteps` over the fresh members, `IsFormulaSet`, lengths (`sLemma` N3 with the TRUE
   `setLen (insert (free p) (setShift s))` — exact, no injectivity lemma needed: the summands are
   the walked lengths of the actual distinct members);
5. identification `c = s''`: (a) `yⱼ ∈ ss` by `shiftMemSetShift [yⱼ, ss, xⱼ, s]` (`“y t x s.”` →
   `[s, x, t, y]`), then `memInsertOfMem` into `c`; `fp ∈ c` by `memInsertSelf`; fold
   `insertSubset` → `s'' ⊆ c`. (b) `c ⊆ s''`: `ss ⊆ s''` through the parent's chain and the NEW row
   `setShiftInsertB “u' u y x s' s. !insertDef s' x s → !(setShiftGraph LAct) u s → !(shiftGraph
   LAct) y x → !insertDef u' y u → !(setShiftGraph LAct) u' s'”` + `setShiftEmptyB “u.
   !(setShiftGraph LAct) u 0 → u = 0”` + `setShiftFunB` (V-lemmas: `setShift_insert` (GAP —
   `mem_ext` + `mem_setShift_iff`), `setShift_empty` ✓ `Proof/Basic.lean:109`): objects `uⱼ =
   setShift sⱼ` (`setShiftTotal`, `k` shifts), `u'ⱼ = insert yⱼ u_{j−1}` (`insertTotal`), `u'ⱼ = uⱼ`
   (`setShiftInsert` + `setShiftFun`), and `uⱼ ⊆ s''` by `insertSubset` + `congSubsetL`; then
   `insert fp ss ⊆ s''`. `O(k)`.
6. `verifySteps d ++ recover(d)`, `congFstIdx`. `node`: `totAllIntro [d, p, s]`, `introAll
   [e, c, ss, fp, r, d, p, s]` (`“e c ss fp r d p s.”` → `[s, p, d, r, fp, ss, c, e]`), `dlenAll`,
   `dlenUnaryLe`.
Steps `O(setLen s')`.

### 4.6 `exsIntro s p t d`

Live: member `r = xᵢ`, `exsF r p`, `p` arity 1. Child sequent `insert (substs1 t p) s`.
1. `describeT W 0 t` (`Describe.lean:1764`) + term `lenSteps` → `t̂`, `tPiF (cT 0) t̂`,
   `tlenF (bnum|t|) t̂` (`O(termLen t)` — exactly `ρ`'s extra charge, `dlenExsB`);
2. `adjoinTotal [t̂, 𝟎]` → `w`; `describeF W 0 (substs1 t p)` + `lenSteps` + `certSubst (w, p)`
   (`O(|substs1 t p|)`, paid by the child's sequent) → `substF pt w p`; `substsSubsts1 [pt, w, t̂, p]`
   → `substs1F pt t̂ p`;
3. copies of the inherited members, `cp := insertTotal [s, pt]`, chain, lengths, identification
   (as 4.3; duplicate case via `eqSteps pt xⱼ`);
4. child, recover, `congFstIdx`; `node`: `totExsIntro [d, t̂, p, s]` (`“d t p s.”`), `introExs
   [e, cp, pt, r, d, t̂, p, s]` (`“e c pt r d t p s.”` → `[s, p, t, d, r, pt, c, e]`; antecedent
   `(isSemiterm).pi 0 t` = `tPiF (cT 0) t̂` — NB the row writes the arity as the literal `0` =
   `𝟎 = cT 0` ✓ `cT_zero`), `dlenExs [bnum|t|, l_s, n', d, t̂, p, s, e]` (`“lt l n d t p s e.”` →
   `[e, s, p, t, d, n, l, lt]`, `lt := bnum|t|` from `tlenF`), `dlenBinaryLe [ū_{d}, bnum|t|, ū_l,
   n', bnum|t|, l_s, T]` (`np := lt`, `b := lt` with `leRefl` — one extra `leRefl [bnum|t|]`),
   `sLemma (bnum(setLen s) + bnum|t| + bnum(dlen d) + 1 ≤ bnum(dlen ν))`, `leTrans`, `sGoal`.

### 4.7 `wkRule s d'`

FACT: `Phi`'s `wk` clause is `fstIdx d' ⊆ s` (`Proof/Basic.lean:286-297`; `introWkB` `:170`),
so the CHILD's sequent is a SUBSET — no formula is introduced at `wk` (DESIGN §3.3's "wk
introduces arbitrary formulas" is wrong; only `cut` does). Child members `M' ⊆ members s`:
copies of `M'`, chain `s''`, lengths (`sLemma` N3 over `M'`); `s'' ⊆ s` by direction (a) only
(`memF xⱼ s` + `insertSubset` fold, `k'` steps); child, recover; `node`: `totWkRule [d', s]`,
`introWk [e, s'', d', s]` (`“e c d s.”` → `[s, d, c, e]`; antecedents `piFS s`, `fstIdxF s'' d'`
(the child's own — no `congFstIdx`), `subF s'' s`, `derF d'`), `dlenWk`, `dlenUnaryLe`.
`O(k')` + 8 steps.

### 4.8 `shiftRule s d'`

FACT: `introShiftB “e ss c d. fstIdxDef c d → setShiftGraph ss c → derivation d →
shiftRuleGraph e ss d → derivation e”` — the node's sequent is the SHIFT of the child's. The
child's members are the unshifts `x'ⱼ` (codes the constructor computes: `s = setShift s'`,
`mem_setShift_iff`):
1. for each `j`: `describeF W 0 x'ⱼ` + `lenSteps`; `describeF W 0 (shift x'ⱼ)` + `certShift` →
   `y''ⱼ` with `shiftF y''ⱼ x'ⱼ`; `eqSteps y''ⱼ xⱼ` (the member object, §3.5) → `eqF y''ⱼ xⱼ`;
   `congShiftL [xⱼ, y''ⱼ, x'ⱼ]` → `shiftF xⱼ x'ⱼ`. (`O(|xⱼ|)` each; `|x'ⱼ| ≤ |xⱼ|`.)
2. chain `s''` over `{x'ⱼ}`, lengths (`sLemma` N3 with `setLen s'`, TRUE); `setShiftTotal [s'']`
   → `ss`, `setShiftF ss s''`;
3. `ss = s`: (a) `ss ⊆ s`: `setShiftInsert` chain on `s''` (as 4.5(b), objects `uⱼ`), each
   `shift x'ⱼ = xⱼ ∈ s`, `insertSubset` fold; (b) `s ⊆ ss`: `xⱼ ∈ ss` by `shiftMemSetShift [xⱼ, ss,
   x'ⱼ, s'']`, `insertSubset` fold along the parent's chain; `subsetAntisymm` → `eqF ss s`;
   `congSetShiftL [s, ss, s'']` → `setShiftF s s''`.
4. child, recover (its goal is `fstIdxF s'' d'`); `node`: `totShiftRule [d', s]`, `fstIdxShift`,
   `introShift [e, s, s'', d']` (`“e ss c d.”` → `[d, c, ss, e]`), `dlenShift [l_s, n', d', s, e]`,
   `dlenUnaryLe`, …
`O(setLen s)` steps. No `shift`-injectivity lemma is needed anywhere (the exact lengths are the
walked ones).

### 4.9 `cutRule s p d₁ d₂`

The cut formula `p` is the ONE arbitrary formula of the calculus: `describeF W 0 p` +
`lenSteps` (`O(|p|)`, paid by BOTH children's sequents), `describeF W 0 (neg p)` + `lenSteps` +
`certNeg` → `negF np p` (`O(|p|)`). Child 1: copies + chain over `members s ∪ {p}`, `c₁ :=
insertTotal [s, p]`, identification; `verifySteps d₁`, recover, `congFstIdx`. Child 2: the same
with `np`, `c₂`. `node`: `totCutRule [d₂, d₁, p, s]` (`“d₂ d₁ p s.”`), `introCut [e, c₂, np, c₁, d₂,
d₁, p, s]` (`“e c₂ np c₁ d₂ d₁ p s.”` → `[s, p, d₁, d₂, c₁, np, c₂, e]`), `dlenCut`, `dlenBinaryLe`.
`formulaLen (neg p) = formulaLen p` (`formulaLenNegB`) is not needed — `neg p` is walked with
its own exact length.

### 4.10 `axm s p`

Live: member `xᵢ = p`. `A_axm`: `piFS s`, `p ∈ s`, `(Theory.Δ₁ch TAct).sigma p`. Two cases the
constructor decides at the V-level (`mem_TAct_class_iff`, `tact_ch_eq`, `Nodes.lean:582-596`):
* **(i) a standard axiom `σ`** (the four action sentences, every `𝗣𝗔⁻` axiom — a FIXED finite
  list): `pinSteps σ xᵢ` — walk `xᵢ`'s dossier against the closed shape facts of the numerals
  `⌜σ⌝, ⌜σ₁⌝, …`: NEW closed rows per σ-subterm (`“!qqAndDef ↑⌜σ⌝ ↑⌜σ₁⌝ ↑⌜σ₂⌝”`, `m = 0`, `Lib.of_pa`
  by `complete` — unary numerals, a CONSTANT of the family) and the functionality rows
  `qqAndFunB “y' q p y. !qqAndDef y p q → !qqAndDef y' p q → y = y'”` (+ `Or/All/Exs/Rel/NRel/Func/
  Adj/Bvar/Fvar`, NEW) with `cong` to rewrite the children's equalities in; result `eqF xᵢ ⌜σ⌝`,
  then `axiomRec σ [xᵢ]` (`“p. p = ⌜σ⌝ → Δ₁ch.sigma p”`, `Nodes.lean:554`). `O(|σ|)` = constant.
* **(ii) an induction instance** (`indRecB “K s fv b m p.”`, `Nodes.lean:617`): `p = ∀^m b`
  with `b`'s objects inside `objs(p)` at depth `m`; steps: `qqAllsZero [b]`, `m` × `qqAllsSucc`
  (NEW rows, `“p' p b m. !qqAllsDef p b m → !qqAllDef p' p → !qqAllsDef p' b (m + 1)”`, `m` as
  `cT m`) → `qqAllsF p b (cT m)`; `describeF W m (shift b)` + `certShift` + `eqSteps` against
  `b` itself (TRUE: `b` is closed) → `shiftF b b`; `bv b = m`: NEW `bv*` rows bottom-up
  (`bvRel/And/All/…`, `bvTerm*`, with `max`/truncated `−` closed facts by `sLemma`) → `bvF (cT m) b`;
  `fvarVecTotal [cT m]` → `fv`; `describeF W 0 (subst (fvarVec m) b)` + `certSubst (fv, b)` —
  the entries `nthDef (^&i) fv i` from NEW `fvarVecNth` rows — → `substF sb fv b`; `K`: the
  1-semiformula inside (`objs`), `totIndBody [K]` → `ib`; the Bridge chain (`Bridge.lean:888-923`:
  ℒₒᵣ-ness lifts, the `LAct → ℒₒᵣ` graph conversions, `indBodyIntro` with `y := sb`,
  `certSubst` for `indSubstConst0/1` at `K`) → `indBodyValF ib K` and `eqF sb ib`; finally
  `indRec [K, sb, fv, b, cT m, p]` → `Δ₁ch.sigma p`. `O(|p|)` steps; every piece paid by `|p| ≤ w_ν`.
Then `node`: `totAxm [p, s]`, `introAxm [e, p, s]` (`“e p s.”`), `dlenAxm`, `dlenLeafLe`.

### 4.11 Index bookkeeping summary

Every producer above computes indices from three static quantities: the layout offsets of §3.2
(from `memberList s` and `descCountF`), the shift counts of its own emitted sub-lists
(`descCountF`, `descCountT`, the copy/chain counts, `shiftsV` of the children's lists — all Σ₁),
and the constants `1`/`2` of `node`/`recover`. `shiftsV (verifySteps ν)` = `σ_ν` is a Σ₁
function (computed alongside, `⟪count, steps⟫` as `descT` does, `Describe.lean:1759-1766`).

---

## 5. Cost (ANALYSIS, from the `stepCost` bounds of `Chain.lean:1108-1154` and `ChainOcc.lean`)

Let `w_ν := 1 + setLen s_ν (+ termLen t at exs)` — `ρ`'s own charge at `ν` (`DlenGraph.*_iff`),
`g := dlen ρ = Σ_ν w_ν`. Per fragment (§4), counting steps and shifts:

| tag | steps | shifts (eigenvariables) | `sLemma`s |
|---|---|---|---|
| `axL`, `verum`, `axm`(i) | `≤ c·|p| + 9` | `1` | 1 |
| `axm`(ii) | `≤ c·|p|` | `≤ c·|p|` | `≤ c·|p|` |
| `and`, `or`, `cut` | `≤ c·(setLen s₁' + setLen s₂')` (copies, walks, chains, identification) | same order | `O(setLen s')` (lengths) + 3 |
| `all`, `exs`, `shift`, `wk` | `≤ c·setLen s'` (+ `termLen t`) | same order | same |

Since every child's `setLen s'` is the child's own `w_{ν'}`, **`len (verifySteps ρ) ≤ C₀·g`
and `shiftsV (verifySteps ρ) ≤ C₀·g`**, and the number of `sLemma`s is `≤ C₀·g`.

Context size along the chain (no drops): the facts ever added number `≤ len ≤ C₀ g`; each is
a canonical code `subst ?[w…] P` with `≤ 9` witnesses, each witness `^&i` (`termLen = i + 1`,
`Length.lean:100-102` — the UNARY index cost), a chain numeral `cT v` (`2v + 1`, `v ≤ w_ν`), a
binary numeral (`O(‖g‖)`), or a `Dlen` sum term (`≤ 4` indices + `O(1)`); `|P| ≤ B` (the largest
row body — `|derivation TAct|` inside `PGoal`, `derF`, `introAnd`…: the constant `B`). An index
is at most the total shift count `≤ C₀ g`. Hence `|fact| ≤ B·(C₀ g + 1)` and
**`setLen Γ_i ≤ setLen Γ_root + C₀ g · B (C₀ g + 1) = O(B·g²)`** for every context `Γ_i` of the
chain, `fvOccS Γ_i ≤ 9·C₀ g`. The witness bound `E ≤ C₀ g + 1 + 2 w_max + ‖g‖·c ≤ C₁ g`.

Per step (`stepCostOcc`, `ChainOcc.lean:39-50`, `DESIGN_describe.md` §2.4: `m ≤ 9`, `j ≤ 8`):
`≤ N + 25·G + fvOccS Γ + K·B·E + K'`; tag 6 `≤ 12 G + 40|G_code| + 4E + 16` with `|G_code| ≤ B·(E + ‖g‖)`;
tag 7 `≤ 2G + 2|A| + 2 + dlen dA` with `dlen dA ≤ C₂·‖g‖³` (N1–N3, N6: `≤ C₂ (w_ν + ‖g‖)³` for
N6 — summed over the leaves `Σ (z+1)² ≤ w_ν²`, so `Σ_ν` of the N6 costs `≤ C₂ g²`). Summing over
`≤ C₀ g` steps:

```
dlen (chainCode tbl Γ_root (verifySteps ρ) d)
  ≤ dlen d + C₀ g · (N + 25·(setLen Γ_root + C₀ B g (C₀ g + 1)) + 9 C₀ g + K B C₁ g + K')
          + C₀ g · (12·(…) + 40 B (C₁ g + ‖g‖)) + C₀ g · C₂ ‖g‖³ + C₂ g²
  = C·(g + 1)·(setLen Γ_root + (g + 1)²) + C·N·(g + 1)          -- the exact polynomial: CUBIC
```
i.e. **`dlen_verifySteps_le : dlen (chainCode …) ≤ dlen d + C·(dlen ρ + 1)·(setLen Γ_root + N + (dlen ρ + 1)²)`**
with `C` absolute in `B`, `K`, `K'`, `M`, and the row count (`N` = `TableOK`'s uniform bound —
the `Lib.univ_code` constant, `|derivation TAct|`-sized). This is DESIGN §3.7's
`O(w_ν · L_ν · (1 + D_ν))` per node summed with `L_ν = O(g)` (nothing dropped) and `D_ν = O(g)`:
`O(g³)`. The `sWkDrop`-discipline would lower `L_ν` to `O(w_ν)` but not the exponent (the index
cost is a factor `g` anyway, DESIGN §3.7), which is why the design does not drop.

Index-cost caveat (FACT, `BRIEF.md` §9 RISK): the `stepCost` blueprint charges tags 2/3 through
`|setShift Γ| ≤ 2|Γ|` (`stepCost_tag3` uses the explicit `setLen (setShift Γ)` — fine — but tag 2's
`introCost` has `(m + 2j + 10)·G`, `Chain.lean:1116`); the SUM over the chain must use the
additive `stepCostOcc` bound per step (`dlen_applyStep_le_occ`) inside `dlen_chainAux_le`'s
induction — i.e. `dlen_verifySteps_le` is proved against a `costSumOcc` with the additive shift
term, or `stepCost` is re-based on `setLen (setShift Γ)` for tag 2 as tag 3 already is
(recommended: ONE blueprint change in `stepCost`, no `_occ` twin).

---

## 6. `verifySteps ρ` as a Σ₁ function, and its theorems (ANALYSIS)

### 6.1 Recommended shape: a Δ₁ graph fixpoint on `⟪ρ, L⟫` (the `DlenGraph` pattern)

`VerifyGraph W tbl ρ L` := `Fixpoint` of a blueprint with parameters `(W, tbl)` on the key
`⟪ρ, L⟫`, ten clauses (the `DlenGraph` blueprint `DerivationLength.lean:55-135` is the template,
`:⟪d', n'⟫:∈ C` for premises), e.g.

```
(∃ s < d, ∃ p < d, ∃ q < d, ∃ dp < d, ∃ dq < d, !andIntroGraph d s p q dp dq ∧
   ∃ L₁ ≤ L, ∃ L₂ ≤ L, :⟪dp, L₁⟫:∈ C ∧ :⟪dq, L₂⟫:∈ C ∧ !fragAndDef L W s p q dp dq L₁ L₂)
```
where `fragAnd W s p q dp dq L₁ L₂ := pro₁ ++ L₁ ++ rec ++ pro₂ ++ L₂ ++ rec ++ node` is a Σ₁
function (the producers of §3–4: `copySteps`, `chainSteps`, `describeF/T`, `lenSteps`,
`certX`, `eqSteps`, `numProof`, the constant `recover`/`node` blocks — each a `PR`/`Fixpoint`
construction of its own with an `_defined` instance; `shiftsV L₁` is read off `L₁` by the Σ₁
`shiftsV`). The Π₁ side of the blueprint uses `∃ L₁ <⁺ L` — sound because
`L₁ ≤ appendV u (appendV L₁ v)` (NEW V-lemma `le_appendV_mid`: `v ≤ x ∷ v` from `le_pair_right`
+ `x ∷ v = ⟪x, v⟫ + 1`, and `pair_le_pair_right` (`IOpen/Basic.lean:653`) along `u`).
`StrongFinite`: `⟪dp, L₁⟫ < ⟪d, L⟫` by `pair_lt_pair_left (dp_lt_andIntro …)` and
`pair_le_pair_right _ (le_appendV_mid …)` — exactly `DerivationLength.lean:189-211`'s proof
shape. Hence `VerifyGraph` is Δ₁ (`fixpointDefΔ₁`) with `case` and `induction`.
BLUEPRINT TRAP (`BRIEF.md` §9, 2026-09-13): every Σ₁ function inside the clause is called
∃-wrapped (`∃ y, !fragAndDef y … ∧ L = y`), never as a bare graph; no closed numeral as an
argument of a Δ₁ predicate inside the blueprint (row indices enter through `W`).

`verifySteps W tbl ρ := the unique L` (existence + uniqueness below), or — simpler for the
theorems — never define the function: state everything for any `L` with `VerifyGraph ρ L`.

Rejected: the `Derivation.induction1`-EXISTENTIAL form for a `verifySteps` taking an environment
(`∀ env, ∃ L` is Π₂; bounding `env` by an external `B` gives a Σ₁ statement but the layout
theorem then needs the bound threaded through every child — the copy-in makes `env` vanish).

### 6.2 Existence and uniqueness

* `verifyGraph_exists : Derivation TAct ρ → ∃ L, VerifyGraph W tbl ρ L` — by
  `Derivation.induction1 𝚺` (`Proof/Basic.lean:560`; `P d := ∃ L, VerifyGraph d L` is Σ₁),
  each case taking the children's `L₁`, `L₂` and closing the clause by `Fixpoint.case`.
* `verifyGraph_unique : VerifyGraph ρ L → VerifyGraph ρ L' → L = L'` — by `Fixpoint.induction`
  on the key (`P ⟪ρ, L⟫ := ∀ L', VerifyGraph ρ L' → L = L'`, Π₁) — optional.

### 6.3 The invariant (`verifySteps_ok`)

```
theorem verifySteps_ok (M := 9) {W tbl N : V} (hW : WalkTable' tbl W) (htbl : TableOK tbl N) :
  ∀ ρ, Derivation TAct ρ → ∀ L Γ, VerifyGraph W tbl ρ L → Layout Γ ρ →
    ListOK tbl E M Γ L ∧ NoDrop L ∧ shiftsV L = σ ρ ∧
    neg (goalFact (^&(memCount ρ + σ ρ)) (bnum (dlen ρ))) ∈ finalCtx Γ L ∧
    Layout' (finalCtx Γ L) ρ (σ ρ)                                  -- the parent's objects, shifted
```
`Layout Γ ρ` (§3.2, Δ₁), `σ ρ := shiftsV L` (or its own Σ₁ function `verifyCount`),
`memCount ρ := len (memberList (fstIdx ρ))`. `E` is a function of `ρ` and the root's index
depth (§5). Proof: `Derivation.induction1 𝚷` with `P ρ := ∀ L Γ, VerifyGraph ρ L → Layout Γ ρ →
(Δ₁ conjunction)` — Π₁ (Σ₁/Δ₁ antecedents, Δ₁ matrix; `finalCtx`, `goalFact`, `bnum`, `σ` enter
through their Σ₁ graphs). In the `andIntro` case: `Fixpoint.case` (`HFS/Fixpoint.lean:222`,
`Finite` suffices) unfolds `VerifyGraph (andIntro …) L` into `L₁`, `L₂`, `fragAnd`; the
`listOK_appendV`/`finalCtx_appendV` composition (`Describe.lean:346-358`) reduces to: (P1) the
prologue is `ListOK` from `Layout Γ ν` and produces `Layout (finalCtx Γ pro₁) dp` — the LAYOUT
THEOREM per tag, proved from `describeF_ok`, `copySteps_ok`, `chainSteps_ok`, `lenSteps_ok`,
`eqSteps_ok`, `certX_ok` (each a Π₁ statement of the same shape, proved once); (R) `recover`
is `ListOK` after the child's goal fact (five concrete `StepOK`s: `Chain.lean:1204-1206`) and
transports; (N) `node` is `ListOK` (the row instances by the `inst_` lemmas of the node rows,
§8) and ends with the `sGoal` fact. Transport of older facts through a sub-list by
`mem_ctxVec_of_mem` (`Describe.lean:410`, needs `NoDrop`) with `shiftIterV` of a canonical code
= the code with every `^&i` bumped (`shift_subst_listToVec`, `termShiftIterV_fvar`
`Describe.lean:199`). The DerivationOf hypotheses of `induction1` supply the V-facts the `sLemma`
closed sentences need (`setLen`/`dlen` values are what they are; N3 is TRUE by `DlenGraph.*_iff`).

### 6.4 The length theorem

```
theorem dlen_verifySteps_le … (hd : DerivationOf TAct d (finalCtx Γ L)) :
  dlen TAct (chainCode tbl Γ L d) ≤ dlen TAct d + C * (dlen TAct ρ + 1) * (setLen LAct Γ + N + (dlen TAct ρ + 1)^2)
```
from `dlen_chainCode_le` (`Chain.lean:1762`) + the per-step bound with the context bound of §5
(`setLen (ctxVec Γ L).[i] ≤ setLen Γ + i·B·(shiftsAux L i + 1)`, itself a Π₁ induction on `i`
using the fact-length bound of `RowInst` §2 and `setLen_setShift_le_occ`) + `len L ≤ C₀ (dlen ρ + 1)`
(from `verifySteps_ok`'s companion `len_verifySteps_le`, by `induction1`).

---

## 7. The top (DESIGN §4.3 as a step list) and the final theorem (ANALYSIS)

FACT: the target `instB ⌜Box_g χ⌝ k` unfolds (DESIGN §1.3) to
`∃ a (gGraph a k̄ ∧ ∃ g' (instBGraph g' ⌜χ⌝ k̄ ∧ ∃ d (proof.sigma d g' ∧ ∃ n (dlenDef n d ∧ n ≤ a))))`
with `k̄ = bnum k`, `gGraph = “y k. ∃ l, !lengthDef l k ∧ y = l * l * l”` (`Prep.lean:554-566`,
`gBudget k = ‖k‖³` since the cube), `instBGraph = “y n k. ∃ t, !bnumGraph t k ∧ ∃ v, !adjoinDef v t 0 ∧
!(substsGraph LAct) y v n”` (`InstV.lean:90`), `proof.sigma = “d φ. ∃ s, !insertDef s φ 0 ∧
!(derivationOf).sigma d s”`, `dlenDef = “n d. (derivation.pi d → dlenGraph.sigma d n) ∧
(¬derivation.sigma d → n = 0)”` (`DerivationLength.lean:404`). The hypothesis: `LenDerivable TAct
(gBudget k) (instB ⌜χ⌝ k)` — a code `ρ` with `Proof ρ (instB ⌜χ⌝ k)` and `dlen ρ ≤ ‖k‖³`
(`CutV.lean:158`).

### 7.1 `topSteps χ k ρ` (context `Γ_top := insert (target) 0`)

1. `describeT W 0 (bnum k)` + term `lenSteps` → `t̂` (`O(‖k‖)`: `|bnum k| = O(‖k‖)`, V-lemma
   `termLen_bnum_le` NEW — `InstV.lean:472` has only the `ℕ` form); certify `bnumGraph t̂ k̄` by
   NEW rows `bnumZeroCert “t. t = 𝟎 → bnumGraph t 0”`, `bnumOneCert`, `bnumEvenCert “u t m. 1 ≤ m →
   bnumGraph t m → qqMulGraph u 𝟐 t → bnumGraph u (2 * m)”`, `bnumOddCert` (`Bnum.lean:345-355`),
   walking the bits of `k` with `m := bnum (k / 2ⁱ)` as the numeral witness (the DSL `2 * m` at
   that witness IS the code `bnum (2·(k/2ⁱ))` by `bnum_two_mul` — CHECK that the DSL literal `2`
   quotes to `𝟐 = 𝟏 ^+ 𝟏`; else write the row with `(1 + 1) * m`) and `sLemma (N7)` for `1 ≤ m`:
   `O(‖k‖)` steps.
2. `adjoinTotal [t̂, 𝟎]` → `v`, `adjF v t̂ 𝟎`.
3. `describeF W 1 ⌜χ⌝` + `lenSteps` → `x_χ` (constant size `|χ|`); `pinSteps χ x_χ` (§4.10(i):
   closed shape rows for the STANDARD code `⌜χ⌝` and its subterms, functionality rows) →
   `eqF x_χ ⌜χ⌝` — the ONLY place the unary numeral `⌜χ⌝` is written (in `O(|χ|)` closed rows
   of size `≥ encode χ`: the constant `C_χ`).
4. `describeF W 0 (instB ⌜χ⌝ k)` + `lenSteps` + `certSubst (v, x_χ)` → `g'` with `substF g' v x_χ`;
   `congSubstR [⌜χ⌝, x_χ, v, g']` (NEW `congSubstArg “n' n w y. n = n' → substsGraph y w n →
   substsGraph y w n'”`) → `substF g' v ⌜χ⌝`; `instBIntro [g', v, t̂, k̄, ⌜χ⌝]` (NEW row
   `“g v t k n. !bnumGraph t k → !adjoinDef v t 0 → !(substsGraph LAct) g v n → !instBGraph g n k”`)
   → `instBF g' ⌜χ⌝ k̄`.
5. `chainSteps [g']` (`insertTotal [g', 𝟎]` → `s₀`), `IsFormulaSet`, lengths → `Layout Γ ρ` with
   `k = 1`: `s₀ = &1`, `l_{s₀} = &0`, `objs(g')` above.
6. `verifySteps W tbl ρ ++ recover(ρ)` → `d = &1`, `n = &0`, `derF d`, `fstIdxF s₀ d`, `dlenF d n`,
   `leF n (bnum (dlen ρ))`.
7. `derivationSigmaPi [d]` → `derivation.pi d`; `dlenDefIntro [n, d]` (NEW row `“n d.
   !(derivation TAct).sigma d → !(derivation TAct).pi d → !(dlenGraphDef LAct).sigma d n →
   !(dlenDef TAct) n d”`; V: `dlenDef` unfolds to the two conjuncts, the second vacuous) →
   `dlenDefF n d`; `proofIntro [d, g', s₀]` (NEW `“s g d. !insertDef s g 0 → !fstIdxDef s d →
   !(derivation TAct).sigma d → !(proof TAct).sigma d g”`) → `proofF d g'`.
8. `lengthTotal [k̄]` (NEW) → `l̂`, `lengthF l̂ k̄`; `sLemma (N5: lengthDef (bnum ‖k‖) (bnum k))`;
   `lengthFun [bnum ‖k‖, l̂, k̄]` (NEW functionality) → `eqF l̂ (bnum ‖k‖)`; `eqRefl [l̂ * l̂ * l̂]`;
   `gIntro [l̂*l̂*l̂, l̂, k̄]` (NEW `“a l k. !lengthDef l k → a = l * l * l → !gGraph a k”`) → `gF a k̄`
   with `a := l̂ * l̂ * l̂` (a TERM witness);
   `sLemma (N4+N2: bnum (dlen ρ) ≤ bnum ‖k‖ * bnum ‖k‖ * bnum ‖k‖)` — TRUE by the hypothesis
   `dlen ρ ≤ gBudget k`; `congMul` ×3 / `leOfLeEq` with `l̂ = bnum ‖k‖` → `leF (bnum (dlen ρ)) a`;
   `leTrans` → `leF n a`.
9. The closing LEAF `targetLeafCode Γ_final a g' d n` — the target's shape is NOT a prefix
   `∃∃∃∃` but `∃ a (A ∧ ∃ g' (B ∧ ∃ d (C ∧ ∃ n (D ∧ E))))`: `exsIntro` (witness `a`), `andIntro`
   (`axL` on `gF a k̄` | `exsIntro g'`, `andIntro` (`axL instBF` | `exsIntro d`, `andIntro` (`axL
   proofF` | `exsIntro n`, `andIntro` (`axL dlenDefF` | `axL leF n a`))))) — 13 nodes, a fixed
   Lean-level constructor with `targetLeafCode_proof` from `Derivation.exsIntro/andIntro/axL`
   (`Proof/Basic.lean:603-636`) and the instantiation lemma of the target (`substs1` at the
   witnesses reproduces the canonical codes `gF a k̄`, … — the `RowInst` technique on
   `instBGraph`/`gGraph`/`proof`/`dlenDef` as quoted subformulas of `boxCore`, `Prep.lean:571`).
   Its cost `≤ 13·(setLen Γ_final + 2·|target|) + Σ|witnesses|`.

`verifyCode χ k ρ := chainCode tbl Γ_top (topSteps χ k ρ) (targetLeafCode …)`.

### 7.2 Sizes at the top

`|target| = |instB ⌜Box_g χ⌝ k| ≤ |Box_g χ| · |bnum k| = C_χ · O(‖k‖)`; `setLen Γ_top = |target|`;
`Γ_top` has ONE fact of index-free size. The top adds `O(|χ| + ‖k‖ + |instB ⌜χ⌝ k|)` steps, all
inside the `C₀ g` count (`|instB ⌜χ⌝ k| ≤ setLen s₀ ≤ dlen ρ`), and the constant-size closed
rows of `pinSteps` (`N_χ ≥ encode χ`, inside `N` for this family — the table `tbl` is
`χ`-dependent, hence the `∃ C` AFTER `∀ χ`).

### 7.3 The final theorem

```
theorem boundedInnerNec_three : BoundedInnerNec 3 where
  nec χ := ⟨C_χ, fun V _ _ k ⟨ρ, hρ, hlen⟩ ↦
    ⟨dlen TAct (verifyCode χ k ρ),
     (dlen_verifyCode_le … : … ≤ C_χ * ((gBudget k)^3 + 1)),
     ⟨verifyCode χ k ρ, verifyCode_proof …, le_rfl⟩⟩⟩
```
with `verifyCode_proof : Proof TAct (verifyCode χ k ρ) (instB ⌜Box_g χ⌝ k)` from `chainCode_proof`
(`Chain.lean:1732`; `M = 9`, `htbl : TableOK tbl N` from `exists_walkTable`-style packaging of
ALL rows incl. the `χ`-rows, `hok` from `verifySteps_ok` + the top's `ListOK`, `hd` =
`targetLeafCode_proof` at `finalCtx`) and `dlen_verifyCode_le` from `dlen_chainCode_le` +
§6.4 + the leaf bound, with `dlen ρ ≤ gBudget k = ‖k‖³` and `setLen Γ_top ≤ C_χ ‖k‖ ≤ C_χ gBudget k`:
`≤ C·(g + 1)·(C_χ g + N_χ + (g + 1)²) ≤ C_χ' · (g³ + 1)` — `d = 3`. `BoundedInnerNec 3` is
exactly `Prep.lean:720-723`'s statement (`∀ χ, ∃ C, ∀ V k, LenDerivable (gBudget k) (instB ⌜χ⌝ k)
→ ∃ e ≤ C·((gBudget k)^3 + 1), LenDerivable e (instB ⌜Box_g χ⌝ k)`), which `pblt_uniform`
consumes (`BRIEF.md` §6/§8). Everything is `V`-generic; the constant `C_χ` is standard (it comes
from `Lib.univ_code`'s `N` for the `χ`-rows, `|Box_g χ|`, and the absolute row constants).

---

## 8. Gaps — everything not yet in `Lib/*`, `RowInst`, `Chain`, `Describe` (ANALYSIS; sizes ≈ lines)

### 8.1 Rows (each ~25 lines on the `Sets.lean` template, generated by `gen_rowinst.py` where marked ★ for the `inst_` lemma)

| group | rows | count |
|---|---|---|
| copy-in | `eqTotal “x. ∃ y, y = x”`, `eqRefl`, `eqTrans`, `congPi`, `congTPi`, `congTvPi`, `congUtvPi`, `congAnd/Or/All/Exs/Rel/NRel/Verum/Falsum` (all args at once), `congFunc/Bvar/Fvar/Adj`, `congLen`, `congTLen`, `congMem`, `congFstIdx`, `congSubsetL/R`, `congSetShiftL`, `congShiftL`, `congSubstArg`, `congInsertL`, `congLenNum` | ~30 ★ |
| identification | `eqOfAnd/Or/All/Exs/Rel/NRel/Verum/Falsum/Func/Bvar/Fvar/Adj` | 12 ★ |
| functionality (`pinSteps`) | `qqAndFun/OrFun/AllFun/ExsFun/RelFun/NRelFun/FuncFun/AdjFun/BvarFun/FvarFun`, `setShiftFun`, `setLenFun`, `lengthFun`, `termLenVecFun`, `listSumFun` | 15 ★ |
| certification (bottom-up) | `negRelCert … negExsCert` (8; or reuse `neg*B` with `useRowEx` + `eqOf*` — the top-down rows deliver `np, nq` EXISTENTIALLY, so certification via them needs the identification of `np` with the walked object: 2 extra steps per node; the dedicated `Cert` rows are cheaper), `shiftRelCert … shiftExsCert` (8), `substsRelCert … substsExsCert` (8), `freeCert`, term level: `tshvNilCert/tshvAdjCert/termShiftBvar/Fvar/FuncCert` (5), `tsvNilCert/tsvAdjCert/termSubstBvar/Fvar/FuncCert` (5), `qVecNth0/qVecNthSucc/termBShift*Cert` (5), `nthAdjoinZero/nthAdjoinSucc` (2), `substsSubsts1` (converse of `substs1Substs`) | ~42 ★ |
| lengths | `termLenVecNil/Adj`, `listSumNil/Adj`, `formulaLenRelCert`/`NRelCert`, `termLenFuncCert` (universal `M, s`) | 7 ★ |
| nodes | `fstIdxAxL … fstIdxAxm` (10), `dlenDefIntro`, `proofIntro`, `instBIntro`, `gIntro`, `lengthTotal`, `bnumZero/One/Even/OddCert` (4) | 19 ★ |
| sets | `subsetAntisymm`, `setShiftInsert`, `setShiftEmpty` | 3 ★ |
| `axm`(ii) | `qqAllsZero/Succ`, `bv*` (formula 8 + term 3 + vector 2 + totality), `fvarVecTotal`, `fvarVecNth`, `max`/`−` glue (`maxLe…`, 3) | ~22 ★ |
| `axm`(i) / top | per standard axiom `σ` and per `χ`: closed shape rows of the numerals (`O(|σ|)`, `O(|χ|)`) — generated from the Lean term, NOT hand-written; `axiomRec σ` exists | family |
| numerals (N4/N5) | `twoMulMul`, `twoMulOneMul`, `lengthZero/One/TwoMul/TwoMulOne` | 6 |
| `inst_` lemmas for EXISTING rows the fragments use | `Nodes` (30), `Sets` (26), `Lengths` (35), `Occ` (§4 glue, 8), `Walk` bridges | ~100 ★ |

### 8.2 Step language (`Chain.lean` Part B)

`sGoal` (tag 6) and `sLemma` (tag 7): codes, `applyStep`/`ctxAfter`/`stepCost` arms (+ their
`Def` blueprints and `_defined` cases), `StepOK` disjuncts, `applyStep_proof`/`dlen_applyStep_le`
arms, `isFormulaSet_ctxAfter`, `mem_ctxAfter_of_noShift` (tags 6/7), `NoDrop` (Describe) —
~250 lines; the leaves `goalLeafCode`/`conj4Code`/`targetLeafCode` with `_proof` and `dlen`
bounds — ~200 lines; the goal's instantiation lemma (`goalFact` = `^∃^∃ qBody`, `instOuter [e,n]
qBody = …`) — ~60 lines; `stepCost` tag-2 re-basing on `setLen (setShift Γ)` — ~30.

### 8.3 Producers (each a `PR`/`Fixpoint` construction + `_ok` (Π₁) + `dlen` bound)

`memberList` (bit-set → ascending list, ~80), `copySteps` (~300), `chainSteps` incl. `IsFormulaSet`,
lengths and the identification of §3.4 (~400), `eqSteps` (~250), `certNeg/Shift/Subst/Free`
(~500, one `Fixpoint` on `⟪kind, x, offsets⟫`), `lenSteps` (~300), `numProof`/`numSteps` (~600),
`pinSteps` (~150 + per-χ generation), `recover`/`node` blocks (~100), the ten `frag<Tag>` (~800),
`VerifyGraph` blueprint + `StrongFinite` + `exists`/`unique` (~500), `verifySteps_ok`
(~1500: ten cases, each a layout theorem), `dlen_verifySteps_le` + context bound (~400),
`topSteps` + final theorem (~500). Total ≈ 6–7 k lines — consistent with `BRIEF.md` §8's
estimate for the recursion.

### 8.4 V-lemmas

`le_appendV_mid` (sub-vector ≤; from `le_pair_right`, `pair_le_pair_right`), `setShift_insert`
(`mem_ext` + `mem_setShift_iff`), `termLen_bnum_le` (V-form), `subsetAntisymm`'s `mem_ext`
(exists), the `bv` constructor laws for `axm`(ii) (Foundation's `bv` on codes — locate), the
`qVec`/`termBShift` entry laws (`Chain.lean:477-517` has `nth_qVecIter_single/nil`), the DSL
literal `2` = `𝟐` check (§7.1).

### 8.5 Not needed (decided against)

`negSteps/shiftSteps/substSteps/freeSteps` top-down (DESIGN_describe §9) — replaced by
certified re-description; the `fvOcc*` rows and `setLenSetShiftLe` (`Occ.lean`) — the shifted
members are walked with exact lengths; `shift`-injectivity — never used; `sWkDrop`; the
bit-set difference; `isSemiformulaNeg/Shift/Subst/Substs1`/`isFormulaFreeC` formation rows —
the walk gives `piF` of every re-described formula directly (they remain useful as sanity rows).

---

## 9. Risks, ranked

1. **The layout theorem per tag** (§6.3 (P1)) is the bulk: it must show that after the
   prologue the context satisfies `Layout (…) child` — every fact at its canonical index — from
   the composition of `describeF_ok`, `copySteps_ok`, `chainSteps_ok`, … through `mem_ctxVec_of_mem`
   with EXPLICIT index arithmetic on `shiftIterV`. The walk's own theorem (`describeSteps_ok`,
   DESIGN_describe §7) is the template; its `off`-bookkeeping is the part that will be redone
   ten times. Mitigation: state `Layout` as "for every `f ∈ layoutFacts ν`, `neg f ∈ Γ`" with
   `layoutFacts` a Σ₁ function, and prove ONE lemma "after `c` shifts `layoutFacts ν` at offset
   `c`" (`shiftIterV` on canonical codes = index bump), so each tag's proof is a list-membership
   argument rather than index arithmetic.
2. **The duplicate/identification machinery** (`eqSteps`, §3.5) and its term-level rows: a
   nonstandard `ρ` can insert a formula already present, and `shiftRule` needs it always. If
   the term-level certification rows (§8.1) turn out heavier than estimated, `shiftRule` alone
   forces them (its members are only definable through their shifts).
3. **`sLemma` soundness rests on `StepOK` checking `DerivationOf dA {A}`** — Δ₁ via
   `derivationOf` (`Proof/Basic.lean:477`); but `derivation` is the fixpoint formula whose
   `simp`/`rfl` manipulation "overflows memory" (`:495`): the `StepOK` definability instance for
   tag 7 must use `derivationOf.defined`-style instances only, never unfold. Same for
   `stepCost`'s `dlenDef` call.
4. **`axm`(ii)** (`bv`, `fvarVec`, `qqAlls`, the ℒₒᵣ bridges): the longest single chain; every
   piece is a constant-size row but the V-lemmas behind `bv` on codes and `fvarVec` entries are
   unverified in Foundation. A nonstandard `ρ` may contain nonstandard induction instances, so
   it cannot be dodged.
5. **Constants**: `B ≥ |derivation TAct|` multiplies `g²` in every context bound; fine for the
   theorem, but any `#eval`/`decide` on these codes is out of the question (`BRIEF.md` §8
   risk (2)).
6. **`Fixpoint` blueprint elaboration** (`BRIEF.md` §9 2026-09-13): ten clauses each calling a
   large Σ₁ producer — ∃-wrap every call; expect the `_defined` proof to be the slowest file.

## 10. Summary

* Recursion: `VerifyGraph` = Δ₁ `Fixpoint` on `⟪ρ, L⟫` (`StrongFinite` via `ρ' < ρ`, `L' ≤ L`),
  existence by `Derivation.induction1 𝚺`, invariant by `induction1 𝚷` + `Fixpoint.case`.
* `sSub`: REJECTED (circular `PR`); replaced by the FLAT list + `sGoal` (tag 6, a constant leaf
  cut) + `sLemma` (tag 7, closed numeral facts with a supplied derivation).
* `ū_ν = bnum (dlen ν)`; the `∃ n` witness is the `Dlen` row's sum term; one `dlenBinaryLe` +
  one `sLemma` + one `leTrans` per node.
* Layout: canonical, copy-in, sequents as chains over distinct members, lengths exact by
  `sLemma` on V-truth; derived formulas re-described and certified bottom-up; identification
  walk for duplicates and `shiftRule`.
* Cost `O(g³)` without dropping; `BoundedInnerNec 3`.
* Biggest risk: the per-tag layout theorems (index bookkeeping ×10) and the term-level
  certification/identification rows that `shiftRule` and duplicates force.
