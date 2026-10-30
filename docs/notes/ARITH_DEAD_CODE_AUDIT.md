# ArithS dead-code audit (2026-09-28) — report only, nothing deleted

**Question.** Which declarations of `arith/ArithS` contribute to nothing the package claims?
**Method.** A reachability closure in Lean (`arith/scripts/DeadCode.lean`), not a text search.
ROOTS = the 1886 names the axiom census prints (`scripts/roots.txt`, extracted from every
`#print axioms` under `ArithS/`) + every `instance` + every macro/notation. LIVE = the closure of the
roots over the constants used in the TYPE and the PROOF/VALUE of each constant (theorem proof terms
included — `ConstantInfo.value? (allowOpaque := true)`; the default hides theorem bodies and a first
run with it reported 57 % dead, all false), plus the constructors of every live inductive. DEAD = an
`ArithS` constant outside the closure. Compiler-generated names (`match_`, `.eq_`, `.rec`, `proof_`,
private …) are tagged `aux` and excluded from every count below; declaration line counts are the
declaration ranges Lean records, so docstrings, `section`/`variable` lines and comments are not counted.

Run (≈3 min, needs the package built):
```
cd arith && lake env lean --run scripts/DeadCode.lean scripts/roots.txt /tmp/deadcode.tsv
```
Output: `name  module  kind  startLine  endLine  ROOT|LIVE|DEAD  aux` (31745 rows).

**Known limits.** (1) A structure projection reached only through `Expr.proj` is not seen as a used
constant; no live projection was flagged (`VerifyKit.ok` etc. are LIVE), so the effect is nil here.
(2) A declaration used only by an `example`, a `#check`, a `#eval` or a docstring is DEAD by this
definition — correctly, from the census' point of view, but such items are usually documentation and
are marked as such below. (3) Sanity: all 14 trusted-base definitions (`TAct`, `proofLen`, `codeBound`,
`LenBox`, `ppair`, `codeTerm`, `descriptions`/`descriptionsB`, `guardCode`/`guardCodeB`, `substCode`, `substTemplate`,
`template`, `EvalGraph`) are LIVE; the headline theorems (`red_cell`, `boundedInnerNec_sixteen`,
`closedInnerNec_sixteen`, `pblt`, `dupoc_self_coop`, `dimcid_vs_closed`)
are ROOTS. (4) Textual cross-check: the ten largest blocks flagged dead by the buggy first run were
each textually referenced from a ROOT — the corrected run flags none of them.

## 1. Totals

| | declarations | declaration lines |
|---|---:|---:|
| `ArithS` non-aux declarations with a source range | 18 091 | 114 329 (of 146 775 file lines) |
| ROOT (in the census) | 1 822 | |
| LIVE (reachable from a root) | 12 191 | |
| **DEAD** | **4 078** | **11 721 (10 %)** |

Where the 11 721 dead lines are:

| category | dead decls | dead lines | note |
|---|---:|---:|---|
| generated row tables (`RowInst`, `RowInstB`, `CertRows`, `IndRecRows`, `Frag1Rows`, `Frag2Rows`, `NumIdRows`, `ProAxmRows`, `PrologueRows`, `Lib/Frag`) | 2 214 | 6 936 | unused library MEMBERS and their rows — cut in the generators, not by hand |
| `Necessitation/Lib/{Formulas,Bridge,Occ,Lengths,Sets,Nodes}` (hand-written library entries) | 795 | 1 631 | same phenomenon, hand-written side |
| `Necessitation/` hand-written proof modules | 631 | 2 055 | mostly `*_definable` boilerplate, `*_inv` lemmas, superseded `ltag_cong*`/`ctag` helpers |
| everything outside `Necessitation/` (Theory/Length/Box/Agents/Eval/Loeb/Bridge/Assembly/Audit/Cells) | 265 | 925 | small; several are documented negative results, not dead code |
| `Cells/Names.lean` | 173 | 174 | the `@[deprecated]` alias file — 100 % dead BY DESIGN |

Thirty-two modules have zero dead declarations, among them every `Cells/Common/*`, `Cells/{RedCell,
SearchFree,PositiveCells,FlipCells,DimcidFlips,FloorDichotomy,FloorVerdicts,SimSlot}`, `Eval/{Eval,EvalN}`,
`Assembly/{Cell,Family}`, `Necessitation/{Package,Assemble,Verify4,Verify5,Dossier,ProAxm,ChainOcc}`,
`Theory/{Sound,Transpose}`, `Length/MetaLength`, `Bridge/Core/Sound`.

## 2. Per module (dead lines ≥ 20)

| module | decls | dead | lines | dead lines | % |
|---|---:|---:|---:|---:|---:|
| Necessitation.RowInstB (generated) | 1700 | 857 | 5375 | 2689 | 50 |
| Necessitation.RowInst (generated) | 1061 | 601 | 3303 | 1836 | 56 |
| Necessitation.CertRows (generated) | 739 | 119 | 4078 | 676 | 17 |
| Necessitation.Cert | 1021 | 164 | 11765 | 631 | 5 |
| Necessitation.Lib.Frag (generated) | 1037 | 349 | 1876 | 627 | 33 |
| Necessitation.Lib.Formulas | 429 | 272 | 864 | 548 | 63 |
| Necessitation.Lib.Bridge | 276 | 192 | 705 | 376 | 53 |
| Necessitation.IndRecRows (generated) | 733 | 135 | 2714 | 366 | 13 |
| Necessitation.Frag1Rows (generated) | 498 | 78 | 2498 | 358 | 14 |
| Necessitation.Frag2Rows (generated) | 320 | 64 | 1631 | 343 | 21 |
| Necessitation.Layout | 908 | 104 | 4710 | 320 | 7 |
| Necessitation.Lib.Occ | 190 | 105 | 472 | 251 | 53 |
| Necessitation.Prologue | 745 | 54 | 8310 | 214 | 3 |
| Necessitation.Lib.Lengths | 179 | 100 | 397 | 210 | 53 |
| Necessitation.Lib.Sets | 130 | 90 | 278 | 181 | 65 |
| Cells.Names | 173 | 173 | 174 | 174 | 100 |
| Necessitation.WalkLemmas | 132 | 31 | 641 | 117 | 18 |
| Necessitation.Frag1 | 155 | 10 | 2548 | 89 | 3 |
| Necessitation.Verify2 | 244 | 38 | 3768 | 88 | 2 |
| Agents.Fit | 50 | 16 | 377 | 85 | 23 |
| Bridge.Neg | 15 | 10 | 115 | 83 | 72 |
| Necessitation.NumSteps | 551 | 28 | 3195 | 79 | 2 |
| Agents.Code | 79 | 13 | 553 | 75 | 14 |
| Necessitation.Verify | 119 | 32 | 917 | 67 | 7 |
| Necessitation.Describe | 650 | 28 | 4818 | 66 | 1 |
| Necessitation.RowInstC | 29 | 18 | 103 | 64 | 62 |
| Necessitation.Lib.Nodes | 206 | 34 | 486 | 59 | 12 |
| Necessitation.NodeSize | 58 | 16 | 219 | 57 | 26 |
| Necessitation.Chain | 393 | 30 | 1847 | 44 | 2 |
| Agents.Guard | 52 | 22 | 149 | 41 | 28 |
| Box.Bew | 12 | 9 | 50 | 39 | 78 |
| Agents.Prog | 105 | 14 | 478 | 36 | 8 |
| Audit.RedCellUnsound | 50 | 11 | 412 | 33 | 8 |
| Assembly.Uniform | 21 | 6 | 142 | 30 | 21 |
| Agents.FitBox | 104 | 5 | 695 | 30 | 4 |
| Necessitation.IndRec | 153 | 13 | 3125 | 29 | 1 |
| Necessitation.Top | 290 | 11 | 2645 | 26 | 1 |
| Agents.CodeTerm | 100 | 8 | 584 | 26 | 4 |
| Eval.SimTest | 8 | 5 | 50 | 26 | 52 |
| Cells.DupocMirror | 42 | 3 | 335 | 25 | 7 |
| Cells.DIMCID | 135 | 5 | 892 | 25 | 3 |
| Bridge.AgentConverse | 21 | 4 | 275 | 25 | 9 |
| Necessitation.Verify3 | 55 | 6 | 1149 | 23 | 2 |
| Agents.Subst | 111 | 9 | 795 | 22 | 3 |
| Necessitation.Bounds | 44 | 4 | 414 | 21 | 5 |
| Cells.CIMCIC | 125 | 5 | 806 | 21 | 3 |
| Cells.JustBot | 82 | 4 | 469 | 20 | 4 |
| Box.ProperBound | 80 | 8 | 605 | 20 | 3 |

The remaining ~55 modules have under 20 dead lines each (1–2-line `X.definable`/`X.definable'`
Foundation boilerplate, a stray `_V` twin, an unused `_inj`).

## 3. What the dead code IS

### 3.1 Unused U10 library members (8 567 lines, 73 % of all dead lines)

The bounded-inner-necessitation kit is built as a LIBRARY of PA-provable formula schemas (`lib_<name>`
+ `models_<name>` + `pa_proves_<name>` + `<name>B` per member, in `Lib/*.lean`) that the flat step
lists cite by name, plus the generated instantiation/quote rows per member (`inst_<name>`,
`quote_row_<name>`, `isSemiformula_<name>_*`, `shift_*`, `fvOccF_*`, `isFormula_*` in `RowInst*.lean`,
and the `ctag/cIdx/cok/cmk/certPieces/certTable` sextuples in `CertRows.lean`). The library was written
ahead of the steps; the steps never cited many members:

| library file | `lib_` members | unused |
|---|---:|---:|
| `Lib/Frag.lean` (generated by `gen_frag.py`) | 207 | 70 |
| `Lib/Formulas.lean` | 84 | 53 |
| `Lib/Bridge.lean` | 49 | 37 |
| `Lib/Occ.lean` | 38 | 21 |
| `Lib/Lengths.lean` | 35 | 20 |
| `Lib/Sets.lean` | 26 | 18 |
| `Lib/Nodes.lean` | 45 | 10 |

and consequently `RowInst.lean` has 44 dead `inst_` rows (of 79) and `RowInstB.lean` 75 (of 207), with
every companion row; `CertRows.lean` has 14 dead certificate sextuples (of 88). The full member names
are in §6. Every one of these is cheap to remove IN THE GENERATOR (drop the member from `ROWS` /
the member list in `gen_rowinst.py`, `gen_frag.py`, `gen_cert.py`, `gen_indrec.py`, `gen_frag1.py`,
`gen_frag2.py`; regenerate; `regen_all.sh` must stay green) and in the hand-written `Lib/*` files
(delete the four-declaration block per member). Removing them cannot change any statement or the
census, because nothing live refers to them; it removes ~8.5k lines from the build's slowest layer.
Caveat: some members are cited by name inside Lean STRINGS in the generators' per-row proofs; the
regen + build is the check.

### 3.2 `Necessitation/` hand-written leftovers (2 055 lines)

* `*_definable` / `*.definable'` theorems (Foundation's definability boilerplate, 1–2 lines each,
  produced next to the `.defined` lemmas that ARE used): ~120 declarations across `Cert`, `Describe`,
  `Verify`, `Verify2`, `NumSteps`, `Guard`, `Prog`, `CodeTerm`, `Subst`, `BinNumeral`, `ProperBound`, `BewV`,
  `WalkLemmas`. Harmless; deleting them is churn for ~200 lines.
* `Layout.lean`: the `ltag_cong*` family (12 × 4 lines, `Layout:828–981`) and `tagAr_defined`/
  `tagAnts_defined` (42 lines each) — a superseded tagging route; 320 lines.
* `Cert.lean`: `dossT_transport`, `*Fact_definable`, `len_subVGraph_le` (40 lines),
  `dossT_func_isFunc` (33 lines) — 631 lines, spread over 164 small declarations.
* `Prologue.lean` 214 lines, `WalkLemmas.lean` 117 (`cTV_*`/`cT_*` LOR-side twins), `Verify.lean`
  67 (gen-1 `VerifyGraph.*_iff` case lemmas — the gen-1 graph itself is LIVE, the later generations
  build on it), `Verify2.lean` 88, `NodeSize.lean` 57 (`Derivation.*_inv`, `formulaLen_*_le_proofLen_*`),
  `RowInstC.lean` 64 (§3.C rows never cited), `Frag1.lean` 89 (`costSum_node*_le`).
* The four superseded U10 GENERATIONS are NOT dead: `VerifyKit`/`'`/`''`/`'''`, `boundedInnerNec_three/
  four_of_kit`, `topBound*_pb`, `deg_one/three/four`, `top_main*` are all ROOTS (the census prints
  them), and `Verify`→`Verify2`→`Verify3`→`Verify4`/`5` is one live chain to `sizeThmAll_holds`. If you
  want the intermediate degrees gone, that is a census DECISION (drop their `#print axioms` lines, rerun
  the audit), not a dead-code finding. Same for `Package.lean`'s `_of_sizeThm` forms.

### 3.3 Outside `Necessitation/` (925 lines) — read before deleting

| where | dead | what it is | verdict |
|---|---:|---|---|
| `Agents/Fit.lean` | 85 | `size_*_le`, `ppair_le_sq`, `canonical_le_self`, `size_canonical_Dupoc/Cupod_le`, `exists_size_const`, `termLenMeta_emb_*` | the pre-route-(c) fit arithmetic; superseded by `FitBox`/`guard_fits` | delete |
| `Agents/FitBox.lean` | 30 | `not_box_guard_fits`, `legibleBot_staggered_guard_never_fits`, `exists_formulaLenMeta_template_legible_const`, `binNumeral_le_quote_emb_subst`, `FOcc_rel` | **negative results cited by the notes** (`box_guard_never_fits` family, `ROUTE_B_SCOPE` §9) — dead only because the census never prints them | ADD to census (`#print axioms`), do not delete |
| `Bridge/Neg.lean` | 83 | `pBotIter`, `size_le_termLenMeta_binNumeralMeta`, `size_canonical_le_formulaLenMeta_sentenceAt`, … | T2 bridge material (frozen by decision) | leave with T2 |
| `Agents/Code.lean` | 75 | `noTauP`/`noTauP_subst`/`noDiag` (the tau/diag exclusion, 40 lines), `subst_of_closedF`, `progCode_tvote/sys/selfIdx`, `*_DupocBot` samples | `noTauP`/`noDiag` document the scope restriction; the rest is scaffolding | keep `noTauP`/`noDiag` (or cite them), delete the rest |
| `Agents/Guard.lean` | 41 | 22 × `.definable` boilerplate + `actTermCode*` (an unused term-level code) | delete `actTermCode*` (13 lines), boilerplate optional |
| `Box/Bew.lean` | 39 | `lenBoxNat`, `lenGödel`, `Arithmetic.*_lenGödel`, `Arithmetic.Proper` — the ℕ-level box | superseded by `Box/BewV` (9 of 12 declarations dead); the `ProofLength` lemmas `formulaLenMeta_le_proofLenMeta`/`formulaLenMeta_le_of_lenBoxNat` (17 lines) hang off it | delete both together, after the rationale note's mention of `lenBoxNat` is repointed |
| `Agents/Prog.lean` | 36 | `ppair_lt/le_ppair_*` order lemmas, `pBot_inj`/`pSim_inj`/`pIte_inj`, `.definable` | small; the `_inj` lemmas are the sort a future proof wants | optional |
| `Audit/RedCellUnsound.lean` | 33 | `evalGraphBadDef/_defined`, `lMap_swap_axEq*`, `exists_lenBox_TBad` | part of the "EvalGraphBad is a copy" debt | leave until that debt is paid |
| `Assembly/Uniform.lean` | 30 | `eval_psi_fixed_point_std/swap`, `chi₁_def`, `instB_quote_chi₁`, `chainBound_PLE`, `exists_forward_length` | the pre-family PBLT assembly, superseded by `Assembly/Family` | delete |
| `Eval/SimTest.lean` | 26 | `mirror_vs_const`, `transposeCode_Mirror`, `sim_search_outer_guard` (5 of 8) | smoke tests of `EvalGraph` (the file's purpose) | either add to census or delete the file |
| `Bridge/AgentConverse.lean` | 25 | `GuardAgree.of_forall/of_T/toT`, `evalGraph_actCode` | T2, frozen | leave with T2 |
| `Cells/DupocMirror` 25, `Cells/DIMCID` 25, `Cells/CIMCIC` 21, `Cells/JustBot` 20 | 91 | `semitermVec_val_q*` (15-line valuation lemmas), `*_instB_V`, `*V_nat`, `transposeCode_*TV`, `phiD_transpose` | leftovers of earlier proof routes inside otherwise fully-live cell files | delete |
| `Bridge/Core/Tr.lean` | 17 | `Core.tr_*` equation lemmas, `leaf_eq*_sound` | T2, frozen | leave |
| `Theory/Symmetry.lean` | 15 | `ProvableLen`, `provableLen_swap(_iff)` — the pre-`proofLen` symmetry statement | superseded by `Theory/Transpose` (`sfp_transpose`) | delete |
| `Theory/TheoryAct.lean` | 13 | `mem_TAct_iff`, `tact_proves_actionAxiom'`, `quote_func/rel_emb`, `stdReading_nat`, `eval_actionAxiom*_swappedReading` | tiny | optional |
| `Theory/LangAct.lean` | 11 | `LAct.encode_*` (4), `instReprAct`, `LAct.instORing`, `swap_inl` | tiny | optional |
| `Length/Proper` 16, `Box/CutV` 14 (`properBound_nat` — the ℕ properness bridge), `Box/ProperBound` 20 (`*_LOR`, `_V` twins), `Loeb/InstV` 13, `Agents/Subst` 22, `Agents/CodeTerm` 26, `Agents/Template` 12, `Agents/RevalueTemplate` 13, `Agents/InstanceV` 14, `Agents/BinNumeral` 11, `Assembly/Prep` 13 | 174 | duplicate `_V`/`_nat`/`'` twins, `.definable` boilerplate, `termLenMeta_emb_codeTermMeta_*` | the textual duplicate list (§5) covers the twins |

### 3.4 `Cells/Names.lean` (174 lines, 100 % dead by construction)

The 173 `@[deprecated]` aliases from the 2026-09-27 renaming (`<method>_<L>_vs_<R>` scheme). They exist
so that notes and the git history resolve; nothing in the package uses them and nothing should.
Decision: keep for one more release of the notes (grep the notes for the OLD names first — the
`ROUTE_B_CENSUS` table was rewritten to the new names, the older RESULTS addenda were not), or delete
the file and add a "renamed 2026-09-27" line to `ROUTE_B_CELLS_MAP.md`.

## 4. Proposed tiers (your call — nothing has been touched)

**Tier A — delete, no argument, no census change (~600 hand-written lines):**
`Agents/Fit.lean` dead block (85), `Assembly/Uniform.lean` dead block (30), `Theory/Symmetry.lean`
dead block (15), `Box/Bew.lean` + `Length/ProofLength.lean` dead blocks (56, one doc repoint), the four
cell-file leftovers (91), `Agents/Guard.lean` `actTermCode*` (13), `Agents/Code.lean` scaffolding
(35), `Layout.lean` `ltag_cong*` + `tagAr/tagAnts_defined` (320 — check no docstring cites them),
`RowInstC.lean` dead rows (64). Expected census change: none (every printed theorem is a root and
stays). Build: unchanged statements, fewer jobs.

**Tier B — delete in the generators + `Lib/*` (~8 500 lines, the real payoff):**
prune the unused library members (§6) from `gen_frag.py`/`gen_rowinst.py`/`gen_cert.py`/
`gen_indrec.py`/`gen_frag1.py`/`gen_frag2.py` and from the hand-written `Lib/*.lean`, regenerate,
`regen_all.sh` green, full build, census byte-identical (the row tables print nothing; the theorems that
do print never cite a dead member — by definition of the audit). One session of agent work; the risk
is a member cited only inside a proof STRING of another row (the build catches it). Also here: the ~120
`.definable` boilerplate lines and the `Cert`/`Prologue`/`Describe`/`Verify*`/`NodeSize`/`WalkLemmas`
small leftovers (~1 000 lines), each a `lake env lean` check on its file.

**Tier C — decisions, not deletions:**
1. `Agents/FitBox.lean`'s negative results and `Eval/SimTest.lean`: add `#print axioms` lines (they
   become roots) — they are results the notes cite.
2. The superseded U10 generations (degree 1/3/4 kits, `Verify`→`Verify3`, `Package._of_sizeThm`): all
   ROOTS today. Keeping them keeps the "degree 16 = 4·m" story checkable; dropping them from the census
   would make ~10k lines of `Necessitation/` deletable. Recommendation: keep (the notes and the paper
   quote the intermediate degrees).
3. `Bridge/*` (T2, 135 dead lines + the frozen modules): frozen by decision; audit again if T2 is
   ever unfrozen or dropped.
4. `Cells/Names.lean`: keep one cycle or delete with a map line (§3.4).
5. `Audit/RedCellUnsound.lean`: pay the "EvalGraphBad is a copy" debt first.

## 5. Textual pass (same session): duplicates and hygiene

No `sorry`, `axiom` or `native_decide` in `ArithS/` (three docstring mentions only). `set_option
maxHeartbeats/maxRecDepth` sites are essentially all in `Necessitation/` (expected for U10). Stale
"not yet"/"superseded" markers: three (`Assembly/Prep` header, `Assemble` header, `Lib/Nodes` design
note).

Identical statements under two names (candidates for one `abbrev`/alias each, or deleting the unused
twin — the audit says which twin is dead):
`termSubst_closed`=`termSubst_of_closed`; `revalue_param_eq`=`substCode_param_eq` (both private, both
dead); `val_ppairTermMeta`=`val_ppairTermMeta_V`; `val_succTT`=`val_succTT_V`; `isFunc_LAct`=`isFunc_LAct_iff_V`;
`IsSemiterm.LAct_of_LOR`=`isSemiterm_LAct_of_LOR`; `nth_descriptionsB_budget`=`nth_descriptionsB_six`;
`term_emb_lMap_emb`=`term_emb_lMap_emb'` (and `typed_val_emb`, each defined in `Template`, `InstV` and
`Diag`); `val_cterm_C/D`=`_V`; `termLen_binNumeral_le_V`=`termLen_binNumeral_le`; `one_le_termLen_V`=
`one_le_termLen` (the `_V` one is dead); `isFunc_LOR` (defined twice: `Subst`, `InstV`)=
`isFunc_LOR_iff_V`; `isFunc_LAct_of_LOR` (twice). Deliberate twins to KEEP: `guard_fits`=
`search_is_real`, `red_cell_words`=`red_cell`, `red_cell_deterministic`=`red_cell_unique` (audit
statements). The `eval_*_iff` groups the regex flagged are NOT duplicates (truncated at `(s := stdReading V)`).

## 6. Unused library members (for Tier B)

`Lib/Frag` (70): adjoinFun, binNumeralFun, binNumeralOddCert, bvAll, bvExs, bvFalsum, bvFun, bvNRel, bvOr, bvRel,
bvTotal, bvVerum, congInsertL, congIsFormulaSet, congNegL, congSubsetR, congSubstL, congUfPi,
formulaLenFun, freeFun, fstIdxFun, fvarVecFun, fvarVecNth, fvarVecTotal, gIntro, insertFun, lengthFun,
lengthTotal, lengthTwoMul, lengthTwoMulOne, listMaxAdj, listMaxNil, listSumFun, maxEqLeft, maxEqRight,
maxTotal, negFun, nthFun, qVecFun, qqAllFun, qqAllsFun, qqBvarFun, qqExsFun, qqFalsumFun, qqFuncFun,
qqFvarFun, qqNRelFun, qqOrFun, qqRelFun, qqVerumFun, sequentLenFun, shiftFun, subAddCancel, subOfLe,
subTotal, substs1Fun, substsFun, termBShiftFun, termBVBvar, termBVFunc, termBVFvar, termBVVecAdj,
termBVVecNil, termLenFun, termLenVecFun, termShiftFun, termShiftVecFun, termSubstFun, termSubstVecFun,
twoMulOneMul.

`Lib/Formulas` (53): freeAll, freeAnd, freeExs, freeFalsum, freeNRel, freeOr, freeRel, freeVerum,
isFormulaFree, isSemiformulaNeg, isSemiformulaShift, isSemiformulaSubsts1, negAll, negExs, negFalsum,
negNRel, negOr, negRel, negVerum, qVecTotal, shiftAll, shiftAnd, shiftExs, shiftFalsum, shiftInvAll,
shiftInvExs, shiftInvFalsum, shiftInvNRel, shiftInvOr, shiftInvRel, shiftInvVerum, shiftNRel, shiftOr,
shiftRel, shiftVerum, substs1Total, substsAnd, substsExs, substsFalsum, substsInvAnd, substsInvExs,
substsInvFalsum, substsInvNRel, substsInvOr, substsInvRel, substsInvVerum, substsNRel, substsOr,
substsRel, substsTotal, substsVerum, termShiftVecTotal, termSubstVecTotal.

`Lib/Bridge` (37): impGraphOROfLAct, indSubstConst1VecOR, isFuncLActOfLOR, isFuncLOROfLAct,
isRelLActOfLOR, isRelLOROfLAct, isSemiformulaAllOR, isSemiformulaAndOR, isSemiformulaExsOR,
isSemiformulaFalsumOR, isSemiformulaNRelOR, isSemiformulaNegOR, isSemiformulaOrOR, isSemiformulaShiftOR,
isSemiformulaSigmaPiLAct, isSemiformulaSubstOR, isSemiformulaVerumOR, isSemitermBvarOR,
isSemitermFuncOR, isSemitermFvarOR, isSemitermLActOfLOR, isSemitermSigmaPiOR, isSemitermVecAdjoinOR,
isSemitermVecLActOfLOR, isSemitermVecNilOR, isSemitermVecSigmaPiOR, isUFormulaLActOfLOR,
isUFormulaOfSemiformulaOR, isUFormulaSigmaPiLAct, isUFormulaSigmaPiOR, isUTermVecLActOfLOR,
isUTermVecOfSemitermVecOR, isUTermVecSigmaPiOR, negGraphOROfLAct, shiftGraphOROfLAct,
termShiftVecGraphOROfLAct, termSubstVecGraphOROfLAct.

`Lib/Occ` (21): addLeAdd₃, fvOccBvar, fvOccFAll, fvOccFExs, fvOccFFalsum, fvOccFLeFormulaLen,
fvOccFNRel, fvOccFOr, fvOccFRel, fvOccFShift, fvOccFTotal, fvOccFVerum, fvOccFvar, fvOccLeTermLen,
fvOccSEmpty, fvOccSLeSetLen, fvOccSSetShiftLe, fvOccTermShift, fvOccVecTotal, leAddLeft, leOfEqLe.

`Lib/Lengths` (20): addAssoc, addComm, binNumeralOdd, binNumeralTotal, formulaLenNRel, formulaLenNeg,
formulaLenRel, leAddRight, leOfEq, leOfLeEq, listSumTotal, sequentLenEmpty, sequentLenTotal, succLeSucc,
termLenFunc, termLenVecTotal, twoMulAdd, twoMulAddOne, twoMulOneAdd, twoMulOneSucc.

`Lib/Sets` (18): emptySubset, freeTotal, insertTotal, isFormulaSetInsertInv, isFormulaSetMem,
isFormulaSetOfNoMem, isFormulaSetOfSetShift, isFormulaSetPiSigma, isFormulaSetSetShift,
isFormulaSetSigmaPi, isSemiformulaPiSigma, memInsertSelf, notMemEmpty, shiftTotal, subsetInsert,
subsetMem, subsetRefl, subsetTrans.

`Lib/Nodes` (10): axPiSigma, axSigmaPi, axiomRec_actionAxiom', axiomRec_constNe, axiomRec_constNe', axiomRec_paMinus,
derivationSigmaPi, proofLenGraphPiSigma, proofLenGraphSigmaPi, totIndBody.

`RowInst` dead `inst_` rows (44) and `RowInstB` (75) follow from the lists above (plus `RowInst`:
isSemiformulaSubst, isSemitermVecQVec, negTotal, shiftTotal, substs1Substs; `RowInstB`: bvAnd,
congMemSet, congShiftL, listSumAdj, qVecNth0, qqAndFun, setShiftFun, twoMulMul — members whose `lib_`
entry is live but whose instantiation row is not).

To regenerate the full table: run the command at the top; the TSV is not committed (2 MB, three minutes).

## 7. Tier B executed (2026-09-28, commit `f2bcc2e`)

**Removed: 3 250 declarations, 12 543 lines over 55 files** (`ArithS` 146 775 → 134 383 lines). Build
green (3370 jobs); census unchanged — 1896 `#print axioms`, every list `[propext, Classical.choice,
Quot.sound]` but the four pre-existing subsets; `regen_all.sh` all nine `ok`. The re-run audit gives
the invariant that matters: **LIVE 12 191 and ROOT 1 822 before and after** — nothing reachable was lost.

| | before | after |
|---|---:|---:|
| non-aux declarations | 18 091 | 14 486 |
| DEAD declarations | 4 078 | 473 |
| DEAD declaration lines | 11 721 | 1 176 |
| of which under `Necessitation/` | 10 622 | 141 |

**What the closure cannot see — 71 declarations kept on purpose** (the five build iterations it took to
find them are the lesson; `ARITH_TRAPS.md` §6):
1. lemmas proved by `rfl` (`exsIter_zero`, `bvarList_*`, `row_*_R_eq`, `vecOf_two`, …): `simp`/`dsimp`
   use them as definitional rewrites and leave no constant in the proof term;
2. names that only OCCUR in code — inside a tactic macro's `simp only [...]` list (`isUTerm_cT` in
   `row_entriesB`), in a `simp [...]` set that never fired, or in an `example` (`addCommB`): deleting
   them is "unknown identifier" at elaboration, with no proof term ever involved.
The rule now applied (`scratchpad` scripts, reproducible from the TSV): restore = names mentioned in the
pruned tree's code (comments stripped, macro bodies included), closed under the pruned names their own
statements mention, plus every `rfl`-proved lemma whose statement mentions no pruned name.

**Mechanism, for the next round.** Generated tables: `scripts/pruned/<module>.txt` + `scripts/prune.py`
(the row TABLES are untouched — indices are append-only — so a pruned producer row keeps its
`⟨m, <row>B, lib_<row>⟩` entry and its `cpiece_`/`certTable_`/`cmk_` derived lemmas; only `inst_`,
`quote_row_`, `isSemiformula_*` and the consumer's `*ok_` go). Hand-written files: deleted by the audit's
declaration ranges; the range sometimes starts at the docstring and sometimes after it, and a bare
`@[…]` line is swallowed while a `@[simp] lemma …` neighbour is not.

**What remains dead (473 declarations, 1 176 lines)** is Tier A/C material outside `Necessitation/`
(`Agents/Fit`, `Assembly/Uniform`, `Theory/Symmetry`, `Box/Bew`, cell-file leftovers, the 173 aliases of
`Cells/Names.lean`, the FitBox/SimTest results to be added to the census, `Bridge/*`) plus the 71
above and ~70 one-line `*_R_eq`/`bvarList_*` rfl twins in the row tables — see §3.3–§3.4 and §4.

## 8. Tier D executed (2026-10-29): the twin audit of `Cells/`

**Question.** After the hand-template twins were retired from the matrix (2026-10-02: every cell stated
on the engine's own `progCode`s), how much of `Cells/` still served a claim? The September audit could not
say: its ROOTS were the census, and the twin cells were still `#print axioms`-ed, hence ROOT by definition.

**Method.** `scripts/DeadCode.lean` (restored from `6bb4855`, gone since the spikes clean-up) gained a
CLAIMS mode: `DEADCODE_ROOT_MODULES=<prefixes>` makes every non-aux constant of the named modules a root,
independently of the census. Roots used: `Outcome.*` (the 132 `@[outcomeA]` cells and 30 `@[floorA]`
floors), `Tau.Rows.*` + `Tau.Check`, `Readings`, `Assembly.Cell` (PBLT), `Necessitation.Package`,
`Cells.{FloorDichotomy,FloorVerdicts,Transposition,RedCell}`, plus the 46 `#check` names of `Tour.lean`;
635 roots. Scope: `ArithS.Cells.*` only (the results tier; the trusted base and the Löb tier were left
alone — `Agents/InstanceV`'s `DupocV`/`CupodV` are LIVE anyway: they are the vehicles of the engine-code cells).

**Result before.** 832 of 2417 hand-written declarations in `Cells/` (4185 lines) unreachable from any
claim; 305 of them were census ROOTS (the retired twin cells `loeb_Just7_vs_Just7`, `loeb_Cimcic_vs_Just7`,
`loeb_DIMCID_vs_Just7`, `loeb_DIMCID_vs_CupodTroll7`, the `Just7`/`CupodTroll7`/`JustV` towers and their
`canonical_*`/`revalue*_*`/`transposeCode_*` kits). Five modules 100 % dead: `Cells/JustBot` (the hand
`JustV`), `Cells/DupocMirror` (the hand-code Dupoc × Mirror route, superseded by `DupocEngine`),
`Cells/SimSlot`, `Cells/TauMember` (Phase-2 gates), `Cells/Names` (the 173 deprecated aliases, §3.4).

**Deletion rule (the fixpoint).** A dead declaration is deleted iff every textual mention of its short
name outside its own range is inside a comment (a proper lexer: nested `/- -/`, `--`, strings) or inside
the range of another declaration being deleted. Hand-written lemmas whose names contain `_eq_`
(`JustV7_eq_inner`, …) are NOT compiler auxiliaries although the tool's `isAuxName` says so — 46 of them
were added back into the candidate set by requiring that an "aux" row share its declaration range with a
non-aux one. Two build-breaking lessons: a deleted module's `import`s are transitive for its importers
(re-add the module's own imports where it was imported); an `omit … in` / `set_option … in` immediately
before a deleted declaration dangles (one case; the six `omit … in` lines that precede a DOC COMMENT are
legitimate — the modifier applies across the docstring).

**Executed.** 795 declarations + the 173 aliases deleted, 5 modules removed, 5371 lines out of `ArithS/`
(`Cells/` 20260 → 15257 lines), 322 `#print axioms` lines dropped from `Audit/Cells.lean` (the census is
every claim's axioms, not every leftover's). 19 dead declarations kept: referenced from live code
(`TBD`/`TBD4` from JustSlot's live `sVec7` kit, `cons_val_*` in JustEngine, `guardTemplateJust7*`, …).
Build green (3502 jobs), censuses unchanged (132 / 30 / 78/78; tau 256/256 COMPLETE), the axiom census
the same four pre-existing subsets, `export_sprime_outcomes` byte-identical, `check_tiers.py` ok.
Confirming re-run: `Cells/` 1527 hand-written declarations, 31 dead (47 lines) from the claims, 35 from
the census; the LIVE set is identical before and after (22264 constants).

The tool and its two modes are documented in `arith/scripts/README.md`; `scripts/roots.txt` is the
regenerated census (2219 names).


## 9. Tier E executed (2026-10-29, same day): the engine's `S` is no longer used by `ArithS`

**Question.** Which parts of the engine does `ArithS` really depend on? A reachability measurement
(`EngineDeps.lean`, the same closure as §8 but collecting the ENGINE constants the live `ArithS`
declarations use) answered: 246 constants in 54 engine modules — `Program` (71: the language),
`Tau.Zoo`/`Roster`/`Spec`/`Vote` (87: the τ-roster), `Base.Transpose` (28: the syntactic transposition
`τ̂`), `Dynamics` (8: `eval`/`play`/`outcome`, the lockstep), `Outcome.Spec` (6: the regimes), one
constant from each of 20 bot files and each of 27 search-free cell theorems. ZERO constants from
`ProofSystem`, `Base/Soundness`, `Base/AtomCerts`, `Base/Exclusion`, `Base/RedCellFramework`: the
rule-based `S` was reached only by the frozen T2 bridge (`Bridge/`) and the engine-level red-cell audit twin
(`Audit/RedCellInstance`), none of which any claim uses.

**Executed.** The §8 fixpoint over `Bridge/*`, `Eval/Det`, `Audit/RedCellInstance`: 112 declarations and the
modules `Bridge/EngineBridge`, `Bridge/Core/{Tr,Sound}`, `Audit/RedCellInstance` deleted (1242 lines); the
five direct imports of `S`'s theory removed. What remains of `Bridge/` is the evaluation-certificate kit the
cells use (`Agent`: `properPlayer_*`, `models_sentenceAt_of_lenBox`, …; `Inst`: the `inst` instantiation and
its simp set; `AgentConverse`: `outcome_eq_some_iff`; `Neg`: the size arithmetic `FitBox`/`NeverFits` need) —
not a bridge any more, kept under its old name so that the notes' paths resolve. Consequence for the engine
dependency: `ArithS` imports the engine's language, evaluator, bots, τ-roster, `τ̂` and 27 search-free cells.
`ProofSystem` stays in the TRANSITIVE closure for one reason only — `Dynamics.eval`'s search clause is
`decide (Pf k φ)`, so `Pf` is part of the evaluator's definition — but no rule, soundness or exclusion
theorem of `S` is used anywhere in `ArithS`.

**Three traps, each one build.** (1) A `simp` set is invisible to the closure: six `@[simp] … := rfl`
lemmas of `Bridge/Inst` (`inst_emb_func`, `inst_emb_rel`, …) were "dead" and `lMap_inst_emb` stopped
closing — restored. (2) A surviving lemma used `PD.play` through a removed import — `Dynamics` imported
explicitly. (3) `Mathlib.Tactic` (and `Mathlib.Data.Nat.Log`) reached `Necessitation/` only through the
engine's `Base/Asymptotics`; `interval_cases` became an unknown tactic in `Layout.lean` — the two imports
now sit in `Bridge/Neg.lean`, the lowest surviving point of the old chain.

Gates: build 3495 jobs, censuses unchanged (132 / 30 / 78/78; tau 256/256), axiom census the same four
subsets, export byte-identical, `check_tiers.py` ok (frozen tier 7 modules), LIVE set 22264 before and
after, engine usage 246 constants before and after.
