# PATHS — the 2026-09-28 reorganization of `arith/ArithS/`

On 2026-09-28 the 47 top-level files of `ArithS/` (and `Core/`) were grouped into layer folders
following `CLAUDE.md` Part III's layer table, and the single `ArithS/Audit.lean` (3.3k lines) was
split per layer. Every move was a `git mv` (history preserved); no declaration NAME or STATEMENT
changed (the namespace is `ArithS` throughout, module paths are not names), the build's axiom census
is identical line for line, and the generated row tables regenerate byte-identically
(`scripts/regen_all.sh`). Notes written before this date cite the OLD paths; read them through this
table. Docstrings inside the `.lean` files that cite a sibling by its old file name were left as they
were (content untouched beyond `import` lines).

## Modules (old → new; module name `ArithS.<path with dots>`)

| Layer (folder) | Old path | New path |
|---|---|---|
| `Theory/` | `ArithS/LangAct.lean` | `ArithS/Theory/LangAct.lean` |
| `Theory/` | `ArithS/TheoryAct.lean` | `ArithS/Theory/TheoryAct.lean` |
| `Theory/` | `ArithS/Symmetry.lean` | `ArithS/Theory/Symmetry.lean` |
| `Theory/` | `ArithS/Transpose.lean` | `ArithS/Theory/Transpose.lean` |
| `Theory/` | `ArithS/Sound.lean` | `ArithS/Theory/Sound.lean` |
| `Length/` | `ArithS/Length.lean` | `ArithS/Length/Length.lean` |
| `Length/` | `ArithS/SequentLength.lean` | `ArithS/Length/SequentLength.lean` |
| `Length/` | `ArithS/DerivationLength.lean` | `ArithS/Length/DerivationLength.lean` |
| `Length/` | `ArithS/MetaLength.lean` | `ArithS/Length/MetaLength.lean` |
| `Length/` | `ArithS/Proper.lean` | `ArithS/Length/Proper.lean` |
| `Length/` | `ArithS/ProofLength.lean` | `ArithS/Length/ProofLength.lean` |
| `Box/` | `ArithS/Bew.lean` | `ArithS/Box/Bew.lean` |
| `Box/` | `ArithS/BewV.lean` | `ArithS/Box/BewV.lean` |
| `Box/` | `ArithS/Cut.lean` | `ArithS/Box/Cut.lean` |
| `Box/` | `ArithS/CutV.lean` | `ArithS/Box/CutV.lean` |
| `Box/` | `ArithS/ProperBound.lean` | `ArithS/Box/ProperBound.lean` |
| `Agents/` | `ArithS/Prog.lean` | `ArithS/Agents/Prog.lean` |
| `Agents/` | `ArithS/CodeTerm.lean` | `ArithS/Agents/CodeTerm.lean` |
| `Agents/` | `ArithS/RevalueTemplate.lean` | `ArithS/Agents/RevalueTemplate.lean` |
| `Agents/` | `ArithS/BinNumeral.lean` | `ArithS/Agents/BinNumeral.lean` |
| `Agents/` | `ArithS/Template.lean` | `ArithS/Agents/Template.lean` |
| `Agents/` | `ArithS/Guard.lean` | `ArithS/Agents/Guard.lean` |
| `Agents/` | `ArithS/Subst.lean` | `ArithS/Agents/Subst.lean` |
| `Agents/` | `ArithS/Code.lean` | `ArithS/Agents/Code.lean` |
| `Agents/` | `ArithS/Instance.lean` | `ArithS/Agents/Instance.lean` |
| `Agents/` | `ArithS/InstanceV.lean` | `ArithS/Agents/InstanceV.lean` |
| `Agents/` | `ArithS/Fit.lean` | `ArithS/Agents/Fit.lean` |
| `Agents/` | `ArithS/FitBox.lean` | `ArithS/Agents/FitBox.lean` |
| `Eval/` | `ArithS/Eval.lean` | `ArithS/Eval/Eval.lean` |
| `Eval/` | `ArithS/EvalN.lean` | `ArithS/Eval/EvalN.lean` |
| `Eval/` | `ArithS/SimTest.lean` | `ArithS/Eval/SimTest.lean` |
| `Eval/` | `ArithS/Transparency.lean` | `ArithS/Eval/Transparency.lean` |
| `Eval/` | `ArithS/Det.lean` | `ArithS/Eval/Det.lean` |
| `Loeb/` | `ArithS/Diag.lean` | `ArithS/Loeb/Diag.lean` |
| `Loeb/` | `ArithS/InstV.lean` | `ArithS/Loeb/InstV.lean` |
| `Loeb/` | `ArithS/NumeralFacts.lean` | `ArithS/Loeb/NumeralFacts.lean` |
| `Bridge/` | `ArithS/Core/Tr.lean` | `ArithS/Bridge/Core/Tr.lean` |
| `Bridge/` | `ArithS/Core/Sound.lean` | `ArithS/Bridge/Core/Sound.lean` |
| `Bridge/` | `ArithS/Agent.lean` | `ArithS/Bridge/Agent.lean` |
| `Bridge/` | `ArithS/AgentConverse.lean` | `ArithS/Bridge/AgentConverse.lean` |
| `Bridge/` | `ArithS/Inst.lean` | `ArithS/Bridge/Inst.lean` |
| `Bridge/` | `ArithS/Neg.lean` | `ArithS/Bridge/Neg.lean` |
| `Bridge/` | `ArithS/EngineBridge.lean` | `ArithS/Bridge/EngineBridge.lean` |
| `Audit/` | `ArithS/RedCellAudit.lean` | `ArithS/Audit/RedCellAudit.lean` |
| `Audit/` | `ArithS/RedCellUnsound.lean` | `ArithS/Audit/RedCellUnsound.lean` |
| `Audit/` | `ArithS/RedCellInstance.lean` | `ArithS/Audit/RedCellInstance.lean` |
| `Cells/` | `ArithS/RedCell.lean` | `ArithS/Cells/RedCell.lean` |
| *(top level)* | `ArithS/Basic.lean` | unchanged (the M0 smoke test, imported only by the root) |
| *(top level)* | `ArithS/Audit.lean` | unchanged path; now a thin module importing the nine `Audit/<Layer>.lean` below |
| `Assembly/`, `Necessitation/`, `Cells/` | unchanged | unchanged |

## The census split (`ArithS/Audit.lean` → `ArithS/Audit/<Layer>.lean`)

| File | `#print axioms` lines | Blocks (former `Audit.lean` line ranges) |
|---|---|---|
| `Audit/Theory.lean` | 9 | τ-closure of `TAct` (127), the action axiom `actionAxiom` (204) |
| `Audit/Length.lean` | 0 | placeholder — no headline theorem of the length layer is printed; its consumers are under `Box` |
| `Audit/Box.lean` | 16 | bounded D2 in rule form (132), `CutV` (141), `ProperBound` (151) |
| `Audit/Agents.lean` | 13 | programs by terms (214), the code translation (367), `FitBox` (379) |
| `Audit/Eval.lean` | 16 | Dupoc transparency (225), `Det` (372) |
| `Audit/Loeb.lean` | 77 | `InstV` (160), `NumeralFacts` (176), `Diag` (189), `Assembly/{Prep,Uniform,Cell,Family}` (243–308) |
| `Audit/Necessitation.lean` | 766 | U10, `Necessitation/Primitives` … `Package`, `ClosedNec` (386–1986) |
| `Audit/Bridge.lean` | 24 | T2-CORE, T2-NEG (retired), T2-AGENT + converse, the instantiation (330–355) |
| `Audit/Cells.lean` | 954 | T1, the red cell and its audit twins (104), then route B: `Cells/Common/*`, the families, SF/SND/POS, the flips, the floors, `PrudentLoose` (2010–3295) |

Sum 1875 = the former `Audit.lean`'s count. The other 26 census lines come from the modules that keep
their own prints: `Audit/RedCellAudit` (5), `Audit/RedCellUnsound` (7), `Eval/Det` (5), `Agents/FitBox`
(9) — 1901 lines in all, every one `[propext, Classical.choice, Quot.sound]` but the four pre-existing
subsets.

## Import-list conventions after the move

Every new module is still imported in BOTH `ArithS.lean` and the census (now the relevant
`ArithS/Audit/<Layer>.lean`, which has its own minimal import list). The generator headers
(`scripts/*.lean.head`, `scripts/gen_*.py`) import only `ArithS.Necessitation.*`, which did not move.

## Renames (2026-09-29, the readability pass)

| old | new | where |
|---|---|---|
| `GtmplA a` | `guardTemplate a` | `Agents/Template.lean` and every user (a word-boundary rename; notes updated) |
| — | `□[k] φ` | scoped notation for `LenBox TAct k φ`, `Outcome/Spec.lean` |
| — | `plays`, `OutcomeAtA`, `OutcomeSpecA`, `bot`, `const` | the engine's outcome vocabulary on codes, `Outcome/Spec.lean` |
| — | `outcome_<L>_vs_<R>` | one theorem per ledger cell, `Outcome/Matrix/<L>.lean` (107), proved from the `Cells/` theorems |
| — | `snd_DupocBot_vs_CupodBot` | the red cell on the engine's `progCode`, `Cells/RedCellEngine.lean` |

`guardCode`/`guardCodeB` and `descriptions`/`descriptionsB` were considered and kept: `guard` collides with the
core library's `guard`, and the `B` suffix is the budget-slot marker every note uses. The reading guide
is `ArithS/README.md`.

## Renames (2026-09-30, the deep clean of the important names)

Component renames: every identifier containing the old name as a component follows it (`dlenDef` →
`proofLenDef`, `DlenGraph` → `ProofLenGraph`, `setLenFact` → `sequentLenFact`, …), in code, generators,
pruned lists, notes and docs alike; no aliases. Conventions: the plain name is the code-level (inside PA)
object, `…Meta` its twin on Lean syntax; the former `V` suffix (model-generic) is gone and the ℕ-only
version, where one survives, is `…Nat`.

| old | new | old | new |
|---|---|---|---|
| `stdAct` / `stdActS M` / `swapActS M` / `stdActV` | `stdReadingNat` / `stdReading M` / `swappedReading M` / `stdReadingV` | `axAct`, `axAct'`, `axNe`, `axNe'` | `actionAxiom`, `actionAxiom'`, `constNe`, `constNe'` |
| `tact_complete'` / `tact_complete` | `TAct_complete_of_readings` / `TAct_complete` | `setLen`, `SetLen` | `sequentLen`, `SequentLen` |
| `dlen`, `Dlen…`, `DLen` | `proofLen`, `ProofLen…` | `tlen`, `flen`, `sqlen`, `mlen` | `termLenMeta`, `formulaLenMeta`, `sequentLenMeta`, `proofLenMeta` |
| `LenProvableV` / `lenProvableV` | `LenBox` / `lenBox` | `LenDerivable` / `lenDerivable` | `LenBoxUnbounded` / `lenBoxUnbounded` |
| `LenProvable` / `lenProvable` (ℕ, parametric bound) | `LenBoxNat` / `lenBoxNat` | `fbound` | `codeBound` |
| `ProperV`, `properV_*` | `ProperBound`, `properBound_*` | `Proper f k T` (`Bew.lean`) | `ProperBoundNat` |
| `Proper (p : Prog)`, `proper_<Bot>` | `ProperPlayer`, `properPlayer_<Bot>` | `lenProvableV_cut_V'` / `…_sharp'` / `lenDerivable_cut_V` | `lenBox_mp` / `lenBox_mp_sharp` / `lenBoxUnbounded_mp` |
| `lenDerivable_iff_lenProvableV` | `lenBoxUnbounded_iff_lenBox` | `lenProvable_fbound_swap_iff` | `lenBoxNat_swap_iff` |
| `relabel`, `Relabel…`, `relabelAct`, `relabelTemplate` | `revalue`, `Revalue…`, `revalueAction`, `revalueTemplate` | `swapAct`, `swapcode` | `swapAction`, `transposeCode` |
| `dnum`, `dU`, `dW` (+ `…T` meta) | `canonical`, `revalueU`, `revalueW` (+ `…Meta`) | `bnum`, `bnumT`, `Bnum…` | `binNumeral`, `binNumeralMeta`, `BinNumeral…` |
| `progT`, `progTT`, `ProgT…` | `codeTerm`, `codeTermMeta`, `CodeTerm…` | `ppairT`, `ppairTT` | `ppairTerm`, `ppairTermMeta` |
| `descVec`, `descVecB`, `descVecSlot`, `descTerms` | `descriptions`, `descriptionsB`, `descriptionsSlot`, `descriptionTerms` | `gtmpl`, `Gtmpl`, `guardSentenceA` | `guardTemplateRaw`, `guardTemplate7`, `guardSentence` |
| `GtmplJ`, `GtmplJ7`, `GtmplJ7A`, `GtmplT7`, `GtmplT7A` | `guardTemplateJust`, `…Just7`, `…Just7A`, `…Troll7`, `…Troll7A` | `pcode`, `tcode`, `tmpl`, `trAt` | `progCode`, `templateCode`, `template`, `sentenceAt` |
| `psubst`, `Psubst…`, `gsubst` | `substCode`, `SubstCode…`, `substTemplate` | `dupoc_self_coop_unconditional` / `dupoc_self_coop` (conditional) | `dupoc_self_coop` / `dupoc_self_coop_of_nec` |
| `pblt_unconditional` | `pblt` | files `Agents/{Bnum,ProgT,RelabelTemplate}.lean` | `Agents/{BinNumeral,CodeTerm,RevalueTemplate}.lean` |

Unchanged on purpose: `LAct`, `TAct`, `swap`, `emb`, `ppair`, `pConst…pSearch`, `EvalGraph`, `guardCode`/
`guardCodeB`, `guardTemplate`, `termLen`/`formulaLen`, `red_cell`, `boundedInnerNec_sixteen`, the cell heads,
and every name internal to `Necessitation/` except where a renamed definition is used there.

## New modules and splits (2026-09-30, the readability moves)

No declaration name or statement changed; two files were split at a top-level boundary and two reordered.

| module | what | where it came from |
|---|---|---|
| `ArithS.Notation` | the scoped notation `□[k] φ` (= `LenBox TAct k φ`) and the three-layer table | hoisted from `Outcome/Spec.lean`, which now imports it |
| `ArithS.Tour` | the guided tour: the nine definitions at ℕ by `rfl`, the red cell step by step, the headline `#check`s, `#print axioms` | new; imported last in `ArithS.lean` |
| `ArithS.Eval.Fixpoint` | `EvalFix.Phi`, blueprint, construction, finiteness | the first two thirds of `Eval/Eval.lean`; `Eval/Eval.lean` keeps `EvalGraph`, `evalGraphDef`, `EvalGraph.case_iff` |
| `ArithS.Agents.SubstTemplate` | `substTemplate`, the gate lemma, the kept slot, the swap equation `revalueTemplate_substTemplate` | the first 764 lines of `Agents/Subst.lean`; `Agents/Subst.lean` keeps `SubstCode`, `substCode`, τ-equivariance |
| `ArithS.Agents.Guard` (reordered) | the eleven definitions first, then one plumbing section with every Σ₁ graph and `defined` instance | same file |
| `ArithS.Theory.LangAct` (reordered) | `emb` and `swap` moved above the Gödel encoding | same file |

Every trusted-base file's module docstring ends with a **Reading guide** line (definition / plumbing to skip /
facts), and plumbing section headers say so. The new modules are imported in `ArithS.lean` and in the
audit file of their layer (`Audit/Box`, `Audit/Agents`, `Audit/Eval`).

## Tiers as lake targets, the ℕ readings, the header rule (2026-09-30, second batch)

| module / file | what |
|---|---|
| `ArithS.Readings` | the nine definitions read at ℕ, one named theorem each (`swap_involutive`, `TAct_sound_nat`, `proofLen_nat`, `box_nat`, `description_nat`, `binNumeral_nat`, `guard_nat`, `eval_deterministic_nat`, `eval_monotone_nat`); every trusted-base reading guide points here |
| `ArithS.Core`, `ArithS.Frozen`, `ArithS.PBLT`, `ArithS.Matrix` | one-file roots of the lake libraries `ArithSCore`, `ArithSFrozen`, `ArithSLoeb`, `ArithSMatrix` (`ArithSAudit` is rooted at the existing `ArithS.Audit`); `lakefile.toml` |
| `scripts/check_tiers.py` | import direction core < frozen < Löb < results < top, results reach `Necessitation/` only through `Package`/`ClosedNec`, each root imports exactly its tier |
| `models_constNe`, `models_constNe'`, `models_TAct` | MOVED from `Cells/RedCell.lean` to `Theory/TheoryAct.lean` (soundness in ℕ belongs to the theory file) — same names |
| `Matrix.lean` docstring | the `Cells/` header rule: uniform methods by method, Löb cells by bot |
| date stamps | removed from module docstrings and section headers across `Cells/`, `Agents/`, `Theory/`, `Eval/`, `Assembly/`, `Necessitation/Package` (30 files; `Cells/Names.lean`'s `since :=` attributes and two historical "since 2026-09-11" sentences kept) |

## Twin retirement (2026-09-30, third batch)

| new module | cells now on the engine's codes (`Outcome/Matrix/`) | replaces |
|---|---|---|
| `ArithS.Cells.DupocEngine` | `outcome_DupocBot_vs_DupocBot`, `outcome_CupodBot_vs_CupodBot`, `outcome_DupocBot_vs_MirrorBot`, `outcome_CupodBot_vs_MirrorBot` (`loeb_<L>_vs_<R>` + `_guard`) | `outcome_Dupoc_vs_Dupoc`, `outcome_Cupod_vs_Cupod`, `outcome_Dupoc_vs_MirrorBot`, `outcome_Cupod_vs_MirrorBot` |
| `ArithS.Cells.CimcicEngine` | `outcome_CIMCIC_vs_DupocBot` (`loeb_CIMCIC_vs_DupocBot`, `_guards`, `loebSound_pCiDb`) | `outcome_CIMCIC_vs_Dupoc` |
| `ArithS.Cells.DimcidEngine` | `outcome_DIMCID_vs_CupodBot` (`loeb_DIMCID_vs_CupodBot`, `_guards`) | `outcome_DIMCID_vs_Cupod` |

The hand-twin `Cells` theorems are untouched (only the `outcome_` statements moved). Seven twin cells remain, all
with `Just`/`Just7`/`CupodTroll7` as a player or opponent — not retirable (`README.md` §4).
