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
| `Box/` | `ArithS/ProperV.lean` | `ArithS/Box/ProperV.lean` |
| `Agents/` | `ArithS/Prog.lean` | `ArithS/Agents/Prog.lean` |
| `Agents/` | `ArithS/ProgT.lean` | `ArithS/Agents/ProgT.lean` |
| `Agents/` | `ArithS/RelabelTemplate.lean` | `ArithS/Agents/RelabelTemplate.lean` |
| `Agents/` | `ArithS/Bnum.lean` | `ArithS/Agents/Bnum.lean` |
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
| `Audit/Theory.lean` | 9 | τ-closure of `TAct` (127), the action axiom `axAct` (204) |
| `Audit/Length.lean` | 0 | placeholder — no headline theorem of the length layer is printed; its consumers are under `Box` |
| `Audit/Box.lean` | 16 | bounded D2 in rule form (132), `CutV` (141), `ProperV` (151) |
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
