# `ArithS` — reading guide

`ArithS` is the engine's proof system `S` replaced by **Peano Arithmetic with a length-bounded
provability predicate** (PA-`S'`), on the Foundation library, with the engine's matrix re-proved cell
by cell. It is 134k lines of Lean, and a reader needs about 5 % of them. This file says which.

The design and its rationale are in `engine/PrisonersDilemma/Research/Notes/SPRIME_DESIGN_RATIONALE.md`;
what is proved is in `ARITHMETIZED_S_RESULTS.md`; the cell ledger is `ROUTE_B_CENSUS.md`. This guide is
the index of the code.

## 0. Two files to open first

* [`Tour.lean`](Tour.lean) — the nine trusted definitions restated at `V = ℕ` (kept in sync by `rfl`), the red
  cell step by step, the headline theorems by `#check`, and the axiom census of what it cites. One file,
  no proofs.
* [`Readings.lean`](Readings.lean) — the nine definitions read at `V = ℕ`, one named theorem each (`box_nat`: `□[k] ⌜σ⌝`
  holds iff some meta derivation of `σ` has symbol count `≤ k`; `guard_nat`; `TAct_sound_nat`; …), each proved from
  the lemma that already carries the fact, so the reading cannot drift from the definition.
* [`Notation.lean`](Notation.lean) — the paper's symbols in Lean: `□[k] φ` is `LenBox TAct k φ` (the paper's
  `□_k φ`, and at a meta budget on a quoted sentence its `⊢_k φ`); the three-layer table is in its docstring.

Every trusted-base file now opens with a **Reading guide** line naming its definition and marking the
Foundation plumbing (Σ₁ mirrors, `defined` instances, fixpoint blueprints) to skip on first reading; the
two files whose definition used to sit under two hundred lines of plumbing are split (`Eval/Fixpoint.lean`
behind `Eval/Eval.lean`, `Agents/SubstTemplate.lean` before `Agents/Subst.lean`).

## 1. The four tiers

| tier | folders | lines | what to do with it | lake target |
|---|---|---:|---|---|
| **Trusted base** — the definitions a reader accepts by eye | `Theory/`, `Length/`, `Box/`, `Agents/`, `Eval/` | ~13k, of which the definitions themselves are a few hundred | read §2 in order; skim the lemmas around them | `ArithSCore` (root `Core.lean`) |
| **Results** — the theorems | `Outcome/` (the matrix in the engine's vocabulary), `Cells/` (the proofs), `Assembly/` + `Loeb/` (PBLT), `Necessitation/Package.lean` (bounded inner necessitation, statements only) | ~19k | read `Outcome/`, then §3's reading order | `ArithSMatrix` (`Matrix.lean`); PBLT: `ArithSLoeb` (`PBLT.lean`) |
| **Construction of U10** — the proof that PA verifies its own proofs within a polynomial budget | everything in `Necessitation/` except `Package.lean` | ~96k (72 %) | do not open; the design notes are `Research/Notes/M4_BOUNDED_HBL/` | pulled in by `ArithSLoeb` |
| **Frozen, estimates, census** | `Bridge/` (the T2 bridge, frozen by decision), `Length/Proper`, `Box/ProperBound`, `Agents/Fit*` (numeric estimates), `Audit/` (every `#print axioms` the build runs) | ~6k | skip; `Audit/` is what `lake build` checks, not what you read | `ArithSFrozen` (`Frozen.lean`), `ArithSAudit` |

Import direction between the tiers (core < frozen < Löb < results < audit; the results tier reaches the U10
construction only through `Necessitation/Package` and `ClosedNec`) is checked by `scripts/check_tiers.py`, which
also verifies that each root imports exactly its tier — Lake cannot enforce this between libraries of one
package. `Agents/Instance*` and `Eval/Transparency` belong to the Löb tier (they describe Dupoc's guard as a
`k`-instance for the family assembly), `Agents/Fit*` and `Eval/Det` to the frozen/estimates tier, and
`Cells/RedCell` to the core (its proof needs nothing else).

Generated files (`Necessitation/*Rows.lean`, `RowInst*.lean`, `Lib/Frag.lean`) carry a `GENERATED` marker;
never edit them (`scripts/README.md`).

## 2. The trusted base, in reading order

Nine definitions. Everything else in the package is a theorem about them or a construction. Each entry
says what a reader accepts and the one design choice behind it.

The other files in these five folders hold no definitions to accept, only theorems about these nine
(`Theory/Transpose`, `Sound`, `Symmetry` = the τ-closure chain ending in `lenBoxNat_swap_iff`;
`Length/Proper`, `Box/ProperBound` = the properness estimates; `Box/Cut*` = bounded modus ponens; `Agents/Fit*`
= the guard fits its budget): read their statements, let Lean keep their proofs.

1. **The language** — `LAct := ℒₒᵣ + {c_C, c_D}` and the transposition `swap` (a language hom that
   exchanges the two constants): [`Theory/LangAct.lean`](Theory/LangAct.lean). Actions are constants,
   not numerals, so that τ is a symmetry of the syntax.
2. **The theory** — `TAct := PA ∪ {c_C ≠ c_D, c_D ≠ c_C, actionAxiom, actionAxiom'}`, the action axiom in BOTH
   orders so the theory is literally closed under `swap`: [`Theory/TheoryAct.lean`](Theory/TheoryAct.lean).
   Its two standard readings `stdReading`/`swappedReading`; ℕ is a model (`models_TAct`, the soundness every negative cell rests on).
3. **The length** — `proofLen`, the structural symbol count of a derivation code (symbol-blind, so τ
   preserves it exactly; weakening and ∃-witnesses charged): [`Length/DerivationLength.lean`](Length/DerivationLength.lean),
   with `proofLen ⌜d⌝ = proofLenMeta d` in [`Length/MetaLength.lean`](Length/MetaLength.lean). The cost is a tree
   shape, never a Gödel number's magnitude.
4. **The box** — `□[k] φ := ∃ d < codeBound k, Proof TAct d φ ∧ proofLen d ≤ k` (`LenBox`, Δ₁; the code
   bound is a margin that properness makes harmless): [`Box/BewV.lean`](Box/BewV.lean); the Σ₁ form
   `LenBoxUnbounded` and their equality in every model, [`Box/CutV.lean`](Box/CutV.lean), [`Box/ProperBound.lean`](Box/ProperBound.lean).
5. **Program codes** — `pConst/pSelf/pOpp/pBot/pSim/pIte/pSearch` and, since 2026-09-30 (Phase 2 of
   `SPRIME_SOURCE_OF_TRUTH.md`), the tau constructors `pTvote/pSys/pSelfIdx` with the tagged list cons `pCons`
   (`pNil = 0`), on the polynomial pairing `ppair`: [`Agents/Prog.lean`](Agents/Prog.lean). `transposeCode` is τ on
   codes (vote entries frozen, system members re-valued, as in the engine's `Base/Transpose`).
6. **Descriptions** — a program named inside a sentence by binary numeral TERMS (`codeTerm`, `canonical`,
   `revalueU`, `revalueW`): [`Agents/CodeTerm.lean`](Agents/CodeTerm.lean), [`Agents/BinNumeral.lean`](Agents/BinNumeral.lean).
7. **The guard template and the runtime guard** — `guardTemplate a` ("opp plays `a` against me", six
   description slots) and the general translation of the engine's guard formulas: the THIRTEEN-variable
   `template13 : PD.Formula → Semisentence LAct 13` that `pSearch` stores (`templateCode φ := ⌜template13 φ⌝`;
   frame `#0..#5`, budget slot `#6`, the two member triples `#7..#12`), whose `progAux13` reads a system member's
   pronoun `.selfIdx j` (`j ∈ {0, 1}`) from member `j`'s triple and `.bot (.selfIdx j)` as that triple with the
   term `pBotTerm` on its code (`pBot` commutes with `revalue` and `canonical`), and the six-variable `template`
   beside it, the reading every `Cells/` file uses — the two agree on every formula without a dangling pronoun
   (`noSelfIdxF`; the bridge `templateCode_eq_quote_template : templateCode φ = ⌜template φ⌝`, since
   2026-10-01); `guardCode g me opp` fills the slots at run time, `guardCodeB` adds the seventh slot holding the
   node's own budget (route (c)): [`Agents/Template.lean`](Agents/Template.lean),
   [`Agents/Code.lean`](Agents/Code.lean), [`Agents/Guard.lean`](Agents/Guard.lean).
8. **Substitution** — `substCode`, the engine's one-shot `Prog.subst` on codes (`.bot` frozen, guards read
   the outer players, vote entries frozen, a system a binder): [`Agents/Subst.lean`](Agents/Subst.lean) (the
   equations `substCode_*` are the definition), on top of `substTemplate`, the instantiation of a stored
   template by the outer frame: [`Agents/SubstTemplate.lean`](Agents/SubstTemplate.lean); agreement with the
   engine `progCode_subst` in `Agents/Code.lean`. **The system closer** — `sysCloseCode d`, the engine's
   `Prog.sysClose` (`pSelfIdx j ↦ pSys d j`, transparent through `pBot`, an inner `pSys` a binder), and the
   member lookup `listGet` (`ProgList.get?`, `m + 1` for `some m`): [`Agents/SysClose.lean`](Agents/SysClose.lean);
   the stored template is closed by `sysCloseTemplate d` (`Agents/Guard.lean`: the member slots `#7..#12`), which
   is the identity on every six/seven-variable template (`sysCloseTemplate_of_template₇`) and, on a compiled
   member's guard, IS the engine's `Formula.sysClose` — `templateCode_sysClose : sysCloseTemplate (progListCode
   defs) (templateCode φ) = templateCode (φ.sysClose defs)`, so `progCode (p.sysClose defs) = sysCloseCode …
   (progCode p)` on every compiled member (`progCode_sysClose_member`): [`Agents/SysTemplate.lean`](Agents/SysTemplate.lean).
9. **The evaluator** — `EvalGraph n me opp p a`, a Σ₁ fixpoint mirroring the engine's `eval` clause
   by clause (the `.tvote` peel, the `.sys` unfold and the search clause consulting the box included):
   [`Eval/Eval.lean`](Eval/Eval.lean) (the characterization `EvalGraph.case_iff` is the definition; the
   fixpoint construction is [`Eval/Fixpoint.lean`](Eval/Fixpoint.lean), skip); on ℕ it is deterministic and
   fuel-monotone, [`Eval/EvalN.lean`](Eval/EvalN.lean); it runs in lockstep with the engine's `eval` on the
   tau-search-free fragment, [`Eval/TauCheck.lean`](Eval/TauCheck.lean) (the Phase-2 gates).

The bridge from the engine is `progCode : PD.Prog → ℕ` and `templateCode : PD.Formula → ℕ` in `Agents/Code.lean`.

## 3. The results, and a reading order

`Outcome/` is the layer to open first. [`Outcome/Spec.lean`](Outcome/Spec.lean) defines the engine's
vocabulary on codes — `plays`, `OutcomeSpecA regime L R (some (a, b))` with the engine's own
`BudgetRegime`, `bot P`/`const P` for the engine's bots, the notation `□[k] φ` — and
`Outcome/Matrix/<L>.lean` states every cell of the ledger with `<L>` on the left in that form, one line
each, proved from the method-named theorem in `Cells/` that carries the mathematics:

```lean
theorem outcome_DupocBot_vs_CupodBot :
    OutcomeSpecA .universal (bot DupocBot) (bot CupodBot) (some (.D, .C))
```

Then, in order:

1. **The red cell** — [`Cells/RedCellEngine.lean`](Cells/RedCellEngine.lean) (the engine's bots, 60
   lines) or [`Cells/RedCell.lean`](Cells/RedCell.lean) (the hand-written `Dupoc k`/`Cupod k`, self-contained): τ-symmetry
   of the two guards + soundness in ℕ + determinism, no Löb, every `k`. The one cell to understand fully.
2. **A soundness cell** — `Cells/SoundnessCells.lean`, `snd_else_of_false` and one `snd_*` cell: a
   guard false in ℕ is never found, so the searcher takes its else branch.
3. **PBLT** — `Assembly/Family.lean` (`LoebSound`, `family_found`, the family-parametric bounded Löb
   theorem) and `Necessitation/Package.lean` (`boundedInnerNec_sixteen`, `pblt`,
   `dupoc_self_coop`): read the STATEMENTS.
4. **One Löb cell** — `Cells/DupocEngine.lean` (Dupoc × Dupoc on the engine's code, the two-guard family `pQ`; 300 lines) or `Cells/CIMCIC.lean`.
5. **The flips** — `Cells/FlipCells.lean`, `Cells/DimcidFlips.lean`: where PA-`S'` contradicts the
   engine, and why (`dimcid_vs_closed`: DIMCID defects against every closed program).
6. **The floors** — `Cells/FloorDichotomy.lean`: the 26 genuine floors as hypothesis-free dichotomies
   on the hinge `□[k] (the outer guard)`; `hinge_reduces_to_bounded_consistency_DupocBot_vs_DBot`.

## 4. Dictionary: engine ↔ `ArithS`

| engine (`PD`) | `ArithS` | note |
|---|---|---|
| `Prog` (syntax tree) | `ℕ` (a code); `progCode p` | `bot P k = progCode (P k)`, `const P = progCode P` |
| `Action` `.C`/`.D` | `actCode .C = 0`, `actCode .D = 1` | the older cell theorems write the literals |
| `Formula` (guard) | `template φ : Semisentence LAct 6`, code `templateCode φ` | `guardTemplate a` is the hand-written template of `.plays .opp .self a` |
| `eval n me opp p` | `EvalGraph n me opp p a` | a graph, not a function: it is a Σ₁ fixpoint |
| `play`, `outcome` | `plays me opp a`, `OutcomeAtA L R r` | `Outcome/Spec.lean` |
| `OutcomeSpec regime pad L R r` | `OutcomeSpecA regime L R r` | same `BudgetRegime`; fuel is `∃ n` here |
| `Pf k φ` (`⊢_k φ`) | `LenBox TAct k ⌜φ⌝` (`□[k] φ`) | PA with a length bound, not a rule set |
| `Pf.transpose` (47 arms) | `transpose_exists` (`Theory/Transpose.lean`) | free: a language hom |
| `sound_upto` | `models_TAct` + the truth equations | soundness in ℕ |
| `bloeb_engine`/`pblt_engine` | `family_found`/`pblt` | Löb needs U10 |
| `outcome_<L>_vs_<R>` | `outcome_<L>_vs_<R>` in `Outcome/Matrix/` | proved from `snd_/pos_/loeb_/khat_/sf_<L>_vs_<R>` |
| `DupocBot k` | `progCode (DupocBot k)`; the hand twin `Dupoc k` | see the twins below |

**The paper's symbols** (`Notation.lean`; the engine column is the engine's own notation):

| paper | engine | `ArithS` |
|---|---|---|
| `□_k φ` (a program mentions provability) | `Formula.box k φ` | the sentence `□[k] φ` = `LenBox TAct k φ`, Δ₁ |
| `⊢_k φ` (`φ` is derivable at budget `k`) | `Pf k φ` | the same sentence read in ℕ: `□[k] ⌜φ⌝` |
| `⊨ φ` (`φ` holds) | `φ.interp` | `ℕ ⊧ₘ φ` (Foundation) |
| `|d|` (transcript length) | cumulative rule costs | `proofLen TAct d` (the symbol count of the code `d`) |
| `⌜p⌝` (a program named in a sentence) | `Prog` is the syntax | `codeTerm (canonical p)`, a binary-numeral term |
| `outcome (A, B) = (a, b)` | `OutcomeSpec regime pad A B (some (a, b))` | `OutcomeSpecA regime (bot A) (bot B) (some (a, b))` |

**Theorem heads in `Cells/`** name the PROOF METHOD: `sf_` search-free transfer, `pa_` PA proves the
atom, `snd_` soundness/else branch, `pos_` guard found without Löb, `loeb_` bounded Löb, `khat_` the
`k̂`-chain, `floor_` a settled floor half, `dich_` a floor dichotomy. The cell name is the `outcome_` one.

**The hand-template twins.** Seven cells are stated on codes that are NOT the engine's `progCode`:
`Just k`/`Just7 k` (`Cells/JustBot.lean`, `Cells/JustSlot.lean`) and `CupodTroll7 k` (`Cells/KhatCells.lean`),
in `outcome_Just_vs_MirrorBot`, `outcome_Just7_vs_Dupoc`, `outcome_Just7_vs_Just7`, `outcome_DIMCID_vs_Just7`,
`outcome_DIMCID_vs_CupodTroll7`, `outcome_CIMCIC_vs_Just7`, `outcome_CupodTroll7_vs_CupodBot`. These are NOT
retirable by re-proving: the engine's `JustBot k`/`CupodTrollBot k` freeze a BUDGET-CARRYING snapshot in their
guard, so `progCode (JustBot k)` is the `binNumeral k`-instance of no fixed term and the family assembly cannot
DESCRIBE it as an opponent (`ROUTE_B_SCOPE.md` §7); the seven-variable twins with a budget slot are the only
describable form, and they play like the hand-written snapshot (`evalGraph_JustV7_iff`), which is itself
`pBot (DupocV k)`, not `.bot (DupocBot k)`. Their `outcome_` theorems keep the twin's name so that a name never
claims more than its statement. The former Dupoc/Cupod twins are RETIRED: `Cells/DupocEngine.lean`,
`Cells/CimcicEngine.lean`, `Cells/DimcidEngine.lean` re-prove Dupoc × Dupoc, Cupod × Cupod, Dupoc/Cupod × Mirror,
CIMCIC × Dupoc and DIMCID × Cupod on `progCode (DupocBot k)`/`progCode (CupodBot k)` (= the generic searcher
`SV gDu 0`/`SV gCu 1` of `Cells/Common/Bots.lean` §4, the guard `qT gDu …`, the family `pQ`), and the cells are
`outcome_DupocBot_vs_DupocBot`, `outcome_CupodBot_vs_CupodBot`, `outcome_DupocBot_vs_MirrorBot`,
`outcome_CupodBot_vs_MirrorBot`, `outcome_CIMCIC_vs_DupocBot`, `outcome_DIMCID_vs_CupodBot`. The hand-written
`Dupoc k`/`Cupod k` stay as the self-contained red cell (`Cells/RedCell.lean`) and the hand-twin Löb theorems
stay beside the engine ones (`Cells/DupocMirror.lean`, `dupoc_self_coop`). `Cimcic`, `Dimcid`, `Prudent`,
`Mirror` ARE the engine's codes (`progCode_CIMCIC`, `progCode_DIMCID`, `progCode_PrudentBot`,
`progCode_MirrorBot`).

## 5. Folder map

One line per file; the module docstring has the rest.

**`Theory/`** — `LangAct` the language and τ · `TheoryAct` the theory, its two readings, completeness over
them · `Transpose` derivations transport along language homs, τ preserves length · `Symmetry` τ-closure
on proof codes at every length · `Sound` internal derivation codes come from meta derivations.

**`Length/`** — `Length` term/formula symbol counts · `SequentLength` sequents (bit-sets) · `DerivationLength`
`proofLen` · `MetaLength` `proofLen ⌜d⌝ = proofLenMeta d` · `Proper` a derivation of length `k` has code below a tower
(estimate) · `ProofLength` a proof is at least as long as its conclusion.

**`Box/`** — `Bew` `□_k` at ℕ · `BewV` the budget as a variable (`LenBox`) · `Cut`/`CutV` bounded
modus ponens with exact length accounting · `ProperBound` properness inside every model.

**`Agents/`** — `Prog` codes · `CodeTerm` descriptions as terms · `BinNumeral` binary numerals · `RevalueTemplate`
τ on template codes · `Template` the guard template · `Guard` the runtime guard, the budget slot ·
`SubstTemplate` instantiating a stored template by the outer frame · `Subst` `substCode` · `Code` `progCode`/`templateCode`/`template`, the engine bridge · `Instance`/`InstanceV`
Dupoc's guard as the `k`-instance of one formula (for Löb) · `Fit`/`FitBox` the guard fits its budget;
`box_guard_never_fits` (why LegibleBot is out).

**`Eval/`** — `Fixpoint` the fixpoint construction (plumbing) · `Eval` `EvalGraph` · `EvalN` inversion, determinism, monotonicity at ℕ · `SimTest` smoke
tests · `Transparency` Dupoc's truth equation in every model · `Det` PA-internal determinism (frozen T2).

**`Loeb/`** — `Diag` the parametric diagonal lemma · `InstV` the instance operator and the parametric
box · `NumeralFacts` short proofs of numeral inequalities.

**`Assembly/`** — `Prep` lemmas the assembly needs · `Family` the family-parametric PBLT · `Cell` the
Löbian cell at ℕ · `Uniform` the earlier uniform chain.

**`Necessitation/`** — U10: `Package` (READ: the statements) · everything else is the construction:
`Chain`/`Steps`/`Describe`/`Layout`/`Prologue`/`Cert`/`Verify*`/`Top`/`Assemble`/`Pin`/`ClosedNec` and the
row tables · `Lib/` the library of PA-provable schemas the steps cite.

**`Cells/`** — the proofs. The header rule: UNIFORM methods are filed by method, LÖB cells by bot (each needs its own
description layer and family); the rule and the file list are in `Matrix.lean`'s docstring. By method: `RedCell`, `RedCellEngine`, `SearchFree`, `SoundnessCells`,
`PositiveCells`, `KhatCells`, `DupocMirror`, `CIMCIC`, `DIMCID`, `JustBot`, `JustSlot`, `PrudentMirror`,
`PrudentLoose`, `FlipCells`, `DimcidFlips`, `FloorVerdicts`, `FloorDichotomy`, `SimSlot`; `Common/` the
shared bot codes, templates, probers, families, the `k̂`-chain; `Names` the deprecated old names.

**`Outcome/`** — `Spec` the vocabulary · `Matrix/<L>` the cells (`@[outcomeA]`) · `Floor` the floor template
`FloorSpecA` · `Floors` the 26 engine-side floor halves (`@[floorA]`) · `Attr` the two tag attributes · `Lint` the
validator, the censuses and the coverage command · `Check` the lake root that runs them · `Export` the JSON exporter.

**Top level** — `Notation` the paper's symbols · `Tour` the guided tour.

**`Bridge/`** — the frozen T2 bridge `S → S'` (`Core/`, `Agent`, `AgentConverse`, `Inst`, `Neg`,
`EngineBridge`): shown impossible at polynomial budgets (`MERGE_CROSSROAD.md`); route B re-proves
cells directly instead.

**`Audit/`** — one census file per layer plus the three red-cell audit files; `Audit.lean` imports them.

## 6. Build and check

```
cd arith && lake build ArithS --try-cache      # ~3350 jobs; never compile Foundation or mathlib
timeout 900 lake env lean ArithS/<file>.lean   # single-file check; CHECK THE EXIT CODE
timeout 900 lake env lean ArithS/Tour.lean     # prints every headline statement and its axioms
lake build ArithSCore                          # one tier (also ArithSFrozen, ArithSLoeb, ArithSMatrix, ArithSAudit)
python3 scripts/check_tiers.py                 # import direction between the tiers, roots complete
scripts/regen_all.sh                           # the generated tables are in sync
lake build ArithSOutcomeCheck --try-cache      # the S' matrix gate (also in the default build), see below
lake exe export_sprime_outcomes                # writes ../app/generated/sprime_outcome_theorems.json
```

**The export discipline** (`Outcome/{Attr,Floor,Floors,Lint,Check,Export}.lean`, the twin of the engine's
`Outcome/{Attr,Lint,Check,Export}.lean`; design: `Research/Notes/SPRIME_SOURCE_OF_TRUTH.md` §1). Every cell of
`Outcome/Matrix/<L>.lean` carries `@[outcomeA]`; every genuine floor has its engine-side half
`@[floorA] theorem outcome_<L>_vs_<R>_floor : FloorSpecA (bot L) (bot R) (fun k ↦ <hinge>) (some (a, b))` in
`Outcome/Floors.lean`, proved from `dich_<L>_vs_<R>` (`Cells/FloorDichotomy.lean`; where `Cells/PrudentLoose.lean`
has the prudence hinge discharged or the partner's side built, that sharper dichotomy). The hinge is inline, in the
`□[k] φ` notation, `¬ hinge k` being exactly the branch the dichotomy settles at the engine's value. `lake build`
runs, through the root `Outcome/Check.lean`:

* `#check_outcomeA_theorems "ArithS/Outcome/Matrix"` — every tagged cell is an `OutcomeSpecA` with a literal
  regime and result whose bots agree with its name (the head is matched SYNTACTICALLY); every cell-shaped
  `theorem outcome_<L>_vs_<R>` under the directory is tagged; one cell per ordered pair;
* `#check_floorA_theorems "ArithS/Cells/FloorDichotomy.lean"` — every tagged floor is a `FloorSpecA` named
  `…_floor` with an existing `dich_<L>_vs_<R>`; every `dich_<L>_vs_<R>` in the file has a floor; no floor shadows a cell;
* `#check_sprime_coverage` — every unordered pair of the 12 paper base bots is a cell or a floor (the hand-template
  twins `Just7`/`CupodTroll7`/… count for their base bot here and nowhere else).

`lake exe export_sprime_outcomes [out.json]` writes the engine's JSON schema plus `"system": "sprime"`, a
`provenance` per row (`sprime` / `floor_dichotomy`) and a `floors` array (`hinge`, `dichotomy`); `fuel_pad` is `0`
everywhere (fuel is existential). `source_digest` is the engine's FNV-1a over the compressed rows of
`theorems ++ companions ++ floors`, each sorted by name; recompute it in Python with
`json.dumps(row, sort_keys=True, separators=(",", ":"), ensure_ascii=False)` — the hinge text is Unicode.

The census is every `#print axioms` the build runs (`Audit/`): all `[propext, Classical.choice,
Quot.sound]` but four pre-existing subsets. Traps: `Research/Notes/ARITH_TRAPS.md`. Dead-code audit and
pruning: `Research/Notes/ARITH_DEAD_CODE_AUDIT.md`, `scripts/DeadCode.lean`.

## 7. What is deliberately not here

* **LegibleBot, OptimBot, WaryBot's floor cells** (22 cells): a box INSIDE a guard needs a third instance of
  the U10 kit for a body computed from the frame (`ROUTE_B_SCOPE.md` §9).
* **The 26 genuine floors** take no side: each is a dichotomy on a hinge that is bounded consistency of
  `TAct` at `k` up to a constant — Pudlák's linear-regime question. Never admit the hinge as an axiom.
* **The outcomes of the entangled tau pairs** (Phase 3). The pronoun reading of `.selfIdx` — the last item of
  Phase 2 — LANDED on 2026-10-01: a system member's guard is described through the member slots `#7..#12` of the
  thirteen-variable `template13`, `sysCloseTemplate` on it is the engine's `Formula.sysClose`
  (`templateCode_sysClose`), and the closed member of `cfdSys k` is the code of the engine's closed member, whose
  search consults "`.bot (.sys (cfdSys k) (1 - i))` plays C against itself" (`Eval/TauCheck.lean`,
  `Cells/TauMember.lean`). What is NOT here is the mutual-Löb family on the member slots that decides those
  searches — the entangled `.sys` bits of the Phase 3 table.
