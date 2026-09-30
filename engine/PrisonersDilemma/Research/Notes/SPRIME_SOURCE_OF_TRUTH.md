# SPRIME_SOURCE_OF_TRUTH — PA-`S'` cells as the app's ground truth, and the tau layer in `S'`

*Decided 2026-09-30. Six phases; this note is the contract every phase codes against. Companion
ledgers: `ROUTE_B_CENSUS.md` (which cell is what in `S'`), `TAUBOTS.md` (the tau layer in the engine).*

## 0. The decisions

1. **`S'` is the source of truth** for the app, the matrices, the tau layer and the EGT experiments.
   The engine's `S` matrix stays loadable as the COMPARISON (`CellSource = engine`), never as the default.
2. **Floors are dichotomies, never stipulations.** Inside the 12 base bots of the paper zoos the `S'` ledger
   has 78 unordered pairs: 56 theorems that agree with the engine, 9 FLIPS (all DIMCID's — in `S'` DIMCID
   defects against every closed program), 13 GENUINE-FLOOR pairs (14 floor rows: Cupod × Prudent has a
   dichotomy in each orientation). Body zoo: 55 pairs = 44 / 7 / 4; critch8: 36 = 33 / 0 / 3. The report:
   `python -m pd_runner.eval.source_diff` → `app/generated/source_diff.md`. A floor is a hypothesis-free `dich_<L>_vs_<R>`
   (`Cells/FloorDichotomy.lean`): `¬A_k →` the engine's value, `A_k →` the other value, with the hinge
   `A_k = LenBox TAct k (outer guard)` — bounded consistency of `TAct` at `k` up to an additive constant
   (Pudlák's linear-regime question, open both ways). Nothing will "prove" a floor; the app carries it as a
   cell with **provenance `floor_dichotomy`** and an explicit **`FloorPolicy`**:
   * `engine_side` (default): the cell takes the `¬A_k` value — the engine's stipulation, now labelled;
   * `restrict_zoo`: floors are holes; a zoo containing one fails totality loudly.
   Never a stipulation that shadows a theorem (the existing loader guard stays).
3. **DIMCID stays in the body zoo** with its `S'` row. Consequence to own in the paper: it is now a behavioral
   twin of DefectBot, so the body zoo's "twin-free, behavioral σ-scale spans [0, 1]" property is gone; the
   confusion-structure comparison must be re-read with that in mind.
4. **"All paper-zoo cells proved" means:** every unordered pair of the 12 base bots is an `@[outcomeA]`
   theorem or an `@[floorA]` dichotomy in `S'` — checked by a build-time census (`#check_sprime_coverage`).

## 1. Phase 1 — the export discipline (arith) and the source switch (app)

### 1.1 Lean (`arith/ArithS/Outcome/`)

Mirror of the engine's `Outcome/{Attr,Lint,Check,Export}.lean`, same design, same traps (tag attribute via
`registerTagAttribute`; read imported tags with `getModuleEntries`; match the `OutcomeSpecA` head
SYNTACTICALLY, never `whnf` through it):

* `Attr.lean` — `@[outcomeA]` (a cell) and `@[floorA]` (a floor dichotomy's engine-side half).
* `Floor.lean` — the floor template, the engine-side HALF of a dichotomy:
  ```lean
  def FloorSpecA (L R : ℕ → ℕ) (hinge : ℕ → Prop) (r : Option PD.Outcome) : Prop :=
    ∃ k₀, ∀ k, k₀ < k → ¬ hinge k → OutcomeAtA (L k) (R k) r
  ```
  `hinge k` is written INLINE with the `□[k] φ` notation; for the nested cells it is the boolean combination
  of the outer hinges under which the engine's value is forced (read the `dich_` statement: the engine's
  value is the branch the ledger column "engine" names). One theorem per floor,
  `@[floorA] theorem outcome_<L>_vs_<R>_floor : FloorSpecA (bot L) (bot R) (fun k ↦ …) (some (a, b))`,
  proved from `dich_<L>_vs_<R>` in `Outcome/Floors.lean`. The full dichotomy stays where it is.
* `Lint.lean` — `inspectCellA` (head `ArithS.OutcomeSpecA`, 4 args; `L`/`R` are `ArithS.bot X`,
  `ArithS.const X` or a lambda over `progCode`; name `outcome_<L>_vs_<R>` must agree with the statement;
  no Prop binders), `inspectFloorA` (head `ArithS.FloorSpecA`, suffix `_floor`, hinge pretty-printed), and
  three commands: `#check_outcomeA_theorems` (validator + census over `Outcome/Matrix/`),
  `#check_floorA_theorems` (every `dich_<L>_vs_<R>` in `Cells/FloorDichotomy.lean` has a tagged floor),
  `#check_sprime_coverage` (every unordered pair of the 12 paper base bots — `CIMCIC CooperateBot CupodBot
  CupodTrollBot DBot DIMCID DefectBot DupocBot EBot OBot PrudentBot TitForTatBot` — is a cell or a floor).
* `Check.lean` — the three commands; lake lib `ArithSOutcomeCheck`, in `defaultTargets`.
* `Export.lean` — `lake exe export_sprime_outcomes [out.json]`, default
  `../app/generated/sprime_outcome_theorems.json`, importing `ArithS.Outcome.Check`.
* Every `Outcome/Matrix/<L>.lean` theorem gets `@[outcomeA]`; `Audit/Outcome.lean` prints the floors' axioms.

### 1.2 The JSON (`app/generated/sprime_outcome_theorems.json`)

The engine's schema, so the Python loader is shared, plus `system`, `provenance` and a `floors` array:
```json
{ "schema_version": 1, "system": "sprime", "source_digest": "<fnv1a64 over theorems+companions+floors rows, engine algorithm>",
  "theorems":   [ { "name", "module", "file", "left_bot", "right_bot", "budget_regime", "fuel_pad": 0,
                    "pair": ["C","D"] | null, "staggered": false, "left", "right", "provenance": "sprime" } ],
  "companions": [],
  "floors":     [ { …same fields…, "provenance": "floor_dichotomy", "pair": <engine-side value>,
                    "hinge": "<pretty text>", "dichotomy": "dich_<L>_vs_<R>" } ] }
```
`fuel_pad` is 0 for every `S'` row (fuel is existential in `OutcomeSpecA`). `budget_regime` is the
`BudgetRegime` literal; floors are always `eventual`.

### 1.3 Python (`app/src/pd_runner/`)

* `settings.py`: `CELL_SOURCE = PD_CELL_SOURCE ∈ {sprime, engine}` (default `sprime`);
  `FLOOR_POLICY = PD_FLOOR_POLICY ∈ {engine_side, restrict_zoo}` (default `engine_side`).
* `eval/outcome_matrix.py`: `CellSource`; one export file per source; `OutcomeTheorem.provenance ∈
  {engine, sprime, floor_dichotomy}` + `hinge`; `scan_outcome_theorems(source=None, floor_policy=None)`
  (floors join the cell list under `engine_side`, are dropped under `restrict_zoo`);
  `build_outcome_matrix(source=…)` with two new legend marks — floor, and "flips the engine";
  `export_staleness`/`refresh_export` per source (`arith/` + `lake exe export_sprime_outcomes`);
  `diff_sources()` → the engine-vs-`S'` report (`python -m pd_runner.eval.source_diff`, writes
  `generated/source_diff.md`: per zoo, agreeing / flipped / floor / missing).
* `tau/matrix.py`: `load_tau_matrix(…, source=None, floor_policy=None)`; `Cell.provenance`;
  `TauMatrix.source`, `.floor_cells`; kernel tau rows are loaded ONLY for `source == engine` until Phase 4
  ships `sprime_tau_rows.json` (`is_kernel_backed` is False on `sprime`, documented, never silently wrong:
  the engine's rows DISAGREE with `S'` at the DIMCID cells and the verifier would raise); `NamedZoo.load(source)`.
* `egt/ingest.py` / `pipeline.py`: `cell_source` + `floor_cells` in every `PayoffMatrix`/`assumptions.json`;
  the run-directory hash covers the source so engine and `S'` runs never share a directory.
* `tau/sweep.py`, `tau/compare.py`, `api/main.py` (`?source=`), `services/sheets.py` (worksheet
  `Auto Matrix (S')` for `sprime`, the old tab for `engine`), the matrix card in `api/static/index.html`.
* Tests (`tests/test_cell_source.py`): engine parity (matrix rows byte-identical to the pre-switch output);
  `S'` totality of all three paper zoos + critch8 under `engine_side`; `restrict_zoo` fails body on exactly
  its 4 floors; `diff_sources` finds exactly 9 flips and 13 floor pairs inside the 12 paper base bots.
  **Landed 2026-09-30**: 647 tests green; the S' export is the default source everywhere; twin names
  (`Just7`, `Just`, `Dupoc`, `Cupod`, `CupodTroll7`) are aliased to their base bots on the `sprime` source only.

## 2. Phase 2 — the tau constructors in the trusted base (specification, 2026-09-30)

### 2.1 What the engine's compiler actually emits (read `Tau/Spec.lean` before believing anything else)

* `inst Z A T` is a PLAIN `Prog` (`const/sim/ite/search/bot`) unless the pair is **entangled** —
  `A ≠ T` and both specs self-probe (`Spec.selfProbes`: `sim .self` or `search _ .self`). Then it is
  `.sys [sysGo 1 A T, sysGo 0 T A] 0`, each member probing the other through `.bot (.selfIdx j)`.
  Self-probers in the roster: `dupoc cupod cimcic dimcid prudent mirror maxconfidence minconfidence`.
  In the 14 paper templates (`coop defect tftSim dupoc ebot obot dbot cupodTroll cupod dimcid` + twins
  `cimcic prudent` + natives `maxconfidence minconfidence`) that is 7 self-probers ⇒ 42 ordered entangled
  cells, plus the cells where a NAMED target is itself entangled with the hypothesis (τ(EBot) names
  `.mirror`: `instAt T mirror` is a system for every self-probing `T` — 7 more). ≈ 49 of 196 paper bits
  carry a `.sys`; the other ≈ 147 are programs that already have `progCode`s today.
* `.tvote` never occurs inside an instance. It is the PLAYER (`tauPlayer`, `maxPlayer`), i.e. the
  phase theorems, not the rows. The rows (`RowSpec`, what the app reads) need only `.sys`/`.selfIdx`.
* Templates are constants per system: a member's guard mentions `.bot (.selfIdx j)`, never `k`
  directly; the budget enters only as the `.search k` leaf — so a system's description IS a fixed
  term in `binNumeral k` (the property the Löb families need).

### 2.2 The codes (`Agents/Prog.lean`)

Three new tagged shapes on the polynomial pairing, tags 7, 8, 9 (the existing 0–6 unchanged):
`pTvote v θ p q = ppair 7 (ppair v (ppair θ (ppair p q))) + 1`, `pSys d i = ppair 8 (ppair d i) + 1`,
`pSelfIdx j = ppair 9 j + 1`, with list codes `pNil = 0`, `pCons x rest = ppair x rest + 1` for both
`ProgList` and `VoteList` (an entry is `pCons (ppair w I) rest`). Each gets its Σ₀ graph, size facts
(components strictly below), injectivity/disjointness, an `IsShape` disjunct, and a `Revalue.Phi`
clause (τ on codes): `pSelfIdx` fixed, `pSys` re-values every member (through a list fixpoint or by
keeping the member-list clause inside the same fixpoint on pairs `⟪x, y⟫`), `pTvote` re-values the
branches and FREEZES the entries (the engine's τ̂ freezes `VoteList`, `Base/Transpose`).

### 2.3 Substitution, and the system closer (`Agents/Subst.lean`, new `Agents/SysClose.lean`)

`substCode`: `pTvote v θ p q ↦ pTvote v θ p' q'` (entries frozen), `pSys d i ↦ pSys d i` (binder),
`pSelfIdx j ↦ pSelfIdx j` — three trivial clauses. `sysCloseCode d : V → V` is a SECOND Δ₁ fixpoint,
the engine's `Prog.sysClose defs`: `pSelfIdx j ↦ pSys d j`, transparent through `pBot`, `pSim`,
`pIte`, the branches of `pSearch` and `pTvote` (entries frozen), an inner `pSys` a barrier, and on a
`pSearch k g p q` the stored template is closed by `sysCloseTemplate d g` (§2.5).

### 2.4 The evaluator (`Eval/Fixpoint.lean`, `Eval/Eval.lean`, `EvalN`, `Det`)

Four clauses added to `EvalFix.Phi`, mirroring `Dynamics.eval` literally:
* `pTvote pNil θ p q`: `θ = 0 → p` else `q`;
* `pTvote (pCons (ppair w I) rest) θ p q`: `θ = 0 → p`; else the entry runs in ITS OWN frame,
  `⟪n, pBot I, pBot I, I, r⟫ ∈ C`, and `r = 0 → pTvote rest (θ ∸ w) p q`, `r = 1 → pTvote rest θ p q`
  (truncated subtraction is `V`'s `∸`);
* `pSys d i`: `∃ m, listGet d i = some m ∧ ⟪n, me, opp, sysCloseCode d m, a⟫ ∈ C` (`listGet` Σ₀);
* `pSelfIdx j`: no clause (a dangling reference plays nothing — the engine's `none`).
Then: the blueprint's Σ/Π twins, `phi_iff`, monotonicity, `Finite`, the four `EvalGraph.*_iff`
inversion lemmas, and new arms in `EvalGraph.unique`/`mono` (ℕ) and `unique_V'` (`Det`). Blast
radius outside `Agents/`+`Eval/`: ONE file case-splits on the seven shapes,
`Audit/RedCellUnsound.lean:470` (add the arms); `FloorDichotomy`/`SoundnessCells` only extract the
fuel from `case_iff`; `fragP`/`progCode_subst` stay "no tau constructor" (unchanged). U10 is
untouched (`Necessitation/Package.lean` names `EvalGraph` only in its headline statements).

### 2.5 Descriptions, templates and the budget slot — THE design decision

A member's guard mentions `.bot (.selfIdx j)`. After `sysClose` it mentions `.bot (.sys defs j)`, a
budget-carrying snapshot — exactly the §7 situation of `ROUTE_B_SCOPE.md` (a `k`-dependent code
inside a stored template is the `binNumeral k`-instance of no fixed formula), and route (c) is the
answer, generalized: **`.selfIdx j` is a PRONOUN with its own description triple**, like `.self`
(`#0 #1 #2`) and `.opp` (`#3 #4 #5`) and the budget (`#6`): member `j` occupies `#7+3j #8+3j #9+3j`.
* `template (.plays (.bot (.selfIdx j)) … )` describes the program `pBot (revalue u w x)` of triple
  `j` as the triple `(pBotTerm x, u, w)` — `pBot` commutes with `revalue`, and `pBotTerm x = ppairTerm 3̂ x ^+ 1`
  is a TERM in the slot variable (the same move as `TBD(#6)` in `Cells/JustSlot.lean`).
* `sysCloseTemplate d g := subst (member triples of d) g` fills the member slots with the closed
  description triples `(codeTerm (canonical (pSys d j)), revalueU (pSys d j), revalueW (pSys d j))` and
  leaves `#0..#6` free — a plain variable substitution on formula codes (Foundation's `subst`, as
  `guardCodeB` does), so the gate lemma pattern of `SubstTemplate` (`guardCodeB_of_template`,
  `guardCodeB_substTemplate₇`) extends verbatim: a template that never reads member slots is unchanged.
* Because `pSys d j`'s description is a fixed term in `binNumeral k` (§2.1), the closed guard is
  `q ⇜ ![k̂]` for a fixed `q` — the instance equation is proved per family exactly as
  `guardCode_DupocV_MirrorV_eq_instB` (`termSubst_tower_of`), and `Assembly/Family.family_found` applies.
  REJECTED alternative: replacing the closed sub-term "description of `pSelfIdx j`" inside a formula
  code after the fact — no such operation exists in Foundation and it would not be a substitution instance.
* `codeTerm`: three new clauses (`pSys d i` as `ppairTerm 8̂ (ppairTerm (listTerm d) (binNumeral i))`,
  the list term by the same fixpoint; `pSelfIdx`, `pTvote` likewise) and the meta twin, code and
  truth equations, length bounds; `Fit` needs the system's guard to fit its budget — the same
  `6·|binNumeral k| + const` shape, one lemma per family.
* `Agents/Code.lean`: `progCode` gets the real codes (`noTauP`'s three `false` arms become the new
  codes; `noTauP` itself is retired or kept only where `fragP` needs it), `progCode_tvote/sys/selfIdx`
  equations replaced, `closedP (.sys _ _) = true` stays (a system is closed for `subst`).

### 2.6 Gates

`Tour.lean`'s census unchanged and all existing `#print axioms` standard; `EvalGraph.case_iff` shows
eleven disjuncts; one `.sys` self-play evaluated at ℕ by the inversion lemmas (the `cfdSys k`
system of `TauMaxConfidence/Helpers.lean`, both components, fuel 3); `progCode (inst (tauZoo k) A T)`
is never `0` for the 14 paper templates (a `decide`/`rfl` census over the roster); lockstep with the
engine's `eval` on the new search-free clauses (`.tvote` peel, `.sys` unfold) extends
`evalGraph_of_eval_searchFree`. Order of work: Prog → Subst/SysClose → Fixpoint/Eval/EvalN/Det →
CodeTerm/Guard slots/SubstTemplate → Code → RedCellUnsound arms → full build.

## 3. Phases 3–5 (headers; each gets its own section when it starts)

3. `RowSpecA` rows in `S'` for the 14 paper templates (`@[tau_rowA]`), floors → dichotomy bits,
   τ(DIMCID) → all D, the native `maxconfidence × dupoc` mutual-Löb system; `.tvote` and the
   player-level phase theorems only after the rows. **The target (derived 2026-09-30 from the `S'`
   export, since a tau bit at point mass IS the base cell — Def 3 ≡ Def 4; the engine's kernel rows
   agree with the engine's cells on every one of these 196 bits, so the derivation is sound):**
   196 ordered bits = 142 agree with the engine's rows, 13 FLIP (`≠`, the engine's value after it),
   41 are floor bits (`‡`, the engine-side value; each is a `dich_` hinge, stated as a dichotomy bit),
   0 missing. Natives are Dupoc's row (clones) and Dupoc-twins as hypotheses.

   | A \ T | coop | defect | tftSim | dupoc | ebot | obot | dbot | cupodTroll | cupod | dimcid | cimcic | prudent | maxconf | minconf |
   |---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
   | coop | C | C | C | C | C | C | C | C | C | C | C | C | C | C |
   | defect | D | D | D | D | D | D | D | D | D | D | D | D | D | D |
   | tftSim | C | D | C | C | D | C | D | C | C | D≠C | C | D | C | C |
   | dupoc | C | D | C | C | D‡ | D | D‡ | D‡ | D | D | C | D‡ | C | C |
   | ebot | D | D | C | C‡ | C | C | D | D | C | D≠C | C‡ | C‡ | C‡ | C‡ |
   | obot | C | D | D | D | D | D | D | C | D‡ | D | D | D | D | D |
   | dbot | D | C | C | C‡ | C | C | D | D | C | C | C‡ | C | C‡ | C‡ |
   | cupodTroll | C | C | C | C‡ | C | C | C | C | D | C | C‡ | C | C‡ | C‡ |
   | cupod | C | D | C | C | C | C‡ | C | D | D | D | C‡ | C‡ | C | C |
   | dimcid | D≠C | D | D≠C | D≠C | D≠C | D≠C | D≠C | D≠C | D | D | D≠C | D≠C | D≠C | D≠C |
   | cimcic | C | D | C | C | D‡ | D | D‡ | D‡ | D‡ | D | C | D‡ | C | C |
   | prudent | D | D | D | D‡ | D‡ | D | D | D | D‡ | D | D‡ | D‡ | D‡ | D‡ |
   | maxconf | C | D | C | C | D‡ | D | D‡ | D‡ | D | D | C | D‡ | C | C |
   | minconf | C | D | C | C | D‡ | D | D‡ | D‡ | D | D | C | D‡ | C | C |

   Row statement: `RowSpecA A order row := ∃ k₂, ∀ k > k₂, ∀ T ∈ order, plays (progCode (inst (tauZoo k) A T))
   (pBot-framed as the engine's RowSpec) (row T)` for the non-floor bits, and a `FloorBitA` dichotomy for
   the `‡` bits with the base cell's hinge. Method per bit = the base cell's method (SF transfer, SND,
   POS, LOEB, FLIP-LOEB) applied to the compiled instance — for non-entangled pairs the instance is
   `.bot`-wrapping plus the base source, so the base `Cells/` theorem transfers; entangled pairs
   (`.sys`) are new mutual-Löb families on the member slots of §2.5.
4. `sprime_tau_rows.json`; kernel rows verified against `S'` cells; every endpoint on `S'`.
5. Re-run Moran / phase diagrams / confusion structure on the three zoos; `EGT_FINDINGS.md` versioned per
   source; the paper's Lean section.
