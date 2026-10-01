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
   196 ordered bits = 135 agree with the engine's rows, 14 FLIP (`≠`, the engine's value after it),
   47 are floor bits (`‡`, the engine-side value; each is a `dich_` hinge, stated as a dichotomy bit — except
   the six tau images of the red cell, floors in `S'` on a base THEOREM, see the 2026-10-01 line below),
   0 missing. Natives are Dupoc's row (clones) and Dupoc-twins as hypotheses. (The 2026-09-30 derivation
   read 142 / 13 / 41; Phases 3b–3d moved `cimcic × tftSim` to the flips and the six red-cell images to the
   floors — the table below is the CURRENT oracle, as of the Phase-3d merge.)

   | A \ T | coop | defect | tftSim | dupoc | ebot | obot | dbot | cupodTroll | cupod | dimcid | cimcic | prudent | maxconf | minconf |
   |---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
   | coop | C | C | C | C | C | C | C | C | C | C | C | C | C | C |
   | defect | D | D | D | D | D | D | D | D | D | D | D | D | D | D |
   | tftSim | C | D | C | C | D | C | D | C | C | D≠C | C | D | C | C |
   | dupoc | C | D | C | C | D‡ | D | D‡ | D‡ | D‡ | D | C | D‡ | C | C |
   | ebot | D | D | C | C‡ | C | C | D | D | C | D≠C | C‡ | C‡ | C‡ | C‡ |
   | obot | C | D | D | D | D | D | D | C | D‡ | D | D | D | D | D |
   | dbot | D | C | C | C‡ | C | C | D | D | C | C | C‡ | C | C‡ | C‡ |
   | cupodTroll | C | C | C | C‡ | C | C | C | C | D | C | C‡ | C | C‡ | C‡ |
   | cupod | C | D | C | C‡ | C | C‡ | C | D | D | D | C‡ | C‡ | C‡ | C‡ |
   | dimcid | D≠C | D | D≠C | D≠C | D≠C | D≠C | D≠C | D≠C | D | D | D≠C | D≠C | D≠C | D≠C |
   | cimcic | C | D | D≠C | C | D‡ | D | D‡ | D‡ | D‡ | D | C | D‡ | C | C |
   | prudent | D | D | D | D‡ | D‡ | D | D | D | D‡ | D | D‡ | D‡ | D‡ | D‡ |
   | maxconf | C | D | C | C | D‡ | D | D‡ | D‡ | D‡ | D | C | D‡ | C | C |
   | minconf | C | D | C | C | D‡ | D | D‡ | D‡ | D‡ | D | C | D‡ | C | C |

   *2026-10-01 (Phase 3d merge).* Six more `‡` than the 2026-09-30 derivation: `dupoc/maxconf/minconf × cupod` (D)
   and `cupod × dupoc/maxconf/minconf` (C) — the tau images of the RED CELL, a THEOREM in the base
   (`outcome_DupocBot_vs_CupodBot`, by τ-symmetry) but FLOORS on the compiled `.sys` systems (τ maps one
   orientation's system to the other's, so the two members' guards are not τ-images inside one system;
   `Tau/Entangled/DupocCupod.lean`; the dichotomy field of these six names the base theorem, no `dich_` exists).
   `cimcic × tftSim` is `D≠C` (the FINDING below). **Five bits remain UNSTATED under the present coding**
   (14/14 rows, 47/47 floor bits, 191/196): `dupoc × tftSim`, `maxconf × tftSim`, `minconf × tftSim`,
   `prudent × dimcid`, `dimcid × prudent` — the budget-snapshot obstruction (a FOUND probe over a
   budget-carrying frozen instance, or a Prudent member whose inner guard freezes one); decision pending
   (route (c) made generic vs. ship under (B)). `dimcid × {tftSim, ebot, obot, dbot, cupodTroll}` are stated with
   the ENGINE's value C (the FINDING below), not the `D≠C` the table shows; `Tau/Rows/DIMCID.lean`.

   **Phase 3 contract (2026-10-01).** In `arith/ArithS/Tau/` (new folder):
   * `Spec.lean` — `paperOrder : List Tmpl` (the 14 templates above, engine order), and
     ```lean
     def instCode (k : ℕ) (A T : Tmpl) : ℕ := progCode (PD.Tau.inst (PD.Tau.tauZoo k) A T)
     def RowSpecA (A : Tmpl) (order : List Tmpl) (row : Tmpl → PD.Action) : Prop :=
       ∃ k₂, ∀ k, k₂ < k → ∀ T ∈ order, plays (pBot (instCode k A T)) (pBot (instCode k A T)) … -- the engine's
       -- RowSpec frame: `eval N (.bot inst) (.bot inst) inst = some (row T)`, i.e.
       -- `∃ N, EvalGraph N (pBot c) (pBot c) c (actCode (row T))` with `c = instCode k A T`
     def FloorBitA (A T : Tmpl) (hinge : ℕ → Prop) (a : PD.Action) : Prop :=
       ∃ k₂, ∀ k, k₂ < k → ¬ hinge k → ∃ N, EvalGraph N (pBot (instCode k A T)) (pBot (instCode k A T)) (instCode k A T) (actCode a)
     ```
     A template's row theorem `@[tau_rowA] theorem <t>RowSpecA : RowSpecA .<t> <order> <t>RowA` states
     the NON-floor slots (`order` = `paperOrder` minus that template's `‡` slots, a literal list); each
     `‡` slot is its own `@[tau_floor_bitA] theorem <t>RowSpecA_<T>_floor : FloorBitA .<t> .<T> (fun k ↦ …) a`
     with the base cell's hinge (`Outcome/Floors.lean` names it). The natives' rows are Dupoc's row by
     the `rfl` bridges (`Zoo.lean`), restated under their own names.
   * `Lint.lean` — the engine's `Tau/Lint.lean` adapted: head `ArithS.RowSpecA` syntactically, template a
     literal constructor, `order` a literal sublist of `paperOrder`, row evaluated by `whnf` at every slot,
     name `<t>RowSpecA`; floor bits: head `ArithS.FloorBitA`, name suffix, hinge text as in `Outcome/Lint`;
     `#check_tau_rowsA` census: every `(A, T) ∈ paperOrder²` is a row slot or a floor bit, never both, and
     the floor bits are EXACTLY the `‡` cells of the table above (hard-coded expected list, so a floor
     that becomes a theorem or a theorem that becomes a floor fails the build and forces the table update).
   * `Export.lean` — `lake exe export_sprime_outcomes` ALSO writes `app/generated/sprime_tau_rows.json`:
     the engine's `tau_rows.json` schema (`order` = `paperOrder`, `rows` with `bits`) plus
     `"system": "sprime"` and `"floor_bits": [{template, slot, action, hinge, dichotomy}]`; digest over
     rows ++ floor_bits.
   * Methods per bit (the base cell's, on the compiled instance): non-entangled instances are the base
     source under `.bot` with the hypothesis's instance in place of `.opp` — transfer from the base
     `Cells/` theorem where the instance's guard is the base guard (`instGo` on a `.name` target is
     `.bot (instAt T B)`; the truth equations of `Cells/Common/Templates.lean` are generic in the opp
     triple); search-free templates by `evalGraph_of_eval_tauSearchFree` from the engine's own
     `Tau/Theorems/<Bot>/Phase.lean` bits (SAME fuel); entangled pairs (`.sys`) are new families on the
     member slots (Phase 2b) — `dupoc × {cupod, cimcic, dimcid, prudent, maxconf, minconf}` and the
     other 36 ordered pairs among the 7 self-probers, plus τ(EBot)'s `.mirror` probe at self-probing
     hypotheses. Order of attack: rows of `coop defect tftSim dbot obot ebot cupodTroll` (search-free or
     SND/POS, 7 rows), then `dupoc cupod cimcic dimcid prudent` non-entangled slots, then the natives by
     bridge, then the entangled slots.

   **FINDING 2026-10-01 (Phase 3b, `Tau/NeverFits.lean`) — the budget-snapshot obstruction, and a fork.**
   The table above assumed Def 3 ≡ Def 4 transfers to `S'`. It does not at every bit: when a guard names a
   hypothesis INSTANCE that carries the budget (`inst tftSim cimcic` contains `inst cimcic coop = .search k …`;
   τ(CupodTroll)'s instance IS a `.search k`), the stored template describes that closed program with
   `binNumeral k` written INSIDE it, so (i) the template code is `k`-dependent (not the `k̂`-instance of a fixed
   formula — `ROUTE_B_SCOPE.md` §7 one level down) and (ii) the frame's description then carries the numeral
   of that template code, of length `≥ k` — the guard sentence never fits its budget and is never found.
   Machine-checked consequences under the PRESENT coding: `cimcic × tftSim = D` (a flip the table lacks);
   `dimcid × {tftSim, ebot, obot, dbot, cupodTroll} = C` (the ENGINE's values, by never-found rather than by
   reading); `cimcic × {ebot, dbot, cupodTroll}` are theorems (hinge false at every `k`), stated as floor bits
   only because the linter's expected list says `‡`; open: `dupoc/maxconf/minconf × tftSim` (C needs a FOUND
   probe over a budget-carrying watch). The base matrix is untouched (base opponents carry no second budget;
   JustBot/CupodTroll were already handled by hand with route (c): the `Just7`/`CupodTroll7` twins).
   This is a violation of Critch's assumption (b) by the coding, not a property of PA: the principled fix is
   **route (c) made generic** — `template13 φ k` describes a closed sub-program by its `codeTerm` tower with
   every `.search` budget EQUAL to the node's own budget written as the slot variable `#6` (budget abstraction);
   then every tau template is a constant, every guard a `k̂`-instance, lengths `O(log k)`, the `Just7`/
   `CupodTroll7` twins become the engine's own bots, and the table's values are recovered (Def 3 ≡ Def 4 again,
   now as a theorem of the coding). Cost: a trusted-base change to `closedDesc`/`template13`/`progCode` plus
   the downstream repair of every `Cells/` proof that unfolds a `k`-dependent template (`JustBot`, `JustSlot`,
   `DimcidFlips` on `CupodTroll7`) — days, not hours. DECISION PENDING (user): (A) generic route (c) now, or
   (B) ship Phase 3 under the present coding with the corrected table and record the deviation as a result.
   **DECIDED 2026-10-01: (A).** Specification (Phase 2c, trusted base):
   * `template13 : PD.Formula → ℕ → Semisentence LAct 13` takes the NODE BUDGET `k₀`; `progCode (.search k φ p q)
     = pSearch k ⌜template13 φ k⌝ …`; `templateCodeAt φ k := ⌜template13 φ k⌝`. The old one-argument
     `templateCode φ` stays as the UNABSTRACTED template (`template13 φ` with no budget to abstract, i.e. the
     present definition), and the bridge `templateCodeAt_eq_templateCode : noBudgetSnapshotF φ = true →
     templateCodeAt φ k = templateCode φ` (new syntactic predicate: no closed sub-program of `φ` contains a
     `.search`) keeps every base statement literally true (Dupoc, Cupod, CIMCIC, DIMCID, Prudent, Mirror,
     Wary, …: their guards name only pronouns and search-free constants). The bots that CHANGE code are exactly
     the ones route (c) handled by hand — `JustBot k` (snapshot `DupocBot k`), `CupodTrollBot k` (snapshot
     `CupodBot k`), LegibleBot/OptimBot (out of scope) — and the tau instances.
   * Budget abstraction in closed descriptions: `codeTermMetaAbs k₀ c` is `codeTermMeta c` except that a
     `pSearch k g p q` leaf with `k = k₀` writes the slot variable `#6` for its budget (the template code `g`
     stays a binary-numeral leaf — under (A) it is a constant); `closedDesc13` uses it; the truth equation
     `val (codeTermMetaAbs k₀ c)[#6 ↦ k₀] = c` and the length bound `O(log)` in the leaves; `revalueU/W` of the
     closed program stay the closed constants they are (`k`-independent, as `Instance.lean` shows for Dupoc).
     The evaluator is UNCHANGED: `guardCodeB` already fills `#6` with the node's budget.
   * Consequences to prove: `progCode (JustBot k) = Just7 k` (and CupodTroll7) — the hand twins become
     theorems about the engine's bots; restate the twelve twin cells of `Outcome/Matrix` on the engine bots
     (names `outcome_<L>_vs_<R>` with the real bot names; the app's twin aliasing becomes dead code, keep it
     harmless); `Cells/JustBot`, `JustSlot`, `DimcidFlips` (CupodTroll7) repaired or re-targeted; `guard_fits`
     untouched.
   * Then Phase 3e: the 12 recorded divergences re-proved with the table's values (the six red-cell floors
     STAY floors — that finding is independent of the coding), the 5 unstated bits stated, `expectedFloorBits`
     re-derived (expected: 41 + 6 = 47 unless (A) reveals otherwise — the build decides),
     `SPRIME_RECORDED_DIVERGENCES` emptied, certification 196/196, `#check_tau_rowsA strict` in the build.


   **STATE 2026-10-02 (Phases 2c + 3e landed): 195/196 paper bits stated — 148 row slots + 47 floor bits.**
   Under (A) the table's values are recovered: `cimcic × tftSim = C`, `dimcid × {tftSim, obot, dbot,
   cupodTroll, prudent} = D≠`, `prudent × dimcid = D`, `dupoc/maxconf/minconf × tftSim = C`
   (`Tau/{Watch,Stored,ClosedWatch,Watch2,ClosedWatch2}.lean`, `Tau/Entangled/{Generic,DimcidPrudent}.lean`).
   The six red-cell cross bits stay FLOORS (independent of the coding). App: the six VALUE divergences are
   gone, the six `provenance` ones (red cell) remain; `tau.compare --zoo paper --source sprime`: 148 agree,
   41 floor-agree, 6 recorded, 0 unexpected, 1 uncovered.
   **ONE BIT OPEN — `dimcid × ebot` (table `D≠`).** `Tau/NeverFitsSys.lean` proves it is C at every budget
   under the present coding (`dimcid_ebot_C`): τ(EBot)'s instance at DIMCID has a third watch on
   `inst dimcid mirror`, a closed SYSTEM with a `.search k` member, and `codeTermMetaAbs` describes systems
   verbatim (Phase 2c's design limit, needed for the literal member-slot equation). So the numeral `k` is back
   inside that one stored template and the guard never fits. It is left UNSTATED; `#check_tau_rowsA` stays
   plain. Decision pending: (α) let the abstraction descend into systems (a code-level `codeTermAbs`,
   `descriptionsSys d k`, `sysCloseTemplate d k`, `Tau/Entangled` re-done — days) or state the bit as C and
   record ONE value divergence (then 196/196 and `strict`).
   **DECIDED 2026-10-02: (α).** Specification (Phase 2d + 3f):
   * `codeTermMetaAbs k₀` DESCENDS into `pSys d i` (member list abstracted member by member; the index a
     numeral); `NoSearchAt`/length/instantiation lemmas extended (`subst_codeTermMetaAbs` stays the identity
     that filling `#6` with `k₀` recovers the verbatim term).
   * The closer takes the node's budget: a code-level Δ₁ `codeTermAbs k₀ : V → V` (the code of the abstracted
     term, `#6` kept as a bound variable), `descriptionsSysAt d k` (member triples from it),
     `sysCloseTemplateAt d k g`, and `sysCloseCode d`'s search clause `pSearch k g p q ↦ pSearch k
     (sysCloseTemplateAt d k g) …`. The literal member equation `templateAt_sysClose` /
     `progCode_sysClose_member` re-proved on the abstracted descriptions (both sides now abstract).
   * THE BRIDGE that keeps `Tau/Entangled` alive: `guardCodeB (sysCloseTemplateAt d k g) me opp k =
     guardCodeB (sysCloseTemplate d g) me opp k` — the CONSULTED sentence of a closed member is unchanged,
     only its stored numerals shrink (the system twin of `guardCodeB_templateCodeAt`). Every Entangled lemma
     about consulted codes (`guardCodeB_sysClose_eq_instB`, the families) is to be bridged, not redone.
   * Then `dimcid × ebot = D` (`dimcid_D_of_towers` on EBot's three-stage watch, whose third stage names the
     system `inst dimcid mirror`: tower from `Entangled/Tower.sysT1`), `NeverFitsSys` restated on the explicit
     pre-abstraction code (vacuous for compiled instances), `#check_tau_rowsA strict`, export, compare
     196/196 with only the six red-cell provenance entries recorded.

   **Phase 4 contract.** `tau/def4_theorems.py`: `TAU_EXPORTS = {engine: tau_rows.json, sprime:
   sprime_tau_rows.json}`, `kernel_bits(source)`, a floor bit loads as the engine-side action with
   `provenance = floor_dichotomy`; `tau/matrix.py::_kernel_rows_for(source="sprime")` verifies rows
   against the `S'` cells (floor bits against floor cells) and sets `is_kernel_backed = True`;
   `tau/compare.py` certifies Def 3 ≡ Def 4 on `sprime` (expected: 196/196 agree, 41 of them floor-bit
   agreements); the `/tau/zoos` route reports `kernel_backed` per source.

4. `sprime_tau_rows.json`; kernel rows verified against `S'` cells; every endpoint on `S'`.
5. Re-run Moran / phase diagrams / confusion structure on the three zoos; `EGT_FINDINGS.md` versioned per
   source; the paper's Lean section.
