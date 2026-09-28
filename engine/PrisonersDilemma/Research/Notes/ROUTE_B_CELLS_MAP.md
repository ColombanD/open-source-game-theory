# ROUTE_B_CELLS_MAP — the consolidation map for `arith/ArithS/Cells/*` (survey 2026-09-24)

*Read-only survey of the thirteen `Cells/*.lean` files (12.5k lines, written by different agents over
two days) and `Assembly/{Prep,Family,Cell}`, produced for the consolidation refactor whose gate is:
EVERY existing theorem name and statement byte-identical; only proofs and locations move; definition
BODIES never change (`Describes`, `SV`, `descVal`, `qT`, `pQ` — `rfl`-based proofs such as `pDM = pQ qDM`
depend on them); `variable`-dependent sections (the `SV` block) keep binder names and order.*

## Headline findings

* Two EXACT duplicate blocks: the TitForTat code block (`TftV`/`TTft` in KhatCells vs `TFTV`/`TTFT` in
  FlipCells, identical bodies) and the substitution vector (`tmplVec` in JustBot vs `gVec` in DIMCID,
  same 6-code vector, arguments in a different order).
* Almost every per-family lemma is an instance of a generic one that exists but lives too far
  DOWNSTREAM: `pQ` (FlipCells), `qT` (PrudentMirror), `SV` (PositiveCells), `Describes` (FlipCells),
  `found_of_all_above` (KhatCells), `mirror_step_V` (DupocMirror), `SV_then_V` (KhatCells).
* **TRAP: `DupocV`/`Dupoc` and `SV gDu 0`/`pcode (DupocBot k)` are DIFFERENT programs** — the first
  stores the hand template `GtmplA 0`, the second `tmpl (.plays .opp .self .C)` (`Agents/Code.lean:699`
  documents it). Same for `Cupod` vs `CupodBot`, `Just`/`Just7` vs `pcode (JustBot k)`. Never merge them;
  bridging lemmas (`DimcidV_eq_SV`, `CimcicV_eq_SV` — these two ARE equal up to a cast) may be ADDED.

## Import DAG (FINAL state, after the consolidation refactor of 2026-09-24 — stages 1–7 landed)

```
InstanceV ─► Transparency ─► Assembly/Prep ─► Family ─► Uniform ─► Cell ─► Necessitation/Package
Cells/Common/Syntax     ← Assembly/Prep, InstanceV, SimTest, Template, EvalN   (quotes/relabel ₄₆₇, descVec entries,
                                                                                tower substitution, casts, pBot/pConst algebra)
Cells/Common/Bots       ← Common/Syntax, Assembly/Prep, SimTest                 (MirrorV/TM, Tft + FlipCells' TFTV twins
                                                                                with rfl bridges, T0/TB0, the SV section
                                                                                (variable block verbatim), botT1, gDu…gWT, TBS)
Cells/Common/Templates  ← Common/Bots                                           (qG/gVec, qT, tmplVec (+ tmplVec_eq_gVec),
                                                                                atom truths, TD/TBD towers, descVal/Describes/
                                                                                DescribesAbove, describes_closed/_CB/_botCB/
                                                                                _TFT/_SV/_botSV/_dupocV/_botDupoc)
Cells/Common/Probers    ← Common/Bots, EvalN                                    (search_then/else_V₆, SV_then_V, SV_search_V,
                                                                                *_frame_search_V, *_search_any_V, mirror_step_V,
                                                                                mirror_copies(3)_V, mirror_bot_*, tft_*_V, const_*)
Cells/Common/Families   ← Common/Templates, Assembly/Uniform                    (pQ + lemmas, loebSound_pQ_of, slack_depth_le,
                                                                                nat_le_of_le_def)
Cells/Common/Khat       ← Common/Families, Necessitation/Package                (linear_size_le_eventually, tact_all_of_both,
                                                                                found_of_all(_V/_above), tact_all_above_of_both,
                                                                                exists_instance_length_above, BoxConseq & co)
Cells/DupocMirror   ← Common/{Templates,Probers,Families,Khat}, Assembly/Cell, SimTest, Necessitation/Package
Cells/JustBot       ← DupocMirror
Cells/DIMCID        ← DupocMirror, Necessitation/Package, PD.DIMCID      (now also holds loebSound_pG_of/_of_above, describes_dimcid/_mirror)
Cells/CIMCIC        ← DIMCID
Cells/PrudentMirror ← DIMCID
Cells/JustSlot      ← JustBot, CIMCIC                                     (now also holds just7_else_V/just7_D_of_probe)
Cells/SimSlot       ← JustSlot
Cells/SearchFree    ← Inst, SimTest, PD theorems           (separate branch: no Assembly, no LoebSound)
Cells/SoundnessCells← SearchFree, Det, InstanceV, NumeralFacts, Diag      (now also holds ebot_D_of_probes_D)
Cells/PositiveCells ← SoundnessCells, CIMCIC, JustBot, PrudentMirror   (the two branches merge here)
Cells/KhatCells     ← PositiveCells, JustSlot
Cells/FlipCells     ← PositiveCells, DIMCID, KhatCells
Cells/DimcidFlips   ← FlipCells
Cells/FloorVerdicts ← DimcidFlips                                         (2026-09-27: the settled halves / true guards of the 26 genuine floors; method prefix `floor`)
Cells/FloorDichotomy← FloorVerdicts                                        (2026-09-27: the hypothesis-free dichotomies `dich_<L>_vs_<R>` of the 26 genuine floors)
Cells/Names         ← every Cells file                                    (since 2026-09-27 the DEPRECATION layer: `@[deprecated]` aliases of the OLD names; imported by ArithS.lean, not Audit)
```
`ArithS.lean` imports every Common module, every Cells file and `Cells/Names`; `Audit.lean` imports the Common
modules and prints, per module, the moved names that were not already printed (Syntax 33, Bots 81 incl. the
four `*_eq_SV` bridges, Templates 42, Probers 14, Families 9, Khat 0 — every Khat theorem was already printed).
The gate held at every stage: 0 headers missing/changed, 15 added (the new lemmas below), 0 definition bodies
changed; final `lake build ArithS` 3357 jobs; census 1757 (baseline 1579 + 178), all standard but the 4
pre-existing subsets. NEW declarations (all additive): `TFTV_eq_TftV`, `TFTTV_eq_TftTV`, `TTFT_eq_TTft`,
`DimcidV_eq_SV`, `DimcidTV_eq_SV`, `CimcicV_eq_SV`, `CimcicTV_eq_SV`, `tmplVec_eq_gVec`, `search_then_V₆`,
`search_else_V₆`, `loebSound_pQ_of`, `slack_depth_le`, `describes_CB`, `describes_dimcid`, `describes_mirror`;
proofs turned into corollaries in place: `loebSound_pDD/_pDMi/_pDi0` (of `loebSound_pG_of`), `loebSound_pWM/_pWW`
(of `loebSound_pQ_of`), `slack4_*`/`slack6_*` (of `slack_depth_le`), `cimcic_self_finds_guard` (of `found_of_all`),
FlipCells' `TFTV` lemmas (of the `Tft` ones). NOT done: `pConj_slack_nat` stays as is (`Assembly/Cell` is
upstream of `Common/Families` and off-limits); `DupocV`/`Dupoc` are NOT bridged to `SV` (the trap below).

## Import DAG before the refactor (survey state, 2026-09-24 morning)

```
InstanceV ─► Transparency ─► Assembly/Prep ─► Family ─► Uniform ─► Cell ─► Necessitation/Package
Cells/DupocMirror   ← Assembly/Cell, SimTest, Necessitation/Package
Cells/JustBot       ← DupocMirror
Cells/DIMCID        ← DupocMirror, Necessitation/Package, PD.DIMCID
Cells/CIMCIC        ← DIMCID
Cells/PrudentMirror ← DIMCID
Cells/JustSlot      ← JustBot, CIMCIC
Cells/SimSlot       ← JustSlot
Cells/SearchFree    ← Inst, SimTest, PD theorems           (separate branch: no Assembly, no LoebSound)
Cells/SoundnessCells← SearchFree, Det, InstanceV, NumeralFacts, Diag
Cells/PositiveCells ← SoundnessCells, CIMCIC, JustBot, PrudentMirror   (the two branches merge here)
Cells/KhatCells     ← PositiveCells, JustSlot
Cells/FlipCells     ← PositiveCells, DIMCID, KhatCells
Cells/DimcidFlips   ← FlipCells
```
`ArithS.lean` and `Audit.lean` import every file explicitly; new `Common/` modules must be added to
`ArithS.lean` (Audit gets them transitively, but each needs its own `#print axioms` block, never
repeating an already-printed name; the only duplicate print today is `sizeThmAll_holds`, Audit 1949/1978).

## Groups (occurrence tables)

### (a) Bot codes and description towers — one ~25-declaration scaffold per tower
| Code (V / ℕ) | Transposed | Description term | Lines | Instance of |
|---|---|---|---|---|
| `DupocV` InstanceV:39 / `Dupoc` RedCell:31 | `CupodV` InstanceV:42 | `TD` Instance:202; `uD/wD` Instance:98/101; `uC/wC` Prep:151/152 | InstanceV | NOT `SV` (hand template) |
| `MirrorV` DupocMirror:74 / `Mirror` SimTest:17 | itself | `TM` DupocMirror:123 (closed) | :74–137 | closed ⇒ `describes_closed Mirror` |
| `DimcidV` DIMCID:140 / `Dimcid` :146 | `DimcidTV` :143 | `TDi` :259; `uDi/wDi` :208/211 | :166–315 | `SV tmplD 1` |
| `CimcicV` CIMCIC:94 / `Cimcic` :100 | `CimcicTV` :97 | `TCi` :213; `uCi/wCi` :162/165 | :120–269 | `SV tmplC 0` (`pcode_CIMCIC_SV`, DimcidFlips:420) |
| `PrudentV` PrudentMirror:96 / `Prudent` :105 | `PrudentTV` :101 | `TP` :415 (nested) | :203–452 | not `SV` (nested search, `hk : KP ≤ k`) |
| `JustV` JustBot:592 / `Just` :673 | — | uses `TBD` | :580–723 | 6-template depending on `k` (the §7 bot) |
| `JustV7` JustSlot:446 / `Just7` :452 | `JustTV7` :449 | `TJ` :611; `uJ/wJ` :560/563 | :518–717 | 7-template |
| `CupodTrollV7` KhatCells:860 / `CupodTroll7` :866 | `CupodTrollTV7` :863 | `TT` :1018; `uT/wT` :967/970 | :925–1100 | 7-template |
| `TftV`/`TftTV` KhatCells:196/199, `TTft` :232 | | | :193–260 | **EXACT DUPLICATE of `TFTV`/`TFTTV` FlipCells:161/163, `TTFT` :191** (FlipCells imports KhatCells) |
| `SV g a k` PositiveCells:183 (`variable (g)(a)`) | `swapcode_SV` :213 | `TS g a` :297; `uS/wS` :239/243 | :178–360 | **the generic one** |
| `pBot (DupocV k)` | `pBot (CupodV k)` | `TBD` JustBot:164 | :143–205 | `TBS (GtmplA 0) 0` pattern (`TBS` PositiveCells:527) |
| `pConst 0/1`, `pBot (pConst 0)` | | `T0`/`TB0` PositiveCells:91/104 | :61–174 | closed ⇒ `describes_closed` (DimcidFlips:115) |
TFT duplicate pairs (KhatCells → FlipCells): `swapcode_TftV`:210→`swapcode_TFTV`:173, `TftV_lt_TftTV`:218→`TFTV_lt_TFTTV`:178, `dnum/dU/dW_TftV`:222–228→`_TFTV`:182–187, `lMap_swap_TTft`:234→`_TTFT`:193, `val_TTft_V`:236→`val_TTFT_V`:195, `quote_emb_TTft`:240→`_TTFT`:199, `cast_Tft`:206→`cast_TFT`:165, `TftV_nat`:204→`TFTV_nat`:170. Only FlipCells' `TFTV_lt_TFTTV`/`describes_TFT` are in Audit.
The `hX_/hU_/hW_/hopp_/hopp'_` (and `hme_`) quintuples = one `Describes X U W` record unpacked: DIMCID:746–765 (`_self` = `TDi,uDi,wDi`), :886–908 (`_mirror`), :1043–1062 (`_cupod` = `TD,uC,wC`), :1067–1073 (`hX/hU/hW_dupoc`) + CIMCIC:686/692 (`hopp/hopp'_dupoc` — the other half, split across files); CIMCIC:664–683 (`_cimcic`); JustSlot:672–691 (`_just7`), :694–712 (`_bot` = `TBD,uD,wD`, named `hme`); KhatCells:1079–1098 (`_troll7`), :245–250 (`_tft`); PrudentMirror:566–570 (`_prudent`, needs `hk` = `DescribesAbove KP`); PositiveCells:118–149 (constants), :315–321/469–479 (`_SV`, generic), :574–588 (`_botSV`); FlipCells:642 (`hme_WT`). Existing `Describes` instances: `describes_botCB` Flip:152, `describes_TFT` :214, `describes_SV` :477, `describes_troll7` :887, `describes_closed` DimcidFlips:115, `describes_botSV` :242, `describes_dupocV` :262, `describes_botDupoc` :275, `describes_just7` :290, `describesAbove_prudent` :309. MISSING: `(TDi,uDi,wDi)`, `(TCi,…)`, `(cl TM, numT 0, numT 1)`.

### (b) Instance and truth equations for templates
Generic: `qT g X U W X' U' W'` PrudentMirror:459 with `quote_qT`/`guardCode_qT_eq_instB`/`guardCode_qT_swap_eq_instB`/`eval_qT_iff` :474–525. Instances: `qG a …` DIMCID:1103 (= `qT (GtmplA a)`) with `quote_qG`/`guardCode_GtmplA_eq_instB`/`_swap_eq_instB`/`eval_qG_iff_V` :1146–1247; JustBot:222/284/305 `quote_GtmplA_subst`/`guardCode_eq_instB_of`/`eval_GtmplA_subst_iff` (NEAR-DUPLICATE of the DIMCID pair: hypotheses via `⌜Rew.emb u⌝`); JustBot:213 `tmplVec` vs DIMCID:1119 `gVec` (EXACT DUPLICATE; `tmplVec_semitermVec`/`termSubstVec_tmplVec` :230/239 vs `gVec_*` :1155/1165); `qDG/qTG/qDGVec/…` DIMCID:387–556 (= `qT tmplD TDi uDi wDi …`); `qCG/qCTG/qCGVec/…` CIMCIC:303–495 (copy of the DIMCID block); `qDM/qDMVec/…` DupocMirror:142–237 (= `qG 0 TD uD wD (cl TM) (numT 0) (numT 1)`); `qBD/qBC_eq/qJM/qJC_eq/guardCode_botDupocV_*` JustBot:343–396, 731–786; Prep:156/184 `qCupod_eq`/`eval_qCupod_iff_V`. Relabel family subsumed by `guardCode_qT_swap_eq_instB`: Prep:99, DupocMirror:250, JustBot:372/763, DIMCID:568, CIMCIC:484; relabel quotes (Prep:95, DupocMirror:246, JustBot:369/760) are instances of `relabelTemplate_quote_sentence_V`. Atom truth (generic, downstream): DIMCID:324/342 `eval_tmpl_plays_self_opp_V`/`_opp_self_V`, PrudentMirror:543 `eval_tmpl_plays_opp_closed_V`, PositiveCells:432/445/460 `eval_qT_plays_opp_self`/`eval_qT_neg_plays_opp_self`/`eval_qT_swap`. Describes layer (generic, at the END of the DAG): FlipCells:76/80/88 `descVal`/`descVal_def`/`Describes`; DimcidFlips:167/177 `DescribesAbove`/`Describes.above`; :96/100/115 `descVal_closed`/`descVal_closed_T`/`describes_closed`. Arity-indexed twins: `coe_quote_sentence₁` Prep:78 / `₆` DIMCID:118 / `₇` JustSlot:218; `relabelTemplate_quote_sentence_V` Prep:85 / `₆_V` DIMCID:123 / `₇_V` JustSlot:222; `semiterm_quote_emb_n/₄/₇` JustSlot:83/88/92; `isSemiformula_quote₄/₇` :97/100. Tower substitution: `termSubst_tower` InstanceV:241, `termSubst_tower_of` JustSlot:106 (generalizes), `termSubst_tower'` PrudentMirror:392, `termSubst_TBD` JustBot:181 vs `termSubst_TBD_of` JustSlot:128, `termSubst_TBS` PositiveCells:547. `descVec` indexing: `nth_descVec_three/four/five` JustBot:602–611; `nth_descVecB_zero…six` JustSlot:153–177. Small helpers: `quote_emb_numT` DupocMirror:137 (≈ `quote_numT` Template:174), `lMap_swap_dnumT'` DimcidFlips:87 (≈ Template:123 + `dnum_swapcode`), `cast_swapcode`/`cast_dnum` DimcidFlips:78/83.

### (c) Conjunction families and ∧-elimination slack
Every family is `pQ q := q ⋏ lMap swap q` (FlipCells:578) by definition: `pConj` Prep:236, `pDM` DupocMirror:394, `pBD` JustBot:444, `pJM` :849, `pCD` DIMCID:1315, `pDCi` CIMCIC:765, `pJJ2` JustSlot:823, `pJD2/pBDD2/pDJ2` :1087–1089, `pJCi2` :1373; `pG` DIMCID:628 and `pGC` CIMCIC:544 are `pQ (qDG …)`/`pQ (qCG …)` by `lMap_swap_qDG`/`_qCG`. Generic: FlipCells:586–620 `instB_quote_pQ`/`formulaLen_instB_pQ`/`pQ_both_V`/`eval_pQ_std`/`eval_pQ_swap`. Instances: `pconj_both_V` Prep:506; `pDM_both_V`/`pDM_guards_V` DupocMirror:416/431; `pBD_*` JustBot:462/478; `pJM_*` :868/884; `pG_*` DIMCID:659/678 (generic in X U W); `pGC_*` CIMCIC:575/594 (copy); depth 2: `pDC_all_V/_guards_V` DIMCID:1384/1415, `pCiD_*` CIMCIC:802/833, `pJJ_all_V/_guard_V` JustSlot:859/891, `pPM_*` PrudentMirror:770/803; depth 3: `pJD_boxes_V/_all_V` JustSlot:1144/1214, `pCJ_all_V` :1413. 24 `instB_quote_*` lemmas (all `instB_quote_and` Prep:278 or `instB_quote_pQ`), 23 `formulaLen_instB_*`, 12 `eval_*_iff_std/_swap/_stdActS` triples (all from `eval_pQ_std/swap`). Slack: base `andL/andR_sharp_le_uniform` Prep:469/476; `pConj_slack_nat` Cell:59 (d=1, (7,8)); `slack4_le/_le'` DIMCID:1353/1363 (d=2, (14,16), differ by `hx` vs `hy`), `slack4_nat/'` :1373/1377; `slack6_le₁` JustSlot:724 (SAME hypotheses/LHS as `slack4_le`, bound (21,24) — follows by monotonicity), `slack6_le/_le'` :736/753 (d=3), `slack6_nat₁/nat/nat'` :769–779. General form: depth d gives `a + Σ(8(xᵢ+yᵢ)+7) ≤ a + 7d + 8d·z`.

### (d) Search-clause lemmas (most general first)
Root: `EvalGraph.search_iff`/`search_iff₆` EvalN:53/65. `SV_then_V g a k me opp` KhatCells:285 (any frame), `botSV_then_V` :295; `dupoc/cupod_frame_search_V` JustBot:103/114, `botDupoc/botCupod_frame_search_V` :127/133; `dupoc/cupod_search_any_V` DIMCID:1089/1076; `dupoc_search_V` Transparency:152; `cupod_search_V/_instB_V` Prep:123/136; `dupoc/cupod_mirror_search_V(+_instB_V)` DupocMirror:274–306; `botDupoc/botCupod(_mirror)_search_V` JustBot:431/436/825/830; `just_search_V` :653; `just7_search_V/just7T_search_V` JustSlot:466/478; **`just7_else_V` DimcidFlips:462 (three files from its `_search_V`)**; `dimcid/dimcidT_search_V` DIMCID:596/609; `cimcic/cimcicT_search_V` CIMCIC:512/524; `SV_search_V` FlipCells:628 (instance of `SV_then_V`); `prudent/prudentT_search_V` PrudentMirror:688/701; `troll7_then_V/_else_V/troll7T_then_V` KhatCells:880–901; ℕ: `search_else/search_then/search_either` SoundnessCells:320–332; bridges `evalGraph_JustV7_iff`/`evalGraph_Just7_iff` JustSlot:491/500, `evalGraph_CupodTroll7_iff` KhatCells:912.

### (e) Prober lemmas
Generic `mirror_step_V` DupocMirror:97; `mirror_copies_V` DIMCID:880 (2→3), `mirror_copies3_V` PrudentMirror:714 (3→4); instances `mirror_copies_dupoc/cupod_V` DupocMirror:105/111, `mirror_copies_botDupoc/botCupod_V` JustBot:836/841; ℕ `mirror_copies` SoundnessCells:345; `mirror_bot_defect_V/_coop_V` PrudentMirror:670/679; `tft_C_of_probe_C_V`/`tftT_D_of_probe_D_V` KhatCells:266/275 (V twins of SoundnessCells:369/378); ℕ-only `dbot_*` :351/360, `obot_*` :387–427, `ebot_*` :435/446; **`ebot_D_of_probes_D` DimcidFlips:442 belongs next to them**; `bot_const_play`/`const_play` (ℕ) SoundnessCells:339/342 vs `_V` PositiveCells:482/486, `const_not_play_V`/`bot_const_not_play_V` :490/495; `just_D_of_probe` SoundnessCells:611 vs `just7_D_of_probe` DimcidFlips:476.

### (f) The `k̂`-chain and "found" lemmas
`tact_all_of_both` PositiveCells:367 (the `k̂ = 0` case of) `tact_all_above_of_both` KhatCells:98; `found_of_all` PositiveCells:388 (the `k̂ = 0` case of) `found_of_all_above` KhatCells:161; `found_of_all_V` :67; `exists_instance_length_above` :117; `found_of_box_conseq` FlipCells:369 with `BoxConseq`/`loebSound_iff_boxConseq`/`box_conseq_uniform`/`substs_imp`/`total_le_eventually` :281–338; CIMCIC:1086–1128 `tact_proves_qCC`/`exists_qCC_length`/`qCC_inst_V`/`cimcic_self_finds_guard` = a hand-inlined `found_of_all`; **`linear_size_le_eventually` CIMCIC:1119 = `poly_size_le_eventually C 1` (Family:165)**; upstream generic: Family:165/683/698/783/730; ℕ branch: `found_of_tact`/`guardian_found` SoundnessCells:181/1019.

### (g) ℕ/V bridging helpers
`le_def_trans` Family:695 and `nat_le_of_le_def` FlipCells:328 — the only `=∨<` helpers, should sit together in Family. ℕ slack twins as in (c). Code casts: `*_nat` (`MirrorV_nat`, `DimcidV_nat`, `CimcicV_nat`, `PrudentV_nat`/`PrudentTV_nat`, `JustV_nat`, `JustV7_nat`, `CupodTrollV7_nat`, `SV_nat`, `TftV_nat`, `TFTV_nat`), `cast_Mirror` DupocMirror:78, `cast_Tft`/`cast_TFT`, `cast_swapcode`/`cast_dnum`. Primed engine-code lemmas: `pcode_DIMCID'` PositiveCells:1013 vs `pcode_DIMCID` DIMCID:151; `pcode_CIMCIC'` :927 vs CIMCIC:105; `pcode_PrudentBot'` SoundnessCells:293 vs PrudentMirror:113; `pcode_DupocBot'` :281 vs Code:699.

### (h) `LoebSound` premise proofs (`LoebSound p S₀ S₁`, Family:607)
(7,8): `loebSound_pConj` Uniform:211, `_pDM` DupocMirror:481, `_pBD` JustBot:515, `_pJM` :923, `_pWM` FlipCells:717, `_pWW` :744 — all `pQ q`, a generic `loebSound_pQ_of` is missing; `loebSound_pG_of` FlipCells:102 (generic for Dimcid, from `Describes`), `_pDD` DIMCID:804, `_pDMi` :945, `_pDi0` PositiveCells:1020 (corollaries once `describes_dimcid`/`describes_mirror`/constants exist); `loebSound_pG_of_above` DimcidFlips:186; `_pCMi` CIMCIC:993 (needs a missing `loebSound_pGC_of`). (14,16): `_pDC` DIMCID:1479, `_pCiD` CIMCIC:897, `_pJJ` JustSlot:944; (14+KP,16): `_pPM` PrudentMirror:854; (21,24): `_pJD` JustSlot:1274, `_pCJ` :1516. Also `loebSound_iff_boxConseq` FlipCells:287.

## Proposed target modules and import DAG
```
Agents/InstanceV, Eval/SimTest, Agents/Template, Eval/EvalN      (paths after the 2026-09-28 reorganization, arith/PATHS.md)
   └─► Cells/Common/Syntax.lean      (arity-generic quote/relabel lemmas, pBot algebra, pConst facts, tower substitution, descVec indexing, casts)
         └─► Assembly/Prep ─► Family ─► Uniform ─► Cell        (option B: Syntax imports Prep and leaves Prep's ₁ lemmas untouched — PREFERRED)
Cells/Common/Bots.lean       imports Common/Syntax, Assembly/Prep, Eval/SimTest   (MirrorV/TM, Tft block, T0/TB0, the SV section with its variable block, TBS, bridging lemmas DimcidV_eq_SV/CimcicV_eq_SV)
Cells/Common/Templates.lean  imports Common/Bots                              (gVec, qT + its four lemmas, qG + four, guardCode_eq_instB_of/eval_GtmplA_subst_iff, the atom truths, descVal/Describes/DescribesAbove/describes_closed/_SV/_botSV/_dupocV/_botDupoc/_TFT/_botCB)
Cells/Common/Probers.lean    imports Common/Bots, Eval/EvalN                       (search_then_V₆/search_else_V₆ NEW, SV_then_V, botSV_then_V, SV_search_V, the frame/any search lemmas, mirror_step_V/copies/copies3, mirror_bot_*, tft_*_V, const_play_V…)
Cells/Common/Families.lean   imports Common/Templates, Assembly/Family        (pQ + its lemmas, loebSound_pQ_of NEW, a depth-d slack lemma NEW with slack4/slack6/pConj_slack_nat as corollaries, nat_le_of_le_def, loebSound_pG_of/_of_above)
Cells/Common/Khat.lean       imports Assembly/Family                          (tact_all_of_both, found_of_all, found_of_all_V, tact_all_above_of_both, exists_instance_length_above, found_of_all_above, BoxConseq & co, linear_size_le_eventually)
Cells/DupocMirror            imports Assembly/Cell, Necessitation/Package, Common/{Families,Probers,Khat}; everything downstream unchanged; SearchFree/SoundnessCells keep their separate branch (ℕ probers stay there).
```
Dependency check: PositiveCells' SV section (61–360) uses only `coe_quote_sentence₆`, `relabelTemplate_quote_sentence₆_V` (DIMCID), `dnum/dU/dW_pBot` (JustBot), `guardCode_qT_eq_instB` (PrudentMirror) — all move down too. PrudentMirror's `qT` section needs only `gVec_semitermVec`, `termSubstVec_gVec`, `relabelTemplate_quote_sentence₆_V`. FlipCells' boxConseq section and DIMCID's `qG` section have no Cells dependencies. KhatCells' chain section needs `found_of_all` and `linear_size_le_eventually`. Placement fixes: `just7_else_V`, `just7_D_of_probe` → JustSlot; `ebot_D_of_probes_D` → SoundnessCells; tower-specific `describes_*` stay with their towers.

## Audit counts (Cells): DupocMirror 24, DIMCID 53, JustBot 37, JustSlot 68, SimSlot 3, CIMCIC 51, PrudentMirror 41, SearchFree 65, SoundnessCells 64, PositiveCells 64, FlipCells 36, KhatCells 48, DimcidFlips 49 = 603; Assembly Prep 23 / Family 13 / Cell 4 / Uniform 9. No Cells/Assembly lemma printed twice.

## Naming (FLIPPED 2026-09-27: the scheme is primary, the old names are deprecated aliases)

**Status.** The 2026-09-24 layer below made the scheme a set of aliases over the original names (the gate: every
original name and statement byte-identical). On 2026-09-27 the gate was relaxed and the flip executed: 166 declarations
renamed in their home files (the 169 `alias new := old` pairs of the layer = 163 distinct old names, six of them
doubled by a `*_finds_guards*` spelling, minus `dupoc_self_coop_unconditional` —
the headline theorem of `Necessitation/Package`, a Necessitation statement, NOT flipped, `loeb_Dupoc_vs_Dupoc` stays a
plain alias of it — plus the four non-scheme names of the newer floor modules: `dupoc_vs_botCB_found` →
`pos_DupocBot_vs_botCB`, `botDupoc_vs_botCB_found` → `pos_botDupocBot_vs_botCB`, `just_vs_botDB` →
`snd_JustBot_vs_botDB`, `dich_CupodBot_PrudentBot_core` → `dich_CupodBot_vs_PrudentBot_core`; `floor_*`/`dich_*` are
method prefixes in the scheme's spirit and use engine head symbols, as their statements have `pcode`); statements
byte-identical modulo the rename map (header diff: 0 changed); every use site and every `#print axioms` line of
`Audit.lean` updated (the census count unchanged); `Cells/Names.lean` is now the DEPRECATION layer —
`@[deprecated new (since := "2026-09-27")] alias old := new` for every pair (the six `*_finds_guards*` spellings of
the old layer that doubled a scheme name are kept as plain aliases). The survey paragraph below is the 2026-09-24
record and reads "old → new".

Inconsistencies: two worlds of codes (`Dimcid k = pcode (DIMCID k)` but `Dupoc ≠ pcode DupocBot`, `Cupod ≠ pcode CupodBot`, `Just ≠ pcode JustBot`) invisible in cell names; `Just/JustV` vs `Just7/JustV7`; `TftV` vs `TFTV`; `hopp_`/`hme_` mixed; `_search_V/_then_V/_frame_search_V/_search_any_V`; `_both_V/_all_V/_boxes_V`, `_guards_V` vs `pJJ_guard_V`; `find_guards`/`finds_guard`/`finds_guards`; `_vs_TFT` vs `_vs_TitForTatBot`, `_vs_Mirror` vs `_vs_mirror`; method prefixes not matching shape (`snd_` on eventually statements, `pos_Guardian*` in SoundnessCells, loose names `botDupoc_vs_botDB`, `dimcid_vs_*_defects`, …); `cimcic_self_coop` Löb-free without `_unconditional`; primed `pcode_X'`.
Scheme: `<method>_<L>_vs_<R>[_<suffix>]`, method ∈ {sf, pa, snd, pos, loeb, khat} = the PROOF METHOD; L/R = the exact head symbol (engine constructor when the statement has `pcode (X k)`, arith code name `Dupoc/Cupod/Dimcid/Cimcic/Just/Just7/Prudent/PrudentT/Mirror/botDupoc` when it has the ℕ-code); suffix ∈ {∅, `_guard`, `_guards`, `_guardOf`, `_notFound`, `_engine`, `_of_nec`, `_core_of_nec`}. Examples: `dupoc_mirror_coop_unconditional` → `loeb_Dupoc_vs_Mirror`; `dupoc_mirror_coop` → `loeb_Dupoc_vs_Mirror_of_nec`; `dimcid_cupod_find_guards_unconditional` → `loeb_Dimcid_vs_Cupod_guards`; `cimcic_self_coop` → `pos_Cimcic_vs_Cimcic`; `snd_CupodBot_vs_DBot` → `pos_CupodBot_vs_DBot`. Implementation: ONE module `Cells/Names.lean` importing all Cells files, containing only `alias <new> := <old>` lines (~31 `_unconditional` + `_of_nec`/`_core_of_nec` companions + ~15 loose cells + helper renames `hopp_*/hme_*` → `desc_*`, `hX_self` → `hX_dimcid`, `hX_bot` → `hX_botDupoc`, `pJJ_guard_V` → `pJJ_guards_V`, `pJD_boxes_V` → `pJD_guards_V`, `*_find_guards*` → `*_finds_guards*`, `pcode_X'` → `pcode_X_search`, `mirror_copies_V` → `mirror_copies2_V`; `TFTV`/`TTFT` re-defined as `TftV`/`TTft`); imported by `ArithS.lean`; no Audit prints needed for aliases. Flip primary/deprecated only after the gate is relaxed.
