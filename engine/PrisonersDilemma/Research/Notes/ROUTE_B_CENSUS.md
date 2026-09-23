# Route B — the cell census by proof mechanism (2026-09-23)

*Phase 0 deliverable of `ROUTE_B_SCOPE.md`. Every one of the 155 cells of
`app/generated/outcome_theorems.json` and the 4 companions, classified by the mechanism its ENGINE
proof uses, following lemma dependencies through the cell's file, all `Theorems/*/Helpers.lean`,
`LlmLemmas.lean`, imported `vs_*` files, `Base/Helpers.lean`, `Base/Closure.lean`, stopping at the base
machinery (`Loeb`, `Exclusion`, `BoundedGL`, `Soundness`, `ValuationSoundness`, `AtomCerts`, `Transpose`,
`ProofSystem`). Produced by a read-only agent pass with hand spot-checks (CIMCIC×CIMCIC, CIMCIC×Mirror,
CIMCIC×OBot, Dupoc×Cupod, Prudent×DBot, Wary×DefectBot, JustBot×CTB, Cupod×Prudent, the `k<n` cost
lemmas, `wv_budget_census`); the negative/positive split of lemmas is a regex on statements, so the
~100 non-trivial cells were NOT all hand-read — treat a single row as a first cut, the class counts as
reliable.*

## Classes

* **SF** — search-free: both players in {CooperateBot, DefectBot, MirrorBot, TitForTatBot, DBot, EBot, OBot}.
* **POS** — a searcher's guard is proved POSITIVELY (`search_t` atom, `weakenImpl`, `implRefl`, `simStep`,
  `atomNeg` proving a `.neg` guard), no Löb, no floor.
* **SND** — a searcher takes its else branch because its guard is SEMANTICALLY FALSE, closed at the Lean
  meta level by soundness (`proofSearch_sound`/`Pf_sound`). No floor, no census, no Löb; nothing is
  refuted inside the system. (Not in the original list; 36 cells.)
* **LOEB-FF / LOEB-FP** — a Löb engine (`pblt_engine`, `pblt_engine_id`, `mutual_pblt_engine_id`,
  `mutual_pblt_engine_staggered`, `bloeb_engine`), floor-free / floor-paying.
* **FLOOR** — `pay`: a `search_f`/`atomNeg`/`eqNeg`/`searchElseChain`/`atom_search_f_*` certificate is
  BUILT; `cen`: a floor-priced census (`no_provable_tailToS_floor`, `searcherElse`, `probeFirst`,
  `nested`, `searcherPlay`, `botSearcherElse`, the `k<n` cost lemmas, `wv_budget_census`); `cenU`: only
  `no_provable_tailTo_unreadable` — no budget, no floor cost, closed by a player being UNREADABLE by `S`.
* **OTHER** — a valuation-soundness census (`wv_sound_upto`, whole-system induction without budget), or
  `Pf.transpose` (the red cell).
* Precedence when several appear: Löb > OTHER > FLOOR > SND > POS > SF.

Facts: `bloeb_std` does not exist on this branch (it is the D-spike's, `colomban-boxcost`). No cell uses
`mutual_loeb`, `vector2_full_pblt_engine`, `pblt_engine_bounded`/`_id_bounded`, `loeb_premise_under_box`,
or `Pf.diagF`/`diagB` directly. A floor is actually PAID only in the 4 companions and the 3 OptimBot
LOEB-FP cells; every other floor use is a negative census. `searchThenSearch_t` (inner-premise citation):
Prudent×Mirror, Prudent×EBot, and the two Löbian companions. Nothing uses `botSysSearchThenSearch`.

## Counts (155 cells)

| class | cells | detail |
|---|---|---|
| SF | 28 | |
| POS | 14 | incl. CIMCIC×CIMCIC, CTB×Cupod (two searchers, both positive), Wary×DefectBot (`atomNeg`) |
| SND | 36 | |
| LOEB-FF | 29 | of which 15 are LegibleBot cells |
| LOEB-FP | 5 | Optim×DBot/DefectBot/TFT, Legible×DIMCID, Prudent×EBot |
| FLOOR | 38 | 6 are `cenU` (budget-free): CIMCIC×DBot, CIMCIC×EBot, CIMCIC×DefectBot, CIMCIC×OBot, DIMCID×CB, DIMCID×TFT |
| OTHER | 5 | DIMCID×CTB, Guardian×DIMCID, Dupoc×Cupod (red cell), Wary×Mirror, Wary×Wary |

Companions: CTB×Dupoc and Just×CTB FLOOR(pay); Just×Prudent and Prudent×Dupoc LOEB-FP(pay), both citing an
inner premise.

Per left bot: CIMCIC 15 (POS 4, LOEB-FF 2, FLOOR 9) · CooperateBot 2 (SF) · CupodBot 9 (SND 4, LOEB-FF 2,
POS 1, FLOOR 2) · CupodTrollBot 9 (SND 8, POS 1) · DBot 3 (SF) · DIMCID 13 (FLOOR 8, LOEB-FF 3, POS 1,
OTHER 1) · DefectBot 1 (SF) · DupocBot 10 (POS 2, SND 2, LOEB-FF 2, FLOOR 3, OTHER 1) · EBot 7 (SF) ·
GuardianBot 15 (SND 8, FLOOR 4, POS 2, OTHER 1) · JustBot 12 (LOEB-FF 3, POS 2, FLOOR 5, SND 2) ·
LegibleBot 16 (LOEB-FF 15, LOEB-FP 1) · MirrorBot 6 (SF) · OBot 5 (SF) · OptimBot 4 (LOEB-FF 1, LOEB-FP 3)
· PrudentBot 11 (SND 6, FLOOR 3, LOEB-FF 1, LOEB-FP 1) · TitForTatBot 4 (SF) · WaryBot 13 (FLOOR 4, SND 6,
POS 1, OTHER 2).

## What each class means in PA-`S'` (the reading `ROUTE_B_SCOPE.md` §2 now uses)

* **SF, POS**: unconditional. SF by `eval_iff_evalGraph` (search-free, no oracle); POS by
  Σ₁-completeness of the positive guard + instantiation fitting the budget for large `k`.
* **SND**: UNCONDITIONAL — the guard is false in ℕ, `TAct` is sound in ℕ, so NO proof of ANY length
  exists and the arithmetized evaluator takes the else branch; this is exactly the red cell's argument
  ("soundness of `TAct` in ℕ + the truth equation"), a LEAN-level fact, no PA proof of a negative
  needed. Not a floor. (The engine's `proofSearch_sound` and `S'`'s `TAct`-soundness play the same role.)
* **LOEB-FF**: unconditional via the family-parametric assembly (Phase 1/2); the 15 LegibleBot cells are
  excluded by coverage (`box_guard_never_fits`), leaving 14.
* **LOEB-FP**: the Löb premise consumes a floor — conditional on `BoundedReflection`; Optim (3) and
  Legible×DIMCID excluded by coverage, leaving Prudent×EBot and the two Löbian companions.
* **FLOOR(cen)**: a TRUE guard that is unprovable WITHIN THE BUDGET (Gödelian/cost floors, the
  `+k` else-play). In PA this is a proof-length LOWER bound — Pudlák territory (`k^ε` vs the engine's
  `+k`, roadmap danger 3); same-`k` cells may be open or FALSE in `S'`. Conditional or not claimed.
* **FLOOR(cenU), OTHER (WV censuses)**: negatives that rest on a player being UNREADABLE by `S`'s rules
  (no rule reads the source). PA reads every source for free (Σ₁-completeness), so these censuses DO
  NOT TRANSFER (roadmap §4) and the `S'` value of these cells may DIFFER from the engine's: to be
  re-evaluated cell by cell, expected to become either POS-like (the guard becomes provable) or a
  genuine FLOOR(cen). Six cenU cells + Wary×Mirror, Wary×Wary, DIMCID×CTB, Guardian×DIMCID.

## Open classification questions (recorded, not resolved)

1. Wary×DBot/DefectBot/EBot use `Pf.atomNeg` only to prove Wary's `.neg` guard positively (no failed
   budget charged): classed POS/SND. In `S'` a `.neg` guard `¬(plays …)` is a Π₁ atom — provable by
   PA-internal determinism of `EvalGraph` (the `atomNeg` leaf of T2-CORE, open) — WaryBot stays excluded.
2. The 6 cenU cells: classed FLOOR by the rule "every `no_provable_*`", but their content is
   unreadability, see above.
3. SND cells may leave an outer guard undecided (`by_cases`, e.g. Prudent×DBot): irrelevant in the
   engine, RELEVANT in `S'` where the outcome needs both branches evaluated — check per cell.

## The table

| name | left | right | pair | regime | class | engines | floor lemmas | cites-inner | notes |
|---|---|---|---|---|---|---|---|---|---|
| llm_outcome_CIMCIC_vs_CIMCIC | CIMCIC | CIMCIC | CC | eventual | POS | - | - | no | both guards fire by `Pf.implRefl` (A→A); two searchers, no Löb |
| llm_outcome_CIMCIC_vs_CupodTrollBot | CIMCIC | CupodTrollBot | DC | eventual | FLOOR(cen) | - | no_provable_tailToS_floor (cimcic_ctb_guard_unprovable_tail) | no | CTB side SND (proofSearch_false_for_not_CupodBot) |
| llm_outcome_CIMCIC_vs_DBot | CIMCIC | DBot | DC | eventual | FLOOR(cenU) | - | no_provable_tailTo_unreadable (cimcic_bot_no_provable_forbidden, dbot_no_provable_forbidden) | no | budget-free; dbot_C_cert_impossible kills the search_f arm by Pf_sound |
| llm_outcome_CIMCIC_vs_DIMCID | CIMCIC | DIMCID | DC | eventual | FLOOR(cen) | - | no_provable_tailToS_floor (cd_no_provable_alpha/beta) | no | census on both guards |
| llm_outcome_CIMCIC_vs_DupocBot | CIMCIC | DupocBot | CC | eventual | LOEB-FF | mutual_pblt_engine_id | - | no | |
| llm_outcome_CIMCIC_vs_EBot | CIMCIC | EBot | DC | eventual | FLOOR(cenU) | - | no_provable_tailTo_unreadable (cimcic_botDef_…, ebot_no_provable_forbidden) | no | CIMCIC vs botCoop guard positive (weakenImpl); SND parts |
| llm_outcome_CIMCIC_vs_JustBot | CIMCIC | JustBot | CC | eventual | LOEB-FF | mutual_pblt_engine_id (cj_CIMCIC_C_vs_botDupoc) | - | no | |
| llm_outcome_CIMCIC_vs_MirrorBot | CIMCIC | MirrorBot | CC | eventual | POS | - | - | no | guard by `Pf.simStep` |
| llm_outcome_CIMCIC_vs_OptimBot | CIMCIC | OptimBot | DC | eventual | FLOOR(cen) | - | no_provable_tailToS_floor (cimcic_optim_G3_unprov, cimcic_optim_guard_B_unprov); cost lemma optim_C_cert_cost | no | + Pf_sound for guard A |
| llm_outcome_CIMCIC_vs_PrudentBot | CIMCIC | PrudentBot | DD | eventual | FLOOR(cen) | - | no_provable_tailToS_floor (cimcic_pb_prudence_unprovable_tail) | no | CIMCIC guard false by Pf_sound |
| llm_outcome_CIMCIC_vs_TitForTatBot | CIMCIC | TitForTatBot | CC | eventual | POS | - | - | no | weakenImpl + search-free TFT atom |
| llm_outcome_DIMCID_vs_CupodTrollBot | DIMCID | CupodTrollBot | CC | eventual | OTHER | - | - | no | WV census (pf_WV via wv_sound_upto); CTB SND |
| llm_outcome_DIMCID_vs_DBot | DIMCID | DBot | CC | eventual | FLOOR(cen) | - | no_provable_tailToS_floor (dimcid_guard_dbot_not_provable) | no | DIMCID vs botDB positive (weakenImpl) |
| llm_outcome_DIMCID_vs_DIMCID | DIMCID | DIMCID | DD | eventual | LOEB-FF | pblt_engine (+boxIntro, axK in dimcid_loeb_premise) | - | no | |
| llm_outcome_DIMCID_vs_EBot | DIMCID | EBot | CC | eventual | FLOOR(cen+cenU) | - | no_provable_tailToS_floor (de_ebot_guard_not_provable); no_provable_tailTo_unreadable (de_botcoop_…) | no | + SND, positive weakenImpl |
| llm_outcome_DIMCID_vs_JustBot | DIMCID | JustBot | CD | eventual | FLOOR(cen) | - | no_provable_tailToS_floor (dj_no_provable_dimcidC, dj_no_provable_justbotD) | no | |
| llm_outcome_DIMCID_vs_MirrorBot | DIMCID | MirrorBot | DD | eventual | LOEB-FF | pblt_engine (+boxIntro, axK) | - | no | |
| llm_outcome_DIMCID_vs_OBot | DIMCID | OBot | CD | eventual | FLOOR(cen+cenU) | - | no_provable_probeFirst_tail (dimcidOb_no_provable_OBot_D_tail); no_provable_tailTo_unreadable | no | + SND |
| llm_outcome_DIMCID_vs_PrudentBot | DIMCID | PrudentBot | CD | eventual | FLOOR(cen) | - | no_provable_tailToS_floor (dp_no_provable_dimcidC, dp_no_provable_pbD) | no | |
| llm_outcome_DIMCID_vs_TitForTatBot | DIMCID | TitForTatBot | CC | eventual | FLOOR(cenU) | - | no_provable_tailTo_unreadable (dimcidTFT_no_provable_TFT/_botCoop) | no | budget-free |
| llm_outcome_GuardianBot_vs_CIMCIC | GuardianBot | CIMCIC | CD | eventual | FLOOR(cen) | - | no_provable_tailToS_floor (gc_no_provable_tail) | no | CIMCIC cannot certify Guardian's else-C; Guardian guard SND |
| llm_outcome_GuardianBot_vs_CupodBot | GuardianBot | CupodBot | CC | eventual | SND | - | - | no | both guards false by soundness |
| llm_outcome_GuardianBot_vs_CupodTrollBot | GuardianBot | CupodTrollBot | CC | eventual | SND | - | - | no | |
| llm_outcome_GuardianBot_vs_DBot | GuardianBot | DBot | DC | eventual | POS | - | - | no | search-free atom (decide) |
| llm_outcome_GuardianBot_vs_DIMCID | GuardianBot | DIMCID | CC | eventual | OTHER | - | no_provable_tailTo_unreadable (gd_dimcid_botCB_guard_not_provable) | no | WV census gd_pf_WV (search_f appears only as a WV case arm); Guardian SND |
| llm_outcome_GuardianBot_vs_DupocBot | GuardianBot | DupocBot | CD | eventual | FLOOR(cen) | - | no_provable_tailToS_floor (gd_no_provable_C_tail) | no | Guardian SND |
| llm_outcome_GuardianBot_vs_EBot | GuardianBot | EBot | DC | eventual | SND | - | - | no | positive part via atom_complete_searchfree |
| llm_outcome_GuardianBot_vs_GuardianBot | GuardianBot | GuardianBot | CC | eventual | SND | - | - | no | no fixpoint; guard refuted semantically |
| llm_outcome_GuardianBot_vs_JustBot | GuardianBot | JustBot | CD | eventual | FLOOR(cen) | - | no_provable_tailToS_floor (gjb_no_provable_Guardian_C_vs_botDupoc) | no | Guardian SND |
| llm_outcome_GuardianBot_vs_OBot | GuardianBot | OBot | CD | eventual | SND | - | - | no | + positive atom |
| llm_outcome_GuardianBot_vs_PrudentBot | GuardianBot | PrudentBot | CD | eventual | FLOOR(cen) | - | no_provable_tailToS_floor (gvp_no_Pf_prudent_D, pvg_no_Pf_guardian_C; atom-kill lemmas gvp_/pvg_…_atom_kill) | no | |
| llm_outcome_GuardianBot_vs_TitForTatBot | GuardianBot | TitForTatBot | CC | eventual | SND | - | - | no | |
| llm_outcome_JustBot_vs_MirrorBot | JustBot | MirrorBot | CC | eventual | LOEB-FF | pblt_engine_id (jm_guard_true) | - | no | |
| llm_outcome_LegibleBot_vs_CupodBot | LegibleBot | CupodBot | CC | eventual, stag | LOEB-FF | pblt_engine (LegibleBot_cooperates_Pf; +box4) | - | no | Cupod SND |
| llm_outcome_LegibleBot_vs_DupocBot | LegibleBot | DupocBot | CC | eventual, stag | LOEB-FF | pblt_engine (+box4) | - | no | Dupoc guard positive (search_t atom) |
| llm_outcome_LegibleBot_vs_GuardianBot | LegibleBot | GuardianBot | CC | eventual, stag | LOEB-FF | pblt_engine (+box4) | - | no | Guardian SND |
| llm_outcome_LegibleBot_vs_JustBot | LegibleBot | JustBot | CC | eventual, stag | LOEB-FF | pblt_engine (+box4) | - | no | |
| llm_outcome_LegibleBot_vs_PrudentBot | LegibleBot | PrudentBot | CD | eventual, stag | LOEB-FF | pblt_engine (+box4) | - | no | prudence SND |
| llm_outcome_OptimBot_vs_CooperateBot | OptimBot | CooperateBot | DC | eventual | LOEB-FF | bloeb_engine (+boxIntro, boxMono) | - | no | rung 1 fires, searchChain |
| llm_outcome_OptimBot_vs_DBot | OptimBot | DBot | CC | eventual, stag | LOEB-FP | bloeb_engine (+boxIntro) | pay: atomNeg, searchElseChain (optim_dbot_selfD_loeb); cen: no_provable_DBot_C_vs_optim (probeFirst) | no | + SND |
| llm_outcome_OptimBot_vs_DefectBot | OptimBot | DefectBot | DD | eventual, stag | LOEB-FP | bloeb_engine (+boxIntro, boxMono) | pay: atomNeg, searchElseChain (od_loeb_premise) | no | + SND |
| llm_outcome_OptimBot_vs_TitForTatBot | OptimBot | TitForTatBot | DD | eventual, stag | LOEB-FP | bloeb_engine ×2 (ot_D_provable_at_stagger, ot_inner_D_at_stagger) | pay: atomNeg, searchElseChain (ot_loeb_premise) | no | + SND |
| llm_outcome_WaryBot_vs_DupocBot | WaryBot | DupocBot | CD | eventual | FLOOR(cen) | - | no_provable_tailToS_floor (wd_no_provable_A_tail); wv_budget_census; cost SPDupoc_no_D_cert | no | Löb/inner rules appear only as census case arms |
| llm_outcome_WaryBot_vs_GuardianBot | WaryBot | GuardianBot | CC | eventual | SND | - | - | no | |
| llm_outcome_WaryBot_vs_JustBot | WaryBot | JustBot | CD | eventual | FLOOR(cen) | - | no_provable_tailToS_floor (wj_no_provable_A_tail); wv_budget_census; cost SPJust_no_D_cert | no | |
| llm_outcome_WaryBot_vs_OptimBot | WaryBot | OptimBot | CC | eventual | FLOOR(cen) | - | no_provable_tailToS_floor (wo_wary_C_vs_optim_unprov); wv_budget_census; cost wo_optim_noD, wo_wary_C_cert_cost | no | |
| llm_outcome_WaryBot_vs_PrudentBot | WaryBot | PrudentBot | CD | eventual | FLOOR(cen) | - | no_provable_tailToS_floor (waryPrudent_no_provable_C_tail); wv_budget_census; waryPrudent_prudent_noD_floor, waryPrudentCensus_noD_floor | no | |
| outcome_CIMCIC_vs_CooperateBot | CIMCIC | CooperateBot | CC | eventual | POS | - | - | no | weakenImpl |
| outcome_CIMCIC_vs_CupodBot | CIMCIC | CupodBot | DC | universal | FLOOR(cen) | - | no_provable_CupodBot_C_tail→no_provable_searcherElse_tail; no_provable_tailToS_floor (cb_no_provable_cimcic_D_tail) | no | |
| outcome_CIMCIC_vs_DefectBot | CIMCIC | DefectBot | DD | universal | FLOOR(cenU) | - | no_provable_tailTo_unreadable (cimcic_no_provable_forbidden) | no | Gödelian true-but-unprovable guard |
| outcome_CIMCIC_vs_OBot | CIMCIC | OBot | DD | eventual | FLOOR(cenU) | - | no_provable_tailTo_unreadable (via CIMCIC/vs_EBot: CIMCIC_plays_D_against_botDef) | no | own guard false by Pf_sound; weakenImpl positive |
| outcome_CooperateBot_vs_CooperateBot | CooperateBot | CooperateBot | CC | nobudget | SF | - | - | no | rfl |
| outcome_CooperateBot_vs_DefectBot | CooperateBot | DefectBot | CD | nobudget | SF | - | - | no | rfl |
| outcome_CupodBot_vs_CooperateBot | CupodBot | CooperateBot | CC | universal | SND | - | - | no | |
| outcome_CupodBot_vs_CupodBot | CupodBot | CupodBot | DD | eventual | LOEB-FF | pblt_engine_id | - | no | |
| outcome_CupodBot_vs_DBot | CupodBot | DBot | CC | eventual | SND | - | - | no | |
| outcome_CupodBot_vs_DefectBot | CupodBot | DefectBot | DD | eventual | POS | - | - | no | DB atom |
| outcome_CupodBot_vs_EBot | CupodBot | EBot | CC | eventual | SND | - | - | no | |
| outcome_CupodBot_vs_MirrorBot | CupodBot | MirrorBot | DD | eventual | LOEB-FF | pblt_engine_id | - | no | |
| outcome_CupodBot_vs_OBot | CupodBot | OBot | CD | eventual | FLOOR(cen) | - | no_provable_OBot_D_tail→no_provable_probeFirst_tail | no | + SND |
| outcome_CupodBot_vs_PrudentBot | CupodBot | PrudentBot | CD | universal | FLOOR(cen) | - | no_provable_CupodBot_C_tail (searcherElse); no_provable_PrudentBot_D_tail (nestedSearcher_D) | no | one-liner citing PrudentBot/vs_CupodBot |
| outcome_CupodBot_vs_TitForTatBot | CupodBot | TitForTatBot | CC | universal | SND | - | - | no | |
| outcome_CupodTrollBot_vs_CooperateBot | CupodTrollBot | CooperateBot | CC | universal | SND | - | - | no | .eq guard false |
| outcome_CupodTrollBot_vs_CupodBot | CupodTrollBot | CupodBot | DD | eventual | POS | - | - | no | two searchers, both positive (eqRefl; search_t atom) |
| outcome_CupodTrollBot_vs_CupodTrollBot | CupodTrollBot | CupodTrollBot | CC | universal | SND | - | - | no | |
| outcome_CupodTrollBot_vs_DBot | CupodTrollBot | DBot | CD | universal | SND | - | - | no | |
| outcome_CupodTrollBot_vs_DefectBot | CupodTrollBot | DefectBot | CD | universal | SND | - | - | no | |
| outcome_CupodTrollBot_vs_EBot | CupodTrollBot | EBot | CD | universal | SND | - | - | no | |
| outcome_CupodTrollBot_vs_MirrorBot | CupodTrollBot | MirrorBot | CC | universal | SND | - | - | no | |
| outcome_CupodTrollBot_vs_OBot | CupodTrollBot | OBot | CC | universal | SND | - | - | no | |
| outcome_CupodTrollBot_vs_TitForTatBot | CupodTrollBot | TitForTatBot | CC | universal | SND | - | - | no | |
| outcome_DBot_vs_CooperateBot | DBot | CooperateBot | DC | nobudget | SF | - | - | no | decide |
| outcome_DBot_vs_DBot | DBot | DBot | DD | nobudget | SF | - | - | no | |
| outcome_DBot_vs_DefectBot | DBot | DefectBot | CD | nobudget | SF | - | - | no | decide |
| outcome_DIMCID_vs_CooperateBot | DIMCID | CooperateBot | CC | universal | FLOOR(cenU) | - | no_provable_tailTo_unreadable (dimcid_no_provable_forbidden) | no | |
| outcome_DIMCID_vs_CupodBot | DIMCID | CupodBot | DD | eventual | LOEB-FF | mutual_pblt_engine_id (dc_mutual) | - | no | |
| outcome_DIMCID_vs_DefectBot | DIMCID | DefectBot | DD | eventual | POS | - | - | no | weakenImpl |
| outcome_DIMCID_vs_DupocBot | DIMCID | DupocBot | CD | universal | FLOOR(cen) | - | no_provable_DIMCID_C_tail, no_provable_DupocBot_D_tail (searcherElse) | no | |
| outcome_DefectBot_vs_DefectBot | DefectBot | DefectBot | DD | nobudget | SF | - | - | no | |
| outcome_DupocBot_vs_CooperateBot | DupocBot | CooperateBot | CC | eventual | POS | - | - | no | CB atom |
| outcome_DupocBot_vs_CupodBot | DupocBot | CupodBot | DC | universal | OTHER | - | - | no | Pf.transpose + Pf_sound (not_Pf_dupoc_guard); "red cell", no census |
| outcome_DupocBot_vs_CupodTrollBot | DupocBot | CupodTrollBot | DC | universal | FLOOR(cen) | - | no_provable_searcherElse_tail (proofSearch_false_CupodTrollBot_C) | no | CTB SND |
| outcome_DupocBot_vs_DBot | DupocBot | DBot | DC | universal | FLOOR(cen) | - | no_provable_DBot_C_tail→probeFirst_tail | no | + SND |
| outcome_DupocBot_vs_DefectBot | DupocBot | DefectBot | DD | universal | SND | - | - | no | |
| outcome_DupocBot_vs_DupocBot | DupocBot | DupocBot | CC | eventual | LOEB-FF | pblt_engine_id | - | no | |
| outcome_DupocBot_vs_EBot | DupocBot | EBot | DC | eventual | FLOOR(cen) | - | no_provable_EBot_C_tail→probeFirst_tail | no | + SND |
| outcome_DupocBot_vs_MirrorBot | DupocBot | MirrorBot | CC | eventual | LOEB-FF | pblt_engine_id | - | no | |
| outcome_DupocBot_vs_OBot | DupocBot | OBot | DD | eventual | SND | - | - | no | + positive atom |
| outcome_DupocBot_vs_TitForTatBot | DupocBot | TitForTatBot | CC | eventual | POS | - | - | no | TFT probes .bot CB, search-free |
| outcome_EBot_vs_CooperateBot | EBot | CooperateBot | DC | nobudget | SF | - | - | no | decide |
| outcome_EBot_vs_DBot | EBot | DBot | DC | nobudget | SF | - | - | no | decide |
| outcome_EBot_vs_DefectBot | EBot | DefectBot | DD | nobudget | SF | - | - | no | |
| outcome_EBot_vs_EBot | EBot | EBot | CC | nobudget | SF | - | - | no | |
| outcome_EBot_vs_MirrorBot | EBot | MirrorBot | CC | nobudget | SF | - | - | no | |
| outcome_EBot_vs_OBot | EBot | OBot | CD | nobudget | SF | - | - | no | |
| outcome_EBot_vs_TitForTatBot | EBot | TitForTatBot | CD | nobudget | SF | - | - | no | decide |
| outcome_GuardianBot_vs_CooperateBot | GuardianBot | CooperateBot | CC | universal | SND | - | - | no | |
| outcome_GuardianBot_vs_DefectBot | GuardianBot | DefectBot | DD | eventual | POS | - | - | no | DB atom |
| outcome_GuardianBot_vs_MirrorBot | GuardianBot | MirrorBot | CC | universal | SND | - | - | no | |
| outcome_JustBot_vs_CooperateBot | JustBot | CooperateBot | CC | eventual | POS | - | - | no | CB atom |
| outcome_JustBot_vs_CupodBot | JustBot | CupodBot | DC | universal | FLOOR(cen) | - | no_provable_CupodBot_C_tail, no_provable_JustBot_D_tail (searcherElse) | no | |
| outcome_JustBot_vs_CupodTrollBot | JustBot | CupodTrollBot | DC | universal | FLOOR(cen) | - | no_provable_searcherElse_tail (via DupocBot/vs_CupodTrollBot) | no | CTB SND |
| outcome_JustBot_vs_DBot | JustBot | DBot | DC | universal | FLOOR(cen) | - | no_provable_DBot_C_vs_botDupoc_tail→probeFirst_tail_botOpp | no | + SND |
| outcome_JustBot_vs_DefectBot | JustBot | DefectBot | DD | universal | SND | - | - | no | |
| outcome_JustBot_vs_DupocBot | JustBot | DupocBot | CC | eventual | LOEB-FF | mutual_pblt_engine_id | - | no | |
| outcome_JustBot_vs_EBot | JustBot | EBot | DC | eventual | FLOOR(cen) | - | no_provable_EBot_C_vs_botDupoc_tail→probeFirst_tail_botOpp | no | + SND |
| outcome_JustBot_vs_JustBot | JustBot | JustBot | CC | eventual | LOEB-FF | pblt_engine_id (botDupoc_self_coop) | - | no | |
| outcome_JustBot_vs_OBot | JustBot | OBot | DD | eventual | SND | - | - | no | + positive atom |
| outcome_JustBot_vs_PrudentBot | JustBot | PrudentBot | DD | universal | FLOOR(cen) | - | no_provable_botSearcherElse_tail (proofSearch_false_botDupoc_D_vs_bot_DefectBot) | no | + SND |
| outcome_JustBot_vs_TitForTatBot | JustBot | TitForTatBot | CC | eventual | POS | - | - | no | |
| outcome_LegibleBot_vs_CIMCIC | LegibleBot | CIMCIC | CC | eventual, stag | LOEB-FF | pblt_engine (+box4) | - | no | CIMCIC positive via weakenImpl |
| outcome_LegibleBot_vs_CooperateBot | LegibleBot | CooperateBot | CC | eventual, stag | LOEB-FF | pblt_engine (+box4) | - | no | |
| outcome_LegibleBot_vs_CupodTrollBot | LegibleBot | CupodTrollBot | CC | eventual, stag | LOEB-FF | pblt_engine (+box4) | - | no | CTB SND |
| outcome_LegibleBot_vs_DBot | LegibleBot | DBot | CD | eventual, stag | LOEB-FF | pblt_engine (+box4) | - | no | |
| outcome_LegibleBot_vs_DIMCID | LegibleBot | DIMCID | CC | eventual, stag | LOEB-FP | pblt_engine (+box4) | no_provable_tailToS_floor (ld_no_provable_tail) | no | floor is census on DIMCID's guard |
| outcome_LegibleBot_vs_DefectBot | LegibleBot | DefectBot | CD | eventual, stag | LOEB-FF | pblt_engine (+box4) | - | no | |
| outcome_LegibleBot_vs_EBot | LegibleBot | EBot | CD | eventual, stag | LOEB-FF | pblt_engine (+box4) | - | no | |
| outcome_LegibleBot_vs_LegibleBot | LegibleBot | LegibleBot | CC | eventual, stag | LOEB-FF | pblt_engine (+box4) | - | no | |
| outcome_LegibleBot_vs_MirrorBot | LegibleBot | MirrorBot | CC | eventual, stag | LOEB-FF | pblt_engine (+box4) | - | no | |
| outcome_LegibleBot_vs_OBot | LegibleBot | OBot | CC | eventual, stag | LOEB-FF | pblt_engine (+box4) | - | no | |
| outcome_LegibleBot_vs_TitForTatBot | LegibleBot | TitForTatBot | CC | eventual, stag | LOEB-FF | pblt_engine (+box4) | - | no | |
| outcome_MirrorBot_vs_CooperateBot | MirrorBot | CooperateBot | CC | nobudget | SF | - | - | no | |
| outcome_MirrorBot_vs_DBot | MirrorBot | DBot | CC | nobudget | SF | - | - | no | |
| outcome_MirrorBot_vs_DefectBot | MirrorBot | DefectBot | DD | nobudget | SF | - | - | no | |
| outcome_MirrorBot_vs_MirrorBot | MirrorBot | MirrorBot | none | nobudget | SF | - | - | no | non-termination |
| outcome_MirrorBot_vs_OBot | MirrorBot | OBot | DD | nobudget | SF | - | - | no | |
| outcome_MirrorBot_vs_TitForTatBot | MirrorBot | TitForTatBot | CC | nobudget | SF | - | - | no | |
| outcome_OBot_vs_CooperateBot | OBot | CooperateBot | CC | nobudget | SF | - | - | no | decide |
| outcome_OBot_vs_DBot | OBot | DBot | DC | nobudget | SF | - | - | no | decide |
| outcome_OBot_vs_DefectBot | OBot | DefectBot | DD | nobudget | SF | - | - | no | |
| outcome_OBot_vs_OBot | OBot | OBot | DD | nobudget | SF | - | - | no | |
| outcome_OBot_vs_TitForTatBot | OBot | TitForTatBot | DC | nobudget | SF | - | - | no | decide |
| outcome_PrudentBot_vs_CooperateBot | PrudentBot | CooperateBot | DC | universal | SND | - | - | no | prudence false |
| outcome_PrudentBot_vs_CupodBot | PrudentBot | CupodBot | DC | universal | FLOOR(cen) | - | no_provable_PrudentBot_D_tail (nestedSearcher_D), no_provable_CupodBot_C_tail (searcherElse) | no | |
| outcome_PrudentBot_vs_CupodTrollBot | PrudentBot | CupodTrollBot | DC | eventual | SND | - | - | no | |
| outcome_PrudentBot_vs_DBot | PrudentBot | DBot | DC | eventual | SND | - | - | no | outer guard left undecided (by_cases); inner false by soundness |
| outcome_PrudentBot_vs_DefectBot | PrudentBot | DefectBot | DD | universal | SND | - | - | no | |
| outcome_PrudentBot_vs_DupocBot | PrudentBot | DupocBot | DD | universal | FLOOR(cen) | - | no_provable_searcherElse_tail (proofSearch_false_DupocBot_D_vs_bot_DefectBot) | no | + SND |
| outcome_PrudentBot_vs_EBot | PrudentBot | EBot | DC | eventual | LOEB-FP | pblt_engine_id (prudent_botmirror_coop) | no_provable_EBot_C_vs_Prudent_tail→probeFirst_tail | yes (searchThenSearch_t in prudent_bot_mirror_loeb_premise) | + SND |
| outcome_PrudentBot_vs_MirrorBot | PrudentBot | MirrorBot | CC | eventual | LOEB-FF | pblt_engine_id | - | yes (searchThenSearch_t in prudent_mirror_loeb_premise) | prudence atom search-free |
| outcome_PrudentBot_vs_OBot | PrudentBot | OBot | DD | eventual | SND | - | - | no | |
| outcome_PrudentBot_vs_PrudentBot | PrudentBot | PrudentBot | DD | universal | FLOOR(cen) | - | no_provable_prudence_self_tail→no_provable_searcherPlay_tail | no | |
| outcome_PrudentBot_vs_TitForTatBot | PrudentBot | TitForTatBot | DD | eventual | SND | - | - | no | |
| outcome_TitForTatBot_vs_CooperateBot | TitForTatBot | CooperateBot | CC | nobudget | SF | - | - | no | decide |
| outcome_TitForTatBot_vs_DBot | TitForTatBot | DBot | DC | nobudget | SF | - | - | no | decide |
| outcome_TitForTatBot_vs_DefectBot | TitForTatBot | DefectBot | DD | nobudget | SF | - | - | no | decide |
| outcome_TitForTatBot_vs_TitForTatBot | TitForTatBot | TitForTatBot | CC | nobudget | SF | - | - | no | decide |
| outcome_WaryBot_vs_CooperateBot | WaryBot | CooperateBot | CC | universal | SND | - | - | no | |
| outcome_WaryBot_vs_CupodTrollBot | WaryBot | CupodTrollBot | CC | universal | SND | - | - | no | |
| outcome_WaryBot_vs_DBot | WaryBot | DBot | CC | eventual | SND | - | atomNeg (positive guard proof, no floor) | no | Wary vs .bot DB fires via Pf.atomNeg; outer guard SND |
| outcome_WaryBot_vs_DefectBot | WaryBot | DefectBot | DD | eventual | POS | - | atomNeg (positive guard proof, no floor) | no | guard ¬(DB plays C) proved by Pf.atomNeg |
| outcome_WaryBot_vs_EBot | WaryBot | EBot | CC | eventual | SND | - | atomNeg (positive guard proof, no floor) | no | as vs DBot |
| outcome_WaryBot_vs_MirrorBot | WaryBot | MirrorBot | CC | universal | OTHER | - | - | no | WV census pf_WV_mirror (wv_sound_upto) |
| outcome_WaryBot_vs_TitForTatBot | WaryBot | TitForTatBot | CC | universal | SND | - | - | no | |
| outcome_WaryBot_vs_WaryBot | WaryBot | WaryBot | CC | universal | OTHER | - | - | no | WV census pf_WV_self |
| COMP outcome_CupodTrollBot_vs_DupocBot_staggered | CupodTrollBot | DupocBot | CC | eventual, stag | FLOOR(pay) | - | search_f + eqNeg (CupodTrollBot_vs_DupocBot_above_floor, DupocBot_plays_C_against_CupodTrollBot) | no | Dupoc pays Troll's floor at a larger budget |
| COMP outcome_JustBot_vs_CupodTrollBot_staggered | JustBot | CupodTrollBot | CC | universal, stag | FLOOR(pay) | - | PlaysProof.search_f + Pf.eqNeg (in the cell body) | no | |
| COMP outcome_JustBot_vs_PrudentBot_staggered | JustBot | PrudentBot | CC | eventual, stag | LOEB-FP(pay) | mutual_pblt_engine_staggered | atomNeg (neg_botDefect_C_vs_botDupoc), atom_search_f_top (justbot_prudence), atom_search_f_bot_top (prudence_botdupoc) | yes (prudent_botdupoc_legPD) | |
| COMP outcome_PrudentBot_vs_DupocBot_staggered | PrudentBot | DupocBot | CC | eventual, stag | LOEB-FP(pay) | mutual_pblt_engine_staggered | atomNeg + atom_search_f_top (prudence_dupoc) | yes (prudent_dupoc_legPD) | |
