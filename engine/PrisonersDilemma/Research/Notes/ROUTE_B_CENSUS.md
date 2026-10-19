# ROUTE_B_CENSUS — the cell ledger of PA-`S'`

*One row per engine cell: the engine's value, the `S'` value (`—` = no `S'` statement), the `S'` class and the
theorem that states it (`arith/ArithS/Cells/`; the engine-vocabulary form is `outcome_<L>_vs_<R>` in
`arith/ArithS/Outcome/Matrix/<L>.lean`; since 2026-10-02 every one of the 107 is stated on the engine's own
`progCode` — the last seven hand-template twin cells were re-proved in `Cells/JustEngine.lean` and
`Cells/CupodTrollEngine.lean`). Script-exact over the 155 cells of
`app/generated/outcome_theorems.json`. The engine-mechanism classification of every cell (how the ENGINE proves
it: Löb engine, floor lemma, census) and the classification method are in git before `c0aa163`.*

## Classes

* **SF** — search-free: transfer at the engine's own fuel.
* **SND** — a searcher's guard is FALSE in ℕ, so never found (soundness); the else branch plays.
* **POS** — the guard is `TAct`-provable (completeness); its `k`-instance fits for large `k`. No Löb.
* **LOEB** — bounded Löb (`family_found`, `BoundedInnerNec 16`).
* **FLIP** — stated in `S'` with a value that CONTRADICTS the engine (all on a self-fulfilling negative guard).
* **GENUINE-FLOOR** — a true guard whose provability within `k` is bounded consistency at `k` (Pudlák); no `S'`
  value; the hypothesis-free dichotomy `dich_<L>_vs_<R>` is the theorem.
* **EXCLUDED** — LegibleBot, OptimBot (boxes inside guards), WaryBot's two floor cells.

## Counts

155 = 28 SF + 39 SND + 13 POS + 14 LOEB + 13 FLIP + 26 GENUINE-FLOOR + 22 EXCLUDED.
**Stated: 107. Agree with the engine: 94. Disagree: 13.**

## The table

| cell | engine | `S'` | `S'` class | theorem or reason |
|---|---|---|---|---|
| llm_outcome_CIMCIC_vs_CIMCIC | (C, C) | (C, C) | POS | pos_Cimcic_vs_Cimcic |
| llm_outcome_CIMCIC_vs_CupodTrollBot | (D, C) | — | GENUINE-FLOOR | CIMCIC's guard TRUE (consequent = CupodTroll's else-play). Settled: `floor_CIMCIC_vs_CupodTrollBot_right`, `_true` — dichotomy: `dich_CIMCIC_vs_CupodTrollBot` |
| llm_outcome_CIMCIC_vs_DBot | (D, C) | — | GENUINE-FLOOR | cenU; CIMCIC's guard TRUE (DBot cooperates: CIMCIC's self-refuting else-play vs `.bot DefectBot`). Settled: `floor_CIMCIC_vs_DBot_right`, `_true` — dichotomy: `dich_CIMCIC_vs_DBot` |
| llm_outcome_CIMCIC_vs_DIMCID | (D, C) | (D, D) | FLIP | loeb_CIMCIC_vs_DIMCID |
| llm_outcome_CIMCIC_vs_DupocBot | (C, C) | (C, C) | LOEB | loeb_CIMCIC_vs_DupocBot (`Cells/CimcicEngine`; the hand-twin form is `loeb_Cimcic_vs_Dupoc`) |
| llm_outcome_CIMCIC_vs_EBot | (D, C) | — | GENUINE-FLOOR | cenU; CIMCIC's guard TRUE (EBot's rung 1 = CIMCIC's else-play vs `.bot DefectBot`). Settled: `floor_CIMCIC_vs_EBot_right`, `_true` — dichotomy: `dich_CIMCIC_vs_EBot` |
| llm_outcome_CIMCIC_vs_JustBot | (C, C) | (C, C) | LOEB | loeb_CIMCIC_vs_JustBot (`Cells/JustEngine`; the hand-twin form is `loeb_Cimcic_vs_Just7`) |
| llm_outcome_CIMCIC_vs_MirrorBot | (C, C) | (C, C) | LOEB | loeb_Cimcic_vs_Mirror |
| llm_outcome_CIMCIC_vs_OptimBot | (D, C) | — | EXCLUDED | OptimBot/LegibleBot out of coverage |
| llm_outcome_CIMCIC_vs_PrudentBot | (D, D) | — | GENUINE-FLOOR | prudence guard TRUE via CIMCIC's self-refuting else-play — `floor_CIMCIC_vs_PrudentBot_true`; if not found CIMCIC's guard is self-refuting ⇒ `(D, D)` — dichotomy: `dich_CIMCIC_vs_PrudentBot` (prudence hinge `B` NOT dischargeable: an else-branch defection, `B_k` is itself a bounded-consistency-type sentence — `Cells/PrudentLoose`) |
| llm_outcome_CIMCIC_vs_TitForTatBot | (C, C) | (C, C) | POS | khat_CIMCIC_vs_TitForTatBot |
| llm_outcome_DIMCID_vs_CupodTrollBot | (C, C) | (D, C) | FLIP | loeb_DIMCID_vs_CupodTrollBot_engine (`Cells/CupodTrollEngine`; the hand-twin form, on `CupodTroll7 k`, is `loeb_DIMCID_vs_CupodTrollBot`) |
| llm_outcome_DIMCID_vs_DBot | (C, C) | (D, C) | FLIP | loeb_DIMCID_vs_DBot |
| llm_outcome_DIMCID_vs_DIMCID | (D, D) | (D, D) | LOEB | loeb_Dimcid_vs_Dimcid |
| llm_outcome_DIMCID_vs_EBot | (C, C) | (D, D) | FLIP | loeb_DIMCID_vs_EBot |
| llm_outcome_DIMCID_vs_JustBot | (C, D) | (D, D) | FLIP | loeb_DIMCID_vs_JustBot_engine (`Cells/JustEngine`; the hand-twin form, on `Just7 k`, is `loeb_DIMCID_vs_JustBot`) |
| llm_outcome_DIMCID_vs_MirrorBot | (D, D) | (D, D) | LOEB | loeb_Dimcid_vs_Mirror |
| llm_outcome_DIMCID_vs_OBot | (C, D) | (D, D) | FLIP | loeb_DIMCID_vs_OBot |
| llm_outcome_DIMCID_vs_PrudentBot | (C, D) | (D, D) | FLIP | loeb_DIMCID_vs_PrudentBot |
| llm_outcome_DIMCID_vs_TitForTatBot | (C, C) | (D, D) | FLIP | loeb_DIMCID_vs_TitForTatBot |
| llm_outcome_GuardianBot_vs_CIMCIC | (C, D) | — | GENUINE-FLOOR | Guardian side (F): guard false (CIMCIC × `.bot CooperateBot` found) — `floor_GuardianBot_vs_CIMCIC_left`; CIMCIC side (G): guard TRUE via Guardian's else-play — `_true` — dichotomy: `dich_GuardianBot_vs_CIMCIC` |
| llm_outcome_GuardianBot_vs_CupodBot | (C, C) | (C, C) | SND | snd_GuardianBot_vs_CupodBot |
| llm_outcome_GuardianBot_vs_CupodTrollBot | (C, C) | (C, C) | SND | snd_GuardianBot_vs_CupodTrollBot |
| llm_outcome_GuardianBot_vs_DBot | (D, C) | (D, C) | POS | pos_GuardianBot_vs_DBot |
| llm_outcome_GuardianBot_vs_DIMCID | (C, C) | (D, D) | FLIP | loeb_GuardianBot_vs_DIMCID |
| llm_outcome_GuardianBot_vs_DupocBot | (C, D) | — | GENUINE-FLOOR | Guardian side (F) — `floor_GuardianBot_vs_DupocBot_left`; Dupoc side (G): guard TRUE via Guardian's else-play — `_true` — dichotomy: `dich_GuardianBot_vs_DupocBot` |
| llm_outcome_GuardianBot_vs_EBot | (D, C) | (D, C) | SND | pos_GuardianBot_vs_EBot |
| llm_outcome_GuardianBot_vs_GuardianBot | (C, C) | (C, C) | SND | snd_GuardianBot_vs_GuardianBot |
| llm_outcome_GuardianBot_vs_JustBot | (C, D) | — | GENUINE-FLOOR | Guardian side (F) — `floor_GuardianBot_vs_JustBot_left`; Just side (G): Guardian's else-play vs the snapshot — `_true` — dichotomy: `dich_GuardianBot_vs_JustBot` |
| llm_outcome_GuardianBot_vs_OBot | (C, D) | (C, D) | SND | pos_GuardianBot_vs_OBot |
| llm_outcome_GuardianBot_vs_PrudentBot | (C, D) | — | GENUINE-FLOOR | Guardian side (G): guard TRUE (Prudent's else-play vs `.bot CooperateBot`) — `floor_GuardianBot_vs_PrudentBot_true`; Prudent outer (G) via Guardian's else-play, prudence (P) FOUND (`prudence_found_vs_GuardianBot`) — dichotomy: `dich_GuardianBot_vs_PrudentBot_prudenceFound` (two hinges `G`, `A`; the three-hinge original `dich_GuardianBot_vs_PrudentBot` stands) |
| llm_outcome_GuardianBot_vs_TitForTatBot | (C, C) | (C, C) | SND | snd_GuardianBot_vs_TitForTatBot |
| llm_outcome_JustBot_vs_MirrorBot | (C, C) | (C, C) | LOEB | loeb_JustBot_vs_MirrorBot (`Cells/JustEngine`; the hand-twin forms are `loeb_Just_vs_Mirror`, `loeb_Just7_vs_Mirror`) |
| llm_outcome_LegibleBot_vs_CupodBot | (C, C) | — | EXCLUDED | OptimBot/LegibleBot out of coverage |
| llm_outcome_LegibleBot_vs_DupocBot | (C, C) | — | EXCLUDED | OptimBot/LegibleBot out of coverage |
| llm_outcome_LegibleBot_vs_GuardianBot | (C, C) | — | EXCLUDED | OptimBot/LegibleBot out of coverage |
| llm_outcome_LegibleBot_vs_JustBot | (C, C) | — | EXCLUDED | OptimBot/LegibleBot out of coverage |
| llm_outcome_LegibleBot_vs_PrudentBot | (C, D) | — | EXCLUDED | OptimBot/LegibleBot out of coverage |
| llm_outcome_OptimBot_vs_CooperateBot | (D, C) | — | EXCLUDED | OptimBot/LegibleBot out of coverage |
| llm_outcome_OptimBot_vs_DBot | (C, C) | — | EXCLUDED | OptimBot/LegibleBot out of coverage |
| llm_outcome_OptimBot_vs_DefectBot | (D, D) | — | EXCLUDED | OptimBot/LegibleBot out of coverage |
| llm_outcome_OptimBot_vs_TitForTatBot | (D, D) | — | EXCLUDED | OptimBot/LegibleBot out of coverage |
| llm_outcome_WaryBot_vs_DupocBot | (C, D) | — | GENUINE-FLOOR | bistable modulo reflection: each guard's Löb closure needs the cheap negative on the other (three consistent scenarios: `(D,D)`/`(C,C)`/`(C,D)`); no side settled — dichotomy: `dich_WaryBot_vs_DupocBot` |
| llm_outcome_WaryBot_vs_GuardianBot | (C, C) | (C, C) | SND | snd_WaryBot_vs_GuardianBot |
| llm_outcome_WaryBot_vs_JustBot | (C, D) | — | GENUINE-FLOOR | as Wary × Dupoc in the snapshot's frame; no side settled — dichotomy: `dich_WaryBot_vs_JustBot` |
| llm_outcome_WaryBot_vs_OptimBot | (C, C) | — | EXCLUDED | OptimBot/LegibleBot out of coverage |
| llm_outcome_WaryBot_vs_PrudentBot | (C, D) | — | GENUINE-FLOOR | prudence (P) FOUND (`prudence_found_vs_WaryBot`); outer/Wary guards bistable modulo reflection; no side settled — dichotomy: `dich_WaryBot_vs_PrudentBot_prudenceFound` (two hinges `A`, `W`; the original `dich_WaryBot_vs_PrudentBot` stands) |
| outcome_CIMCIC_vs_CooperateBot | (C, C) | (C, C) | POS | pos_CIMCIC_vs_CooperateBot |
| outcome_CIMCIC_vs_CupodBot | (D, C) | — | GENUINE-FLOOR | as Just × Cupod; no side settled — dichotomy: `dich_CIMCIC_vs_CupodBot` |
| outcome_CIMCIC_vs_DefectBot | (D, D) | (D, D) | SND (unreadability census → self-refuting guard, soundness) | snd_CIMCIC_vs_DefectBot |
| outcome_CIMCIC_vs_OBot | (D, D) | (D, D) | SND (unreadability census → self-refuting guard, soundness) | snd_CIMCIC_vs_OBot |
| outcome_CooperateBot_vs_CooperateBot | (C, C) | (C, C) | SF | sf_CooperateBot_vs_CooperateBot |
| outcome_CooperateBot_vs_DefectBot | (C, D) | (C, D) | SF | sf_CooperateBot_vs_DefectBot |
| outcome_CupodBot_vs_CooperateBot | (C, C) | (C, C) | SND | snd_CupodBot_vs_CooperateBot |
| outcome_CupodBot_vs_CupodBot | (D, D) | (D, D) | LOEB | loeb_CupodBot_vs_CupodBot (`Cells/DupocEngine`; the hand-twin form is `dupoc_self_coop`) |
| outcome_CupodBot_vs_DBot | (C, C) | (C, C) | SND | pos_CupodBot_vs_DBot |
| outcome_CupodBot_vs_DefectBot | (D, D) | (D, D) | POS | pos_CupodBot_vs_DefectBot |
| outcome_CupodBot_vs_EBot | (C, C) | (C, C) | SND | pos_CupodBot_vs_EBot |
| outcome_CupodBot_vs_MirrorBot | (D, D) | (D, D) | LOEB | loeb_CupodBot_vs_MirrorBot (`Cells/DupocEngine`; the hand-twin form is `loeb_Cupod_vs_Mirror`) |
| outcome_CupodBot_vs_OBot | (C, D) | — | GENUINE-FLOOR | Cupod's guard TRUE (OBot's D needs Cupod's else-play vs `.bot CooperateBot`). Settled: `floor_CupodBot_vs_OBot_right`, `_true` — dichotomy: `dich_CupodBot_vs_OBot` |
| outcome_CupodBot_vs_PrudentBot | (C, D) | — | GENUINE-FLOOR | prudence (P) FOUND (`prudence_found_vs_CupodBot`); Cupod's guard / Prudent's outer bistable modulo reflection; no side settled — dichotomy: `dich_CupodBot_vs_PrudentBot_prudenceFound` (two hinges `Cu`, `A`; the original `dich_CupodBot_vs_PrudentBot` stands) |
| outcome_CupodBot_vs_TitForTatBot | (C, C) | (C, C) | SND | snd_CupodBot_vs_TitForTatBot |
| outcome_CupodTrollBot_vs_CooperateBot | (C, C) | (C, C) | SND | snd_CupodTrollBot_vs_CooperateBot |
| outcome_CupodTrollBot_vs_CupodBot | (D, D) | (D, D) | POS | khat_CupodBot_vs_CupodTrollBot (`Cells/CupodTrollEngine`, the pair in the other orientation; CupodTroll's half `khat_CupodTrollBot_vs_CupodBot_engine`; the hand-twin form, on `CupodTroll7 k`, is `khat_CupodTrollBot_vs_CupodBot`) |
| outcome_CupodTrollBot_vs_CupodTrollBot | (C, C) | (C, C) | SND | snd_CupodTrollBot_vs_CupodTrollBot |
| outcome_CupodTrollBot_vs_DBot | (C, D) | (C, D) | SND | snd_CupodTrollBot_vs_DBot |
| outcome_CupodTrollBot_vs_DefectBot | (C, D) | (C, D) | SND | snd_CupodTrollBot_vs_DefectBot |
| outcome_CupodTrollBot_vs_EBot | (C, D) | (C, D) | SND | snd_CupodTrollBot_vs_EBot |
| outcome_CupodTrollBot_vs_MirrorBot | (C, C) | (C, C) | SND | snd_CupodTrollBot_vs_MirrorBot |
| outcome_CupodTrollBot_vs_OBot | (C, C) | (C, C) | SND | snd_CupodTrollBot_vs_OBot |
| outcome_CupodTrollBot_vs_TitForTatBot | (C, C) | (C, C) | SND | snd_CupodTrollBot_vs_TitForTatBot |
| outcome_DBot_vs_CooperateBot | (D, C) | (D, C) | SF | sf_DBot_vs_CooperateBot |
| outcome_DBot_vs_DBot | (D, D) | (D, D) | SF | sf_DBot_vs_DBot |
| outcome_DBot_vs_DefectBot | (C, D) | (C, D) | SF | sf_DBot_vs_DefectBot |
| outcome_DIMCID_vs_CooperateBot | (C, C) | (D, C) | FLIP | loeb_DIMCID_vs_CooperateBot |
| outcome_DIMCID_vs_CupodBot | (D, D) | (D, D) | LOEB | loeb_DIMCID_vs_CupodBot (`Cells/DimcidEngine`; the hand-twin form is `loeb_Dimcid_vs_Cupod`) |
| outcome_DIMCID_vs_DefectBot | (D, D) | (D, D) | POS | pos_DIMCID_vs_DefectBot |
| outcome_DIMCID_vs_DupocBot | (C, D) | (D, D) | FLIP | loeb_DIMCID_vs_DupocBot (engine UNIVERSAL `(C, D)`) |
| outcome_DefectBot_vs_DefectBot | (D, D) | (D, D) | SF | sf_DefectBot_vs_DefectBot |
| outcome_DupocBot_vs_CooperateBot | (C, C) | (C, C) | POS | pos_DupocBot_vs_CooperateBot |
| outcome_DupocBot_vs_CupodBot | (D, C) | (D, C) | SND (τ-symmetry + soundness) | snd_DupocBot_vs_CupodBot (`Cells/RedCellEngine`; the hand-twin form is `red_cell`) |
| outcome_DupocBot_vs_CupodTrollBot | (D, C) | — | GENUINE-FLOOR | Dupoc's guard TRUE (CupodTroll's else-play: a false `.eq`). Settled: `floor_DupocBot_vs_CupodTrollBot_right`, `_true` — dichotomy: `dich_DupocBot_vs_CupodTrollBot` |
| outcome_DupocBot_vs_DBot | (D, C) | — | GENUINE-FLOOR | Dupoc's guard TRUE (DBot cooperates: Dupoc's else-play vs `.bot DefectBot`); residue `Con_TAct(k+c)`. Settled: `floor_DupocBot_vs_DBot_right`, `_true` — dichotomy: `dich_DupocBot_vs_DBot` |
| outcome_DupocBot_vs_DefectBot | (D, D) | (D, D) | SND | snd_DupocBot_vs_DefectBot |
| outcome_DupocBot_vs_DupocBot | (C, C) | (C, C) | LOEB | loeb_DupocBot_vs_DupocBot (`Cells/DupocEngine`; the hand-twin form is `dupoc_self_coop`) |
| outcome_DupocBot_vs_EBot | (D, C) | — | GENUINE-FLOOR | Dupoc's guard TRUE (EBot's rung 1 = Dupoc's else-play vs `.bot DefectBot`). Settled: `floor_DupocBot_vs_EBot_right`, `_true` — dichotomy: `dich_DupocBot_vs_EBot` |
| outcome_DupocBot_vs_MirrorBot | (C, C) | (C, C) | LOEB | loeb_DupocBot_vs_MirrorBot (`Cells/DupocEngine`; the hand-twin form is `loeb_Dupoc_vs_Mirror`) |
| outcome_DupocBot_vs_OBot | (D, D) | (D, D) | SND | snd_DupocBot_vs_OBot |
| outcome_DupocBot_vs_TitForTatBot | (C, C) | (C, C) | POS | khat_DupocBot_vs_TitForTatBot |
| outcome_EBot_vs_CooperateBot | (D, C) | (D, C) | SF | sf_EBot_vs_CooperateBot |
| outcome_EBot_vs_DBot | (D, C) | (D, C) | SF | sf_EBot_vs_DBot |
| outcome_EBot_vs_DefectBot | (D, D) | (D, D) | SF | sf_EBot_vs_DefectBot |
| outcome_EBot_vs_EBot | (C, C) | (C, C) | SF | sf_EBot_vs_EBot |
| outcome_EBot_vs_MirrorBot | (C, C) | (C, C) | SF | sf_EBot_vs_MirrorBot |
| outcome_EBot_vs_OBot | (C, D) | (C, D) | SF | sf_EBot_vs_OBot |
| outcome_EBot_vs_TitForTatBot | (C, D) | (C, D) | SF | sf_EBot_vs_TitForTatBot |
| outcome_GuardianBot_vs_CooperateBot | (C, C) | (C, C) | SND | snd_GuardianBot_vs_CooperateBot |
| outcome_GuardianBot_vs_DefectBot | (D, D) | (D, D) | POS | pos_GuardianBot_vs_DefectBot |
| outcome_GuardianBot_vs_MirrorBot | (C, C) | (C, C) | SND | snd_GuardianBot_vs_MirrorBot |
| outcome_JustBot_vs_CooperateBot | (C, C) | (C, C) | POS | pos_JustBot_vs_CooperateBot |
| outcome_JustBot_vs_CupodBot | (D, C) | — | GENUINE-FLOOR | both guards true only through the other's else-play; bistable modulo reflection; no side settled — dichotomy: `dich_JustBot_vs_CupodBot` |
| outcome_JustBot_vs_CupodTrollBot | (D, C) | — | GENUINE-FLOOR | Just's guard TRUE (CupodTroll's else-play vs the snapshot). Settled: `floor_JustBot_vs_CupodTrollBot_right`, `_true` — dichotomy: `dich_JustBot_vs_CupodTrollBot` |
| outcome_JustBot_vs_DBot | (D, C) | — | GENUINE-FLOOR | Just's guard TRUE (DBot cooperates with the snapshot: its else-play vs `.bot DefectBot`). Settled: `floor_JustBot_vs_DBot_right`, `_true` — dichotomy: `dich_JustBot_vs_DBot` |
| outcome_JustBot_vs_DefectBot | (D, D) | (D, D) | SND | snd_JustBot_vs_DefectBot |
| outcome_JustBot_vs_DupocBot | (C, C) | (C, C) | LOEB | loeb_JustBot_vs_DupocBot (`Cells/JustEngine`; the hand-twin form is `loeb_Just7_vs_Dupoc`) |
| outcome_JustBot_vs_EBot | (D, C) | — | GENUINE-FLOOR | Just's guard TRUE (EBot's rung 1 on the snapshot = an else-play). Settled: `floor_JustBot_vs_EBot_right`, `_true` — dichotomy: `dich_JustBot_vs_EBot` |
| outcome_JustBot_vs_JustBot | (C, C) | (C, C) | LOEB | loeb_JustBot_vs_JustBot (`Cells/JustEngine`; the hand-twin form is `loeb_Just7_vs_Just7`) |
| outcome_JustBot_vs_OBot | (D, D) | (D, D) | SND | snd_JustBot_vs_OBot |
| outcome_JustBot_vs_PrudentBot | (D, D) | — | GENUINE-FLOOR | prudence guard TRUE via Just's else-play vs `.bot DefectBot` — `floor_JustBot_vs_PrudentBot_true`; if not found `(D, D)` follows — dichotomy: `dich_JustBot_vs_PrudentBot` (prudence hinge `B` NOT dischargeable: an else-branch defection, plus §7 on `progCode (JustBot k)` — `Cells/PrudentLoose`) |
| outcome_JustBot_vs_TitForTatBot | (C, C) | (C, C) | POS | khat_JustBot_vs_TitForTatBot |
| outcome_LegibleBot_vs_CIMCIC | (C, C) | — | EXCLUDED | OptimBot/LegibleBot out of coverage |
| outcome_LegibleBot_vs_CooperateBot | (C, C) | — | EXCLUDED | OptimBot/LegibleBot out of coverage |
| outcome_LegibleBot_vs_CupodTrollBot | (C, C) | — | EXCLUDED | OptimBot/LegibleBot out of coverage |
| outcome_LegibleBot_vs_DBot | (C, D) | — | EXCLUDED | OptimBot/LegibleBot out of coverage |
| outcome_LegibleBot_vs_DIMCID | (C, C) | — | EXCLUDED | OptimBot/LegibleBot out of coverage |
| outcome_LegibleBot_vs_DefectBot | (C, D) | — | EXCLUDED | OptimBot/LegibleBot out of coverage |
| outcome_LegibleBot_vs_EBot | (C, D) | — | EXCLUDED | OptimBot/LegibleBot out of coverage |
| outcome_LegibleBot_vs_LegibleBot | (C, C) | — | EXCLUDED | OptimBot/LegibleBot out of coverage |
| outcome_LegibleBot_vs_MirrorBot | (C, C) | — | EXCLUDED | OptimBot/LegibleBot out of coverage |
| outcome_LegibleBot_vs_OBot | (C, C) | — | EXCLUDED | OptimBot/LegibleBot out of coverage |
| outcome_LegibleBot_vs_TitForTatBot | (C, C) | — | EXCLUDED | OptimBot/LegibleBot out of coverage |
| outcome_MirrorBot_vs_CooperateBot | (C, C) | (C, C) | SF | sf_MirrorBot_vs_CooperateBot |
| outcome_MirrorBot_vs_DBot | (C, C) | (C, C) | SF | sf_MirrorBot_vs_DBot |
| outcome_MirrorBot_vs_DefectBot | (D, D) | (D, D) | SF | sf_MirrorBot_vs_DefectBot |
| outcome_MirrorBot_vs_MirrorBot | none | none | SF | sf_MirrorBot_vs_MirrorBot |
| outcome_MirrorBot_vs_OBot | (D, D) | (D, D) | SF | sf_MirrorBot_vs_OBot |
| outcome_MirrorBot_vs_TitForTatBot | (C, C) | (C, C) | SF | sf_MirrorBot_vs_TitForTatBot |
| outcome_OBot_vs_CooperateBot | (C, C) | (C, C) | SF | sf_OBot_vs_CooperateBot |
| outcome_OBot_vs_DBot | (D, C) | (D, C) | SF | sf_OBot_vs_DBot |
| outcome_OBot_vs_DefectBot | (D, D) | (D, D) | SF | sf_OBot_vs_DefectBot |
| outcome_OBot_vs_OBot | (D, D) | (D, D) | SF | sf_OBot_vs_OBot |
| outcome_OBot_vs_TitForTatBot | (D, C) | (D, C) | SF | sf_OBot_vs_TitForTatBot |
| outcome_PrudentBot_vs_CooperateBot | (D, C) | (D, C) | SND | snd_PrudentBot_vs_CooperateBot |
| outcome_PrudentBot_vs_CupodBot | (D, C) | — | GENUINE-FLOOR | same pair as Cupod × Prudent; prudence (P) FOUND; no side settled — dichotomy: `dich_PrudentBot_vs_CupodBot_prudenceFound` (two hinges; the original `dich_PrudentBot_vs_CupodBot` stands) |
| outcome_PrudentBot_vs_CupodTrollBot | (D, C) | (D, C) | SND | snd_PrudentBot_vs_CupodTrollBot |
| outcome_PrudentBot_vs_DBot | (D, C) | (D, C) | SND | snd_PrudentBot_vs_DBot |
| outcome_PrudentBot_vs_DefectBot | (D, D) | (D, D) | SND | snd_PrudentBot_vs_DefectBot |
| outcome_PrudentBot_vs_DupocBot | (D, D) | — | GENUINE-FLOOR | prudence guard TRUE via Dupoc's else-play — `floor_PrudentBot_vs_DupocBot_true`; if not found `(D, D)`, if found the mutual Löb `(C, C)` (the staggered companion's value) — dichotomy: `dich_PrudentBot_vs_DupocBot` |
| outcome_PrudentBot_vs_EBot | (D, C) | — | GENUINE-FLOOR | LOEB-FP: Prudent's outer guard TRUE only through EBot's rung 1 (Prudent's else-play vs `.bot DefectBot`); EBot's C SETTLED via Prudent × `.bot MirrorBot` by Löb (`loeb_PrudentBot_vs_botMirror`, `floor_PrudentBot_vs_EBot_right`) — dichotomy: `dich_PrudentBot_vs_EBot_full` (both worlds: `(¬A → (D, C)) ∧ (A → (C, C))`; the original `dich_PrudentBot_vs_EBot` stands) |
| outcome_PrudentBot_vs_MirrorBot | (C, C) | (C, C) | LOEB | loeb_Prudent_vs_Mirror |
| outcome_PrudentBot_vs_OBot | (D, D) | (D, D) | SND | snd_PrudentBot_vs_OBot |
| outcome_PrudentBot_vs_PrudentBot | (D, D) | — | GENUINE-FLOOR | prudence guard TRUE via Prudent's else-play — `floor_PrudentBot_vs_PrudentBot_true` — dichotomy: `dich_PrudentBot_vs_PrudentBot` |
| outcome_PrudentBot_vs_TitForTatBot | (D, D) | (D, D) | SND | snd_PrudentBot_vs_TitForTatBot |
| outcome_TitForTatBot_vs_CooperateBot | (C, C) | (C, C) | SF | sf_TitForTatBot_vs_CooperateBot |
| outcome_TitForTatBot_vs_DBot | (D, C) | (D, C) | SF | sf_TitForTatBot_vs_DBot |
| outcome_TitForTatBot_vs_DefectBot | (D, D) | (D, D) | SF | sf_TitForTatBot_vs_DefectBot |
| outcome_TitForTatBot_vs_TitForTatBot | (C, C) | (C, C) | SF | sf_TitForTatBot_vs_TitForTatBot |
| outcome_WaryBot_vs_CooperateBot | (C, C) | (C, C) | SND | snd_WaryBot_vs_CooperateBot |
| outcome_WaryBot_vs_CupodTrollBot | (C, C) | (C, C) | SND | snd_WaryBot_vs_CupodTrollBot |
| outcome_WaryBot_vs_DBot | (C, C) | (C, C) | SND | pos_WaryBot_vs_DBot |
| outcome_WaryBot_vs_DefectBot | (D, D) | (D, D) | POS | pos_WaryBot_vs_DefectBot |
| outcome_WaryBot_vs_EBot | (C, C) | (C, C) | SND | pos_WaryBot_vs_EBot |
| outcome_WaryBot_vs_MirrorBot | (C, C) | (D, D) | FLIP | loeb_WaryBot_vs_MirrorBot |
| outcome_WaryBot_vs_TitForTatBot | (C, C) | (C, C) | SND | snd_WaryBot_vs_TitForTatBot |
| outcome_WaryBot_vs_WaryBot | (C, C) | (D, D) | FLIP | loeb_WaryBot_vs_WaryBot |

## `S'`-only cells (no engine counterpart)

**DupocTrollBot (2026-10-13).** `DupocTrollBot k := .search k (.eq .opp (DupocBot k)) D C` — "defect iff the
opponent IS `DupocBot k`", the mirror image of CupodTrollBot — was added as an `S'` bot: the engine has its
DEFINITION (`Bots/DupocTrollBot.lean`) and no theorem, so the cells below (thirteen on 2026-10-13, plus the
PrudentBot pair of 2026-10-19 — fifteen with the DIMDID pair listed under DIMDID) are outside the 155-row ledger
above and are counted separately. Theorems in `arith/ArithS/Cells/DupocTrollBot.lean`, statements in
`Outcome/Matrix/DupocTrollBot.lean`, the floor in `Outcome/Floors.lean`. "Engine side" of the floor = what the
engine's `+k` floor stipulation (`search_f`) would give. Roster: the ten `body` bots, CIMCIC, itself.

Same row shape as the ledger above (the sample-fixture generator reads it): the `engine` column is `—` for a cell
and, for the floor, the ENGINE-SIDE value the `+k` stipulation gives.

| cell | engine | `S'` | class | theorem or reason |
|---|---|---|---|---|
| outcome_DupocTrollBot_vs_CooperateBot | — | (C, C) | SND | snd_DupocTrollBot_vs_CooperateBot (`.eq` guard false ⇒ C; every `k`) |
| outcome_DupocTrollBot_vs_CupodBot | — | (C, C) | SND | snd_DupocTrollBot_vs_CupodBot (Cupod's "the opponent defects against me" false too) |
| outcome_DupocTrollBot_vs_CupodTrollBot | — | (C, C) | SND | snd_DupocTrollBot_vs_CupodTrollBot (two false `.eq` guards; `progCode_DupocTrollBot_ne_CupodBot` separates the stored templates at `(CooperateBot, DefectBot)`) |
| outcome_DupocTrollBot_vs_DBot | — | (C, D) | SND | snd_DupocTrollBot_vs_DBot |
| outcome_DupocTrollBot_vs_DIMCID | — | (C, D) | LOEB | loeb_DupocTrollBot_vs_DIMCID (`dimcid_vs_described` on the troll's own tower; DIMCID defects against every closed program) |
| outcome_DupocTrollBot_vs_DefectBot | — | (C, D) | SND | snd_DupocTrollBot_vs_DefectBot |
| outcome_DupocTrollBot_vs_DupocBot | — | (D, D) | POS | pos_DupocTrollBot_vs_DupocBot (the reflexive equation "`DupocBot k` IS `DupocBot k`" is a `TAct`-theorem in both readings, found ⇒ D; Dupoc's guard then false ⇒ D) |
| outcome_DupocTrollBot_vs_DupocTrollBot | — | (C, C) | SND | snd_DupocTrollBot_vs_DupocTrollBot |
| outcome_DupocTrollBot_vs_DIMDID | — | (C, C) | SND | snd_DIMDID_vs_DupocTrollBot read from the troll's side (`Cells/DimdidTroll.lean`, 2026-10-13: `.eq` guard false by branch constants, `progCode_DIMDID_ne_DupocBot`; DIMDID's guard then self-defeating) |
| outcome_DupocTrollBot_vs_EBot | — | (C, D) | SND | snd_DupocTrollBot_vs_EBot |
| outcome_DupocTrollBot_vs_OBot | — | (C, C) | SND | snd_DupocTrollBot_vs_OBot |
| outcome_DupocTrollBot_vs_TitForTatBot | — | (C, C) | SND | snd_DupocTrollBot_vs_TitForTatBot |
| outcome_DupocTrollBot_vs_PrudentBot | — | (C, D) | SND | snd_PrudentBot_vs_DupocTrollBot read from the troll's side (`Cells/DupocTrollPrudent.lean`, 2026-10-19: the pair the 15-template tau table needs; Prudent's prudence guard is false of the troll, which trusts the defector) |
| outcome_PrudentBot_vs_DupocTrollBot | — | (D, C) | SND | snd_PrudentBot_vs_DupocTrollBot (`Cells/DupocTrollPrudent.lean`, 2026-10-19; `progCode_PrudentBot_ne_DupocBot` for the troll's false `.eq`) |
| outcome_DupocTrollBot_vs_CIMCIC | (C, D) | — | GENUINE-FLOOR | CIMCIC's guard TRUE (consequent = the troll's else-play on a false `.eq`). Settled: `floor_DupocTrollBot_vs_CIMCIC_right`, `_true` — dichotomy `dich_DupocTrollBot_vs_CIMCIC` (hinge side `(C, C)`) |

Counts with this bot: **stated 118 = 107 + 11; floors 27 = 26 + 1** (2026-10-13; with DIMDID 130/30, with the PrudentBot pair of 2026-10-19 **132/30**). CIMCIC and DupocBot, behavioral twins on the
engine's matrix, are separated by it: `(C, C)`-free `(D, D)` against DupocBot, a floor against CIMCIC.

**DIMDID (2026-10-13).** `DIMDID k := .search k (.impl (.plays .self .opp .D) (.plays .opp .self .D)) D C` —
"Defect If My Defection Implies Defection": defect only when defection is provably reciprocated. It is the C/D
TRANSPOSITION of CIMCIC (`(CIMCIC k).transpose = DIMDID k` by `rfl`, `DIMDID_eq_transpose`), so on codes it is the
generic searcher `SV (gI .D) 1 k`; the engine has its DEFINITION (`Bots/DIMDID.lean`) and no theorem, so the fourteen
cells below are outside the 155-row ledger. Theorems in `arith/ArithS/Cells/Dimdid.lean`, statements in
`Outcome/Matrix/DIMDID.lean`, the three floors in `Outcome/Floors.lean` (their `dich_` beside the cells;
`#check_floorA_theorems` runs on that file). Roster: the ten `body` bots, CIMCIC, PrudentBot, itself. Three cells are
CIMCIC's through the general transposition theorem (`outcomeSpecA_transpose`, class TAU): the partner's transposition is
in the zoo. The one new argument is the SELF-DEFEATING guard (`dimdid_selfref_not_found`, the dual of CIMCIC's
self-refuting one): a proof of "I defect ⇒ you defect" makes DIMDID defect, so by soundness the opponent defects —
against the fact when it cooperates; so DIMDID cooperates with everyone who cooperates with it, and the only hinges
are the three partners whose cooperation is itself an else-play (Dupoc, CIMCIC, Prudent).

| cell | engine | `S'` | class | theorem or reason |
|---|---|---|---|---|
| outcome_DIMDID_vs_CooperateBot | — | (C, C) | SND | snd_DIMDID_vs_CooperateBot (self-defeating guard; every `k`) |
| outcome_DIMDID_vs_DefectBot | — | (D, D) | TAU | τ of `outcome_CIMCIC_vs_CooperateBot` (POS: "I defect ⇒ DefectBot defects" is a `TAct`-theorem instance) |
| outcome_DIMDID_vs_TitForTatBot | — | (C, C) | SND | snd_DIMDID_vs_TitForTatBot (TFT sees DIMDID cooperate with `.bot CooperateBot`; every `k`) |
| outcome_DIMDID_vs_DBot | — | (C, C) | POS | pos_DIMDID_vs_DBot (DBot sees DIMDID's FOUND defection against `.bot DefectBot`, `pos_DIMDID_vs_botDB`, and cooperates) |
| outcome_DIMDID_vs_EBot | — | (C, C) | POS | pos_DIMDID_vs_EBot |
| outcome_DIMDID_vs_CupodTrollBot | — | (C, C) | SND | snd_DIMDID_vs_CupodTrollBot (the `.eq` guard false: `templateCode_phiDd_ne_phiCu` at the frame `(CooperateBot, CooperateBot)`; every `k`) |
| outcome_DIMDID_vs_DupocTrollBot | — | (C, C) | SND | snd_DIMDID_vs_DupocTrollBot (`Cells/DimdidTroll.lean`, 2026-10-13: the troll's `.eq` guard false by branch constants; stated in both orientations) |
| outcome_DIMDID_vs_OBot | — | (D, D) | LOEB | loeb_DIMDID_vs_OBot (family: DIMDID's guard vs OBot + vs `.bot DefectBot`; OBot defects against anyone who defects against `.bot DefectBot`, whatever its first probe — `obot_D_of_any_V`) |
| outcome_DIMDID_vs_CupodBot | — | (D, D) | TAU | τ of `outcome_CIMCIC_vs_DupocBot` (the mutual Löb cell) |
| outcome_DIMDID_vs_DIMCID | — | (D, D) | LOEB | loeb_DIMDID_vs_DIMCID (mutual family: "I defect ⇒ you defect" and "I cooperate ⇒ you defect", each consequent the other's found defection) |
| outcome_DIMDID_vs_DIMDID | — | (D, D) | TAU | τ of `outcome_CIMCIC_vs_CIMCIC` (the guard against itself is a tautology) |
| outcome_DIMDID_vs_DupocBot | (C, D) | — | GENUINE-FLOOR | two hinges, NESTED: `A` = DIMDID's guard (outer), `B` = Dupoc's "DIMDID cooperates with me"; `A ⇒ (D, D)`, `¬A ∧ ¬B ⇒ (C, D)` (DIMDID exploited — the engine's `+k` world), `¬A ∧ B ⇒ (C, C)` — dichotomy `dich_DIMDID_vs_DupocBot` (hinge side `(D, D)`) |
| outcome_DIMDID_vs_CIMCIC | (C, D) | — | GENUINE-FLOOR | the self-dual pair; `A` = DIMDID's guard, `B` = CIMCIC's; `A ⇒ (D, D)` (CIMCIC's guard self-refuting), `¬A ∧ ¬B ⇒ (C, D)`, `¬A ∧ B ⇒ (C, C)` — dichotomy `dich_DIMDID_vs_CIMCIC` (hinge side `(D, D)`) |
| outcome_DIMDID_vs_PrudentBot | (C, D) | — | GENUINE-FLOOR | `A` = DIMDID's guard, `B` = Prudent's outer guard, the prudence guard DISCHARGED (`prudence_found_vs_DIMDID`: DIMDID's defection against `.bot DefectBot` is its then-branch, the `k̂`-chain); `A ⇒ (D, D)`, `¬A ∧ ¬B ⇒ (C, D)`, `¬A ∧ B ⇒ (C, C)` — dichotomy `dich_DIMDID_vs_PrudentBot` (hinge side `(D, D)`) |

Counts with both `S'`-only bots: **stated 128 = 107 + 11 + 10; floors 30 = 26 + 1 + 3.** DIMDID's row differs from
every body member's: it is CupodBot's at DefectBot/OBot/CupodBot/DIMCID/itself but cooperates with CupodTrollBot and
TitForTatBot, and it is exploited (engine side) by DupocBot, the partner whose cooperation it cannot see.

## The floor verdicts, per side

(F) the guard is false, the side settled by soundness; (P) found, via the partner's box (verdict only);
(G) genuine: true, provable only above the budget. Every remaining floor cell is (G) on at least one side.

| cell | side | verdict | reason | proved |
|---|---|---|---|---|
| Dupoc × DBot | Dupoc | G | guard "DBot plays C vs me" true; DBot's C runs through Dupoc's else-play vs `.bot DefectBot` | `_true` |
| Dupoc × DBot | DBot | F/settled | search-free; sees Dupoc defect vs `.bot DefectBot` | `_right` (every `k`) |
| Dupoc × EBot | Dupoc | G | EBot's C runs through Dupoc's else-play (rung 1) | `_true` |
| Dupoc × EBot | EBot | settled | D vs `.bot DefectBot` (else), C vs `.bot CooperateBot` (found) | `_right` (large `k`) |
| Dupoc × CupodTroll | Dupoc | G | CupodTroll's C is its else-play on a false `.eq` | `_true` |
| Dupoc × CupodTroll | CupodTroll | F | `.eq` guard false (`progCode_DupocBot_ne_CupodBot`) | `_right` (every `k`) |
| Just × DBot | Just | G | DBot's C vs the snapshot runs through the snapshot's else-play | `_true` |
| Just × DBot | DBot | settled | Just defects vs `.bot DefectBot` (`snd_JustBot_vs_botDB`) | `_right` |
| Just × EBot | Just | G | as Dupoc × EBot in the snapshot's frame | `_true` |
| Just × EBot | EBot | settled | Just: D vs `.bot DefectBot`, C vs `.bot CooperateBot` (`pos_JustBot_vs_botCB`) | `_right` |
| Just × CupodTroll | Just | G | CupodTroll's C vs the snapshot is an else-play | `_true` |
| Just × CupodTroll | CupodTroll | F | `.eq` guard false | `_right` |
| Just × Cupod | both | G | each guard true only through the other's else-play; bistable modulo reflection | — |
| Just × Prudent | Prudent (prudence) | G | "Just plays D vs `.bot DefectBot`" true via Just's else-play | `_true` |
| Just × Prudent | Just / Prudent outer | G | conditional on the prudence verdict | — |
| CIMCIC × CupodTroll | CIMCIC | G | consequent "CupodTroll plays C vs me" is an else-play | `_true` |
| CIMCIC × CupodTroll | CupodTroll | F | `.eq` guard false (`progCode_CIMCIC_ne_CupodBot`) | `_right` |
| CIMCIC × DBot (cenU) | CIMCIC | G | DBot's C runs through CIMCIC's self-refuting else-play vs `.bot DefectBot` | `_true` |
| CIMCIC × DBot (cenU) | DBot | settled | `snd_CIMCIC_vs_botDB` | `_right` |
| CIMCIC × EBot (cenU) | CIMCIC | G | EBot's rung 1 = CIMCIC's else-play | `_true` |
| CIMCIC × EBot (cenU) | EBot | settled | D vs `.bot DefectBot`, C vs `.bot CooperateBot` (found) | `_right` |
| CIMCIC × Cupod | both | G | bistable modulo reflection | — |
| CIMCIC × Prudent | Prudent (prudence) | G | "CIMCIC plays D vs `.bot DefectBot`" true via the self-refuting else-play | `_true` |
| CIMCIC × Prudent | CIMCIC | (F given the floor) | if Prudent defects, CIMCIC's guard is self-refuting — conditional | — |
| Guardian × CIMCIC | Guardian | F | guard "CIMCIC plays D vs `.bot CooperateBot`" false (found guard, C) | `_left` (large `k`) |
| Guardian × CIMCIC | CIMCIC | G | consequent "Guardian plays C vs me" is Guardian's else-play | `_true` |
| Guardian × Dupoc | Guardian | F | Dupoc cooperates with `.bot CooperateBot` (`pos_DupocBot_vs_botCB`) | `_left` |
| Guardian × Dupoc | Dupoc | G | "Guardian plays C vs me" is an else-play | `_true` |
| Guardian × Just | Guardian | F | Just cooperates with `.bot CooperateBot` | `_left` |
| Guardian × Just | Just | G | Guardian's C vs the snapshot is an else-play | `_true` |
| Guardian × Prudent | Guardian | G | "Prudent plays D vs `.bot CooperateBot`" true via Prudent's inner else-play | `_true` |
| Guardian × Prudent | Prudent outer | G | "Guardian plays C vs me" is an else-play (if Guardian's guard is not found) | — |
| Guardian × Prudent | Prudent prudence | P | Guardian defects vs `.bot DefectBot` (found) — found via the partner's box | verdict only |
| Wary × Dupoc | both | G | bistable modulo reflection (`(D,D)`/`(C,C)`/`(C,D)`) | — |
| Wary × Just | both | G | idem in the snapshot's frame | — |
| Wary × Prudent | Prudent prudence | P | Wary defects vs `.bot DefectBot` (`pos_WaryBot_vs_botDB`) | verdict only |
| Wary × Prudent | Wary / Prudent outer | G | bistable modulo reflection | — |
| Cupod × OBot | Cupod | G | OBot's D runs through Cupod's else-play vs `.bot CooperateBot` | `_true` |
| Cupod × OBot | OBot | settled | C vs `.bot CooperateBot` (else), D vs `.bot DefectBot` (found) | `_right` |
| Cupod × Prudent, Prudent × Cupod | Prudent prudence | P | Cupod defects vs `.bot DefectBot` (found) | verdict only |
| Cupod × Prudent, Prudent × Cupod | Cupod / Prudent outer | G | bistable modulo reflection | — |
| Prudent × Dupoc | Prudent prudence | G | "Dupoc plays D vs `.bot DefectBot`" true via Dupoc's else-play | `_true` |
| Prudent × Dupoc | outer / Dupoc | G | if the prudence guard is not found `(D, D)`; if found, mutual Löb `(C, C)` (the companion's value) | — |
| Prudent × Prudent | prudence | G | true via Prudent's own else-play vs `.bot DefectBot` | `_true` |
| Prudent × EBot | Prudent outer | G | EBot's C runs through Prudent's else-play (rung 1) | — |
| Prudent × EBot | EBot | Löb (not built) | needs Prudent × `.bot MirrorBot` by Löb; two rungs proved (`snd_PrudentBot_vs_botDB/_botCB`) | — |
