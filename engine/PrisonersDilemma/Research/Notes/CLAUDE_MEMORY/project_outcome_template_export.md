---
name: outcome-template-export
description: The @[outcome]/OutcomeSpec template + Lean export is the matrix's ONLY source; proof agent ALIGNED 2026-08-26 (#validate_outcome gate, writer builds OutcomeCheck); census tightened, no exclusions file
metadata:
  type: project
---

Audited 2026-08-26. Matrix cells come from `engine/PrisonersDilemma/Outcome/` (Spec/Attr/Lint/Check/Export) →
`lake exe export_outcomes` → committed `app/generated/outcome_theorems.json` (FNV digest) →
`outcome_matrix.scan_outcome_theorems` (3 lines, no regex). Dagger = `staggered` lambda OR `side_conditions`
(Prop binder / `OutcomeSpecIf` guard); budget floors are `.eventual`, not daggered (3 cells de-daggered).
`OutcomeCheck` is in the default `lake build` (census: every `outcome_X_vs_Y` on disk tagged or in exclusions.txt).

**Why:** the old Python regex inferred † from "binder starts with `h`" and mis-flagged cells.

**How to apply:**
- Proof agent aligned 2026-08-26: `Outcome/Spec.lean` embedded in block A; request templates are `OutcomeSpec`
  statements; verdict gate compiles the submission with `with_outcome_validation` (inserts
  `import PrisonersDilemma.Outcome.Lint`, appends `#validate_outcome PD.Theorems.<name>` — the library's own
  `inspectCell`) + textual checks in `verdicts.check_proved_source` (tag, template head, no Prop binders,
  no `OutcomeSpecIf`, bots named); `library_writer` builds `("PrisonersDilemma","OutcomeCheck")` then
  `refresh_export`. Legacy raw `outcome … = some …` submissions are REJECTED.
- Census tightened: exact `(llm_)?outcome_<Alnum>_vs_<Alnum>` names with both bot DIRECTORIES; `exclusions.txt`,
  `pending`/`expecting` deleted. `botOf` flags free-variable / literal bot args as staggered (hidden 2nd budget).
- Dagger audit: two false daggers fixed (`GuardianBot_vs_DefectBot` → `.eventual`; `CupodTrollBot_vs_CupodBot`
  → `.eventual`, its fuel guard was unused). 23 daggered cells remain: 22 staggered (LegibleBot 2k+64/k ×14,
  OptimBot 65536k ×3, Prudent×Dupoc, Just×Prudent, Just×CupodTroll, CupodTroll×Dupoc(j)) — all genuine.
- 2026-08-27: `OutcomeSpecEx`/`OutcomeAtEx` RETIRED — all 29 Löbian cells now `OutcomeSpec .eventual <pad>` (pads 2–6).
  Key insight: no need to bound `Pf_sound`'s fuel witness; fuel is per-node while `k` is a numeral, so every zoo
  match is DETERMINED at a structural pad. `Base/Helpers`: `play_unique` (fuel determinism), `play_at_of_ex` /
  `outcome_at_of_ex` (∃-witness + totality-at-pad ⇒ cofinite), totality lemmas `play_search_const_total` (search
  with const leaves, pad 2), `play_sim_opp_self_total` (Mirror, +1), `eval_const_total`/`eval_ite_total`/
  `play_ite_total`/`eval_sim_opp_bot_total` (TFT/DBot pad 4, OBot 5, EBot 6), `outcome_total_of_plays`,
  `play_total_mono`. Migration pattern: `refine ⟨K, fun k hk fuel => outcome_at_of_ex ?_ ?_ fuel⟩`, old body
  verbatim in bullet 1, totality in bullet 2. Trap: anchor rewrites AFTER `@[outcome]` — helper lemmas in the same
  file share the `refine ⟨k₂, fun k hk => ?_⟩` shape.
- 2026-08-27 (later): `OutcomeSpecIf`/`OutcomeAtIf` RETIRED too. Sole user `CupodTrollBot_vs_DupocBot (j)` was a
  floor in disguise → now the conventional stagger `OutcomeSpec .eventual 2 CupodTrollBot (fun k => DupocBot (2*k+64))`
  (general fact kept as non-cell `CupodTrollBot_vs_DupocBot_above_floor`). Template = ONE head, `OutcomeSpec`, 5 args.
  Linter now REJECTS Prop binders; `side_conditions` gone from export; Python field renamed `has_hypotheses`→`staggered`
  (tau/matrix.py too). Dagger ≡ staggered, nothing else. Re-add a guarded template only for a genuine k/fuel-coupled
  condition (none in the zoo).
- 2026-08-27 (tau): `Tau/RowSpec.lean` (`RowSpec A order row` = ∃k₂ ∀k>k₂ ∀T∈order, inst plays row T; `.bits` derives
  VoteBits), `@[tau_row]` in Outcome/Attr, `Tau/Lint.lean` (`inspectRow` whnf-evaluates the row fn; roster census
  `#check_tau_rows` in Check.lean), export → `app/generated/tau_rows.json`; `def4_theorems.kernel_bits` reads JSON
  (regex gone). Each Phase.lean: `<t>RowSpec` unconditional via the phase theorem's composition; old `*Bits` deleted.
  `tauOrderInit`/`tauOrder_eq` moved to Roster, `vecOf_append` to Tau/Spec. Finding: the old scanned `*Bits` were
  CONDITIONAL on Löb-gated hyps — invisible to the regex.
- 2026-08-27 (cells): CONVENTION DECIDED — the matrix cell is the SHARED-budget value. The four staggered
  cooperative cells became `*_staggered` non-cell theorems; their `_samek` values are the cells:
  Prudent×Dupoc (D,D) pad 3, Just×Prudent (D,D), Just×CupodTroll (D,C), Dupoc×CupodTroll (D,C) (Dupoc-left
  file). Tau WHITELIST empty, certification 225/225/0; harness case Prudent×Dupoc expects (D,D). Remaining
  daggers = LegibleBot/OptimBot two-tier cells only (19). CASCADE in the tau zoo (twin policy): PrudentBot ≡ DefectBot
  at a shared budget on the default zoo, then Guardian ≡ TFT without Prudent's column → both in `_TWIN_EXCLUSIONS`;
  default zoo = 9 bots (Coop, Cupod, CupodTroll, DBot, Defect, Dupoc, EBot, OBot, TFT), ceiling 1.0. Enlarged twins:
  {CIMCIC, Dupoc, Just}. EGT headline RE-RUN 08-27 on the new cells/9-bot zoo: SURVIVES — Dupoc uniquely stochastically stable at t=1,
  27→56→82→88% with selection; t=0 ties (Defect/Dupoc/OBot at α=.45; +EBot at α=.62). CLAUDE.md updated. Committed `101162a`.
- 2026-08-27 (companions): `@[outcome_companion]` on `…_staggered` theorems (same template, must be staggered, must
  have a cell; census refuses untagged `…_staggered`). Export `companions` list; Python attaches by unordered pair;
  cell is BUDGET-SENSITIVE (`(D, D) ⇄ (C, C)`) when a companion disagrees. `MATRIX_LEGEND` = one legend for CLI, UI
  (`GET /matrix` → legend), Sheet. Lean-idiom trap: `arr.mapM (f env)` with optional/MetaM args — eta-expand.
- Freshness: `export_staleness()`/`refresh_export()`; `/matrix` reports `stale`; `POST /matrix/export`.
- Pre-existing failing test: `tests/egt/test_report.py::test_conditional_results_are_flagged` (expects a
  stipulation banner; tau zoo has none since 08-25). See [[outcome-matrix-sheet-sync]].
