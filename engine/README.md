# `engine/` — the host: programs, evaluator, zoo, and the rule-based `S`

Lean 4 package `PrisonersDilemma` (namespace `PD`). It defines what an open-source game *is* —
the agent language, the evaluator, the bots — and the rule-based proof system `S` with its
machine-checked outcome matrix. The paper's proof system is the arithmetized PA-`S'` in
[`../arith/`](../arith/), which imports this package (the language, the evaluator, the bots, the
τ-bot specs, and the search-free cells) and never the other way round.

## Layout (`PrisonersDilemma/`)

| Layer | Files | What it defines |
|---|---|---|
| Language | `Program.lean` | `Action`, `Outcome`, the mutually recursive `Prog` (agent source: `.const/.self/.opp/.bot/.sim/.ite/.search`, plus the τ-bot constructors `.tvote/.sys/.selfIdx`) and `Formula` (`.plays/.impl/.neg/.box/.eq`); `subst`, `size`. |
| Proof system `S` | `ProofSystem.lean` | The unified proof-term type `Pf k φ` (`⊢_k φ`), transcript-cumulative costs, the named eliminators. |
| Dynamics | `Dynamics.lean` | The fuelled evaluator `eval`; `play`, `outcome`; `Formula.interp` (truth, `⊨ φ`). |
| Meta-theorems | `Base/` | Soundness, monotonicity, the internalized bounded Löb (`Loeb`), the negative direction (`Exclusion`: the cost floors), the C/D transposition `τ̂` (`Transpose`: `S` is closed under it at the same budget — the red cell), the abstract bounded-GL interface (`BoundedGL`). `BaseTheorems.lean` re-exports. |
| Bots | `Bots/`, `Bots/LlmGenerations/` | The zoo: CooperateBot, DefectBot, DBot, TitForTatBot, OBot, EBot, MirrorBot, CupodBot, DupocBot, CupodTrollBot, DupocTrollBot, DIMDID, and the LLM-written PrudentBot, JustBot, CIMCIC, DIMCID, WaryBot, LegibleBot, OptimBot, GuardianBot. |
| Outcome theorems | `Theorems/<Left>/vs_<Right>.lean` | One file per ordered pair, `@[outcome] theorem outcome_<L>_vs_<R> : OutcomeSpec <regime> <pad> L R (some (.X, .Y))`; dir-local helpers in `Theorems/<Bot>/Helpers.lean`. |
| Template, linter, census, export | `Outcome/` | `Spec.lean` (the typed statement), `Lint.lean`, `Check.lean` (lake target `OutcomeCheck`), `Export.lean` (`lake exe export_outcomes` → `app/generated/outcome_theorems.json`, `tau_rows.json`). |
| τ-bots | `Tau/` | The Spec DSL and its compiler (`Spec.lean`), the vote constructor, the roster `Zoo.lean`, `RowSpec`, the per-template `Theorems/<T>/Phase.lean` rows, the row linter. |
| Research notes | `Research/Notes/`, `Research/Readings/`, `Research/Data/` | Design notes and results records for the whole project (both Lean packages and the Python layer), source-paper extracts, golden outcome lists. |

The root `PrisonersDilemma.lean` imports every theorem module directly; the pipeline's library
writer appends to it.

## Build

```bash
cd engine
lake build                  # default targets: PrisonersDilemma + OutcomeCheck (linter + census)
lake exe export_outcomes    # refresh app/generated/outcome_theorems.json and tau_rows.json
```

Toolchain `v4.33.1`, mathlib pinned in `lakefile.toml`. Zero project axioms, no `sorry`.

## History

The decidability metatheory (`Decidability/`, T31–T54: the verified enumerator `decFull`, the
computable evaluator `evalG`, the modest and instance strata, CutRelevance) and the research spikes
(`Research/Spikes/`) were removed on 2026-10-29 for the paper submission; both are in the git history
before that date (last commit with them: `3f99464`). Docstrings that cite a spike by path refer to
that history. The notes under `Research/Notes/` describe them (`DECIDABILITY_ROADMAP.md`,
`CUT_RELEVANCE.md`).
