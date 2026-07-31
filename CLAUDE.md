# Project Guidelines

**What this project is.** A mechanization of **Open-Source Game Theory (OSGT)** —
Critch 2022's bounded-proof-search agents (`critch22.pdf`) — in **Lean 4**, plus an
**LLM pipeline** that automates writing new agents and their correctness proofs. Two
halves, in dependency order:

1. **`engine/`** — the Lean library: the agent language, evaluator, proof system `S`,
   the bot zoo, and machine-checked outcome theorems. **This is the foundation; the app
   sits on top of it.**
2. **`app/`** — a Python service (`pd_runner`) that drives an LLM to generate bots from
   natural language and prove their outcomes against the engine.

Other top-level: `latex/` (paper), `Research/` notes live under the engine, `README.md`,
`critch22.pdf` (the source paper), `Pipeline Figure.jpeg`.

---

# Part I — The Lean engine (`engine/PrisonersDilemma/`)

Build: `cd engine && lake build`. TWO lake targets (both default): `PrisonersDilemma`
(root module `PrisonersDilemma.lean` — language, proof system, zoo, outcome theorems) and
`Metatheory` (rooted at `PrisonersDilemma.Decidability` — the T31…T54 decidability chain;
builds on the engine, the engine never imports it). Namespace `PD`. Layered bottom-up
(each file imports the ones above):

| Layer | File(s) | What it defines |
|---|---|---|
| **Language** | `Program.lean` | `Action` (C/D), `Outcome`; the mutually-recursive `Prog` (agent source code — `.const/.self/.opp/.bot/.sim/.ite/.search`) and `Formula` (the logic agents reason in — `.plays/.impl/.neg/.box/.eq`); `subst`, `size`. Pure syntax — no actions until `eval`. |
| **Proof system `S`** | `ProofSystem.lean` | **Pf-only since 2026-07-14** (`PF_ONLY_ROADMAP.md`): the mutual `PlaysProof`/`AtomProvable`/`Pf k φ` block — `Pf` is the ONE unified proof-term type (22 constructors; the former `Derivation`(Type)+`Provable`(Prop) split and its `struct`/`app`/`hypSyll` duplication are GONE). Ships the named eliminators `Pf.induct`/`PlaysProof.induct` (`@[elab_as_elim]`; NEVER use the raw mutual recursors outside `ProofSystem.lean` §4 and `Base/ValuationSoundness.lean` — the ONE parametric valuation-soundness master lemma `wv_sound_upto`, of which `sound_upto` (= the empty valuation) and the WaryBot `.neg`-guard censuses are instantiations since 2026-07-30). Cost constants `c_leaf/c_node/c_guard`; `atom_cost`. Meaning-preservation vs the pre-merge `S` is a THEOREM: `legacy_iff_live` in `Research/Spikes/unified_pf/LegacyS.lean`. |
| **Dynamics** | `Dynamics.lean` | The fuelled evaluator `eval` (its `.search` guard consults `proofSearch k φ := decide (Pf k φ)` — **currently `noncomputable`, see crux below**); `play`, `outcome`; `Formula.interp` (denotational semantics; `.box` = `Pf`). |
| **Axioms** | *(file deleted — nothing to hold)* | **ZERO project axioms** (2026-07-03): the last one, `atom_complete_false_guard`, was machine-checked INCONSISTENT (anti-diagonal bot, `Research/Spikes/transcript/T32Inconsistency.lean`) and DELETED — replaced by the sound `search_f`/`atomNeg`/`eqNeg` machinery with a cost FLOOR. `PBLT` fell 2026-07-01 (theorem via the `.diag` fixpoint); everything rests on Lean's 3 standard axioms. Costs are transcript-cumulative (Critch's literal model) since 2026-07-02. |
| **Meta-theorems** | `Base/` (`Asymptotics`, `AtomCerts`, `Soundness`, `Exclusion`, `Loeb`); `BaseTheorems.lean` is the re-exporting umbrella | Split 2026-07-09 (absorbed the former `SizeLemmas.lean` into `Base/Asymptotics`). Soundness (`sound_upto` — the ex-`Derivation.sound` arms folded in, `proofSearch_sound`), monotonicity, `atom_complete_searchfree`, log₂ arithmetic, the internalized Löb engines (`bloeb_engine`, `pblt_engine`, `mutual_pblt_*`), and the NEGATIVE direction (`Exclusion`: the transparency census `tail_plays_readable` + the generalized floor bound `no_provable_probeFirst_tail` (+`_botOpp` for `.bot`-wrapped searchers), plus `no_provable_searcherPlay_tail` for the searcher's OWN else-play, which resolved ALL SEVEN floor tombstones into honest outcomes: `outcome_DupocBot_vs_DBot`, `outcome_DupocBot_vs_EBot`, `outcome_PrudentBot_vs_EBot`, `outcome_JustBot_vs_DBot`, `outcome_JustBot_vs_EBot` — all `(D, C)` — `outcome_CupodBot_vs_OBot = (C, D)` (the defection-detector exploited), and the same-`k` `outcome_PrudentBot_vs_PrudentBot = (D, D)` (single-tier prudence is self-defeating; `PrudentBot2` is the escape)). All names still in `PD.BaseTheorems` (arithmetic in `PD`). The bridge from provability to real plays. |
| **Unified proof terms** | `ProofSystem.lean` (the system itself) | **The `Pf` migration is COMPLETE (2026-07-14)**: `Pf` IS the proof system (see the row above); the coexistence module `Pf.lean` was absorbed. History and evidence: `Research/Notes/UNIFIED_PF_SKETCH.md` (design), `PF_REPLACEMENT_ASSESSMENT.md` (cost model), `PF_ONLY_ROADMAP.md` (the executed 5-phase plan, all gates met: 81/81 outcome statements byte-identical, 3-axiom footprint, D2 acceptance passed, `#eval` demos unchanged), `Research/Spikes/unified_pf/LegacyS.lean` (the frozen pre-merge `S` + `legacy_iff_live`). |
| **Bots** | `Bots/*.lean`, `Bots/LlmGenerations/*.lean` | The agent zoo: `CooperateBot`, `DefectBot`, `MirrorBot`, `TitForTatBot`, `DupocBot`, `CupodBot`, `EBot`, … and LLM-generated `PrudentBot`, `JustBot`, `CIMCIC`, `DIMCID`. |
| **Outcome theorems** | `Theorems/<LeftBot>/vs_<RightBot>.lean` (per-pair layout, FULLY MIGRATED 2026-07-27) | The headline results: `outcome_X_vs_Y = some (a,b)` (and `∃k₂,∀k>k₂,…` families). One file per ordered matchup, sharded into per-bot directories; dir-local shared lemmas (play/guard/probe/floor machinery) in `Theorems/<Bot>/Helpers.lean`; reusable rules go to `LlmLemmas`. **NO top-level per-bot files or umbrellas**: importers name the specific per-pair modules they need, and the ROOT `PrisonersDilemma.lean` imports every theorem module directly (the app's library writer appends new imports there). LLM-written theorems keep the `llm_outcome_` prefix. |
| **Decidability** | `Decidability/` | The T3.2c/T4 chain (modules keep milestone names `T31`…`T54`; umbrella `Decidability.lean` re-exports the API): `decFull` (verified enumerator, `Pf_iff_decFull`), `evalG` (computable evaluation of search bots, sound both guard polarities, `#eval` demos), `PfG` strata (gate-parametric mirror of the unified `Pf`; uniform gating incl. ex-`Derivation` cuts — D2), the modest universe, `decideProvableG` (modest stratum decidable). Then the cut-relevance arc `T48`–`T54`: literal bounds + antecedent census (T48), the tree substrate / extraction machine / normalization theorem / excisor (T49), **the instance gate + transport theorem** (T50), **the falsification theorem** — the original CutRelevance is FALSE (T51), the gate-parametric decider (T52), **decidability at the instance gate** (T53), and **the certified zoo** (T54). |
| **Research notes** | `Research/Notes/`, `Research/Readings/`, `Research/Data/` | Theory write-ups (esp. `COMPUTABLE_EVAL_NOTES.md`, `UnderstandingTheLayers.md`), extracted source papers, tournament data. |

**The strict outcome-theorem template** is the linchpin the whole pipeline relies on:
`outcome_X_Y = some (.Action_X, .Action_Y)`. Because the statement is fully concrete,
**compilation == correctness** — an LLM-written proof that type-checks is, modulo the
NL→Lean *bot* translation, a verified result.

## Foundational status — zero axioms, transcript costs; `eval` computability reduced to ONE conjecture

Authoritative notes: `engine/PrisonersDilemma/Research/Notes/DECIDABILITY_ROADMAP.md` (current),
`COMPUTABLE_EVAL_NOTES.md`, `INTERNALIZATION_ROADMAP.md` (historical).

- **2026-07-01 — `PBLT` became a THEOREM** (`BaseTheorems.bloeb_engine`/`pblt_engine`): bounded
  Löb proven inside `Provable` via the internalized fixpoint sentence `Formula.diag`.
- **2026-07-02 — transcript-length accounting (Route B)**: every `Provable`/`Derivation` cost is
  CUMULATIVE ("`k` means characters of proof transcript", Critch's literal model). This paid the
  cuts (premise formulas are budget-bounded), making bounded proof search genuinely finite:
  the logical fragment of `Provable` is DECIDABLE relative to the atom layer
  (`Research/Spikes/transcript/T3DeciderMini.lean`, `T31EngineDecider.lean`).
- **2026-07-02 — the last axiom was INCONSISTENT**: `atom_complete_false_guard` injected
  else-play certificates below the guard budgets they refute; the anti-diagonal bot
  ("if I can prove I defect vs myself, cooperate") yields machine-checked `False`
  (`T32Inconsistency.lean`). Every result that had cited it was vacuous.
- **2026-07-03 — the repair, ZERO axioms**: sound `PlaysProof.search_f` (else-certificates from a
  Σ₁ REFUTATION of the guard, paying the full failed budget — the floor, forced by consistency,
  by decidability, and by the provability of soundness alike), `Provable.atomNeg` + `Derivation.eqNeg`
  (the refutation suppliers), soundness by budget-strong-induction (`sound_upto`). Consequences,
  all Critch-faithful: same-budget results whose proofs consumed a partner's else-play are
  honestly FALSE and retired (tombstones in the theorem files); the survivors are re-certified
  constructively; cross-bot cooperation returns at STAGGERED budgets
  (`outcome_PrudentBot_vs_DupocBot`: `PrudentBot (2k+64)` vs `DupocBot k`;
  `outcome_JustBot_vs_PrudentBot`; `outcome_JustBot_vs_CupodTrollBot`), and self-play needs the
  two-tier `PrudentBot2` (prudence budget above the cooperation literal — the bounded analogue
  of MIRI PrudentBot's PA+1 prudence, rediscovered here from consistency alone).
- **2026-07-03 (later) — `Provable` is ABSOLUTELY SEMIDECIDABLE**: `decFull`, a verified
  computable enumerator with `Provable k φ ↔ ∃ fuel, decFull fuel k φ = true`
  (`Decidability/T31EngineDecider.lean` §7–8) — the logic and atom layers tied by fuel
  stratification, no oracle, no hypothesis. And **search bots RUN**: `evalG` (spike §9) is a computable evaluator
  with SOUND commits in BOTH guard polarities (true via `decFull`; false via a DERIVABLE
  refutation + soundness/consistency — the honest replacement for what the deleted axiom
  faked); `#eval` demos print real outcomes, `none` only at the Löb boundary. This supersedes
  `evalC`'s role.
- **2026-07-03 (latest) — the T4 pipeline: DECIDABILITY over the zoo universe.** The
  `Decidability/` chain `T42ProvableB` → `T43ModestUniverse` → `T44BoundedDecider` →
  `T45CertReads` → `T46LogicSpace` → `T47Stabilization` (promoted 2026-07-03 from
  `Research/Spikes/transcript/`, wired into `lake build`; the abstract stabilization mini
  `T4QueryBound` stays a spike) delivers
  **`Decidable (ProvableG (modestGate N) k φ)`** with a computable fuel bound `|SL|`:
  `ProvableG G` is the gate-parametric proof system (six conclusion-absent premise formulas
  gated); `modestGate N` = literal-bounded + modest cuts; MODESTY (all `.sim` args and
  guard-atom args are `.self`/`.opp`/frozen — true of the WHOLE zoo, each by `rfl`) makes the
  substitution dynamics' query universe finite; the decider `decB` is sound + complete for
  the stratum and stabilizes on the finite space by a countP pigeonhole.
  `Provable ↔ ∃N, ProvableB N` (every derivation is finitely-cut) is a theorem.
- **2026-07-08/09 — CutRelevance RESOLVED: falsified as stated, repaired, and the
  repair delivered** (full history: `Research/Notes/CUT_RELEVANCE.md`):
  * **FALSIFICATION (theorem, T51)**: `cutRelevance_modestGate_false` — the DupocBot
    self-cooperation fact is `Provable` (bounded Löb) but `¬ProvableG (modestGate N)`
    at EVERY `N` and budget: instance formulas are never `modestF`, the modest gate
    blocks `diagF/diagB` on instances, and only diag breaks the fixpoint's cite
    regress. The original conjecture is FALSE.
  * **THE REPAIR (T50)**: the INSTANCE GATE `instGate P N` (argument positions may
    hold pool members / closed raw-modest programs; stored guards stay raw). Real
    Löb derivations pass it RAW. `ProvT.transport`/`certifyTransport`: four
    kernel-decidable certificates put any tree into `ProvableG (instGate P N)`.
  * **DECIDABILITY (T52/T53)**: the bounded decider is gate-parametric;
    `ProvableG (instGate P N)` is semidecidable both ways and
    `decideProvableG_inst` decides it with the computable fuel bound `|SL|`.
  * **THE CERTIFIED ZOO (T54)**: every zoo guard shape (plays/impl/eq), every Löb
    pattern (self, staggered mutual, bot-wrapped mutual) and every refutation
    route is certified into the instance stratum — kernel-sealed, no excision.
  * **Open frontier (universal closure)**: `Provable k φ → ProvableG (instGate P N₀) k φ`
    for ARBITRARY minimal proofs (arbitrary trees may need excision + the cite/rawness
    certificates established; the machinery exists, the composition is unproven).
    `eval` is computable relative to certificates — uniform computability rests on
    the universal closure.

**Dead ends (do not retry):** deciding `Provable` by structural recursion on the program
(`DecMeasure.lean`); the `derivable`/`playsCheck` separate-gas checker; proof-term enumeration
under CONCLUSION-cost (mp-cut wall, `MN1_decidable.lean` — dissolved by transcript costs);
model/realizability witness extraction (`ConstructiveLobToy.lean` §8); unprovability-premised
`search_f` (non-monotone fixpoint — the anti-diagonal bot is its paradox); charging
`searchThenSearch_t`'s inner premise (sinks the staggered Löb chains — cite via `c_guard`, like
`search_t`); uniform (non-budget-stratified) size bounds for the decider's query space
(cut-composites grow per descent — stratify: `ZS b := Z₀ + (RR−b)·stride`); structural size
bounds for `enumFormula` members (the enum is a deliberate SUPERSET — bound by `foldMax` over
the list itself).

---

# Part II — The LLM pipeline (`app/`)

Python service `pd_runner` (`app/src/pd_runner/`) that drives an LLM to **generate new
bots from natural language and prove their outcome theorems against the engine.** The
engine (Part I) is the ground truth: the LLM writes `.lean`, the Lean kernel judges it.

## Package management — ALWAYS use `uv`, never `pip`

- Install/sync: `uv sync` (inside `app/`)
- Add a dependency: `uv add <package>` (inside `app/`)
- Run a script: `uv run <script>` (inside `app/`)
- Run tests: `uv run pytest` (inside `app/`)
- Serve the API+UI: `uv run pd-serve --reload`

## Pipeline vision

Two programs enter → game outcome out. Inputs can be LLM-generated, user
natural-language, or chosen from the predefined zoo. Backend = the Lean engine with an
LLM writing the proofs, using the existing library as RAG / few-shot context.

## Proof-agent architecture (AxProverBase-style rework, 2026-07-30)

The proof agent follows the **Proposer → Compiler → Reviewer → Memory** loop of
AxProverBase (arXiv 2602.24273), adapted to this domain:

- **Episode loop** (`services/proof_episodes.py::run_proof_search`): up to
  `max_episodes` (default 3) fresh-context episodes × `max_turns_per_episode`
  (default 10) API round-trips. Only four things cross episodes: the **lab
  notebook** (`update_notebook` tool, replace-whole-text ≤4k chars; a forced
  reflection turn fires at episode end if stale), the best compiling source,
  the last compiler feedback, and (retry only) the prior open verdict. Context
  overflow ends an episode gracefully (~350k-token guard), never a hard crash.
  **Open-verdict retry (2026-07-31)**: the FIRST `open_blocked`/`open_bistable`
  verdict of a run does not end it — it buys ONE fresh retry episode that sees
  the prior verdict + explanation and is told to re-derive the blocker from
  scratch. The second open verdict (or one on the last available episode) is
  final; if the retry ends with no verdict at all, the run falls back to the
  retried open verdict rather than reporting `exhausted`. `proved` and
  `constructor_proposed` always end the run immediately.
- **Fast compile + sketch-then-fill** (`lean/interact.py`): `run_lean_proof`
  first tries a persistent **LeanInteract** REPL (env cached per import block;
  invalidated when `add_base_lemma` mutates the library; disable with
  `PD_LEAN_INTERACT=0`) and silently degrades to `lake env lean` on any
  problem. The REPL also reports the GOAL at every `sorry`, so the agent may
  check sketches in-loop; a sketch never becomes the "best attempt" and the
  verdict gate rejects `sorry`. The verdict gate and library writer ALWAYS
  file-compile — acceptance never depends on REPL state.
- **`search_library` tool** (`llm/library_search.py`): declaration search over
  the whole engine (name or statement content, regex, leak-filtered like
  `read_library_file`) — the closed-world replacement for LeanSearch; fixes
  the find-the-census-in-another-bot's-Helpers problem (the DIMCID-vs-OBot
  incident) without web access.
- **Structured verdicts** (`services/verdicts.py`): the agent finishes via the
  `submit_verdict` tool — `proved | open_bistable | open_blocked |
  constructor_proposed` — never via prose ("PROOF COMPLETE" string sniffing is
  gone). `search_proof_outcome(request) -> ProofOutcome` is the structured entry
  point; `search_proof` remains the legacy facade (raises `ProofSearchError`
  with `.outcome` attached).
- **Deterministic exit verification** (`proof_episodes.verify_proved_submission`):
  on `submit_verdict(proved)` the submitted source is RE-COMPILED and checked
  against the strict template (exact `llm_outcome_<L>_vs_<R>` name, outcome
  equation, no `proofSearch` premises, no sorry/axiom, no hand-rolled `Pf.induct`
  census, no library name collisions — the same checks `library_writer` enforces
  at write time). Rejections bounce back into the episode (cap 3/episode).
  `CompileService`/`CompileReport.goals` is the reserved v2 seam for sorry-sketch
  goal-state extraction.
- **Prompt caching** (`llm/prompts.py::build_system_prompt_blocks` +
  `llm/client.py`): 4 breakpoints — tools array, system block A (pair-INVARIANT:
  role + core modules + rules; caches across a whole matrix run), system block B
  (pair/session: search-tier modules, LlmLemmas, proposals), and a moving marker
  on the newest user turn. `ProofSystem.lean` and `Base/Exclusion.lean` are
  embedded as signature digests (`llm/lean_index.py::strip_proof_bodies`);
  `Loeb/Asymptotics/Closure` stay verbatim (their proof bodies are templates).
- **Config** (`settings.py`): single source for model default, budgets,
  `RetryPolicy` (retries 429/500/529, honors retry-after), `RetrievalConfig`,
  and `EvalGuard` — the explicit split of the old `exclude_bots` overload into
  `hidden_bots` (leak prevention) vs `allow_library_growth` (mutation).
- **Eval** (`eval/common.py` shared by `harness.py` + `run_bot_matrix.py`):
  14 harness cases incl. `.search` Löb self-play, the staggered
  PrudentBot-vs-DupocBot, the (D,D) census case, and the known-OPEN
  JustBot-vs-MirrorBot (passes ONLY on the `open_bistable` verdict). Records
  tokens/cost/cache-hit-rate; every run persists to one timestamped directory
  under `generated/outcomes/` — per-episode meta `.json` (notebook embedded) +
  transcript, plus the final episode's Lean source (never deleted —
  longitudinal thesis data).

Growth-tool semantics (Tier-1 `add_base_lemma` / Tier-2 `propose_pf_constructor`,
human gates, escalation ladder) are UNCHANGED — only the signalling channel moved
into `submit_verdict`.

**Cross-cutting design decisions:**
1. Proof agent may only ADD new files, never modify existing ones (v1 safety).
2. Theorem statements use the strict `outcome_X_Y = some (.Action_X, .Action_Y)` template
   (Part I) ⇒ compilation == correctness, modulo the NL→Lean *bot* translation step.
3. NL→Lean translation accuracy is the remaining weak link; mitigated by an agent
   reviewer + few-shotting from existing bots.
4. Human-in-the-loop v1: a human accepts each new bot and theorem before it lands.
5. The engine's reflection axioms (Part I crux) are orthogonal to this pipeline and not a
   blocker for it.

## Phase 2 milestones (proof-writing first) — COMPLETE ✅

Start with proof-writing for human-written bots/theorem statements, NOT end-to-end NL→bot→proof. The agentic Lean loop is the riskiest unknown; test it against existing ground-truth proofs first.

**Milestones:**
1. **Real LLM client** ✅ — `llm/client.py` replaced with Anthropic-SDK-backed client (multi-turn tool use, prompt caching). Auto-retry on 529 overload errors with exponential backoff.
2. **Lean tools for the agent** ✅ — `llm/tools.py` wraps `run_lean_proof_file` + `read_library_file` as Claude tool definitions. Fast per-iteration check (no `lake build`).
3. **Retrieval over the library** ✅ — `llm/retrieval.py` returns relevant theorem files as few-shot context (name match). Bot definitions always injected upfront into the prompt. Eval harness uses `exclude_bots` to prevent leaking the target proof via few-shots or known-theorems summary.
4. **Proof-search loop in `proof_service.py`** ✅ — agentic loop with retrieval, prompt building, tool use, and error feedback. `ProofRequest` carries `fuel` (correct minimum fuel offset per bot pair) and `exclude_bots`.
5. **Evaluation harness** ✅ — `eval/harness.py` re-proves 10 held-out theorems. **10/10 passed** in ~263s avg 1.5 iterations on clean (leak-free) run. Supports `--cases N [M]`, `--log-level` (TRACE/DEBUG/INFO/WARNING), `--model`, `--max-iterations`, `--output`.
6. **Library writer** ✅ — `services/library_writer.py` writes proven proofs to `engine/PrisonersDilemma/Theorems/LlmGenerations/`, appends import to `LlmGenerations.lean`, runs `lake build`, rolls back on failure. LLM-generated theorems use `llm_outcome_X_vs_Y` naming to avoid clashes with existing library theorems.

**Key design notes:**
- Theorem name prefix `llm_outcome_` avoids collision with hand-written theorems in the same namespace.
- The ROOT `PrisonersDilemma.lean` is the index: the library writer (and
  `add_base_lemma`'s bootstrap) append `import` lines directly to it. There is no
  `Theorems/LlmGenerations.lean` index anymore.
- Proof files land per-pair at `Theorems/<LeftBot>/vs_<RightBot>.lean` (module
  `PrisonersDilemma.Theorems.<LeftBot>.vs_<RightBot>`); `library_writer.theorem_file_path`
  is the single source of truth for the path.
- Eval harness excludes the target bot pair from few-shots AND known-theorems summary to prevent answer leakage.

## Phase 3 — NL→bot synthesis (current)

Given a natural language description of a strategy, generate a valid Lean 4 bot definition, verify its behavior against canonical opponents, and prove its outcome theorems end-to-end.

**Architecture:**
```
NL description
    → bot writer agent → BotName.lean (compiles)
    → reviewer workflow:
        for each canonical opponent (CooperateBot, DefectBot, MirrorBot, TitForTatBot):
            run search_proof(BotName, opponent)
            record (opponent, action_pair)
    → present outcomes to human: "Your bot cooperates with X, defects against Y..."
    → human accepts → write bot + proofs to library
```

**Design decisions:**
1. Bot writer agent has access to the full `Prog` language (all constructors including `.search`). No artificial restrictions — if a strategy needs `.search`, use it.
2. Reviewer is a **workflow** (not a second agent) for v1 — deterministic execution of `search_proof` against fixed canonical opponents, no LLM reasoning needed.
3. Automatic rewriter loop (reviewer feeds back into bot writer on mismatch) is deferred to v2.
4. Bot files go in `Bots/LlmGenerations/`, proofs in `Theorems/LlmGenerations/` (same pattern as phase 2).
5. Human acceptance gate before anything lands in the library.

**Bot writer agent:**
- **Input**: NL strategy description + desired bot name
- **System prompt**: embeds `Program.lean` (full `Prog` language + semantics), all existing bot definitions as few-shots
- **Tools**: `run_lean_build` (compile candidate bot file), `read_library_file` (inspect existing bots)
- **Output**: valid `Bots/LlmGenerations/BotName.lean`

**Milestones:**
1. **Bot writer agent** ✅ — `services/bot_service.py`. Input = NL description + bot name, output = compiled `.lean` bot file. Uses `run_lean_build` tool (lake env lean, not lake build). Bot files go in `Bots/LlmGenerations/`.
2. **Bot library writer** ✅ — `write_bot_to_library` in `library_writer.py`. Writes bot to `Bots/LlmGenerations/BotName.lean`. No `lake build` needed (bots imported transitively via theorem files).
3. **Pipeline script** ✅ — `eval/run_bot_pipeline.py`. CLI: `--bot-a-name`, `--bot-a-strategy`, `--bot-b-name`, `--bot-b-strategy`, `--model`, `--log-level`. Generates two bots, human gates for each, proof agent discovers+proves outcome, human gate for proof, writes to library. Handles existing bot names (overwrite / rename / use existing).
4. **Reviewer workflow** — deferred. Proof agent discovers outcome on its own; no separate prediction step needed.
5. **End-to-end test** ✅ — KindBot vs MeanBot pipeline ran successfully. Both bots compiled, proof found in 1 iteration, `lake build` green after write.
6. API+UI ✅ — FastAPI server (`api/main.py`, `pd-serve` CLI). Two-step async job with human acceptance gates at bots and proof. Minimal HTML/JS frontend at `/`. Start with `uv run pd-serve --reload`.
   - `POST /pipeline` returns 409 with `ConflictResponse` if any bot name already exists and no `conflict_resolution` is set.
   - Conflict resolution options: `use_existing`, `overwrite`, or rename (client changes the name and resubmits).
   - UI shows existing bot source on conflict, per-bot dropdown (use existing / overwrite / rename), rename input pre-filled with `<OldName>2`.
   - Bot review gate shows `existing` / `new` badge per bot. Proof review gate shows full Lean source before accept/reject.

**The OUTCOME-OPEN escalation ladder (2026-07-14).** The proof agent no longer dead-ends at
`OUTCOME OPEN` when the missing piece is a missing rule. Two production-only tools (registered
iff `exclude_bots` is empty — the eval harness never mutates the library):
1. **`add_base_lemma` (Tier 1, autonomous)** — grow a persistent DERIVED-rule library
   (`Theorems/LlmGenerations/LlmLemmas.lean`, namespace `PD.LlmLemmas`). Sound by
   construction (theorems only; `axiom`/`sorry`/`inductive`/`native_decide`/metaprogramming
   rejected by static guards); additive-only; transactional (byte-identical rollback on a
   failed `lake build`). Motivated by history: `boxInternalize`/`box_provable` were both
   thought to need axioms and turned out derivable.
2. **`propose_pf_constructor` (Tier 2, human-gated)** — for genuinely UNDERIVABLE rules the
   agent files an evidence bundle (`app/generated/constructor_proposals/<name>/`), never
   touching the engine. Machine gate: a **soundness certificate** — the rule's interp-level
   content proved as a theorem against the CURRENT engine, compiled by the tool (rejects
   FALSE rules; the historically-inconsistent `atom_complete_false_guard` could never have
   produced one). Human gate: the **faithfulness rationale** (sound-but-unfaithful rules like
   a semantic-completeness oracle are machine-undetectable by design). Integration follows
   the Phase-4 playbook in `PF_ONLY_ROADMAP.md`; at that point the floor/exclusion censuses
   (which quantify over ALL constructors) are the canaries.
Bare `OUTCOME OPEN` is now reserved for BISTABLE matchups (two fixed points, neither forced —
e.g. JustBot vs MirrorBot), where no sound rule can exist.

**Constructor integration (Stage C/D, landed 2026-07-27):** accepted Tier-2 proposals
are integrated by an INTEGRATION AGENT working in a git WORKTREE (never the live
tree) — constructor + `sound_upto` arm + `Pf_mono`/`Pf.induct` wiring + census/
metatheory repairs until BOTH lake targets are green (the compiling `sound_upto` arm
is the machine soundness gate) — then the `git diff` is human-reviewed and only on
acceptance applied to the real tree (rebuild + rollback). Two human gates end to end
(`/proposals/{name}/integrate`, `/integration/{job}/accept-diff`). Precedent: the
first proposal (`identImpl`, 2026-07-27) was integrated MANUALLY as `Pf.implRefl`
via the family-completion program before this flow ever ran; the agent flow remains
unexercised in anger.

**Deferred:** reviewer with outcome prediction (v2), automatic rewriter loop (v2).

## Phase 4 — Paper experiments (next)

Workshop paper target: ICML math workshop, 8 pages, framing "first mechanized OSGT library + LLM-assisted proof automation."

**Experiments to run:**

1. **E1 — Full bot-matrix proof automation (headline).** Run `search_proof` on every ordered pair of bots in the library (N² theorems). Report pass-rate, iterations-to-success, wall-clock. Stratify by bot complexity (constant bots vs. `.search`-using bots). If N grows past ~30, sample a stratified subset.
2. **E2 — NL→bot synthesis accuracy.** 10–20 NL strategy descriptions (mix of paraphrases of existing bots + genuinely new strategies). Measure: (a) compiles, (b) behaves as described against the four canonical opponents (CooperateBot, DefectBot, MirrorBot, TitForTatBot), (c) full pipeline end-to-end.
3. **E3 — Ablations.** At minimum: retrieval on/off, tool-feedback on/off (single-shot whole-proof vs. agentic loop).
4. **E4 — SOTA baseline (small slice).** Run Goedel-Prover-V2 or Kimina-Prover on 10–20 theorems from E1 to quantify the domain gap. Expected outcome: very low pass-rate (these are trained on competition math, not custom inductive types). Even a 0/20 result is publishable — it justifies the bespoke pipeline. Budget: 1–2 days, not a refactor.

**SOTA pipeline decision (not swapping in):** Do NOT replace the current Claude-based agent with DeepSeek-Prover / Goedel / Kimina / TheoremLlama / Lean Copilot / LeanDojo for v1 of the paper. Reasons: (1) those provers are fine-tuned on miniF2F/ProofNet-style competition math and are out-of-distribution for our custom `Prog` inductive type and `outcome_X_Y` templates; (2) LeanDojo/Lean Copilot are infrastructure, not drop-in solvers — our current `tools.py` + agentic loop already implements the LeanDojo retrieve-propose-check pattern; (3) the paper contribution is the mechanized OSGT library + NL→verified-outcome pipeline, not beating SOTA at proof search. Treat SOTA integration as future work, backed by E4 numbers.

## Phase 5 — TauBots: graded transparency (upcoming, design fixed 2026-07-31)

**Authoritative design note: `engine/PrisonersDilemma/Research/Notes/TAUBOT_TRANSPARENCY_DESIGN.md`** —
read it before touching anything tau. Summary of the FIXED decisions:

- **What it is.** Partial transparency as a Harsanyi type space over the zoo: a bot
  receives a **signal** — candidates `B₁…Bₙ` with weights `pᵢ` (blur in the weights,
  NEVER in the programs — prover bots need exact syntax, so every hypothesis is a real
  zoo member backed by a proven matrix cell). The σ family (temperature `t`) interpolates
  Critch's OSGT (`t=0`, point mass) ↔ classical opaque PD (`t=∞`, uniform → unconditional
  strategies). Headline experiment: *how much transparency does Löbian cooperation need?*
- **THE definition (Def 3 — self probe, base hypotheses):**
  `TauA(α)(sig) = C iff Σ{pᵢ : A's action in outcome(A, Bᵢ) = C} ≥ α`. Deterministic by
  expectation-then-threshold (NO probabilistic agents). Anchor theorem: at `t=0` the tau
  tournament equals the base matrix. REJECTED: Def 1 (tau hypotheses in the signal —
  ill-typed + ungrounded bistable recursion with no Löb rescue) and Def 2 (reciprocity
  probe `outcome(Bᵢ, A)` — a generalized-FairBot family, not a lift of A; doesn't
  converge to A at full transparency). `outcome(A(TauB)) = outcome(A(B))` is FALSE as a
  theorem (OSGT is intensional; costs scale with term size) but IS Def 3 as a stipulation.
- **Two dials, never conflated:** σ-temperature `t` = transparency (signal property;
  % scale via normalized mutual information); `α` = the agent's caution threshold.
- **Division of labor:** the tau layer is pure matrix-arithmetic ⇒ **experiments live in
  Python (`app/`)** over the exported matrix (the sheet-sync extraction +
  `outcome_status.toml` already provide the table incl. open cells) — σ family, behavioral
  Hamming distances, `(t, α)` phase-diagram sweeps, tau tournaments. A **thin Lean core**
  keeps only what must be a theorem: the meta-level `Signal`/`coopMass`/`tauPlay` defs,
  the anchor theorem, a few `decide`-certified sample cells cross-checking the Python.
- **Order of work:** v1a Python explorer → v1b Lean core → (only if the prover-vs-tau
  frontier matters) v2 compilation of TauBots to real `Prog`s (fixed signal ⇒ the
  threshold is a finite monotone boolean function ⇒ nested `.ite`/`.sim` tree, NO
  language extension) enabling mixed base-vs-tau matches and the **behavioral/prover
  split theorem** (blur invisible to sim-only bots, detectable exactly by the Löbian
  fragment).
- **Conventions still OPEN** (decide before implementing): open matrix cells (pessimistic
  vs renormalize), canonical budget per pair, static vs dynamic signals (static/compiled
  ⇒ TauB is extensionally a CONSTANT program — this silently kills the split theorem),
  δ vs σ inside counterfactual sims, `≥` vs `>` at the threshold.
