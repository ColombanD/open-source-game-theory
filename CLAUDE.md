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

Build: `cd engine && lake build`. Single root module `PrisonersDilemma.lean` imports
everything. Namespace `PD`. Layered bottom-up (each file imports the ones above):

| Layer | File(s) | What it defines |
|---|---|---|
| **Language** | `Program.lean` | `Action` (C/D), `Outcome`; the mutually-recursive `Prog` (agent source code — `.const/.self/.opp/.bot/.sim/.ite/.search`) and `Formula` (the logic agents reason in — `.plays/.impl/.neg/.box/.eq`); `subst`, `size`. Pure syntax — no actions until `eval`. |
| **Proof system `S`** | `Derivation.lean` | The inductive `Derivation`/`PlaysProof`/`AtomProvable`/`Provable k φ` (bounded provability, budget `k`); cost constants `c_leaf/c_node/c_guard`; `atom_cost`. This is `S`, the bounded modal logic agents query. |
| **Dynamics** | `Dynamics.lean` | The fuelled evaluator `eval` (its `.search` guard consults `proofSearch k φ := decide (Provable k φ)` — **currently `noncomputable`, see crux below**); `play`, `outcome`; `Formula.interp` (denotational semantics; `.box` = `Provable`). |
| **Axioms** | `Axioms.lean` | **ONE axiom remains**: `atom_complete_false_guard` (machine-proven irreducible, the Π₁ false-guard residue). `PBLT` is now a THEOREM (`BaseTheorems.bloeb_engine`/`pblt_engine`, 2026-07-01 — bounded Löb proven inside `Provable` via the internalized `.diag` fixpoint sentence); `box_provable`/`atom_box_provable_impl`/`boxInternalize` fell earlier to sound constructors; `c_guard_mono` demoted to a theorem. |
| **Meta-theorems** | `BaseTheorems.lean`, `SizeLemmas.lean` | Soundness (`Derivation.sound`, `proofSearch_sound`), `proofSearch_spec`/`_monotone`, `atom_complete`, size/log bounds. The bridge from provability to real plays. |
| **Bots** | `Bots/*.lean`, `Bots/LlmGenerations/*.lean` | The agent zoo: `CooperateBot`, `DefectBot`, `MirrorBot`, `TitForTatBot`, `DupocBot`, `CupodBot`, `EBot`, … and LLM-generated `PrudentBot`, `JustBot`, `CIMCIC`, `DIMCID`. |
| **Outcome theorems** | `Theorems/*.lean`, `Theorems/LlmGenerations/*.lean` | The headline results: `outcome_X_vs_Y = some (a,b)` (and `∃k₂,∀k>k₂,…` families). Hand-written + LLM-written (`llm_outcome_` prefix; indexed via `Theorems/LlmGenerations.lean`). |
| **Computable evaluator** | `ComputableEval/` | `evalC` — a sound, total, computable **partial** evaluator (the reviewer-facing demo); see crux. |
| **Research notes** | `Research/Notes/`, `Research/Readings/`, `Research/Data/` | Theory write-ups (esp. `COMPUTABLE_EVAL_NOTES.md`, `UnderstandingTheLayers.md`), extracted source papers, tournament data. |

**The strict outcome-theorem template** is the linchpin the whole pipeline relies on:
`outcome_X_Y = some (.Action_X, .Action_Y)`. Because the statement is fully concrete,
**compilation == correctness** — an LLM-written proof that type-checks is, modulo the
NL→Lean *bot* translation, a verified result.

## Foundational crux — why `eval` is `noncomputable`, and what would fix it

This is the theoretical heart of the project. Authoritative write-up:
`engine/PrisonersDilemma/Research/Notes/COMPUTABLE_EVAL_NOTES.md`.

- A reviewer flagged that the central evaluator `eval` is `noncomputable`. The current, honest
  status (updated 2026-07-01, after the `PBLT` deletion): **not a Gödel/Π₁ wall; the Löb side is
  fully discharged; the remaining block is (a) one irreducible Π₁ axiom and (b) an open
  decidability question.**
- The `.search` guard is a bounded-provability oracle `proofSearch k φ = decide (Provable k φ)`.
- **UPDATE (2026-07-01): bounded Löb / `PBLT` is now a THEOREM** (`BaseTheorems.bloeb_engine`/
  `pblt_engine`, via the internalized fixpoint sentence `Formula.diag` + the `diagF`/`diagB`/
  `axKf`/`impS2` rules — `Research/Notes/INTERNALIZATION_ROADMAP.md`). Every Löb-fixpoint
  cooperation (PrudentBot↔DupocBot etc.) now has a REAL constructor tree — no witness-free axiom
  injects `Provable` members on the Löb side anymore. **Engine axiom count: 1**
  (`atom_complete_false_guard`, machine-proven irreducible — the Π₁ false-guard residue).
- **Why `eval` is STILL noncomputable:** decidability of `Provable k φ` (∃ proof TERM of size ≤ k)
  is OPEN. Naive enumeration is refuted (the `mp`-cut ranges over infinitely many provable cut
  formulas; atom-closure is false — machine-checked in `Research/Spikes/pblt/MN1_decidable.lean`);
  a decision procedure would need cut-elimination-style normal forms. Separately,
  `atom_complete_false_guard` still injects witness-free `AtomProvable` members. So "Löb proven"
  ≠ "eval computable" — do not conflate (they were decoupled by the internalization).
- **Shipped (option D, build green, no new axioms):** `engine/PrisonersDilemma/ComputableEval/`
  — `evalC`, a sound TOTAL computable PARTIAL evaluator (3-valued guard; commits only with a finite
  witness, returns `none` exactly at the Löb fixpoints; `outcomeC_sound` proven). It answers the
  reviewer concretely and locates the boundary. `c_guard_mono` was demoted axiom→theorem.
- **Dead ends (do not retry):** deciding `Provable k φ` by structural recursion on the program
  (refuted, `DecMeasure.lean`); the `derivable`/`playsCheck` separate-search-gas checker
  (non-monotone); decidability by proof-term enumeration (mp-cut wall, `MN1_decidable.lean`);
  model/realizability witness extraction (unsound, `ConstructiveLobToy.lean` §8).
- **`atom_complete_false_guard` is the floor:** proven irreducible (the else-play's certificate
  type is provably EMPTY — `ComputableEval/Exclusion.lean`); it does not fall to any known lever.

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
- `LlmGenerations.lean` acts as the index file; `PrisonersDilemma.lean` imports it once.
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

**Deferred:** reviewer with outcome prediction (v2), automatic rewriter loop (v2).

## Phase 4 — Paper experiments (next)

Workshop paper target: ICML math workshop, 8 pages, framing "first mechanized OSGT library + LLM-assisted proof automation."

**Experiments to run:**

1. **E1 — Full bot-matrix proof automation (headline).** Run `search_proof` on every ordered pair of bots in the library (N² theorems). Report pass-rate, iterations-to-success, wall-clock. Stratify by bot complexity (constant bots vs. `.search`-using bots). If N grows past ~30, sample a stratified subset.
2. **E2 — NL→bot synthesis accuracy.** 10–20 NL strategy descriptions (mix of paraphrases of existing bots + genuinely new strategies). Measure: (a) compiles, (b) behaves as described against the four canonical opponents (CooperateBot, DefectBot, MirrorBot, TitForTatBot), (c) full pipeline end-to-end.
3. **E3 — Ablations.** At minimum: retrieval on/off, tool-feedback on/off (single-shot whole-proof vs. agentic loop).
4. **E4 — SOTA baseline (small slice).** Run Goedel-Prover-V2 or Kimina-Prover on 10–20 theorems from E1 to quantify the domain gap. Expected outcome: very low pass-rate (these are trained on competition math, not custom inductive types). Even a 0/20 result is publishable — it justifies the bespoke pipeline. Budget: 1–2 days, not a refactor.

**SOTA pipeline decision (not swapping in):** Do NOT replace the current Claude-based agent with DeepSeek-Prover / Goedel / Kimina / TheoremLlama / Lean Copilot / LeanDojo for v1 of the paper. Reasons: (1) those provers are fine-tuned on miniF2F/ProofNet-style competition math and are out-of-distribution for our custom `Prog` inductive type and `outcome_X_Y` templates; (2) LeanDojo/Lean Copilot are infrastructure, not drop-in solvers — our current `tools.py` + agentic loop already implements the LeanDojo retrieve-propose-check pattern; (3) the paper contribution is the mechanized OSGT library + NL→verified-outcome pipeline, not beating SOTA at proof search. Treat SOTA integration as future work, backed by E4 numbers.
