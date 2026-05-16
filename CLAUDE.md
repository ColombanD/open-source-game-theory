# Project Guidelines

## Package management

Always use `uv` for Python package operations — never `pip` directly.

- Install/sync: `uv sync` (inside `app/`)
- Add a dependency: `uv add <package>` (inside `app/`)
- Run a script: `uv run <script>` (inside `app/`)
- Run tests: `uv run pytest` (inside `app/`)

## Project vision — LLM bot+proof pipeline

Next phase of the project: automate the creation of bots and proofs that today are written manually (`engine/PrisonersDilemma/Bots/`, `engine/PrisonersDilemma/Theorems/`).

**Architecture:**
- Frontend UI: two programs enter the pipeline → game outcome out. Input programs can be LLM-generated, user natural-language, or chosen from a predefined set.
- Backend: Lean engine with an LLM writing proofs. Uses the existing library as RAG context / few-shot examples.

**Design decisions:**
1. Proof agent may only ADD new files, never modify existing ones (v1 safety).
2. Theorem statements use a strict template — `outcome_X_Y = some (.Action_X, .Action_Y)` — so compilation == correctness, modulo the NL→Lean bot translation step.
3. NL→Lean translation accuracy is the remaining weak link; plan is to use an agent reviewer + few-shotting from existing bots.
4. Human-in-the-loop v1: human accepts each new bot and theorem before it lands in the library.
5. Foundational issues with the proof system S (temporary axiom for CupodBot self-play) are expected to be fixed before MVP and are not a blocker for design.

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
