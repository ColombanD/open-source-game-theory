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
1. **Bot writer agent** ✅ — `services/bot_service.py`. Input = NL description + bot name, output = compiled `.lean` bot file. Uses `run_lean_build` tool (lake env lean, not lake build). Bot files go in `Bots/LlmGenerations/`, indexed by `Bots/LlmGenerations.lean`.
2. **Bot library writer** ✅ — `write_bot_to_library` in `library_writer.py`. Writes bot to `Bots/LlmGenerations/BotName.lean`, appends import to index. No `lake build` needed (bots not imported by root module).
3. **Pipeline script** ✅ — `eval/run_bot_pipeline.py`. CLI: `--bot-name`, `--strategy`, `--model`, `--log-level`. Runs bot writer → shows source → `[y/N]` human gate → writes to library.
4. **Reviewer workflow** — `services/reviewer.py`. Runs `search_proof` against canonical opponents (CooperateBot, DefectBot, MirrorBot, TitForTatBot), returns outcome table. **Deferred** — design: run all 4 sequentially, report pass/fail per opponent, default fuel=5 and let the proof agent adapt.
5. **End-to-end test** ← **NEXT**. KindBot is already generated and saved in `Bots/LlmGenerations/KindBot.lean`. Run `search_proof` manually against canonical opponents, verify proofs land in `Theorems/LlmGenerations/`. This validates the full Phase 3 story.
6. **Phase 4 / API+UI** — FastAPI endpoint: user submits NL description, gets back outcome table. Deferred.

**Deferred:** reviewer (design above), automatic rewriter loop (v2), API/UI.
