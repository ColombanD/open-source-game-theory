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

## Phase 2 milestones (proof-writing first)

Start with proof-writing for human-written bots/theorem statements, NOT end-to-end NL→bot→proof. The agentic Lean loop is the riskiest unknown; test it against existing ground-truth proofs first.

**Milestones:**
1. **Real LLM client** ✅ — `llm/client.py` replaced with Anthropic-SDK-backed client (multi-turn tool use, prompt caching).
2. **Lean tools for the agent** ✅ — `llm/tools.py` wraps `run_lean_proof_file` + `read_library_file` as Claude tool definitions. Fast per-iteration check (no `lake build`).
3. **Retrieval over the library** — given target theorem, return most relevant existing proofs as few-shot context. Start with structural match on bot names using `_UNIVERSAL_OUTCOME_THEOREMS` / `_EXISTENTIAL_OUTCOME_THEOREMS`.
4. **Proof-search loop in `proof_service.py`** — the actual agent. Input = theorem statement, output = proven `.lean` file or failure. Loop: retrieve few-shots → propose proof → run Lean → feed errors back → iterate up to N steps.
5. **Evaluation harness** — pick ~10 existing theorems, hide proofs, have agent re-prove them. Measure success rate, iterations, token cost.
6. **Library writer** — on success, write proof to new file under `engine/PrisonersDilemma/Theorems/`. Confirm `lake build` passes. Add human-acceptance gate.

**Deferred:** NL→bot synthesis, behavioral testing vs canonical opponents, API/UI for human-accept flow.
