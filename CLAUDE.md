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
| **Axioms** | `Axioms.lean` | **ZERO project axioms** (2026-07-03): the last one, `atom_complete_false_guard`, was machine-checked INCONSISTENT (anti-diagonal bot, `Research/Spikes/transcript/T32Inconsistency.lean`) and DELETED — replaced by the sound `search_f`/`atomNeg`/`eqNeg` machinery with a cost FLOOR. `PBLT` fell 2026-07-01 (theorem via the `.diag` fixpoint); everything rests on Lean's 3 standard axioms. Costs are transcript-cumulative (Critch's literal model) since 2026-07-02. |
| **Meta-theorems** | `BaseTheorems.lean`, `SizeLemmas.lean` | Soundness (`Derivation.sound`, `proofSearch_sound`), `proofSearch_spec`/`_monotone`, `atom_complete`, size/log bounds. The bridge from provability to real plays. |
| **Bots** | `Bots/*.lean`, `Bots/LlmGenerations/*.lean` | The agent zoo: `CooperateBot`, `DefectBot`, `MirrorBot`, `TitForTatBot`, `DupocBot`, `CupodBot`, `EBot`, … and LLM-generated `PrudentBot`, `JustBot`, `CIMCIC`, `DIMCID`. |
| **Outcome theorems** | `Theorems/*.lean`, `Theorems/LlmGenerations/*.lean` | The headline results: `outcome_X_vs_Y = some (a,b)` (and `∃k₂,∀k>k₂,…` families). Hand-written + LLM-written (`llm_outcome_` prefix; indexed via `Theorems/LlmGenerations.lean`). |
| **Decidability** | `Decidability/` | The T3.2c/T4 chain (modules keep milestone names `T31`…`T47`; umbrella `Decidability.lean` re-exports the API): `decFull` (verified enumerator, `Provable_iff_decFull`), `evalG` (computable evaluation of search bots, sound both guard polarities, `#eval` demos), `ProvableG` strata + `CutRelevance` (THE open conjecture), the modest universe, and `decideProvableG : Decidable (ProvableG (modestGate N) k φ)` with computable fuel bound. |
| **Computable evaluator (historical)** | `ComputableEval/` | `evalC` — the original sound computable partial evaluator; SUPERSEDED by `Decidability`'s `evalG` (kept building, header marks it historical). |
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
- **Open — exactly ONE conjecture (T4.1b, `CutRelevance` in `Decidability/T42ProvableB.lean`)**: a
  computable `N₀` with `Provable k φ → ProvableG (modestGate (N₀ k φ)) k φ` (minimal
  derivations never need exotic cuts). Given it: `proofSearch` becomes decidable, `eval`
  computable, outcomes `by decide`. If it FAILS, `Provable` is a candidate undecidable
  bounded-provability predicate — either resolution is thesis-grade. ATTACK STATE
  (2026-07-03, see `Research/Notes/CUT_RELEVANCE.md` + `Research/Spikes/transcript/`
  `T48`/`T49`): judgment-local invariants REFUTED (3 kernel-checked counterexamples);
  conjecture REDUCED to atom modesty via the tree substrate (`ProvT`, exact) + the
  extraction machine (`boxInvGo` — runs, correct by construction, weight/diet/depth-
  conserving, total with closed-form fuel on the contraction-free fragment). Open
  kernel: `impS2`-contraction totality (local-charge measures provably insufficient —
  needs Tait/Gentzen machinery, or per-instance #eval certificates for zoo trees).

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
