# Poster Cheat Sheet — Proof-Based Open Source Game Theory in Lean

*ICML AI4Math Workshop. Authors: Colomban Duclaux, Riccardo Formenti, Pepijn Cobben, Bernhard Schölkopf, Zhijing Jin*

---

*A standalone briefing for whoever is presenting this poster. Read it once start to finish, then keep the "Questions you'll get" boxes and the closing "sentences to never forget" within reach at the poster itself.*

**How it's organized:** a 30-second pitch and the three contributions up front (enough to field a passing glance), then one deep-dive section per contribution — the **Lean engine** (what's verified), the **agentic pipeline** (how the proofs get written), and the **equilibrium analysis** (what it all buys us) — each closing with the objections you're most likely to hear and how to answer them. Throughout, "we" means the authors and "you" means you, standing at the poster.

**The core claim in one breath:** open-source game theory says cooperation becomes rational when programs can read each other's source code; we made that theory machine-checkable in Lean, taught an LLM to write the proofs, and then used the verified results to show the cooperative equilibria actually appear.

## The 30-second pitch

Cooperation is hard in multi-agent settings: every agent has a private incentive to defect, free-ride, or overexploit (think overfishing, arms races, emissions). **Open Source Game Theory (OSGT)** offers a way out: if players submit *programs* that can read each other's source code, then commitments become *verifiable*, and mutual cooperation can become a Nash equilibrium even in the Prisoner's Dilemma.

**The catch:** OSGT so far lives only on paper. Its proofs lean on modal logic and Gödel/Löb-style self-reference — hard to write, easy to get wrong, and impossible to machine-check.

**What we did:** We built the first **Lean 4 formalization** of OSGT (so the proofs are machine-verified), plus an **LLM agent that writes those Lean proofs automatically** from a bot pair or a natural-language strategy, plus a **Nash-equilibrium analysis** of the resulting bot meta-game.

One line if someone's rushing past: *"We turned open-source game theory from pen-and-paper modal logic into a machine-checked Lean library, and taught an LLM to write the proofs."*

---

## The three contributions (one panel each)

**Contribution 1 — Lean 4 formalization of OSGT.** The agent language, the evaluator, the proof oracle, and machine-checked outcome theorems for a library of bots. This is the foundation.

**Contribution 2 — Agentic pipeline (NL → proof).** An LLM agent that (a) writes the Lean *proof* for a given bot matchup, and (b) writes the Lean *bot itself* from a natural-language strategy description. Built on the Anthropic API with a tool-use loop (write candidate → run Lean → read errors → retry), few-shot retrieval from the existing library, and a human acceptance gate.

**Contribution 3 — Nash equilibria analysis.** We enumerate every mixed Nash equilibrium of the PD meta-game, restricted to the implemented bot library.

---

## Headline numbers

- **40 / 45 bot-pair outcome theorems proved automatically (≈ 89%)** by the LLM agent, with no human edits to the proofs.
- The pass/fail split tracks formal difficulty almost exactly:
  - **32 / 32** on every pair *without* a `.search` bot on both sides — these close nearly by Lean's evaluator alone (median 1–2 iterations, under 90 s).
  - **6 / 10** on simulation × `.search` pairs — these must chain the oracle axioms, and cost roughly an order of magnitude more in both iterations and wall-clock.
- **Five pairs go unproved, but only one is a genuine failure:** `CupodBot` vs `DupocBot` — the `.search`-vs-`.search` cell that is Critch's known open problem, expected to be unprovable in the library as it stands. (In the equilibrium analysis, that single cell is fixed by configuration to its conjectured value `(C, D)`.) The other four are hard simulation × `.search` proofs where the agent hit the per-call output-token ceiling *mid-proof*, not a dead end — in the first pass all seven misses were token-truncation, and raising the per-call budget from 16k to 32k recovered two, giving the final 40/45. Say this confidently if asked.

---

## How the Lean engine works (plain English)

Repo layout: `engine/` (Lean) and `app/` (Python pipeline). The whole formalization rests on **two mutually-recursive languages**: `Prog`, the language of *agents* (source code), and `Formula`, the language of *claims that agents reason about*. They're mutually recursive on purpose — a bot can search for a proof of a formula, and a formula can talk about what bots do. Agents reasoning about agents reasoning about agents.

### `Prog` — the agent language (`Program.lean`)

A bot is *pure source code* — no constructor produces an action directly; actions only appear once `eval` runs the code. Built from:

| Constructor | Meaning |
|---|---|
| `.const a` | Always play action `a` (CooperateBot / DefectBot). |
| `.self` / `.opp` | Placeholders for "my source" / "opponent's source", closed by `subst` at each evaluation boundary. |
| `.sim p q` | Source code for "run `p` with `q` as its opponent". |
| `.ite b a p q` | If running guard `b` yields action `a`, run `p`, else `q`. |
| `.search k φ p q` | Ask the oracle to prove formula `φ` within budget `k`; if it succeeds run `p`, else `q`. |
| `.bot p` | A closed reference to another named bot — a scope barrier so the outer frame's `me`/`opp` can't capture `p`'s internals. |

`.self`/`.opp` are free variables; `subst` freezes them to the concrete programs currently playing whenever evaluation enters a new context (`.sim`, `.search`). This is what lets the oracle receive a **closed** formula with no dangling placeholders.

### `Formula` — what agents prove about each other (`Program.lean`)

This is the part of the ambient logic that agents query through the oracle. It is **deliberately not a full internalization** of the proof system — only the constructs the theorems actually need:

| Constructor | Meaning |
|---|---|
| `.plays p q a` | Atomic: "`p` plays action `a` against `q`". |
| `.impl φ ψ` | `φ → ψ`. Needed for Löb-style hypotheses like `□C → C`. |
| `.neg φ` | `¬ φ`. |
| `.box k φ` | `□ₖ φ`: "`φ` is provable by the oracle with budget `k`". The modal operator. |

The point to be able to make under questioning: **`.box` is syntax for provability, not truth.** A formula can be *true* without being *provable within budget k*, and that gap is exactly where Löb's theorem lives.

### `eval` — fuel-bounded interpreter (`Dynamics.lean`)

Bots can simulate each other recursively without bound, so `eval` carries **fuel** (a step budget). It returns `some action`, or `none` if fuel runs out. Fuel is what makes `eval` a *total, terminating* function — the precondition for Lean reasoning about it at all. More fuel = deeper nested simulations; each `.sim` step costs one unit.

- `play fuel me opp` = one agent's move (run `me` against `opp`).
- `outcome fuel p q` = the pair `(play p q, play q p)`.

### Two notions of truth — and why it matters

There are **two** ways the system talks about a formula being "true", and keeping them apart is the cleanest thing to demonstrate fluency on:

- **Operational / syntactic:** `proofSearch k φ` — an **axiomatized oracle** meaning "there's a proof of `φ` of size ≤ k". This is what `eval` actually calls at a `.search` node. It's an axiom because we reason *about* a bounded prover without implementing one — it stands in for the ambient proof system `S`.
- **Denotational / model:** `Formula.interp` maps a `Formula` to a real Lean `Prop` — e.g. `.plays p q a` interprets as `∃ n, play n p q = some a` (it genuinely plays `a`), and `.impl`/`.neg` map to honest Lean `→`/`¬`. This is *truth in the model*, independent of any prover.

The oracle and the model are bridged by the axioms below: **soundness** says provable ⇒ true, **completeness** (for the decidable fragment) says true ⇒ provable. Once you have that bridge, every outcome theorem is an ordinary Lean derivation.

### The bot library, by tier

| Tier | Bots | What they do |
|---|---|---|
| 0 — constant | CooperateBot, DefectBot | Ignore opponent, fixed action. |
| 1 — simulation | MirrorBot, TitForTatBot, DBot, OBot, EBot | `.sim` the opponent against a fixed probe (CooperateBot/DefectBot) and branch on the result. |
| 2 — search | CupodBot, DupocBot | Use the `.search` oracle + the modal machinery (Löb). |

```lean
-- CupodBot: cooperate unless a proof the opponent defects is found within k steps
def CupodBot (k : Nat) : Prog :=
  .search k (.plays .opp .self Action.D) (.const Action.D) (.const Action.C)

-- EBot: nested probes — sim opp vs DefectBot, then CooperateBot, then MirrorBot
def EBot : Prog := .ite (.sim .opp (.bot DefectBot)) Action.C (.const Action.D) ( ... )
```

### Why axioms instead of building the proof system `S` explicitly

This is the design decision most likely to draw a sharp question, so it's worth being able to defend it crisply.

A "complete" formalization would construct the entire ambient logic `S` from scratch: a deductive calculus, Gödel numbering, an internal provability predicate, and a full machine derivation of Löb's theorem. That is an enormous metatheoretic project — and it is **not the contribution of this paper.** Instead we model `S` *abstractly* through a small, auditable **interface** (`Axioms.lean`):

- **`proofSearch_spec`** — the oracle returns true iff a witness of size ≤ k exists. This pins down what "bounded provability" means.
- **`witness_sound`** — anything a witness proves is actually true in the model (`witnessProves w φ → φ.interp`). The soundness bridge.
- **`witness_complete_plays`** — the *converse*, but **restricted to atomic `.plays` formulas**: if a bot genuinely plays an action, the oracle can find a witness. This restriction is principled, not lazy — `.plays` claims are decidable arithmetic (Σ₁), so completeness holds *there* without running into Gödel. We don't assume full completeness because full completeness is false.
- **`proof_system_verifies_search_branch` / `proof_system_verifies_sim`** — "S can read source code": if a bot's literal body is a `.search` or `.sim` node, S can inspect that code and verify how it branches. Critch uses these steps silently on paper; we make them explicit assumptions.
- **`PBLT` — Parametric Bounded Löb's Theorem** (Lemma 3.6, Critch 2022). The self-reference engine: it's what lets `□φ → φ`-style hypotheses collapse into outright provability of `φ`, which is exactly what makes mutual cooperation provable. If someone asks "where's the magic?" — it's here.

The framing to land: **the axioms are an interface specification of a sound, bounded prover satisfying Löb — all of them are standard, well-understood metatheoretic facts.** The *novel, risky* content — the actual bot behaviors and the equilibria — is **derived** on top of that interface, not assumed. So "the Lean file compiles" means the outcome is verified *modulo a small, fixed, auditable axiom set*, rather than modulo a giant hand-built metatheory we'd also have to trust.

You can see the payoff in `Theorems/ProofSearch.lean`: `proofSearch_sound`, `proofSearch_complete_plays`, and `proofSearch_monotone` are **theorems** (proved from the axioms), not further assumptions — the derived layer already starts doing real work on top of the interface.

### Questions you'll get

**"Isn't `proofSearch` just an axiom — aren't you assuming what you want to prove?"**
We axiomatize the *oracle* (an abstract bounded prover) and its specification, **not** the individual outcomes. Every outcome theorem is *derived*. The oracle stands in for the background proof system, exactly as Critch does on paper; modeling its internals is out of scope. Σ₁-completeness for atomic "plays" formulas is decidable arithmetic — no Gödel issue there.

**"What about Gödel / Löb's theorem?"**
The cooperative equilibria genuinely need Löb's theorem — you can't naively prove "if I cooperate, you cooperate" without self-reference paradoxes. We encode a **Parametric Bounded Löb's Theorem** as an axiom and apply it. That's the engine behind the search-bot proofs.

**"Why fuel? Why not just run the bots?"**
Bots can simulate opponents that simulate them, ad infinitum. Fuel bounds recursion depth so `eval` is a *total, terminating* function — which is what lets Lean reason about it at all.

---

## The agentic pipeline: NL → verified proof (Contribution 2)

The Lean library is hand-written ground truth. Contribution 2 is the claim that an **LLM agent can produce those machine-checked proofs on its own** — and, one step further, can write the *bots* themselves from a plain-English strategy description. The project got there in two stages.

### Stage 1 — proof-writing (the validated core)

Given a bot pair and a claimed outcome, an agent writes the Lean proof and verifies it. It's a tool-use loop, not a one-shot generation:

1. **Retrieve** the most relevant existing theorem files as few-shot context (name match first, then content); the bot *definitions* are always injected up front.
2. **Propose** a candidate Lean proof.
3. **Check** it with the `run_lean_proof` tool — a fast per-iteration `lake env lean` call (no full `lake build`).
4. **Read the errors** and retry; the agent can also call `read_library_file` to inspect any file under `engine/PrisonersDilemma/`.
5. On success, the **library writer** writes the proof into `Theorems/LlmGenerations/`, runs a real `lake build`, and **rolls back on failure**.

This is the classic retrieve–propose–check pattern (the same shape as LeanDojo), implemented over the Anthropic API with multi-turn tool use and prompt caching.

**Why "it compiles" means "it's correct."** Theorem statements use a strict template — `outcome_X_Y = some (.A, .B)`. There's no room for the agent to prove a weaker or different claim: either the Lean kernel accepts a proof of *exactly* that outcome, or it doesn't. So a green build *is* the verification. The only trust left outside the kernel is the NL→bot translation step (see Stage 2).

### Stage 2 — NL → bot synthesis (the end-to-end extension)

Stage 1 assumes the bot already exists in Lean. Stage 2 removes that assumption:

- A **bot-writer agent** takes an English strategy description + a name and emits a compiling `Bots/LlmGenerations/BotName.lean`, using the full `Prog` language and every existing bot as a few-shot example (tool: `run_lean_build`).
- A **reviewer workflow** — deterministic, not a second LLM — runs the new bot against the canonical opponents (CooperateBot, DefectBot, MirrorBot, TitForTatBot) via the Stage-1 proof agent and records what it actually does.
- The outcomes are surfaced to a **human acceptance gate** ("your bot cooperates with X, defects against Y…") before anything lands in the library.

End-to-end this has run cleanly (the KindBot-vs-MeanBot pipeline: both bots compiled, proof found, `lake build` green), and there's a small FastAPI + HTML front end exposing the whole flow with the human gates in place.

**Safety by construction (v1).** The agent may only *add* new files, never modify existing ones, and every new bot and proof passes a human gate before entering the library. Generated theorems are namespaced `llm_outcome_X_vs_Y` so they can't clash with or silently overwrite the hand-written ones.

### The headline result

Run the proof agent on **every ordered pair** in the 9-bot matrix (45 theorems) and it closes **40 of 45**. The structure of the successes and failures is the interesting part, and it lines up exactly with the formal complexity tiers from the Lean section:

| Matchup tier | Pass rate | Cost | Why |
|---|---|---|---|
| No `.search` bot on both sides (tiers 0×0, 0×1, 0×2, 1×1) | **32/32** | median 1–2 iterations, < 90 s | These close by Lean's evaluator alone, modulo small rewriting — the agent just has to find the right unfolding lemmas. |
| Simulation × search (1×2) | **6/10** | ~10× more iterations and wall-clock | These must *chain the oracle axioms* — soundness, completeness, witness transport, PBLT, the code-reading axioms. Hard. |
| Search × search (2×2) | the one true failure | — | `CupodBot` vs `DupocBot` — Critch's open problem, expected to be unprovable in the library as it stands. |

A detail worth stating confidently: of the 7 misses in the first pass, **all 7 failed with `stop_reason = max_tokens`** — the agent was *truncated mid-proof*, not stuck. Re-running those pairs with the per-call output budget raised from 16k to 32k tokens recovered 2 of them, giving 40/45. So the empirical bottleneck on the failures is output budget, not the agent running out of ideas — *except* for the genuine `(CupodBot, DupocBot)` open problem, which no budget would fix.

### Questions you'll get

**"How do you know the agent didn't just hallucinate a proof?"**
It can't. The proof is checked by the Lean kernel, and the theorem statement is a fixed template pinning the exact outcome. A hallucinated or wrong proof simply fails `lake build` and gets rolled back. The kernel, not the LLM, is the source of truth.

**"Isn't the agent just copying the answer from the few-shot examples?"**
The evaluation explicitly guards against this: for each target pair, the harness *excludes that bot pair* from both the few-shot retrieval and the known-theorems summary, so the answer can't leak in. The 40/45 is on leak-free runs.

**"Which model, and how much hand-holding?"**
Claude Opus 4.7 with extended thinking, in an agentic loop with a default cap of 20 tool-use iterations per proof. On the easy tiers it converges in 1–2 iterations; the cost concentrates entirely on the axiom-chaining `.search` proofs.

**"What's the real limitation, then?"**
Two honest ones. (1) The NL→bot translation in Stage 2 is the least-guaranteed link — a faithful-looking English description can yield a subtly different bot — which is why the reviewer workflow + human gate exist. (2) The hard `.search × .search` proofs sit right at the foundational gap in the axiom interface, and closing them is the principal direction for future work.

---

## The equilibrium analysis (Contribution 3)

This is the "so what" of the whole paper: once the outcome matrix is machine-verified, we can ask what *equilibria* the bot library actually supports — and show that open-source play escapes the tragedy of the Prisoner's Dilemma.

### The question

In the ordinary one-shot PD, defection strictly dominates, so `(D, D)` is the **unique** Nash equilibrium — payoff `0`, cooperation rate `0` — even though both players would prefer `(C, C)`. The meta-game `G^prog` enlarges each player's strategy set from *two actions* to *the whole library of programs*: a "mixed strategy" is now a probability distribution over **which bot you submit**. The question is whether this larger strategy space buys you *new* equilibria — in particular, cooperative ones that the base game structurally forbids.

### Setup (how the bimatrix is built)

- **8 bots.** We take the library programs with a well-defined self-play outcome: CooperateBot, DefectBot, DBot, EBot, OBot, TitForTatBot, CupodBot, DupocBot. *MirrorBot is excluded — it doesn't terminate against itself*, so it has no self-play cell. (Useful Q&A fact.)
- **The payoff matrix is the Lean-verified outcome matrix.** Each ordered bot pair's action outcome comes from the machine-checked theorems — **63 of the 64 cells**. The single exception is the `(CupodBot, DupocBot)` cell, fixed by configuration to `(C, D)` (Critch's conjectured value) — *the same cell the proof pipeline can't close.* That's not a coincidence to hide; it's the one genuinely open problem, and it shows up identically in both halves of the paper.
- **PD payoffs** `(T, R, P, S) = (3, 2, 0, -1)`: temptation 3, reward 2, punishment 0, sucker −1.
- **Enumeration.** We compute *every* extreme Nash equilibrium with `lrsnash` (from `lrslib`), using the labelled best-response-polytope method of Avis et al., in **exact rational arithmetic** (no floating-point error — supports and probabilities come out as exact fractions). A positivity shift is applied to the matrix; it leaves the equilibrium set exactly invariant.

One honest scoping point worth volunteering: the *inputs* (the outcome matrix) are Lean-verified; the *equilibrium enumeration itself* is a separate exact-arithmetic computation, not a Lean proof. The machine-checking guarantees the game we're solving is the right one.

### The result

The enumeration yields **exactly 16 extreme Nash equilibria, grouped into 5 Nash components.** A *Nash component* is a maximal connected family of equilibria (in the sense of Jansen): a polytope `X × Y` of mixed strategies. The 16 rows in the paper's table are its **vertices** — and by convex closure, *every* convex combination within a component is also an equilibrium. So the cooperative outcomes aren't isolated knife-edge points; they form a positive-measure set. Payoff and cooperation rate are constant across a component.

The headline is the **spectrum** of cooperation rates `Pr[(C,C)]` that appear in equilibrium:

| Component | `Pr[(C,C)]` | Payoff `u = v` | Supported on (key bots) |
|---|---|---|---|
| Full cooperation | `1` | `2` (Pareto-optimal `R`) | CooperateBot, **DupocBot**, TitForTatBot |
| Partial | `11/18 ≈ 0.61` | `3/2` | CooperateBot, OBot, EBot |
| Partial | `14/27 ≈ 0.52` | `4/3` | CooperateBot, DupocBot, OBot, EBot |
| Partial | `43/147 ≈ 0.29` | `6/7` | CooperateBot, DefectBot, DupocBot, OBot, EBot |
| Mutual defection | `0` | `0` | DefectBot (+ OBot) |

The base-game equilibrium `(D, D)` survives as the `Pr[(C,C)] = 0` component, exactly as expected. But the meta-game also admits an **entire component of full-cooperation equilibria** at the efficient payoff `R = 2` — an outcome that is *structurally unreachable* in equilibrium of the underlying PD. The PD has cooperation image `{0}`; the meta-game has `{1, 11/18, 14/27, 43/147, 0}`, the full range from total defection to total cooperation.

### The punchline: DupocBot is necessary for full cooperation

This is the result to lead with if someone asks "what's the one finding?" Take the full-cooperation component and intersect the supports across all its vertices. The intersection is exactly `{DupocBot}` — **every** full-cooperation equilibrium puts positive mass on DupocBot on *both* sides. Remove DupocBot from the library and the entire full-cooperation component collapses; nothing left supports a cooperation rate above `11/18`.

So **DupocBot is the unique element of the library whose presence is necessary for full mutual cooperation to arise as a rational, equilibrium phenomenon.**

The reason ties straight back to the engine. Naive CooperateBot can *never* anchor a cooperative equilibrium — against two CooperateBots, either player profits by switching to DefectBot and grabbing `T > R`. DupocBot can, because it's **unexploitable**: it only cooperates when it has an actual proof the opponent cooperates against it, so it never eats the sucker payoff `S`. And the reason it cooperates *with itself* is the Parametric Bounded Löb's Theorem from the Lean section above — `DupocBot(k)` locates, within its own budget `k`, a proof that `DupocBot(k)` cooperates against `DupocBot(k)`, and acts on it. The equilibrium result is the **population-level shadow of that self-cooperation theorem.**

### Questions you'll get

**"You only verified 63 of 64 cells — isn't the result built on an unproven assumption?"**
The one unverified cell, `(CupodBot, DupocBot)`, is fixed to Critch's conjectured value `(C, D)`. It's a single entry, clearly flagged, and it's the known open problem of the field — the same cell the proof agent can't close. Every other cell is machine-checked.

**"Why 8 bots and not all 9?"**
MirrorBot has no well-defined self-play outcome (it doesn't terminate against itself), so it can't sit on the diagonal of the payoff matrix. The other eight all have a defined self-play cell.

**"A mixed strategy over *programs* — what does that mean physically?"**
You randomize over which bot you submit before the game runs. A full-cooperation equilibrium might be "submit DupocBot with probability 2/3, CooperateBot 1/9, TitForTatBot 2/9" — and the claim is no unilateral re-weighting does better.

**"Why are there 16 equilibria but only 5 'real' outcomes?"**
Equilibria here come in convex families (Nash components), not as isolated points. The 16 are the polytope vertices; any blend within a component is also an equilibrium, and payoff + cooperation rate are constant across the whole component. So there are 5 genuinely distinct equilibrium *behaviors*.

**"Is the equilibrium computation also in Lean?"**
No — and that's the clean division of labor. Lean verifies the outcome matrix (the game). The equilibrium enumeration is a separate exact-rational computation with `lrsnash`. We're solving a game whose rules are machine-certified.

### One sentence to never forget

*Enlarging the strategy space from actions to programs turns the PD's unique defection equilibrium into a full spectrum of cooperative equilibria — up to full cooperation at the efficient payoff — and provability-conditioned DupocBot is the one program without which that full-cooperation equilibrium disappears.*

---

## The 3 sentences to never forget

1. **Open-source game theory makes cooperation a Nash equilibrium by letting programs read each other's source code — but its proofs were pen-and-paper modal logic.**
2. **We built the first machine-checked Lean 4 library of it, with a bounded proof oracle and Löb's theorem encoded as axioms.**
3. **An LLM agent then writes the Lean proofs automatically — 40/45 outcomes verified — and even synthesizes bots from natural-language descriptions.**
