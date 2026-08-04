# TauBots — graded transparency over the zoo (design note)

*Status: design fixed 2026-07-31; **v1a Python explorer SHIPPED 2026-08-03**
(`app/src/pd_runner/tau/`). Part I below is design + what is implemented;
Part II is everything not yet implemented.*

*Updated 2026-08-04: the **syntactic σ family was rewritten onto real ASTs**
(Zhang–Shasha tree edit distance, replacing the constructor-profile feature
vector — this RETRACTS the old "DBot/TitForTatBot are syntactic twins,
ceiling ≈ 0.947" claim, which was an artifact of the metric); selectable
**named sub-zoos** landed (`ZOOS` in `tau/matrix.py`, surfaced in the CLI,
the API and the UI); and a proven `outcome = none` is now a **fifth cell
state** `"N"` rather than grounds for excluding a bot.*

---

# Part I — Design & implemented (v1a)

## Goal

Model **partial transparency**: bots receive a *blurred signal* of the opponent
instead of its full source code. Two constraints:

1. **Reuse the existing zoo and outcome matrix.** Prover bots (DupocBot & co.)
   need *exact syntax* to prove anything — a corrupted source is useless to them.
2. **Graded intensity**: we want to speak of 20%, 40%, … transparency.

## The core construction

A **signal** is a distribution over the zoo: candidates `B₁…Bₙ` with weights
`p₁…pₙ`, `Σpᵢ = 1`. The uncertainty is over *which exact program* the opponent
is — each hypothesis is real, fully-transparent syntax backed by a proven matrix
cell. This is a Harsanyi type space with the zoo as type space, and it is what
satisfies constraint 1: the blur lives in the weights, never in the programs.

The tau lift of a base bot `A` (**the chosen definition — "Def 3"**):

```
TauA(α)(B₁…Bₙ, p₁…pₙ):
  C  iff  Σ { pᵢ : A's action in outcome(A, Bᵢ) = C } ≥ α
```

i.e. *A best-responds to each hypothesis with its own decision procedure, then
takes the weighted vote of its own intended actions.* Deterministic by
**expectation-then-threshold derandomization**: we integrate the uncertainty out
before the decision instead of sampling, so no probabilistic agents, no
measure-theoretic eval, no probabilistic Löb.

### Harsanyi anchor (why "type space" is the right citation)

Harsanyi (1967–68) models incomplete information by compressing the infinite
belief hierarchy into a **type**: each player holds a probability distribution
over a set of types, converting incomplete information into an ordinary game
with a chance move. Our signal is exactly such a belief: the type set is the
zoo, and σ's concentration is the information dial (point mass = complete
information = Critch's regime; uniform = no information = classical PD). Three
deliberate deviations from full Harsanyi: the hierarchy is truncated (level-k
with the zoo as level 0, no beliefs-about-beliefs); there is no common prior
(signals are exogenous, so outputs are phase diagrams, not equilibria); and
types are **intensional** — they determine the opponent's *term*, not just
payoffs, which is what makes behaviorally-twin types separable by the Löbian
fragment. The tau lift is also NOT Bayesian best response (it thresholds A's
own cooperation mass, preserving A's decision procedure) — the information
structure is Harsanyi, the decision rule deliberately isn't.

### Interpolation story (the headline)

- σ = point mass (full transparency, t = 1) → the tau tournament **provably
  reproduces the base outcome matrix** (the anchor theorem) → Critch's OSGT
  regime.
- σ = uniform (zero transparency, t = 0) → cooperation mass is a constant per
  agent → everyone plays an *unconditional* strategy → classical opaque
  one-shot PD.

The tau family continuously interpolates between OSGT and classical game theory.
Headline experiment: *how much transparency does Löbian cooperation need?*

## Two dials — do NOT conflate them

- **`t ∈ [0,1]`** = *transparency* (property of the signal/environment): how
  concentrated the posterior is on the true opponent. **Fixed 2026-08-03: the
  dial IS the normalized mutual information** `I(B; σ(B)) / H(B)`, with t = 1
  full transparency and t = 0 opaque (raw softmax temperature is internal-only,
  bisection-inverted per family).
- **α** = *caution/generosity* (property of the agent): how much cooperation
  mass it demands. It is NOT transparency.

Sweep both → `(t, α)` phase diagrams; piecewise-constant with finitely many
breakpoints, so each cell is one `decide`-grade theorem.

## Definitions considered, and why Def 3 wins

**Def 1 — tau hypotheses, reciprocity probe** `play(TauBᵢ(TauA))`. REJECTED:
1. *Ill-typed before circular*: a tau bot consumes a signal, not a bot, so the
   inner match needs a signal convention — which recurses if the support
   contains tau bots.
2. *Ungrounded recursion*: mutual tau consultation is the bistable
   JustBot-vs-MirrorBot fixpoint in EVERY tau-vs-tau cell, and the tau layer has
   no Löb machinery to break it — `play` is total only by fuel, so everything
   bottoms out in defaults.

**Def 2 — base hypotheses, reciprocity probe** `play(Bᵢ(A))`. Well-founded
(stratified: layer 1 consults only layer-0 matrix cells; this is level-k
reasoning with the zoo as level 0). But the probe direction is wrong as a *lift*
of A: it asks "does the hypothesis cooperate with my base bot", making every
tau bot a threshold-*reciprocator* (a generalized FairBot). At full transparency
Tau(DefectBot) plays whatever the opponent concedes to DefectBot — the lift does
NOT converge to A.

**Def 3 — base hypotheses, self probe** `outcome(A, Bᵢ)` (A's own action).
CHOSEN. Same stratification and matrix reuse as Def 2, plus the decisive
property:

> **Anchor theorem: at full transparency (t = 1) the tau tournament equals the
> base outcome matrix.** TauA(δ_B) plays exactly what A plays against B.
> Verified in the v1a explorer for all α; the Lean statement is v1b.

So Def 3 is genuinely "A with blurred vision"; Def 2's reciprocity probe is a
separate interesting bot *family*, not the lift. The two coincide exactly on
outcome-reciprocal bots (worth a lemma).

### The probe × hypothesis square

|                       | hypotheses = base Bᵢ | hypotheses = TauBᵢ |
|-----------------------|----------------------|--------------------|
| **self probe** (A vs hyp)      | ✅ matrix cell — **Def 3** | ❌ needs A run on tau source: new proofs, breaks constraint 1 |
| **reciprocity probe** (hyp vs A) | ✅ matrix cell — Def 2 | ✅ meta-computable (level-2, Part II) |

`outcome(A, TauBᵢ)` (top right) is the unique corner NOT reducible to the
matrix: A's *machinery* must execute on tau *source* — a bigger term, new
theorems, budget floors shift with program size, Löb shapes change. And
`outcome(A(TauB)) = outcome(A(B))` is FALSE as a theorem in general (three
failure levels: TauB ≠ B behaviorally at intermediate blur; OSGT is intensional
— provability is about terms, and costs scale with term size; the mutual-Löb
fixpoint shapes don't exist against tau-shaped terms). Stipulating the equation
as a *definition* is fine — but that stipulation IS Def 3, so just write
`outcome(A, Bᵢ)`.

## Conventions — FIXED (2026-08-03)

1. **Open matrix cells**: restrict the zoo to closed sub-matrices (NOT
   drop-and-renormalize). UNPROVEN cells still fail loudly; a cell may only be
   filled by an explicit STIPULATION, which is flagged so downstream results
   report as conditional (`TauMatrix.is_fully_proven`).

   **Named sub-zoos (2026-08-04)** — the `ZOOS` registry in `tau/matrix.py` is
   the single source of truth, surfaced by `report.py --zoo`, `/tau/report?zoo=`
   and the UI dropdown. Adding one is a one-place edit.

   | key | bots | provenance |
   |---|---|---|
   | `default` | 11 | 2 stipulated pairs; twin-free, ceiling 1.0 |
   | `enlarged` | 16 | 7 stipulated pairs; 2 behavioral twin groups (ceiling ≈ 0.938); holds the `N` cell |
   | `full-certified` | 12 | kernel-clean; 2 twin groups (ceiling ≈ 0.843) |
   | `proven-only` | 10 | kernel-clean; 1 twin pair (ceiling ≈ 0.940) |

   A stipulation may only fill a genuine hole — the loader RAISES if one
   shadows a proven cell, which is how a stale entry gets caught when its
   theorem finally lands (this fired for real on DIMCID vs CupodTrollBot).
1b. **Proven `none` is a FIFTH CELL STATE (2026-08-04), not an exclusion.**
   `outcome_MirrorBot_vs_MirrorBot = none` (mutual simulation never
   terminates) loads as a real kernel-backed cell with both actions `"N"`,
   so MirrorBot is admissible; it was previously excluded for lack of a truth
   value. Downstream `"N"` reads PESSIMISTICALLY — `cooperates` tests `== "C"`,
   so a hypothesis whose cell is `N` contributes no cooperation mass — and it
   is a third symbol for twin/distance purposes. A stipulation may NOT shadow
   it.
2. **Budgets**: matrix entries are budget families, often staggered
   (PrudentBot 2k+64 vs Dupoc k); the tau layer uses the collapsed stable
   asymptotic outcome, one canonical convention per pair.
3. **Tie-breaking**: `≥ α`. Only finitely many α matter (subset sums of the
   support); sweeps must step BETWEEN `alpha_breakpoints` (knife-edge trap:
   α exactly on an achievable coop fraction lets float noise decide plays).
4. **Dial**: t ∈ [0,1] = normalized MI, per the two-dials section; t = 0 maps
   to a finite internal temperature (1e4), not exact uniform, keeping the
   knife-edge observable.

## Division of labor & v1a (implemented)

**Key consequence of Def 3: the tau layer is matrix-arithmetic, so the
*experiments* belong in Python, not Lean.** The matrix is exported via the
sheet-sync extraction of `(llm_)?outcome_A_vs_B` + `outcome_status.toml`;
everything downstream — the σ family, behavioral distances, the MI transparency
scale, (t, α) sweeps, phase diagrams, whole tau tournaments — is plain
arithmetic in `app/`. No Lean in the loop, instant iteration. The trust chain
stays honest: Lean-verified cells + transparent Python arithmetic.

**v1a explorer** (`app/src/pd_runner/tau/`: matrix / signal / play / sweep /
report / channels / syntax + `tests/test_tau.py`): σ/α sweep engine, phase
diagrams, report with inline SVG (`uv run python -m pd_runner.tau.report
--open`, or the "Run tau analysis" button → `GET /tau/report`).

## σ families — implemented (v1)

A σ family is **(what leaks) × (how it blurs)** — two orthogonal axes. All
families are calibrated onto the SAME transparency dial t ∈ [0,1] (normalized
MI, inverted per family by bisection — `tau/channels.py`), so at matched t the
information rate is identical and only the confusion structure differs:
cross-family gaps are purely about WHICH bots get confused.

1. **behavioral** — softmax over Hamming distance on own-action rows. NOT ad
   hoc: it is the exact Bayes posterior (uniform prior) of watching every
   match through a binary symmetric channel, since p^d(1-p)^(n-d) ∝
   exp(-d·ln((1-p)/p)).
2. **ε-uniform** — (1-ε)δ + ε·U. The null control: no similarity structure,
   identity-based (no twin ceiling). Divergence from it isolates the effect
   of confusion structure itself.
3. **syntactic (AST)** — softmax over **normalized Zhang–Shasha tree edit
   distance** between parsed `Prog` terms (`tau/syntax.py`). Partial
   transparency of the SOURCE — degraded OSGT.
   **Confusion-structure inversion** (the headline, and it survives the v2
   rewrite below): Dupoc/Cupod are syntactic near-twins (same tree, action
   leaves swapped) but behavioral opposites; while Coop/CupodTroll are
   behavioral near-twins yet syntactic opposites. Globally the two channels
   correlate at only **+0.16** over the enlarged zoo, which is what makes the
   code channel a genuinely second object rather than a noisy copy.
   **No syntactic twins on any current zoo** ⇒ ceiling 1.0; the residual
   blindness is budget erasure (two bots differing only in search budget are
   one program to this observer — see "what the distance erases" below).

   **v2 rewrite (2026-08-04) — was: constructor-profile feature vectors.**
   v1 counted constructor tokens into a 14-dim bag and took unnormalized L1.
   Replaced after four defects were measured, each verified before the
   rewrite:
   * **Structure blindness.** A bag cannot see argument order or nesting, so
     `DBot` and `TitForTatBot` — both `.ite (.sim .opp (.bot X)) C · ·` with a
     *different probe target* and the *branches swapped* — had distance 0.
     The "DBot/TFT are syntactic twins, ceiling ≈ 0.947" claim this note
     previously made was therefore an ARTIFACT OF THE METRIC, not a property
     of the zoo. Under the AST distance they sit at 3.0 and the ceiling is 1.0.
   * **Reference blindness.** The `ref` feature counted how many bot names
     appeared, never *which* — so probing CooperateBot and probing DefectBot
     were indistinguishable, discarding most of what source actually reveals.
   * **Scale sensitivity.** Unnormalized L1 grows with program SIZE: mean
     distance correlated **+0.75** with node count (EBot, 22 nodes, sat 17.6
     from everything; the 1-node constants sat at 8.6). The channel largely
     encoded "how big is this bot", which the softmax then read as big bots
     being highly identifiable. Post-normalization the correlation is −0.19.
   * **Comment bleed.** The body regex stripped `--` lines but not `/- … -/`
     blocks, feeding JustBot's and PrudentBot's doc-comment prose to the token
     counter as if it were syntax. Harmless by luck (that prose contains no
     `.foo` tokens) but a docstring mentioning `.search` would have silently
     corrupted the vector.

   The v1 metric is retained as `feature_distance_matrix` / `feature_twins`
   for comparison — the tests assert the twin collapse was real by showing v1
   gives 0 where the AST gives > 0.

   **What the distance is.** Terms are parsed from `Bots/*.lean` by a strict
   S-expression reader (it raises rather than returning a partial tree, so a
   drifted source fails loudly instead of silently getting a wrong distance),
   then compared by unit-cost Zhang–Shasha tree edit distance — the minimum
   number of node insertions, deletions and relabels turning one AST into the
   other — divided by the larger tree's node count, giving a scale-free ratio
   in [0, 1].
   **What it erases, deliberately:** (a) **search budgets** — `CupodBot k` and
   `CupodBot (2*k+64)` are the same code to a source-reading observer; budget
   is *Critch's own depth dial*, and folding it in would silently merge two
   transparency axes; (b) **referenced bot bodies** — `.bot DefectBot` is a
   labelled leaf `ref:DefectBot`, never inlined, because an observer glimpsing
   the term sees the name, not the body (unchanged from v1).

   Parsing rather than `#eval`-exporting is a deliberate v2 choice: it keeps
   the tau layer a pure-Python read-only consumer of the engine, with no build
   step and no `lake` dependency in the analysis path. The exporter remains the
   recorded upgrade if the reader's strictness ever becomes the bottleneck.

---

# Part II — Not yet implemented

## v1b — meta-level Lean core (next)

TauBots as Lean functions over the matrix, not `Prog`s — only what must be a
theorem: the definitions below, the anchor theorem (t = 1 reproduces the
matrix), and a few `decide`-certified sample cells cross-checking the Python.

```lean
structure Signal where hyps : List (Prog × ℚ)
def OutcomeTable := Prog → Prog → Option (Action × Action)  -- none = open cell
def coopMass (tbl) (A) (s) : ℚ := Σ pᵢ over hyps with (tbl A Bᵢ).map .fst = some .C
def tauPlay (tbl) (A) (α) (s) : Action := if α ≤ coopMass … then .C else .D
```

The table comes from a hand-maintained `zooTable : OutcomeTable` with one
one-liner certification lemma per cell tying it to the existing
`outcome_A_vs_B` theorems. Tau-vs-tau theorems then reduce to rational
arithmetic + `decide`.

## v2 — in-language compilation (upgrade path)

Only if mixed base-vs-tau matches are wanted. For a fixed signal,
`Σ pᵢ·[Cᵢ] ≥ α` is a fixed monotone boolean function of n bits → TauA compiles
to an ordinary nested `.ite`/`.sim` `Prog`. **No language extension needed**
(no arithmetic in `Prog`; p and α are baked in at compile time). Caveats: fuel
scales with tree size; `.sim` of search-bot matchups hits the evalG/Löb
boundary. Mixed matches (and the split theorem below) cannot even be *stated*
outside Lean.

## The behavioral/prover split (thesis-grade theorem candidate)

Under *dynamic signals with transparent counterfactuals* (open conventions
below):

- **Sim-only A** (TitForTatBot, MirrorBot, …): `outcome(A(TauB)) =
  outcome(A(B))` for sufficient fuel — sims only see behavior, and TauB under a
  point-mass counterfactual signal is behaviorally B. **Blur is invisible to
  behavioral bots.**
- **Proof-search A** (DupocBot, PrudentBot, JustBot, WaryBot): the equation
  fails — guards are `Pf k ⌜…⌝` about the opponent's *term*. **Blur is
  detectable exactly by the Löbian fragment.**

This both justifies the construction (the phenomena live where Critch's
machinery lives) and cuts the workload: behavioral base-vs-tau cells reduce to
existing matrix cells; only prover-vs-tau cells are new objects.

**Open conventions it depends on (undecided):**
1. **Static vs dynamic signals.** *Static* (signal baked in at compile time):
   the compiled TauB sims only closed matchups → TauB is extensionally a
   CONSTANT program; simple, but counterfactual queries about it are degenerate
   — this silently kills the split theorem. *Dynamic* (evaluator applies σ at
   every interface, including inside sims): needed for the split theorem; a
   real eval-semantics change.
2. **Transparency inside counterfactuals.** Does an in-sim TauB get δ (identity
   is given by construction inside a sim) or σ (blur compounds through nested
   counterfactuals)? δ is the convention assumed by the split theorem; σ gives
   a different, also interesting object.

## Level-2 — tau-aware opponents (deferred to v2)

The bottom-right corner of the probe × hypothesis square (reciprocity against
TauBᵢ) stays matrix-computable — TauBᵢ's response is itself arithmetic over
layer-0 cells (given conventions for its α′ and its signal). Hard-stop the
hierarchy at depth 2.

## σ families — recorded for later (rough priority)

- ~~**AST tree edit distance** (Zhang–Shasha) on real `Prog` terms~~ —
  **DONE 2026-08-04**, see the syntactic family in Part I. Implemented by
  PARSING `Bots/*.lean` with a strict S-expression reader rather than the
  `#eval` exporter sketched here, to keep the tau layer a pure-Python
  read-only consumer of the engine (no build step, no `lake` in the analysis
  path). The exporter stays the recorded upgrade if reader strictness ever
  becomes the bottleneck.
- **Node-masking generative σ** — observer sees the AST with each node hidden
  w.p. p; posterior = P(observed fragment | candidate). The finite-zoo
  approximation of the hole-masked-source ideal below, and the syntactic
  analogue of the BSC justification.
- **Sampling/reputation σ** — posterior from m observed past matches; the dial
  is TIME WATCHED, not noise. The most natural game-theoretic story.
- **Theorem-library σ** — distance = shared proven outcome facts; the only
  family whose similarity structure is itself Lean-certified.
- **Query-signature σ** — what the bot does to YOU leaks (simulates you /
  proof-searches you / neither): the split-theorem partition as a channel.
- **Mixtures** λ·behavioral + (1-λ)·syntactic — a second dial for WHAT leaks.
- Behavioral variants: payoff-weighted / discriminativeness-weighted Hamming,
  outcome-pair rows, enriched probe sets; architectures: k-NN, truncated
  support (sparsemax), non-uniform priors.

## The wider landscape — alternative transparency formalizations

Five genuinely different ways to formalize partial transparency, organized by
WHAT gets blurred. The one-sentence defense of our choice: identity uncertainty
is the only graded notion that keeps exact syntax in every hypothesis, and
exact syntax is the load-bearing requirement of Löbian cooperation — so it is
the unique choice compatible with constraint 1 at v1 cost.

1. **Identity uncertainty (CHOSEN).** Full syntax, uncertainty over *which*
   program; blur in the weights. This note.
2. **Structural partiality — masked source.** See the AST with holes;
   cooperation = "prove C for all completions of the hidden subterm". The
   semantic ideal our finite type space approximates (node-masking σ above is
   its finite-zoo shadow); needs program quantifiers in `Formula` — heavy
   engine work, framing/future work only.
3. **Resource-bounded introspection.** Everyone sees full source; analysis
   power is bounded. Three flavors: **budget k** — Critch's OWN transparency
   dial, already in the engine (*depth* vs our *breadth*; compare the axes);
   **obfuscation** (transparency = compute to de-obfuscate; hostile to Löbian
   reasoning — provers need equivalence proofs first; a research program in
   itself); **abstract interpretation** (analyze source only through a coarse
   abstract domain; Lean-natural, but grades the OBSERVER, not the channel).
4. **Interface/spec transparency (the v3 candidate).** The opponent reveals
   not its code but a *certified property*: a formula φ + a `Pf`-proof ("I
   provably cooperate if you provably cooperate"); you reason from φ instead
   of the source. Transparency graded by the lattice of published formulas.
   Closest to the AI-safety motivation (verify properties, don't read
   weights), adjacent to program equilibrium with mediators / Oesterheld's
   robust program equilibrium, and **engine-native**: it is "reason from a
   boxed premise" rather than "reason from source", with `Pf` certificates as
   the currency. If a v3 is ever wanted, this over masked-AST.
5. **Behavioral/extensional blur.** Never see code; observe actions noisily
   (Halpern–Pass translucent players; imperfect-monitoring literature) or get
   bounded black-box query access. The classical-economics route — and
   definitionally blind to intensional twins (a black-box channel can never
   separate Coop/Legible), so it would amputate exactly the phenomenon this
   thesis is about.

**Rejected outright**: syntactic noise on the source (prover bots reason
soundly from a wrong premise — kills constraint 1); genuinely probabilistic
agents (measure-theoretic eval + probabilistic Löb — a thesis in itself).
