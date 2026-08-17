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

---

# Part III — Definition 4: tau-native bots (design fixed & Milestone 1 SHIPPED 2026-08-11)

**Def 4** generalizes past the Def-3 lift: hypotheses AND probes are TauBots, every
recursive reference routed through `proofSearch`. This escapes Def 1's rejection —
Def 1's recursion was semantic (via `play`, fuel-total, no Löb rescue); Def 4's is
proof-theoretic, so bounded Löb breaks the regress exactly as in base DupocBot
self-play.

> **CORRECTED 2026-08-13 (see the retraction section at the end of this part).**
> This part originally framed Def 4 as "a bot LANGUAGE, not a uniform lift" with
> per-bot probe direction, and claimed its (t, α) diagrams answer a different
> question than Def 3's. That framing was wrong: properly read, Def 4 is a uniform
> STRUCTURAL SOURCE LIFT of each base bot, its per-hypothesis bit is the self-probe
> bit, and **Def 4 COINCIDES with Def 3** (at large k, on terminating cells). What
> Def 4 adds is the in-language, finite-budget implementation — Löb thresholds,
> floor cells, the prover/behavioral budget gap — not a different phase geometry.
> The "separating" TauEBot below is retracted as a lift of EBot. A refined
> definition is being specified separately.

## Fixed conventions

1. **Signals are weighted lists over template NAMES**; probes re-instantiate the
   hypothesis at a point-mass signal. The probed objects are the finite closed
   instance family `B(δ_T)`; for the milestone-1 zoo the reference graph is a DAG
   except the single `L(δ_L)` self-loop, cut by the `.self` quine `TauDupocδ`.
2. **Probe atom** `probe I := .plays (.bot I) (.bot I) .C` — `.bot`-freezing is
   mandatory (subst barrier); the second slot is inert (`.opp`-free programs).
   Anti-patterns (rejected): encoding "B sees T" in the opponent slot; `.self` in a
   probing bot's guard (resolves to the σ-player, the wrong object).
3. **θ = ⌈α·W⌉** over integer weights summing to W; cooperate iff fired mass ≥ θ.
   Lossless: the α-diagram is piecewise constant with breakpoints at subset sums.
4. **TauBots are `.opp`-free** — the defining constraint of the tau fragment; under a
   static signal every tau player is extensionally constant (the static-signal caveat
   of Part II applies in full force).
5. **Guard order: Löbian guards LAST** (stepwise rules read in order; low-θ regimes
   short-circuit before the walled Löb guard).
6. **Prover instances stay `.search` singletons** (point-mass tsearch ≡ search),
   keeping `searchBranch`/`botSearchStep` applicable; only σ-players use `.tsearch`.

## The engine extension (Route B, landed)

`Prog.tsearch k gs θ p q` — weighted-threshold proof search; `GuardList` lives in the
mutual block (not a nested `List` payload). Eval = stepwise PEEL (θ=0 then-shortcut;
firing subtracts the weight, truncated). Five PlaysProof rules mirror the peel:
`tsearchZero_t/Nil_f/Cons_t/Cons_f/High_f`; `Cons_f` pays the per-guard `search_f`
floor (`n+m+k+c_node`); `High_f` commits else on the static arithmetic `θ > totalMass`
(bit-independent, hence consistent) paying `gs.gsize`. NO new Pf modal rules; the
Exclusion censuses gained only a kill obligation (`h_tsearch`) — no tsearch program is
ever a census subject. Meaning preservation: all 81 pre-existing outcome statements
byte-identical, 3-axiom footprint. Gotchas hit: the equation compiler silently
compiled the enlarged `subst` mutual block by WF recursion (killing defeq) — forced
back with `termination_by structural`; an inner `match gs` in the eval arm breaks
equation generation — use nested patterns (two `.tsearch` arms) instead; the tactic
`induction` refuses the mutually-inductive `GuardList` — write equation-style
recursion (`cases` is fine).

## Milestone 1 results (all in `Tau/` + `Theorems/Tau/Matrix.lean`, zero sorry, 3 axioms)

Zoo: TauCooperate, TauDefect, TauDupoc, TauTFTSim (behavioral), TauTFTPf (prover).
The δ-instance closure is 7 terms. Headline (`Tau/Phases.lean`): all three
non-constant players cooperate — against every opponent — **iff θ ≤ wC+wTs+wTp+wL**
(the same α-boundary), at different BUDGET thresholds: TauTFTSim needs only the
trivial Coop bit (k ≥ 2-ish), TauTFTPf shallow proof budgets, TauDupoc the **Löb
threshold** (`ps_probe_quine`: past k₂, `proofSearch k (probe (TauDupocδ k)) = true`
at the probing budget itself — `botSearchStep` + `pblt_engine_id` on the
`.bot`-wrapped quine fixpoint). **The prover/behavioral split is a budget-phase gap,
not an α-gap.** Matrix: 25 cooperative-regime cells incl. the `(C, D)` exploitation
cells against TauDefect (wrong signal costs payoff — the price of partial
transparency, now a theorem), + 3 defect-regime self-plays exhibiting the α-flip.

## Milestone 2 (open)

Restore `Metatheory` to the default build (unpinned in `lakefile.toml`) and extend
T31–T54 to `tsearch`: `enumProg` over `GuardList`, gated mirror rules, `evalG`
3-valued peel (squeeze non-pivotal undetermined guards), modest/instance-gate
walkers, the T49 substrate (~1wk alone). Until then the certified outcome-prepass
cannot see tau terms. Also open: `tsim` (action-vote constructor) for behavioral tau
bots — TauTFTSim currently compiles to an `.ite` decision tree; below-Löb-budget
regimes for TauDupoc (need ¬Pf cost floors); mutual tau probes (reference-by-name /
zoo environment).

## Def 3 vs Def 4 — the comparison experiment (2026-08-11)

`app/src/pd_runner/tau/{def4,compare}.py`, run with
`uv run python -m pd_runner.tau.compare --zoo {control,separating}`.

**Method.** Both definitions run over the SAME certified base matrix, the SAME
σ_t channel, and the SAME exact α-breakpoint bands; only the probe semantics
differ. Each matchup is instantiated with its own signal `σ_t(true opponent)`,
which is what makes the comparison fair: the Lean Def-4 bots carry one STATIC
weight vector, and comparing that against Def 3's correlated signals would show
a t = 1 difference that is an artefact of the signal model, not of the
definition. The phase theorems quantify over arbitrary weights, so per-matchup
instantiation is faithful. All tables are at LARGE k (past the Löb threshold);
the sub-Löb regime is unproven and not modelled.

**Result 1 — the control zoo cannot separate them.** On
{Dupoc, Coop, Defect, TFT} the two definitions give byte-identical outcome
matrices at every (t, α) — 19 phase cells, 0 divergences. And the agreement is
STRUCTURAL, not sampling luck: every bot's probe bit-vector is identical
(Dupoc 11010, Coop 11111, Defect 00000, TFT 11010 under both).

**The sharpened criterion.** Raw base-matrix asymmetry is NOT sufficient for
separation — the control zoo *has* asymmetric cells (Coop/Defect) and still
cannot separate, because their actors are CONSTANT bots whose bit-vector is
all-ones/all-zeros under every probe geometry. The right criterion is a
differing BIT-VECTOR, i.e. an asymmetric cell sitting under a CONDITIONAL bot's
probe. `compare.asymmetry_report` decides on that and reports the raw asymmetry
only as a diagnostic.

**TauEBot v1 (2026-08-11) — superseded.** The first Lean TauEBot was a
δ_E-probing reciprocity vote (`eSig`, a second `.self` quine `TauEBotδ`, boundary
`wC + wE`), with its δ-instances stipulated from base-matrix cells. The five-slot →
six-slot widening (2026-08-12, morning) made both runs 100% certified against it
and surfaced per-column masses plus twenty `_mixedRC/_mixedCR` straddling-cell
theorems. All of that is retired by the cascade refactor below; it is recorded here
because the kernel-vs-model check found five real Python bugs along the way
(constant bots modelled as probing bots; a reversed-orientation lookup; a
breakpoint rounded above its own mass; a θ off-by-one from weight-rounding drift;
TauEBot wrongly given TauDupoc's all-but-Defect boundary), which is the standing
argument for keeping the comparison kernel-verified.

## The faithfulness audit and the cascade refactor (2026-08-12)

**The trigger.** In review of the Def3/Def4 divergence table, Colomban asked: *"in
Def 4, Dupoc should NOT be able to prove that EBot cooperates — like the base
case?"* Correct: Def 4 routes every bit through `proofSearch`, and base
`outcome_DupocBot_vs_EBot = (D, C)` holds precisely because EBot's cooperation
transcript embeds a FAILED search (the `search_f` floor `> k`). The then-current
`eOfSearchδ = probeSearchδ k tauCoopδ` stipulated a PROVABLE cooperator — bit 1 by
fiat. The full-zoo audit that followed found four bugs, all in the EBot corner:

1. `eOfSearchδ` (`E(δ_L)`): stipulated provable cooperator — the floor erased.
2. `eOfCoopδ` (`E(δ_C)`): right bit (0), wrong mechanism (stipulated refutable
   guard instead of base EBot's FIRING exploit-check).
3. `searchOfEδ` doing double duty as both `L(δ_E)` and `Tp(δ_E)` — faithfully two
   different programs (one probes a true-but-floor-blocked atom, one a false one).
4. **The root cause: TauEBot's σ-player itself.** The δ_E reciprocity vote is
   Def 2's REJECTED geometry ("a generalized-FairBot family, not a lift of A")
   wearing EBot's name — and it is *why* the stipulations existed: two self-probing
   bots need mutual quines (`E(δ_L) ↔ L(δ_E)` is a genuine 2-cycle), which `.self`
   cannot express, so the instances got faked from base cells.

**The fix (all landed, engine green, 3 axioms).** Base EBot's exploiter cascade
lifted at BOTH levels:

* **Instance template** `eδ k I_D I_C := .search k (probe I_D) (.const D)
  (.search k (probe I_C) (.const C) (.const D))` — exploit-check then reciprocity.
  `eOfCoopδ = eδ k tauCoopδ tauCoopδ` (defects via a FIRING guard),
  `eOfDefectδ = eδ k tauDefectδ tauDefectδ`,
  `eOfSearchδ = eδ k (searchOfDefectδ k) (searchOfCoopδ k)` — which **really
  cooperates, UNPROVABLY**: `interp_probe_eOfSearch` (true) +
  `ps_probe_eOfSearch_false` (bit 0 at every budget ≤ k), the Gödelian pair. The
  old names `searchOfEδ`/`simOfEδ` live on as their honest δ_D-column roles
  (`searchOfDefectδ`/`simOfDefectδ`). NO quine for E: the cascade probes only the
  δ_D/δ_C columns, so the whole family GROUNDS — the 2-cycle never forms.
* **The floor lemma** (`Base/Exclusion.no_provable_botSearcherElse_tail`): a
  `.bot`-frozen budget-`kb` searcher's non-then-action play is unprovable at every
  budget ≤ kb — `search_t` dies by action mismatch, `search_f` carries the literal
  `kb` floor summand; shape-general in the else branch, NO guard-truth hypothesis.
  Built directly on the action-refined set kernel (`no_provable_tailToS_floor`),
  whose docstring anticipated exactly this use.
* **σ-player** `TauEBot = .tsearch k exploitSig θ (.const D) (.tsearch k tftPfSig θ
  (.const C) (.const D))` — a NESTED tsearch, both stages sharing θ. At point-mass
  it IS `eδ`, so σ-player and instance family cohere there. No Löb budget
  anywhere in its phase theorem. **[RETRACTED as a lift of EBot, 2026-08-13:
  away from point-mass, thresholding each STAGE against θ is a different agent
  from voting once over the per-hypothesis cascade decisions — see the
  retraction section.]**

**The new phase structure** (`Tau/Phases.lean`, `Theorems/Tau/Matrix.lean` — 79
theorems: 4 constants, 42 cooperator cells low/high, 33 EBot cells
exploitθ/window/highθ):

* All three cooperators share ONE boundary `θ ≤ wC + wTs + wTp + wL` — TauDupoc's
  mass honestly EXCLUDES `wE` (the floor). No mixed regime exists between them;
  the twenty straddling-cell theorems were artifacts of the stipulated bit and are
  deleted.
* **TauEBot cooperates in a WINDOW** `wC < θ ≤ wC + wTs + wTp + wL`: below it the
  exploit stage fires on the Coop mass (it DEFECTS against cooperators that
  cooperate with it — the lifted exploiter exploits, incl. at θ = 0); above it the
  reciprocity mass runs out. **Defection at both ends of the α axis.**

**Verification state after the refactor**: control 100% certified, separating
1400/1400 cells, 0 conflicts. One durable finding from that run: **TauDupoc's
Def-3 and Def-4 bit-vectors COINCIDE** (`11010`) — its EBot bit is 0 under both,
for matching reasons (Def 3: "my own action vs EBot is D"; Def 4: "EBot's real
cooperation is floor-priced") — so at full transparency the per-side lookups
reproduce the base cell `(D, C)` exactly. The run's *separation* claims (45/56
diverging phase cells, the window-vs-threshold reading) are RETRACTED below:
they measured the crowd-exploiter σ-player, not a Def-4 lift of EBot.

**Conventions clarified by the refactor** (supplementing the fixed list above):
each template's instance family must be its own point-mass instantiation (the
coherence rule the stipulations violated); self-probe geometries are reserved for
bots whose base strategy IS the self-probe (Dupoc — the quine stays); and a probe
column is named by the SIGNAL it instantiates (δ_C, δ_D, δ_L — there is no δ_E
column anymore).

## RETRACTION — Def 4, correctly read, COINCIDES with Def 3 (2026-08-13)

Colomban caught the error starting from the Def-4 self-play cell
`TauEBot vs TauEBot = (D, D)`: that bot should not be defined that way, and once
Def 4 is stated properly the two definitions coincide. Everything in this part
claiming a Def3/Def4 SEPARATION is retracted; the mechanics (the audit, the
instance layer, the floor lemma) stand.

**The correct reading of Def 4: a uniform STRUCTURAL SOURCE LIFT τ**, not a
per-bot probe-geometry choice. Take base bot A's own code and lift it
constructor by constructor — `search(k, g, ·, ·)` keeps its shape with every
program reference replaced by its tau instance, `sim(X, Y) ↦ sim(τX, τY)`,
`ite` lifts its branches — and let the σ-player take ONE weighted vote over the
COMPOUND per-hypothesis bits:

```
TauA(α)(B₁…Bₙ; w₁…wₙ)  =  C   iff   Σ { wᵢ : TauA(δ_{Bᵢ}) plays C } ≥ θ
```

where `TauA(δ_B)` is A's *entire lifted decision procedure* run at point mass
on B.

**Why this makes Def 4 = Def 3.** The compound bit for `(A, Bᵢ)` is "what does
A's code decide against Bᵢ's instance" — the SELF-probe direction. Whenever the
instances behave like the base opponents (the anchor property: large k,
terminating cells), that is exactly Def 3's bit "A's action in
`outcome(A, Bᵢ)`". Both definitions then threshold the SAME bit-vector, so the
(t, α) phase diagrams coincide. Def 4 is Def 3 *implemented in-language*, not a
rival definition. Even the floor cells agree: Def 3's Dupoc-on-EBot bit is 0
because Dupoc's real action is D (the base floor); Def 4's is 0 because the
lifted search hits the tau floor — the same bit, produced by the same mechanism
one level up. The TauDupoc bit-vector coincidence found by the audit was the
first instance of this general fact, misread at the time as a special property
of reciprocators.

**Where the implemented TauEBot went wrong.** Dupoc and the TFTs have ONE
decision point, so "vote over guard bits" and "vote over compound decisions"
agree by accident of shape — they conform to τ. EBot is the first multi-branch
bot, and the implemented σ-player moved θ INSIDE the cascade: a vote per STAGE
("is the crowd exploitable?", then "does the crowd reciprocate?"). That is a
coherent agent — the *crowd-exploiter* — but it is NOT τ(EBot), which runs
EBot's whole cascade per hypothesis and votes once. τ(EBot)'s bits on this zoo
are Coop 0, Defect 0, TFT 1, Dupoc 1 (mass `wTs + wTp + wL`) — a ONE-SIDED
boundary, no window. The window, the `(D, D)` self-play, and the "45/56 phase
cells diverge" summary are all properties of the crowd-exploiter and must not
be cited as Def-4 results.

**The residual, honest divergences** — the content Def 4 adds over Def 3, none
of it a new phase geometry:

1. **Budget structure.** Def 3 stipulates the bits; Def 4 computes them with
   real `proofSearch` at finite k. Löb thresholds, the prover/behavioral budget
   gap, floor costs, sub-Löb regimes — all invisible to Def 3, all theorems in
   Def 4. The definitions agree asymptotically and differ below the thresholds.
2. **Non-terminating branches.** Base EBot's third branch sims MirrorBot, which
   is not `.opp`-free-liftable; dropping it flips E's SELF-bit (Def 3 reads 1
   via the Mirror escape, the truncated lift reads 0). The one genuinely open
   lift convention.
3. **Cost intensionality.** `outcome(A vs τB) = outcome(A vs B)` is false as a
   theorem (term sizes move costs); Def 3 stipulates it, Def 4 computes the
   left-hand side.

**Status of the artifacts.** The Lean *instance layer* is correct under the new
reading and is precisely what τ consumes: `eδ` and the per-hypothesis compound
bits, the Gödelian pair (`interp_probe_eOfSearch` + `ps_probe_eOfSearch_false`),
the floor lemma `no_provable_botSearcherElse_tail`, and the cooperators' shared
boundary all stand. The σ-player `TauEBot` (nested tsearch, shared θ) and its 33
exploit/window/high matrix cells remain in the engine as certified theorems
*about the crowd-exploiter* — kernel-true, wrongly labelled — pending
redefinition. The Python comparison's separation summary is retracted with the
same scope. **A refined Def 4 is being specified separately (Colomban,
2026-08-13) and will replace the σ-player definition; the redefinition should
reuse the instance layer unchanged.**

---

# Part IV — Definition 5: σ-probing (common-knowledge blur) — SHELVED; see `DEF5_SYS_BINDER_ROADMAP.md`

**SHELVED 2026-08-17 — the project continues on Def 4.** Def 5 was fully mechanized
through milestone 1 (2026-08-13: the `.sys` mutual-fixpoint binder, `PlaysProof.sysStep`,
two σ-instance Pf readers, and `outcome_TauDupocSys_vs_TauDupocSys = (C, C)` as a
3-axiom theorem), then the engine extensions were reverted; the complete buildable
state is archived at git tag `taubot-def5-research`. The Phase-4 vector Löb engine and the
`sysLob` spikes remain in-tree (no Def-5 dependency). Full record in the roadmap note.

**Def 5** replaces Def 4's point-mass probes with σ-probes: hypotheses are
instantiated at the *blurred signal itself* (`probe(B, σ_T)`, not `probe(B, δ_T)`),
making blur common knowledge rather than a private handicap. No closed `Prog` term
exists for the σ-zoo (the reference graph is the complete digraph; one `.self` cuts
one cycle), so Def 5 forces either a mutual-fixpoint binder `.sys` (**Route A**,
provisionally chosen 2026-08-13) or a belief-order tower over closed lower-level
instances (**Route B**, the standing fallback, no language change, Löb only at the
bottom level — i.e. Def 4 is the Löbian base case of Def 5's approximation tower).
Fixed conventions, predictions (split collapse, non-total matrix), the phased
roadmap with byte-identity gates, and the kill criteria all live in
`DEF5_SYS_BINDER_ROADMAP.md` — read it before touching anything `.sys`.
