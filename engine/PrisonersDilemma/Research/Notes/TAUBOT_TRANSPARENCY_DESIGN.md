# TauBots — graded transparency over the zoo (design note)

*Status: design discussion, 2026-07-31. Nothing implemented yet.*

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

- σ = point mass (full transparency) → the tau tournament **provably reproduces
  the base outcome matrix** (see the anchor below) → Critch's OSGT regime.
- σ = uniform (zero transparency) → cooperation mass is a constant per agent →
  everyone plays an *unconditional* strategy → classical opaque one-shot PD.

The tau family continuously interpolates between OSGT and classical game theory.
Headline experiment: *how much transparency does Löbian cooperation need?*

## Two dials — do NOT conflate them

- **σ-temperature `t`** = *transparency* (property of the signal/environment):
  how concentrated the posterior is on the true opponent. Principled % scale:
  normalized mutual information `I(B; σ(B)) / H(B)`.
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

> **Anchor theorem (cheap in Lean): at t = 0 the tau tournament equals the base
> outcome matrix.** TauA(δ_B) plays exactly what A plays against B.

So Def 3 is genuinely "A with blurred vision"; Def 2's reciprocity probe is a
separate interesting bot *family*, not the lift. The two coincide exactly on
outcome-reciprocal bots (worth a lemma).

### The probe × hypothesis square

|                       | hypotheses = base Bᵢ | hypotheses = TauBᵢ |
|-----------------------|----------------------|--------------------|
| **self probe** (A vs hyp)      | ✅ matrix cell — **Def 3** | ❌ needs A run on tau source: new proofs, breaks constraint 1 |
| **reciprocity probe** (hyp vs A) | ✅ matrix cell — Def 2 | ✅ meta-computable (level-2, see below) |

`outcome(A, TauBᵢ)` (top right) is the unique corner NOT reducible to the
matrix: A's *machinery* must execute on tau *source* — a bigger term, new
theorems, budget floors shift with program size, Löb shapes change. And
`outcome(A(TauB)) = outcome(A(B))` is FALSE as a theorem in general (three
failure levels: TauB ≠ B behaviorally at intermediate blur; OSGT is intensional
— provability is about terms, and costs scale with term size; the mutual-Löb
fixpoint shapes don't exist against tau-shaped terms). Stipulating the equation
as a *definition* is fine — but that stipulation IS Def 3, so just write
`outcome(A, Bᵢ)`.

If tau-aware opponents are ever wanted: the bottom-right corner (level-2
reciprocity) stays matrix-computable — TauBᵢ's response is itself arithmetic
over layer-0 cells (given conventions for its α′ and its signal). Hard-stop the
hierarchy at depth 2. Deferred to v2.

## The behavioral/prover split (thesis-grade theorem candidate)

Under *dynamic signals with transparent counterfactuals* (see conventions):

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

## Conventions & open design decisions

1. **Open matrix cells.** The matrix is PARTIAL by theorem (JustBot-vs-MirrorBot
   is bistable). Convention needed: pessimistic (open counts as non-C — current
   default in the sketch) vs drop-and-renormalize. They give different results.
2. **Budgets.** Matrix entries are budget families, often staggered
   (PrudentBot 2k+64 vs Dupoc k). The tau layer is defined over the stable
   asymptotic outcome with one canonical budget convention per pair.
3. **Static vs dynamic signals.** *Static* (signal baked in at compile time):
   the compiled TauB sims only closed matchups → TauB is extensionally a
   CONSTANT program; simple, but counterfactual queries about it are degenerate.
   *Dynamic* (evaluator applies σ at every interface, including inside sims):
   needed for the behavioral/prover split theorem; a real eval-semantics change.
4. **Transparency inside counterfactuals.** Does an in-sim TauB get δ (identity
   is given by construction inside a sim) or σ (blur compounds through nested
   counterfactuals)? δ is the convention assumed by the split theorem; σ gives a
   different, also interesting object.
5. **σ design.** Needs a distance on bots: use *behavioral* distance (Hamming
   between outcome-matrix rows), softmax with temperature t. Computable from
   data we already have; "close" means "plays like".
6. **Tie-breaking**: `≥ α` vs `> α`; only finitely many α matter (subset sums of
   the support) — enumerate them for sweeps.

## Implementation plan

**Division of labor (key consequence of Def 3): the tau layer is
matrix-arithmetic, so the *experiments* belong in Python, not Lean.** Once the
matrix is exported (the sheet-sync extraction of `(llm_)?outcome_A_vs_B` +
`outcome_status.toml` for open cells already does this), everything downstream
— the σ family, behavioral distances, the MI transparency scale, (t, α) sweeps,
phase diagrams, whole tau tournaments — is plain arithmetic in `app/`. No Lean
in the loop, instant iteration. The trust chain stays honest: Lean-verified
cells + transparent Python arithmetic.

Keep a **thin Lean core** only for what must be a theorem: the meta-level
definitions below, the anchor theorem (t = 0 reproduces the matrix), a few
certified sample cells cross-checking the Python, and — later — anything
involving mixed base-vs-tau matches (the split theorem, the v2 compilation),
which cannot even be *stated* outside Lean.

**v1a — Python explorer (start here).** Matrix export → σ/α sweep engine →
phase diagrams. Purely `app/`-side.

**v1b — meta-level Lean core.** TauBots as Lean functions over the
matrix, not `Prog`s:

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

**v2 — in-language compilation (upgrade path, only if mixed base-vs-tau matches
are wanted).** For a fixed signal, `Σ pᵢ·[Cᵢ] ≥ α` is a fixed monotone boolean
function of n bits → TauA compiles to an ordinary nested `.ite`/`.sim` `Prog`.
**No language extension needed** (no arithmetic in `Prog`; p and α are baked in
at compile time). Caveats: fuel scales with tree size; `.sim` of search-bot
matchups hits the evalG/Löb boundary.

## σ family roadmap (2026-08-03)

A σ family is **(what leaks) × (how it blurs)** — two orthogonal axes. All
families are calibrated onto the SAME transparency dial t ∈ [0,1] (normalized
MI, inverted per family by bisection — `app/src/pd_runner/tau/channels.py`),
so at matched t the information rate is identical and only the confusion
structure differs: cross-family gaps are purely about WHICH bots get confused.

**Implemented (v1):**
1. **behavioral** — softmax over Hamming distance on own-action rows. NOT ad
   hoc: it is the exact Bayes posterior (uniform prior) of watching every
   match through a binary symmetric channel, since p^d(1-p)^(n-d) ∝
   exp(-d·ln((1-p)/p)).
2. **ε-uniform** — (1-ε)δ + ε·U. The null control: no similarity structure,
   identity-based (no twin ceiling). Divergence from it isolates the effect
   of confusion structure itself.
3. **syntactic (codebase)** — softmax over L1 distance between `Prog`
   constructor-profile feature vectors extracted from `Bots/*.lean`
   (`tau/syntax.py`). Partial transparency of the SOURCE — degraded OSGT.
   **Confusion-structure inversion** (the headline): Dupoc/Cupod are
   syntactic near-twins (identical tree, leaf labels swapped, d=2) but
   behavioral opposites; Coop/Defect adjacent constants (d=2) but conduct
   opposites; while Coop/CupodTroll are behavioral near-twins yet syntactic
   opposites. Own blind spot: **DBot/TitForTatBot are syntactic twins**
   (identical constructor profiles, referenced-bot names opaque) ⇒ syntactic
   ceiling ≈ 0.947 — even full code transparency cannot anchor, mirroring the
   behavioral twin ceiling.

**Recorded for later (in rough priority):**
- **AST tree edit distance** (Zhang–Shasha) on real `Prog` terms — replace the
  feature-vector shadow; wants a Lean-side `#eval` exporter printing canonical
  S-expressions rather than parsing `.lean` text.
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

## Related dials & future work

- **Budget k is the *depth* transparency dial** (Critch's original bounded
  mutual transparency); σ is *breadth* (identity uncertainty). Compare the axes.
- **Hole-masked source** ("prove C for all completions of the hidden AST") is
  the semantic ideal that this finite type space approximates; heavy engine work
  (program quantifiers in `Formula`), framing/future work only.
- **Rejected**: syntactic noise on the source (prover bots reason soundly from a
  wrong premise — kills constraint 1); genuinely probabilistic agents
  (measure-theoretic eval + probabilistic Löb — a thesis in itself).
