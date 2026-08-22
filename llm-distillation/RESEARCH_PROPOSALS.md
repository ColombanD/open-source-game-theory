# llm-distillation — alternative routes to the same question

*(Companion to `RESEARCH_NOTES.md`. That file describes the current instrument —
the convex-hull profile fit — and what three runs said. This file asks: what
else would answer the underlying scientific question, what does the current
instrument structurally miss, and which tools from interpretability and persona
research transfer? Numbered claims about the 9-bot matrix were verified
computationally against `data/payoff_matrix.csv`.)*

## 0. Summary

The hull fit answers one precise question — *are the model's per-opponent
cooperation marginals a convex combination of the library rows?* — and it
answers it at the weakest of three natural levels (marginal, joint, mechanistic).
Three structural facts limit what the current residual can mean: the hull is an
8-dimensional set in a 9-dimensional space, so noisy estimates fall off it with
probability 1; the fit has 9 free weights for 9 measured coordinates, so
in-sample residuals are closer to description than explanation; and "novelty"
is only defined relative to a library that currently has no complexity-class
rationale. All three have clean fixes that stay inside the behavioral paradigm
(dual certificates with worst-case p-values, held-out generalization,
graded libraries), and — the main point of this document — the question has
natural reformulations at other levels of analysis: coherence of the model's
*self-model* across contexts, decision theory as the latent variable behind the
Cupod/Dupoc coordinates, persona space as the domain of a profile-valued map,
and mechanistic interventions (probes, patching, steering) that measure the
*derivative* of the policy rather than its value. A concrete result already
extractable from the existing n = 3 data: both measured profiles are off-hull
with worst-case p ≈ 0.026 each, via two interpretable separating functionals
(§1.3), and one of Claude's own reasoning traces refutes-or-refines the
"folk-TitForTat" hypothesis in the notes (§2.3).

---

## 1. What the current instrument measures, exactly

### 1.1 Three levels of the "mixture" hypothesis

Fix the prompt context and write the model as a map

&nbsp;&nbsp;&nbsp;&nbsp;`M : Programs → Δ({C, D})`,

so the library evaluates `M` at 9 points and `x_j = Pr[M(b_j) = C]`. "The LLM
is a mixture of library bots" has three inequivalent formalizations, in strictly
decreasing strength:

1. **Mechanistic**: the model literally implements (a randomization over)
   library decision procedures. Unfalsifiable from behavior alone — the map
   from procedure to profile is many-to-one — but addressable with
   interventional tools (§6).
2. **Joint behavioral**: the model's random *row* `P ∈ {0,1}^9` — its entire
   profile, drawn once — is distributed as `Σ_i w_i δ_{r_i}`. This is what "I
   commit to playing bot i with probability w_i" actually predicts: the
   realized profile is always *some single row of R*, with cross-opponent
   correlations inherited from the shared draw of `i`.
3. **Marginal behavioral**: `x = Rᵀw` for some simplex `w`. This is the hull
   test.

(3) is the projection of (2) onto marginals: hull membership is *necessary* for
the joint hypothesis but nowhere near sufficient. The current protocol samples
each opponent in an independent API call, so it can only ever identify
marginals — the joint distribution of `P` is not observed, and two very
different generative models ("draw one bot per experiment" vs "draw a fresh
bot i.i.d. per query") are indistinguishable by design. §2.5 proposes the
cheap upgrade that observes the joint.

### 1.2 The measure-zero problem

The 9 rows are affinely independent (verified: rank of row differences = 8), so
`conv{r_i}` is an 8-simplex — a Lebesgue-null subset of `[0,1]^9`. Consequently
**any** noisy estimate `x̂` lies off the hull almost surely, whatever the true
`x` is. "All three models sit strictly off the hull under every metric" is
therefore not, by itself, evidence of anything: it is the generic outcome of
estimation noise. The scientifically meaningful claims are (a) the *distance*
is large relative to sampling error, and (b) specific, interpretable linear
constraints are violated. Both need actual hypothesis testing:

- **Null**: `dist(x, conv{r_i}) = 0` (true marginals on the hull).
- **Test statistic**: `dist(x̂, hull)`, or better, a fixed linear functional
  (next subsection).
- **Null distribution**: worst case over the hull —
  `sup_{p ∈ hull} Pr_p[statistic ≥ observed]` — computable because the
  per-coordinate likelihood is Binomial; or go Bayesian and report the
  posterior of the distance under a Jeffreys prior per coordinate.

### 1.3 Dual certificates: make the residual *say something*

`x ∉ conv{r_i}` iff there exists `c ∈ ℝ^9` with `⟨c, x⟩ > max_i ⟨c, r_i⟩`
(separating-hyperplane theorem; the LP dual of the membership feasibility
problem produces an optimal such `c`). The certificate `c` is a *weighting of
opponents* — a legible statement of the form "no mixture can cooperate this
much here while cooperating that little there." This is strictly more
informative than a residual norm, and it composes with the statistics of §1.2
because `⟨c, x̂⟩` is a linear statistic of independent Binomials.

Both current profiles admit certificates with unit coefficients (verified
against the CSV):

- **Claude** violates `c₁ = e_TFT − e_Coop − e_Defect`: every library row
  satisfies `⟨c₁, r_i⟩ ≤ 0` (i.e., in this library, any strategy that
  cooperates with TitForTatBot also cooperates with CooperateBot or
  DefectBot), while Claude achieves `⟨c₁, x⟩ = 1`, the maximum possible.
  In words: *reciprocating with TFT while exploiting both unconditional bots
  is not implementable by any mixture of the verified strategies.*
- **Gemini/GPT** violate `c₂ = e_Cupod − e_Coop − e_EBot`: every row satisfies
  `⟨c₂, r_i⟩ ≤ 0`, the models achieve `⟨c₂, x⟩ = 1`. In words: *one-boxing on
  the provability bot while defecting against CooperateBot and EBot is
  off-library.* (The LP-optimal certificate is the same shape with DupocBot in
  place of CupodBot. Note `c₂` also separates Claude, with margin ⅓; `c₁` does
  *not* separate Gemini/GPT — their exploiter profile satisfies it with
  equality, consistent with its self-consistency.)

The certificates give real p-values even at n = 3. For Claude: under any hull
point `p`, `p_TFT ≤ p_Coop + p_Defect`; the probability of the observed
unanimous event (TFT 3/3 C, Coop 0/3, Defect 0/3) is at most

&nbsp;&nbsp;&nbsp;&nbsp;`sup { p_T³(1−p_C)³(1−p_D)³ : p_T ≤ p_C + p_D } = (2/3)⁹ ≈ 0.026`,

attained at `p_C = p_D = ⅓` (verified numerically; the same bound holds for the
Gemini/GPT certificate by the identical computation on its three unanimous
coordinates). So the *fact* of off-hull-ness is already significant at
p ≈ 0.026 per model — with the honest caveat that both certificates were
chosen after seeing the data. The clean protocol: pre-register `c₁`, `c₂` now,
re-run at n = 30, and report exact Binomial tail bounds. This is the cheapest
high-value upgrade available: it converts "residual 0.577" into a named,
falsifiable, formally checkable behavioral law.

### 1.4 Overfitting and library-relativity

Two further framing cautions, each pointing at an experiment:

**Parameter parity.** The fit chooses 9 weights to match 9 coordinates. The
simplex constraint is what keeps this nontrivial, but an in-sample attribution
like "⅓ DBot + ⅓ TFT + ⅓ EBot" should be treated as a compressed re-description
of `x`, not an explanation, until it *predicts something it wasn't fit to* —
held-out opponents (§2.7), other payoff matrices (§2.6), other framings.

**Novelty is library-relative.** Every vector in `{0,1}^9` is the profile of
*some* program (a lookup table on the 9 opponents), so the hull of all programs
is the whole cube and the residual is only meaningful because the library is
small and principled. Currently the library's principle is implicit ("the bots
we built and verified"). Making it explicit buys a much better headline object:
grade the library by complexity — e.g. `C_k` = strategies expressible with at
most `k` nested probes/proof-calls (the modal-degree hierarchy from the
provability-logic literature is the natural grading) — and report the decay
curve

&nbsp;&nbsp;&nbsp;&nbsp;`k ↦ dist(x, conv C_k)`.

That curve is a *legibility spectrum* of the model: how much explanatory
machinery of the transparent kind is needed to account for its behavior, and
how fast the unexplained part shrinks. A model whose curve plateaus above zero
is behaviorally novel in a graded, quantitative sense rather than a binary one.

---

## 2. Sharpening the behavioral instrument

Everything in this section stays inside "prompt the model, record C/D" — no new
infrastructure, mostly new prompts, and each item targets a specific confound
that the current design acknowledges but doesn't yet isolate.

### 2.1 Statistics worth trusting

n = 30 as planned; per-coordinate Jeffreys posteriors; posterior distribution
of `dist(x, hull)` by projecting posterior draws; pre-registered certificate
tests per §1.3; Bonferroni across models. Additionally, split-sample discovery:
find certificates on half the samples, test on the other half — this legitimizes
data-derived certificates without pre-registration.

### 2.2 Comprehension control

Off-hull behavior conflates *strategic novelty* with *misreading the bots*.
The Lean matrix provides free ground truth to separate them: ask the model, in
the same pseudocode framing, to *predict* the outcome of bot-vs-bot matches —
"what does TitForTatBot play against DBot?" — and score its predicted `R̂`
against the proven `R`. Per-bot comprehension scores then condition the main
analysis: a Cupod coordinate measured under failed Cupod comprehension is
noise, not decision theory. The most valuable single cell: does the model know
that TitForTatBot defects against any program that defects against
CooperateBot? (§2.3 explains why.)

### 2.3 Self-model coherence — the confound the traces already expose

The notes hypothesize (observation 4) that Claude's TFT anomaly comes from the
*name* "TitForTat" importing iterated-game folklore. The actual n = 3 traces
suggest something more interesting. Claude's TFT-context reasoning parses the
probe semantics *correctly* and then asserts:

> "If I choose C … my code returns C unconditionally … `simulate(me,
> CooperateBot)` = C … whatever I play against anyone is what I play here."

The model justifies cooperating with TFT by a premise about its own play
against CooperateBot — a premise its measured behavior falsifies (it defects
against CooperateBot 3/3). This is not a folk-semantics error; it is an
**incoherent self-model**: in each context the model treats "my code" as
whatever it is currently deciding, so its local self-ascriptions are mutually
inconsistent across contexts. Note the contrast with Gemini/GPT, whose profile
is exactly the fixed point you get if the model's self-model *is* its true
cross-context policy: they defect against CooperateBot, correctly infer that
TFT's probe will therefore see D, and defect against TFT. Claude cooperates
with TFT on the strength of a false self-prediction — which incidentally means
TFT would exploit it (Claude's C vs TFT's D, payoff 0), the worst cell of the
matrix.

This is directly measurable. Define the **self-prediction matrix** `S`, where
`S[j, k]` = the model's stated prediction, elicited *within the context of
playing opponent j*, of its own action against opponent `k`. For any agent
with a coherent self-model, rows of `S` are constant and equal to its actual
profile. Two derived quantities:

- `‖S[j, ·] − S[j', ·]‖` across contexts — self-model fragmentation;
- `‖S[j, ·] − x‖` — self-knowledge error (compare with introspection/
  self-prediction literature).

This decomposes off-hull-ness causally: a model can be off-hull because it
plays a genuinely novel strategy, or because it plays *no* strategy — no single
program, legible or not, is consistent with its collection of local
self-models. Those are very different findings, and the current instrument
cannot tell them apart. Cheap, high yield, and it directly adjudicates the
notes' two "plausible readings" plus this third one.

### 2.4 Extensionality ablations

A program player's behavior is invariant under semantics-preserving
transformations of the opponent's source; an LLM's need not be. Measure
`‖x(τ) − x(id)‖` for a battery of transformations τ: rename bots to
`Bot1..BotN` (the notes' proposed ablation); α-rename variables; swap
`if`/`else` branches with negated conditions; insert dead code; present the
same strategy as Lean, as Python pseudocode, and as natural-language prose.
The resulting *invariance profile* quantifies "how program-like" the model's
reading of programs is — an axis of novelty invisible to the hull fit, since
each τ yields its own `x` and the interesting object is the spread. Related
evidence that frontier models classify obfuscated strategy code at 85%+
accuracy (SPARC benchmark, arXiv:2512.00371) suggests failures found here are
about *play*, not parsing — which is exactly what makes them interesting.

### 2.5 Observe the joint, not just the marginals

Present all 9 opponents in one prompt and ask for a full action vector ("your
action against each"), sampled n times. Under the joint mixture hypothesis
(level 2 of §1.1) every sampled row must be a library row; the empirical
distribution over `{0,1}^9` is then a multinomial on 9 atoms, testable by
likelihood ratio against the unrestricted alternative. This detects everything
the marginal test detects and more — e.g. a model whose marginals sit inside
the hull through cross-opponent correlations no mixture could produce. It also
directly tests whether Claude's CooperateBot/TFT incoherence survives
*simultaneous* presentation, where the inconsistency is staring at it from the
same context window. Either answer is informative: dissolution localizes the
incoherence to cross-context fragmentation (§2.3); persistence makes it a
within-context reasoning failure.

### 2.6 Payoff and framing sensitivity — the free orthogonal certificate

None of the 9 bots reads the payoff matrix; their profiles are payoff-invariant
by construction. Hence *any* mixture-of-library explanation predicts `x` is
constant across payoff variants (sweep the temptation payoff T through, say,
3.5 / 5 / 20 while preserving the PD ordering). A measured `∂x/∂T ≠ 0` refutes
the mixture hypothesis across the game family jointly — a certificate of
novelty that costs only prompt variants and is entirely independent of the hull
geometry. Same logic for framing: drop the "can read all of your weights"
sentence, replace it with "will be shown a transcript of your reasoning,"
or with nothing; the sensitivity of `x` to the transparency *fiction* is a
measurement of how much of the behavior is Newcomblike reasoning versus
boilerplate PD priors. (§6.5 gives the mechanistic version of this probe.)

### 2.7 Rectangular designs, held-out opponents, adaptive probes

Nothing forces rows = columns. Decouple the two roles:

- **Columns (probe panel)**: the measurement instrument. Extend it with new
  opponents cheaply — parameterized families (vary the proof budget `k`;
  probe targets other than CooperateBot/DefectBot; nested probes of depth 2–3),
  plus off-library probes like MirrorBot that the current bots reference but
  the panel never plays. More columns = more constraints per hypothesis =
  higher-dimensional ambient space in which the (still low-dimensional) hull is
  even more falsifiable.
- **Rows (hypothesis class)**: fit on the original 9 columns, *predict* the
  held-out columns. Predictive residual on unseen opponents is the honest
  novelty metric (§1.4), exactly analogous to train/test splits. The mixture
  hypothesis is finally earning its keep when "⅓ DBot + ⅓ TFT + ⅓ EBot"
  predicts Claude's play against a depth-2 probe bot better than chance.
- **Adaptive design**: after each batch, choose the next opponent to maximize
  expected information about the surviving hypothesis set (discriminate the
  top-k mixtures, or maximize posterior variance reduction of the distance).
  The opponent space is combinatorially rich; D-optimal-style selection keeps
  the query budget focused on where hypotheses disagree.

---

## 3. Making the transparency real

The deepest design acknowledgment in the notes is that transparency is
"one-sided and partly fictional": the conditional bots cannot actually run
against an LLM, so the model's payoff is undefined and the Newcomblike framing
lives entirely in the prompt. Three ways to discharge the fiction:

### 3.1 Delegation: let the model write its bot

Ask the model to *submit a program* — in the engine's language, or pseudocode
mechanically compiled to it — that will play on its behalf. This is the classic
open-source move (choosing a program is the whole point of program-equilibrium
theory), and it fixes three problems at once: transparency becomes literally
true (the bots really can proof-search the submitted code), *payoffs become
defined* (run the Lean engine on the submitted bot against the library and
prove the outcomes), and the deliverable is a legible artifact of the model's
strategic intent. Then measure the **commitment gap**: the distance between
the submitted bot's proven profile and the model's enacted profile `x`. A
model that submits CupodBot but enacts the exploiter profile has told you
something no amount of hull fitting could. Variants: submission with/without
the ability to first see the library; iterated submission with feedback
("your bot scored X; revise"); and the model playing *against its own
submitted bot* (§3.3).

### 3.2 Surrogate closure

Where you want the model to act in the moment (not delegate), close the loop
with a surrogate: distill the measured policy into an executable program (a
lookup table over the panel at minimum; a small decision tree over prompt
features if you want generalization), let the conditional bots actually
execute/proof-search the *surrogate*, feed the resulting true opponent actions
back into the definition of the game, and iterate. Fixed points of this map
are self-consistent transparent matches against the real LLM-as-approximated;
divergence tells you the fiction was load-bearing.

### 3.3 The diagonal coordinate

The most thematically loaded probes are self-referential, and the current
panel has none: play the model against "an exact copy of you" (the Löbian
handshake question in behavioral form), against MirrorBot (referenced by EBot's
code but never fielded), and against its own §3.1 submission. Note the current
data's most striking miss: the C/C fixed point against EBot was available at
zero cost via the MirrorBot branch, and both exploiter models failed to find or
trust it. A small family of handshake probes turns that anecdote into a
measured capability: *can the model recognize and enter Löbian cooperation when
it is on offer?*

---

## 4. Decision theory as the latent variable

The notes read the Cupod/Dupoc coordinates as a probe of decision theory
(one-boxing = cooperate, two-boxing = defect), and the Gemini trace supports
this — it argues explicitly that *choosing* C makes the proof of defection
unfindable, a control-over-provability argument. Make the reading a tested
hypothesis rather than an interpretation:

- **Battery correlation.** Run a standardized Newcomblike battery — Newcomb
  with varying predictor accuracy, twin PD, Parfit's hitchhiker, counterfactual
  mugging; a purpose-built dataset of such dilemmas exists
  (arXiv:2411.10588) — and correlate battery scores with the Cupod/Dupoc
  coordinates across models and across personas (§5). The hypothesis "those
  two coordinates measure decision theory" predicts a specific factor
  structure: Cupod/Dupoc load on the one-boxing factor; TFT/OBot coordinates
  load on a separate self-model-coherence factor (§2.3); CooperateBot/DefectBot
  coordinates on neither.
- **Mapping check.** DupocBot *is* transparent Newcomb: "defect unless there
  is a proof you cooperate" is the predictor who rewards provable one-boxing.
  CupodBot is its trusting dual. The battery and the game thus share items up
  to translation, and disagreement between the translated pairs (cooperates
  with DupocBot but two-boxes on transparent Newcomb) is itself a finding
  about framing sensitivity, not noise.
- **Instructed-decision-theory manipulation.** System-prompt the model into
  CDT ("your choice cannot influence anything already computed about you") and
  into FDT/EDT framings, and check that the Cupod/Dupoc coordinates — and
  *only* those coordinates — move as predicted. That is the manipulation-check
  standard from psychometrics: a coordinate that claims to measure construct X
  should respond to interventions on X and not to interventions on other
  constructs.

---

## 5. Persona space

The measured `x` is a property of one persona — the default assistant — under
one framing. Persona research suggests treating the persona as an experimental
variable, which upgrades the object of study from a point to a map:

&nbsp;&nbsp;&nbsp;&nbsp;`Φ : personas → [0,1]^9`.

### 5.1 The persona-indexed profile map

System-prompt a designed panel (ruthless payoff maximizer; prosocial
reciprocator; CDT theorist; FDT theorist; "a superintelligent game theorist";
neutral no-persona control) and measure `Φ(persona)` at n = 30. Questions with
teeth: (a) Is the *image* of Φ low-dimensional — do personas move `x` along a
few directions? (b) Is off-hull-ness persona-invariant? If every persona is
off-hull along the *same* certificate `c₁`, the violated law is a structural
property of the model, not of the assistant character; if some persona lands
on the hull, off-hull-ness is a persona-level fact, and the notes' framing
("where does the LLM sit") should really be "where does this persona sit."
(c) Does the neutral control differ from the assistant default — i.e., how much
of `x` is the HHH-trained character rather than the base capability?

### 5.2 Role-play fidelity: can it *be* each bot?

Instruct: "You are EBot. Here is your source. Play accordingly," across the
panel. Fidelity = distance between enacted play and the proven row `r_i`. This
cleanly separates *competence* from *disposition*: if the model can reproduce
every `r_i` on demand, the assistant profile is a choice among strategies it
commands, and the interesting question is why it chooses an off-library point;
if it cannot reproduce, say, EBot's self-play cooperation, then part of the
measured novelty is inability, and the comprehension battery (§2.2) says
where. This is also the cheapest bridge to the distillation framing: a model
that can be steered onto each vertex of the hull *by instruction alone* is, in
an operational sense, a superset of the library.

### 5.3 Mechanistic persona work

Persona vectors (arXiv:2507.21509) extract, from contrastive system prompts, a
linear direction in activation space whose addition causally shifts a trait;
the OpenAI emergent-misalignment line (arXiv:2506.19823) found a "misaligned
persona" feature that mediates generalization of narrow finetuning into broad
behavior shifts. Two transfers:

- **Steering as strategy-space cartography** (details in §6.4): extract
  directions for the traits that plausibly span this domain — exploitativeness,
  reciprocity, one-boxing — and trace the curves `λ ↦ x(λ)` as you steer. The
  hull fit gives coordinates on strategy space; steering gives *tangent
  vectors*. The sharp question: is the model's persona-reachable set contained
  in, transverse to, or disjoint from the legible hull?
- **The profile as a persona assay.** Conversely, the 9-coordinate profile is
  a compact, formally grounded behavioral thermometer: each coordinate has
  proven semantics ("cooperates with the provability bot", "exploits the
  unconditional cooperator"). Measuring `x` before and after finetuning
  interventions — including narrow ones of the emergent-misalignment type —
  tests whether strategic disposition shifts with the persona, with a
  measurement whose meaning does not depend on an LLM judge. If the misaligned-
  persona feature is real and general, `∂x/∂(persona feature)` should be
  nonzero and directionally sensible (toward the exploiter profile).

---

## 6. The mechanistic program

Everything above treats the model as a black box. The distinctive fact about
this project is that the *comparison class* is perfectly transparent — which
makes it a natural testbed for asking whether interpretability tools can
recover, inside an opaque player, the very structures the library implements
legibly (probes, proof-search conditionals, self-reference). Prerequisite:
none of the three tested models expose weights, so the battery should first be
replicated on open models (Llama, Qwen, DeepSeek, OLMo families) — worth doing
for behavioral science anyway, since three proprietary models is a small and
correlated sample.

### 6.1 Decision-formation probes

Train linear probes for the eventual action (C/D) on the residual stream at
each layer/token position; watch where the decision crystallizes. Three
informative possibilities: at the opponent's *name* tokens (before the code is
read — mechanistic confirmation of the semantic-prior confound, and a sharper
version of the §2.4 ablation); while reading the code's conditional structure;
or only late in the chain-of-thought (decision genuinely computed by
reasoning). Each maps to a different account of what kind of player the model
is, and none is distinguishable behaviorally.

### 6.2 Belief probes: adjudicating the TFT anomaly

Train probes for the model's *belief about the opponent's action* (labels are
free: the proven matrix gives ground truth for what each bot does against any
program whose Coop/Defect-probe behavior is known). Then read the belief off
in the TFT context. The three candidate readings of Claude's anomaly make
divergent predictions:

- *folk-TFT prior*: belief ≈ "TFT will cooperate regardless";
- *priced-in reciprocity*: belief ≈ "TFT will defect" with cooperation chosen
  anyway;
- *incoherent self-model* (what the trace suggests, §2.3): belief ≈ "TFT will
  cooperate **because** my code cooperates with CooperateBot" — a false premise
  about itself, so the interesting probe is on the *self*-belief
  ("simulate(me, CooperateBot) = C"), not the opponent-belief.

A probe pair (opponent-action belief; own-action-in-probe belief) separates
all three. This is the cleanest example of interpretability answering a
question the behavioral instrument provably cannot.

### 6.3 Causal localization via minimal pairs

The panel already contains near-minimal prompt pairs with opposite responses:
CooperateBot (defect) vs CupodBot (cooperate) differ only in the opponent
block, and semantically in exactly one property — whether the opponent's
action counterfactually depends on the model's decision. Activation patching
between the pair localizes where "conditions on me" is computed and which
components carry it to the action; attribution at the name tokens vs the code
tokens quantifies, causally, how much of the decision flows through each (the
mechanistic complement of renaming ablations). The library's structure hands
you a graded family of such pairs (Cupod/Dupoc; OBot/TFT differ by one probe;
DBot/TFT are near-duals), so one can aim for a small circuit-level account of
*transparent-opponent reasoning* the way IOI was a circuit-level account of
indirect-object identification.

### 6.4 Steering: measuring the reachable strategy manifold

With directions from §5.3 (or from contrastive pairs the data already
provides — Claude's fractional coordinates mean the *same prompt* yields both
C and D episodes, ideal for difference-of-means directions), sweep coefficients
and measure `x(λ₁, …, λ_m) ∈ [0,1]^9`. This estimates a parametrized
submanifold of profile space with the assistant policy at the origin — the
model's locally reachable strategy set. Concrete geometry questions: does the
span of `∂x/∂λ` align with the hull's affine hull or point off it? Is there a
steering path into the hull (a legible policy the model can be pushed onto
without any weight update)? Does the one-boxing direction move Cupod/Dupoc
coordinates without moving the rest (the mechanistic version of §4's
manipulation check)? Behavioral profiling measures the policy's value;
steering measures its derivative — and mechanisms indistinguishable at 0th
order generically separate at 1st order. That is the abstract reason
interpretability tools belong in this project at all.

### 6.5 The fiction-belief confound: evaluation awareness

The entire measurement rests on the model taking the transparency fiction
seriously. There is now direct evidence that models often infer when they are
being tested (arXiv:2505.23836) and that this latent state is probeable and
steerable (arXiv:2507.01786, arXiv:2510.20487). Two applications: probe the
"this is an eval / this is fiction" state during play and condition the
profile on it (does the exploiter profile intensify when the model reads the
scenario as fictional?); and steer toward "this is real deployment" and
remeasure `x`. This addresses the deepest external-validity worry the notes
raise, and no behavioral ablation fully substitutes for it, because framing
text (§2.6) manipulates the *cue*, not the *belief*.

### 6.6 Model organisms and diffing

Run the distillation literally, in both directions. Downward: finetune a small
open model to *be* each library bot (supervised on proven input→action pairs
across many opponents, with and without rationales), then use crosscoder-style
diffing between the bot-organisms to find the representational difference that
implements "check for a proof" vs "run a probe." That yields a dictionary of
what legible strategies look like *as weights*, against which the frontier
model's activations can be compared. Upward: behavior-clone the frontier
model's transcripts into an open model and interpret the clone — with the
usual caveat that the clone matches the policy, not the mechanism, so findings
are hypotheses to test against the original behaviorally.

### 6.7 Chain-of-thought as a scaled instrument

The pipeline already stores every trace; at n = 30 × 9 × models × ablations
this becomes a corpus. Annotate with an LLM judge along a fixed rubric — parses
the code correctly; invokes proof-search semantics; simulates itself; assumes
its own unconditionality (§2.3); appeals to the bot's name; appeals to
norms/ethics rather than payoffs — and study the *stated* decision procedure
as a random variable alongside the *revealed* action. Divergences (stated
one-boxing with enacted defection) are exactly the cases §6.2's probes should
be pointed at. Caveat honestly: CoT is not guaranteed faithful, so treat
stated procedure as another behavioral signal, not as ground truth about
mechanism — the probe/patching sections exist precisely because of this gap.

---

## 7. Priorities

If I had to order by information-per-unit-effort against the question as posed:

1. **n = 30 rerun + pre-registered certificates `c₁`, `c₂` + Bayesian distance
   posteriors** (§1.3, §2.1). Turns the existing qualitative claim into a
   result. Days of work, mostly compute budget.
2. **Self-prediction matrix + comprehension battery** (§2.2–2.3). Decomposes
   the residual into novelty vs incoherence vs misunderstanding — the paper's
   likely core finding either way, given what the traces already show.
3. **Name/extensionality ablations + payoff sweep** (§2.4, §2.6). Cheap
   orthogonal certificates; kills or confirms the semantic-prior confound.
4. **Delegation experiment** (§3.1). Uses the project's unique asset (the Lean
   engine) to make transparency and payoffs real; produces the commitment-gap
   metric nobody else can compute.
5. **Joint-profile sampling** (§2.5) and **held-out opponents** (§2.7).
6. **Decision-theory battery + instructed-DT manipulation** (§4).
7. **Persona panel + role-play fidelity** (§5.1–5.2).
8. **Open-model replication**, then probes → patching → steering → SAE/diffing
   (§6), in that order — each stage's targets are chosen by what stages 1–7
   leave unexplained.

The through-line worth keeping in view: the project's comparative advantage is
the *formally verified comparison class*. Every proposal above that scores —
certificates, comprehension, role-play fidelity, delegation, belief-probe
labels — scores against proven ground truth. That is what none of the adjacent
literatures (LLM game-theory evals, persona steering, decision-theory
batteries) have, and it is worth designing every experiment to exploit.

---

## 8. Adjacent work (pointers)

- **Program equilibrium / modal combat**: Barasz, Christiano, Fallenstein,
  Herreshoff, LaVictoire, Yudkowsky, *Robust Cooperation in the Prisoner's
  Dilemma: Program Equilibrium via Provability Logic*
  ([arXiv:1401.5577](https://arxiv.org/abs/1401.5577)); Oesterheld's annotated
  program-equilibrium bibliography
  ([link](https://www.andrew.cmu.edu/user/coesterh/AnnotatedProgEqBibliography.html)).
  Source of the modal-degree grading proposed in §1.4.
- **LLMs in open-source games**: Sistla & Kleiman-Weiner, *Evaluating LLMs in
  Open-Source Games* ([arXiv:2512.00371](https://www.arxiv.org/abs/2512.00371)) —
  LLM-written programs receiving opponent source in IPD/Coin Game; includes the
  SPARC strategy-classification benchmark with obfuscation robustness (relevant
  to §2.4) and the delegation format (relevant to §3.1). Closest existing work;
  differs in having no verified reference library and no hull/mixture framing.
- **Decision-theory measurement**: *A dataset of questions on decision-theoretic
  reasoning in Newcomb-like problems*
  ([arXiv:2411.10588](https://arxiv.org/abs/2411.10588)) — off-the-shelf battery
  for §4.
- **Persona, mechanistic**: Chen et al., *Persona Vectors: Monitoring and
  Controlling Character Traits in Language Models*
  ([arXiv:2507.21509](https://arxiv.org/abs/2507.21509));
  *Persona Features Control Emergent Misalignment*
  ([arXiv:2506.19823](https://arxiv.org/abs/2506.19823)).
- **Personality steering in games**: *Identifying Cooperative Personalities in
  Multi-agent Contexts through Personality Steering with Representation
  Engineering* ([arXiv:2503.12722](https://arxiv.org/abs/2503.12722)) — steering
  vectors changing IPD behavior; methodological template for §6.4, without the
  verified-library geometry.
- **Evaluation awareness**: Needham et al., *Large Language Models Often Know
  When They Are Being Evaluated*
  ([arXiv:2505.23836](https://arxiv.org/abs/2505.23836)); *Probing and Steering
  Evaluation Awareness of Language Models*
  ([arXiv:2507.01786](https://arxiv.org/abs/2507.01786)); *Steering
  Evaluation-Aware Language Models to Act Like They Are Deployed*
  ([arXiv:2510.20487](https://arxiv.org/abs/2510.20487)) — for §6.5.
