# LLM distillation via automata learning / program synthesis — design discussion recap

*Recap of a design conversation, 2026-08-10. Status: idea stage, nothing implemented.
Goal: extract an open-source program that mimics an LLM's game-playing behavior, so the
LLM becomes a formal object the Lean engine can prove theorems about.*

---

## 1. The starting idea (Route A: behavioral automaton extraction)

Treat the LLM as a black-box oracle: feed it a game situation, read off C or D. Use
classical automata learning — Angluin's **L\*** — to extract a minimal finite-state
strategy, as Weiss et al. (ICML 2018) did for RNNs. The extracted object is small,
formal, and directly consumable by the engine: import it, prove outcome theorems,
measure exploitability.

**Reference:** Weiss, Goldberg & Yahav, *Extracting Automata from Recurrent Neural
Networks Using Queries and Counterexamples*, ICML 2018, arXiv:1711.09576. Membership
queries = forward passes of the RNN. Equivalence queries = the clever part: a parallel
abstraction of the RNN's hidden-state space (partition, refined on demand); disagreements
between the L\* hypothesis and the abstraction yield candidate counterexamples, each
checked against the real RNN. **That trick is white-box** — with an API-only LLM we fall
back on sampling / bounded-exhaustive equivalence testing.

## 2. L\* in one page

Learner knows the alphabet Σ, nothing else. Two query types against a teacher/oracle:

- **Membership**: what is the output after input string w? (Moore-machine variant.)
- **Equivalence**: is my hypothesis automaton correct? If not, give a counterexample.

Data structure: the **observation table** — rows indexed by prefixes S ∪ S·Σ (access
strings ≈ candidate states), columns by suffixes E (**distinguishing experiments**),
entry (s, e) = oracle's answer on s·e. A row is a behavioral fingerprint; identical rows
are provisionally the same state (finite approximation of Myhill–Nerode classes).

Loop: fill table until **closed** (every one-step successor row matches some S-row —
else promote: new state found) and **consistent** (same-row prefixes stay same-row after
any letter — else a distinguishing suffix a·e joins E and splits them). A closed,
consistent table *is* an automaton (states = distinct rows). Submit as equivalence query;
counterexamples force at least one new row. Distinct rows ≤ n (minimal target size) ⇒
termination in ≤ n equivalence queries, polynomial queries total, and the output is the
**minimal** machine.

**Suffixes are the anti-early-stopping mechanism.** TFT needs only E = {ε} (its two
states differ in immediate output). Tit-for-Two-Tats does not: fresh and one-strike both
output C, merge under E = {ε}, hypothesis collapses to always-C; a counterexample (cd·cd)
contributes suffix "cd", the rows split, the third state appears. L\* never *invents*
suffixes creatively — they are extracted mechanically from counterexamples. **The whole
burden of "don't stop too early" lives in the equivalence oracle.**

**States ≠ outputs.** {C, D} is the output alphabet; states are Nerode classes of
histories (memory). Same-output states differ by transitions (TFT's D-state vs Grim's
absorbing D-state). State counts are unbounded (tit-for-k-tats: k+1; "defect when total
defections exceed cooperations": not finite-state at all — L\* state blow-up is the
*diagnostic* for non-regularity or nondeterminism).

## 3. When to stop — the honest options

Exact identification of a black box from finitely many queries is impossible (infinitely
many consistent machines always remain). Every stopping rule is a stated assumption:

1. **State bound n** → W-method/Chow test suite → *exact* result relative to the bound.
2. **Horizon bound d** → exhaustive testing → "correct on all inputs of length ≤ d."
3. **Sampling** → PAC: ε-close under the sampling distribution, prob 1−δ. The
   distribution does silent epistemic work (a distribution that rarely produces dd·dd
   never refutes always-C for TF2T).
4. **Stability under escalating budgets** → inductive evidence only.

**Resolution for our use case: bounded horizon is all we need.** Any experiment we run is
finite; two strategies agreeing on every history reachable in the actual experiments are
interchangeable *for those experiments*. The claim is never "the LLM *is* TFT" but "in
this scope, the LLM's play is identical to this machine, whose properties are proven."
The extracted object is a **certified compression of observed behavior with a stated
scope**; the unbounded tail is where residual trust lives, irreducibly.

Efficiency note (vs "just fill in the whole depth-d table"): the exhaustive sweep is the
*equivalence oracle*, not the table. Only failures (counterexamples) enter the table,
which stays O(states) — a compressed, human-readable certificate (S = one access string
per state, E = one experiment per distinction). L\* membership queries also probe beyond
depth d where the state structure demands it. LLM inference calls are the scarce
resource; L\*'s table for a 3-state strategy is ~50 calls regardless of d.

## 4. The OSGT twist: there are no histories

Critch's game is **one-shot transparent PD**: a strategy is a function
`Prog → {C, D}` (at budget k) — the input is the *opponent's source code*, a tree, not a
move sequence. The object to extract is the set {B : LLM cooperates against B}, i.e. a
**classifier over program space**. Two formulations:

### Formulation A — faithful analog: tree automata

`Prog` is a tree over the ranked constructor alphabet (.const/.self/.opp/.bot/.sim/
.ite/.search + Formula constructors). Sets of programs = tree languages; the DFA analog
is a deterministic bottom-up tree automaton; MAT-model learners exist (Drewes–Högberg).
Caveats: (i) do **not** serialize trees and run string-L\* — serialized well-formed
programs are Dyck-like/context-free, string-regularity is the wrong lens; (ii) the
interesting policies ("cooperate iff provably-cooperates-back") are **semantic, not
syntax-regular** — the learner would not converge, which is itself a finding but not an
extraction.

### Formulation B — bounded domain + compile-back (the buildable one)

1. **Domain**: all `Prog` of size ≤ s. Finite even with `.search` budgets (numCost =
   log₂k+1 counts toward size), but cap budget literals to a small menu in practice;
   restrict guard formulas to zoo shapes (the modest fragment) or pay the enumeration.
2. **Oracle**: existing LLM client. Frozen rendering convention (Lean source or Critch
   pseudocode — the LLM sees text), frozen prompt incl. **the self-representation
   convention** (what the LLM is told its own visible source is — a real degree of
   freedom, see §6), temperature 0, best-of-3 majority; disagreeing votes → `unstable`,
   excluded from certified support. Persist all transcripts (they are the ground truth
   that the Lean table is generated from).
3. **Table + compression** (the experiment): fit the finite table with
   (a) a decision tree over syntactic features, (b) a minimal tree automaton
   (state-merging on the finite sample), (c) **behavioral regression** — replace each
   opponent's syntax by its certified profile row (`build_profile`) and fit against
   that; if semantically-equal-but-syntactically-far pairs always get the same verdict,
   the LLM tracks meaning, not syntax. The compression ratio is the result. Validate on
   a held-out size-(s+1) ring.
4. **Compile-back into `Prog`** — the language was accidentally ready for this:
   `Formula.eq` has a frozen-literal RHS and a substituted probe LHS
   (Program.lean), and `Pf.eqRefl` / `Pf.eqNeg` make both polarities of an identity
   test cheaply certifiable atoms. Finite-support policy ⇒ right-nested chain
   `.search kᵢ (.eq .opp Bᵢ) (.const aᵢ) (…)` ending in `.const d`; budgets computed
   from the table (kᵢ ≥ 2·|Bᵢ|+1 for eqRefl). No Löb anywhere: the guard universe is
   trivially decidable and modest ⇒ `guardFastN`/`outcome_prepass` determines every
   cell. Behavioral variant if (3c) wins: nested `.ite` with `.sim` guards
   (branch on the opponent's play against a probe bot); wrap named bots in `.bot`;
   beware guard nontermination (fuelled eval can return none — the MirrorBot trap).
5. **Lean certification**, three separate theorems with separate jobs:
   - **(a) Agreement certificate**: transcripts → generated Lean constant
     `llmTranscript : List (Prog × Action)`; per-row theorems "mimic plays aᵢ vs Bᵢ".
     `eval` is noncomputable (proofSearch), so these go through the prepass:
     `outcomeG_sound ∘ guardFast_sound` Tier-0 certificates. Scope honesty: Lean
     certifies *mimic ≡ transcript*; transcript ≡ LLM is the frozen experimental
     protocol — same trust boundary as the NL→Lean bot translation.
   - **(b) Outcome theorems**: stage the mimic, run the normal pipeline, land
     `llm_outcome_LlmMimicBot_vs_X`; the mimic then participates in tau sweeps, EGT
     populations, the sheet — for free.
   - **(c) Interpretive theorems** (the payoff): non-identity with named strategies
     (exhibit a certified distinguishing opponent), exploitability (worst-case payoff
     over the zoo + the exploiting program), characterization of the compressed rule.

## 5. The Löbian objection (the important one)

**A lookup mimic cannot represent "if I can prove you cooperate against me, then…".**
On the tested support it is extensionally perfect and even highly legible (support
opponents can verify its plays at tiny budget, so support matchup outcomes reproduce).
The failure is **off-support and qualitative**: a fresh Löbian opponent hits the default
branch (say D), proves it, defects — (D,D) where the true semantic policy would have run
the Löb handshake to (C,C). Finite extensional agreement cannot pin down the intensional
rule; the TF2T lesson lifted to program space.

**Fix: the hypothesis class is `Prog` itself — synthesis, not automata.** The language
already contains the Löbian policies (CIMCIC, DIMCID, PrudentBot are ~10-node terms):

- Candidates = the same size-bounded enumeration (incl. `.search` schemas with a swept
  budget parameter); find the **smallest program (MDL) matching the transcript table**.
- Scoring is certified and LLM-free: the prepass computes each candidate's row against
  the battery. (Searcher-heavy candidates are the slow cells — filter on cheap cells
  first, verify survivors.)
- **L\* returns as hypothesis splitting**: when two candidates survive (lookup table vs
  PrudentBot₃₂), both are white-box Lean objects — *search opponent space for a
  discriminating opponent* (their certified plays differ), query the LLM only there.
  Counterexample-driven refinement with a computable equivalence check between
  candidates; maximally query-efficient.
- The lookup chain remains the **null hypothesis**: if no small semantic term beats it
  under MDL, the finding is "no evidence of proof-theoretic structure at this scale,"
  quantified by the compression ratio.

Steps 3 and 5 are unchanged under this upgrade — only the compile/compress step widens.

## 6. The reflective fixed point (possibly the headline)

In OSGT, "what does B play against the LLM?" is **ill-defined**: B's move is a function
of the opponent's source, and the LLM has none. The membership queries only ever capture
one side of the game. The mimic is therefore not just a compression — **it is what makes
the LLM a player at all**: the source handed to opponents on the LLM's behalf.

This closes the self-representation convention reflectively: tell the LLM "your visible
source is M" (current extraction), re-run the table, extract M′, iterate. A **fixed
point** M — the LLM, told its code is M, behaves exactly as M — is a *self-fulfilling
source*: the program the LLM is willing to be. Does the iteration converge? Does it
converge to something Löbian (does a frontier model honor a legible cooperative source)?
Every step is certified by the engine. No known prior art for this experiment.

## 7. Open decisions / next steps (if pursued)

- Rendering convention (Lean source vs pseudocode) and prompt freeze; self-representation
  for round 0 (before any mimic exists).
- Budget-literal menu and guard-formula fragment for the size-≤s enumeration; choice of s.
- Default action d off-support (compression's prediction vs paranoid D).
- Stability protocol: votes per query, `unstable` handling, model/version pinning
  (the extraction is per-checkpoint).
- Where the Python lives: `app/`, sibling of `bot_profile.py` (enumerator, query loop,
  compressor/synthesizer, transcript→Lean generator); memory discipline from the EGT
  notes applies to prepass sweeps.
- Relation to E-experiments: this is a candidate E5; the discriminating-opponent loop and
  the fixed-point iteration are the two publishable novelties beyond straight distillation.
