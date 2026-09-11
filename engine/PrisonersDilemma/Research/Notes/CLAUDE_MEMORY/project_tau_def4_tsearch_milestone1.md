---
name: tau-def4-tsearch-milestone1
description: Def-4 TauBots — σ-player layer RETRACTED 2026-08-13 (correct Def 4 = uniform SOURCE LIFT, coincides with Def 3; implemented TauEBot = crowd-exploiter, wrong); tsearch core + instance layer stand; Metatheory UNPINNED pending M2
metadata: 
  node_type: memory
  type: project
  originSessionId: 74dc1ffb-8539-458e-acdb-91ab279f8107
  modified: 2026-08-13T14:41:42.379Z
---

**Def 4 = tau-native bots** (hypotheses AND probes are TauBots, all recursion through
`proofSearch` — Löb breaks the regress that sank Def 1). Authoritative: Part III of
`engine/PrisonersDilemma/Research/Notes/TAUBOTS.md (condensed 2026-08-26)`. Milestone 1
landed 2026-08-11 (commits 7b2d617 + the tau-layer commit after it).

**What shipped.** `Prog.tsearch k gs θ p q` (weighted-threshold search; `GuardList`
INSIDE the mutual block, never `List (Nat × Formula)`); stepwise peel eval (θ=0
short-circuit; per-peel fuel); 5 PlaysProof rules (`tsearchZero_t/Nil_f/Cons_t/
Cons_f/High_f` — Cons_f keeps the per-guard search_f floor; High_f is the
bit-independent `θ > totalMass` else-commit); NO new Pf modal rules (probed
δ-instances stay `.search` singletons — the quine `TauDupocδ k` reads via
`botSearchStep`). Zoo: TauCooperate/TauDefect/TauDupoc/TauTFTSim/TauTFTPf in
`Tau/{Defs,PeelLemmas,Certs,Phases}.lean` + `Theorems/Tau/Matrix.lean` (25 coop-regime
cells + 3 highθ self-plays). Headline: all three θ-bots flip C→D at θ = wC+wTs+wTp+wL;
the prover/behavioral split is a BUDGET gap (TFTSim k≥2ish, TFTPf shallow, Dupoc the
Löb threshold via `ps_probe_quine`). Exploitation cells (C,D) vs TauDefect are
theorems. 81 old outcome statements byte-identical; 3 axioms; zero sorry.

**Why: proof-craft traps hit (do not re-hit).**
- The equation compiler SILENTLY fell back to WF recursion on the enlarged `subst`
  mutual block, killing rfl/defeq everywhere (Base/Helpers `show`s, AtomCerts rfl).
  Fix: `termination_by structural p _ _ => p` on all three defs. Check defeq with a
  scratch `example : ... := rfl` after ANY mutual-block change.
- An inner `match gs` inside an eval arm breaks equation-lemma generation
  (`rw [eval]` fails); use NESTED PATTERNS (`.tsearch _ .nil …` / `.tsearch k (.cons …)`)
  as separate top-level arms.
- Tactic `induction` refuses mutually-inductive `GuardList`; `cases` works; write
  list inductions as equation-style recursive theorems (+ `termination_by structural`).
- Auto-bound implicit order in new constructors is unpredictable — declare binders
  explicitly when eliminator lambdas must match positionally.
- simp δ-reduces named defs inside eval-unfoldings: state guard-bit hypotheses in the
  UNFOLDED form (`have hps' : … := hps` via defeq) before `simp [..., hps']`.
- Derived-BEq ifs (`(C == C) = true`) don't reduce under `simp only`; discharge with
  `if_pos rfl` / `if_neg (by decide)` or trailing `decide`.
- One heartbeat bump needed: MirrorBot_plays_D_against_OBot (enlarged eval simp-set).

**THE CASCADE REFACTOR (2026-08-12, commit 5fe2fd2) — supersedes the EBot parts
above.** Colomban caught the class bug: Def 4 routes bits through `proofSearch`, so
Dupoc must NOT prove EBot's cooperation (the base floor). Audit found 4 bugs, one
root cause: TauEBot-as-reciprocity-vote was Def 2's rejected geometry, and two
self-probing bots form an INEXPRESSIBLE mutual-quine 2-cycle (`E(δ_L) ↔ L(δ_E)`) —
hence the stipulated instances. Fix: base EBot's CASCADE lifted at both levels —
`eδ k I_D I_C` instance template (exploit δ_D probe then reciprocity δ_C probe);
`eOfSearchδ` now REALLY cooperates UNPROVABLY (`interp_probe_eOfSearch` +
`ps_probe_eOfSearch_false`, the Gödelian pair) via the NEW Exclusion lemma
`no_provable_botSearcherElse_tail` (.bot-frozen searcher's non-then-action play:
search_t dies by action mismatch, search_f pays the kb floor; else-branch
shape-general, no guard-truth hypothesis — the action-refined set kernel was built
for this); TauEBot σ-player = NESTED tsearch (exploit stage then tftPfSig stage,
shared θ; at point-mass ≡ eδ; NO quine, NO Löb). Results: TauDupoc's boundary
honestly drops wE → all three cooperators share `wC+wTs+wTp+wL` (the 20 mixed-cell
theorems were artifacts, deleted); **TauEBot cooperates in a WINDOW
`wC < θ ≤ wC+wTs+wTp+wL` — defects at BOTH α-extremes**; Matrix.lean regenerated:
79 theorems (exploitθ/window/highθ for every EBot pair). Python: `Probe.CASCADE` +
`prover` flag + `FLOOR_BLOCKED_HYPOTHESES` in def4.py; scanner = conjunctive
hypothesis lists (theorems PARTITION the θ-axis per pair — row_action is just
full-applies at the player's own (θ,w⃗)). Verified: control + separating both 100%
certified (1400/1400), 0 conflicts.

**RETRACTION (2026-08-13): Def 4, correctly read, COINCIDES with Def 3.** Colomban
(from the TauEBot self-play (D,D) cell): Def 4 is a uniform STRUCTURAL SOURCE LIFT
— lift A's own code constructor-by-constructor, σ-player takes ONE vote over the
COMPOUND per-hypothesis bits ("what does A's lifted code decide vs B's instance" =
the self-probe bit = Def 3's bit). Dupoc/TFTs conformed by accident (one decision
point); the cascade TauEBot moved θ INSIDE (per-STAGE crowd votes) — a coherent
"crowd-exploiter" but NOT τ(EBot), whose bits give a ONE-SIDED boundary
wTs+wTp+wL, no window. The window/(D,D)-self-play/45-56-divergence claims are
retracted (they describe the crowd-exploiter); the instance layer (eδ, Gödelian
pair, floor lemma, shared cooperator boundary) STANDS and is what τ consumes.
Def 4's real content over Def 3: budget structure (Löb thresholds, floor,
prover/behavioral gap), non-liftable Mirror branch (E's self-bit convention), cost
intensionality. A refined Def 4 is being specified separately by Colomban; reuse
the instance layer, replace the σ-player. Design note Part III carries the full
retraction section.

**DEBT (Milestone 2, planned):** `Metatheory` is UNPINNED from `lakefile.toml`
defaultTargets (header note in `Decidability.lean`) — T31–T54 have no tsearch arms
yet; the certified outcome-prepass (evalG/guardFastN) cannot see tau terms until M2.
Restore + extend: enumProg over GuardList, decCertG stepwise cases, evalG 3-valued
peel with non-pivotal squeeze, T43/T50 walkers, T49 substrate (~1wk alone).

Related: [[tau-v1a-explorer]], [[egt-integration]].
