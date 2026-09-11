---
name: def5-sys-binder-route-a
description: "Def-5 σ-probing TauBots — FULLY MECHANIZED then SHELVED 2026-08-17 (project stays on Def 4); archive tag taubot-def5-research; vector Löb engine + sysLob spikes retained in-tree"
metadata: 
  node_type: memory
  type: project
  originSessionId: 972a594b-b246-44dd-8f2b-080f8d467155
  modified: 2026-08-13T17:04:12.589Z
---

**SHELVED (2026-08-17, project decision): the thesis continues on Def 4.** The
full Route-A arc (Phases 0–5, milestone 1) was completed 2026-08-13 — 
`outcome_TauDupocSys_vs_TauDupocSys = (C,C)` was a 3-axiom theorem — then the
ENGINE extensions were reverted in one commit to free the Def-4 track of the
standing tax (T31–T54 arms for .sys/.selfIdx + 2 Pf constructors; hbotsys/h_sys
census obligations; prompt surface). **Archive: git tag `taubot-def5-research`** — the
complete buildable state; do NOT try to re-land from memory, check out the tag.
KEPT in-tree (no Def-5 dependency): Base/Loeb's vector Löb engine
(compUnder/postUnder/swapAnte, loeb_premise_under_box, vector2_full_pblt_engine
— full-dependency mutual Löb, available for Def-4 cross-bot arcs) and
Research/Spikes/sysLob/. Revival path if ever wanted: Route B (belief-order
tower, no language change) is cheaper than re-landing Route A. Everything below
is the historical execution record.

**Def 5** (2026-08-13): σ-probing TauBots — hypotheses instantiated at the blurred
signal itself (`probe(B, σ_T)`), making blur COMMON KNOWLEDGE, vs Def 4's point-mass
`probe(B, δ_T)` (first-order uncertainty). No closed `Prog` term exists for the σ-zoo
(complete-digraph reference graph; one `.self` cuts one cycle), so it forces either:

- **Route A** (provisionally CHOSEN): mutual-fixpoint binder `.sys`/`.selfIdx`/`ProgList`
  in the `Program.lean` mutual block; vector bounded Löb generalizing
  `mutual_pblt_engine_id` to n sentences; positivity condition on the zoo (anti-monotone
  member = zoo-level anti-diagonal inconsistency).
- **Route B** (standing FALLBACK at every gate): belief-order tower over closed
  lower-level instances — no language change, Löb only at the bottom (Def 4 IS the
  Löbian base case of the tower).

Authoritative note: `engine/PrisonersDilemma/Research/Notes/TAUBOTS.md (condensed 2026-08-26)`
(conventions 1–9, predictions, phase table, kill criteria); pointer added as Part IV of
`TAUBOTS.md (condensed 2026-08-26)`. **Phase 0 (conventions) is DONE; nothing committed.**

**Phase 1 DONE (2026-08-13): BOTH SPIKES PASS** (`Research/Spikes/sysLob/`, committed).
- Spike A `VectorPblt.lean`: `vector2_full_pblt_engine` is a THEOREM on the live
  engine (full-dependency n=2 premises incl. self-loops → both sentences provable;
  3-axiom footprint). Iterated-unary route, ZERO new constructors (Family-B `implS`
  carries the B-combinator glue); reusable atom = `loeb_premise_under_box` (Löb under
  a boxed side-antecedent, side box PRE-LOWERED so K-dist lands under the self-box).
  Cost caveat: threshold constants cascade 2^(O(n)) (master 2⁵²·V vs cycle 2¹⁷·V) —
  fine at zoo scale; n-ary diag is the unscheduled poly(n) refinement. The `_id`
  engines' hardcoded 100·log+1000 bounds DON'T fit intermediates — Phase 4's
  vector engine must stay budget-parametric.
- Spike B `MiniSys.lean`: equation-compiler gate PASS (all rfl defeq tests; sysClose
  structural unannotated; nested-.sys shadowing benign; Nat+Option indexing fine).
  BINDING constraint for Phase 2: eval must THREAD FUEL PER LIST ELEMENT (same-fuel
  list recursion silently goes well-founded and kills rfl — tsearch landmine).
**Phase 2 DONE (2026-08-13): LANGUAGE LANDED, GATE MET.** `ProgList` + `.sys`/`.selfIdx`
in the Program.lean mutual block; subst: `.sys` barrier / `.selfIdx` fixpoint;
`sysClose` family (structural, `.bot`-transparent, inner-`.sys` shadowing) +
`get?`/`psize`; honest size; `hasSearch := true` both (searchfree overapprox).
Dynamics: lazy-unfold eval arm + `eval_sys_some/none`/`eval_selfIdx` unfolding
lemmas. Fallout = 6 files, ALL proof-internal arms (subst-preimage censuses,
`hasSearch_subst`, `cert_searchfree`, `eval_mono`) — ZERO statement changes,
3-axiom footprint re-verified, Spike A recompiles, real-engine defeq suite passes.
Metatheory debt now covers `.sys`/`.selfIdx` (lakefile note).
**Phase 3 DONE (2026-08-13, same day): S READS THE BINDER.** `PlaysProof.sysStep`
(get? + one sysClose level, c_node; NO `.selfIdx` rule — absence IS the honest
reading); both eliminators wired; `Pf_mono` untouched (cases-on-Pf only);
`wv_sound_upto` gained `h_sys` (h_tsearch pattern) + PASS-1 soundness arm
(`eval_sys_some`, the machine gate) + PASS-2 kill arm; 5 instantiation sites
discharged trivially; `Base/Exclusion.lean` untouched (Pf constructors unchanged).
Build green, zero statement changes, 3 axioms; sanity derives
`Pf 16 (.plays (.sys demo 0) opp .C)` through the .bot-frozen reference.
**Phase 4 DONE (2026-08-13, same day): vector engine PROMOTED, size-parametric.**
`Base/Loeb.lean` now has compUnder/postUnder/swapAnte + `loeb_premise_under_box` +
`vector2_full_pblt_engine` with a `C·log₂k + D` envelope (verified at 5000/90000).
Omega gotcha: parametric coefficients need `ring`-supplied expansions
(`(4C+1)·L = C·L+C·L+C·L+C·L+L`) since `C·log₂k` is a nonlinear atom. Build green,
3 axioms, cycle engines untouched, spike kept as historical record.
**Phase-5 ZOO FIXED by Colomban (2026-08-13, revised same day: TauTFTPf OUT of
M1) — `Tau/SysDefs.lean` LANDED, building (3306 jobs):** probe DIRECTION
survives, only the SIGNAL blurs. TauDupocσ probes `Bᵢ(σ_Dupoc)` ("Bᵢ whose
signal is the blur of ME" — reciprocity); TFTσ watches `Bᵢ(σ_Coop)`. REJECTED:
probing members directly (collapses Dupoc into TFT). Closure = SIX members:
0=C, 1=D, 2=Dupoc(σ_D) [probes {0,1,2,3}, slot 2 = SELF = quine φ₁],
3=TFTSim(σ_D) [runs σ_C column {0,1,4,5}], 4=Dupoc(σ_C) [probes {0,1,2,3},
L-slot → member 2 not itself — same guard list wires both correctly],
5=TFTSim(σ_C) [runs {0,1,4,5}, slot 5 sims ITSELF]. Top players
TauDupocSys/TauTFTSimSys over the closed system (.sys defs j, free w⃗/θ).
THREE M1 findings: (1) Löb core is UNARY (no prover probes σ_C) →
pblt_engine_id suffices, vector engine waits for M2; (2) regime-dependent
DIVERGENCE — member 5's self-sim diverges, iteTree's structural θ=0
short-circuit saves cooperative regimes, elsewhere false-but-IRREFUTABLE bits
→ OPEN bands; guard order: irrefutable-risk LAST; (3) peel-to-implication
RESOLVED: ONE new Pf modal rule needed, `botSysTsearchBranch` (botSearchStep
generalized to .bot (.sys …)-wrapped .tsearch, peel prefix by actual
premises, ONE deferred guard as □-antecedent, θ-arithmetic side conditions) —
NEXT ENGINE STEP via constructor playbook (sound_upto arm = machine gate).
**botSysTsearchBranch LANDED (2026-08-13, commit 7d138ba): the 32nd Pf
constructor.** S reads .bot (.sys defs i) with member i a .tsearch: peel prefix
by ACTUAL premises (head cited at c_guard, second refuted paying the m+g floor),
ONE deferred guard = the □-antecedent; w₁ < θ ≤ w₁+w₃ commits at the deferred
guard, trailing (irrefutable-risk) slots never read. Machine gate (wv PASS-2 arm)
compiled: interp half = eval chain with the refuted bit via strong IH + floor;
census half = self-cite + hs. ReadableMe gained the 7th disjunct
(.bot (.sys …)); floor censuses gained hbotsys; ~25 theorem files discharge by
shape (zero statement changes). VALIDATED: at dC=dD=dL=dT=1, θ₂=2, S derives the
REAL quine Löb premise □_100 φ₁ → φ₁ (refutation needs budget ~2000 — psize
counts the whole zoo; plan budgets accordingly in ps_probe_sysQuine).
**MILESTONE 1 COMPLETE (2026-08-13, a82e01b): outcome_TauDupocSys_vs_TauDupocSys
= (C,C) IS A THEOREM** (+ (D,D) α-flip), 3 axioms, build green 3308 jobs.
Final design fix by COST: Löb premise must be O(log k) but a prefix refutation
pays the floor ≥ k ⟹ guard order [C, L, D, Ts] (Löbian SECOND) + 33rd
constructor botSysTsearchDefer (cited head + deferred Löb guard; trailing
unread). Files: Tau/SysCerts.lean (iteTree_size_le, probe_sysZoo_size_le with
sysB weight-envelope, sysQuine_loeb_premise, ps_probe_sysQuine via pblt_engine
+ play→bit inversion, tauDupocSys_phase), Theorems/Tau/SysMatrix.lean.
Regimes: instance dC+dT < θ₂ ≤ dC+dL; player θ ≤ wC+wL / wC+wL+wT < θ; band =
honest OPEN. k₂ depends on weights (honest .sys sizes) — unlike Def 4.
Proof-craft traps hit: simp [Nat.log2] explodes the structural rec (use decide
on literal numCost facts); rw needs syntactically uniform n+1+1 fuel shapes
(never n+2); eval_mono_le returns the eval-form (state eval-form lemmas).
Milestone 2 = TauTFTPf return (vector engine) + TauEBotσ (blocked on Def-4
τ(EBot) redefinition). Key fixed conventions: lazy unfold (sysClose structural,
fuel pays unfolding); `.bot` is a subst barrier but TRANSPARENT for sysClose; system
members `.self`- and `.opp`-free; honest size (`.sys` counts the whole system);
Def-4's ".search singleton" convention DIES under σ (everything non-constant is
.tsearch; sysStep + peel rules replace searchBranch/botSearchStep). Predictions to
check: prover/behavioral split COLLAPSES; Def-5 matrix NOT total (bistable cross-θ
cells). Related: [[tau-def4-tsearch-milestone1]].
