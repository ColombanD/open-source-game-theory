# Definition 5 — σ-probing TauBots via a mutual-fixpoint binder (Route A)

**Status: PROVISIONAL, Phase 0 fixed 2026-08-13.** Route A chosen provisionally over
Route B (the belief-order tower); Route B remains the fallback at **every** gate below,
and nothing before Phase 2 is Route-A-specific sunk cost. Re-decide after Phase 1, with
Spike A's budget arithmetic in hand. Parent note: `TAUBOT_TRANSPARENCY_DESIGN.md`
(Parts I–III: Defs 1–4); this note is its Part IV.

## What Def 5 isTauA(alpha)(TauBi(alpha); 1)

Def 4 probes hypotheses at **point-mass** signals: `probe(B, δ_T)` = "does B, seeing
exactly T, cooperate". Def 5 probes at the **σ-blur itself**: `probe(B, σ_T)` = "does
B, seeing T through the same blurred signal I have, cooperate". Blur stops being a
private handicap and becomes **common knowledge** — the full Harsanyi hierarchy where
Def 4 is the degenerate one (first-order uncertainty: I'm unsure who you are, but I
assume you know who I am).

**The two routes** (decision record 2026-08-13):

- **Route A (this note):** extend `Prog` with a mutual-fixpoint binder `.sys`; the
  σ-zoo is ONE mutually-recursive system. Exact semantics.
- **Route B (fallback):** belief-order tower — level-(n+1) instances probe hypotheses
  instantiated at signals over *closed level-n terms*. No language change, Löb only at
  the bottom level (= Def 4 as shipped), term size ~`|zoo|ⁿ` per level. Approximates A,
  converging on monotone zoos; doubles as A's validation oracle later (tower plays must
  converge to the fixpoint's).

**Why Route A needs a binder — the forcing fact.** `Prog` is a plain inductive: a term
contains itself only through `.self`/`.opp`. TauDupocσ's guard list must contain
`probe(TFTPfσ)` and TFTPfσ's must contain `probe(TauDupocσ)`; a `.self` inside another
bot's `.bot`-frozen source resolves to *that bot* (the subst barrier), the wrong object.
One `.self` cuts one cycle; the σ-reference graph is the **complete digraph** on the
non-constant zoo. No closed term exists.

**Anti-patterns (do not retry):** single-`.self` quine encodings of the mutual system;
eager unfolding at definition time (no fixed point, size-divergent); encoding "B sees T"
in the opponent slot (Def-4 anti-pattern, still banned).

---

## Part I — Fixed conventions (Phase 0)

1. **The binder.** Three additions to the `Program.lean` mutual block:
   `ProgList` (a mutual-block member, the `GuardList` precedent — NEVER a nested
   `List Prog` payload), `.sys : ProgList → Nat → Prog` (the i-th component of a
   mutually-recursive system) and `.selfIdx : Nat → Prog` (reference to component j
   from inside a system). Out-of-range index: `.sys defs i` with `i ≥ defs.length`
   evals to `none` (fuel-style failure), never a default action.

2. **Lazy unfold.** `sysClose defs : Prog → Prog` is a STRUCTURAL map replacing
   `.selfIdx j ↦ .sys defs j` and touching nothing else. The eval arm unfolds ONE
   level per fuel tick: evaluating `.sys defs i` runs `sysClose defs (defs.get i)` at
   decremented fuel — repeated unfolding is paid by fuel exactly as `.self` re-entry
   is. `.sys` terms never unfold at definition time. This is the choice that keeps
   `subst`/`sysClose` structurally recursive (the tsearch landing's `termination_by
   structural` lesson).

3. **Two closers, complementary barriers.** `subst` (match-level: `.self`/`.opp`)
   never touches `.selfIdx`; `sysClose` (system-level) never touches `.self`/`.opp`.
   Crucially, **`.bot` is a barrier for `subst` but TRANSPARENT for `sysClose`** —
   frozen hypotheses inside guard formulas carry `.selfIdx` references and must close.
   Simplifying convention: **system members are `.self`- AND `.opp`-free** (all
   self-reference through `.selfIdx`; tau players stay extensionally constant, Def-4
   convention 4 in force). Obligation: the subst/sysClose commutation lemma, trivial
   under this freeness convention — state and prove it in Phase 2.

4. **Honest size.** `(.sys defs i).size = 1 + defs.gsize + numCost i`;
   `(.selfIdx j).size = 1 + numCost j`. Transcript costs must see the WHOLE system —
   this is where Route A's n-dependent constant enters every budget. Sizes stay
   `O(log k)` in k for a fixed zoo, with constants `O(n · maxMemberSize)`. Obligation
   (Spike A): measure whether the milestone zoo's probe atoms fit the hardcoded
   `≤ 100·log₂ k + 1000` hypotheses of the pblt engines, or parametrize the engines
   (the n-ary engine should be size-parametric regardless).

5. **Probe atoms unchanged in shape.** `probe I := .plays (.bot I) (.bot I) .C`,
   `.bot`-freezing mandatory (the OUTER match's subst barrier). Inside a system
   definition a guard stores `probe (.selfIdx j)`; after `sysClose` it is the closed
   atom `φ_j = probe (.sys defs j)`. The sentence system of Def 5 is the vector
   `{φ_j : j entangled}`.

6. **Positivity is load-bearing.** A decidable syntactic predicate
   `Positive : Prog → Prop`: every guard is a positive probe (`.plays … .C`; no `.neg`
   above a sys-referencing atom; thresholds on cooperation mass only). STANDING
   HYPOTHESIS of every Def-5 theorem, discharged per-zoo by `decide`. Forced by: an
   anti-monotone member reproduces the anti-diagonal inconsistency (the
   `atom_complete_false_guard` killer) at the ZOO level — under Def 4 an anti-diagonal
   bot poisons only itself; under Def 5 the sentence system is shared.

7. **Guard order: entangled (sys-referencing) guards LAST** — Def-4 convention 5,
   same short-circuit rationale; "Löbian" now means "sys-referencing".

8. **Def-4 convention 6 DIES.** Prover instances are no longer `.search` singletons —
   every non-constant σ-instance is a `.tsearch` over the full signal.
   `searchBranch`/`botSearchStep` do NOT apply; the transparency route is the new
   `sysStep` rule + the tsearch peel rules (`tsearchCons_t` citing entangled guards at
   `c_guard k`, the same cite-not-reprove affordance that makes the mutual premises
   affordable). Recorded so nobody hunts for the singleton trick.

9. **τ-reading inherited** (the 2026-08-13 TauEBot retraction): ONE vote per bot over
   whole-cascade hypothesis bits; θ never moves inside a cascade. Def-5 instances of
   multi-branch bots follow the corrected τ, not the crowd-exploiter.

---

## Part II — Predictions (to check, not to assume)

1. **Split collapse.** TauTFTSimσ's `.sim` guards watch Löb-gated σ-instances, so its
   budget threshold inherits the Löb constant *semantically*. The Def-4 headline
   "prover/behavioral split = budget gap" should NOT survive σ-probing — and the exact
   way it fails is the finding.
2. **One collective α-boundary** for the entangled core: the bits fire jointly (vector
   fixpoint), so cooperation is more all-or-nothing than Def 4's per-bot boundaries.
3. **Defect legs restructure.** `θ > W`: shallow via `tsearchHigh_f` + a refutation
   cascade — the defect regime needs NO Löb (roles exactly swapped vs the cooperative
   leg). The band `W_coop < θ ≤ W`: meta-level consistency inversion (the
   `interp_probe_*_false` pattern, longer chains). Cross-θ pairs may be genuinely
   bistable ⇒ **the Def-5 matrix is NOT total by construction**; open cells are
   findings (JustBot-vs-MirrorBot treatment, `outcome_status.toml`).

---

## Part III — Roadmap

| Phase | Deliverable | Gate | Effort |
|---|---|---|---|
| **0** ✓ | This note: conventions + kill criteria | — | ½ day |
| **1a** | Spike A `Research/Spikes/sysLob/VectorPblt.lean`: n-ary mutual bounded Löb (iterated-unary vs n-ary `Formula.diag` — try both) | budgets close at `O(log k)`, constants poly(n) | 2–3 days |
| **1b** | Spike B `Research/Spikes/sysLob/MiniSys.lean`: stripped `Prog` clone with `.sys`/`.selfIdx`/`ProgList`; a 2-bot mutual quine `#eval`s correctly | `sysClose`/eval equations stay structural | 1–2 days |
| **—** | **RE-DECIDE A vs B** with Spike A's arithmetic | — | — |

**Phase 1 RESULTS (2026-08-13, both spikes green, zero sorry, 3-axiom footprint):**

* **Spike A: PASS.** `vector2_full_pblt_engine` is a theorem on the LIVE engine —
  from the two full-dependency premises `□_k A → (□_k B → A)` and
  `□_k A → (□_k B → B)` (self-loops included), both sentences are provable past a
  threshold. Iterated-unary route, ZERO new constructors (Family-B completion's
  `implS`/`implK` carry the B-combinator glue). The stage lemma
  `loeb_premise_under_box` is the reusable atom: Löb under a boxed side-antecedent,
  side box pre-lowered so the K-distribution lands below the premise's self-box.
  Budget caveat (inside the gate, but worth eyes): threshold constants CASCADE —
  master `2⁵²·V ≤ k` vs the cycle engine's `2¹⁷·V`, growing `2^(O(n))` in
  elimination stages. Fine for the 3-instance milestone zoo; the n-ary
  `Formula.diag` is the poly(n) refinement if ever needed.
* **Spike B: PASS.** All `rfl` defeq tests hold; `sysClose` stays structural
  unannotated; nested-`.sys` shadowing is benign; the mutual list member causes no
  equation trouble. ONE binding constraint found for Phase 2: the guard-list
  evaluator must THREAD FUEL PER LIST ELEMENT — the naive same-fuel `evalL`
  silently compiles by well-founded recursion and `rfl` dies (the tsearch landmine,
  reproduced and dodged at toy scale). `.sys`'s eval must charge fuel per element,
  like `.tsearch`'s stepwise peel.
| **2** ✓ | Language landing: `Program.lean` mutual block + `sysClose` + size + subst arm; `Dynamics.lean` eval arm | all 81 base + 88 tau outcome statements byte-identical; 3 axioms; `#eval` demos unchanged; Metatheory pinning decided consciously | 3–5 days |

**Phase 2 RESULTS (2026-08-13, one session): GATE MET.** `ProgList` + `.sys`/`.selfIdx`
landed in the `Program.lean` mutual block; `subst` treats `.sys` as a barrier and
`.selfIdx` as a fixpoint; the `sysClose` family (Prog/GuardList/Formula, structural,
`.bot`-transparent, inner-`.sys` shadowing) + `ProgList.get?`/`psize`; honest `.size`
(a `.sys` reference carries the whole system); `hasSearch := true` for both (kept out
of the searchfree fragment by overapproximation). `Dynamics.lean`: lazy-unfold eval
arm (`sysClose` one level per fuel tick, same frame; out-of-range/dangling → `none`)
+ the `eval_sys_some/none`/`eval_selfIdx` unfolding lemmas (the `.tsearch`-quartet
pattern). Fallout was 6 files, ALL proof-internal match arms (subst-preimage
censuses in WaryBot/GuardianBot/DIMCID helpers + `hasSearch_subst`/`cert_searchfree`
+ `eval_mono`): **zero statement changes** (verified by diff), 3-axiom footprint
re-checked on a representative outcome theorem, Spike A recompiles against the
extended engine, and a scratch defeq suite (sysClose/get?/subst/size + a real
4-step eval chain through a 2-member system) passes on the live engine. Metatheory
debt extended to `.sys`/`.selfIdx` (lakefile note updated).
| **3** ✓ | `PlaysProof.sysStep` (twin of `botSearchStep`) + `sound_upto`/`wv_sound_upto` arms + `Pf_mono`/`Pf.induct` wiring + `h_sys` kill obligation in every Exclusion census | both targets green; no existing exclusion theorem weakened | 3–5 days |

**Phase 3 RESULTS (2026-08-13, same session): GATE MET.** `PlaysProof.sysStep`
landed — S reads the system (component `i`, one `sysClose` level, `c_node`, the
`.bot`-transparency twin); deliberately NO rule for `.selfIdx` (dangling evals
`none`; absence of a rule IS the honest reading). Both named eliminators gained the
arm (`Pf.induct` trivial-motive; `PlaysProof.induct` full); `Pf_mono` needed
NOTHING (plain `cases` on `Pf`; `atom_monotone` covers the atom layer). The master
lemma `wv_sound_upto` gained the `h_sys` census kill hypothesis (the `h_tsearch`
pattern verbatim) + the PASS-1 soundness arm (`eval_sys_some` — the machine gate,
compiling) + the PASS-2 census kill arm; all five instantiation sites discharged
`h_sys` trivially (no census contains a `.sys` shape). `Base/Exclusion.lean`
untouched entirely — the Pf-tier censuses quantify over `Pf` constructors, which
did not change. Build green (3305 jobs), zero statement changes, 3-axiom footprint;
sanity: `Pf 16 (.plays (.sys demo 0) opp .C)` derives via `sysStep ∘ bot ∘ sysStep`
through the `.bot`-frozen system reference — S genuinely reads mutual systems.
NOTE for Phase 5: the peel-to-implication machinery (deriving `□φ⃗ → φᵢ` from a
frozen σ-player's source) is NOT part of sysStep — it will need either new Pf
modal rules for `.bot (.sys …)`-wrapped `.tsearch` shapes (with their own
`sound_upto` arms, the constructor-integration playbook) or a meta-level
derivation via the Spike-A stage lemma; decide there, not here.
| **4** | Promote Spike A → `Base/Loeb.vector_pblt_engine` (size-parametric; n=2 engines untouched) | consumed hypotheses match Phase-5 needs | 2–3 days |
| **5** | `Tau/SysDefs.lean` (σ-zoo as ONE `ProgList` + `Positive` by `decide`) → constants' certificates → mutual premises by peel-chaining → `ps_probe_sysQuine` (vector engine + n-ary eval inversion) → `tauDupocσ_phase` (both legs) → `outcome_TauDupocσ_vs_TauDupocσ` → bistability audit | first Route-A theorem compiles; open cells documented, not fought | 1–2 weeks |
| **6** | Split-collapse theorem pair; Python mirror in `app/src/pd_runner/tau/` for `(t, α)` sweeps → EGT | — | 1 week (parallel with 5's audit) |

The Matrix-level proof shape survives byte-for-byte (`outcome_of_ex_plays` on the
phase theorem's `.1`/`.2`); everything new lives below the phase theorem.

---

## Part IV — Kill criteria (each ⇒ stop, take Route B, document here)

| Gate | Condition to kill Route A |
|---|---|
| Spike A | vector-Löb budgets don't close at `O(log k)` with poly(n) constants |
| Spike B | `sysClose`/eval equations can't be kept structural |
| Phase 2 | byte-identity of existing outcome statements unachievable without touching them |
| Phase 3 | a census repair requires WEAKENING an existing exclusion theorem |
| Phase 5 | the first mutual premise derivation exceeds the size bounds the engine hypotheses allow |

---

## Part V — Open decisions (deferred, with their decision point)

- ~~**n-ary `Formula.diag` vs iterated unary fixpoints**~~ **RESOLVED (Spike A,
  2026-08-13): iterated unary.** Zero new constructors, closes at `O(log k)`;
  constants cascade `2^(O(n))` — acceptable at zoo scale. The n-ary diag stays a
  documented poly(n) refinement, not scheduled.
- ~~**Engine size hypotheses**~~ **RESOLVED (Spike A): stay parametric.** The
  cascade's intermediate transcripts (`2²⁸·V`-order) do not fit `100·log₂ k + 1000`;
  `bloeb_engine`/`mutual_loeb` being budget-parametric absorbed this with no engine
  change. Phase 4's `vector_pblt_engine` must keep parametric budget hypotheses and
  NOT copy the `_id` wrappers' hardcoded bounds.
- **Index type** `Nat` (with `none` out-of-range) vs `Fin` in `.selfIdx`/`.sys` —
  Spike B used `Nat` + `Option` throughout with no friction; default to `Nat` at
  Phase 2 unless the subst arms say otherwise.
- **NEW (Spike B): fuel-per-element eval.** `.sys`'s list evaluation must thread
  fuel per element (naive same-fuel list recursion silently compiles well-founded
  and kills `rfl`). Binding constraint on the Phase-2 `Dynamics.lean` arm.
- **Metatheory pinning**: the Decidability target is already unpinned pending tau M2;
  decide at Phase 2 whether Def 5 lands before or after the M2 re-pin — modesty of
  `.sys` args (closed terms, plausibly modest) is unexamined.
