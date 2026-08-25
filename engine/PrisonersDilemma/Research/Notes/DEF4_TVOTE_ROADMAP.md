# Def-4 refined: the source lift + `tvote` action-vote — refactor roadmap

*Status: **ALL PHASES LANDED 2026-08-18** (plan fixed, executed, and closed the
same day — phases 1–4b, 5 (Spec DSL), 6 (Python coincidence certification),
7 (docs). Supersedes the σ-player layer of `TAUBOT_TRANSPARENCY_DESIGN.md`
Part III, whose retraction section this executed. The instance layer of
milestone 1 was reused unchanged, as predicted. **Next frontier: the `.sys`
revival** (mutual self-probers / full-zoo lift), landing on the Spec DSL — only
the compiler's probed-object resolution changes. **SCOPED 2026-08-20 in §8c**,
which finds the five "self-probers" are FOUR different blockers and that `.sys`
cleanly unblocks only ONE of them — read §8c.7 before starting.)*

---

## 0. The locked decisions (agreed 2026-08-18)

1. **Def 4 IS the uniform structural source lift τ** (the 2026-08-13 retraction's
   reading, confirmed):
   * **Step 1 — lift the code.** Base A's source, constructor by constructor;
     every reference to the severed `.opp` wire becomes a reference to the
     hypothesis's tau instance.
   * **Step 2 — point-mass instances.** `inst(A, δ_B)` = A's ENTIRE lifted
     decision procedure at point mass on B — the encapsulation of base A's real
     definition (for Dupoc: one `proofSearch` about `inst(B, δ_A)`; for
     multi-stage bots: ALL stages inside the encapsulation, only the final
     action leaves it).
   * **Step 3 — one vote, over actions.** At a blurred signal the tau player
     plays `C` iff `Σ { wᵢ : inst(A, δ_Bᵢ) plays C } ≥ θ`, where "plays" is the
     TRUE play, read by EVALUATION. `proofSearch` appears only where base A's
     own code has it — inside the instances, never at the vote.
2. **Vote primitive = a new `Prog.tvote` constructor** (weighted action-vote over
   frozen instance terms; linear size). NOT `iteTree` compilation (2ⁿ term
   blow-up kills the full-zoo goal) and NOT `.tsearch` (provability-vote — the
   wrong modality for step 3: it misreads true-but-unprovable else-branch plays).
3. **`.tsearch` (and `GuardList`) are REMOVED — Phase 4b** (decision revised
   2026-08-18, same day). `tvote` SUBSUMES it extensionally:
   `tsearch k [(wᵢ,φᵢ)] θ p q ≡ tvote [(wᵢ, .search k φᵢ C D)] θ p q` — each
   entry plays C iff its guard is provable, so even a native provability-vote
   strategy is a `tvote` vector at linear size. Keeping the constructor taxes
   EVERY future structural induction over `Prog` (subst/size/eval/soundness/
   eliminator/census arms + the entire gated Metatheory mirror — removing it
   visibly shrinks the M2 debt). Honest caveat, recorded: `tsearch` guards
   subst at consultation (may mention `.self`/`.opp`); `tvote` entries are
   frozen — frame-dependent weighted guards are lost. Nothing ever used them
   (every zoo probe is `.bot`-frozen closed); git archives the constructor.
   Removal happens AFTER the tau rebuild (Phase 4b), never mid-way — every
   gate stays green.
4. **Zoo restricted for now** (≤ 1 self-prober — the current 6 templates).
   The mutual self-probe wall (`inst(A,δ_B)` ⊃ `inst(B,δ_A)` ⊃ `inst(A,δ_B)`
   is impossible by containment; `.self` cuts only the diagonal quine) is
   deferred: **`.sys` revival (tag `taubot-def5-research`) is the designated
   full-zoo route**, attacked only after this refactor is green.
5. **Instances stay hand-written** for this zoo. τ-as-a-Lean-function
   (spec DSL + compiler + once-proven anchor) is deferred to the
   lift-all-base-bots milestone. Rationale: signal-native bots (e.g. "cooperate
   iff the Coop-hypothesis weight exceeds ½") are FIRST-CLASS and never come
   from τ anyway — in this architecture **every tau player = a decision vector
   over hypotheses + the shared vote**; τ is merely one *producer* of vectors
   (lifted family), hand-writing is the other (native family). The vote layer
   and its phase theorem are shared by both.
   **[UPDATED 2026-08-18, post-Phase-4 review: the DSL is now SCHEDULED as
   Phase 5 (§6) — immediately after Phase 4b, BEFORE the Python phase and
   BEFORE the `.sys`/Def-5 revival (reordered same day: certify the layer that
   persists, not the prototype). The Phase-4 layer is correct but is a fixed-6
   prototype: hand-written vectors and instances scale quadratically
   (N=100 ⇒ ~10,000 hand terms + ~10,000 proof steps).]**
6. **Faithfulness guard while hand-written**: the kernel-vs-Python coincidence
   check (the mechanism that caught every bug so far). Expected outcome after
   the refactor: **Def 4 ≡ Def 3 at large k on every terminating cell** — the
   comparison's job flips from hunting separation to CERTIFYING coincidence,
   plus charting the honest budget-structure divergences (Löb thresholds,
   floors, sub-Löb regimes) that Def 3 cannot see.

**Non-goals of this refactor:** `.sys` / mutual quines; lifting more base bots;
`Metatheory` restoration (M2 debt grows by `tvote`, see §6); Def 5 anything.

---

## 1. Target architecture (after the refactor)

```
Program.lean    .tvote : VoteList → Nat(θ) → Prog → Prog → Prog     [NEW]
                VoteList = weighted list of FROZEN closed Progs      [NEW, mutual block]
                .tsearch + GuardList                                 [REMOVED, Phase 4b]
Tau/Defs.lean   instance layer (UNCHANGED: probe, probeSearchδ, tftSimδ, eδ, quine)
                + ~5 new thin instance wrappers (the A-side closure, §4)
                + ONE uniform player:  tauPlayer (v : VoteList) (θ : Nat) : Prog
                + one decision VECTOR per template (its list of own-instances)
Tau/PeelLemmas  eval_tvote_of_plays (the action-mass peel, once for all vectors)
Tau/Phases      ONE generic phase theorem + per-template corollaries from bit lemmas
Theorems/Tau/   Matrix regenerated; TauEBot's crowd-exploiter cells DELETED,
                replaced by the true τ(EBot) one-sided-boundary cells
```

Key structural facts the design exploits:

* **Entries are closed and `.opp`-free** ⇒ a tau player is extensionally
  constant (play = function of its signal only) ⇒ the matrix still factors
  through play theorems, as today.
* **The vote layer is ATOM-layer only.** Reading an entry's play is a positive
  fact about a deterministic closed program — certified by that program's own
  transcript, in BOTH directions ("plays C" and "plays D" are both plays-atoms).
  No refutations, no `search_f`, **no floors at the vote level**. Floors live
  exactly where base bots put them: inside instances, at their `proofSearch`
  sites. (Contrast `.tsearch`, whose `Cons_f` needed the Σ₁-refutation floor.)
* **Coincidence for single-guard bots becomes structural**: Dupoc's vote entry
  is `.search k (probe (B(δ_L))) C D` — literally the old tsearch guard wrapped
  in Dupoc's own decision — so entry-plays-C ⟺ old guard bit, and the old
  boundary theorems transfer.

---

## 2. Phase 1 — language: `VoteList` + `.tvote` (`Program.lean`)

* `VoteList : nil | cons (w : Nat) (I : Prog) (rest : VoteList)` — INSIDE the
  mutual block (the GuardList precedent: a nested `List (Nat × Prog)` payload
  would wreck the recursors). `deriving DecidableEq`.
* `Prog.tvote : VoteList → Nat → Prog → Prog → Prog` — `tvote v θ p q`.
  **NO budget argument**: the vote consults no oracle. Budgets live inside
  entries.
* **`subst` does NOT descend into `VoteList`** — entries are frozen (the
  `.bot` / `.eq`-RHS / `.diag` convention). The tvote subst arm rewrites only
  the branches: `.tvote v θ p q ↦ .tvote v θ (p.subst m o) (q.subst m o)`.
  No `vsubst` exists. This is what keeps players `.opp`-free by construction.
* `size`: `numCost θ + v.vsize + p.size + q.size + 1` with
  `vsize (cons w I rest) = numCost w + I.size + rest.vsize + 1`.
* `hasSearch (.tvote …) = true` **UNCONDITIONALLY** (the tsearch precedent).
  NOT a fold over entries: letting a search-free-entry vote into the
  search-free fragment would add a `tvote` induction case to
  `atom_complete_searchfree` (search-free plays must be structurally
  certifiable) for zero benefit — tau players are never census subjects and
  need no atom-completeness. Conservative over-approximation; refine only if
  a search-free vote ever needs atom certs.
* Helpers: `VoteList.totalMass`, `VoteList.massWhere (f : Prog → Bool)`
  (the action-valuation mass — instantiated with "eval says C" downstream).

**Trap list (from the tsearch landing — re-hit NONE of these):**
`termination_by structural` on every enlarged mutual def (the equation compiler
silently falls back to WF recursion and kills defeq — check with scratch
`example : … := rfl` after ANY mutual-block change); nested patterns as separate
top-level arms, never an inner `match` (breaks equation lemmas); `cases` not
`induction` on the mutual `VoteList`; explicit binders where eliminator lambdas
must match positionally.

**Gate 1**: engine builds green; the defeq `rfl` scratch checks pass; all 81
base outcome statements byte-identical (nothing touches them).

**✅ PHASES 1 + 2 LANDED 2026-08-18.** Engine green (3305 jobs), 3 standard axioms,
zero sorry, **114/114 outcome declarations byte-identical**, 22 defeq scratch checks
pass, three-regime peel demo proven. Two findings worth keeping:

1. **A `do`-bind in the eval arm blocks equation-lemma generation.** The arm must
   match the entry's result EXPLICITLY (`match eval n I I I with | some .C => … |
   some .D => … | none => none`), NOT `let r ← eval n I I I`. With `do`, `rw [eval]`
   fails ("failed to generate equality theorems for match expression") and no amount
   of budget-raising helps — this is also why the `.ite` arm has no unfolding lemmas.
   With the explicit match, all four `eval_tvote_*` lemmas close by a single `rw`.
   (A NEW trap, distinct from the known "inner `match gs` breaks equation
   generation": here the LIST is matched by nested patterns as prescribed, and it is
   the entry RESULT that must not be `do`-bound.)
2. **Blind `simp [eval]` proofs degrade with every new constructor.** `.tvote` pushed
   MirrorBot/Helpers' three "mirror copies its opponent" steps past `whnf` timeouts
   (they had already needed a heartbeat bump for `.tsearch` in 2026-08-11). Raising
   budgets only moved the failure; they were REWRITTEN as targeted steps
   (`MirrorBot = .sim .opp .self` ⇒ `rw [MirrorBot, eval]; simp only [Prog.subst]`),
   which is constructor-count independent and cut that file 139s → 9s. Two EBot files
   (`vs_DBot`, `vs_OBot`) took a file-level `maxHeartbeats 1000000` instead — their
   `simpa [eval] using hPlay` steps are shallow but wide. **Prefer targeted rewrites
   over budget bumps**; the budget route just defers the next break.

Touch-list actually hit (matches §4's prediction): `Program.lean` (constructor,
`VoteList`, subst/size/vsize/hasSearch/mass helpers, DecidableEq), `Dynamics.lean`
(2 eval arms + 4 unfolding lemmas incl. `eval_tvote_cons_none`),
`Base/AtomCerts.lean` (2 search-free discharges — trivial, exactly as the
unconditional `hasSearch` intended), `Base/ValuationSoundness.lean` (`eval_mono` —
the one case needing real work: an entry is evaluated at the SAME fuel, so the IH
must lift the entry's play before the peel step transfers), and 13 mechanical
`| tvote` census arms across 4 theorem files.

## 3. Phase 2 — dynamics (`Dynamics.lean`)

Stepwise peel, mirroring `.tsearch` but with an EVALUATED guard:

```
| .tvote .nil θ p q            => if θ = 0 then eval n me opp p else eval n me opp q
| .tvote (.cons w I rest) θ p q =>
    if θ = 0 then eval n me opp p
    else do let r ← eval n I I I          -- the entry plays ITSELF: closed, .opp-free
            if r == .C then eval n me opp (.tvote rest (θ-w) p q)
            else           eval n me opp (.tvote rest θ p q)
```

* Entry frame is `eval n I I I` — the closed-instance convention (matches the
  probe atom `plays (.bot I) (.bot I)`; the `.sim` arm is the precedent for
  running an inner program inside the fuel monad).
* A non-terminating entry ⇒ the player is `none` at every fuel — a tau player
  is total iff its entries are. Fine on this zoo (all instances terminate);
  record as the vote-level analogue of `NonTerminationPolicy` for later zoos.
* Four unfolding lemmas `eval_tvote_zero/nil/cons_c/cons_notc` (the GuardList
  lesson: the inner match won't reduce on a variable list — every consumer
  rewrites with these, never `rw [eval]` directly). Fuel-monotonicity arm.

**Gate 2**: `#eval` demos — a hand-built vote plays correctly at point mass and
at a mixed signal, both θ-regimes.

## 4. Phase 3 — proof system (`ProofSystem.lean`, `Base/`)

Five `PlaysProof` rules mirroring the peel — all ATOM-tier, modelled on `sim`
(inner premise = the entry's own transcript in its own frame, cost cumulative):

```
voteZero_t : PlaysProof me opp p a n → …(.tvote v 0 p q) a (n + c_node)
voteNil_f  : θ ≠ 0 → PlaysProof me opp q a n → …(.tvote .nil θ p q) a (n + c_node)
voteCons_c : θ ≠ 0 → PlaysProof I I I .C m →
             PlaysProof me opp (.tvote rest (θ-w) p q) a n →
             …(.tvote (.cons w I rest) θ p q) a (n + m + c_node)
voteCons_d : θ ≠ 0 → PlaysProof I I I .D m →      -- a POSITIVE transcript, no refutation, NO floor
             PlaysProof me opp (.tvote rest θ p q) a n →
             …(.tvote (.cons w I rest) θ p q) a (n + m + c_node)
voteHigh_f : θ > v.totalMass → PlaysProof me opp q a n →
             …(.tvote v θ p q) a (n + v.vsize + c_node)   -- static-arithmetic else shortcut
```

* `voteCons_d` is the payoff of the action-vote: "entry does not add mass" is
  the entry's honest D-transcript — determinism of eval is what replaces
  tsearch's `search_f` refutation + floor. (Soundness arm: the D-transcript's
  soundness + eval determinism force the `cons_notc` eval path.)
* Wire into: `Pf.induct` / `PlaysProof.induct` named eliminators (new arms);
  `wv_sound_upto` (five arms, using the `eval_tvote_*` lemmas);
  `Base/Exclusion` censuses gain the `h_tvote` kill obligation (no census
  subject is a tvote node — trivially discharged, the `h_tsearch` precedent).
* Exact premise shapes to be confirmed against the `sim` arm of `wv_sound_upto`
  during implementation — do not invent a second convention.

**Why five rules are COMPLETE for the peel**: every terminating eval path is
mirrored — θ=0 (`voteZero_t`), exhaustion (`voteNil_f`), and the cons step where
`Action` being BINARY makes `voteCons_c`/`voteCons_d` exhaustive over entry
outcomes. A `none` path (non-terminating entry) needs NO rule by design:
`PlaysProof` certifies actual plays, and where eval never commits no transcript
should exist (the `.sim`-of-nonterminating precedent). `voteHigh_f` is a cost
shortcut, not a completeness requirement.

**Full new-constructor touch-list** (coverage is wider than the five rules):
`subst`/`size`/`DecidableEq` (P1); `hasSearch` unconditional-true (P1, see the
AtomCerts rationale there); eval arms + unfolding lemmas + FUEL-MONOTONICITY
(P2); the 5 rules + `Pf.induct`/`PlaysProof.induct` arms + 5 `wv_sound_upto`
arms (P3); per-census kill arms in `Base/Exclusion` — 5 impossible-case
discharges each, the `h_tsearch` precedent (P3); `LegacyS.lean`/`legacy_iff_live`
recompiles (verify, don't assume — it survived the tsearch landing). **NO modal
`Pf` reading rules**: nothing probes a tau player (only instances are probed,
and instances contain no `tvote`). Future trigger, recorded: mixed base-vs-tau
matches where a base prover reads a tau player's source would need a
`voteBranch`-style rule — out of scope.

**Gate 3**: 3-axiom footprint unchanged; zero sorry; all 81 base outcome
statements byte-identical; `sound_upto` green.

**✅ PHASE 3 LANDED 2026-08-18.** Engine green (3305 jobs), 3 standard axioms, zero
sorry, 114/114 outcome declarations byte-identical, `wv_sound_upto` proven with all
five arms, worked transcripts + soundness demo typecheck.

**THE DESIGN PILLAR HOLDS — with one correction the plan did not anticipate.**
`voteCons_d` needs no refutation and no floor: it cites the entry's own honest
D-transcript, and eval determinism does the rest. Confirmed by construction (a
`voteCons_c ∘ voteCons_d ∘ voteNil_f` certificate builds with no `Pf` premise
anywhere) and by soundness going through. The correction:

**`voteHigh_f` AS SPECIFIED IN §4 WAS UNSOUND.** The spec let the threshold
shortcut commit to the else-branch citing only `θ > totalMass`. But a `.tvote`
entry is an arbitrary program that may not TERMINATE, and `eval` sinks the whole
vote to `none` when one doesn't — whereas `.tsearch`'s guard bit comes from the
total function `proofSearch`, so its `tsearchHigh_f` twin is fine. Machine-checked
counterexample: `tvote [(1, MirrorBot)] 5 C D` has `θ = 5 > totalMass = 1` and
evaluates to `none` at every fuel, yet the rule would have licensed a
`D`-transcript for a program that never plays. Caught by the soundness arm
refusing to close — i.e. exactly the gate §9 relies on.

*The repair* (two parts, both forced):
1. A new `VoteAllPlay v c` predicate in the mutual block — "every entry plays
   SOMETHING, at total transcript cost `c`" — added as a premise of `voteHigh_f`.
   WHICH action each entry plays stays irrelevant; that irrelevance is the rule's
   whole content. The shortcut may skip READING the entries, never their
   TERMINATION.
2. The evidence is CHARGED (`n + c + v.vsize + c_node`). Not cosmetic: with the
   premise uncharged, the budget-strong-induction in `wv_sound_upto` cannot reach
   the entries' own certificates (`m ≤ B` is unavailable) and the arm is unprovable.
   Cumulative costs then give both bounds from `m + c ≤ B`.

Consequences worth noting: `VoteAllPlay` is a FOURTH inductive in the mutual block,
so every `motive_N` in both named eliminators and both `wv_sound_upto` passes
shifted by one; `wv_sound_upto` gained an `h_tvote` kill obligation (twin of
`h_tsearch`), discharged trivially at all four instantiation sites (`sound_upto`,
both WaryBot censuses, DIMCID-vs-CupodTrollBot, GuardianBot-vs-DIMCID) since no
census subject is ever a tau player. A semantic `VoteAllRun` (the "every entry
actually runs" counterpart) is the `motive_2` the certificate pass carries, and it
must be BUDGET-GATED like `motive_1`.

**Proof-craft trap (cost me several iterations):** the raw recursor's argument
order for a rule with two recursive premises is *all premises first, then all
motives* (`hθ hI hp ihI ihp`) — NOT premise/motive interleaved. And when a
positional application still mismatches, `exact f _ _ _ … hyp₁ hyp₂` with
underscores beats hand-counting binders; the roadmap's "auto-bound implicit order
is unpredictable" warning applies to eliminator ARGUMENT order too.

## 5. Phase 4 — the tau layer rebuild (`Tau/`, `Theorems/Tau/`)

**Keep verbatim**: the probe atom, `probeSearchδ`, `tftSimδ`, `eδ`, the quine
`TauDupocδ`, the whole δ-closure, every Certs bit lemma (incl. the Gödelian pair
and `ps_probe_quine`), the floor lemma in Exclusion.

**Add the A-side instance closure** (thin wrappers over probed objects that
already have bit lemmas — reuse names where terms coincide):

| template | vote entry at hypothesis T | status |
|---|---|---|
| Dupoc | `probeSearchδ k (T(δ_L))` | δ_C/δ_D exist (`searchOfCoopδ`/`searchOfDefectδ`); δ_L = quine ✓; δ_Ts/δ_Tp/δ_E = NEW wrappers over `simOfSearchδ`/`searchOfSearchδ`/`eOfSearchδ` |
| TFTPf | `probeSearchδ k (T(δ_C))` | wrappers over the δ_C column ✓ |
| TFTSim | `tftSimδ (T(δ_C))` | `simOf*δ` exist; `Ts(δ_Tp) = Ts(δ_L)` (shared term, since `Tp(δ_C) = L(δ_C)`) |
| EBot | `eδ k (T(δ_D)) (T(δ_C))` | `eOfCoopδ/eOfDefectδ/eOfSearchδ` ✓; NEW: `eOfTsδ = eδ k simOfDefectδ simOfCoopδ`, and `inst(E,δ_E) = eδ k (eOfDefectδ k) (eOfCoopδ k)` — E's self-hypothesis GROUNDS (cascade probes the closed δ_D/δ_C columns; no quine, no 2-cycle) |
| Coop/Defect | `.const C` / `.const D` | signal-blind ✓ |

**Replace the σ-players** with the uniform definition + per-template vectors:

```
def tauPlayer (v : VoteList) (θ : Nat) : Prog := .tvote v θ (.const .C) (.const .D)
def dupocVec (k wC wD wTs wTp wL wE : Nat) : VoteList := …6 entries…   -- etc.
```

DELETE: `TauEBot` (nested tsearch, the crowd-exploiter), `dupocSig`/`tftPfSig`/
`exploitSig`/`tftSimSig`, `iteTree` + `TauTFTSim`'s tree compilation (git + the
design-note record are the archive). `.tsearch` itself stays (decision 3).

**Lemma economy** (the point of the whole exercise):

1. Per-template ONE parametric entry-play lemma (`probeSearchδ_plays`,
   `tftSimδ_plays`, `eδ_plays`) turning Certs guard bits into entry actions —
   trivial eval unfoldings.
2. `PeelLemmas.eval_tvote_of_plays`: player plays C iff
   `massWhere (entry plays C) ≥ θ` — proven ONCE (the `eval_iteTree_of_vals`
   proof is the template; it dies with iteTree and is reborn generic).
3. `Phases`: ONE generic `tauPlayer_phase` + six corollaries. Expected
   boundaries: Coop/Defect constant; **Dupoc/TFTPf/TFTSim unchanged at
   `θ ≤ wC+wTs+wTp+wL`** (Dupoc's E-entry plays D via the floor INSIDE the
   entry — the boundary survives the modality move, which is itself a good
   regression check); **τ(EBot) = ONE-SIDED boundary `θ ≤ wTs+wTp+wL`** (bits:
   Coop 0, Defect 0, Ts 1, Tp 1, L 1, self 0) — no window, defection only at
   high θ. E's self-bit 0 is the truncated-lift convention (Mirror branch not
   liftable), already recorded as the open honest divergence from Def 3.
4. **The point-mass coherence lemma** (the Def-4 anchor at the vote level,
   NEW and load-bearing): `tauPlayer [(w, I)] θ` with `0 < θ ≤ w` plays exactly
   what `I` plays — the σ-player at point mass IS its instance. This is the
   theorem the crowd-exploiter would have failed; it becomes the standing
   coherence gate for every future vector (lifted or native).
5. `Matrix.lean`: regenerate — cooperator cells carry over with new proofs;
   the 33 crowd-exploiter cells are deleted and replaced by τ(EBot)'s
   two-regime cells (~its row/column against the zoo + self-play, low/high).

**✅ PHASE 4 LANDED 2026-08-18.** Engine green (3306 jobs), 3 standard axioms, zero
sorry, base outcome declarations byte-identical, point-mass coherence lemma proven.

**Results.**
* `Tau/Vote.lean` — `tauPlayer v θ` (ONE player for every bot), the peel workhorse,
  the **point-mass coherence lemma** `tauPlayer_point_mass`, the generic phase theorem,
  and the probe↔entry bridge.
* `Tau/Vectors.lean` — the six decision vectors + entry-play lemmas. τ(EBot) needed
  three new instances (`eOfSimδ`, `eOfPfδ`, `eOfSelfδ`); all GROUND (the cascade probes
  only closed δ_D/δ_C columns), so no quine and no stipulation.
* `Tau/VotePhases.lean` — six α-phase theorems. **τ(EBot)'s boundary is
  `θ ≤ wTs + wTp + wL` — ONE-SIDED, no window**, exactly as the retraction predicted.
  The three cooperators keep `θ ≤ wC + wTs + wTp + wL`, TauDupoc's mass still honestly
  excluding `wE` (the floor cell) — the regression check that the modality move left
  the Gödelian content where it belongs, inside the entry.
* `Theorems/Tau/VoteMatrix.lean` — the matrix, including the **separating band**
  `wTs+wTp+wL < θ ≤ wC+wTs+wTp+wL` (nonempty iff `wC > 0`) where cooperators still
  cooperate and τ(EBot) has already flipped: `outcome_TauTFTPf_vs_TauEBot_band = (C,D)`.
* DELETED: `Tau/Phases.lean`, `Tau/PeelLemmas.lean`, `Theorems/Tau/Matrix.lean` (79
  theorems, 33 about the crowd-exploiter), and the σ-player layer of `Tau/Defs.lean`
  (guard lists, `iteTree`, the six `.tsearch` players). The instance layer and every
  `Certs` bit lemma survive UNCHANGED — as the retraction said they would.

**The frame decision that made the reuse work.** A `.tvote` entry runs `.bot`-framed
(`eval n (.bot I) (.bot I) I`), which is LITERALLY the probe atom's frame. So every
existing `probe`/`Pf`/`interp` bit lemma applies to entries one `.bot` unfolding apart
(`entry_C_of_interp`, `entry_D_of_not_interp`, `entry_C_of_pf`). The first draft used
the bare frame `eval n I I I` and none of the `Certs` layer applied — a half-hour of
rework avoided permanently by matching the probe convention.

**Proof-craft trap: valuation FUNCTIONS force term equality; use positional bits.**
`VoteAllVals (val : Prog → Action)` requires proving `val Iᵢ = aᵢ` for six large
cascade terms, which drags in either `decide` on terms containing the free budget `k`
(the kernel cannot evaluate it) or a simp-normalization race. Replaced by `VoteBits v
bs` — the entries' actions supplied POSITIONALLY as a `List (Nat × Action)`, with
`massOf` computing the C-mass. No term comparison anywhere; every per-bot proof is a
`.cons` chain of entry-play lemmas. `VoteAllVals` is kept (it reads better when a
valuation is natural) but `VoteBits` is the interface the phase theorems use.

**Gate 4** (original text): zero sorry; point-mass coherence lemma proven; τ(EBot) self-play =
`(D, D)` at θ ≤ wTs+wTp+wL? — NO: check carefully — self-bit 0 means E's own
mass excludes wE, so vs itself both sides play by their own (θ, w⃗); write the
cells the theorems actually give, do not pattern-match the old table.

## 5b. Phase 4b — REMOVE `.tsearch` + `GuardList`

Only after Gate 4 (no user left). One commit, full checklist:

* `Program.lean`: the constructor, `GuardList`, `gsubst`, `gsize`, the
  `hasSearch` arm, `totalMass`/`massWhere` (their `VoteList` analogues live on),
  the `DecidableEq` derive list.
* `Dynamics.lean`: two eval arms, `eval_tsearch_zero/nil/cons_t/cons_f`,
  fuel-monotonicity arms.
* `ProofSystem.lean`: the 5 `tsearch*` rules, their `Pf.induct`/
  `PlaysProof.induct` arms, the §4 raw-recursor uses.
* `Base/ValuationSoundness.lean`: 5 `wv_sound_upto` arms.
* `Base/Exclusion.lean`: every `h_tsearch` kill obligation.
* Verify `Research/Spikes/unified_pf/LegacyS.lean` + `legacy_iff_live` still
  compile (removal only shrinks the live system — but check).

**Gate 4b**: engine green; 3 axioms; the 81 base outcome statements
byte-identical; `grep -r tsearch engine/PrisonersDilemma --include='*.lean'`
returns only historical comments (or nothing).

**✅ PHASE 4b LANDED 2026-08-18.** Engine green (3306 jobs), 3 standard axioms, zero
sorry, 78/78 base outcome declarations byte-identical, and the only surviving
`tsearch`/`GuardList` mentions are prose in doc-comments (the stale ones were
rewritten to name `tvote`/`VoteList`).

Removed: the constructor and `GuardList` + `gsubst`/`gsize`/`totalMass`/`massWhere`
(`Program.lean`), 2 eval arms + 4 unfolding lemmas (`Dynamics.lean`), 5 `PlaysProof`
rules + both eliminators' arms (`ProofSystem.lean`), `eval_tsearch_high` + the
`eval_mono` case + 5 soundness arms + 5 census arms + the `h_tsearch` obligation
(`ValuationSoundness.lean`), 2 search-free discharges (`AtomCerts.lean`), and the
13 `| tsearch` census arms across the 4 theorem files. `sound_upto` and the three
census instantiations each shed one argument.

**Finding: `Research/Spikes/unified_pf/LegacyS.lean` does NOT compile — but it was
already broken before this phase.** The roadmap said to verify rather than assume, and
that was worth doing: it has 30 errors, IDENTICAL in count before and after the
removal (checked by stashing). It is a research spike outside BOTH lake targets
(`lakefile.toml` declares only `PrisonersDilemma` and `Metatheory`), untouched since
the Pf-only migration (98bf9eb), and it broke when `.tsearch` LANDED — the frozen
pre-merge `S` it defines never gained the constructor's arms. Removing `tsearch`
neither fixed nor worsened it. Repairing `legacy_iff_live` against the current
(now `tvote`-bearing) system is separate work, unrelated to this roadmap; flagged here
so the next reader does not mistake it for Phase-4b fallout.

## 6. Phase 5 — the Spec DSL (scale milestone; REORDERED 2026-08-18 to run BEFORE the Python phase, and BEFORE `.sys`/Def-5)

*Spec fixed 2026-08-18 (Colomban + review of the Phase-4 layer). The two findings
that force it: (a) the instance layer's def-chains (`simOfSearchδ = tftSimδ
(searchOfCoopδ k)` …) are PURE NAMING — every instance is `rfl`-equal to a plain
base-bot-style `Prog` tree, so that unease is cosmetic (bad names, fixable); but
(b) the fixed-arity vectors are a REAL wall: `dupocVec` hardcodes six `.cons` and
six weight parameters, and the whole layer is O(N²) hand-written terms + proofs —
36 at N=6, ~10,000 + 10,000 at N=100. The DSL replaces hand-writing with one
compiler and one induction; per-pair MATHEMATICS stays hand-written (it must).*

**Ordering rationale.** (a) *Why before the Python phase (reordered 2026-08-18,
Colomban):* the coincidence certification should run ONCE, against the layer that
will persist — the DSL changes the public interface (weights become `ι → Nat`, the
fixed-6 vectors and shape-named instances retire), so certifying the Phase-4
prototype first would mean writing the Python `def4` model against an interface
scheduled for deletion and then redoing both sides. (b) *Why before `.sys`:* the
specs are route-independent. When
the `.sys` binder (or a tower) later replaces how mutually-recursive instances are
EXPRESSED, only the compiler's probed-object resolution changes — the specs, the
vectors, the mass lemma and every phase-theorem statement survive. Landing `.sys`
on top of six hand terms would mean redoing this layer twice.

### 6.1 The types

```lean
inductive Mode | prove | run              -- proofSearch the probe  vs  .sim-run it
inductive Target (ι : Type) | self | name (i : ι)
structure Stage (ι) where
  mode   : Mode
  target : Target ι     -- the counterfactual opponent the hypothesis is imagined facing
  fire   : Action        -- played when the stage fires (probe/run yields C)
structure Spec (ι) where
  stages : List (Stage ι)
  dflt   : Action        -- played when the cascade falls through
structure Zoo (ι) [DecidableEq ι] where
  spec : ι → Spec ι
  -- + the termination discipline of §6.3 (rank + ≤1 self-prober)
```

The six current templates as specs (the worked table — this IS the zoo definition
afterwards):

| bot | stages | dflt |
|---|---|---|
| Coop   | `[]` | C |
| Defect | `[]` | D |
| Dupoc  | `[⟨prove, self, C⟩]` | D |
| TFTPf  | `[⟨prove, name Coop, C⟩]` | D |
| TFTSim | `[⟨run,   name Coop, C⟩]` | D |
| EBot   | `[⟨prove, name Defect, D⟩, ⟨prove, name Coop, C⟩]` | D |

Out of scope BY DESIGN (recorded, not hidden): non-cascade shapes — MirrorBot's raw
copy, base EBot's Mirror branch, `.neg`-guard bots (WaryBot). A `test : Action`
field on `Stage` is the recorded extension for negative probes; do not add it until
a lifted bot needs it.

> **`Tau/Theorems/Matrix.lean` REMOVED 2026-08-24.** The tau matrix was never
> stored per pair: tau players are `.opp`-free, so a match is two INDEPENDENT
> plays and every cell is `outcome_of_ex_plays` of two per-bot PHASE theorems.
> `Matrix.lean` only spelled out 29 headline cells on top of that, and the
> Python certification reads the `Phase.lean` bit tables, never `Matrix.lean`.
> The phase layer is now the ONLY layer: every `outcome_Tau*` name cited below
> is historical, and the mirror gates those cells carried are discharged INSIDE
> the phase theorems (`tauDupoc_phase`, `tauJust_phase`, `tauCIMCIC_phase`,
> `tauCupod_phase` — the last keeps only the dimcid `TailToA` gate).
>
> **2026-08-25 — EVERY phase is stated and unconditional.** τ(DIMCID)'s row
> landed; the certification now runs on the full 15×15 = 225 cells, 219 agree,
> the same 6 whitelisted, no missing rows. The two cells that blocked it —
> DIMCID vs guardian and vs cupodTroll — needed a NEW KERNEL,
> `Base/TowerCensus.lean` (the tower census): a target CHAIN (`T → Y → T₃`, each
> the guard-box of the previous one's reading rule, ending at a player nothing
> reads) and, per level, a TOWER of classes indexed by box depth, whose
> antecedents must avoid every lower index of the level and every deeper level.
> That single rule makes every premise-free axiom self-annihilate and lets a
> `mp`/`implTrans` with a box in the middle be discharged by the DEEPER level's
> already-proven theorem — never an induction hypothesis, which is where both
> earlier attempts (the note's `TailToA`, the valuation transplant) failed.
> `tower_census` is 31 arms on the 3 standard axioms; the DIMCID instantiation is
> three levels for guardian, two for cupodTroll (its second target is the
> index-decided `.eq`, an atom no rule reads). The four "reachable" cells landed
> the same day (tftSim/ebot/dbot by the budget-free unreadable census, obot by
> the floor census with a transcript-cost bound through its watch of
> `inst .dimcid .coop`).
>
> **2026-08-24 evening — the phase layer, made unconditional as far as it goes.**
> `tauCupod_phase` lost its last gate: the aligned-on-D dimcid×cupod pair is
> closed by mutual bounded Löb in BOTH orientations (`TauDIMCID/Helpers`,
> `dimCupSys`/`cupDimSys`). τ(Mirror) has a PHASE THEOREM at last
> (`TauMirror/Phase.lean`): `C` below the prefix mass of its 14 other slots,
> and honestly `none` — not `D` — above it, because the vote commits before
> consulting the divergent diagonal (`Vote.lean`: `eval_tvote_prefix_C`,
> `eval_tvote_prefix_none`, `tauPlayer_phase_prefix`). Its scanner row is the
> 14-slot prefix over `tauOrderInit`, diagonal recorded as `N`; the base
> `none` cell compares as `N` too, so the certification now runs on 210 cells
> (204 agree, same 6 whitelisted). The two remaining mirror closures
> (mirror×cimcic at the mirror's head, mirror×dimcid both ways) landed with it.
>
> **What is still NOT unconditional: τ(DIMCID)'s own row**, and only because of
> two cells — its play against `guardian` and `cupodTroll`, the then-`D`
> searcher partners. Both census techniques in the library fail on them for
> the SAME reason, now understood precisely: (i) the tail census's class
> contains `□(partner's guard) → T`, a genuine theorem (`botSearchStep`), so
> "no proof tails at T" is false as stated; (ii) the valuation census (base
> `GuardianBot × DIMCID` uses it with `gdS = {(DIMCID, Guardian)}`) needs the
> forced antecedent pair in `S`, which in the tau frame is `(bot I, bot P)` —
> a `.bot` OPPONENT, and `h_nb` is not incidental: with such a pair forced,
> `iteBranchSearch_t` derives a real theorem whose truth depends on the forced
> atom, so the valuation is unsound exactly in the world the census is meant
> to exclude. A correct argument must be syntactic and track PROVABILITY of
> box antecedents along the tail (the reading rule's box is unprovable by
> soundness; every mp/implTrans with a box in the middle must be discharged
> from that); that is a new kernel over the 31-arm induction, not a
> hypothesis tweak. Everything else in DIMCID's row is proven or reachable
> (tftSim/ebot/dbot: budget-free unreadable census; obot: floor census with a
> transcript-cost bound; the four other cells and the diagonal are theorems).
>
> **RESOLVED 2026-08-24 — the DSL is a TREE now.** MirrorBot's raw copy was the
> shape that broke the stage list: a forwarder has no `test`/`fire`/fall-through,
> and encoding it as a one-stage threshold test (`if the watch plays C then C else
> D`) changed its SHAPE from forwarder to classifier — behaviourally identical on
> `{C, D}`, but `S` reads shape, and the encoding blocked the mirror×cupod cells
> (a Löb fixpoint on the ELSE branch). `Spec` is now `const | sim | ite | search`
> — `Prog` with a `Target` hole where the base says "`.opp` facing Q", i.e. the
> uniform source lift taken literally — and every bot is written as its base
> source: τ(Mirror) = `sim self`, τ(TFTSim) = `ite (sim (name coop)) C (const C)
> (const D)`, and so on. `run` is no longer a mode (it is `ite ∘ sim`); `prove`
> stages are `search` nodes. Every classifier's compiled term is BYTE-IDENTICAL to
> the stage list's (Gate D1 + every phase theorem's pinned shape, by `rfl`, zero
> theorem edits); only τ(Mirror)'s term changed, from `.ite (.sim P P) C (.const
> C) (.const D)` to `.sim P P`. Base EBot's Mirror branch is in scope with it.
> `.neg`/`.box` guards (WaryBot, LegibleBot) remain the recorded extension — now a
> `Mode` (guard-descriptor) extension on `search`, not a new node.

### 6.2 The compiler

```lean
inst (Z : Zoo ι) : ι → ι → Prog       -- inst A T = A's entire decision at point mass on T
```

Cascade compilation, stage by stage (right-nested, exactly the shapes Phase 4
hand-wrote):

* `prove` stage, probed object `P`:  `.search k (probe P) (.const fire) (rest)`
* `run` stage, probed object `P`:    `.ite (.sim (.bot P) (.bot P)) .C (.const fire) (rest)`
* exhausted:                          `.const dflt`

Probed-object resolution — the ONE place the recursion lives:

* `target = name B` → `P := inst Z T B`  (the hypothesis's instance seeing B)
* `target = self`, `T ≠ A` → `P := inst Z T A`  (the hypothesis's instance seeing ME)
* `target = self`, `T = A` → emit the QUINE guard `.plays .self .self .C` directly
  (no recursion — the language's pronoun cuts the diagonal, byte-identical to
  `TauDupocδ`)

### 6.3 Termination — the measure IS the mutual-quine wall, mechanized

The recursion `(A,T) → (T,B)` terminates with measure
`m(A,T) = r A + r T` lexicographically paired with `s A`, where `r : ι → Nat` has
`r B < r A` for every NAMED target `B` of `A` (constants rank 0), and
`s A = 1` iff A has a `self` target:

* named target: `m(T,B) = r T + r B < r T + r A = m(A,T)` ✓ (for any T);
* self target, `T ≠ A`: the sum ties, `s` breaks it — needs `s T = 0`, i.e. **T is
  not itself a self-prober**;
* self target, `T = A`: the quine, no recursive call.

So `decreasing_by` closes **exactly when the zoo has at most one self-prober** —
the ≤1-self-prober restriction stops being prose and becomes the termination
certificate. Two self-probers = the mutual-quine 2-cycle = a failed
`decreasing_by`, at compile time. When `.sys` lands, `inst` is redefined by
binding instead of recursion and the obligation lifts. (Implementation fallback if
WF-recursion fights the equation compiler: fuel-indexed `instF` + a proven
sufficient bound `2·maxRank + 2` + a fuel-independence lemma; the measure version
is preferred — its failure mode is the feature.)

### 6.4 Vectors, weights, and the one mass lemma

```lean
def vecOf (Z : Zoo ι) (order : List ι) (A : ι) (w : ι → Nat) : VoteList  -- map + fold
def TauBot (Z) (order) (A) (w) (θ) : Prog := tauPlayer (vecOf Z order A w) θ
```

Weights become a FUNCTION `ι → Nat` (kills the `wC wD wTs wTp wL wE` signature
bloat — already painful at 6, absurd at 100). The per-bot `*_bits` cons-chains are
replaced by ONE list induction:

```lean
theorem vecOf_bits (b : ι → Action)
    (h : ∀ T ∈ order, ∃ N, eval N (.bot (inst Z A T)) (.bot (inst Z A T)) (inst Z A T)
                        = some (b T)) :
    VoteBits (vecOf Z order A w) (order.map fun T => (w T, b T))
-- and massOf (order.map …) = Σ {w T : T ∈ order, b T = C}   (one fold lemma)
```

Every per-bot phase theorem becomes: a BIT TABLE `b : ι → Action` + the
per-hypothesis h-obligation + `tauPlayer_phase_bits`. Nothing else.

### 6.5 Honest compression estimate — what shrinks, what stays

SHRINKS (mechanical, quadratic → constant/linear):
* N² instance terms → one `inst` compiler (the entire hand-written δ-closure of
  `Defs.lean` becomes derived notation; the maze of shape-names — `simOfSearchδ`,
  `searchOfSearchδ` … — retires in favour of `inst Z A T`, fixing the naming
  complaint at the root);
* N per-bot vectors + N `*_bits` cons-chains → `vecOf` + `vecOf_bits`;
* 6-ary weight signatures → `w : ι → Nat`.

STAYS HAND-WRITTEN (the mathematics — a DSL generates terms, not theorems):
* the COLUMN bit lemmas: what `probe (inst T X)` does at budget k, per hypothesis
  T and per column X actually used by the zoo's targets. Currently
  X ∈ {Coop, Defect, self-column}: ~3N lemmas, NOT N² — bits factor through
  columns because every prover stage probes a column object. This is today's
  `Certs.lean` reorganized by column; it grows LINEARLY in N (× the number of
  distinct targets, a property of the zoo's strategy diversity, not of N);
* the Löb lemma per self-prober (`ps_probe_quine`) and every floor/refutation
  argument — irreducible, they ARE the content;
* run-mode needs TRUE-play versions of the same column facts (today's behavioral
  entries) — same objects, eval-level.

### 6.6 Migration plan + gates

1. Land types + compiler + `vecOf` ALONGSIDE the Phase-4 layer (no deletion yet).
2. **Gate D1 (byte-identity, the tsearch-landing discipline):** `rfl` checks that
   the compiler reproduces the hand-written closure EXACTLY —
   `inst Z Dupoc Coop = searchOfCoopδ k`, `inst Z Dupoc Dupoc = TauDupocδ k`,
   `inst Z EBot Dupoc = eOfSearchδ k`, … (full list = the 36 entries of the
   Phase-4 vectors). A failed `rfl` = the compiler is wrong, not the closure.
3. Restate the six phase theorems as bit-table corollaries; `Certs` lemmas
   reorganized by column, statements unchanged.
4. Retire the hand-written vectors + shape-named instances (keep `abbrev`s for one
   commit, then delete; git archives).
5. **Gate D2:** engine green, 3 axioms, zero sorry, base outcomes byte-identical,
   tau matrix statements unchanged up to the weight-function refactor.

**✅ PHASE 5 LANDED 2026-08-18.** Engine green (3307 jobs), 3 standard axioms, zero
sorry, 78/78 base outcomes byte-identical, **all 26 Gate-D1 `rfl` checks pass on the
first build** — the compiler reproduces the hand-written closure byte-for-byte,
including the quine, the floor entry, and τ(EBot)'s whole cascade row.

What landed: `Tau/Spec.lean` (Mode/Target/Stage/Spec/Zoo, the `instGo`/`inst`
compiler, `vecOf`, the generic `vecOf_bits` list induction, the `tauZoo` spec table,
`TauBotZ`, Gate D1); `VotePhases`/`VoteMatrix` restated on the DSL interface
(`w : Tmpl → Nat`); the six hand-written `*Vec` lists and fixed-arity players
RETIRED from `Vectors.lean`. The named instances and `Certs` bit lemmas stay — they
are the ground truth D1 certifies against and the vocabulary the bits proofs use.

**DEVIATION from §6.3, recorded: FUEL, not the WF measure.** Tested before choosing:
WF-compiled definitions do NOT reduce by `rfl` even at fully concrete inputs (a toy
`termination_by` function fails `rfl` with a metavariable mismatch), and Gate D1 is
BY `rfl` — the measure version would force all 26 checks through simp-normalization
with a free budget `k`, reviving Phase 4's normalization fights. The fuel version is
structurally recursive (every call decrements fuel, including the cascade
continuation), fully `rfl`-reducing, `instFuel = 16` ≫ the zoo's nesting depth.
What the measure was buying is compensated: mis-compiles INCLUDING fuel exhaustion
cannot pass D1 (an exhausted compile emits a default constant, never byte-identical
to the closure). RECORDED DEBT, due when a SECOND zoo instantiates the DSL: the
generic `Zoo.WellFormed` predicate + fuel-sufficiency lemma — until then, D1-style
byte checks are the per-zoo certificate.

**Proof-craft note:** with compiled vectors, goals display entries in `instGo` form,
so `rw` against NAMED instances fails inside the bits proofs — state the entry play
as an explicitly-annotated `have` on the named instance and let defeq (which Gate D1
guarantees) bridge via `exact`. Two sites needed this (the tftSim EBot-entry witness
and the Dupoc quine entry).

Open question 5 resolved: `ι` = a readable enum (`Tmpl`), not `Fin n`; the interim
instance names were NOT abbrev'd — they persist as the ground-truth vocabulary of
`Certs`, with D1 tying them to the compiler output.

## 7. Phase 6 — Python: from separation-hunt to coincidence-certification

*(Was "Phase 5"; reordered 2026-08-18 to run AFTER the Spec DSL — see §6's ordering rationale. The `def4` model below is written against the DSL's interface: zoo list + `w : ι → Nat`, computed instances.)*

* `def4.py`: replace the per-bot probe-geometry model with the source-lift
  model — per-hypothesis COMPOUND bits computed by running the lifted cascade
  at point mass (pure matrix arithmetic, as today). Drop
  `Probe.*` geometries; keep the floor modelling (it now sits inside compound
  bits).
* `compare.py`: the expected headline INVERTS — assert Def3 ≡ Def4 at large k
  on every terminating cell of both zoos (this is the coincidence theorem,
  checked kernel-vs-arithmetic cell by cell); report the budget-axis
  divergences (floor cells, Löb thresholds) as the honest Def-4 content.
  Any (t, α) divergence on a terminating cell at large k is now a BUG in one
  side, by definition.
* `def4_theorems.py`: adapt the scanner to the new theorem names/regimes
  (one-sided EBot boundary; unchanged cooperator boundary).
* Retraction banners in these files then come down (replaced by the new
  model's docstrings).

**Gate 5**: coincidence check 100% on control + separating zoos at large k;
`uv run pytest` green.

**✅ PHASE 6 LANDED 2026-08-18.** All three Python tau modules rewritten; full
pytest green (349 + 198 EGT).

* `def4.py` — the SOURCE-LIFT model, the Python twin of the Lean Spec DSL:
  `LiftSpec`/`Stage`/`Mode` transcribed 1:1 from `tmplSpec`, and `decide(A, T)`
  computes compound decisions recursively with two pieces of proof-theoretic
  bookkeeping — the FLOOR is now STRUCTURAL (a cooperation reached after a failed
  `prove` stage is true-but-unprovable; the stipulated `FLOOR_BLOCKED_HYPOTHESES`
  set is gone) and the quine diagonal is the Löb rule. The mutual-quine wall is a
  loud `UnsupportedDiagonal`, mirroring the Lean termination discipline. The
  retracted `Probe.*` geometries are deleted.
* `def4_theorems.py` — the kernel scanner now reads the `VoteBits` theorems of
  `Tau/VotePhases.lean` (per-template bit rows in `tauOrder` slot order), failing
  loudly on drift.
* `compare.py` — INVERTED, as planned: three checks, strongest first. (1) KERNEL:
  all 36 Python compound decisions equal the Lean bit tables. (2) BITS: Def-4 vs
  Def-3 base-matrix bits — control 25/25 agree; separating 35/36 with the ONE
  divergence exactly the whitelisted Mirror-truncation cell (τ(EBot) self-bit,
  def4 D vs def3 C). A whitelisted cell that AGREES also fails (stale whitelists
  must not over-approve). (3) PHASE ATTRIBUTION: (t, α) sweeps with the
  whitelisted bit PATCHED to Def 3's value — control 35/35 divergent cells
  attributed (all α=0 constant artifacts), separating 167/167 attributed over
  1400 cells, 0 unexplained. **The zoo that "separated" the definitions under the
  retracted reading now certifies their coincidence** — the run's headline.

The α=0 constant artifact remains (Def 3's uniform lift cooperates on mass 0 at
α=0; Lean's `.const .D` defects) — recorded, classified, never counted as probe
semantics.

## 8. Phase 7 — docs, memory, cleanup (LAST)

*(Was "Phase 6". Deliberately the final phase: the design-note cleanup and the M2 ledger must describe the POST-DSL layer — writing them before §6 lands would document names and vectors scheduled for deletion.)*

**✅ PHASE 7 LANDED 2026-08-18 — the roadmap is CLOSED.** Design note Part III got
a STATUS box (what is live vs history), its stale convention 6 and Milestone-2
debt were corrected (debt retargeted `tsearch`→`tvote`; the `tsim` idea RESOLVED —
it IS `tvote`), the retraction pointer now records execution, and CLAUDE.md's tau
pointer names both notes. Memory consolidated. Remaining debts, all recorded at
their sites: Metatheory M2 (`tvote` arms), the generic `Zoo.WellFormed` +
fuel-sufficiency lemma (due at the second zoo), sub-Löb regimes, `LegacyS.lean`
(broken since the `tsearch` landing, pre-existing), and the `.sys` revival.

* `TAUBOT_TRANSPARENCY_DESIGN.md`: Part III gets a one-line pointer to this
  note as the executed redefinition (full cleanup of that note is a SEPARATE
  later task — agreed 2026-08-18).
* Memory: update the Def-4 milestone note; record the locked decisions.
* M2 debt ledger: `Metatheory` restoration owes `tvote` arms (`enumProg` over
  `VoteList`, `evalG` peel with entry evaluation, gate walkers) and NO LONGER
  owes any `tsearch` arms (Phase 4b removes them before M2 starts) — a net
  shrink of the M2 surface. Still deferred.

---

## 8b. Addendum 2026-08-19 — the generality pass, and the SCHEDULED zoo-generic fuel debt

Post-closure work (Colomban: "be as general as possible to invite larger zoos"),
in three steps; **steps 1+2 LANDED 2026-08-19, step 3 is the scheduled debt.**

**Step 1 — `phase_of_bits`, the generic phase theorem (LANDED).** `Spec.lean` now
composes `vecOf_bits` + `tauPlayer_phase_bits` ONCE: supply a bit table
`b : ι → Action` and its witness (`∀ T ∈ order`, the instance plays `b T`), get
both phase directions thresholded at `bitMass w b order` (`Vote.lean`: `massOf`
over the mapped table — the fold form of every regime mass). Every per-bot
`Phase.lean` was restated on it: a bit ROW `def <bot>Row : Tmpl → Action` (9
explicit arms), a witness lemma `<bot>Row_plays : ∀ T, …` (match arms = the old
chain's slot proofs), and the phase theorem = `phase_of_bits` + one `simp`
reduction of `bitMass` to the display mass. The nine hand-rolled 9-deep `.cons`
chains are GONE; adding a bot to the zoo now costs one row arm + one witness arm
per file, not a chain restructuring.

**Step 2 — masses as folds (LANDED, display-preserving).** `bitMass` is the
general mass; the hand-written regime masses (`simMass`, `pfMass`, …) SURVIVE as
display forms because (a) `Matrix.lean`'s band proofs do `simp only [mass]; omega`
on literal sums, and (b) they are what `bitMass` reduces to on the concrete
enumeration. The phase proofs bridge the two by the same simp step.

**Scanner constraint, load-bearing:** the per-bot `<bot>Bits` theorems' LITERAL
bit lists are read by `app`'s `def4_theorems.py` — their statements must stay
byte-stable. They are now one-line corollaries of `vecOf_bits` (the mapped row is
the literal list by defeq on the concrete zoo) and are annotated scanner-facing.
If the scanner is ever retargeted at the `<bot>Row` tables (easier to parse), the
corollaries can go.

**The 9-zoo coincidence certification (2026-08-19, later the same day) — and what
it CAUGHT.** Extending `bit_coincidence` to all 81 template cells (`FULL_BOTS`, the
base matrix is total over the 8 base bots) failed on two cells beyond the recorded
Mirror one, both at the Guardian hypothesis, both `def4 D` vs `def3 C`:

* `(TauTFTPf, TauGuardian)` — BY DESIGN: the prover variant of behavioral base TFT
  cannot cite Guardian's floor-priced cooperation. The BASE_OF claim "the twins'
  bits coincide at large k" was thereby FALSIFIED (it held only floor-free);
  whitelisted with the honest reason — the α-gap headline as a bit.
* `(TauEBot, TauGuardian)` — A REAL TRANSCRIPTION INFIDELITY, dating to the
  original 2026-08-11 tau layer and invisible until Guardian joined the zoo: **base
  EBot is a SIMULATOR** (`.sim .opp (.bot DefectBot)` / `(.bot CooperateBot)`), but
  the tau template used `prove` stages. Guardian's floor is the first cell where
  the modalities disagree at large k, and the certification flagged it on first
  contact. FIXED (run-mode spec, the faithful lift): `tauEBotSpec` is two `run`
  stages; Gate D1 re-pinned by `rfl`; `eRow`/`eMass` now include `w .guardian`;
  the exploiter/trust bands restated (`eMass` and `pfMass` are now incomparable —
  they differ by wC vs wGuardian; the trust band is nonempty iff wC > 0).

**The run-mode fix forced the EMBEDDED-floor census** — the kernel the DBot lift
was deferred on, now delivered (`Tau/Theorems/TauEBot/Helpers.lean`,
`no_provable_botRunCascade_C`): `inst .ebot .dupoc` still truly cooperates and its
probe is still 0, but the floor moved ONE LEVEL DOWN — any certificate must certify
the exploit-WATCH falling, i.e. that the watched `inst .dupoc .defect` (a budget-k
searcher) plays its else-action, and that subproof pays the `search_f` floor. The
census instantiates `no_provable_tailToS_floor` with a two-level-deeper atom killer
(`bot → ite_t` fire-mismatch / `ite_f → sim → bot → search_t` const-mismatch /
`search_f` floor `kb`), needs NO hypothesis on the inner guard, and unblocks the
DBot lift's recorded blocker. Python's `decide` needed no change (its floored
run-consultation tracking, built for OBot, already computes the embedded floor);
whitelist now has exactly TWO entries, and the full-zoo certification passes
79/81 + 2 whitelisted.

**DBot LIFTED (2026-08-19) — the 10th template, and the last non-`.sys` bot.**
Unblocked by the embedded-floor census the run-mode EBot fix had just forced: the
single-stage twin `no_provable_botRunStage_C` (`Theorems/TauDBot/Helpers.lean`)
prices out `inst .dbot .dupoc`'s cooperation, which is REAL (its watch sees
Dupoc-seeing-Defect defect and falls to the trusting default) but sits behind a
watched budget-`k` searcher whose D-play certificate pays `search_f`. Spec:
`⟨[⟨.run, .name .defect, .C, .D⟩], .C⟩` — one watch, trusting default.

**The result it produced: τ(DBot) PUNISHES ITSELF** (`dbot_selfWatch_fires`,
`outcome_TauDBot_vs_TauDBot_high`). Its own instance at the defector TRUSTS (a
defector is no pushover), and trust-toward-a-defector is exactly what the punisher
fires on — so `dbotMass` excludes `w .dbot` as well as `w .coop`. The behavioral
analogue of single-tier PrudentBot's `(D, D)` self-play: a detector whose test
cannot exempt its own reasoning. Base `outcome_DBot_vs_DBot = (D, D)` agrees, and
the coincidence certification confirms it independently.

Certification after the lift: **100 cells, 98 agree, 2 whitelisted** (unchanged —
DBot introduced NO new divergence; all ten of its cells coincide with base DBot).
Zoo is now 10 templates over 9 base bots. Remaining unlifted: the 5 self-probers
(`.sys`) and the 4 non-cascade-fragment bots (CIMCIC/DIMCID impl, WaryBot `.neg`,
CupodTrollBot `.eq`).

**FRAGMENT EXTENSION 1 + CupodTrollBot LIFTED (2026-08-20) — and §8c's blocker
classification CORRECTED by Gate D1.** Following §8c.7's recommendation (fragment
work before `.sys`), the first attempt targeted CIMCIC. The `Mode.proveImpl`
machinery (the `probeImpl` atom + both compiler arms, with the antecedent's subject
kept as the `.self` pronoun since the instance cannot contain itself) LANDED and is
correct — but **Gate D1 refused the CIMCIC row by `rfl`**, on exactly three
hypotheses: `dupoc`, `just`, `cimcic`.

*The correction it forced:* **CIMCIC is a SELF-PROBER.** Its guard
`.impl (.plays .self .opp C) (.plays .opp .self C)` mentions BOTH pronouns, so its
target is `self`, so `inst(cimcic, dupoc)` needs `inst(dupoc, cimcic)` needs
`inst(cimcic, dupoc)` — the mutual-quine wall, not the fragment wall. Same for
DIMCID (identical shape) and WaryBot (`.neg (.plays .opp .self C)`). §8c's estimate
"six bots for no engine tax" was therefore WRONG: it is **one**. The rule the note
should have applied: *a guard mentioning `.opp`'s view of `.self` is a self-probe,
whatever its outer connective* — the connective decides the FRAGMENT, the pronouns
decide the `.sys` question, and they are independent.

*What landed instead:* **`Mode.proveEq` + τ(CupodTrollBot)** — the ONLY unlifted bot
whose guard names a literal third party (`.eq .opp (.bot (CupodBot k))`) rather than
the opponent's view of me, hence the only one liftable without `.sys`. Spec
`⟨[⟨.proveEq, .name .dupoc, .C, .D⟩], .C⟩`; 11th template; Gate D1 green on all rows
including every pre-existing one (the regression gate §8c.5 demanded).

*Two honest results, both recorded at their sites:*
1. **τ(CupodTroll) is constant-C on this zoo** — its identity check never fires
   because the bot it looks for (CupodBot) is `.sys`-blocked and absent. That is a
   faithful lift of a bot whose only target is missing, not a degenerate one; the row
   changes the day CupodBot lands, which makes this bot the zoo's standing
   REGRESSION TEST for the `.sys` milestone.
2. **It is the zoo's SECOND floor bot.** Its C is reached through a FAILED `.eq`
   search, so the transcript pays `search_f` and no prover can cite it
   (`ps_probe_inst_cupodTroll_false`, via `no_provable_botSearcherElse_tail`) — the
   Guardian shape reached by a different route. Consequence: three new whitelisted
   coincidence cells (`TauTFTPf`, `TauDupoc`, `TauJust` × `TauCupodTroll`), all
   `def4 D` vs `def3 C`, all the same mechanism. Whitelist is now 5 cells; the
   certification passes **121 cells, 116 agree, 5 whitelisted**.
3. Two Python tests were legitimately FALSIFIED and restated rather than patched:
   the TFT-variants split is now "exactly at the FLOOR bots" (Guardian ∪ CupodTroll,
   not Guardian alone), and OBot's boundary is `obotMass = w .coop + w .cupodTroll`
   (a second bot passes both defection watches). `simMass` gained `w .cupodTroll`;
   `eMass` did not (τ(EBot) fires on CupodTroll's trust of the defector).

*Revised remaining backlog:* **9 bots, and 8 of them need `.sys`** — CupodBot,
PrudentBot, MirrorBot, LegibleBot, OptimBot, CIMCIC, DIMCID, WaryBot (all
self-probers; several ALSO need fragment work). The genuinely fragment-only backlog
is now EMPTY. This inverts §8c.7's recommendation: the fragment-first argument was
built on a miscount, and `.sys` is now the only path to any further bot.

**THE `.sys` MILESTONE (2026-08-20/21) — the mutual-quine wall is BROKEN, and the
first thing through it is a NEGATIVE result.** Phases S1–S4 of §8c executed:

* **S1/S2 — the binder** (`9e8135f`): `.sys`/`.selfIdx`/`ProgList`, `sysClose`, the
  lazy-unfold eval arm, `PlaysProof.sysStep`, soundness, and (new work the archive
  did not have) τ-closure — τ̂ DESCENDS into system members, unlike frozen vote
  entries, which forced `ProgList.transpose`, `sysClose_transpose` and
  `get?_transpose`. Kernel-checked: a mutually-simulating pair evaluates to `none`,
  fuel-grounded rather than divergent.
* **S3 — the compiler emits it** (`2b2acff`): `Zoo.entangled` + `sysGo`. **Spike B's
  landmine hit for real**: with plain `termination_by fuel` the mutual pair compiled
  by WF recursion and `inst` stopped reducing — Gate D1 failed on the CONSTANT row.
  `termination_by structural fuel` restores defeq. Gate S1 held: every pre-existing
  peel still `rfl`.
* **S4 — CupodBot lifted** (`06b9369`, `83ba46b`): the 12th template, 13 new D1
  peels including both entangled cells. **τ(Cupod) defects against itself** —
  polarity-inverted Löb, and a first attempt to get it cheaply from the `search_f`
  floor was WRONG (that floor excludes the ELSE-play; the guard atom is the
  THEN-play, which `search_t` reaches — the kernel caught it).
* **`botSysSearchStep`** (`0231670`): the rule letting S read a component through
  `sysClose` and conclude about its partner. Soundness passed first try. Its cost
  was NOT the rule but the census: a `.bot (.sys …)` player is genuinely READABLE,
  so `ReadableMe` gained a disjunct and ~25 call sites across the library needed a
  new kill obligation. **Recorded for the next constructor: adding a readable player
  shape is far more expensive than adding an unreadable one (`tvote`).**

**THE FINDING — the 2-cycle is NOT Löbian.** With `sys_cross_D`/`sys_cross_C`
derived, the available implications at the cupod/dupoc system are, by inspection of
the shape requirements, exactly two:

    □(component 1 plays D) → component 0 plays D      (Cupod punishes a provable defector)
    □(component 0 plays C) → component 1 plays C      (Dupoc rewards a provable cooperator)

A Löb cycle needs one consequent to be the other's antecedent; here they meet at
OPPOSITE ACTIONS on both sides. The chain never closes and
`mutual_pblt_engine_id` has nothing to consume. This is the right answer, not a
missing lemma: Dupoc's fixpoint is self-SUPPORTING (hence its Löbian diagonal),
while the mixed pair's would have to be self-DEFEATING, and bounded Löb cannot
manufacture one from an anti-monotone loop. So `(cupod, dupoc)` and `(dupoc, cupod)`
are **genuinely open at the object level** — the bistable shape, with
`outcome_JustBot_vs_MirrorBot` as the base-library precedent — and enter the column
and phase theorems as hypotheses, exactly as the Dupoc quine bit once did.

**The natural next question**, recorded: base `(CupodBot, DupocBot)` — Critch's open
problem — WAS resolved in the base library (2026-08-20) by the τ-transposition,
which needs only soundness and τ-closure and never needs the fixpoint to close.
`Pf.transpose` now has its `sysStep` arm, so S is closed under τ WITH the binder
present: the ingredient for lifting that route to the `.sys` layer is in place, the
argument is not yet written.

**Python mirror** extended to match: `EntangledCell` (distinct from
`UnsupportedDiagonal` — the answer does not exist, rather than the model being
unable to express it), `open_cells`, the punish-polarity quine, and open-cell
skipping in `kernel_check`/`bit_coincidence`. Openness PROPAGATES correctly: Just
and CupodTroll probe the Dupoc column, so their Cupod cells are open too — matching
Lean, where those rows carry the same hypothesis.

**Certification refreshed for the 12-zoo (2026-08-21):** `kernel_check` now
distinguishes UNSTATED rows from mismatched ones — 129 cells checked, zero
mismatches, `TauCupod` reported as unstated (its `VoteBits` theorem awaits the
δ_Cu guard column, below). `bit_coincidence` passes at 121 cells / 116 agree /
5 whitelisted / **0 unexpected**. Two tests were legitimately falsified and
restated rather than patched: the mutual-quine wall now raises `EntangledCell`
("the answer does not exist") instead of `UnsupportedDiagonal` ("I cannot express
this") — a strictly more informative refusal — and **τ(Cupod) is the zoo's THIRD
floor bot**, so the prover/behavioral TFT split now shows at three hypotheses
(Guardian, CupodTroll, Cupod) rather than two.

**The τ-route was TRIED and does not transfer (2026-08-21, Colomban's suggestion —
worth recording because the ingredients all exist).** The base red cell is settled
without any fixpoint by the τ-transposition, and here: the components ARE each
other's τ-images (`cdSys_transpose`), `Pf.transpose` HAS its `sysStep` arm, and the
transposed system is literally the cell in the other order
(`inst_dupoc_cupod_transpose`, proven). The argument still fails, for a structural
reason. In the BASE, Dupoc and Cupod are two separate programs whose guards name
each other directly, so a proof of one guard both fires Dupoc's search AND
transports to a statement whose soundness makes Dupoc play the opposite action —
**same program, two actions**, refuted by `eval_det`. In the TAU layer the binder
makes the pair ONE object and each component names the other by INDEX; τ̂ swaps the
roles in place, mapping the system to a DIFFERENT system. So the transported proof
concerns `cdSys.transpose`'s component, not `cdSys`'s, and the closing move has no
analogue (checked: `(cdSys k).transpose.get? 0 ≠ (cdSys k).get? 1`). What would be
needed: a τ-argument at the SYSTEM level rather than the component level — relating
`.sys defs i` to `.sys defs.transpose i` as plays of one object, which the current
`Prog.transpose` does not give since it descends into members. Open.

**Open debt from this milestone**, recorded at their sites:
* **the δ_Cu guard column** (`probeD (inst T .cupod)`). Its blocking cell is now
  PROVEN — `pf_probeD_obotSecondFires` (the OBot idiom's `probeD` transcript; the
  cost is `m + n + 8`, and the earlier failure was a missing outer `bot`'s
  `c_node`). The column itself still needs assembling from it.
* **`TauCupod/Phase.lean`** states its bit row (`cupodRow`, parameterized by the
  open `.dupoc` bit) but not its witness, `VoteBits` or phase theorem; those need
  the δ_Cu column.

**Status: 12 templates over 10 base bots.** Remaining unlifted: PrudentBot and
OptimBot (`.sys` + fragment extensions), MirrorBot and LegibleBot (fragment only),
CIMCIC/DIMCID/WaryBot (self-probers needing the `proveImpl`/`.neg` fragments, which
`.sys` now unblocks structurally). Debt opened by this milestone: TauCupod's
`Phase.lean` states its bit row but not yet its phase theorem, and the Python
certification counts need refreshing for the 12-template zoo.

**Step 3 — SCHEDULED DEBT: `Zoo.WellFormed` + computed fuel (NOT started).** The
piece that would make MACHINE-GENERATED zoos possible by replacing Gate D1's
hand-written closures. Components, sketched 2026-08-19:
* `Spec.probeDepth` / `Zoo.maxDepth` — syntactic probe-nesting depth over the
  spec table;
* `fuelFor Z` replacing the bare `instFuel = 16`;
* the FUEL-STABILITY lemma `depth ≤ n → instGo Z (n+1) … = instGo Z n …` —
  sufficient fuel is a fixpoint, so `inst` is canonically fuel-independent above
  the bound (the structural induction needs care at the quine diagonal);
* `Zoo.WellFormed` (decidable): probe chains bottom out, at most quine-cut
  self-reference; well-formed ⇒ `fuelFor` suffices.
Deliberately deferred: with one zoo, D1 IS the certificate, and the design is
better informed by the first real second zoo (which may be `Fin n`-indexed,
changing what `WellFormed` quantifies over). DUE when a second zoo instantiates
the DSL — same trigger as the §6 deviation's original debt note, now with the
concrete component list.

**THE ENTANGLED CELLS FALL (2026-08-21, evening) — the "genuinely open" verdict
above lasted one session, and its own negative finding is what killed it.** Three
moves, in order:

1. **The wrapped-emission fidelity fix** (`2eeb39b`). `sysGo`'s self-arms emitted
   bare `.selfIdx j` where every off-cycle guard freezes `.bot P`. Uniformity
   demanded `.bot (.selfIdx j)` — and turned out to be load-bearing: with wrapped
   references every entangled guard is a `probe`/`probeD` of the wrapped partner
   component, exactly the shapes `botSysSearchStep` and the census kernel speak.
   All Gate D1 peels survived as `rfl`.
2. **THE FLOOR DECIDES anti-aligned 2-cycles.** The Löb-wall finding said the
   cupod/dupoc implications meet at OPPOSITE actions — the flip side nobody
   pushed: if `search_t` cannot conclude the target (action mismatch with the
   partner's then-branch), the ONLY other route pays the partner's `search_f`
   floor. New census `no_provable_botSysSearcherElse_tail` (the `hbotsys` kernel
   obligation became ACTION-REFINED like `hbotsearch` — 25 mechanical call
   sites): **both bits of an anti-aligned pair are provably FALSE, both
   components play their defaults, and no bistability survives the cost floor.**
   `hdc`/`hcdP`/`hcupodDupoc` — the open-cell hypotheses — became theorems with
   exactly their canonical values: the tau image of the red cell is
   `(D, C)`, PROVEN. The JustBot-vs-MirrorBot analogy was wrong in an
   instructive way: bistability needs the self-fulfilling branch to be
   affordable, and inside `.sys` it never is unless the actions align.
3. **MUTUAL LÖB THROUGH THE BINDER — CIMCIC lands as the 13th template**
   (`ebaa425`, `2eeb39b`, and the total-zoo commit). Where the actions DO align
   the opposite happens: `botSysSearchStep` yields precisely the two
   box-implications `mutual_pblt_engine_id` consumes, and the base
   `llm_outcome_CIMCIC_vs_DupocBot` fixpoint transfers to `.sys` verbatim —
   `outcome_TauCIMCIC_vs_TauDupoc = (C, C)`, the FIRST entangled cell resolved
   by cooperation. CIMCIC's off-cycle row is the first `.impl`-guard row: TRUE
   bits by `weakenImpl` (+ `implRefl` on the diagonal — after subst the guard is
   literally `φ → φ`), FALSE bits by the existing censuses THROUGH the
   implication (TailTo walks to the consequent), plus two new budget-free
   censuses (`no_provable_botConst_tail`, `no_provable_twoTestD_cimcic_C`).
   τ(CIMCIC)'s row comes out IDENTICAL to τ(Dupoc)'s: conditional cooperation
   and Löbian cooperation coincide on this zoo, by different mechanisms.

**The layer is now TOTAL and hypothesis-free: 13 templates, 169 stated cells, no
open cells; every phase theorem unconditional modulo its `∃k₂` Löb gate.** The
δ_Cu-column and TauCupod-phase debts above are PAID. The Python mirror computes
the entangled cells (`_resolve_entangled`: alignment → mutual Löb, else floor);
`open_cells()` is empty; kernel check 169/169; Def-3 coincidence 144 cells with
the same five whitelisted divergences.

The alignment rule, for the record (it is the entire decision procedure): an
entangled pair cooperates-by-Löb iff each member's guard target (its `test`, or
`C` for a `proveImpl` consequent) equals the OTHER member's fire action;
otherwise both bits are floor-false and both members play their defaults.

**Debt from this milestone:** base `CIMCIC ↔ OBot` is the one base pair the
Def-3 comparison consults without a theorem (stipulated `(D, D)` in the
comparison and the enlarged zoo) — the two-watch C-target census exists at the
tau shapes (`no_provable_twoTestD_cimcic_C`) and wants transplanting to the base
OBot shape (`.sim .opp (.bot z)` watches). The system-level τ-argument (relating
`.sys defs i` to `.sys defs.transpose i`) remains open but is no longer needed
for any current cell.

**Remaining unlifted: DIMCID** (CIMCIC's twin — the same machinery with polarity
flips; expected cheap), **WaryBot** (`.neg` fragment), **MirrorBot** (raw `.sim`
+ the non-termination whitelist decision), **LegibleBot** (`.box`),
**PrudentBot/OptimBot** (nested/self-side shapes).

---

---

## 8c. SCOPING NOTE 2026-08-20 — the `.sys` revival for Def-4 self-probers

*Written before any code (Colomban: "scope the `.sys` design first"). Reuses the
design record of `DEF5_SYS_BINDER_ROADMAP.md` (Route A, SHELVED) but **re-scopes it
for Def 4**, where the requirement is strictly weaker. Nothing here is committed to
yet; §8c.7 is the decision list.*

### 8c.0 The headline: `.sys` is an INTEGRATION decision, not a research question

The archived tag **`taubot-def5-research`** holds a complete, machine-checked `.sys`
implementation: the binder + `ProgList` in `Program.lean`, `sysClose`, the lazy-unfold
eval arm, `PlaysProof.sysStep`, and milestone 1
(`outcome_TauDupocSys_vs_TauDupocSys = (C, C)`) — 3-axiom footprint, build green.
Both go/no-go spikes PASSED (`Research/Spikes/sysLob/`, in-tree, zero maintenance):

* **Spike B (`MiniSys.lean`) — equation-compiler gate: PASS.** `sysClose` is
  structurally recursive with definitional unfolding *without* annotation; the inner
  `match` in the `.sys` eval arm caused no equation-generation problem; mutual proofs
  are ergonomic in equation style. **One binding constraint discovered: the mutual
  list evaluator must charge fuel PER `cons`** (keeping fuel constant across the list
  makes the pair non-structural and silently drops to WF recursion, killing `rfl`).
* **Spike A (`VectorPblt.lean`) — vector-Löb gate: PASS**, and its glue was
  PROMOTED into `Base/Loeb.lean` and is live today: `compUnder`/`postUnder`/
  `swapAnte`, `loeb_premise_under_box`, `vector2_full_pblt_engine`. Zero new
  constructors (Family-B completion made the B-combinator dance derivable).

It was reverted for a stated, non-technical reason: the **standing tax** on the Def-4
track (T31–T54 Metatheory arms for `.sys`/`.selfIdx`, two extra `Pf` constructors,
`hbotsys`/`h_sys` census obligations at every future call site, proof-agent prompt
surface). So the question is not "does this work" but "what is the smallest version
that unblocks Def-4, and is its tax worth paying now".

### 8c.1 THE RE-SCOPING — Def 4 needs strictly less than Def 5

This is the most important paragraph in the note. Def 5 probes hypotheses **at the
σ-blur itself** (blur as common knowledge, the full Harsanyi hierarchy); its
σ-reference graph is the COMPLETE digraph on the non-constant zoo, and its Löb
premises are FULL-DEPENDENCY vectors — which is exactly why Spike A had to build
`vector2_full_pblt_engine`.

Def-4 self-probers are a **containment** problem, not a semantic one. The sentences
stay point-mass Def-4 sentences; only the compiler cannot write the term, because
`inst(X, δ_Y)` must contain `inst(Y, δ_X)` must contain `inst(X, δ_Y)`.

| | Def 5 (archived) | Def-4 self-probers (this scope) |
|---|---|---|
| Sentence system | σ-blurred, complete digraph | point-mass, only between mutually-probing pairs |
| Löb shape | full-dependency vector | **2-cycles** (pairwise) + the existing diagonal quine |
| Engine | `vector2_full_pblt_engine` (built, live) | likely `mutual_pblt_engine_id`/`_staggered` — ALREADY LIVE and used by the base zoo |
| New `Pf` rules | `sysStep` + `botSysTsearchBranch` | **`sysStep` alone** (no `tsearch` exists any more) |

**Measured entanglement.** With today's 10 templates the only self-prober is `dupoc`.
Adding CupodBot yields exactly ONE 2-cycle (`dupoc ↔ cupod`) — a 2-sentence system,
which is precisely the shape `mutual_pblt_engine_id`/`_staggered` already close for
the base zoo (`outcome_PrudentBot_vs_DupocBot` etc.). **The vector engine is probably
not needed at all** for the first `.sys` bot; it becomes needed only at ≥3 mutually
probing self-probers (complete digraph on 3 = 3 two-cycles plus 3-cycles).

### 8c.2 The five "self-probers" are FOUR different blockers — only one is `.sys`

Reading the base definitions (`Bots/*.lean`) against the Spec DSL's `Stage`
vocabulary (`mode : prove | run`, `target : self | name i`, `test`, `fire`):

| bot | base guard | real blocker | verdict |
|---|---|---|---|
| **CupodBot** | `.plays .opp .self D` | mutual quine ONLY | **`.sys` alone unblocks it** — spec is `⟨[⟨.prove, .self, .D, .D⟩], .C⟩`, already in the fragment |
| **PrudentBot** | `.plays .opp .self C` then `.plays .opp (.bot DefectBot) D` | quine **+ a NESTED target** ("opp vs a *third party*", not opp-vs-me) | needs `.sys` AND a `Target` extension |
| **OptimBot** | `.plays .self .opp …` (both polarities, 3 rungs) | quine **+ SELF-SIDE probes** ("what do *I* do vs them") — a new target kind | needs `.sys` AND a new target kind |
| **MirrorBot** | `.sim .opp .self` (raw copy) | **not a cascade at all** — no `.ite`, no test | needs a `Mode`/shape extension, `.sys` irrelevant |
| **LegibleBot** | `.box kIn (…)` | **modal guard** — outside the plays-atom fragment entirely | same class as WaryBot/CIMCIC; `.sys` irrelevant |

**Consequence for planning: "attack the 5 self-probers" is not one project.**
`.sys` buys exactly **one** bot cleanly (CupodBot), is a *necessary but insufficient*
condition for two more (PrudentBot, OptimBot), and is **irrelevant** to the last two
(MirrorBot, LegibleBot — they belong with the 4 non-fragment bots).
Honest revised count: the fragment-extension work is the bigger half.

### 8c.3 Base-matrix status — openness is a PYTHON constraint, never a Lean one

Asked and answered before designing (Colomban, 2026-08-20): *what if the base matchup
is open?*

* **Lean does not care.** The tau layer never reads base outcome theorems. `inst A T`
  is compiled from specs and its bits are proven from the TAU columns. A tau cell is
  open only if the LIFTED terms have no proof — a fresh question about different
  objects. (`outcome_JustBot_vs_MirrorBot` is famously bistable-open; it says nothing
  about `τ(Just)`'s mirror bit.)
* **Python refuses, loudly, by design.** `load_tau_matrix` demands totality;
  `bit_coincidence` compares Def-4's bit against `matrix.cooperates(base_a, base_t)`,
  so an open base cell leaves nothing to compare. This guard is what caught the EBot
  modality infidelity — do not weaken it.
* **The third option already exists**: `NamedZoo.stipulations` fills a genuine hole
  and flips `TauMatrix.is_fully_proven` to False. Policy (unchanged, honor it):
  stipulations may ONLY fill real holes (the loader raises if one shadows a proven
  cell — that is how the red-cell removal was forced), and any non-invariant result
  must be reported as conditional.

**Measured (2026-08-20), each self-prober added to the current 9 base bots:**

| bot | base matrix |
|---|---|
| PrudentBot, MirrorBot, LegibleBot | **join cleanly** (no holes) |
| CupodBot, OptimBot | **blocked** — unproven cells |
| all five at once | 21 unproven ordered cells |

**The irony worth flagging: the base matrix and the DSL disagree about which bot is
easiest.** CupodBot is the only clean `.sys` win in Lean but has open base cells;
PrudentBot/MirrorBot/LegibleBot have total base rows but need fragment extensions.
So the first `.sys` bot will EITHER carry a recorded stipulation OR require proving
CupodBot's missing base cells first. That trade is a decision, not a detail (§8c.7).

### 8c.4 Design deltas vs the archived Route A (what changes on re-application)

The archived conventions (Part I of `DEF5_SYS_BINDER_ROADMAP.md`) are adopted
UNCHANGED — binder + `.selfIdx`, lazy unfold, two complementary closers (`subst` never
touches `.selfIdx`; `sysClose` never touches `.self`/`.opp`; **`.bot` is a barrier for
`subst` but TRANSPARENT for `sysClose`**), honest size, unchanged probe-atom shape,
positivity. Deltas forced by everything that landed since 2026-08-13:

1. **A cherry-pick will NOT apply.** The engine commits (`3b2f130` binder,
   `1d85be9` `sysStep`) predate: `.tsearch` removal, `.tvote` + `VoteList`,
   `VoteAllPlay` (a FOURTH mutual inductive — every `motive_N` index shifted), and the
   Spec DSL. Re-apply guided by the diff, do not `git cherry-pick`.
2. **The tax is SMALLER than at revert time, in one direction and larger in another.**
   Smaller: `.tsearch`'s removal deleted exactly the surface `.sys` regrows (5 rules,
   both eliminators' arms, 5 soundness arms, 13 census arms, the M2 mirror), and the
   `h_tvote` precedent shows the census obligation is ~7 trivial discharges across 4
   files. Larger: **Metatheory M2 already owes `tvote` arms and is unpaid** — `.sys`
   compounds an existing debt rather than opening a fresh one.
3. **`instGo` is FUEL-based now** (§6 deviation), and Gate D1 is by `rfl`. `.sys`
   changes probed-object resolution: a `.selfIdx` reference is where the recursion
   STOPS rather than descends, so it should make fuel sufficiency EASIER, not harder.
   This interacts with — and may partly discharge — the Step-3 debt (§8b).
4. **Spike B's binding constraint applies verbatim**: any mutual list traversal added
   for `ProgList` must charge fuel per `cons`, or the equation compiler silently drops
   to WF recursion and `rfl` dies (and with it Gate D1).
5. **`vector2_full_pblt_engine` is already in-tree** — if a ≥3-cycle ever appears the
   engine is there; the first bot almost certainly does not need it (§8c.1).

### 8c.5 The compiler change (the ONE place the design actually lands)

Today `instGo` emits the quine pronoun only at the diagonal (`target = self, T = A`)
and recurses otherwise; two self-probers make that recursion non-terminating (§6.3's
measure fails exactly there — "the failure mode is the feature").

The `.sys` version replaces the recursion with a **binding** step: the entangled
instances become components of ONE system, and a probe that would revisit a pair
already on the stack emits `.selfIdx j` instead of recursing. Sketch, to be fixed at
implementation:

* compute the entangled set (the SCC of the probe-reference digraph containing the
  pair) — a spec-level, decidable computation;
* emit `defs : ProgList` = one component per member of the SCC, each compiled with
  intra-SCC references as `.selfIdx`;
* `inst Z A T` for an entangled pair = `.sys defs i` at the right index;
* everything outside the SCC compiles exactly as today (so the 10 current templates'
  Gate-D1 equations must remain byte-identical — that is the regression gate).

**Gate S1 (the D1 analogue, non-negotiable):** every existing `inst_*_peel` equation
still holds by `rfl` after the change. A `.sys` revival that perturbs the current zoo's
compiled terms is wrong.

### 8c.6 Phase sketch (NOT scheduled — costed for the decision)

| phase | content | gate |
|---|---|---|
| S0 | Decide §8c.7. Re-read the archived diff; confirm the Löb engine choice against the measured 2-cycle | — |
| S1 | Binder re-application: `ProgList`/`.sys`/`.selfIdx`, `sysClose`, eval arm, subst/size/hasSearch/DecidableEq | engine green; **all current D1 peels still `rfl`**; base outcomes byte-identical |
| S2 | `PlaysProof.sysStep` + eliminator arms + `wv_sound_upto` arm + `h_sys` census discharges | 3 axioms, zero sorry, `sound_upto` green |
| S3 | Compiler: SCC detection + `.selfIdx` emission; `tauCupodSpec`; Gate S1 | Gate S1 + new peel equations by `rfl` |
| S4 | The mathematics: Cupod's column arms, the `dupoc ↔ cupod` 2-cycle Löb closure, phase theorem | the bits/phase theorems; `is_fully_proven` status recorded |
| S5 | Python mirror: `.sys` in `def4.py` (the SCC/binder case replacing `UnsupportedDiagonal`), TEMPLATES/TAU_ORDER/LEAN_SLOT/BASE_OF, coincidence re-run | 121 cells, divergences whitelisted-or-explained |

Realistic reading: **S1+S2 are a day of mechanical re-application** (the design is
settled and the spikes de-risked the compiler questions); **S3 is the genuinely new
engineering** (SCC detection inside a `rfl`-reducing fuel-based compiler); **S4 is the
real mathematics** and where surprises live, exactly as Guardian and DBot were.

### 8c.7 OPEN DECISIONS (must be settled before S1)

1. **Is `.sys` worth its standing tax for ONE clean bot?** `.sys` unblocks CupodBot
   alone; PrudentBot/OptimBot additionally need fragment extensions, MirrorBot and
   LegibleBot need them INSTEAD. A defensible alternative ordering: do the
   fragment extensions FIRST (they unblock MirrorBot/LegibleBot/CIMCIC/DIMCID/
   WaryBot/CupodTrollBot — six bots, no engine tax), and revive `.sys` once ≥2 of the
   remaining bots genuinely need it. **Recommendation: seriously consider this
   ordering.** It maximizes bots-per-unit-tax and defers the Metatheory compounding.
2. **CupodBot's open base cells**: prove them, or admit CupodBot under recorded
   stipulations with `is_fully_proven = False`? (Note `CUPOD_STIPULATIONS` already
   exists in `tau/matrix.py` for exactly this bot, with the invariance argument
   written out — precedent exists, but it was for a DIFFERENT purpose.)
3. **Route B (the belief-order tower)** remains the standing fallback and is
   *cheaper*: no language change, Löb only at the bottom level, term size `|zoo|ⁿ`.
   It approximates A and doubles as A's validation oracle. Worth a re-read before
   committing to A, since our sentences are point-mass (Route B's convergence story
   is stronger here than it was for σ-blur).
4. **MirrorBot's non-termination** (if it is ever lifted): base `outcome` is genuinely
   `none` on some matchups and `NonTerminationPolicy` drops it from base-path
   analyses, but **a TauBot always terminates** (a proven-`none` base cell reads as
   not-cooperating and the lift emits a real D). That is a guaranteed coincidence
   divergence needing a deliberate whitelist entry — settle it before lifting, not in
   a failing test.
5. **Metatheory M2**: `.sys` arms are additional to the unpaid `tvote` arms. Decide
   whether M2 stays deferred (and the debt is recorded as compounding) or is paid
   before the surface grows again.

---

## Addendum (2026-08-25, evening) — PrudentBot ported at a SINGLE budget

Colomban's call: the tau zoo represents every bot at ONE shared budget `k`;
base cells that exist only at a staggered budget become whitelisted
budget-staggering divergences, never a second budget in the lift.

* **Row:** `tauPrudentSpec := .search .prove .self .C (.search .prove (.name .defect) .D (.const .C) (.const .D)) (.const .D)`
  — Critch's PrudentBot as a tree. Roster slot `.prudent` BEFORE `.mirror`
  (mirror stays last: its diagonal is the divergent slot). 16 templates.
* **The row is `D` everywhere except `.mirror = C`**, and the mechanism is
  uniform (`Tau/Theorems/TauPrudent/Helpers.lean`): the INNER check
  `probeD (inst T defect)` is an else-play floor for coop/tftPf/dupoc/just/dbot/
  cupodTroll/cimcic/prudent-itself (`nested_plays_D_of_inner`); where it passes
  cheaply the OUTER probe fails — by soundness (defect, tftSim, obot), by a
  watch-cost floor (ebot: its C embeds Prudent's floor-priced D on the defector,
  `prudent_defect_watch_over_budget`), by the else-play floor (guardian), or by
  `ps_botSys_mismatch_false` on the entangled partner (cupod, dimcid). The mirror
  cell is bounded Löb through the binder with the ONE new core rule
  **`Pf.botSysSearchThenSearch`** — the `.sys` twin of `searchThenSearch_t`
  (nested searcher member; inner premise held at budget ≤ k₂) — chained after
  `botSysSimStep` via `implTrans`, `pblt_engine_id_bounded`, both orientations.
* **Column:** every classifier's `.prudent` arm; τ(EBot)'s row gained the
  Löb-gated hypothesis `hpm` (its third watch sees Prudent cooperate with the
  mirror) — supplied by `prudent_mirror_plays_C` in `TauMirror/Phase`.
  τ(Mirror)'s prefix is now 15 slots (`tauOrderInit` ends `.dimcid, .prudent`).
* **Self-play:** `prudent_quine_plays_D` — single-tier prudence is self-defeating
  at one budget, as base `outcome_PrudentBot_vs_PrudentBot = (D, D)`.
* **Certification:** 256 cells / 246 agree / 10 whitelisted (the 6 prior + the
  four staggered cells (Prudent, Dupoc), (Dupoc, Prudent), (Prudent, Just),
  (Just, Prudent) — base `outcome_PrudentBot_vs_DupocBot` and
  `outcome_JustBot_vs_PrudentBot` are stated at `PrudentBot (2k+64)`). No
  missing rows; all 16 phases unconditional.
* **Census kernel:** `no_provable_tailToS_floor` has a 15th hypothesis
  `hbotsyssts` (the nested-searcher bridge; LAST slot, 17 binders) — in the
  D-tail census it is a constructor CLASH (`c0 = C`), in the C-tail census it is
  THE reading rule and is killed by the inner guard's unprovability
  (`no_provable_sysNested_C_tail` takes that as `hinner`).
* **TauTFTPf dropped from the certification (Colomban, 2026-08-25 evening).** It
  is the PROVER reading of TitForTatBot's question, a tau-only variant with no
  base bot, so `BASE_OF` has no entry for it and `direct_kernel_vs_base` compares
  it nowhere (row or hypothesis). Its four "prover-modality floor" whitelist
  entries went with it; the whitelist is now exactly the six budget-staggered
  dagger cells, and the certification is 225/219/6 over 15 templates. The
  prover/behavioral α-gap is still visible — in the kernel-row tests comparing
  `tftPf` and `tftSim` bits — it just is not a base-vs-tau claim.
* **THE PORTING PHASE IS CLOSED AT 16 TEMPLATES (Colomban's decision,
  2026-08-25).** WaryBot, LegibleBot and OptimBot are EXCLUDED, not deferred,
  and the reason is a property of the BASE library, not of the lift:
  - *WaryBot* (`search k (¬(opp plays C vs me)) D C`): five base cells are OPEN
    at large k (OBot, CIMCIC, DIMCID, CupodBot, LegibleBot) — one wall, refuting a
    FLOOR-priced cooperation: the WV valuation census dies on `h_ite`, the
    TailTo-neg census is FALSE (`implK` + `contrapose` manufacture
    `¬(ψ → CA) → ¬CA`), and the cost-floor lever was never built. τ(Wary) meets
    the identical wall against obot/cimcic/dimcid/cupod and its `.sys` partners,
    so an unconditional row is a census research project, and there is no base
    value to certify those cells against.
  - *LegibleBot* (`search kOut (□kIn (me plays C vs opp)) C D`): inherently
    TWO-budget. Base has large-k values for 5 cells only, all at the stagger
    `LegibleBot (2k+64) k`; the other 10 are `_floor` theorems valid only while
    `kOut < |□kIn …|` (small k). At one budget the row is open in base too.
  - *OptimBot*: 6 base cells, three open.
  A future `Mode.proveNeg` / `Mode.proveBox` is a new `Mode` on `search`, not a
  new node (the DSL extension point is unchanged); the precondition is a proven
  single-budget base row, which none of the three has.

## 9. Open questions (decide during implementation, none blocking)

1. `voteHigh_f` — include from day one (cheap else-commits) or add on demand?
   Default: include (mirrors `tsearchHigh_f`, trivial).
2. Cost constant for the peel step — bare `c_node` (proposed: the vote consults
   no oracle, so no `c_guard`) vs a per-entry surcharge. Default: `c_node`.
3. ~~Whether `.tsearch` gets a demo native bot or is deprecated~~ — RESOLVED
   2026-08-18: removed (Phase 4b); a provability-vote native bot is a `tvote`
   over search-wrapped entries.
4. Sub-Löb / low-budget regimes for the vote entries (TauDupoc's entries below
   the Löb threshold): needs ¬Pf cost floors — recorded as future work, same
   status as before the refactor.
5. (Phase 5/DSL) Whether `ι` is `Fin n` or a string-keyed enum; and whether the
   interim instance names survive as `abbrev`s or die immediately after Gate D1.
   Cosmetic; decide at implementation.

## 10. Kill criteria

* If the frozen-`VoteList` subst convention breaks any base-engine defeq
  (Gate 1) in a way `termination_by structural` does not fix → fall back to
  `.bot`-wrapped entries in a `GuardList`-shaped list WITH subst descent
  (strictly more machinery, known-safe pattern).
* If `voteCons_d`'s soundness arm cannot be closed from eval determinism alone
  (it should — no oracle in the path) → STOP and re-derive; do NOT add an
  axiom or a floor. This rule being floor-free is a design pillar; failure
  means the design is misunderstood somewhere.
* If the coincidence check (Gate 5) fails on a terminating large-k cell and
  the kernel side is confirmed → the DEFINITION transcription is wrong, not
  the check; halt and audit against §0 step by step (the TauEBot lesson).
