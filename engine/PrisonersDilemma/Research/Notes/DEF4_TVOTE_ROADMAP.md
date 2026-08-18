# Def-4 refined: the source lift + `tvote` action-vote — refactor roadmap

*Status: plan fixed 2026-08-18 (Colomban + review). Supersedes the σ-player layer of
`TAUBOT_TRANSPARENCY_DESIGN.md` Part III (whose retraction section this executes).
The instance layer of milestone 1 is REUSED; the four ad-hoc top-level player
shapes are REPLACED by one uniform action-vote.*

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

## 6. Phase 5 — Python: from separation-hunt to coincidence-certification

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

## 7. Phase 6 — docs, memory, cleanup

* `TAUBOT_TRANSPARENCY_DESIGN.md`: Part III gets a one-line pointer to this
  note as the executed redefinition (full cleanup of that note is a SEPARATE
  later task — agreed 2026-08-18).
* Memory: update the Def-4 milestone note; record the locked decisions.
* M2 debt ledger: `Metatheory` restoration owes `tvote` arms (`enumProg` over
  `VoteList`, `evalG` peel with entry evaluation, gate walkers) and NO LONGER
  owes any `tsearch` arms (Phase 4b removes them before M2 starts) — a net
  shrink of the M2 surface. Still deferred.

---

## 8. Open questions (decide during implementation, none blocking)

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

## 9. Kill criteria

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
