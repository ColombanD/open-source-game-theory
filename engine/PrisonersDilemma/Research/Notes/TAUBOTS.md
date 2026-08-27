# TauBots — graded transparency over the zoo

*Condensed 2026-08-26 from three notes (`TAUBOT_TRANSPARENCY_DESIGN.md`,
`DEF4_TVOTE_ROADMAP.md`, `DEF5_SYS_BINDER_ROADMAP.md`, all deleted; git has them).
Status: **the porting phase is CLOSED at 16 lifted templates, every phase theorem
unconditional, no stipulations; since 08-27 every row is a linted, exported `RowSpec`
theorem, and the roster holds a 17th, NATIVE member — ConfidenceBot, the first tau
player that is the lift of no base bot (§1, "Native players"); certification
256/256/0.** What is left is debt, not design.*

---

## 1. The definition

**Partial transparency as identity uncertainty.** A bot receives a **signal** — a
distribution `(B₁…Bₙ; p₁…pₙ)` over the zoo — instead of the opponent's source. The
blur lives in the WEIGHTS, never in the programs: every hypothesis is exact zoo
syntax backed by a proven matrix cell, which is what prover bots need. This is a
Harsanyi type space with the zoo as types, truncated at level 1, no common prior,
and *intensional* types (they fix the opponent's term, so behavioral twins are
separable by the Löbian fragment).

**Def 3 (the semantics).** `TauA(α)(sig) = C iff Σ{pᵢ : A's action in outcome(A,Bᵢ) = C} ≥ α`
— A best-responds to each hypothesis with its own decision procedure, then votes
once over its own intended actions (expectation-then-threshold; no probabilistic
agents). Anchor: at a point mass the tau tournament IS the base matrix; at the
uniform signal every bot is unconditional (classical opaque PD). So the family
interpolates Critch's OSGT ↔ classical game theory.

**Def 4 (the implementation, coincides with Def 3).** The uniform structural
source lift τ: (1) lift A's code constructor by constructor, every severed `.opp`
reference becoming the hypothesis's tau instance; (2) `inst(A, δ_B)` = A's ENTIRE
lifted decision procedure at point mass on B; (3) ONE weighted vote over the true
PLAYS of the instances (`Prog.tvote`). `proofSearch` appears only where A's own
code has it. At large k on terminating cells Def 4's bit equals Def 3's, so the
`(t, α)` phase diagrams coincide; Def 4 adds what Def 3 stipulates — Löb
thresholds, floor cells, sub-Löb regimes, cost intensionality — as theorems.

**Two dials, never conflated.** `t ∈ [0,1]` = transparency (normalized mutual
information of the signal, inverted per σ-family by bisection; `t = 0` is a finite
internal temperature so the knife-edge stays observable). `α` = the agent's caution.

**σ families** (`tau/channels.py`, `tau/syntax.py`): *behavioral* (softmax over
Hamming distance on own-action rows = the Bayes posterior of a binary symmetric
channel), *ε-uniform* (the structureless control), *syntactic* (normalized
Zhang–Shasha edit distance on parsed `Prog` ASTs; deliberately erases search
budgets and referenced bot bodies). The two structured channels correlate at only
+0.16 — Dupoc/Cupod are syntactic near-twins and behavioral opposites.

**Conventions in force.**
- Open base cells: restrict the zoo; a stipulation may fill only a genuine hole and
  the loader RAISES if it shadows a proven cell. Currently NO stipulations exist.
- Proven `none` is a fifth cell state `"N"`, read pessimistically (`cooperates`
  tests `== "C"`); a TauBot therefore always terminates — swept matrices never
  contain `N`.
- Threshold `≥ α`; sweeps step BETWEEN `alpha_breakpoints`. In Lean, `θ = ⌈α·W⌉`
  over integer weights.
- **One shared budget `k` for the whole tau zoo — and, since 08-27, for the base cells
  too.** The four pairs whose cooperation exists only at a stagger (`PrudentBot (2k+64)`
  vs Dupoc, `PrudentBot (2k+64)` vs Just, `JustBot (4j+100)` vs Troll, `DupocBot (2k+64)`
  vs Troll) now have their shared-budget value AS the cell (`(D,D)`, `(D,D)`, `(D,C)`,
  `(D,C)`); the staggered results are `*_staggered` non-cell theorems. The tau
  `WHITELIST` is therefore EMPTY and the certification is 225/225/0. In the base export
  the dagger has exactly ONE cause, a staggered budget — now only the two-tier
  LegibleBot/OptimBot cells, which have no shared-budget theorem.
- **Every row is a `RowSpec` theorem** (`Tau/RowSpec.lean`, 08-27):
  `@[tau_row] theorem <t>RowSpec : RowSpec .<t> tauOrder <t>Row` =
  `∃ k₂, ∀ k > k₂, ∀ T ∈ order, ∃ N, eval N (.bot I) (.bot I) I = some (row T)` with
  `I = inst (tauZoo k) <t> T` — unconditional, floors and Löb gates discharged
  inside; τ(Mirror)'s over `tauOrderInit`. `Tau/Lint.lean` validates it (literal
  template and order, row `whnf`-evaluated to bits, name `<template>RowSpec`, no
  hypotheses) and `#check_tau_rows` (in `lake build`) is a ROSTER census — one row per
  `Tmpl` constructor. `lake exe export_outcomes` writes `app/generated/tau_rows.json`;
  `tau/def4_theorems.kernel_bits` reads ONLY that file.
- Tau players are `.opp`-free (extensionally constant given the signal); probe atom
  `probe I := .plays (.bot I) (.bot I) .C`, `.bot`-frozen; vote entries frozen.
- Guard order: Löbian/entangled guards LAST.

**Native players (08-27) — a tau player is a (TEST, AGGREGATOR) pair.** The
per-hypothesis TEST is a `Spec` (what the player decides at point mass on each
hypothesis; it is ALL an opponent's instance ever sees, since instances are point
mass by construction — the anchor). The AGGREGATOR turns the weighted per-hypothesis
bits into one play. Every lift has aggregator `sum ≥ θ` (`tauPlayer`, the C-mass); a
NATIVE player has some other aggregator, and is therefore the lift of NO base bot.
The criterion is **linearity**: a lift's play is `θ' ≤ bitMass w r`, a threshold of a
quantity LINEAR in the signal; any aggregator that is not is native, and three
signals witness it (`2·δ_coop`, `δ_coop + δ_tftSim`, `2·δ_tftSim` — the middle mass
is the average of the outer two, so "C, D, C" is impossible for a threshold of a
linear mass). The circular reading "cooperate iff there is a heavy hypothesis I'd
cooperate with" is NOT a definition — at point mass the weight condition is vacuous
and "I'd cooperate" is an ungrounded fixpoint; the test must be a concrete probe of
the hypothesis, and choosing it fixes the point-mass collapse.

*ConfidenceBot* = (Dupoc's test, **`max ≥ θ`**): "cooperate iff some SINGLE
hypothesis carrying at least θ of the signal on its own provably cooperates with me"
— the ambiguity-averse Löbian cooperator, which makes the headline question literal:
its cooperation with τ(Dupoc) switches off exactly when the channel's confidence on a
Löb-cooperating hypothesis drops below θ, however high the expected cooperation.
Machinery: `Tau/Vote.lean::maxPlayer` — a chain of ONE-entry `.tvote`s (a one-entry
vote fires iff its entry plays C and `θ ≤ w`; no new primitive), `maxHit`,
`eval_maxPlayer_of_bits`, `maxPlayer_phase_bits`; `Zoo.lean::ConfidenceBotZ`;
`Tau/Theorems/TauConfidence/Phase.lean::tauConfidence_phase` (+ the readable `'`
form) and **`confidence_not_linear`** (the three-signal witness, for every row and
threshold). Rows: it IS a roster slot (`.confidence`, before `.mirror`), because
`inst` depends only on specs and `tauConfidenceSpec = tauDupocSpec`: in the
HYPOTHESIS role ConfidenceBot is Dupoc, by `rfl` (`inst_confidence_eq_dupoc`,
`inst_at_confidence_eq_dupoc`, `inst_confidence_quine`) everywhere except the
`confidence × dupoc` pair — two Dupoc-spec self-probers in the symmetric system
`cfdSys`, the same term in both orientations, closed by the simplest mutual Löb in
the zoo (`TauConfidence/Helpers.lean`: both cross-readings are `sys_cross_C_at`) — and
the `.just` slot, which probes that system. So `confidenceRow = dupocRow`
(`confidenceRow_eq_dupocRow`), every other row's 17th bit is its `.dupoc` bit, and the
port cost one new Löb lemma plus one-line arms (the `.dupoc` arm through the bridge).
Python: `NATIVE_PLAYERS` (`tau/matrix.py`) — a zoo member named there is loaded as a
CLONE of its base's cells (`Cell.clone_of`) and played with its own aggregator
(`play.decision_mass` → `max_mass`); `BASE_OF["TauConfidence"] = "DupocBot"` makes
the certification check the clone against the base matrix (256/256/0). Zoo
`default+confidence`. Consequence to report, not prune: as a hypothesis it is a
behavioral AND syntactic twin of DupocBot (its source, to a partial reader, is its
instance's), so the distance-based σ families have a ceiling below 1 on that zoo and
split mass between the twins for `t < 1` — which is precisely what ambiguity aversion
costs a Löbian cooperator (with `θ > ½` it cannot cooperate with Dupoc or itself
under behavior-blur); the `epsilon` family is identity-based and unaffected.

---

## 2. What landed (chronological)

| Date | Landed |
|---|---|
| 07-31 | Design fixed: Def 3 chosen over Def 1 (tau hypotheses — ill-typed, ungrounded recursion) and Def 2 (reciprocity probe — a FairBot family, not a lift). |
| 08-03/04 | **v1a Python explorer** (`app/src/pd_runner/tau/`): σ/α sweeps, MI dial, phase diagrams, report + UI button, named zoos (`ZOOS`), the `N` state, AST syntactic family (replacing a constructor-count metric). |
| 08-11 | Def-4 milestone 1: `.tsearch` provability-vote, 5-bot zoo, first Lean tau matrix. Finding that survived: **the prover/behavioral split is a budget-phase gap, not an α-gap** (TauDupoc needs the Löb threshold, TauTFTSim ~nothing). |
| 08-12/13 | Faithfulness audit: EBot's exploiter cascade lifted properly; the floor lemma `no_provable_botSearcherElse_tail`. **Retraction**: the σ-player TauEBot thresholded each cascade stage — a "crowd-exploiter", not τ(EBot); Def 4 correctly read COINCIDES with Def 3. |
| 08-13/17 | Def 5 (σ-probing, blur as common knowledge) mechanized through M1 via the `.sys` binder (`outcome_TauDupocSys_vs_TauDupocSys = (C,C)`), then **shelved and reverted** (tag `taubot-def5-research`). Kept: the size-parametric vector Löb engine `vector2_full_pblt_engine` (`Base/Loeb.lean`) and `Research/Spikes/sysLob/`. |
| 08-18 | **The refactor**: `Prog.tvote : VoteList → θ → Prog → Prog → Prog` (weighted ACTION-vote over frozen instances; atom-layer only, no floors at the vote) replaces `.tsearch`+`GuardList` (removed). **Spec DSL** (`Tau/Spec.lean`): bots are spec rows compiled to instance vectors; Gate D1 = compiled closure `rfl`-identical to the hand terms. Python flipped from separation-hunt to **coincidence certification** (kernel bits vs Def-3 bits). |
| 08-19 | Generic phase theorem `phase_of_bits`, masses as folds. Certification caught a real infidelity — base EBot is a SIMULATOR, the tau row had used `prove` — forcing the embedded-floor census (`no_provable_botRunCascade_C`); DBot lifted (τ(DBot) punishes itself, as base `(D,D)`). |
| 08-20 | `Mode.proveImpl`, `Mode.proveEq`; CupodTroll lifted. Gate D1 corrected the plan: **pronouns decide `.sys`, the connective decides the fragment** — a guard mentioning `.opp`'s view of `.self` is a self-prober whatever its connective, so 8 of 9 remaining bots needed the binder. **`.sys` revived for Def 4** (`ProgList`/`.sys`/`.selfIdx`, `sysClose`, lazy-unfold eval, `PlaysProof.sysStep`, τ-closure with `ProgList.transpose`; compiler `sysGo`; `Pf.botSysSearchStep` — readable player shape, ~25 census call sites). CupodBot lifted. |
| 08-21 | **Entangled cells fall**: wrapped emission `.bot (.selfIdx j)`; `no_provable_botSysSearcherElse_tail` — anti-aligned 2-cycles are decided by the FLOOR (both defaults, no bistability); aligned pairs by mutual Löb through the binder. **Alignment rule**: an entangled pair cooperates-by-Löb iff each guard target equals the other's fire action. CIMCIC lifted; layer total, hypothesis-free. Three base cells transplanted from tau closures. |
| 08-22/24 | DIMCID (`Mode.proveImplD`; a Löb fixpoint on DEFECTION), Mirror (honest `none` regime above its prefix mass). **Spec DSL became a TREE** (`Spec = const | sim | ite | search`, `Prog` with a `Target` hole) — τ-bots are written as their base source. `Matrix.lean` removed: the per-bot `Tau/Theorems/<Bot>/Phase.lean` theorems ARE the matrix (players `.opp`-free ⇒ a match is two independent plays). |
| 08-25 | Tower census `Base/TowerCensus.lean` closes DIMCID's row. **PrudentBot at ONE budget** (`Pf.botSysSearchThenSearch`, the nested-searcher `.sys` reader; row D everywhere but the mirror). The four `_samek` base theorems; the last stipulation (`outcome_PrudentBot_vs_CupodBot`) falls; TauTFTPf (no base bot) compared nowhere; census library unified into `Base/Exclusion.lean`. **Porting CLOSED at 16.** |
| 08-27 | **Tau rows linted and exported.** `Tau/RowSpec.lean` + `@[tau_row]` (registry in `Outcome/Attr.lean`) + `Tau/Lint.lean` + `tau_rows.json`; the 16 literal `VoteBits` `*Bits` theorems deleted (`RowSpec.bits` derives them); `tauOrderInit`/`tauOrder_eq` to `Roster`, `vecOf_append` to `Tau/Spec`. **Finding that forced it**: the rows the app regex-scanned were CONDITIONAL on Löb-gated hypotheses (`hquine`, the entangled cells) discharged only in the phase theorems — invisible to a source scanner. Certification reproduced byte-for-byte (225/219/6), then **225/225/0** once the four staggered base cells became their shared-budget values (`*_staggered` companions keep the cooperative results; the whitelist is EMPTY). Consequence in Python: single-tier PrudentBot is behaviorally DefectBot at one budget (its only same-`k` cooperation is with Mirror), and without its column GuardianBot ≡ TitForTatBot — both left the DEFAULT zoo by the twin policy (9 bots: Coop, Cupod, CupodTroll, DBot, Defect, Dupoc, EBot, OBot, TFT; ceiling 1.0). The EGT headline was re-run the same day on the 9-bot zoo and SURVIVES (Dupoc uniquely stochastically stable at t = 1, 27→56→82→88% with selection). The four staggered results stay visible: `@[outcome_companion]` theorems, exported beside the cells and rendered `(D, D) ⇄ (C, C)` (BUDGET-SENSITIVE) in the matrix, with a hover note naming both theorems and the exact budgets. Same day in base: `OutcomeSpecEx` and `OutcomeSpecIf` retired (fuel determinism + structural totality, `Base/Helpers.outcome_at_of_ex`), so the base template is ONE head. |

| 08-27 (later) | **ConfidenceBot — the first NATIVE player** (§1 "Native players"): roster slot `.confidence` with Dupoc's spec; `maxPlayer` in `Tau/Vote.lean`; `cfdSys` mutual Löb (`TauConfidence/Helpers`); `confidenceRow = dupocRow`; `tauConfidence_phase`, `confidence_not_linear`; every other row's 17th arm is its `.dupoc` arm through the `rfl` bridges. Trap met: the threshold `max`-towers in the phase theorems are case-split by `omega` (2ⁿ) — eleven of them timed out; they are SUMS now (Mirror, Dupoc, Just, Confidence). Python: `NATIVE_PLAYERS`, cell clones, `decision_mass`, zoo `default+confidence`; certification 256/256/0. |

**Live layout.** `Program.lean` (`.tvote`, `.sys`, `.selfIdx`); `Tau/Roster.lean`
(17 slots incl. the native `.confidence`, `tauOrder`/`tauOrderInit`), `Tau/Spec.lean` (DSL + compiler, `instFuel = 16`),
`Tau/Vote.lean`, `Tau/Zoo.lean`, `Tau/RowSpec.lean` (the row template), `Tau/Lint.lean`
(validator + roster census), `Tau/Bots/Tau<Bot>.lean`,
`Tau/Theorems/<Bot>/{Helpers,Phase}.lean` (`Phase` = `<t>Row`, `<t>Row_plays`, the
tagged `<t>RowSpec`, `tau<T>_phase`), `Tau/Theorems/Columns.lean`; censuses in
`Base/Exclusion.lean` + `Base/TowerCensus.lean`; the shared gate `Outcome/Check.lean`
and exporter `Outcome/Export.lean`. Python: `tau/matrix.py` (`ZOOS`, `BASE_OF`),
`tau/def4_theorems.py` (reads `app/generated/tau_rows.json`, digest-checked),
`tau/compare.py` (`WHITELIST` EMPTY since 08-27), `sweep/report/
signal/channels/syntax/play`. EGT (`egt/`) consumes tau tournaments at fixed `(t, α)`.

**Headline findings.** Def 4 ≡ Def 3 at large k (certified, not assumed). A tau
player is (test, aggregator); lifts are exactly the linear-threshold aggregators, and
ConfidenceBot (max) is provably outside that class while being Dupoc as a hypothesis. The
prover/behavioral split is a budget gap. Floors, not fixpoints, decide anti-aligned
Löb pairs. τ(CIMCIC)'s row equals τ(Dupoc)'s: conditional and Löbian cooperation
coincide on this zoo by different mechanisms. Three floor bots (Guardian,
CupodTroll, Cupod) are where TFT's prover and behavioral readings separate.

---

## 3. Dead ends (do not retry)

- **Def 1 / Def 2** — see the 07-31 row. **Def 5 σ-probing** is parked, not dead:
  Route B (belief-order tower, no language change) is the cheaper revival.
- **The σ-player TauEBot** (θ inside the cascade). Its window / `(D,D)` self-play /
  "45/56 diverging cells" describe the crowd-exploiter — never cite as Def-4 results.
- **`.tsearch` provability-votes** — wrong modality (misreads true-but-unprovable
  else-plays); `tvote` subsumes it. **`iteTree` compilation** — 2ⁿ blow-up.
- **Constructor-profile syntactic distance** — the "DBot/TFT are syntactic twins"
  claim was a metric artifact.
- **Fragment-first ordering** (the 08-20 scoping note) — built on miscounting
  self-probers; only CupodTroll was ever fragment-only.
- **The τ-transposition route inside `.sys`** — the binder makes the pair one
  object indexed by position, τ̂ maps it to a DIFFERENT system; the base red-cell
  argument needs "same program, two actions" and has no analogue here.
- **Cheap Cupod self-defection from the `search_f` floor** — that floor excludes
  the ELSE-play; the guard atom is the THEN-play. The kernel caught it.
- **TailTo-`.neg` census** is FALSE (`implK` + `contrapose`), which is why WaryBot
  is excluded. **Single-`.self` encodings of mutual systems**; **same-fuel list
  evaluation** (compiles by WF recursion, kills `rfl` — `termination_by structural`).
- **Adding a READABLE player shape** (`.bot (.sys …)`) costs ~25 census sites;
  an unreadable one (`tvote`) costs nothing. Budget accordingly.

---

## 4. What is left

**Debts (recorded at their sites).**
1. **Metatheory M2** — `Decidability/` has NO `tvote`/`sys`/`selfIdx` arms; the
   target is unpinned from the default build (`lakefile.toml`) and the certified
   outcome-prepass cannot see tau terms. Compounding since 08-11.
2. **`Zoo.WellFormed` + computed fuel** — `instFuel = 16` is a hand constant;
   Gate D1 is the certificate. Due when a SECOND zoo instantiates the DSL
   (`probeDepth`, `fuelFor`, fuel-stability lemma, decidable well-formedness).
3. **`Research/Spikes/unified_pf/LegacyS.lean`** broken since the first tau
   constructor landed (not in the build).
4. **Sub-Löb regimes** for the vote entries (need `¬Pf` cost floors).
5. **`tau/syntax.py` cannot parse `.tvote`** — a native player's OWN source (the
   `maxPlayer` chain) is not readable by the syntactic family; it currently presents
   its base's source (its hypothesis-role instance), which is the semantically right
   reading for the channel but should be a documented choice, not a parser gap.
6. **The ConfidenceBot experiments.** First EGT sweep of `default+confidence`
   (08-27, behavioral family, 6×6 grid → 17 matrices, 186 s), Moran small-mutation
   limit, (M, β) ∈ {10,50,100}×{0.01,0.1,1}:
   * `t = 1`: ConfidenceBot and Dupoc TIE (the anchor — identical at point mass),
     the pair holding 42→70→88→92% of the long run with selection, DefectBot ≤ 4%.
   * Under blur, `t ∈ [0.2, 0.6]`, α ∈ {0.45, 0.62, 0.8} (and α = 0.3 at `t = 0.4`):
     **ConfidenceBot is UNIQUELY stochastically stable** — 85–93% of the long run at
     strong selection while Dupoc collapses to 1–4%. The ambiguity-averse Löbian
     cooperator beats the risk-neutral one once identities blur: the sum player is
     fooled into cooperating with blurred exploiters, the max player is not.
   * The exception band — `(t = 0.4, α = 0.45)` and `t ≥ 0.6, α = 0.62` (one matrix,
     `65dc50f5aba3`) — flips to {Dupoc, TitForTat} stable with ConfidenceBot at
     9–13%: at moderate blur and moderate caution the single-hypothesis requirement
     costs more cooperation than it saves. Non-monotone in both dials; map it.
   * `t = 0`: ConfidenceBot is an unconditional defector for α > 1/|zoo| (no
     hypothesis carries α alone), so it ties with {DefectBot, OBot} (α = 0.3) or joins
     the 4/5-way ties with Dupoc/EBot (α = 0.45/0.62).
   Caveat: behavioral family ⇒ Dupoc/Confidence are twins with mass split for
   `t < 1`; re-run under `epsilon` before citing the exception band. The isolating
   `(t, α)` curve (ConfidenceBot vs τ(Dupoc), same bits) is still to be plotted.

**Open conventions.**
5. ~~Canonical budget per pair~~ — **decided 08-27: the cell is the shared-budget
   value.** Staggered cooperation is a `*_staggered` companion theorem, not the cell;
   `_samek` is gone.
6. ~~Tau phase theorems sit outside the export~~ — **decided 08-27: a separate
   template on the same machinery.** Rows are `RowSpec`/`@[tau_row]`/`tau_rows.json`,
   not `OutcomeSpec` cells (a row is 16 plays under one budget, not a pair). The
   `tau<T>_phase` theorems stay human-facing corollaries and are not exported. Left
   open only: the rows' fuel is still `∃ N` per `(k, T)` — a literal pad (as the base
   cells now have) would be the `play_at_of_ex` move again, cosmetic until a consumer
   needs it.

**Excluded by decision (08-25), reason = the BASE library, not the lift.** WaryBot
(five base cells open at large k, the `.neg` refutation-floor wall), LegibleBot
(inherently two-budget `.box` guard), OptimBot (three open base cells). A lift
would be a new `Mode.proveNeg`/`proveBox` on `search`; precondition is a proven
single-budget base row, which none has.

**Not needed, recorded.** A system-level τ-argument (`.sys defs i` vs
`.sys defs.transpose i`); the n-ary `Formula.diag` (poly(n) Löb constants);
Def 5 / TauTFTPf's return via the vector engine.
