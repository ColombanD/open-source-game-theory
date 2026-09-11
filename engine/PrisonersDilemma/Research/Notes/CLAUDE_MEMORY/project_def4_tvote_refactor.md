---
name: def4-tvote-refactor
description: Refined Def 4 COMPLETE 2026-08-18 (all phases): tvote action-vote + Spec DSL (bots = spec rows, inst compiler, Gate D1 rfl); tsearch REMOVED; Python certifies Def3≡Def4; next = .sys revival
metadata: 
  node_type: memory
  type: project
  originSessionId: b183cd9a-24de-42a5-9709-1bb395f61fb9
  modified: 2026-08-18T10:51:07.308Z
---

**The refined Def 4, agreed with Colomban 2026-08-18** (executes the 2026-08-13
retraction). Authoritative plan: `engine/PrisonersDilemma/Research/Notes/TAUBOTS.md (condensed 2026-08-26)`.

**The definition (3 steps, confirmed verbatim):** (1) lift base A's code
constructor-by-constructor, `.opp`-wire references become hypothesis-instance
references; (2) `inst(A, δ_B)` = A's ENTIRE base decision procedure encapsulated
at point mass on B (multi-stage bots: all stages inside, only the action leaves);
(3) top-level player plays C iff `Σ{wᵢ : inst(A,δ_Bᵢ) plays C} ≥ θ` — "plays"
read by EVALUATION, never proofSearch at the vote level.

**Locked decisions:**
- **`tvote` constructor** (weighted ACTION-vote over frozen closed Prog entries,
  NO budget arg, subst does NOT descend into entries): the σ-level primitive.
  NOT tsearch (provability-vote = wrong modality, misreads true-but-unprovable
  else-plays) and NOT iteTree compilation (2ⁿ blow-up). `voteCons_d` reads
  "no mass" from the entry's positive D-transcript — atom-tier, NO floor at the
  vote level (floors stay inside instances). **tsearch + GuardList REMOVED
  (Phase 4b, after the tau rebuild)** — tvote subsumes it
  (`tsearch ≡ tvote over .search-wrapped entries`); lost expressiveness =
  frame-dependent weighted guards, never used. hasSearch(tvote) = true
  UNCONDITIONALLY (else atom_complete_searchfree gains a case). No modal Pf
  rules for tvote (players never probed; future trigger = mixed base-vs-tau).
- **Every tau bot = decision vector + shared vote**: τ produces vectors for the
  lifted family; signal-native bots (e.g. "C iff wC > W/2") hand-write vectors —
  first-class, resolves the DSL-vs-hand-written question. DSL deferred to the
  lift-all-base-bots milestone.
- **Zoo restricted (≤1 self-prober) now; `.sys` revival (tag
  taubot-def5-research) is the designated full-zoo route** for the mutual
  self-probe wall (inst(A,δ_B) ⊃ inst(B,δ_A) ⊃ … impossible by containment;
  `.self` cuts only the diagonal).
- Expected results: cooperator boundaries UNCHANGED (θ ≤ wC+wTs+wTp+wL; Dupoc's
  E-floor moves inside the entry); **τ(EBot) = one-sided θ ≤ wTs+wTp+wL, NO
  window** (bits C0 D0 Ts1 Tp1 L1 self0); crowd-exploiter TauEBot + its 33
  cells + all GuardList sigs + iteTree DELETED. New load-bearing lemma: the
  point-mass coherence lemma (player at δ ≡ its instance) — the theorem the
  crowd-exploiter would have failed. Python compare flips to CERTIFYING
  Def3≡Def4 at large k (divergence on a terminating cell = a bug by definition).

**STATUS: THE ROADMAP IS CLOSED — ALL PHASES (1–4b, 5 DSL, 6 Python, 7 docs)
LANDED AND COMMITTED 2026-08-18.** Final state: engine green (3307 jobs), 3
standard axioms, zero sorry, base outcomes byte-identical throughout; `tsearch` +
`GuardList` REMOVED from the language; tau bots are Spec-DSL rows compiled by
`Tau/Spec.lean` (Gate D1: 26 rfl byte-identity checks); Python compare.py
CERTIFIES Def3≡Def4 (kernel 36/36, bits 35/36 + exactly the whitelisted Mirror
cell, 1400 phase cells all attributed). NEXT FRONTIER: the `.sys` revival for
mutual self-probers, landing on the DSL — only the compiler's probed-object
resolution changes. Open debts recorded in the roadmap Phase-7 note: Metatheory
M2 (tvote arms), Zoo.WellFormed + fuel-sufficiency (at the 2nd zoo), sub-Löb
regimes, LegacyS.lean (pre-existing break).

**Post-close addendum (2026-08-18): Tau/InstCerts.lean** — the bit lemmas restated
over `inst Z A T` (the second-era API): three COLUMN theorems (δ_C/δ_D/δ_L, `∀ T`,
one arm per zoo member; each arm = plain `exact` of the Certs lemma, D1 defeq
bridging), the quine + Gödelian pair inst-native, and the behavioral δ_C column
(`inst_coop_plays`). VotePhases rewired: every bits proof is now a COLUMN READ
(`let bC := ps_probe_inst_coop …; .cons (… (bC .coop)) …`) — eBits = two column
reads, the others one. Certs stays the proof layer underneath, untouched. Scope
cut recorded in the header: only CONSULTED columns (a full 6×6 table needs ~15
new floor/certificate lemmas with no consumer). Adding a bot now = one spec row
+ one arm per consulted column.

**THE 9-ZOO (2026-08-18, "lift everything that doesn't need .sys"):** added
TauJust, TauOBot, TauGuardian via the Spec DSL. Stage gained `test : Action`
(recorded extension, first needed by OBot run-testD / Guardian prove-testD);
zoo6/order6 renamed tauZoo/tauOrder. NEW RESULTS, all kernel-checked + Python-
mirrored (81/81): (1) **Guardian's cooperation is NEVER provable** (always behind
its failed punish-search; parametric floor ps_probe_guardCell_false on the
EXISTING botSearcherElse kernel) ⇒ (2) **the prover/behavioral split became an
α-GAP**: tftSim/tftPf rows differ exactly at guardian; modality-split band
pfMass < θ ≤ simMass = (C,D) matrix cell; the old "split is budget-only" test
falsified and corrected. (3) TRUST band eMass < θ ≤ guardMass: ebot defects,
guardian trusts (D,C). (4) Just = Dupoc's bits exactly (norm ≡ self reciprocity
on this zoo), both Löb-gated. (5) OBot: narrowest boundary θ ≤ wC. Mass ladder:
obotMass=wC ≤ eMass ≤ pfMass ≤ simMass=guardMass; dupMass(=justMass) ≤ pfMass.
Generic false-bit lemmas via eval_det landed in Vote (probe/probeD false from
any opposite-play witness — killed the per-shape match-n proofs). EXCLUDED +
why (recorded in Roster): self-probers (Cupod/Prudent/Mirror/Legible/Optim →
.sys), impl-guards (CIMCIC/DIMCID), .neg (Wary), .eq (CupodTroll); **DBot
deferred**: liftable shape but its δ_L cell needs a NEW Exclusion kernel
(frozen probe-first player sim-embedding a floor-priced searcher — the tau
image of no_provable_probeFirst_tail, which is .opp-wired).

**Tau fully self-contained (2026-08-18, final layout):** Theorems/Tau/ moved INTO
Tau/Theorems/ — the whole tau world is one directory (Tau/{Vote,Spec,Roster,Bots/,
Zoo} = definitions; Tau/Theorems/{Helpers,<Bot>/{Helpers,Phase},Columns,Matrix} =
math). Module names PrisonersDilemma.Tau.Theorems.*; NAMESPACES unchanged
(PD.Tau / PD.Theorems.Tau) so all theorem names preserved. Scanner glob:
Tau/Theorems/*/Phase.lean. Side benefit: engine Theorems/ is base-only again.

**Math rearranged base-style (2026-08-18, Colomban):** Tau/Certs + Tau/VotePhases
DISSOLVED into Theorems/Tau/ — `Tau/` is now DEFINITIONS ONLY (Vote, Spec, Roster,
Bots/, Zoo). New math layout: Helpers.lean (shape lemmas + masses) →
TauDupoc/Helpers (quine chain) & TauEBot/Helpers (floor pair) → Columns.lean (the
3 column theorems — aggregate per-bot rows, hence import the bot Helpers) →
<Bot>/Phase.lean ×6 (bits + phase theorem = the per-bot RESULT) → Matrix.lean.
The 13 per-pair vs_ files REVERTED to one Matrix.lean (Colomban's own call:
tau plays are opponent-independent ⇒ a pair file has no pair-local content;
rationale recorded in Matrix header — base keeps per-pair because base proofs ARE
pair-specific). Python scanner retargeted: def4_theorems globs
Theorems/Tau/*/Phase.lean. All statements preserved (15 tau + 78 base), 3 axioms,
zero sorry, coincidence certification still passes.

**Legacy-layer deletion (2026-08-18, Colomban: "only what's used today"):**
Defs.lean, Vectors.lean, InstCerts.lean DELETED — the DSL is now THE definition
path, no parallel hand-closure. probe/probe_subst + SHAPE play-lemmas
(searchProbe_/cascade_/simCopy_plays, over explicit Prog shapes) moved to Vote.lean
(new tau chain: Vote → Spec → Roster → Bots → Zoo → Certs → VotePhases). Gate D1
reinvented as ONE-LEVEL PEEL EQUATIONS in Zoo.lean (inst_*_peel + inst_dupoc_quine:
each rfl-pins one compile step with inst-subterms; composition pins every byte;
they double as Certs' rewrite handles). Certs REWRITTEN over inst with full proofs
(shape lemmas private + columns + quine chain + Gödelian pair + behavioral column);
key tricks: probe_subst in simp sets kills the verbose subst-form haves; term-mode
Pf transcripts elaborate against inst-types via whnf; peel-rw before eval-simp.
All 15 tau statements + 78 base outcomes byte-identical; 3 axioms; zero sorry.

**Per-bot-file reorganization (2026-08-18, post-close, Colomban's layout):** the
tau zoo now mirrors the base-bot layout. `Tau/Roster.lean` (the Tmpl cast — must
precede bot files: tau specs reference by NAME in a shared index, not by importing
terms) → `Tau/Bots/<TauBot>.lean` (ONE FILE PER BOT: spec row + strategy doc; math
stays centralized in Certs/InstCerts per Colomban's choice) → `Tau/Zoo.lean`
(assembly: tmplSpec match + zoo6 + TauBotZ + Gate D1, moved from Spec.lean, which
is now machinery-only/generic). Outcomes split per-pair (base convention):
`Theorems/Tau/<L>/vs_<R>.lean`, 13 files, 15 theorems, VoteMatrix.lean deleted;
coopMass/eMass hoisted public into VotePhases. Root imports each per-pair module
(no umbrella). Adding a bot: roster constructor + bot file + one tmplSpec arm +
InstCerts column arms + its per-pair files. All names/statements preserved; engine
green (3328 jobs), 3 axioms, zero sorry, base outcomes byte-identical.

**Phases 1–4b history (landed same day)** (engine green
3306 jobs, 3 axioms, zero sorry, base outcomes byte-identical throughout).
Phase-3 finding: voteHigh_f as planned was UNSOUND (non-terminating entry sinks the
vote to none; machine-checked MirrorBot counterexample) — repaired with the
cost-indexed `VoteAllPlay` premise (4th mutual inductive). Phase-4 findings: entries
must run `.bot`-FRAMED (= the probe atom's frame) or no Certs lemma applies;
positional `VoteBits` beats valuation functions (term-equality obligations).
tsearch+GuardList removed (Phase 4b); LegacyS.lean was ALREADY broken pre-existing
(30 errors, broke when tsearch landed, outside both lake targets — not our fallout).

**Spec DSL = Phase 5 (spec in TAUBOTS.md (condensed 2026-08-26) §6) — REORDERED 2026-08-18:
runs NEXT (before the Python phase, before .sys/Def-5; rationale: certify the layer
that persists, not the fixed-6 prototype — the DSL changes the public interface).
New execution order: DSL → Python coincidence (Phase 6) → docs/cleanup (Phase 7,
LAST).**

**Phase 6 (Python) LANDED 2026-08-18**: def4.py = source-lift model (spec table
1:1 with Lean tmplSpec; floor STRUCTURAL not stipulated; quine = Löb rule;
mutual-quine wall raises); def4_theorems.py scans VoteBits theorems;
compare.py INVERTED to coincidence certification (kernel 36/36; bits control
25/25, separating 35/36 with exactly the whitelisted Mirror cell; phase sweeps
167/167 divergences attributed via whitelist-patch + α=0 artifact). The
ex-"separating" zoo now CERTIFIES coincidence. 18 new tests; full suite green.

**Phase 5 (DSL) LANDED 2026-08-18**: Tau/Spec.lean (types, instGo/inst compiler,
vecOf, generic vecOf_bits, zoo6 table, TauBotZ), phases+matrix on `w : Tmpl → Nat`,
hand vectors retired; 26 Gate-D1 rfl checks pass first build. DEVIATION recorded:
FUEL not WF-measure (WF defs don't reduce by rfl even at concrete inputs — tested;
D1 is by rfl). Debt: generic Zoo.WellFormed + fuel-sufficiency lemma, due at the
SECOND zoo. Trap: compiled goals display instGo-form ⇒ rw against named instances
fails — use annotated `have` on the named instance + defeq `exact` (2 sites: tftSim
EBot-entry, Dupoc quine). Trigger: Colomban's review — hand-written
vectors/instances are a fixed-6 prototype, O(N²) at scale. Key design points:
Spec = stage list (mode prove/run, target self/name, fire action) + default;
`inst Z A T` compiler with quine emission at the diagonal; TERMINATION MEASURE
(r A + r T, lex s A) whose decreasing_by closes EXACTLY iff ≤1 self-prober — the
mutual-quine wall becomes a compile-time certificate; vecOf + ONE vecOf_bits list
induction replaces all per-bot cons-chains; weights become ι → Nat. What stays
hand-written: ~3N COLUMN bit lemmas (bits factor through probe columns, not N²),
the Löb quine lemma, floors. Gate D1 = rfl byte-identity of all 36 compiled
instances vs the Phase-4 closure. The instance def-chains being "recursive" was a
false alarm — pure naming, rfl-equal to flat trees.

**Vote.lean pruned (2026-08-19, cea2881):** the whole VoteAllVals valuation-function
interface (voteMass, eval_tvote_of_vals, tauPlayer_phase, cons helpers) DELETED —
zero consumers ever; it was the first Phase-4 interface, superseded by positional
VoteBits within hours. Also gone: entry_D_of_not_interp, entry_C_of_pf.
tauPlayer_point_mass KEPT, annotated "intentionally unconsumed" (spec-level result,
consumer = thesis/design review, not proofs). Pruning trap: index/anchor-range cuts
swallowed the live C-idiom shape lemmas (searchProbe_/cascade_/simCopy_plays) that
sat BETWEEN two dead bridges — caught only by the full rebuild; always rebuild after
deletion sweeps even when the audit says zero consumers.

**Generality pass (2026-08-19, roadmap §8b):** `phase_of_bits` in Spec.lean (the
composed master theorem, finally consuming vecOf_bits) + `bitMass` fold in Vote.lean;
all 9 Phase files restated as bit ROW (`<bot>Row : Tmpl → Action`, 9 explicit arms —
wildcards risk missing equation lemmas) + witness lemma (`∀ T`, match arms = old
chain slots) + phase via phase_of_bits; the 9-deep .cons chains are GONE. CONSTRAINT:
the `<bot>Bits` literal lists are scanner-facing (app def4_theorems.py) — statements
byte-stable, now one-line vecOf_bits corollaries (mapped row = literal list by defeq).
Regime masses stay literal abbrevs (Matrix's `simp only [mass]; omega` needs sums);
bitMass reduces to them via the same simp step (NOT rfl — `0 + x` from D-slots isn't
defeq to `x`). Step 3 = SCHEDULED debt (roadmap §8b): Zoo.WellFormed + fuelFor +
fuel-stability lemma, due at the second zoo.

**9-zoo coincidence extension CAUGHT a modality infidelity (2026-08-19):** base EBot
is a SIMULATOR (.sim watches) but TauEBot used prove stages since 2026-08-11 —
invisible until Guardian's floor separated the modalities. FIXED: run-mode spec
(faithful lift); eMass now includes w .guardian; eMass/pfMass incomparable (bands
restated). Forced the EMBEDDED-floor census `no_provable_botRunCascade_C`
(TauEBot/Helpers) — the deferred DBot-lift kernel, now delivered: atom killer walks
bot→ite_f→sim→bot→search_f, no inner-guard hypothesis. WHITELIST now 2 cells:
(TauEBot,TauEBot) Mirror truncation + (TauTFTPf,TauGuardian) prover-modality floor
(BASE_OF's "twins coincide at large k" FALSIFIED — holds floor-free only). Full-zoo
certification: 81 cells, 79 agree + 2 whitelisted. Python decide unchanged (floored
run-consultation already computed it). Lesson: extend the coincidence zoo whenever
the tau zoo grows — it catches transcription drift on first contact.

**DBot lifted 2026-08-19 — 10th template, last non-.sys bot.** Unblocked by
`no_provable_botRunStage_C` (single-stage twin of the EBot embedded-floor census).
Spec `⟨[⟨.run, .name .defect, .C, .D⟩], .C⟩`. NEW RESULT: **τ(DBot) punishes
itself** — its own δ_D instance TRUSTS the defector, and trust-toward-a-defector is
its fire condition; dbotMass excludes w .coop AND w .dbot (behavioral analogue of
single-tier PrudentBot self-defeat; base DBot-vs-DBot = (D,D) agrees). Certification
100 cells / 98 agree / 2 whitelisted — DBot added ZERO divergences. Traps hit:
TAU_ORDER + LEAN_SLOT + TEMPLATES are THREE separate tuples (all must grow); a
`rw [inst_X_peel]` rewrites frame slots too — use `rw [show … from …] at h ⊢`;
adding a template forces every other bot's row/witness/bit-list AND every regime
mass to be re-checked (simMass/eMass do NOT gain the new slot — their rows read D
there). Remaining: 5 self-probers (.sys) + 4 non-fragment bots.

**.sys SCOPED (2026-08-20, roadmap §8c) — KEY FINDING: the 5 "self-probers" are FOUR
different blockers.** Only CupodBot is unblocked by .sys alone (spec
⟨[⟨.prove,.self,.D,.D⟩],.C⟩); PrudentBot needs .sys + NESTED targets (opp-vs-third-party);
OptimBot needs .sys + SELF-SIDE probes (.plays .self .opp); MirrorBot (raw .sim, not a
cascade) and LegibleBot (.box modal guard) do NOT need .sys at all — they belong with the
4 non-fragment bots. RECOMMENDATION recorded: do fragment extensions FIRST (6 bots, no
engine tax) before reviving .sys (1 bot, standing tax + compounds unpaid Metatheory M2).
Also: Def-4 needs strictly LESS than archived Def-5 — sentences stay point-mass, measured
entanglement is ONE 2-cycle (dupoc↔cupod), so the live mutual_pblt engines likely suffice
and vector2_full_pblt_engine (already in Base/Loeb) is not needed until ≥3 self-probers.
Base-matrix openness is a PYTHON-only constraint (Lean never reads base theorems);
measured: Prudent/Mirror/Legible join cleanly, Cupod/Optim have holes — so the DSL and the
matrix disagree about which bot is easiest. Archived impl at tag taubot-def5-research
(cherry-pick will NOT apply — predates tvote/VoteAllPlay/DSL).

**CupodTrollBot lifted + §8c CORRECTED (2026-08-20).** Gate D1 refused the CIMCIC row:
**CIMCIC is a SELF-PROBER** (its `.impl` guard mentions BOTH .self and .opp), as are
DIMCID and WaryBot. RULE TO REMEMBER: the connective decides the FRAGMENT, the PRONOUNS
decide the .sys question — independent axes; §8c's "six fragment bots" was a miscount,
the real number was ONE. Landed: Mode.proveImpl (correct, unused until .sys) +
Mode.proveEq + τ(CupodTroll), the 11th template and the only non-.sys-blocked bot left.
It is constant-C here (its target CupodBot is absent → standing regression test for the
.sys milestone) and the zoo's SECOND FLOOR BOT (C behind a failed .eq search) → 3 new
whitelisted cells, all the Guardian mechanism; certification 121 cells / 116 agree / 5
whitelisted. Two tests legitimately falsified + restated (TFT split is at the FLOOR bots
now, not Guardian alone; obotMass = wC + wCupodTroll). BACKLOG NOW: 9 bots, 8 need .sys;
the fragment-only backlog is EMPTY, which INVERTS the fragment-first recommendation.
Trap: `rw [inst_X_peel]` rewrites frame slots too — use `conv_lhs => arg 4; rw [...]`.

Related: [[tau-def4-tsearch-milestone1]] (retraction context, trap list),
[[def5-sys-binder-route-a]] (the shelved .sys machinery to revive).
