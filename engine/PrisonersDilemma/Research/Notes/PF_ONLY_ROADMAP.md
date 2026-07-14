# Roadmap — making `Pf` the ONLY proof system `S`

**Date**: 2026-07-14. **Decision record**: `PF_REPLACEMENT_ASSESSMENT.md` priced full
replacement and recommended coexistence; the decision is now to REPLACE — retire
`Derivation`/`Provable`, make the unified `Pf` the one proof system the oracle consults.
This roadmap plans that migration, incorporating everything the assessment and the two
spikes established. The assessment's findings become the plan's mitigations, not
objections:

* the mutualization regression and its cure are machine-checked
  (`Research/Spikes/unified_pf/PfMutualInductSpike.lean`) — `PfM.induct` is the ship-ready
  template for the day-one named eliminator;
* the coexistence layer (`PrisonersDilemma/Pf.lean` + `pf_iff_provable`) is the migration's
  safety net: until the final flip, every port can be cross-checked against the old system
  through the iff;
* the demo ports (`PfEngineSpike.lean`) are the pattern catalogue for Phase 3.

**Measured blast radius** (2026-07-14): 14 files import `PrisonersDilemma.Derivation`
directly; 16 engine-proper files mention `Provable`; engine proper (Base/ + Theorems/)
≈ 7.1k lines; Metatheory ≈ 16k lines (9 of 14 modules speak the gated mirror triple, 90
`Derivation` references). `ComputableEval/` no longer exists on disk (CLAUDE.md row is
stale — delete it in Phase 5; nothing to port). The Python pipeline embeds
`Derivation.lean`, `Program.lean`, `BaseTheorems.lean` into the proof agent's system
prompt BY FILENAME (`app/src/pd_runner/llm/prompts.py`) — keep those filenames and the
app follows the migration automatically.

---

## 0. Invariants (hold at the end of EVERY phase)

* `lake build` green on the migration branch at each phase boundary (phases = commits;
  the only intentionally-red window is inside Phase 1's single commit).
* **Axiom audit**: everything rests on Lean's 3 standard axioms — no new axiom, ever.
  A `#print axioms` sentinel file per phase.
* **The golden statements**: every `outcome_*` / `llm_outcome_*` theorem statement is
  byte-identical before and after (they mention `play`/`outcome`, never `Provable`).
  Phase 0 dumps the inventory; every later phase diffs against it. This is the
  compilation-==-correctness regression check for the whole migration.
* **Semantic anchor**: until Phase 4 deletes the old system, the coexistence iff
  (re-proved against the frozen legacy copy, see Phase 1) certifies the new oracle decides
  THE SAME relation — `proofSearch` behaviour provably unchanged, not just re-tested.

## 1. Design decisions — **SETTLED 2026-07-14 (Phase 0)**; recommendations adopted as-is

* **D1 — the name.** The unified type keeps the name **`Pf`**; `Provable` is retired
  (theorems rename `Provable_sound → Pf_sound` etc., pure grep). Rationale: `Pf` is
  already shipped and self-describing ("proof term, budget k"); reusing the name
  `Provable` for a different constructor set invites silent confusion in old notes and
  papers. Optional flourish: notation `⊢[k] φ` for `Pf k φ` for the paper.
* **D2 — the gates on ex-`Derivation` cuts** (the one real THEORY decision, assessment
  §2a). In the gated mirror, the merged `mp`/`implTrans` carry the gate where
  `Derivation.modusPonens`/`hypSyll` inside `struct` were gate-free. **Gate uniformly**
  (option a): one rule set, one census; the zoo's ex-`Derivation` cut formulas are
  pool-program plays-atoms, exactly the instance-gate shape, so T54 re-certifies —
  but that re-certification is a Phase 4 deliverable, not an assumption. Rejected:
  conditional gates (re-introduces the two-tier structure the merge removes).
* **D3 — sequencing vs the open conjecture (universal closure).** Phase 4 rewrites the
  very trees the conjecture quantifies over; any partial progress on old trees is lost.
  **Restate the conjecture over `PfG` at the END of Phase 4 and hunt it there** — the
  unified grammar (no `struct` boundary, single-induction skeleton via `Pf.induct`) is a
  strictly better substrate for the closure proof. Do NOT run Phase 4 and a conjecture
  hunt concurrently.
* **D4 — file layout.** Keep the FILENAMES `Derivation.lean` (content becomes the new
  mutual block; header retitled "the proof system `S`") and `Dynamics.lean` through
  Phases 1–4: 14 importers and the app's prompt embedding stay untouched. Optional
  Phase 6 rename (`Derivation.lean → ProofSystem.lean`) is pure cosmetics — decide then.
* **D5 — what happens to today's coexistence module.** `PrisonersDilemma/Pf.lean`'s
  inductive moves into `Derivation.lean` (mutualized); its Löb engines move to
  `Base/Loeb.lean` (dropping the `_pf` suffixes, REPLACING the old engines); the
  round-trip theorems (`pf_of_provable` etc.) die with `Provable` — except during the
  migration itself, where they serve as the cross-check (Phase 1).

## 2. Phase plan

### Phase 0 — preflight (on the CURRENT green build) — ✅ **DONE 2026-07-14**
1. ✅ Branch `pf-only` (base commit `1e711ee`, the coexistence-`Pf` commit).
2. ✅ **Golden inventory** — `Research/Data/golden_outcomes_pre_pf.txt`: **81** outcome
   theorems, each with its **kernel-elaborated type** and **axiom footprint**. NOT a text
   grep (statements span lines and would not diff faithfully): a generated probe file,
   `Research/Data/GoldenProbe.lean`, `#check`s + `#print axioms` every theorem with
   `pp.fullNames`, and the baseline is that output. All 81 rest on Lean's 3 standard axioms;
   zero non-standard. Regenerate + diff at every phase gate.
3. ✅ **Legacy snapshot + FIDELITY anchor** — `Research/Spikes/unified_pf/LegacyS.lean`:
   the pre-migration `Derivation` + mutual `PlaysProof`/`AtomProvable`/`Provable`, extracted
   mechanically and re-namespaced `PD → PD.Legacy`, depending only on `Program.lean`.
   **The snapshot does not merely exist — it is PROVED to be the live system**:
   * `deriv_fwd`/`deriv_bwd` — the two `Derivation`s embed both ways **at equal `.size`**
     (the size equality is what transports the `struct` budgets; proved alongside, not after);
   * `legacy_to_live`/`live_to_legacy` — the full mutual block both ways (all three motives
     ride in one induction per entry type; every arm is its own twin);
   * **`legacy_iff_live : Legacy.Provable k φ ↔ PD.Provable k φ`** — the anchor, `[propext]`;
   * `proofSearch_eq_legacy` — hence the ORACLE is unchanged by re-basing on the snapshot.

   Phase 1 replaces this section's right-hand side with `Pf`, giving the chain
   `Pf ↔ Legacy.Provable ↔ (the S that proved the 81 golden outcomes)`. A desync between the
   snapshot and the live system now breaks the BUILD of this file — the intended alarm.
4. ✅ D1–D5 settled: **all recommendations adopted unchanged** (see §1).

*Deviation from plan*: the roadmap expected a grep-based inventory and a snapshot that was
merely "compiled". Both were upgraded — kernel-elaborated types, and a machine-checked
fidelity theorem — because a baseline that is not certified equal to the system it snapshots
would let the whole migration anchor to a subtly different `S`. Cost: one extra file section.

### Phase 1 — the core swap (`Derivation.lean`, `Dynamics.lean`) — ✅ **DONE 2026-07-14**
The intentionally-red commit window: the core is `Pf`-only and the anchor holds; everything
downstream is Phases 2–4's repair work.
1. ✅ `Derivation.lean` → the mutual block `{PlaysProof, AtomProvable, Pf}` (filename kept,
   per D4 — the 14 importers and the app's prompt-embedding follow automatically):
   * `PlaysProof.search_t`/`search_f` re-pointed at `Pf` (the back-edge that mutualizes);
   * `Pf` = the 22 constructors; `Derivation`, `Derivation.size`, `Provable` DELETED.
2. ✅ Day-one eliminators, same commit (the retired `PfMutualInductSpike` template):
   `Pf.induct` and `PlaysProof.induct`, both `@[elab_as_elim]`, motives TAKING the proof term.
   The file header states the rule: **never call `Pf.rec`/`PlaysProof.rec` outside §4**.
   Also `Pf_mono` + `atom_monotone` (the `cases` field-reordering gotcha on `mp` bites here
   too — `rename_i`, as in the spike).
3. ✅ `Dynamics.lean`: `proofSearch k φ := decide (Pf k φ)`; `interp`'s `.box`/`.diag` → `Pf`.
4. ✅ **The anchor, re-proved against `Pf`** (`LegacyS.lean`):
   **`legacy_iff_live : Legacy.Provable k φ ↔ PD.Pf k φ`**, `[propext]`, plus
   `proofSearch_eq_legacy` — the oracle decides the same relation it always did, so every
   `eval`/`play`/`outcome` in the library takes the same branches. The arms are now the
   *interesting* part (they were twins before the merge): legacy `struct ⟨d, size⟩` routes
   through `deriv_to_pf` (a legacy `Derivation` becomes a `Pf` AT THE SAME transcript size);
   legacy `app` and `implTrans` BOTH land on the merged `Pf.mp`/`Pf.implTrans`; `Pf` leaves
   re-enter legacy through `struct` (a leaf's `.size` IS its conclusion's size).
5. ✅ D5 executed: `PrisonersDilemma/Pf.lean` DELETED (its inductive is now the core; its
   `_pf`-suffixed Löb engines are redundant — `Base/Loeb.lean` holds the same engines, which
   Phase 2 renames in place). Root import dropped. The three `unified_pf` spikes retired with
   `TOMBSTONES.md`; `LegacyS.lean` is the only live artifact there (retires in Phase 4.5).

**Gate MET**: `Derivation.lean`, `Dynamics.lean`, and the anchor all compile; axiom audit clean
(3 standard axioms; the anchor itself is `[propext]`).

**Phase 2–4 inbox** (measured — per-file error counts after the swap; the build reaches
**3126 of 3158 jobs** before the first failure, and every theorem file that never touched the
proof system directly — DefectBot, CooperateBot, EBot, DBot, TitForTatBot, OBot, MirrorBot,
Helpers — is **already green**):

| Phase 2 — `Base/` | | Phase 3 — `Theorems/` | | Phase 4 — `Decidability/` | |
|---|---|---|---|---|---|
| `Loeb` | 63 | `PrudentBot` | 74 | `T49TreeSubstrate` | 101 |
| `Soundness` | 34 | `JustBot` | 65 | `T48CutRelevance` | 80 |
| `AtomCerts` | 7 | `DupocBot` | 40 | `T31EngineDecider` | 39 |
| `Exclusion` | 4 | `CupodBot` | 25 | `T54ZooCert` | 37 |
| | | `CIMCIC`/`DIMCID` | 14 each | `T50InstanceLob` | 36 |
| | | `CupodTrollBot` | 10 | `T42`/`T44`/`T51`/`T52` | 13/10/10/10 |
| **total** | **108** | **total** | **242** | **total** | **336** |

Caveat on reading those numbers: `Loeb`'s 63 are almost entirely one rename (`Provable.• → Pf.•`,
`app → mp`) repeated across the 14-step chain — error COUNT is not proof-difficulty. The genuine
thinking is in `Soundness` (fold the old `Derivation.sound` induction into the `Pf` arms; the
`search_f` floor argument is cost-model-side and survives) and, later, T42's gate decision (D2).

### Phase 2 — `Base/` re-proof (~1.6k lines) — ~1–2 sessions
Dependency order:
1. `Base/Asymptotics` — untouched (arithmetic).
2. `Base/Soundness` — the delicate file:
   * `atom_monotone` unchanged; `Provable_mono` deleted (superseded by `Pf_mono`);
   * `sound_upto` restructured: still budget-strong-induction (the `search_f` floor
     argument is UNCHANGED — it lives in the cost model, not the type split), but the
     inner recursor is the new 32-arm mutual one; the old `Derivation.sound` induction
     FOLDS INTO the `Pf` arms (leaves = their side conditions; `mp`/`implTrans` = the old
     `modusPonens`/`hypSyll` soundness bodies);
   * `proofSearch_spec`/`proofSearch_sound`/`proofSearch_monotone` — statements keep
     their names, proofs repoint.
3. `Base/AtomCerts` — mechanical rename.
4. `Base/Exclusion` — the census re-proved via `PlaysProof.induct`/`Pf.induct`: the
   `Derivation` census (`tail_plays_readable`) merges into the `Pf` induction (no nested
   hop); `no_provable_probeFirst_tail` (+`_botOpp`, `no_provable_searcherPlay_tail`)
   rename to `no_pf_*`. The seven floor outcomes' support — treat with care, this is
   load-bearing for five theorem files.
5. `Base/Loeb` — adopt the already-ported engines from `Pf.lean` (drop `_pf` suffixes);
   `mutual_loeb` is a mechanical rename (it never touched `Derivation`).
6. `BaseTheorems.lean` umbrella + `Axioms.lean` header notes.

**Gate**: `Base/` compiles; the equivalence scratch still compiles.

### Phase 3 — `Theorems/` + `Bots/` — ✅ **DONE 2026-07-14**

**Gate MET, including the headline check**: `lake build PrisonersDilemma` green (3142 jobs),
and the **golden-inventory diff is EMPTY** — all **81** outcome theorems have byte-identical
kernel-elaborated types and identical axiom footprints (standard three; zero non-standard),
on a proof system rebuilt from scratch underneath them
(`Research/Data/golden_outcomes_post_pf.txt` vs `…_pre_pf.txt`). That is the migration's
correctness claim, discharged mechanically rather than asserted.

Error counts fell as predicted (242 → 0): the sweep (constructor renames, `struct`-unwrapping,
`app → mp`) cleared ~95%. Two things needed real thought, both recorded below.

**FINDING (the sequel to Phase 2's census gap).** Phase 2 generalized `hinner` from the
target-action form to all actions, to feed the new stacked-search disjunct. **That
generalization is FALSE for PrudentBot**, whose then-branch genuinely IS a const-branched
`.search` — it is the stacked shape. The honest structure, now in place:
* `hinner` keeps its **action-specific** form (`pT ≠ .search k₂ ψ₂ (.const aTgt) (.const c1)`).
  It is what discharges the `searchThenSearch_t` arm — that rule concludes a play of the INNER
  THEN-action, never the else-action a floor theorem is about. PrudentBot: inner then = `C`,
  floor target = `D`. The arm dies on the action mismatch, on its merits.
* `not_readable_searchNonConst` no longer claims `¬ ReadableMe` (which is **false** for a
  stacked searcher). It now refutes exactly the **five** source-transparency bridge shapes —
  all the bridge arms can produce. The sixth disjunct belongs to `searchThenSearch_t`, which
  every floor theorem handles in its own arm.

The lesson generalizes: the two-type split let `searchThenSearch_t` (a `Provable` rule) hide
from the `Derivation` census, so each floor theorem killed it ad hoc. Unification forces the
shape into the open, where it must be discharged once, correctly. No outcome changed.

The pattern catalogue as applied (worked examples were in the retired `PfEngineSpike.lean`):

| old pattern | new pattern |
|---|---|
| `Provable.struct ⟨Derivation.<leaf> …, by simp [Derivation.size]; omega⟩` (19 sites) | bare `Pf.<leaf> … (by simp [Formula.subst, Prog.subst, numCost, Formula.size, Prog.size, <bots>]; omega)` |
| `Provable.struct ⟨.hypSyll _ _ _ l₁ l₂, size⟩` | flat `Pf.implTrans _ _ _ b₁ b₂ leg₁ leg₂ size` (pick per-leaf budgets; generous slack, `omega` closes) |
| `Provable.rec` exclusion (CIMCIC, DIMCID: the two double-inductions) | ONE `induction h using Pf.induct with` — named arms; DELETE the separate `*_no_deriv_*` lemma |
| `Provable.weakenImpl/…` constructor calls | same-name `Pf.…` (only `app → mp`) |
| statements `Provable k g` in guard lemmas | `Pf k g` (grep rename; `proofSearch_spec` bridges to the oracle as before) |

Files: `Theorems/{CupodBot, CooperateBot, DefectBot, DupocBot, EBot, Helpers,
TitForTatBot, OBot, MirrorBot, DBot, CupodTrollBot}` + `Theorems/LlmGenerations/{PrudentBot,
JustBot, CIMCIC, DIMCID}` (hand-port these — do NOT re-run the LLM pipeline mid-migration).

✅ **Gate MET** (see above). **The engine is now Pf-only.**

### Phase 4 — Metatheory (~16k lines; the big one) — ~5–10 sessions
Sub-order (each its own commit):
1. **T42 (the gated mirror + D2)**: `{PlaysProofG, AtomProvableG, PfG}` with the gate on
   the six premise formulas PLUS the merged `mp`/`implTrans` (uniform gating). Re-prove
   `PfG_sound` (erase gates) and the stratification `Pf ↔ ∃N, PfB N`. Derive `PfG.induct`
   (same template — the mirror needs its own named eliminator, budget one).
2. **T31 (enumerator)**: unified `decFull` — ONE grammar to enumerate (no separate
   `Derivation` enumeration, no `Type`-level size recursion): expect a NET
   SIMPLIFICATION. Re-prove `Pf_iff_decFull`; re-derive `evalG` sound commits; keep the
   `#eval` demos as the executable regression test.
3. **T43–T47**: modest universe, bounded decider, cert reads, logic space, stabilization —
   re-prove over `PfG`. The countP pigeonhole and query-space stratification arguments are
   budget-arithmetic, not grammar-specific; expect mechanical.
4. **T48–T54**: census (T48), the tree substrate (T49, ~6k lines — the largest single
   rewrite AND the largest simplification: no `struct`-boundary node kinds, no
   `Derivation`-vs-`Provable` case split in the extraction machine/normalizer/excisor),
   instance gate + transport (T50), falsification (T51 — re-check: the diag-blocking
   argument is gate-side, expected to survive verbatim), gate-parametric decider (T52),
   instance-stratum decidability (T53), **certified zoo (T54: the D2 acceptance test** —
   every zoo tree's ex-`Derivation` cuts must pass the instance gate; if one does not,
   revisit D2 before proceeding).
5. **Retire the legacy**: delete the Phase-1 `LegacyS` scratch + equivalence (archive the
   file under `Research/Spikes/unified_pf/` with a tombstone header); restate the
   universal-closure conjecture over `PfG` in `DECIDABILITY_ROADMAP.md`.

**Gate**: `lake build` BOTH targets green; `#eval` demos print the same outcomes as
pre-migration; axiom audit clean.

### Phase 5 — app + docs — ~0.5–1 session
1. `app/`: filenames unchanged ⇒ the proof agent's prompt embeds the NEW
   `Derivation.lean`/`BaseTheorems.lean` automatically. Sweep
   `app/src/pd_runner/llm/prompts.py` prose for stale rule names (`weakenImpl` etc.
   survive; `struct`/`Provable.rec` guidance dies). Few-shot retrieval auto-follows the
   ported theorem library.
2. **Re-run the Phase-2 eval harness** (10 held-out theorems, `exclude_bots` leak-free
   config) — the acceptance test that the agent can still write proofs in the new
   language. Expect ≥ the old 10/10; if the agent stumbles, the fix is prompt-side
   (add a `Pf.induct` exclusion few-shot), not engine-side.
3. Docs: CLAUDE.md (rewrite the proof-system row + the `Pf` row; delete the stale
   `ComputableEval` row), `UNIFIED_PF_SKETCH.md` + `PF_REPLACEMENT_ASSESSMENT.md` addenda
   ("superseded by the migration, see PF_ONLY_ROADMAP"), memory files.
4. Mark `PfEngineSpike.lean` historical (its demos are now the library's normal style).

### Phase 6 (optional, cosmetic) — renames
`Derivation.lean → ProofSystem.lean` (or `Pf.lean`), notation `⊢[k] φ`, prune dead
aliases. Zero urgency; do only if the paper wants the cleaner story.

## 3. Risk register

| risk | phase | mitigation |
|---|---|---|
| `sound_upto` restructure breaks the `search_f` floor argument | 2 | the floor is cost-model-side, untouched; port the strong induction FIRST, keep the old proof text side-by-side while porting |
| D2 uniform gating rejects a real zoo tree | 4.1/4.4 | T54 is the explicit acceptance test; fallback = weaken the gate on `mp`/`implTrans` to "conclusion-bounded" (documented deviation), not conditional two-tier gating |
| positional-recursor arity churn (the `cases` reordering gotcha) | 1–4 | `Pf.induct`/`PfG.induct`/`PlaysProof.induct` built FIRST (Phase 1.2/4.1); raw `.rec` allowed ONLY inside the eliminator definitions themselves |
| oracle semantics silently change | 1–4 | the Phase-1 legacy equivalence (`Pf ↔ Legacy.Provable`) is a THEOREM, kept compiling until Phase 4.5 |
| golden outcome statement drifts | 3 | byte-diff against the Phase-0 inventory at every gate |
| conjecture progress lost mid-rewrite | 4 | D3: no concurrent hunt; restate over `PfG` after 4.4 |
| LLM-generated proofs (CIMCIC/DIMCID) hard to hand-port | 3 | they are the two double-induction files — the exact pattern the spike already ported; budget extra time, not extra risk |

## 4. What does NOT change (the fixed points)

`Program.lean` (syntax, `subst`, `size`), the cost constants and `atom_cost`, `eval`'s
recursion structure (only the oracle's referent), every bot definition, every outcome
theorem STATEMENT, the strict `outcome_X_Y` template and compilation-==-correctness, the
app's architecture (tools, retrieval, harness), and the axiom count (3 standard, 0
project).

## 5. Effort summary

| phase | scope | estimate (focused sessions) |
|---|---|---|
| 0 | preflight | 0.5 |
| 1 | core swap + eliminators + legacy equivalence | 1 |
| 2 | Base/ | 1–2 |
| 3 | Theorems/ | 2–3 |
| 4 | Metatheory | 5–10 |
| 5 | app + docs | 0.5–1 |
| **total** | | **~10–17** |

Front-loaded certainty: after Phase 3 (~4–6 sessions) the ENGINE is fully Pf-only and
green — the paper's Part-I story is already told at that point. Phase 4 is where the
estimate variance lives (T49 dominates); it can be scheduled as its own campaign, with
the engine shipping first.
