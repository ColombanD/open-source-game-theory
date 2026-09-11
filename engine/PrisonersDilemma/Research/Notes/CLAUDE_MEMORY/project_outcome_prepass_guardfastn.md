---
name: project-outcome-prepass-guardfastn
description: "Deterministic outcome pre-pass tool + guardFastN engine guard — what they decide, calibration traps (batch #eval death, OOM caps, arm order), and the Tier-0 decide-proof route"
metadata: 
  node_type: memory
  type: project
  originSessionId: 31323ee8-77f4-468f-80b6-f2699ed2b872
  modified: 2026-07-29T14:48:09.682Z
---

**The pre-pass** (`app/src/pd_runner/eval/outcome_prepass.py`, 2026-07-29): computes
bot-pair outcomes deterministically via `PD.T31.outcomeG` before any LLM call; every
`some (a,b)` is certified (`outcomeG_sound ∘ guardFastN_sound`). Run:
`uv run python -m pd_runner.eval.outcome_prepass [--resume]`. Results JSONL in
`app/generated/prepass/`. Purpose: hand the proof agent TRUE statements + budgets
instead of letting it discover outcomes (its dominant failure cost).

**`guardFastN`** (T31EngineDecider.lean, after `guardFast_sound`): sound 3-arm guard —
(1) SIZE FLOOR first: non-atom guard with `k < φ.size` commits false via
`pf_size_or_atom` (Pf pays conclusion size unless plays-atom); (2) `.neg (.plays …)`
goal-directed both polarities (`Pf.atomNeg` true / positive-cert+soundness false);
(3) plays delegate to `guardFast`. Floor-first ordering is LOAD-BEARING: cert search
before the floor lets `decCertG` descend into `.search` subjects → `decFull` sweep →
OOM (SIGKILL 137 during `lake build`, demos at file end).

**Calibration traps (hard-won):**
- NEVER batch many `#eval`s in one lean process for risky cells: a dying cell
  (interpreter stack overflow) silently discards the WHOLE batch's buffered output.
  One process per cell + wall timeout + `lean -M <MB>` cap (without the cap, sweeps
  ballooned to many GB and crashed Colomban's Mac twice).
- `guardFull` is infeasible in practice even at budget 2 (silent death) — don't use.
- `lake env lean` needs the imported bots' oleans built first (`lake build +Mod`).
- Both-searcher plays-guard cells at k>2: 100% infeasible (skip rule in tool).

**Results (2026-07-29, prepass2.jsonl, 56/160 determined):** WaryBot has a certified
BUDGET PHASE TRANSITION vs DefectBot: (C,D) at k≤4 (floor — refutation doesn't fit,
suckered) → (D,D) at k≥16 (atomNeg fits, defends). WaryBot vs EBot flips (C,D)→(C,C)
at 32 (EBot's probe sees WaryBot@32 defend vs DefectBot). WaryBot self-play (C,C) at
k=2 by floor ("can't refute → trust"). LegibleBot k k is floor-dominated (defects,
exploits CooperateBot (D,C)) until k≈30 where its box guard first fits; then needs a
box-prover — LLM territory. OptimBot: NOTHING deterministic (own-play conjuncts are
Löbian; k=4 hops OOM) — pure LLM territory, as is GuardianBot vs searchers.

**Tier-0 proofs**: determined cells lift to kernel theorems with zero LLM:
`outcomeG_sound (guardFastN d) (guardFastN_sound d) fuel _ _ _ (by decide)` — verified
compiling for GuardianBot vs DefectBot/CooperateBot (plain `decide`, no native_decide).
Staged (NOT wired into targets): `Decidability/CertifiedOutcomes/*.lean`, 28 theorems.

**STRUCTURAL theorems LANDED (2026-07-29, uncommitted)**: 27 outcome theorems in
`Theorems/{GuardianBot,WaryBot,LegibleBot}/` (house template, ∀fuel, wired into root
`PrisonersDilemma.lean`; full 3282-job two-target build green). Key new Base lemma:
`pf_size_or_atom` + `proofSearch_false_{neg,impl,box,eq}_undersized` in
`Base/Exclusion.lean` (engine-side size floor — a proof pays its conclusion's size
unless it's a plays-atom; the workhorse for ALL floor-dominated cells; discharge the
size hypothesis per-opponent `by decide`). LARGE-k upgrade (user request:
theorems must be big-k, not small-k): headline statements are `∃k₂,∀k≥k₂` via
`linear_log2_add_le` (guard sizes are log₂k + O(1)) or unconditional ∀k (soundness
cells: GuardianBot row, WaryBot vs CooperateBot/TitForTatBot). OUTCOME FLIPS proven:
WaryBot vs DBot and vs EBot are (C,D) at k=2 but (C,C) at large k (defended vs the
DefectBot probe → simulators cooperate). Phase-transition triple:
`outcome_WaryBot_vs_DefectBot` (∃k₂ (D,D)) / `_floor` (k=2, (C,D)) / `_defended`
(k=16 — atomNeg transcript 1+15 exactly fits). FULL GENERALIZATION (same day): NO
theorem is pinned to concrete small k anymore — three tiers: ∀k unconditional
(soundness cells incl. WaryBot vs CupodTrollBot — identity guard fails structurally,
`by simp [WaryBot, CupodBot]` proves the ≠), ∃k₂∀k≥k₂ (atomNeg-affordable), and
floor-regime-general `(hsz : k < guardsize) → outcome` with `_floor2` concrete
instances (`by decide`). OPEN large-k cells (prover-agent test set, documented in
per-file docstrings): WaryBot Mirror/self (.neg-guard Löb fixpoint — no diag
analogue for refutation guards), OBot (¬Pf of TRUE formula — needs neg-spine floor
census; expected flip to (C,D)), impl/eq/box opponents, LegibleBot row past k≈30. Proof idioms: floor→`unfold Bot at hg ⊢; simp [eval,
Prog.subst, Formula.subst, hg]`; probers→`eval_sim_opp_bot_of_play` +
`play_ite_from_guard` (+`eval_ite_from_guard` chains for OBot/EBot nesting).
Related: [[project-computable-eval-routeii]], [[project-onedrive-lake-replay-timeout]],
[[project-floor-exclusion-blueprint]].
