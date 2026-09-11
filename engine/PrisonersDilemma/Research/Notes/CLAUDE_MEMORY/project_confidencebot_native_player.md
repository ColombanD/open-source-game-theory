---
name: project_confidencebot_native_player
description: "ConfidenceBot (2026-08-27) — the first NATIVE tau player (Dupoc's test + MAX aggregator), roster slot .confidence, lives on branch colomban-taubots via the worktree ~/wt/osgt-taubots; design criterion, port method, traps"
metadata: 
  node_type: memory
  type: project
  originSessionId: 606fd3ab-9860-4e91-9507-6449185aaaa1
  modified: 2026-08-27T10:08:22.552Z
---

**SUPERSEDED IN PART (2026-09-01, commit df56c99):** ConfidenceBot is RENAMED
**MaxConfidenceBot** everywhere (slot `.maxconfidence`, `TauMaxConfidence` files,
`maxconfidenceRow…`); its dual **MinConfidenceBot** (MIN/worst-case aggregator)
landed the same day. See [[project_paper_freeze_2026_09_01]] for the current state.

**What landed (2026-08-27, branch `colomban-taubots`, built in the git worktree
`~/wt/osgt-taubots` — outside OneDrive, `.lake/packages` symlinked to the main tree's,
`.lake/build` copied; the user's main checkout was on `colomban-bounded-gl` with
uncommitted bounded-GL work, so tau work must NOT be done in the main tree).**

- A tau player = (per-hypothesis TEST = a `Spec`, AGGREGATOR). Lifts = `sum ≥ θ`
  (linear in the signal). ConfidenceBot = (Dupoc's test, `max ≥ θ`): cooperate iff
  some SINGLE hypothesis with ≥ θ of the signal provably cooperates with me.
  Criterion for "not a lift" = nonlinearity; witness = three signals
  `2δ_coop, δ_coop+δ_tftSim, 2δ_tftSim` (max plays C,D,C; a threshold of a linear
  mass cannot) — `confidence_not_linear` in `Tau/Theorems/TauConfidence/Phase.lean`.
- As a HYPOTHESIS it IS Dupoc (`inst` depends only on specs): instances equal by `rfl`
  except `confidence × dupoc` (symmetric `.sys` `cfdSys`, mutual Löb C — the easiest
  mutual-Löb shape, both cross-readings `sys_cross_C_at`) and Just's slot (probes that
  system). `confidenceRow = dupocRow`; port cost = 1 Löb lemma + one-line arms.
- Python: `NATIVE_PLAYERS` in `tau/matrix.py` (cells CLONED from the base,
  `Cell.clone_of`), `play.decision_mass` dispatch, zoo `default+confidence`,
  `BASE_OF["TauConfidence"]="DupocBot"` → certification 256/256/0.

**Why:** Colomban wanted a tau bot "not tied to a base bot" AND in the roster so the
EGT zoo analysis can include it. The circular "cooperate iff a heavy hypothesis I'd
cooperate with" was rejected by Colomban (at point mass "I'd cooperate" is an
ungrounded fixpoint) — the test must be a concrete probe; Dupoc's chosen for the
headline question (transparency needed for Löbian cooperation).

**How to apply / traps:**
- `omega` case-splits every `max` in a threshold tower (2ⁿ): eleven `max`es in
  `TauMirror/Phase.lean` timed out → thresholds are SUMS (`kA + kQ + …`) now. Use sums.
- Name clash: `cdSys` already = Cupod×Dupoc system in `TauCupod/Helpers.lean`.
- Adding a roster slot: `tauOrder` AND `tauOrderInit` (before `.mirror`), every
  `Columns.lean` table/theorem arm, all 16 `Phase.lean` witnesses, the display
  `abbrev *Mass` in `Tau/Theorems/Helpers.lean` (right-nested in tauOrder order — `simpa`
  matches syntactically), `TAU_ORDER/TEMPLATES/LEAN_SLOT/BASE_OF` in
  `def4_theorems.py`, regen `tau_rows.json`, the 225→256 count in `test_def4_compare`.
- Tactic-block arms: a term continued on the next line after `exact` breaks parsing.
- `uv sync` in a fresh worktree needs `--all-groups` for pytest; `httpx` is imported
  by `llm/client.py` but NOT declared in pyproject (install ad hoc to run API tests).
- Pre-existing failing test (also on main): `tests/egt/test_report.py::
  test_conditional_results_are_flagged` (asserts stipulation text; default zoo has none).
- Twin consequence: ConfidenceBot is a behavioral+syntactic twin of Dupoc as a hypothesis
  → ceiling < 1 for distance σ families on `default+confidence`; `epsilon` unaffected.
  `tau/syntax.py` cannot parse `.tvote`; a native presents its base's source (debt #5).
