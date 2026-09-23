# Route B — scope and plan (decided 2026-09-23)

*The decision taken at the `MERGE_CROSSROAD.md` fork: **B** — no rule bridge; the engine's cells are
re-proved directly in PA-`S'`, family by family, on the M5 pattern (`Assembly/`), with the floor
as ONE named hypothesis. The engine is untouched. Companion notes: `MERGE_CROSSROAD.md` (the
routes and the citation obstruction), `BOXCOST_SPIKE.md` (branch `colomban-boxcost`, the D spike),
`ARITHMETIZED_S_RESULTS.md` (what is proved), `ARITHMETIZED_S_ROADMAP.md` §3 M6 (the status log).
Branch: `colomban-route-b` (off `colomban-recost`, which keeps the atom re-cost).*

## 0. Why B, in one paragraph

The citation problem (`MERGE_CROSSROAD.md` "The obstruction") is a problem of TRANSFERRING engine
proofs: replace each free citation (`boxIntro` at `a + |□_a φ|`, `search_t` at `log k`) by the PA
verification U10 proves (polynomial, degree 16) and the budgets compose doubly-exponentially through
nested boxes. B never transfers an engine proof. Each cell is re-proved by Critch's UNIFORM argument,
which necessitates only constant-length proofs and inner-necessitates only at the polylog subscript
`gBudget k = ‖k‖³`, so the verification cost `E(g(k))` stays `≺ k`. The citation cost is paid, but
only where it is cheap. That is how `dupoc_self_coop_unconditional` went through. What B gives up:
a rule-level theorem "engine rule ⇒ `S'` rule" (false at polynomial budgets; stated instead as the two
proven sentences below), one `S'` proof per family (labour), polynomial staggers instead of `2k+64`.

Route D (re-cost the engine's box rules to Critch's (d) at the polynomial U10 proves) is INDEPENDENT
of B, engine-side, and recommended to land separately; it is not part of this plan. Route A is
rejected (nominal budgets). Route C only if months appear (the box would mean `S''`-provability).

## 1. In hand (all three standard axioms)

* The system: `LenDerivable`/`LenProvableV`, properness, τ-symmetry; the evaluator covers every
  base constructor (`const/self/opp/bot/sim/ite/search`).
* The M4 kit: bounded D2 (`CutV`), instantiation (`InstV`), the parametric diagonal lemma (`Diag`),
  `ProperV`, `NumeralFacts`, Dupoc's truth equations (`Transparency`), the conjunction family and
  ∧-elimination on codes (`Assembly/Prep`).
* U10: `boundedInnerNec_sixteen : BoundedInnerNec 16` (`Necessitation/Package.lean`) — PARAMETRIC
  ONLY: stated for `instB ⌜χ⌝ k` at budget `gBudget k`.
* Two cells: `red_cell` (every `k`), `dupoc_self_coop_unconditional` (all large `k`).
* The atom re-cost (`colomban-recost`, engine): keep regardless.

## 2. The census (155 cells, 18 bots), by mechanism

Bot sources: search-free = CooperateBot, DefectBot, MirrorBot, TitForTatBot, DBot, EBot, OBot
(`const/sim/ite` only); box-free searchers = DupocBot, CupodBot, CupodTrollBot, CIMCIC, DIMCID,
GuardianBot, JustBot, PrudentBot; excluded = WaryBot (`.neg` guards: refutation floors only),
LegibleBot (box guard: `box_guard_never_fits`), OptimBot (seven searches, floor-paying Löb premise;
out of the merge's scope by the M6 decision).

| Class (from `ROUTE_B_CENSUS.md`, the Phase-0 census) | cells | In `S'` |
|---|---|---|
| SF — search-free, both players | 28 | covered: `eval_iff_evalGraph` is unconditional for search-free players; a census pass |
| POS — a positive guard, no Löb, no floor | 14 | Σ₁-completeness + instantiation fits at large `k`; unconditional |
| **SND — the guard is semantically FALSE; the else branch by SOUNDNESS** | **36** | **UNCONDITIONAL: `TAct` sound in ℕ ⇒ no proof of any length ⇒ else branch; the red cell's own argument. Not a floor.** |
| LOEB-FF — Löb, floor-free | 29 (14 without LegibleBot) | the core of B; unconditional via the family-parametric assembly |
| LOEB-FP — Löb, floor-paying | 5 (Prudent×EBot + the two Löbian companions in scope) | conditional on `BoundedReflection`; POLYNOMIAL staggers |
| FLOOR(cen) — a TRUE guard unprovable within the budget | 32 | a proof-length LOWER bound in PA (Pudlák; `k^ε` vs `+k`, roadmap danger 3): conditional or not claimed; same-`k` cells may be open or FALSE in `S'` |
| FLOOR(cenU) + OTHER(WV) — negatives resting on UNREADABILITY | 6 + 4 | do NOT transfer: PA reads every source (Σ₁-completeness); the `S'` value may DIFFER — re-evaluate cell by cell |
| OTHER — the red cell | 1 | done |

The SND class is the census's correction to the first cut: 36 of the cells I had lumped with the floor
need no lower bound at all — the guard is false, and Lean-level soundness closes them exactly as it
closes the red cell. The floor hypothesis is needed only where a PA PROOF must assert a negative
(inside a Löb premise: LOEB-FP) or where the guard is TRUE but too long to prove (FLOOR(cen)).

## 3. Phases

**Phase 0 — packaging and census (~2 days).**
* U10 in closed-sentence, arbitrary-budget form: `∀ σ, ∃ C_σ, ∀ V b, LenDerivable TAct b ⌜σ⌝ →
  LenDerivable TAct (C_σ·(b^16+1)) ⌜□_b σ⌝` (with `□_b σ` the `LenDerivable`/`bewB` sentence at the
  budget `b` written as a term), re-packaged from `Necessitation/Top.lean`'s kit. Needed the moment one
  bot cites another searcher's success at the partner's FULL budget (asymmetric cells).
* The bounded diagonal-lemma wrapper (`Diag.tact_parametric_diagonal_inst` carries no length; the
  `Uniform.exists_forward_length`/`forward_inst_V` pattern, one existential constant per template).
* The cell census against `Helpers.lean`: the definitive family list (deliverable: a table in this note).

**Phase 1 — the family-parametric assembly (THE REFACTOR, ~3 days).** `Assembly/Uniform.lean` and
`Assembly/Cell.lean` are hard-wired to `pConj = qDupoc ⋏ qCupod` (`theta = boxCoreA 🡒 pConjL`,
`psi = tactFixedpoint theta`, `chi₁`, `chain_core_V`, `psi_true_V`, `pblt_uniform`,
`exists_psi_instance_length`, `cell_core`). Abstract them over the FAMILY: a target
`p : Semisentence LAct 1` and the bounded Löb premise as a hypothesis ("a proof of the `k`-instance
of `p` within budget `k` makes `p(k)` true in both standard readings"); output the arithmetized
`pblt_engine`: `∃ k₀, ∀ k > k₀, ∃ a ≤ k, LenDerivable TAct a (instB ⌜p⌝ k)` (the family's box is
found within its budget, at ℕ and V-generic) and the uniform `TAct ⊢ ∀k ≥ k̂, psi_p(k)`. GATE:
`dupoc_self_coop_unconditional` and `pblt_unconditional` re-derived with BYTE-IDENTICAL statements
(`Package.lean` unchanged), census unchanged, build green. Also needed here: the `.sim` clause in
`V` (Mirror-facing cells; `Subst.lean`/`SimTest.lean` hold the ℕ side).

**Phase 2 — floor-free Löb families, unconditional (~1 day each).** Candidates (Phase 0 confirms):
Dupoc/Cupod (done), CIMCIC, DIMCID, Just self-play; Dupoc×Mirror, Cupod×Mirror, DIMCID×Mirror,
Just×Mirror (the frozen-`.bot` Löb: `botSearchStep`'s `S'` twin); CIMCIC×Dupoc, DIMCID×Cupod,
Just×Dupoc, CIMCIC×Just. Each = truth equation in both readings + the engine of Phase 1.

**Phase 3 — the hypothesis and the floor-paying families (~3 days).** State `BoundedReflection`
`BoundedGL`-style, per family with a polynomial constant: from a refutation of the guard at budget
`m` (a `TAct`-proof code of `∼guard`), a `TAct`-proof, at cost `C·poly(m, k)`, of "no `k`-proof of the
guard exists" — the `S'` twin of the engine's `search_f`. Then Prudent×Dupoc, Just×Prudent,
CupodTroll×Dupoc at POLYNOMIAL staggers, conditional; and the honest negative list: which same-`k`
floor cells are NOT claimed. Its discharge (proof-length lower bounds, Pudlák) is OUT.

**Phase 4 — the SF/POS/SND census (~2 days).** SF and POS mechanical (`AgentConverse` + `Inst`); SND = the
red cell's soundness argument per cell (guard false in ℕ ⇒ `¬LenProvableV` at every budget ⇒ else branch):
78 cells unconditional. Then the 10 unreadability cells (cenU + WV) re-evaluated in `S'` — expected to
split into POS-like and genuine FLOOR(cen).

**Phase 5 (optional) — LegibleBot** via box budgets/bodies as node data in `tmpl` (`FitBox`'s fix).

## 4. Statement conventions (unchanged from M4/M5)

All results "for all large `k`"; thresholds and constants EXISTENTIAL, never quoted (Cantor coding);
staggers polynomial; `≤` on `V = ℕ` is `le_def`; `simp` never sees a closed quote of a fixpoint;
`omega` is never asked about `V`; two Lean agents concurrently at most; single-file checks with
`timeout 600 lake env lean`, check the exit code; census in `Audit.lean` must stay all-standard.

## 5. What it delivers for the thesis

The census table of §2 with `S'` status per family, and two proven sentences: *the Löbian cells and
the red cell hold in PA-`S'` for all large `k`, unconditionally where the guard is positive and
relative to bounded reflection where it pays a floor; citation is polynomially eliminable (U10) and
no polynomial budget-preserving embedding of the citation rule exists.*

## 6. Status log

* 2026-09-23: decided B; branch `colomban-route-b`; Phase 0 (U10 re-packaging, census) and Phase 1
  (the family-parametric assembly) started. Census DONE (`ROUTE_B_CENSUS.md`): the SND class found (36
  cells closed by soundness, not floors); 10 unreadability cells flagged as possibly DIFFERENT in `S'`.
* 2026-09-23 (later): **Phase 1 DONE** (`173bfa5`, `Assembly/Family.lean`): `LoebSound p S₀ S₁`,
  `pblt_uniformF`, `family_found` (the arithmetized `pblt_engine`); Uniform/Cell = the `pConj` instance,
  53/53 statements byte-identical, `Package.lean`/`Prep.lean` untouched, census 926 all standard.
  Deviation: `theta/psi/psi_fixed_point` stay in `Prep.lean`, bridged by `rfl` (`psi = psiF pConj`).
