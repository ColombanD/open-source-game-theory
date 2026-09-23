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

| Class | First cut (to be confirmed by Phase 0) | In `S'` |
|---|---|---|
| Search-free, both players | 28 `nobudget` + their `universal` cells | covered: `eval_iff_evalGraph` is unconditional for search-free players (`AgentConverse`); a census pass |
| One searcher vs a search-free bot, positive guard (Dupoc vs Cooperate) | by hand | Σ₁-completeness + instantiation fits at large `k`; unconditional |
| Löb families, FLOOR-FREE | the Löb pair files (23) minus the floor pair files (43) | the core of B; unconditional |
| Löb families, FLOOR-PAYING (Prudent, Guardian, CupodTroll, Just×Prudent; the 4 `_staggered` companions) | intersection | conditional on `BoundedReflection`; POLYNOMIAL staggers |
| Pure floor cells `(D, C)` | the rest of the 43 | conditional; same-`k` ones may be OPEN or FALSE in `S'` (`k^ε` vs `+k`, roadmap danger 3) — not promised |

The file grep is a first cut only: floors hide in `Theorems/<Bot>/Helpers.lean`. Phase 0 produces
the definitive per-cell table.

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

**Phase 4 — the search-free and simple-search census (~1 day).** Mechanical; `AgentConverse` + `Inst`.

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
  (the family-parametric assembly) started.
