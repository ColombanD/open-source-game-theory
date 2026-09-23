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
* 2026-09-23 (later): **Phase 0 item 1 DONE** (`715851b`, `Necessitation/ClosedNec.lean`):
  `closedInnerNec_sixteen : ∀ σ : Sentence LAct, ∃ C, ∀ V b, LenDerivable TAct b ⌜σ⌝ → ∃ e ≤ C·(b^16+1),
  LenDerivable TAct e (boxSentenceCode σ b)` with `boxSentenceCode σ b = instB ⌜boxClosed σ⌝ b` (budget as
  the BINARY numeral `bnum b`, `σ` by its Gödel numeral — the `Box_g` discipline; semantics
  `eval_boxSentence_iff`). The verification kit (`Assemble.VerifyKit'''`) was re-used VERBATIM for an
  arbitrary conclusion; only the pin (`NumId.numId_sentence` on the root dossier), the closing block
  (`closeStepsC`, one appended library row `lenDerCong` in `closedRows := indRecRows ++ [lenDerCongRow]`)
  and the cost grading (`G = b+1`, `u = 1`, degree still `deg 4 = 16`) are new. **MERGED GATE**: full
  `lake build ArithS` on `715851b` = 3297 jobs, 0 errors, census 957 standard triples (+3 pre-existing
  `[propext, Quot.sound]` subsets, 4 axiom-free), i.e. Phase 0 + Phase 1 together are green.
  TRAPS (ClosedNec): a `getElem` on a ~200-row list with a CLOSED index or an implicit bound proof
  makes `get_elem_tactic` walk the list (recursion depth / whnf timeout) — state for a VARIABLE index
  with `hi : i = cIdx` and explicit `l[i]'h`, go through `getElem?` (`List.getElem?_append_left/right`);
  `(l₁ ++ l₂)[i]?` does not parse (collides with the `?[…]` vector notation) — `unfold` first; an
  `obtain`ed `x` is not definitionally `⌜σ⌝` — feed the pin `hxdef ▸ …` and shift with the
  `numeral`-stated `termShiftIterV_numeral`; python heredocs die on `'''` inside Lean text
  (`VerifyKit'''`) — write Lean/notes via SHELL heredocs.
* 2026-09-23 (later): Phase 2 cell 1 IN FLIGHT: `Cells/DupocMirror.lean` — the conjunction family
  `pDM := qDM ⋏ qCM` (Mirror is τ-fixed) for `Dupoc × Mirror = (C, C)` and `Cupod × Mirror = (D, D)`.
* 2026-09-23 (later): **Phase 2 cell 1 DONE** (`52f9136`, `Cells/DupocMirror.lean`, 562 lines): the
  conjunction family `pDM := qDM ⋏ qCM` gives `dupoc_mirror_coop_unconditional` (`EvalGraph 2 (Dupoc k)
  Mirror (Dupoc k) 0 ∧ EvalGraph 3 Mirror (Dupoc k) Mirror 0`, the `(C, C)` cell) and
  `cupod_mirror_defect_unconditional` (`(D, D)`) plus the box forms, all large `k`, three standard
  axioms; NO generalization of `Instance*`/`Guard`/`Template` was needed — a closed opponent goes
  through the existing `quote_emb_cl_V`/`termSubst_closed` route. Full build 3298 jobs, census 984
  (+27). The engine is now used as a FUNCTION OF THE FAMILY: a cell = its truth equation + one
  `LoebSound` proof. IN FLIGHT: `Cells/DIMCID.lean` (the `.impl` guard via `tmpl`: DIMCID×DIMCID,
  DIMCID×Mirror, then DIMCID×Cupod mutual) and `Cells/JustBot.lean` (the frozen `.bot (Dupoc k)`
  guard: bot-wrapped Dupoc self-coop, Just×Just, Just×Mirror, then Just×Dupoc mutual).

## 7. FINDING (2026-09-23): budget-dependent snapshots inside a guard are not `bnum k`-instances

`Cells/JustBot.lean` (`8df39b4`, `b9d0dcf`) landed the bot-wrapped Dupoc self-cooperation
(`botDupoc_self_coop_unconditional : ∃ k₀, ∀ k > k₀, EvalGraph 3 (pBot (Dupoc k)) (pBot (Dupoc k))
(pBot (Dupoc k)) 0`, twin `botCupod_self_defect_unconditional`) and **Just × Mirror = (C, C)**
(`just_mirror_coop_unconditional : … EvalGraph 2 (Just k) Mirror (Just k) 0 ∧ EvalGraph 3 Mirror (Just k)
Mirror 0`), unconditional, plus a GENERIC instance equation `guardCode_eq_instB_of` and generic truth
equation `eval_GtmplA_subst_iff` that make each new instance equation a one-liner. Build 3301 jobs, census
1059 all standard.

**Just × Just and Just × Dupoc did NOT go through, for a structural reason, not for lack of time.**
`JustBot k := .search k (.plays .opp (.bot (DupocBot k)) C)` carries the budget `k` TWICE: as its search
budget and INSIDE its guard, in the frozen snapshot `DupocBot k`. Its arithmetized code
`JustV k = pSearch k (gJ k) …` therefore stores a template `gJ k = subst (jVec k) ⌜GtmplA 0⌝` whose CODE
depends on `k`, and the canonical description `progT (dnum (JustV k))` has the leaf `bnum (gJ k)` — the
binary numeral of a `k`-dependent formula code, which is NOT `termSubst (bnum k ∷ 0)` of any fixed term.
So a guard that DESCRIBES `Just k` ("Just k plays C against …") is not `instB ⌜q⌝ k` for any fixed
`q : Semisentence LAct 1`, and `Assembly/Family.family_found` (Critch's uniform argument, which needs
the family to be the `bnum k`-instance of ONE formula) does not apply. Dupoc/Cupod/Mirror never hit this
because their stored templates are CONSTANTS (`⌜GtmplA a⌝`) — the M4 brief's `ppair` fix (§2 there) made
the PROGRAM description a term in `k`, but a `k`-dependent TEMPLATE inside the program is the same
mismatch one level down. The engine never sees it: `search_t` CITES the fact at `O(log k)`.

Affected in-scope cells: Just × Just, Just × Dupoc, CIMCIC × Just (everything that describes `Just k`),
and any future bot whose guard freezes a budget-carrying snapshot. Not affected: every bot whose stored
templates are budget-free (Dupoc, Cupod, Mirror-facing cells, DIMCID/CIMCIC self and vs constants,
PrudentBot's `.bot DefectBot` snapshot is constant).

Three routes (USER DECISION):
 (a) **The transparency lift** — PA proves, at polynomial cost, the evaluation of the Σ₁ description
     of `Just k` (bounded-length Σ₁-evaluation of closed description terms and of `subst` on codes +
     inner necessitation + a uniform transparency theorem cut): the `S'` twin of the engine's `search_t`
     certificate, the "POS" mechanism of §2. New infrastructure (the U10 walk/dossier kit is the
     natural substrate), days.
 (b) **Fix the snapshot's budget** — the engine's own two-tier `JustBot2 K k` (`JustBot k = JustBot2 k k`,
     the FREEZE TRICK): at a FIXED snapshot budget `k₀` the template is a constant and `JustBot2 K k₀`
     IS a `bnum K`-instance of a fixed formula, so the family machinery applies verbatim and gives
     "for all large `K`" cells at each fixed `k₀` (with `k₀` large enough for the snapshot's own Löb).
     Honest, cheap, matches the engine's `outcome_JustBot2_vs_*` variants — but it is a statement
     about `JustBot2`, not the same-`k` `JustBot k` cell.
 (c) **Templates with a budget SLOT** (the "node data" fix of `FitBox`, one level down): let `pSearch`
     store a template with a free budget variable filled at instantiation, so `gJ` is constant and the
     snapshot's budget is a term — a re-coding of `Prog.lean`/`Template.lean`; faithful, touches the
     trusted base (`SPRIME_DESIGN_RATIONALE.md`), every code equation re-proved.
Recommendation: (b) now for the Just cells (one agent-day), (a) or (c) as the general fix decided
together with the LegibleBot node-data question (Phase 5) — they are the same design decision.

* 2026-09-23 (later): **Phase 2 JustBot family**: cells (1) bot-wrapped Dupoc self-coop and (3)
  Just × Mirror DONE unconditional (`8df39b4`, `b9d0dcf`); Just × Just / Just × Dupoc blocked by §7.
* 2026-09-23 (later): **Phase 2 DIMCID family DONE** (`c5f83f6`, `da5bd3c`, `Cells/DIMCID.lean`):
  DIMCID × DIMCID `(D, D)`, DIMCID × Mirror `(D, D)` and the first MUTUAL cell DIMCID × Cupod `(D, D)`,
  all unconditional. The guard went through the GENERAL translation `tmpl φD` (new: the truth of `tmpl`
  at the pronoun atoms in every model, `eval_tmpl_plays_self_opp_V/_opp_self_V`; fixed formulas
  generic in the opponent triple `pG X U W`); the mutual family is `pDC = pG TD uC wC ⋏ (qCD ⋏ τqCD)`,
  four guards from one box by a two-level ∧-elimination at slack `(14, 16)`. **MERGED GATE on
  `da5bd3c`: 3301 jobs, 0 errors, census 1071 standard.** Phase 2 tally: 8 cells unconditional
  (Dupoc×Mirror, Cupod×Mirror, botDupoc self, Just×Mirror, DIMCID×DIMCID, DIMCID×Mirror,
  DIMCID×Cupod, + Dupoc/Cupod self from M5). NEXT in flight: CIMCIC × Dupoc (mutual, `.impl`),
  Prudent × Mirror (nested search).
* 2026-09-23 (later): **Phase 2 CIMCIC family DONE** (`fa60f3a`, `Cells/CIMCIC.lean`): CIMCIC × Dupoc
  `(C, C)` (the second MUTUAL family `pCiD`, slack `(14, 16)`), CIMCIC × Mirror `(C, C)`, and CIMCIC ×
  CIMCIC `(C, C)` **Löb-FREE** — the guard is `A → A`, `tact_proves_qCC : TAct ⊢ ∀¹ qCC` by completeness,
  the instance at `k` costs `K₀ + K₁·size k` (the `S'` twin of the engine's `Pf.implRefl`, the POS
  mechanism of §2 realized: `cimcic_self_coop` needs no `BoundedInnerNec`). Nothing outside the new
  file changed. Gate: 3303 jobs, 0 errors, census 1125 all standard. **Phase 2 tally: 11 cells
  unconditional** (+ Dupoc/Cupod self from M5). TRAP: at ℕ `rw [pow_one]`/`simp [pow_one]` do not fire on
  an instantiated `‖k‖ ^ 1` (the pow comes through `instCommSemiring_foundation ℕ`) — remove the
  exponent inside the V-generic binder (`linear_size_le_eventually`). IN FLIGHT: Prudent × Mirror
  (STEP 0 = the §7 verdict on Prudent's nested searches).
* 2026-09-23 (later): **Phase 2 Prudent × Mirror DONE** (`9a71612`, `Cells/PrudentMirror.lean`):
  `prudent_mirror_coop_unconditional : ∃ k₀, ∀ k > k₀, EvalGraph 3 (Prudent k) Mirror (Prudent k) 0 ∧
  EvalGraph 4 Mirror (Prudent k) Mirror 0` (fuels 3/4: outer search, inner search, constant), the τ-twin
  `(D, D)`, box forms for BOTH guards, bridge `pcode_PrudentBot`. **STEP-0 verdict: nested searches are
  NOT the §7 obstruction** — Prudent's two stored templates are budget-free constants (`.bot DefectBot`
  is closed), `k` sits only in the two `pSearch` budget slots, so `PrudentV k` IS a `bnum k`-instance of a
  fixed two-`#0` term. What nesting costs: the canonical description compares two `k`-dependent codes
  (`PrudentV k` vs its transposition), uniform only ABOVE a standard threshold `KP` (`nested_search_lt`,
  an ordered-semiring argument on `ppair`); every description/instance/truth equation carries
  `hk : KP ≤ k`, supplied by the family slack `S₀ = 14 + KP`. The two engine mechanisms replaced: the
  prudence conjunct (engine: a search-free atom at `⊢_33`) is a fixed formula `qPP` whose truth is the
  closed Σ₁ fact "Mirror plays D against `pBot (pConst 1)`", carried as a CONJUNCT of the family; the
  inner-search citation (`searchThenSearch_t`) is ∧-elimination from the family's box, so both searches
  fire from ONE Löb fixed point (`pPM = (qPM ⋏ qPP) ⋏ (qPMT ⋏ qPPT)`, `loebSound_pPM : LoebSound pPM
  (14 + KP) 16`). Generic pieces added for any six-variable template: `qT`, `guardCode_qT_eq_instB`,
  `eval_qT_iff`, `eval_tmpl_plays_opp_closed_V`. **FINAL GATE on `9a71612`: 3305 jobs, 0 errors, census
  1163 standard.** **Phase 2 tally: 12 cells unconditional; of the 14 in-scope LOEB-FF cells of the
  census, 11 are done; Just × Just, Just × Dupoc, CIMCIC × Just parked on §7.** TRAPS: in this Mathlib
  `add_le_add_left h a : h.lhs + a ≤ h.rhs + a` and `add_le_add_right h a : a + … ≤ a + …` (`_root_.`
  needed, Foundation shadows them); a statement mentioning only `MirrorV`/`pBot`/`pConst` without a
  `V`-pinned term elaborates at ℕ silently (write `(MirrorV : V)`); `rw [relabel_const]` rewrites every
  `pConst 1` at once; zsh: `${pipestatus[1]}`, not `${PIPESTATUS[0]}`, to read `lake env lean`'s exit
  code through a pipe.

## 8. Decisions (Colomban, 2026-09-23 evening)

1. **§7 route: try (c) — templates with a BUDGET SLOT — with (a) the transparency lift as the fallback.**
   Design of (c): a stored template may have a 7th free variable; the evaluator's `search` clause fills
   it with the NODE'S OWN budget at guard time, `guardCode g me opp k := subst (descVec me opp ++ [bnum k])
   g`, so a frozen snapshot whose budget equals the searcher's is described by a TERM in the slot and the
   stored template is a constant (`JustBot k = JustBot2 k k`, the diagonal; `JustBot2 K k` keeps a constant
   description as today). Existing 6-variable templates are untouched iff `subst` ignores entries beyond
   the formula's arity (the one lemma the spike must establish first); the blast radius is the set of
   files that unfold `EvalGraph.search_iff`. Fallback trigger: that lemma fails, the `EvalGraph` fixpoint
   fights the extra substitution, or the re-check exceeds ~a day.
2. **Floors DROPPED from `S'` for now**: no `BoundedReflection`, no Phase 3; the 32 FLOOR(cen) cells, the
   3 in-scope LOEB-FP cells and the 4 companions stay the ENGINE's results, with the reflection assumption
   stated in prose. `S'` is the positive theory.
3. Branch pushed by Colomban.
Also: the thesis is DONE (2026-09-23); the audience from here is the JMLR paper and the project.
Phase 4 starts with the search-free cells (they never unfold the `search` clause, so they are safe
alongside (c)); SND/POS wait for (c) to settle.
* 2026-09-23 (evening): **Phase 4 search-free class DONE** (`8c49ec4`, `Cells/SearchFree.lean`): all 28 SF
  cells of the census as `sf_<L>_vs_<R> : EvalGraph n (pcode L) (pcode R) (pcode L) a ∧ EvalGraph n (pcode R)
  (pcode L) (pcode R) b` at an EXPLICIT fuel, by TRANSFER from the engine's `OutcomeSpec` theorems
  (`outcomeSpec_evalGraph_of_searchFree`); Mirror × Mirror as non-termination (`SimTest.mirror_vs_mirror`);
  the PA corollary `pa_proves_trAt_of_evalGraph` (certificate-free Σ₁-completeness) with 27 instances (54
  atoms); summary `searchFree_census`/`searchFree_pa_census`. FINDING: the engine's `eval` and `EvalGraph`
  step in LOCKSTEP on `const/self/opp/bot/sim/ite` (`evalGraph_of_eval_searchFree_core` at the SAME
  fuel — stronger than `AgentConverse.evalGraph_of_eval`'s existential `N`, and it would hold with
  `GuardAgree` too). `AgentConverse.eval_iff_evalGraph` quantifies `GuardAgree` over ALL formulas, so it
  cannot be discharged for search-free players; the search-free induction was redone with `Agent.Inv`
  at `sf = true`. Gate: 3339 jobs, census 1228 standard. **Tally: 12 Löbian/POS + 28 SF = 40 cells in `S'`.**
* 2026-09-23 (night): **ROUTE (c) DONE** — `271f6d7` (trusted base) + `f2cf619` (`Cells/JustSlot.lean`).
  THE GATE LEMMA IS A THEOREM: `guardCodeB_of_template : IsSemiformula LAct 6 g → guardCodeB g me opp k =
  guardCode g me opp` (a seventh entry is never read; via the identity vector `idVec6`, `subst_eq_self`,
  `substs_substs`). Representation: the budget slot is `#6`, LAST (`descVecB me opp k = descVec me opp ++
  [bnum k]`), so every six-variable template, `descVec`, `guardCode`, `gsubst`, `psubst` are
  byte-identical; the evaluator's `search` clause (Phi, Δ₁ blueprint, `case_iff`, `EvalN.search_iff`)
  now consults `guardCodeB g me opp k`; `search_iff₆` is the old reading on six-variable templates. Blast
  radius: 14 files, 34 sites, each one rewrite; **`Necessitation/` untouched** (rebuilt, green). The
  three parked cells, all unconditional on the constant-template diagonal `Just7 k := pSearch k ⌜GtmplJ7⌝
  …` (`evalGraph_JustV7_iff`: identical PLAY to `Just k` in every frame at every fuel — an opponent's guard
  that DESCRIBES the code is what differs, by design): `just7_self_coop_unconditional` (`(C, C)`),
  `just7_dupoc_coop_unconditional` (`(C, C)`, a THREE-guard mutual family, three-level ∧-elimination at
  slack `(21, 24)`), `cimcic_just7_coop_unconditional` (`(C, C)`). **FINAL GATE on `f2cf619`: 3340 jobs,
  0 errors, census 1301 standard. Tally: 43 cells in `S'` (15 Löbian/POS + 28 SF); ALL 14 in-scope
  LOEB-FF cells of the census are done.**
  DESIGN DEBT (record, not done): a seven-variable template is not `IsSemiformula LAct 6`, so `gsubst`
  leaves it and `psubst` never fills its frame slots — the evaluator is faithful for every program that
  never `.sim`s a seven-variable searcher (none of the three cells does); for a `.sim`-wrapped `Just7`
  the inner guard would read the INNER frame. The faithful extension (~150 lines): a middle case in
  `gsubst` — `IsSemiformula LAct 7 g ↦ subst (descVec me opp ++ [^#6]) g`, keeping `#6` — which changes
  the hypothesis of `gsubst_of_not` to `¬IsSemiformula LAct 7 g` and the middle case of
  `gsubstGraph`/`relabelTemplate_gsubst`. Do it before any `.sim`-of-Just cell.
  Note: `SPRIME_DESIGN_RATIONALE.md` does not exist on this branch (the trusted-base description lives in
  `HANDOVER_ARITHMETIZED_S.md` §1/§6 and the module docstrings) — write it or drop the reference.
  TRAPS (JustSlot): `IsSemiterm LAct n t` with `n : ℕ` silently forces `V = ℕ` (cast the arity);
  `nth_adjoin_one/two` SHIFT (`(x ∷ v).[1] = v.[0]`); `rw [show (4:V) = 0+1+1+1+1]` also rewrites the `4`
  inside `^#4`; `LogicalConnective.HomClass.map_and` fires on `Semiformula.Eval` (unfold the family defs,
  `simp only`); a `-/` inside prose (`four-/seven-`) closes a docstring.
* 2026-09-23 (night, later): **Phase 4 SND + POS classes DONE** (`5df270d`, `541cbb8`, `d988e63`, `7b7f609`;
  `Cells/SoundnessCells.lean` 1080 lines, `Cells/PositiveCells.lean` 990 lines). **SND (36 of 36)**: the general
  lemma `snd_else_of_false : ¬ (ℕ ⊨ trAt me opp φ) → ¬ LenProvableV TAct k (guardOf φ me opp)` (soundness of
  `TAct` in ℕ) + `trAt_subst` (the realization of a fragment guard in a proper frame IS the realization of its
  closed instantiation) + per-shape "not found" lemmas (`.plays .opp .self`, `.plays .opp (.bot P)`, `.neg`, `.eq`)
  + the search-free probers' plays from their probe results; NO engine transfer for SND (the falsity of a guard
  needs the arithmetized sub-play, which is the cell itself — the SF lockstep transfer stays the template;
  `search_either` handles nodes whose branches agree, e.g. Prudent's outer guard and Dupoc's/Just's probe against
  `.bot CooperateBot` inside OBot). All 36 on the ENGINE's own codes `pcode (L k)` at the engine's pads: 30 at
  every `k`, 6 for large `k` (they need a positive sub-fact: Guardian × EBot/OBot, Cupod × DBot/EBot, Wary ×
  DBot/EBot). **POS (10 of 13)**: `pos_GuardianBot_vs_DefectBot`/`_DBot` (fixed closed atoms: Guardian's guard
  names no `.self`, `tact_proves_plays_closed` by Σ₁-completeness in both readings + `tact_complete'`),
  `pos_DupocBot_vs_CooperateBot`, `pos_CupodBot_vs_DefectBot`, `pos_CIMCIC_vs_CooperateBot`,
  `pos_DIMCID_vs_DefectBot`, `pos_JustBot_vs_CooperateBot` (on `pcode (JustBot k)`: `guardCode_JustBot_eq`),
  `pos_WaryBot_vs_DefectBot` (the `.neg` guard, a Π₁ truth by determinism — `Pf.atomNeg`'s twin) — via the
  GENERIC engine-searcher description layer `SV g a` (Dupoc/Cupod/Wary ENGINE codes described like
  CIMCIC/DIMCID), `tact_all_of_both`, `found_of_all` (`K₀ + K₁·size k ≤ k`). NOT done (the "k̂ chain": the
  opponent's play in `V` needs the searcher's guard found in `V`, i.e. `TAct ⊢ ∀ k ≥ k̂, q(k)` + `NumeralFacts`
  instantiation): Dupoc × TFT, Just × TFT, CIMCIC × TFT, CupodTroll × Cupod. **The unreadability cells
  re-evaluated**: CIMCIC's guard against an opponent that defects against it is SELF-REFUTING
  (`cimcic_selfref_not_found`), so CIMCIC × DefectBot `(D, D)` (every `k`) and CIMCIC × OBot `(D, D)` hold in
  `S'` by soundness; **DIMCID × CooperateBot FLIPS to `(D, C)`** (`loeb_DIMCID_vs_CooperateBot`, bounded Löb on
  the self-fulfilling refutation "I do not cooperate"); verdicts for the rest in the hand-over report (DIMCID ×
  TFT/CupodTroll, Guardian × DIMCID, Wary × Mirror/Wary all FLIP by the same Löb; CIMCIC × DBot/EBot are genuine
  floors: a TRUE guard whose consequent needs PA to refute a self-search within the budget). **GATE on
  `7b7f609`+audit fix: 3346 jobs, 0 errors, census 1436 lines = 1436 commands, 1428 standard triples (the 7
  pre-existing subsets/axiom-free lines + `sfp_transpose` `[propext]`).** Tally: 43 + 36 SND + 10 POS + 3
  re-evaluated = 92 cells in `S'`. TRAPS: BSD `sed` has no `\b` (use `perl -pi`); `closedP` is FALSE on DBot/EBot/
  TFT/OBot (pronouns inside `.sim`) — `fragF` of a closed atom over them fails, so τ on `tmpl (.plays p q a)` must
  be stated with `fragP` only (`lMap_swap_tmpl_plays`); `pgrep -f "lake env lean …"` matches the polling shell's
  own command line (anchor with `^lean`, or poll a sentinel file); a `simp [closedDesc, descF, cl, dnumT]` on a
  template hangs (giant terms) — separate templates SEMANTICALLY (`tcode_ne_of_models`), Wary from Cupod at the
  non-terminating frame `(Mirror, Mirror)`; `EvalGraph.mono_le (by omega)` needs the source fuel explicit
  (`const_play 3 _ _ _`, not `_`); `one_ne_zero` is ambiguous under `open Arithmetic` (`_root_.`).
