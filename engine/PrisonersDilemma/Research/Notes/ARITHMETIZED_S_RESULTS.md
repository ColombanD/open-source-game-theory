# ARITHMETIZED_S_RESULTS — what the arithmetized layer proves (2026-09-10)

*Results record for the paper/thesis. Companion to `ARITHMETIZED_S_ROADMAP.md` (the plan and
its status log) and `M3_TRANSFER/` (design materials). Every statement below is a Lean theorem
in `arith/ArithS/` on branch `colomban-arith-m3`, with `#print axioms` = `[propext,
Classical.choice, Quot.sound]` (the census is `ArithS/Audit.lean`, rebuilt by `lake build ArithS`).
Notation follows `PROVABILITY_NOTATION.md`: `S ⊢_k φ` is the engine's `Pf k φ`; `PA ⊢ σ` is
Foundation derivability; `□_k` is the length-bounded provability sentence; `⊨` is truth in ℕ.*

## 1. The object: PA-`S`

Foundation (FormalizedFormalLogic) supplies PA, its Gödel numbering, the internal proof
predicate and IΣ₁ metatheory. On top of it:

* **Length.** `len` is the STRUCTURAL symbol count of a coded term/formula/sequent/derivation
  (`termLen`, `formulaLen`, `setLen`, `dlen`; Δ₁ in IΣ₁), with the meta twins `tlen/flen/mlen`
  and `dlen_quote : dlen ⌜d⌝ = mlen d`. A derivation is at least as long as any formula of its
  conclusion (`flen_le_mlen`).
* **`□_k`.** `LenProvable f k T φ := ∃ d < f k, Proof T d φ ∧ dlen T d ≤ k`; PROPERNESS
  (`quote_derivation_le`, `fbound k = exp³(12k)+1`) makes the code bound invisible, so
  `□_k` is Δ₁ (`LenProvableV`, the budget an object variable). Gate: the length-restricted
  Gödel sentence is true and provable with a proof-length lower bound
  (`true_lenGödel`, `provable_lenGödel`, `lower_bound_dlen_proof_lenGödel_fbound`).
* **Actions as constants.** `LAct = ℒₒᵣ + {c_C, c_D}`, `TAct = PA ∪ {c_C ≠ c_D, c_D ≠ c_C}`
  (Δ₁-axiomatized), τ = the constant swap. `TAct ⊢_k φ ↔ TAct ⊢_k τφ` at EVERY length
  (`lenProvable_fbound_swap_iff`): the engine's `Pf.transpose` (47 arms) becomes one theorem
  about codes, because derivations transport along language homomorphisms and `len` is
  symbol-blind.
* **Programs.** Codes `pConst a | pSelf | pOpp | pBot p | pSim p q | pIte b a p q | pSearch k g p q`
  (actions `0 = C, 1 = D`; `g` a six-variable template code). `relabel u w` re-values actions
  and acts on templates (`relabelTemplate`); `swapcode = relabel 1 0` is an involution.
  Program substitution `psubst me opp p` is one-shot as in the engine (`.bot` frozen, a search
  node's guard instantiated by the OUTER players), τ-equivariant unconditionally
  (`swapcode_psubst`).
* **Descriptions and guards.** A program `x` enters a sentence through its canonical
  description `(bnum (dnum x), dU x, dW x)` — a BINARY numeral of `min x (swapcode x)` and the
  two constants in the order that reconstructs `x` — so τ acts on guard sentences
  SYNTACTICALLY (`lMap_swap_guardSentenceA`) and descriptions have length `O(log x)`
  (Critch's assumption (b)). `guardCode g me opp := subst (descVec me opp) g`, with the code
  equation `⌜guardSentenceA a me opp⌝ = guardCode ⌜GtmplA a⌝ me opp`.
* **Evaluator.** `EvalGraph n me opp p a` — a Σ₁ fixpoint in IΣ₁ with fuel; clauses for
  const/self/opp/bot/sim/ite/search; the search clause consults `LenProvableV TAct k
  (guardCode g me opp)`. Deterministic and fuel-monotone (`EvalGraph.unique'`, `mono_le`).
  Truth equation: `ℕ ⊨ guardSentenceA a me opp ↔ ∃ n, EvalGraph n opp me opp a`.

## 2. Tier T1 — the red cell

```
Dupoc k := pSearch k ⌜GtmplA 0⌝ (pConst 0) (pConst 1)     -- "cooperate iff □_k(opp cooperates with me)"
Cupod k := swapcode (Dupoc k) = pSearch k ⌜GtmplA 1⌝ (pConst 1) (pConst 0)

theorem red_cell (k : ℕ) :
    EvalGraph 2 (Dupoc k) (Cupod k) (Dupoc k) 1 ∧ EvalGraph 2 (Cupod k) (Dupoc k) (Cupod k) 0
theorem red_cell_unique : any result at any fuel is (D, C)
```
Proof: the two guards are τ-transposes (code + swap equations), so by τ-closure they are
found together or not at all; both found ⇒ (soundness of `TAct` in ℕ + truth equation) Cupod
cooperates and Dupoc defects, but Dupoc, having found its proof, cooperates — contradiction
with determinism; so neither is found and the else-branches give (D, C). No Löb, no census,
no cost constant — the same argument as the engine's `outcome_DupocBot_vs_CupodBot`, now
about PA.

**Non-vacuity (`guard_fits`, `guard_fits'`).** `∃ K, ∀ k ≥ K, ∀ a ≤ 1,
flen (guardSentenceA a (Dupoc k) (Cupod k)) ≤ k`: for all large budgets the searcher's own
guard sentence fits inside its budget. This matters because with Foundation's UNARY numerals
it did not (the retired `Vacuity.lean`, commit 470ee43, proved `search_never_found` for every
top-level search node — the model was degenerate, and Critch's (b) is exactly what prevents
that). The threshold `K` is a constant of the fixed template; never quote it (Cantor pairing
makes it astronomically large; only "for all large k" is coding-independent).

## 3. Tier T2 — `S` relative to PA, in three theorems

A single same-budget theorem "`S ⊢_k φ ⇒ PA ⊢_k tr φ`" over all 33 rules of `Pf` is
IMPOSSIBLE, and we prove it; what survives is stated exactly.

**T2-NEG (`no_budget_keeping_transfer`).** For every inflation `e : ℕ → ℕ` and every
translation `tr` whose atom sentences name the opponent's code (as any evaluator-based
translation must):
`∃ k φ, S ⊢_k φ ∧ ¬ TAct ⊢_{e k} ⌜tr φ⌝`. Witness `k = 1`,
`φ = plays (const C) (bot^m (const C)) C` with `m = e 1 + 1`: `AtomProvable.mk` charges an
evaluation certificate by its STEPS (`n ≤ k`), never by the size of its conclusion
(`pf_size_or_atom`'s exception), while a PA proof is at least as long as its conclusion,
which contains the numeral of `bot^m (const C)`. Instances: `no_budget_keeping_transfer_tmpl`
for the concrete `trAt`, `…_guardCode` for the code the evaluator consults. A second departure
of the engine's cost model from a character count is the cheap citation `search_t` at
`numCost k = log₂ k + 1` (`atom_search_t_top`). Consequence: bounded HBL (Critch's (d)) is not
a corollary of anything in the engine; it is a separate obligation (M4).

**T2-CORE (`Core.Pf_core_sound`).** Budget-erased translation `tr A` (`.box _ ψ ↦
provabilityPred 𝗣𝗔 (tr ψ)`, `.diag _ tgt ↦ fixedpoint “x. prov x → tr tgt”` = Foundation's
`kreisel`, `.eq ↦ ⊤/⊥`, atoms by a parameter `A`), and `Leaf ψ` the conclusion shapes of the 17
non-core rules (evaluation certificates, refutation suppliers, source-reading rules):
`(∀ ψ, Leaf ψ → 𝗣𝗔 ⊢ tr A ψ) → S ⊢_k φ → 𝗣𝗔 ⊢ tr A φ`,
by `Pf.induct`, the 16 core arms discharged by Foundation's D1/D2/D3, the fixpoint lemma and
classical propositional logic. Reading: **the engine's Löbian core is a fragment of GL over
PA** — its `boxIntro/axK/axKf/box4/boxMono/diagF/diagB` and propositional glue are sound for
PA's real provability predicate; everything about budgets lives in the leaves.

**T2-AGENT (`playsProof_evalGraph`).** On the engine's MODEST programs (`modestP`: every
`.sim` argument a placeholder or closed — true of the whole zoo; players ≠ `.self/.opp`),
with the code translation `pcode : Prog → ℕ` and the guard `guardOf φ me opp := guardCode
(tcode φ) (pcode me) (pcode opp)` (= the template code of the closed instantiation, by the
substitution code equations `pcode_subst`/`tcode_subst`):
```
GuardAgreeT := ∀ φ me opp k, S ⊢_k (φ.subst me opp) → LenProvableV TAct k (guardOf φ me opp)
GuardAgreeF := ∀ φ me opp k m, S ⊢_m ¬(φ.subst me opp) → ¬ LenProvableV TAct k (guardOf φ me opp)
GuardAgreeT → GuardAgreeF → PlaysProof me opp body a n → ∃ N, EvalGraph N ⌜me⌝ ⌜opp⌝ ⌜body⌝ a
```
and `playsProof_evalGraph_searchFree`: for search-free programs, with NO oracle hypothesis.
Corollaries for `AtomProvable`; truth equation `models_trAt_plays` for the atom sentences.
Reading: **every evaluation certificate of `S` is a run of the arithmetized evaluator at the
same budgets, given agreement on the consulted `□_k` facts** — and that agreement IS bounded
D1, named as a hypothesis, never an axiom.

**T2-AGENT, the converse (`eval_iff_evalGraph`, `ArithS/AgentConverse.lean`).** With ONE
two-sided oracle, restricted to exactly the guards a modest match can consult,
```
GuardAgree := ∀ φ me opp k, fragF φ → Proper me → Proper opp → modestP me → modestP opp →
                (S ⊢_k (φ.subst me opp) ↔ LenProvableV TAct k (guardOf φ me opp))
eval_iff_evalGraph    : (∃ n, eval n me opp body = some a) ↔ ∃ N, EvalGraph N ⌜me⌝ ⌜opp⌝ ⌜body⌝ a
play_iff_evalGraph    : (∃ n, play n me opp = some a)     ↔ ∃ N, EvalGraph N ⌜me⌝ ⌜opp⌝ ⌜me⌝ a
outcome_iff_evalGraph : (∃ n, outcome n me opp = some (a, b)) ↔ (∃ N, EvalGraph N ⌜me⌝ ⌜opp⌝ ⌜me⌝ a) ∧ (∃ N, EvalGraph N ⌜opp⌝ ⌜me⌝ ⌜opp⌝ b)
plays_interp_iff      : (.plays me opp a).interp ↔ ℕ ⊨ trAt me' opp' (.plays me opp a)    (proper modest me, opp)
```
on proper modest players and a modest body. Both directions are inductions on the FUEL with
the engine program in the frame (`evalGraph_of_eval`: the engine's `eval` unfolded clause by
clause; `eval_of_evalGraph`: the arithmetized inversion lemmas, the result generalized to an
arbitrary code — on a coded modest frame the arithmetized evaluator only returns action codes,
`evalGraph_actCode`). Neither goes through `PlaysProof`, so no refutation-form hypothesis
enters: `GuardAgree.toT`/`GuardAgree.toF` show the `Iff` SUBSUMES both of T2-AGENT's
hypotheses on modest frames, the negative one by engine soundness (`Pf_sound`: a refuted guard
is not derivable, hence, by the `Iff`, not found), and `playsProof_evalGraph_of_guardAgree`
re-derives T2-AGENT from it through `playsProof_sound`. Reading: **given agreement on the
consulted `□_k` facts, the arithmetized evaluator and the engine's evaluator compute the same
plays on modest programs — an equivalence, and the engine's truth of a play-atom is the truth
in ℕ of its arithmetical translation.**

**Provability of the atom sentences (`pa_proves_trAt_inst`, `ArithS/Inst.lean`).** The
realized atom sentence is over `LAct`; Σ₁-completeness is over `ℒₒᵣ`. The INSTANTIATION hom
`inst : LAct →ᵥ ℒₒᵣ` (`c_C ↦ 0`, `c_D ↦ 1`, `ℒₒᵣ`-symbols fixed; `inst ∘ emb = id`,
`Structure.lMap inst (standardModel ℕ) = stdAct`) transfers truth (`models_inst : ℕ ⊨ lMap inst σ
↔ ℕ↓[LAct] ⊨ σ`), and the instantiated atom sentence is Σ₁ for EVERY frame and pair
(`hierarchy_lMap_inst_trAt_plays`: `tmpl (.plays …)` is `∃∃∃ (D ∧ D ∧ EvalGraph)` over
`emb`-images of Σ₁ semisentences, which `lMap inst` sends back to themselves). Hence
```
pa_proves_trAt_inst : GuardAgree → Proper me → Proper opp → modestP me → modestP opp →
    (∃ n, play n me opp = some a) → 𝗣𝗔 ⊢ lMap inst (trAt me' opp' (.plays me opp a))
pa_proves_trAt_inst_of_atomProvable : (same players) AtomProvable k (.plays me opp a) → 𝗣𝗔 ⊢ …
pa_proves_trAt_inst_searchFree      : (search-free players, NO oracle) AtomProvable k (.plays me opp a) → 𝗣𝗔 ⊢ …
```
by `sigma_one_completeness` (`𝗥₀ ⪯ 𝗣𝗔`). The players are PROPER (not a bare pronoun), not
`closedP`: no searcher is `closedP`, and `models_trAt_plays`/`plays_interp_iff` were generalized
accordingly (their proofs used closedness only through `≠ .self/.opp`). Composition with
T2-CORE: `Aι p q a := lMap inst (trAt p q (.plays p q a))`; `leaf_atom_sound` discharges the
`Leaf.atom` shape on proper modest players, `leaf_atomBoxImpl_sound` discharges
`Leaf.atomBoxImpl` for ALL programs and budgets, certificate or not (formalized
Σ₁-completeness, `provable_sigma_one_complete` — the remark closing `Core/Sound.lean` made good),
`Core.leaf_eqRefl_sound`/`leaf_eqNeg_sound` the identity leaves; `transfer_of_leaves =
Pf_core_sound Aι`. What `hleaf` still has to supply: the twelve SOURCE-READING leaves (`□_g guard
→ plays`: PA's unbounded box of the erased guard against the evaluator's length-bounded `□_k` of
the realized guard — bounded D1 in both directions, `GuardAgree` inside PA; boundary 1) and
`atomNeg` (Π₁: PA-internal determinism of `EvalGraph` — `EvalGraph.unique'` holds in every model
of IΣ₁, but the description-evaluation lemmas `val_bnumT`/`relabel_val_desc` are stated for ℕ
only, so the completeness-theorem route is not built). Reading: **every positive engine cell,
read as a PA sentence with the action constants instantiated, is a PA theorem — given agreement
on the consulted `□_k` facts, and unconditionally for search-free players.**

**The sentence for the paper.** "`S` is sound relative to PA wherever a character count
exists: its modal core for PA's provability predicate (T2-CORE) and its evaluation
certificates for the arithmetized evaluator at the same budgets (T2-AGENT). Where the engine
charges evaluation steps or cheap citations instead of characters, no PA proof length can
match at any inflation, and we prove it (T2-NEG). Budget-keeping soundness of `S` is
therefore exactly Critch's assumption (d), stated as the one open hypothesis." The
budget-erased world of T2-CORE is that of Barász et al.'s unbounded modal agents (cf. Berns'
mechanization); the contribution stays the BOUNDED `S` of T1/T2-AGENT.

**Addendum (2026-09-11) — the first M4 field: bounded D2 in rule form
(`ArithS/Cut.lean`, `lenProvable_mp`).** PA-`S` closes under modus ponens at additive cost:
`□_{k₁}(φ ➝ ψ) → □_{k₂} φ → □_{k₁ + k₂ + 10(|φ| + |ψ|) + 9} ψ` for sentences of `LAct` over
`TAct` (sharp: `k₁ + k₂ + 5|φ| + 10|ψ| + 9`), via one `cut` in Foundation's one-sided calculus
whose five sequents are charged exactly by `mlen`; with budget monotonicity
(`lenProvable_fbound_mono`) and the `verum` leaf (`lenProvable_verum`, length 2) it is the
character-count analogue of the engine's `mp` at cost `m₁ + m₂ + |ψ|`. The engine charges
only `|ψ|`; PA-`S` also pays `|φ|` because the cut formula is copied into the side sequents —
a constant-factor departure that any budget-keeping transfer must absorb, and not the
obstruction: T2-NEG locates that in the atoms. D1 (`e(k) + |□_k σ|`), D3 and the bounded
diagonal lemma remain open (M4).

**Addendum (2026-09-12) — M4: the parametric bounded Löb theorem and the Dupoc cell, conditional
on one hypothesis (`ArithS/Assembly/*`, `CutV`, `InstV`, `Diag`, `ProperV`, `NumeralFacts`,
`Transparency`, `ProgT`/`Instance*`; census 162).** Following Critch 2019's UNIFORM proof of PBLT:
programs are described by TERMS over the pairing `ppair x y = (x+y)²+y` (so a searcher's guard is
the `bnum k`-instance of a fixed formula: `guardCode_DupocV_eq_instB`), the Σ₁ box on codes
`LenDerivable` coincides in every model with the evaluator's Δ₁ `LenProvableV` (`ProperV`), bounded
D2 and ∀-instantiation hold on codes with `dlen` accounting in every model (`CutV`, `InstV`), the
parametric diagonal lemma holds over `TAct` (`Diag`), `TAct` carries the action axiom
`(c_C, c_D) ∈ {(0,1), (1,0)}` (without it NO guard sentence is `TAct`-provable — a vacuity found and
fixed), and then, for the fixed point `psi ↔ (□_{‖k‖³} psi(k) → (Dupoc k plays C vs Dupoc k ∧
Cupod k plays D vs Cupod k))`:
```
pblt_uniform     (hE : BoundedInnerNec d) : ∃ k̂, TAct ⊢ ∀k (k̂ ≤ k → psi(k))
dupoc_self_coop  (hE : BoundedInnerNec d) : ∃ k₀, ∀ k > k₀, EvalGraph 2 (Dupoc k) (Dupoc k) (Dupoc k) 0
                                                        ∧ EvalGraph 2 (Cupod k) (Cupod k) (Cupod k) 1
dupoc_finds_guard (hE) : ∃ k₀, ∀ k > k₀, TAct ⊢_k guard(Dupoc k) ∧ TAct ⊢_k guard(Cupod k)
BoundedInnerNec d := ∀ χ, ∃ C, ∀ V k, □_{‖k‖³} χ(k) → ∃ e ≤ C·(‖k‖^{3d} + 1), □_e (□_{‖k‖³} χ(k))   (inside every model)
```
Every other ingredient is a theorem; the hypothesis is exactly Critch's assumption (d) (bounded
inner necessitation with a polynomial expansion). **Sentence for the paper:** "In PA-`S`, Dupoc
cooperates with itself for all large budgets, given bounded inner necessitation with polynomial
expansion — Critch's assumption (d) — and every other step of the parametric bounded Löb argument
is a theorem about Peano arithmetic." Discharging (d) is `DESIGN_inner_necessitation.md`.

**Status of the hypothesis (2026-09-13).** Discharging `BoundedInnerNec 3` is under way on branch
`colomban-arith-u10` (`arith/ArithS/Necessitation/*`, ~10 modules, census 292): the library of
universal lemma-sentences, the two primitive proof-code moves, the composite steps, and the additive
length accounting are theorems; the chain builder, the formula walk, the per-tag fragments and the
top assembly remain (roadmap status log, brief §9–§10). Until then every M4 result is CONDITIONAL.

## 4. Boundaries (recorded, not gaps in proofs)

1. `.box` cannot be translated compositionally under LENGTH-bounded provability: a box carries
   its body's CODE as a numeral, `tmpl (.box k (ψ.subst me opp))` and `tmpl (.box k ψ) ⇜ desc`
   are PA-provably equivalent but not identical, and `□_k` is not invariant under provable
   equivalence. The code equations and τ are therefore proved on the box-free search-bot
   fragment; boxes are what T2-AGENT's hypotheses are about.
2. ~~Truth → `TAct ⊢` for the atom sentences (Σ₁-completeness over `LAct`).~~ CLOSED in its
   honest form by `Inst`: PA proves the atom sentences with the constants INSTANTIATED
   (`pa_proves_trAt_inst`: `𝗣𝗔 ⊢ lMap inst (trAt …)` with `c_C ↦ 0, c_D ↦ 1`; unconditional
   on search-free players). What stays open is the GENERIC form `TAct ⊢ trAt …` over `LAct`
   with `c_C, c_D` as constants. Before U0b (2026-09-12) `TAct` said only `c_C ≠ c_D`, a model
   could read the constants as any distinct pair, the evaluator's clauses compare action codes,
   and the generic form was not even true — and it IS needed downstream: the Löbian cells
   (Dupoc's self-cooperation, the whole M4 ladder) are `TAct ⊢ guard` statements over `LAct`,
   and with `c_C ↦ 5, c_D ↦ 7` every guard sentence is false, so nothing Löbian was ever
   `TAct`-provable (a vacuity). `TAct` now carries the action axiom
   `axAct : (c_C = 0 ∧ c_D = 1) ∨ (c_C = 1 ∧ c_D = 0)` (`TheoryAct.lean`; τ-symmetric, the axiom
   set stays literally swap-closed), its real-equality models are exactly the two standard readings
   `stdActS M`/`swapActS M` (`structure_eq_of_axAct`), and `tact_complete'` reduces `TAct ⊢ σ` to
   truth in both readings over every model of PA — the generic form is now an instance of
   completeness plus the `stdActV V` truth equations and their τ-twins. τ-symmetry (`Symmetry`)
   lives over `TAct`, atom provability over PA. Also open: the NEGATIVE atom
   `𝗣𝗔 ⊢ ∼ lMap inst (trAt … (.plays me opp a))` from a play of `b ≠ a` — Π₁, so outside
   Σ₁-completeness; it needs PA-internal determinism of `EvalGraph` (the route: completeness
   theorem + upward transfer of the positive run + `EvalGraph.unique'` in the model), and the
   description-evaluation lemmas are ℕ-only. This is the `atomNeg` leaf of T2-CORE.
3. The tau constructors `tvote/sys/selfIdx` are outside the translation (code 0).
4. ~~`GuardAgreeF` from engine soundness would need the converse of T2-AGENT.~~ CLOSED by
   `AgentConverse`: under the two-sided `GuardAgree` the refutation form is a theorem
   (`GuardAgree.toF`), and `eval ↔ EvalGraph` is an equivalence. What remains open is
   `GuardAgree` itself — bounded D1 AND its converse on the consulted guards.
5. Encoding sensitivity: Cantor pairing makes `‖⌜φ⌝‖` exponential in syntax depth; every
   quantitative statement is "for all large k".

## 5. Engine-side finding for the maintainers — HALF ADOPTED 2026-09-16

Charging `AtomProvable.mk` by `n + |φ| ≤ k` and `search_t` by `n + k + c_node` would remove
both departures from a character count and make a budget-keeping transfer plausible on the
size-gated fragment — at the price of every cheap-citation cell (the `(2k+64)` staggers,
`outcome_DupocBot_vs_CooperateBot` at pad `atom_cost 1`, which survives only as `eventual`).
A design decision, not part of M3.

**The atom half was adopted (branch `colomban-recost`, 2026-09-16, roadmap M6).**
`AtomProvable.mk` now requires `n + (Formula.plays me opponent a).size ≤ k` — the whole
conclusion (a first pass charged `opponent.size` only; the subject side has its own witness, an
untaken `.ite` branch that `ite_t` never pays). Consequences: T2-NEG is RETIRED (its witness is no
longer an engine theorem; `ArithS/Neg.lean` keeps the record and proves `no_budget_keeping_witness_pays`
and `pf_size : Pf k φ → φ.size ≤ k`, the exception of `pf_size_or_atom` closed); every outcome
VALUE survived; the blast radius was budget arithmetic only: 6 `Base/` sites, then ~120 errors
across 61 theorem files in two layers (Helpers first, their consumers second; the tau layer
last), repaired in one day by five agents plus the coordinator; the export of 155 cells, 4
staggered companions and 18 tau rows is BYTE-IDENTICAL (values, regimes, fuel pads all
unchanged — every `.eventual` witness and every internal threshold simply grew by the atom
size, typically `+ (Nat.log2 k + c)` for a searcher against a constant, twice `Nat.log2 k` at a
fired top-level search). Statement changes: `outcome_WaryBot_vs_DefectBot_defended` (non-cell
companion) moved from `WaryBot 16` to `WaryBot 32` — the 16 statement is FALSE under the new
charge (transcript 30), so the documented "phase transition at k = 16" is now "exploited at 2,
defended from 32"; `GuardianBot_defects_vs_DefectBot` at `GuardianBot (k+5)` (was `k+1`); the
WaryBot literal lemmas renamed `…wary32…`; `Tau/Theorems/Helpers` literal thresholds grew
(`2 ≤ K` → `7 ≤ K`, `6 → 25`, `10 → 43`, `c_guard k + 3 → 3 * c_guard k + 22`, …). Engine build
3278 jobs, both targets + `OutcomeCheck` green.
**The `search_t` half is NOT adopted** — it is needed only for a budget-keeping rule bridge
(roadmap M6, obstruction 2), which is waiting on a design decision.

## 6. Where things are

* Branch `colomban-arith-m3` (worktree `~/wt/osgt-arith-m3`): engine on Lean v4.33.1
  (proof-only repairs), `arith` requires the engine as a path dependency, `lake build ArithS`
  builds both (~3200 jobs; ~15 s incremental). The OneDrive checkout stays on
  `colomban-arith-s` (arith-only, engine v4.28) so the app and IDE keep working.
* Files: `Length, SequentLength, DerivationLength, Bew, MetaLength, Proper` (M1);
  `LangAct, TheoryAct, Transpose, Sound, Symmetry, ProofLength` (τ, lengths of proofs);
  `Prog, RelabelTemplate, Bnum, BewV, Guard, Subst, Eval, EvalN, SimTest, Template, RedCell,
  Fit` (agents, T1); `Core/Tr, Core/Sound` (T2-CORE); `Code, Neg, Agent, AgentConverse, Inst` (T2-NEG, T2-AGENT, its converse, the instantiation);
  `EngineBridge, Audit`.

## M5 — THE HYPOTHESIS DISCHARGED (2026-09-16): the headline results are UNCONDITIONAL

`BoundedInnerNec` — Critch's assumption (d), the single hypothesis every M4 result rested on — is
now a **theorem** at degree 16, and with it the two headline results hold with no assumption beyond
Lean's own three axioms:

```
ArithS.boundedInnerNec_sixteen        : BoundedInnerNec 16
ArithS.dupoc_self_coop_unconditional  : ∃ k₀, ∀ k > k₀, EvalGraph 2 (Dupoc k) (Dupoc k) (Dupoc k) 0
                                                       ∧ EvalGraph 2 (Cupod k) (Cupod k) (Cupod k) 1
ArithS.pblt_unconditional             : ∃ kHat, TAct ⊢ ∀¹ (leF kHat #0 🡒 psi)
```

All three at `[propext, Classical.choice, Quot.sound]`; build 3270 jobs; census 918 lines, one
pre-existing subset line (`substs_leF_imp`); zero `sorry`, zero `axiom` declarations, zero
`native_decide` in the package.

**THE PAPER SENTENCE.** *In Peano Arithmetic with a length-bounded provability predicate, Dupoc
cooperates with itself and Cupod defects against itself at every sufficiently large budget — and
the bounded inner necessitation principle this rests on is itself a theorem of the system, with
polynomial (degree 16) expansion.* Nothing is assumed; the conditional phrasing of the M4 addendum
is superseded.

**How it was discharged.** The verification proof is built as a derivation CODE inside every model:
a Σ₁ step-list producer that walks an arbitrary (possibly nonstandard) derivation, introduces every
code it mentions as an EIGENVARIABLE via ∃-elimination from a finite library of universal
lemma-sentences, and never writes a code as a numeral. Ten per-tag fragments, ten motive wrappers,
a `Derivation.induction1 𝚷` recursion over the derivation, certified re-description of every
derived formula, an axiom recogniser covering both the standard axioms and nonstandard induction
instances, and a per-χ pinning of the target's numeral.

**On the degree.** 16, not the design's 3. Every loss traces to ONE cause: variable indices are
charged in UNARY by the M1 length measure, which inflates the eigenvariable cap, the substitution
certificate's `qVec` iterate, and the per-step context growth. Critch asserts polynomial expansion
and does not fix a degree, so 16 satisfies the assumption as stated; the M4 results are parametric
in `d` (`pblt_uniform {d}`, `dupoc_self_coop {d}`), so nothing downstream depends on the value.
Three improvements are available and were deliberately deferred as optional: the substitution
certificate redesigned to take one `qVec` step per depth; fine occurrence accounting
(`fvOccF`-based) in place of full-length charging; and — the root fix — binary variable-index
charging in `Length.lean`, which touches the M1 constants and the whole census.

**Addendum (2026-09-23) — route B, the first cells beyond self-play (`Cells/DupocMirror.lean`, branch
`colomban-route-b`).** With the PBLT assembly parametrized by the Löb family (`Assembly/Family.lean`:
`LoebSound p S₀ S₁` — "a proof of the `k`-instance of `p` within the budget, slack to spare, makes
`p(k)` true in both standard readings" — and `family_found p : ∃ k₀, ∀ k > k₀, ∃ a ≤ k − slack,
LenDerivable TAct a (instB ⌜p⌝ k)`, the arithmetized `pblt_engine`; U10 re-packaged for a closed
sentence at an arbitrary budget, `closedInnerNec_sixteen`), the Mirror cells follow from one
conjunction family `pDM := qDM ⋏ qCM` (Mirror is τ-fixed, so the swap reading is Cupod's cell):
```
dupoc_mirror_coop_unconditional   : ∃ k₀, ∀ k > k₀, EvalGraph 2 (Dupoc k) Mirror (Dupoc k) 0 ∧ EvalGraph 3 Mirror (Dupoc k) Mirror 0
cupod_mirror_defect_unconditional : ∃ k₀, ∀ k > k₀, EvalGraph 2 (Cupod k) Mirror (Cupod k) 1 ∧ EvalGraph 3 Mirror (Cupod k) Mirror 1
```
— the engine's `outcome_DupocBot_vs_MirrorBot = (C, C)` and `outcome_CupodBot_vs_MirrorBot = (D, D)`
in PA-`S'`, unconditional, three standard axioms. The route-B census of all 155 cells by mechanism is
`ROUTE_B_CENSUS.md`; the plan is `ROUTE_B_SCOPE.md`.
Further route-B cells the same day, all unconditional on three standard axioms (`Cells/JustBot.lean`,
`Cells/DIMCID.lean`; merged gate `da5bd3c`, 3301 jobs, census 1071): the bot-wrapped Dupoc
self-cooperation `botDupoc_self_coop_unconditional` (`EvalGraph 3 (pBot (Dupoc k)) … 0`), **Just × Mirror
= (C, C)** (`just_mirror_coop_unconditional`), **DIMCID × DIMCID = (D, D)**, **DIMCID × Mirror = (D, D)**,
and the first MUTUAL-Löb cell **DIMCID × Cupod = (D, D)** (`Cells/DIMCID.lean`: the `.impl` guard through
the general translation `tmpl`, the conjunction of both bots' guards as one family). Finding recorded in
`ROUTE_B_SCOPE.md` §7: a bot whose guard freezes a budget-carrying snapshot (`JustBot k` with `DupocBot k`
inside) is NOT a `bnum k`-instance of a fixed formula, so cells that DESCRIBE it (Just × Just, Just ×
Dupoc, CIMCIC × Just) need either the transparency lift or the two-tier `JustBot2` — a user decision.
Then `Cells/CIMCIC.lean` (`fa60f3a`; gate 3303 jobs, census 1125): **CIMCIC × Dupoc = (C, C)** (the second
mutual family), **CIMCIC × Mirror = (C, C)**, and **CIMCIC × CIMCIC = (C, C)** with NO Löb and no
`BoundedInnerNec` — the guard is `A → A`, `TAct ⊢ ∀¹ qCC` by completeness, and the `k`-instance costs
`K₀ + K₁·size k`, below `k` for large `k`: the first cell of the POS class of `ROUTE_B_CENSUS.md` in `S'`,
and the `S'` reading of the engine's `Pf.implRefl`.
And `Cells/PrudentMirror.lean` (`9a71612`; FINAL GATE 3305 jobs, census 1163): **PrudentBot × Mirror =
(C, C)** — the NESTED-search family: both of Prudent's searches fire from one Löb fixed point, the
prudence conjunct ("I defect against DefectBot") carried as a conjunct of the family and the engine's
inner-search citation (`searchThenSearch_t`) replaced by ∧-elimination from the box. Nested searches are
not the §7 obstruction (their stored templates are budget-free); their price is a canonical description
uniform only above a standard threshold `KP`, absorbed by the family slack. **Route-B day-1 total: 12
cells unconditional in PA-`S'`** (Dupoc/Cupod × Mirror, bot-Dupoc self, Just × Mirror, DIMCID × DIMCID /
Mirror / Cupod, CIMCIC × Dupoc / Mirror / CIMCIC, Prudent × Mirror and its τ-twin), plus Dupoc/Cupod
self-play from M5; 11 of the 14 in-scope Löbian cells of `ROUTE_B_CENSUS.md`.
**Route (c) (2026-09-23 night, `271f6d7` + `f2cf619`).** Templates may read the searching node's own
budget through a seventh slot (`guardCodeB g me opp k := subst (descVec me opp ++ [bnum k]) g`; the
evaluator's `search` clause consults it); the gate lemma `guardCodeB_of_template` proves a six-variable
template never reads the extra entry, so every earlier statement is byte-identical. With it `JustBot`'s
frozen snapshot is a term in the slot, the stored template is a constant, and **Just × Just = (C, C)**,
**Just × Dupoc = (C, C)** (a three-guard mutual family) and **CIMCIC × Just = (C, C)** are unconditional in
PA-`S'` on the constant-template diagonal `Just7 k` (same play as `Just k` in every frame). With
`Cells/SearchFree.lean` (28 cells by transfer at the engine's own fuel — `eval` and `EvalGraph` step in
lockstep on the search-free constructors): **43 cells of the engine's matrix hold in PA-`S'`, all 14
in-scope Löbian cells among them; three standard axioms; census 1301.**

**Phase 4 (2026-09-23 night, `5df270d`…`a63037b`; FINAL GATE 3346 jobs, census 1428 standard).**
`Cells/SoundnessCells.lean`: all **36 SND cells**, on the ENGINE's own codes `pcode (L k)` at the engine's
pads — 30 at EVERY `k`, 6 for all large `k` — by the red cell's argument (`snd_else_of_false`: a guard false
in ℕ has no `TAct`-proof of any length, `TAct` being sound in ℕ), including WaryBot's `.neg` guards (the
`S'` twin of `Pf.atomNeg` is Π₁ truth by evaluator determinism). `Cells/PositiveCells.lean`: **10 of the
13 POS cells**, Löb-free (`found_of_all : TAct ⊢ ∀¹ q → … → ∃ k₀, ∀ k > k₀, LenProvableV TAct k (G k)`, the
instance costing `K₀ + K₁·size k`); the 4 remaining need the `k̂`-chain instantiation (machinery exists).
**Total: 92 cells of the engine's 155 hold in PA-`S'`** — every cell that is not a floor, an excluded bot
(Legible/Optim/Wary-floor), or one of the 4 `k̂`-chain POS cells.

**THE FINDING — `S'` DISAGREES with `S` on the "unreadability" cells, as the roadmap §4 predicted
("PA reads every source; negatives are weaker").** The engine closes 10 cells by censuses that rest on a
player being UNREADABLE by `S`'s rules (`no_provable_tailTo_unreadable`, the WV valuation censuses). In
PA every source is readable (Σ₁-completeness), and 6 of the 10 FLIP:
| cell | engine | `S'` |
|---|---|---|
| DIMCID × CooperateBot | (C, C) | **(D, C), PROVED** (`loeb_DIMCID_vs_CooperateBot`): DIMCID's guard "my cooperating implies your defecting" has a FALSE consequent, so it says "I do not cooperate" — SELF-FULFILLING; bounded Löb finds it and DIMCID defects |
| DIMCID × TitForTatBot | (C, C) | (D, D) — same Löb; TFT side a `k̂` chain, verdict only |
| DIMCID × CupodTrollBot | (C, C) | (D, C) — verdict only |
| GuardianBot × DIMCID | (C, C) | (D, D) — verdict only |
| WaryBot × MirrorBot | (C, C) | (D, D) — "¬(Mirror cooperates with me)" self-fulfilling under copying |
| WaryBot × WaryBot | (C, C) | (D, D) — same |
| CIMCIC × DefectBot, CIMCIC × OBot | (D, D) | **(D, D), PROVED** — kept, but by SOUNDNESS: CIMCIC's guard is SELF-REFUTING (found ⇒ CIMCIC cooperates ⇒ DefectBot would cooperate) |
| CIMCIC × DBot, CIMCIC × EBot | (D, C) | genuine floors (guard true, provable only above the budget) |
Reading: the engine's `S` is not only PA plus free citation; it is also PA MINUS the ability to read a
source its rules do not cover, and those two departures pull in opposite directions. The unreadability
censuses are artifacts of the rule set: under a real proof predicate a negative-Löb guard ("I will not
cooperate") is self-fulfilling and gets FOUND. This is the paper's clean example of a cell whose value is
a property of the proof system, not of the bots.

**The flips are THEOREMS (2026-09-24, `Cells/FlipCells.lean`, `9719f67`…`a1d28a7`; with `Cells/KhatCells.lean`
`1995f5a`/`1239a5b`; gate 3348 jobs, census 1512 standard).** All five verdict-only rows above are now
proved, each for all large `k`, each with its box form, each docstring naming the engine theorem it
contradicts: `loeb_DIMCID_vs_TitForTatBot` (D, D), `loeb_GuardianBot_vs_DIMCID` (D, D),
`loeb_WaryBot_vs_MirrorBot` (D, D), `loeb_WaryBot_vs_WaryBot` (D, D), `loeb_DIMCID_vs_CupodTrollBot`
(D, C) — the last on the budget-slot `CupodTroll7 k` (same play as `pcode (CupodTrollBot k)` in every frame).
**A stronger theorem fell out: `dimcid_vs_described` — in `S'`, DIMCID DEFECTS AGAINST EVERY described
opponent and finds its guard.** The self-fulfilling Löb never uses the guard's consequent: "my
cooperating implies X" is found because its antecedent ("I cooperate") is refuted by the very act of
finding it, whatever `X` is. So DIMCID is a universal defector under a real proof predicate — while the
engine has it COOPERATING in six cells (vs CooperateBot, TitForTatBot, CupodTrollBot, Guardian, and the
FLOOR-census cells vs DBot and EBot), every one of them by a census that cannot read DIMCID's own guard.
Consequence to check next: DIMCID × DBot and DIMCID × EBot, engine (C, C) by `no_provable_tailToS_floor`,
are expected to flip on DIMCID's side too — the floor class is not immune. Also from KhatCells: the four
`k̂`-chain POS cells (Dupoc/Just/CIMCIC × TFT `(C, C)`, CupodTroll × Cupod `(D, D)`) — POS 14/14 — and the
general lemma `found_of_all_above`; from FlipCells: `BoxConseq`/`found_of_box_conseq`, the `k̂`-chain for a
guard whose truth needs ANOTHER searcher's Löb-found guard, run in every model (no nonstandard
found-ness needed). **Tally: 105 cells of the engine's 155 have an `S'` statement; 97 agree with the
engine, 8 DISAGREE (6 flips + 2 CIMCIC cells kept for a different reason).**

**DIMCID's row is closed (2026-09-24, `Cells/DimcidFlips.lean`, `614144b`; gate 3350 jobs, census 1579, 1575
standard + the 4 pre-existing subsets).** The "consequence to check next" is settled, and it goes further than
DBot/EBot: **the floor class is not immune, and neither is a UNIVERSAL cell.** All seven engine cells with DIMCID
cooperating that `FlipCells` had left — every one closed by a census that never reads DIMCID's guard — flip on
DIMCID's side in `S'`, unconditional, with box forms:
| cell | engine | `S'` |
|---|---|---|
| DIMCID × DBot | (C, C), `no_provable_tailToS_floor` | **(D, C)** `loeb_DIMCID_vs_DBot` — DBot cooperates with a defector against `.bot DefectBot` |
| DIMCID × EBot | (C, C), floor + unreadability | **(D, D)** `loeb_DIMCID_vs_EBot` — all three frozen probes see a defection |
| DIMCID × OBot | (C, D), probe-first floor | **(D, D)** `loeb_DIMCID_vs_OBot` |
| DIMCID × DupocBot | **(C, D) at EVERY `k`** (`outcome_DIMCID_vs_DupocBot`, universal) | **(D, D) for all large `k`** `loeb_DIMCID_vs_DupocBot` — Dupoc's guard "DIMCID cooperates with me" is FALSE, never found (soundness) |
| DIMCID × JustBot | (C, D), floor | **(D, D)** `loeb_DIMCID_vs_JustBot` — on the budget-slot `Just7 k` (Just's half also on the engine code, `just_engine_vs_DIMCID_defects`) |
| DIMCID × PrudentBot | (C, D), floor | **(D, D)** `loeb_DIMCID_vs_PrudentBot` — Prudent's outer guard false |
| CIMCIC × DIMCID | (D, C), floor on both guards | **(D, D)** `loeb_CIMCIC_vs_DIMCID` — CIMCIC's guard self-refuting |
The Dupoc cell is the sharpest statement of the finding so far: the engine's theorem is universal (every
budget), `S'`'s is cofinal (every large budget), and they disagree — under a real proof predicate DIMCID's
"else-play" is not an else-play, it is FOUND, and the floor the engine charges for it does not exist. The
general lemma behind the row: **every closed code is described** (`describes_closed P`, the generic triple
`(cl (dnumT P), dUT P, dWT P)` of `Template.lean` in every model), so `dimcid_vs_closed`: DIMCID defects against
EVERY closed opponent; plus `DescribesAbove` for Prudent's threshold and the `SV`/`TD`/`TBD`/`TJ` tower instances
for the searchers. Row summary: `dimcid_flips_census`. With `loeb_DIMCID_vs_CooperateBot`, `_TitForTatBot`,
`_CupodTrollBot`, `loeb_GuardianBot_vs_DIMCID` and the Löbian `(D, D)` cells, **DIMCID cooperates nowhere in `S'`:
its row is D against every described opponent, and the engine's thirteen cooperative DIMCID-related cells are
census artifacts.** **Tally: 112 cells of the engine's 155 have an `S'` statement; 97 agree with the engine, 15
DISAGREE (13 flips + 2 CIMCIC cells kept for a different reason).**

**The floor verdict pass (2026-09-27, `Cells/FloorVerdicts.lean`, `620a2b5`; gate 3358 jobs, census 1792, 1788
standard + the 4 pre-existing subsets).** Every remaining engine "floor" cell without an `S'` statement — the 24
FLOOR(cen)/FLOOR(cen+cenU)/LOEB-FP cells with OptimBot/LegibleBot and the four staggered companions excluded, plus
the two `cenU` cells CIMCIC × DBot/EBot — was classified by the trichotomy (guard FALSE ⇒ soundness; TRUE and
PROVABLE ⇒ found, possibly a flip; TRUE and only long proofs ⇒ a genuine floor). **The numbers: (F) 0 cells,
(P) 0 cells, (G) 26 cells; 0 new flips.** Per side, (F) holds on one side of 8 cells (Guardian × CIMCIC/Dupoc/Just,
the three CupodTroll cells, and the search-free reactors), (P) on the prudence guard of Cupod × Prudent (both
orders), Wary × Prudent, Guardian × Prudent; but in every cell at least one guard is (G), so no cell theorem
exists. **The cell-exact tally** (`ROUTE_B_CENSUS.md`, "S' status per cell", script-generated over the 155 rows
and superseding the hand-kept 112/97/15): **107 cells stated in `S'`, 94 agree with the engine, 13 disagree**
(the twelve DIMCID flips and Wary × Mirror/Wary), 26 genuine floors, 22 excluded.

*Why they are all (G), in one sentence.* In each cell the floor guard is a TRUE Σ₁ sentence "X plays a against Y"
whose only evaluation witness passes through the ELSE branch of a search node whose guard σ is FALSE in ℕ; the else
clause is `¬ LenProvableV TAct k ⌜σ⌝`, and because `TAct ⊢ ¬σ` cheaply (evaluator determinism), that statement is
inter-derivable with additive-constant overhead with the bounded consistency statement `Con_TAct(k ± c)`. So the
whole residue of the floor class in `S'` is ONE proof-complexity question — *does `TAct` prove its own bounded
consistency `Con_TAct(k)` with proofs of length ≤ k?* — Pudlák's question (lower bound `k^ε`, polynomial upper
bound, the linear regime open). The engine's `+k` floor (`search_f` pays the failed budget) is its stipulated
answer; the DIMCID row was the exception precisely because DIMCID's guard is self-fulfilling WITHOUT the negative
(the found box refutes the antecedent directly), which is why it flipped and these do not.

*What is unconditional* (all on the engine's codes at its pads, three standard axioms): the SETTLED HALVES
`floor_<L>_vs_<R>_left/_right` of the 13 single-floor cells — DBot cooperates with Dupoc/Just/CIMCIC at every `k`,
EBot cooperates with Dupoc/Just/CIMCIC for all large `k`, CupodTroll cooperates with Dupoc/Just/CIMCIC at every `k`,
Guardian cooperates with CIMCIC/Dupoc/Just for all large `k`, OBot defects against Cupod for all large `k`
(`floor_settled_census` at one threshold) — and the TRUE GUARDS `floor_<L>_vs_<R>_true` (17 statements: the
floor side's consulted sentence `trAt me opp φ` holds in ℕ, so the residue is exactly its provability within `k`).
New sub-plays: `dupoc_vs_botCB_found`, `botDupoc_vs_botCB_found`, `just_vs_botDB`.

*The genuine floors and their lower-bound sub-facts* (each `σ` a FALSE guard; the sub-fact is
`TAct ⊢ ¬ LenProvableV TAct k ⌜σ⌝` within length ≤ k, i.e. `Con_TAct(k ± c)` within budget):
| cell(s) | floor guard (TRUE) | the else-play it runs through (σ FALSE) |
|---|---|---|
| Dupoc × DBot, Dupoc × EBot, Prudent × Dupoc (prudence), Guardian × Dupoc | "DBot/EBot/Guardian plays C vs Dupoc k", "Dupoc plays D vs `.bot DefectBot`" | Dupoc's guard vs `.bot DefectBot` / vs Guardian: "… plays C against me" |
| Just × DBot, Just × EBot, Just × Prudent (prudence), Guardian × Just | the same with the snapshot `.bot (DupocBot k)` in Dupoc's place | the snapshot's guard vs `.bot DefectBot`; Guardian's guard vs the snapshot |
| CIMCIC × DBot, CIMCIC × EBot, CIMCIC × Prudent (prudence), Guardian × CIMCIC | "DBot/EBot/Guardian plays C vs CIMCIC k", "CIMCIC plays D vs `.bot DefectBot`" | CIMCIC's SELF-REFUTING guard vs `.bot DefectBot` (found ⇒ `.bot DefectBot` cooperates); Guardian's guard vs CIMCIC |
| Dupoc/Just/CIMCIC × CupodTroll | "CupodTroll plays C vs me / vs the snapshot" | CupodTroll's `.eq` guard, a false closed equation |
| Cupod × OBot | "OBot plays D vs Cupod k" | Cupod's guard vs `.bot CooperateBot` |
| Guardian × Prudent | Guardian: "Prudent plays D vs `.bot CooperateBot`"; Prudent outer: "Guardian plays C vs me" | Prudent's prudence guard vs `.bot CooperateBot`; Guardian's guard vs Prudent |
| Prudent × Prudent | prudence: "Prudent plays D vs `.bot DefectBot`" | Prudent's outer guard vs `.bot DefectBot` |
| Prudent × EBot | outer: "EBot plays C vs Prudent k" | Prudent's outer guard vs `.bot DefectBot` (EBot's rung 1); EBot's C itself needs Prudent × `.bot MirrorBot` by Löb, not built |
| Wary × Dupoc, Wary × Just, Wary × Prudent, Cupod × Prudent (both orders), Just × Cupod, CIMCIC × Cupod | BISTABLE MODULO REFLECTION: each guard is true only in the scenario where the other is not found, and each Löb closure needs the cheap negative on the other | the partner's guard, in every scenario |

Sentence for the paper: *in PA-`S'` the engine's thirty-two floor cells split into the seven DIMCID cells, whose
"else-play" is a found self-fulfilling guard (the flips), and twenty-six cells whose value hinges on a single
proof-complexity fact — the length of `TAct`'s own bounded consistency proof relative to the budget — which the
engine stipulates (`+k`) and `S'` leaves open; the half of each cell that does not depend on it is a theorem.*

**The floors as dichotomies (2026-09-27, `Cells/FloorDichotomy.lean`, `1704ad6` + `5e5bde0`; gate 3359 jobs, census 1855
= 1851 standard + the 4 pre-existing subsets).** The 26 genuine floors are not admitted, not stipulated and not left as
prose: each is now a HYPOTHESIS-FREE theorem that proves the DEPENDENCE of the cell on its hinge without taking a side.
With `A_k` the cell's hinge — the Lean proposition `LenProvableV TAct k (guardCodeB (tcode φ) (pcode me) (pcode opp) k)`,
the evaluator's literal guard clause for the floor side's outermost search node at its own budget, written INLINE in the
statement (no structure, no named hypothesis, no conditional value in the ledger) —

  `dich_<L>_vs_<R> : ∃ k₀, ∀ k > k₀, (¬ A_k → ⟨the engine's value⟩) ∧ (A_k → ⟨the found-branch value⟩)`

both worlds at the engine's fuel on the engine's own codes. The ELSE world is the verdict pass's settled half plus the
search-else clause; the THEN world is the then-branch plus the partner's play — where the partner is a searcher whose guard
speaks about the floor side, SOUNDNESS of the found hinge and the evaluator's determinism recover its verdict
(`found_of_search_play`: a play through a search node with a constant else-branch it differs from means the guard was
found and the then-branch played; `play_of_found_opp_self/_opp_bot/_neg/_cimcic`). Cells with two or three hinges are
NESTED dichotomies (outer split on the hinge that settles the most), every determined case proved, the inconsistent
combinations absorbed by soundness. Prudent's prudence guard `B_k` stays a hinge of its own where the verdict pass rated
it (P) (five cells; its `k̂`-chain is not built), and is proved FOUND against EBot (`prudence_found_vs_EBot`).

| cell (engine value) | hinge(s) `A_k` = `□_k` of … (frame) | `¬A_k` world | `A_k` world | theorem (fuel) |
|---|---|---|---|---|
| Dupoc × DBot `(D, C)` | "DBot plays C vs me" (Dupoc, DBot) | `(D, C)` | `(C, C)` | `dich_DupocBot_vs_DBot` (4) |
| Dupoc × EBot `(D, C)` | "EBot plays C vs me" | `(D, C)` | `(C, C)` | `dich_DupocBot_vs_EBot` (5) |
| Dupoc × CupodTroll `(D, C)` | "CupodTroll plays C vs me" | `(D, C)` | `(C, C)` | `dich_DupocBot_vs_CupodTrollBot` (2) |
| Just × DBot `(D, C)` | "DBot plays C vs `.bot (Dupoc k)`" (Just, DBot) | `(D, C)` | `(C, C)` | `dich_JustBot_vs_DBot` (4) |
| Just × EBot `(D, C)` | "EBot plays C vs the snapshot" | `(D, C)` | `(C, C)` | `dich_JustBot_vs_EBot` (5) |
| Just × CupodTroll `(D, C)` | "CupodTroll plays C vs the snapshot" | `(D, C)` | `(C, C)` | `dich_JustBot_vs_CupodTrollBot` (2) |
| CIMCIC × CupodTroll `(D, C)` | "I coop with CupodTroll ⇒ it coops with me" (CIMCIC, CupodTroll) | `(D, C)` | `(C, C)` | `dich_CIMCIC_vs_CupodTrollBot` (2) |
| CIMCIC × DBot `(D, C)` | CIMCIC's guard vs DBot | `(D, C)` | `(C, C)` | `dich_CIMCIC_vs_DBot` (4) |
| CIMCIC × EBot `(D, C)` | CIMCIC's guard vs EBot | `(D, C)` | `(C, C)` | `dich_CIMCIC_vs_EBot` (5) |
| Guardian × CIMCIC `(C, D)` | CIMCIC's guard vs Guardian (CIMCIC, Guardian); Guardian's C settled | `(C, D)` | `(C, C)` | `dich_GuardianBot_vs_CIMCIC` (2) |
| Guardian × Dupoc `(C, D)` | "Guardian plays C vs me" (Dupoc, Guardian) | `(C, D)` | `(C, C)` | `dich_GuardianBot_vs_DupocBot` (2) |
| Guardian × Just `(C, D)` | "Guardian plays C vs the snapshot" (Just, Guardian) | `(C, D)` | `(C, C)` | `dich_GuardianBot_vs_JustBot` (2) |
| Cupod × OBot `(C, D)` | "OBot plays D vs me" (Cupod, OBot); OBot's D settled | `(C, D)` | `(D, D)` | `dich_CupodBot_vs_OBot` (5) |
| Prudent × Dupoc `(D, D)` | Prudent's OUTER guard "Dupoc plays C vs me" (Prudent, Dupoc) | `(D, D)` | `(C, C)` (soundness twice ⇒ Dupoc's guard and the prudence guard found — the companion's mutual-Löb world) | `dich_PrudentBot_vs_DupocBot` (3) |
| Prudent × Prudent `(D, D)` | the outer guard in self-play (one sentence, both sides) | `(D, D)` | `(C, C)` | `dich_PrudentBot_vs_PrudentBot` (3) |
| Prudent × EBot `(D, C)` | Prudent's outer guard "EBot plays C vs me"; prudence guard FOUND | Prudent D (EBot's C = the unbuilt Löb Prudent × `.bot Mirror`) | `(C, C)` | `dich_PrudentBot_vs_EBot` (7) |
| Just × Prudent `(D, D)` | NESTED: `J` = Just's guard "Prudent plays C vs the snapshot"; then Prudent's outer `A` "Just plays C vs me" and prudence `B` "Just plays D vs `.bot DefectBot`" (TRUE) | `¬J ⇒ (D, D)` | `J ⇒` Just C; Prudent C iff `A ∧ B` | `dich_JustBot_vs_PrudentBot` (3) |
| CIMCIC × Prudent `(D, D)` | NESTED: Prudent's outer `A` "CIMCIC plays C vs me"; then prudence `B` (TRUE) | `¬A ⇒ (D, D)` (CIMCIC's guard self-refuting) | `A ⇒` CIMCIC C; Prudent C iff `B` | `dich_CIMCIC_vs_PrudentBot` (3) |
| Guardian × Prudent `(C, D)` | NESTED: `G` = Guardian's guard "Prudent plays D vs `.bot CooperateBot`" (TRUE); then Prudent's `A` "Guardian plays C vs me", `B` (P) | `G ⇒ (D, D)`; `¬G ∧ ¬(A ∧ B) ⇒ (C, D)` | `¬G ∧ A ∧ B ⇒ (C, C)` | `dich_GuardianBot_vs_PrudentBot` (3) |
| Wary × Dupoc `(C, D)` | NESTED: `W` = Wary's `.neg` guard "¬(Dupoc plays C vs me)"; then Dupoc's `A` "Wary plays C vs me" | `W ⇒ (D, D)`; `¬W ∧ ¬A ⇒ (C, D)` | `¬W ∧ A ⇒ (C, C)` | `dich_WaryBot_vs_DupocBot` (2) |
| Wary × Just `(C, D)` | NESTED: `J` = Just's guard "Wary plays C vs the snapshot"; then `W` "¬(Just plays C vs me)" | `¬J ∧ ¬W ⇒ (C, D)`; `¬J ∧ W ⇒ (D, D)` | `J ⇒ (C, C)` | `dich_WaryBot_vs_JustBot` (2) |
| Wary × Prudent `(C, D)` | NESTED: Prudent's `A ∧ B` ("Wary plays C vs me", "Wary plays D vs `.bot DefectBot`" (P)); then `W` | `¬(A ∧ B) ∧ ¬W ⇒ (C, D)`; `¬(A ∧ B) ∧ W ⇒ (D, D)` | `A ∧ B ⇒ (C, C)` | `dich_WaryBot_vs_PrudentBot` (3) |
| Cupod × Prudent `(C, D)`, Prudent × Cupod `(D, C)` | NESTED: `Cu` = Cupod's guard "Prudent plays D vs me"; then Prudent's `A` "Cupod plays C vs me", `B` (P) | `Cu ⇒ (D, D)`; `¬Cu ∧ ¬(A ∧ B) ⇒ (C, D)` | `¬Cu ∧ A ∧ B ⇒ (C, C)` | `dich_CupodBot_vs_PrudentBot`, `dich_PrudentBot_vs_CupodBot` (3) |
| Just × Cupod `(D, C)` | NESTED: `J` = Just's guard "Cupod plays C vs the snapshot"; then `Cu` "Just plays D vs me" | `¬J ∧ ¬Cu ⇒ (D, C)`; `¬J ∧ Cu ⇒ (D, D)` | `J ⇒ (C, C)` | `dich_JustBot_vs_CupodBot` (2) |
| CIMCIC × Cupod `(D, C)` | NESTED: `G` = CIMCIC's guard; then `Cu` "CIMCIC plays D vs me" | `¬G ∧ ¬Cu ⇒ (D, C)`; `¬G ∧ Cu ⇒ (D, D)` | `G ⇒ (C, C)` | `dich_CIMCIC_vs_CupodBot` (2) |

(Values are (left, right) in the cell's order; the world columns list the determined scenarios of the nested split.)

**The reduction theorem** — the hinge is at least as hard as bounded consistency at `k`. For the simplest cell:
```
hinge_reduces_to_bounded_consistency_DupocBot_vs_DBot :
  ∃ C₀ C₁ : ℕ, ∀ k : ℕ,
    LenProvableV TAct k (guardCodeB (tcode phiDu) (pcode (DupocBot k)) (pcode DBot) k) →
    LenProvableV TAct (k + C₀ + C₁ * Nat.size k) ⌜negTwin ⇜ ![bnumT k]⌝
```
where `negTwin := ∼ boxK qDuB1 ⋎ ∼ boxK (τ qDuB1)`, `boxK χ (k) := □_k χ(k)` (the budget box at the budget ITSELF —
`Box_g` has `gBudget k`), and `qDuB1(k)` = `σ_k` = Dupoc's guard against `.bot DefectBot`, "`.bot DefectBot` plays C
against `DupocBot k`", FALSE in ℕ. So: the hinge within `k` ⇒ "`σ_k` or its τ-twin is not provable within `k`" within
`k + C₀ + C₁·size k` — one instantiation of the uniform theorem `tact_rDB_imp_negTwin : TAct ⊢ ∀ k, r(k) → negTwin(k)`
at `bnum k` (`lenProvable_inst_size`) and one modus ponens (`lenProvable_mp`), whose cut formulas carry the binary
numeral of `k`: the additive overhead `C₀ + C₁·size k` is a constant plus the formula lengths at `k`. The uniform theorem
is completeness (`tact_all_of_both`): in every model of `TAct` and both readings, DBot's cooperation means Dupoc did not
cooperate with `.bot DefectBot` (`probe_of_dbot_C_V`, determinism on the constant branches), hence Dupoc's guard was not
found (`not_found_of_SV_play`) — `σ_k` in the standard reading, its τ-twin in the swapped one. The DISJUNCTION is what
`TAct` proves: it cannot tell its two readings apart and internal τ-invariance of `□_k` is not available; at ℕ the two
disjuncts are equivalent by the exact τ-symmetry of `TAct`'s proofs (`lenProvable_fbound_swap_iff`), so
`negTwin_true_iff : ℕ ⊧ negTwin(k̄) ↔ ¬ LenProvableV TAct k (guardCode (tcode phiDu) (pcode (DupocBot k)) (pBot (pConst 1)))`
— the sentence SAYS `¬□_k σ_k`, a bounded-consistency instance (`TAct ⊢ ¬σ_k` cheaply, so `□_k σ_k → □_{k+c} ⊥`). The
CONVERSE is cheap and proved from the conjunction (`conjTwin := ∼ boxK qDuB1 ⋏ ∼ boxK (τ qDuB1)`):
```
bounded_consistency_reduces_to_hinge_DupocBot_vs_DBot :
  ∃ C₀ C₁ : ℕ, ∀ k m : ℕ,
    LenProvableV TAct m ⌜conjTwin ⇜ ![bnumT k]⌝ →
    LenProvableV TAct (m + C₀ + C₁ * Nat.size k) (guardCodeB (tcode phiDu) (pcode (DupocBot k)) (pcode DBot) k)
```
by the evaluator's determinism inside `TAct` (`tact_conjTwin_imp_rDB`: neither guard found ⇒ Dupoc's else-branch ⇒
DBot's probe fails ⇒ DBot cooperates, in both readings — `EvalGraph.search_iff₆`, `EvalGraph.unique_V'`-free, only the
constant branches). The ∨/∧ gap between the two directions is exactly the τ-symmetry `TAct` does not internalize.

Sentence for the paper: *the engine's floor rule stipulates the negative side of the linear-regime finite-consistency
question; `S'` proves the dependence and takes no side — each of the twenty-six genuine floors is a theorem
`(¬A_k → engine value) ∧ (A_k → the other value)` with `A_k` the hinge written inline, and for the simplest cell the hinge is
shown inter-derivable, up to an additive polylog overhead, with the bounded consistency of `TAct` at `k`.*
**LegibleBot (2026-09-27, spike, nothing landed).** Not a length problem after all: the exponential numeral is
the inner box's BUDGET inside the searcher's own description, and it is fixable within route (c) by writing the
inner budget as `gBudget #6` (polylog) — a linear stagger is impossible in `S'`, where necessitation is
polynomial. The block is that the box's body is COMPUTED FROM THE FRAME, and neither certified necessitation
(`boundedInnerNec_sixteen`: the `bnum K`-instance of a fixed formula; `closedInnerNec_sixteen`: a closed
sentence) has that shape; a third instance of the U10 kit is needed (`ROUTE_B_SCOPE.md` §9). Expected, unproven:
15 cells at the polylog stagger, and Legible × DIMCID a flip to `(C, D)`.

**The Prudent loose ends (2026-09-27, `Cells/PrudentLoose.lean`, `cefdb43` + `4e21d83`; gate 3360 jobs, census all standard but
the 4 pre-existing subsets).** Two of the dichotomy addendum's open items are closed, one is recorded as NOT closable.
* **The prudence hinge discharged where it was rated (P).** Against an engine searcher `SV g a k` (constant template, the
  budget in the search slot) Prudent's prudence guard `B_k` = "opp defects against `.bot DefectBot`" is the `bnum k`-instance
  of ONE fixed formula `qPiS g a` (Prudent above `KP`, the opponent by its `SV` triple; the me-slots inert). When the opponent's
  defection against the probe is its THEN-branch — its guard against the closed probe is a positive fact, found in every model
  above a threshold — `qPiS g a (k)` is true in every model of `TAct` above a threshold in both readings, so
  `TAct ⊢ ∀¹ (k̂ ≤ #0 🡒 qPiS g a)` by completeness and the instance fits `k` for all large `k` (`prudence_found_of_SV`, the
  `k̂`-chain): `prudence_found_vs_GuardianBot` (Guardian's guard "`.bot DefectBot` defects against `.bot CooperateBot`", a true
  closed atom; `guardian_botDB_V`), `prudence_found_vs_WaryBot` (Wary's `.neg` guard is a Π₁ truth by determinism; `wary_botDB_V`),
  `prudence_found_vs_CupodBot` (`cupod_botDB_V`), each `∃ k₀, ∀ k > k₀, LenProvableV TAct k (guardCode (tcode phiPi)
  (pcode (PrudentBot k)) (pcode (X k)))`, the τ-twins (`guardianT_botCB_V`, `waryT_botCB_V`, `dupoc_botCB_V`) supplying the
  swapped reading. The restated cells, originals untouched:

  | cell (engine value) | hinges now | `¬`-world / found world | theorem (fuel 3) |
  |---|---|---|---|
  | Guardian × Prudent `(C, D)` | `G` (Guardian's guard), then Prudent's outer `A` | `G ⇒ (D, D)`; `¬G ∧ ¬A ⇒ (C, D)`; `¬G ∧ A ⇒ (C, C)` | `dich_GuardianBot_vs_PrudentBot_prudenceFound` |
  | Wary × Prudent `(C, D)` | Prudent's outer `A`, then Wary's `W` | `A ⇒ (C, C)`; `¬A ∧ W ⇒ (D, D)`; `¬A ∧ ¬W ⇒ (C, D)` | `dich_WaryBot_vs_PrudentBot_prudenceFound` |
  | Cupod × Prudent `(C, D)`, Prudent × Cupod `(D, C)` | `Cu` (Cupod's guard), then Prudent's outer `A` | `Cu ⇒ (D, D)`; `¬Cu ∧ ¬A ⇒ (C, D)`; `¬Cu ∧ A ⇒ (C, C)` | `dich_CupodBot_vs_PrudentBot_prudenceFound`, `dich_PrudentBot_vs_CupodBot_prudenceFound` |

* **NOT discharged: Just × Prudent and CIMCIC × Prudent** (the table's "(TRUE)" prudence entries). There the opponent's
  defection against `.bot DefectBot` is its ELSE-branch (Just's guard "`.bot DefectBot` cooperates with `.bot (DupocBot k)`" is
  false; CIMCIC's guard against the probe is self-refuting), so `B_k` says "`TAct` does not prove the opponent's guard within
  `k`" — true in ℕ, but NOT in every model of `TAct` (a nonstandard proof of the false guard makes the searcher take its
  then-branch), so completeness cannot make it a `TAct`-theorem: `B_k` is itself the (G) residue of the verdict pass
  (`floor_JustBot_vs_PrudentBot_true`, `floor_CIMCIC_vs_PrudentBot_true` are its truth halves). For Just there is also §7: no
  fixed formula has the guard describing `pcode (JustBot k)` as its `bnum k`-instance. Both cells keep `B` as a hinge
  (`dich_JustBot_vs_PrudentBot`, `dich_CIMCIC_vs_PrudentBot` stand as stated).
* **Prudent × `.bot MirrorBot` by Löb** — the unbuilt piece of Prudent × EBot's `¬A` world. `Cells/PrudentMirror`'s family
  re-instantiated at the closed opponent `pBot Mirror` (`describes_closed`): `qPB1` ("`.bot MirrorBot` plays C against
  `Prudent k`"), `qPB2` (the prudence conjunct "`.bot MirrorBot` plays D against `.bot DefectBot`", a closed Σ₁ fact at fuel 4),
  their τ-twins, `pPB = (qPB1 ⋏ qPB2) ⋏ (τqPB1 ⋏ τqPB2)`, `loebSound_pPB : LoebSound pPB (14 + KP) 16` (`.bot MirrorBot` copies at
  fuel 5 = the `.bot` step + Mirror's sim step + Prudent's 3, `botMirror_step_V`), `family_found`:
  ```
  loeb_PrudentBot_vs_botMirror :
    ∃ k₀, ∀ k > k₀, EvalGraph 3 (pcode (PrudentBot k)) (pBot Mirror) (pcode (PrudentBot k)) (actCode .C) ∧
                    EvalGraph 5 (pBot Mirror) (pcode (PrudentBot k)) (pBot Mirror) (actCode .C)
  ```
  (fuel 3 as against Mirror: outer search, inner search, constant), the box form `loeb_PrudentBot_vs_botMirror_guards` (both
  guards, the outer one the `S'` twin of the engine's `prudent_botmirror_coop`), the τ-twin `loeb_PrudentT_vs_botMirror` `(D, D)`.
* **Prudent × EBot closed in both worlds.** EBot's ladder: rung 1 (`.bot DefectBot`) and rung 2 (`.bot CooperateBot`) Prudent
  defects (SND), rung 3 (`.bot MirrorBot`) Prudent cooperates (above), so EBot cooperates whatever Prudent's outer verdict
  (`ebot_C_of_probes3`, `floor_PrudentBot_vs_EBot_right`, pad 7), and
  `dich_PrudentBot_vs_EBot_full : ∃ k₀, ∀ k > k₀, (¬A_k → (D, C)) ∧ (A_k → (C, C))` at fuel 7 — the `¬A_k` world is now the
  engine's full `(D, C)`; the cell stays a genuine floor on Prudent's outer hinge alone.
