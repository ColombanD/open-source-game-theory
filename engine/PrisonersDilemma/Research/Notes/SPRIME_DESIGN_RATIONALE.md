# SPRIME_DESIGN_RATIONALE — the trusted base of PA-`S'` (2026-09-23)

*What a reader must accept BY EYE in `arith/ArithS/`, as opposed to what Lean checks. Companion
to `ARITHMETIZED_S_RESULTS.md` (what is proved), `ROUTE_B_SCOPE.md` (the plan and its status
log), `RED_CELL_AUDIT.md` (the trusted-base/checked-part split for ONE result, with the
mutation protocol — this note generalizes its §2 table to the whole package and does not repeat
it) and `HANDOVER_ARITHMETIZED_S.md` §1/§3/§6 (where things are, what is achieved, the traps).
Notation follows `PROVABILITY_NOTATION.md`: `□_k` is the length-bounded provability sentence,
`⊨` is truth in ℕ, `TAct ⊢ σ` is Foundation derivability; a turnstile never means Lean. Written
against the tree at `0e1effd` (branch `colomban-route-b`), after route (c) — every name below
is a declaration in that tree and is marked DEF (a definition, to be read) or THM (a theorem,
checked on Lean's three standard axioms).*

## 0. What "trusted" means here

A result of the package is a Lean theorem about definitions. The kernel guarantees the theorem
follows from the definitions; it guarantees nothing about whether the definitions say what the
prose claims. The trusted base is the set of definitions whose MEANING the reader must
establish by reading them, because every headline statement (`red_cell`,
`dupoc_self_coop_unconditional`, `pblt_unconditional`, the 92 route-B cells) is phrased in them:

> the theory `TAct` (`TheoryAct.lean`, with the language `LAct` and the transposition `swap` of
> `LangAct.lean`); the length measure `dlen` (`Length`, `SequentLength`, `DerivationLength`;
> meta twins in `MetaLength`); the bounded boxes `LenProvable`/`LenProvableV`/`LenDerivable`
> (`Bew`, `BewV`, `CutV`) with the code bound `fbound` (`Proper`); program codes on `ppair`
> (`Prog`) and their description terms (`ProgT`, `Bnum`); the guard template `gtmpl`/`GtmplA`
> (`Template`) and the general translation `tmpl`/`pcode` (`Code`); descriptions and guard codes
> `descVec`/`guardCode`/`descVecB`/`guardCodeB` (`Guard`); substitution `psubst`/`gsubst`
> (`Subst`); the evaluator `EvalGraph` (`Eval`); the box of the Löb argument `gBudget`/`Box_g`
> (`Assembly/Prep.lean` §4) and the family premise `LoebSound` (`Assembly/Family.lean`).

Everything else in the package is a theorem about these, and `Audit.lean` — rebuilt by every
`lake build ArithS`, its own import list, `#print axioms` on every headline theorem plus
`example`s that fail to compile if a theorem is renamed — is the census. The last docs commit
(`87b14b9`, recorded in `a63037b`) reports it as 1436 lines, 1428 of them the triple
`[propext, Classical.choice, Quot.sound]`, the rest pre-existing subsets or axiom-free lines
and `sfp_transpose` at `[propext]`. There is no `axiom`, `sorry` or `native_decide` in the
package (`arith/README.md`). Foundation (FormalizedFormalLogic) — its Gödel numbering, `Proof`,
`subst`, `⌜·⌝`, the IΣ₁ metatheory and the completeness theorem — is trusted as a library.

Two conventions the reader should carry through: every quantitative statement is "for all
large `k`" with an EXISTENTIAL threshold, never a quoted number (Cantor pairing makes every
constant astronomical and coding-dependent: `ROUTE_B_SCOPE.md` §4); and the size of the trusted
base is what makes the audit feasible — `RED_CELL_AUDIT.md` counts its T1–T7 at under 300
lines of definitions, and route (c) added two (`descVecB`, `guardCodeB`).

## 1. The theory `TAct = PA + {c_C, c_D}`

**The language (DEF, `LangAct.lean`).** `LAct := ℒₒᵣ + Language.constant Act` with
`inductive Act` = `C | D`; the constants are `const Act.C`, `const Act.D` (terms `cterm Act.C`,
`cterm Act.D`). The Gödel encoding is written by hand so that "an `ℒₒᵣ`-formula has the SAME code
in both languages", which is what lets PA's Δ₁ axiom class be reused. `emb : ℒₒᵣ →ᵥ LAct` is the
inclusion; `swap : LAct →ᵥ LAct` exchanges the two constants and fixes everything else — τ IS a
language automorphism, not an operation on codes.

**The axioms (DEF, `TheoryAct.lean`).** `TAct := insert axAct (insert axAct' (insert axNe
(insert axNe' (Theory.lMap emb 𝗣𝗔))))`, i.e. PA transported along `emb` plus four closed
sentences: `axNe : c_C ≠ c_D`, its transpose `axNe'`, and `axAct : (c_C = 0 ∧ c_D = 1) ∨ (c_C = 1
∧ c_D = 0)` with its transpose `axAct'`. Each axiom is present in BOTH orientations so that the
axiom set is literally closed under `swap` (`lMap_swap_mem_TAct`, THM) — closure up to a
one-line derivation would cost `k` vs `k + c`, and the red cell needs an exact iff. `TAct` is
Δ₁-axiomatized (THM, via `isFormulaOR` and the shared codes), which is what Foundation's `Proof`
predicate needs.

**Why constants and not numerals.** Roadmap §2.4: a numeral is rigid — a derivation may reason
about it arithmetically, so "swap the codes of C and D" is not a symbol substitution and does not
transport derivations. With the actions as fresh constants, τ = `swap` acts on derivations node
for node (`Transpose.lean`: `mlen_lMapT`, `transpose_exists` — a `TAct`-proof of `φ` has a twin
proof of `swap φ` of the SAME length, THM) and the engine's 47-arm `Pf.transpose` becomes one
theorem about codes, `lenProvable_fbound_swap_iff` (`Symmetry.lean`, THM). Audit item inherited
from the roadmap: NO action numeral in any axiom or agent-facing definition — actions enter
sentences through `cterm`/`actT`, programs through the re-valuation terms `dU`/`dW` (§4).

**The vacuity fixed on 2026-09-12 (`axAct`).** Before U0b `TAct` said only `c_C ≠ c_D`. A model
could then read the constants as any distinct pair; the guard sentences feed the constants as
action VALUES into `relabel` (§4), which is meaningful only on `{0, 1}`, so in such a model the
described program is garbage and every guard sentence is false — `TAct ⊬ guard` for every `k`,
and nothing Löbian was ever `TAct`-provable. `axAct` is the repair (`TheoryAct.lean` docstring;
results note §4 boundary 2). It is τ-symmetric, so the swap-closure above survives.

**The two readings, and why completeness over exactly those is the method (THM).**
`stdActS M` reads `c_C ↦ 0, c_D ↦ 1` on any `ORingStructure M`; `swapActS M` reads them the other
way (`stdActS_nat : stdActS ℕ = stdAct`; `stdActV V` of `Det.lean` is the same structure as a
pull-back). `structure_eq_of_axAct`: every real-equality `LAct`-structure satisfying `axAct` IS
one of the two. Hence `tact_complete'` (`Diag.lean`): a sentence true in `stdActS M` AND
`swapActS M` for every `M ⊧ PA` is a `TAct`-theorem (Foundation's
`Theory.Proof.complete_on_eq_models`, needing `eqAxiom_weakerThan_TAct`). This is the whole
positive method of the package: a guard is shown `TAct`-provable never by exhibiting a
derivation but by proving its truth in both readings of every model — the swap reading being,
by the truth equations of §7, the cell of the TRANSPOSED programs. Soundness in ℕ (`stdAct` is a
model) is the whole negative method: `models_trAt_of_lenProvableV` (`Agent.lean`), a found
guard is true, is what closes the red cell and the 36 SND cells.

## 2. The length `dlen`

**Terms and formulas (DEF, `Length.lean`).** `termLen`/`formulaLen` are Σ₁ functions on
Foundation's codes, defined by its `TermRec`/`UformulaRec1` recursion schemes: the number of
symbols of the decoded syntax tree. Two commitments from the docstring: "it is STRUCTURAL — a
function symbol or relation symbol counts `1` whatever its code, so swapping two constant
symbols preserves it exactly"; and "variable indices are charged unary". Symbol-blindness is
what makes `tlen`/`flen` invariant under ANY language hom (`LangAct.lean`), hence under `swap`.

**Sequents and derivations (DEF, `SequentLength.lean`, `DerivationLength.lean`).** `setLen s`
sums `formulaLen` over the bit-set `s`; `dlen d` is the graph of a `Fixpoint` on pairs and reads,
per the docstring, "`Σ_{nodes} (1 + setLen (sequent at the node)) + Σ_{exsIntro nodes} termLen
(witness)`: the length of the derivation written out as its list of sequents, plus the witness
terms of ∃-introductions". Both charges are forced by PROPERNESS: weakening introduces arbitrary
formulas, so the target sequent must be charged; an ∃-witness with `#0` not occurring in the body
would otherwise be unconstrained. `dlen` is defined on all codes of the right shape; validity
(`Derivation T d`) is combined with it only in `Bew`.

**The meta twins (THM, `MetaLength.lean`, `ProofLength.lean`).** `tlen`/`flen`/`sqlen`/`mlen` are
the same counts on Foundation's meta syntax by structural recursion; `termLen_quote`,
`formulaLen_quote` and `dlen_quote : dlen T ⌜d⌝ = mlen d` say the coded functions compute them on
Gödel codes in every model. `flen_le_mlen`: a derivation is at least as long as any formula of
its conclusion (every node charges its whole sequent) — the fact behind "a PA proof of a
sentence that writes a program's code is at least as long as that code".

**Properness (DEF `Proper` in `Bew.lean`; THM `quote_derivation_le` in `Proper.lean` at ℕ,
`properV_TAct` in `ProperV.lean` in every model).** `fbound k := Exp.exp (Exp.exp (Exp.exp (12 *
k))) + 1`, a tower of three exponentials in a fixed multiple of `k`, is a Σ₁-definable function
such that every derivation of length `≤ k` has code `< fbound k`. It is a coding estimate, not a
threshold the reader should interpret; its only job is §3.

**The honest residue.** (i) Variable indices are UNARY in `dlen`: Critch's assumption (b),
"`k` in `O(lg k)` characters", is met for budgets and program codes (binary numerals, §4) but
not for the raw ℒₒᵣ coding of variables; the results note's M5 entry traces every loss in the
U10 degree (16 rather than the design's 3) to this one cause. (ii) A quoted formula `⌜φ⌝` used as
a numeral (Foundation's Gödel numeral) is UNARY, which is why `Box_g` carries "the unary Gödel
numeral of `χ` (a constant; never evaluated)" and why the constant `C` of `BoundedInnerNec`
depends on `χ` (`Assembly/Prep.lean` §4, §6). Neither affects a "for all large `k`" statement;
both are recorded rather than hidden.

## 3. The predicate `□_k`

Three boxes, one meaning (DEF):

* `LenProvable f k T φ := ∃ d < f (numeral k), Proof T d φ ∧ dlen T d ≤ numeral k` (`Bew.lean`):
  meta budget `k : ℕ`, parametric in the bounding function `f`, written as the Π₁ semisentence
  `lenProvable`. Foundation's `Theory.RestrictedProvable` with the LENGTH conjunct added —
  Critch's Notation 3.5 with `dlen` as "characters".
* `LenProvableV T k φ := ∃ d < fbound k, Proof T d φ ∧ dlen T d ≤ k` (`BewV.lean`): the same
  with `k : V` an object element, written as the Δ₁ semisentence `lenProvableV`. This is the box
  the evaluator's `search` clause consults (§6), because the budget is stored in the program
  code. "Δ₁: the code bound `fbound k` makes the search bounded; properness is what makes the
  bound invisible."
* `LenDerivable T k φ := ∃ d, Proof T d φ ∧ dlen T d ≤ k` (`CutV.lean`): Σ₁, NO code bound. This
  is the box of the Löb argument (`bewB a n k := LenDerivable TAct a (instB n k)`, `InstV.lean`;
  `Box_g`, §4 of `Prep.lean`), because bounded D2 and inner necessitation are proved by
  constructing derivation CODES inside arbitrary models, where the code bound would be an
  obstacle.

The tie (THM): `lenDerivable_iff_lenProvableV : LenDerivable TAct k φ ↔ LenProvableV TAct k φ`
(`ProperV.lean`), in every model of IΣ₁ — the Löb argument's Σ₁ box and the evaluator's Δ₁ box
coincide. Properness "never bites" is therefore a theorem, not a hope; `Proper` in `Bew.lean`
is the hypothesis form kept for the M1 gate (`lower_bound_dlen_proof_lenGödel`, THM: every
proof of the length-restricted Gödel sentence is longer than `k`).

What the reader must decide by eye: that `dlen` is an acceptable "number of characters" (§2)
and that `LenProvableV` says "some `T`-proof of `φ` has at most `k` characters". Nothing in the
package is sensitive to the choice of `fbound` beyond properness.

## 4. Programs as codes; descriptions; templates; the budget slot

**Codes (DEF, `Prog.lean`).** `ppair x y := (x + y) * (x + y) + y`, and
`pConst a = ppair 0 a + 1`, `pSelf = ppair 1 0 + 1`, `pOpp = ppair 2 0 + 1`, `pBot p = ppair 3
p + 1`, `pSim p q = ppair 4 (ppair p q) + 1`, `pIte b a p q = ppair 5 (ppair b (ppair a (ppair
p q))) + 1`, `pSearch k g p q = ppair 6 (ppair k (ppair g (ppair p q))) + 1`. Actions are the
values `0 = C`, `1 = D`. Sub-programs sit strictly below their parent and the constructors are
injective and disjoint (THM, `le_ppair_left`/`le_ppair_right`, `ppair_ext_iff` + the tag).

**Why `ppair` and not Foundation's `pair` (`M4_BOUNDED_HBL/BRIEF.md` §2).** Foundation's Cantor
pair is defined by an `if` that no ℒₒᵣ-term denotes. The parametric bounded Löb argument needs a
searcher's guard to be the `bnum k`-instance of ONE fixed formula — Critch's "source with `k`
written in binary" — which requires the description of `pSearch k g p q` to be a TERM with `k`
as a leaf. `ppair` is injective, Δ₀-decodable, monotone and term-expressible (`ppairT` on term
codes, `ppairTT` on meta terms, `ProgT.lean`); the price is term duplication by a constant factor
per nesting level, harmless at the zoo's constant depth. Rejected: structural descriptions as
formulas (reshapes every bridge module), indexing the family by the whole code (the final
instantiation would have to decode a numeral inside PA), a `pair` symbol in `LAct` with a
defining axiom (kills the instantiation hom `inst : LAct →ᵥ ℒₒᵣ` of `Inst.lean`).

**τ on codes (DEF `relabel`, `swapcode`; THM `swapcode_swapcode`).** `relabel u w x` re-values
every action occurrence of `x` (`pConst`/`pIte` values, and stored templates through
`relabelTemplate`, `RelabelTemplate.lean`, the symbol map `c_C ↦ …, c_D ↦ …` on `^func` nodes);
`swapcode := relabel 1 0` is an involution. `relabelTemplate 1 0 ⌜φ⌝ = ⌜lMap swap φ⌝`
(`relabelTemplate_quote`, THM): the code-level τ IS the syntactic `swap`.

**Descriptions (DEF, `Guard.lean`, `Template.lean`, `ProgT.lean`, `Bnum.lean`).** A program `x`
enters a sentence as the triple `(progT (dnum x), dU x, dW x)`, meaning `relabel (dU x) (dW x)
(dnum x)`: `dnum x` is the canonical member of the τ-orbit, `if x ≤ swapcode x then x else
swapcode x`; `dU x`/`dW x` are the constants `c_C`/`c_D` in the order that reconstructs `x`
(the numerals `0`/`1` on a tie); `progT x` is the structural term of the code over `ppairT` with
binary-numeral leaves (`bnum`), total (`progT x = bnum x` on non-shapes). Meta side: `progTT`
with `⌜progTT x⌝ = progT x` in every model and the truth equation `val_progTT_V : (progTT x).val
= x`; `bnumT n` with `⌜bnumT n⌝ = bnum n` and length `O(size n)` (all THM). So the swap of the two
constants turns the description of `x` into that of `swapcode x` SYNTACTICALLY, in every case,
and a description has length `O(log x)` — Critch's (b) for codes. The retired `Vacuity.lean`
(commit 470ee43) proved that with Foundation's unary numerals NO top-level search could ever
succeed (`search_never_found`); `guard_fits` (`Fit.lean`, THM) is the positive replacement: for
all large `k` the searcher's own guard sentence is shorter than `k`.

**The six-variable template (DEF, `Template.lean`).** `gtmpl : 𝚺₁.Semisentence 7` reads
`x₁ u₁ w₁ x₂ u₂ w₂ t ↦ ∃ me, relabelDef me u₁ w₁ x₁ ∧ ∃ opp, relabelDef opp u₂ w₂ x₂ ∧ ∃ n,
evalGraphDef n opp me opp t` — "the program described by `(x₂, u₂, w₂)` plays `t` against the one
described by `(x₁, u₁, w₁)`"; note the run is `EvalGraph n opp me opp t`, the OPPONENT's play.
`Gtmpl := lMap emb gtmpl.val` lifts it to `LAct`; `GtmplA a := Gtmpl ⇜ ![#0, …, #5, actT6 a]`
fixes the action as the constant `c_a`; `descVec me opp` is the six-entry description vector,
`guardCode g me opp := subst LAct (descVec me opp) g`, and the meta sentence `guardSentenceA a
me opp := GtmplA a ⇜ descTerms me opp` has code `guardCode ⌜GtmplA a⌝ me opp`
(`quote_guardSentenceA`, THM). Dupoc is `Dupoc k := pSearch k ⌜GtmplA 0⌝ (pConst 0) (pConst 1)`
(`RedCell.lean`); compare by eye with the engine's `DupocBot k := .search k (.plays .opp .self
Action.C) (.const C) (.const D)`.

**The general translation (DEF, `Code.lean`).** `pcode : PD.Prog → ℕ` and `tmpl : PD.Formula →
Semisentence LAct 6` are mutually recursive like `Prog`/`Formula`; `tcode φ := ⌜tmpl φ⌝` is what
`pcode (.search k φ p q)` stores. Clauses: `.plays p q a ↦ ∃ x y n, D_p(x) ∧ D_q(y) ∧ EvalGraph n
x y x c_a` (the engine's `play`), with a placeholder described by the frame triple and any other
program by the closed description of its code (`progAux`, `descF`, `closedDesc`); `.impl`/`.neg`
↦ `🡒`/`∼`; `.eq p q ↦ ∃ x y, D_p(x) ∧ D̂_q(y) ∧ x = y` with the frozen literal `q` always
described by its code; `.box k ψ` ↦ "the instance of `ψ` at the current players has a
`TAct`-proof of length `≤ k`" (`guardCodeG`, `lenProvG`, the constant `numTB (tcode ψ)`);
`.diag ↦ ⊥` (`tmpl_diag`; side condition `noDiag`); the tau constructors `.tvote/.sys/.selfIdx`
↦ the non-shape code `0` (`pcode_tvote`, `pcode_sys`, `pcode_selfIdx`; side condition `noTauP`).
`trAt me opp φ := tmpl φ ⇜ descTerms (pcode me) (pcode opp)` is the realized sentence and
`quote_trAt` (THM) its code equation. Side conditions the theorems carry: `fragP`/`fragF` (atoms
name a placeholder or a `closedP` program, no box inside a template, no tau), `modestP` (every
`.sim` argument a placeholder or closed — true of the whole zoo), `Proper` (a player is not a
bare pronoun).

**Route (c): the seventh budget slot (DEF, `Guard.lean`, 2026-09-23).** `descVecB me opp k :=
descVec me opp` extended by `bnum k` in the seventh entry, and `guardCodeB g me opp k := subst
LAct (descVecB me opp k) g`. The evaluator's `search` clause consults `guardCodeB g me opp k`
with the NODE'S OWN budget. Why: `JustBot k := .search k (.plays .opp (.bot (DupocBot k)) C) …`
carries `k` inside its guard, in the frozen snapshot; with six-variable templates its stored
template CODE depends on `k` and no guard that describes `Just k` is a `bnum k`-instance of a
fixed formula (`ROUTE_B_SCOPE.md` §7). With the slot, the snapshot's budget is a term `#6` and
the template is the constant `GtmplJ7` (`Cells/JustSlot.lean`); `JustV7 k := pSearch k ⌜GtmplJ7⌝
(pConst 0) (pConst 1)` plays exactly as `JustV k` in every frame at every fuel
(`evalGraph_JustV7_iff`, THM), and `guardCodeB_GtmplJ7` (THM) says its guard against `opp` is the
bot-wrapped Dupoc's guard against `opp`. Why LAST: so that every six-variable template is
literally untouched — the gate lemma `guardCodeB_of_template : IsSemiformula LAct 6 g →
guardCodeB g me opp k = guardCode g me opp` (`Subst.lean`, THM, via `idVec6`, `subst_eq_self`,
`substs_substs`, `termSubstVec_descVecB_idVec6`) makes every earlier statement byte-identical;
`EvalGraph.search_iff₆` is the old reading on six-variable templates. This is the "node data"
fix `FitBox.lean` describes for box budgets, applied one level down.

**Known limitation (the `.sim` debt, `ROUTE_B_SCOPE.md` §8).** `gsubst` (§5) instantiates a
template iff `IsSemiformula LAct 6 g`; a seven-variable template fails that test, so `gsubst`
leaves it unchanged and `psubst` never fills its frame slots. The evaluator is faithful for
every program that never `.sim`s a seven-variable searcher (none of the three JustSlot cells
does); for a `.sim`-wrapped `Just7` the inner guard would read the INNER frame, against the
engine's `Prog.subst`. The recipe (not done): a middle case in `gsubst`, `IsSemiformula LAct 7 g
↦ subst (descVec me opp ++ [^#6]) g` keeping `#6`, which changes the hypothesis of
`gsubst_of_not` to `¬IsSemiformula LAct 7 g` and the middle case of `gsubstGraph` and
`relabelTemplate_gsubst`. Do it before any `.sim`-of-Just cell.

## 5. Substitution `psubst`/`gsubst`

**The engine's semantics to mirror.** `Prog.subst` (`Program.lean`) is ONE-SHOT: `.self ↦ me`,
`.opp ↦ opp`, `.bot p ↦ .bot p` (a barrier — frozen), and it descends into a `.search` node's
guard through `Formula.subst`, so a guard inside a simulated program refers to the OUTER players;
`.eq` substitutes only its probe side, `.diag` is frozen.

**On codes (DEF, `Subst.lean`).** `gsubst me opp g := if IsSemiformula LAct 6 g then guardCode g
me opp else g`; `psubst me opp p` is the Δ₁ fixpoint on pairs with parameters, `pConst a ↦ pConst
a`, `pSelf ↦ me`, `pOpp ↦ opp`, `pBot p ↦ pBot p`, `pSim`/`pIte` structurally, `pSearch k g p q ↦
pSearch k (gsubst me opp g) (psubst p) (psubst q)`, non-shapes fixed (equations
`psubst_const` … `psubst_search`, THM). An instantiated template is a SENTENCE, so a later
`guardCode`/`guardCodeB` in any frame is the identity on it (`guardCode_gsubst`,
`guardCodeB_gsubst`, THM): outer reference, exactly the engine's.

**The truncation caveat (why `gsubst` is the identity off templates).** Foundation's `subst`
truncates out-of-range variables to `0` and `relabelTemplate` fixes the resulting non-formula, so
on a code with more than six free variables the two do not commute (the docstring's
counterexample `^rel 2 R ?[c_C, #7]`). Restricting instantiation to genuine templates is what
makes τ-equivariance hold on EVERY code: `swapcode_psubst : swapcode (psubst me opp p) = psubst
(swapcode me) (swapcode opp) (swapcode p)` (THM). The same restriction is the source of the
`.sim` debt of §4.

**Agreement with the engine (THM, `Code.lean`).** `pcode_subst : pcode (p.subst me opp) = psubst
(pcode me) (pcode opp) (pcode p)` and `tcode_subst : tcode (ψ.subst me opp) = gsubst (pcode me)
(pcode opp) (tcode ψ)` on the fragment `fragP`/`fragF` with proper players, through the meta
equation `tmpl_subst`. `.box` is excluded there for a reason the docstring states exactly: the
translated box carries its body's CODE as a numeral, `tmpl (.box k (ψ.subst me opp))` and `tmpl
(.box k ψ) ⇜ desc` are PA-provably equivalent but not identical, and length-bounded provability
is not invariant under provable equivalence (results note §4 boundary 1).

## 6. The evaluator `EvalGraph`

**Definition (DEF, `Eval.lean`).** `EvalGraph n me opp p a := EvalFix.construction.Fixpoint ![]
⟪n, me, opp, p, a⟫`, the least fixed point of the operator `EvalFix.Phi` on tuples, with
`evalGraphDef : 𝚺₁.Semisentence 5` its Σ₁ graph. The clauses of `Phi`, to be read against the
engine's `eval` (`Dynamics.lean`):

* `pConst a` plays `a` at fuel `n + 1`;
* `pSelf` runs `me`, `pOpp` runs `opp`, `pBot p` runs `p`, all in the same frame at fuel `n`;
* `pSim p q` runs `psubst me opp p` in the frame `(psubst me opp p, psubst me opp q)` at fuel `n`
  — the engine's `let p' := p.subst me opponent; eval n p' q' p'`;
* `pIte b a' p q` runs `b` to some `r`, then `p` if `r = a'` else `q`;
* `pSearch k g p q` runs `p` if `LenProvableV TAct k (guardCodeB g me opp k)` and `q` if
  `¬LenProvableV TAct k (guardCodeB g me opp k)` — the engine's `if proofSearch k (φ.subst me
  opponent) then … else …`, with `proofSearch` (= `decide (Pf k φ)`) replaced by the
  length-bounded box over `TAct`;
* fuel `0` plays nothing (`EvalGraph.zero_iff`, THM).

The Δ₁ blueprint writes the search clause twice, with `lenProvableV` in its `.sigma` and `.pi`
polarities; sub-calls decrease the fuel but may grow the other components, so the fixpoint is
`Finite`, not `StrongFinite`, and functionality is not part of the construction.

**What is V-generic and what is at ℕ (THM).** The clause inversions `EvalGraph.const_iff` …
`EvalGraph.search_iff` (`EvalN.lean`) and `EvalGraph.case_iff` (`Eval.lean`) hold in every model
of IΣ₁. Determinism and fuel monotonicity are proved at ℕ by ordinary induction on the fuel
(`EvalGraph.unique`, `EvalGraph.unique'`, `EvalGraph.mono`, `EvalGraph.mono_le`, `EvalN.lean`;
`evalN` packages the graph as a partial function), and determinism again INSIDE every model by
Π₁-induction (`EvalGraph.unique_V'`, `Det.lean`). The evaluator's theory is HARDWIRED: `TAct`
sits in `Phi` and in the blueprint's `!(lenProvableV TAct)` literal; making it a parameter would
touch every consumer, which is why the mutation of §9 is a verbatim copy.

**Lockstep with the engine (THM, `Cells/SearchFree.lean`).** On the search-free constructors
`const/self/opp/bot/sim/ite`, `evalGraph_of_eval_searchFree_core : PD.eval n me opp body = some a
→ EvalGraph n (pcode me) (pcode opp) (pcode body) (actCode a)` at the SAME fuel — stronger than
`AgentConverse.evalGraph_of_eval`'s existential fuel, and the basis of the 28 SF cells
transferred from the engine's `OutcomeSpec` theorems (`outcomeSpec_evalGraph_of_searchFree`).
With a search node the two evaluators agree exactly when their boxes agree on the consulted
guards: the named two-sided hypothesis `GuardAgree` (`AgentConverse.lean`) gives
`eval_iff_evalGraph`, and `GuardAgree` is bounded D1 and its converse — never assumed anywhere
in the route-B cells, which are proved directly in `S'`.

## 7. The truth equations

"The sentence says what the program does" is the claim that, under the standard reading of the
constants, a guard sentence is TRUE iff the arithmetized evaluator produces the action it names.
The reader checks the DEFINITION of `gtmpl` (§4) and the description terms once; the equations
are theorems:

* `models_guardSentenceA_iff : ℕ↓[LAct] ⊧ guardSentenceA a me opp ↔ ∃ n, EvalGraph n opp me opp
  a` (`Template.lean`, at ℕ) — the descriptions denote the codes (`val_progTT_V`, the
  `relabel_val_desc` reconstructions) and `Gtmpl`'s body is `evalGraphDef`.
* `eval_qDupoc_iff_V : (stdActV V ⊧ qDupoc [k]) ↔ ∃ n, EvalGraph n (DupocV k) (DupocV k)
  (DupocV k) 0` (`Transparency.lean`): the same in EVERY model of IΣ₁ at a possibly nonstandard
  budget, for the one-variable family formula `qDupoc` (`Instance.lean`: Dupoc's guard is the
  `bnum k`-instance of ONE fixed formula, `exists_dupoc_instance`, `guardCode_DupocV_eq_instB`).
* `models_trAt_plays : ℕ↓[LAct] ⊧ trAt me' opp' (.plays me opp a) ↔ ∃ N, EvalGraph N (pcode me)
  (pcode opp) (pcode me) (actCode a)` (`Agent.lean`, proper players — the frame is irrelevant);
  `models_trAt_neg`/`models_trAt_impl`/`models_trAt_eq` (`Cells/SoundnessCells.lean`) for the
  other guard shapes, and `trAt_subst` (the realization of a fragment guard in a proper frame is
  the realization of its closed instantiation).
* At the pronoun atoms in every model: `eval_tmpl_plays_self_opp_V`,
  `eval_tmpl_plays_opp_self_V` (`Cells/DIMCID.lean`), `eval_tmpl_plays_opp_closed_V`
  (`Cells/PrudentMirror.lean`), and the generic instance/truth pair for an arbitrary
  six-variable template, `guardCode_qT_eq_instB`/`eval_qT_iff` (`Cells/PrudentMirror.lean`) and
  `guardCode_eq_instB_of`/`eval_GtmplA_subst_iff` (`Cells/JustBot.lean`).
* The swap reading: `lMap_swap_guardSentenceA` (`Template.lean`) sends the guard of `(a, me,
  opp)` to that of `(swapAct a, swapcode me, swapcode opp)`, so truth in `swapActS` is the
  transposed cell — which is how one `LoebSound` proof covers a cell and its τ-twin.

The link from provability to truth is soundness of `TAct` in ℕ (`models_trAt_of_lenProvableV`);
the link from truth to provability is `tact_complete'` (§1) plus, for the instance at `bnum k`,
the length accounting of `found_of_all` (`Cells/PositiveCells.lean`: `TAct ⊢ ∀¹ q` makes the
`k`-instance found for all large `k`) or the Löb engine `family_found` (`Assembly/Family.lean`:
given `LoebSound p S₀ S₁` — "a proof of the `k`-instance of `p` within the budget, slack to
spare, makes `p(k)` true in both standard readings" — the family's box is found within its
budget, with `BoundedInnerNec 16` supplied by `boundedInnerNec_sixteen`,
`Necessitation/Package.lean`). `LoebSound` is the last trusted-base item: it is the shape of
the Löb premise a cell must prove, and its meaning is fixed by `Box_g` (`Assembly/Prep.lean`
§4: `Box_g χ (k) ↔ LenDerivable TAct (gBudget k) (instB ⌜χ⌝ k)`, `eval_Box_g_iff`, THM, with
`gBudget k := ‖k‖ * ‖k‖ * ‖k‖`, Critch's polylog `g`).

## 8. What is deliberately outside

* **`.box` inside guards.** `tmpl (.box k ψ)` is defined, but `box_guard_never_fits`
  (`FitBox.lean`, THM): under the present coding a searcher whose guard mentions `□_k` can never
  find its guard within `k`, because the Cantor-pair CODE of a binary numeral has more bits than
  the numeral has value (`size_bnum_ge`), and the box writes its body's code as a numeral.
  Instances `legibleBot_guard_never_fits`. The fix is the node-data one (§4, route (c) applied to
  box budgets), not done; LegibleBot/OptimBot are therefore outside `S'`.
* **The tau constructors** `.tvote/.sys/.selfIdx` map to code `0` (`Code.lean`); `.diag ↦ ⊥`. The
  tau layer stays a property of the engine.
* **Floors.** `ROUTE_B_SCOPE.md` §8 decision 2 (2026-09-23): no `BoundedReflection`, no Phase 3;
  the FLOOR(cen) cells, the floor-paying Löb cells and the staggered companions remain the
  ENGINE's results, with the reflection assumption stated in prose. `S'` is the positive theory;
  a same-`k` floor cell is neither claimed nor refuted in it. WaryBot's `.neg` guards enter only
  where the else branch follows by soundness or the guard is a Π₁ truth by determinism
  (`pos_WaryBot_vs_DefectBot`, the `S'` twin of `Pf.atomNeg`).
* **The one place `S'` disagrees with the engine.** The results note's addendum "THE FINDING"
  (2026-09-23): the engine closes ten cells by censuses that rest on a player being UNREADABLE by
  `S`'s rules; in PA every source is readable (Σ₁-completeness), and six of the ten flip.
  `loeb_DIMCID_vs_CooperateBot` (`Cells/PositiveCells.lean`, THM): DIMCID × CooperateBot is
  `(D, C)` in `S'` against the engine's `(C, C)` — a negative-Löb guard ("I do not cooperate") is
  self-fulfilling under a real proof predicate and bounded Löb finds it. Two cells keep the
  engine's value by soundness instead (`cimcic_selfref_not_found`), two are genuine floors, four
  more flips are verdict-only. Roadmap §4 predicted the direction ("PA reads source for free
  … negatives are weaker"). This is not a defect of either system; it is the paper's example of
  a cell whose value is a property of the proof system, not of the bots.

## 9. Why the definitions are not vacuous — the mutation evidence

The trusted base is small, but a wrong definition can compile. The evidence that these ones
carry their intended meaning is the deliberate-break protocol of `RED_CELL_AUDIT.md` §4 and its
executable companions, all THM:

* **Negative controls and pins** (`RedCellAudit.lean`): `dupoc_not_coop`/`cupod_not_defect` (the
  opposite outcomes are REFUTED at every fuel — an under-determined evaluator could not refute
  them), `red_cell_deterministic`, `red_cell_any_fuel`, `guard_is_about_the_run` (a provable guard
  is a true statement about the run — if `gtmpl` were misread this would not compile),
  `guards_both_fail`, `search_is_real` (= `guard_fits`, so "unprovable at `k`" is not "too long
  to state").
* **The executed mutations.** Swapping Dupoc's continuations breaks `swapcode_Dupoc` and
  `red_cell` (executed 2026-09-16, audit §4); dropping `dlen` from the box trivializes
  `guard_fits` and breaks the M1 gate. **Dropping soundness is a theorem**
  (`RedCellUnsound.lean`): `TBad := insert axEq (insert axEq' TAct)` adds `c_C = c_D` and its
  transpose; `tbad_inconsistent`; every sentence gets a three-node proof
  (`lenProvable_TBad_of_flen`); `EvalGraphBad` is a verbatim copy of `EvalGraph` with the theory
  swapped in the `search` clause and nowhere else; and `red_cell_flips_when_unsound`: for all
  large `k` both searchers find their guards and the cell becomes `(C, D)` (`red_cell_flip`
  shows both values at the same budgets). A vacuous box, a symmetric-only argument or an
  evaluator that ignored its guard could not produce this flip.
* **Stated once, instantiated twice.** `engine/PrisonersDilemma/Base/RedCellFramework.lean`
  proves the red cell axiom-free against an abstract hypothesis package (bounded derivability,
  an involutive τ, the two guards, fire/else clauses, soundness at one instance, determinism);
  `PD.Theorems.red_cell_engine` and `ArithS.red_cell_via_framework` instantiate it with `Pf`
  and with `LenProvableV TAct` — sharing no code, agreeing on the conclusion.
* **The two vacuities that were caught.** Unary numerals made every search fail
  (`search_never_found`, retired with commit 470ee43 — `guard_fits` is the guard against its
  return); a `TAct` without `axAct` made every guard unprovable (§1). Both were found by asking
  for a POSITIVE fact — a guard found, a Löbian cell — and both are now theorems in the
  opposite direction. The reader who wants to repeat the exercise for a new headline result
  follows `RED_CELL_AUDIT.md` §6: the same table, plus the negative control `¬ EvalGraph n (…)`
  for the opposite action.

## 10. A reading order for the code

Read in this order, docstrings first (each file's header says what it defines and why):

1. `LangAct.lean`, `TheoryAct.lean` — the language, `swap`, `TAct`, the two readings (§1).
2. `Length.lean`, `SequentLength.lean`, `DerivationLength.lean`, `MetaLength.lean`,
   `ProofLength.lean` — `dlen` and its meta twins (§2).
3. `Bew.lean`, `BewV.lean`, `Proper.lean`, `CutV.lean` (the `LenDerivable` definition only),
   `ProperV.lean` (the `lenDerivable_iff_lenProvableV` bridge) — the three boxes (§3).
4. `Prog.lean`, `Bnum.lean`, `ProgT.lean`, `RelabelTemplate.lean`, `Guard.lean`, `Template.lean`
   — codes, descriptions, the six-variable template, the budget slot (§4).
5. `Subst.lean` — `gsubst`, `psubst`, the gate lemma `guardCodeB_of_template` (§4–§5).
6. `Eval.lean`, `EvalN.lean` — the evaluator and its ℕ facts (§6); `SimTest.lean` for `Mirror`.
7. `Code.lean`, `Agent.lean` (the definitions `trAt`, `modestP`, `Proper`, `GuardAgree` in
   `AgentConverse.lean`) — the general translation and the engine bridge (§4, §6).
8. `RedCell.lean`, `Fit.lean`, `RedCellAudit.lean`, `RedCellUnsound.lean`, `RedCellInstance.lean`
   — the anchor result and its audit (§9).
9. `Instance.lean`, `InstV.lean`, `Diag.lean`, `Transparency.lean`, `Assembly/Prep.lean` §4–§6,
   `Assembly/Family.lean` — the Löb vocabulary: `instB`, `bewB`, `Box_g`, `gBudget`, `LoebSound`,
   `family_found` (§3, §7). `Necessitation/Package.lean` states the unconditional headline
   theorems; the directory behind it is proof, not definition.
10. `Cells/*.lean` — the route-B cells; `Cells/SearchFree.lean` for the lockstep transfer,
    `Cells/JustSlot.lean` for the budget slot in use, `Cells/SoundnessCells.lean` and
    `Cells/PositiveCells.lean` for the SND/POS mechanisms and the flips (§7–§8).
11. `Audit.lean` — the census; `arith/README.md` — the one-page summary.
