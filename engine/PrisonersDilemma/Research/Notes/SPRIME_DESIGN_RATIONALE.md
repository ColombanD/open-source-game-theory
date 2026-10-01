# SPRIME_DESIGN_RATIONALE — the trusted base of PA-`S'`

*What a reader must accept BY EYE in `arith/ArithS/`; everything else is a Lean theorem on the three
standard axioms. Code reading guide: `arith/ArithS/README.md`. What is proved: `ARITHMETIZED_S_RESULTS.md`.
Notation: `□_k σ` length-bounded provability, `⊨` truth in ℕ, `TAct ⊢ σ` Foundation derivability. The long
form of this note (history, every lemma name) is in git before `c0aa163`.*

## 0. What "trusted" means

The kernel checks that theorems follow from definitions; it says nothing about whether the definitions mean
what the prose claims. The trusted base is the nine definitions every headline statement is phrased in.
Foundation (Gödel numbering, `Proof`, `subst`, IΣ₁, completeness) is trusted as a library. No `axiom`,
`sorry` or `native_decide` in the package; the census (`Audit/`) is every `#print axioms` the build runs.

Two conventions: every quantitative statement is "for all large `k`" with an existential threshold (Cantor
pairing makes constants astronomical — never quote one); and the base is small on purpose (a few hundred
lines of definitions), which is what makes an audit feasible.

## 1. The nine definitions

| # | definition | file | the design choice, and why |
|---|---|---|---|
| 1 | `LAct = ℒₒᵣ + {c_C, c_D}`; `swap` exchanges the constants | `Theory/LangAct` | actions are CONSTANTS, not numerals: a numeral is rigid (a proof may reason about it arithmetically), a constant symbol is renamed node by node, so τ transports derivations and preserves length. Engine's 47-arm `Pf.transpose` becomes one generic theorem. |
| 2 | `TAct = PA + {c_C ≠ c_D, c_D ≠ c_C, actionAxiom, actionAxiom'}`, `actionAxiom : (c_C=0 ∧ c_D=1) ∨ (c_C=1 ∧ c_D=0)` | `Theory/TheoryAct` | each axiom in BOTH orientations so the set is literally swap-closed (an exact iff, not `k` vs `k+c`). `actionAxiom` was the fix for a vacuity: with only `c_C ≠ c_D` a model could read the constants as any pair and no guard was ever provable. Consequence: `TAct` has exactly two standard readings (`stdReading`/`swappedReading`). |
| 3 | `proofLen`: symbol count of a derivation code — every node charges its sequent, ∃-witnesses charged | `Length/DerivationLength`, meta twin `proofLenMeta` | symbol-BLIND (a symbol counts 1 whatever its code) ⇒ invariant under every language hom, hence under τ. Charges forced by properness (weakening, unconstrained witnesses). Residue: variable indices unary (the only cause of U10's degree 16 rather than 3). |
| 4 | `□_k φ := ∃ d < codeBound k, Proof TAct d φ ∧ proofLen d ≤ k` (`LenBox`, Δ₁; `codeBound k = exp³(12k)+1`) | `Box/BewV` | the code bound only makes the box Δ₁; properness (`quote_derivation_le`, `ProperBound`) proves it never excludes a proof of length ≤ k, so it equals the Σ₁ `LenBoxUnbounded` in every model. The reader decides once that `proofLen` is an acceptable "number of characters". |
| 5 | program codes on `ppair x y = (x+y)²+y`: `pConst pSelf pOpp pBot pSim pIte pSearch`; `transposeCode` | `Agents/Prog` | `ppair` is term-expressible (Foundation's `pair` is an `if`), so a searcher's guard is the `binNumeral k`-instance of ONE fixed formula — what the parametric Löb argument needs. |
| 6 | descriptions: a program enters a sentence as `(codeTerm (canonical x), revalueU x, revalueW x)` — a binary-numeral TERM of the canonical τ-orbit member plus the two constants in reconstructing order; INSIDE a stored template (2026-10-01, route (c) made generic) a closed program is described with the node's own budget abstracted: `codeTermMetaAbs k₀` writes every `pSearch k₀` budget as the frame's budget slot `#6` (`canonicalSlot (some k₀)`, `closedDescAt`); a system is described verbatim | `Agents/CodeTerm`, `CodeTermAbs`, `BinNumeral`, `Guard`, `Code` | τ acts on descriptions SYNTACTICALLY; length `O(log x)` (Critch's (b)). With unary numerals no search could ever succeed (the retired `Vacuity.lean`); `guard_fits` is the positive replacement. The abstraction exists because a template describing a budget-carrying closed program (JustBot's `DupocBot k`, a tau hypothesis instance) was otherwise a different code at every `k` — not the `k̂`-instance of any fixed formula, and of length `≥ k` once named by a frame (`Tau/NeverFits.lean`). Filling the slot with the node's budget recovers the verbatim term (`subst_codeTermMetaAbs`), so the consulted sentence is unchanged (`guardCodeB_templateCodeAt`): the reader accepts that a program's description inside a guard may name the guard's own budget by a variable. Systems stay verbatim because the closer fills pronoun slots verbatim (`descriptionsSys`); no paper-zoo guard names a closed system. |
| 7 | `guardTemplate a` ("the program described by the opp-triple plays `a` against the one described by the me-triple"); `template : PD.Formula → sentence`, `progCode`; `guardCode g me opp` fills the six slots; `guardCodeB` adds slot `#6` = the node's own budget; `progCode (.search k φ p q)` stores `templateCodeAt φ k = ⌜templateAt φ (some k)⌝` (closed programs abstracted at `k`), equal to the unabstracted `templateCode φ` on every guard without a budget snapshot (`templateCodeAt_eq_templateCode`) | `Agents/Template`, `Code`, `Guard` | the seventh slot (route (c)) exists because `JustBot k` freezes a budget-carrying snapshot in its guard, so no six-variable template describes it as a `binNumeral k`-instance; since 2026-10-01 the slot is written by the translation itself (generic route (c)) instead of by hand (`Just7`/`CupodTroll7`); the gate lemma `guardCodeB_of_template` keeps every six-variable statement byte-identical, `EvalGraph.search_iff_at` the stored-template search clause. |
| 8 | `substCode`/`substTemplate`: the engine's ONE-SHOT `Prog.subst` on codes (`.bot` frozen, a simulated program's guard reads the OUTER players) | `Agents/Subst` | restricted to genuine templates (6 or 7 variables) because Foundation's `subst` truncates out-of-range variables; that restriction is what makes τ-equivariance hold on every code. `progCode_subst` proves agreement with the engine on the box-free fragment. |
| 9 | `EvalGraph n me opp p a`: a Σ₁ fixpoint mirroring `eval` clause by clause; `pSearch k g p q` runs `p` iff `□_k (guardCodeB g me opp k)` | `Eval/Eval` | determinism and fuel-monotonicity at ℕ (`EvalGraph.unique'`, `mono_le`); on search-free constructors in LOCKSTEP with the engine's `eval` at the same fuel (the 28 SF cells transfer). |

## 2. The two methods

* **Positive (found guards).** Never by exhibiting a derivation: `TAct_complete_of_readings` — a sentence true in BOTH
  readings of every model of PA is a `TAct`-theorem. The swap reading is, by the truth equations, the cell of
  the transposed programs, so one `LoebSound` proof covers a cell and its τ-twin. Then `found_of_all` (the
  `k`-instance of a `TAct`-theorem fits the budget for large `k`) or the Löb engine `family_found` with
  `BoundedInnerNec 16` (`Necessitation/Package.lean`).
* **Negative (else branches).** Soundness of `TAct` in ℕ: a found guard is a true play
  (`models_sentenceAt_of_lenBox` + the truth equations `models_guardSentence_iff`, `models_sentenceAt_plays`).
  This closes the red cell and the 36 SND cells; no negative is ever proved inside `TAct`.

## 3. Outside, by decision

* **Boxes inside guards** (LegibleBot, OptimBot): a box names its body's code as a numeral, exponential in
  the body's length (`box_guard_never_fits`); the length is fixable inside route (c) with a polylog inner
  budget, but the cells need necessitation for a body computed from the frame — a third U10-kit instance.
* **Floors**: no `BoundedReflection`, no conditional values. Each of the 26 genuine floors is a
  hypothesis-free dichotomy on the hinge `□_k (the outer guard)`; the hinge is bounded consistency of
  `TAct` at `k` up to a constant (Pudlák's linear regime, open both ways; the engine's `+k` stipulates the
  negative side). NEVER admit the hinge as an axiom.
* **The tau constructors** have real codes since 2026-09-30 (Phase 2 of `SPRIME_SOURCE_OF_TRUTH.md`): `.tvote`,
  `.sys`, `.selfIdx` are the shapes `pTvote`/`pSys`/`pSelfIdx` (tags 7–9, plus the tagged list cons `pCons`,
  tag 10), with τ, description terms, substitution, the system closer `sysCloseCode` (member lookup `listGet`)
  and the evaluator's three clauses in lockstep with the engine's `eval` on the tau-search-free fragment
  (`Eval/TauCheck.lean`). What is still missing is the PRONOUN reading of `.selfIdx j` inside a member's
  guard: `template` has six variables, so the pronoun is described literally (the dangling code
  `pSelfIdx j`) and the member slots `#7..#12` that `sysCloseTemplate` fills are read by no compiled
  template — a system's searcher takes its else branch in `S'` until `template` is widened. `.diag ↦ ⊥`.
* **Where `S'` disagrees with the engine** (13 cells): the engine's censuses rest on a player being
  UNREADABLE by `S`'s rules; PA reads every source. DIMCID's guard "my cooperating implies X" is
  self-fulfilling for any `X`, so DIMCID defects against every closed program (`dimcid_vs_closed`). Not a
  defect of either system: a cell value that is a property of the proof system, not of the bots.

## 4. Why the definitions are not vacuous

* Negative controls: the opposite outcomes of the red cell are REFUTED at every fuel; `search_is_real`
  (= `guard_fits`): "unprovable at `k`" is not "too long to state" (`Audit/RedCellAudit.lean`).
* Executed mutations: swapping Dupoc's branches breaks the red cell; dropping `proofLen` trivializes
  `guard_fits`; dropping soundness (`TBad = TAct + c_C = c_D`) makes both searchers find their guards and
  the cell FLIPS to `(C, D)` (`Audit/RedCellUnsound.lean`) — a vacuous box could not produce this.
* Stated once, instantiated twice: the engine's abstract `RedCellFramework` is instantiated with `Pf` and
  with `LenBox TAct`, sharing no code, agreeing on the conclusion.
* Two vacuities were caught by asking for a POSITIVE fact (unary numerals; `TAct` without `actionAxiom`); both
  are now theorems in the opposite direction.
