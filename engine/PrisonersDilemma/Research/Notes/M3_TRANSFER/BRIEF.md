# M3 design brief — the transfer theorem "S is sound relative to PA" (T2)

Author: the orchestrating model, 2026-09-10, after finishing T1 (`ArithS.red_cell`).
Audience: the design panel. Everything below is either a verified fact (marked FACT, with
file references) or the orchestrator's analysis (marked ANALYSIS). Challenge the analysis.

## 1. What exists

FACT. Standalone package `arith/` (`ArithS`, Lean v4.33.1, Foundation commit 58c76ac8),
branch `colomban-arith-s`. Files in import order: Length, SequentLength, DerivationLength,
Bew, MetaLength, Proper, LangAct, TheoryAct, Transpose, Sound, Symmetry, Prog, BewV,
Guard, Eval, EvalN, Template, RedCell. Key objects:
- `termLen/formulaLen/setLen/dlen`: STRUCTURAL symbol counts on Foundation's codes
  (function/relation symbols cost 1, variable index i costs i+1, a numeral n is the term
  `1+1+…+1` and costs ~2n). `mlen : T ⟹₂ Γ → ℕ` is the meta twin; every node adds
  `sqlen Γ` (the whole sequent), so `mlen d ≥ flen σ` for any proof d of σ.
- `LenProvable f k T φ := ∃ d < f (numeral k), Proof T d φ ∧ dlen T d ≤ numeral k`;
  `fbound k = exp³(12k)+1` is PROPER: every derivation of length ≤ k has code < fbound k
  (`quote_derivation_le`). `LenProvableV T k φ` is the same with k an object variable (Δ₁).
- `LAct = ℒₒᵣ + {c_C, c_D}`, `TAct = PA ∪ {c_C ≠ c_D, c_D ≠ c_C}` (Δ₁, swap-closed);
  `swap` the constant transposition; `lenProvable_fbound_swap_iff : TAct ⊢_k ⌜φ⌝ ↔ TAct ⊢_k ⌜swap φ⌝`.
- Program codes: `pConst a | pSelf | pOpp | pBot p | pSim p q | pIte b a p q | pSearch k g a p q`
  (actions 0 = C, 1 = D; `g` = a template code with seven description variables; `a` the
  action the template is tested against). `relabel u w x` re-values actions, `swapcode = relabel 1 0`.
- `EvalGraph n me opp p a` (Σ₁ Finite fixpoint on ⟪n,me,opp,p,a⟫): clauses for const, self,
  opp, bot, ite, search; the search clause tests `LenProvableV TAct k (guardCode g me opp a')`;
  NO clause for `pSim` (and none for the engine's tau constructors tvote/sys/selfIdx).
  Determinism and fuel monotonicity at ℕ (`EvalN`).
- Restricted template `Gtmpl` ("opp plays a against me") with code/swap/truth equations
  (`Template.lean`), and `red_cell : EvalGraph 2 (Dupoc k) (Cupod k) (Dupoc k) 1 ∧ …` for
  every k, three standard axioms.

FACT (engine). `engine/` is on Lean/mathlib v4.28.0; a separate agent is bumping it to
v4.33.1 in `~/wt/osgt-arith-m3` (branch `colomban-arith-m3`). The engine's `Pf k φ` is the
unified proof system (33 constructors; mutual with `PlaysProof`/`AtomProvable`), costs are
transcript-cumulative, `sound_upto : Pf k φ → φ.interp` with `(.box k ψ).interp = Pf k ψ`,
`.plays p q a` interpreted by the fuelled `eval` whose `.search` clause calls
`proofSearch k φ := decide (Pf k φ)`. Negative rules: `search_f` (else-play from a Σ₁
REFUTATION of the guard, i.e. a derivation of `.neg guard`), `atomNeg`, `eqNeg`.
Löb is DERIVED (`bloeb_engine` via the internalized fixpoint `Formula.diag` and the rules
`diagF/diagB/axKf/impS2`). The reader reports (attached) have the verbatim constructors.

## 2. A finding that changes what T1 means (verify it, then fix it)

ANALYSIS (to be turned into a Lean lemma). Under the current `len`, numerals are unary.
The guard sentence of `Dupoc k` against anybody contains `numeral (dnum (Dupoc k))` and
`dnum (Dupoc k) ≥ k` (the code of `pSearch k …` is a nested Cantor pair containing k). So
`flen (guardSentence (Dupoc k) opp a) ≥ 2k`, hence `mlen d ≥ 2k > k` for every proof d,
hence `LenProvableV TAct k (guardCode ⌜Gtmpl⌝ (Dupoc k) opp a)` is FALSE for every k, opp,
a. Dupoc never finds anything: under this coding it is DefectBot in disguise, Cupod is
CooperateBot in disguise, and `red_cell` is true for a reason that has nothing to do with
symmetry. The symmetry proof is still valid and coding-independent, but the MODEL is
degenerate: no Löbian cooperation is possible at any budget, which contradicts the point
of OSGT. This is exactly Critch's assumption (b) ("k is written in O(lg k) characters"):
an agent's own source, which contains k, must fit inside budget k.

Required fix (part of M3, before any bounded transfer is meaningful): charge a numeral
term of value n as `‖n‖ + 1` (Foundation's binary length `‖·‖`, `Exponential/Log.lean`,
Δ₀-definable via `length_graph`; `numeralGraph` is Σ₁ and `numeral n ≥ n`, so
"t is a numeral" is a bounded search `∃ n ≤ t, t = numeral n`). Consequences: `termLen`'s
func clause gets a numeral case; `tlen` (meta) gets the matching case; `termLen_quote`,
`quote_term_le`/`quote_formula_le`/`quote_derivation_le` and `fbound` need a taller tower
(a numeral of length L has value ≤ 2^L and code ≤ a tower over that); `tlen_lMap`
invariance survives (homs map numerals to numerals). Then `flen (guardSentence (Dupoc k) opp a)
= O(‖k‖) + C` for a constant C (the template code and the pairing overhead), so guards fit
in the budget for all large k. State this as a theorem (`guard_len_le`). Note Cantor
pairing makes `‖code⌝‖` exponential in the nesting DEPTH of the syntax; that is a
cost-faithfulness issue for T3 (danger 4), not for T1/T2 non-vacuity.

## 3. The two obstructions to a same-budget transfer (ANALYSIS — the panel must confirm)

Let `φ*` be an arithmetical realization of engine formulas. Two natural choices:

(U) budget-ERASING: `(.box k ψ)* = □(ψ*)` with □ = PA's standard provability predicate
    (Foundation `provabilityPred`, D1/D2/D3/Löb available). Programs' search nodes would
    then have to be tested by □ too (the evaluator is no longer Δ₁). The `search_f` arm
    fails: from the IH `PA ⊢ ¬g*` one needs `PA ⊢ ¬□g*`, which is PA proving a
    consistency-like statement (Gödel II). Dead for the refutation rules.

(B) budget-KEEPING: `(.box k ψ)* = Bew_k(⌜ψ*⌝)` (the Δ₁ `LenProvableV`), programs keep
    their k. `search_f` works: IH gives `PA ⊢ ¬g*`, PA is sound (ℕ ⊧ PA), so PA ⊬ g* at
    all, so `¬Bew_k(⌜g*⌝)` is a TRUE Δ₁ sentence, hence PA-provable (Σ₁-completeness on
    the Σ₁ form of the Δ₁ predicate). `boxIntro`/necessitation fails: from `PA ⊢ ψ*` one
    needs a PA proof of ψ* of length ≤ k — the transferred proof has length F(k) > k
    (roadmap danger 2). Dead at the same budget.

(B_e) budget-INFLATING: fix `e : ℕ → ℕ`; `(.box k ψ)* = Bew_{e k}(⌜ψ*⌝)`, program search
    budgets `k ↦ e k`. Then the theorem is quantitative: `Pf k φ → PA ⊢_{e k} φ*`, and every
    arm must produce a proof of bounded length. `boxIntro`: from a proof of ψ* of length
    ≤ e kIn, `Bew_{e kIn}(⌜ψ*⌝)` is true Δ₁, provable with SOME length L(kIn, |ψ*|) — bounded
    D1, Critch's (d). `search_f`: as in (B), plus a length bound on the Δ₁-completeness
    proof. Existence of e by strong recursion on k needs (i) `Pf k φ ⇒ |φ| ≤ B(k)` (T48
    literal bounds — the reader must confirm the exact statement and whether box budgets
    inside φ can exceed k, e.g. `implRefl` at tiny cost on a formula with `.box 10^9 ψ`),
    (ii) premise budgets strictly below the conclusion's in every rule, (iii) every arm's
    output length a function of premise lengths, budgets and formula sizes only. Numerals
    inside `Bew_{e m}` for m > k are a trap: with unary numerals the sentence `φ*` itself
    is longer than e k. With log-cost numerals it is O(‖e m‖) — still needs e m ≤ 2^{e k}
    for m ≤ B(k). If e must be Σ₁-definable to be written as a term, its definition must be
    given, not merely proved to exist.

(R) representation of the ENGINE's own S (Church route): `(.box k ψ)* = "Pf k ψ"` as the
    Σ₁ sentence obtained from `Pf_iff_decFull` and Foundation's
    `computable_iff_sigma1_simulate` (computable functions are Σ₁-simulable);
    `(.plays p q a)*` = the engine's evaluation, Σ₁-represented. Then every derivable atom
    or box fact is a TRUE Σ₁ sentence and PA proves it by Σ₁-completeness with NO induction
    on Pf at all; but the general `tr φ` (implications, negations of boxes) is not Σ₁, and
    proving the propositional/modal rules SOUND INSIDE PA for the represented `Pf` means PA
    proving S closed under its own rules — formalizing decFull's correctness in PA. Only the
    Σ₁ fragment is cheap here. Note also `Dynamics.eval` is noncomputable (decide on Pf), so
    `evalG` (computable, commits when a certificate exists) would be the represented object.

(G) GL reuse: Foundation may contain the arithmetical realization of modal formulas and the
    arithmetical soundness of GL (Solovay's theorem, `Foundation/ProvabilityLogic`). If so,
    the engine's propositional+modal core (boxIntro, axK, box4, boxMono, diagF, diagB, axKf,
    impS2, impl*, contrapose, negElim, mp, implTrans, weakenImpl) could be mapped to GL
    derivations and inherit soundness for free — but only for the budget-erased reading (U),
    with atoms as free propositional letters, so the evaluation/search/refutation rules are
    outside it. Still valuable as "S's modal core is a fragment of GL".

## 4. What the panel must deliver

A concrete, honest T2 that is (a) TRUE, (b) provable at M3 scale (weeks, one person plus
agents, on top of the existing arith package and the bumped engine), (c) a claim the paper
can state without asterisks, and (d) explicit about what it does NOT say. Each proposal:
1. the exact Lean statement(s) (types, hypotheses, which theory: PA, TAct, or an extension);
2. the definition of the realization `tr`/`TR` (formulas AND programs, including how
   `.self/.opp` and `Formula.subst` are handled, how budgets are handled, whether the tau
   constructors tvote/sys/selfIdx are covered or excluded with a syntactic side condition
   that is CLOSED under the Pf rules used);
3. a per-rule-group proof plan for ALL Pf constructors (name every arm; say which Foundation
   lemma or which arith lemma discharges it; flag any arm that needs a new metatheorem);
4. the list of new arith files/lemmas with estimated size, and the changes to M1/M2 objects
   (e.g. log-cost numerals, `pSim` clause, general templates, full-Prog evaluator or the
   Church route);
5. risks, with the failure mode that would make the statement FALSE, and the fallback.
Prefer a theorem with fewer moving parts and a crisp English meaning over a "full" theorem
that is false at the edges. If you conclude that no unconditional T2 exists below M4 (bounded
HBL), say so and propose the strongest TRUE statement plus the exact conditional form of the
full one (stated with named hypotheses, never with `sorry`/`axiom`).

## 5. Addendum after the reader reports (FACTS unless marked)

FACT (engine). `(.box n φ).interp = Pf n φ` DEFINITIONALLY, and `WV S (.box n φ) = Pf n φ`.
So the engine's `boxIntro` (`Pf kIn φ → kIn + |box kIn φ| ≤ K → Pf K (.box kIn φ)`) is sound
by FIAT: its soundness arm is `Pf kIn φ → Pf kIn φ`. No length bookkeeping exists anywhere
in the engine for "the proof of φ fits in kIn"; the transcript cost model PRESUPPOSES
Critch's (d). `search_t`/`search_f` are `PlaysProof` constructors with `Pf` premises;
`search_f` refutes `ψ.subst me opp` at a FREE budget m and pays `n + m + k + c_node`.
`Pf k φ` bounds `φ.size ≤ k` except for `.plays` atoms (`pf_size_or_atom`), and every
box/search literal inside φ is `< 2^k` (`maxLitF_lt_two_pow_size`, `box_lit_bound`).
`Pf` is r.e. (`Pf_iff_decFull`); full decidability is OPEN (CutRelevance false at the
modest gate; universal closure unproven). `eval` is noncomputable (classical `decide (Pf k φ)`);
`evalG` is the computable approximation that commits only with a certificate.
The tau constructors (`tvote`, `sys`, `selfIdx`) are part of `Prog`; `Pf` has three `botSys*`
reading rules; `PlaysProof` has vote/sys certificates; `.selfIdx` has no rule.
`.diag g tgt` is a Formula CONSTRUCTOR with `interp = Pf g (.diag g tgt) → tgt.interp`.

FACT (Foundation, pinned commit). NO modal-logic/realization package (removed in #829/#852);
what survives is `ProvabilityAbstraction/` (`Provability`, `HBL` with D1/D2/D3,
`formalized_löb_theorem`, `Diagonalization`, `Height`) — the old 15-line
`GL.arithmetical_soundness` consumed exactly these, so a budget-erased soundness of the
engine's modal core can be written directly against them. Representability is rich:
`rePred_weak_representation : REPred p → (p x ↔ T ⊢ (codeOfREPred p)/[x])` for Σ₁-sound T;
`codeOfComputablePred_provable` and `_neg` (both polarities for computable predicates);
`computablePred_iff_delta1`, `rePred_iff_sigma1`, `computable_iff_sigma1`;
`sigma_one_completeness_iff_param` for `𝚺₁.Semisentence` with numeral parameters;
`models_iff_provable_of_Delta1_param` for proper Δ₁ semisentences (both polarities).
`Provability.prov` is UNindexed by budget; a bounded family is `k ↦ Provability`, and its
D1 is exactly the missing bounded D1.

ANALYSIS (orchestrator; refute if wrong). A HYBRID realization — budgets erased in boxes
(`□`), kept in programs (`Bew_g` inside the evaluator) — fails at the reading rules:
`searchBranch` gives `.box g ψ' → plays me opp a`, whose realization needs
`PA ⊢ □(ψ'*) → Bew_g(⌜ψ'*⌝)`, the false direction. Since the SAME `.box g ψ'` formula can
be produced by `boxIntro` (needs the erased reading) and consumed by `searchBranch` (needs
the bounded reading), no single realization of `.box` makes both arms PA-derivable without
bounded D1. Conclusion to test: a same-budget, unconditional "Pf k φ → PA ⊢ tr φ" over ALL
33 rules is EQUIVALENT to bounded HBL (M4). The candidates that remain honest at M3:
 (i) the budget-erased soundness of the modal-propositional core with atoms as hypotheses
     ("S's Löbian core is a fragment of GL over PA"), via ProvabilityAbstraction;
 (ii) same-budget PA-soundness of the AGENT layer (evaluation certificates, search
     polarity, reading rules, refutations) for the arith evaluator, relative to the truth
     of the consulted bounded box facts — every arm a Δ₁/Σ₁-completeness instance;
 (iii) the engine's `BoundedGL` interface instantiated for PA-S with the bounded-HBL fields
     left as NAMED HYPOTHESES (a structure parameter, never an axiom), everything else
     proved — the "stated, unfilled obligation" of Base/BoundedGL.lean made precise;
 (iv) a representation-based statement using `rePred_weak_representation`: for the r.e.
     predicate `Pf`, `Pf k φ ↔ PA ⊢ ρ(k, ⌜φ⌝)` — exact, cheap, but it says "PA can verify S's
     derivations", not "S's conclusions are PA theorems"; judge whether it is worth stating.
The panel decides which combination is THE M3 deliverable and how the paper phrases T2.
