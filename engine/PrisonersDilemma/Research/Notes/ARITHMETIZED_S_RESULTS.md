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

**The sentence for the paper.** "`S` is sound relative to PA wherever a character count
exists: its modal core for PA's provability predicate (T2-CORE) and its evaluation
certificates for the arithmetized evaluator at the same budgets (T2-AGENT). Where the engine
charges evaluation steps or cheap citations instead of characters, no PA proof length can
match at any inflation, and we prove it (T2-NEG). Budget-keeping soundness of `S` is
therefore exactly Critch's assumption (d), stated as the one open hypothesis." The
budget-erased world of T2-CORE is that of Barász et al.'s unbounded modal agents (cf. Berns'
mechanization); the contribution stays the BOUNDED `S` of T1/T2-AGENT.

## 4. Boundaries (recorded, not gaps in proofs)

1. `.box` cannot be translated compositionally under LENGTH-bounded provability: a box carries
   its body's CODE as a numeral, `tmpl (.box k (ψ.subst me opp))` and `tmpl (.box k ψ) ⇜ desc`
   are PA-provably equivalent but not identical, and `□_k` is not invariant under provable
   equivalence. The code equations and τ are therefore proved on the box-free search-bot
   fragment; boxes are what T2-AGENT's hypotheses are about.
2. Truth → `TAct ⊢` for the atom sentences (Σ₁-completeness over `LAct`): Foundation's
   completeness is over ℒₒᵣ, and the sentences name `c_C, c_D`, which `TAct` leaves
   uninterpreted; a proof would reason uniformly in two distinct constants. Open.
3. The tau constructors `tvote/sys/selfIdx` are outside the translation (code 0).
4. `GuardAgreeF` from engine soundness would need the converse of T2-AGENT.
5. Encoding sensitivity: Cantor pairing makes `‖⌜φ⌝‖` exponential in syntax depth; every
   quantitative statement is "for all large k".

## 5. Engine-side finding for the maintainers

Charging `AtomProvable.mk` by `n + |φ| ≤ k` and `search_t` by `n + k + c_node` would remove
both departures from a character count and make a budget-keeping transfer plausible on the
size-gated fragment — at the price of every cheap-citation cell (the `(2k+64)` staggers,
`outcome_DupocBot_vs_CooperateBot` at pad `atom_cost 1`, which survives only as `eventual`).
A design decision, not part of M3.

## 6. Where things are

* Branch `colomban-arith-m3` (worktree `~/wt/osgt-arith-m3`): engine on Lean v4.33.1
  (proof-only repairs), `arith` requires the engine as a path dependency, `lake build ArithS`
  builds both (~3200 jobs; ~15 s incremental). The OneDrive checkout stays on
  `colomban-arith-s` (arith-only, engine v4.28) so the app and IDE keep working.
* Files: `Length, SequentLength, DerivationLength, Bew, MetaLength, Proper` (M1);
  `LangAct, TheoryAct, Transpose, Sound, Symmetry, ProofLength` (τ, lengths of proofs);
  `Prog, RelabelTemplate, Bnum, BewV, Guard, Subst, Eval, EvalN, SimTest, Template, RedCell,
  Fit` (agents, T1); `Core/Tr, Core/Sound` (T2-CORE); `Code, Neg, Agent` (T2-NEG, T2-AGENT);
  `EngineBridge, Audit`.
