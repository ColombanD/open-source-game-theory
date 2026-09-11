# ARITHMETIZED_S_ROADMAP — from the rule set `Pf` to length-bounded provability over PA (2026-09-09)

*Companion to `DESIGN_CHOICES.md` ("Why `S` is a RULE SET", 2026-08-20; the `BoundedGL`
interface entry, 2026-08-27). This note is the executable plan for the obligation those
entries leave open: an ARITHMETIZED instance of `S`, built on Foundation
(FormalizedFormalLogic), so that the outcome theorems are connected to an independently
maintained formalization of PA rather than to a stipulated rule set.*

**Decisions fixed 2026-09-09.** (1) The measure is proof LENGTH (characters / structural
size), not Gödel-number magnitude. (2) The work lives in a STANDALONE lake package
(working name `ArithS`) that requires Foundation, and later the engine for the transfer
theorem; the engine never imports it.

---

## 0. The end goal, stated precisely

The sentence we want to be able to write in the paper:

> OSGT is formalized in Lean. The agents' proof system `S` is Peano Arithmetic with a
> length-bounded provability predicate `□_k`, built on Foundation's arithmetization of
> IΣ₁/PA. `outcome(CupodBot k, DupocBot k) = (D, C)` for all large `k` is a theorem about
> THAT `S`, and its proof uses only soundness of PA and the C/D symmetry of the encoding,
> so it does not depend on which proof calculus or constants one picks.

What this does NOT say, and the map is honest about: Critch's own `S` is not a single
theory. Appendix B of `critch22` fixes `S` only by four assumptions — (a) represents all
computable functions, (b) writes `k` in `O(lg k)` characters, (c) allows abbreviations
mid-proof, (d) has a LINEAR proof-expansion constant `e*` (a `k`-character proof can be
verified by an `e*·k`-character proof). "Literally like Critch" therefore means: a concrete
theory over PA, with a concrete length measure, for which (a)–(d) are THEOREMS. (d) is the
one nobody has proved in any prover, and for a plain Hilbert calculus without abbreviations
the honest bound is polynomial, not linear (§5, danger 1).

Three tiers of claim, each a milestone gate:

| Tier | Claim | Needs |
|---|---|---|
| T1 | The red cell `(Cupod, Dupoc) = (D, C)` holds for PA with `□_k` | M1 + M2 (Foundation only, no Löb, no costs) |
| T2 | `S` relative to PA, as PROVED (2026-09-10): T2-CORE (modal core sound over PA, budget erased), T2-AGENT (evaluation certificates = arith evaluator runs, same budgets, relative to the consulted `□_k` facts), T2-NEG (no budget-keeping transfer at any inflation) — see `ARITHMETIZED_S_RESULTS.md` | M3 DONE |
| T3 | The Löbian cells (`Dupoc` self-cooperation, mutual Löb) hold in PA at large `k` | M4 + M5 (bounded HBL, parametric PBLT) |

T1 and T2 together are the thesis-scoped finish line (BOTH DONE 2026-09-10; results record: `ARITHMETIZED_S_RESULTS.md`). T3 is a second program.

---

## 1. What Foundation provides (declarations, as of master 2026-09, Lean v4.33.1)

`Foundation/FirstOrder/Incompleteness/`:

* `RestrictedProvability.lean` — `Theory.RestrictedProvable f e T φ :=
  ∃ d < f (numeral e), Bootstrapping.Proof T d φ` (a 𝚷₁ predicate via `restrictedProvable`),
  the restricted Gödel sentence `restrictedGödel`, `true_restrictedGödel`,
  `provable_restrictedGödel`, and `lower_bound_gödelNumber_proof_restrictedGödel`
  (every proof of it has code `≥ f e`). Bounds the CODE `d`, not a length. The template
  for M1, not the object.
* `StandardProvability.lean` — `provable_D1` (meta), `provable_D2`, `provable_D3`
  (via `provable_sigma_one_complete`), `Diagonalization 𝗜𝚺₁`, `HBL2`/`HBL3`/`HBL`
  instances, `SoundOn ℕ`, `provable_sound`/`provable_complete`. All UNBOUNDED.
* `ProvabilityAbstraction/Basic.lean` — `structure Provability T₀ T` (`prov`, `bew_def` =
  D1), classes `HBL2` (D2), `HBL3` (D3), `Mono`, `Ext`, `Rosser`, `FormalizedCompleteOn`,
  `SoundOn`, `Kreisel`. Two-theory pattern: schemes about provability in `T` are proved in
  the metatheory `T₀` (IΣ₁). Our `Bew_k` follows the same pattern.
* `Löb.lean`, `Second.lean`, `Consistency.lean` — qualitative Löb/G2 from HBL.
* `Speedup.lean` — `Theory.minProof`, `computablePred_proof` (the proof relation is
  computable): the ingredients for "the set of proofs below a bound is finite/decidable".
* `Arithmetic/HFS/Superexp.lean` — `Superexp.superexp`, `two_pow_le_superexp`: the
  Σ₁-definable bound that makes a length-bounded search finite inside IΣ₁.

Not in Foundation: any length measure on proofs, any costed derivability condition, any
bounded diagonal lemma, any bounded Löb. Maintainers' view (Zulip, 2026-08-27): bounded
provability is "too niche" for Foundation proper; an abstract bounded-GL is "legitimate";
arithmetized instances "would probably be technically difficult". Plan for a standalone
package pinned to a Foundation commit, not for upstreaming.

Toolchain: Foundation pins Lean/mathlib v4.33.1; the engine is on mathlib v4.28.0. M1–M2
need only Foundation; M3 needs both, so the engine must be bumped before M3.

---

## 2. The objects

**2.1 Length.** `len : ℕ → ℕ`, Δ₁-definable in IΣ₁ on proof codes, STRUCTURAL: the size
of the decoded derivation tree, formulas counted by symbol, binary numerals by bit-length,
and a quotation `⌜φ⌝` occurring as a numeral counted as `size φ` (so quotation is
structural, exactly as in the engine's `Formula.size`). Two properties are load-bearing:

* PROPER: `{d | len d ≤ k}` is finite, with an IΣ₁-provable bound `d < superexp k` (or a
  weaker Σ₁ function). Without this `Bew_k` is not Δ₁, the evaluator is not total, and the
  agents do not terminate.
* τ-INVARIANT: the C/D relabeling of a coded derivation preserves `len` EXACTLY. This is why
  the measure is structural and not the bit-length of the code — pairing-based codes of `C`
  and `D` differ in magnitude and would break exact preservation (cf. the "nonstandard token
  encoding" caveat, `DESIGN_CHOICES.md` 2026-08-20 item 3).

**2.2 The predicate.** `Bew_k(x) := ∃ d, len d ≤ k ∧ Proof PA d x`. Δ₁ in IΣ₁ by
properness. Meta-level: `PA ⊢_k σ :⇔ ∃ d, len d ≤ k ∧ Proof PA d ⌜σ⌝`. The sentence
`□_k σ := Bew_k(⌜σ⌝)` is Critch's Notation 3.5 verbatim, with `len` as "characters".

**2.3 Agents.** `Prog`/`Formula` re-declared in the package as coded data (HFS or ℕ), with
`tr : Formula → ArithmeticSentence` (`impl`/`neg` → connectives, `box k φ` → `Bew_k(⌜tr φ⌝)`,
`diag g φ` → Foundation's `fixedpoint`, `plays me opp p a` → `Eval(⌜me⌝,⌜opp⌝,⌜p⌝) = ⌜a⌝`).
`Eval` is the fuelled evaluator of `Dynamics.lean`, Δ₁-definable, whose `.search` clause
evaluates `Bew_k(TR(guard))` with `TR` the PA-internal twin of `tr`. Bookkeeping lemma:
`tr` agrees with `TR` on codes. No circularity: `Bew_k` quantifies over PA proofs of
arbitrary sentences; `Eval` is just a Δ₁ function mentioning it.

**2.4 Transposition — abstract action constants, not code swapping.** A naive "swap the
codes of `C` and `D` throughout" is NOT a symbol substitution: actions, programs and quoted
formulas are numerals, numerals are rigid, and a derivation may reason about them
arithmetically. So the theory is `T' := PA` plus two FRESH constant symbols `c_C`, `c_D`
with only the axioms `c_C ≠ c_D`, `c_D ≠ c_C` (both orientations, literally — closure up to a
one-line derivation would give `k` vs `k + c`, and the red cell needs an exact iff) and
`Act(x) ↔ x = c_C ∨ x = c_D`. Everything agent-facing is PARAMETRIC in them: programs are
values built by pairing functions (`const(a)`, `search(k, g, p, q)`) with the action passed
as the constant, so `cupod(k)` and `dupoc(k)` differ only by which constant sits where;
quoted actions go through Foundation's value substitution `⌜σ(ẏ)⌝[y := c_C]`, never a
symbol code; `Eval`, formula decoding and `len` mention no action numeral. Foundation's
Gödel numbering is untouched: `Proof T' d y` mentions symbol codes as numerals, τ swaps
symbols, so it is literally τ-invariant. Standard model: `c_C ↦ 0`, `c_D ↦ 1`; `T'` is
conservative over PA (Critch: "PA or an extension thereof").

τ is then the language automorphism swapping the constants, and the per-rule check of the
engine's `Pf.transpose` (47 arms) becomes three finite lemmas:
1. renaming: each rule of Foundation's derivation calculus commutes with a constant swap
   (check whether derivations already transport along Foundation's language maps);
2. axiom closure: PA's schemata never mention the constants, the action axioms are closed by
   construction;
3. `len ∘ τ = len`, by induction on derivations (a constant symbol counts 1 either way).
Plus `τ(cupod k) = dupoc k` as values and τ-invariance of `Eval`'s definition (`tvote`
stays frozen). Then `T' ⊢_k σ ↔ T' ⊢_k τσ` is a META theorem over Lean-level derivations,
which is all the red cell needs because outcomes are evaluated in ℕ. Audit item: NO action
numeral anywhere in the axiom set or the definitions — one baked-in numeral breaks lemma 2
silently while everything still type-checks.

**2.5 The interface instance (T3 only).** `BoundedGL ArithmeticSentence` with
`Proves k σ := PA ⊢_k σ`, `box k σ := □_k σ`, `diag := fixedpoint`, and `size` := the
CERTIFIED cost (a polynomial of syntactic size and the budget numerals), NOT the symbol
count — so that all ten fields hold literally. `SizeExact` fails; `bloeb`/`mutual_loeb`
transfer as they use no size law; `pblt` gets a new asymptotic wrapper.

---

## 3. Milestones

**M0 — package and toolchain.** `ArithS` lakefile requiring Foundation at a pinned commit;
CI builds it. **Build recipe (learned the hard way, 2026-09-09):** `arith/.lake` is a
SYMLINK to `~/wt/arith-lake` (a Foundation build under OneDrive stalls in disk wait), and
Foundation is NEVER compiled locally — `lake build --try-cache ArithS` downloads its
prebuilt artifacts (Reservoir cache) in ~90 s; a local compile of `Term/Basic.lean` alone
took 22 min and 11 GB. A Lean check of one `ArithS` file needs ~5 GB of resident imports;
on the 16 GB laptop with swap full it thrashes (10 min per file) — reboot first. Decide HFS vs ℕ coding for `Prog` (follow Foundation's `Bootstrapping`
conventions so `Proof` and `Eval` live in the same coding). Engine bump to Foundation's
toolchain is scheduled before M3, not before.

**M1 status (2026-09-09 evening, branch `colomban-arith-s`, all compiling):**
`ArithS/Length.lean` (listSum, termLen, formulaLen — Σ₁ functions by Foundation's
`VecRec`/`TermRec`/`UformulaRec1` schemes), `SequentLength.lean` (`setLen` by PR over the
bit-set), `DerivationLength.lean` (`DlenGraph` as a Δ₁ fixpoint on pairs `⟪d, n⟫`, the ten
inversion lemmas, existence/uniqueness by `Derivation.induction1`, `dlen T` a Σ₁ function),
`Bew.lean` (`LenProvable f k T φ := ∃ d < f k, Proof T d φ ∧ dlen T d ≤ k`, Π₁-defined;
`lenGödel`, `true_lenGödel`, `provable_lenGödel`, `lower_bound_dlen_proof_lenGödel` under
the `Proper` hypothesis). DONE 2026-09-10: the meta bridge (`MetaLength.lean`: `termLen/formulaLen/setLen/dlen` =
`tlen/flen/sqlen/mlen` under quotation) and PROPERNESS (`Proper.lean`: towers
`E s = 2^2^s`, `F s = 2^2^2^s`; `⌜t⌝ ≤ E (8 tlen t)`, `⌜φ⌝ ≤ E (8 flen φ)`,
`⌜Γ⌝ ≤ F (8 sqlen Γ + 1)`, `⌜d⌝ ≤ F (12 mlen d)`; `fbound k = exp³(12k) + 1`, Σ₁-definable;
`proper_of_small` for any language with symbol codes ≤ 8). **The M1 gate
`lower_bound_dlen_proof_lenGödel_fbound` is unconditional.** M1 is COMPLETE.
Proof-craft traps hit: `omega` is useless on `V` (use `le_self_add`/`le_add_self` under
`open PeanoMinus`); a `“ ”`-DSL wrapper around a PR `resultDef` makes `simp` run away
(17 GB) — define such wrappers as `.rew (Rew.subst …)` instances; Δ₁ blueprints put the Σ
formula in antecedent position of the Π form; `Fin 0 → V` parameter vectors need a
`Subsingleton.elim` step; `≤` on `V = ℕ` is `le_def` (`x = y ∨ x < y`), NOT `Nat.le`.

**M1 — `Bew_k` by length (Foundation only).** `len`, properness with the `superexp` bound,
`Bew_k` as a Δ₁ predicate (mirror `RestrictedProvable.defined`), monotonicity in `k`,
standard-model characterisation (`models_iff`), `Bew_k σ → PA ⊢ σ` (soundness, from
`SoundOn ℕ`). Gate: the restricted Gödel sentence and its lower bound re-proved for the
length measure — a like-for-like check against `RestrictedProvability.lean`.

**M2 status (2026-09-09 night, all compiling):** `LangAct.lean` (`LAct := ℒₒᵣ + constant Act`,
hand-written encoding keeping the `ℒₒᵣ` codes, Δ₀ symbol sets, `emb`, `swap`, `tlen`/`flen`
invariant under any hom), `TheoryAct.lean` (`TAct := insert axNe (insert axNe' (lMap emb 𝗣𝗔))`,
standard model `c_C ↦ 0, c_D ↦ 1`, `quote_lMap_emb` code agreement, Δ₁ via PA's own class ∧
"is an ℒₒᵣ-formula", `lMap_swap_mem_TAct`), `Transpose.lean` (`lMapT`: derivations transport
along a hom mapping axioms to axioms; `mlen_lMapT` for injective homs; `lMap_swap_swap`;
`transpose_exists`), `Sound.lean` (`Derivation.sound'`: a code IS the code of a meta
derivation), `Symmetry.lean` (`provableLen_swap_iff : TAct ⊢_k φ ↔ TAct ⊢_k swap φ`, Σ₁ form).
DESIGN CONCLUSION: the evaluator must be a Δ₁ FORMULA inside `TAct` (Critch's own setup —
"PA represents the evaluator"), not a new relation symbol with clause axioms: the latter's
axioms would mention the proof predicate of the theory they axiomatize, a circularity
Foundation's `Theory.Δ₁` (a `ch` given upfront) cannot express. A Δ₁ evaluator needs the
Δ₁ (code-bounded) `□_k`, whose swap-symmetry needs PROPERNESS (same length, different
code) — so properness precedes the evaluator. Proof-craft traps: `axm`/`func`/`verum` are
ambiguous patterns (qualify or dot-pattern); instances on `LAct.Func k` must be keyed on the
folded `Sum` form; simp lemmas about `encode` must fix `(α := LAct.Func k)`; Foundation's
notation forms (`⊤`, `⋏`, `∀¹`) differ syntactically from the constructors `induction`
produces — bridge with `change`; the hom lemmas are `LogicalConnective.HomClass.map_*`.

**M2 evaluator design (decided 2026-09-10, restricted template first).** Programs are
pair-codes in ℕ with action VALUES `0/1` (as in the engine): `const a`, `self`, `opp`,
`bot p`, `sim p q`, `ite b a p q`, `search k a p q` — a search node carries only the budget
and the action `a` of the ONE template "opp plays `a` against me" (generalisation to arbitrary
guard templates later). Numerals are rigid under τ, so a program never enters a sentence as a
bare numeral: the runtime guard sentence of `search k a p q` at `(me, opp)` is
`∃ m o, m = relabel(⌜x_me⌝, c_?, c_?) ∧ o = relabel(⌜x_opp⌝, c_?, c_?) ∧ ∃ n, Eval(n, o, m, o, c_a)`,
where `relabel(x, u, v)` re-values the actions `0 ↦ u, 1 ↦ v` and each program is described
CANONICALLY: `x₀ := min(x, swapcode x)` as the numeral, constants in the matching order,
and `(0, 1)` (no constants) in the tie case `x = swapcode x`. Then
`guard(swapcode me, swapcode opp, swap a) = swap (guard me opp a)` SYNTACTICALLY, for every
program. No diagonal lemma, no circular theory: self-reference happens at runtime, as with
the engine's `.self`/`.opp`. Files: `Prog.lean` (codes, Δ₀ graphs, `swapcode`),
`BewV.lean` (`□_k` with `k` a variable, Δ₁), `Guard.lean` (template, canonical description,
internal `guardCode` via `substs`), `Eval.lean` (Δ₁ fixpoint with fuel, meta `evalN`,
correctness, determinism), `RedCell.lean`.

**M2 COMPLETE (2026-09-10) — T1 IS A THEOREM.** `arith/ArithS/RedCell.lean`:

```
theorem red_cell (k : ℕ) :
    EvalGraph 2 (Dupoc k) (Cupod k) (Dupoc k) 1 ∧ EvalGraph 2 (Cupod k) (Dupoc k) (Cupod k) 0
theorem red_cell_unique : any result at any fuel is (1, 0)      -- determinism
#print axioms red_cell  = [propext, Classical.choice, Quot.sound]
```

with `Dupoc k := pSearch k ⌜Gtmpl⌝ 0 (pConst 0) (pConst 1)` and `Cupod k := swapcode (Dupoc k)`
(= `pSearch k ⌜Gtmpl⌝ 1 (pConst 1) (pConst 0)`, `swapcode_Dupoc`). Proof, exactly the engine's
`outcome_DupocBot_vs_CupodBot`: (i) `guard_Dupoc_iff_guard_Cupod` — the two runtime guard
codes are `⌜σ⌝` and `⌜swap σ⌝` (code equation + swap equation), so
`lenProvable_fbound_swap_iff` makes them provable together; (ii) `evalGraph_of_guard` — a found
guard is TRUE in `ℕ` (`LenProvable.provable` → `provable_iff_provable` → `models_of_provable`
with `ℕ ⊧* TAct` → the truth equation); (iii) both found ⇒ Dupoc plays `1` (truth of Cupod's
guard) and `0` (its own search clause) ⇒ `EvalGraph.unique'`. Files landed for M2 stage 2:
`Prog.lean` (codes, `relabel` fixpoint, `swapcode` involution), `BewV.lean` (`□_k` with `k` a
variable, Δ₁), `Guard.lean` (canonical descriptions `dnum/dU/dW`, `guardCode` via internal
`subst`), `Eval.lean` (`EvalGraph` as a `Finite` Σ₁ fixpoint on `⟪n,me,opp,p,a⟫`; `sim` has NO
clause yet), `EvalN.lean` (inversion per shape, determinism, fuel monotonicity at ℕ),
`Template.lean` (`gtmpl : 𝚺₁.Semisentence 7` from `relabelDef`/`evalGraphDef`; `Gtmpl` its
`emb`; `guardSentence`; `quote_guardSentence`, `lMap_swap_guardSentence`,
`models_guardSentence_iff`). Proof-craft traps added: at `V = ℕ`, `<` is `Nat.lt` but `≤` is
PeanoMinus's `x = y ∨ x < y` — `if_pos` on a `≤` needs `le_def`, so prove `dnum_of_lt/eq/gt`
helpers instead of rewriting; `.val` of a closed term is `t.val (s := stdAct) ![] Empty.elim`
(`s` is instance-implicit); `Semisentence` quotes use `Sentence.quote_def`;
`Semiformula.coe_subst_eq_subst_coe` + `typed_quote_substs` + `val_substs` is the code equation
route; `decide` fails on `Structure.rel` (classical instance) — `change ¬((0:ℕ) = 1)` first.

**2026-09-10, later — the unary-numeral VACUITY (theorem, then fixed).** `Vacuity.lean`
(commit 470ee43) proved: under Foundation's unary numerals a guard sentence mentions the
searcher's own code as `numeral (dnum me)` with `dnum me ≥ k`, so `flen guard ≥ 2k > k`,
every proof of it is longer than the budget, and `search_never_found : ¬LenProvableV TAct k
(guardCode ⌜Gtmpl⌝ (pSearch k ⌜Gtmpl⌝ a p q) opp a')` for EVERY top-level search node —
`Dupoc_always_defects`, `Cupod_always_cooperates`. `red_cell` was true, but for a reason
unrelated to symmetry: the model was degenerate (no bounded search can ever succeed). This
is Critch's assumption (b) — a number `k` must be written in `O(lg k)` characters, so that
an agent's own source, which contains `k`, fits inside budget `k` — and `Length.lean`'s
claim that (b) is "irrelevant to T1/T2" was wrong. FIX (M3 prerequisite, in progress):
describe programs by BINARY numeral TERMS `bnum n` (`𝟎`, `𝟏`, `𝟐·t`, `𝟐·t+𝟏` along the bits
of `n`, length `O(‖n‖)`), a Σ₁ StrongFinite fixpoint like `relabel`, with a meta twin
`bnumT`, code equation `⌜bnumT n⌝ = bnum n`, truth `val (bnumT n) = n`; only `descVec`
(Guard.lean) and `dnumT` (Template.lean) change — the length measure, properness and the
symmetry layer are untouched, and the honest symbol count stays a character count.
`Vacuity.lean` is retired for `Fit.lean`: `guard_fits : ∃ K, ∀ k ≥ K, flen (guardSentence
(Dupoc k) (Cupod k) a) ≤ k` — for all large budgets the guard fits (its constant is the bit
length of `⌜Gtmpl⌝` under Cantor pairing: large, but a constant). Non-vacuity of T1 is then
a theorem; whether a guard is actually PROVABLE within `k` is T3's question.

**Left open by design (generalise next):** `pSim` semantics (program substitution); general
guard templates (any Σ₁ formula in the seven description variables, swap-invariant); an
`Option`-valued meta evaluator `evalN` and its agreement with the engine's `Dynamics.eval`
(that is M3's bridge, on the bumped toolchain).

**M2 — the original plan (kept for the record).** Coded `Prog`, Δ₁ `Eval`,
`plays` sentences, `tr`/`TR` agreement, τ as the constant-swap automorphism of `T'` (2.4: renaming, axiom closure, `len ∘ τ = len`, `Eval` invariance),
Σ₁-soundness for `plays` sentences. Then, verbatim from `Theorems/DupocBot/vs_CupodBot.lean`:

```
Dupoc plays C  iff  PA ⊢_k ⌜Cupod plays C vs Dupoc⌝
Cupod plays D  iff  PA ⊢_k ⌜Dupoc plays D vs Cupod⌝
τ(cupod k) = dupoc k as values, so the two searches succeed together (2.4).
Both succeed ⇒ (soundness) Cupod plays C and Dupoc plays D, but Dupoc's search succeeded
so Dupoc plays C — contradiction. Both fail ⇒ (D, C).
```

No Löb, no cost constants, no floor. Gate: `outcome_arith (CupodBot k) (DupocBot k) = some (.C, .D)`
mirrored as `(DupocBot, CupodBot) = (D, C)`, for every `k` with enough fuel, `#print axioms`
= Lean's three. **This is T1 and the paper's headline for the arithmetized layer.**

**M3 status (2026-09-10 night, session wrap-up).** Started on the user's go-ahead. State:
1. ENGINE BUMP DONE: worktree `~/wt/osgt-arith-m3`, branch `colomban-arith-m3` (off
   `colomban-arith-s` @2a16615), commit 5b0dc7b: `engine/` on Lean v4.33.1, mathlib
   0df444a360ea (= arith's), `PrisonersDilemma` + `OutcomeCheck` green, proof-only repairs
   (127 `simpa … using!`, `dsimp +instances` for stale `Decidable` instances, `clear_value`
   for an omega recursion-depth regression, `simpa [-forall_const]` for typeclass timeouts).
   `Metatheory` was already broken before the bump (docstring above imports; the T31 chain
   lacks tvote/sys arms — TAUBOTS.md §4 debt). App caveat: LeanInteract's REPL fork has no
   v4.33.1 tag yet — the proof agent's fast checker will fall back to `lake env lean`.
2. WORKSPACE WIRING DONE (same worktree, commit aededc4, arith builds against the engine in
   3.5 s with zero engine rebuild; only `Formula` needs the `PD.` prefix): `arith/lakefile.toml`
   gains `[[require]] name = "PrisonersDilemma" path = "../engine"`, `arith/.lake ->
   ~/wt/arith-lake-m3` (packages shared with `~/wt/arith-lake`, own `build/`), smoke module
   `arith/ArithS/EngineBridge.lean` (`#check @PD.Pf`, `@ArithS.red_cell`). Next: MERGE `colomban-arith-s` (Vacuity/Fit commits) into `colomban-arith-m3`.
3. VACUITY FIXED (binary descriptions LANDED on `colomban-arith-s`: `Bnum.lean` 9a66980,
   `Guard.lean`/`Template.lean` binary `descVec`/`dnumT`, `ProofLength.lean`; package green
   through `Fit`). `Fit.lean` LANDED: `guard_fits : ∃ K, ∀ k ≥ K, ∀ a ≤ 1, flen (guardSentence
   (Dupoc k) (Cupod k) a) ≤ k` (and the swapped `guard_fits'`) — T1 is non-vacuous. TRAP
   (cost a day): a theorem stated with CLOSED constants built from the template (`10 * cG₀`,
   `Nat.size cP`) makes Lean's `Nat` defeq machinery try to EVALUATE `flen Gtmpl`/`encode
   Gtmpl` on the giant DSL term — hours, then a kernel "deterministic timeout";
   `@[irreducible]` does not stop the kernel. Cure: package such constants EXISTENTIALLY
   (`exists_guard_const`, `exists_size_const`) and do all arithmetic over variables. Also:
   `lake env lean` output is block-buffered when redirected, so a partial log shows nothing;
   bisect slow files by truncation with `timeout`. Original note: `Vacuity.lean` (470ee43, see the paragraph above) proves the
   unary-numeral degeneracy; an agent is replacing it by `Bnum.lean` (binary numeral term
   codes, Σ₁ fixpoint) + binary `descVec`/`dnumT` + `Fit.lean` (`guard_fits`). If that work
   is not on `colomban-arith-s` when you read this, redo it from the plan in `Notes/M3_TRANSFER/BRIEF.md` §2.
3b. `pSim` SEMANTICS — LANDED 2026-09-10 (see step (b) below; the paragraph is the original brief): `psubst me opp p` one-shot as in the engine (`pBot` frozen; a `pSearch`
   node's TEMPLATE is instantiated with the outer `me`/`opp` descriptions, keeping the action
   slot `#6` free, so `guardCode (gsubst me opp g) me' opp' a = guardCode g me opp a` — the
   engine's "guards inside a simulated program refer to the outer players"), the evaluator
   clause `EvalGraph n me opp (pSim p q) a ↔ EvalGraph n' p' q' p' a`, and τ generalised to act
   on templates (`relabelTemplate u w`: symbol code `2+a ↦ 2+relabelAct a u w`), so that
   `swapcode (psubst me opp p) = psubst (swapcode me) (swapcode opp) (swapcode p)`. If this is
   not on the branch when you read this, redo it from this paragraph.

4. THE TRANSFER THEOREM — DESIGN, NOT YET DECIDED. The reading (`M3_TRANSFER/READ_*.md`) and
   the brief (`M3_TRANSFER/BRIEF.md`, §3 and §5) establish: the engine's `.box` is interpreted
   by `Pf` ITSELF, so `boxIntro` is sound by fiat and no length bookkeeping exists; a
   same-budget "Pf k φ → PA ⊢ tr φ" over all 33 rules is equivalent to bounded HBL (M4):
   the budget-erased reading breaks `search_f` (Gödel II), the budget-keeping reading breaks
   `boxIntro` (danger 2), and a hybrid breaks `searchBranch`. Foundation at the pinned commit
   has NO modal realization package but keeps `ProvabilityAbstraction` (D1/D2/D3,
   formalized Löb, Diagonalization) and full r.e./computable representability
   (`rePred_weak_representation`, `codeOfComputablePred_provable(_neg)`). Honest M3
   candidates (to be settled by the judge panel whose first proposal is saved as
   `M3_TRANSFER/PROPOSAL_faithful.md`): (i) budget-erased soundness of the modal-
   propositional core with atoms as hypotheses ("S's Löbian core is a fragment of GL over
   PA"); (ii) same-budget PA-soundness of the agent layer for the arith evaluator, relative
   to the consulted bounded box facts (Δ₁/Σ₁-completeness per arm); (iii) the engine's
   `BoundedGL` interface instantiated for PA-S with the bounded-HBL fields as NAMED
   hypotheses; (iv) `Pf k φ ↔ PA ⊢ ρ(k,⌜φ⌝)` by representability (cheap, but it says "PA
   verifies S", not "S ⊆ PA"). Recommended combination: (i) + (ii) + (iii), stated
   with explicit boundaries; T2's paper sentence becomes "S is sound relative to PA up to
   Critch's assumption (d), which is stated as the one open hypothesis".

**M3 DESIGN DECISION (2026-09-10, after the panel's surviving proposal
`M3_TRANSFER/PROPOSAL_faithful.md`; the judge/synthesis stages were killed by a rate limit
and are NOT needed — the decision below is the orchestrator's, on the evidence in
`M3_TRANSFER/BRIEF.md` §3/§5 and the proposal's §0/§3).** T2 is REFORMULATED as three
theorems that locate exactly where the engine's `Pf` and PA-`S` agree and where they cannot:

* **T2-NEG (impossibility, unconditional).** No budget-keeping transfer exists at ANY
  inflation `e`: `Pf 1 (.plays (.const C) q C)` holds for every program `q`
  (`AtomProvable.mk` charges evaluation STEPS `n ≤ k`, never the conclusion's size —
  `pf_size_or_atom`'s exception), while any arithmetical realization of that atom writes
  `⌜TR q⌝` and a PA proof is at least as long as its conclusion (`flen_le_mlen`), so its
  length is unbounded in `q`. Second departure: `search_t` cites a budget-`k` proof at cost
  `numCost k = log₂ k + 1` (a budget DROP; `atom_search_t_top`). These are the two places
  where the engine's transcript-cost model presupposes Critch's (b)/(d) instead of
  counting characters. Deliverable: `theorem no_budget_keeping_transfer (e : ℕ → ℕ) :
  ∃ k φ, PD.Pf k φ ∧ ¬LenProvable fbound (e k) 𝗣𝗔 ⌜tr φ⌝` (witness `k = 1`,
  `q = botIter (e 1 + 8) (.const C)`), stated parametrically in the realization
  (hypothesis: `flen (tr (.plays p q a)) ≥ ‖⌜TR q⌝‖`).
* **T2-AGENT (same budgets, relative to the consulted box facts).** Every engine evaluation
  certificate is a run of the arithmetized evaluator: `PlaysProof me opp body a n → GuardAgree
  → ∃ N, EvalGraph N ⌜TR me⌝ ⌜TR opp⌝ ⌜TR body⌝ a`, where `GuardAgree` says that at every
  `.search k ψ` node the engine's `Pf k` verdict and `LenProvableV 𝗣𝗔 k ⌜tr (ψ.subst me opp)⌝`
  agree; unconditional for search-free programs. Needs the full-Prog evaluator (`pSim` via
  `psubst`, then `tvote`/`sys`/`selfIdx` or a `noTau` side condition closed under subst),
  the code translation `TR : Prog → ℕ`, and the substitution code equation
  `psubst ⌜me⌝ ⌜opp⌝ ⌜p⌝ = ⌜p.subst me opp⌝`. The box agreement IS bounded D1 — it is a
  hypothesis, named, never an axiom.
* **T2-CORE (budget-erased soundness of the modal-propositional core).** A `PfCore Γ φ`
  mirror of the 16 modal/propositional rules (`boxIntro axK axKf box4 boxMono diagF diagB
  atomBoxImpl implRefl implK implS mp implTrans weakenImpl impS2 contrapose negElim`) with
  atom hypotheses `Γ`, and `PfCore Γ φ → 𝗣𝗔 + tr⁰ Γ ⊢ tr⁰ φ` for `tr⁰` sending `.box k ψ` to
  Foundation's `provabilityPred 𝗣𝗔` and `.diag` to `fixedpoint`, discharged by
  `ProvabilityAbstraction` (D1/D2/D3, `formalized_löb_theorem`, `Diagonalization`) — "S's
  Löbian core is a fragment of GL over PA". (`atomBoxImpl` needs the atom realization to be
  Σ₁: `provable_sigma_one_complete`.)
* **T2-COND (the precise M4 obligation, optional).** `PALength e` with fields bounded
  D1/D2/D3/diag/cut/mono and `transfer_bounded` on the size-gated fragment; only `cut` and
  `mono` are provable now. State it as the `BoundedGL` instance's missing fields; do not
  put it in the paper as a result.

Paper sentence: "`S` is sound relative to PA wherever a character count exists (T2-CORE for
the logic, T2-AGENT for the agents); where the engine charges evaluation steps and cheap
citations instead of characters, no PA proof length can match, and we prove it (T2-NEG);
budget-keeping soundness is therefore exactly Critch's assumption (d), left as M4." The
budget-erased world is Barász/Berns' unbounded modal agents — T2-CORE reuses it, our
novelty stays the BOUNDED `S`. Engine-side cost-model finding for the user: charging
`AtomProvable.mk` by `n + |φ| ≤ k` and `search_t` by `n + k` would make a budget-keeping
transfer plausible but breaks every cheap-citation cell (`(2k+64)` staggers,
`outcome_DupocBot_vs_CooperateBot` at pad `atom_cost 1`) — a design decision, not M3.
CANONICAL BRANCH (2026-09-10): `colomban-arith-m3` in the worktree `~/wt/osgt-arith-m3`
(merge commit 2584ed4 = engine bump + workspace wiring + every arith result incl. `Fit`;
`lake build ArithS` there builds engine + arith in ~20 s incremental). The OneDrive checkout
stays on `colomban-arith-s` (arith-only, engine still v4.28 there) so the app/IDE keep working;
do NOT develop on `-s` any more — cherry-pick or merge INTO `-m3`.

**T2-CORE LANDED (2026-09-10, `colomban-arith-m3` commits 2cb55aa, f8382f4; files
`arith/ArithS/Core/Tr.lean`, `Core/Sound.lean`; not yet in `ArithS.lean`'s import list —
add `import ArithS.Core.Sound` after the template re-shaping lands).**
`tr A : PD.Formula → ArithmeticSentence` (budget-erased: `.box _ ψ ↦ provabilityPred 𝗣𝗔 (tr ψ)`,
`.diag _ tgt ↦ fixedpoint “x. prov x → tr tgt”` = Foundation's `kreisel`, `.eq ↦ ⊤/⊥`,
atoms by a parameter `A`), `inductive Leaf` (17 constructors = the non-core rules' conclusion
shapes, budgets dropped), and
`Pf_core_sound (A) (hleaf : ∀ ψ, Leaf ψ → 𝗣𝗔 ⊢ tr A ψ) : PD.Pf k φ → 𝗣𝗔 ⊢ tr A φ`
by `Pf.induct` (34 arms; core arms via `Entailment` lemmas `C_trans/C_of_conseq/mdp₁/implyK/
implyS/contra/neg_mdp`, `provable_D1/D2/D3`, `kreisel_spec`), three standard axioms. Reading:
"the engine's Löbian core is a fragment of GL over PA". Remaining for T2-CORE's paper use: an
instance `A` (the arith evaluator's `∃ n, EvalGraph …` sentence, after step (c)) and the leaf
discharge for that `A` — which is exactly T2-AGENT's content.

**M4 first field — bounded D2 in rule form (DONE 2026-09-11, `colomban-arith-m3`,
`ArithS/Cut.lean`, imported after `ProofLength`; census +6, three axioms).** The meta cut
`cutMP : T ⟹₂ {φ ➝ ψ} → T ⟹₂ {φ} → T ⟹₂ {ψ}` (one `cut` on `φ ➝ ψ = ∼φ ⋎ ψ`; right premise
`and` from a weakening of the proof of `φ` and the closed leaf `{ψ, ∼ψ}`; no cast needed —
`∼(∼φ ⋎ ψ) = φ ⋏ ∼ψ` is a `simp` fact) with EXACT accounting `mlen (cutMP d₁ d₂) ≤ mlen d₁ +
mlen d₂ + 5|φ| + 10|ψ| + 9` (every node charges its whole conclusion sequent: five sequents
of the cut tree, each bounded by `sqlen_insert_le`/`flen_neg`/`flen_imply`). Code level by
the `lenProvable_fbound_swap` pattern, factored into two reusable bridges:
`derivation_of_lenProvable` (code → meta derivation of `mlen ≤ k`) and
`lenProvable_of_derivation` (meta derivation of `mlen ≤ k` → `LenProvable fbound k`, code
bound by properness) — every further rule of the bounded-GL interface is "meta construction +
these two". Traps met: the arrow token in Foundation is `🡒` (`➝` does not parse); `have b := d.cast _`
forgets the definition so `mlen_cast` cannot fire — `obtain ⟨b, hb⟩ : ∃ b, mlen b ≤ k`;
`Monotone fbound` under Mathlib's `Preorder ℕ` does NOT unify with `LenProvable.mono`'s
`ORingStructure` preorder — prove monotonicity inline through `le_def`; `flen_neg`/`flen_imply`
were already in `FitBox.lean` (deleted there, `Cut` is upstream).

**Post-M3 increments (2026-09-10/11, `colomban-arith-m3`).** DONE: `AgentConverse` (eval ↔
EvalGraph under one two-sided `GuardAgree`; `GuardAgreeF` derived from engine soundness),
`Inst` (hom `c_C ↦ 0, c_D ↦ 1`; `pa_proves_trAt_inst`; atom leaves of T2-CORE discharged),
`Det` (determinism in every model of IΣ₁ by `pi1_order_induction`; negative atoms PA-provable
via the completeness theorem; `atomNeg` leaf discharged — only the twelve source-reading
leaves remain hypotheses = bounded D1), `Audit.lean` census (43 theorems, 3 axioms).
FitBox DONE (commit 7fd38cc, wired; census 47 theorems): Critch's (b) for box-carrying guards
SPLITS. Positive: `exists_flen_tmpl_const : BudgetLinear F → ∃ c₀ c₁, ∀ k, flen (tmpl (F k)) ≤
c₀ + c₁ · size k` (the TEMPLATE of a box is short). Negative, at EVERY budget:
`size_bnum_ge : n + 2 ≤ Nat.size (bnum n)` (under Cantor pairing the CODE of a binary numeral
term squares at every bit, so it is as long as a unary numeral), hence
`box_guard_never_fits : HasBox k φ → k < flen (trAt (.search k' φ p q) opp φ)` and the zoo
instances `legibleBot_guard_never_fits` — a searcher whose guard names its own budget inside a
box cannot fit its budget. T1/T2 unaffected (box-free guards); this blocks T3 until the
coding changes. Design fix (not implemented): store box budgets as node DATA referenced by a
seventh template variable (`lenProvG ⇜ ![#6, #0]`, filled by `descVec` from the node's `k`),
so the stored template's code is constant in `k`; or balanced numeral terms (depth
O(log log n), polylog codes). Occurrence of `#0` in `lenProvG` turned out provable
SYNTACTICALLY in 10 s (`simp only [sigma_mkDelta, val_mkSigma]` exposes only the connective
skeleton; the `!p` substitutions stay opaque) — the hangs were three other mechanisms, all
recorded in the file's proof-craft note (unification unfolding `qqAnd/qqExs` to `pair`; an
index mismatch `9` vs `6+1+1+1` making `isDefEq` unfold a giant quote; `whnf` of closed
`Nat` arithmetic on symbol counts).

IMPLEMENTATION SEQUENCE (decided 2026-09-10; each step is one agent-sized task, committed and
recorded here before the next starts):
 (a) TEMPLATE RE-SHAPING: `pSearch k g p q` with `g` a SIX-variable template code
     (me-triple `x₁ u₁ w₁`, opp-triple `x₂ u₂ w₂`; no action slot), `guardCode g me opp :=
     subst LAct (descVec6 me opp) g`; τ acts on templates: `relabelTemplate u w` maps function
     symbol code `2+a ↦ 2+relabelAct a u w` (identity for `(0,1)`, the `swap` code image for
     `(1,0)`), and `relabel u w (pSearch k g p q) = pSearch k (relabelTemplate u w g) …`. The
     restricted templates become the two closed instances `GtmplA a := gtmpl ⇜ [#0..#5, c_a]`
     (so `relabelTemplate 1 0 (GtmplA 0) = GtmplA 1`), `Dupoc k = pSearch k (GtmplA 0) (pConst 0)
     (pConst 1)`, `Cupod k = swapcode (Dupoc k) = pSearch k (GtmplA 1) (pConst 1) (pConst 0)`;
     `red_cell` re-proved (same argument). Guard/Template/RedCell/Fit change; Eval's search
     clause loses the action argument.
     **DONE 2026-09-10 (branch `colomban-arith-m3`, commits 7b96eda + 6dcb1b8, `lake build
     ArithS` green, `#print axioms red_cell`/`guard_fits` = Lean's three).** New module
     `ArithS/RelabelTemplate.lean`: `relabelSym` (Δ₀, `2 ↦ 2+u`, `3 ↦ 2+w`), `termRelabel`/
     `termRelabelVec` (`TermRec`, arity 2) and `relabelTemplate u w g` (`UformulaRec1` with
     param `⟪u, w⟫`, identity on non-formula codes) — Σ₁ functions; `relabelTemplate_zero_one`
     and `relabelTemplate_swap_swap` on EVERY code (formula codes by `sigma1_succ_induction`
     with the `IsUFormula` preservation lemma for `u, w ∈ {0,1}`); the meta link at ℕ,
     `relabelTemplate_quote : relabelTemplate 1 0 ⌜φ⌝ = ⌜lMap swap φ⌝` (propositions, then
     `_sentence`). `Prog.lean`: `pSearch k g p q`, the `Relabel` core is now a Δ₁ blueprint
     (`.mkDelta`, both polarities cite `relabelTemplateGraph` like `Eval` cites
     `guardCodeGraph`; still StrongFinite — the bound on `relabelTemplate` is never needed,
     the referenced pairs are `⟪p, p'⟫` with `p < x`, `p' < y`). `Template.lean`: `actT6`,
     `GtmplA a := Gtmpl ⇜ ![#0..#5, actT6 a]`, `guardSentenceA a me opp`, `lMap_swap_GtmplA`,
     `relabelTemplate_quote_GtmplA`, and the code/swap/truth equations under the new names.
     `Fit.lean`: constants `cG a := flen (GtmplA a)` (irreducible, packaged as `cG 0 + cG 1`
     in `exists_guard_const`) and `cP := ⟪⌜GtmplA 0⌝, pConst 0, pConst 1⟫`. Proof-craft traps
     added: (i) at `V = ℕ` the coercion `(↑k : ℕ)` inside quoted codes is Foundation's
     `Nat.cast` (from `instCommSemiring_foundation`), NOT definitionally `k` — `show`/`change`
     to plain `k` fails; the simp lemma is `natCast_nat` (`Nat.numeral_eq` is for
     `ORingStructure.numeral`); (ii) for the same reason numeral literals inside a generic-`V`
     definition (`if f = 2`) do not match ℕ-literals after `change` — prove the equations
     generically (`relabelSym_two : relabelSym 2 u w = 2 + u`) and instantiate with `exact
     (… (V := ℕ) …).trans rfl`; (iii) a `TermRec` graph `.rew (Rew.subst ![…])` of arity ≥ 5
     needs the evaluation spelled out (`val_rew`, `Semiformula.eval_substs`, a `funext`
     lemma for `val ∘ ![#0, #3, …]`) — `simpa [Matrix.comp_vecCons']` alone stalls; (iv)
     `section meta` is a syntax error on v4.33.1 (`meta` is a keyword); (v) `fin_cases` is
     not in scope in modules importing only `LangAct` — use `match i with | 0 => rfl | …`;
     (vi) `IsUTermVec`/`IsUTerm`/`IsUFormula` are defs, so dot-notation (`hv.termRelabelVec`)
     fails — call the lemmas explicitly.
 (b) `psubst`/`pSim` (3b above, now with `gsubst me opp g := subst (descVec6 me opp) g` closed —
     no free slot to keep), evaluator clause, determinism/mono, τ-equivariance.
     **DONE 2026-09-10 (branch `colomban-arith-m3`, commits fd45457 + 40eae59; `lake build
     ArithS` green, `#print axioms red_cell`/`guard_fits`/`swapcode_psubst`/`guardCode_gsubst` =
     Lean's three).** New module `ArithS/Subst.lean` (between `Guard` and `Eval`): `gsubst me
     opp g` = `guardCode g me opp` on templates (`IsSemiformula LAct 6 g`, `gsubst_of_template`)
     and the IDENTITY on every other code — ONE deliberate deviation from the brief, forced by
     τ-equivariance (trap (i) below); `guardCode_gsubst : IsSemiformula LAct 6 g → guardCode
     (gsubst me opp g) me' opp' = gsubst me opp g` (the instantiated template is a SENTENCE:
     `descVec_semitermVec`, `isSemiformula_guardCode`, and the new `subst_eq_self_of_le` — a
     formula with `n` free variables is fixed by any LONGER vector whose first `n` entries are
     the variables; Foundation's `subst_eq_self` needs exactly `n`); Σ₁ graph `gsubstGraph`.
     `psubst me opp p`: Δ₁ fixpoint with parameters `me opp`, **StrongFinite** (the referenced
     pairs `⟪p, p'⟫` are sub-pairs, as for `Relabel` — the brief's "Finite if gsubst grows codes"
     was too cautious), `psubstDef : 𝚺₁.Semisentence 4`, `𝚺₁-Function₃`, equations
     `psubst_const/self/opp/bot/sim/ite/search`, `psubst_of_not_shape`. τ-equivariance on EVERY
     code: `swapcode_psubst : swapcode (psubst me opp p) = psubst (swapcode me) (swapcode opp)
     (swapcode p)`, from `relabelTemplate_subst` (`relabelTemplate u w (subst v p) = subst
     (termRelabelVec u w n v) (relabelTemplate u w p)` for `u, w ∈ {0,1}`, `IsSemiformula n p`,
     `IsSemitermVec n m v` — term/formula recursions as `substs_substs`, plus
     `termRelabelVec_qVec`), the code-level description swap `termRelabelVec_descVec :
     termRelabelVec 1 0 6 (descVec me opp) = descVec (swapcode me) (swapcode opp)`
     (`termRelabel_dU/dW`, `termRelabel_bnum` via `termRelabel_of_LOR`, `dnum_swapcode` — the
     `dnum_*` helpers moved here from `Template.lean`) and `relabelTemplate_gsubst`. `Eval.lean`:
     the sim clause `⟪n, psubst me opp p, psubst me opp q, psubst me opp p, a⟫ ∈ C` in `Phi` and
     both blueprint polarities (`∃ sp, !psubstDef sp me opp p' ∧ …` / `∀ sp, … →`), `Finite`
     kept, `case_iff` extended; `EvalN.lean`: real `sim_iff`, `unique`/`mono` extended.
     `SimTest.lean`: `Mirror := pSim pOpp pSelf`, `mirror_vs_const : EvalGraph 2 Mirror (pConst a)
     Mirror a`, `mirror_vs_mirror : ∀ n a, ¬EvalGraph n Mirror Mirror Mirror a` (the engine's
     `none`), `swapcode_psubst_Mirror`, `sim_search_outer_guard` (a search node under `sim`
     consults `guardCode g me opp` of the OUTER frame). Proof-craft traps: (i) with `gsubst :=
     guardCode` on ALL codes the τ-equivariance is FALSE — `subst` truncates out-of-range
     variables to `0` and `relabelTemplate` fixes the resulting non-formula, so on `g = ^rel 2 R
     ?[c_C, #7]` (seven free variables) `relabelTemplate 1 0 (subst v g) = ^rel 2 R ?[c_C, 0]`
     but `subst v' (relabelTemplate 1 0 g) = ^rel 2 R ?[c_D, 0]`; the `IsSemiformula LAct 6`
     guard is what makes the statement unconditional (`isSemiformula_relabelTemplate_swap_iff`);
     (ii) `bnum_semiterm`/`numeral_semiterm` are stated over `ℒₒᵣ` — transport with
     `IsSemiterm.LAct_of_LOR` (`isFunc_LOR` from `func_def_LOR`; `LAct` keeps the `ℒₒᵣ` symbol
     codes); (iii) inside a `have … (x ∷ 0)` the `0` elaborates at `ℕ` (`Adjoin V ℕ` failure) —
     write `(0 : V)`, and never leave `bnum _` with a hole inside a `.isUTerm` chain; (iv)
     numerals: `(6 : V) = 0+1+1+1+1+1+1`, `(2:V)+1 = 3`, `(0:V) ≠ 2` etc. are all `norm_num` —
     rewrite `six_eq` before `IsSemitermVec.adjoin`/`termRelabelVec_cons` chains; (v)
     `add_le_add_right` on `V` yields `1 + n ≤ 1 + m` — use `add_le_add h (le_refl 1)`; (vi)
     names of the form `IsSemiformula.foo` declared in `ArithS` are not reachable by dot
     notation on Foundation's `IsSemiformula` (trap (vi) of step (a)) — call them, or name them
     `isSemiformula_foo`.
 (c) `TR : PD.Prog → ℕ` and `tcode : PD.Formula → template code` (the general template
     builder: `.plays p q a ↦ ∃ n, EvalGraph n (pc p) (pc q) (pc p) a` with the program terms
     built by Σ₁ graphs from the description triples, `.box k ψ ↦ ∃ g', substsGraph g'
     (descVec6 me opp) ⌜tcode ψ⌝ ∧ lenProvableV k g'`, `.eq`, `.diag` via fixedpoint codes),
     the code equations `TR (p.subst me opp) = psubst (TR me) (TR opp) (TR p)` and
     `⌜tr (ψ.subst me opp)⌝ = guardCode (tcode ψ) (TR me) (TR opp)`.
 **DONE 2026-09-10 (branch `colomban-arith-m3`, commit 21a31aa; `lake build ArithS` green,
     `#print axioms` of every headline theorem = Lean's three).** New module `ArithS/Code.lean`
     (imported after `Fit` in `ArithS.lean`). NAMES: `pcode : PD.Prog → ℕ` (the brief's `TR`),
     `tmpl : PD.Formula → Semisentence LAct 6`, `tcode φ := ⌜tmpl φ⌝` — one `mutual` block by
     STRUCTURAL recursion on the engine's mutual inductive (works with only the `Prog`/`Formula`
     functions declared; equation lemmas `pcode_*`/`tmpl_*` by `rw [pcode]`/`rw [tmpl]`, never
     `rfl`). `actCode : Action → ℕ` (`C ↦ 0`, `D ↦ 1`), tau constructors `↦ 0` (non-shape).
     THE DESIGN THAT MAKES THE META EQUATION LITERAL: every program inside an atom is described
     by ONE shape `descF X T U W := ∃ d, d = T ∧ X = relabel U W d` (`relDesc := lMap emb
     relabelDef.val`), with `(T, U, W)` = the frame variables for `.self`/`.opp` and the closed
     terms `cl (dnumT c), cl (dUT c), cl (dWT c)` of the program's own code `c` otherwise
     (`progAux`/`progGraph`/`closedDesc`; `cl t := Rew.castLE _ t` casts a closed term into any
     context and is fixed by EVERY rewriter, `rew_cl`). `.plays p q a ↦ ∃ x y n, D_p(x) ∧ D_q(y)
     ∧ evalG n x y x c_a` (`evalG := lMap emb evalGraphDef.val`; the engine's `play = eval me opp
     me`); `.eq p q ↦ ∃ x y, D_p(x) ∧ closedDesc (pcode q) y ∧ x = y` (frozen RHS by its code);
     `.box k ψ ↦ ∃ me opp, D_self(me) ∧ D_opp(opp) ∧ ∃ g, guardCodeG g (numTB ⌜tmpl ψ⌝) me opp ∧
     lenProvG (numTB k) g` (binary numerals `numTB c := lMap emb (bnumT c)` everywhere — no
     unary numeral of a code); `.diag ↦ ⊥` (side condition `noDiag`). Side conditions: `noTauP`
     (+ `noTauP_subst`), `closedP`/`closedF` (`subst_of_closedP/F`: `subst` fixes a closed
     program/formula), `atomicP p := p = .self ∨ p = .opp ∨ closedP p`, and THE FRAGMENT
     `fragP`/`fragF` (no tau, no `.box`, atoms over `atomicP ∧ fragP` programs).
     THEOREMS (all under `hme : me ≠ .self ∧ me ≠ .opp`, `hopp` likewise — players are programs,
     not pronouns; needed because `progAux .self` is the frame description):
     `tmpl_subst : fragF ψ → tmpl (ψ.subst me opp) = tmpl ψ ⇜ descTerms6 me opp` (the meta
     equation, `descTerms6 := cl ∘ descTerms (pcode me) (pcode opp)` at SIX variables — the two
     sides must have the same type; the LHS simply does not use its frame variables);
     `quote_subst_cl : ⌜σ ⇜ (cl ∘ w)⌝ = ⌜σ ⇜ w⌝` (codes do not see the context);
     `quote_trAt : ⌜trAt me opp φ⌝ = guardCode (tcode φ) (pcode me) (pcode opp)` for
     `trAt me opp φ := tmpl φ ⇜ descTerms (pcode me) (pcode opp)` (EVERY φ — this is the
     T2-AGENT atom realization); `tcode_subst : fragF ψ → tcode (ψ.subst me opp) = gsubst
     (pcode me) (pcode opp) (tcode ψ)`; `pcode_subst : fragP p → pcode (p.subst me opp) = psubst
     (pcode me) (pcode opp) (pcode p)`. τ: `lMap_swap_tmpl : fragF φ → lMap swap (tmpl φ) = tmpl
     φ.transpose` and `swapcode_pcode : fragP p → swapcode (pcode p) = pcode p.transpose`
     (mutual), `relabelTemplate_tcode : fragF φ → relabelTemplate 1 0 (tcode φ) = tcode
     φ.transpose`. Sanity: `pcode_DupocBot`, `fragP_DupocBot`, `swapcode_pcode_DupocBot`.
     SCOPE, HONESTLY: the code equations and τ hold on the BOX-FREE fragment, and cannot hold
     for `.box` under ANY compositional `tmpl`: the translated box carries the CODE of its body
     as a numeral, and `⌜tmpl (ψ.subst me opp)⌝ ≠ ⌜tmpl ψ⌝` — `tmpl (.box k (ψ.subst me opp))`
     and `tmpl (.box k ψ) ⇜ desc` are PA-provably equivalent sentences, not identical ones,
     and length-bounded provability is not invariant under provable equivalence (`□A(x)` vs
     `Prov(sub(⌜A⌝, x))`). The same numeral blocks τ on boxes (`swap` does not re-value a
     code constant; a `relabelTemplate`-based canonical description of TEMPLATE codes, like
     `dnum`/`dU`/`dW` for programs, would fix τ but not substitution). The zoo is box-free in
     its templates except LegibleBot/OptimBot. `.tvote/.sys/.selfIdx` satisfy both code
     equations trivially (`0 = 0`) but are excluded from `frag` since `EvalGraph` knows nothing
     about code `0`. The stored template of `pcode (DupocBot k)` is NOT `⌜GtmplA 0⌝` (different
     quantifier order/shape; equivalent guards, two different searchers) — `Dupoc k` of
     `RedCell.lean` stays the red cell's object. Proof-craft traps: (i) a `/-! … -/` docstring
     containing `me-/opp` ENDS at that `-/` (cost a cascade of 30 phantom errors); (ii) `∃¹ ∃¹ φ`
     does not parse — write `∃¹ (∃¹ (…))`, and parenthesize `⋏ (∃¹ …)`; (iii) `Rew.q`-chains on
     literal bound variables compute by `rfl` (`ω.q.q.q #3 = bShift³ (ω #0)`), so state the
     needed instance with `show … = _` and finish with `rw [rew_cl]; try rfl` — `simp
     [Rew.q_bvar_succ]` never fires on a literal `#3`; (iv) `refine (lemma _ _ ?_ …)` with a
     `rfl` argument for `w 0 = w' 0` UNIFIES `w := w'` — give the equation as a `?_` goal;
     (v) `congr n` counts `∃¹` AND `⋏` layers (`∃¹∃¹∃¹ (A ⋏ (B ⋏ C))` needs `congr 4` then `congr
     1`); (vi) `Semiformula.rel` is ambiguous under the opens (`Bootstrapping.` vs
     `FirstOrder.`) inside `show` — qualify; (vii) `induction` on the engine's mutual `Formula`
     is unavailable — write recursive `theorem`s with pattern matching (Lean accepts the
     structural recursion), `mutual theorem … end` for the τ pair.
 (d) T2-NEG (`ProofLength.lean` has `flen_le_of_lenProvable`; add `TR`'s code lower bound
     for `.bot`-iterates and the engine example `Pf 1 (.plays (.const C) q C)`).
     **DONE 2026-09-10 (commit 2882d49; `lake build ArithS` green, three axioms).** New module
     `ArithS/Neg.lean` (after `Code`). `botIter n p := .bot^n p`, `pBotIter`, `pcode_botIter`,
     `two_mul_lt_pBot : 2x < pBot x` (`unfold pBot pair; split_ifs; nlinarith/omega` after `show`
     at ℕ), `size_lt_size_pBot`, `le_size_dnum_pBotIter : n ≤ size (dnum (pBot^n x))` (`dnum` is
     the code or its `swapcode`, and `swapcode (pBot^n x) = pBot^n (swapcode x)`),
     `size_le_tlen_bnumT : size n ≤ tlen (bnumT n)` (the lower bound twin of `tlen_bnumT`),
     `flen_emb_descF_ge : tlen T + 1 ≤ flen (emb (descF X T U W))` (the `∃ d, d = T` shape puts
     the numeral at a SHALLOW position — no occurrence argument through the Σ₁ graphs needed),
     `size_dnum_le_flen_trAt : closedP q → size (dnum (pcode q)) ≤ flen (trAt me opp (.plays p
     q a))`. HEADLINE: `no_budget_keeping_transfer (e : ℕ → ℕ) (tr : PD.Formula → Sentence LAct)
     (htr : ∀ p q a, closedP q = true → Nat.size (dnum (pcode q)) ≤ flen (tr (.plays p q a))) :
     ∃ k φ, PD.Pf k φ ∧ ¬LenProvable fbound (e k) TAct ⌜tr φ⌝` — witness `k = 1`, `φ = .plays
     (.const C) (botIter (e 1 + 1) (.const C)) C`, `Pf.atom (AtomProvable.mk PlaysProof.const
     (le_refl _))`; instances `no_budget_keeping_transfer_tmpl` (for `trAt me opp`) and
     `no_budget_keeping_transfer_guardCode` (on `guardCode (tcode φ) (pcode me) (pcode opp)`,
     the code the arithmetized evaluator consults). Trap: after `simp only [app_exs, map_and,
     flen_exs, flen_and]` the conjunct's context is `3`, not `9` (the outer `⇜ descTerms` closes
     the six frame variables) — read the goal before writing the `have`; `omega` needs the
     bound `hB` stated with the goal's exact `Rewriting.app Rew.emb` spelling (`Rewriting.emb`
     is an abbrev but a different atom to omega) — ascribe the type and `exact` the lemma.
 (e) T2-AGENT for the const/self/opp/bot/sim/ite/search fragment (`noTau` side condition),
     then tvote/sys if time permits.
     **DONE 2026-09-10 (branch `colomban-arith-m3`; `lake build ArithS` green, 3201 jobs;
     `#print axioms` of every headline theorem = Lean's three).** New module `ArithS/Agent.lean`
     (imported after `Neg` in `ArithS.lean`). THE CONSULTED GUARD: `guardOf φ me opp :=
     guardCode (tcode φ) (pcode me) (pcode opp)` (= `⌜trAt me opp φ⌝`, `guardOf_eq_quote_trAt`;
     on the fragment = `tcode (φ.subst me opp)`, the template code of the CLOSED instantiation,
     `guardOf_eq_tcode_subst` from `tcode_subst` + `gsubst_of_template`). THE ORACLE HYPOTHESES
     (bounded D1 on the consulted guards — named, never an axiom; T2-NEG says no budget-keeping
     transfer exists in general, so this is exactly where Critch's (d) enters):
     `GuardAgreeT := ∀ φ me opp k, PD.Pf k (φ.subst me opp) → LenProvableV TAct k (guardOf φ me opp)`
     and `GuardAgreeF := ∀ φ me opp k m, PD.Pf m (.neg (φ.subst me opp)) → ¬LenProvableV TAct k
     (guardOf φ me opp)`. One-sided facts proved: `models_trAt_of_lenProvableV` (a found
     arithmetized guard is TRUE in ℕ — `lenProvableV_nat`, `provable_iff_provable`,
     `models_of_provable models_TAct`) and `not_interp_of_pf_neg` (an engine refutation
     falsifies the ENGINE reading `Formula.interp`, via `PD.BaseTheorems.Pf_sound`) — two
     different sentences (`play` vs `EvalGraph`), so `GuardAgreeF` is NOT derived.
     THE THEOREM: `playsProof_evalGraph (hag : GuardAgreeT) (hneg : GuardAgreeF) (h : PD.PlaysProof
     me opp body a n) (hme : Proper me) (hopp : Proper opp) (modestP me) (modestP opp) (modestP body) :
     ∃ N, EvalGraph N (pcode me) (pcode opp) (pcode body) (actCode a)`, by `PD.PlaysProof.induct`
     with the invariant IN THE MOTIVE (`Inv sf me opp body := Proper me ∧ Proper opp ∧ modestP
     me ∧ modestP opp ∧ modestP body ∧ (sf = true → all three `hasSearch = false`)`; the core
     `playsProof_evalGraph_core sf (hag : sf = false → …) (hneg : sf = false → …)` runs ONE
     induction for both headline versions). Arms: `const` at fuel 1; `self/opp/bot` at `N+1`
     through the inversion lemmas; `sim` through `pcode_subst` (both players) and `sim_iff`;
     `ite_t/ite_f` at `max N₁ N₂ + 1` via `mono_le` (`actCode_eq_of_beq`/`actCode_ne_of_beq_false`
     bridge the engine's derived `BEq` — `cases <;> decide`); `search_t/search_f` cite the oracle on
     the closed guard; the five vote arms and `sysStep` are `False` from modesty.
     `playsProof_evalGraph_searchFree` (same, `me/opp/body.hasSearch = false`, NO oracle),
     `atomProvable_evalGraph`/`_searchFree` (the `AtomProvable k (.plays me opp a)` forms —
     `cases` on the mutual-block inductive works), and THE TRUTH EQUATION `models_trAt_plays
     (me' opp' me opp a) : closedP me → closedP opp → (ℕ↓[LAct] ⊧ trAt me' opp' (.plays me opp a)
     ↔ ∃ N, EvalGraph N (pcode me) (pcode opp) (pcode me) (actCode a))` (`eval_relDesc`,
     `eval_evalG`, `eval_closedDesc : Eval b (closedDesc c) ↔ b 0 = c` via `relabel_val_desc`).
     THE FRAGMENT IS MODEST, NOT `fragP`: the brief's `fragP_subst : fragP p → fragP me → fragP opp
     → fragP (p.subst me opp)` is FALSE — `.self.subst me opp = me` must be `atomicP`, i.e.
     `closedP me`, and NO searcher is `closedP` (its template names `.self`/`.opp`; `closedP
     (DupocBot k) = false`). `modestP` = `fragP` with every `.sim` argument `atomicP` (placeholder
     or closed) — the engine's own T43 modesty, `modestP (DupocBot k) = true` by `rfl` — and then
     the `.sim` step's new frame is drawn from `{me, opp, p, q}` (`Inv.sim`), so no substitution
     closure lemma is needed at all. GAPS: (i) [CLOSED in instantiated form — the INSTANTIATION paragraph below] TRUTH → `TAct ⊢ trAt …` (Σ₁-completeness) is NOT
     derived: Foundation's `sigma_one_completeness` is over `ℒₒᵣ`, `TAct` is over `LAct`, and the
     realized sentence names `c_C`/`c_D`, which `TAct` leaves uninterpreted (only `c_C ≠ c_D`; the
     descriptions re-value programs through the same constants, so the sentence is
     action-symmetric and NOT an `emb`-image) — a proof would reason generically in the two
     constants; (ii) `GuardAgreeF` from engine soundness would need the CONVERSE of T2-AGENT
     (`EvalGraph → eval`) — DONE, the CONVERSE paragraph below; (iii) tvote/sys stay outside
     (code `0`). Proof-craft
     traps: `simp` never rewrites inside the INSTANCE-IMPLICIT structure argument of
     `Semiformula.Eval`, so `stdAct_lMap_emb` must be applied by `rw` in standalone
     evaluation lemmas (`eval_relDesc`/`eval_evalG`, using `relabel_defined.df v` /
     `evalGraph_defined.df v`) and those used under binders; `⋏` on `Prop` is
     `LogicalConnective.Prop.and_eq`; `stdAct.rel op(=) v ↔ v 0 = v 1` is `Iff.rfl`; literal
     `![…] i` indices need `Matrix.cons_val_two/three` AND `Matrix.cons_val_succ` together;
     `Pf_sound` lives in `PD.BaseTheorems` (import `PrisonersDilemma.Base.Soundness`;
     `hasSearch_subst` in `Base.AtomCerts`); a `variable {me opp}` clashes with a lemma named
     `opp` in the same namespace; `Bool.true_ne_false` does not exist (`Bool.noConfusion`).
     **THE CONVERSE — DONE 2026-09-10 (`ArithS/AgentConverse.lean`, imported after `Agent`;
     `lake build ArithS` green, 3203 jobs; eight new census lines in `Audit.lean`, all three
     standard axioms).** ONE two-sided oracle `GuardAgree := ∀ φ me opp k, fragF φ → Proper me →
     Proper opp → modestP me → modestP opp → (PD.Pf k (φ.subst me opp) ↔ LenProvableV TAct k
     (guardOf φ me opp))` — restricted to exactly the guards a modest match consults, the WEAKEST
     hypothesis both directions need (`GuardAgree.of_forall` from the unrestricted `Iff`,
     `GuardAgree.of_T` from `GuardAgreeT` + its converse). `GuardAgree.toT`/`.toF`: the `Iff`
     subsumes the modest instances of BOTH T2-AGENT hypotheses, `F` by engine soundness
     (`not_interp_of_pf_neg` + `Pf_sound` on the guard the `Iff` hands back). THEOREMS:
     `evalGraph_of_eval` (`PD.eval n me opp body = some a → ∃ N, EvalGraph N ⌜me⌝ ⌜opp⌝ ⌜body⌝ a`,
     induction on the ENGINE fuel unfolding `PD.eval` clause by clause, mirroring
     `eval_mono`'s case skeleton), `eval_of_evalGraph` (the converse, induction on the ARITH fuel
     through `EvalN`'s inversion lemmas), `eval_iff_evalGraph` / `play_iff_evalGraph` /
     `outcome_iff_evalGraph` (the `outcome` form via `outcome_eq_some_iff` + `eval_mono_le` at
     `max`), `playsProof_evalGraph_of_guardAgree` (T2-AGENT re-derived through
     `playsProof_sound`), `plays_interp_iff` (`(.plays me opp a).interp ↔ ℕ↓[LAct] ⊧ trAt me' opp'
     (.plays me opp a)` for closed modest players, via `models_trAt_plays`). PROOF-CRAFT: (1) the
     converse's core is stated for an ARBITRARY result code `r` (`∃ a, r = actCode a ∧ ∃ n, eval n
     … = some a`, `eval_of_evalGraph_core`) — the arithmetized `.ite` clause returns the guard's
     result as a bare natural, and the IH must first learn it is an action code; with an
     `actCode a`-shaped statement the `.ite` case is stuck. (2) NO `pcode` injectivity: induct on
     the fuel with the engine program in the frame, rewrite `pcode body` by its `@[simp]` equations
     and apply the inversion lemma of that shape; the `.sim` case is `← pcode_subst` on both
     players (the frame stays inside `{me, opp, p, q}` by `Inv.sim`). (3) `guardCode (tcode φ)
     (pcode me) (pcode opp) = guardOf φ me opp` is `rfl` — state it as a lemma so `rw` after
     `search_iff` lands on the oracle's spelling. (4) The engine's `.ite` `do` block: `rw [PD.eval,
     h₁]; simp only [bind, Option.bind]; rw [if_pos (beq_of_actCode_eq e)]` — `BEq` on `Action`
     is bridged by `cases <;> first | rfl | exact absurd …` (`beq_of_actCode_eq`,
     `beq_false_of_actCode_ne`; `if_neg` wants `¬ (r == c) = true`, take
     `Bool.eq_false_iff.mp`). (5) The `.search` `if` on a `Bool` is `if proofSearch … = true`;
     `proofSearch_spec` + the `Iff` in either direction; the else-branch needs only the
     contrapositive of `mp`, never a refutation.
     **THE INSTANTIATION — DONE 2026-09-10 (`ArithS/Inst.lean`, imported after `AgentConverse`;
     `lake build ArithS` green, 3204 jobs; nine new census lines in `Audit.lean`, all three
     standard axioms).** Closes gap (i) in its honest form: PA proves the atom sentences with
     the action constants INSTANTIATED. `inst : LAct →ᵥ ℒₒᵣ` (`Sum.inl f ↦ f`, `c_C ↦
     Language.Zero.zero`, `c_D ↦ Language.One.one`; match on `k, f` as `swap` does);
     `inst_emb_func`/`lMap_inst_emb` (the retraction `inst ∘ emb = id`, the same induction as
     `lMap_swap_emb`); `lMap_inst_std : Structure.lMap inst (standardModel ℕ) = stdAct`;
     `models_inst : ℕ↓[ℒₒᵣ] ⊧ lMap inst σ ↔ ℕ↓[LAct] ⊧ σ` (`Semiformula.models_lMap` with `(s₂ :=
     standardModel ℕ)`, then `rw` the structure equation). Σ₁-NESS WITHOUT A GENERIC
     `Hierarchy.lMap`: `Hierarchy` is defined over any `[L.LT]` language, but nothing beyond
     `∃¹/⋏/rel/⇜` closure is needed (`sigma_iff`, `and_iff`, `rel`, `rew_iff` — `⇜` is an abbrev
     for `Rew.subst w ▹`, so `rew_iff` fires under `simp`) once `lMap inst relDesc =
     relabelDef.val` and `lMap inst evalG = evalGraphDef.val` (instances of `lMap_inst_emb`)
     and `hierarchy_sigma` for the `𝚺₁.Semisentence`s; `progAux` by `split_ifs` (all three
     branches are `descF`), so `hierarchy_lMap_inst_trAt_plays` holds for EVERY frame and pair.
     THEOREMS: `pa_proves_trAt_inst (hga : GuardAgree) (me' opp' me opp a) (Proper me) (Proper
     opp) (modestP me) (modestP opp) : (∃ n, PD.play n me opp = some a) → 𝗣𝗔 ⊢ lMap inst (trAt
     me' opp' (.plays me opp a))` (`play_iff_evalGraph` → `models_trAt_plays` → `models_inst` →
     `sigma_one_completeness`); `pa_proves_trAt_inst_of_atomProvable` (through
     `playsProof_sound`); `pa_proves_trAt_inst_searchFree` (NO oracle, through
     `atomProvable_evalGraph_searchFree`); `Aι : Core.AtomRealization := fun p q a ↦ lMap inst
     (trAt p q (.plays p q a))`; `leaf_atom_sound`/`_searchFree` (the `Leaf.atom` shape),
     `leaf_atomBoxImpl_sound (kBox p q a)` (ALL programs, formalized Σ₁-completeness
     `provable_sigma_one_complete (T := 𝗣𝗔)` lifted by `Entailment.WeakerThan.pbl`),
     `transfer_of_leaves = Core.Pf_core_sound Aι`. PROOF-CRAFT: `Structure.ext` takes equalities
     of the WHOLE `func`/`rel` fields — `refine Structure.ext ?_ ?_` then `funext k f v` and
     `rcases f with f | ⟨(_ | _)⟩ <;> rfl` (a bare `ext k f v` misparses the second goal);
     `sigma_one_completeness (T := 𝗣𝗔)` finds `𝗥₀ ⪯ 𝗣𝗔` through `[𝗣𝗔⁻ ⪯ T] : 𝗥₀ ⪯ T`
     (Schemata.lean), no extra import; `Core.tr_plays` is `rfl`, so the leaf lemmas are the
     PA theorems verbatim; `Inst` must import `ArithS.Core.Sound` itself (`AgentConverse` does
     not). `closedP` → `Proper`: `models_trAt_plays` and `plays_interp_iff` now take `Proper`
     (their proofs used closedness only through `closedP_ne_self/opp`); every searcher is
     `Proper` and NONE is `closedP` (`closedP (DupocBot k) = false`), so the `closedP`-stated
     versions would have excluded every Löbian cell. NOT BUILT (recorded, results §4 boundary
     2): the NEGATIVE atom `𝗣𝗔 ⊢ ∼ lMap inst (trAt …)` from a play of `b ≠ a` — Π₁, needs
     PA-internal determinism (`EvalGraph.unique'` holds in every model of IΣ₁; the route is the
     completeness theorem + Σ₁ upward transfer of the positive run + internal uniqueness, but
     `val_bnumT`/`relabel_val_desc` are ℕ-only, ~150 lines of general-model evaluation lemmas
     first) — this is exactly T2-CORE's `atomNeg` leaf; and the generic `TAct ⊢ trAt …` with
     the constants uninterpreted (not an instance of Σ₁-completeness, not known true, needed
     by nothing).
 (f) T2-CORE via `ProvabilityAbstraction`.
Order of work: (1) merge `colomban-arith-s` (binary descriptions, `Fit.lean`) into
`colomban-arith-m3`; (2) `pSim`/`psubst`/`relabelTemplate` (3b); (3) T2-NEG (small);
(4) `TR` + substitution code equation + T2-AGENT for the sim/search fragment; (5) T2-CORE.

**M3 — unbounded soundness of `Pf` relative to PA.** Engine bumped; `ArithS` requires
`PrisonersDilemma`. Theorem `Pf k φ → PA ⊢ tr φ` by `Pf.induct`: modal arms from
`provable_D1/D2/D3` + `diagonal` + Löb; atom arms from Σ₁-completeness of true computation
steps (`provable_sigma_one_complete`); `search_f`/`atomNeg`/`eqNeg` arms from the sound
refutation + soundness of PA. Gate: every positive engine cell (a `Pf` witness) is a PA
theorem. **This is T2.** Corollary worth stating: `Pf_sound` factors through PA-soundness.

**M4 STARTED 2026-09-11 (new session; design brief `M4_BOUNDED_HBL/BRIEF.md`, reader reports
`M4_BOUNDED_HBL/READ_*.md`).** Goal restated by Colomban: a working `S'` with PBLT as a theorem;
the T2 bridge is DEFERRED (do not extend). Decisions: (1) follow Critch 2019's UNIFORM proof of
PBLT (one PA proof with `k` free, one meta instantiation at `O(lg k)`) — this needs NO
proof-producing bounded D1; the only hard item is bounded INNER necessitation
(`□_a ψ → □_{E a} □_a ψ`, `E` subexponential), stated first as a named hypothesis; bounded D2 and
instantiation are V-GENERIC lemmas on codes + `complete`. (2) The guard mismatch (a searcher's
guard names the numeral of its whole code, which is the `k`-instance of no formula because
Foundation's `pair` has an `if`) is fixed by re-coding PROGRAMS on the term-expressible pairing
`ppair x y = (x+y)²+y` and describing programs by TERMS — then Dupoc's guard is literally
`subst (bnum k) ⌜q_D⌝`. The earlier "box budgets as node data" fix is NOT a PBLT prerequisite
(Dupoc's guard is box-free); it stays deferred with the bridge. Agents launched: `ppair`
re-pairing of `Prog.lean` + downstream; `CutV.lean` (bounded D2 on codes inside every model).

**U2 DONE 2026-09-11 — bounded D2 on CODES inside every model of IΣ₁ (`ArithS/CutV.lean`,
census +6, three axioms).** `cutCode φ ψ d₁ d₂` (the five-sequent cut of `Cut.lean`, now on
derivation CODES via Foundation's internal constructors), `cutCode_proof`, `dlen_cutCode_le`
(`≤ dlen d₁ + dlen d₂ + 5|φ| + 10|ψ| + 9` by the `DlenGraph` inversion clauses);
`LenDerivable T k φ := ∃ d, Proof T d φ ∧ dlen T d ≤ k` (Σ₁, NO code bound) with
`lenDerivable_cut_V` UNCONDITIONAL for any Δ₁ theory; the `LenProvableV`-shaped
`lenProvableV_cut_V` (uniform `c₁ = 10, c₀ = 9`) under the named hypothesis `ProperV V T`
("a `T`-proof code of length `≤ k` is `< fbound k`") — a THEOREM at `V = ℕ` (`properV_nat_TAct`,
through `Proof.sound'` + `quote_derivation_le`), OPEN for general `V` (needs a V-internal
induction on derivation codes — brief §5 danger 4; wanted for the uniform argument);
`lenProvableV_mono_V`; and the whole thing as ONE ℒₒᵣ-sentence `cutSentence` with
`isigma1_proves_cutSentence`/`pa_proves_cutSentence`/`tact_proves_cutSentence` by the
completeness theorem (`Det.lean`'s pattern) — Critch's Property 1 as a PA theorem.
LESSON for the parametric box (U1): use `LenDerivable` (Σ₁, no `fbound`) inside the Löb
argument; `fbound`/`LenProvableV` is only needed where the EVALUATOR's guard is consulted
(Δ₁-ness of the search clause), so `ProperV V` enters exactly once, at the final step.

**U1 + U3 DONE 2026-09-11 (`ArithS/InstV.lean`, commit 47fa241, census 79 lines, three axioms,
NO named hypotheses).** `instB n k := subst LAct (bnum k ∷ 0) n` (the `bnum`-instance of a
one-variable formula code; Σ₁ graph; `quote_instB : instB ⌜φ⌝ k = ⌜φ ⇜ ![lMap emb (bnumT k)]⌝`;
`formulaLen_instB_le : |instB n k| ≤ |n| · |bnum k|` via a general `formulaLen_subst_le` with the
Δ₁ invariant `SubstInv`), the PARAMETRIC BOX `bewB a n k := LenDerivable TAct a (instB n k)` with
`bewBDef : 𝚺₁.Semisentence 3` — every later Löb sentence is written with it. Property 2 on codes:
`instCode` (cut of the `∀`-proof against `exsIntro` from an `axL` leaf), `dlen_instCode_le ≤
dlen d + 5|χ[t]| + 3|χ| + |t| + 7`, `lenDerivable_inst_V`/`lenDerivable_instB_V`/`bewB_of_all`
(V-generic, unconditional), meta twin `lenProvable_inst`/`lenProvable_inst_size`
(`+ 6·size k + 8` for the term) — the FINAL meta step of PBLT — and `pa_proves_instSentence`/
`tact_proves_instSentence`. Trap: state instantiation costs in `|χ[t]|, |χ|, |t|` separately
(`|χ| ≤ |χ[t]|` needs `#0` to occur). NEXT: U6 `Diag.lean` (parametric diagonal lemma over TAct
for LAct formulas — agent launched), then `ProperV V TAct` for general V, U7 (after the term
descriptions land), U8/U9.

**U0 DONE 2026-09-12 (`ArithS/ProgT.lean`, `ArithS/Instance.lean`, `ArithS/InstanceV.lean`;
descriptions switched in `Guard`/`Template`, consumers `Subst`/`Code`/`Neg`/`FitBox`/`Det`/`Fit`
repaired; full build green, every census line three axioms).** Programs are described by the
STRUCTURAL TERM of their code over `ppair`: `ppairT s t := ((s ^+ t) ^* (s ^+ t)) ^+ t` on term
codes and `progT : V → V` (Σ₁, a StrongFinite fixpoint on pairs exactly like `relabel`; budget
`k` and template code `g` as `bnum` leaves; `bnum x` on non-shapes), `IsSemiterm ℒₒᵣ`, Δ₁ graph
`progTGraphDef`, `progT.defined`; meta twin `progTT : ℕ → ClosedSemiterm ℒₒᵣ 0` (an inductive
graph with EXPLICIT equations — `cases` on a family indexed by `pBot p` fails — plus choice),
`quote_progTT : ⌜progTT x⌝ = progT ↑x` in EVERY model (proved in `V` with cast lemmas
`cast_pConst … cast_pSearch` for the shapes and Σ₁-absoluteness `cast_progT` +
`Semiterm.coe_quote_eq_quote` for the non-shape leaf — the ℕ-only route drowns in `OfNat`
instance mismatches, `instOfNatNat 3` vs `instOfNat` at `V = ℕ`), `val_progTT : val (progTT x) = x`
(`ppair` being a term is exactly what makes the description DENOTE the code), exact lengths
`|ppairTT s t| = 2|s| + 3|t| + 4`, `|succTT t| = |t| + 2` (searcher: `2|6̂| + 6|k̂| + 18|ĝ| +
54|p| + 81|q| + 162`), and the lower bound `size x ≤ |progTT x|` for free from
`val_lt_two_pow_tlen` (every closed ℒₒᵣ-term denotes `< 2^length`) — no size arithmetic on the
tower at all. `descVec me opp := progT (dnum me) ∷ dU me ∷ dW me ∷ …`, `dnumT x := lMap emb
(progTT (dnum x))`; `dnumT_eq_numTB` is gone. `Fit`: `exists_guard_const` now
`flen ≤ c · (|dnumT me| + |dnumT opp| + 5)`, `exists_desc_const : |dnumT (Dupoc k)| ≤ 36 · size k
+ D` (the constant carries `|bnumT ⌜GtmplA a⌝|`, packaged existentially), `guard_fits`/`guard_fits'`
byte-identical. THE HEADLINE: `dnum (Dupoc k) = pSearch k gD pD qD` with a `k`-INDEPENDENT inner
triple decided by the fixed inequality `innerD ≤ innerC` between two closed constants (never
evaluated; `ppair` reflects the order in its second argument, `pSearchInner_lt_iff`), `dUT/dWT
(Dupoc k)` `k`-independent, `progTT (pSearch k g p q) = searchT1 g p q ⇜ ![bnumT k]`, hence
`exists_dupoc_instance : ∃ q : Semisentence LAct 1, ∀ k, guardSentenceA 0 (Dupoc k) (Dupoc k) =
q ⇜ ![lMap emb (bnumT k)]` (witness `qDupoc := GtmplA 0 ⇜ ![TD, cl uD, cl wD, TD, cl uD, cl wD]`)
and `exists_dupoc_instance_code : ∃ cq, IsSemiformula LAct 1 cq ∧ ∀ k, guardCode ⌜GtmplA 0⌝
(Dupoc k) (Dupoc k) = subst LAct (bnum k ∷ 0) cq`; and V-GENERIC, for possibly NONSTANDARD
budgets: `exists_dupoc_instance_code_V : ∃ cq : ℕ, IsSemiformula LAct 1 cq ∧ ∀ (V) [𝗜𝚺₁] (k : V),
guardCode ⌜GtmplA 0⌝ (DupocV k) (DupocV k) = subst LAct (bnum k ∷ 0) ↑cq` — i.e. the guard code
is `instB cq k` (`InstV`), the input the parametric box `bewB` expects. Its proof re-runs the
analysis inside `V` (`swapcode_DupocV` by Σ₁-absoluteness of `relabelTemplate`; `Nat.cast_lt` for
the deciding inequality — PA⁻ models are `IsStrictOrderedRing`) and then composes internal
substitutions: `substs_substs` on the code of `qDupoc`, the code of the one-variable term `TD`
being the `ppairT`-tower with `^#0` in the budget slot (`quote_emb_searchT1`) which
`termSubst (bnum k ∷ 0)` fills (`termSubst_tower`, via `termSubst_func` + `termSubstVec_cons₂`
and `termSubst_eq_self` for the closed leaves). Traps: `≤` at `V = ℕ` is `instLE_foundation`
(`x = y ∨ x < y`), NOT `instLENat` — state comparisons with `<` (which IS `Nat.lt`) or with
V-generic lemmas instantiated at ℕ; `Phi`/equations over `V` must annotate `(𝟏 : V)` and the
existentials `: V`, or the whole pair elaborates at ℕ and casts; `(bnum k ∷ 0)` in a STATEMENT
needs `(0 : V)`; `rw [quote_bnumT]` at ℕ leaves `bnum ↑3` whose cast is not `rfl`-removable —
use `quote_bnumT_nat` or stay in `V`; `omega` mis-atomizes `2^a * 2^b` written twice through
different instance paths — factor the arithmetic into a helper over variables; the `‘…’`
term notation's `1` is the numeral operator, not `func one ![]` (`succTT` is characterized
through `oneTT`); the meta inductive graph needs explicit `hx : x = pBot p` arguments.
NEXT: U7 (Dupoc transparency in `V`, on `DupocV`), then U8/U9 with U5 as the named hypothesis.

**U6 DONE 2026-09-12 (`ArithS/Diag.lean`, commit 669704c, census +8, three axioms).** The
parametric diagonal lemma over `TAct` for `LAct` formulas: `tact_parametric_diagonal θ : ∃ ψ,
TAct ⊢ ∀¹ (ψ 🡘 θ ⇜ ![lMap emb ⌜ψ⌝, #0])` (Foundation's `parameterizedFixedpoint` is ℒₒᵣ-only —
`subst ℒₒᵣ` is the `L`-indexed recursion and ignores `c_C/c_D`; re-done with
`substNumeralParamsA := subst LAct (numeral x ∷ ^#0 ∷ 0)`), the `bnumT k` instances
(`tact_parametric_diagonal_inst`, `models_…`, `provable_code_…`; the two sides are DIFFERENT codes
`instB ⌜ψ⌝ k` / `instB ⌜θ/[⌜ψ⌝,#0]⌝ k` that TAct proves equivalent). REUSABLE: `tact_complete`
(completeness for `TAct` restricted to models with REAL equality — `Theory.Proof.complete` alone
admits congruence models; Foundation's `complete_on_eq_models` needs `𝗘𝗤 LAct ⪯ TAct`, proved here
axiom by axiom via PA's equality axioms along `emb`). TRAP: any `simp` touching the closed quote
`⌜tactDiag θ⌝` makes the kernel build a numeral over `LEAN_NAT_MAX_SIZE` — prove quote equations
for a VARIABLE sentence and instantiate; unfold `tactFixedpoint` only by its `rfl` lemma.

**U0b 2026-09-12 — the action axiom (a vacuity fixed).** `TAct` had only `axNe : c_C ≠ c_D`
(both orientations): the action constants were merely DISTINCT. But the guard sentences of the
search bots (`Template`/`Guard`) feed the constants as action VALUES into `relabel U W d`
(`Prog.lean`), which is only meaningful on `{0, 1}`: in a model of `TAct` reading `c_C ↦ 5, c_D ↦ 7`
the described program `relabel 5 7 (dnum (Dupoc k))` has a garbage template (`relabelTemplate 5 7`
produces the non-existent symbol code `2 + 5`), its search finds nothing, it plays `7`, and Dupoc's
guard sentence `guardSentenceA 0 (Dupoc k) (Dupoc k)` is FALSE there. Hence `TAct ⊬ guard` for every
`k`, and Dupoc could never cooperate in the arithmetized `S'` — a vacuity of the same kind as the
retired unary-numeral one (the model-class finding of `Transparency.lean`, 54aee07: the truth
equations hold only in `stdActV V`). THE FIX (`TheoryAct.lean`): the closed `LAct`-sentences
`axAct : (c_C = 0 ∧ c_D = 1) ∨ (c_C = 1 ∧ c_D = 0)` and its transposition
`axAct' : (c_D = 0 ∧ c_C = 1) ∨ (c_D = 1 ∧ c_C = 0)` (`lMap swap axAct = axAct'` and back, so the
axiom set stays LITERALLY swap-closed — `lMap_swap_mem_TAct`, the red cell's exact iff survives);
`TAct := insert axAct (insert axAct' (insert axNe (insert axNe' (lMap emb PA))))` — `axNe/axNe'`
KEPT (implied, but every membership chain expected them; now the chains go through the named
lemmas `axAct_mem_TAct … lMap_emb_PA_subset_TAct`, never re-derived downstream). `0`/`1` are
`zeroT/oneT := func (emb.func zero/one) ![]`, `eqF t u := rel eq ![t, u]`; Δ₁ by Foundation's
`Theory.Δ₁.insert` (two short closed codes). NEW: `stdActS M`/`swapActS M` (the two readings,
generic over `ORingStructure M`; `stdActV_eq_stdActS`, `stdActS_nat`), `eval_axAct_iff`/
`models_axAct_iff` (a structure with standard reduct — hence real equality — satisfies `axAct` iff
its constants read `(0,1)` or `(1,0)`), **`structure_eq_of_axAct : S = stdActS M ∨ S = swapActS M`**
(the model class of `TAct` on `M` is EXACTLY the two standard readings), `tact_proves_axAct`,
`models_axAct` (ℕ), and in `Diag.lean` `tact_complete` now hands `H` the four action axioms and
**`tact_complete' : (∀ M ⊧ PA, σ true in stdActS M ∧ in swapActS M) → TAct ⊢ σ`** — the form the
Löbian cells need (the guard truth equations are proved in `stdActV V`, i.e. `stdActS V`; the swapped
reading is its τ-twin). Every Audit statement unchanged, census three-axiom, +8 lines. Consumers
touched: `RedCell.models_TAct`, `Diag`, the `hPA` extractions of `CutV/InstV/Transparency`, `Det`.
Not changed: `Neg.lean` (`¬LenProvable` is a length argument, theory-independent); `Symmetry`/
`Transpose` (through `lMap_swap_mem_TAct`, statement unchanged).

**U7 DONE 2026-09-12 (`ArithS/Transparency.lean`, 54aee07, census +11).** Critch's step 0 for
Dupoc in every model: `eval_qDupoc_iff_V` (truth equation of `qDupoc` in `stdActV V`, `k : V`
arbitrary), `dupoc_search_V` (`LenProvableV TAct k (guard) → EvalGraph 2 (DupocV k) … 0`),
`dupoc_search_instB_V` (unconditional), `dupoc_loeb_premise_V` (via `ProperV`), the ℕ forms, and the
uniform ℒₒᵣ-sentence `dupocPremise` proved by IΣ₁/PA/TAct. FINDING that led to U0b: the truth
equations hold only in the standard readings of the constants — `Det.lean` already had the V-generic
evaluation lemmas (`val_bnumT_V`, `stdActV`, …; the reader's "ℕ-only" note was stale).
**ProperV DONE 2026-09-12 (`ArithS/ProperV.lean`, 5d9fc0a, census 115, UNCONDITIONAL).**
Properness of derivation codes inside every model of IΣ₁: internal towers `EV/FV` (Σ₁), sharp
`⟪a,b⟫ + 1 ≤ (max+1)²` (Foundation's `pair_polybound` is too weak for two tower levels),
`isUTerm_le_EV`, `isSemiformula_le_EV`, `isFormulaSet_le_FV`, `derivation_le_FV_dlen` (by
`IsUTerm.induction`/`sigma1_structural_induction`/`Derivation.induction1`), hence `properV_TAct`,
`properV_LOR`, `lenProvableV_cut_V'` (no hypothesis) and **`lenDerivable_iff_lenProvableV`** — the
Σ₁ box of the Löb argument and the Δ₁ box of the evaluator coincide in every model. Small-code
hypotheses are the INTERNAL `SmallCodesV`/`SmallRelCodesV` (a nonstandard model can carry
nonstandard symbol codes; for `LAct`/`ℒₒᵣ` they are explicit Δ₀ disjunctions). Traps: unification
whnf-timeouts on `V` from mismatched `+` shapes (state helper lemmas with the exact shape);
`1 ≤ dlen`/`1 ≤ formulaLen` are load-bearing for the `wk/shift` and `∀/∃` nodes.
IN FLIGHT: `NumeralFacts.lean` (short proofs of `numeral c ≤ bnumT k`), `Assembly/Prep.lean`
(Cupod's instance + truth equations, the conjunction `qDupoc ⋏ qCupod`, ∧-elimination on codes,
`Box_g`/`θ`, Σ₁ upward transfer, `BoundedInnerNec`); then U8/U9.

**U8-prep DONE 2026-09-12 (`ArithS/Assembly/Prep.lean`, ec5a8b6, census 138, no hypotheses).**
Cupod's instance (`qCupod := lMap swap qDupoc`, `guardCode_CupodV_eq_instB`, `cupod_search_V`), the
truth equations in BOTH readings (`eval_qCupod_iff_V`; `eval_swapActS : Eval (swapActS) φ ↔ Eval
(stdActS) (lMap swap φ)` — `swapActS` is literally the pull-back), the conjunction family
`pConj := qDupoc ⋏ qCupod` with `instB_quote_pConj`, ∧-elimination on codes (`lenDerivable_andL_V`:
`+ 8(|x|+|y|) + 7`), `pconj_both_V` (a bounded proof of the conjunction ⇒ BOTH searchers find their
guards ⇒ `EvalGraph 2 Dupoc … 0 ∧ EvalGraph 2 Cupod … 1`), `gBudget k := ‖k‖²`, the box formula
`Box_g χ` with `eval_Box_g_iff` in both readings, `theta` (`#0` = code slot, `#1` = budget),
`psi := tactFixedpoint theta` with **`psi_fixed_point : TAct ⊢ ∀¹ (psi 🡘 (Box_g psi 🡒 pConj))`**,
Σ₁ upward transfer `lenDerivable_of_nat`, `exists_lenDerivable_V_of_proof`, and the ONE hypothesis
`structure BoundedInnerNec (d c c₁ c₀ : ℕ)` (Critch's Property 4 / assumption (d), polynomial `E`).
IN FLIGHT: `Assembly/Uniform.lean` (U8: `poly_size_le_eventually`, `chain_V`, `psi_true_V`,
`pblt_uniform`), `Assembly/Cell.lean` (U9: `dupoc_self_coop`), `NumeralFacts.lean`.

**NumeralFacts DONE 2026-09-12 (`ArithS/NumeralFacts.lean`, 7ab172f, census +8).**
`lenProvable_le_bnumT (c) : ∃ C₀ C₁, ∀ k ≥ c, LenProvable fbound (C₀ + C₁·size k²) TAct
⌜leF ↑c (lMap emb (bnumT k))⌝` (+ strict twin): bit recursion cutting two uniform PA lemmas
(`c ≤ x → c ≤ 2x`, `c ≤ x → c ≤ 2x+1`, lengths existential) into the chain, finite base cases by
completeness; QUADRATIC in `size k` (each bit step pays the instantiation cost `5|χ[t]|`), so the
Löb budget becomes `gBudget k := ‖k‖³` (Prep). `leF t u := rel Eq ⋎ rel LT` = Foundation's `“t ≤ u”`;
bridge `substs_leF_imp` gives the exact instance shape for the meta closure.

**U8 + U9 DONE 2026-09-12 — PBLT IN PA-`S` AND THE DUPOC CELL, CONDITIONAL ON ONE NAMED HYPOTHESIS
(`ArithS/Assembly/Uniform.lean` 91df6b9, `ArithS/Assembly/Cell.lean` 4c8ecc9; census 162, three
axioms).** With `psi := tactFixedpoint theta` (`TAct ⊢ ∀¹ (psi 🡘 (Box_g psi 🡒 pConj))`,
`pConj = qDupoc ⋏ qCupod`, `gBudget k = ‖k‖³`) and the ONE hypothesis
`BoundedInnerNec d : ∀ χ, ∃ C, ∀ V k, L (g k) (instB ⌜χ⌝ k) → ∃ e ≤ C·((g k)^d + 1), L e (instB ⌜Box_g χ⌝ k)`
(Critch's Property 4 / assumption (d), polynomial expansion; the FIRST formulation with a uniform
`c₁·flen χ` term was UNSATISFIABLE — the target names `χ` by a unary numeral — and was restated;
`M4_BOUNDED_HBL/DESIGN_inner_necessitation.md` §10):
* `chain_V` — the uniform chain in every model (`chainBound … ≤ k` + a box of `psi(k)` at `g k` ⇒
  both searchers find their guards ⇒ `EvalGraph 2 (DupocV k) … 0 ∧ EvalGraph 2 (CupodV k) … 1`),
  `chainBound_poly` (`≤ C·‖k‖^(3d+3)`), `poly_size_le_eventually` (no induction inside `V`),
  `psi_true_V` (in both standard readings), **`pblt_uniform : ∃ k̂, TAct ⊢ ∀¹ (leF ↑k̂ #0 🡒 psi)`**;
* `exists_psi_instance_length` (the meta closure: `LenProvable (K₀ + K₁·size k + K₂·size k²)
  TAct ⌜psi[bnumT k]⌝`, via `lenProvable_inst_size` + `NumeralFacts` + `Cut`),
  **`dupoc_self_coop (hE : BoundedInnerNec d) : ∃ k₀, ∀ k > k₀, EvalGraph 2 (Dupoc k) (Dupoc k)
  (Dupoc k) 0 ∧ EvalGraph 2 (Cupod k) (Cupod k) (Cupod k) 1`** and `dupoc_finds_guard` (both
  searchers actually FIND their guards within `k`) — Critch's Theorem 3.7 in PA-`S`.
Thresholds are strict at ℕ (`k₀ < k`: `<` is `Nat.lt`, `≤` is `le_def`). Traps: `k̂`/`lit` are not
identifiers; uniform existential constants must be built as pure terms (mvar depth); `set` does not
fold into later facts; pin `(k := 0)` on `qqTwo_semiterm.isUTerm`; two `Nat.cast` instances at ℕ.
**REMAINING for the unconditional cell: U10 = prove `BoundedInnerNec 3`** (design + estimate in
`M4_BOUNDED_HBL/DESIGN_inner_necessitation.md`: eigenvariable construction, ~40 lemma-sentences by
`complete`, a `Derivation.induction1` recursion; 2.5–4 months; risk (1) checked OK). Notes NOT yet
synced to the OneDrive branch (do by copy, as before).

**M4 — quantitative HBL and parametric bounded Löb in PA.** The research-grade block:
* bounded D1: `PA ⊢_k σ → PA ⊢_{e(k)+|□_k σ|} □_k σ` — Critch's (d) with `e` linear or
  polynomial (danger 1);
* bounded D2: additive (concatenation), cheap — **DONE 2026-09-11 in RULE form with
  constants (`ArithS/Cut.lean`, first M4 field): `lenProvable_mp : □_{k₁}(φ ➝ ψ) → □_{k₂} φ →
  □_{k₁ + k₂ + c₁(|φ| + |ψ|) + c₀} ψ` with `(c₁, c₀) = (10, 9)`, sharp form
  `k₁ + k₂ + 5|φ| + 10|ψ| + 9` (`lenProvable_mp_sharp`), plus `lenProvableV_mp`,
  `lenProvable_fbound_mono`, `lenProvable_verum`; three axioms. The engine's `mp` charges
  `|ψ|` only, PA-S also pays `|φ|` (the cut formula is copied into the side sequents) — a
  constant-factor departure. Still open here: D2 as an INTERNAL sentence (`IΣ₁ ⊢ □_a(φ➝ψ) ⋏
  □_b φ ➝ □_{…} ψ`), which needs the cut construction formalized inside IΣ₁;**
* bounded D3: `IΣ₁ ⊢ □_a σ → □_{q(a,|σ|)} □_a σ` — formalized FEASIBLE Σ₁-completeness with
  its length tracked inside IΣ₁; the hardest single item;
* bounded diagonal lemma (fixed shape: constant + linear terms);
* PBLT (Critch Lemma 3.6) in its PARAMETRIC form: one uniform proof of `∀k ≥ N, ψ(k)`,
  instantiated at cost `O(lg k)` — this is what lets a bounded agent's certificate fit its
  OWN budget `k` (danger 2).

**M5 — the interface instance and the Löbian cells.** `pfBoundedGL`'s arithmetized sibling
(2.5); `bloeb`/`mutual_loeb` for free; new `pblt_arith` with polynomial staggering; the
Dupoc self-cooperation and mutual-Löb cells RE-PROVED parametrically (not transferred —
danger 2). **This is T3.**

**M6 — floors (open-ended, report honestly).** Each engine floor cell is, in PA, a
proof-length LOWER bound on `¬Bew_k(⌜φ⌝)` — a restricted-consistency statement. Template:
`lower_bound_gödelNumber_proof_restrictedGödel`; the mathematics is Pudlák's `k^ε` bound on
finite consistency, which is BELOW the engine's `+k` floor (danger 3). Expected result: some
same-`k` floor cells are OPEN in PA and are reported as such. Not thesis scope.

---

## 4. What transfers and what does not

| Engine result | In PA-`S` | Route |
|---|---|---|
| Red cell `(Dupoc, Cupod) = (D, C)` | holds, every `k` | M2, soundness + τ |
| Every positive `Pf`-cell (as a PA theorem, budget forgotten) | holds | M3 |
| Löbian cells at same `k`, large `k` | expected to hold | M4–M5, parametric PBLT, re-proved |
| Staggered cells `(2k+64, k)` | hold with POLYNOMIAL stagger | M5 |
| Floor cells `(D, C)` by `search_f` | OPEN until a lower bound is proved | M6 |
| Censuses (`no_provable_*`) | do not transfer; PA reads source for free (Σ₁-completeness), so PA-`S` is STRONGER than `Pf` and negatives are weaker | — |

The rule set `Pf` stays: it is the proof-search-friendly calculus the LLM pipeline targets,
and after M3 it is certified sound for PA-`S`. Nothing in the engine is replaced.

---

## 5. The real dangers

1. **Critch's assumption (d) is unproven and may be false for plain PA.** Linear proof
   expansion (`e*·k`) presupposes (c), abbreviations mid-proof. For a Hilbert calculus
   without a definition mechanism the verification proof is polynomial. Either extend the
   calculus with abbreviations (a design choice that must itself be justified as "an
   extension of PA") or accept polynomial `e` (Critch 2019's general setting; thresholds
   change, PBLT survives). Decide at M4, not before; T1/T2 do not depend on it.
2. **Budget fit.** A transferred `Pf` derivation of budget `k` becomes a PA proof of length
   `F(k) > k`, which does not fit the agent's own `□_k`. Same-`k` positive cells are NOT
   corollaries of M3; they need the parametric route (uniform proof + `O(lg k)`
   instantiation). The engine's additive costs are a faithful MODEL of that trick, not of
   raw PA lengths.
3. **Floors may flip.** The engine charges exactly `+k` for an else-certificate; in PA the
   proven lower bound on finite consistency is `k^ε`. A same-`k` floor cell can therefore
   be genuinely open in PA. This is the one place the arithmetized `S` can DISAGREE with the
   engine, and it is why the red cell (no floor) is the headline, not a floor cell.
4. **Encoding sensitivity.** Every cost constant depends on the coding of terms, numerals,
   and derivations; state large-`k` results only, never quote a constant. τ-equivariance
   depends on the abstract-constant design of 2.4: actions must NEVER be baked in as
   numerals visible to derivations (a silent, type-checking failure mode).
5. **Properness of `len` inside IΣ₁.** If the finiteness bound (`superexp`) is not proved
   internally, `Bew_k` is merely Σ₁, `Eval` is not Δ₁, and the agents are not provably
   total. Do this in M1 before anything else.
6. **Soundness as an instance, not an axiom.** Foundation states `SoundOn`/`SoundOnHierarchy`
   as classes; make sure the PA instance for ℕ is DISCHARGED (it is, from `ℕ ⊧* 𝗣𝗔`), and
   run `#print axioms` at every gate. A class assumption left open reads exactly like the
   deleted `atom_complete_false_guard` did.
7. **Toolchain and API churn.** Foundation moves fast (module system, `public import`,
   `grind` attributes). Pin a commit; budget a re-pin per quarter; the engine bump for M3 is
   a separate, dated task.
8. **Scope.** M4 is a research program (no prover has costed HBL). Finish line for the
   thesis is T1 + T2; M4–M6 are future work and must be labelled so in the paper.
9. **Overclaiming.** "Cannot be false" is true of the red cell in the precise sense that its
   proof uses only PA-soundness and τ-symmetry, which every instance of Critch's (a)–(d)
   has. It is NOT true of floor cells (3) and not of same-`k` Löb cells until M5. Say which.

---

## 6. Order of work (first four weeks)

1. M0: package skeleton, Foundation pinned, CI green on an empty theory.
2. M1: `len`, properness via `superexp`, `Bew_k` Δ₁, mono, `models_iff`, restricted
   Gödel re-proved by length. Post the design (length vs code) on the Zulip topic of
   2026-08-27 for a sanity check before M2.
3. M2 in three PRs: coded `Prog` + `Eval` Δ₁; `plays` soundness + `tr`/`TR`; τ + the red
   cell. Gate: `#print axioms`.
4. Schedule the engine toolchain bump; M3 starts after.
