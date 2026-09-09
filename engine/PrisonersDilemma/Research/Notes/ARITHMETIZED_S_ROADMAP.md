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
| T2 | Every `Pf`-derivation is a PA proof (`S` is sound relative to PA) | M3 (unbounded transfer) |
| T3 | The Löbian cells (`Dupoc` self-cooperation, mutual Löb) hold in PA at large `k` | M4 + M5 (bounded HBL, parametric PBLT) |

T1 and T2 together are the thesis-scoped finish line. T3 is a second program.

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

**M2 — agents, evaluator, the red cell (Foundation only).** Coded `Prog`, Δ₁ `Eval`,
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

**M3 — unbounded soundness of `Pf` relative to PA.** Engine bumped; `ArithS` requires
`PrisonersDilemma`. Theorem `Pf k φ → PA ⊢ tr φ` by `Pf.induct`: modal arms from
`provable_D1/D2/D3` + `diagonal` + Löb; atom arms from Σ₁-completeness of true computation
steps (`provable_sigma_one_complete`); `search_f`/`atomNeg`/`eqNeg` arms from the sound
refutation + soundness of PA. Gate: every positive engine cell (a `Pf` witness) is a PA
theorem. **This is T2.** Corollary worth stating: `Pf_sound` factors through PA-soundness.

**M4 — quantitative HBL and parametric bounded Löb in PA.** The research-grade block:
* bounded D1: `PA ⊢_k σ → PA ⊢_{e(k)+|□_k σ|} □_k σ` — Critch's (d) with `e` linear or
  polynomial (danger 1);
* bounded D2: additive (concatenation), cheap;
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
