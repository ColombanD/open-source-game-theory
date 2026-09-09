# The Bew Primer — provability predicates, incompleteness, Löb, and what `ArithS.Bew` is doing (2026-09-09)

*A self-contained study note for the arithmetized-`S` refactor (`ARITHMETIZED_S_ROADMAP.md`).
Reading time about three hours with the exercises. It assumes you know what PA is and what a
Lean proof looks like, and nothing else. Section 9 is the only one about the bounded case; it
is there so that `arith/ArithS/Bew.lean` reads line by line. Notation follows
`PROVABILITY_NOTATION.md`: `T ⊢ σ` is derivability (a fact about proofs), `ℕ ⊧ σ` is truth in
the standard model, and `□σ` is a SENTENCE of arithmetic — never a Lean judgment.*

---

## 0. What you should be able to do afterwards

1. Say in one sentence what `Bew_T(x)` is, why it is Σ₁ and not Δ₁, and why bounding the
   proof makes it Δ₁.
2. Write down the three Hilbert–Bernays–Löb conditions D1–D3, say which of them is
   "free", which is "cheap", and which is the hard one — and why the same ranking survives
   when every step is charged a length.
3. Reproduce the proofs of Gödel I, Gödel II, and Löb's theorem from D1–D3 and the diagonal
   lemma, on the back of a bus ticket.
4. Explain why the restricted Gödel sentence `G_k` ("I have no proof of length ≤ k") is
   TRUE and PROVABLE, while Gödel's `G` is true and unprovable — and read
   `true_lenGödel`, `provable_lenGödel`, `lower_bound_dlen_proof_lenGödel` as the three
   halves of that one fact.
5. Explain why the red cell `(Dupoc, Cupod) = (D, C)` needs soundness and the C/D symmetry
   only, and why Löbian cooperation needs Löb.

---

## 1. Arithmetization: how a theory talks about itself

**Gödel numbering.** Fix a computable injection `⌜·⌝` from syntax (terms, formulas,
sequents, derivations) into ℕ. Foundation builds codes with `Nat.pair` and represents sets
of formulas (sequents) as bit-sets `Σ 2^⌜φ⌝`; `ArithS.Proper` estimates how big these codes
get. Nothing below depends on the particular coding except the constants — and that is
exactly the roadmap's "danger 4", encoding sensitivity: state large-`k` results, never
quote a constant.

**Numerals.** For `n : ℕ` the numeral `n̄` is the closed term `S(S(…S(0)…))` (or a binary
variant; Critch's assumption (b) is that `k` is written in `O(lg k)` characters). The
QUOTATION of a sentence `σ` is the numeral of its code, `⌜σ⌝ := (code σ)‾`. A formula
`θ(x)` with one free variable can be applied to a quotation: `θ(⌜σ⌝)` is a sentence about
`σ`. This is the whole trick: the theory cannot mention `σ`, but it can mention the number
`⌜σ⌝`, and the coding is transparent enough that "the number `⌜σ⌝` has property `θ`"
can encode "the sentence `σ` has property P".

**The arithmetical hierarchy, bottom three rungs.** A formula is
* Δ₀ (bounded) if all its quantifiers are bounded, `∀x < t`, `∃x < t`;
* Σ₁ if it is `∃x₁…∃xₙ. δ` with `δ` Δ₀;
* Π₁ if it is `∀x₁…∀xₙ. δ` with `δ` Δ₀;
* Δ₁ (relative to a theory `T`) if it is `T`-provably equivalent to both a Σ₁ and a Π₁ formula.

Δ₀ sentences are decidable by evaluation. Σ₁ sentences are the semidecidable ones ("a
witness exists, search for it"); Π₁ sentences are the co-semidecidable ones ("no
counterexample exists"); Δ₁ predicates are the decidable ones. Every primitive recursive
relation is Δ₁ in IΣ₁ (Foundation's `𝚫₁` classes and the `definability` tactic exist for
this reason — `lenGödel'_sigmaOne` is one call to it).

**Σ₁-completeness — the single most used fact in this note.**

> **Theorem (Σ₁-completeness).** If `σ` is a Σ₁ sentence and `ℕ ⊧ σ`, then `PA⁻ ⊢ σ`
> (in particular `IΣ₁ ⊢ σ` and `PA ⊢ σ`).
>
> *Why.* A true Σ₁ sentence has a witness `n`; plugging in `n̄` leaves a true Δ₀ sentence,
> and a true Δ₀ sentence is provable because its bounded quantifiers can be unfolded into
> a finite conjunction/disjunction of numeral computations, each of which is a `PA⁻`
> theorem. The proof is a concrete, if long, computation trace.

Foundation: `Arithmetic.sigma_one_completeness_iff` (used in `provable_lenGödel`) and the
formalized version `provable_sigma_one_complete : IΣ₁ ⊢ σ → □σ` for Σ₁ `σ`.

**Soundness, the converse we do not get for free.** `T` is *sound* if `T ⊢ σ` implies
`ℕ ⊧ σ`; it is *Σ₁-sound* if this holds for Σ₁ sentences. PA is sound (ℕ is a model), but
soundness is a META assumption about `T`, not something `T` proves about itself (that
would be Gödel II). Foundation states it as the class `T.SoundOnHierarchy 𝚺 1`, which is
why every theorem in the second half of `Bew.lean` carries `[T.SoundOnHierarchy 𝚺 1]`.

---

## 2. The proof predicate and Bew

**`Prf_T(d, x)`: "`d` codes a `T`-derivation whose conclusion is the formula coded by `x`".**
Checking a proof is a primitive recursive job — decode `d`, check each step is an axiom or
an instance of a rule applied to earlier steps, compare the last line to `x` — so `Prf_T`
is Δ₁ in IΣ₁ provided the axiom set of `T` is itself Δ₁ (recognizable). Foundation:
`Bootstrapping.Proof T d φ`, requiring `[T.Δ₁]`; this is the `Proof T d φ` conjunct inside
`LenProvable`.

**`Bew_T(x) := ∃d. Prf_T(d, x)`: "`x` is provable".** One unbounded existential in front
of a Δ₁ matrix: **Σ₁, and in general NOT Δ₁**. There is no bound on how long a proof of
`x` might be, so no bounded search decides provability — and indeed provability in PA is
undecidable (Church). Hold on to this asymmetry; §9 is about what happens when you remove it.

**Notation.** `□σ := Bew_T(⌜σ⌝)`, a sentence of the metatheory's language. Foundation:
`provabilityPred T σ`, packaged with D1 as the structure `Provability T₀ T` (field `prov`,
the Σ₁ formula, and `bew_def`, which is D1). `Con_T := ¬□⊥` (`Provability.con`).

**Three levels that must never be confused.**

| Level | Statement | What it is |
|---|---|---|
| meta | `T ⊢ σ` | a derivation exists (a Lean term `T ⊢! σ`) |
| object | `□σ` | a Σ₁ SENTENCE of arithmetic; it can be provable, refutable, true, false |
| semantic | `ℕ ⊧ □σ` | the sentence `□σ` is true in the standard model |

> **Lemma (standard model).** `ℕ ⊧ □σ ⟺ T ⊢ σ`.
>
> *Why.* Left to right: a witness `d` in ℕ decodes to an actual derivation
> (`provable_of_standard_proof`). Right to left: an actual derivation has a code, which
> witnesses the existential (`proof_of_quote_proof`). This is the meaning-preservation of
> the coding, and it is the ONLY place where the object level and the meta level touch.

Combine with §1: if `T ⊢ σ` then `ℕ ⊧ □σ`, a true Σ₁ sentence, so `IΣ₁ ⊢ □σ`. That is D1
(§5). Conversely, if `IΣ₁ ⊢ □σ` and `IΣ₁` is Σ₁-sound, then `ℕ ⊧ □σ`, so `T ⊢ σ`; Foundation
calls this `provable_sound`, and the biconditional `T ⊢ σ ↔ IΣ₁ ⊢ □σ` is `provable_complete`.
Note the hypothesis: the direction "provably provable ⇒ provable" costs Σ₁-soundness. In
the engine this is `proofSearch_sound`; in the notation note it is why `⊢_k ¬φ` (`S`
refutes `φ`) and `¬ ⊢_k φ` (no derivation) are different statements.

**The two-theory pattern.** Statements ABOUT provability in `T` are proved in a metatheory
`T₀`, always IΣ₁ in Foundation (it is where Δ₁ coding and Σ₁-completeness are available),
while `T` itself is any Δ₁-axiomatized extension, PA or your `T' = PA + c_C, c_D`. `Provability
T₀ T` has both as parameters. You will see `[𝗜𝚺₁ ⪯ U]` ("U extends IΣ₁") on lemmas in
`Bew.lean`: that is the metatheory hypothesis.

**How Foundation actually proves the schemes.** Look at `provable_D1`: it does not build a
derivation of `□σ`; it shows `□σ` holds in EVERY model `V` of IΣ₁ (`internalize_provability`)
and invokes the completeness theorem `complete 𝗜𝚺₁`. That is why every file in `ArithS` is
written over an arbitrary `V` with `[V ⊧* 𝗜𝚺₁]` and why "meta-level" lemmas are the
`V = ℕ` instances: a statement proved for all models is a theorem of IΣ₁; a statement
proved for ℕ only is a fact about the standard model. `Proper` is of the second kind.

---

## 3. The diagonal lemma

> **Theorem (diagonal lemma, Gödel–Carnap).** For every formula `θ(x)` with one free
> variable there is a sentence `φ` with `IΣ₁ ⊢ φ ↔ θ(⌜φ⌝)`.
>
> *Why.* The substitution map `sub(⌜ψ(x)⌝, n) := ⌜ψ(n̄)⌝` is primitive recursive, hence
> represented by a Δ₁ formula. Put `D(x) := ∀y. (y = sub(x, x) → θ(y))` — "θ holds of
> the self-application of `x`" — and `φ := D(⌜D⌝)`. Unfolding, `φ` says "θ holds of
> `sub(⌜D⌝, ⌜D⌝)`", and `sub(⌜D⌝, ⌜D⌝) = ⌜D(⌜D⌝)⌝ = ⌜φ⌝`. So `φ ↔ θ(⌜φ⌝)`, provably,
> because the equation is a numeral computation IΣ₁ can carry out.

Foundation: `Bootstrapping.diag θ := “x. ∀ y, !ssnum y x x → !θ y”` is exactly `D`,
`fixedpoint θ := (diag θ)/[⌜diag θ⌝]` is exactly `φ`, and `diagonal θ : T ⊢ fixedpoint θ
🡘 θ/[⌜fixedpoint θ⌝]`. Abstractly, `class Diagonalization T` bundles the pair. `Bew.lean`
uses it twice: `lenGödel := fixedpoint (∼(lenProvable T fDef k))` and `def_lenGödel := diagonal _`.

Two remarks that matter for the engine. First, the fixed point is a SENTENCE, not a
program; there is no "self" object, only a sentence that provably talks about its own
code. Second, the engine's `Formula.diag` with the `diagF`/`diagB` rules is the rule-set
analogue of `fixedpoint` + `diagonal`, and the roadmap's `tr` maps one to the other. When
M3 comes, this section is the `diag` arm of `Pf.induct`.

---

## 4. Gödel's first incompleteness theorem

Apply the diagonal lemma to `θ(x) := ¬Bew_T(x)`:

`G ↔ ¬□G` — "I am not provable in `T`."

> **Theorem (G1).** Let `T` be a consistent, Δ₁-axiomatized extension of IΣ₁.
> (i) `T ⊬ G`. (ii) If moreover `T` is Σ₁-sound, `T ⊬ ¬G`. So `G` is independent of `T`,
> and (by soundness of PA) TRUE.
>
> *Why (i).* Suppose `T ⊢ G`. Then `ℕ ⊧ □G` (standard-model lemma), a true Σ₁ sentence, so
> `T ⊢ □G` (Σ₁-completeness). But `T ⊢ G ↔ ¬□G`, so `T ⊢ ¬□G`. Inconsistent.
>
> *Why (ii).* Suppose `T ⊢ ¬G`, i.e. `T ⊢ □G`. Σ₁-soundness gives `ℕ ⊧ □G`, so `T ⊢ G`.
> Inconsistent. (Gödel assumed ω-consistency; Rosser's trick — "every proof of me is
> preceded by a shorter refutation" — removes even that, needing consistency only.
> Foundation has `RosserProvability.lean`; we do not need it.)

Foundation: `Provability.gödel 𝔅 := fixedpoint T₀ “x. ¬!𝔅.prov x”`, `gödel_spec`,
`unprovable_gödel`, `unrefutable_gödel [𝔅.Kreisel]`, `first_incompleteness`. The class
`Kreisel` is precisely the hypothesis used in (ii), abstracted: `KR : T ⊢ 𝔅 σ → T ⊢ σ`
(the meta-level reflection that Σ₁-soundness delivers for the standard predicate).

Keep in mind the shape: the proof of (i) is a short chain
*meta derivation → true Σ₁ sentence → object derivation of `□G` → diagonal → contradiction*.
Every result below is that chain with different ingredients.

---

## 5. The Hilbert–Bernays–Löb derivability conditions

Gödel II and Löb do not use the coding directly. They use three properties of `□` and
nothing else, which is what makes a modal logic of provability (§8) possible.

> **D1 (necessitation).** If `T ⊢ σ` then `T₀ ⊢ □σ`.
> **D2 (distribution).** `T₀ ⊢ □(σ → π) → (□σ → □π)`.
> **D3 (formalized D1).** `T₀ ⊢ □σ → □□σ`.

**Why they hold, and what each costs.**

*D1 is free.* It is §1 + §2: a derivation exists, its code is a witness, the witnessed
Σ₁ sentence is provable. Note the level shift: D1 is a META rule ("if there is a proof of
σ then there is a proof of □σ"), not an implication inside `T₀`. Foundation:
`Provability.bew_def`, `provable_D1`.

*D2 is cheap.* Given codes of a proof of `σ → π` and a proof of `σ`, concatenate them and
append one modus ponens step; that is a Δ₁ operation on codes, and IΣ₁ proves it always
produces a proof of `π`. Foundation: `provable_D2`, class `HBL2`. In the length-charged
setting, D2 is ADDITIVE — the new proof is about as long as the two inputs together plus a
constant — which is why the engine's `mp`-type rules have `c_node`-style costs.

*D3 is the hard one.* It is D1 formalized INSIDE `T₀`: "for every `x`, if `x` is provable
then `□x` is provable". Unformalized, D1 was a meta argument with a concrete witness in
hand. Formalized, we must prove in IΣ₁ that from ANY code `d` of a proof of `σ` one can
compute a code of a proof of `□σ` — that is, IΣ₁ must prove Σ₁-completeness of `T` for
the specific sentence `□σ`, uniformly in the witness. This is "formalized Σ₁-completeness",
`IΣ₁ ⊢ σ → □σ` for every Σ₁ sentence `σ` (`provable_sigma_one_complete`), and D3 is the
instance `σ := □σ` (`provable_D3 := provable_sigma_one_complete (by simp)` — the `simp`
discharges "`□σ` is Σ₁"). It is the one condition whose proof requires an induction inside
IΣ₁ over the structure of the witness, and that is exactly why the roadmap marks bounded D3
(`IΣ₁ ⊢ □_a σ → □_{q(a,|σ|)} □_a σ`) as "the hardest single item" of M4: you have to track
the LENGTH of the computation trace that formalized Σ₁-completeness produces, inside IΣ₁.

Foundation groups D2 and D3 as classes `HBL2`, `HBL3`, `HBL`, over an abstract
`Provability T₀ T`; `Mono` (`T₀ ⊢ σ → π` gives `T₀ ⊢ □σ → □π`) and `Ext` follow from
D1 + D2. The engine's `Base/BoundedGL` is this structure with a cost index on every
field; `pfBoundedGL` shows the rule set `Pf` is a model, and after M4 the arithmetized
`□_k` should be a second model — that is milestone M5.

---

## 6. Gödel's second incompleteness theorem

`Con_T := ¬□⊥`. "`T` is consistent" is a Π₁ sentence.

> **Theorem (G2).** If `T` is consistent (and D1–D3 hold) then `T ⊬ Con_T`.
>
> *Why.* Work inside `T` (which extends `T₀`).
> 1. `G → ¬□G` (diagonal, §4)
> 2. `□G → □¬□G` (D1 on line 1, then D2)
> 3. `□G → □□G` (D3)
> 4. `□□G ∧ □¬□G → □⊥` (`¬□G` is `□G → ⊥`; D2 twice)
> 5. `□G → □⊥` (2, 3, 4), i.e. `Con_T → ¬□G`, i.e. `Con_T → G` (diagonal again).
>
> If `T ⊢ Con_T` then `T ⊢ G`, contradicting G1(i).

Foundation: `formalized_unprovable_gödel : T₀ ⊢ 𝔅.con 🡒 ∼𝔅 𝐆` (line 5),
`gödel_iff_con` (the converse direction too: `G` and `Con` are provably equivalent),
`con_unprovable`. The ONLY facts used were the diagonal lemma and D1–D3 — check the
derivation, no coding appears. This is the sense in which G2 is a theorem of the modal
logic GL, and the reason the engine can state `bloeb`/`pblt` on an abstract `BoundedGL`
structure without any arithmetic.

**What consistency statements have to do with floors.** A bounded consistency statement
"there is no proof of `⊥` of length ≤ k" IS provable (§9), but Pudlák showed every proof
of it has length at least `k^ε`. The engine's `search_f` charges a flat `+k` for an
else-play certificate; `k^ε < k`, so an engine floor may be an OPEN cell in PA. That is
roadmap danger 3 and milestone M6, and it is why the headline arithmetized result (the red
cell) is chosen to avoid floors entirely.

---

## 7. Löb's theorem

Löb answered Henkin's question "is the sentence `H ↔ □H` — 'I am provable' — provable?"
by proving something much stronger.

> **Theorem (Löb).** If `T ⊢ □σ → σ` then `T ⊢ σ`.
>
> *Why.* Diagonalize `θ(x) := (Bew(x) → σ)` to get the Kreisel sentence
> `K ↔ (□K → σ)` — "if I am provable then σ".
> 1. `K → (□K → σ)` (diagonal)
> 2. `□K → □(□K → σ)` (D1 on 1, D2)
> 3. `□(□K → σ) → (□□K → □σ)` (D2)
> 4. `□K → □□K` (D3)
> 5. `□K → □σ` (2, 3, 4)
> 6. `□K → σ` (5 and the hypothesis `□σ → σ`)
> 7. `K` (6 and the diagonal, right to left)
> 8. `□K` (D1 on 7)
> 9. `σ` (6, 8). ∎

Two corollaries. Henkin's sentence is provable (take `σ := H`: `T ⊢ □H → H` by the
diagonal, so `T ⊢ H`). And G2 is the case `σ := ⊥`: `T ⊢ □⊥ → ⊥` is `T ⊢ Con_T`, and Löb
turns it into `T ⊢ ⊥`. Löb is therefore the general form; G2 is its instance at `⊥`.

**Formalized Löb.** Running the same argument inside `T₀` gives the SENTENCE
`□(□σ → σ) → □σ` (`formalized_löb_theorem`). This is the Löb axiom of GL (§8), and it is
the shape the engine's `bloeb_engine` produces: from a derivation of the Löb premise at
one budget, a derivation of `□σ` at a computable larger budget.

**Why it is the heart of OSGT.** Take `DupocBot`: "cooperate iff I can prove my opponent
cooperates with me". Against itself, with `σ := "Dupoc plays C vs Dupoc"`, the program's
own definition gives `□σ → σ` (if the proof search succeeds, the guard fires and the play
is C). Löb concludes `σ`, and then — because that argument is itself a proof of `σ` — the
search succeeds and the play really is C. Two Dupocs cooperate because each can prove
that the other's cooperation follows from the provability of its own. Nothing in the
argument depends on either bot's SOURCE beyond the one implication; that is why the
mutual-Löb cells (`mutual_pblt_*`) work between different bots, and why the engine had to
internalize the diagonal (`Formula.diag`) to derive bounded Löb without an axiom.

Now the two dangers the roadmap lists become visible. The proof above is UNBOUNDED: it
uses D3 and D1 freely, and each use lengthens the derivation. In the bounded world, a
Dupoc with budget `k` needs the `□_k σ → σ` handshake to close at a length that fits
under `k`, and the naive translation costs `F(k) > k` ("budget fit", danger 2). Critch's
parametric bounded Löb theorem (Lemma 3.6, PBLT) is the way out: prove `∀k ≥ N. ψ(k)`
once, uniformly, and instantiate it at `k` for `O(lg k)` characters. The engine's
`pblt_engine` is the rule-set model of that trick; M4–M5 is the arithmetic version.

---

## 8. GL, the modal logic of provability (one page)

Since G2 and Löb used only D1–D3 and the diagonal lemma, abstract them: propositional
modal logic with

* all tautologies, modus ponens;
* **K**: `□(p → q) → (□p → □q)` (D2);
* **necessitation**: from `p` infer `□p` (D1);
* **Löb axiom (GL)**: `□(□p → p) → □p` (formalized Löb).

`4`: `□p → □□p` (D3) is DERIVABLE from GL, so it need not be postulated. The resulting
logic is GL (Gödel–Löb). Its Kripke models are the finite transitive irreflexive frames
(conversely-well-founded, which is exactly what the Löb axiom expresses semantically:
there are no infinite ascending chains, so induction along the accessibility relation is
available — the fixed point `K` in §7 is the syntactic shadow of this).

> **Theorem (Solovay 1976, arithmetical completeness).** `GL ⊢ A` iff for every
> realization `*` (an assignment of arithmetical sentences to propositional letters, with
> `□` read as `Bew_PA`), `PA ⊢ A*`.

So GL is EXACTLY what PA can prove about its own provability, schematically. Two facts
worth knowing. Fixed points are explicit in GL (de Jongh–Sambin): for a formula `A(p)` in
which `p` occurs only under `□`, there is a `□`-free-in-`p` sentence `D` with
`GL ⊢ D ↔ A(D)` — e.g. the fixed point of `¬□p` is `¬□⊥`, which is `gödel_iff_con` again.
And GL is decidable, so modal arguments about provability can be machine-checked cheaply.

The engine's `Base/BoundedGL` is a GL where every scheme carries a cost: `box k`,
`Proves k`, K at `k₁ + k₂ + c`, and so on. It is not a logic with a Kripke semantics of
its own yet — it is an INTERFACE, and its two models are the rule set `Pf` (proved) and
the arithmetized `□_k` (M5). This is the framing Foundation's maintainers found
"legitimate" on Zulip, and it is why M4's bounded D1–D3 are the fields to fill.

---

## 9. What bounding the proof changes (read this with `Bew.lean` open)

**The predicate.** Critch's Notation 3.5: `□_k σ` is "there is a proof of `σ` that takes at
most `k` characters of text". With a structural length measure `len` on derivation codes:

`Bew_k(x) := ∃d. (len d ≤ k ∧ Prf_T(d, x))`.

Two things happen at once, and they are the whole point.

**(a) It becomes Δ₁.** A derivation of length ≤ k has a code below some computable `f k`
(this is PROPERNESS, `Proper`: for Foundation's pairing-and-bitset coding the roadmap's
estimate is a triple tower, `F(12k)`), so the existential can be bounded:
`∃d < f(k). (Prf_T(d, x) ∧ len d ≤ k)` — a bounded quantifier over a Δ₁ matrix. Hence the
truth of `□_k σ` is decidable and both `□_k σ` and `¬□_k σ` are decided by IΣ₁
(Δ₁-completeness, the two-polarity version of Σ₁-completeness). Consequences the engine
already lives with: proof search is a finite computation, the guard of `.search` is a
decidable test, and agents TERMINATE. The unbounded `Bew` had none of these.

Look at `LenProvable f k T φ := ∃ d < f (numeral k), Proof T d φ ∧ dlen T d ≤ numeral k`
and its definition `lenProvable`, stated as a Π₁ formula: `∀ E, fDef E k → ∃ d < E, …`.
The Π₁ shape is because `f` is given by a Σ₁ GRAPH `fDef` (three `Exp.exp`s are not a
term), and "for every value `E` of `f k`" is the standard way to use a Σ₁-defined function
inside a Π₁ formula — the roadmap trap "Δ₁ blueprints put the Σ formula in antecedent
position". The predicate is nevertheless Δ₁ in IΣ₁, and the code bound is NEVER meant to
bite: it is there to make the search bounded, and `Proper` says every real derivation of
length ≤ k satisfies it. The docstring of `Bew.lean` says exactly this.

**(b) The Gödel sentence flips from unprovable to provable.** Diagonalize `¬Bew_k`:

`G_k ↔ ¬□_k G_k` — "I have no proof of length ≤ k."

> **Theorem (restricted Gödel sentence).** For `T` a Σ₁-sound Δ₁ extension of IΣ₁:
> (i) `ℕ ⊧ G_k`; (ii) `T ⊢ G_k`; (iii) every proof of `G_k` has length > k.
>
> *Why (i).* Suppose `G_k` is false. Then `□_k G_k` is true, so there is a real proof `d`
> of `G_k`, so `T ⊢ G_k`, so (Σ₁-soundness — `G_k` is provably equivalent to the Σ₁
> sentence `¬□_k G_k`, negation of a Δ₁ sentence) `ℕ ⊧ G_k`. Contradiction.
> *Why (ii).* `G_k` is true and Σ₁, so provable by Σ₁-completeness.
> *Why (iii).* If a proof of length ≤ k existed, `□_k G_k` would be true, contradicting (i).

Compare with §4: `G` is true because unprovable; `G_k` is true AND provable, but only by
proofs longer than the bound it talks about. The three theorems in `Bew.lean` —
`true_lenGödel`, `provable_lenGödel`, `lower_bound_dlen_proof_lenGödel` — are (i), (ii),
(iii) with `len` for "length"; Foundation's `RestrictedProvability.lean` has the same three
with `⌜d⌝ < f e` (the CODE) in place of the length, which is the template and not the
object (the roadmap's whole reason for M1). The intermediate `lower_bound_proof_lenGödel`
is the honest disjunction "code ≥ f k OR length > k"; `Proper` kills the first disjunct.

**(c) The derivability conditions acquire costs.** Rerun §5 with lengths:
* D1: `T ⊢_k σ` implies `T₀ ⊢_{e(k) + |□_k σ|} □_k σ` — the trace of the Σ₁-completeness
  argument for `□_k σ` is a proof, and its length is a function `e` of `k`. Critch's
  assumption (d) is that `e` is LINEAR; for a Hilbert calculus without abbreviations the
  honest bound is polynomial (danger 1). Decide at M4.
* D2: additive, as before.
* D3: `IΣ₁ ⊢ □_a σ → □_{q(a,|σ|)} □_a σ` — formalized Σ₁-completeness WITH its length
  tracked inside IΣ₁. Hardest item, as in §5, now with bookkeeping.
* Diagonal lemma: the fixed point has a fixed shape, so its size is a constant plus
  linear terms in the size of `θ`.

Löb's proof (§7) then goes through with a budget that is a computable function of the
input budgets — that is the abstract `BoundedGL.bloeb`. Whether the resulting budget is
≤ the agent's OWN `k` is the separate, parametric question (PBLT).

**(d) Why the red cell needs none of this.** `outcome(Dupoc k, Cupod k) = (D, C)`:
Dupoc plays C iff `T ⊢_k ⌜Cupod plays C vs Dupoc⌝`; Cupod plays D iff
`T ⊢_k ⌜Dupoc plays D vs Cupod⌝`. Under the C/D transposition τ (a constant-swap
automorphism of `T' = PA + c_C, c_D`, §2.4 of the roadmap) the two guard sentences are
each other's image and `len` is τ-invariant, so the two searches succeed or fail
TOGETHER. If both succeed, soundness makes both guarded plays true — Cupod plays C and
Dupoc plays D — but a successful search makes Dupoc play C. Contradiction. So both fail,
and the else-plays give `(D, C)`. Ingredients: `Bew_k σ → T ⊢ σ` (soundness), the
transposition lemma, and the standard-model lemma for the `plays` sentences. No D3, no
Löb, no cost constant, no floor. That is why it is T1 and the headline.

---

## 10. Map: concept → Foundation → `ArithS` → engine

| Concept | Foundation (pinned `58c76ac`) | `ArithS` | Engine (`Pf`) |
|---|---|---|---|
| proof predicate `Prf(d,x)` | `Bootstrapping.Proof T d φ`, `[T.Δ₁]` | conjunct of `LenProvable` | the `Pf` inductive itself |
| length of a derivation | — (none) | `dlen T` (`DerivationLength.lean`), meta bridge `MetaLength.lean` | the budget index `k` of `Pf k φ` |
| `Bew(x)` / `□σ` | `provabilityPred T σ`, `Provability T₀ T` | `LenProvable f k T φ`, `lenProvabilityPred` | `Formula.box k φ` |
| standard-model lemma | `provable_of_standard_proof`, `proof_of_quote_proof` | used in `true_lenGödel`, `lower_bound_*` | `Formula.interp` of `.box` = `Pf` |
| Σ₁-completeness | `sigma_one_completeness_iff`, `provable_sigma_one_complete` | `provable_lenGödel` | atom rules read true computation steps |
| soundness | `T.SoundOnHierarchy 𝚺 1`, `SoundOn`, `provable_sound` | hypothesis on every §-9 theorem | `sound_upto`, `proofSearch_sound` |
| diagonal lemma | `fixedpoint`, `diagonal`, `Diagonalization` | `lenGödel`, `def_lenGödel` | `Formula.diag`, `diagF`/`diagB` |
| G1 | `gödel`, `unprovable_gödel`, `first_incompleteness` | restricted twin: `true_lenGödel` + `lower_bound_dlen_proof_lenGödel` | — |
| D1 / D2 / D3 | `provable_D1/D2/D3`, classes `HBL2/HBL3/HBL` | M4 (costed) | `BoundedGL` fields, `pfBoundedGL` |
| G2 / Löb | `con_unprovable`, `löb_theorem`, `formalized_löb_theorem` | M5 | `bloeb_engine`, `pblt_engine`, `mutual_pblt_*` |
| bounded provability | `RestrictedProvable` (bounds the CODE) | `LenProvable` (bounds the LENGTH) | `Pf k` |
| properness | `Superexp.superexp`, `two_pow_le_superexp` | `Proper`, towers `E`/`F` (`Proper.lean`) | structural: `size` bounds are exact |
| transposition τ | — | `LangAct.swap` (constant swap, involution) | `Base/Transpose`, `Pf.transpose` |

---

## 11. Exercises for the bus (answers are in the sections named)

1. `Bew` is Σ₁. Write the Δ₀ matrix and the one unbounded quantifier. Now write `Bew_k` and
   say which extra fact turns the quantifier into a bounded one. (§2, §9a)
2. Derive G2 from Löb in one line, and Löb's "Henkin sentence is provable" in one line. (§7)
3. In the G2 derivation (§6), mark which line uses D1, D2, D3. Which line would fail if
   you only had D1 and D2? (Answer: line 3; and that is exactly the line whose bounded
   version is M4's hard item.)
4. `G` is true because it is unprovable; `G_k` is true and provable. Explain in two
   sentences why there is no contradiction, using the word "length". (§9b)
5. State the three ingredients of the red-cell proof and, for each, name the Foundation
   or `ArithS` declaration that provides it. Then say which of D1–D3 it uses. (§9d; the
   answer to the last part is "none".)
6. Harder. `LenProvable` is stated Π₁. Argue that it is nevertheless Δ₁ in IΣ₁, assuming
   `fDef` is a total Σ₁ function. (§1, §9a: a Σ₁-defined total function can be pushed
   through as `∃E. fDef E k ∧ …` as well.)
7. Harder. Why does the roadmap insist the actions are fresh CONSTANT SYMBOLS rather than
   the numerals `0̄`, `1̄`? Give a derivation step that would break τ-invariance if `C` were
   `0̄`. (§9d; hint: `0̄ < 1̄` is a theorem of PA, and `len` cannot see which numeral is which.)

---

## 12. Where to read more (in order of usefulness for this refactor)

* **Peter Smith, *An Introduction to Gödel's Theorems* (2nd ed., CUP 2013).** The
  chapters on the diagonal lemma, on the derivability conditions and Gödel II, and on
  Löb's theorem are the gentlest complete treatment; the presentation of D1–D3 and the
  ranking "D3 is the hard one" is the one used above. Smith's free companion, *Gödel
  Without (Too Many) Tears* (logicmatters.net, PDF), covers §§3–7 of this note in about
  forty pages and is the best single download for a bus.
* **George Boolos, *The Logic of Provability* (CUP 1993), chapters 1–3.** Chapter 2 is
  the canonical treatment of D1–D3 and the proof of Löb; chapter 3 is Solovay's theorem.
  Dense but exact; this is where to check any step in §§5–8.
* **Rineke Verbrugge, "Provability Logic", *Stanford Encyclopedia of Philosophy*.** GL,
  Solovay, the fixed-point theorem, and a survey of bounded and interpretability variants,
  with a good bibliography. Free, and readable offline if saved beforehand.
* **Craig Smoryński, *Self-Reference and Modal Logic* (Springer 1985), chapters 0–2.**
  The diagonal lemma done thoroughly, and the cleanest account of why D3 is formalized
  Σ₁-completeness.
* **Hájek & Pudlák, *Metamathematics of First-Order Arithmetic*, chapter III**, and
  **Pudlák, "On the length of proofs of finitistic consistency statements in first order
  theories" (1986).** The bounded world: lengths of proofs, the `k^ε` lower bound on
  finite consistency, and why IΣ₁ is the right metatheory. This is the mathematics behind
  §9c and M6.
* **Critch, "A parametric, resource-bounded generalization of Löb's theorem" (2019/2022),
  §3 and Appendix B.** Notation 3.5 (`□_k`), Lemma 3.6 (PBLT), and assumptions (a)–(d)
  that fix `S`. Read Appendix B once against §9c above; the roadmap's danger 1 is the
  observation that (d) is assumed, not proved.
* **Foundation's own sources.** `Incompleteness/ProvabilityAbstraction/Basic.lean`
  (100 lines: `Provability`, `HBL2`, `HBL3`, `Kreisel`, the Gödel sentence, G1, G2, Löb —
  the entire §§4–7 in Lean, worth reading top to bottom once), then
  `StandardProvability.lean` (the concrete `provable_D1/D2/D3`), then
  `RestrictedProvability.lean` (the template `Bew.lean` was written against).
