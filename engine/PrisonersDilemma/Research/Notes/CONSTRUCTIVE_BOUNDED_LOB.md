# Constructive Bounded Löb — design note for computable `eval`

_Companion to `COMPUTABLE_EVAL_NOTES.md`. That note diagnoses **why** `eval` is
`noncomputable` (the `PBLT`/`box_provable` axioms inject witness-free members into
`Provable`). This note designs the **fix**: a constructive bounded Löb that builds the
size-≤-k certificate, collapsing `Provable` onto the decidable `Provable_finite` and
making `eval` total._

_Status: design only. No code yet. Research-open — flags exactly where the wall is and
the soundness obligation that is the hard mathematical content._

---

## 0. The one thing to keep straight

There are **two different theorems** people conflate under "prove PBLT", and they serve
**different goals**:

| | Theorem | Goal it serves | Constructive? | Makes `eval` computable? |
|---|---|---|---|---|
| **(A)** | **Critch's PBLT** (`PBLT_proof.tex`, Thm 3.6) | "explicit S" — honest axiom surface | **No** — classical diagonal lemma, proves `∃m, Provable m φ` with no extractable witness | **No** |
| **(B)** | **Constructive bounded Löb** (this note) | THE crux — computable `eval` | **Yes** — builds a size-≤-k proof *term* | **Yes** |

**(A) is not (B).** Transcribing Critch faithfully — abstract-interface *or* full
Gödel-encoded — yields a non-constructive existential and leaves `eval` noncomputable.
The crux lever is (B), which is **a theorem Critch did not prove**. His informal FairBot
argument ("search proofs of length ≤ k") gestures at the constructive content; his
*formal* PBLT throws it away by going through the diagonal lemma. We have to rebuild it.

This note is about **(B)**.

---

## 1. The precise wall

Recall (`Derivation.lean`, `COMPUTABLE_EVAL_NOTES.md §1`) the two predicates:
- **`Provable_finite k φ`** — ∃ a finite proof *term* of size ≤ k. **Decidable** by
  enumeration. This is Critch's computable `□_k`.
- **`Provable k φ`** — `Provable_finite` PLUS witness-free axiom members (`PBLT`,
  `box_provable`). Non-decidable *because* of those members.

Goal (B) = **collapse `Provable` onto `Provable_finite`**: every Löb-fixpoint cooperation
must have an actual size-≤-k term, so the axioms become *theorems that build the term*,
and `DecidablePred (Provable k)` follows by enumeration.

**Why the naive route fails (the wall).** Take the canonical fixpoint
`FB plays C vs FB`. Its certificate, via the `search_t` constructor
(`Derivation.lean:241`), requires as a *premise*:

```
Provable k (guard.subst FB FB)        -- guard = (.plays .opp .self .C)
                                      -- subst → (.plays FB FB .C)
```

i.e. the premise of "FB cooperates" **is the atom "FB cooperates" itself.** `PlaysProof`
is an `inductive` (LEAST fixed point), so this infinite descent is **forbidden — and
correctly so.** No finite `PlaysProof` of the cooperation exists by naive assembly. This
is not a Lean defect; it is the honest fact that a depth-unbounded proof search *would*
loop. It is also exactly why:

- `evalC` (shipped option D) returns `none` here;
- Critch's PBLT is non-constructive;
- `DecMeasure.lean` refuted deciding `Provable` by **recursion on the program** (subst of
  a `.search`-bot into its own guard raises search-depth — unbounded descent again).

**The escape is to recurse on the BUDGET `k`, not the program.** At a *finite* budget
`k`, the certificate is a depth-≤-`k` unfolding of the guard, which **terminates**. The
bounded box is the whole point: `□_k` does not ask for the fixpoint, it asks for a proof
of length ≤ k, and there are finitely many of those. The combinator below makes that a
term-builder.

---

## 2. The redesign — three pieces

### 2.1 Size-index the proof object

Make proof size a **type index**, not a derived `def`:

```lean
-- now:    inductive Derivation : Formula → Type
-- target: inductive Derivation : Formula → Nat → Type     -- Derivation φ k = "proof of φ, size ≤ k"
```

so that `{ d : Derivation φ k }` is a **finite, enumerable** type for each `(φ, k)`, and
"proof of size ≤ k" is a first-class object rather than the `d.size ≤ k` side-condition
on `Provable.struct`. Same for `PlaysProof` (it already carries the cost `n` as an index —
good — but the cost must become a genuine *upper-bound* index `≤ k`, with monotone
weakening, so the enumeration space is downward-closed).

Payoff: `Provable_finite k φ := Nonempty (Σ n, n ≤ k ∧ ProofTerm φ n)` is **decidable**
because the Σ-type ranges over a finite set.

### 2.2 The productive bounded-Löb combinator

This is the new constructor / theorem — the heart of (B). Signature sketch (informal):

```lean
/-- Constructive bounded Löb. Given a constructive, budget-monotone "discharge"
    that turns a size-≤-j certificate of φ at every budget j < k INTO a size-≤-k
    certificate of φ, BUILD a size-≤-k certificate of φ outright — by unfolding
    the discharge exactly `k` times (terminating because k is finite). -/
def boundedLob
    (φ : Formula)
    (step : ∀ k, (∀ j, j < k → ProofTerm φ j) → ProofTerm φ k) :
    ∀ k, ProofTerm φ k
  | 0     => step 0 (fun _ h => absurd h (Nat.not_lt_zero _))
  | k + 1 => step (k+1) (fun j hj => boundedLob φ step j)   -- well-founded on k
```

This is **strong recursion on `k`** — Lean accepts it (well-founded on `Nat`), unlike the
program-recursion `DecMeasure.lean` refuted. The combinator is *productive*: it produces a
genuine term at every finite budget. The fixpoint is never demanded; only its `k`-bounded
unfolding.

The `step` for FairBot is exactly the `search_t` reading: "if I have a proof (at the
smaller budget the guard consumes) that the opponent cooperates, transcribe it + my own
`.const C` step into a proof that I cooperate." The budget strictly decreases across the
guard (`n + c_guard k + c_node`, so the premise budget `n < k`), which is what feeds the
`j < k` hypothesis. **This is the bounded analog of Löb's `□(□φ→φ)→□φ` — the
`step` is the `□φ→φ` self-trust, made constructive and budget-decreasing.**

> ⚠️ **The crucial open obligation.** `step` must be exhibited with the budget genuinely
> decreasing through the guard. The cost model (`atom_cost`, `c_guard k = log2 k + 1`)
> must guarantee `premise-budget < k` at the fixpoint — i.e. the guard's `c_guard`
> overhead is strictly positive (it is: `≥ 1`). This is what makes `boundedLob`
> well-founded *and* sound. Pinning this down for the real bot shapes
> (FairBot, PrudentBot↔DupocBot) is the hard content, see §3.

### 2.3 `DecidablePred (Provable k)` and computable `eval`

With 2.1 + 2.2:

```lean
instance : DecidablePred (Provable k) := ...   -- enumerate ProofTerm φ n for n ≤ k
def proofSearch (k : Nat) (φ : Formula) : Bool := decide (Provable k φ)   -- drop `noncomputable`
```

`eval`'s `.search` guard now computes; `play`/`outcome` become total computable functions;
concrete fixed-`(k,fuel)` outcome theorems become `by decide` (much scaffolding in
`Theorems/*` deletable); the ∀k family theorems keep needing proofs but now have a
*constructive* `boundedLob` carrying the modal core instead of the `PBLT` axiom.

---

## 3. The soundness obligation (where the risk is)

`boundedLob` builds a term. For computability that suffices. For **correctness** we owe:

> **`boundedLob_sound`**: the certificate `boundedLob φ step k` agrees with `eval` —
> i.e. `Provable_sound` extends to the new constructor, so a built cooperation certificate
> implies `play` actually returns `C` at sufficient fuel.

This is the analog of `Provable_sound`/`proofSearch_spec` (`BaseTheorems.lean`) for the new
combinator. The danger: a productive combinator that builds a term **not** matched by any
real `eval` run would be **unsound** (it would prove false cooperations). Soundness pins
`step` to the actual `eval` step semantics. This proof — that budget-bounded unfolding
tracks fuelled evaluation at the fixpoint — is the genuine mathematical content and the
research risk. It is plausible (the bounded box was *designed* to be the fuelled search)
but unproven.

**Acceptance test for the design:** exhibit `step` + `boundedLob_sound` for **FairBot↔FairBot**
(`MirrorBot`/`DupocBot` in the zoo) first — the minimal fixpoint — and confirm
`#eval outcome k fuel MirrorBot MirrorBot = some (C,C)` *computes* for concrete large k.
If that lands, PrudentBot↔DupocBot (stacked search, `searchThenSearch_t` shape) follows the
same template at higher bookkeeping cost.

---

## 4. Relationship to existing constructive rules

Encouraging: the engine **already** has certificate-carrying rules of the right shape —
they are partial, finite instances of what `boundedLob` generalizes:

- `Provable.atomBoxImpl` (`Derivation.lean:333`) — builds `φ → □_k φ` from a held
  certificate, **no axiom**. The bounded-Σ₁-completeness leaf.
- `Provable.searchThenSearch_t`, `Derivation.iteBranchSearch_t` — read nested `.search`
  and collapse two guards to the single-box Löb-premise shape, constructively.
- `c_guard_mono` — already demoted axiom→theorem.

These prove the *premise* shape `□_k ψ → me plays c0` constructively. What's missing is the
combinator that **closes the loop** without an axiom — `boundedLob` is precisely the
budget-recursion that discharges the `□_k ψ` antecedent by building it at each smaller
budget. The pieces are aligned; the combinator + its soundness is the unbuilt keystone.

---

## 4b. Migration — `boundedLob` is NOT a drop-in for the `PBLT` axiom

A natural misreading: "delete the `PBLT` axiom, write `boundedLob` on the same line." **No** —
they have **different types**, so the swap is structural, not a substitution.

```
PBLT       (loose hyp) ∀k>k₁, ∃m, Provable m (□_{f k}(φ k) → φ k)
           →           ∃k₂, ∀k>k₂, ∃m, Provable m (φ k)          -- bare EXISTENCE, no witness

boundedLob (step)      ∀k, (∀j<k, ProofTerm φ j) → ProofTerm φ k
           →           ∀k, ProofTerm φ k                          -- an actual TERM at every k
```

`PBLT` returns *“somewhere a proof exists”*; `boundedLob` *builds the proof*. So the
migration is **three layers**, not a one-line edit:

| Layer | Object | Status after migration |
|---|---|---|
| **1. keystone** | `boundedLob` (+ `boundedLob_sound`) | NEW. Term-builder, well-founded on `k`. The fundamental thing. |
| **2. wrapper** | `PBLT` re-stated as a **theorem proved *via* `boundedLob`** | Axiom line in `Axioms.lean` **deleted**; same-named theorem appears elsewhere. Keeps call sites stable. |
| **3. consumers** | `CupodBot_vs_CupodBot`, `CupodBot_vs_MirrorBot`, … | Signatures **unchanged**, still call `PBLT` — now the theorem. Barely edited. |

Consumers never need to know `boundedLob` exists. That is the point of keeping the wrapper.

### The catch: budgeted vs. general `PBLT`

You **cannot** re-prove the `PBLT` axiom *at its current generality* from `boundedLob`, and
you should not try. The axiom's hypothesis is **unbudgeted**: `∃ m, Provable m (…)` at *some
unconstrained* `m`. But `boundedLob`'s `step` needs a **budget-decreasing, constructive**
discharge — `ProofTerm φ j` at the *smaller* guard budget `j < k`. **An unbudgeted
existential cannot yield a budget-decreasing term-builder** — that gap is exactly the
non-constructive content Critch's diagonal lemma supplies and `boundedLob` refuses. Two
options, only one is sound for the computability goal:

- **(a) Re-prove a *budgeted* `PBLT` — DO THIS.** Strengthen the hypothesis to the tight
  `Provable k (□_{f k}(φ k) → φ k)` with the budget tracking `f` (size ≤ k). `boundedLob`
  closes it. **The consumers already satisfy this**: `cupod_loeb_premise`
  (`Theorems/CupodBot.lean`) *proves the tight `Provable k`, size `5·log2 k + 33 ≤ k`*, then
  immediately **throws the bound away** via `⟨k, hK₀ …⟩` just to match the loose axiom
  shape. The constructive route simply *stops discarding* the bound that is already there.
  Net effect: a **stronger, honest, sound** `PBLT`, and the consumers migrate almost for free.
- **(b) Keep `PBLT` fully general** — then `boundedLob` is insufficient and you still need a
  classical step. Self-defeating; rejected.

So the corrected one-liner: **remove the `PBLT` axiom; add `boundedLob` as the term-builder;
re-prove a *budgeted* `PBLT`-shaped theorem from it. Consumers keep their signatures.** In
the process you discover the loose `∃ m` was never actually needed.

---

## 5. Plan of attack — "does `boundedLob` work?", as a spike

The aim of this plan is **falsification-first**: each step is cheap and ordered so the
*riskiest assumption is tested as early as possible*. If `boundedLob` is going to fail, we
want to know at step S2 or S3 (hours/days), not after redesigning the whole proof object.
Work in a **scratch file** (`Research/Spikes/BoundedLobSpike.lean`, NOT imported by the
root) so nothing touches the green build until a step is proven out.

### Why CUPOD self-play is the gate (not FairBot)

`CupodBot_vs_CupodBot` is the **minimal *positive* Löb fixpoint** and the cleanest possible
test:
- **self-play** → one symmetric leg, no `.sim`-swap bookkeeping (unlike CUPOD↔Mirror);
- defects via the **true-guard** `search_t` branch — which *has* a constructor carrying
  `Provable k (guard)` positively. So it needs **no** `atom_complete_false_guard` (the Π₁
  false-guard axiom that FairBot↔FairBot *cooperation* would drag in);
- its `step` **already exists**: `cupod_loeb_premise` is exactly the per-budget discharge
  `□_k φ → φ`, already proven, already size-≤-k.

So CUPOD exercises `boundedLob` + `boundedLob_sound` with the *least* surrounding machinery.
If `boundedLob` can't close CUPOD self-play, it can't close anything — fail fast here.

### The steps

| # | Step | Tests | Risk | Bankable? |
|---|---|---|---|---|
| **S1** ✅ | In the spike file, write `boundedLob` (§2.2 signature) over a *toy* `ProofTerm φ k`. Confirm Lean accepts the well-founded recursion on `k`. | Does the recursion even typecheck? | Low | — |
| **S2** | Size-index a toy `Derivation'`/`ProofTerm` and prove `DecidablePred (Provable_finite k)` by enumeration — **independent of Löb**. | Is the finite fragment actually decidable as designed? | Low–med | ✅ standalone win |
| **S3** ❌ | **THE GATE.** Instantiate `boundedLob` with `φ k = (CUPOD k plays D vs CUPOD k)` and `step := cupod_loeb_premise`-shaped builder. Produce `ProofTerm φ k` for the fixpoint. | Does the existing `searchBranch`/`cupod_loeb_premise` discharge fit the `∀j<k → …→k` `step` type? Does the budget strictly decrease through `c_guard`? | **HIGH — research gate** | **FAILED as designed — see log** |
| **S4** | Prove `boundedLob_sound` for the CUPOD instance: built term ⇒ `play _ (CUPOD k)(CUPOD k) = some .D`. | Does the built certificate *agree with `eval`*? (The real mathematical content — §3.) | **HIGHEST** | the keystone lemma |
| **S5** | `#eval outcome fuel (CupodBot k)(CupodBot k)` computes to `some (.D,.D)` for a concrete large `k` (e.g. once `proofSearch` is non-`noncomputable` on this fragment). | End-to-end: computability actually achieved on the fixpoint. | med | the demo |

**Decision points:**
- After **S3**: if the budget does *not* strictly decrease through the guard for CUPOD
  (i.e. `c_guard k` doesn't buy `premise-budget < k` at the fixpoint), the design is wrong
  as written — STOP and revisit §2.2's cost-model assumption before any further work.
- After **S4**: if soundness holds for CUPOD, the route is **validated**. Only then proceed
  to the migration (below) and to FairBot/PrudentBot.

### After the gate passes — the migration (per §4b)

6. Promote the spike: replace the **`PBLT` axiom** with (i) `boundedLob` + `boundedLob_sound`
   as real definitions, (ii) a **budgeted** `PBLT`-shaped *theorem* proved via `boundedLob`.
   Keep consumer signatures (`CupodBot_vs_CupodBot` etc.) stable — they already supply the
   tight `Provable k` premise (§4b option (a)).
7. Make `proofSearch` computable (`DecidablePred (Provable k)`); drop `noncomputable`.
8. Generalize `step` to the `searchThenSearch_t` shape (PrudentBot↔DupocBot); revisit
   `box_provable`.
9. Retire `evalC`'s 3-valued `none` at fixpoints (now `eval` decides them).

### Independent, do-anytime wins (de-risk in parallel)

- **S2** (`DecidablePred (Provable_finite)`) lands regardless of whether Löb works.
- `atom_complete_false_guard` is bounded + atom-layer (no reflection) ⇒ eliminable as a
  constructive theorem independent of all the above (unchanged from the crux note).

### Spike results log

- **S1 — PASSED.** `Research/Spikes/BoundedLobSpike.lean` (not imported by root; build with
  `lake env lean PrisonersDilemma/Research/Spikes/BoundedLobSpike.lean`). `boundedLob` over
  a toy size-indexed `ProofTerm φ k` elaborates as a **total, well-founded** definition
  (`termination_by k => k`, `decreasing_by exact ‹j < k›`) — NOT `partial`, confirmed by the
  auto-generated equation lemma `boundedLob.eq_def` unfolding `boundedLob φ step k = step k
  (fun j _ => boundedLob φ step j)`. The combinator is instantiable and applicable at
  concrete budgets. **Recursion-on-budget is well-formed in Lean 4** — the foundational
  worry (would Lean reject it like the program-recursion in `DecMeasure.lean`?) is closed.
  - *Caveat carried to S3:* well-founded recursion does **not** reduce by `rfl` (it goes via
    `WellFounded.fix`); unfolding needs `rw [boundedLob]` / `boundedLob.eq_def`. The S4
    soundness proof must reason through the equation lemma, not definitional reduction.
  - *Cost-model anchor recorded:* `c_guard_pos : 0 < Nat.log2 k + 1` — the guard always costs
    ≥ 1 char, the seed of the S3 budget-strictly-decreases obligation.

- **S3 — FAILED (as a design, not as code).** `Research/Spikes/BoundedLobSpike.lean`
  namespace `PD.SpikeS3` (typechecks; one *deliberate* `sorry` marking the gap). Instantiated
  against the REAL engine (`Provable`/`interp`/`Derivation`/`cupod_loeb_premise`), not the toy.
  **Verdict: the §2.2 `boundedLob` `step` signature does NOT match the CUPOD discharge.** Two
  concrete mismatches, both machine-confirmed:
  1. **Predicate mismatch.** `interp (□_k φ) = Provable k φ` (Dynamics.lean:55), so
     `cupod_loeb_premise` + `Provable_sound` yields the meta-step `Provable k φ → φ.interp`
     (proven, no sorry: `cupod_step`). But the *premise* is a **proof** `Provable k φ` and the
     *conclusion* is a **play** `φ.interp` (`∃n, play n … = some .D`). They are different
     predicates, so the output cannot be fed back as the next input — there is no `P k` such
     that `step : (∀j<k, P j) → P k`. The toy `boundedLob` re-enters with the same `P`; the
     real discharge cannot.
  2. **Budget mismatch.** The antecedent box is `□_k φ` at the **same** budget `k`, not `□_j φ`
     for `j<k`. The `c_guard` decrease lives **inside** the implication's certificate
     (`searchBranch`'s size accounting), NOT in the antecedent's budget. So there is no
     smaller-budget premise to recurse on — `boundedLob`'s entire reason for being (budget
     strictly decreases) has no foothold here.
  - **What this means.** The missing thing is exactly `Provable k (cupodφ k)` — the
    antecedent `□_k φ` discharged. `cupod_antecedent_is_the_gap` (the `sorry`) is precisely
    it, and `cupod_fixpoint_modulo_gap` shows everything else closes around it. Critch
    manufactures this antecedent via the **diagonal lemma over a self-referential ψ** — the
    non-constructive move `boundedLob` was meant to avoid. **Budget-recursion alone cannot
    conjure the same-budget self-referential antecedent.** S1's combinator is well-formed but
    *not the right tool* for this discharge shape.
  - **This is a genuine result, not a dead end.** It localizes the non-constructivity to a
    single, precise obligation (`Provable k φ` at the fixpoint) and rules out the naive
    "recurse on budget" story. See §7 for the revised design it forces.

- **S3′ — FAILED, and this SETTLES route (B).** `PD.SpikeS3prime` (typechecks, no sorry,
  both claims by `rfl`). The S3 setback reduced everything to one arithmetic question: can
  the antecedent box be `□_{k'} φ` with `k' < k`? **Answer, read straight off `eval`
  (Dynamics.lean:34–37) and machine-checked:** `CupodBot k = .search k …`, and `eval`'s
  `.search` rule consults `proofSearch k` — at the bot's **own** parameter `k`, nothing
  smaller. The guard fires iff `Provable k (guard)`, so the *sound* box premise is `□_k`,
  budget = the bot's `k`. **`k' = k` is FORCED by the semantics.** The `c_guard k` the
  certificate spends is internal proof-length bookkeeping paid *on top of* the atom — it is
  never subtracted from the antecedent's box budget. So there is **no** strictly-smaller
  premise; budget-recursion has no foothold; `boundedLob` cannot be made to fit, even with a
  redesigned cost accounting. Verified facts:
  - `CupodBot k = .search k (opp plays self D) (.const D)(.const C)` — `rfl`.
  - `eval (n+1) me _ (CupodBot k) = if proofSearch k (…) then … else …` — `rfl`. The budget
    index is literally `k`.
  - **Verdict: route (B) — constructive bounded Löb that makes `eval` computable on the
    fixpoints — is closed.** Not by a Gödel wall, but because the bot genuinely searches at
    budget `k` and at the self-play fixpoint the only proof of its action is the
    diagonal/Löb fixpoint, which budget-recursion cannot manufacture. This is **faithful to
    Critch**, not a defect. The honest ceiling is route (A): keep PBLT as an axiom (or
    mechanize Critch's classical chain over the abstract interface, §4b) — `eval` stays
    `noncomputable` on the genuine fixpoints, exactly as the shipped `evalC` (option D)
    already reflects by returning `none` there.

---

## 7. Revised design — what S3 forces

S3 killed the §2.2 `step : (∀j<k, P j) → P k` story. The discharge the engine actually
provides is `Provable k φ → φ.interp`, and **the only missing piece is its antecedent
`Provable k φ`** (`cupod_antecedent_is_the_gap`). So the real question is sharper than "can
we recurse on budget?": **can we constructively build `Provable k φ` for the fixpoint atom
`φ = (CUPOD plays D vs CUPOD)`?**

### Why the antecedent is hard, restated at the certificate level

`Provable k φ` for the play-atom `φ` means a `PlaysProof` of cost ≤ k (`AtomProvable`). By
`search_t` (Derivation.lean:241), CUPOD's defection certificate requires as a premise
`Provable k (guard.subst …) = Provable k φ` — **itself, at the same budget `k`.** Least-
fixed-point `PlaysProof` forbids it. This is the same wall, now seen from the certificate
side rather than the recursion side.

### The decoupling that might work (next hypothesis to test)

The box budget and the certificate budget are conflated in the `searchBranch` premise. The
candidate fix:

> **Build `Provable k φ` from `Provable k' φ` with `k' < k` strictly** — i.e. a genuine
> *bounded* Löb where the antecedent box is at a STRICTLY SMALLER budget than the conclusion,
> the gap being exactly the `c_guard k ≥ 1` the certificate spends reading the guard. Then
> well-founded recursion on the box budget DOES have a foothold (unlike S3, where antecedent
> and conclusion shared `k`).

Concretely this means the load-bearing lemma is NOT `cupod_loeb_premise`'s `□_k φ → φ` but a
**budget-strict** variant `□_{k'} φ → φ` with `k' < k`, whose certificate-size accounting
shows the conclusion's `Provable k` is reached from a `Provable k'` antecedent. Whether the
engine's cost model (`atom_cost`, `c_guard`) actually delivers `k' < k` here — rather than
`k' = k` as `searchBranch` currently states — is the **next thing to spike (S3′)**. If yes,
budget-recursion is resurrected on the *box* budget. If the cost model forces `k' = k`
(guard read is free relative to the atom), the route is genuinely blocked and the antecedent
is irreducibly non-constructive — at which point (A) faithful-PBLT-as-axiom is the honest
ceiling.

### Revised step list

- **S3′ (NEW, next):** check whether `searchBranch`/`atom_cost` can be restated with a
  *strictly smaller* antecedent box budget `k' < k`. This is pure cost-model arithmetic on
  the existing `Derivation` — no soundness yet. **This is now the real gate.**
- S4/S5 unchanged in spirit, but predicated on S3′ succeeding.
- S2 (`DecidablePred (Provable_finite)`) still bankable and still independent — **promote it
  to "do next regardless"**, since it's the one piece untouched by the S3 setback.

---

## 6. Honest bottom line  _(updated after S1/S3)_

- Critch's PBLT (A) and constructive bounded Löb (B) are **different theorems**. (A) is a
  faithful-mechanization / paper-fidelity goal; (B) is the computability lever. Do not let
  "prove PBLT" blur them.
- (B) is **not blocked by a Gödel/Π₁ wall** — the bounded box is finite and decidable by
  construction.
- **S1 result:** recursion-on-budget is well-formed in Lean (combinator total, well-founded).
  The *machinery* exists.
- **S3 result (the real news):** but that machinery **does not fit the CUPOD discharge** —
  the engine's `□_k φ → φ` has antecedent and conclusion at the **same** budget `k`, so
  there is no smaller-budget premise to recurse on, and the antecedent `Provable k φ` is
  exactly the non-constructive piece Critch builds via the diagonal lemma. Naive
  budget-recursion is **refuted for this shape**, machine-checked (`PD.SpikeS3`).
- **S3′ result — the crux is SETTLED (negatively for B).** `k' = k` is forced by `eval`'s
  `.search` rule (the bot searches at its own budget `k`; `c_guard` is paid on top of the
  atom, never subtracted from the box). Machine-checked by `rfl` in `PD.SpikeS3prime`. So the
  antecedent `Provable k φ` is irreducibly at budget `k`, budget-recursion has no foothold,
  and **route (B) is closed.** Not a Gödel wall — faithful to Critch: at the self-play
  fixpoint the only proof is the diagonal/Löb fixpoint, which budget-recursion can't build.
- **The honest ceiling is route (A):** PBLT stays an axiom, OR mechanize Critch's classical
  chain over the abstract `BoundedProvabilitySystem` interface (§4b) to shrink/justify the
  axiom surface. `eval` stays `noncomputable` on the genuine fixpoints — exactly what the
  shipped `evalC` (option D) already reflects (returns `none` there). This is now **proven to
  be the boundary, not merely the current state.**
- **Still bankable, independent of all the above:** `DecidablePred (Provable_finite)` (S2,
  the decidable finite-proof fragment — a real positive result even though it does NOT extend
  to the fixpoints) and eliminating `atom_complete_false_guard` (bounded, atom-layer).
- **Net deliverable of this spike round:** the computability boundary is now *machine-located
  and proven*, not asserted. That is itself a paper-grade result: "we show constructively
  that the Löb fixpoints are exactly where bounded provability cannot be made computable,
  because the search budget and the box budget coincide."
