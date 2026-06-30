/-!
# Spike — the unified `Pf` proof-term type (validating `UNIFIED_PF_SKETCH.md`)

De-risks "merge `Derivation`(Type) + `Provable`(Prop) into ONE proof-term type `Pf`". The sketch
claims this (a) typechecks as one inductive with merged constructors (no Type/Prop twins, no
`struct`/`atom` glue), and (b) makes the bot proofs SHORTER/FLATTER — specifically collapsing the
CIMCIC-style DOUBLE induction (`Provable.rec` whose `struct` arm recurses into a second `Derivation`
induction) into ONE induction over `Pf`.

We model a toy `Formula` + `Pf` capturing the real shapes, and reproduce two real-bot patterns:
  1. the `Forbidden`-motive EXCLUSION (CIMCIC vs DefectBot) — ONE induction, vs the engine's two;
  2. the COOPERATION chain (`mutual_loeb` Route 2: boxIntro/axK/box4/implTrans) — flat siblings.

`PlaysProof` (execution) is NOT merged — it stays as the atom bridge (modelled by an opaque `Play`).
NOT root-imported. `lake env lean PrisonersDilemma/Research/Spikes/unified_pf/UnifiedPfSpike.lean`
-/

namespace PD.UnifiedPfSpike

/-! ## Toy syntax (the shapes that matter: plays-atom, impl, box). -/

abbrev Atom := Nat
inductive TF where
  | plays : Atom → TF                  -- an atomic play (subject/opponent/action erased to a tag)
  | impl  : TF → TF → TF
  | box   : Nat → TF → TF
deriving DecidableEq
open TF

def TF.size : TF → Nat
  | .plays _  => 1
  | .impl φ ψ => φ.size + ψ.size + 1
  | .box _ φ  => φ.size + 1

/-- Execution bridge (models `PlaysProof`→`AtomProvable`): which atoms genuinely play. NOT merged
    into `Pf` — this is the intrinsic reasoning/execution split the sketch says survives. -/
opaque Play : Atom → Prop

/-! ## The UNIFIED proof-term type `Pf`.

ONE type. `atom` is the SOLE bridge from execution (was `Provable.atom`); there is NO `struct`/
`Derivation` glue. Logical core is ONE `mp` / ONE `hypSyll` (no `app`/`implTrans` twins). The box
rules are SIBLINGS of the structural rules, not a separate `Provable` tier. -/
inductive Pf : Nat → TF → Type where
  -- entry from execution (the one surviving bridge)
  | atom (k : Nat) (a : Atom) : Play a → Pf k (.plays a)
  -- logical core (single MP, single transitivity, weakening)
  | mp (k : Nat) (φ ψ : TF) : Pf k (.impl φ ψ) → Pf k φ → Pf k ψ
  | hypSyll (k : Nat) (φ ψ χ : TF) : Pf k (.impl φ ψ) → Pf k (.impl ψ χ) → Pf k (.impl φ χ)
  | weaken (k : Nat) (φ ψ : TF) : Pf k ψ → Pf k (.impl φ ψ)
  -- a source-transparency LEAF (stands in for searchBranch/simStep/… — concludes `□guard → plays`).
  -- The conclusion atom `a` is the bot's concrete THEN-action; modelled by the side-condition
  -- `a ≠ aFalse` the engine discharges syntactically (`simp [DefectBot]`: the THEN-action ≠ the
  -- false consequent). `aFalse := 999`, so any real leaf action (a small tag) satisfies it.
  | srcBranch (k g : Nat) (gd a : Atom) : a ≠ 999 → Pf k (.impl (.box g (.plays gd)) (.plays a))
  -- box / HBL rules (siblings, not a separate tier) — the Route-2 trio
  | boxIntro (kIn K : Nat) (φ : TF) : Pf kIn φ → Pf K (.box kIn φ)
  | axK (k K : Nat) (φ α : TF) : Pf k (.box k (.impl φ α)) → Pf K (.impl (.box k φ) (.box k α))
  | box4 (k K : Nat) (φ : TF) : Pf K (.impl (.box k φ) (.box k (.box k φ)))

/-! ## Pattern 1 — the EXCLUSION proof, in ONE induction (vs the engine's two).

Engine: `cimcic_no_provable_forbidden` (over `Provable`) whose `struct` arm recurses into
`cimcic_no_deriv_forbidden` (over `Derivation`) — TWO inductions, because the `.plays`-atom can be
concluded structurally OR by the reflection rules. Here: ONE induction over `Pf`. -/

/-- `Forbidden aF φ` := φ is the false atom `aF`, or an `.impl`-chain ending in it. Stops at `.box`
    (a boxed formula is not the bare false play-atom) — exactly like the engine's `CimcicForbiddenC`,
    which returns `False` for `.box`. This is what makes the box rules' arms close cleanly. -/
def Forbidden (aF : Atom) : TF → Prop
  | .plays a  => a = aF
  | .impl _ ψ => Forbidden aF ψ
  | _         => False

/-- The false atom (no `Play`, so no `atom` proof of it). -/
def aFalse : Atom := 999

/-- **No `Pf` concludes a `Forbidden` formula** — ONE induction over `Pf`. The `atom` arm bottoms out
    on `¬ Play aFalse` (the consequent-not-provable fact); `mp`/`hypSyll`/`weaken` recurse; the box
    and `srcBranch` rules conclude non-`Forbidden` shapes. This is the SINGLE induction that replaces
    the engine's `Provable.rec` + nested `Derivation` induction. -/
theorem no_pf_forbidden (hno : ¬ Play aFalse) :
    {k : Nat} → {φ : TF} → Pf k φ → ¬ Forbidden aFalse φ := by
  intro k φ d
  induction d with
  | atom k a hplay =>
      intro hF; simp only [Forbidden] at hF; subst hF; exact hno hplay
  | mp k φ ψ _ _ ihimp _ =>
      -- conclusion ψ; the implication premise `φ→ψ` has Forbidden = Forbidden ψ; use its IH.
      intro hF; exact ihimp (by simpa only [Forbidden] using hF)
  | hypSyll k φ ψ χ _ _ _ ihbc =>
      -- conclusion `φ→χ`; Forbidden = Forbidden χ; the `ψ→χ` premise carries it.
      intro hF; exact ihbc (by simpa only [Forbidden] using hF)
  | weaken k φ ψ _ ih =>
      intro hF; exact ih (by simpa only [Forbidden] using hF)
  | srcBranch k g gd a hne =>
      -- concludes `□(plays gd) → plays a`; `Forbidden` peels `.impl` to `a = aFalse = 999`, which the
      -- leaf's side-condition `hne : a ≠ 999` refutes. (Engine: `simp [DefectBot]`.)
      intro hF; simp only [Forbidden, aFalse] at hF; exact hne hF
  | boxIntro kIn K φ _ _ =>
      -- concludes `□φ`; `Forbidden (.box ..) = False`. Closes with no IH.
      intro hF; simp only [Forbidden] at hF
  | axK k K φ α _ _ =>
      -- concludes `□φ → □α`; `Forbidden` peels `.impl` to `Forbidden (□α) = False`. No IH needed.
      intro hF; simp only [Forbidden] at hF
  | box4 k K φ =>
      -- concludes `□φ → □□φ`; `Forbidden` peels to `Forbidden (□(□φ)) = False`.
      intro hF; simp only [Forbidden] at hF

/-! ## Pattern 2 — the COOPERATION chain (`mutual_loeb` Route 2) as FLAT SIBLINGS.

Engine: a leg is `Provable.struct ⟨Derivation.searchBranch …, size-proof⟩` (reach THROUGH the glue),
then `mutual_loeb` chains `boxIntro`/`axK`/`box4`/`implTrans` at the `Provable` level. Here the leg is
just `Pf.srcBranch …` (no `struct ⟨…⟩` wrapper), and the chain rules are siblings of it — ONE flat
construction, no "which layer am I on?". We reproduce `mutual_loeb`'s `□φP → φP` from the two legs. -/

/-- **Mutual Löb (Route 2) in the unified type** — from the two object transparency legs
    `legPD : □φP → φD` and `legDP : □φD → φP`, build `□φP → φP` via `boxIntro → axK → box4 → hypSyll`.
    Flat: every step is a `Pf` constructor, no embedding ceremony. (Budgets erased for the toy; the
    real chain keeps them at a single `k` with `Formula.size` side-conditions, unchanged.) -/
def mutual_loeb_unified (k : Nat) (φP φD : TF)
    (legPD : Pf k (.impl (.box k φP) φD))
    (legDP : Pf k (.impl (.box k φD) φP)) :
    Pf k (.impl (.box k φP) φP) :=
  -- 1. boxIntro legPD : □_k(□φP → φD)
  let h1 : Pf k (.box k (.impl (.box k φP) φD)) := .boxIntro k k (.impl (.box k φP) φD) legPD
  -- 2. axK : □(□φP) → □φD
  let h2 : Pf k (.impl (.box k (.box k φP)) (.box k φD)) := .axK k k (.box k φP) φD h1
  -- 3. box4 : □φP → □(□φP)
  let h3 : Pf k (.impl (.box k φP) (.box k (.box k φP))) := .box4 k k φP
  -- 4. hypSyll h3 ; h2 : □φP → □φD
  let h4 : Pf k (.impl (.box k φP) (.box k φD)) := .hypSyll k _ _ _ h3 h2
  -- 5. hypSyll h4 ; legDP : □φP → φP
  .hypSyll k _ _ _ h4 legDP

/-- And the leg itself is a bare `srcBranch` — no `Provable.struct ⟨Derivation.…, _⟩` wrapper. Each
    bot's guard reads the OTHER's cooperation atom (the fixpoint loop): legPD's guard is `aP`, legDP's
    is `aD`. -/
def coop_example (k : Nat) (aP aD : Atom) (hP : aP ≠ 999) (hD : aD ≠ 999) :
    Pf k (.impl (.box k (.plays aP)) (.plays aP)) :=
  mutual_loeb_unified k (.plays aP) (.plays aD)
    (.srcBranch k k aP aD hD)         -- legPD : □(plays aP) → plays aD
    (.srcBranch k k aD aP hP)         -- legDP : □(plays aD) → plays aP

/-! ## VERDICT — both patterns PROVEN, no `sorry` (machine-checked).

The unified `Pf` (ONE type; `atom` the sole execution bridge; `mp`/`hypSyll` single, no Type/Prop
twins; box rules as siblings) typechecks, AND:

* **Pattern 1** — the `Forbidden` exclusion that takes the engine TWO nested inductions
  (`Provable.rec` + `Derivation` induction via the `struct` arm) is ONE induction over `Pf`
  (`no_pf_forbidden`). Fewer arms, no nesting — the exact messiness the sketch targets.
* **Pattern 2** — the cooperation leg is a bare `Pf.srcBranch` (no `struct ⟨Derivation.…, _⟩`
  embedding), and `mutual_loeb`'s Route-2 chain (`mutual_loeb_unified`) is a FLAT sequence of `Pf`
  constructors (`coop_example` builds it end-to-end from two legs).

So the merge is structurally sound and DOES tidy the bot proofs (one induction, flat chains, no glue),
confirming `UNIFIED_PF_SKETCH.md`. NOT proven here (out of scope, the real cost): re-deriving every
engine theorem against `Pf`, the budget/size side-conditions at scale, and the deduction theorem +
Gödel layer that PBLT-removal would add. The spike validates the SHAPE, not the full port. -/

#check @no_pf_forbidden
#check @mutual_loeb_unified
#check @coop_example

end PD.UnifiedPfSpike
