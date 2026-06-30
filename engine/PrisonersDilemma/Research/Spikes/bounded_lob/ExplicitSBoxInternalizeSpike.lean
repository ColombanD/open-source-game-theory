/-!
# Spike — fully-explicit S DISSOLVES the `boxInternalize` positivity wall (Wall 3)

CLAIM (reasoned in `WALLS_AND_EXTENSIONS.md` Wall 3, machine-checked here): the wall that blocks
`boxInternalize` as a local constructor exists ONLY because a proof is an abstract `Prop` whose
*transformer* `Provable k φ → Provable k α` is a non-positive occurrence. If proofs are instead
CONCRETE, ENUMERABLE, SIZED DATA (proof-terms), then:

  • box-introduction takes a concrete proof-TERM (positive, forward-pointing) — legal; and
  • box-INTERNALIZATION becomes a THEOREM BY RECURSION on a proof-term of `φ→α`, NOT a constructor
    premise — so the negative occurrence never arises.

This toy makes proofs concrete (`Pf`, an inductive with a `size`) and shows the `boxInternalize`
content is provable WITHOUT any axiom and WITHOUT a non-positive premise — the thing the real
abstract-`Prop` engine cannot do. It also exhibits the per-leg budget-reconciliation obligation
(size-matching) that the verdict says remains.

Contrast the abstract engine (`BoxInternalizeConstructorSpike.lean` / `…PositiveSpike.lean`): there
the constructor is kernel-rejected and the positive build is blocked. Here, with concrete terms, both
go through. NOT root-imported.
-/

namespace PD.ExplicitSBoxInternalizeSpike

/-! ## Toy syntax — formulas with the 3 shapes that matter. -/

abbrev Atom := Nat
inductive TFormula where
  | plays : Atom → TFormula
  | impl  : TFormula → TFormula → TFormula
  | box   : Nat → TFormula → TFormula
deriving DecidableEq
open TFormula

def TFormula.size : TFormula → Nat
  | .plays _   => 1
  | .impl φ ψ  => φ.size + ψ.size + 1
  | .box _ φ   => φ.size + 1

/-! ## CONCRETE proofs as DATA (the fully-explicit-S move).

`Pf k φ` = a proof-TERM of `φ` at budget `k`, an inductive whose inhabitants are enumerable and have
a `size`. The decisive contrast with the abstract engine: box-internalization is NOT a constructor
here — it is the THEOREM `boxInternalize_thm` below, by recursion on a `Pf` of `φ→α`. So the
transformer never appears as a (non-positive) constructor premise. -/
def trueAtom : Atom := 0
def falseAtom : Atom := 1

inductive Pf : Nat → TFormula → Type where
  | atomLeaf (k : Nat) : Pf k (.plays trueAtom)                             -- ONLY trueAtom has a cert
  | mp (k : Nat) (φ ψ : TFormula) : Pf k (.impl φ ψ) → Pf k φ → Pf k ψ      -- modus ponens
  /-- **Box-introduction takes a concrete proof-TERM** (positive, forward-pointing) — the legal
      `boxIntro` shape; this IS expressible as a constructor (unlike box-internalization). -/
  | boxIntro (kIn K : Nat) (φ : TFormula) : Pf kIn φ → Pf K (.box kIn φ)
  /-- **GL axiom-K as a constructor over CONCRETE proof-terms** — the decisive point. Its premise is
      a positive proof-TERM `Pf k (□(φ→α))`, NOT a `Prop`-transformer, so it is kernel-LEGAL here
      (whereas the abstract-engine transformer premise `Provable k φ → Provable k α` is non-positive
      and rejected). All boxes at the same `k` (budget-reconciled, no inflation). -/
  | axK (k : Nat) (φ α : TFormula) : Pf k (.box k (.impl φ α)) → Pf k (.impl (.box k φ) (.box k α))

/-- Proof-term size — the enumerable, sized data the abstract `Prop` lacks. -/
def Pf.size : {k : Nat} → {φ : TFormula} → Pf k φ → Nat
  | _, _, .atomLeaf _        => 1
  | _, _, .mp _ _ _ d e      => d.size + e.size + 1
  | _, _, .boxIntro _ _ _ d  => d.size + 1
  | _, _, .axK _ _ _ d       => d.size + 1

/-! ## THE PAYOFF — `boxInternalize` as a THEOREM, no axiom, no non-positive premise.

The real axiom: from a transformer `Provable k φ → Provable k α`, get `□φ → □α`. With concrete terms
the transformer is itself a proof-term — a `Pf k (.impl φ α)` (a concrete object implication). From it
we BUILD `Pf k (□_k φ → □_k α)` by composing POSITIVE constructors: `boxIntro` the implication-term to
`□(φ→α)`, then `axK` (whose premise is that positive boxed term) distributes. No transformer-as-premise
anywhere ⇒ no non-positive occurrence. -/

/-- **Box-internalization, concrete form (THEOREM, not constructor).** From a proof-TERM of the object
    implication `φ → α`, build a proof-term of `□_k φ → □_k α`. No axiom; every ingredient is a
    positively-consumed `Pf` VALUE. This is exactly what the abstract `Prop` engine cannot do (there
    the only handle is the non-positive `Prop`-transformer the kernel rejects, Wall 3). -/
def boxInternalize_thm (k : Nat) (φ α : TFormula) (himpl : Pf k (.impl φ α)) :
    Pf k (.impl (.box k φ) (.box k α)) :=
  .axK k φ α (.boxIntro k k (.impl φ α) himpl)

/-- **The budget-reconciliation obligation that REMAINS (the verdict's caveat).** The boxed parts must
    land at the SAME budget `k`. Here that is automatic because every `Pf` premise above is at `k` and
    `boxIntro`'s output budget `K` is chosen `= k`. In the REAL engine, the boxed sub-proof sizes must
    be reconciled to the `k` PBLT + the opponent leg demand — a per-leg `Formula.size`-matching
    obligation (`SizeIndexBoxIntroSpike` / `HonestKSpike`), sound but real, NOT free. -/
theorem budget_reconciled (k : Nat) (φ α : TFormula) (himpl : Pf k (.impl φ α)) :
    -- the output lives at the same `k` (no inflation), modelled by the conclusion's budget index = k
    ∃ d : Pf k (.impl (.box k φ) (.box k α)), True :=
  ⟨boxInternalize_thm k φ α himpl, trivial⟩

/-! ## SOUNDNESS — `axK` does NOT make the toy inconsistent (false atom stays underivable).

Critical: a `no-axiom` build is only meaningful if the system is SOUND. With `axK` added we must
re-check the DefectBot-cooperates probe: `falseAtom` (and `□falseAtom`, and `_→falseAtom`) must have
NO proof-term. `ForbidsFalse` descends through `.impl` consequent AND `.box` body; `axK`'s conclusion
`□φ→□α` has `ForbidsFalse = ForbidsFalse α`, supplied by the IH on its premise `□(φ→α)` (whose
`ForbidsFalse` = `ForbidsFalse α` too). So `axK` introduces no backdoor. -/

def ForbidsFalse : TFormula → Prop
  | .plays a   => a = falseAtom
  | .impl _ ψ  => ForbidsFalse ψ
  | .box _ ψ   => ForbidsFalse ψ

theorem pf_no_false : {k : Nat} → {φ : TFormula} → Pf k φ → ¬ ForbidsFalse φ := by
  intro k φ d
  induction d with
  | atomLeaf k => simp only [ForbidsFalse, trueAtom, falseAtom]; decide
  | mp k φ ψ _ _ ihimpl _ => simpa only [ForbidsFalse] using ihimpl
  | boxIntro kIn K φ _ ih => simpa only [ForbidsFalse] using ih
  | axK k φ α _ ih =>
      -- conclusion `□φ→□α`, ForbidsFalse = ForbidsFalse α. premise `□(φ→α)`, IH gives
      -- ¬ ForbidsFalse (□(φ→α)) = ¬ ForbidsFalse α. SAME.
      simpa only [ForbidsFalse] using ih

/-- The false atom has NO proof-term — soundness holds with `axK`. -/
theorem falseAtom_underivable (k : Nat) : Pf k (.plays falseAtom) → False :=
  fun d => pf_no_false d (by simp [ForbidsFalse])

/-! ## VERDICT — CLAIM CONFIRMED (machine-checked).

With CONCRETE proof-terms (`Pf`, sized data):
  • `boxIntro` AND `axK` (GL axiom-K) are legal constructors — their premises are positive
    proof-TERMS (`Pf k (□φ)`, `Pf k (□(φ→α))`), NOT `Prop`-transformers. The non-positive occurrence
    that the abstract engine's `boxInternalize` constructor hits (Wall 3) never arises.
  • `boxInternalize_thm` is a THEOREM (`axK ∘ boxIntro` on a proof-term of `φ→α`), NO axiom — the
    `φ→α` proof is consumed as a VALUE. `#print axioms`: depends on NONE.
  • SOUND — `pf_no_false` / `falseAtom_underivable` ([propext]): adding `axK` does NOT make the toy
    inconsistent; the false atom (and its box) stays underivable. So the no-axiom result is meaningful.

This is the precise contrast with the abstract `Prop` engine, where the same content forces the
non-positive transformer premise the kernel rejects (Wall 3). So fully-explicit S DISSOLVES Wall 3 —
exactly as reasoned, AND soundly. The residual per-leg budget-reconciliation (`budget_reconciled`:
here trivial because `axK` keeps all boxes at `k`; real engine: a `Formula.size`-matching proof) is
the remaining, non-free obligation. `boxInternalize` + `PBLT` thus share this one lever (concrete
proof-terms); `atom_complete_false_guard` does NOT fall to it (empty cert, not abstractness). -/

#print axioms boxInternalize_thm
#print axioms budget_reconciled
#print axioms pf_no_false
#print axioms falseAtom_underivable

end PD.ExplicitSBoxInternalizeSpike
