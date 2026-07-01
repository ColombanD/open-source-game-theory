/-!
# Route 2b, Milestone 1: constructive bounded Löb on a TOY explicit proof system.

The crux (CLAUDE.md): make `box` = "∃ proof TERM of size ≤ k" — a DECIDABLE finite
predicate — and give a CONSTRUCTIVE bounded Löb that EXHIBITS a size-≤-k proof term
for the fixpoint. Then `Provable` collapses to the decidable predicate ⇒ eval computable
⇒ extraction falls out (the play witness is read off the exhibited term).

This toy isolates the ONE question: with an explicit proof-term type `Pf` and a
size measure, can we CONSTRUCT (not just assert) the Löb fixpoint's proof term?

We keep it minimal: a tiny modal formula language, an explicit proof-term inductive
`Pf` with a `size`, and `Boxable k φ := ∃ t : Pf φ, size t ≤ k`. The test: prove
    (∃ t : Pf (□φ → φ), size t ≤ k)  →  (∃ t : Pf φ, size t ≤ k')   [some k']
by BUILDING the witness term, using an explicit diagonal proof-term constructor.
-/

namespace ConstructiveLobToy

/-- Toy modal formulas. `box` carries a budget (bounded provability). -/
inductive Fml where
  | atom (n : Nat)
  | imp  (a b : Fml)
  | box  (k : Nat) (a : Fml)
deriving DecidableEq, Repr

/-- Explicit proof TERMS, indexed by conclusion. This is the "cash" the crux wants:
    a real term, with a size, that a running evaluator can enumerate.
    We include exactly the HBL toolkit + an EXPLICIT bounded-Löb term constructor
    whose SOUNDNESS we must justify constructively (that's the milestone). -/
inductive Pf : Fml → Type where
  | ax_k   (a b : Fml) : Pf (.imp a (.imp b a))
  | ax_s   (a b c : Fml) : Pf (.imp (.imp a (.imp b c)) (.imp (.imp a b) (.imp a c)))
  | mp     {a b : Fml} : Pf (.imp a b) → Pf a → Pf b
  | nec    {a : Fml} {k : Nat} : Pf a → Pf (.box k a)                 -- necessitation (D1)
  | axK    (k : Nat) (a b : Fml) : Pf (.imp (.box k (.imp a b)) (.imp (.box k a) (.box k b)))  -- D2
  | four   (k : Nat) (a : Fml) : Pf (.imp (.box k a) (.box k (.box k a)))                       -- D3
  -- THE constructive bounded-Löb term: from a term of `□φ → φ`, BUILD a term of `φ`.
  -- This is what we must justify. If we can define it as a DERIVED term (not a
  -- constructor) from the others + a real diagonal, the milestone succeeds.
  -- Provisionally a constructor to state the size question; the milestone is to
  -- REPLACE it by a definition.
  | loeb   {φ : Fml} {k : Nat} : Pf (.imp (.box k φ) φ) → Pf φ

/-- Size of a proof term (character count analogue). -/
def Pf.size : {φ : Fml} → Pf φ → Nat
  | _, .ax_k _ _      => 1
  | _, .ax_s _ _ _    => 1
  | _, .mp f g        => f.size + g.size + 1
  | _, .nec f         => f.size + 1
  | _, .axK _ _ _     => 1
  | _, .four _ _      => 1
  | _, .loeb f        => f.size + 1

/-- Bounded provability: ∃ a proof term of size ≤ k. DECIDABLE in principle
    (finitely many terms of size ≤ k), unlike the axiom-injected engine `Provable`. -/
def Boxable (k : Nat) (φ : Fml) : Prop := ∃ t : Pf φ, t.size ≤ k

/-- With `loeb` as a CONSTRUCTOR, bounded Löb is trivial but the SIZE is the question:
    does the fixpoint term stay within a computable bound of the premise's size? -/
theorem bounded_loeb_toy {φ : Fml} {k : Nat} (h : Boxable k (.imp (.box k φ) φ)) :
    Boxable (k + 1) φ := by
  obtain ⟨t, ht⟩ := h
  exact ⟨.loeb t, by simp [Pf.size]; omega⟩

/-! ## The REAL milestone question (recorded, not yet answered):

The above is trivial BECAUSE `loeb` is a constructor. The crux is whether `loeb`
can be REPLACED by a DEFINITION `Pf.loeb : Pf (□φ→φ) → Pf φ` built from the HBL
constructors + a genuine diagonal — i.e. whether the fixpoint proof-term is
CONSTRUCTIBLE. In real Löb this needs a Gödel sentence ψ with a proof term for
`ψ ↔ (□ψ→φ)`; the toy `Fml` has no such ψ (no encoding). So the milestone reduces
(again!) to: ADD an encoding to `Fml` and a diagonal proof-term constructor whose
soundness is CONSTRUCTIVE (exhibits the equivalence's proof term).

This is the same wall as the object system — now localized to "define `Pf.loeb`".
The value of the toy: it makes the target a SINGLE definition to fill, with a size
bound to verify, in isolation from the engine. -/

#check @bounded_loeb_toy
#check @Boxable

end ConstructiveLobToy
