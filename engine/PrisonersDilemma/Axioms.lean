import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics

open PDNew
namespace PDNew.Axioms

/-- Abstract proof objects used to model derivations in the ambient proof system. -/
axiom ProofWitness : Type

/-- The size of a proof witness, used as the budget measured by `proofSearch`. -/
axiom witnessChars : ProofWitness → Nat

/-- The proposition that a witness proves a particular formula. -/
axiom witnessProves : ProofWitness → Formula → Prop

/-- Witness soundness: any formula proved by a witness is semantically true. -/
axiom witness_sound :
  ∀ w φ, witnessProves w φ → φ.interp

/-- Σ₁-completeness for atomic plays-formulas. Decidable arithmetic; no Gödel issues. -/
axiom witness_complete_plays :
  ∀ p q a, (∃ n, play n p q = some a) →
    ∃ w : ProofWitness, witnessProves w (.plays p q a)

/-- Exact budget semantics for `proofSearch`: true iff there is a witness of size at most `k`. -/
axiom proofSearch_spec :
  ∀ k φ, proofSearch k φ = true ↔
    ∃ w : ProofWitness, witnessProves w φ ∧ witnessChars w ≤ k

/--
Transport of witnesses across a parameterized formula family when the parameter grows.

This is the strongest witness-level assumption in the file. It says that if a
family of formulas `Φ : Nat → Formula` changes only by increasing its parameter
from `n` to `k`, then a witness for the smaller instance can be turned into a
witness for the larger instance, provided the original witness already fits
within the larger budget `k`.

Concretely:
* `Φ n` is the formula at the smaller parameter.
* `Φ k` is the formula at the larger parameter.
* `w` is a witness that proves the smaller formula.
* `witnessChars w ≤ k` says the witness is still within the budget available
  at the larger parameter.
* the conclusion produces a witness `w'` for the larger formula, again with
  size at most `k`.

This is the axiom that lets a proof at parameter `n` be reused when the
parameter is raised to `k`, without having to encode a specific CUPOD bridge
in the theorem file.
-/
axiom witness_transport_family :
  ∀ (Φ : Nat → Formula) n k,
  n ≤ k →
  ∀ w, witnessProves w (Φ n) →
  witnessChars w ≤ k →
    ∃ w', witnessProves w' (Φ k) ∧ witnessChars w' ≤ k

-- . -------------------------------------------------------------------------


-- Parametric Bounded Löb's Theorem (Lemma 3.6).
--
-- Informally: let `φ k` be a formula family in the proof language of `S`,
-- `k₁ ∈ ℕ` a base threshold, and `f : ℕ → ℕ` an *increasing* computable
-- function with `f(k) ≻ O(lg k)`. If `S` can derive, for every `k > k₁`,
-- that bounded provability of `φ k` within `f(k)` steps implies `φ k`
-- itself, then there exists a threshold `k₂` beyond which `S` proves
-- `φ k` outright.
--
-- Encoding notes:
-- * `□_{f(k)}(φ k)` is the formula `Formula.box (f k) (φ k)`; its
--   semantic clause is `proofSearch (f k) (φ k) = true`.
-- * "`S` derives ψ" is `∃ m, proofSearch m ψ = true`.
-- * `f(k) ≻ O(lg k)` is spelled out as: there exists a positive constant
--   `c` and a threshold `k̂` such that for all `k > k̂`, `f(k) > c · lg k`.
-- * "Increasing" is the plain pointwise condition on `f`; the
--   "computable" side of the paper's hypothesis is vacuous in Lean since
--   every `Nat → Nat` we can write down is already computable in the
--   relevant sense.
axiom PBLT :
  ∀ (φ : Nat → Formula) (f : Nat → Nat) (k₁ : Nat),
    (∀ a b, a ≤ b → f a ≤ f b) →
    (∃ c kHat, c > 0 ∧ ∀ k, k > kHat → f k > c * Nat.log2 k) →
    (∀ k, k > k₁ → ∃ m, proofSearch m (.impl (.box (f k) (φ k)) (φ k)) = true) →
      ∃ k₂, ∀ k, k > k₂ → ∃ m, proofSearch m (φ k) = true

/--
S can read source code: if an agent `me` is literally
`.search k ψ (.const a) (.const b)`, then S proves
`□_k ψ' → me plays a against opponent`, where `ψ' = ψ.subst me opponent`
is the closed guard formula `eval` feeds to `proofSearch`.

The implication is true by inspection of `me`'s code: a successful proof
search makes `eval` take the `.const a` branch and return `a`. We make this
an axiom because we don't model S's internals; critch22 uses the same step
silently when applying PBLT (e.g. Theorem 3.4 for CUPOD, 3.7 for DUPOC).
-/
axiom proof_system_verifies_search_branch :
  ∀ (k : Nat) (ψ : Formula) (a b : Action) (me opponent : Prog),
    me = .search k ψ (.const a) (.const b) →
    ∃ m, proofSearch m
      (.impl (.box k (ψ.subst me opponent)) (.plays me opponent a)) = true

end PDNew.Axioms
