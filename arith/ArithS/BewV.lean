import ArithS.Proper

/-!
# ArithS.BewV — `□_k` with the budget `k` as a formula variable

`LenProvableV T k φ := ∃ d < fbound k, Proof T d φ ∧ dlen T d ≤ k`, for `k φ : V`. This is
`LenProvable fbound k T φ` (`ArithS.Bew`) with the meta budget replaced by an object
variable, which is what the evaluator's `search` clause needs (the budget is stored in the
program code). Δ₁: the code bound `fbound k` makes the search bounded; properness
(`ArithS.Proper`) is what makes the bound invisible.
-/

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {L : Language} [L.Encodable] [L.LORDefinable]
variable (T : Theory L) [T.Δ₁]

/-- Provability by a proof of length `≤ k` (code below `fbound k`), `k` an element of `V`. -/
def LenProvableV (k φ : V) : Prop := ∃ d < fbound k, Proof T d φ ∧ dlen T d ≤ k

noncomputable def lenProvableV : 𝚫₁.Semisentence 2 := .mkDelta
  (.mkSigma “k φ. ∃ E, !fboundDef E k ∧ ∃ d < E, !(proof T).sigma d φ ∧ ∃ n, !(dlenDef T) n d ∧ n ≤ k”)
  (.mkPi “k φ. ∀ E, !fboundDef E k → ∃ d < E, !(proof T).pi d φ ∧ ∀ n, !(dlenDef T) n d → n ≤ k”)

instance LenProvableV.defined : 𝚫₁-Relation[V] (LenProvableV T) via lenProvableV T := .mk
  ⟨by intro v
      simp [lenProvableV, HierarchySymbol.Semiformula.val_sigma, fbound_defined.iff,
        (Proof.defined (T := T)).proper.iff', dlen_defined.iff],
   by intro v
      simp [lenProvableV, HierarchySymbol.Semiformula.val_sigma, fbound_defined.iff,
        (Proof.defined (T := T)).df, dlen_defined.iff, LenProvableV]⟩

instance LenProvableV.definable : 𝚫₁-Relation[V] (LenProvableV T) := (LenProvableV.defined T).to_definable

instance LenProvableV.definable' : Γ-[m + 1]-Relation[V] (LenProvableV T) :=
  (LenProvableV.definable T).of_deltaOne

/-- At a meta budget, `LenProvableV` is `LenProvable fbound`. -/
lemma lenProvableV_numeral (k : ℕ) (φ : V) :
    LenProvableV T (ORingStructure.numeral k) φ ↔ LenProvable (fbound : V → V) k T φ := Iff.rfl

end ArithS
