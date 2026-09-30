import ArithS.Length.Proper

/-!
# ArithS.BewV — `□_k` with the budget `k` as a formula variable

`LenBox T k φ := ∃ d < codeBound k, Proof T d φ ∧ proofLen T d ≤ k`, for `k φ : V`. This is
`LenBoxNat codeBound k T φ` (`ArithS.Bew`) with the meta budget replaced by an object
variable, which is what the evaluator's `search` clause needs (the budget is stored in the
program code). Δ₁: the code bound `codeBound k` makes the search bounded; properness
(`ArithS.Proper`) is what makes the bound invisible.

**Reading guide.** Definition: `LenBox` (the first declaration). Foundation plumbing: `lenBox` (the Δ₁ formula) and `LenBox.defined` — skip on first reading. Fact: `lenBox_numeral` (at a meta budget it is `LenBoxNat`).
-/

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {L : Language} [L.Encodable] [L.LORDefinable]
variable (T : Theory L) [T.Δ₁]

/-! ### Definition -/

/-- Provability by a proof of length `≤ k` (code below `codeBound k`), `k` an element of `V`. -/
def LenBox (k φ : V) : Prop := ∃ d < codeBound k, Proof T d φ ∧ proofLen T d ≤ k

/-! ### Foundation plumbing — the Δ₁ formula, skip on first reading -/

noncomputable def lenBox : 𝚫₁.Semisentence 2 := .mkDelta
  (.mkSigma “k φ. ∃ E, !codeBoundDef E k ∧ ∃ d < E, !(proof T).sigma d φ ∧ ∃ n, !(proofLenDef T) n d ∧ n ≤ k”)
  (.mkPi “k φ. ∀ E, !codeBoundDef E k → ∃ d < E, !(proof T).pi d φ ∧ ∀ n, !(proofLenDef T) n d → n ≤ k”)

instance LenBox.defined : 𝚫₁-Relation[V] (LenBox T) via lenBox T := .mk
  ⟨by intro v
      simp [lenBox, HierarchySymbol.Semiformula.val_sigma, codeBound_defined.iff,
        (Proof.defined (T := T)).proper.iff', proofLen_defined.iff],
   by intro v
      simp [lenBox, HierarchySymbol.Semiformula.val_sigma, codeBound_defined.iff,
        (Proof.defined (T := T)).df, proofLen_defined.iff, LenBox]⟩

/-! ### Facts -/

/-- At a meta budget, `LenBox` is `LenBoxNat codeBound`. -/
lemma lenBox_numeral (k : ℕ) (φ : V) :
    LenBox T (ORingStructure.numeral k) φ ↔ LenBoxNat (codeBound : V → V) k T φ := Iff.rfl

end ArithS
