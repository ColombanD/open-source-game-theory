import ArithS.Bew
import Mathlib.Algebra.BigOperators.Fin

/-!
# ArithS.MetaLength — the code-level length agrees with the meta-level symbol count

`tlen`/`flen` are the symbol counts on Foundation's META syntax (`SyntacticSemiterm`,
`Semiproposition`), defined by structural recursion; `termLen_quote`/`formulaLen_quote`
say the Σ₁ functions of `ArithS.Length` compute exactly them on Gödel codes, in EVERY
model `V`. This is the bridge both the properness estimate (M1) and the τ-transposition
argument (M2, `len ∘ τ = len` is proved on the meta side) run through. Sequents and
derivations follow in the second half of the file.
-/

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {L : Language} [L.Encodable] [L.LORDefinable]

/-! ### Terms -/

/-- Symbol count of a syntactic term: a variable of index `i` counts `i + 1`, a function
symbol `1`. -/
def tlen {n : ℕ} : SyntacticSemiterm L n → ℕ
  | #x => x + 1
  | &x => x + 1
  | FirstOrder.Semiterm.func _ v => (∑ i, tlen (v i)) + 1

@[simp] lemma tlen_bvar {n : ℕ} (x : Fin n) : tlen (#x : SyntacticSemiterm L n) = x + 1 := by
  simp [tlen]
@[simp] lemma tlen_fvar {n : ℕ} (x : ℕ) : tlen (&x : SyntacticSemiterm L n) = x + 1 := by
  simp [tlen]
@[simp] lemma tlen_func {n k : ℕ} (f : L.Func k) (v : Fin k → SyntacticSemiterm L n) :
    tlen (FirstOrder.Semiterm.func f v) = (∑ i, tlen (v i)) + 1 := by simp [tlen]

lemma listSum_termLenVec {k n : ℕ} (w : SemitermVec V L k n) :
    listSum (termLenVec L ↑k w.val) = ∑ i, termLen L (w i).val := by
  induction k with
  | zero =>
    rw [SemitermVec.val_nil, Nat.cast_zero, termLenVec_nil, listSum_nil]
    simp
  | succ k ih =>
    rw [SemitermVec.val_succ, Nat.cast_succ,
      termLenVec_cons (Semiterm.isUTerm _) (SemitermVec.isUTermVec _), listSum_adjoin,
      ih, Fin.sum_univ_succ]
    rfl

theorem termLen_quote {n : ℕ} (t : SyntacticSemiterm L n) :
    termLen L (⌜t⌝ : V) = ↑(tlen t) := by
  induction t with
  | bvar x => simp
  | fvar x => simp
  | func f v ih =>
    rw [Semiterm.quote_func, termLen_func (by simp) (SemitermVec.isUTermVec _),
      listSum_termLenVec, tlen_func]
    push_cast
    congr 1
    exact Finset.sum_congr rfl (fun i _ ↦ ih i)

/-! ### Formulas -/

/-- Symbol count of a syntactic formula. -/
def flen {n : ℕ} : Semiproposition L n → ℕ
  | .rel _ v => (∑ i, tlen (v i)) + 1
  | .nrel _ v => (∑ i, tlen (v i)) + 1
  | .verum => 1
  | .falsum => 1
  | .and φ ψ => flen φ + flen ψ + 1
  | .or φ ψ => flen φ + flen ψ + 1
  | .all φ => flen φ + 1
  | .exs φ => flen φ + 1

theorem formulaLen_quote {n : ℕ} (φ : Semiproposition L n) :
    formulaLen L (⌜φ⌝ : V) = ↑(flen φ) := by
  induction φ with
  | rel R v =>
    rw [Semiformula.quote_rel, formulaLen_rel (by simp) (SemitermVec.isUTermVec _),
      listSum_termLenVec]
    simp only [flen]
    push_cast
    congr 1
    exact Finset.sum_congr rfl (fun i _ ↦ termLen_quote (v i))
  | nrel R v =>
    rw [Semiformula.quote_nrel, formulaLen_nrel (by simp) (SemitermVec.isUTermVec _),
      listSum_termLenVec]
    simp only [flen]
    push_cast
    congr 1
    exact Finset.sum_congr rfl (fun i _ ↦ termLen_quote (v i))
  | verum =>
    change formulaLen L ⌜(⊤ : Semiproposition L _)⌝ = ((1 : ℕ) : V)
    simp
  | falsum =>
    change formulaLen L ⌜(⊥ : Semiproposition L _)⌝ = ((1 : ℕ) : V)
    simp
  | and φ ψ ihφ ihψ =>
    change formulaLen L ⌜φ ⋏ ψ⌝ = ((flen φ + flen ψ + 1 : ℕ) : V)
    rw [Semiformula.quote_and, formulaLen_and (Semiformula.quote_isSemiformula _).isUFormula (Semiformula.quote_isSemiformula _).isUFormula, ihφ, ihψ]; push_cast; rfl
  | or φ ψ ihφ ihψ =>
    change formulaLen L ⌜φ ⋎ ψ⌝ = ((flen φ + flen ψ + 1 : ℕ) : V)
    rw [Semiformula.quote_or, formulaLen_or (Semiformula.quote_isSemiformula _).isUFormula (Semiformula.quote_isSemiformula _).isUFormula, ihφ, ihψ]; push_cast; rfl
  | all φ ih =>
    change formulaLen L ⌜∀¹ φ⌝ = ((flen φ + 1 : ℕ) : V)
    rw [Semiformula.quote_all, formulaLen_all (Semiformula.quote_isSemiformula _).isUFormula, ih]; push_cast; rfl
  | exs φ ih =>
    change formulaLen L ⌜∃¹ φ⌝ = ((flen φ + 1 : ℕ) : V)
    rw [Semiformula.quote_ex, formulaLen_exs (Semiformula.quote_isSemiformula _).isUFormula, ih]; push_cast; rfl

end ArithS
