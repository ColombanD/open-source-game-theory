import ArithS.Symmetry

/-!
# ArithS.ProofLength — a proof is at least as long as what it proves

Two general facts kept from the retired `Vacuity.lean` (commit 470ee43): every node of `mlen`
charges its whole conclusion sequent, so a derivation is at least as long as any formula of
its conclusion, and length-bounded provability bounds the length of the sentence proved.
Both are used by the impossibility theorem T2-NEG (roadmap M3): a PA proof of a sentence that
writes a program's code is at least as long as that code.
-/

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus
open LAct

/-! ### `flen` on the connectives (definitional equations, for `rw`) -/

section flenEqns

variable {L : Language} {n : ℕ}

@[simp] lemma flen_rel {k : ℕ} (R : L.Rel k) (v : Fin k → SyntacticSemiterm L n) :
    flen (Semiformula.rel R v) = (∑ i, tlen (v i)) + 1 := rfl
@[simp] lemma flen_nrel {k : ℕ} (R : L.Rel k) (v : Fin k → SyntacticSemiterm L n) :
    flen (Semiformula.nrel R v) = (∑ i, tlen (v i)) + 1 := rfl
@[simp] lemma flen_verum : flen (⊤ : Semiproposition L n) = 1 := rfl
@[simp] lemma flen_falsum : flen (⊥ : Semiproposition L n) = 1 := rfl
@[simp] lemma flen_and (φ ψ : Semiproposition L n) : flen (φ ⋏ ψ) = flen φ + flen ψ + 1 := rfl
@[simp] lemma flen_or (φ ψ : Semiproposition L n) : flen (φ ⋎ ψ) = flen φ + flen ψ + 1 := rfl
@[simp] lemma flen_all (φ : Semiproposition L (n + 1)) : flen (∀¹ φ) = flen φ + 1 := rfl
@[simp] lemma flen_exs (φ : Semiproposition L (n + 1)) : flen (∃¹ φ) = flen φ + 1 := rfl

end flenEqns

section derivation

variable {L : Language} [L.DecidableEq] [L.Encodable] [L.LORDefinable] {T : Theory L} [T.Δ₁]

/-- A derivation is at least as long as any formula of its conclusion. -/
lemma flen_le_mlen {Γ : Finset (Proposition L)} (d : T ⟹₂ Γ) {σ : Proposition L} (h : σ ∈ Γ) :
    flen σ ≤ mlen d :=
  le_trans (flen_le_sqlen h) (sqlen_le_mlen d)

end derivation

/-- Length-bounded provability bounds the length of the sentence proved. -/
theorem flen_le_of_lenProvable {σ : Sentence LAct} {k : ℕ}
    (h : LenProvable (fbound : ℕ → ℕ) k TAct (⌜σ⌝ : ℕ)) : flen (σ : Proposition LAct) ≤ k := by
  rcases h with ⟨d, _, hd, hk⟩
  have e : (ORingStructure.numeral k : ℕ) = k := by simp
  rw [Sentence.quote_def] at hd
  obtain ⟨b, rfl⟩ := Proof.sound' hd
  rw [dlen_quote, e] at hk
  have hk' : mlen b ≤ k := by
    rcases le_def.mp hk with h | h
    · exact Nat.le_of_eq h
    · exact Nat.le_of_lt h
  exact le_trans (flen_le_mlen b (Finset.mem_singleton_self _)) hk'

end ArithS
