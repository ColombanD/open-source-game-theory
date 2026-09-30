import ArithS.Theory.Symmetry

/-!
# ArithS.ProofLength — a proof is at least as long as what it proves

Two general facts kept from the retired `Vacuity.lean` (commit 470ee43): every node of `proofLenMeta`
charges its whole conclusion sequent, so a derivation is at least as long as any formula of
its conclusion, and length-bounded provability bounds the length of the sentence proved.
Both are used by the impossibility theorem T2-NEG (roadmap M3): a PA proof of a sentence that
writes a program's code is at least as long as that code.
-/

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus
open LAct

/-! ### `formulaLenMeta` on the connectives (definitional equations, for `rw`) -/

section formulaLenMetaEqns

variable {L : Language} {n : ℕ}

@[simp] lemma formulaLenMeta_rel {k : ℕ} (R : L.Rel k) (v : Fin k → SyntacticSemiterm L n) :
    formulaLenMeta (Semiformula.rel R v) = (∑ i, termLenMeta (v i)) + 1 := rfl
@[simp] lemma formulaLenMeta_nrel {k : ℕ} (R : L.Rel k) (v : Fin k → SyntacticSemiterm L n) :
    formulaLenMeta (Semiformula.nrel R v) = (∑ i, termLenMeta (v i)) + 1 := rfl
@[simp] lemma formulaLenMeta_verum : formulaLenMeta (⊤ : Semiproposition L n) = 1 := rfl
@[simp] lemma formulaLenMeta_falsum : formulaLenMeta (⊥ : Semiproposition L n) = 1 := rfl
@[simp] lemma formulaLenMeta_and (φ ψ : Semiproposition L n) : formulaLenMeta (φ ⋏ ψ) = formulaLenMeta φ + formulaLenMeta ψ + 1 := rfl
@[simp] lemma formulaLenMeta_or (φ ψ : Semiproposition L n) : formulaLenMeta (φ ⋎ ψ) = formulaLenMeta φ + formulaLenMeta ψ + 1 := rfl
@[simp] lemma formulaLenMeta_all (φ : Semiproposition L (n + 1)) : formulaLenMeta (∀¹ φ) = formulaLenMeta φ + 1 := rfl
@[simp] lemma formulaLenMeta_exs (φ : Semiproposition L (n + 1)) : formulaLenMeta (∃¹ φ) = formulaLenMeta φ + 1 := rfl

end formulaLenMetaEqns

section derivation

variable {L : Language} [L.DecidableEq] [L.Encodable] [L.LORDefinable] {T : Theory L} [T.Δ₁]

/-- A derivation is at least as long as any formula of its conclusion. -/
lemma formulaLenMeta_le_proofLenMeta {Γ : Finset (Proposition L)} (d : T ⟹₂ Γ) {σ : Proposition L} (h : σ ∈ Γ) :
    formulaLenMeta σ ≤ proofLenMeta d :=
  le_trans (formulaLenMeta_le_sequentLenMeta h) (sequentLenMeta_le_proofLenMeta d)

end derivation

/-- Length-bounded provability bounds the length of the sentence proved. -/
theorem formulaLenMeta_le_of_lenBoxNat {σ : Sentence LAct} {k : ℕ}
    (h : LenBoxNat (codeBound : ℕ → ℕ) k TAct (⌜σ⌝ : ℕ)) : formulaLenMeta (σ : Proposition LAct) ≤ k := by
  rcases h with ⟨d, _, hd, hk⟩
  have e : (ORingStructure.numeral k : ℕ) = k := by simp
  rw [Sentence.quote_def] at hd
  obtain ⟨b, rfl⟩ := Proof.sound' hd
  rw [proofLen_quote, e] at hk
  have hk' : proofLenMeta b ≤ k := by
    rcases le_def.mp hk with h | h
    · exact Nat.le_of_eq h
    · exact Nat.le_of_lt h
  exact le_trans (formulaLenMeta_le_proofLenMeta b (Finset.mem_singleton_self _)) hk'

end ArithS
