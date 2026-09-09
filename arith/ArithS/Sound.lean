import ArithS.MetaLength

/-!
# ArithS.Sound — internal derivation codes come from meta derivations, code for code

Foundation's `Derivation.sound` reconstructs, from an internal derivation code `d`, SOME
meta derivation of the decoded sequent. We need more: a meta derivation `b` with
`⌜b⌝ = d` exactly, so that `dlen T d = mlen b` (`dlen_quote`) and the length-preserving
transposition of `ArithS.Transpose` can be pulled back to codes. The proof is Foundation's,
with the `quote_*` equations threaded through every case.
-/

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping Derivation2

variable {L : Language} [L.DecidableEq] [L.Encodable] [L.LORDefinable]
variable {T : Theory L} [T.Δ₁]

/-- The conclusion of a quoted derivation is the quoted conclusion. -/
lemma fstIdx_quote {Γ : Finset (Proposition L)} (b : T ⟹₂ Γ) : fstIdx (⌜b⌝ : ℕ) = ⌜Γ⌝ :=
  (Derivation2.typedQuote ℕ b).derivationOf.1

/-- Every internal derivation code is the code of a meta derivation. -/
theorem Derivation.sound' {d : ℕ} (h : Derivation T d) :
    ∃ Γ : Finset (Proposition L), ∃ b : T ⟹₂ Γ, (⌜b⌝ : ℕ) = d := by
  induction d using Nat.strongRec
  case ind d ih =>
  rcases h.case with ⟨hs, H⟩
  rcases isFormulaSet_sound hs with ⟨Γ, hΓ⟩
  rcases H with (⟨s, φ, rfl, hφ, hnp⟩ | ⟨s, rfl, hv⟩ |
    ⟨s, φ, ψ, dp, dq, rfl, hpq, ⟨hφ, hdφ⟩, ⟨hψ, hdq⟩⟩ | ⟨s, φ, ψ, d, rfl, hpq, ⟨h, hd⟩⟩ |
    ⟨s, φ, d, rfl, hps, hd, dd⟩ | ⟨s, φ, t, d, rfl, hps, ht, hd, dd⟩ |
    ⟨s, d, rfl, hs', dd⟩ | ⟨s, d, rfl, rfl, dd⟩ |
    ⟨s, φ, d₁, d₂, rfl, ⟨h₁, dd₁⟩, ⟨h₂, dd₂⟩⟩ | ⟨s, φ, rfl, hs', hT⟩)
  · rcases (hs φ (by simp [hφ])).sound with ⟨φ, rfl⟩
    rcases by simpa using hΓ
    refine ⟨Γ, Derivation2.closed Γ φ
      (by simp [←Sequent.mem_quote_iff (V := ℕ), hφ])
      (by simpa [←Sequent.mem_quote_iff (V := ℕ), Semiformula.quote_def] using hnp), ?_⟩
    rw [quote_closed]
  · rcases by simpa using hΓ
    refine ⟨Γ, Derivation2.verum (by simp [←Sequent.mem_quote_iff (V := ℕ), hv]), ?_⟩
    rw [quote_verum]
  · have fpq : IsFormula L φ ∧ IsFormula L ψ := by simpa using hs (φ ^⋏ ψ) (by simp [hpq])
    rcases by simpa using hΓ
    rcases fpq.1.sound with ⟨φ, rfl⟩
    rcases fpq.2.sound with ⟨ψ, rfl⟩
    rcases ih dp (by simp) hdφ with ⟨Γφ, bφ, rfl⟩
    rcases ih dq (by simp) hdq with ⟨Γψ, bψ, rfl⟩
    have eφ : Γφ = insert φ Γ :=
      Sequent.quote_inj (V := ℕ) (by rw [← fstIdx_quote bφ, hφ]; simp)
    have eψ : Γψ = insert ψ Γ :=
      Sequent.quote_inj (V := ℕ) (by rw [← fstIdx_quote bψ, hψ]; simp)
    refine ⟨Γ, Derivation2.and (φ := φ) (ψ := ψ)
      (by simp [←Sequent.mem_quote_iff (V := ℕ), hpq]) (bφ.cast eφ) (bψ.cast eψ), ?_⟩
    rw [quote_and, quote_cast, quote_cast]
  · have fpq : IsFormula L φ ∧ IsFormula L ψ := by simpa using hs (φ ^⋎ ψ) (by simp [hpq])
    rcases by simpa using hΓ
    rcases fpq.1.sound with ⟨φ, rfl⟩
    rcases fpq.2.sound with ⟨ψ, rfl⟩
    rcases ih d (by simp) hd with ⟨Δ, b, rfl⟩
    have e : Δ = insert φ (insert ψ Γ) :=
      Sequent.quote_inj (V := ℕ) (by rw [← fstIdx_quote b, h]; simp)
    refine ⟨Γ, Derivation2.or (φ := φ) (ψ := ψ)
      (by simp [←Sequent.mem_quote_iff (V := ℕ), Semiformula.quote_or, hpq]) (b.cast e), ?_⟩
    rw [quote_or, quote_cast]
  · rcases by simpa using hΓ
    have : IsSemiformula L 1 φ := by simpa using hs (^∀ φ) (by simp [hps])
    rcases this.sound with ⟨φ, rfl⟩
    rcases ih d (by simp) dd with ⟨Δ, b, rfl⟩
    have e : Δ = insert (Rewriting.free φ) (Γ.image Rewriting.shift) :=
      Sequent.quote_inj (V := ℕ) (by
        rw [← fstIdx_quote b, hd]; simp [setShift_quote, Semiformula.quote_def])
    refine ⟨Γ, Derivation2.all (φ := φ)
      (by simp [←Sequent.mem_quote_iff (V := ℕ), Semiformula.quote_all, hps]) (b.cast e), ?_⟩
    rw [quote_all, quote_cast]
  · rcases by simpa using hΓ
    have : IsSemiformula L 1 φ := by simpa using hs (^∃ φ) (by simp [hps])
    rcases this.sound with ⟨φ, rfl⟩
    rcases ht.sound with ⟨t, rfl⟩
    rcases ih d (by simp) dd with ⟨Δ, b, rfl⟩
    have e : Δ = insert (φ/[t]) Γ :=
      Sequent.quote_inj (V := ℕ) (by
        rw [← fstIdx_quote b, hd]
        simp [substs1, Matrix.constant_eq_singleton, Semiformula.quote_def, Semiterm.quote_def])
    refine ⟨Γ, Derivation2.exs (φ := φ)
      (by simp [←Sequent.mem_quote_iff (V := ℕ), Semiformula.quote_ex, hps]) t (b.cast e), ?_⟩
    rw [quote_exs, quote_cast]
  · rcases by simpa using hΓ
    rcases ih d (by simp) dd with ⟨Δ, b, rfl⟩
    rw [fstIdx_quote b] at hs'
    refine ⟨Γ, Derivation2.wk (Δ := Δ) b ((Sequent.quote_subset_quote (V := ℕ)).mp hs'), ?_⟩
    rw [quote_wk]
  · rcases ih d (by simp) dd with ⟨Δ, b, rfl⟩
    have : Γ = Finset.image Rewriting.shift Δ :=
      Sequent.quote_inj <| by simpa [fstIdx_quote b, setShift_quote] using hΓ
    rcases this
    exact ⟨_, Derivation2.shift b, by rw [quote_shift, fstIdx_quote b, setShift_quote]⟩
  · rcases by simpa using hΓ
    have : IsFormula L φ := dd₁.isFormulaSet φ (by simp [h₁])
    rcases this.sound with ⟨φ, rfl⟩
    rcases ih d₁ (by simp) dd₁ with ⟨Δ₁, b₁, rfl⟩
    have e₁ : Δ₁ = insert φ Γ :=
      Sequent.quote_inj (V := ℕ) (by rw [← fstIdx_quote b₁, h₁]; simp)
    rcases ih d₂ (by simp) dd₂ with ⟨Δ₂, b₂, rfl⟩
    have e₂ : Δ₂ = insert (∼φ) Γ :=
      Sequent.quote_inj (V := ℕ) (by rw [← fstIdx_quote b₂, h₂]; simp [Semiformula.quote_def])
    refine ⟨Γ, Derivation2.cut (b₁.cast e₁) (b₂.cast e₂), ?_⟩
    rw [quote_cut, quote_cast, quote_cast]
  · rcases by simpa using hΓ
    rcases Sequent.mem_quote hs' with ⟨φ, hφ, rfl⟩
    have : ∃ σ ∈ T, φ = ↑σ := by simpa using hT
    rcases this with ⟨σ, hσ, rfl⟩
    exact ⟨Γ, Derivation2.axm σ (by simp [hσ]) hφ, by rw [quote_axm]; rfl⟩

/-- Every internal proof code of `⌜φ⌝` is the code of a meta proof of `φ`. -/
theorem Proof.sound' {φ : Proposition L} {d : ℕ} (h : Proof T d (⌜φ⌝ : ℕ)) :
    ∃ b : T ⟹₂ {φ}, (⌜b⌝ : ℕ) = d := by
  rcases Derivation.sound' h.2 with ⟨Γ, b, rfl⟩
  have hΓ : Γ = {φ} := Sequent.quote_inj (V := ℕ) (by
    rw [← fstIdx_quote b, h.1]; exact (Sequent.quote_singleton φ).symm)
  subst hΓ
  exact ⟨b, rfl⟩

end ArithS
