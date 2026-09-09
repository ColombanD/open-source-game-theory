import ArithS.Transpose
import ArithS.Sound
import ArithS.Proper

/-!
# ArithS.Symmetry — τ-closure of `TAct` on internal proof codes, at every length

`T ⊢_k φ ↔ T ⊢_k (swap φ)` for `T = TAct`, where `⊢_k` is "some internal proof code of
length `≤ k`" (the Σ₁, code-bound-free reading of `□_k`). Proof: a code is the code of a
meta proof (`Proof.sound'`), whose length is its `mlen` (`dlen_quote`); the transposed meta
proof (`transpose_exists`) has the same `mlen`; quote it back (`derivation_quote`).

The `f`-bounded predicate `LenProvable f k TAct` is symmetric too as soon as the code bound
never bites (properness, M1's last item): the transposed code has the same LENGTH, but not
the same magnitude.
-/

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus
open LAct

/-- Length-bounded provability on codes, without the code bound. -/
def ProvableLen (T : Theory LAct) [T.Δ₁] (k : ℕ) (φ : Proposition LAct) : Prop :=
  ∃ d : ℕ, Proof T d (⌜φ⌝ : ℕ) ∧ dlen T d ≤ k

theorem provableLen_swap {k : ℕ} {φ : Proposition LAct} (h : ProvableLen TAct k φ) :
    ProvableLen TAct k (Semiformula.lMap swap φ) := by
  rcases h with ⟨d, hd, hk⟩
  obtain ⟨b, rfl⟩ := Proof.sound' hd
  obtain ⟨b', hb'⟩ := transpose_exists φ b
  refine ⟨⌜b'⌝, ⟨?_, derivation_quote b'⟩, ?_⟩
  · rw [fstIdx_quote b']; exact Derivation2.Sequent.quote_singleton _
  · rw [dlen_quote, hb', ← dlen_quote]; exact hk

/-- **τ-closure of `TAct` at every length**: `TAct ⊢_k φ ↔ TAct ⊢_k (swap φ)`. -/
theorem provableLen_swap_iff (k : ℕ) (φ : Proposition LAct) :
    ProvableLen TAct k φ ↔ ProvableLen TAct k (Semiformula.lMap swap φ) :=
  ⟨provableLen_swap, fun h ↦ by simpa [lMap_swap_swap] using provableLen_swap h⟩

/-! ### The bounded predicate is symmetric too, by properness -/

/-- `swap` preserves `LenProvable fbound k TAct`: the transposed proof has the same length,
and properness puts its code below `fbound k`. -/
theorem lenProvable_fbound_swap {k : ℕ} {φ : Sentence LAct}
    (h : LenProvable (fbound : ℕ → ℕ) k TAct (⌜φ⌝ : ℕ)) :
    LenProvable (fbound : ℕ → ℕ) k TAct (⌜Semiformula.lMap swap φ⌝ : ℕ) := by
  rcases h with ⟨d, hdk, hd, hk⟩
  have e : (ORingStructure.numeral k : ℕ) = k := by simp
  rw [Sentence.quote_def] at hd
  obtain ⟨b, rfl⟩ := Proof.sound' hd
  obtain ⟨b', hb'⟩ := transpose_exists _ b
  rw [dlen_quote, e] at hk
  have hk' : mlen b ≤ k := by
    rcases le_def.mp hk with h | h
    · exact Nat.le_of_eq h
    · exact Nat.le_of_lt h
  refine ⟨⌜b'⌝, ?_, ⟨?_, derivation_quote b'⟩, ?_⟩
  · rw [e, fbound_nat]
    refine Nat.lt_succ_of_le (le_trans (quote_derivation_le smallCodes_LAct smallRelCodes_LAct b')
      (F_mono ?_))
    rw [hb']
    exact Nat.mul_le_mul_left 12 hk'
  · rw [fstIdx_quote b', Sentence.quote_def, ← Semiformula.lMap_emb]
    exact Derivation2.Sequent.quote_singleton _
  · rw [dlen_quote, hb', e]; exact hk

theorem lenProvable_fbound_swap_iff (k : ℕ) (φ : Sentence LAct) :
    LenProvable (fbound : ℕ → ℕ) k TAct (⌜φ⌝ : ℕ) ↔
    LenProvable (fbound : ℕ → ℕ) k TAct (⌜Semiformula.lMap swap φ⌝ : ℕ) :=
  ⟨lenProvable_fbound_swap, fun h ↦ by simpa [lMap_swap_swap] using lenProvable_fbound_swap h⟩

end ArithS
