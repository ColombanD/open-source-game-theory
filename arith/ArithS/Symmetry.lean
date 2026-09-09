import ArithS.Transpose
import ArithS.Sound

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

end ArithS
