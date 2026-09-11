import ArithS.Symmetry
import ArithS.ProofLength

/-!
# ArithS.Cut — bounded D2 in rule form: modus ponens with exact length accounting

**Bounded D2 (rule form): PA-`S` closes under modus ponens at additive cost
`k₁ + k₂ + c₁·(|φ| + |ψ|) + c₀`**, a character-count analogue of the engine's `mp` at cost
`m₁ + m₂ + |ψ|` — the first field of the bounded-GL interface (`Base/BoundedGL.lean`) that the
arithmetized system satisfies (roadmap M4, "D2 / cut").

The construction is one `cut` on `φ ➝ ψ` in Foundation's one-sided calculus `Derivation2`
(`cutMP`): weaken the proof of `φ ➝ ψ` to `{ψ, φ ➝ ψ}`; on the other side, `∼(φ ➝ ψ) = φ ⋏ ∼ψ`
is introduced by `and` from a weakening of the proof of `φ` and the closed leaf `{ψ, ∼ψ}`.
Every node charges its whole conclusion sequent (`mlen`), which gives the exact bound
`mlen d₁ + mlen d₂ + 5|φ| + 10|ψ| + 9` (`mlen_cutMP`); the uniform constants are
`c₁ = 10, c₀ = 9`.

Note that the engine charges only `|ψ|` while PA-`S` also pays `|φ|`: the cut formula is
copied into the side sequents. This is a constant-factor departure that any budget-keeping
transfer must absorb (T2-NEG shows the atoms — evaluation steps and cheap citations — are the
real obstruction, not this).

Code level: a length-bounded code is the code of a meta proof (`Proof.sound'`), the meta cut
has the bounded `mlen`, quoting it back gives a code (`derivation_quote`) of that length
(`dlen_quote`) and, by properness (`quote_derivation_le`), below `fbound` of the new budget —
the pattern of `lenProvable_fbound_swap`. Also here: `fbound` is monotone, so
`LenProvable fbound` is budget-monotone (`lenProvable_fbound_mono`), and the `verum` leaf
(`lenProvable_verum`) as the sanity instance.
-/

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus
open LAct

/-! ### `flen` and `sqlen` on the shapes the cut produces -/

section flen

variable {L : Language}

/-- The de Morgan dual has the same symbol count (`∼` swaps `rel/nrel`, `⋏/⋎`, `∀/∃`). -/
lemma flen_neg {n : ℕ} (φ : Semiproposition L n) : flen (∼φ) = flen φ := by
  induction φ with
  | rel R v => rfl
  | nrel R v => rfl
  | verum => rfl
  | falsum => rfl
  | and φ ψ ihφ ihψ =>
    rw [Semiformula.neg_eq] at ihφ ihψ ⊢
    simp only [Semiformula.neg, flen, ihφ, ihψ]
  | or φ ψ ihφ ihψ =>
    rw [Semiformula.neg_eq] at ihφ ihψ ⊢
    simp only [Semiformula.neg, flen, ihφ, ihψ]
  | all φ ih =>
    rw [Semiformula.neg_eq] at ih ⊢
    simp only [Semiformula.neg, flen, ih]
  | exs φ ih =>
    rw [Semiformula.neg_eq] at ih ⊢
    simp only [Semiformula.neg, flen, ih]

/-- `φ ➝ ψ` is `∼φ ⋎ ψ`: one symbol more than its parts. -/
lemma flen_imp {n : ℕ} (φ ψ : Semiproposition L n) : flen (φ ➝ ψ) = flen φ + flen ψ + 1 := by
  rw [Semiformula.imp_eq, flen_or, flen_neg]

lemma sqlen_singleton (φ : Proposition L) : sqlen ({φ} : Finset (Proposition L)) = flen φ :=
  Finset.sum_singleton _ _

/-- Inserting a formula adds at most its symbol count (exactly, unless it was already there). -/
lemma sqlen_insert_le (φ : Proposition L) (Γ : Finset (Proposition L)) :
    sqlen (insert φ Γ) ≤ flen φ + sqlen Γ := by
  by_cases h : φ ∈ Γ
  · rw [Finset.insert_eq_of_mem h]; exact Nat.le_add_left _ _
  · rw [sqlen, Finset.sum_insert h]

end flen

/-! ### `mlen` of the basic constructions -/

section mlen

variable {L : Language} [L.DecidableEq] [L.Encodable] [L.LORDefinable]
variable {T : Theory L} [T.Δ₁]

lemma mlen_closed (Γ : Finset (Proposition L)) (φ : Proposition L) (h : φ ∈ Γ) (hn : ∼φ ∈ Γ) :
    mlen (Derivation2.closed (T := T) Γ φ h hn) = sqlen Γ + 1 := by simp [mlen]

lemma mlen_verum {Γ : Finset (Proposition L)} (h : ⊤ ∈ Γ) :
    mlen (Derivation2.verum (T := T) h) = sqlen Γ + 1 := by simp [mlen]

lemma mlen_wk {Δ Γ : Finset (Proposition L)} (d : T ⟹₂ Δ) (ss : Δ ⊆ Γ) :
    mlen (Derivation2.wk d ss) = sqlen Γ + mlen d + 1 := by simp [mlen]

lemma mlen_and {Γ : Finset (Proposition L)} {φ ψ : Proposition L} (h : φ ⋏ ψ ∈ Γ)
    (d₁ : T ⟹₂ insert φ Γ) (d₂ : T ⟹₂ insert ψ Γ) :
    mlen (Derivation2.and h d₁ d₂) = sqlen Γ + mlen d₁ + mlen d₂ + 1 := by simp [mlen]

lemma mlen_cut {Γ : Finset (Proposition L)} {φ : Proposition L}
    (d₁ : T ⟹₂ insert φ Γ) (d₂ : T ⟹₂ insert (∼φ) Γ) :
    mlen (Derivation2.cut d₁ d₂) = sqlen Γ + mlen d₁ + mlen d₂ + 1 := by simp [mlen]

/-! ### The cut construction -/

/-- Modus ponens as a `Derivation2`: from `{φ ➝ ψ}` and `{φ}` derive `{ψ}` by one `cut` on
`φ ➝ ψ` — the left premise is the weakened proof of `φ ➝ ψ`, the right one introduces
`∼(φ ➝ ψ) = φ ⋏ ∼ψ` from the weakened proof of `φ` and the closed leaf `{ψ, ∼ψ}`. -/
noncomputable def cutMP {φ ψ : Proposition L} (d₁ : T ⟹₂ {φ ➝ ψ}) (d₂ : T ⟹₂ {φ}) :
    T ⟹₂ {ψ} :=
  Derivation2.cut (Γ := {ψ}) (φ := φ ➝ ψ)
    (Derivation2.wk d₁ (by simp))
    (Derivation2.and (φ := φ) (ψ := ∼ψ) (by simp [Semiformula.imp_eq])
      (Derivation2.wk d₂ (by simp))
      (Derivation2.closed _ ψ (by simp) (by simp)))

/-- **Exact length accounting for the cut**: `5|φ| + 10|ψ| + 9` on top of the premises. -/
theorem mlen_cutMP {φ ψ : Proposition L} (d₁ : T ⟹₂ {φ ➝ ψ}) (d₂ : T ⟹₂ {φ}) :
    mlen (cutMP d₁ d₂) ≤ mlen d₁ + mlen d₂ + 5 * flen φ + 10 * flen ψ + 9 := by
  unfold cutMP
  rw [mlen_cut, mlen_wk, mlen_and, mlen_wk, mlen_closed]
  have hψ : sqlen ({ψ} : Finset (Proposition L)) = flen ψ := sqlen_singleton ψ
  have h₁ : sqlen (insert (φ ➝ ψ) {ψ}) ≤ flen φ + flen ψ + 1 + flen ψ := by
    have := sqlen_insert_le (φ ➝ ψ) {ψ}
    rwa [flen_imp, hψ] at this
  have h₂ : sqlen (insert (∼(φ ➝ ψ)) {ψ}) ≤ flen φ + flen ψ + 1 + flen ψ := by
    have := sqlen_insert_le (∼(φ ➝ ψ)) {ψ}
    rwa [flen_neg, flen_imp, hψ] at this
  have h₃ : sqlen (insert φ (insert (∼(φ ➝ ψ)) {ψ})) ≤
      flen φ + sqlen (insert (∼(φ ➝ ψ)) {ψ}) := sqlen_insert_le _ _
  have h₄ : sqlen (insert (∼ψ) (insert (∼(φ ➝ ψ)) {ψ})) ≤
      flen ψ + sqlen (insert (∼(φ ➝ ψ)) {ψ}) := by
    have := sqlen_insert_le (∼ψ) (insert (∼(φ ➝ ψ)) {ψ})
    rwa [flen_neg] at this
  omega

end mlen

/-! ### Code level, at `ℕ` -/

section code

variable {L : Language} [L.DecidableEq] [L.Encodable] [L.LORDefinable]
variable {T : Theory L} [T.Δ₁]

/-- `≤` at `ℕ` read through `ORingStructure` is PeanoMinus's `x = y ∨ x < y` (`le_def`);
bridge from `Nat.le`. -/
lemma le_of_nat_le {a b : ℕ} (h : a ≤ b) : @LE.le ℕ (ORingStructure.toLE) a b :=
  le_def.mpr (Nat.lt_or_eq_of_le h).symm

lemma nat_le_of_le {a b : ℕ} (h : @LE.le ℕ (ORingStructure.toLE) a b) : a ≤ b := by
  rcases le_def.mp h with h | h
  · exact Nat.le_of_eq h
  · exact Nat.le_of_lt h

/-- The bound `fbound` is monotone (three exponentials of `12 k`, plus one). -/
lemma fbound_mono : Monotone (fbound : ℕ → ℕ) := fun a b h ↦ by
  rw [fbound_nat, fbound_nat]
  exact Nat.succ_le_succ (F_mono (Nat.mul_le_mul_left 12 h))

/-- Budget monotonicity of `□_k` for the concrete bound. -/
theorem lenProvable_fbound_mono {k k' : ℕ} (h : k ≤ k') {φ : ℕ} :
    LenProvable (fbound : ℕ → ℕ) k T φ → LenProvable (fbound : ℕ → ℕ) k' T φ :=
  LenProvable.mono fbound_mono h

/-- A meta derivation of `{σ}` of length `≤ k` is a `LenProvable fbound k` witness (the
quote-back step shared by every rule below). -/
theorem lenProvable_of_derivation (hL : SmallCodes L) (hR : SmallRelCodes L)
    {σ : Sentence L} {k : ℕ} (b : T ⟹₂ {(σ : Proposition L)}) (hb : mlen b ≤ k) :
    LenProvable (fbound : ℕ → ℕ) k T (⌜σ⌝ : ℕ) := by
  have e : (ORingStructure.numeral k : ℕ) = k := by simp
  refine ⟨⌜b⌝, ?_, ⟨?_, derivation_quote b⟩, ?_⟩
  · rw [e, fbound_nat]
    exact Nat.lt_succ_of_le (le_trans (quote_derivation_le hL hR b)
      (F_mono (Nat.mul_le_mul_left 12 hb)))
  · rw [fstIdx_quote b, Sentence.quote_def]
    exact Derivation2.Sequent.quote_singleton _
  · rw [dlen_quote, e]
    exact le_of_nat_le hb

/-- The converse direction: a `LenProvable fbound k` witness is the code of a meta derivation
of length `≤ k` (`Proof.sound'` + `dlen_quote`). -/
theorem derivation_of_lenProvable {σ : Sentence L} {k : ℕ}
    (h : LenProvable (fbound : ℕ → ℕ) k T (⌜σ⌝ : ℕ)) :
    ∃ b : T ⟹₂ {(σ : Proposition L)}, mlen b ≤ k := by
  rcases h with ⟨d, _, hd, hk⟩
  have e : (ORingStructure.numeral k : ℕ) = k := by simp
  rw [Sentence.quote_def] at hd
  obtain ⟨b, rfl⟩ := Proof.sound' hd
  rw [dlen_quote, e] at hk
  exact ⟨b, nat_le_of_le hk⟩

/-- **Bounded D2, rule form, sharp constants** (generic `L`, `T` with small symbol codes). -/
theorem lenProvable_mp_sharp_of_small (hL : SmallCodes L) (hR : SmallRelCodes L)
    {k₁ k₂ : ℕ} {φ ψ : Sentence L}
    (h₁ : LenProvable (fbound : ℕ → ℕ) k₁ T (⌜φ ➝ ψ⌝ : ℕ))
    (h₂ : LenProvable (fbound : ℕ → ℕ) k₂ T (⌜φ⌝ : ℕ)) :
    LenProvable (fbound : ℕ → ℕ)
      (k₁ + k₂ + 5 * flen (φ : Proposition L) + 10 * flen (ψ : Proposition L) + 9)
      T (⌜ψ⌝ : ℕ) := by
  obtain ⟨b₁, hb₁⟩ := derivation_of_lenProvable h₁
  obtain ⟨b₂, hb₂⟩ := derivation_of_lenProvable h₂
  have b₁' : T ⟹₂ {(φ : Proposition L) ➝ (ψ : Proposition L)} := b₁.cast (by simp)
  have hb₁' : mlen b₁' ≤ k₁ := by rw [mlen_cast]; exact hb₁
  refine lenProvable_of_derivation hL hR (cutMP b₁' b₂) ?_
  have := mlen_cutMP b₁' b₂
  omega

/-- The verum leaf: `⊤` has a proof of length `2 = |⊤| + 1`. -/
theorem lenProvable_verum_of_small (hL : SmallCodes L) (hR : SmallRelCodes L) :
    LenProvable (fbound : ℕ → ℕ) 2 T (⌜(⊤ : Sentence L)⌝ : ℕ) := by
  refine lenProvable_of_derivation hL hR (Derivation2.verum (Γ := {(⊤ : Proposition L)}) (by simp)) ?_
  rw [mlen_verum, sqlen_singleton, flen_verum]

end code

/-! ### At `TAct` — the statements the bounded-GL interface asks for -/

/-- **Bounded D2 (rule form), sharp**: `PA-S` closes under modus ponens at cost
`k₁ + k₂ + 5|φ| + 10|ψ| + 9`. -/
theorem lenProvable_mp_sharp {k₁ k₂ : ℕ} {φ ψ : Sentence LAct}
    (h₁ : LenProvable (fbound : ℕ → ℕ) k₁ TAct (⌜φ ➝ ψ⌝ : ℕ))
    (h₂ : LenProvable (fbound : ℕ → ℕ) k₂ TAct (⌜φ⌝ : ℕ)) :
    LenProvable (fbound : ℕ → ℕ)
      (k₁ + k₂ + 5 * flen (φ : Proposition LAct) + 10 * flen (ψ : Proposition LAct) + 9)
      TAct (⌜ψ⌝ : ℕ) :=
  lenProvable_mp_sharp_of_small smallCodes_LAct smallRelCodes_LAct h₁ h₂

/-- **Bounded D2 (rule form)**: PA-`S` closes under modus ponens at additive cost
`k₁ + k₂ + c₁·(|φ| + |ψ|) + c₀` with `c₁ = 10, c₀ = 9` — a character-count analogue of the
engine's `mp` at cost `m₁ + m₂ + |ψ|`. The engine charges only `|ψ|`; PA-`S` also pays `|φ|`
(the cut formula is copied into the side sequents): a constant-factor departure that any
budget-keeping transfer must absorb (T2-NEG shows atoms are the real obstruction, not this). -/
theorem lenProvable_mp {k₁ k₂ : ℕ} {φ ψ : Sentence LAct}
    (h₁ : LenProvable (fbound : ℕ → ℕ) k₁ TAct (⌜φ ➝ ψ⌝ : ℕ))
    (h₂ : LenProvable (fbound : ℕ → ℕ) k₂ TAct (⌜φ⌝ : ℕ)) :
    LenProvable (fbound : ℕ → ℕ)
      (k₁ + k₂ + 10 * (flen (φ : Proposition LAct) + flen (ψ : Proposition LAct)) + 9)
      TAct (⌜ψ⌝ : ℕ) :=
  lenProvable_fbound_mono (by omega) (lenProvable_mp_sharp h₁ h₂)

/-- The verum leaf at `TAct`: `⊤` has a proof of length `2 = |⊤| + 1`. -/
theorem lenProvable_verum : LenProvable (fbound : ℕ → ℕ) 2 TAct (⌜(⊤ : Sentence LAct)⌝ : ℕ) :=
  lenProvable_verum_of_small smallCodes_LAct smallRelCodes_LAct

end ArithS
