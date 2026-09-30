import ArithS.Theory.Symmetry
import ArithS.Length.ProofLength

/-!
# ArithS.Cut — bounded D2 in rule form: modus ponens with exact length accounting

**Bounded D2 (rule form): PA-`S` closes under modus ponens at additive cost
`k₁ + k₂ + c₁·(|φ| + |ψ|) + c₀`**, a character-count analogue of the engine's `mp` at cost
`m₁ + m₂ + |ψ|` — the first field of the bounded-GL interface (`Base/BoundedGL.lean`) that the
arithmetized system satisfies (roadmap M4, "D2 / cut").

The construction is one `cut` on `φ 🡒 ψ` in Foundation's one-sided calculus `Derivation2`
(`cutMP`): weaken the proof of `φ 🡒 ψ` to `{ψ, φ 🡒 ψ}`; on the other side, `∼(φ 🡒 ψ) = φ ⋏ ∼ψ`
is introduced by `and` from a weakening of the proof of `φ` and the closed leaf `{ψ, ∼ψ}`.
Every node charges its whole conclusion sequent (`proofLenMeta`), which gives the exact bound
`proofLenMeta d₁ + proofLenMeta d₂ + 5|φ| + 10|ψ| + 9` (`proofLenMeta_cutMP`); the uniform constants are
`c₁ = 10, c₀ = 9`.

Note that the engine charges only `|ψ|` while PA-`S` also pays `|φ|`: the cut formula is
copied into the side sequents. This is a constant-factor departure that any budget-keeping
transfer must absorb (T2-NEG shows the atoms — evaluation steps and cheap citations — are the
real obstruction, not this).

Code level: a length-bounded code is the code of a meta proof (`Proof.sound'`), the meta cut
has the bounded `proofLenMeta`, quoting it back gives a code (`derivation_quote`) of that length
(`proofLen_quote`) and, by properness (`quote_derivation_le`), below `codeBound` of the new budget —
the pattern of `lenBoxNat_codeBound_swap`. Also here: `codeBound` is monotone, so
`LenBoxNat codeBound` is budget-monotone (`lenBoxNat_codeBound_mono`), and the `verum` leaf
(`lenBoxNat_verum`) as the sanity instance.
-/

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus
open LAct

/-! ### `formulaLenMeta` and `sequentLenMeta` on the shapes the cut produces -/

section formulaLenMeta

variable {L : Language} [L.DecidableEq]

omit [L.DecidableEq] in
/-- The de Morgan dual has the same symbol count (`∼` swaps `rel/nrel`, `⋏/⋎`, `∀/∃`). -/
lemma formulaLenMeta_neg {n : ℕ} (φ : Semiproposition L n) : formulaLenMeta (∼φ) = formulaLenMeta φ := by
  induction φ with
  | rel R v => rfl
  | nrel R v => rfl
  | verum => rfl
  | falsum => rfl
  | and φ ψ ihφ ihψ =>
    rw [Semiformula.neg_eq] at ihφ ihψ ⊢
    simp only [Semiformula.neg, formulaLenMeta, ihφ, ihψ]
  | or φ ψ ihφ ihψ =>
    rw [Semiformula.neg_eq] at ihφ ihψ ⊢
    simp only [Semiformula.neg, formulaLenMeta, ihφ, ihψ]
  | all φ ih =>
    rw [Semiformula.neg_eq] at ih ⊢
    simp only [Semiformula.neg, formulaLenMeta, ih]
  | exs φ ih =>
    rw [Semiformula.neg_eq] at ih ⊢
    simp only [Semiformula.neg, formulaLenMeta, ih]

omit [L.DecidableEq] in
/-- `φ 🡒 ψ` is `∼φ ⋎ ψ`: one symbol more than its parts. -/
lemma formulaLenMeta_imply {n : ℕ} (φ ψ : Semiproposition L n) : formulaLenMeta (φ 🡒 ψ) = formulaLenMeta φ + formulaLenMeta ψ + 1 := by
  rw [Semiformula.imp_eq, formulaLenMeta_or, formulaLenMeta_neg]

omit [L.DecidableEq] in
lemma sequentLenMeta_singleton (φ : Proposition L) : sequentLenMeta ({φ} : Finset (Proposition L)) = formulaLenMeta φ :=
  Finset.sum_singleton _ _

/-- Inserting a formula adds at most its symbol count (exactly, unless it was already there). -/
lemma sequentLenMeta_insert_le (φ : Proposition L) (Γ : Finset (Proposition L)) :
    sequentLenMeta (insert φ Γ) ≤ formulaLenMeta φ + sequentLenMeta Γ := by
  by_cases h : φ ∈ Γ
  · rw [Finset.insert_eq_of_mem h]; exact Nat.le_add_left _ _
  · rw [sequentLenMeta, Finset.sum_insert h]

end formulaLenMeta

/-! ### `proofLenMeta` of the basic constructions -/

section proofLenMeta

variable {L : Language} [L.DecidableEq] {T : Theory L}

lemma proofLenMeta_closed (Γ : Finset (Proposition L)) (φ : Proposition L) (h : φ ∈ Γ) (hn : ∼φ ∈ Γ) :
    proofLenMeta (Derivation2.closed (T := T) Γ φ h hn) = sequentLenMeta Γ + 1 := by simp [proofLenMeta]

lemma proofLenMeta_verum {Γ : Finset (Proposition L)} (h : ⊤ ∈ Γ) :
    proofLenMeta (Derivation2.verum (T := T) h) = sequentLenMeta Γ + 1 := by simp [proofLenMeta]

lemma proofLenMeta_wk {Δ Γ : Finset (Proposition L)} (d : T ⟹₂ Δ) (ss : Δ ⊆ Γ) :
    proofLenMeta (Derivation2.wk d ss) = sequentLenMeta Γ + proofLenMeta d + 1 := by simp [proofLenMeta]

lemma proofLenMeta_and {Γ : Finset (Proposition L)} {φ ψ : Proposition L} (h : φ ⋏ ψ ∈ Γ)
    (d₁ : T ⟹₂ insert φ Γ) (d₂ : T ⟹₂ insert ψ Γ) :
    proofLenMeta (Derivation2.and h d₁ d₂) = sequentLenMeta Γ + proofLenMeta d₁ + proofLenMeta d₂ + 1 := by simp [proofLenMeta]

lemma proofLenMeta_cut {Γ : Finset (Proposition L)} {φ : Proposition L}
    (d₁ : T ⟹₂ insert φ Γ) (d₂ : T ⟹₂ insert (∼φ) Γ) :
    proofLenMeta (Derivation2.cut d₁ d₂) = sequentLenMeta Γ + proofLenMeta d₁ + proofLenMeta d₂ + 1 := by simp [proofLenMeta]

/-! ### The cut construction -/

/-- Modus ponens as a `Derivation2`: from `{φ 🡒 ψ}` and `{φ}` derive `{ψ}` by one `cut` on
`φ 🡒 ψ` — the left premise is the weakened proof of `φ 🡒 ψ`, the right one introduces
`∼(φ 🡒 ψ) = φ ⋏ ∼ψ` from the weakened proof of `φ` and the closed leaf `{ψ, ∼ψ}`. -/
noncomputable def cutMP {φ ψ : Proposition L} (d₁ : T ⟹₂ {φ 🡒 ψ}) (d₂ : T ⟹₂ {φ}) :
    T ⟹₂ {ψ} :=
  Derivation2.cut (Γ := {ψ}) (φ := φ 🡒 ψ)
    (Derivation2.wk d₁ (by simp))
    (Derivation2.and (φ := φ) (ψ := ∼ψ) (by simp [Semiformula.imp_eq])
      (Derivation2.wk d₂ (by simp))
      (Derivation2.closed _ ψ (by simp) (by simp)))

/-- **Exact length accounting for the cut**: `5|φ| + 10|ψ| + 9` on top of the premises. -/
theorem proofLenMeta_cutMP {φ ψ : Proposition L} (d₁ : T ⟹₂ {φ 🡒 ψ}) (d₂ : T ⟹₂ {φ}) :
    proofLenMeta (cutMP d₁ d₂) ≤ proofLenMeta d₁ + proofLenMeta d₂ + 5 * formulaLenMeta φ + 10 * formulaLenMeta ψ + 9 := by
  unfold cutMP
  rw [proofLenMeta_cut, proofLenMeta_wk, proofLenMeta_and, proofLenMeta_wk, proofLenMeta_closed]
  have hψ : sequentLenMeta ({ψ} : Finset (Proposition L)) = formulaLenMeta ψ := sequentLenMeta_singleton ψ
  have h₁ : sequentLenMeta (insert (φ 🡒 ψ) {ψ}) ≤ formulaLenMeta φ + formulaLenMeta ψ + 1 + formulaLenMeta ψ := by
    have := sequentLenMeta_insert_le (φ 🡒 ψ) {ψ}
    rwa [formulaLenMeta_imply, hψ] at this
  have h₂ : sequentLenMeta (insert (∼(φ 🡒 ψ)) {ψ}) ≤ formulaLenMeta φ + formulaLenMeta ψ + 1 + formulaLenMeta ψ := by
    have := sequentLenMeta_insert_le (∼(φ 🡒 ψ)) {ψ}
    rwa [formulaLenMeta_neg, formulaLenMeta_imply, hψ] at this
  have h₃ : sequentLenMeta (insert φ (insert (∼(φ 🡒 ψ)) {ψ})) ≤
      formulaLenMeta φ + sequentLenMeta (insert (∼(φ 🡒 ψ)) {ψ}) := sequentLenMeta_insert_le _ _
  have h₄ : sequentLenMeta (insert (∼ψ) (insert (∼(φ 🡒 ψ)) {ψ})) ≤
      formulaLenMeta ψ + sequentLenMeta (insert (∼(φ 🡒 ψ)) {ψ}) := by
    have := sequentLenMeta_insert_le (∼ψ) (insert (∼(φ 🡒 ψ)) {ψ})
    rwa [formulaLenMeta_neg] at this
  omega

end proofLenMeta

/-! ### Code level, at `ℕ` -/

section code

variable {L : Language} [L.DecidableEq] [L.Encodable] [L.LORDefinable]
variable {T : Theory L} [T.Δ₁]

omit [L.DecidableEq] in
/-- Budget monotonicity of `□_k` for the concrete bound: `codeBound` (three exponentials of
`12 k`, plus one) is monotone. -/
theorem lenBoxNat_codeBound_mono {k k' : ℕ} (h : k ≤ k') {φ : ℕ} :
    LenBoxNat (codeBound : ℕ → ℕ) k T φ → LenBoxNat (codeBound : ℕ → ℕ) k' T φ :=
  LenBoxNat.mono (fun a b hab ↦ by
    have hab' : a ≤ b := by
      rcases le_def.mp hab with h | h
      · exact Nat.le_of_eq h
      · exact Nat.le_of_lt h
    rw [codeBound_nat, codeBound_nat]
    exact le_def.mpr (Nat.lt_or_eq_of_le
      (Nat.succ_le_succ (F_mono (Nat.mul_le_mul_left 12 hab')))).symm) h

/-- A meta derivation of `{σ}` of length `≤ k` is a `LenBoxNat codeBound k` witness (the
quote-back step shared by every rule below). -/
theorem lenBoxNat_of_derivation (hL : SmallCodes L) (hR : SmallRelCodes L)
    {σ : Sentence L} {k : ℕ} (b : T ⟹₂ {(σ : Proposition L)}) (hb : proofLenMeta b ≤ k) :
    LenBoxNat (codeBound : ℕ → ℕ) k T (⌜σ⌝ : ℕ) := by
  have e : (ORingStructure.numeral k : ℕ) = k := by simp
  refine ⟨⌜b⌝, ?_, ⟨?_, derivation_quote b⟩, ?_⟩
  · rw [e, codeBound_nat]
    exact Nat.lt_succ_of_le (le_trans (quote_derivation_le hL hR b)
      (F_mono (Nat.mul_le_mul_left 12 hb)))
  · rw [fstIdx_quote b, Sentence.quote_def]
    exact Derivation2.Sequent.quote_singleton _
  · rw [proofLen_quote, e]
    exact le_def.mpr (Nat.lt_or_eq_of_le hb).symm

/-- The converse direction: a `LenBoxNat codeBound k` witness is the code of a meta derivation
of length `≤ k` (`Proof.sound'` + `proofLen_quote`). -/
theorem derivation_of_lenBoxNat {σ : Sentence L} {k : ℕ}
    (h : LenBoxNat (codeBound : ℕ → ℕ) k T (⌜σ⌝ : ℕ)) :
    ∃ b : T ⟹₂ {(σ : Proposition L)}, proofLenMeta b ≤ k := by
  rcases h with ⟨d, _, hd, hk⟩
  have e : (ORingStructure.numeral k : ℕ) = k := by simp
  rw [Sentence.quote_def] at hd
  obtain ⟨b, rfl⟩ := Proof.sound' hd
  rw [proofLen_quote, e] at hk
  refine ⟨b, ?_⟩
  rcases le_def.mp hk with h | h
  · exact Nat.le_of_eq h
  · exact Nat.le_of_lt h

/-- **Bounded D2, rule form, sharp constants** (generic `L`, `T` with small symbol codes). -/
theorem lenBoxNat_mp_sharp_of_small (hL : SmallCodes L) (hR : SmallRelCodes L)
    {k₁ k₂ : ℕ} {φ ψ : Sentence L}
    (h₁ : LenBoxNat (codeBound : ℕ → ℕ) k₁ T (⌜φ 🡒 ψ⌝ : ℕ))
    (h₂ : LenBoxNat (codeBound : ℕ → ℕ) k₂ T (⌜φ⌝ : ℕ)) :
    LenBoxNat (codeBound : ℕ → ℕ)
      (k₁ + k₂ + 5 * formulaLenMeta (φ : Proposition L) + 10 * formulaLenMeta (ψ : Proposition L) + 9)
      T (⌜ψ⌝ : ℕ) := by
  obtain ⟨b₁, hb₁⟩ := derivation_of_lenBoxNat h₁
  obtain ⟨b₂, hb₂⟩ := derivation_of_lenBoxNat h₂
  obtain ⟨b₁', hb₁'⟩ : ∃ b : T ⟹₂ {(φ : Proposition L) 🡒 (ψ : Proposition L)}, proofLenMeta b ≤ k₁ :=
    ⟨b₁.cast (by simp), by rw [proofLenMeta_cast]; exact hb₁⟩
  refine lenBoxNat_of_derivation hL hR (cutMP b₁' b₂) ?_
  have := proofLenMeta_cutMP b₁' b₂
  omega

/-- The verum leaf: `⊤` has a proof of length `2 = |⊤| + 1`. -/
theorem lenBoxNat_verum_of_small (hL : SmallCodes L) (hR : SmallRelCodes L) :
    LenBoxNat (codeBound : ℕ → ℕ) 2 T (⌜(⊤ : Sentence L)⌝ : ℕ) := by
  refine lenBoxNat_of_derivation hL hR
    (Derivation2.verum (T := T) (Γ := {((⊤ : Sentence L) : Proposition L)}) (by simp)) ?_
  simp [proofLenMeta]

end code

/-! ### At `TAct` — the statements the bounded-GL interface asks for -/

/-- **Bounded D2 (rule form), sharp**: `PA-S` closes under modus ponens at cost
`k₁ + k₂ + 5|φ| + 10|ψ| + 9`. -/
theorem lenBoxNat_mp_sharp {k₁ k₂ : ℕ} {φ ψ : Sentence LAct}
    (h₁ : LenBoxNat (codeBound : ℕ → ℕ) k₁ TAct (⌜φ 🡒 ψ⌝ : ℕ))
    (h₂ : LenBoxNat (codeBound : ℕ → ℕ) k₂ TAct (⌜φ⌝ : ℕ)) :
    LenBoxNat (codeBound : ℕ → ℕ)
      (k₁ + k₂ + 5 * formulaLenMeta (φ : Proposition LAct) + 10 * formulaLenMeta (ψ : Proposition LAct) + 9)
      TAct (⌜ψ⌝ : ℕ) :=
  lenBoxNat_mp_sharp_of_small smallCodes_LAct smallRelCodes_LAct h₁ h₂

/-- **Bounded D2 (rule form)**: PA-`S` closes under modus ponens at additive cost
`k₁ + k₂ + c₁·(|φ| + |ψ|) + c₀` with `c₁ = 10, c₀ = 9` — a character-count analogue of the
engine's `mp` at cost `m₁ + m₂ + |ψ|`. The engine charges only `|ψ|`; PA-`S` also pays `|φ|`
(the cut formula is copied into the side sequents): a constant-factor departure that any
budget-keeping transfer must absorb (T2-NEG shows atoms are the real obstruction, not this). -/
theorem lenBoxNat_mp {k₁ k₂ : ℕ} {φ ψ : Sentence LAct}
    (h₁ : LenBoxNat (codeBound : ℕ → ℕ) k₁ TAct (⌜φ 🡒 ψ⌝ : ℕ))
    (h₂ : LenBoxNat (codeBound : ℕ → ℕ) k₂ TAct (⌜φ⌝ : ℕ)) :
    LenBoxNat (codeBound : ℕ → ℕ)
      (k₁ + k₂ + 10 * (formulaLenMeta (φ : Proposition LAct) + formulaLenMeta (ψ : Proposition LAct)) + 9)
      TAct (⌜ψ⌝ : ℕ) :=
  lenBoxNat_codeBound_mono (by omega) (lenBoxNat_mp_sharp h₁ h₂)

/-- The verum leaf at `TAct`: `⊤` has a proof of length `2 = |⊤| + 1`. -/
theorem lenBoxNat_verum : LenBoxNat (codeBound : ℕ → ℕ) 2 TAct (⌜(⊤ : Sentence LAct)⌝ : ℕ) :=
  lenBoxNat_verum_of_small smallCodes_LAct smallRelCodes_LAct

end ArithS
