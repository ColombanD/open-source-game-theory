import ArithS.Cut

/-!
# ArithS.CutV — bounded D2 on codes, inside every model of `IΣ₁`

`ArithS.Cut` proves modus ponens for `□_k` at the META level (`V = ℕ`, through quotes of meta
derivations). This module proves the SAME cut on derivation CODES, in every model `V` of
`IΣ₁`, with the budgets `a b : V` object elements — the form the bounded-GL interface
(`Base/BoundedGL.lean`, field D2) needs when the box is `LenProvableV` (`ArithS.BewV`,
`∃ d < fbound k, Proof T d φ ∧ dlen T d ≤ k`).

The construction is the five-sequent cut of `Cut.cutMP`, written with Foundation's internal
node codes (`Proof/Basic.lean:134-152`: `wkRule`, `axL`, `andIntro`, `cutRule`) and their
introduction lemmas (`Derivation.wkRule/axL/andIntro/cutRule`, `Proof/Basic.lean:603-657`):
`cutCode φ ψ d₁ d₂ = cutRule {ψ} (φ → ψ) (wk {ψ, φ→ψ} d₁) (andIntro {ψ, φ ⋏ ∼ψ} φ ∼ψ (wk … d₂) (axL … ψ))`,
using `neg (φ → ψ) = φ ⋏ ∼ψ` on codes (`neg_or`, `IsUFormula.neg_neg`,
`Formula/Functions.lean:88-127`). Its `Proof` is `cutCode_proof`; its length is EXACT
(`dlen_cutCode`, by the `DlenGraph.*_iff` inversion clauses of `ArithS.DerivationLength`:
each node charges its whole conclusion sequent), and bounded by
`dlen d₁ + dlen d₂ + 5|φ| + 10|ψ| + 9` (`dlen_cutCode_le`) — the constants of the meta
`mlen_cutMP`, unchanged. Two V-internal length facts were needed: `formulaLen (neg p) =
formulaLen p` (`formulaLen_neg`, by `IsUFormula` induction) and `setLen (insert p s) ≤
setLen s + formulaLen p` (`setLen_insert_le`, by `IΣ₁` induction on the partial sums).

## The theorems

* `lenDerivable_cut_V` — UNCONDITIONAL, any Δ₁ theory: `LenDerivable T a (φ → ψ) →
  LenDerivable T b φ → LenDerivable T (a + b + 5|φ| + 10|ψ| + 9) ψ`, where
  `LenDerivable T k φ := ∃ d, Proof T d φ ∧ dlen T d ≤ k` is `LenProvableV` WITHOUT the
  code bound.
* `lenProvableV_cut_V_sharp_of` / `lenProvableV_cut_V_sharp` / `lenProvableV_cut_V` — the
  `LenProvableV`-shaped statements (`(5, 10, 9)`, resp. the uniform `c₁ = 10, c₀ = 9` at
  `TAct`), under a NAMED HYPOTHESIS: properness inside `V` (`ProperV V T`: a `T`-proof code of
  length `≤ k` is `< fbound k`; the `_of` form asks it only for the result `ψ` at the new
  budget). `ArithS.Proper` proves properness at `ℕ` through quotes (`quote_derivation_le`);
  no V-generic form exists (it would need the code/length estimates of `Proper.lean` redone
  by internal formula induction — bounds on symbol codes are not available inside `V`), so
  it is stated as a hypothesis, discharged at `V = ℕ` (`properV_nat`, `properV_nat_TAct`).
* `lenProvableV_mono_V` — budget monotonicity of `LenProvableV` inside `V` (`fbound_mono_V`),
  unconditional.
* `cutSentence` — bounded D2 as ONE `ℒₒᵣ`-sentence (`LenDerivable` form, Σ₁ definition
  `lenDerivableDef`); `isigma1_proves_cutSentence : 𝗜𝚺₁ ⊢ cutSentence`,
  `pa_proves_cutSentence : 𝗣𝗔 ⊢ cutSentence` (completeness theorem over the V-generic
  theorem, `Arithmetic.complete`), and `tact_proves_cutSentence : TAct ⊢ lMap emb cutSentence`
  (soundness + `lMap_models_lMap` + `Theory.Proof.complete`).

Imports only modules upstream of `ArithS.Prog`; `LenProvableV` (`ArithS.BewV`) is therefore
not named — its body is written out, and `lenProvableV_numeral`-style restatements are
one-liners downstream.
-/

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {L : Language} [L.Encodable] [L.LORDefinable]

/-! ### `formulaLen` of the de Morgan dual, inside `V` -/

/-- The internal negation preserves the symbol count (`neg` swaps `rel/nrel`, `⋏/⋎`, `∀/∃`). -/
lemma formulaLen_neg {p : V} : IsUFormula L p → formulaLen L (neg L p) = formulaLen L p := by
  apply IsUFormula.ISigma1.sigma1_succ_induction
  · definability
  · intro k R v hR hv; simp [hR, hv]
  · intro k R v hR hv; simp [hR, hv]
  · simp
  · simp
  · intro p q hp hq ihp ihq; simp [hp, hq, hp.neg, hq.neg, ihp, ihq]
  · intro p q hp hq ihp ihq; simp [hp, hq, hp.neg, hq.neg, ihp, ihq]
  · intro p hp ihp; simp [hp, hp.neg, ihp]
  · intro p hp ihp; simp [hp, hp.neg, ihp]

lemma formulaLen_imp {p q : V} (hp : IsUFormula L p) (hq : IsUFormula L q) :
    formulaLen L (Bootstrapping.imp L p q) = formulaLen L p + formulaLen L q + 1 := by
  simp [Bootstrapping.imp, formulaLen_or hp.neg hq, formulaLen_neg hp]

/-! ### `setLen` on `insert`, inside `V` -/

section setLen

/-- The partial sums stabilise once the index passes the set (all members are below it). -/
lemma setLenAux_add_eq (s j : V) : setLenAux L s (s + j) = setLen L s := by
  induction j using ISigma1.sigma1_succ_induction with
  | hP => definability
  | zero => simp [setLen]
  | succ j ih =>
    have hnot : s + j ∉ s := fun hm ↦ absurd (lt_of_mem hm) (not_lt.mpr le_self_add)
    rw [← add_assoc, setLenAux_succ_of_not_mem hnot, ih]

lemma setLenAux_eq_of_le_V {s i : V} (h : s ≤ i) : setLenAux L s i = setLen L s := by
  obtain ⟨j, rfl⟩ := exists_add_of_le h
  exact setLenAux_add_eq s j

lemma setLenAux_insert_of_not_mem_V {x s : V} (hx : x ∉ s) (i : V) :
    (i ≤ x → setLenAux L (insert x s) i = setLenAux L s i) ∧
    (x < i → setLenAux L (insert x s) i = setLenAux L s i + formulaLen L x) := by
  induction i using ISigma1.sigma1_succ_induction with
  | hP => definability
  | zero => simp
  | succ i ih =>
    by_cases hix : i = x
    · subst hix
      refine ⟨fun h ↦ absurd h (not_le.mpr (lt_add_one i)), fun _ ↦ ?_⟩
      rw [setLenAux_succ_of_mem (mem_insert i s), setLenAux_succ_of_not_mem hx, ih.1 (le_refl i)]
    · have hmem : (i ∈ insert x s) ↔ i ∈ s := by simp [hix]
      constructor
      · intro hi
        have hi' : i ≤ x := le_of_lt (lt_of_lt_of_le (lt_add_one i) hi)
        by_cases his : i ∈ s
        · rw [setLenAux_succ_of_mem (hmem.mpr his), setLenAux_succ_of_mem his, ih.1 hi']
        · rw [setLenAux_succ_of_not_mem (fun h ↦ his (hmem.mp h)),
            setLenAux_succ_of_not_mem his, ih.1 hi']
      · intro hi
        have hxi : x < i := lt_of_le_of_ne (lt_succ_iff_le.mp hi) (Ne.symm hix)
        by_cases his : i ∈ s
        · rw [setLenAux_succ_of_mem (hmem.mpr his), setLenAux_succ_of_mem his, ih.2 hxi]
          exact add_right_comm _ _ _
        · rw [setLenAux_succ_of_not_mem (fun h ↦ his (hmem.mp h)),
            setLenAux_succ_of_not_mem his, ih.2 hxi]

lemma setLen_insert_of_not_mem_V {x s : V} (hx : x ∉ s) :
    setLen L (insert x s) = setLen L s + formulaLen L x := by
  have hlt : x < insert x s := lt_of_mem (by simp)
  have hle : s ≤ insert x s := le_of_subset (fun i hi ↦ by simp [hi])
  rw [setLen, (setLenAux_insert_of_not_mem_V hx _).2 hlt, setLenAux_eq_of_le_V hle]

/-- Inserting a formula adds at most its symbol count. -/
lemma setLen_insert_le (x s : V) : setLen L (insert x s) ≤ setLen L s + formulaLen L x := by
  by_cases hx : x ∈ s
  · rw [insert_eq_self_of_mem hx]; exact le_self_add
  · exact le_of_eq (setLen_insert_of_not_mem_V hx)

@[simp] lemma setLen_empty : setLen L (∅ : V) = 0 := by
  simp [setLen, emptyset_def]

@[simp] lemma setLen_singleton (x : V) : setLen L ({x} : V) = formulaLen L x := by
  rw [singleton_eq_insert, setLen_insert_of_not_mem_V (by simp), setLen_empty, zero_add]

end setLen

/-! ### `fbound` is monotone inside `V` -/

lemma fbound_mono_V {a b : V} (h : a ≤ b) : fbound a ≤ fbound b := by
  unfold fbound
  exact add_le_add (exp_monotone_le.mpr (exp_monotone_le.mpr (exp_monotone_le.mpr
    (mul_le_mul_of_nonneg_left h (by simp))))) (le_refl 1)

/-! ### The cut on codes -/

section cut

variable {T : Theory L} [T.Δ₁]

/-- Length-bounded derivability WITHOUT the code bound: `φ` has a `T`-proof code of
length `≤ k`. `LenProvableV T k φ` is this plus `d < fbound k`. -/
def LenDerivable (T : Theory L) [T.Δ₁] (k φ : V) : Prop := ∃ d, Proof T d φ ∧ dlen T d ≤ k

/-- **Properness inside `V`** (a HYPOTHESIS, see the module docstring): every `T`-proof code of
length `≤ k` is below `fbound k`. `proper_of_small` is its instance at `V = ℕ` for sentence
codes. -/
def ProperV (V : Type*) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (T : Theory L) [T.Δ₁] : Prop :=
  ∀ k d φ : V, Proof T d φ → dlen T d ≤ k → d < fbound k

lemma neg_imp_code {φ ψ : V} (hφ : IsUFormula L φ) (hψ : IsUFormula L ψ) :
    neg L (Bootstrapping.imp L φ ψ) = φ ^⋏ neg L ψ := by
  simp [Bootstrapping.imp, neg_or hφ.neg hψ, hφ.neg_neg]

variable (L)

/-- The code of the cut derivation of `{ψ}` from `d₁ : {φ → ψ}` and `d₂ : {φ}` — the same
five-sequent construction as the meta `cutMP`: weaken `d₁` to `{ψ, φ → ψ}`; introduce
`∼(φ → ψ) = φ ⋏ ∼ψ` by `andIntro` from the weakening of `d₂` to `{ψ, φ ⋏ ∼ψ, φ}` and the
closed leaf `{ψ, φ ⋏ ∼ψ, ∼ψ}`; cut on `φ → ψ`. -/
noncomputable def cutCode (φ ψ d₁ d₂ : V) : V :=
  cutRule {ψ} (Bootstrapping.imp L φ ψ)
    (wkRule (insert (Bootstrapping.imp L φ ψ) {ψ}) d₁)
    (andIntro (insert (φ ^⋏ neg L ψ) {ψ}) φ (neg L ψ)
      (wkRule (insert φ (insert (φ ^⋏ neg L ψ) {ψ})) d₂)
      (axL (insert (neg L ψ) (insert (φ ^⋏ neg L ψ) {ψ})) ψ))

variable {L}

/-- The cut code is a `T`-proof of `ψ`. -/
theorem cutCode_proof {φ ψ d₁ d₂ : V} (hφ : IsFormula L φ) (hψ : IsFormula L ψ)
    (h₁ : Proof T d₁ (Bootstrapping.imp L φ ψ)) (h₂ : Proof T d₂ φ) :
    Proof T (cutCode L φ ψ d₁ d₂) ψ := by
  have hS₁ : IsFormulaSet L (insert (φ ^⋏ neg L ψ) ({ψ} : V)) := by simp [hφ, hψ]
  have e₁ : DerivationOf T (wkRule (insert (Bootstrapping.imp L φ ψ) {ψ}) d₁)
      (insert (Bootstrapping.imp L φ ψ) {ψ}) :=
    ⟨by simp, Derivation.wkRule (by simp [hφ, hψ]) (fun x hx ↦ by simp [mem_singleton_iff.mp hx]) h₁⟩
  have e₂ : DerivationOf T (wkRule (insert φ (insert (φ ^⋏ neg L ψ) {ψ})) d₂)
      (insert φ (insert (φ ^⋏ neg L ψ) {ψ})) :=
    ⟨by simp, Derivation.wkRule (by simp [hφ, hψ]) (fun x hx ↦ by simp [mem_singleton_iff.mp hx]) h₂⟩
  have e₃ : DerivationOf T (axL (insert (neg L ψ) (insert (φ ^⋏ neg L ψ) {ψ})) ψ)
      (insert (neg L ψ) (insert (φ ^⋏ neg L ψ) {ψ})) :=
    ⟨by simp, Derivation.axL (by simp [hφ, hψ]) (by simp) (by simp)⟩
  have e₄ : DerivationOf T (andIntro (insert (φ ^⋏ neg L ψ) {ψ}) φ (neg L ψ)
      (wkRule (insert φ (insert (φ ^⋏ neg L ψ) {ψ})) d₂)
      (axL (insert (neg L ψ) (insert (φ ^⋏ neg L ψ) {ψ})) ψ))
      (insert (φ ^⋏ neg L ψ) {ψ}) :=
    ⟨by simp, Derivation.andIntro (by simp) e₂ e₃⟩
  refine ⟨by simp [cutCode], Derivation.cutRule e₁ ?_⟩
  rw [neg_imp_code hφ.isUFormula hψ.isUFormula]
  exact e₄

/-- The exact length of the cut code, node by node (each node charges its whole conclusion). -/
theorem dlen_cutCode {φ ψ d₁ d₂ : V} (hφ : IsFormula L φ) (hψ : IsFormula L ψ)
    (h₁ : Proof T d₁ (Bootstrapping.imp L φ ψ)) (h₂ : Proof T d₂ φ) :
    dlen T (cutCode L φ ψ d₁ d₂) =
      setLen L ({ψ} : V)
      + (setLen L (insert (Bootstrapping.imp L φ ψ) {ψ}) + dlen T d₁ + 1)
      + (setLen L (insert (φ ^⋏ neg L ψ) {ψ})
          + (setLen L (insert φ (insert (φ ^⋏ neg L ψ) {ψ})) + dlen T d₂ + 1)
          + (setLen L (insert (neg L ψ) (insert (φ ^⋏ neg L ψ) {ψ})) + 1) + 1)
      + 1 := by
  apply dlen_eq_of_graph (cutCode_proof hφ hψ h₁ h₂).2
  unfold cutCode
  refine DlenGraph.cutRule_iff.mpr ⟨_, _, DlenGraph.wkRule_iff.mpr ⟨_, dlen_graph h₁.2, rfl⟩, ?_, rfl⟩
  refine DlenGraph.andIntro_iff.mpr ⟨_, _, DlenGraph.wkRule_iff.mpr ⟨_, dlen_graph h₂.2, rfl⟩,
    DlenGraph.axL_iff.mpr rfl, rfl⟩

/-- **Bounded D2 on codes, sharp**: `dlen (cutCode) ≤ dlen d₁ + dlen d₂ + 5|φ| + 10|ψ| + 9`. -/
theorem dlen_cutCode_le {φ ψ d₁ d₂ : V} (hφ : IsFormula L φ) (hψ : IsFormula L ψ)
    (h₁ : Proof T d₁ (Bootstrapping.imp L φ ψ)) (h₂ : Proof T d₂ φ) :
    dlen T (cutCode L φ ψ d₁ d₂) ≤
      dlen T d₁ + dlen T d₂ + 5 * formulaLen L φ + 10 * formulaLen L ψ + 9 := by
  have hφ' := hφ.isUFormula
  have hψ' := hψ.isUFormula
  have hS₁ : setLen L (insert (φ ^⋏ neg L ψ) ({ψ} : V)) ≤
      formulaLen L φ + 2 * formulaLen L ψ + 1 := by
    have := setLen_insert_le (L := L) (φ ^⋏ neg L ψ) {ψ}
    rw [setLen_singleton, formulaLen_and hφ' hψ'.neg, formulaLen_neg hψ'] at this
    exact le_trans this (le_of_eq (by ring))
  have hI : setLen L (insert (Bootstrapping.imp L φ ψ) ({ψ} : V)) ≤
      formulaLen L φ + 2 * formulaLen L ψ + 1 := by
    have := setLen_insert_le (L := L) (Bootstrapping.imp L φ ψ) {ψ}
    rw [setLen_singleton, formulaLen_imp hφ' hψ'] at this
    exact le_trans this (le_of_eq (by ring))
  have hA : setLen L (insert φ (insert (φ ^⋏ neg L ψ) ({ψ} : V))) ≤
      2 * formulaLen L φ + 2 * formulaLen L ψ + 1 :=
    le_trans (setLen_insert_le _ _) (le_trans (add_le_add hS₁ (le_refl _)) (le_of_eq (by ring)))
  have hB : setLen L (insert (neg L ψ) (insert (φ ^⋏ neg L ψ) ({ψ} : V))) ≤
      formulaLen L φ + 3 * formulaLen L ψ + 1 := by
    refine le_trans (setLen_insert_le _ _) ?_
    rw [formulaLen_neg hψ']
    exact le_trans (add_le_add hS₁ (le_refl _)) (le_of_eq (by ring))
  rw [dlen_cutCode hφ hψ h₁ h₂, setLen_singleton]
  calc formulaLen L ψ
      + (setLen L (insert (Bootstrapping.imp L φ ψ) {ψ}) + dlen T d₁ + 1)
      + (setLen L (insert (φ ^⋏ neg L ψ) {ψ})
          + (setLen L (insert φ (insert (φ ^⋏ neg L ψ) {ψ})) + dlen T d₂ + 1)
          + (setLen L (insert (neg L ψ) (insert (φ ^⋏ neg L ψ) {ψ})) + 1) + 1)
      + 1
      ≤ formulaLen L ψ
      + ((formulaLen L φ + 2 * formulaLen L ψ + 1) + dlen T d₁ + 1)
      + ((formulaLen L φ + 2 * formulaLen L ψ + 1)
          + ((2 * formulaLen L φ + 2 * formulaLen L ψ + 1) + dlen T d₂ + 1)
          + ((formulaLen L φ + 3 * formulaLen L ψ + 1) + 1) + 1)
      + 1 := by gcongr
    _ = dlen T d₁ + dlen T d₂ + 5 * formulaLen L φ + 10 * formulaLen L ψ + 9 := by ring

end cut

/-! ### The theorems -/

section theorems

variable {T : Theory L} [T.Δ₁]

lemma lenDerivable_mono_V {a b φ : V} (h : a ≤ b) : LenDerivable T a φ → LenDerivable T b φ := by
  rintro ⟨d, hd, hk⟩; exact ⟨d, hd, le_trans hk h⟩

/-- Budget monotonicity of `LenProvableV` (`∃ d < fbound k, Proof T d φ ∧ dlen T d ≤ k`) inside
`V`: `fbound` is monotone. Unconditional. -/
theorem lenProvableV_mono_V {a b φ : V} (h : a ≤ b)
    (H : ∃ d < fbound a, Proof T d φ ∧ dlen T d ≤ a) :
    ∃ d < fbound b, Proof T d φ ∧ dlen T d ≤ b := by
  obtain ⟨d, hd, hp, hk⟩ := H
  exact ⟨d, lt_of_lt_of_le hd (fbound_mono_V h), hp, le_trans hk h⟩

/-- **Bounded D2 on codes, sharp, unconditional** (any Δ₁ theory, every model of `IΣ₁`):
from a proof code of `φ → ψ` of length `≤ a` and one of `φ` of length `≤ b`, a proof code of
`ψ` of length `≤ a + b + 5|φ| + 10|ψ| + 9`. -/
theorem lenDerivable_cut_V {a b φ ψ : V} (hφ : IsFormula L φ) (hψ : IsFormula L ψ)
    (h₁ : LenDerivable T a (Bootstrapping.imp L φ ψ)) (h₂ : LenDerivable T b φ) :
    LenDerivable T (a + b + 5 * formulaLen L φ + 10 * formulaLen L ψ + 9) ψ := by
  obtain ⟨d₁, hd₁, ha⟩ := h₁
  obtain ⟨d₂, hd₂, hb⟩ := h₂
  refine ⟨cutCode L φ ψ d₁ d₂, cutCode_proof hφ hψ hd₁ hd₂, ?_⟩
  refine le_trans (dlen_cutCode_le hφ hψ hd₁ hd₂) ?_
  gcongr

/-- **Bounded D2 on codes for `LenProvableV`, sharp**, under properness of the RESULT only:
`hP` says that a `T`-proof code of `ψ` of length `≤ k'` (the new budget) is below `fbound k'`. -/
theorem lenProvableV_cut_V_sharp_of {a b φ ψ : V} (hφ : IsFormula L φ) (hψ : IsFormula L ψ)
    (hP : ∀ d, Proof T d ψ → dlen T d ≤ a + b + 5 * formulaLen L φ + 10 * formulaLen L ψ + 9 →
      d < fbound (a + b + 5 * formulaLen L φ + 10 * formulaLen L ψ + 9))
    (h₁ : ∃ d < fbound a, Proof T d (Bootstrapping.imp L φ ψ) ∧ dlen T d ≤ a)
    (h₂ : ∃ d < fbound b, Proof T d φ ∧ dlen T d ≤ b) :
    ∃ d < fbound (a + b + 5 * formulaLen L φ + 10 * formulaLen L ψ + 9),
      Proof T d ψ ∧ dlen T d ≤ a + b + 5 * formulaLen L φ + 10 * formulaLen L ψ + 9 := by
  obtain ⟨d₁, _, hd₁, ha⟩ := h₁
  obtain ⟨d₂, _, hd₂, hb⟩ := h₂
  obtain ⟨d, hd, hk⟩ := lenDerivable_cut_V hφ hψ ⟨d₁, hd₁, ha⟩ ⟨d₂, hd₂, hb⟩
  exact ⟨d, hP d hd hk, hd, hk⟩

/-- The same under the uniform hypothesis `ProperV V T`. -/
theorem lenProvableV_cut_V_sharp (hP : ProperV V T) {a b φ ψ : V}
    (hφ : IsFormula L φ) (hψ : IsFormula L ψ)
    (h₁ : ∃ d < fbound a, Proof T d (Bootstrapping.imp L φ ψ) ∧ dlen T d ≤ a)
    (h₂ : ∃ d < fbound b, Proof T d φ ∧ dlen T d ≤ b) :
    ∃ d < fbound (a + b + 5 * formulaLen L φ + 10 * formulaLen L ψ + 9),
      Proof T d ψ ∧ dlen T d ≤ a + b + 5 * formulaLen L φ + 10 * formulaLen L ψ + 9 :=
  lenProvableV_cut_V_sharp_of hφ hψ (fun d hd hk ↦ hP _ d ψ hd hk) h₁ h₂

/-- `5|φ| + 10|ψ| + 9 ≤ 10(|φ| + |ψ|) + 9`, the step from the sharp to the uniform constants. -/
lemma sharp_le_uniform (a b x y : V) :
    a + b + 5 * x + 10 * y + 9 ≤ a + b + 10 * (x + y) + 9 := by
  have h5 : 5 * x ≤ 10 * x :=
    calc 5 * x ≤ 5 * x + 5 * x := le_self_add
      _ = 10 * x := by ring
  calc a + b + 5 * x + 10 * y + 9 ≤ a + b + 10 * x + 10 * y + 9 := by gcongr
    _ = a + b + 10 * (x + y) + 9 := by ring

end theorems

/-! ### Properness inside `V` at `V = ℕ` -/

section nat

variable [L.DecidableEq] {T : Theory L} [T.Δ₁]

/-- At `V = ℕ` the properness hypothesis is a THEOREM (`quote_derivation_le` through
`Proof.sound'`): a proof code of length `≤ k` is below `fbound k`. -/
theorem properV_nat (hL : SmallCodes L) (hR : SmallRelCodes L) : ProperV ℕ T := by
  intro k d φ hd hk
  have hF : IsFormula L φ := by simpa using hd.isFormulaSet
  obtain ⟨F, rfl⟩ := hF.sound
  obtain ⟨b, rfl⟩ := Proof.sound' hd
  rw [dlen_quote] at hk
  rw [fbound_nat]
  have hk' : mlen b ≤ k := (le_def.mp hk).elim Nat.le_of_eq Nat.le_of_lt
  exact Nat.lt_succ_of_le (le_trans (quote_derivation_le hL hR b) (F_mono (Nat.mul_le_mul_left 12 hk')))

theorem properV_nat_TAct : ProperV ℕ TAct := properV_nat smallCodes_LAct smallRelCodes_LAct

end nat

/-! ### At `TAct` — the statements the bounded-GL interface asks for -/

section TAct

/-- **Bounded D2 on codes at `TAct`, inside every model of `IΣ₁`** (`LenProvableV`-shaped,
uniform constants `c₁ = 10, c₀ = 9`), under properness inside `V` (`ProperV V TAct`, a
theorem at `V = ℕ`: `properV_nat_TAct`). -/
theorem lenProvableV_cut_V (hP : ProperV V TAct) (a b φ ψ : V)
    (hφ : IsSemiformula LAct 0 φ) (hψ : IsSemiformula LAct 0 ψ) :
    (∃ d < fbound a, Proof TAct d (Bootstrapping.imp LAct φ ψ) ∧ dlen TAct d ≤ a) →
    (∃ d < fbound b, Proof TAct d φ ∧ dlen TAct d ≤ b) →
    ∃ d < fbound (a + b + 10 * (formulaLen LAct φ + formulaLen LAct ψ) + 9),
      Proof TAct d ψ ∧ dlen TAct d ≤ a + b + 10 * (formulaLen LAct φ + formulaLen LAct ψ) + 9 :=
  fun h₁ h₂ ↦ lenProvableV_mono_V (sharp_le_uniform _ _ _ _) (lenProvableV_cut_V_sharp hP hφ hψ h₁ h₂)

/-- **Bounded D2 on codes at `TAct`, unconditional** (no code bound in the predicate):
`LenDerivable`, uniform constants. -/
theorem lenDerivable_cut_V_TAct (a b φ ψ : V)
    (hφ : IsSemiformula LAct 0 φ) (hψ : IsSemiformula LAct 0 ψ) :
    LenDerivable TAct a (Bootstrapping.imp LAct φ ψ) → LenDerivable TAct b φ →
    LenDerivable TAct (a + b + 10 * (formulaLen LAct φ + formulaLen LAct ψ) + 9) ψ :=
  fun h₁ h₂ ↦ lenDerivable_mono_V (sharp_le_uniform _ _ _ _) (lenDerivable_cut_V hφ hψ h₁ h₂)

end TAct

/-! ### Bounded D2 as ONE arithmetic sentence, provable in `IΣ₁` (hence in `PA`) -/

section sentence

variable (T : Theory L) [T.Δ₁]

/-- `LenDerivable T k φ` as a Σ₁ semisentence (`k φ`). -/
noncomputable def lenDerivableDef : 𝚺₁.Semisentence 2 := .mkSigma
  “k φ. ∃ d, !(proof T).sigma d φ ∧ ∃ n, !(dlenDef T) n d ∧ n ≤ k”

instance LenDerivable.defined : 𝚺₁-Relation[V] (LenDerivable T) via lenDerivableDef T :=
  .mk fun v ↦ by
    simp [lenDerivableDef, HierarchySymbol.Semiformula.val_sigma,
      (Proof.defined (T := T)).df, dlen_defined.iff, LenDerivable]

instance LenDerivable.definable : 𝚺₁-Relation[V] (LenDerivable T) :=
  (LenDerivable.defined T).to_definable

variable {T}

/-- **Bounded D2 on codes as a single `ℒₒᵣ`-sentence**: "for all `a b x y`, if `x, y` are
formula codes, `x → y` has a `TAct`-proof of length `≤ a` and `x` one of length `≤ b`, then
`y` has one of length `≤ a + b + 5|x| + 10|y| + 9`." -/
noncomputable def cutSentence : ArithmeticSentence :=
  “∀ a b x y, !(isSemiformula LAct).pi 0 x → !(isSemiformula LAct).pi 0 y →
    ∀ i, !(impGraph LAct) i x y → !(lenDerivableDef TAct) a i → !(lenDerivableDef TAct) b x →
    ∀ lx, !(formulaLenGraph LAct) lx x → ∀ ly, !(formulaLenGraph LAct) ly y →
    !(lenDerivableDef TAct) (a + b + 5 * lx + 10 * ly + 9) y”

lemma models_cutSentence :
    V↓[ℒₒᵣ] ⊧ cutSentence ↔
    ∀ a b x y : V, IsFormula LAct x → IsFormula LAct y →
      LenDerivable TAct a (Bootstrapping.imp LAct x y) → LenDerivable TAct b x →
      LenDerivable TAct (a + b + 5 * formulaLen LAct x + 10 * formulaLen LAct y + 9) y := by
  simp [cutSentence, models_iff, (IsSemiformula.defined (V := V) (L := LAct)).proper.iff',
    imp.defined.iff, formulaLen.defined.iff, (LenDerivable.defined (V := V) TAct).iff,
    numeral_eq_natCast]

/-- **`IΣ₁` proves bounded D2 on codes** (by the completeness theorem over
`lenDerivable_cut_V`). -/
theorem isigma1_proves_cutSentence : 𝗜𝚺₁ ⊢ cutSentence :=
  complete 𝗜𝚺₁ _ fun (V : Type) _ _ ↦ models_cutSentence.mpr fun _ _ _ _ hx hy h₁ h₂ ↦
    lenDerivable_cut_V hx hy h₁ h₂

/-- **`PA` proves bounded D2 on codes.** -/
theorem pa_proves_cutSentence : 𝗣𝗔 ⊢ cutSentence :=
  complete 𝗣𝗔 _ fun (V : Type) _ _ ↦
    haveI : V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    models_cutSentence.mpr fun _ _ _ _ hx hy h₁ h₂ ↦ lenDerivable_cut_V hx hy h₁ h₂

/-- **`TAct` proves bounded D2 on codes** (the `ℒₒᵣ`-sentence embedded along `emb`): soundness
of `𝗣𝗔 ⊢ cutSentence`, transported along `emb` (`lMap_models_lMap`), and the completeness
theorem for `LAct`-theories (`TAct ⊇ Theory.lMap emb 𝗣𝗔`). -/
theorem tact_proves_cutSentence : TAct ⊢ Semiformula.lMap LAct.emb cutSentence := by
  refine Theory.Proof.complete fun (s : Struc.{0} LAct) hs ↦ ?_
  have hPA : s ⊧* Theory.lMap LAct.emb 𝗣𝗔 :=
    Semantics.ModelsSet.of_subset hs (fun x hx ↦ Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ hx))
  exact lMap_models_lMap (Theory.Proof.sound pa_proves_cutSentence) hPA

end sentence

end ArithS
