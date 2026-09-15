import ArithS.Necessitation.NumIdRows

/-!
# ArithS.Necessitation.BnumSteps — the bit-wise certification of `bnum k` (`Pin.BnumOracle`)

`DESIGN_fragments.md` §7.1 step 1. From the term dossier of the binary numeral `bnum k` at `&j`
(`DossT walkPieces Γ 0 (bnum k) j`), a shift-free step list `bnumSteps Wn Wd T k j` leaves
`bnumFact &j (bnum k)` — the object-level certificate "`&j` is the binary numeral of `k`", one Horn step
per bit (rows `bnumZeroCert`/`bnumOneCert`/`bnumEvenCert`/`bnumOddOfEven` of `NumIdRows.lean`) plus, per
bit `m ≥ 1`, the `sLemma` `𝟏 ≤ bnum m` (`NumSteps.oneLe_proof`, a closed `NumSteps` derivation) and, at an
even bit, the identification of the two eigenvariables of `𝟐 = 𝟏 ^+ 𝟏` (`eqRefl`/`eqOfFunc`/`eqRefl`/
`congAdj`, `Layout` rows `41/71/59`, read through the piece-table chain down to `layoutPieces`).

* §0 the offsets and the two tails `bnEvenTail`/`bnOddTop` as Σ₁ functions (explicit `Def`s);
* §1 the producer: a `Fixpoint` on `⟪k, j, y⟫` over the bits of `k` (parameters `Wn Wd T c₁ c₂`, `c₁ c₂`
  the dossier counts of `𝟏` and `𝟐`), `BnGraph`, the case lemma, existence (Σ₁ motive, offsets bounded);
  `bnumSteps` by `Classical.choose` (no uniqueness needed — every statement runs over the graph);
* §2 `bnumSteps_ok`: applicable at cap `9`, cut-admitting, SHIFT-FREE, `len ≤ 8‖k‖ + 1`, `SizeOK`, and the
  fact `bnumFact &j (bnum k)` in the final context (Π₁ order induction on `k`);
* §3 `bnumOracle_of : NumTableOK tblN … → BnumOracle tbl E k Cb` with the explicit standard `Cb`.

Offsets of the dossier of `bnum (2m) = 𝟐 ^* bnum m = ^func 2 1 ?[𝟐, bnum m]` at `&j` (`Cert.dossT_func`,
`dossV_succ`): `funcFact &j (cT 2) (cT 1) &(j+1)`; `adjFact &(j+1) &(j+2) &(j+2+c₂)`; the dossier of `𝟐` at
`j+2`: `funcFact &(j+2) (cT 2) 𝟎 &(j+3)`, `adjFact &(j+3) &(j+4) &(j+4+c₁)`, `funcFact &(j+4) 𝟎 (cT 1) 𝟎`,
`adjFact &(j+4+c₁) &(j+5+c₁) 𝟎`, `funcFact &(j+5+c₁) 𝟎 (cT 1) 𝟎`; then `adjFact &(j+2+c₂) &(j+3+c₂) 𝟎` and the
dossier of `bnum m` at `j+3+c₂`. For `bnum (2m+1) = (𝟐 ^* bnum m) ^+ 𝟏 = ^func 2 0 ?[𝟐 ^* bnum m, 𝟏]`:
`funcFact &j (cT 2) 𝟎 &(j+1)`, `adjFact &(j+1) &(j+2) &(j+2+cₑ)` with `cₑ = descCountT (bnum (2m))`, the even
dossier at `j+2`, `adjFact &(j+2+cₑ) &(j+3+cₑ) 𝟎`, `funcFact &(j+3+cₑ) 𝟎 (cT 1) 𝟎`.
-/

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open PeanoMinus ISigma0 ISigma1
open LAct

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSectionVars false
set_option maxRecDepth 20000

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ## 0. The tails -/

section tails

/-- The even tail at offset `j` for `k = 2m`: `eqRefl 𝟎`, `eqOfFunc` (the two `𝟏`s of `𝟐`), `eqRefl`,
`congAdj`, the `sLemma` `𝟏 ≤ bnum m`, `bnumEvenCert`. -/
noncomputable def bnEvenTail (Wn T c₁ c₂ m j : V) : V :=
  ?[mkStep Wn 41 ?[(𝟎 : V)],
    mkStep Wn 71 ?[^&(j + 4), (𝟎 : V), cT 1, (𝟎 : V), (𝟎 : V), ^&(j + 5 + c₁)],
    mkStep Wn 41 ?[^&(j + 4 + c₁)],
    mkStep Wn 59 ?[^&(j + 5 + c₁), (𝟎 : V), ^&(j + 4 + c₁), ^&(j + 4), (𝟎 : V), ^&(j + 4 + c₁)],
    sLemma (leFact (𝟏 : V) (bnum m)) (leCode T 1 m),
    mkStep Wn ((nIdx_bnumEvenCert : ℕ) : V)
      ?[bnum m, ^&(j + 3 + c₂), ^&(j + 4), ^&(j + 4 + c₁), ^&(j + 3), ^&(j + 2), ^&(j + 2 + c₂), ^&(j + 1), ^&j]]

/-- The top of the odd tail at offset `j` for `k = 2m + 1` (`ce` the dossier count of `bnum (2m)`): the
`sLemma` `𝟏 ≤ bnum m` and `bnumOddOfEven`. -/
noncomputable def bnOddTop (Wn T ce m j : V) : V :=
  ?[sLemma (leFact (𝟏 : V) (bnum m)) (leCode T 1 m),
    mkStep Wn ((nIdx_bnumOddOfEven : ℕ) : V) ?[bnum m, ^&(j + 3 + ce), ^&(j + 2), ^&(j + 2 + ce), ^&(j + 1), ^&j]]

noncomputable def bnEvenTailDef : 𝚺₁.Semisentence 7 := .mkSigma
  “y Wn T c₁ c₂ m j.
    ∃ z, z = ↑Arithmetic.zero ∧ ∃ one, one = ↑Arithmetic.one ∧ ∃ ct1, !cTVGraph ct1 1 ∧ ∃ bm, !bnumGraph bm m ∧
    ∃ f0, !qqFvarDef f0 j ∧ ∃ f1, !qqFvarDef f1 (j + 1) ∧ ∃ f2, !qqFvarDef f2 (j + 2) ∧ ∃ f3, !qqFvarDef f3 (j + 3) ∧
    ∃ f4, !qqFvarDef f4 (j + 4) ∧ ∃ f4c, !qqFvarDef f4c (j + 4 + c₁) ∧ ∃ f5c, !qqFvarDef f5c (j + 5 + c₁) ∧
    ∃ f2d, !qqFvarDef f2d (j + 2 + c₂) ∧ ∃ f3d, !qqFvarDef f3d (j + 3 + c₂) ∧
    ∃ e₁, !mkVec₁Def e₁ z ∧ ∃ s₁, !mkStepDef s₁ Wn 41 e₁ ∧
    ∃ e₂₀, !mkVec₂Def e₂₀ z f5c ∧ ∃ e₂₁, !adjoinDef e₂₁ z e₂₀ ∧ ∃ e₂₂, !adjoinDef e₂₂ ct1 e₂₁ ∧
    ∃ e₂₃, !adjoinDef e₂₃ z e₂₂ ∧ ∃ e₂, !adjoinDef e₂ f4 e₂₃ ∧ ∃ s₂, !mkStepDef s₂ Wn 71 e₂ ∧
    ∃ e₃, !mkVec₁Def e₃ f4c ∧ ∃ s₃, !mkStepDef s₃ Wn 41 e₃ ∧
    ∃ e₄₀, !mkVec₂Def e₄₀ z f4c ∧ ∃ e₄₁, !adjoinDef e₄₁ f4 e₄₀ ∧ ∃ e₄₂, !adjoinDef e₄₂ f4c e₄₁ ∧
    ∃ e₄₃, !adjoinDef e₄₃ z e₄₂ ∧ ∃ e₄, !adjoinDef e₄ f5c e₄₃ ∧ ∃ s₄, !mkStepDef s₄ Wn 59 e₄ ∧
    ∃ A₅, !leFactDef A₅ one bm ∧ ∃ d₅, !leCodeDef d₅ T 1 m ∧ ∃ q₅, !pairDef q₅ A₅ d₅ ∧ ∃ s₅, !pairDef s₅ 7 q₅ ∧
    ∃ e₆₀, !mkVec₂Def e₆₀ f1 f0 ∧ ∃ e₆₁, !adjoinDef e₆₁ f2d e₆₀ ∧ ∃ e₆₂, !adjoinDef e₆₂ f2 e₆₁ ∧
    ∃ e₆₃, !adjoinDef e₆₃ f3 e₆₂ ∧ ∃ e₆₄, !adjoinDef e₆₄ f4c e₆₃ ∧ ∃ e₆₅, !adjoinDef e₆₅ f4 e₆₄ ∧
    ∃ e₆₆, !adjoinDef e₆₆ f3d e₆₅ ∧ ∃ e₆, !adjoinDef e₆ bm e₆₆ ∧ ∃ s₆, !mkStepDef s₆ Wn ↑nIdx_bnumEvenCert e₆ ∧
    ∃ l₆, !mkVec₁Def l₆ s₆ ∧ ∃ l₅, !adjoinDef l₅ s₅ l₆ ∧ ∃ l₄, !adjoinDef l₄ s₄ l₅ ∧ ∃ l₃, !adjoinDef l₃ s₃ l₄ ∧
    ∃ l₂, !adjoinDef l₂ s₂ l₃ ∧ !adjoinDef y s₁ l₂”

instance bnEvenTail_defined :
    𝚺₁.DefinedFunction (fun v : Fin 6 → V ↦ bnEvenTail (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)) bnEvenTailDef := .mk
  fun v ↦ by
    simp [bnEvenTailDef, bnEvenTail, numeral_eq_natCast, mkStep_defined.iff, bnum.defined.iff, cTV.defined.iff,
      leFact_defined.iff, leCode_defined.iff, sLemma, cT]
instance bnEvenTail_definable :
    𝚺₁.DefinableFunction (fun v : Fin 6 → V ↦ bnEvenTail (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)) :=
  bnEvenTail_defined.to_definable

noncomputable def bnOddTopDef : 𝚺₁.Semisentence 6 := .mkSigma
  “y Wn T ce m j.
    ∃ one, one = ↑Arithmetic.one ∧ ∃ bm, !bnumGraph bm m ∧
    ∃ f0, !qqFvarDef f0 j ∧ ∃ f1, !qqFvarDef f1 (j + 1) ∧ ∃ f2, !qqFvarDef f2 (j + 2) ∧
    ∃ f2e, !qqFvarDef f2e (j + 2 + ce) ∧ ∃ f3e, !qqFvarDef f3e (j + 3 + ce) ∧
    ∃ A₁, !leFactDef A₁ one bm ∧ ∃ d₁, !leCodeDef d₁ T 1 m ∧ ∃ q₁, !pairDef q₁ A₁ d₁ ∧ ∃ s₁, !pairDef s₁ 7 q₁ ∧
    ∃ e₂₀, !mkVec₂Def e₂₀ f1 f0 ∧ ∃ e₂₁, !adjoinDef e₂₁ f2e e₂₀ ∧ ∃ e₂₂, !adjoinDef e₂₂ f2 e₂₁ ∧
    ∃ e₂₃, !adjoinDef e₂₃ f3e e₂₂ ∧ ∃ e₂, !adjoinDef e₂ bm e₂₃ ∧ ∃ s₂, !mkStepDef s₂ Wn ↑nIdx_bnumOddOfEven e₂ ∧
    ∃ l₂, !mkVec₁Def l₂ s₂ ∧ !adjoinDef y s₁ l₂”

instance bnOddTop_defined :
    𝚺₁.DefinedFunction (fun v : Fin 5 → V ↦ bnOddTop (v 0) (v 1) (v 2) (v 3) (v 4)) bnOddTopDef := .mk
  fun v ↦ by
    simp [bnOddTopDef, bnOddTop, numeral_eq_natCast, mkStep_defined.iff, bnum.defined.iff,
      leFact_defined.iff, leCode_defined.iff, sLemma]
instance bnOddTop_definable :
    𝚺₁.DefinableFunction (fun v : Fin 5 → V ↦ bnOddTop (v 0) (v 1) (v 2) (v 3) (v 4)) :=
  bnOddTop_defined.to_definable

lemma len_bnEvenTail (Wn T c₁ c₂ m j : V) : len (bnEvenTail Wn T c₁ c₂ m j) = 6 := by
  simp [bnEvenTail]; norm_num
lemma len_bnOddTop (Wn T ce m j : V) : len (bnOddTop Wn T ce m j) = 2 := by
  simp [bnOddTop]; norm_num

end tails

/-! ## 1. The producer: a fixpoint over the bits of `k` -/

namespace BnSteps

/-- The four cases: `k = 0`, `k = 1`, `k = 2m` (the sub-list at `j + 3 + c₂`, then the even tail), and
`k = 2m + 1` (the sub-list at `j + 5 + c₂`, the even tail at `j + 2`, then the odd top). -/
def Cases (Wn Wd T c₁ c₂ : V) (C : Set V) (k j y : V) : Prop :=
  (k = 0 ∧ y = ?[mkStep Wn ((nIdx_bnumZeroCert : ℕ) : V) ?[^&j]]) ∨
  (k = 1 ∧ y = ?[mkStep Wn ((nIdx_bnumOneCert : ℕ) : V) ?[^&j]]) ∨
  (∃ m < k, 1 ≤ m ∧ k = 2 * m ∧ ∃ y' ≤ y, ⟪m, j + 3 + c₂, y'⟫ ∈ C ∧ y = appendV y' (bnEvenTail Wn T c₁ c₂ m j)) ∨
  (∃ m < k, 1 ≤ m ∧ k = 2 * m + 1 ∧ ∃ y' ≤ y, ⟪m, j + 5 + c₂, y'⟫ ∈ C ∧
    y = appendV y' (appendV (bnEvenTail Wn T c₁ c₂ m (j + 2)) (bnOddTop Wn T (descCountT Wd 0 (bnum (2 * m))) m j)))

def Phi (Wn Wd T c₁ c₂ : V) (C : Set V) (pr : V) : Prop :=
  ∃ k ≤ pr, ∃ q₁ ≤ pr, pr = ⟪k, q₁⟫ ∧ ∃ j ≤ q₁, ∃ y ≤ q₁, q₁ = ⟪j, y⟫ ∧ Cases Wn Wd T c₁ c₂ C k j y

lemma phi_unpack (Wn Wd T c₁ c₂ : V) (C : Set V) (pr : V) :
    Phi Wn Wd T c₁ c₂ C pr ↔ ∃ k j y, pr = ⟪k, j, y⟫ ∧ Cases Wn Wd T c₁ c₂ C k j y := by
  constructor
  · rintro ⟨k, _, q₁, _, rfl, j, _, y, _, rfl, h⟩
    exact ⟨k, j, y, rfl, h⟩
  · rintro ⟨k, j, y, rfl, h⟩
    exact ⟨k, le_pair_left _ _, _, le_pair_right _ _, rfl, j, le_pair_left _ _, y, le_pair_right _ _, rfl, h⟩

noncomputable def blueprint : Fixpoint.Blueprint 5 := ⟨.mkDelta
  (.mkSigma “pr C Wn Wd T c₁ c₂.
    ∃ k <⁺ pr, ∃ q₁ <⁺ pr, !pairDef pr k q₁ ∧ ∃ j <⁺ q₁, ∃ y <⁺ q₁, !pairDef q₁ j y ∧
    ( (k = 0 ∧ ∃ f, !qqFvarDef f j ∧ ∃ e, !mkVec₁Def e f ∧ ∃ s, !mkStepDef s Wn ↑nIdx_bnumZeroCert e ∧ ∃ l, !mkVec₁Def l s ∧ y = l) ∨
      (k = 1 ∧ ∃ f, !qqFvarDef f j ∧ ∃ e, !mkVec₁Def e f ∧ ∃ s, !mkStepDef s Wn ↑nIdx_bnumOneCert e ∧ ∃ l, !mkVec₁Def l s ∧ y = l) ∨
      (∃ m < k, 1 ≤ m ∧ k = 2 * m ∧ ∃ y' <⁺ y, ∃ b₃, !pairDef b₃ (j + 3 + c₂) y' ∧ :⟪m, b₃⟫:∈ C ∧
        ∃ t, !bnEvenTailDef t Wn T c₁ c₂ m j ∧ ∃ a, !appendVDef a y' t ∧ y = a) ∨
      (∃ m < k, 1 ≤ m ∧ k = 2 * m + 1 ∧ ∃ y' <⁺ y, ∃ b₃, !pairDef b₃ (j + 5 + c₂) y' ∧ :⟪m, b₃⟫:∈ C ∧
        ∃ t, !bnEvenTailDef t Wn T c₁ c₂ m (j + 2) ∧ ∃ b2, !bnumGraph b2 (2 * m) ∧ ∃ ce, !descCountTDef ce Wd 0 b2 ∧
        ∃ o, !bnOddTopDef o Wn T ce m j ∧ ∃ a₁, !appendVDef a₁ t o ∧ ∃ a, !appendVDef a y' a₁ ∧ y = a) )”)
  (.mkPi “pr C Wn Wd T c₁ c₂.
    ∃ k <⁺ pr, ∃ q₁ <⁺ pr, !pairDef pr k q₁ ∧ ∃ j <⁺ q₁, ∃ y <⁺ q₁, !pairDef q₁ j y ∧
    ( (k = 0 ∧ ∀ f, !qqFvarDef f j → ∀ e, !mkVec₁Def e f → ∀ s, !mkStepDef s Wn ↑nIdx_bnumZeroCert e → ∀ l, !mkVec₁Def l s → y = l) ∨
      (k = 1 ∧ ∀ f, !qqFvarDef f j → ∀ e, !mkVec₁Def e f → ∀ s, !mkStepDef s Wn ↑nIdx_bnumOneCert e → ∀ l, !mkVec₁Def l s → y = l) ∨
      (∃ m < k, 1 ≤ m ∧ k = 2 * m ∧ ∃ y' <⁺ y, ∀ b₃, !pairDef b₃ (j + 3 + c₂) y' → :⟪m, b₃⟫:∈ C ∧
        ∀ t, !bnEvenTailDef t Wn T c₁ c₂ m j → ∀ a, !appendVDef a y' t → y = a) ∨
      (∃ m < k, 1 ≤ m ∧ k = 2 * m + 1 ∧ ∃ y' <⁺ y, ∀ b₃, !pairDef b₃ (j + 5 + c₂) y' → :⟪m, b₃⟫:∈ C ∧
        ∀ t, !bnEvenTailDef t Wn T c₁ c₂ m (j + 2) → ∀ b2, !bnumGraph b2 (2 * m) → ∀ ce, !descCountTDef ce Wd 0 b2 →
        ∀ o, !bnOddTopDef o Wn T ce m j → ∀ a₁, !appendVDef a₁ t o → ∀ a, !appendVDef a y' a₁ → y = a) )”)⟩

set_option maxHeartbeats 2000000 in
noncomputable def construction : Fixpoint.Construction V blueprint where
  Φ := fun v ↦ Phi (v 0) (v 1) (v 2) (v 3) (v 4)
  defined := .mk <| by
    constructor
    · intro v
      simp [blueprint, mkStep_defined.iff, bnEvenTail_defined.iff, bnOddTop_defined.iff, bnum.defined.iff,
        descCountT_defined.iff, appendV_defined.iff, numeral_eq_natCast]
    · intro v
      simp [blueprint, Phi, Cases, mkStep_defined.iff, bnEvenTail_defined.iff, bnOddTop_defined.iff, bnum.defined.iff,
        descCountT_defined.iff, appendV_defined.iff, numeral_eq_natCast]
  monotone := by
    intro C C' hC w pr h
    change Phi (w 0) (w 1) (w 2) (w 3) (w 4) C pr at h
    rw [phi_unpack] at h ⊢
    obtain ⟨k, j, y, rfl, h⟩ := h
    refine ⟨k, j, y, rfl, ?_⟩
    rcases h with h | h | ⟨m, hm, h1, rfl, y', hy, hmem, rfl⟩ | ⟨m, hm, h1, rfl, y', hy, hmem, rfl⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl ⟨m, hm, h1, rfl, y', hy, hC hmem, rfl⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨m, hm, h1, rfl, y', hy, hC hmem, rfl⟩))

instance : construction.Finite V where
  finite := by
    intro C w pr h
    change Phi (w 0) (w 1) (w 2) (w 3) (w 4) C pr at h
    change ∃ m, Phi (w 0) (w 1) (w 2) (w 3) (w 4) {y ∈ C | y < m} pr
    rw [phi_unpack] at h
    simp only [phi_unpack]
    obtain ⟨k, j, y, rfl, h⟩ := h
    rcases h with h | h | ⟨m, hm, h1, hk, y', hy, hmem, hyy⟩ | ⟨m, hm, h1, hk, y', hy, hmem, hyy⟩
    · exact ⟨0, k, j, y, rfl, Or.inl h⟩
    · exact ⟨0, k, j, y, rfl, Or.inr (Or.inl h)⟩
    · exact ⟨⟪m, j + 3 + (w 4), y'⟫ + 1, k, j, y, rfl,
        Or.inr (Or.inr (Or.inl ⟨m, hm, h1, hk, y', hy, ⟨hmem, lt_add_one _⟩, hyy⟩))⟩
    · exact ⟨⟪m, j + 5 + (w 4), y'⟫ + 1, k, j, y, rfl,
        Or.inr (Or.inr (Or.inr ⟨m, hm, h1, hk, y', hy, ⟨hmem, lt_add_one _⟩, hyy⟩))⟩

end BnSteps

/-- The fixpoint at the PACKED parameter `P = ⟪Wn, Wd, T, c₁, c₂⟫` (binary, so that `definability` composes:
its `comp` rules stop at arity 5). -/
def BnPackedP (P pr : V) : Prop :=
  BnSteps.construction.Fixpoint ![π₁ P, π₁ (π₂ P), π₁ (π₂ (π₂ P)), π₁ (π₂ (π₂ (π₂ P))), π₂ (π₂ (π₂ (π₂ P)))] pr
/-- `BnGraph Wn Wd T c₁ c₂ k j y`: the certification list of `bnum k` at offset `j` is `y`. -/
def BnGraph (Wn Wd T c₁ c₂ k j y : V) : Prop := BnPackedP ⟪Wn, Wd, T, c₁, c₂⟫ ⟪k, j, y⟫

noncomputable def bnPackedPDef : 𝚺₁.Semisentence 2 := .mkSigma
  “P pr. ∃ a, !pi₁Def a P ∧ ∃ r₁, !pi₂Def r₁ P ∧ ∃ b, !pi₁Def b r₁ ∧ ∃ r₂, !pi₂Def r₂ r₁ ∧ ∃ c, !pi₁Def c r₂ ∧
    ∃ r₃, !pi₂Def r₃ r₂ ∧ ∃ d, !pi₁Def d r₃ ∧ ∃ e, !pi₂Def e r₃ ∧ !BnSteps.blueprint.fixpointDef pr a b c d e”

instance bnPackedP_defined : 𝚺₁-Relation (BnPackedP : V → V → Prop) via bnPackedPDef := .mk
  fun v ↦ by
    simp [bnPackedPDef, BnPackedP, BnSteps.construction.eval_fixpointDef]
    first
    | exact Iff.rfl
    | (constructor <;> intro h <;> convert h using 2 <;> funext i <;> fin_cases i <;> rfl)
instance bnPackedP_definable : 𝚺₁-Relation (BnPackedP : V → V → Prop) := bnPackedP_defined.to_definable

noncomputable def bnGraphDef : 𝚺₁.Semisentence 8 := .mkSigma
  “Wn Wd T c₁ c₂ k j y. ∃ q₁, !pairDef q₁ j y ∧ ∃ pr, !pairDef pr k q₁ ∧
    ∃ p₄, !pairDef p₄ c₁ c₂ ∧ ∃ p₃, !pairDef p₃ T p₄ ∧ ∃ p₂, !pairDef p₂ Wd p₃ ∧ ∃ P, !pairDef P Wn p₂ ∧ !bnPackedPDef P pr”
instance bnGraph_defined :
    𝚺₁.Defined (fun v : Fin 8 → V ↦ BnGraph (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7)) bnGraphDef := .mk
  fun v ↦ by simp [bnGraphDef, bnPackedP_defined.iff, BnGraph]
instance bnGraph_definable :
    𝚺₁.Definable (fun v : Fin 8 → V ↦ BnGraph (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7)) := bnGraph_defined.to_definable

lemma BnGraph.case_iff {Wn Wd T c₁ c₂ k j y : V} :
    BnGraph Wn Wd T c₁ c₂ k j y ↔
    ( (k = 0 ∧ y = ?[mkStep Wn ((nIdx_bnumZeroCert : ℕ) : V) ?[^&j]]) ∨
      (k = 1 ∧ y = ?[mkStep Wn ((nIdx_bnumOneCert : ℕ) : V) ?[^&j]]) ∨
      (∃ m < k, 1 ≤ m ∧ k = 2 * m ∧ ∃ y' ≤ y, BnGraph Wn Wd T c₁ c₂ m (j + 3 + c₂) y' ∧
        y = appendV y' (bnEvenTail Wn T c₁ c₂ m j)) ∨
      (∃ m < k, 1 ≤ m ∧ k = 2 * m + 1 ∧ ∃ y' ≤ y, BnGraph Wn Wd T c₁ c₂ m (j + 5 + c₂) y' ∧
        y = appendV y' (appendV (bnEvenTail Wn T c₁ c₂ m (j + 2)) (bnOddTop Wn T (descCountT Wd 0 (bnum (2 * m))) m j))) ) := by
  unfold BnGraph BnPackedP
  simp only [pi₁_pair, pi₂_pair]
  rw [BnSteps.construction.case]
  exact BnSteps.phi_unpack _ _ _ _ _ _ _ |>.trans ⟨fun ⟨k', j', y', e, h⟩ ↦ by
    rw [pair_ext_iff, pair_ext_iff] at e
    obtain ⟨rfl, rfl, rfl⟩ := e
    exact h, fun h ↦ ⟨k, j, y, rfl, h⟩⟩

lemma BnGraph.zero_iff {Wn Wd T c₁ c₂ j y : V} :
    BnGraph Wn Wd T c₁ c₂ 0 j y ↔ y = ?[mkStep Wn ((nIdx_bnumZeroCert : ℕ) : V) ?[^&j]] := by
  rw [BnGraph.case_iff]
  constructor
  · rintro (⟨_, h⟩ | ⟨h, _⟩ | ⟨m, hm, h1, hk, _⟩ | ⟨m, hm, h1, hk, _⟩)
    · exact h
    · exact absurd h zero_ne_one
    · exact absurd hk.symm (two_mul_ne_zero h1)
    · exact absurd hk.symm (two_mul_add_one_ne_zero m)
  · intro h; exact Or.inl ⟨rfl, h⟩

lemma BnGraph.one_iff {Wn Wd T c₁ c₂ j y : V} :
    BnGraph Wn Wd T c₁ c₂ 1 j y ↔ y = ?[mkStep Wn ((nIdx_bnumOneCert : ℕ) : V) ?[^&j]] := by
  rw [BnGraph.case_iff]
  constructor
  · rintro (⟨h, _⟩ | ⟨_, h⟩ | ⟨m, hm, h1, hk, _⟩ | ⟨m, hm, h1, hk, _⟩)
    · exact absurd h _root_.one_ne_zero
    · exact h
    · exact absurd hk.symm (two_mul_ne_one m)
    · exact absurd hk.symm (two_mul_add_one_ne_one h1)
  · intro h; exact Or.inr (Or.inl ⟨rfl, h⟩)

lemma BnGraph.even_iff {Wn Wd T c₁ c₂ m j y : V} (hm : 1 ≤ m) :
    BnGraph Wn Wd T c₁ c₂ (2 * m) j y ↔
    ∃ y' ≤ y, BnGraph Wn Wd T c₁ c₂ m (j + 3 + c₂) y' ∧ y = appendV y' (bnEvenTail Wn T c₁ c₂ m j) := by
  rw [BnGraph.case_iff]
  constructor
  · rintro (⟨h, _⟩ | ⟨h, _⟩ | ⟨m', _, _, hk, y', hy, hg, rfl⟩ | ⟨m', _, _, hk, _⟩)
    · exact absurd h (two_mul_ne_zero hm)
    · exact absurd h (two_mul_ne_one m)
    · obtain rfl := two_mul_inj hk; exact ⟨y', hy, hg, rfl⟩
    · exact absurd hk (two_mul_ne_two_mul_add_one m m')
  · rintro ⟨y', hy, hg, rfl⟩
    exact Or.inr (Or.inr (Or.inl ⟨m, Bnum.lt_two_mul hm, hm, rfl, y', hy, hg, rfl⟩))

lemma BnGraph.odd_iff {Wn Wd T c₁ c₂ m j y : V} (hm : 1 ≤ m) :
    BnGraph Wn Wd T c₁ c₂ (2 * m + 1) j y ↔
    ∃ y' ≤ y, BnGraph Wn Wd T c₁ c₂ m (j + 5 + c₂) y' ∧
      y = appendV y' (appendV (bnEvenTail Wn T c₁ c₂ m (j + 2)) (bnOddTop Wn T (descCountT Wd 0 (bnum (2 * m))) m j)) := by
  rw [BnGraph.case_iff]
  constructor
  · rintro (⟨h, _⟩ | ⟨h, _⟩ | ⟨m', _, _, hk, _⟩ | ⟨m', _, _, hk, y', hy, hg, rfl⟩)
    · exact absurd h (two_mul_add_one_ne_zero m)
    · exact absurd h (two_mul_add_one_ne_one hm)
    · exact absurd hk.symm (two_mul_ne_two_mul_add_one m' m)
    · obtain rfl := two_mul_add_one_inj hk; exact ⟨y', hy, hg, rfl⟩
  · rintro ⟨y', hy, hg, rfl⟩
    exact Or.inr (Or.inr (Or.inr ⟨m, Bnum.lt_two_mul_add_one hm, hm, rfl, y', hy, hg, rfl⟩))

section existence

/-- **Existence**, offsets bounded (Σ₁ motive): for `j + (k + 1)·(c₁ + c₂ + 8) ≤ B`. -/
lemma bnGraph_exists_bounded (Wn Wd T c₁ c₂ B : V) :
    ∀ k : V, ∀ j ≤ B, j + (k + 1) * (c₁ + c₂ + 8) ≤ B → ∃ y, BnGraph Wn Wd T c₁ c₂ k j y := by
  intro k
  induction k using ISigma1.sigma1_order_induction with
  | hP => simp only [BnGraph]; definability
  | ind k ih =>
    intro j hj hB
    rcases zero_one_or_two_le k with rfl | rfl | h2
    · exact ⟨_, BnGraph.zero_iff.mpr rfl⟩
    · exact ⟨_, BnGraph.one_iff.mpr rfl⟩
    obtain ⟨hm, hlt, he | ho⟩ := two_le_cases h2
    · -- k = 2 * (k / 2)
      set m := k / 2 with hmdef
      have hB' : j + 3 + c₂ + (m + 1) * (c₁ + c₂ + 8) ≤ B := by
        refine le_trans ?_ hB
        rw [he]
        have : (m + 1) * (c₁ + c₂ + 8) + (3 + c₂) ≤ (2 * m + 1) * (c₁ + c₂ + 8) := by
          have h1 : 3 + c₂ ≤ m * (c₁ + c₂ + 8) := by
            calc 3 + c₂ ≤ c₁ + c₂ + 8 := by
                  calc 3 + c₂ ≤ (c₁ + 5) + (c₂ + 3) := add_le_add (by
                        calc (3 : V) ≤ 5 := by norm_num
                          _ ≤ c₁ + 5 := le_add_self) le_self_add
                    _ = c₁ + c₂ + 8 := by ring
              _ = 1 * (c₁ + c₂ + 8) := (one_mul _).symm
              _ ≤ m * (c₁ + c₂ + 8) := mul_le_mul_of_nonneg_right hm zero_le
          calc (m + 1) * (c₁ + c₂ + 8) + (3 + c₂) ≤ (m + 1) * (c₁ + c₂ + 8) + m * (c₁ + c₂ + 8) := add_le_add le_rfl h1
            _ = (2 * m + 1) * (c₁ + c₂ + 8) := by ring
        calc j + 3 + c₂ + (m + 1) * (c₁ + c₂ + 8) = j + ((m + 1) * (c₁ + c₂ + 8) + (3 + c₂)) := by ring
          _ ≤ j + (2 * m + 1) * (c₁ + c₂ + 8) := add_le_add le_rfl this
      obtain ⟨y', hy'⟩ := ih m hlt (j + 3 + c₂) (le_trans le_self_add hB') hB'
      rw [he]
      exact ⟨_, (BnGraph.even_iff hm).mpr ⟨y', le_appendV_left _ _, hy', rfl⟩⟩
    · -- k = 2 * (k / 2) + 1
      set m := k / 2 with hmdef
      have hB' : j + 5 + c₂ + (m + 1) * (c₁ + c₂ + 8) ≤ B := by
        refine le_trans ?_ hB
        rw [ho]
        have : (m + 1) * (c₁ + c₂ + 8) + (5 + c₂) ≤ (2 * m + 1 + 1) * (c₁ + c₂ + 8) := by
          have h1 : 5 + c₂ ≤ (m + 1) * (c₁ + c₂ + 8) := by
            calc 5 + c₂ ≤ c₁ + c₂ + 8 := by
                  calc 5 + c₂ ≤ (c₁ + 5) + (c₂ + 3) := add_le_add le_add_self le_self_add
                    _ = c₁ + c₂ + 8 := by ring
              _ = 1 * (c₁ + c₂ + 8) := (one_mul _).symm
              _ ≤ (m + 1) * (c₁ + c₂ + 8) := mul_le_mul_of_nonneg_right (le_trans hm le_self_add) zero_le
          calc (m + 1) * (c₁ + c₂ + 8) + (5 + c₂) ≤ (m + 1) * (c₁ + c₂ + 8) + (m + 1) * (c₁ + c₂ + 8) := add_le_add le_rfl h1
            _ = (2 * m + 1 + 1) * (c₁ + c₂ + 8) := by ring
        calc j + 5 + c₂ + (m + 1) * (c₁ + c₂ + 8) = j + ((m + 1) * (c₁ + c₂ + 8) + (5 + c₂)) := by ring
          _ ≤ j + (2 * m + 1 + 1) * (c₁ + c₂ + 8) := add_le_add le_rfl this
      obtain ⟨y', hy'⟩ := ih m hlt (j + 5 + c₂) (le_trans le_self_add hB') hB'
      rw [ho]
      exact ⟨_, (BnGraph.odd_iff hm).mpr ⟨y', le_appendV_left _ _, hy', rfl⟩⟩

lemma bnGraph_exists (Wn Wd T c₁ c₂ k j : V) : ∃ y, BnGraph Wn Wd T c₁ c₂ k j y :=
  bnGraph_exists_bounded Wn Wd T c₁ c₂ (j + (k + 1) * (c₁ + c₂ + 8)) k j le_self_add le_rfl

end existence

/-- **The producer `bnumSteps Wn Wd T k j`**: the certification list of `bnum k` at offset `j` (`Wn` the pin's
pieces, `Wd` the walk pieces, `T` the `NumSteps` table); a chosen graph witness — no uniqueness is needed, every
statement below runs over `BnGraph`. -/
noncomputable def bnumSteps (Wn Wd T k j : V) : V :=
  Classical.choose (bnGraph_exists Wn Wd T (descCountT Wd 0 (𝟏 : V)) (descCountT Wd 0 (𝟐 : V)) k j)

theorem bnumSteps_graph (Wn Wd T k j : V) :
    BnGraph Wn Wd T (descCountT Wd 0 (𝟏 : V)) (descCountT Wd 0 (𝟐 : V)) k j (bnumSteps Wn Wd T k j) :=
  Classical.choose_spec (bnGraph_exists Wn Wd T _ _ k j)

end ArithS
