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

/-! ## 2. Applicability -/

section readers

lemma cT_one_eq : (cT 1 : V) = cTV (1 : V) := by simp [cT]
lemma cT_two_eq : (cT 2 : V) = cTV (2 : V) := by simp [cT]

variable {tbl N : V} (htbl : TableOK tbl N) (hW : WalkTable tbl)
include htbl hW

/-- The dossier of a nullary function code `^func 0 f 0` at `&i`: `funcFact &i 𝟎 (cTV f) 𝟎`. -/
lemma dossT_const {Γ f i : V} (hf : LAct.IsFunc 0 f) (h : DossT walkPieces Γ 0 (^func 0 f 0) i) :
    neg LAct (funcFact (^&i) (𝟎 : V) (cTV f) (𝟎 : V)) ∈ Γ := by
  obtain ⟨h1, _, _, _⟩ := dossT_func htbl hW rfl hf (IsSemitermVec.nil (L := LAct) (0 : V)) h
  rwa [cTV_zero, vRef_zero] at h1

/-- The dossier of a binary function code `^func 2 f ?[a, b]` at `&i`: the function fact, the two `adj`
facts and the entries' dossiers at `&(i+2)` (for `a`) and `&(i+3+descCountT a)` (for `b`). -/
lemma dossT_pair {Γ f a b i : V} (hf : LAct.IsFunc 2 f) (ha : IsSemiterm LAct 0 a) (hb : IsSemiterm LAct 0 b)
    (h : DossT walkPieces Γ 0 (^func 2 f ?[a, b]) i) :
    neg LAct (funcFact (^&i) (cT 2) (cTV f) (^&(i + 1))) ∈ Γ ∧
    neg LAct (adjFact (^&(i + 1)) (^&(i + 2)) (^&(i + 2 + descCountT walkPieces 0 a))) ∈ Γ ∧
    DossT walkPieces Γ 0 a (i + 2) ∧
    neg LAct (adjFact (^&(i + 2 + descCountT walkPieces 0 a)) (^&(i + 3 + descCountT walkPieces 0 a)) (𝟎 : V)) ∈ Γ ∧
    DossT walkPieces Γ 0 b (i + 3 + descCountT walkPieces 0 a) := by
  have hv : IsSemitermVec LAct 2 0 (?[a, b] : V) := by simp [ha, hb]
  obtain ⟨h1, _, _, hV⟩ := dossT_func htbl hW rfl hf hv h
  rw [vRef_of_ne two_ne_zero, ← cT_two_eq] at h1
  have hV' : DossV walkPieces Γ 0 2 ?[a, b] (1 + 1) (i + 1) := by rw [one_add_one_eq_two]; exact hV
  obtain ⟨ha1, _, hD1, hV1⟩ := dossV_succ htbl hW rfl hv (by rw [one_add_one_eq_two]) hV'
  have e0 : (2 : V) - (1 + 1) = 0 := by rw [one_add_one_eq_two, tsub_self]
  rw [e0, nth_adjoin_zero, vRef_of_ne _root_.one_ne_zero, add_assoc, one_add_one_eq_two] at ha1
  rw [e0, nth_adjoin_zero, add_assoc, one_add_one_eq_two] at hD1
  rw [e0, nth_adjoin_zero, show i + 1 + 1 + descCountT walkPieces 0 a = i + 2 + descCountT walkPieces 0 a by ring] at hV1
  have hV1' : DossV walkPieces Γ 0 2 ?[a, b] (0 + 1) (i + 2 + descCountT walkPieces 0 a) := by rw [zero_add]; exact hV1
  obtain ⟨ha2, _, hD2, _⟩ := dossV_succ htbl hW rfl hv (by rw [zero_add]; exact one_le_two) hV1'
  have e1 : (2 : V) - (0 + 1) = 1 := by rw [zero_add, ← one_add_one_eq_two, add_tsub_cancel_right]
  rw [vRef_zero, show i + 2 + descCountT walkPieces 0 a + 1 = i + 3 + descCountT walkPieces 0 a by ring] at ha2
  rw [e1, nth_adjoin_one, nth_adjoin_zero, show i + 2 + descCountT walkPieces 0 a + 1 = i + 3 + descCountT walkPieces 0 a by ring] at hD2
  exact ⟨h1, ha1, hD1, ha2, hD2⟩

/-- The two dossier counts are standard-bounded: `descCountT 𝟏 ≤ 1`, `descCountT 𝟐 ≤ 5`. -/
lemma descCountT_one_le : descCountT walkPieces 0 (𝟏 : V) ≤ 1 := by
  have := descCountT_walk_le htbl hW rfl (isSemiterm_qqOne_LAct (0 : V))
  rw [termLen_qqOne isFunc_LAct_oneIndex] at this
  have h2 : descCountT walkPieces 0 (𝟏 : V) + 1 ≤ 1 + 1 := by rw [one_add_one_eq_two]; exact le_trans this (by norm_num)
  exact le_of_add_le_add_right h2
lemma descCountT_two_le : descCountT walkPieces 0 (𝟐 : V) ≤ 5 := by
  have := descCountT_walk_le htbl hW rfl (isSemiterm_qqTwo_LAct (0 : V))
  rw [show (𝟐 : V) = (𝟏 : V) ^+ (𝟏 : V) from rfl,
    termLen_qqAdd isFunc_LAct_addIndex (isSemiterm_qqOne_LAct (0 : V)).isUTerm (isSemiterm_qqOne_LAct (0 : V)).isUTerm,
    termLen_qqOne isFunc_LAct_oneIndex] at this
  have h2 : descCountT walkPieces 0 (𝟐 : V) + 1 ≤ 5 + 1 := le_trans this (by norm_num)
  exact le_of_add_le_add_right h2

end readers

section tailsOK

/-- The four `bnum` rows of `NumIdRows` read at their indices (what `Pin.NumIdTable` provides). -/
def BnRows (tbl : V) : Prop :=
  (((nIdx_bnumZeroCert : ℕ) : V) < len tbl ∧ rowM tbl.[((nIdx_bnumZeroCert : ℕ) : V)] = ((1 : ℕ) : V) ∧
    rowB tbl.[((nIdx_bnumZeroCert : ℕ) : V)] = impChainV LAct (vecOf row_bnumZeroCert_as) row_bnumZeroCert_c) ∧
  (((nIdx_bnumOneCert : ℕ) : V) < len tbl ∧ rowM tbl.[((nIdx_bnumOneCert : ℕ) : V)] = ((1 : ℕ) : V) ∧
    rowB tbl.[((nIdx_bnumOneCert : ℕ) : V)] = impChainV LAct (vecOf row_bnumOneCert_as) row_bnumOneCert_c) ∧
  (((nIdx_bnumEvenCert : ℕ) : V) < len tbl ∧ rowM tbl.[((nIdx_bnumEvenCert : ℕ) : V)] = ((9 : ℕ) : V) ∧
    rowB tbl.[((nIdx_bnumEvenCert : ℕ) : V)] = impChainV LAct (vecOf row_bnumEvenCert_as) row_bnumEvenCert_c) ∧
  (((nIdx_bnumOddOfEven : ℕ) : V) < len tbl ∧ rowM tbl.[((nIdx_bnumOddOfEven : ℕ) : V)] = ((6 : ℕ) : V) ∧
    rowB tbl.[((nIdx_bnumOddOfEven : ℕ) : V)] = impChainV LAct (vecOf row_bnumOddOfEven_as) row_bnumOddOfEven_c)

/-- A layout row read from the pin's pieces is the layout's step (the piece-table chain). -/
lemma mkStep_numIdPieces_layout (i : ℕ) (hi : i < layoutRowCount) (ev : V) :
    mkStep numIdPieces (i : V) ev = mkStep layoutPieces (i : V) ev := by
  have h1 : i < proBase := by simp only [proBase, topRowCount, proExtraRowCount, layoutRowCount] at hi ⊢; omega
  have h2 : i < topRowCount := by simp only [topRowCount, layoutRowCount] at hi ⊢; omega
  have h3 : i < frag2RowCount := by simp only [frag2RowCount, layoutRowCount] at hi ⊢; omega
  have h4 : i < frag1RowCount := by simp only [frag1RowCount, layoutRowCount] at hi ⊢; omega
  rw [mkStep_numIdPieces_lt i h1, mkStep_proPieces_lt i h2, mkStep_topPieces_lt i h3, mkStep_frag2Pieces_lt i h4,
    mkStep_frag1Pieces_lt i hi]

lemma mkStep_numId_41 (ev : V) : mkStep numIdPieces (41 : V) ev = mkStep layoutPieces (41 : V) ev := by
  have := mkStep_numIdPieces_layout 41 (by decide) ev; simpa using this
lemma mkStep_numId_59 (ev : V) : mkStep numIdPieces (59 : V) ev = mkStep layoutPieces (59 : V) ev := by
  have := mkStep_numIdPieces_layout 59 (by decide) ev; simpa using this
lemma mkStep_numId_71 (ev : V) : mkStep numIdPieces (71 : V) ev = mkStep layoutPieces (71 : V) ev := by
  have := mkStep_numIdPieces_layout 71 (by decide) ev; simpa using this

lemma termLen_cT_one_le {E : V} (hE : 3 ≤ E) : termLen LAct (cT 1 : V) ≤ E := by
  have e : termLen LAct (cT 1 : V) = 3 := by rw [termLen_cT]; norm_num
  rw [e]; exact hE
lemma termLen_qqZero_le {E : V} (hE : 1 ≤ E) : termLen LAct (𝟎 : V) ≤ E := by
  rw [termLen_qqZero isFunc_LAct_zeroIndex]; exact hE

variable {tbl N T N' B' : V} (htbl : TableOK tbl N) (hL : LayoutTable tbl) (hR : BnRows tbl) (htblN : NumTableOK T N' B')
include htbl hL hR htblN

set_option maxHeartbeats 2000000 in
/-- **The even tail is applicable** (`k = 2m`, `m ≥ 1`), from the dossier facts at the offsets of
`𝟐 ^* bnum m` at `&j` and the certified `bnumFact &(j+3+c₂) (bnum m)`; shift-free; leaves
`bnumFact &j (𝟐 ^* bnum m)`. -/
theorem bnEvenTail_ok {E Γ m j c₁ c₂ : V} (hΓ : IsFormulaSet LAct Γ) (hm : 1 ≤ m)
    (hc₁ : c₁ ≤ 1) (hc₂ : c₂ ≤ 5) (hEj : j + 9 ≤ E) (hEm : termLen LAct (bnum m) ≤ E)
    (f1 : neg LAct (funcFact (^&j) (cT 2) (cT 1) (^&(j + 1))) ∈ Γ)
    (f2 : neg LAct (adjFact (^&(j + 1)) (^&(j + 2)) (^&(j + 2 + c₂))) ∈ Γ)
    (f3 : neg LAct (funcFact (^&(j + 2)) (cT 2) (𝟎 : V) (^&(j + 3))) ∈ Γ)
    (f4 : neg LAct (adjFact (^&(j + 3)) (^&(j + 4)) (^&(j + 4 + c₁))) ∈ Γ)
    (f5 : neg LAct (funcFact (^&(j + 4)) (𝟎 : V) (cT 1) (𝟎 : V)) ∈ Γ)
    (f6 : neg LAct (adjFact (^&(j + 4 + c₁)) (^&(j + 5 + c₁)) (𝟎 : V)) ∈ Γ)
    (f7 : neg LAct (funcFact (^&(j + 5 + c₁)) (𝟎 : V) (cT 1) (𝟎 : V)) ∈ Γ)
    (f8 : neg LAct (adjFact (^&(j + 2 + c₂)) (^&(j + 3 + c₂)) (𝟎 : V)) ∈ Γ)
    (f9 : neg LAct (bnumFact (^&(j + 3 + c₂)) (bnum m)) ∈ Γ) :
    ListOK tbl E ((9 : ℕ) : V) Γ (bnEvenTail numIdPieces T c₁ c₂ m j) ∧ NoDrop' (bnEvenTail numIdPieces T c₁ c₂ m j) ∧
    shiftsV (bnEvenTail numIdPieces T c₁ c₂ m j) = 0 ∧
    neg LAct (bnumFact (^&j) (𝟐 ^* bnum m)) ∈ finalCtx Γ (bnEvenTail numIdPieces T c₁ c₂ m j) := by
  have h89 : ((8 : ℕ) : V) ≤ ((9 : ℕ) : V) := by exact_mod_cast (by decide : 8 ≤ 9)
  have hE1 : (1 : V) ≤ E := le_trans (by norm_num) (le_trans le_add_self hEj)
  have hE3 : (3 : V) ≤ E := le_trans (by norm_num) (le_trans le_add_self hEj)
  have h0 : IsSemiterm LAct 0 (𝟎 : V) := isSemiterm_qqZero_LAct 0
  have h0E : termLen LAct (𝟎 : V) ≤ E := termLen_qqZero_le hE1
  have hc1 : IsSemiterm LAct 0 (cT 1 : V) := cTV_semiterm_LAct 0 _
  have hc1E : termLen LAct (cT 1 : V) ≤ E := termLen_cT_one_le hE3
  have hbm : IsSemiterm LAct 0 (bnum m) := isSemiterm_bnum_LAct 0 m
  have fv : ∀ x : V, x + 1 ≤ j + 9 → termLen LAct (^&x : V) ≤ E := fun x hx ↦ termLen_fvar_le (le_trans hx hEj)
  have hx4 : j + 4 + 1 ≤ j + 9 := by
    calc j + 4 + 1 = j + 5 := by ring
      _ ≤ j + 9 := add_le_add le_rfl (by norm_num)
  have hx4c : j + 4 + c₁ + 1 ≤ j + 9 := by
    calc j + 4 + c₁ + 1 ≤ j + 4 + 1 + 1 := add_le_add (add_le_add le_rfl hc₁) le_rfl
      _ = j + 6 := by ring
      _ ≤ j + 9 := add_le_add le_rfl (by norm_num)
  have hx5c : j + 5 + c₁ + 1 ≤ j + 9 := by
    calc j + 5 + c₁ + 1 ≤ j + 5 + 1 + 1 := add_le_add (add_le_add le_rfl hc₁) le_rfl
      _ = j + 7 := by ring
      _ ≤ j + 9 := add_le_add le_rfl (by norm_num)
  have hx3d : j + 3 + c₂ + 1 ≤ j + 9 := by
    calc j + 3 + c₂ + 1 ≤ j + 3 + 5 + 1 := add_le_add (add_le_add le_rfl hc₂) le_rfl
      _ = j + 9 := by ring
  have hx2d : j + 2 + c₂ + 1 ≤ j + 9 := by
    calc j + 2 + c₂ + 1 ≤ j + 2 + 5 + 1 := add_le_add (add_le_add le_rfl hc₂) le_rfl
      _ = j + 8 := by ring
      _ ≤ j + 9 := add_le_add le_rfl (by norm_num)
  have hx3 : j + 3 + 1 ≤ j + 9 := by
    calc j + 3 + 1 = j + 4 := by ring
      _ ≤ j + 9 := add_le_add le_rfl (by norm_num)
  have hx2 : j + 2 + 1 ≤ j + 9 := by
    calc j + 2 + 1 = j + 3 := by ring
      _ ≤ j + 9 := add_le_add le_rfl (by norm_num)
  have hx1 : j + 1 + 1 ≤ j + 9 := by
    calc j + 1 + 1 = j + 2 := by ring
      _ ≤ j + 9 := add_le_add le_rfl (by norm_num)
  have hx0 : j + 1 ≤ j + 9 := add_le_add le_rfl (by norm_num)
  -- step 1: eqRefl 𝟎
  obtain ⟨ok₁, tg₁, cx₁⟩ := lok_eqRefl htbl hL rfl hΓ h0 h0E
  rw [← mkStep_numId_41] at ok₁ tg₁ cx₁
  set Γ₁ := insert (neg LAct (eqFactB (𝟎 : V) (𝟎 : V))) Γ with hΓ₁
  have hΓ₁s : IsFormulaSet LAct Γ₁ := by rw [← cx₁]; exact isFormulaSet_ctxAfter 8 htbl ok₁
  -- step 2: eqOfFunc: &(j+4) = &(j+5+c₁)
  obtain ⟨ok₂, tg₂, cx₂⟩ := lok_eqOfFunc htbl hL rfl hΓ₁s (by simp) (fv _ hx4) h0 h0E hc1 hc1E h0 h0E h0 h0E (by simp) (fv _ hx5c)
    (mem_insert_of_mem' f5) (mem_insert_of_mem' f7) mem_insert_self'
  rw [← mkStep_numId_71] at ok₂ tg₂ cx₂
  set Γ₂ := insert (neg LAct (eqFactB (^&(j + 4)) (^&(j + 5 + c₁)))) Γ₁ with hΓ₂
  have hΓ₂s : IsFormulaSet LAct Γ₂ := by rw [← cx₂]; exact isFormulaSet_ctxAfter 8 htbl ok₂
  -- step 3: eqRefl &(j+4+c₁)
  obtain ⟨ok₃, tg₃, cx₃⟩ := lok_eqRefl htbl hL rfl hΓ₂s (by simp) (fv _ hx4c)
  rw [← mkStep_numId_41] at ok₃ tg₃ cx₃
  set Γ₃ := insert (neg LAct (eqFactB (^&(j + 4 + c₁)) (^&(j + 4 + c₁)))) Γ₂ with hΓ₃
  have hΓ₃s : IsFormulaSet LAct Γ₃ := by rw [← cx₃]; exact isFormulaSet_ctxAfter 8 htbl ok₃
  -- step 4: congAdj: adjFact &(j+4+c₁) &(j+4) 𝟎
  obtain ⟨ok₄, tg₄, cx₄⟩ := lok_congAdj htbl hL rfl hΓ₃s (by simp) (fv _ hx5c) h0 h0E (by simp) (fv _ hx4c)
    (by simp) (fv _ hx4) h0 h0E (by simp) (fv _ hx4c)
    (by rw [hΓ₃]; exact mem_insert_self')
    (by rw [hΓ₃, hΓ₂]; exact mem_insert_of_mem' mem_insert_self')
    (by rw [hΓ₃, hΓ₂, hΓ₁]; exact mem_insert_of_mem' (mem_insert_of_mem' mem_insert_self'))
    (by rw [hΓ₃, hΓ₂, hΓ₁]; exact mem_insert_of_mem' (mem_insert_of_mem' (mem_insert_of_mem' f6)))
  rw [← mkStep_numId_59] at ok₄ tg₄ cx₄
  set Γ₄ := insert (neg LAct (adjFact (^&(j + 4 + c₁)) (^&(j + 4)) (𝟎 : V))) Γ₃ with hΓ₄
  have hΓ₄s : IsFormulaSet LAct Γ₄ := by rw [← cx₄]; exact isFormulaSet_ctxAfter 8 htbl ok₄
  -- step 5: the closed fact 𝟏 ≤ bnum m
  have ok₅ : StepOK tbl E ((9 : ℕ) : V) Γ₄ (sLemma (leFact (𝟏 : V) (bnum m)) (leCode T 1 m)) :=
    stepOK_sLemma hΓ₄s (lemmaOK_of (isFormula_leFact (isSemiterm_qqOne_LAct 0) hbm) (oneLe_proof htblN hm))
  have cx₅ := ctxAfter_sLemma Γ₄ (leFact (𝟏 : V) (bnum m)) (leCode T 1 m)
  set Γ₅ := insert (neg LAct (leFact (𝟏 : V) (bnum m))) Γ₄ with hΓ₅
  have hΓ₅s : IsFormulaSet LAct Γ₅ := by rw [← cx₅]; exact isFormulaSet_ctxAfter 9 htbl ok₅
  -- step 6: bnumEvenCert
  have hup : ∀ {x : V}, x ∈ Γ → x ∈ Γ₅ := fun hx ↦ by
    rw [hΓ₅, hΓ₄, hΓ₃, hΓ₂, hΓ₁]
    exact mem_insert_of_mem' (mem_insert_of_mem' (mem_insert_of_mem' (mem_insert_of_mem' (mem_insert_of_mem' hx))))
  obtain ⟨ok₆, tg₆, cx₆⟩ := nok_bnumEvenCert htbl rfl hR.2.2.1.1 ⟨hR.2.2.1.2.1, hR.2.2.1.2.2⟩ hΓ₅s hbm hEm
    (by simp) (fv _ hx3d) (by simp) (fv _ hx4) (by simp) (fv _ hx4c) (by simp) (fv _ hx3) (by simp) (fv _ hx2)
    (by simp) (fv _ hx2d) (by simp) (fv _ hx1) (by simp) (fv _ hx0)
    (by rw [hΓ₅]; exact mem_insert_self') (hup f9) (hup f5)
    (by rw [hΓ₅, hΓ₄]; exact mem_insert_of_mem' mem_insert_self') (hup f4) (hup f3) (hup f8) (hup f2) (hup f1)
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold bnEvenTail
    refine listOK_cons (ok₁.mono h89) ?_
    rw [cx₁]
    refine listOK_cons (ok₂.mono h89) ?_
    rw [cx₂]
    refine listOK_cons (ok₃.mono h89) ?_
    rw [cx₃]
    refine listOK_cons (ok₄.mono h89) ?_
    rw [cx₄]
    refine listOK_cons ok₅ ?_
    rw [cx₅]
    exact listOK_single ok₆
  · unfold bnEvenTail
    exact noDrop'_cons (Or.inl tg₁) (noDrop'_cons (Or.inl tg₂) (noDrop'_cons (Or.inl tg₃) (noDrop'_cons (Or.inl tg₄)
      (noDrop'_cons (by simp) (noDrop'_single (Or.inl tg₆))))))
  · unfold bnEvenTail
    rw [shiftsV_cons_tag0 tg₁, shiftsV_cons_tag0 tg₂, shiftsV_cons_tag0 tg₃, shiftsV_cons_tag0 tg₄, shiftsV_cons_sLemma,
      shiftsV_single_tag0 tg₆]
  · unfold bnEvenTail
    rw [finalCtx_cons, cx₁, finalCtx_cons, cx₂, finalCtx_cons, cx₃, finalCtx_cons, cx₄, finalCtx_cons, cx₅,
      finalCtx_single, cx₆]
    exact mem_insert_self'

/-- **The odd top is applicable** (`k = 2m + 1`): from the certified even numeral at `&(j+2)` and the dossier
facts of `(𝟐 ^* bnum m) ^+ 𝟏` at `&j` (`ce` the count of the even numeral's dossier). -/
theorem bnOddTop_ok {E Γ m j ce : V} (hΓ : IsFormulaSet LAct Γ) (hm : 1 ≤ m)
    (hEj : j + 3 + ce + 1 ≤ E) (hEm : termLen LAct (bnum m) ≤ E)
    (g1 : neg LAct (funcFact (^&j) (cT 2) (𝟎 : V) (^&(j + 1))) ∈ Γ)
    (g2 : neg LAct (adjFact (^&(j + 1)) (^&(j + 2)) (^&(j + 2 + ce))) ∈ Γ)
    (g3 : neg LAct (bnumFact (^&(j + 2)) (𝟐 ^* bnum m)) ∈ Γ)
    (g4 : neg LAct (adjFact (^&(j + 2 + ce)) (^&(j + 3 + ce)) (𝟎 : V)) ∈ Γ)
    (g5 : neg LAct (funcFact (^&(j + 3 + ce)) (𝟎 : V) (cT 1) (𝟎 : V)) ∈ Γ) :
    ListOK tbl E ((9 : ℕ) : V) Γ (bnOddTop numIdPieces T ce m j) ∧ NoDrop' (bnOddTop numIdPieces T ce m j) ∧
    shiftsV (bnOddTop numIdPieces T ce m j) = 0 ∧
    neg LAct (bnumFact (^&j) ((𝟐 ^* bnum m) ^+ 𝟏)) ∈ finalCtx Γ (bnOddTop numIdPieces T ce m j) := by
  have h89 : ((8 : ℕ) : V) ≤ ((9 : ℕ) : V) := by exact_mod_cast (by decide : 8 ≤ 9)
  have hbm : IsSemiterm LAct 0 (bnum m) := isSemiterm_bnum_LAct 0 m
  have fv : ∀ x : V, x + 1 ≤ j + 3 + ce + 1 → termLen LAct (^&x : V) ≤ E := fun x hx ↦ termLen_fvar_le (le_trans hx hEj)
  have hx3e : j + 3 + ce + 1 ≤ j + 3 + ce + 1 := le_rfl
  have hx2e : j + 2 + ce + 1 ≤ j + 3 + ce + 1 := by
    calc j + 2 + ce + 1 ≤ j + 2 + ce + 1 + 1 := le_self_add
      _ = j + 3 + ce + 1 := by ring
  have hx2 : j + 2 + 1 ≤ j + 3 + ce + 1 := by
    calc j + 2 + 1 ≤ j + 2 + 1 + (ce + 1) := le_self_add
      _ = j + 3 + ce + 1 := by ring
  have hx1 : j + 1 + 1 ≤ j + 3 + ce + 1 := by
    calc j + 1 + 1 ≤ j + 1 + 1 + (ce + 2) := le_self_add
      _ = j + 3 + ce + 1 := by ring
  have hx0 : j + 1 ≤ j + 3 + ce + 1 := by
    calc j + 1 ≤ j + 1 + (ce + 3) := le_self_add
      _ = j + 3 + ce + 1 := by ring
  -- step 1: the closed fact 𝟏 ≤ bnum m
  have ok₁ : StepOK tbl E ((9 : ℕ) : V) Γ (sLemma (leFact (𝟏 : V) (bnum m)) (leCode T 1 m)) :=
    stepOK_sLemma hΓ (lemmaOK_of (isFormula_leFact (isSemiterm_qqOne_LAct 0) hbm) (oneLe_proof htblN hm))
  have cx₁ := ctxAfter_sLemma Γ (leFact (𝟏 : V) (bnum m)) (leCode T 1 m)
  set Γ₁ := insert (neg LAct (leFact (𝟏 : V) (bnum m))) Γ with hΓ₁
  have hΓ₁s : IsFormulaSet LAct Γ₁ := by rw [← cx₁]; exact isFormulaSet_ctxAfter 9 htbl ok₁
  -- step 2: bnumOddOfEven
  obtain ⟨ok₂, tg₂, cx₂⟩ := nok_bnumOddOfEven htbl rfl hR.2.2.2.1 ⟨hR.2.2.2.2.1, hR.2.2.2.2.2⟩ hΓ₁s hbm hEm
    (by simp) (fv _ hx3e) (by simp) (fv _ hx2) (by simp) (fv _ hx2e) (by simp) (fv _ hx1) (by simp) (fv _ hx0)
    (by rw [hΓ₁]; exact mem_insert_self') (mem_insert_of_mem' g3) (mem_insert_of_mem' g5) (mem_insert_of_mem' g4)
    (mem_insert_of_mem' g2) (mem_insert_of_mem' g1)
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold bnOddTop
    refine listOK_cons ok₁ ?_
    rw [cx₁]
    exact listOK_single (ok₂.mono h89)
  · unfold bnOddTop
    exact noDrop'_cons (by simp) (noDrop'_single (Or.inl tg₂))
  · unfold bnOddTop
    rw [shiftsV_cons_sLemma, shiftsV_single_tag0 tg₂]
  · unfold bnOddTop
    rw [finalCtx_cons, cx₁, finalCtx_single, cx₂]
    exact mem_insert_self'

end tailsOK

/-! ## 3. The producer is applicable (Π₁ order induction on `k`) -/

section okInduction

/-- The conclusion of one certification list: applicable at cap `9`, cut-admitting, SHIFT-FREE, `neg F` in the
final context. -/
def BnPost (tbl E Γ y F : V) : Prop :=
  ListOK tbl E ((9 : ℕ) : V) Γ y ∧ NoDrop' y ∧ shiftsV y = 0 ∧ neg LAct F ∈ finalCtx Γ y
instance bnPost_definable : 𝚫₁-Relation₅ (BnPost : V → V → V → V → V → Prop) := by
  unfold BnPost; definability

/-- The size parameters of the `sLemma` steps (`𝟏 ≤ bnum m`, `m ≤ k`, `‖k‖ ≤ L`): the fact `≤ B'·(6L + 1)`, the
derivation `≤ 2(L + 2)·nodeCost N' B' (12L + 3) + nodeCost N' B' (12L + 3)` (`NumSteps.dlen_leCode_le'`). -/
noncomputable def bQ (B' L : V) : V := B' * (6 * L + 1)
noncomputable def bD (N' B' L : V) : V := (1 + 1) * (L + 2) * nodeCost N' B' (12 * L + 3) + nodeCost N' B' (12 * L + 3)

lemma mem_final0 {Γ S x : V} (hS : NoDrop' S) (h0 : shiftsV S = 0) (hx : x ∈ Γ) : x ∈ finalCtx Γ S := by
  have := mem_finalCtx_of_mem' hS hx
  rwa [h0, shiftIterV_zero] at this

lemma bnumFact_eq_subst (t k : V) : bnumFact t k = subst LAct (t ∷ k ∷ 0) Pbnum := rfl

variable {tbl N T N' B' : V} (htbl : TableOK tbl N) (hL : LayoutTable tbl) (hR : BnRows tbl) (htblN : NumTableOK T N' B')
include htbl hL hR htblN

set_option maxHeartbeats 4000000 in
/-- **Applicability of every certification list** (over the graph; `Pb` an opaque copy of `Pbnum`, `Wn`/`Wd`/`c₁`/`c₂`
opaque copies of the pieces and counts — the motive must not mention closed quotes): from the dossier of `bnum k`
at `&j` under the cap `j + 27(‖k‖ + 1) ≤ E`, `BnPost` with the fact `bnumFact &j (bnum k)`. -/
theorem bnGraph_ok {Wn Wd c₁ c₂ Pb E : V} (hWn : Wn = numIdPieces) (hWd : Wd = walkPieces)
    (hc₁ : c₁ = descCountT walkPieces 0 (𝟏 : V)) (hc₂ : c₂ = descCountT walkPieces 0 (𝟐 : V)) (hPb : Pb = Pbnum) :
    ∀ k : V, ∀ j y Γ : V, BnGraph Wn Wd T c₁ c₂ k j y → IsFormulaSet LAct Γ → DossT Wd Γ 0 (bnum k) j →
      j + 27 * (‖k‖ + 1) ≤ E → BnPost tbl E Γ y (subst LAct (^&j ∷ bnum k ∷ 0) Pb) := by
  have hW : WalkTable tbl := hL.walkTable
  have h89 : ((8 : ℕ) : V) ≤ ((9 : ℕ) : V) := by exact_mod_cast (by decide : 8 ≤ 9)
  have hc₁le : c₁ ≤ 1 := by rw [hc₁]; exact descCountT_one_le htbl hW
  have hc₂le : c₂ ≤ 5 := by rw [hc₂]; exact descCountT_two_le htbl hW
  intro k
  induction k using ISigma1.pi1_order_induction with
  | hP => simp only [BnGraph]; definability
  | ind k ih =>
    intro j y Γ hg hΓ hD hE
    subst hWd
    rcases zero_one_or_two_le k with rfl | rfl | h2
    · -- k = 0
      rw [BnGraph.zero_iff] at hg
      subst hg
      rw [bnum_zero, qqZero_eq] at hD
      have f0 := dossT_const htbl hW isFunc_LAct_zeroIndex hD
      rw [coe_zeroIndex_eq, cTV_zero] at f0
      have hj : j + 1 ≤ E := le_trans (add_le_add le_rfl (by
        calc (1 : V) ≤ 27 := by norm_num
          _ ≤ 27 * (‖(0 : V)‖ + 1) := le_mul_of_one_le_right zero_le le_add_self)) hE
      obtain ⟨ok₁, tg₁, cx₁⟩ := nok_bnumZeroCert htbl hWn hR.1.1 ⟨hR.1.2.1, hR.1.2.2⟩ hΓ (by simp) (termLen_fvar_le hj) f0
      refine ⟨listOK_single (ok₁.mono h89), noDrop'_single (Or.inl tg₁), shiftsV_single_tag0 tg₁, ?_⟩
      rw [finalCtx_single, cx₁, hPb, ← bnumFact_eq_subst, bnum_zero]
      exact mem_insert_self'
    · -- k = 1
      rw [BnGraph.one_iff] at hg
      subst hg
      rw [bnum_one, qqOne_eq] at hD
      have f0 := dossT_const htbl hW isFunc_LAct_oneIndex hD
      rw [coe_oneIndex_eq, ← cT_one_eq] at f0
      have hj : j + 1 ≤ E := le_trans (add_le_add le_rfl (by
        calc (1 : V) ≤ 27 := by norm_num
          _ ≤ 27 * (‖(1 : V)‖ + 1) := le_mul_of_one_le_right zero_le le_add_self)) hE
      obtain ⟨ok₁, tg₁, cx₁⟩ := nok_bnumOneCert htbl hWn hR.2.1.1 ⟨hR.2.1.2.1, hR.2.1.2.2⟩ hΓ (by simp) (termLen_fvar_le hj) f0
      refine ⟨listOK_single (ok₁.mono h89), noDrop'_single (Or.inl tg₁), shiftsV_single_tag0 tg₁, ?_⟩
      rw [finalCtx_single, cx₁, hPb, ← bnumFact_eq_subst, bnum_one]
      exact mem_insert_self'
    obtain ⟨hm, hlt, he | ho⟩ := two_le_cases h2
    · -- k = 2 * m
      obtain ⟨m, hmdef⟩ : ∃ m : V, m = k / 2 := ⟨_, rfl⟩
      rw [← hmdef] at hm hlt he
      subst he
      have hlen : ‖2 * m‖ = ‖m‖ + 1 := length_two_mul_of_pos (lt_of_lt_of_le _root_.zero_lt_one hm)
      rw [hlen] at hE
      have hbm : IsSemiterm LAct 0 (bnum m) := isSemiterm_bnum_LAct 0 m
      have hEm : termLen LAct (bnum m) ≤ E := by
        refine le_trans (termLen_bnum_le_bk (n := m) le_rfl) (le_trans ?_ (le_trans le_add_self hE))
        calc 6 * ‖m‖ + 1 ≤ 27 * ‖m‖ + 54 := add_le_add (mul_le_mul_of_nonneg_right (by norm_num) zero_le) (by norm_num)
          _ = 27 * (‖m‖ + 1 + 1) := by ring
      have hEj : j + 9 ≤ E := le_trans (add_le_add le_rfl (by
        calc (9 : V) ≤ 27 * 2 := by norm_num
          _ ≤ 27 * (‖m‖ + 1 + 1) := mul_le_mul_of_nonneg_left (by rw [add_assoc, one_add_one_eq_two]; exact le_add_self) zero_le)) hE
      have hEsub : j + 3 + c₂ + 27 * (‖m‖ + 1) ≤ E := by
        refine le_trans ?_ hE
        calc j + 3 + c₂ + 27 * (‖m‖ + 1) ≤ j + 3 + 5 + 27 * (‖m‖ + 1) := add_le_add (add_le_add le_rfl hc₂le) le_rfl
          _ = j + (27 * (‖m‖ + 1) + 8) := by ring
          _ ≤ j + (27 * (‖m‖ + 1) + 27) := add_le_add le_rfl (add_le_add le_rfl (by norm_num))
          _ = j + 27 * (‖m‖ + 1 + 1) := by ring
      obtain ⟨y', _, hg', rfl⟩ := (BnGraph.even_iff hm).mp hg
      -- the dossier facts
      rw [bnum_two_mul hm] at hD
      have hD' : DossT walkPieces Γ 0 (^func 2 (mulIndex : V) ?[(𝟐 : V), bnum m]) j := hD
      obtain ⟨f1, f2, hD2, f8, hDm⟩ := dossT_pair htbl hW isFunc_LAct_mulIndex (isSemiterm_qqTwo_LAct 0) hbm hD'
      rw [coe_mulIndex_eq, ← cT_one_eq] at f1
      rw [← hc₂] at f2 f8 hDm
      have hD2' : DossT walkPieces Γ 0 (^func 2 (addIndex : V) ?[(𝟏 : V), (𝟏 : V)]) (j + 2) := hD2
      obtain ⟨f3, f4, hD1a, f6, hD1b⟩ := dossT_pair htbl hW isFunc_LAct_addIndex (isSemiterm_qqOne_LAct 0) (isSemiterm_qqOne_LAct 0) hD2'
      rw [coe_addIndex_eq, cTV_zero, show j + 2 + 1 = j + 3 by ring] at f3
      rw [← hc₁, show j + 2 + 2 = j + 4 by ring, show j + 2 + 1 = j + 3 by ring] at f4
      rw [← hc₁, show j + 2 + 2 = j + 4 by ring, show j + 2 + 3 = j + 5 by ring] at f6
      rw [show j + 2 + 2 = j + 4 by ring] at hD1a
      rw [← hc₁, show j + 2 + 3 = j + 5 by ring] at hD1b
      rw [qqOne_eq] at hD1a hD1b
      have f5 := dossT_const htbl hW isFunc_LAct_oneIndex hD1a
      have f7 := dossT_const htbl hW isFunc_LAct_oneIndex hD1b
      rw [coe_oneIndex_eq, ← cT_one_eq] at f5 f7
      -- the sub-list
      obtain ⟨ok', nd', sh', hf'⟩ := ih m hlt (j + 3 + c₂) y' Γ hg' hΓ hDm hEsub
      obtain ⟨Γ', hΓ'⟩ : ∃ Γ', Γ' = finalCtx Γ y' := ⟨_, rfl⟩
      have hΓ's : IsFormulaSet LAct Γ' := by rw [hΓ']; exact finalCtx_isFormulaSet 9 htbl hΓ ok'
      have up : ∀ {x : V}, x ∈ Γ → x ∈ Γ' := fun hx ↦ by rw [hΓ']; exact mem_final0 nd' sh' hx
      have f9 : neg LAct (bnumFact (^&(j + 3 + c₂)) (bnum m)) ∈ Γ' := by
        rw [hΓ', bnumFact_eq_subst, ← hPb]; exact hf'
      obtain ⟨okT, ndT, shT, hfT⟩ := bnEvenTail_ok htbl hL hR htblN hΓ's hm hc₁le hc₂le hEj hEm
        (up f1) (up f2) (up f3) (up f4) (up f5) (up f6) (up f7) (up f8) f9
      rw [hWn]
      refine ⟨?_, noDrop'_appendV nd' ndT, ?_, ?_⟩
      · refine listOK_appendV ok' ?_; rw [← hΓ']; exact okT
      · rw [shiftsV_appendV, sh', shT, add_zero]
      · rw [finalCtx_appendV, ← hΓ', bnum_two_mul hm, hPb, ← bnumFact_eq_subst]
        exact hfT
    · -- k = 2 * m + 1
      obtain ⟨m, hmdef⟩ : ∃ m : V, m = k / 2 := ⟨_, rfl⟩
      rw [← hmdef] at hm hlt ho
      subst ho
      have hlen : ‖2 * m + 1‖ = ‖m‖ + 1 := length_two_mul_add_one m
      rw [hlen] at hE
      have hbm : IsSemiterm LAct 0 (bnum m) := isSemiterm_bnum_LAct 0 m
      have hEm : termLen LAct (bnum m) ≤ E := by
        refine le_trans (termLen_bnum_le_bk (n := m) le_rfl) (le_trans ?_ (le_trans le_add_self hE))
        calc 6 * ‖m‖ + 1 ≤ 27 * ‖m‖ + 54 := add_le_add (mul_le_mul_of_nonneg_right (by norm_num) zero_le) (by norm_num)
          _ = 27 * (‖m‖ + 1 + 1) := by ring
      have hEj : j + 2 + 9 ≤ E := le_trans (by
        calc j + 2 + 9 = j + 11 := by ring
          _ ≤ j + 27 * 2 := add_le_add le_rfl (by norm_num)
          _ ≤ j + 27 * (‖m‖ + 1 + 1) := add_le_add le_rfl (mul_le_mul_of_nonneg_left
              (by rw [add_assoc, one_add_one_eq_two]; exact le_add_self) zero_le)) hE
      have hEsub : j + 5 + c₂ + 27 * (‖m‖ + 1) ≤ E := by
        refine le_trans ?_ hE
        calc j + 5 + c₂ + 27 * (‖m‖ + 1) ≤ j + 5 + 5 + 27 * (‖m‖ + 1) := add_le_add (add_le_add le_rfl hc₂le) le_rfl
          _ = j + (27 * (‖m‖ + 1) + 10) := by ring
          _ ≤ j + (27 * (‖m‖ + 1) + 27) := add_le_add le_rfl (add_le_add le_rfl (by norm_num))
          _ = j + 27 * (‖m‖ + 1 + 1) := by ring
      obtain ⟨y', _, hg', rfl⟩ := (BnGraph.odd_iff hm).mp hg
      -- the dossier facts of the odd numeral
      rw [bnum_two_mul_add_one hm] at hD
      have hD' : DossT walkPieces Γ 0 (^func 2 (addIndex : V) ?[(𝟐 ^* bnum m : V), (𝟏 : V)]) j := hD
      have hev : IsSemiterm LAct 0 (𝟐 ^* bnum m : V) := by simp [hbm]
      obtain ⟨g1, g2, hDe, g4, hD1⟩ := dossT_pair htbl hW isFunc_LAct_addIndex hev (isSemiterm_qqOne_LAct 0) hD'
      rw [coe_addIndex_eq, cTV_zero] at g1
      rw [qqOne_eq] at hD1
      have g5 := dossT_const htbl hW isFunc_LAct_oneIndex hD1
      rw [coe_oneIndex_eq, ← cT_one_eq] at g5
      obtain ⟨ce, hce⟩ : ∃ ce : V, ce = descCountT walkPieces 0 (𝟐 ^* bnum m : V) := ⟨_, rfl⟩
      rw [← hce] at g2 g4 g5
      have hceE : j + 3 + ce + 1 ≤ E := by
        have h1 := descCountT_walk_le htbl hW rfl hev
        rw [← hce, ← bnum_two_mul hm] at h1
        have h2 : termLen LAct (bnum (2 * m)) ≤ 6 * ‖2 * m‖ + 1 := termLen_bnum_le_bk le_rfl
        rw [length_two_mul_of_pos (lt_of_lt_of_le _root_.zero_lt_one hm)] at h2
        refine le_trans ?_ hE
        calc j + 3 + ce + 1 = j + 3 + (ce + 1) := by ring
          _ ≤ j + 3 + 2 * termLen LAct (bnum (2 * m)) := add_le_add le_rfl h1
          _ ≤ j + 3 + 2 * (6 * (‖m‖ + 1) + 1) := add_le_add le_rfl (mul_le_mul_of_nonneg_left h2 zero_le)
          _ = j + (12 * ‖m‖ + 17) := by ring
          _ ≤ j + (27 * ‖m‖ + 54) := add_le_add le_rfl (add_le_add (mul_le_mul_of_nonneg_right (by norm_num) zero_le) (by norm_num))
          _ = j + 27 * (‖m‖ + 1 + 1) := by ring
      -- the dossier facts of the even numeral at j + 2
      have hDe' : DossT walkPieces Γ 0 (^func 2 (mulIndex : V) ?[(𝟐 : V), bnum m]) (j + 2) := hDe
      obtain ⟨f1, f2, hD2, f8, hDm⟩ := dossT_pair htbl hW isFunc_LAct_mulIndex (isSemiterm_qqTwo_LAct 0) hbm hDe'
      rw [coe_mulIndex_eq, ← cT_one_eq] at f1
      rw [← hc₂] at f2 f8 hDm
      rw [show j + 2 + 3 + c₂ = j + 5 + c₂ by ring] at hDm
      have hD2' : DossT walkPieces Γ 0 (^func 2 (addIndex : V) ?[(𝟏 : V), (𝟏 : V)]) (j + 2 + 2) := hD2
      obtain ⟨f3, f4, hD1a, f6, hD1b⟩ := dossT_pair htbl hW isFunc_LAct_addIndex (isSemiterm_qqOne_LAct 0) (isSemiterm_qqOne_LAct 0) hD2'
      rw [coe_addIndex_eq, cTV_zero, show j + 2 + 2 + 1 = j + 2 + 3 by ring] at f3
      rw [← hc₁, show j + 2 + 2 + 1 = j + 2 + 3 by ring, show j + 2 + 2 + 2 = j + 2 + 4 by ring] at f4
      rw [← hc₁, show j + 2 + 2 + 2 = j + 2 + 4 by ring, show j + 2 + 2 + 3 = j + 2 + 5 by ring] at f6
      rw [show j + 2 + 2 + 2 = j + 2 + 4 by ring] at hD1a
      rw [← hc₁, show j + 2 + 2 + 3 = j + 2 + 5 by ring] at hD1b
      rw [qqOne_eq] at hD1a hD1b
      have f5 := dossT_const htbl hW isFunc_LAct_oneIndex hD1a
      have f7 := dossT_const htbl hW isFunc_LAct_oneIndex hD1b
      rw [coe_oneIndex_eq, ← cT_one_eq] at f5 f7
      -- the sub-list
      obtain ⟨ok', nd', sh', hf'⟩ := ih m hlt (j + 5 + c₂) y' Γ hg' hΓ hDm hEsub
      obtain ⟨Γ', hΓ'⟩ : ∃ Γ', Γ' = finalCtx Γ y' := ⟨_, rfl⟩
      have hΓ's : IsFormulaSet LAct Γ' := by rw [hΓ']; exact finalCtx_isFormulaSet 9 htbl hΓ ok'
      have up : ∀ {x : V}, x ∈ Γ → x ∈ Γ' := fun hx ↦ by rw [hΓ']; exact mem_final0 nd' sh' hx
      have f9 : neg LAct (bnumFact (^&(j + 2 + 3 + c₂)) (bnum m)) ∈ Γ' := by
        rw [hΓ', bnumFact_eq_subst, ← hPb, show j + 2 + 3 + c₂ = j + 5 + c₂ by ring]; exact hf'
      -- the even tail at j + 2
      obtain ⟨okT, ndT, shT, hfT⟩ := bnEvenTail_ok htbl hL hR htblN hΓ's hm hc₁le hc₂le hEj hEm
        (up f1) (up f2) (up f3) (up f4) (up f5) (up f6) (up f7) (up f8) f9
      obtain ⟨Γ'', hΓ''⟩ : ∃ Γ'', Γ'' = finalCtx Γ' (bnEvenTail numIdPieces T c₁ c₂ m (j + 2)) := ⟨_, rfl⟩
      have hΓ''s : IsFormulaSet LAct Γ'' := by rw [hΓ'']; exact finalCtx_isFormulaSet 9 htbl hΓ's okT
      have up' : ∀ {x : V}, x ∈ Γ → x ∈ Γ'' := fun hx ↦ by rw [hΓ'']; exact mem_final0 ndT shT (up hx)
      have g3 : neg LAct (bnumFact (^&(j + 2)) (𝟐 ^* bnum m)) ∈ Γ'' := by rw [hΓ'']; exact hfT
      -- the odd top
      obtain ⟨okO, ndO, shO, hfO⟩ := bnOddTop_ok htbl hL hR htblN hΓ''s hm hceE hEm (up' g1) (up' g2) g3 (up' g4) (up' g5)
      rw [hWn, bnum_two_mul hm, ← hce]
      refine ⟨?_, noDrop'_appendV nd' (noDrop'_appendV ndT ndO), ?_, ?_⟩
      · refine listOK_appendV ok' ?_
        rw [← hΓ']
        refine listOK_appendV okT ?_
        rw [← hΓ'']
        exact okO
      · rw [shiftsV_appendV, shiftsV_appendV, sh', shT, shO, add_zero, add_zero]
      · rw [finalCtx_appendV, finalCtx_appendV, ← hΓ', ← hΓ'', bnum_two_mul_add_one hm, hPb, ← bnumFact_eq_subst]
        exact hfO

set_option maxHeartbeats 2000000 in
/-- **Length and size discipline** of every certification list: `len ≤ 8‖k‖ + 1`, `SizeOK (bQ B' L) (bD N' B' L)`
for `‖k‖ ≤ L`. -/
theorem bnGraph_len_size {Wn Wd c₁ c₂ : V} (hWn : Wn = numIdPieces) :
    ∀ k : V, ∀ L : V, ‖k‖ ≤ L → ∀ j y : V, BnGraph Wn Wd T c₁ c₂ k j y →
      len y ≤ 8 * ‖k‖ + 1 ∧ SizeOK (bQ B' L) (bD N' B' L) y := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hPle, -, hB1⟩ := id htblN
  -- the size data of the `sLemma` `𝟏 ≤ bnum m` for `‖m‖ ≤ L`
  have hLem : ∀ {m L : V}, 1 ≤ m → ‖m‖ ≤ L →
      StepSizeOK (bQ B' L) (bD N' B' L) (sLemma (leFact (𝟏 : V) (bnum m)) (leCode T 1 m)) := by
    intro m L hm hmL
    refine stepSizeOK_sLemma ?_ ?_
    · have h6 : (1 : V) ≤ 6 * L + 1 := le_add_self
      have hb : termLen LAct (bnum m) ≤ 6 * L + 1 :=
        le_trans (termLen_bnum_le_bk (n := m) le_rfl) (add_le_add (mul_le_mul_of_nonneg_left hmL zero_le) le_rfl)
      have h1 : termLen LAct (𝟏 : V) ≤ 6 * L + 1 := by rw [termLen_qqOne isFunc_LAct_oneIndex]; exact h6
      refine le_trans (formulaLen_leFact_le h6 (isSemiterm_qqOne_LAct 0) (isSemiterm_bnum_LAct 0 m) h1 hb) ?_
      unfold bQ
      exact mul_le_mul_of_nonneg_right hPle zero_le
    · refine le_trans (dlen_leCode_le' htblN hm) ?_
      unfold bD
      rw [length_one]
      have hn : nodeCost N' B' (12 * ‖m‖ + 3) ≤ nodeCost N' B' (12 * L + 3) :=
        nodeCost_mono (add_le_add (mul_le_mul_of_nonneg_left hmL zero_le) le_rfl)
      exact add_le_add (mul_le_mul (mul_le_mul_of_nonneg_left (add_le_add hmL le_rfl) zero_le) hn zero_le zero_le) hn
  have hTailE : ∀ {m L j : V}, 1 ≤ m → ‖m‖ ≤ L → SizeOK (bQ B' L) (bD N' B' L) (bnEvenTail Wn T c₁ c₂ m j) := by
    intro m L j hm hmL
    unfold bnEvenTail
    refine sizeOK_cons (stepSizeOK_horn0 (by rw [hWn, mkStep_numId_41]; exact ltag_eqRefl rfl _)) ?_
    refine sizeOK_cons (stepSizeOK_horn0 (by rw [hWn, mkStep_numId_71]; exact ltag_eqOfFunc rfl _)) ?_
    refine sizeOK_cons (stepSizeOK_horn0 (by rw [hWn, mkStep_numId_41]; exact ltag_eqRefl rfl _)) ?_
    refine sizeOK_cons (stepSizeOK_horn0 (by rw [hWn, mkStep_numId_59]; exact ltag_congAdj rfl _)) ?_
    refine sizeOK_cons (hLem hm hmL) ?_
    exact sizeOK_single (stepSizeOK_horn0 (ntag_bnumEvenCert hWn _))
  have hTopO : ∀ {m L j ce : V}, 1 ≤ m → ‖m‖ ≤ L → SizeOK (bQ B' L) (bD N' B' L) (bnOddTop Wn T ce m j) := by
    intro m L j ce hm hmL
    unfold bnOddTop
    refine sizeOK_cons (hLem hm hmL) ?_
    exact sizeOK_single (stepSizeOK_horn0 (ntag_bnumOddOfEven hWn _))
  intro k
  induction k using ISigma1.pi1_order_induction with
  | hP => simp only [BnGraph, bQ, bD]; definability
  | ind k ih =>
    intro L hkL j y hg
    rcases zero_one_or_two_le k with rfl | rfl | h2
    · rw [BnGraph.zero_iff] at hg
      subst hg
      refine ⟨?_, sizeOK_single (stepSizeOK_horn0 (ntag_bnumZeroCert hWn _))⟩
      rw [len_adjoin, len_nil, zero_add]; exact le_add_self
    · rw [BnGraph.one_iff] at hg
      subst hg
      refine ⟨?_, sizeOK_single (stepSizeOK_horn0 (ntag_bnumOneCert hWn _))⟩
      rw [len_adjoin, len_nil, zero_add]; exact le_add_self
    obtain ⟨hm, hlt, he | ho⟩ := two_le_cases h2
    · obtain ⟨m, hmdef⟩ : ∃ m : V, m = k / 2 := ⟨_, rfl⟩
      rw [← hmdef] at hm hlt he
      subst he
      have hlen : ‖2 * m‖ = ‖m‖ + 1 := length_two_mul_of_pos (lt_of_lt_of_le _root_.zero_lt_one hm)
      rw [hlen] at hkL ⊢
      have hmL : ‖m‖ ≤ L := le_trans le_self_add hkL
      obtain ⟨y', _, hg', rfl⟩ := (BnGraph.even_iff hm).mp hg
      obtain ⟨hl, hs⟩ := ih m hlt L hmL _ _ hg'
      refine ⟨?_, sizeOK_appendV hs (hTailE hm hmL)⟩
      rw [len_appendV, len_bnEvenTail]
      calc len y' + 6 ≤ 8 * ‖m‖ + 1 + 6 := add_le_add hl le_rfl
        _ ≤ 8 * (‖m‖ + 1) + 1 := by
          rw [show 8 * (‖m‖ + 1) + 1 = 8 * ‖m‖ + 1 + 8 by ring]
          exact add_le_add le_rfl (by norm_num)
    · obtain ⟨m, hmdef⟩ : ∃ m : V, m = k / 2 := ⟨_, rfl⟩
      rw [← hmdef] at hm hlt ho
      subst ho
      have hlen : ‖2 * m + 1‖ = ‖m‖ + 1 := length_two_mul_add_one m
      rw [hlen] at hkL ⊢
      have hmL : ‖m‖ ≤ L := le_trans le_self_add hkL
      obtain ⟨y', _, hg', rfl⟩ := (BnGraph.odd_iff hm).mp hg
      obtain ⟨hl, hs⟩ := ih m hlt L hmL _ _ hg'
      refine ⟨?_, sizeOK_appendV hs (sizeOK_appendV (hTailE hm hmL) (hTopO hm hmL))⟩
      rw [len_appendV, len_appendV, len_bnEvenTail, len_bnOddTop]
      calc len y' + (6 + 2) ≤ 8 * ‖m‖ + 1 + (6 + 2) := add_le_add hl le_rfl
        _ = 8 * (‖m‖ + 1) + 1 := by ring

/-- **The certification list of `bnum k` is applicable** (the exact shape `Pin.BnumOracle` needs, plus the length
and size discipline): from the dossier of `bnum k` at `&j` under `j + 27(‖k‖ + 1) ≤ E`, the list
`bnumSteps numIdPieces walkPieces T k j` is applicable at cap `9`, cut-admitting, shift-free, of length
`≤ 8‖k‖ + 1`, `SizeOK (bQ B' ‖k‖) (bD N' B' ‖k‖)`, and leaves `bnumFact &j (bnum k)`. -/
theorem bnumSteps_ok {E Γ k j : V} (hΓ : IsFormulaSet LAct Γ) (hD : DossT walkPieces Γ 0 (bnum k) j)
    (hE : j + 27 * (‖k‖ + 1) ≤ E) :
    ListOK tbl E ((9 : ℕ) : V) Γ (bnumSteps numIdPieces walkPieces T k j) ∧
    NoDrop' (bnumSteps numIdPieces walkPieces T k j) ∧ shiftsV (bnumSteps numIdPieces walkPieces T k j) = 0 ∧
    len (bnumSteps numIdPieces walkPieces T k j) ≤ 8 * ‖k‖ + 1 ∧
    SizeOK (bQ B' ‖k‖) (bD N' B' ‖k‖) (bnumSteps numIdPieces walkPieces T k j) ∧
    neg LAct (bnumFact (^&j) (bnum k)) ∈ finalCtx Γ (bnumSteps numIdPieces walkPieces T k j) := by
  obtain ⟨Pb, hPb⟩ : ∃ P : V, P = Pbnum := ⟨_, rfl⟩
  have hg := bnumSteps_graph numIdPieces walkPieces T k j
  obtain ⟨ok, nd, sh, hf⟩ := bnGraph_ok htbl hL hR htblN rfl rfl rfl rfl hPb k j _ Γ hg hΓ hD hE
  obtain ⟨hl, hs⟩ := bnGraph_len_size htbl hL hR htblN (Wd := walkPieces) (c₁ := descCountT walkPieces 0 (𝟏 : V))
    (c₂ := descCountT walkPieces 0 (𝟐 : V)) rfl k ‖k‖ le_rfl j _ hg
  refine ⟨ok, nd, sh, hl, hs, ?_⟩
  rw [bnumFact_eq_subst, ← hPb]
  exact hf

end okInduction

end ArithS
