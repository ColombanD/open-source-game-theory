import ArithS.Necessitation.RowInst
import ArithS.Necessitation.ChainOcc

/-!
# ArithS.Necessitation.Describe — the bottom-up syntax walk as a Σ₁ step-list producer

`M4_BOUNDED_HBL/DESIGN_describe.md`: from a context `Γ`, introduce one eigenvariable per node of
a code's syntax tree and leave, for the top node's eigenvariable `&0`, its SHAPE fact and its
FORMATION fact (`(isSemiterm LAct).pi n &0`, …) — as a LIST of `Chain.lean` steps, a Σ₁
function of the code alone (never of `Γ`), so that `chainCode_proof`/`dlen_chainCode_le` give
the derivation and its length.

## Part 0 — infrastructure on step lists

* `appendV` — vector append (`VecRec`); `shiftsAux/shiftsV` — the number of eigenvariable
  steps (tags 2/3) in a list; `shiftIterV/termShiftIterV` — V-indexed iterates of `shift`/
  `termShift` (what `s` shifting steps do to a fact about `&i`: `&i ↦ &(i + s)`, chain numerals
  fixed);
* the context vector of an appended list is the two context vectors glued
  (`ctxVecAux_congr`, `nth_ctxVec_appendV_le`, `nth_ctxVec_appendV_add`, `final_appendV`), so
  `ListOK` (every step applicable at its context) composes (`listOK_appendV`);
* **transport**: a fact in the initial context reappears in the final one, shifted once per
  eigenvariable step, provided the list drops nothing (`mem_final_of_mem`).

## Part 1 — the row table of the walk (D1)

`walkRowsB`, the fixed order of the 40 rows the walk uses with index constants `rIdx_<row>`;
`walkPieces : V` (every model), the table of `⟪tag, ⟪as, c⟫⟫` decompositions read off
`RowInst`'s `row_<row>_as/_c/_R`; `WalkTable tbl` (the proof-table has the right matrices at the
right indices, each a `TableOK` row) and `exists_walkTable : ∃ N, ∀ V, ∃ tbl, TableOK tbl N ∧
WalkTable tbl` from `Lib.univ_code` row by row.

## Part 2 — the term walk (D2 for terms)

`descT W n t = ⟪count, steps⟫` by a `TermRec` construction with the parameters `(W, n)` —
terms carry no arity change — with the vector fold `descVecAux` (primitive recursion from the
END of the vector: tail first) and the node emitters `bvarNode` (the `z < n` chain `ltSteps`
+ 3 steps), `fvarNode`, `funcNode`, `adjNode`, `nilNode`; `describeT`, `descCountT`,
`describeTV`, `descCountTV` and their per-constructor equations.
-/

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1
open LAct

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ## Part 0 — infrastructure on step lists -/

/-! ### 0.1 Vector append -/

namespace AppendV

def blueprint : VecRec.Blueprint 1 where
  nil := .mkSigma “y w. y = w”
  adjoin := .mkSigma “y x xs ih w. !adjoinDef y x ih”

noncomputable def construction : VecRec.Construction V blueprint where
  nil v := v 0
  adjoin _ x _ ih := x ∷ ih
  nil_defined := .mk fun v ↦ by simp [blueprint]
  adjoin_defined := .mk fun v ↦ by simp [blueprint]

end AppendV

/-- `appendV u w` — the vector `u` followed by the vector `w`. -/
noncomputable def appendV (u w : V) : V := AppendV.construction.result ![w] u

@[simp] lemma appendV_nil (w : V) : appendV 0 w = w := by simp [appendV, AppendV.construction]
@[simp] lemma appendV_adjoin (x u w : V) : appendV (x ∷ u) w = x ∷ appendV u w := by
  simp [appendV, AppendV.construction]

def appendVDef : 𝚺₁.Semisentence 3 := AppendV.blueprint.resultDef

instance appendV_defined : 𝚺₁-Function₂ (appendV : V → V → V) via appendVDef := .mk
  fun v ↦ by simp [AppendV.construction.eval_resultDef, appendVDef]; rfl
instance appendV_definable : 𝚺₁-Function₂ (appendV : V → V → V) := appendV_defined.to_definable

lemma appendV_vecOf : ∀ (xs ys : List V), appendV (vecOf xs) (vecOf ys) = vecOf (xs ++ ys)
  | [], ys => by simp
  | x :: xs, ys => by simp [appendV_vecOf xs ys]

@[simp] lemma len_appendV (u w : V) : len (appendV u w) = len u + len w := by
  induction u using adjoin_ISigma1.sigma1_succ_induction with
  | hP => definability
  | nil => simp
  | adjoin x u ih => rw [appendV_adjoin, len_adjoin, len_adjoin, ih]; ring

lemma nth_appendV_lt (u w : V) : ∀ i < len u, (appendV u w).[i] = u.[i] := by
  induction u using adjoin_ISigma1.pi1_succ_induction with
  | hP => definability
  | nil => intro i hi; simp at hi
  | adjoin x u ih =>
    intro i hi
    rcases zero_or_succ i with rfl | ⟨i, rfl⟩
    · simp
    · rw [appendV_adjoin, nth_adjoin_succ, nth_adjoin_succ]
      exact ih i (by rw [len_adjoin] at hi; exact lt_of_add_lt_add_right hi)

lemma nth_appendV_add (u w : V) : ∀ i, (appendV u w).[len u + i] = w.[i] := by
  induction u using adjoin_ISigma1.pi1_succ_induction with
  | hP => definability
  | nil => intro i; simp
  | adjoin x u ih =>
    intro i
    rw [appendV_adjoin, len_adjoin, show len u + 1 + i = (len u + i) + 1 by ring, nth_adjoin_succ, ih]

@[simp] lemma appendV_nil_right (u : V) : appendV u 0 = u := by
  induction u using adjoin_ISigma1.sigma1_succ_induction with
  | hP => definability
  | nil => simp
  | adjoin x u ih => rw [appendV_adjoin, ih]

lemma appendV_assoc (u v w : V) : appendV (appendV u v) w = appendV u (appendV v w) := by
  induction u using adjoin_ISigma1.sigma1_succ_induction with
  | hP => definability
  | nil => simp
  | adjoin x u ih => rw [appendV_adjoin, appendV_adjoin, appendV_adjoin, ih]

/-! ### 0.2 Iterated shifts (V-indexed) -/

namespace ShiftIterV

variable (L : Language) [L.Encodable] [L.LORDefinable]

noncomputable def blueprint : PR.Blueprint 1 where
  zero := .mkSigma “y x. y = x”
  succ := .mkSigma “y ih i x. ∃ s, !(shiftGraph L) s ih ∧ y = s”

noncomputable def construction : PR.Construction V (blueprint L) where
  zero := fun v ↦ v 0
  succ := fun _ _ ih ↦ shift L ih
  zero_defined := .mk fun v ↦ by simp [blueprint]
  succ_defined := .mk fun v ↦ by simp [blueprint, shift.defined.iff]

end ShiftIterV

namespace TermShiftIterV

variable (L : Language) [L.Encodable] [L.LORDefinable]

noncomputable def blueprint : PR.Blueprint 1 where
  zero := .mkSigma “y x. y = x”
  succ := .mkSigma “y ih i x. ∃ s, !(termShiftGraph L) s ih ∧ y = s”

noncomputable def construction : PR.Construction V (blueprint L) where
  zero := fun v ↦ v 0
  succ := fun _ _ ih ↦ termShift L ih
  zero_defined := .mk fun v ↦ by simp [blueprint]
  succ_defined := .mk fun v ↦ by simp [blueprint, termShift.defined.iff]

end TermShiftIterV

/-- `shiftIterV x k = shift^[k] x`, `k : V`. -/
noncomputable def shiftIterV (x k : V) : V := (ShiftIterV.construction LAct).result ![x] k
/-- `termShiftIterV t k = termShift^[k] t`, `k : V`. -/
noncomputable def termShiftIterV (t k : V) : V := (TermShiftIterV.construction LAct).result ![t] k

@[simp] lemma shiftIterV_zero (x : V) : shiftIterV x 0 = x := by simp [shiftIterV, ShiftIterV.construction]
@[simp] lemma shiftIterV_succ (x k : V) : shiftIterV x (k + 1) = shift LAct (shiftIterV x k) := by
  simp [shiftIterV, ShiftIterV.construction]
@[simp] lemma termShiftIterV_zero (t : V) : termShiftIterV t 0 = t := by
  simp [termShiftIterV, TermShiftIterV.construction]
@[simp] lemma termShiftIterV_succ (t k : V) : termShiftIterV t (k + 1) = termShift LAct (termShiftIterV t k) := by
  simp [termShiftIterV, TermShiftIterV.construction]

noncomputable def shiftIterVDef : 𝚺₁.Semisentence 3 :=
  (ShiftIterV.blueprint LAct).resultDef |>.rew (Rew.subst ![#0, #2, #1])
noncomputable def termShiftIterVDef : 𝚺₁.Semisentence 3 :=
  (TermShiftIterV.blueprint LAct).resultDef |>.rew (Rew.subst ![#0, #2, #1])

instance shiftIterV_defined : 𝚺₁-Function₂ (shiftIterV : V → V → V) via shiftIterVDef := .mk
  fun v ↦ by simp [(ShiftIterV.construction LAct).result_defined_iff, shiftIterVDef]; rfl
instance shiftIterV_definable : 𝚺₁-Function₂ (shiftIterV : V → V → V) := shiftIterV_defined.to_definable
instance termShiftIterV_defined : 𝚺₁-Function₂ (termShiftIterV : V → V → V) via termShiftIterVDef := .mk
  fun v ↦ by simp [(TermShiftIterV.construction LAct).result_defined_iff, termShiftIterVDef]; rfl
instance termShiftIterV_definable : 𝚺₁-Function₂ (termShiftIterV : V → V → V) :=
  termShiftIterV_defined.to_definable

lemma termShiftIterV_fvar (x : V) : ∀ k : V, termShiftIterV (^&x) k = ^&(x + k) := by
  intro k
  induction k using ISigma1.sigma1_succ_induction with
  | hP => definability
  | zero => simp
  | succ k ih => rw [termShiftIterV_succ, ih, termShift_fvar, add_assoc]

lemma termShiftIterV_cTV (n : V) : ∀ k : V, termShiftIterV (cTV n) k = cTV n := by
  intro k
  induction k using ISigma1.sigma1_succ_induction with
  | hP => definability
  | zero => simp
  | succ k ih => rw [termShiftIterV_succ, ih, termShift_cTV]

lemma termShiftIterV_add (t : V) : ∀ k j : V, termShiftIterV t (k + j) = termShiftIterV (termShiftIterV t k) j := by
  intro k j
  induction j using ISigma1.sigma1_succ_induction with
  | hP => definability
  | zero => simp
  | succ j ih => rw [← add_assoc, termShiftIterV_succ, termShiftIterV_succ, ih]

lemma shiftIterV_add (x : V) : ∀ k j : V, shiftIterV x (k + j) = shiftIterV (shiftIterV x k) j := by
  intro k j
  induction j using ISigma1.sigma1_succ_induction with
  | hP => definability
  | zero => simp
  | succ j ih => rw [← add_assoc, shiftIterV_succ, shiftIterV_succ, ih]

lemma isSemiterm_termShiftIterV {t : V} (ht : IsSemiterm LAct 0 t) : ∀ k : V, IsSemiterm LAct 0 (termShiftIterV t k) := by
  intro k
  induction k using ISigma1.sigma1_succ_induction with
  | hP => definability
  | zero => simpa
  | succ k ih => rw [termShiftIterV_succ]; exact ih.termShift

lemma isFormula_shiftIterV {x : V} (hx : IsFormula LAct x) : ∀ k : V, IsFormula LAct (shiftIterV x k) := by
  intro k
  induction k using ISigma1.sigma1_succ_induction with
  | hP => definability
  | zero => simpa
  | succ k ih => rw [shiftIterV_succ]; exact ih.shift

/-! ### 0.3 The number of eigenvariable steps in a list -/

namespace ShiftsAux

noncomputable def blueprint : PR.Blueprint 1 where
  zero := .mkSigma “y S. y = 0”
  succ := .mkSigma “y ih i S. ∃ s, !nthDef s S i ∧ ∃ t, !pi₁Def t s ∧
    ((t = 2 ∨ t = 3) → y = ih + 1) ∧ (t ≠ 2 → t ≠ 3 → y = ih)”

noncomputable def construction : PR.Construction V blueprint where
  zero := fun _ ↦ 0
  succ := fun v i ih ↦ if sTag (v 0).[i] = 2 ∨ sTag (v 0).[i] = 3 then ih + 1 else ih
  zero_defined := .mk fun v ↦ by simp [blueprint]
  succ_defined := .mk fun v ↦ by
    simp [blueprint, sTag]
    by_cases h2 : π₁ (v 3).[v 2] = 2
    · simp [h2]
    by_cases h3 : π₁ (v 3).[v 2] = 3
    · simp [h3]
    · simp [h2, h3]

end ShiftsAux

/-- `shiftsAux S j` — the number of eigenvariable steps (tags 2/3) among the first `j` steps. -/
noncomputable def shiftsAux (S j : V) : V := ShiftsAux.construction.result ![S] j
/-- `shiftsV S` — the number of eigenvariable steps in the whole list. -/
noncomputable def shiftsV (S : V) : V := shiftsAux S (len S)

@[simp] lemma shiftsAux_zero (S : V) : shiftsAux S 0 = 0 := by simp [shiftsAux, ShiftsAux.construction]
lemma shiftsAux_succ (S j : V) :
    shiftsAux S (j + 1) = if sTag S.[j] = 2 ∨ sTag S.[j] = 3 then shiftsAux S j + 1 else shiftsAux S j := by
  simp [shiftsAux, ShiftsAux.construction]

noncomputable def shiftsAuxDef : 𝚺₁.Semisentence 3 :=
  ShiftsAux.blueprint.resultDef |>.rew (Rew.subst ![#0, #2, #1])

instance shiftsAux_defined : 𝚺₁-Function₂ (shiftsAux : V → V → V) via shiftsAuxDef := .mk
  fun v ↦ by simp [ShiftsAux.construction.result_defined_iff, shiftsAuxDef]; rfl
instance shiftsAux_definable : 𝚺₁-Function₂ (shiftsAux : V → V → V) := shiftsAux_defined.to_definable

noncomputable def shiftsVDef : 𝚺₁.Semisentence 2 := .mkSigma “y S. ∃ n, !lenDef n S ∧ !shiftsAuxDef y S n”

instance shiftsV_defined : 𝚺₁-Function₁ (shiftsV : V → V) via shiftsVDef := .mk
  fun v ↦ by simp [shiftsVDef, shiftsAux_defined.iff, shiftsV]
instance shiftsV_definable : 𝚺₁-Function₁ (shiftsV : V → V) := shiftsV_defined.to_definable

lemma shiftsAux_succ_of_shift {S j : V} (h : sTag S.[j] = 2 ∨ sTag S.[j] = 3) :
    shiftsAux S (j + 1) = shiftsAux S j + 1 := by rw [shiftsAux_succ, if_pos h]
lemma shiftsAux_succ_of_noShift {S j : V} (h : ¬(sTag S.[j] = 2 ∨ sTag S.[j] = 3)) :
    shiftsAux S (j + 1) = shiftsAux S j := by rw [shiftsAux_succ, if_neg h]

/-- `shiftsAux` depends only on the first `j` entries. -/
lemma shiftsAux_congr {S S' : V} : ∀ j, (∀ i < j, S.[i] = S'.[i]) → shiftsAux S j = shiftsAux S' j := by
  intro j
  induction j using ISigma1.sigma1_succ_induction with
  | hP => definability
  | zero => intro _; simp
  | succ j ih =>
    intro h
    rw [shiftsAux_succ, shiftsAux_succ, h j (lt_add_one j), ih (fun i hi ↦ h i (lt_trans hi (lt_add_one j)))]

lemma shiftsAux_add {S S' : V} (n : V) : ∀ k, (∀ i < k, S'.[i] = S.[n + i]) →
    shiftsAux S (n + k) = shiftsAux S n + shiftsAux S' k := by
  intro k
  induction k using ISigma1.sigma1_succ_induction with
  | hP => definability
  | zero => intro _; simp
  | succ k ih =>
    intro h
    rw [← add_assoc, shiftsAux_succ, shiftsAux_succ, ih (fun i hi ↦ h i (lt_trans hi (lt_add_one k))),
      h k (lt_add_one k)]
    split_ifs <;> ring

/-- `shiftsV (appendV S₁ S₂) = shiftsV S₁ + shiftsV S₂`. -/
lemma shiftsV_appendV (S₁ S₂ : V) : shiftsV (appendV S₁ S₂) = shiftsV S₁ + shiftsV S₂ := by
  unfold shiftsV
  rw [len_appendV, shiftsAux_add (len S₁) (len S₂) (fun i _ ↦ (nth_appendV_add S₁ S₂ i).symm),
    shiftsAux_congr (len S₁) (fun i hi ↦ nth_appendV_lt S₁ S₂ i hi)]

/-! ### 0.4 The context vector of an appended list -/

/-- `ctxVecAux` depends only on the first `n` entries of the list. -/
lemma ctxVecAux_congr (Γ₀ : V) {S S' : V} : ∀ n, (∀ i < n, S.[i] = S'.[i]) → ctxVecAux Γ₀ S n = ctxVecAux Γ₀ S' n := by
  intro n
  induction n using ISigma1.sigma1_succ_induction with
  | hP => definability
  | zero => intro _; simp
  | succ n ih =>
    intro h
    rw [ctxVecAux_succ, ctxVecAux_succ, ih (fun i hi ↦ h i (lt_trans hi (lt_add_one n))), h n (lt_add_one n)]

/-- The final context of a list. -/
noncomputable def finalCtx (Γ₀ S : V) : V := (ctxVec Γ₀ S).[len S]

noncomputable def finalCtxDef : 𝚺₁.Semisentence 3 :=
  .mkSigma “y Γ₀ S. ∃ n, !lenDef n S ∧ ∃ c, !ctxVecDef c Γ₀ S ∧ !nthDef y c n”

instance finalCtx_defined : 𝚺₁-Function₂ (finalCtx : V → V → V) via finalCtxDef := .mk
  fun v ↦ by simp [finalCtxDef, ctxVec_defined.iff, finalCtx]
instance finalCtx_definable : 𝚺₁-Function₂ (finalCtx : V → V → V) := finalCtx_defined.to_definable

/-- Entries of the context vector of `appendV S₁ S₂` up to `len S₁` are those of `S₁`. -/
lemma nth_ctxVec_appendV_le (Γ₀ S₁ S₂ : V) {i : V} (hi : i ≤ len S₁) :
    (ctxVec Γ₀ (appendV S₁ S₂)).[i] = (ctxVec Γ₀ S₁).[i] := by
  unfold ctxVec
  rw [len_appendV, nth_ctxVecAux_add Γ₀ (appendV S₁ S₂) (len S₂) (len S₁) i hi,
    ctxVecAux_congr Γ₀ (len S₁) (fun j hj ↦ nth_appendV_lt S₁ S₂ j hj)]

/-- Entries of the context vector of `appendV S₁ S₂` beyond `len S₁` are those of `S₂` started at
the final context of `S₁`. -/
lemma nth_ctxVec_appendV_add (Γ₀ S₁ S₂ : V) : ∀ i ≤ len S₂,
    (ctxVec Γ₀ (appendV S₁ S₂)).[len S₁ + i] = (ctxVec (finalCtx Γ₀ S₁) S₂).[i] := by
  intro i
  induction i using ISigma1.sigma1_succ_induction with
  | hP => definability
  | zero => intro _; rw [add_zero, nth_ctxVec_appendV_le Γ₀ S₁ S₂ le_rfl, nth_ctxVec_zero]; rfl
  | succ i ih =>
    intro hi
    have hi' : i < len S₂ := lt_of_lt_of_le (lt_add_one i) hi
    rw [← add_assoc, nth_ctxVec_succ Γ₀ (appendV S₁ S₂) (by rw [len_appendV]; exact (add_lt_add_iff_left (len S₁)).mpr hi'),
      nth_ctxVec_succ _ S₂ hi', ih (le_of_lt hi'), nth_appendV_add]

lemma finalCtx_appendV (Γ₀ S₁ S₂ : V) : finalCtx Γ₀ (appendV S₁ S₂) = finalCtx (finalCtx Γ₀ S₁) S₂ := by
  unfold finalCtx
  rw [len_appendV, nth_ctxVec_appendV_add Γ₀ S₁ S₂ (len S₂) le_rfl]
  rfl

/-- **Every step of the list is applicable at its context.** -/
def ListOK (tbl E M Γ₀ S : V) : Prop := ∀ i < len S, StepOK tbl E M (ctxVec Γ₀ S).[i] S.[i]

instance listOK_definable : 𝚫₁-Relation₅ (ListOK : V → V → V → V → V → Prop) := by
  unfold ListOK; definability

lemma listOK_appendV {tbl E M Γ₀ S₁ S₂ : V} (h₁ : ListOK tbl E M Γ₀ S₁) (h₂ : ListOK tbl E M (finalCtx Γ₀ S₁) S₂) :
    ListOK tbl E M Γ₀ (appendV S₁ S₂) := by
  intro i hi
  rw [len_appendV] at hi
  rcases lt_or_ge i (len S₁) with h | h
  · rw [nth_ctxVec_appendV_le Γ₀ S₁ S₂ (le_of_lt h), nth_appendV_lt S₁ S₂ i h]
    exact h₁ i h
  · obtain ⟨j, rfl⟩ : ∃ j, i = len S₁ + j := ⟨i - len S₁, (add_tsub_cancel_of_le h).symm⟩
    have hj : j < len S₂ := lt_of_add_lt_add_left hi
    rw [nth_ctxVec_appendV_add Γ₀ S₁ S₂ j (le_of_lt hj), nth_appendV_add]
    exact h₂ j hj

lemma listOK_nil (tbl E M Γ₀ : V) : ListOK tbl E M Γ₀ 0 := fun i hi ↦ by simp at hi

lemma finalCtx_nil (Γ₀ : V) : finalCtx Γ₀ 0 = Γ₀ := by simp [finalCtx]

/-- A one-step list. -/
lemma listOK_single {tbl E M Γ₀ s : V} (h : StepOK tbl E M Γ₀ s) : ListOK tbl E M Γ₀ ?[s] := by
  intro i hi
  rw [len_adjoin, len_nil, zero_add] at hi
  rcases zero_or_succ i with rfl | ⟨i, rfl⟩
  · simpa using h
  · exact absurd hi (not_lt.mpr le_add_self)

lemma finalCtx_single (Γ₀ s : V) : finalCtx Γ₀ ?[s] = ctxAfter Γ₀ s := by
  unfold finalCtx
  have h := nth_ctxVec_succ Γ₀ (?[s]) (i := 0) (by simp)
  rw [zero_add] at h
  rw [len_adjoin, len_nil, zero_add, h, nth_ctxVec_zero, nth_adjoin_zero]

lemma finalCtx_isFormulaSet (M : ℕ) {tbl N E Γ₀ S : V} (htbl : TableOK tbl N) (hΓ₀ : IsFormulaSet LAct Γ₀)
    (hok : ListOK tbl E (M : V) Γ₀ S) : IsFormulaSet LAct (finalCtx Γ₀ S) :=
  ctxVec_isFormulaSet M htbl hΓ₀ hok (len S) le_rfl

/-! ### 0.5 Transport of facts through a list -/

/-- **A well-tagged list**: every step carries one of the five non-dropping tags. -/
def NoDrop (S : V) : Prop :=
  ∀ i < len S, sTag S.[i] = 0 ∨ sTag S.[i] = 1 ∨ sTag S.[i] = 2 ∨ sTag S.[i] = 3 ∨ sTag S.[i] = 4

instance noDrop_definable : 𝚫₁-Predicate (NoDrop : V → Prop) := by
  unfold NoDrop sTag; definability

lemma noDrop_nil : NoDrop (0 : V) := fun i hi ↦ by simp at hi

lemma noDrop_appendV {S₁ S₂ : V} (h₁ : NoDrop S₁) (h₂ : NoDrop S₂) : NoDrop (appendV S₁ S₂) := by
  intro i hi
  rw [len_appendV] at hi
  rcases lt_or_ge i (len S₁) with h | h
  · rw [nth_appendV_lt S₁ S₂ i h]; exact h₁ i h
  · obtain ⟨j, rfl⟩ : ∃ j, i = len S₁ + j := ⟨i - len S₁, (add_tsub_cancel_of_le h).symm⟩
    rw [nth_appendV_add]; exact h₂ j (lt_of_add_lt_add_left hi)

lemma noDrop_single {s : V} (h : sTag s = 0 ∨ sTag s = 1 ∨ sTag s = 2 ∨ sTag s = 3 ∨ sTag s = 4) :
    NoDrop (?[s] : V) := by
  intro i hi
  rw [len_adjoin, len_nil, zero_add] at hi
  rcases zero_or_succ i with rfl | ⟨i, rfl⟩
  · simpa using h
  · exact absurd hi (not_lt.mpr le_add_self)

/-- **A fact survives a well-tagged list, shifted once per eigenvariable step.** -/
lemma mem_ctxVec_of_mem {Γ₀ S x : V} (hS : NoDrop S) (hx : x ∈ Γ₀) :
    ∀ j ≤ len S, shiftIterV x (shiftsAux S j) ∈ (ctxVec Γ₀ S).[j] := by
  intro j
  induction j using ISigma1.pi1_succ_induction with
  | hP => definability
  | zero => intro _; simpa using hx
  | succ j ih =>
    intro hj
    have hj' : j < len S := lt_of_lt_of_le (lt_add_one j) hj
    have ih' := ih (le_of_lt hj')
    rw [nth_ctxVec_succ Γ₀ S hj']
    rcases hS j hj' with h | h | h | h | h
    · rw [shiftsAux_succ_of_noShift (by rw [h]; norm_num)]
      exact mem_ctxAfter_of_noShift (Or.inl h) ih'
    · rw [shiftsAux_succ_of_noShift (by rw [h]; norm_num)]
      exact mem_ctxAfter_of_noShift (Or.inr (Or.inl h)) ih'
    · rw [shiftsAux_succ_of_shift (Or.inl h), shiftIterV_succ]
      exact mem_ctxAfter_of_shift (Or.inl h) ih'
    · rw [shiftsAux_succ_of_shift (Or.inr h), shiftIterV_succ]
      exact mem_ctxAfter_of_shift (Or.inr h) ih'
    · rw [shiftsAux_succ_of_noShift (by rw [h]; norm_num)]
      exact mem_ctxAfter_of_noShift (Or.inr (Or.inr h)) ih'

lemma mem_finalCtx_of_mem {Γ₀ S x : V} (hS : NoDrop S) (hx : x ∈ Γ₀) :
    shiftIterV x (shiftsV S) ∈ finalCtx Γ₀ S :=
  mem_ctxVec_of_mem hS hx (len S) le_rfl


/-! ## Part 1 — the row table of the walk (D1)

The 40 rows the walk uses, in a FIXED order (`rIdx_<row>`: terms 0–14, vectors 15–18, formulas
19–39). Two tables: the PROOF table `tbl` (rows `⟪dΛ, m, B⟫`, existential per model —
`exists_walkTable`) and the PIECE table `walkPieces` (rows `⟪tag, as, c⟫`: the Horn
decomposition of the matrix, a closed V-generic term built from `RowInst`'s `row_<row>_as/_c/_R`),
from which a step is assembled by `mkStep W i ev = ⟪tag, i, ev, as, c⟫`. Every producer of the
walk takes `W := walkPieces` as a PARAMETER (a closed quote of a big sentence must never enter a
blueprint), and `StepOK`'s syntactic check `rowB tbl.[i] = impChainV as c` is discharged once
per row by `walkTable_<row>` (from `quote_row_<row>`). -/

section rowTable

/-- A library row as the walk sees it: an arity, a body, its library proof. -/
structure WRow where
  m : ℕ
  B : ArithmeticSemisentence m
  lib : Lib (∀¹* B)

/-- A sound table row of length `≤ N` (one conjunct of `TableOK`). -/
def RowOK (r N : V) : Prop :=
  IsSemiformula LAct (rowM r) (rowB r) ∧ Proof TAct (rowD r) (qqAlls (rowB r) (rowM r)) ∧ dlen TAct (rowD r) ≤ N

lemma RowOK.mono {r N N' : V} (h : RowOK r N) (hN : N ≤ N') : RowOK r N' :=
  ⟨h.1, h.2.1, le_trans h.2.2 hN⟩

lemma tableOK_vecOf {N : V} : ∀ (rows : List V), (∀ r ∈ rows, RowOK r N) → TableOK (vecOf rows) N
  | [], _ => fun i hi => by simp at hi
  | r :: rows, h => by
    intro i hi
    rw [vecOf_cons, len_adjoin] at hi
    rcases zero_or_succ i with rfl | ⟨i, rfl⟩
    · rw [vecOf_cons, nth_adjoin_zero]; exact h r (List.mem_cons_self ..)
    · rw [vecOf_cons, nth_adjoin_succ]
      exact tableOK_vecOf rows (fun r' hr' ↦ h r' (List.mem_cons_of_mem _ hr')) i (lt_of_add_lt_add_right hi)

/-- **A list of library rows has a proof table in every model**, with one standard bound. -/
theorem exists_rows : ∀ (rs : List WRow), ∃ N : ℕ, ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁],
    ∃ rows : List V, rows.length = rs.length ∧ (∀ r ∈ rows, RowOK r (N : V)) ∧
      ∀ (i : ℕ) (h : i < rs.length) (h' : i < rows.length),
        rowM rows[i] = ((rs[i]).m : V) ∧ rowB rows[i] = ⌜Semiformula.lMap emb (rs[i]).B⌝
  | [] => ⟨0, fun V _ _ ↦ ⟨[], rfl, fun _ h ↦ absurd h List.not_mem_nil, fun i h ↦ absurd h (Nat.not_lt_zero _)⟩⟩
  | r :: rs => by
    obtain ⟨N₁, h₁⟩ := r.lib.univ_code
    obtain ⟨N₂, h₂⟩ := exists_rows rs
    refine ⟨N₁ + N₂, fun V _ _ ↦ ?_⟩
    obtain ⟨d, hd, hdl⟩ := h₁ V
    obtain ⟨rows, hlen, hok, hidx⟩ := h₂ V
    refine ⟨mkRow d (r.m : V) ⌜Semiformula.lMap emb r.B⌝ :: rows, by simp [hlen], ?_, ?_⟩
    · intro r' hr'
      rcases List.mem_cons.mp hr' with rfl | hr'
      · refine ⟨?_, ?_, ?_⟩
        · rw [rowM_mkRow, rowB_mkRow]; exact Sentence.quote_isSemiformula _
        · rw [rowD_mkRow, rowM_mkRow, rowB_mkRow]; exact hd
        · rw [rowD_mkRow]
          exact le_trans hdl (by exact_mod_cast Nat.le_add_right N₁ N₂)
      · exact (hok r' hr').mono (by exact_mod_cast Nat.le_add_left N₂ N₁)
    · intro i h h'
      cases i with
      | zero => simp
      | succ i =>
        simp only [List.getElem_cons_succ]
        exact hidx i (Nat.lt_of_succ_lt_succ h) (Nat.lt_of_succ_lt_succ h')


def rIdx_zeroLtSucc : ℕ := 0
def rIdx_succLtSucc : ℕ := 1
def rIdx_qqBvarTotal : ℕ := 2
def rIdx_isSemitermBvar : ℕ := 3
def rIdx_isSemitermSigmaPiLAct : ℕ := 4
def rIdx_qqFvarTotal : ℕ := 5
def rIdx_isSemitermFvar : ℕ := 6
def rIdx_qqFuncTotal : ℕ := 7
def rIdx_isSemitermFunc : ℕ := 8
def rIdx_isFuncConst_zero : ℕ := 9
def rIdx_isFuncConst_one : ℕ := 10
def rIdx_isFuncConst_add : ℕ := 11
def rIdx_isFuncConst_mul : ℕ := 12
def rIdx_isFuncConst_cC : ℕ := 13
def rIdx_isFuncConst_cD : ℕ := 14
def rIdx_isSemitermVecNil : ℕ := 15
def rIdx_isSemitermVecSigmaPiLAct : ℕ := 16
def rIdx_adjoinTotal : ℕ := 17
def rIdx_isSemitermVecAdjoin : ℕ := 18
def rIdx_qqVerumTotal : ℕ := 19
def rIdx_isSemiformulaVerum : ℕ := 20
def rIdx_isSemiformulaSigmaPi : ℕ := 21
def rIdx_qqFalsumTotal : ℕ := 22
def rIdx_isSemiformulaFalsum : ℕ := 23
def rIdx_qqAndTotal : ℕ := 24
def rIdx_isSemiformulaAnd : ℕ := 25
def rIdx_qqOrTotal : ℕ := 26
def rIdx_isSemiformulaOr : ℕ := 27
def rIdx_qqAllTotal : ℕ := 28
def rIdx_isSemiformulaAll : ℕ := 29
def rIdx_qqExsTotal : ℕ := 30
def rIdx_isSemiformulaExs : ℕ := 31
def rIdx_qqRelTotal : ℕ := 32
def rIdx_isSemiformulaRel : ℕ := 33
def rIdx_qqNRelTotal : ℕ := 34
def rIdx_isSemiformulaNRel : ℕ := 35
def rIdx_isRelConst_eq : ℕ := 36
def rIdx_isRelConst_lt : ℕ := 37
def rIdx_isUTermVecOfSemitermVecLAct : ℕ := 38
def rIdx_isUTermVecSigmaPiLAct : ℕ := 39
def walkRowCount : ℕ := 40

/-- **The rows of the walk**, in index order. -/
noncomputable def walkRows : List WRow := [
  ⟨1, zeroLtSuccB, lib_zeroLtSucc⟩,
  ⟨2, succLtSuccB, lib_succLtSucc⟩,
  ⟨1, qqBvarTotalB, lib_qqBvarTotal⟩,
  ⟨3, isSemitermBvarB, lib_isSemitermBvar⟩,
  ⟨2, isSemitermSigmaPiLActB, lib_isSemitermSigmaPiLAct⟩,
  ⟨1, qqFvarTotalB, lib_qqFvarTotal⟩,
  ⟨3, isSemitermFvarB, lib_isSemitermFvar⟩,
  ⟨3, qqFuncTotalB, lib_qqFuncTotal⟩,
  ⟨5, isSemitermFuncB, lib_isSemitermFunc⟩,
  ⟨0, isFuncConst_zeroB, lib_isFuncConst_zero⟩,
  ⟨0, isFuncConst_oneB, lib_isFuncConst_one⟩,
  ⟨0, isFuncConst_addB, lib_isFuncConst_add⟩,
  ⟨0, isFuncConst_mulB, lib_isFuncConst_mul⟩,
  ⟨0, isFuncConst_cCB, lib_isFuncConst_cC⟩,
  ⟨0, isFuncConst_cDB, lib_isFuncConst_cD⟩,
  ⟨1, isSemitermVecNilB, lib_isSemitermVecNil⟩,
  ⟨3, isSemitermVecSigmaPiLActB, lib_isSemitermVecSigmaPiLAct⟩,
  ⟨2, adjoinTotalB, lib_adjoinTotal⟩,
  ⟨5, isSemitermVecAdjoinB, lib_isSemitermVecAdjoin⟩,
  ⟨0, qqVerumTotalB, lib_qqVerumTotal⟩,
  ⟨2, isSemiformulaVerumB, lib_isSemiformulaVerum⟩,
  ⟨2, isSemiformulaSigmaPiB, lib_isSemiformulaSigmaPi⟩,
  ⟨0, qqFalsumTotalB, lib_qqFalsumTotal⟩,
  ⟨2, isSemiformulaFalsumB, lib_isSemiformulaFalsum⟩,
  ⟨2, qqAndTotalB, lib_qqAndTotal⟩,
  ⟨4, isSemiformulaAndB, lib_isSemiformulaAnd⟩,
  ⟨2, qqOrTotalB, lib_qqOrTotal⟩,
  ⟨4, isSemiformulaOrB, lib_isSemiformulaOr⟩,
  ⟨1, qqAllTotalB, lib_qqAllTotal⟩,
  ⟨3, isSemiformulaAllB, lib_isSemiformulaAll⟩,
  ⟨1, qqExsTotalB, lib_qqExsTotal⟩,
  ⟨3, isSemiformulaExsB, lib_isSemiformulaExs⟩,
  ⟨3, qqRelTotalB, lib_qqRelTotal⟩,
  ⟨5, isSemiformulaRelB, lib_isSemiformulaRel⟩,
  ⟨3, qqNRelTotalB, lib_qqNRelTotal⟩,
  ⟨5, isSemiformulaNRelB, lib_isSemiformulaNRel⟩,
  ⟨0, isRelConst_eqB, lib_isRelConst_eq⟩,
  ⟨0, isRelConst_ltB, lib_isRelConst_lt⟩,
  ⟨3, isUTermVecOfSemitermVecLActB, lib_isUTermVecOfSemitermVecLAct⟩,
  ⟨2, isUTermVecSigmaPiLActB, lib_isUTermVecSigmaPiLAct⟩
]

lemma walkRows_length : walkRows.length = walkRowCount := rfl

/-- **The proof table of the walk**: `walkRowCount` rows at least, the `i`-th with the arity and the
matrix of `walkRows[i]`. -/
def WalkTable (tbl : V) : Prop :=
  (walkRowCount : V) ≤ len tbl ∧
  ∀ (i : ℕ) (h : i < walkRows.length),
    rowM tbl.[(i : V)] = ((walkRows[i]).m : V) ∧ rowB tbl.[(i : V)] = ⌜Semiformula.lMap emb (walkRows[i]).B⌝

/-- **D1. The walk's proof table exists in every model, with one standard length bound.** -/
theorem exists_walkTable : ∃ N : ℕ, ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁],
    ∃ tbl : V, TableOK tbl (N : V) ∧ WalkTable tbl := by
  obtain ⟨N, hN⟩ := exists_rows walkRows
  refine ⟨N, fun V _ _ ↦ ?_⟩
  obtain ⟨rows, hlen, hok, hidx⟩ := hN V
  refine ⟨vecOf rows, tableOK_vecOf rows hok, ?_, ?_⟩
  · rw [len_vecOf, hlen, walkRows_length]
  · intro i h
    have h' : i < rows.length := by rw [hlen]; exact h
    rw [nth_vecOf rows i h']
    exact hidx i h h'

/-! ### The per-row readings of `WalkTable` -/

lemma walkTable_zeroLtSucc {tbl : V} (h : WalkTable tbl) :
    rowM tbl.[((rIdx_zeroLtSucc : ℕ) : V)] = ((1 : ℕ) : V) ∧
    rowB tbl.[((rIdx_zeroLtSucc : ℕ) : V)] = impChainV LAct (vecOf row_zeroLtSucc_as) row_zeroLtSucc_c := by
  have this : rowM tbl.[((rIdx_zeroLtSucc : ℕ) : V)] = ((1 : ℕ) : V) ∧
      rowB tbl.[((rIdx_zeroLtSucc : ℕ) : V)] = ⌜Semiformula.lMap emb zeroLtSuccB⌝ :=
    h.2 rIdx_zeroLtSucc (Nat.lt_of_sub_eq_succ rfl)
  refine ⟨this.1, ?_⟩
  rw [impChainV_vecOf, this.2, quote_row_zeroLtSucc]

lemma walkTable_succLtSucc {tbl : V} (h : WalkTable tbl) :
    rowM tbl.[((rIdx_succLtSucc : ℕ) : V)] = ((2 : ℕ) : V) ∧
    rowB tbl.[((rIdx_succLtSucc : ℕ) : V)] = impChainV LAct (vecOf row_succLtSucc_as) row_succLtSucc_c := by
  have this : rowM tbl.[((rIdx_succLtSucc : ℕ) : V)] = ((2 : ℕ) : V) ∧
      rowB tbl.[((rIdx_succLtSucc : ℕ) : V)] = ⌜Semiformula.lMap emb succLtSuccB⌝ :=
    h.2 rIdx_succLtSucc (Nat.lt_of_sub_eq_succ rfl)
  refine ⟨this.1, ?_⟩
  rw [impChainV_vecOf, this.2, quote_row_succLtSucc]

lemma walkTable_qqBvarTotal {tbl : V} (h : WalkTable tbl) :
    rowM tbl.[((rIdx_qqBvarTotal : ℕ) : V)] = ((1 : ℕ) : V) ∧
    rowB tbl.[((rIdx_qqBvarTotal : ℕ) : V)] = impChainV LAct (vecOf row_qqBvarTotal_as) (^∃ row_qqBvarTotal_R) := by
  have this : rowM tbl.[((rIdx_qqBvarTotal : ℕ) : V)] = ((1 : ℕ) : V) ∧
      rowB tbl.[((rIdx_qqBvarTotal : ℕ) : V)] = ⌜Semiformula.lMap emb qqBvarTotalB⌝ :=
    h.2 rIdx_qqBvarTotal (Nat.lt_of_sub_eq_succ rfl)
  refine ⟨this.1, ?_⟩
  rw [impChainV_vecOf, this.2, quote_row_qqBvarTotal]
  rfl

lemma walkTable_isSemitermBvar {tbl : V} (h : WalkTable tbl) :
    rowM tbl.[((rIdx_isSemitermBvar : ℕ) : V)] = ((3 : ℕ) : V) ∧
    rowB tbl.[((rIdx_isSemitermBvar : ℕ) : V)] = impChainV LAct (vecOf row_isSemitermBvar_as) row_isSemitermBvar_c := by
  have this : rowM tbl.[((rIdx_isSemitermBvar : ℕ) : V)] = ((3 : ℕ) : V) ∧
      rowB tbl.[((rIdx_isSemitermBvar : ℕ) : V)] = ⌜Semiformula.lMap emb isSemitermBvarB⌝ :=
    h.2 rIdx_isSemitermBvar (Nat.lt_of_sub_eq_succ rfl)
  refine ⟨this.1, ?_⟩
  rw [impChainV_vecOf, this.2, quote_row_isSemitermBvar]

lemma walkTable_isSemitermSigmaPiLAct {tbl : V} (h : WalkTable tbl) :
    rowM tbl.[((rIdx_isSemitermSigmaPiLAct : ℕ) : V)] = ((2 : ℕ) : V) ∧
    rowB tbl.[((rIdx_isSemitermSigmaPiLAct : ℕ) : V)] = impChainV LAct (vecOf row_isSemitermSigmaPiLAct_as) row_isSemitermSigmaPiLAct_c := by
  have this : rowM tbl.[((rIdx_isSemitermSigmaPiLAct : ℕ) : V)] = ((2 : ℕ) : V) ∧
      rowB tbl.[((rIdx_isSemitermSigmaPiLAct : ℕ) : V)] = ⌜Semiformula.lMap emb isSemitermSigmaPiLActB⌝ :=
    h.2 rIdx_isSemitermSigmaPiLAct (Nat.lt_of_sub_eq_succ rfl)
  refine ⟨this.1, ?_⟩
  rw [impChainV_vecOf, this.2, quote_row_isSemitermSigmaPiLAct]

lemma walkTable_qqFvarTotal {tbl : V} (h : WalkTable tbl) :
    rowM tbl.[((rIdx_qqFvarTotal : ℕ) : V)] = ((1 : ℕ) : V) ∧
    rowB tbl.[((rIdx_qqFvarTotal : ℕ) : V)] = impChainV LAct (vecOf row_qqFvarTotal_as) (^∃ row_qqFvarTotal_R) := by
  have this : rowM tbl.[((rIdx_qqFvarTotal : ℕ) : V)] = ((1 : ℕ) : V) ∧
      rowB tbl.[((rIdx_qqFvarTotal : ℕ) : V)] = ⌜Semiformula.lMap emb qqFvarTotalB⌝ :=
    h.2 rIdx_qqFvarTotal (Nat.lt_of_sub_eq_succ rfl)
  refine ⟨this.1, ?_⟩
  rw [impChainV_vecOf, this.2, quote_row_qqFvarTotal]
  rfl

lemma walkTable_isSemitermFvar {tbl : V} (h : WalkTable tbl) :
    rowM tbl.[((rIdx_isSemitermFvar : ℕ) : V)] = ((3 : ℕ) : V) ∧
    rowB tbl.[((rIdx_isSemitermFvar : ℕ) : V)] = impChainV LAct (vecOf row_isSemitermFvar_as) row_isSemitermFvar_c := by
  have this : rowM tbl.[((rIdx_isSemitermFvar : ℕ) : V)] = ((3 : ℕ) : V) ∧
      rowB tbl.[((rIdx_isSemitermFvar : ℕ) : V)] = ⌜Semiformula.lMap emb isSemitermFvarB⌝ :=
    h.2 rIdx_isSemitermFvar (Nat.lt_of_sub_eq_succ rfl)
  refine ⟨this.1, ?_⟩
  rw [impChainV_vecOf, this.2, quote_row_isSemitermFvar]

lemma walkTable_qqFuncTotal {tbl : V} (h : WalkTable tbl) :
    rowM tbl.[((rIdx_qqFuncTotal : ℕ) : V)] = ((3 : ℕ) : V) ∧
    rowB tbl.[((rIdx_qqFuncTotal : ℕ) : V)] = impChainV LAct (vecOf row_qqFuncTotal_as) (^∃ row_qqFuncTotal_R) := by
  have this : rowM tbl.[((rIdx_qqFuncTotal : ℕ) : V)] = ((3 : ℕ) : V) ∧
      rowB tbl.[((rIdx_qqFuncTotal : ℕ) : V)] = ⌜Semiformula.lMap emb qqFuncTotalB⌝ :=
    h.2 rIdx_qqFuncTotal (Nat.lt_of_sub_eq_succ rfl)
  refine ⟨this.1, ?_⟩
  rw [impChainV_vecOf, this.2, quote_row_qqFuncTotal]
  rfl

lemma walkTable_isSemitermFunc {tbl : V} (h : WalkTable tbl) :
    rowM tbl.[((rIdx_isSemitermFunc : ℕ) : V)] = ((5 : ℕ) : V) ∧
    rowB tbl.[((rIdx_isSemitermFunc : ℕ) : V)] = impChainV LAct (vecOf row_isSemitermFunc_as) row_isSemitermFunc_c := by
  have this : rowM tbl.[((rIdx_isSemitermFunc : ℕ) : V)] = ((5 : ℕ) : V) ∧
      rowB tbl.[((rIdx_isSemitermFunc : ℕ) : V)] = ⌜Semiformula.lMap emb isSemitermFuncB⌝ :=
    h.2 rIdx_isSemitermFunc (Nat.lt_of_sub_eq_succ rfl)
  refine ⟨this.1, ?_⟩
  rw [impChainV_vecOf, this.2, quote_row_isSemitermFunc]

lemma walkTable_isFuncConst_zero {tbl : V} (h : WalkTable tbl) :
    rowM tbl.[((rIdx_isFuncConst_zero : ℕ) : V)] = ((0 : ℕ) : V) ∧
    rowB tbl.[((rIdx_isFuncConst_zero : ℕ) : V)] = impChainV LAct (vecOf row_isFuncConst_zero_as) row_isFuncConst_zero_c := by
  have this : rowM tbl.[((rIdx_isFuncConst_zero : ℕ) : V)] = ((0 : ℕ) : V) ∧
      rowB tbl.[((rIdx_isFuncConst_zero : ℕ) : V)] = ⌜Semiformula.lMap emb isFuncConst_zeroB⌝ :=
    h.2 rIdx_isFuncConst_zero (Nat.lt_of_sub_eq_succ rfl)
  refine ⟨this.1, ?_⟩
  rw [impChainV_vecOf, this.2, quote_row_isFuncConst_zero]

lemma walkTable_isFuncConst_one {tbl : V} (h : WalkTable tbl) :
    rowM tbl.[((rIdx_isFuncConst_one : ℕ) : V)] = ((0 : ℕ) : V) ∧
    rowB tbl.[((rIdx_isFuncConst_one : ℕ) : V)] = impChainV LAct (vecOf row_isFuncConst_one_as) row_isFuncConst_one_c := by
  have this : rowM tbl.[((rIdx_isFuncConst_one : ℕ) : V)] = ((0 : ℕ) : V) ∧
      rowB tbl.[((rIdx_isFuncConst_one : ℕ) : V)] = ⌜Semiformula.lMap emb isFuncConst_oneB⌝ :=
    h.2 rIdx_isFuncConst_one (Nat.lt_of_sub_eq_succ rfl)
  refine ⟨this.1, ?_⟩
  rw [impChainV_vecOf, this.2, quote_row_isFuncConst_one]

lemma walkTable_isFuncConst_add {tbl : V} (h : WalkTable tbl) :
    rowM tbl.[((rIdx_isFuncConst_add : ℕ) : V)] = ((0 : ℕ) : V) ∧
    rowB tbl.[((rIdx_isFuncConst_add : ℕ) : V)] = impChainV LAct (vecOf row_isFuncConst_add_as) row_isFuncConst_add_c := by
  have this : rowM tbl.[((rIdx_isFuncConst_add : ℕ) : V)] = ((0 : ℕ) : V) ∧
      rowB tbl.[((rIdx_isFuncConst_add : ℕ) : V)] = ⌜Semiformula.lMap emb isFuncConst_addB⌝ :=
    h.2 rIdx_isFuncConst_add (Nat.lt_of_sub_eq_succ rfl)
  refine ⟨this.1, ?_⟩
  rw [impChainV_vecOf, this.2, quote_row_isFuncConst_add]

lemma walkTable_isFuncConst_mul {tbl : V} (h : WalkTable tbl) :
    rowM tbl.[((rIdx_isFuncConst_mul : ℕ) : V)] = ((0 : ℕ) : V) ∧
    rowB tbl.[((rIdx_isFuncConst_mul : ℕ) : V)] = impChainV LAct (vecOf row_isFuncConst_mul_as) row_isFuncConst_mul_c := by
  have this : rowM tbl.[((rIdx_isFuncConst_mul : ℕ) : V)] = ((0 : ℕ) : V) ∧
      rowB tbl.[((rIdx_isFuncConst_mul : ℕ) : V)] = ⌜Semiformula.lMap emb isFuncConst_mulB⌝ :=
    h.2 rIdx_isFuncConst_mul (Nat.lt_of_sub_eq_succ rfl)
  refine ⟨this.1, ?_⟩
  rw [impChainV_vecOf, this.2, quote_row_isFuncConst_mul]

lemma walkTable_isFuncConst_cC {tbl : V} (h : WalkTable tbl) :
    rowM tbl.[((rIdx_isFuncConst_cC : ℕ) : V)] = ((0 : ℕ) : V) ∧
    rowB tbl.[((rIdx_isFuncConst_cC : ℕ) : V)] = impChainV LAct (vecOf row_isFuncConst_cC_as) row_isFuncConst_cC_c := by
  have this : rowM tbl.[((rIdx_isFuncConst_cC : ℕ) : V)] = ((0 : ℕ) : V) ∧
      rowB tbl.[((rIdx_isFuncConst_cC : ℕ) : V)] = ⌜Semiformula.lMap emb isFuncConst_cCB⌝ :=
    h.2 rIdx_isFuncConst_cC (Nat.lt_of_sub_eq_succ rfl)
  refine ⟨this.1, ?_⟩
  rw [impChainV_vecOf, this.2, quote_row_isFuncConst_cC]

lemma walkTable_isFuncConst_cD {tbl : V} (h : WalkTable tbl) :
    rowM tbl.[((rIdx_isFuncConst_cD : ℕ) : V)] = ((0 : ℕ) : V) ∧
    rowB tbl.[((rIdx_isFuncConst_cD : ℕ) : V)] = impChainV LAct (vecOf row_isFuncConst_cD_as) row_isFuncConst_cD_c := by
  have this : rowM tbl.[((rIdx_isFuncConst_cD : ℕ) : V)] = ((0 : ℕ) : V) ∧
      rowB tbl.[((rIdx_isFuncConst_cD : ℕ) : V)] = ⌜Semiformula.lMap emb isFuncConst_cDB⌝ :=
    h.2 rIdx_isFuncConst_cD (Nat.lt_of_sub_eq_succ rfl)
  refine ⟨this.1, ?_⟩
  rw [impChainV_vecOf, this.2, quote_row_isFuncConst_cD]

lemma walkTable_isSemitermVecNil {tbl : V} (h : WalkTable tbl) :
    rowM tbl.[((rIdx_isSemitermVecNil : ℕ) : V)] = ((1 : ℕ) : V) ∧
    rowB tbl.[((rIdx_isSemitermVecNil : ℕ) : V)] = impChainV LAct (vecOf row_isSemitermVecNil_as) row_isSemitermVecNil_c := by
  have this : rowM tbl.[((rIdx_isSemitermVecNil : ℕ) : V)] = ((1 : ℕ) : V) ∧
      rowB tbl.[((rIdx_isSemitermVecNil : ℕ) : V)] = ⌜Semiformula.lMap emb isSemitermVecNilB⌝ :=
    h.2 rIdx_isSemitermVecNil (Nat.lt_of_sub_eq_succ rfl)
  refine ⟨this.1, ?_⟩
  rw [impChainV_vecOf, this.2, quote_row_isSemitermVecNil]

lemma walkTable_isSemitermVecSigmaPiLAct {tbl : V} (h : WalkTable tbl) :
    rowM tbl.[((rIdx_isSemitermVecSigmaPiLAct : ℕ) : V)] = ((3 : ℕ) : V) ∧
    rowB tbl.[((rIdx_isSemitermVecSigmaPiLAct : ℕ) : V)] = impChainV LAct (vecOf row_isSemitermVecSigmaPiLAct_as) row_isSemitermVecSigmaPiLAct_c := by
  have this : rowM tbl.[((rIdx_isSemitermVecSigmaPiLAct : ℕ) : V)] = ((3 : ℕ) : V) ∧
      rowB tbl.[((rIdx_isSemitermVecSigmaPiLAct : ℕ) : V)] = ⌜Semiformula.lMap emb isSemitermVecSigmaPiLActB⌝ :=
    h.2 rIdx_isSemitermVecSigmaPiLAct (Nat.lt_of_sub_eq_succ rfl)
  refine ⟨this.1, ?_⟩
  rw [impChainV_vecOf, this.2, quote_row_isSemitermVecSigmaPiLAct]

lemma walkTable_adjoinTotal {tbl : V} (h : WalkTable tbl) :
    rowM tbl.[((rIdx_adjoinTotal : ℕ) : V)] = ((2 : ℕ) : V) ∧
    rowB tbl.[((rIdx_adjoinTotal : ℕ) : V)] = impChainV LAct (vecOf row_adjoinTotal_as) (^∃ row_adjoinTotal_R) := by
  have this : rowM tbl.[((rIdx_adjoinTotal : ℕ) : V)] = ((2 : ℕ) : V) ∧
      rowB tbl.[((rIdx_adjoinTotal : ℕ) : V)] = ⌜Semiformula.lMap emb adjoinTotalB⌝ :=
    h.2 rIdx_adjoinTotal (Nat.lt_of_sub_eq_succ rfl)
  refine ⟨this.1, ?_⟩
  rw [impChainV_vecOf, this.2, quote_row_adjoinTotal]
  rfl

lemma walkTable_isSemitermVecAdjoin {tbl : V} (h : WalkTable tbl) :
    rowM tbl.[((rIdx_isSemitermVecAdjoin : ℕ) : V)] = ((5 : ℕ) : V) ∧
    rowB tbl.[((rIdx_isSemitermVecAdjoin : ℕ) : V)] = impChainV LAct (vecOf row_isSemitermVecAdjoin_as) row_isSemitermVecAdjoin_c := by
  have this : rowM tbl.[((rIdx_isSemitermVecAdjoin : ℕ) : V)] = ((5 : ℕ) : V) ∧
      rowB tbl.[((rIdx_isSemitermVecAdjoin : ℕ) : V)] = ⌜Semiformula.lMap emb isSemitermVecAdjoinB⌝ :=
    h.2 rIdx_isSemitermVecAdjoin (Nat.lt_of_sub_eq_succ rfl)
  refine ⟨this.1, ?_⟩
  rw [impChainV_vecOf, this.2, quote_row_isSemitermVecAdjoin]

lemma walkTable_qqVerumTotal {tbl : V} (h : WalkTable tbl) :
    rowM tbl.[((rIdx_qqVerumTotal : ℕ) : V)] = ((0 : ℕ) : V) ∧
    rowB tbl.[((rIdx_qqVerumTotal : ℕ) : V)] = impChainV LAct (vecOf row_qqVerumTotal_as) (^∃ row_qqVerumTotal_R) := by
  have this : rowM tbl.[((rIdx_qqVerumTotal : ℕ) : V)] = ((0 : ℕ) : V) ∧
      rowB tbl.[((rIdx_qqVerumTotal : ℕ) : V)] = ⌜Semiformula.lMap emb qqVerumTotalB⌝ :=
    h.2 rIdx_qqVerumTotal (Nat.lt_of_sub_eq_succ rfl)
  refine ⟨this.1, ?_⟩
  rw [impChainV_vecOf, this.2, quote_row_qqVerumTotal]
  rfl

lemma walkTable_isSemiformulaVerum {tbl : V} (h : WalkTable tbl) :
    rowM tbl.[((rIdx_isSemiformulaVerum : ℕ) : V)] = ((2 : ℕ) : V) ∧
    rowB tbl.[((rIdx_isSemiformulaVerum : ℕ) : V)] = impChainV LAct (vecOf row_isSemiformulaVerum_as) row_isSemiformulaVerum_c := by
  have this : rowM tbl.[((rIdx_isSemiformulaVerum : ℕ) : V)] = ((2 : ℕ) : V) ∧
      rowB tbl.[((rIdx_isSemiformulaVerum : ℕ) : V)] = ⌜Semiformula.lMap emb isSemiformulaVerumB⌝ :=
    h.2 rIdx_isSemiformulaVerum (Nat.lt_of_sub_eq_succ rfl)
  refine ⟨this.1, ?_⟩
  rw [impChainV_vecOf, this.2, quote_row_isSemiformulaVerum]

lemma walkTable_isSemiformulaSigmaPi {tbl : V} (h : WalkTable tbl) :
    rowM tbl.[((rIdx_isSemiformulaSigmaPi : ℕ) : V)] = ((2 : ℕ) : V) ∧
    rowB tbl.[((rIdx_isSemiformulaSigmaPi : ℕ) : V)] = impChainV LAct (vecOf row_isSemiformulaSigmaPi_as) row_isSemiformulaSigmaPi_c := by
  have this : rowM tbl.[((rIdx_isSemiformulaSigmaPi : ℕ) : V)] = ((2 : ℕ) : V) ∧
      rowB tbl.[((rIdx_isSemiformulaSigmaPi : ℕ) : V)] = ⌜Semiformula.lMap emb isSemiformulaSigmaPiB⌝ :=
    h.2 rIdx_isSemiformulaSigmaPi (Nat.lt_of_sub_eq_succ rfl)
  refine ⟨this.1, ?_⟩
  rw [impChainV_vecOf, this.2, quote_row_isSemiformulaSigmaPi]

lemma walkTable_qqFalsumTotal {tbl : V} (h : WalkTable tbl) :
    rowM tbl.[((rIdx_qqFalsumTotal : ℕ) : V)] = ((0 : ℕ) : V) ∧
    rowB tbl.[((rIdx_qqFalsumTotal : ℕ) : V)] = impChainV LAct (vecOf row_qqFalsumTotal_as) (^∃ row_qqFalsumTotal_R) := by
  have this : rowM tbl.[((rIdx_qqFalsumTotal : ℕ) : V)] = ((0 : ℕ) : V) ∧
      rowB tbl.[((rIdx_qqFalsumTotal : ℕ) : V)] = ⌜Semiformula.lMap emb qqFalsumTotalB⌝ :=
    h.2 rIdx_qqFalsumTotal (Nat.lt_of_sub_eq_succ rfl)
  refine ⟨this.1, ?_⟩
  rw [impChainV_vecOf, this.2, quote_row_qqFalsumTotal]
  rfl

lemma walkTable_isSemiformulaFalsum {tbl : V} (h : WalkTable tbl) :
    rowM tbl.[((rIdx_isSemiformulaFalsum : ℕ) : V)] = ((2 : ℕ) : V) ∧
    rowB tbl.[((rIdx_isSemiformulaFalsum : ℕ) : V)] = impChainV LAct (vecOf row_isSemiformulaFalsum_as) row_isSemiformulaFalsum_c := by
  have this : rowM tbl.[((rIdx_isSemiformulaFalsum : ℕ) : V)] = ((2 : ℕ) : V) ∧
      rowB tbl.[((rIdx_isSemiformulaFalsum : ℕ) : V)] = ⌜Semiformula.lMap emb isSemiformulaFalsumB⌝ :=
    h.2 rIdx_isSemiformulaFalsum (Nat.lt_of_sub_eq_succ rfl)
  refine ⟨this.1, ?_⟩
  rw [impChainV_vecOf, this.2, quote_row_isSemiformulaFalsum]

lemma walkTable_qqAndTotal {tbl : V} (h : WalkTable tbl) :
    rowM tbl.[((rIdx_qqAndTotal : ℕ) : V)] = ((2 : ℕ) : V) ∧
    rowB tbl.[((rIdx_qqAndTotal : ℕ) : V)] = impChainV LAct (vecOf row_qqAndTotal_as) (^∃ row_qqAndTotal_R) := by
  have this : rowM tbl.[((rIdx_qqAndTotal : ℕ) : V)] = ((2 : ℕ) : V) ∧
      rowB tbl.[((rIdx_qqAndTotal : ℕ) : V)] = ⌜Semiformula.lMap emb qqAndTotalB⌝ :=
    h.2 rIdx_qqAndTotal (Nat.lt_of_sub_eq_succ rfl)
  refine ⟨this.1, ?_⟩
  rw [impChainV_vecOf, this.2, quote_row_qqAndTotal]
  rfl

lemma walkTable_isSemiformulaAnd {tbl : V} (h : WalkTable tbl) :
    rowM tbl.[((rIdx_isSemiformulaAnd : ℕ) : V)] = ((4 : ℕ) : V) ∧
    rowB tbl.[((rIdx_isSemiformulaAnd : ℕ) : V)] = impChainV LAct (vecOf row_isSemiformulaAnd_as) row_isSemiformulaAnd_c := by
  have this : rowM tbl.[((rIdx_isSemiformulaAnd : ℕ) : V)] = ((4 : ℕ) : V) ∧
      rowB tbl.[((rIdx_isSemiformulaAnd : ℕ) : V)] = ⌜Semiformula.lMap emb isSemiformulaAndB⌝ :=
    h.2 rIdx_isSemiformulaAnd (Nat.lt_of_sub_eq_succ rfl)
  refine ⟨this.1, ?_⟩
  rw [impChainV_vecOf, this.2, quote_row_isSemiformulaAnd]

lemma walkTable_qqOrTotal {tbl : V} (h : WalkTable tbl) :
    rowM tbl.[((rIdx_qqOrTotal : ℕ) : V)] = ((2 : ℕ) : V) ∧
    rowB tbl.[((rIdx_qqOrTotal : ℕ) : V)] = impChainV LAct (vecOf row_qqOrTotal_as) (^∃ row_qqOrTotal_R) := by
  have this : rowM tbl.[((rIdx_qqOrTotal : ℕ) : V)] = ((2 : ℕ) : V) ∧
      rowB tbl.[((rIdx_qqOrTotal : ℕ) : V)] = ⌜Semiformula.lMap emb qqOrTotalB⌝ :=
    h.2 rIdx_qqOrTotal (Nat.lt_of_sub_eq_succ rfl)
  refine ⟨this.1, ?_⟩
  rw [impChainV_vecOf, this.2, quote_row_qqOrTotal]
  rfl

lemma walkTable_isSemiformulaOr {tbl : V} (h : WalkTable tbl) :
    rowM tbl.[((rIdx_isSemiformulaOr : ℕ) : V)] = ((4 : ℕ) : V) ∧
    rowB tbl.[((rIdx_isSemiformulaOr : ℕ) : V)] = impChainV LAct (vecOf row_isSemiformulaOr_as) row_isSemiformulaOr_c := by
  have this : rowM tbl.[((rIdx_isSemiformulaOr : ℕ) : V)] = ((4 : ℕ) : V) ∧
      rowB tbl.[((rIdx_isSemiformulaOr : ℕ) : V)] = ⌜Semiformula.lMap emb isSemiformulaOrB⌝ :=
    h.2 rIdx_isSemiformulaOr (Nat.lt_of_sub_eq_succ rfl)
  refine ⟨this.1, ?_⟩
  rw [impChainV_vecOf, this.2, quote_row_isSemiformulaOr]

lemma walkTable_qqAllTotal {tbl : V} (h : WalkTable tbl) :
    rowM tbl.[((rIdx_qqAllTotal : ℕ) : V)] = ((1 : ℕ) : V) ∧
    rowB tbl.[((rIdx_qqAllTotal : ℕ) : V)] = impChainV LAct (vecOf row_qqAllTotal_as) (^∃ row_qqAllTotal_R) := by
  have this : rowM tbl.[((rIdx_qqAllTotal : ℕ) : V)] = ((1 : ℕ) : V) ∧
      rowB tbl.[((rIdx_qqAllTotal : ℕ) : V)] = ⌜Semiformula.lMap emb qqAllTotalB⌝ :=
    h.2 rIdx_qqAllTotal (Nat.lt_of_sub_eq_succ rfl)
  refine ⟨this.1, ?_⟩
  rw [impChainV_vecOf, this.2, quote_row_qqAllTotal]
  rfl

lemma walkTable_isSemiformulaAll {tbl : V} (h : WalkTable tbl) :
    rowM tbl.[((rIdx_isSemiformulaAll : ℕ) : V)] = ((3 : ℕ) : V) ∧
    rowB tbl.[((rIdx_isSemiformulaAll : ℕ) : V)] = impChainV LAct (vecOf row_isSemiformulaAll_as) row_isSemiformulaAll_c := by
  have this : rowM tbl.[((rIdx_isSemiformulaAll : ℕ) : V)] = ((3 : ℕ) : V) ∧
      rowB tbl.[((rIdx_isSemiformulaAll : ℕ) : V)] = ⌜Semiformula.lMap emb isSemiformulaAllB⌝ :=
    h.2 rIdx_isSemiformulaAll (Nat.lt_of_sub_eq_succ rfl)
  refine ⟨this.1, ?_⟩
  rw [impChainV_vecOf, this.2, quote_row_isSemiformulaAll]

lemma walkTable_qqExsTotal {tbl : V} (h : WalkTable tbl) :
    rowM tbl.[((rIdx_qqExsTotal : ℕ) : V)] = ((1 : ℕ) : V) ∧
    rowB tbl.[((rIdx_qqExsTotal : ℕ) : V)] = impChainV LAct (vecOf row_qqExsTotal_as) (^∃ row_qqExsTotal_R) := by
  have this : rowM tbl.[((rIdx_qqExsTotal : ℕ) : V)] = ((1 : ℕ) : V) ∧
      rowB tbl.[((rIdx_qqExsTotal : ℕ) : V)] = ⌜Semiformula.lMap emb qqExsTotalB⌝ :=
    h.2 rIdx_qqExsTotal (Nat.lt_of_sub_eq_succ rfl)
  refine ⟨this.1, ?_⟩
  rw [impChainV_vecOf, this.2, quote_row_qqExsTotal]
  rfl

lemma walkTable_isSemiformulaExs {tbl : V} (h : WalkTable tbl) :
    rowM tbl.[((rIdx_isSemiformulaExs : ℕ) : V)] = ((3 : ℕ) : V) ∧
    rowB tbl.[((rIdx_isSemiformulaExs : ℕ) : V)] = impChainV LAct (vecOf row_isSemiformulaExs_as) row_isSemiformulaExs_c := by
  have this : rowM tbl.[((rIdx_isSemiformulaExs : ℕ) : V)] = ((3 : ℕ) : V) ∧
      rowB tbl.[((rIdx_isSemiformulaExs : ℕ) : V)] = ⌜Semiformula.lMap emb isSemiformulaExsB⌝ :=
    h.2 rIdx_isSemiformulaExs (Nat.lt_of_sub_eq_succ rfl)
  refine ⟨this.1, ?_⟩
  rw [impChainV_vecOf, this.2, quote_row_isSemiformulaExs]

lemma walkTable_qqRelTotal {tbl : V} (h : WalkTable tbl) :
    rowM tbl.[((rIdx_qqRelTotal : ℕ) : V)] = ((3 : ℕ) : V) ∧
    rowB tbl.[((rIdx_qqRelTotal : ℕ) : V)] = impChainV LAct (vecOf row_qqRelTotal_as) (^∃ row_qqRelTotal_R) := by
  have this : rowM tbl.[((rIdx_qqRelTotal : ℕ) : V)] = ((3 : ℕ) : V) ∧
      rowB tbl.[((rIdx_qqRelTotal : ℕ) : V)] = ⌜Semiformula.lMap emb qqRelTotalB⌝ :=
    h.2 rIdx_qqRelTotal (Nat.lt_of_sub_eq_succ rfl)
  refine ⟨this.1, ?_⟩
  rw [impChainV_vecOf, this.2, quote_row_qqRelTotal]
  rfl

lemma walkTable_isSemiformulaRel {tbl : V} (h : WalkTable tbl) :
    rowM tbl.[((rIdx_isSemiformulaRel : ℕ) : V)] = ((5 : ℕ) : V) ∧
    rowB tbl.[((rIdx_isSemiformulaRel : ℕ) : V)] = impChainV LAct (vecOf row_isSemiformulaRel_as) row_isSemiformulaRel_c := by
  have this : rowM tbl.[((rIdx_isSemiformulaRel : ℕ) : V)] = ((5 : ℕ) : V) ∧
      rowB tbl.[((rIdx_isSemiformulaRel : ℕ) : V)] = ⌜Semiformula.lMap emb isSemiformulaRelB⌝ :=
    h.2 rIdx_isSemiformulaRel (Nat.lt_of_sub_eq_succ rfl)
  refine ⟨this.1, ?_⟩
  rw [impChainV_vecOf, this.2, quote_row_isSemiformulaRel]

lemma walkTable_qqNRelTotal {tbl : V} (h : WalkTable tbl) :
    rowM tbl.[((rIdx_qqNRelTotal : ℕ) : V)] = ((3 : ℕ) : V) ∧
    rowB tbl.[((rIdx_qqNRelTotal : ℕ) : V)] = impChainV LAct (vecOf row_qqNRelTotal_as) (^∃ row_qqNRelTotal_R) := by
  have this : rowM tbl.[((rIdx_qqNRelTotal : ℕ) : V)] = ((3 : ℕ) : V) ∧
      rowB tbl.[((rIdx_qqNRelTotal : ℕ) : V)] = ⌜Semiformula.lMap emb qqNRelTotalB⌝ :=
    h.2 rIdx_qqNRelTotal (Nat.lt_of_sub_eq_succ rfl)
  refine ⟨this.1, ?_⟩
  rw [impChainV_vecOf, this.2, quote_row_qqNRelTotal]
  rfl

lemma walkTable_isSemiformulaNRel {tbl : V} (h : WalkTable tbl) :
    rowM tbl.[((rIdx_isSemiformulaNRel : ℕ) : V)] = ((5 : ℕ) : V) ∧
    rowB tbl.[((rIdx_isSemiformulaNRel : ℕ) : V)] = impChainV LAct (vecOf row_isSemiformulaNRel_as) row_isSemiformulaNRel_c := by
  have this : rowM tbl.[((rIdx_isSemiformulaNRel : ℕ) : V)] = ((5 : ℕ) : V) ∧
      rowB tbl.[((rIdx_isSemiformulaNRel : ℕ) : V)] = ⌜Semiformula.lMap emb isSemiformulaNRelB⌝ :=
    h.2 rIdx_isSemiformulaNRel (Nat.lt_of_sub_eq_succ rfl)
  refine ⟨this.1, ?_⟩
  rw [impChainV_vecOf, this.2, quote_row_isSemiformulaNRel]

lemma walkTable_isRelConst_eq {tbl : V} (h : WalkTable tbl) :
    rowM tbl.[((rIdx_isRelConst_eq : ℕ) : V)] = ((0 : ℕ) : V) ∧
    rowB tbl.[((rIdx_isRelConst_eq : ℕ) : V)] = impChainV LAct (vecOf row_isRelConst_eq_as) row_isRelConst_eq_c := by
  have this : rowM tbl.[((rIdx_isRelConst_eq : ℕ) : V)] = ((0 : ℕ) : V) ∧
      rowB tbl.[((rIdx_isRelConst_eq : ℕ) : V)] = ⌜Semiformula.lMap emb isRelConst_eqB⌝ :=
    h.2 rIdx_isRelConst_eq (Nat.lt_of_sub_eq_succ rfl)
  refine ⟨this.1, ?_⟩
  rw [impChainV_vecOf, this.2, quote_row_isRelConst_eq]

lemma walkTable_isRelConst_lt {tbl : V} (h : WalkTable tbl) :
    rowM tbl.[((rIdx_isRelConst_lt : ℕ) : V)] = ((0 : ℕ) : V) ∧
    rowB tbl.[((rIdx_isRelConst_lt : ℕ) : V)] = impChainV LAct (vecOf row_isRelConst_lt_as) row_isRelConst_lt_c := by
  have this : rowM tbl.[((rIdx_isRelConst_lt : ℕ) : V)] = ((0 : ℕ) : V) ∧
      rowB tbl.[((rIdx_isRelConst_lt : ℕ) : V)] = ⌜Semiformula.lMap emb isRelConst_ltB⌝ :=
    h.2 rIdx_isRelConst_lt (Nat.lt_of_sub_eq_succ rfl)
  refine ⟨this.1, ?_⟩
  rw [impChainV_vecOf, this.2, quote_row_isRelConst_lt]

lemma walkTable_isUTermVecOfSemitermVecLAct {tbl : V} (h : WalkTable tbl) :
    rowM tbl.[((rIdx_isUTermVecOfSemitermVecLAct : ℕ) : V)] = ((3 : ℕ) : V) ∧
    rowB tbl.[((rIdx_isUTermVecOfSemitermVecLAct : ℕ) : V)] = impChainV LAct (vecOf row_isUTermVecOfSemitermVecLAct_as) row_isUTermVecOfSemitermVecLAct_c := by
  have this : rowM tbl.[((rIdx_isUTermVecOfSemitermVecLAct : ℕ) : V)] = ((3 : ℕ) : V) ∧
      rowB tbl.[((rIdx_isUTermVecOfSemitermVecLAct : ℕ) : V)] = ⌜Semiformula.lMap emb isUTermVecOfSemitermVecLActB⌝ :=
    h.2 rIdx_isUTermVecOfSemitermVecLAct (Nat.lt_of_sub_eq_succ rfl)
  refine ⟨this.1, ?_⟩
  rw [impChainV_vecOf, this.2, quote_row_isUTermVecOfSemitermVecLAct]

lemma walkTable_isUTermVecSigmaPiLAct {tbl : V} (h : WalkTable tbl) :
    rowM tbl.[((rIdx_isUTermVecSigmaPiLAct : ℕ) : V)] = ((2 : ℕ) : V) ∧
    rowB tbl.[((rIdx_isUTermVecSigmaPiLAct : ℕ) : V)] = impChainV LAct (vecOf row_isUTermVecSigmaPiLAct_as) row_isUTermVecSigmaPiLAct_c := by
  have this : rowM tbl.[((rIdx_isUTermVecSigmaPiLAct : ℕ) : V)] = ((2 : ℕ) : V) ∧
      rowB tbl.[((rIdx_isUTermVecSigmaPiLAct : ℕ) : V)] = ⌜Semiformula.lMap emb isUTermVecSigmaPiLActB⌝ :=
    h.2 rIdx_isUTermVecSigmaPiLAct (Nat.lt_of_sub_eq_succ rfl)
  refine ⟨this.1, ?_⟩
  rw [impChainV_vecOf, this.2, quote_row_isUTermVecSigmaPiLAct]

lemma walkTable_len {tbl : V} (h : WalkTable tbl) (i : ℕ) (hi : i < walkRowCount) : ((i : ℕ) : V) < len tbl :=
  lt_of_lt_of_le (by exact_mod_cast hi) h.1

/-! ### The piece table -/

/-- A step from the piece table: `mkStep W i ev = ⟪tag, i, ev, as, c⟫` where `W.[i] = ⟪tag, as, c⟫`. -/
noncomputable def mkStep (W i ev : V) : V := ⟪π₁ W.[i], i, ev, π₁ (π₂ W.[i]), π₂ (π₂ W.[i])⟫

def mkStepDef : 𝚺₁.Semisentence 4 := .mkSigma
  “y W i ev. ∃ r, !nthDef r W i ∧ ∃ t, !pi₁Def t r ∧ ∃ p, !pi₂Def p r ∧ ∃ as, !pi₁Def as p ∧ ∃ c, !pi₂Def c p ∧
    ∃ q₁, !pairDef q₁ as c ∧ ∃ q₂, !pairDef q₂ ev q₁ ∧ ∃ q₃, !pairDef q₃ i q₂ ∧ !pairDef y t q₃”

instance mkStep_defined : 𝚺₁-Function₃ (mkStep : V → V → V → V) via mkStepDef := .mk
  fun v ↦ by simp [mkStepDef, mkStep]
instance mkStep_definable : 𝚺₁-Function₃ (mkStep : V → V → V → V) := mkStep_defined.to_definable


noncomputable def piece_zeroLtSucc : V := ⟪(0 : V), vecOf row_zeroLtSucc_as, row_zeroLtSucc_c⟫
noncomputable def piece_succLtSucc : V := ⟪(0 : V), vecOf row_succLtSucc_as, row_succLtSucc_c⟫
noncomputable def piece_qqBvarTotal : V := ⟪(2 : V), vecOf row_qqBvarTotal_as, row_qqBvarTotal_R⟫
noncomputable def piece_isSemitermBvar : V := ⟪(0 : V), vecOf row_isSemitermBvar_as, row_isSemitermBvar_c⟫
noncomputable def piece_isSemitermSigmaPiLAct : V := ⟪(0 : V), vecOf row_isSemitermSigmaPiLAct_as, row_isSemitermSigmaPiLAct_c⟫
noncomputable def piece_qqFvarTotal : V := ⟪(2 : V), vecOf row_qqFvarTotal_as, row_qqFvarTotal_R⟫
noncomputable def piece_isSemitermFvar : V := ⟪(0 : V), vecOf row_isSemitermFvar_as, row_isSemitermFvar_c⟫
noncomputable def piece_qqFuncTotal : V := ⟪(2 : V), vecOf row_qqFuncTotal_as, row_qqFuncTotal_R⟫
noncomputable def piece_isSemitermFunc : V := ⟪(0 : V), vecOf row_isSemitermFunc_as, row_isSemitermFunc_c⟫
noncomputable def piece_isFuncConst_zero : V := ⟪(0 : V), vecOf row_isFuncConst_zero_as, row_isFuncConst_zero_c⟫
noncomputable def piece_isFuncConst_one : V := ⟪(0 : V), vecOf row_isFuncConst_one_as, row_isFuncConst_one_c⟫
noncomputable def piece_isFuncConst_add : V := ⟪(0 : V), vecOf row_isFuncConst_add_as, row_isFuncConst_add_c⟫
noncomputable def piece_isFuncConst_mul : V := ⟪(0 : V), vecOf row_isFuncConst_mul_as, row_isFuncConst_mul_c⟫
noncomputable def piece_isFuncConst_cC : V := ⟪(0 : V), vecOf row_isFuncConst_cC_as, row_isFuncConst_cC_c⟫
noncomputable def piece_isFuncConst_cD : V := ⟪(0 : V), vecOf row_isFuncConst_cD_as, row_isFuncConst_cD_c⟫
noncomputable def piece_isSemitermVecNil : V := ⟪(0 : V), vecOf row_isSemitermVecNil_as, row_isSemitermVecNil_c⟫
noncomputable def piece_isSemitermVecSigmaPiLAct : V := ⟪(0 : V), vecOf row_isSemitermVecSigmaPiLAct_as, row_isSemitermVecSigmaPiLAct_c⟫
noncomputable def piece_adjoinTotal : V := ⟪(2 : V), vecOf row_adjoinTotal_as, row_adjoinTotal_R⟫
noncomputable def piece_isSemitermVecAdjoin : V := ⟪(0 : V), vecOf row_isSemitermVecAdjoin_as, row_isSemitermVecAdjoin_c⟫
noncomputable def piece_qqVerumTotal : V := ⟪(2 : V), vecOf row_qqVerumTotal_as, row_qqVerumTotal_R⟫
noncomputable def piece_isSemiformulaVerum : V := ⟪(0 : V), vecOf row_isSemiformulaVerum_as, row_isSemiformulaVerum_c⟫
noncomputable def piece_isSemiformulaSigmaPi : V := ⟪(0 : V), vecOf row_isSemiformulaSigmaPi_as, row_isSemiformulaSigmaPi_c⟫
noncomputable def piece_qqFalsumTotal : V := ⟪(2 : V), vecOf row_qqFalsumTotal_as, row_qqFalsumTotal_R⟫
noncomputable def piece_isSemiformulaFalsum : V := ⟪(0 : V), vecOf row_isSemiformulaFalsum_as, row_isSemiformulaFalsum_c⟫
noncomputable def piece_qqAndTotal : V := ⟪(2 : V), vecOf row_qqAndTotal_as, row_qqAndTotal_R⟫
noncomputable def piece_isSemiformulaAnd : V := ⟪(0 : V), vecOf row_isSemiformulaAnd_as, row_isSemiformulaAnd_c⟫
noncomputable def piece_qqOrTotal : V := ⟪(2 : V), vecOf row_qqOrTotal_as, row_qqOrTotal_R⟫
noncomputable def piece_isSemiformulaOr : V := ⟪(0 : V), vecOf row_isSemiformulaOr_as, row_isSemiformulaOr_c⟫
noncomputable def piece_qqAllTotal : V := ⟪(2 : V), vecOf row_qqAllTotal_as, row_qqAllTotal_R⟫
noncomputable def piece_isSemiformulaAll : V := ⟪(0 : V), vecOf row_isSemiformulaAll_as, row_isSemiformulaAll_c⟫
noncomputable def piece_qqExsTotal : V := ⟪(2 : V), vecOf row_qqExsTotal_as, row_qqExsTotal_R⟫
noncomputable def piece_isSemiformulaExs : V := ⟪(0 : V), vecOf row_isSemiformulaExs_as, row_isSemiformulaExs_c⟫
noncomputable def piece_qqRelTotal : V := ⟪(2 : V), vecOf row_qqRelTotal_as, row_qqRelTotal_R⟫
noncomputable def piece_isSemiformulaRel : V := ⟪(0 : V), vecOf row_isSemiformulaRel_as, row_isSemiformulaRel_c⟫
noncomputable def piece_qqNRelTotal : V := ⟪(2 : V), vecOf row_qqNRelTotal_as, row_qqNRelTotal_R⟫
noncomputable def piece_isSemiformulaNRel : V := ⟪(0 : V), vecOf row_isSemiformulaNRel_as, row_isSemiformulaNRel_c⟫
noncomputable def piece_isRelConst_eq : V := ⟪(0 : V), vecOf row_isRelConst_eq_as, row_isRelConst_eq_c⟫
noncomputable def piece_isRelConst_lt : V := ⟪(0 : V), vecOf row_isRelConst_lt_as, row_isRelConst_lt_c⟫
noncomputable def piece_isUTermVecOfSemitermVecLAct : V := ⟪(0 : V), vecOf row_isUTermVecOfSemitermVecLAct_as, row_isUTermVecOfSemitermVecLAct_c⟫
noncomputable def piece_isUTermVecSigmaPiLAct : V := ⟪(0 : V), vecOf row_isUTermVecSigmaPiLAct_as, row_isUTermVecSigmaPiLAct_c⟫

/-- The pieces in index order. -/
noncomputable def walkPieceList : List V := [
  piece_zeroLtSucc,
  piece_succLtSucc,
  piece_qqBvarTotal,
  piece_isSemitermBvar,
  piece_isSemitermSigmaPiLAct,
  piece_qqFvarTotal,
  piece_isSemitermFvar,
  piece_qqFuncTotal,
  piece_isSemitermFunc,
  piece_isFuncConst_zero,
  piece_isFuncConst_one,
  piece_isFuncConst_add,
  piece_isFuncConst_mul,
  piece_isFuncConst_cC,
  piece_isFuncConst_cD,
  piece_isSemitermVecNil,
  piece_isSemitermVecSigmaPiLAct,
  piece_adjoinTotal,
  piece_isSemitermVecAdjoin,
  piece_qqVerumTotal,
  piece_isSemiformulaVerum,
  piece_isSemiformulaSigmaPi,
  piece_qqFalsumTotal,
  piece_isSemiformulaFalsum,
  piece_qqAndTotal,
  piece_isSemiformulaAnd,
  piece_qqOrTotal,
  piece_isSemiformulaOr,
  piece_qqAllTotal,
  piece_isSemiformulaAll,
  piece_qqExsTotal,
  piece_isSemiformulaExs,
  piece_qqRelTotal,
  piece_isSemiformulaRel,
  piece_qqNRelTotal,
  piece_isSemiformulaNRel,
  piece_isRelConst_eq,
  piece_isRelConst_lt,
  piece_isUTermVecOfSemitermVecLAct,
  piece_isUTermVecSigmaPiLAct]

/-- **The piece table of the walk** (a closed V-generic term). -/
noncomputable def walkPieces : V := vecOf walkPieceList


lemma walkPieces_zeroLtSucc : (walkPieces : V).[((rIdx_zeroLtSucc : ℕ) : V)] = piece_zeroLtSucc := by
  unfold walkPieces
  rw [nth_vecOf _ rIdx_zeroLtSucc (Nat.lt_of_sub_eq_succ rfl)]
  rfl

lemma mkStep_zeroLtSucc (ev : V) :
    mkStep walkPieces ((rIdx_zeroLtSucc : ℕ) : V) ev = sUseHorn ((rIdx_zeroLtSucc : ℕ) : V) ev (vecOf row_zeroLtSucc_as) row_zeroLtSucc_c := by
  rw [mkStep, walkPieces_zeroLtSucc]
  simp [piece_zeroLtSucc, sUseHorn]

lemma walkPieces_succLtSucc : (walkPieces : V).[((rIdx_succLtSucc : ℕ) : V)] = piece_succLtSucc := by
  unfold walkPieces
  rw [nth_vecOf _ rIdx_succLtSucc (Nat.lt_of_sub_eq_succ rfl)]
  rfl

lemma mkStep_succLtSucc (ev : V) :
    mkStep walkPieces ((rIdx_succLtSucc : ℕ) : V) ev = sUseHorn ((rIdx_succLtSucc : ℕ) : V) ev (vecOf row_succLtSucc_as) row_succLtSucc_c := by
  rw [mkStep, walkPieces_succLtSucc]
  simp [piece_succLtSucc, sUseHorn]

lemma walkPieces_qqBvarTotal : (walkPieces : V).[((rIdx_qqBvarTotal : ℕ) : V)] = piece_qqBvarTotal := by
  unfold walkPieces
  rw [nth_vecOf _ rIdx_qqBvarTotal (Nat.lt_of_sub_eq_succ rfl)]
  rfl

lemma mkStep_qqBvarTotal (ev : V) :
    mkStep walkPieces ((rIdx_qqBvarTotal : ℕ) : V) ev = sIntroFact ((rIdx_qqBvarTotal : ℕ) : V) ev (vecOf row_qqBvarTotal_as) row_qqBvarTotal_R := by
  rw [mkStep, walkPieces_qqBvarTotal]
  simp [piece_qqBvarTotal, sIntroFact]

lemma walkPieces_isSemitermBvar : (walkPieces : V).[((rIdx_isSemitermBvar : ℕ) : V)] = piece_isSemitermBvar := by
  unfold walkPieces
  rw [nth_vecOf _ rIdx_isSemitermBvar (Nat.lt_of_sub_eq_succ rfl)]
  rfl

lemma mkStep_isSemitermBvar (ev : V) :
    mkStep walkPieces ((rIdx_isSemitermBvar : ℕ) : V) ev = sUseHorn ((rIdx_isSemitermBvar : ℕ) : V) ev (vecOf row_isSemitermBvar_as) row_isSemitermBvar_c := by
  rw [mkStep, walkPieces_isSemitermBvar]
  simp [piece_isSemitermBvar, sUseHorn]

lemma walkPieces_isSemitermSigmaPiLAct : (walkPieces : V).[((rIdx_isSemitermSigmaPiLAct : ℕ) : V)] = piece_isSemitermSigmaPiLAct := by
  unfold walkPieces
  rw [nth_vecOf _ rIdx_isSemitermSigmaPiLAct (Nat.lt_of_sub_eq_succ rfl)]
  rfl

lemma mkStep_isSemitermSigmaPiLAct (ev : V) :
    mkStep walkPieces ((rIdx_isSemitermSigmaPiLAct : ℕ) : V) ev = sUseHorn ((rIdx_isSemitermSigmaPiLAct : ℕ) : V) ev (vecOf row_isSemitermSigmaPiLAct_as) row_isSemitermSigmaPiLAct_c := by
  rw [mkStep, walkPieces_isSemitermSigmaPiLAct]
  simp [piece_isSemitermSigmaPiLAct, sUseHorn]

lemma walkPieces_qqFvarTotal : (walkPieces : V).[((rIdx_qqFvarTotal : ℕ) : V)] = piece_qqFvarTotal := by
  unfold walkPieces
  rw [nth_vecOf _ rIdx_qqFvarTotal (Nat.lt_of_sub_eq_succ rfl)]
  rfl

lemma mkStep_qqFvarTotal (ev : V) :
    mkStep walkPieces ((rIdx_qqFvarTotal : ℕ) : V) ev = sIntroFact ((rIdx_qqFvarTotal : ℕ) : V) ev (vecOf row_qqFvarTotal_as) row_qqFvarTotal_R := by
  rw [mkStep, walkPieces_qqFvarTotal]
  simp [piece_qqFvarTotal, sIntroFact]

lemma walkPieces_isSemitermFvar : (walkPieces : V).[((rIdx_isSemitermFvar : ℕ) : V)] = piece_isSemitermFvar := by
  unfold walkPieces
  rw [nth_vecOf _ rIdx_isSemitermFvar (Nat.lt_of_sub_eq_succ rfl)]
  rfl

lemma mkStep_isSemitermFvar (ev : V) :
    mkStep walkPieces ((rIdx_isSemitermFvar : ℕ) : V) ev = sUseHorn ((rIdx_isSemitermFvar : ℕ) : V) ev (vecOf row_isSemitermFvar_as) row_isSemitermFvar_c := by
  rw [mkStep, walkPieces_isSemitermFvar]
  simp [piece_isSemitermFvar, sUseHorn]

lemma walkPieces_qqFuncTotal : (walkPieces : V).[((rIdx_qqFuncTotal : ℕ) : V)] = piece_qqFuncTotal := by
  unfold walkPieces
  rw [nth_vecOf _ rIdx_qqFuncTotal (Nat.lt_of_sub_eq_succ rfl)]
  rfl

lemma mkStep_qqFuncTotal (ev : V) :
    mkStep walkPieces ((rIdx_qqFuncTotal : ℕ) : V) ev = sIntroFact ((rIdx_qqFuncTotal : ℕ) : V) ev (vecOf row_qqFuncTotal_as) row_qqFuncTotal_R := by
  rw [mkStep, walkPieces_qqFuncTotal]
  simp [piece_qqFuncTotal, sIntroFact]

lemma walkPieces_isSemitermFunc : (walkPieces : V).[((rIdx_isSemitermFunc : ℕ) : V)] = piece_isSemitermFunc := by
  unfold walkPieces
  rw [nth_vecOf _ rIdx_isSemitermFunc (Nat.lt_of_sub_eq_succ rfl)]
  rfl

lemma mkStep_isSemitermFunc (ev : V) :
    mkStep walkPieces ((rIdx_isSemitermFunc : ℕ) : V) ev = sUseHorn ((rIdx_isSemitermFunc : ℕ) : V) ev (vecOf row_isSemitermFunc_as) row_isSemitermFunc_c := by
  rw [mkStep, walkPieces_isSemitermFunc]
  simp [piece_isSemitermFunc, sUseHorn]

lemma walkPieces_isFuncConst_zero : (walkPieces : V).[((rIdx_isFuncConst_zero : ℕ) : V)] = piece_isFuncConst_zero := by
  unfold walkPieces
  rw [nth_vecOf _ rIdx_isFuncConst_zero (Nat.lt_of_sub_eq_succ rfl)]
  rfl

lemma mkStep_isFuncConst_zero (ev : V) :
    mkStep walkPieces ((rIdx_isFuncConst_zero : ℕ) : V) ev = sUseHorn ((rIdx_isFuncConst_zero : ℕ) : V) ev (vecOf row_isFuncConst_zero_as) row_isFuncConst_zero_c := by
  rw [mkStep, walkPieces_isFuncConst_zero]
  simp [piece_isFuncConst_zero, sUseHorn]

lemma walkPieces_isFuncConst_one : (walkPieces : V).[((rIdx_isFuncConst_one : ℕ) : V)] = piece_isFuncConst_one := by
  unfold walkPieces
  rw [nth_vecOf _ rIdx_isFuncConst_one (Nat.lt_of_sub_eq_succ rfl)]
  rfl

lemma mkStep_isFuncConst_one (ev : V) :
    mkStep walkPieces ((rIdx_isFuncConst_one : ℕ) : V) ev = sUseHorn ((rIdx_isFuncConst_one : ℕ) : V) ev (vecOf row_isFuncConst_one_as) row_isFuncConst_one_c := by
  rw [mkStep, walkPieces_isFuncConst_one]
  simp [piece_isFuncConst_one, sUseHorn]

lemma walkPieces_isFuncConst_add : (walkPieces : V).[((rIdx_isFuncConst_add : ℕ) : V)] = piece_isFuncConst_add := by
  unfold walkPieces
  rw [nth_vecOf _ rIdx_isFuncConst_add (Nat.lt_of_sub_eq_succ rfl)]
  rfl

lemma mkStep_isFuncConst_add (ev : V) :
    mkStep walkPieces ((rIdx_isFuncConst_add : ℕ) : V) ev = sUseHorn ((rIdx_isFuncConst_add : ℕ) : V) ev (vecOf row_isFuncConst_add_as) row_isFuncConst_add_c := by
  rw [mkStep, walkPieces_isFuncConst_add]
  simp [piece_isFuncConst_add, sUseHorn]

lemma walkPieces_isFuncConst_mul : (walkPieces : V).[((rIdx_isFuncConst_mul : ℕ) : V)] = piece_isFuncConst_mul := by
  unfold walkPieces
  rw [nth_vecOf _ rIdx_isFuncConst_mul (Nat.lt_of_sub_eq_succ rfl)]
  rfl

lemma mkStep_isFuncConst_mul (ev : V) :
    mkStep walkPieces ((rIdx_isFuncConst_mul : ℕ) : V) ev = sUseHorn ((rIdx_isFuncConst_mul : ℕ) : V) ev (vecOf row_isFuncConst_mul_as) row_isFuncConst_mul_c := by
  rw [mkStep, walkPieces_isFuncConst_mul]
  simp [piece_isFuncConst_mul, sUseHorn]

lemma walkPieces_isFuncConst_cC : (walkPieces : V).[((rIdx_isFuncConst_cC : ℕ) : V)] = piece_isFuncConst_cC := by
  unfold walkPieces
  rw [nth_vecOf _ rIdx_isFuncConst_cC (Nat.lt_of_sub_eq_succ rfl)]
  rfl

lemma mkStep_isFuncConst_cC (ev : V) :
    mkStep walkPieces ((rIdx_isFuncConst_cC : ℕ) : V) ev = sUseHorn ((rIdx_isFuncConst_cC : ℕ) : V) ev (vecOf row_isFuncConst_cC_as) row_isFuncConst_cC_c := by
  rw [mkStep, walkPieces_isFuncConst_cC]
  simp [piece_isFuncConst_cC, sUseHorn]

lemma walkPieces_isFuncConst_cD : (walkPieces : V).[((rIdx_isFuncConst_cD : ℕ) : V)] = piece_isFuncConst_cD := by
  unfold walkPieces
  rw [nth_vecOf _ rIdx_isFuncConst_cD (Nat.lt_of_sub_eq_succ rfl)]
  rfl

lemma mkStep_isFuncConst_cD (ev : V) :
    mkStep walkPieces ((rIdx_isFuncConst_cD : ℕ) : V) ev = sUseHorn ((rIdx_isFuncConst_cD : ℕ) : V) ev (vecOf row_isFuncConst_cD_as) row_isFuncConst_cD_c := by
  rw [mkStep, walkPieces_isFuncConst_cD]
  simp [piece_isFuncConst_cD, sUseHorn]

lemma walkPieces_isSemitermVecNil : (walkPieces : V).[((rIdx_isSemitermVecNil : ℕ) : V)] = piece_isSemitermVecNil := by
  unfold walkPieces
  rw [nth_vecOf _ rIdx_isSemitermVecNil (Nat.lt_of_sub_eq_succ rfl)]
  rfl

lemma mkStep_isSemitermVecNil (ev : V) :
    mkStep walkPieces ((rIdx_isSemitermVecNil : ℕ) : V) ev = sUseHorn ((rIdx_isSemitermVecNil : ℕ) : V) ev (vecOf row_isSemitermVecNil_as) row_isSemitermVecNil_c := by
  rw [mkStep, walkPieces_isSemitermVecNil]
  simp [piece_isSemitermVecNil, sUseHorn]

lemma walkPieces_isSemitermVecSigmaPiLAct : (walkPieces : V).[((rIdx_isSemitermVecSigmaPiLAct : ℕ) : V)] = piece_isSemitermVecSigmaPiLAct := by
  unfold walkPieces
  rw [nth_vecOf _ rIdx_isSemitermVecSigmaPiLAct (Nat.lt_of_sub_eq_succ rfl)]
  rfl

lemma mkStep_isSemitermVecSigmaPiLAct (ev : V) :
    mkStep walkPieces ((rIdx_isSemitermVecSigmaPiLAct : ℕ) : V) ev = sUseHorn ((rIdx_isSemitermVecSigmaPiLAct : ℕ) : V) ev (vecOf row_isSemitermVecSigmaPiLAct_as) row_isSemitermVecSigmaPiLAct_c := by
  rw [mkStep, walkPieces_isSemitermVecSigmaPiLAct]
  simp [piece_isSemitermVecSigmaPiLAct, sUseHorn]

lemma walkPieces_adjoinTotal : (walkPieces : V).[((rIdx_adjoinTotal : ℕ) : V)] = piece_adjoinTotal := by
  unfold walkPieces
  rw [nth_vecOf _ rIdx_adjoinTotal (Nat.lt_of_sub_eq_succ rfl)]
  rfl

lemma mkStep_adjoinTotal (ev : V) :
    mkStep walkPieces ((rIdx_adjoinTotal : ℕ) : V) ev = sIntroFact ((rIdx_adjoinTotal : ℕ) : V) ev (vecOf row_adjoinTotal_as) row_adjoinTotal_R := by
  rw [mkStep, walkPieces_adjoinTotal]
  simp [piece_adjoinTotal, sIntroFact]

lemma walkPieces_isSemitermVecAdjoin : (walkPieces : V).[((rIdx_isSemitermVecAdjoin : ℕ) : V)] = piece_isSemitermVecAdjoin := by
  unfold walkPieces
  rw [nth_vecOf _ rIdx_isSemitermVecAdjoin (Nat.lt_of_sub_eq_succ rfl)]
  rfl

lemma mkStep_isSemitermVecAdjoin (ev : V) :
    mkStep walkPieces ((rIdx_isSemitermVecAdjoin : ℕ) : V) ev = sUseHorn ((rIdx_isSemitermVecAdjoin : ℕ) : V) ev (vecOf row_isSemitermVecAdjoin_as) row_isSemitermVecAdjoin_c := by
  rw [mkStep, walkPieces_isSemitermVecAdjoin]
  simp [piece_isSemitermVecAdjoin, sUseHorn]

lemma walkPieces_qqVerumTotal : (walkPieces : V).[((rIdx_qqVerumTotal : ℕ) : V)] = piece_qqVerumTotal := by
  unfold walkPieces
  rw [nth_vecOf _ rIdx_qqVerumTotal (Nat.lt_of_sub_eq_succ rfl)]
  rfl

lemma mkStep_qqVerumTotal (ev : V) :
    mkStep walkPieces ((rIdx_qqVerumTotal : ℕ) : V) ev = sIntroFact ((rIdx_qqVerumTotal : ℕ) : V) ev (vecOf row_qqVerumTotal_as) row_qqVerumTotal_R := by
  rw [mkStep, walkPieces_qqVerumTotal]
  simp [piece_qqVerumTotal, sIntroFact]

lemma walkPieces_isSemiformulaVerum : (walkPieces : V).[((rIdx_isSemiformulaVerum : ℕ) : V)] = piece_isSemiformulaVerum := by
  unfold walkPieces
  rw [nth_vecOf _ rIdx_isSemiformulaVerum (Nat.lt_of_sub_eq_succ rfl)]
  rfl

lemma mkStep_isSemiformulaVerum (ev : V) :
    mkStep walkPieces ((rIdx_isSemiformulaVerum : ℕ) : V) ev = sUseHorn ((rIdx_isSemiformulaVerum : ℕ) : V) ev (vecOf row_isSemiformulaVerum_as) row_isSemiformulaVerum_c := by
  rw [mkStep, walkPieces_isSemiformulaVerum]
  simp [piece_isSemiformulaVerum, sUseHorn]

lemma walkPieces_isSemiformulaSigmaPi : (walkPieces : V).[((rIdx_isSemiformulaSigmaPi : ℕ) : V)] = piece_isSemiformulaSigmaPi := by
  unfold walkPieces
  rw [nth_vecOf _ rIdx_isSemiformulaSigmaPi (Nat.lt_of_sub_eq_succ rfl)]
  rfl

lemma mkStep_isSemiformulaSigmaPi (ev : V) :
    mkStep walkPieces ((rIdx_isSemiformulaSigmaPi : ℕ) : V) ev = sUseHorn ((rIdx_isSemiformulaSigmaPi : ℕ) : V) ev (vecOf row_isSemiformulaSigmaPi_as) row_isSemiformulaSigmaPi_c := by
  rw [mkStep, walkPieces_isSemiformulaSigmaPi]
  simp [piece_isSemiformulaSigmaPi, sUseHorn]

lemma walkPieces_qqFalsumTotal : (walkPieces : V).[((rIdx_qqFalsumTotal : ℕ) : V)] = piece_qqFalsumTotal := by
  unfold walkPieces
  rw [nth_vecOf _ rIdx_qqFalsumTotal (Nat.lt_of_sub_eq_succ rfl)]
  rfl

lemma mkStep_qqFalsumTotal (ev : V) :
    mkStep walkPieces ((rIdx_qqFalsumTotal : ℕ) : V) ev = sIntroFact ((rIdx_qqFalsumTotal : ℕ) : V) ev (vecOf row_qqFalsumTotal_as) row_qqFalsumTotal_R := by
  rw [mkStep, walkPieces_qqFalsumTotal]
  simp [piece_qqFalsumTotal, sIntroFact]

lemma walkPieces_isSemiformulaFalsum : (walkPieces : V).[((rIdx_isSemiformulaFalsum : ℕ) : V)] = piece_isSemiformulaFalsum := by
  unfold walkPieces
  rw [nth_vecOf _ rIdx_isSemiformulaFalsum (Nat.lt_of_sub_eq_succ rfl)]
  rfl

lemma mkStep_isSemiformulaFalsum (ev : V) :
    mkStep walkPieces ((rIdx_isSemiformulaFalsum : ℕ) : V) ev = sUseHorn ((rIdx_isSemiformulaFalsum : ℕ) : V) ev (vecOf row_isSemiformulaFalsum_as) row_isSemiformulaFalsum_c := by
  rw [mkStep, walkPieces_isSemiformulaFalsum]
  simp [piece_isSemiformulaFalsum, sUseHorn]

lemma walkPieces_qqAndTotal : (walkPieces : V).[((rIdx_qqAndTotal : ℕ) : V)] = piece_qqAndTotal := by
  unfold walkPieces
  rw [nth_vecOf _ rIdx_qqAndTotal (Nat.lt_of_sub_eq_succ rfl)]
  rfl

lemma mkStep_qqAndTotal (ev : V) :
    mkStep walkPieces ((rIdx_qqAndTotal : ℕ) : V) ev = sIntroFact ((rIdx_qqAndTotal : ℕ) : V) ev (vecOf row_qqAndTotal_as) row_qqAndTotal_R := by
  rw [mkStep, walkPieces_qqAndTotal]
  simp [piece_qqAndTotal, sIntroFact]

lemma walkPieces_isSemiformulaAnd : (walkPieces : V).[((rIdx_isSemiformulaAnd : ℕ) : V)] = piece_isSemiformulaAnd := by
  unfold walkPieces
  rw [nth_vecOf _ rIdx_isSemiformulaAnd (Nat.lt_of_sub_eq_succ rfl)]
  rfl

lemma mkStep_isSemiformulaAnd (ev : V) :
    mkStep walkPieces ((rIdx_isSemiformulaAnd : ℕ) : V) ev = sUseHorn ((rIdx_isSemiformulaAnd : ℕ) : V) ev (vecOf row_isSemiformulaAnd_as) row_isSemiformulaAnd_c := by
  rw [mkStep, walkPieces_isSemiformulaAnd]
  simp [piece_isSemiformulaAnd, sUseHorn]

lemma walkPieces_qqOrTotal : (walkPieces : V).[((rIdx_qqOrTotal : ℕ) : V)] = piece_qqOrTotal := by
  unfold walkPieces
  rw [nth_vecOf _ rIdx_qqOrTotal (Nat.lt_of_sub_eq_succ rfl)]
  rfl

lemma mkStep_qqOrTotal (ev : V) :
    mkStep walkPieces ((rIdx_qqOrTotal : ℕ) : V) ev = sIntroFact ((rIdx_qqOrTotal : ℕ) : V) ev (vecOf row_qqOrTotal_as) row_qqOrTotal_R := by
  rw [mkStep, walkPieces_qqOrTotal]
  simp [piece_qqOrTotal, sIntroFact]

lemma walkPieces_isSemiformulaOr : (walkPieces : V).[((rIdx_isSemiformulaOr : ℕ) : V)] = piece_isSemiformulaOr := by
  unfold walkPieces
  rw [nth_vecOf _ rIdx_isSemiformulaOr (Nat.lt_of_sub_eq_succ rfl)]
  rfl

lemma mkStep_isSemiformulaOr (ev : V) :
    mkStep walkPieces ((rIdx_isSemiformulaOr : ℕ) : V) ev = sUseHorn ((rIdx_isSemiformulaOr : ℕ) : V) ev (vecOf row_isSemiformulaOr_as) row_isSemiformulaOr_c := by
  rw [mkStep, walkPieces_isSemiformulaOr]
  simp [piece_isSemiformulaOr, sUseHorn]

lemma walkPieces_qqAllTotal : (walkPieces : V).[((rIdx_qqAllTotal : ℕ) : V)] = piece_qqAllTotal := by
  unfold walkPieces
  rw [nth_vecOf _ rIdx_qqAllTotal (Nat.lt_of_sub_eq_succ rfl)]
  rfl

lemma mkStep_qqAllTotal (ev : V) :
    mkStep walkPieces ((rIdx_qqAllTotal : ℕ) : V) ev = sIntroFact ((rIdx_qqAllTotal : ℕ) : V) ev (vecOf row_qqAllTotal_as) row_qqAllTotal_R := by
  rw [mkStep, walkPieces_qqAllTotal]
  simp [piece_qqAllTotal, sIntroFact]

lemma walkPieces_isSemiformulaAll : (walkPieces : V).[((rIdx_isSemiformulaAll : ℕ) : V)] = piece_isSemiformulaAll := by
  unfold walkPieces
  rw [nth_vecOf _ rIdx_isSemiformulaAll (Nat.lt_of_sub_eq_succ rfl)]
  rfl

lemma mkStep_isSemiformulaAll (ev : V) :
    mkStep walkPieces ((rIdx_isSemiformulaAll : ℕ) : V) ev = sUseHorn ((rIdx_isSemiformulaAll : ℕ) : V) ev (vecOf row_isSemiformulaAll_as) row_isSemiformulaAll_c := by
  rw [mkStep, walkPieces_isSemiformulaAll]
  simp [piece_isSemiformulaAll, sUseHorn]

lemma walkPieces_qqExsTotal : (walkPieces : V).[((rIdx_qqExsTotal : ℕ) : V)] = piece_qqExsTotal := by
  unfold walkPieces
  rw [nth_vecOf _ rIdx_qqExsTotal (Nat.lt_of_sub_eq_succ rfl)]
  rfl

lemma mkStep_qqExsTotal (ev : V) :
    mkStep walkPieces ((rIdx_qqExsTotal : ℕ) : V) ev = sIntroFact ((rIdx_qqExsTotal : ℕ) : V) ev (vecOf row_qqExsTotal_as) row_qqExsTotal_R := by
  rw [mkStep, walkPieces_qqExsTotal]
  simp [piece_qqExsTotal, sIntroFact]

lemma walkPieces_isSemiformulaExs : (walkPieces : V).[((rIdx_isSemiformulaExs : ℕ) : V)] = piece_isSemiformulaExs := by
  unfold walkPieces
  rw [nth_vecOf _ rIdx_isSemiformulaExs (Nat.lt_of_sub_eq_succ rfl)]
  rfl

lemma mkStep_isSemiformulaExs (ev : V) :
    mkStep walkPieces ((rIdx_isSemiformulaExs : ℕ) : V) ev = sUseHorn ((rIdx_isSemiformulaExs : ℕ) : V) ev (vecOf row_isSemiformulaExs_as) row_isSemiformulaExs_c := by
  rw [mkStep, walkPieces_isSemiformulaExs]
  simp [piece_isSemiformulaExs, sUseHorn]

lemma walkPieces_qqRelTotal : (walkPieces : V).[((rIdx_qqRelTotal : ℕ) : V)] = piece_qqRelTotal := by
  unfold walkPieces
  rw [nth_vecOf _ rIdx_qqRelTotal (Nat.lt_of_sub_eq_succ rfl)]
  rfl

lemma mkStep_qqRelTotal (ev : V) :
    mkStep walkPieces ((rIdx_qqRelTotal : ℕ) : V) ev = sIntroFact ((rIdx_qqRelTotal : ℕ) : V) ev (vecOf row_qqRelTotal_as) row_qqRelTotal_R := by
  rw [mkStep, walkPieces_qqRelTotal]
  simp [piece_qqRelTotal, sIntroFact]

lemma walkPieces_isSemiformulaRel : (walkPieces : V).[((rIdx_isSemiformulaRel : ℕ) : V)] = piece_isSemiformulaRel := by
  unfold walkPieces
  rw [nth_vecOf _ rIdx_isSemiformulaRel (Nat.lt_of_sub_eq_succ rfl)]
  rfl

lemma mkStep_isSemiformulaRel (ev : V) :
    mkStep walkPieces ((rIdx_isSemiformulaRel : ℕ) : V) ev = sUseHorn ((rIdx_isSemiformulaRel : ℕ) : V) ev (vecOf row_isSemiformulaRel_as) row_isSemiformulaRel_c := by
  rw [mkStep, walkPieces_isSemiformulaRel]
  simp [piece_isSemiformulaRel, sUseHorn]

lemma walkPieces_qqNRelTotal : (walkPieces : V).[((rIdx_qqNRelTotal : ℕ) : V)] = piece_qqNRelTotal := by
  unfold walkPieces
  rw [nth_vecOf _ rIdx_qqNRelTotal (Nat.lt_of_sub_eq_succ rfl)]
  rfl

lemma mkStep_qqNRelTotal (ev : V) :
    mkStep walkPieces ((rIdx_qqNRelTotal : ℕ) : V) ev = sIntroFact ((rIdx_qqNRelTotal : ℕ) : V) ev (vecOf row_qqNRelTotal_as) row_qqNRelTotal_R := by
  rw [mkStep, walkPieces_qqNRelTotal]
  simp [piece_qqNRelTotal, sIntroFact]

lemma walkPieces_isSemiformulaNRel : (walkPieces : V).[((rIdx_isSemiformulaNRel : ℕ) : V)] = piece_isSemiformulaNRel := by
  unfold walkPieces
  rw [nth_vecOf _ rIdx_isSemiformulaNRel (Nat.lt_of_sub_eq_succ rfl)]
  rfl

lemma mkStep_isSemiformulaNRel (ev : V) :
    mkStep walkPieces ((rIdx_isSemiformulaNRel : ℕ) : V) ev = sUseHorn ((rIdx_isSemiformulaNRel : ℕ) : V) ev (vecOf row_isSemiformulaNRel_as) row_isSemiformulaNRel_c := by
  rw [mkStep, walkPieces_isSemiformulaNRel]
  simp [piece_isSemiformulaNRel, sUseHorn]

lemma walkPieces_isRelConst_eq : (walkPieces : V).[((rIdx_isRelConst_eq : ℕ) : V)] = piece_isRelConst_eq := by
  unfold walkPieces
  rw [nth_vecOf _ rIdx_isRelConst_eq (Nat.lt_of_sub_eq_succ rfl)]
  rfl

lemma mkStep_isRelConst_eq (ev : V) :
    mkStep walkPieces ((rIdx_isRelConst_eq : ℕ) : V) ev = sUseHorn ((rIdx_isRelConst_eq : ℕ) : V) ev (vecOf row_isRelConst_eq_as) row_isRelConst_eq_c := by
  rw [mkStep, walkPieces_isRelConst_eq]
  simp [piece_isRelConst_eq, sUseHorn]

lemma walkPieces_isRelConst_lt : (walkPieces : V).[((rIdx_isRelConst_lt : ℕ) : V)] = piece_isRelConst_lt := by
  unfold walkPieces
  rw [nth_vecOf _ rIdx_isRelConst_lt (Nat.lt_of_sub_eq_succ rfl)]
  rfl

lemma mkStep_isRelConst_lt (ev : V) :
    mkStep walkPieces ((rIdx_isRelConst_lt : ℕ) : V) ev = sUseHorn ((rIdx_isRelConst_lt : ℕ) : V) ev (vecOf row_isRelConst_lt_as) row_isRelConst_lt_c := by
  rw [mkStep, walkPieces_isRelConst_lt]
  simp [piece_isRelConst_lt, sUseHorn]

lemma walkPieces_isUTermVecOfSemitermVecLAct : (walkPieces : V).[((rIdx_isUTermVecOfSemitermVecLAct : ℕ) : V)] = piece_isUTermVecOfSemitermVecLAct := by
  unfold walkPieces
  rw [nth_vecOf _ rIdx_isUTermVecOfSemitermVecLAct (Nat.lt_of_sub_eq_succ rfl)]
  rfl

lemma mkStep_isUTermVecOfSemitermVecLAct (ev : V) :
    mkStep walkPieces ((rIdx_isUTermVecOfSemitermVecLAct : ℕ) : V) ev = sUseHorn ((rIdx_isUTermVecOfSemitermVecLAct : ℕ) : V) ev (vecOf row_isUTermVecOfSemitermVecLAct_as) row_isUTermVecOfSemitermVecLAct_c := by
  rw [mkStep, walkPieces_isUTermVecOfSemitermVecLAct]
  simp [piece_isUTermVecOfSemitermVecLAct, sUseHorn]

lemma walkPieces_isUTermVecSigmaPiLAct : (walkPieces : V).[((rIdx_isUTermVecSigmaPiLAct : ℕ) : V)] = piece_isUTermVecSigmaPiLAct := by
  unfold walkPieces
  rw [nth_vecOf _ rIdx_isUTermVecSigmaPiLAct (Nat.lt_of_sub_eq_succ rfl)]
  rfl

lemma mkStep_isUTermVecSigmaPiLAct (ev : V) :
    mkStep walkPieces ((rIdx_isUTermVecSigmaPiLAct : ℕ) : V) ev = sUseHorn ((rIdx_isUTermVecSigmaPiLAct : ℕ) : V) ev (vecOf row_isUTermVecSigmaPiLAct_as) row_isUTermVecSigmaPiLAct_c := by
  rw [mkStep, walkPieces_isUTermVecSigmaPiLAct]
  simp [piece_isUTermVecSigmaPiLAct, sUseHorn]

end rowTable

end ArithS
