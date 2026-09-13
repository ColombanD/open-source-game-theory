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

end ArithS
