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


/-! ## Part 2 — the term walk (D2 for terms)

DESIGN §4.2, the term and vector tables. Every producer takes the piece table `W` and the arity
`n` as parameters; a node's steps are assembled with `mkStep W (rIdx_<row>) ev` and the
witnesses are chain numerals `cTV _` or eigenvariable references `^&i`. Results are pairs
`⟪count, steps⟫` (`count` = the number of eigenvariable steps = `shiftsV steps`). -/

section termWalk

open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic

/-- The reference to a vector eigenvariable: `&c` when the vector is non-empty (`j ≠ 0`), the
literal `𝟎 = cT 0` (the empty vector IS the number `0`) when `j = 0`. -/
noncomputable def vRef (c j : V) : V := if j = 0 then 𝟎 else ^&c

def vRefDef : 𝚺₁.Semisentence 3 := .mkSigma “y c j. (j = 0 → y = ↑Arithmetic.zero) ∧ (j ≠ 0 → !qqFvarDef y c)”

instance vRef_defined : 𝚺₁-Function₂ (vRef : V → V → V) via vRefDef := .mk fun v ↦ by
  simp [vRefDef, vRef, numeral_eq_natCast]
  by_cases h : v 2 = 0 <;> simp [h]
instance vRef_definable : 𝚺₁-Function₂ (vRef : V → V → V) := vRef_defined.to_definable

@[simp] lemma vRef_zero (c : V) : vRef c 0 = 𝟎 := by simp [vRef]
lemma vRef_of_ne {c j : V} (h : j ≠ 0) : vRef c j = ^&c := by simp [vRef, h]

/-! ### 2.1 The `z < n` chain -/

namespace LtAux

noncomputable def blueprint : PR.Blueprint 3 where
  zero := .mkSigma “y W n z. ∃ m, !subDef m n (z + 1) ∧ ∃ c, !cTVGraph c m ∧ ∃ ev, !mkVec₁Def ev c ∧
    ∃ s, !mkStepDef s W 0 ev ∧ !mkVec₁Def y s”
  succ := .mkSigma “y ih i W n z. ∃ a, !cTVGraph a i ∧ ∃ m, !subDef m n z ∧ ∃ b, !cTVGraph b (m + i) ∧
    ∃ ev, !mkVec₂Def ev a b ∧ ∃ s, !mkStepDef s W 1 ev ∧ !concatDef y ih s”

noncomputable def construction : PR.Construction V blueprint where
  zero := fun v ↦ ?[mkStep (v 0) 0 ?[cTV (v 1 - (v 2 + 1))]]
  succ := fun v i ih ↦ concat ih (mkStep (v 0) 1 ?[cTV i, cTV (v 1 - v 2 + i)])
  zero_defined := .mk fun v ↦ by simp [blueprint, cTV.defined.iff, mkStep_defined.iff]
  succ_defined := .mk fun v ↦ by simp [blueprint, cTV.defined.iff, mkStep_defined.iff]

end LtAux

/-- `ltAux W n z j` — the first `j + 1` steps of the derivation of `z < n`: `0 < n - z`, then
`i < n - z + i → i + 1 < n - z + i + 1` for `i < j`. -/
noncomputable def ltAux (W n z j : V) : V := LtAux.construction.result ![W, n, z] j

/-- `ltSteps W n z = ltAux W n z z` derives `ltFact (cTV z) (cTV n)` (when `z < n`). -/
noncomputable def ltSteps (W n z : V) : V := ltAux W n z z

@[simp] lemma ltAux_zero (W n z : V) :
    ltAux W n z 0 = ?[mkStep W 0 ?[cTV (n - (z + 1))]] := by simp [ltAux, LtAux.construction]
@[simp] lemma ltAux_succ (W n z j : V) :
    ltAux W n z (j + 1) = concat (ltAux W n z j) (mkStep W 1 ?[cTV j, cTV (n - z + j)]) := by
  simp [ltAux, LtAux.construction]

noncomputable def ltAuxDef : 𝚺₁.Semisentence 5 :=
  LtAux.blueprint.resultDef |>.rew (Rew.subst ![#0, #4, #1, #2, #3])

instance ltAux_defined : 𝚺₁-Function₄ (ltAux : V → V → V → V → V) via ltAuxDef := .mk
  fun v ↦ by simp [LtAux.construction.result_defined_iff, ltAuxDef]; rfl
instance ltAux_definable : 𝚺₁-Function₄ (ltAux : V → V → V → V → V) := ltAux_defined.to_definable

/-- `ltSteps` as a substitution instance of `ltAuxDef` (NOT a DSL wrapper: `simp` on the wrapper
form normalizes the duplicated variable through the whole PR `resultDef` and runs away). -/
noncomputable def ltStepsDef : 𝚺₁.Semisentence 4 := ltAuxDef.rew (Rew.subst ![#0, #1, #2, #3, #3])

instance ltSteps_defined : 𝚺₁-Function₃ (ltSteps : V → V → V → V) via ltStepsDef := .mk
  fun v ↦ by simp [ltStepsDef, ltAuxDef, LtAux.construction.result_defined_iff, ltSteps]; rfl
instance ltSteps_definable : 𝚺₁-Function₃ (ltSteps : V → V → V → V) := ltSteps_defined.to_definable

/-! ### 2.2 The node emitters -/

/-- (T#) the bound variable `^#z`: `ltSteps`, then `qqBvarTotal [cTV z]`, `isSemitermBvar
[cTV n, cTV z, &0]`, the bridge `[cTV n, &0]`. Count `1`. -/
noncomputable def bvarNode (W n z : V) : V :=
  ⟪1, appendV (ltSteps W n z)
    ?[mkStep W 2 ?[cTV z], mkStep W 3 ?[cTV n, cTV z, ^&0], mkStep W 4 ?[cTV n, ^&0]]⟫

noncomputable def bvarNodeDef : 𝚺₁.Semisentence 4 := .mkSigma
  “y W n z. ∃ L, !ltStepsDef L W n z ∧ ∃ cz, !cTVGraph cz z ∧ ∃ cn, !cTVGraph cn n ∧ ∃ f0, !qqFvarDef f0 0 ∧
    ∃ e₁, !mkVec₁Def e₁ cz ∧ ∃ s₁, !mkStepDef s₁ W 2 e₁ ∧
    ∃ e₂₀, !mkVec₁Def e₂₀ f0 ∧ ∃ e₂₁, !adjoinDef e₂₁ cz e₂₀ ∧ ∃ e₂, !adjoinDef e₂ cn e₂₁ ∧ ∃ s₂, !mkStepDef s₂ W 3 e₂ ∧
    ∃ e₃, !mkVec₂Def e₃ cn f0 ∧ ∃ s₃, !mkStepDef s₃ W 4 e₃ ∧
    ∃ l₃, !mkVec₁Def l₃ s₃ ∧ ∃ l₂, !adjoinDef l₂ s₂ l₃ ∧ ∃ l₁, !adjoinDef l₁ s₁ l₂ ∧
    ∃ S, !appendVDef S L l₁ ∧ !pairDef y 1 S”

instance bvarNode_defined : 𝚺₁-Function₃ (bvarNode : V → V → V → V) via bvarNodeDef := .mk
  fun v ↦ by simp [bvarNodeDef, bvarNode, numeral_eq_natCast, ltSteps_defined.iff, cTV.defined.iff, mkStep_defined.iff, appendV_defined.iff]
instance bvarNode_definable : 𝚺₁-Function₃ (bvarNode : V → V → V → V) := bvarNode_defined.to_definable

/-- (T&) the free variable `^&x`: `qqFvarTotal [cTV x]`, `isSemitermFvar [cTV n, cTV x, &0]`, the
bridge. Count `1`. -/
noncomputable def fvarNode (W n x : V) : V :=
  ⟪1, ?[mkStep W 5 ?[cTV x], mkStep W 6 ?[cTV n, cTV x, ^&0], mkStep W 4 ?[cTV n, ^&0]]⟫

noncomputable def fvarNodeDef : 𝚺₁.Semisentence 4 := .mkSigma
  “y W n x. ∃ cx, !cTVGraph cx x ∧ ∃ cn, !cTVGraph cn n ∧ ∃ f0, !qqFvarDef f0 0 ∧
    ∃ e₁, !mkVec₁Def e₁ cx ∧ ∃ s₁, !mkStepDef s₁ W 5 e₁ ∧
    ∃ e₂₀, !mkVec₁Def e₂₀ f0 ∧ ∃ e₂₁, !adjoinDef e₂₁ cx e₂₀ ∧ ∃ e₂, !adjoinDef e₂ cn e₂₁ ∧ ∃ s₂, !mkStepDef s₂ W 6 e₂ ∧
    ∃ e₃, !mkVec₂Def e₃ cn f0 ∧ ∃ s₃, !mkStepDef s₃ W 4 e₃ ∧
    ∃ l₃, !mkVec₁Def l₃ s₃ ∧ ∃ l₂, !adjoinDef l₂ s₂ l₃ ∧ ∃ l₁, !adjoinDef l₁ s₁ l₂ ∧ !pairDef y 1 l₁”

instance fvarNode_defined : 𝚺₁-Function₃ (fvarNode : V → V → V → V) via fvarNodeDef := .mk
  fun v ↦ by simp [fvarNodeDef, fvarNode, numeral_eq_natCast, cTV.defined.iff, mkStep_defined.iff]
instance fvarNode_definable : 𝚺₁-Function₃ (fvarNode : V → V → V → V) := fvarNode_defined.to_definable

/-- (V0) the empty vector: `isSemitermVecNil [cTV n]`, the bridge `[cTV 0, cTV n, cTV 0]`. Count `0`. -/
noncomputable def nilNode (W n : V) : V :=
  ⟪0, ?[mkStep W 15 ?[cTV n], mkStep W 16 ?[cTV 0, cTV n, cTV 0]]⟫

noncomputable def nilNodeDef : 𝚺₁.Semisentence 3 := .mkSigma
  “y W n. ∃ cn, !cTVGraph cn n ∧ ∃ c0, !cTVGraph c0 0 ∧
    ∃ e₁, !mkVec₁Def e₁ cn ∧ ∃ s₁, !mkStepDef s₁ W 15 e₁ ∧
    ∃ e₂₀, !mkVec₁Def e₂₀ c0 ∧ ∃ e₂₁, !adjoinDef e₂₁ cn e₂₀ ∧ ∃ e₂, !adjoinDef e₂ c0 e₂₁ ∧ ∃ s₂, !mkStepDef s₂ W 16 e₂ ∧
    ∃ l₂, !mkVec₁Def l₂ s₂ ∧ ∃ l₁, !adjoinDef l₁ s₁ l₂ ∧ !pairDef y 0 l₁”

instance nilNode_defined : 𝚺₁-Function₂ (nilNode : V → V → V) via nilNodeDef := .mk
  fun v ↦ by simp [nilNodeDef, nilNode, numeral_eq_natCast, cTV.defined.iff, mkStep_defined.iff]
instance nilNode_definable : 𝚺₁-Function₂ (nilNode : V → V → V) := nilNode_defined.to_definable

/-- (V∷) one more entry in front of a described vector of length `j`: given the entry's result
`p = ⟪ct, St⟫` and the tail's result `ih = ⟪cv, Sv⟫`, the steps `Sv ++ St ++ [adjoinTotal [&0, ⟨v'⟩],
isSemitermVecAdjoin [cTV j, cTV n, ⟨v'⟩', &1, &0], the bridge [cTV (j+1), cTV n, &0]]` with
`⟨v'⟩ = vRef ct j` (the tail's eigenvariable after the entry's `ct` shifts) and `⟨v'⟩' = vRef (ct+1) j`.
Count `cv + ct + 1`. -/
noncomputable def adjNode (W n j p ih : V) : V :=
  ⟪π₁ ih + π₁ p + 1, appendV (π₂ ih) (appendV (π₂ p)
    ?[mkStep W 17 ?[^&0, vRef (π₁ p) j],
      mkStep W 18 ?[cTV j, cTV n, vRef (π₁ p + 1) j, ^&1, ^&0],
      mkStep W 16 ?[cTV (j + 1), cTV n, ^&0]])⟫

noncomputable def adjNodeDef : 𝚺₁.Semisentence 6 := .mkSigma
  “y W n j p ih. ∃ cv, !pi₁Def cv ih ∧ ∃ Sv, !pi₂Def Sv ih ∧ ∃ ct, !pi₁Def ct p ∧ ∃ St, !pi₂Def St p ∧
    ∃ f0, !qqFvarDef f0 0 ∧ ∃ f1, !qqFvarDef f1 1 ∧ ∃ r, !vRefDef r ct j ∧ ∃ r', !vRefDef r' (ct + 1) j ∧
    ∃ cj, !cTVGraph cj j ∧ ∃ cn, !cTVGraph cn n ∧ ∃ cj', !cTVGraph cj' (j + 1) ∧
    ∃ e₁, !mkVec₂Def e₁ f0 r ∧ ∃ s₁, !mkStepDef s₁ W 17 e₁ ∧
    ∃ e₂₀, !mkVec₂Def e₂₀ f1 f0 ∧ ∃ e₂₁, !adjoinDef e₂₁ r' e₂₀ ∧ ∃ e₂₂, !adjoinDef e₂₂ cn e₂₁ ∧
    ∃ e₂, !adjoinDef e₂ cj e₂₂ ∧ ∃ s₂, !mkStepDef s₂ W 18 e₂ ∧
    ∃ e₃₀, !mkVec₁Def e₃₀ f0 ∧ ∃ e₃₁, !adjoinDef e₃₁ cn e₃₀ ∧ ∃ e₃, !adjoinDef e₃ cj' e₃₁ ∧ ∃ s₃, !mkStepDef s₃ W 16 e₃ ∧
    ∃ l₃, !mkVec₁Def l₃ s₃ ∧ ∃ l₂, !adjoinDef l₂ s₂ l₃ ∧ ∃ l₁, !adjoinDef l₁ s₁ l₂ ∧
    ∃ S₂, !appendVDef S₂ St l₁ ∧ ∃ S, !appendVDef S Sv S₂ ∧ !pairDef y (cv + ct + 1) S”

instance adjNode_defined : 𝚺₁-Function₅ (adjNode : V → V → V → V → V → V) via adjNodeDef := .mk
  fun v ↦ by
    simp [adjNodeDef, adjNode, numeral_eq_natCast, cTV.defined.iff, mkStep_defined.iff, appendV_defined.iff, vRef_defined.iff]
instance adjNode_definable : 𝚺₁.DefinableFunction₅ (adjNode : V → V → V → V → V → V) :=
  adjNode_defined.to_definable

namespace DescVecAux

noncomputable def blueprint : PR.Blueprint 3 where
  zero := .mkSigma “y W n w. ∃ s, !nilNodeDef s W n ∧ y = s”
  succ := .mkSigma “y ih i W n w. ∃ p, !nthFromEndDef p w i ∧ ∃ s, !adjNodeDef s W n i p ih ∧ y = s”

noncomputable def construction : PR.Construction V blueprint where
  zero := fun v ↦ nilNode (v 0) (v 1)
  succ := fun v i ih ↦ adjNode (v 0) (v 1) i (nthFromEnd (v 2) i) ih
  zero_defined := .mk fun v ↦ by simp [blueprint, nilNode_defined.iff]
  succ_defined := .mk fun v ↦ by simp [blueprint, nthFromEnd_defined.iff, adjNode_defined.iff]

end DescVecAux

/-- `descVecAux W n w j` — the vector walk over the LAST `j` entries of the result vector `w`
(entry `w.[i] = ⟪count, steps⟫` of the `i`-th term), tail first. -/
noncomputable def descVecAux (W n w j : V) : V := DescVecAux.construction.result ![W, n, w] j

@[simp] lemma descVecAux_zero (W n w : V) : descVecAux W n w 0 = nilNode W n := by
  simp [descVecAux, DescVecAux.construction]
@[simp] lemma descVecAux_succ (W n w j : V) :
    descVecAux W n w (j + 1) = adjNode W n j (nthFromEnd w j) (descVecAux W n w j) := by
  simp [descVecAux, DescVecAux.construction]

noncomputable def descVecAuxDef : 𝚺₁.Semisentence 5 :=
  DescVecAux.blueprint.resultDef |>.rew (Rew.subst ![#0, #4, #1, #2, #3])

instance descVecAux_defined : 𝚺₁-Function₄ (descVecAux : V → V → V → V → V) via descVecAuxDef := .mk
  fun v ↦ by simp [DescVecAux.construction.result_defined_iff, descVecAuxDef]; rfl
instance descVecAux_definable : 𝚺₁-Function₄ (descVecAux : V → V → V → V → V) :=
  descVecAux_defined.to_definable

/-- The row of the closed symbol fact `isFunc k f` (`LAct`: `(0,0)` zero, `(0,1)` one, `(0,2)` c_C,
`(0,3)` c_D, `(2,0)` add, `(2,1)` mul). -/
noncomputable def funcRow (k f : V) : V :=
  if k = 0 then (if f = 0 then 9 else if f = 1 then 10 else if f = 2 then 13 else 14)
  else (if f = 0 then 11 else 12)

def funcRowDef : 𝚺₀.Semisentence 3 := .mkSigma
  “y k f. (k = 0 → ((f = 0 → y = 9) ∧ (f = 1 → y = 10) ∧ (f = 2 → y = 13) ∧ (f ≠ 0 → f ≠ 1 → f ≠ 2 → y = 14))) ∧
    (k ≠ 0 → ((f = 0 → y = 11) ∧ (f ≠ 0 → y = 12)))”

instance funcRow_defined : 𝚺₀-Function₂ (funcRow : V → V → V) via funcRowDef := .mk fun v ↦ by
  simp [funcRowDef, funcRow, numeral_eq_natCast]
  by_cases hk : v 1 = 0 <;> simp [hk]
  · by_cases h0 : v 2 = 0
    · simp [h0]
    by_cases h1 : v 2 = 1
    · simp [h0, h1]
    by_cases h2 : v 2 = 2
    · simp [h0, h1, h2]
    · simp [h0, h1, h2]
  · by_cases h0 : v 2 = 0 <;> simp [h0]
instance funcRow_definable : 𝚺₀-Function₂ (funcRow : V → V → V) := funcRow_defined.to_definable

/-- (Tf) the function node `^func k f v` after its vector (result `d = ⟪cv, Sv⟫`): the closed symbol
row, `qqFuncTotal [cTV k, cTV f, ⟨v⟩]`, `isSemitermFunc [cTV n, cTV k, cTV f, ⟨v⟩', &0]`, the bridge,
then `isUTermVecOfSemitermVecLAct [cTV k, cTV n, ⟨v⟩']` and its bridge `[cTV k, ⟨v⟩']`, with
`⟨v⟩ = vRef 0 k`, `⟨v⟩' = vRef 1 k`. Count `cv + 1`. -/
noncomputable def funcNode (W n k f d : V) : V :=
  ⟪π₁ d + 1, appendV (π₂ d)
    ?[mkStep W (funcRow k f) 0,
      mkStep W 7 ?[cTV k, cTV f, vRef 0 k],
      mkStep W 8 ?[cTV n, cTV k, cTV f, vRef 1 k, ^&0],
      mkStep W 4 ?[cTV n, ^&0],
      mkStep W 38 ?[cTV k, cTV n, vRef 1 k],
      mkStep W 39 ?[cTV k, vRef 1 k]]⟫

noncomputable def funcNodeDef : 𝚺₁.Semisentence 6 := .mkSigma
  “y W n k f d. ∃ cv, !pi₁Def cv d ∧ ∃ Sv, !pi₂Def Sv d ∧
    ∃ f0, !qqFvarDef f0 0 ∧ ∃ r0, !vRefDef r0 0 k ∧ ∃ r1, !vRefDef r1 1 k ∧
    ∃ ck, !cTVGraph ck k ∧ ∃ cf, !cTVGraph cf f ∧ ∃ cn, !cTVGraph cn n ∧
    ∃ i₁, !funcRowDef i₁ k f ∧ ∃ s₁, !mkStepDef s₁ W i₁ 0 ∧
    ∃ e₂₀, !mkVec₂Def e₂₀ cf r0 ∧ ∃ e₂, !adjoinDef e₂ ck e₂₀ ∧ ∃ s₂, !mkStepDef s₂ W 7 e₂ ∧
    ∃ e₃₀, !mkVec₂Def e₃₀ r1 f0 ∧ ∃ e₃₁, !adjoinDef e₃₁ cf e₃₀ ∧ ∃ e₃₂, !adjoinDef e₃₂ ck e₃₁ ∧
    ∃ e₃, !adjoinDef e₃ cn e₃₂ ∧ ∃ s₃, !mkStepDef s₃ W 8 e₃ ∧
    ∃ e₄, !mkVec₂Def e₄ cn f0 ∧ ∃ s₄, !mkStepDef s₄ W 4 e₄ ∧
    ∃ e₅₀, !mkVec₂Def e₅₀ cn r1 ∧ ∃ e₅, !adjoinDef e₅ ck e₅₀ ∧ ∃ s₅, !mkStepDef s₅ W 38 e₅ ∧
    ∃ e₆, !mkVec₂Def e₆ ck r1 ∧ ∃ s₆, !mkStepDef s₆ W 39 e₆ ∧
    ∃ l₆, !mkVec₁Def l₆ s₆ ∧ ∃ l₅, !adjoinDef l₅ s₅ l₆ ∧ ∃ l₄, !adjoinDef l₄ s₄ l₅ ∧
    ∃ l₃, !adjoinDef l₃ s₃ l₄ ∧ ∃ l₂, !adjoinDef l₂ s₂ l₃ ∧ ∃ l₁, !adjoinDef l₁ s₁ l₂ ∧
    ∃ S, !appendVDef S Sv l₁ ∧ !pairDef y (cv + 1) S”

instance funcNode_defined : 𝚺₁-Function₅ (funcNode : V → V → V → V → V → V) via funcNodeDef := .mk
  fun v ↦ by
    simp [funcNodeDef, funcNode, numeral_eq_natCast, cTV.defined.iff, mkStep_defined.iff, appendV_defined.iff, vRef_defined.iff,
      funcRow_defined.iff]
instance funcNode_definable : 𝚺₁.DefinableFunction₅ (funcNode : V → V → V → V → V → V) :=
  funcNode_defined.to_definable

/-! ### 2.3 The term walk (`TermRec` with the parameters `W`, `n`) -/

namespace DescT

noncomputable def blueprint : Language.TermRec.Blueprint 2 where
  bvar := .mkSigma “y z W n. ∃ s, !bvarNodeDef s W n z ∧ y = s”
  fvar := .mkSigma “y x W n. ∃ s, !fvarNodeDef s W n x ∧ y = s”
  func := .mkSigma “y k f v w W n. ∃ d, !descVecAuxDef d W n w k ∧ ∃ s, !funcNodeDef s W n k f d ∧ y = s”

noncomputable def construction : Language.TermRec.Construction V blueprint where
  bvar := fun param z ↦ bvarNode (param 0) (param 1) z
  fvar := fun param x ↦ fvarNode (param 0) (param 1) x
  func := fun param k f _ w ↦ funcNode (param 0) (param 1) k f (descVecAux (param 0) (param 1) w k)
  bvar_defined := .mk fun v ↦ by simp [blueprint, bvarNode_defined.iff]
  fvar_defined := .mk fun v ↦ by simp [blueprint, fvarNode_defined.iff]
  func_defined := .mk fun v ↦ by simp [blueprint, descVecAux_defined.iff, funcNode_defined.iff]

end DescT

/-- **The term walk**: `descT W n t = ⟪count, steps⟫`. -/
noncomputable def descT (W n t : V) : V := DescT.construction.result LAct ![W, n] t
/-- The result vector of the term walk over a vector `v` of length `k`. -/
noncomputable def descTVec (W n k v : V) : V := DescT.construction.resultVec LAct ![W, n] k v

/-- The step list of the term walk. -/
noncomputable def describeT (W n t : V) : V := π₂ (descT W n t)
/-- The number of eigenvariables the term walk introduces. -/
noncomputable def descCountT (W n t : V) : V := π₁ (descT W n t)

@[simp] lemma descT_bvar (W n z : V) : descT W n (^#z) = bvarNode W n z := by
  simp [descT, DescT.construction]
@[simp] lemma descT_fvar (W n x : V) : descT W n (^&x) = fvarNode W n x := by
  simp [descT, DescT.construction]
lemma descT_func (W n : V) {k f v : V} (hkf : LAct.IsFunc k f) (hv : IsUTermVec LAct k v) :
    descT W n (^func k f v) = funcNode W n k f (descVecAux W n (descTVec W n k v) k) := by
  simp [descT, descTVec, DescT.construction, hkf, hv]

lemma len_descTVec (W n : V) {k v : V} (hv : IsUTermVec LAct k v) : len (descTVec W n k v) = k :=
  DescT.construction.resultVec_lh LAct _ hv
lemma nth_descTVec (W n : V) {k v i : V} (hv : IsUTermVec LAct k v) (hi : i < k) :
    (descTVec W n k v).[i] = descT W n v.[i] :=
  DescT.construction.nth_resultVec LAct _ hv hi

noncomputable def descTDef : 𝚺₁.Semisentence 4 :=
  (DescT.blueprint.result LAct).rew (Rew.subst ![#0, #3, #1, #2])

instance descT_defined : 𝚺₁-Function₃ (descT : V → V → V → V) via descTDef := .mk
  fun v ↦ by simp [descTDef, DescT.construction.result_graphDef]; rfl
instance descT_definable : 𝚺₁-Function₃ (descT : V → V → V → V) := descT_defined.to_definable

noncomputable def descTVecDef : 𝚺₁.Semisentence 5 :=
  (DescT.blueprint.resultVec LAct).rew (Rew.subst ![#0, #3, #4, #1, #2])

instance descTVec_defined : 𝚺₁-Function₄ (descTVec : V → V → V → V → V) via descTVecDef := .mk
  fun v ↦ by simp [descTVecDef, DescT.construction.resultVec_defined.iff]; rfl
instance descTVec_definable : 𝚺₁-Function₄ (descTVec : V → V → V → V → V) := descTVec_defined.to_definable

noncomputable def describeTDef : 𝚺₁.Semisentence 4 := .mkSigma “y W n t. ∃ d, !descTDef d W n t ∧ !pi₂Def y d”
noncomputable def descCountTDef : 𝚺₁.Semisentence 4 := .mkSigma “y W n t. ∃ d, !descTDef d W n t ∧ !pi₁Def y d”

instance describeT_defined : 𝚺₁-Function₃ (describeT : V → V → V → V) via describeTDef := .mk
  fun v ↦ by simp [describeTDef, descT_defined.iff, describeT]
instance describeT_definable : 𝚺₁-Function₃ (describeT : V → V → V → V) := describeT_defined.to_definable
instance descCountT_defined : 𝚺₁-Function₃ (descCountT : V → V → V → V) via descCountTDef := .mk
  fun v ↦ by simp [descCountTDef, descT_defined.iff, descCountT]
instance descCountT_definable : 𝚺₁-Function₃ (descCountT : V → V → V → V) := descCountT_defined.to_definable

/-! ### The per-constructor equations -/

lemma describeT_bvar (W n z : V) : describeT W n (^#z) =
    appendV (ltSteps W n z) ?[mkStep W 2 ?[cTV z], mkStep W 3 ?[cTV n, cTV z, ^&0], mkStep W 4 ?[cTV n, ^&0]] := by
  simp [describeT, bvarNode]
lemma descCountT_bvar (W n z : V) : descCountT W n (^#z) = 1 := by simp [descCountT, bvarNode]
lemma describeT_fvar (W n x : V) : describeT W n (^&x) =
    ?[mkStep W 5 ?[cTV x], mkStep W 6 ?[cTV n, cTV x, ^&0], mkStep W 4 ?[cTV n, ^&0]] := by
  simp [describeT, fvarNode]
lemma descCountT_fvar (W n x : V) : descCountT W n (^&x) = 1 := by simp [descCountT, fvarNode]
lemma describeT_func (W n : V) {k f v : V} (hkf : LAct.IsFunc k f) (hv : IsUTermVec LAct k v) :
    describeT W n (^func k f v) =
      appendV (π₂ (descVecAux W n (descTVec W n k v) k))
        ?[mkStep W (funcRow k f) 0,
          mkStep W 7 ?[cTV k, cTV f, vRef 0 k],
          mkStep W 8 ?[cTV n, cTV k, cTV f, vRef 1 k, ^&0],
          mkStep W 4 ?[cTV n, ^&0],
          mkStep W 38 ?[cTV k, cTV n, vRef 1 k],
          mkStep W 39 ?[cTV k, vRef 1 k]] := by
  rw [describeT, descT_func W n hkf hv]; simp [funcNode]
lemma descCountT_func (W n : V) {k f v : V} (hkf : LAct.IsFunc k f) (hv : IsUTermVec LAct k v) :
    descCountT W n (^func k f v) = π₁ (descVecAux W n (descTVec W n k v) k) + 1 := by
  rw [descCountT, descT_func W n hkf hv]; simp [funcNode]

end termWalk

/-! ## Part 3 — applicability of the term walk (D3 for terms) -/

section stepLemmas

/-- **A Horn step assembled from lists is applicable.** -/
lemma stepOK_useHorn {tbl N E M Γ : V} (htbl : TableOK tbl N) {i : V} (es l : List V) {c : V}
    (hΓ : IsFormulaSet LAct Γ) (hi : i < len tbl) (hm : rowM tbl.[i] = (es.length : V))
    (hB : rowB tbl.[i] = impChainV LAct (vecOf l) c)
    (hM : (es.length : V) ≤ M) (hM' : (l.length : V) ≤ M)
    (hes : ∀ e ∈ es, IsSemiterm LAct 0 e ∧ termLen LAct e ≤ E)
    (hneg : ∀ a ∈ l, neg LAct (instOuter LAct es a) ∈ Γ) :
    StepOK tbl E M Γ (sUseHorn i (vecOf es) (vecOf l) c) := by
  have hrow := (htbl i hi).1
  rw [hm, hB, impChainV_vecOf] at hrow
  have hl : ∀ a ∈ l, IsSemiformula LAct (es.length : V) a := (isSemiformula_of_impChain hrow).1
  refine ⟨hΓ, Or.inl ⟨by simp, ⟨by simpa using hi, by simpa using hm, by simpa using hM, by simpa using hM', ?_, ?_⟩,
    by simpa using hB⟩⟩
  · intro k hk
    rw [sEv_sUseHorn, len_vecOf] at hk
    obtain ⟨k', rfl⟩ := eq_nat_of_lt_nat hk
    have hk' : k' < es.length := by exact_mod_cast hk
    rw [sEv_sUseHorn, nth_vecOf es k' hk']
    exact hes _ (List.getElem_mem hk')
  · intro k hk
    rw [sAs_sUseHorn, len_vecOf] at hk
    obtain ⟨k', rfl⟩ := eq_nat_of_lt_nat hk
    have hk' : k' < l.length := by exact_mod_cast hk
    rw [sAs_sUseHorn, sEv_sUseHorn, nth_vecOf l k' hk',
      subst_revV_vecOf es (hl _ (List.getElem_mem hk')) (fun e he ↦ (hes e he).1)]
    exact hneg _ (List.getElem_mem hk')

lemma ctxAfter_useHorn {Γ i : V} (es l : List V) {c : V} (hc : IsSemiformula LAct (es.length : V) c)
    (hes : ∀ e ∈ es, IsSemiterm LAct 0 e) :
    ctxAfter Γ (sUseHorn i (vecOf es) (vecOf l) c) = insert (neg LAct (instOuter LAct es c)) Γ := by
  rw [ctxAfter_tag0 (by simp), sEv_sUseHorn, sC_sUseHorn, subst_revV_vecOf es hc hes]

/-- **A totality step assembled from lists is applicable.** -/
lemma stepOK_introFact {tbl N E M Γ : V} (htbl : TableOK tbl N) {i : V} (es l : List V) {R : V}
    (hΓ : IsFormulaSet LAct Γ) (hi : i < len tbl) (hm : rowM tbl.[i] = (es.length : V))
    (hB : rowB tbl.[i] = impChainV LAct (vecOf l) (^∃ R))
    (hM : (es.length : V) ≤ M) (hM' : (l.length : V) ≤ M)
    (hes : ∀ e ∈ es, IsSemiterm LAct 0 e ∧ termLen LAct e ≤ E)
    (hneg : ∀ a ∈ l, neg LAct (instOuter LAct es a) ∈ Γ) :
    StepOK tbl E M Γ (sIntroFact i (vecOf es) (vecOf l) R) := by
  have hrow := (htbl i hi).1
  rw [hm, hB, impChainV_vecOf] at hrow
  have hl : ∀ a ∈ l, IsSemiformula LAct (es.length : V) a := (isSemiformula_of_impChain hrow).1
  refine ⟨hΓ, Or.inr (Or.inr (Or.inl ⟨by simp, ⟨by simpa using hi, by simpa using hm, by simpa using hM,
    by simpa using hM', ?_, ?_⟩, by simpa using hB⟩))⟩
  · intro k hk
    rw [sEv_sIntroFact, len_vecOf] at hk
    obtain ⟨k', rfl⟩ := eq_nat_of_lt_nat hk
    have hk' : k' < es.length := by exact_mod_cast hk
    rw [sEv_sIntroFact, nth_vecOf es k' hk']
    exact hes _ (List.getElem_mem hk')
  · intro k hk
    rw [sAs_sIntroFact, len_vecOf] at hk
    obtain ⟨k', rfl⟩ := eq_nat_of_lt_nat hk
    have hk' : k' < l.length := by exact_mod_cast hk
    rw [sAs_sIntroFact, sEv_sIntroFact, nth_vecOf l k' hk',
      subst_revV_vecOf es (hl _ (List.getElem_mem hk')) (fun e he ↦ (hes e he).1)]
    exact hneg _ (List.getElem_mem hk')

lemma ctxAfter_introFact {Γ i : V} (es l : List V) {R : V} (hR : IsSemiformula LAct ((es.length : V) + 1) R)
    (hes : ∀ e ∈ es, IsSemiterm LAct 0 e) :
    ctxAfter Γ (sIntroFact i (vecOf es) (vecOf l) R) =
      insert (neg LAct (free LAct (instOuterAt LAct 1 es R))) (setShift LAct Γ) := by
  rw [ctxAfter_tag2 (by simp), sEv_sIntroFact, sC_sIntroFact, subst_qVec_revV_vecOf es hR hes]

lemma vecOf_two (a b : V) : vecOf [a, b] = ?[a, b] := rfl
lemma vecOf_three (a b c : V) : vecOf [a, b, c] = ?[a, b, c] := rfl

/-- The antecedent memberships from an `inst_<row>` map equation. -/
lemma neg_mem_of_map {es l fs : List V} {Γ : V} (h : l.map (instOuter LAct es) = fs)
    (hfs : ∀ b ∈ fs, neg LAct b ∈ Γ) : ∀ a ∈ l, neg LAct (instOuter LAct es a) ∈ Γ :=
  fun a ha ↦ hfs _ (h ▸ List.mem_map_of_mem ha)

/-- Row `zeroLtSucc` as a step. -/
lemma ok_zeroLtSucc {tbl N E Γ W : V} {wy : V} (htbl : TableOK tbl N) (hW : WalkTable tbl) (hWp : W = walkPieces)
    (hΓ : IsFormulaSet LAct Γ) (hwy : IsSemiterm LAct 0 wy) (hEwy : termLen LAct wy ≤ E)  :
    StepOK tbl E ((8 : ℕ) : V) Γ (mkStep W 0 ?[wy]) ∧ sTag (mkStep W 0 ?[wy]) = 0 ∧
    ctxAfter Γ (mkStep W 0 ?[wy]) = insert (neg LAct (ltFact (𝟎 : V) (wy ^+ (𝟏 : V)))) Γ := by
  subst hWp
  have hk : ((rIdx_zeroLtSucc : ℕ) : V) = (0 : V) := by simp [rIdx_zeroLtSucc]
  have hstep := mkStep_zeroLtSucc (V := V) ?[wy]
  have hlen := walkTable_len hW rIdx_zeroLtSucc (by decide)
  have hrow := walkTable_zeroLtSucc hW
  rw [hk] at hstep hlen hrow
  have hes : ∀ e ∈ [wy], IsSemiterm LAct 0 e ∧ termLen LAct e ≤ E := List.forall_mem_cons.mpr ⟨⟨hwy, hEwy⟩, List.forall_mem_nil _⟩
  have hinst := inst_zeroLtSucc hwy
  rw [hstep]
  rw [show (?[wy] : V) = vecOf [wy] from rfl]
  refine ⟨stepOK_useHorn htbl [wy] row_zeroLtSucc_as hΓ hlen hrow.1 hrow.2 (by exact_mod_cast (by decide : 1 ≤ 8))
    (by rw [show row_zeroLtSucc_as.length = 0 from rfl]; exact_mod_cast (by decide : 0 ≤ 8)) hes ?_, by simp, ?_⟩
  · exact neg_mem_of_map hinst.1 (List.forall_mem_nil _)
  · rw [ctxAfter_useHorn [wy] row_zeroLtSucc_as isSemiformula_zeroLtSucc_c (fun e he ↦ (hes e he).1), hinst.2]

/-- Row `succLtSucc` as a step. -/
lemma ok_succLtSucc {tbl N E Γ W : V} {wx : V} {wy : V} (htbl : TableOK tbl N) (hW : WalkTable tbl) (hWp : W = walkPieces)
    (hΓ : IsFormulaSet LAct Γ) (hwx : IsSemiterm LAct 0 wx) (hEwx : termLen LAct wx ≤ E) (hwy : IsSemiterm LAct 0 wy) (hEwy : termLen LAct wy ≤ E) (hmem0 : neg LAct (ltFact wx wy) ∈ Γ) :
    StepOK tbl E ((8 : ℕ) : V) Γ (mkStep W 1 ?[wx, wy]) ∧ sTag (mkStep W 1 ?[wx, wy]) = 0 ∧
    ctxAfter Γ (mkStep W 1 ?[wx, wy]) = insert (neg LAct (ltFact (wx ^+ (𝟏 : V)) (wy ^+ (𝟏 : V)))) Γ := by
  subst hWp
  have hk : ((rIdx_succLtSucc : ℕ) : V) = (1 : V) := by simp [rIdx_succLtSucc]
  have hstep := mkStep_succLtSucc (V := V) ?[wx, wy]
  have hlen := walkTable_len hW rIdx_succLtSucc (by decide)
  have hrow := walkTable_succLtSucc hW
  rw [hk] at hstep hlen hrow
  have hes : ∀ e ∈ [wx, wy], IsSemiterm LAct 0 e ∧ termLen LAct e ≤ E := List.forall_mem_cons.mpr ⟨⟨hwx, hEwx⟩, List.forall_mem_cons.mpr ⟨⟨hwy, hEwy⟩, List.forall_mem_nil _⟩⟩
  have hinst := inst_succLtSucc hwx hwy
  rw [hstep]
  rw [show (?[wx, wy] : V) = vecOf [wx, wy] from rfl]
  refine ⟨stepOK_useHorn htbl [wx, wy] row_succLtSucc_as hΓ hlen hrow.1 hrow.2 (by exact_mod_cast (by decide : 2 ≤ 8))
    (by rw [show row_succLtSucc_as.length = 1 from rfl]; exact_mod_cast (by decide : 1 ≤ 8)) hes ?_, by simp, ?_⟩
  · exact neg_mem_of_map hinst.1 (List.forall_mem_cons.mpr ⟨hmem0, List.forall_mem_nil _⟩)
  · rw [ctxAfter_useHorn [wx, wy] row_succLtSucc_as isSemiformula_succLtSucc_c (fun e he ↦ (hes e he).1), hinst.2]

/-- Row `isSemitermBvar` as a step. -/
lemma ok_isSemitermBvar {tbl N E Γ W : V} {wn : V} {wz : V} {wt : V} (htbl : TableOK tbl N) (hW : WalkTable tbl) (hWp : W = walkPieces)
    (hΓ : IsFormulaSet LAct Γ) (hwn : IsSemiterm LAct 0 wn) (hEwn : termLen LAct wn ≤ E) (hwz : IsSemiterm LAct 0 wz) (hEwz : termLen LAct wz ≤ E) (hwt : IsSemiterm LAct 0 wt) (hEwt : termLen LAct wt ≤ E) (hmem0 : neg LAct (ltFact wz wn) ∈ Γ) (hmem1 : neg LAct (bvarFact wt wz) ∈ Γ) :
    StepOK tbl E ((8 : ℕ) : V) Γ (mkStep W 3 ?[wn, wz, wt]) ∧ sTag (mkStep W 3 ?[wn, wz, wt]) = 0 ∧
    ctxAfter Γ (mkStep W 3 ?[wn, wz, wt]) = insert (neg LAct (tSigmaFact wn wt)) Γ := by
  subst hWp
  have hk : ((rIdx_isSemitermBvar : ℕ) : V) = (3 : V) := by simp [rIdx_isSemitermBvar]
  have hstep := mkStep_isSemitermBvar (V := V) ?[wn, wz, wt]
  have hlen := walkTable_len hW rIdx_isSemitermBvar (by decide)
  have hrow := walkTable_isSemitermBvar hW
  rw [hk] at hstep hlen hrow
  have hes : ∀ e ∈ [wn, wz, wt], IsSemiterm LAct 0 e ∧ termLen LAct e ≤ E := List.forall_mem_cons.mpr ⟨⟨hwn, hEwn⟩, List.forall_mem_cons.mpr ⟨⟨hwz, hEwz⟩, List.forall_mem_cons.mpr ⟨⟨hwt, hEwt⟩, List.forall_mem_nil _⟩⟩⟩
  have hinst := inst_isSemitermBvar hwn hwz hwt
  rw [hstep]
  rw [show (?[wn, wz, wt] : V) = vecOf [wn, wz, wt] from rfl]
  refine ⟨stepOK_useHorn htbl [wn, wz, wt] row_isSemitermBvar_as hΓ hlen hrow.1 hrow.2 (by exact_mod_cast (by decide : 3 ≤ 8))
    (by rw [show row_isSemitermBvar_as.length = 2 from rfl]; exact_mod_cast (by decide : 2 ≤ 8)) hes ?_, by simp, ?_⟩
  · exact neg_mem_of_map hinst.1 (List.forall_mem_cons.mpr ⟨hmem0, List.forall_mem_cons.mpr ⟨hmem1, List.forall_mem_nil _⟩⟩)
  · rw [ctxAfter_useHorn [wn, wz, wt] row_isSemitermBvar_as isSemiformula_isSemitermBvar_c (fun e he ↦ (hes e he).1), hinst.2]

/-- Row `isSemitermSigmaPiLAct` as a step. -/
lemma ok_isSemitermSigmaPiLAct {tbl N E Γ W : V} {wn : V} {wt : V} (htbl : TableOK tbl N) (hW : WalkTable tbl) (hWp : W = walkPieces)
    (hΓ : IsFormulaSet LAct Γ) (hwn : IsSemiterm LAct 0 wn) (hEwn : termLen LAct wn ≤ E) (hwt : IsSemiterm LAct 0 wt) (hEwt : termLen LAct wt ≤ E) (hmem0 : neg LAct (tSigmaFact wn wt) ∈ Γ) :
    StepOK tbl E ((8 : ℕ) : V) Γ (mkStep W 4 ?[wn, wt]) ∧ sTag (mkStep W 4 ?[wn, wt]) = 0 ∧
    ctxAfter Γ (mkStep W 4 ?[wn, wt]) = insert (neg LAct (tPiFact wn wt)) Γ := by
  subst hWp
  have hk : ((rIdx_isSemitermSigmaPiLAct : ℕ) : V) = (4 : V) := by simp [rIdx_isSemitermSigmaPiLAct]
  have hstep := mkStep_isSemitermSigmaPiLAct (V := V) ?[wn, wt]
  have hlen := walkTable_len hW rIdx_isSemitermSigmaPiLAct (by decide)
  have hrow := walkTable_isSemitermSigmaPiLAct hW
  rw [hk] at hstep hlen hrow
  have hes : ∀ e ∈ [wn, wt], IsSemiterm LAct 0 e ∧ termLen LAct e ≤ E := List.forall_mem_cons.mpr ⟨⟨hwn, hEwn⟩, List.forall_mem_cons.mpr ⟨⟨hwt, hEwt⟩, List.forall_mem_nil _⟩⟩
  have hinst := inst_isSemitermSigmaPiLAct hwn hwt
  rw [hstep]
  rw [show (?[wn, wt] : V) = vecOf [wn, wt] from rfl]
  refine ⟨stepOK_useHorn htbl [wn, wt] row_isSemitermSigmaPiLAct_as hΓ hlen hrow.1 hrow.2 (by exact_mod_cast (by decide : 2 ≤ 8))
    (by rw [show row_isSemitermSigmaPiLAct_as.length = 1 from rfl]; exact_mod_cast (by decide : 1 ≤ 8)) hes ?_, by simp, ?_⟩
  · exact neg_mem_of_map hinst.1 (List.forall_mem_cons.mpr ⟨hmem0, List.forall_mem_nil _⟩)
  · rw [ctxAfter_useHorn [wn, wt] row_isSemitermSigmaPiLAct_as isSemiformula_isSemitermSigmaPiLAct_c (fun e he ↦ (hes e he).1), hinst.2]

/-- Row `isSemitermFvar` as a step. -/
lemma ok_isSemitermFvar {tbl N E Γ W : V} {wn : V} {wx : V} {wt : V} (htbl : TableOK tbl N) (hW : WalkTable tbl) (hWp : W = walkPieces)
    (hΓ : IsFormulaSet LAct Γ) (hwn : IsSemiterm LAct 0 wn) (hEwn : termLen LAct wn ≤ E) (hwx : IsSemiterm LAct 0 wx) (hEwx : termLen LAct wx ≤ E) (hwt : IsSemiterm LAct 0 wt) (hEwt : termLen LAct wt ≤ E) (hmem0 : neg LAct (fvarFact wt wx) ∈ Γ) :
    StepOK tbl E ((8 : ℕ) : V) Γ (mkStep W 6 ?[wn, wx, wt]) ∧ sTag (mkStep W 6 ?[wn, wx, wt]) = 0 ∧
    ctxAfter Γ (mkStep W 6 ?[wn, wx, wt]) = insert (neg LAct (tSigmaFact wn wt)) Γ := by
  subst hWp
  have hk : ((rIdx_isSemitermFvar : ℕ) : V) = (6 : V) := by simp [rIdx_isSemitermFvar]
  have hstep := mkStep_isSemitermFvar (V := V) ?[wn, wx, wt]
  have hlen := walkTable_len hW rIdx_isSemitermFvar (by decide)
  have hrow := walkTable_isSemitermFvar hW
  rw [hk] at hstep hlen hrow
  have hes : ∀ e ∈ [wn, wx, wt], IsSemiterm LAct 0 e ∧ termLen LAct e ≤ E := List.forall_mem_cons.mpr ⟨⟨hwn, hEwn⟩, List.forall_mem_cons.mpr ⟨⟨hwx, hEwx⟩, List.forall_mem_cons.mpr ⟨⟨hwt, hEwt⟩, List.forall_mem_nil _⟩⟩⟩
  have hinst := inst_isSemitermFvar hwn hwx hwt
  rw [hstep]
  rw [show (?[wn, wx, wt] : V) = vecOf [wn, wx, wt] from rfl]
  refine ⟨stepOK_useHorn htbl [wn, wx, wt] row_isSemitermFvar_as hΓ hlen hrow.1 hrow.2 (by exact_mod_cast (by decide : 3 ≤ 8))
    (by rw [show row_isSemitermFvar_as.length = 1 from rfl]; exact_mod_cast (by decide : 1 ≤ 8)) hes ?_, by simp, ?_⟩
  · exact neg_mem_of_map hinst.1 (List.forall_mem_cons.mpr ⟨hmem0, List.forall_mem_nil _⟩)
  · rw [ctxAfter_useHorn [wn, wx, wt] row_isSemitermFvar_as isSemiformula_isSemitermFvar_c (fun e he ↦ (hes e he).1), hinst.2]

/-- Row `isSemitermFunc` as a step. -/
lemma ok_isSemitermFunc {tbl N E Γ W : V} {wn : V} {wk : V} {wf : V} {wv : V} {wt : V} (htbl : TableOK tbl N) (hW : WalkTable tbl) (hWp : W = walkPieces)
    (hΓ : IsFormulaSet LAct Γ) (hwn : IsSemiterm LAct 0 wn) (hEwn : termLen LAct wn ≤ E) (hwk : IsSemiterm LAct 0 wk) (hEwk : termLen LAct wk ≤ E) (hwf : IsSemiterm LAct 0 wf) (hEwf : termLen LAct wf ≤ E) (hwv : IsSemiterm LAct 0 wv) (hEwv : termLen LAct wv ≤ E) (hwt : IsSemiterm LAct 0 wt) (hEwt : termLen LAct wt ≤ E) (hmem0 : neg LAct (isFuncFact wk wf) ∈ Γ) (hmem1 : neg LAct (tvPiFact wk wn wv) ∈ Γ) (hmem2 : neg LAct (funcFact wt wk wf wv) ∈ Γ) :
    StepOK tbl E ((8 : ℕ) : V) Γ (mkStep W 8 ?[wn, wk, wf, wv, wt]) ∧ sTag (mkStep W 8 ?[wn, wk, wf, wv, wt]) = 0 ∧
    ctxAfter Γ (mkStep W 8 ?[wn, wk, wf, wv, wt]) = insert (neg LAct (tSigmaFact wn wt)) Γ := by
  subst hWp
  have hk : ((rIdx_isSemitermFunc : ℕ) : V) = (8 : V) := by simp [rIdx_isSemitermFunc]
  have hstep := mkStep_isSemitermFunc (V := V) ?[wn, wk, wf, wv, wt]
  have hlen := walkTable_len hW rIdx_isSemitermFunc (by decide)
  have hrow := walkTable_isSemitermFunc hW
  rw [hk] at hstep hlen hrow
  have hes : ∀ e ∈ [wn, wk, wf, wv, wt], IsSemiterm LAct 0 e ∧ termLen LAct e ≤ E := List.forall_mem_cons.mpr ⟨⟨hwn, hEwn⟩, List.forall_mem_cons.mpr ⟨⟨hwk, hEwk⟩, List.forall_mem_cons.mpr ⟨⟨hwf, hEwf⟩, List.forall_mem_cons.mpr ⟨⟨hwv, hEwv⟩, List.forall_mem_cons.mpr ⟨⟨hwt, hEwt⟩, List.forall_mem_nil _⟩⟩⟩⟩⟩
  have hinst := inst_isSemitermFunc hwn hwk hwf hwv hwt
  rw [hstep]
  rw [show (?[wn, wk, wf, wv, wt] : V) = vecOf [wn, wk, wf, wv, wt] from rfl]
  refine ⟨stepOK_useHorn htbl [wn, wk, wf, wv, wt] row_isSemitermFunc_as hΓ hlen hrow.1 hrow.2 (by exact_mod_cast (by decide : 5 ≤ 8))
    (by rw [show row_isSemitermFunc_as.length = 3 from rfl]; exact_mod_cast (by decide : 3 ≤ 8)) hes ?_, by simp, ?_⟩
  · exact neg_mem_of_map hinst.1 (List.forall_mem_cons.mpr ⟨hmem0, List.forall_mem_cons.mpr ⟨hmem1, List.forall_mem_cons.mpr ⟨hmem2, List.forall_mem_nil _⟩⟩⟩)
  · rw [ctxAfter_useHorn [wn, wk, wf, wv, wt] row_isSemitermFunc_as isSemiformula_isSemitermFunc_c (fun e he ↦ (hes e he).1), hinst.2]

/-- Row `isFuncConst_zero` as a step. -/
lemma ok_isFuncConst_zero {tbl N E Γ W : V}  (htbl : TableOK tbl N) (hW : WalkTable tbl) (hWp : W = walkPieces)
    (hΓ : IsFormulaSet LAct Γ)   :
    StepOK tbl E ((8 : ℕ) : V) Γ (mkStep W 9 0) ∧ sTag (mkStep W 9 0) = 0 ∧
    ctxAfter Γ (mkStep W 9 0) = insert (neg LAct (isFuncFact (cT 0) (cT 0))) Γ := by
  subst hWp
  have hk : ((rIdx_isFuncConst_zero : ℕ) : V) = (9 : V) := by simp [rIdx_isFuncConst_zero]
  have hstep := mkStep_isFuncConst_zero (V := V) 0
  have hlen := walkTable_len hW rIdx_isFuncConst_zero (by decide)
  have hrow := walkTable_isFuncConst_zero hW
  rw [hk] at hstep hlen hrow
  have hes : ∀ e ∈ ([] : List V), IsSemiterm LAct 0 e ∧ termLen LAct e ≤ E := List.forall_mem_nil _
  have hinst := inst_isFuncConst_zero (V := V)
  rw [hstep]
  refine ⟨stepOK_useHorn htbl ([] : List V) row_isFuncConst_zero_as hΓ hlen hrow.1 hrow.2 (by exact_mod_cast (by decide : 0 ≤ 8))
    (by rw [show row_isFuncConst_zero_as.length = 0 from rfl]; exact_mod_cast (by decide : 0 ≤ 8)) hes ?_, by simp, ?_⟩
  · exact neg_mem_of_map hinst.1 (List.forall_mem_nil _)
  · show ctxAfter Γ (sUseHorn 9 (vecOf ([] : List V)) (vecOf row_isFuncConst_zero_as) row_isFuncConst_zero_c) = _
    rw [ctxAfter_useHorn ([] : List V) row_isFuncConst_zero_as isSemiformula_isFuncConst_zero_c (fun e he ↦ (hes e he).1), hinst.2]

/-- Row `isFuncConst_one` as a step. -/
lemma ok_isFuncConst_one {tbl N E Γ W : V}  (htbl : TableOK tbl N) (hW : WalkTable tbl) (hWp : W = walkPieces)
    (hΓ : IsFormulaSet LAct Γ)   :
    StepOK tbl E ((8 : ℕ) : V) Γ (mkStep W 10 0) ∧ sTag (mkStep W 10 0) = 0 ∧
    ctxAfter Γ (mkStep W 10 0) = insert (neg LAct (isFuncFact (cT 0) (cT 1))) Γ := by
  subst hWp
  have hk : ((rIdx_isFuncConst_one : ℕ) : V) = (10 : V) := by simp [rIdx_isFuncConst_one]
  have hstep := mkStep_isFuncConst_one (V := V) 0
  have hlen := walkTable_len hW rIdx_isFuncConst_one (by decide)
  have hrow := walkTable_isFuncConst_one hW
  rw [hk] at hstep hlen hrow
  have hes : ∀ e ∈ ([] : List V), IsSemiterm LAct 0 e ∧ termLen LAct e ≤ E := List.forall_mem_nil _
  have hinst := inst_isFuncConst_one (V := V)
  rw [hstep]
  refine ⟨stepOK_useHorn htbl ([] : List V) row_isFuncConst_one_as hΓ hlen hrow.1 hrow.2 (by exact_mod_cast (by decide : 0 ≤ 8))
    (by rw [show row_isFuncConst_one_as.length = 0 from rfl]; exact_mod_cast (by decide : 0 ≤ 8)) hes ?_, by simp, ?_⟩
  · exact neg_mem_of_map hinst.1 (List.forall_mem_nil _)
  · show ctxAfter Γ (sUseHorn 10 (vecOf ([] : List V)) (vecOf row_isFuncConst_one_as) row_isFuncConst_one_c) = _
    rw [ctxAfter_useHorn ([] : List V) row_isFuncConst_one_as isSemiformula_isFuncConst_one_c (fun e he ↦ (hes e he).1), hinst.2]

/-- Row `isFuncConst_add` as a step. -/
lemma ok_isFuncConst_add {tbl N E Γ W : V}  (htbl : TableOK tbl N) (hW : WalkTable tbl) (hWp : W = walkPieces)
    (hΓ : IsFormulaSet LAct Γ)   :
    StepOK tbl E ((8 : ℕ) : V) Γ (mkStep W 11 0) ∧ sTag (mkStep W 11 0) = 0 ∧
    ctxAfter Γ (mkStep W 11 0) = insert (neg LAct (isFuncFact (cT 2) (cT 0))) Γ := by
  subst hWp
  have hk : ((rIdx_isFuncConst_add : ℕ) : V) = (11 : V) := by simp [rIdx_isFuncConst_add]
  have hstep := mkStep_isFuncConst_add (V := V) 0
  have hlen := walkTable_len hW rIdx_isFuncConst_add (by decide)
  have hrow := walkTable_isFuncConst_add hW
  rw [hk] at hstep hlen hrow
  have hes : ∀ e ∈ ([] : List V), IsSemiterm LAct 0 e ∧ termLen LAct e ≤ E := List.forall_mem_nil _
  have hinst := inst_isFuncConst_add (V := V)
  rw [hstep]
  refine ⟨stepOK_useHorn htbl ([] : List V) row_isFuncConst_add_as hΓ hlen hrow.1 hrow.2 (by exact_mod_cast (by decide : 0 ≤ 8))
    (by rw [show row_isFuncConst_add_as.length = 0 from rfl]; exact_mod_cast (by decide : 0 ≤ 8)) hes ?_, by simp, ?_⟩
  · exact neg_mem_of_map hinst.1 (List.forall_mem_nil _)
  · show ctxAfter Γ (sUseHorn 11 (vecOf ([] : List V)) (vecOf row_isFuncConst_add_as) row_isFuncConst_add_c) = _
    rw [ctxAfter_useHorn ([] : List V) row_isFuncConst_add_as isSemiformula_isFuncConst_add_c (fun e he ↦ (hes e he).1), hinst.2]

/-- Row `isFuncConst_mul` as a step. -/
lemma ok_isFuncConst_mul {tbl N E Γ W : V}  (htbl : TableOK tbl N) (hW : WalkTable tbl) (hWp : W = walkPieces)
    (hΓ : IsFormulaSet LAct Γ)   :
    StepOK tbl E ((8 : ℕ) : V) Γ (mkStep W 12 0) ∧ sTag (mkStep W 12 0) = 0 ∧
    ctxAfter Γ (mkStep W 12 0) = insert (neg LAct (isFuncFact (cT 2) (cT 1))) Γ := by
  subst hWp
  have hk : ((rIdx_isFuncConst_mul : ℕ) : V) = (12 : V) := by simp [rIdx_isFuncConst_mul]
  have hstep := mkStep_isFuncConst_mul (V := V) 0
  have hlen := walkTable_len hW rIdx_isFuncConst_mul (by decide)
  have hrow := walkTable_isFuncConst_mul hW
  rw [hk] at hstep hlen hrow
  have hes : ∀ e ∈ ([] : List V), IsSemiterm LAct 0 e ∧ termLen LAct e ≤ E := List.forall_mem_nil _
  have hinst := inst_isFuncConst_mul (V := V)
  rw [hstep]
  refine ⟨stepOK_useHorn htbl ([] : List V) row_isFuncConst_mul_as hΓ hlen hrow.1 hrow.2 (by exact_mod_cast (by decide : 0 ≤ 8))
    (by rw [show row_isFuncConst_mul_as.length = 0 from rfl]; exact_mod_cast (by decide : 0 ≤ 8)) hes ?_, by simp, ?_⟩
  · exact neg_mem_of_map hinst.1 (List.forall_mem_nil _)
  · show ctxAfter Γ (sUseHorn 12 (vecOf ([] : List V)) (vecOf row_isFuncConst_mul_as) row_isFuncConst_mul_c) = _
    rw [ctxAfter_useHorn ([] : List V) row_isFuncConst_mul_as isSemiformula_isFuncConst_mul_c (fun e he ↦ (hes e he).1), hinst.2]

/-- Row `isFuncConst_cC` as a step. -/
lemma ok_isFuncConst_cC {tbl N E Γ W : V}  (htbl : TableOK tbl N) (hW : WalkTable tbl) (hWp : W = walkPieces)
    (hΓ : IsFormulaSet LAct Γ)   :
    StepOK tbl E ((8 : ℕ) : V) Γ (mkStep W 13 0) ∧ sTag (mkStep W 13 0) = 0 ∧
    ctxAfter Γ (mkStep W 13 0) = insert (neg LAct (isFuncFact (cT 0) (cT 2))) Γ := by
  subst hWp
  have hk : ((rIdx_isFuncConst_cC : ℕ) : V) = (13 : V) := by simp [rIdx_isFuncConst_cC]
  have hstep := mkStep_isFuncConst_cC (V := V) 0
  have hlen := walkTable_len hW rIdx_isFuncConst_cC (by decide)
  have hrow := walkTable_isFuncConst_cC hW
  rw [hk] at hstep hlen hrow
  have hes : ∀ e ∈ ([] : List V), IsSemiterm LAct 0 e ∧ termLen LAct e ≤ E := List.forall_mem_nil _
  have hinst := inst_isFuncConst_cC (V := V)
  rw [hstep]
  refine ⟨stepOK_useHorn htbl ([] : List V) row_isFuncConst_cC_as hΓ hlen hrow.1 hrow.2 (by exact_mod_cast (by decide : 0 ≤ 8))
    (by rw [show row_isFuncConst_cC_as.length = 0 from rfl]; exact_mod_cast (by decide : 0 ≤ 8)) hes ?_, by simp, ?_⟩
  · exact neg_mem_of_map hinst.1 (List.forall_mem_nil _)
  · show ctxAfter Γ (sUseHorn 13 (vecOf ([] : List V)) (vecOf row_isFuncConst_cC_as) row_isFuncConst_cC_c) = _
    rw [ctxAfter_useHorn ([] : List V) row_isFuncConst_cC_as isSemiformula_isFuncConst_cC_c (fun e he ↦ (hes e he).1), hinst.2]

/-- Row `isFuncConst_cD` as a step. -/
lemma ok_isFuncConst_cD {tbl N E Γ W : V}  (htbl : TableOK tbl N) (hW : WalkTable tbl) (hWp : W = walkPieces)
    (hΓ : IsFormulaSet LAct Γ)   :
    StepOK tbl E ((8 : ℕ) : V) Γ (mkStep W 14 0) ∧ sTag (mkStep W 14 0) = 0 ∧
    ctxAfter Γ (mkStep W 14 0) = insert (neg LAct (isFuncFact (cT 0) (cT 3))) Γ := by
  subst hWp
  have hk : ((rIdx_isFuncConst_cD : ℕ) : V) = (14 : V) := by simp [rIdx_isFuncConst_cD]
  have hstep := mkStep_isFuncConst_cD (V := V) 0
  have hlen := walkTable_len hW rIdx_isFuncConst_cD (by decide)
  have hrow := walkTable_isFuncConst_cD hW
  rw [hk] at hstep hlen hrow
  have hes : ∀ e ∈ ([] : List V), IsSemiterm LAct 0 e ∧ termLen LAct e ≤ E := List.forall_mem_nil _
  have hinst := inst_isFuncConst_cD (V := V)
  rw [hstep]
  refine ⟨stepOK_useHorn htbl ([] : List V) row_isFuncConst_cD_as hΓ hlen hrow.1 hrow.2 (by exact_mod_cast (by decide : 0 ≤ 8))
    (by rw [show row_isFuncConst_cD_as.length = 0 from rfl]; exact_mod_cast (by decide : 0 ≤ 8)) hes ?_, by simp, ?_⟩
  · exact neg_mem_of_map hinst.1 (List.forall_mem_nil _)
  · show ctxAfter Γ (sUseHorn 14 (vecOf ([] : List V)) (vecOf row_isFuncConst_cD_as) row_isFuncConst_cD_c) = _
    rw [ctxAfter_useHorn ([] : List V) row_isFuncConst_cD_as isSemiformula_isFuncConst_cD_c (fun e he ↦ (hes e he).1), hinst.2]

/-- Row `isSemitermVecNil` as a step. -/
lemma ok_isSemitermVecNil {tbl N E Γ W : V} {wn : V} (htbl : TableOK tbl N) (hW : WalkTable tbl) (hWp : W = walkPieces)
    (hΓ : IsFormulaSet LAct Γ) (hwn : IsSemiterm LAct 0 wn) (hEwn : termLen LAct wn ≤ E)  :
    StepOK tbl E ((8 : ℕ) : V) Γ (mkStep W 15 ?[wn]) ∧ sTag (mkStep W 15 ?[wn]) = 0 ∧
    ctxAfter Γ (mkStep W 15 ?[wn]) = insert (neg LAct (tvSigmaFact (𝟎 : V) wn (𝟎 : V))) Γ := by
  subst hWp
  have hk : ((rIdx_isSemitermVecNil : ℕ) : V) = (15 : V) := by simp [rIdx_isSemitermVecNil]
  have hstep := mkStep_isSemitermVecNil (V := V) ?[wn]
  have hlen := walkTable_len hW rIdx_isSemitermVecNil (by decide)
  have hrow := walkTable_isSemitermVecNil hW
  rw [hk] at hstep hlen hrow
  have hes : ∀ e ∈ [wn], IsSemiterm LAct 0 e ∧ termLen LAct e ≤ E := List.forall_mem_cons.mpr ⟨⟨hwn, hEwn⟩, List.forall_mem_nil _⟩
  have hinst := inst_isSemitermVecNil hwn
  rw [hstep]
  rw [show (?[wn] : V) = vecOf [wn] from rfl]
  refine ⟨stepOK_useHorn htbl [wn] row_isSemitermVecNil_as hΓ hlen hrow.1 hrow.2 (by exact_mod_cast (by decide : 1 ≤ 8))
    (by rw [show row_isSemitermVecNil_as.length = 0 from rfl]; exact_mod_cast (by decide : 0 ≤ 8)) hes ?_, by simp, ?_⟩
  · exact neg_mem_of_map hinst.1 (List.forall_mem_nil _)
  · rw [ctxAfter_useHorn [wn] row_isSemitermVecNil_as isSemiformula_isSemitermVecNil_c (fun e he ↦ (hes e he).1), hinst.2]

/-- Row `isSemitermVecSigmaPiLAct` as a step. -/
lemma ok_isSemitermVecSigmaPiLAct {tbl N E Γ W : V} {wk : V} {wn : V} {wv : V} (htbl : TableOK tbl N) (hW : WalkTable tbl) (hWp : W = walkPieces)
    (hΓ : IsFormulaSet LAct Γ) (hwk : IsSemiterm LAct 0 wk) (hEwk : termLen LAct wk ≤ E) (hwn : IsSemiterm LAct 0 wn) (hEwn : termLen LAct wn ≤ E) (hwv : IsSemiterm LAct 0 wv) (hEwv : termLen LAct wv ≤ E) (hmem0 : neg LAct (tvSigmaFact wk wn wv) ∈ Γ) :
    StepOK tbl E ((8 : ℕ) : V) Γ (mkStep W 16 ?[wk, wn, wv]) ∧ sTag (mkStep W 16 ?[wk, wn, wv]) = 0 ∧
    ctxAfter Γ (mkStep W 16 ?[wk, wn, wv]) = insert (neg LAct (tvPiFact wk wn wv)) Γ := by
  subst hWp
  have hk : ((rIdx_isSemitermVecSigmaPiLAct : ℕ) : V) = (16 : V) := by simp [rIdx_isSemitermVecSigmaPiLAct]
  have hstep := mkStep_isSemitermVecSigmaPiLAct (V := V) ?[wk, wn, wv]
  have hlen := walkTable_len hW rIdx_isSemitermVecSigmaPiLAct (by decide)
  have hrow := walkTable_isSemitermVecSigmaPiLAct hW
  rw [hk] at hstep hlen hrow
  have hes : ∀ e ∈ [wk, wn, wv], IsSemiterm LAct 0 e ∧ termLen LAct e ≤ E := List.forall_mem_cons.mpr ⟨⟨hwk, hEwk⟩, List.forall_mem_cons.mpr ⟨⟨hwn, hEwn⟩, List.forall_mem_cons.mpr ⟨⟨hwv, hEwv⟩, List.forall_mem_nil _⟩⟩⟩
  have hinst := inst_isSemitermVecSigmaPiLAct hwk hwn hwv
  rw [hstep]
  rw [show (?[wk, wn, wv] : V) = vecOf [wk, wn, wv] from rfl]
  refine ⟨stepOK_useHorn htbl [wk, wn, wv] row_isSemitermVecSigmaPiLAct_as hΓ hlen hrow.1 hrow.2 (by exact_mod_cast (by decide : 3 ≤ 8))
    (by rw [show row_isSemitermVecSigmaPiLAct_as.length = 1 from rfl]; exact_mod_cast (by decide : 1 ≤ 8)) hes ?_, by simp, ?_⟩
  · exact neg_mem_of_map hinst.1 (List.forall_mem_cons.mpr ⟨hmem0, List.forall_mem_nil _⟩)
  · rw [ctxAfter_useHorn [wk, wn, wv] row_isSemitermVecSigmaPiLAct_as isSemiformula_isSemitermVecSigmaPiLAct_c (fun e he ↦ (hes e he).1), hinst.2]

/-- Row `isSemitermVecAdjoin` as a step. -/
lemma ok_isSemitermVecAdjoin {tbl N E Γ W : V} {wk : V} {wn : V} {ww : V} {wt : V} {wu : V} (htbl : TableOK tbl N) (hW : WalkTable tbl) (hWp : W = walkPieces)
    (hΓ : IsFormulaSet LAct Γ) (hwk : IsSemiterm LAct 0 wk) (hEwk : termLen LAct wk ≤ E) (hwn : IsSemiterm LAct 0 wn) (hEwn : termLen LAct wn ≤ E) (hww : IsSemiterm LAct 0 ww) (hEww : termLen LAct ww ≤ E) (hwt : IsSemiterm LAct 0 wt) (hEwt : termLen LAct wt ≤ E) (hwu : IsSemiterm LAct 0 wu) (hEwu : termLen LAct wu ≤ E) (hmem0 : neg LAct (tvPiFact wk wn ww) ∈ Γ) (hmem1 : neg LAct (tPiFact wn wt) ∈ Γ) (hmem2 : neg LAct (adjFact wu wt ww) ∈ Γ) :
    StepOK tbl E ((8 : ℕ) : V) Γ (mkStep W 18 ?[wk, wn, ww, wt, wu]) ∧ sTag (mkStep W 18 ?[wk, wn, ww, wt, wu]) = 0 ∧
    ctxAfter Γ (mkStep W 18 ?[wk, wn, ww, wt, wu]) = insert (neg LAct (tvSigmaFact (wk ^+ (𝟏 : V)) wn wu)) Γ := by
  subst hWp
  have hk : ((rIdx_isSemitermVecAdjoin : ℕ) : V) = (18 : V) := by simp [rIdx_isSemitermVecAdjoin]
  have hstep := mkStep_isSemitermVecAdjoin (V := V) ?[wk, wn, ww, wt, wu]
  have hlen := walkTable_len hW rIdx_isSemitermVecAdjoin (by decide)
  have hrow := walkTable_isSemitermVecAdjoin hW
  rw [hk] at hstep hlen hrow
  have hes : ∀ e ∈ [wk, wn, ww, wt, wu], IsSemiterm LAct 0 e ∧ termLen LAct e ≤ E := List.forall_mem_cons.mpr ⟨⟨hwk, hEwk⟩, List.forall_mem_cons.mpr ⟨⟨hwn, hEwn⟩, List.forall_mem_cons.mpr ⟨⟨hww, hEww⟩, List.forall_mem_cons.mpr ⟨⟨hwt, hEwt⟩, List.forall_mem_cons.mpr ⟨⟨hwu, hEwu⟩, List.forall_mem_nil _⟩⟩⟩⟩⟩
  have hinst := inst_isSemitermVecAdjoin hwk hwn hww hwt hwu
  rw [hstep]
  rw [show (?[wk, wn, ww, wt, wu] : V) = vecOf [wk, wn, ww, wt, wu] from rfl]
  refine ⟨stepOK_useHorn htbl [wk, wn, ww, wt, wu] row_isSemitermVecAdjoin_as hΓ hlen hrow.1 hrow.2 (by exact_mod_cast (by decide : 5 ≤ 8))
    (by rw [show row_isSemitermVecAdjoin_as.length = 3 from rfl]; exact_mod_cast (by decide : 3 ≤ 8)) hes ?_, by simp, ?_⟩
  · exact neg_mem_of_map hinst.1 (List.forall_mem_cons.mpr ⟨hmem0, List.forall_mem_cons.mpr ⟨hmem1, List.forall_mem_cons.mpr ⟨hmem2, List.forall_mem_nil _⟩⟩⟩)
  · rw [ctxAfter_useHorn [wk, wn, ww, wt, wu] row_isSemitermVecAdjoin_as isSemiformula_isSemitermVecAdjoin_c (fun e he ↦ (hes e he).1), hinst.2]

/-- Row `isUTermVecOfSemitermVecLAct` as a step. -/
lemma ok_isUTermVecOfSemitermVecLAct {tbl N E Γ W : V} {wk : V} {wn : V} {wv : V} (htbl : TableOK tbl N) (hW : WalkTable tbl) (hWp : W = walkPieces)
    (hΓ : IsFormulaSet LAct Γ) (hwk : IsSemiterm LAct 0 wk) (hEwk : termLen LAct wk ≤ E) (hwn : IsSemiterm LAct 0 wn) (hEwn : termLen LAct wn ≤ E) (hwv : IsSemiterm LAct 0 wv) (hEwv : termLen LAct wv ≤ E) (hmem0 : neg LAct (tvPiFact wk wn wv) ∈ Γ) :
    StepOK tbl E ((8 : ℕ) : V) Γ (mkStep W 38 ?[wk, wn, wv]) ∧ sTag (mkStep W 38 ?[wk, wn, wv]) = 0 ∧
    ctxAfter Γ (mkStep W 38 ?[wk, wn, wv]) = insert (neg LAct (utvSigmaFact wk wv)) Γ := by
  subst hWp
  have hk : ((rIdx_isUTermVecOfSemitermVecLAct : ℕ) : V) = (38 : V) := by simp [rIdx_isUTermVecOfSemitermVecLAct]
  have hstep := mkStep_isUTermVecOfSemitermVecLAct (V := V) ?[wk, wn, wv]
  have hlen := walkTable_len hW rIdx_isUTermVecOfSemitermVecLAct (by decide)
  have hrow := walkTable_isUTermVecOfSemitermVecLAct hW
  rw [hk] at hstep hlen hrow
  have hes : ∀ e ∈ [wk, wn, wv], IsSemiterm LAct 0 e ∧ termLen LAct e ≤ E := List.forall_mem_cons.mpr ⟨⟨hwk, hEwk⟩, List.forall_mem_cons.mpr ⟨⟨hwn, hEwn⟩, List.forall_mem_cons.mpr ⟨⟨hwv, hEwv⟩, List.forall_mem_nil _⟩⟩⟩
  have hinst := inst_isUTermVecOfSemitermVecLAct hwk hwn hwv
  rw [hstep]
  rw [show (?[wk, wn, wv] : V) = vecOf [wk, wn, wv] from rfl]
  refine ⟨stepOK_useHorn htbl [wk, wn, wv] row_isUTermVecOfSemitermVecLAct_as hΓ hlen hrow.1 hrow.2 (by exact_mod_cast (by decide : 3 ≤ 8))
    (by rw [show row_isUTermVecOfSemitermVecLAct_as.length = 1 from rfl]; exact_mod_cast (by decide : 1 ≤ 8)) hes ?_, by simp, ?_⟩
  · exact neg_mem_of_map hinst.1 (List.forall_mem_cons.mpr ⟨hmem0, List.forall_mem_nil _⟩)
  · rw [ctxAfter_useHorn [wk, wn, wv] row_isUTermVecOfSemitermVecLAct_as isSemiformula_isUTermVecOfSemitermVecLAct_c (fun e he ↦ (hes e he).1), hinst.2]

/-- Row `isUTermVecSigmaPiLAct` as a step. -/
lemma ok_isUTermVecSigmaPiLAct {tbl N E Γ W : V} {wk : V} {wv : V} (htbl : TableOK tbl N) (hW : WalkTable tbl) (hWp : W = walkPieces)
    (hΓ : IsFormulaSet LAct Γ) (hwk : IsSemiterm LAct 0 wk) (hEwk : termLen LAct wk ≤ E) (hwv : IsSemiterm LAct 0 wv) (hEwv : termLen LAct wv ≤ E) (hmem0 : neg LAct (utvSigmaFact wk wv) ∈ Γ) :
    StepOK tbl E ((8 : ℕ) : V) Γ (mkStep W 39 ?[wk, wv]) ∧ sTag (mkStep W 39 ?[wk, wv]) = 0 ∧
    ctxAfter Γ (mkStep W 39 ?[wk, wv]) = insert (neg LAct (utvPiFact wk wv)) Γ := by
  subst hWp
  have hk : ((rIdx_isUTermVecSigmaPiLAct : ℕ) : V) = (39 : V) := by simp [rIdx_isUTermVecSigmaPiLAct]
  have hstep := mkStep_isUTermVecSigmaPiLAct (V := V) ?[wk, wv]
  have hlen := walkTable_len hW rIdx_isUTermVecSigmaPiLAct (by decide)
  have hrow := walkTable_isUTermVecSigmaPiLAct hW
  rw [hk] at hstep hlen hrow
  have hes : ∀ e ∈ [wk, wv], IsSemiterm LAct 0 e ∧ termLen LAct e ≤ E := List.forall_mem_cons.mpr ⟨⟨hwk, hEwk⟩, List.forall_mem_cons.mpr ⟨⟨hwv, hEwv⟩, List.forall_mem_nil _⟩⟩
  have hinst := inst_isUTermVecSigmaPiLAct hwk hwv
  rw [hstep]
  rw [show (?[wk, wv] : V) = vecOf [wk, wv] from rfl]
  refine ⟨stepOK_useHorn htbl [wk, wv] row_isUTermVecSigmaPiLAct_as hΓ hlen hrow.1 hrow.2 (by exact_mod_cast (by decide : 2 ≤ 8))
    (by rw [show row_isUTermVecSigmaPiLAct_as.length = 1 from rfl]; exact_mod_cast (by decide : 1 ≤ 8)) hes ?_, by simp, ?_⟩
  · exact neg_mem_of_map hinst.1 (List.forall_mem_cons.mpr ⟨hmem0, List.forall_mem_nil _⟩)
  · rw [ctxAfter_useHorn [wk, wv] row_isUTermVecSigmaPiLAct_as isSemiformula_isUTermVecSigmaPiLAct_c (fun e he ↦ (hes e he).1), hinst.2]

/-- Totality row `qqBvarTotal` as a step: the new eigenvariable `&0`, the context shifted. -/
lemma ok_qqBvarTotal {tbl N E Γ W : V} {wz : V} (htbl : TableOK tbl N) (hW : WalkTable tbl) (hWp : W = walkPieces)
    (hΓ : IsFormulaSet LAct Γ) (hwz : IsSemiterm LAct 0 wz) (hEwz : termLen LAct wz ≤ E) :
    StepOK tbl E ((8 : ℕ) : V) Γ (mkStep W 2 ?[wz]) ∧ sTag (mkStep W 2 ?[wz]) = 2 ∧
    ctxAfter Γ (mkStep W 2 ?[wz]) = insert (neg LAct (bvarFact (^&((0 : ℕ) : V)) (termShift LAct wz))) (setShift LAct Γ) := by
  subst hWp
  have hk : ((rIdx_qqBvarTotal : ℕ) : V) = (2 : V) := by simp [rIdx_qqBvarTotal]
  have hstep := mkStep_qqBvarTotal (V := V) ?[wz]
  have hlen := walkTable_len hW rIdx_qqBvarTotal (by decide)
  have hrow := walkTable_qqBvarTotal hW
  rw [hk] at hstep hlen hrow
  have hes : ∀ e ∈ [wz], IsSemiterm LAct 0 e ∧ termLen LAct e ≤ E := List.forall_mem_cons.mpr ⟨⟨hwz, hEwz⟩, List.forall_mem_nil _⟩
  have hinst := inst_qqBvarTotal hwz
  rw [hstep, show (?[wz] : V) = vecOf [wz] from rfl]
  refine ⟨stepOK_introFact htbl [wz] row_qqBvarTotal_as hΓ hlen hrow.1 hrow.2 (by exact_mod_cast (by decide : 1 ≤ 8))
    (by rw [show row_qqBvarTotal_as.length = 0 from rfl]; exact_mod_cast (by decide : 0 ≤ 8)) hes ?_, by simp, ?_⟩
  · exact neg_mem_of_map hinst.1 (List.forall_mem_nil _)
  · rw [ctxAfter_introFact [wz] row_qqBvarTotal_as (by rw [← Nat.cast_succ]; exact isSemiformula_qqBvarTotal_R) (fun e he ↦ (hes e he).1),
      show row_qqBvarTotal_R = row_qqBvarTotal_body from rfl, ← freeIter_one, hinst.2]

/-- Totality row `qqFvarTotal` as a step: the new eigenvariable `&0`, the context shifted. -/
lemma ok_qqFvarTotal {tbl N E Γ W : V} {wx : V} (htbl : TableOK tbl N) (hW : WalkTable tbl) (hWp : W = walkPieces)
    (hΓ : IsFormulaSet LAct Γ) (hwx : IsSemiterm LAct 0 wx) (hEwx : termLen LAct wx ≤ E) :
    StepOK tbl E ((8 : ℕ) : V) Γ (mkStep W 5 ?[wx]) ∧ sTag (mkStep W 5 ?[wx]) = 2 ∧
    ctxAfter Γ (mkStep W 5 ?[wx]) = insert (neg LAct (fvarFact (^&((0 : ℕ) : V)) (termShift LAct wx))) (setShift LAct Γ) := by
  subst hWp
  have hk : ((rIdx_qqFvarTotal : ℕ) : V) = (5 : V) := by simp [rIdx_qqFvarTotal]
  have hstep := mkStep_qqFvarTotal (V := V) ?[wx]
  have hlen := walkTable_len hW rIdx_qqFvarTotal (by decide)
  have hrow := walkTable_qqFvarTotal hW
  rw [hk] at hstep hlen hrow
  have hes : ∀ e ∈ [wx], IsSemiterm LAct 0 e ∧ termLen LAct e ≤ E := List.forall_mem_cons.mpr ⟨⟨hwx, hEwx⟩, List.forall_mem_nil _⟩
  have hinst := inst_qqFvarTotal hwx
  rw [hstep, show (?[wx] : V) = vecOf [wx] from rfl]
  refine ⟨stepOK_introFact htbl [wx] row_qqFvarTotal_as hΓ hlen hrow.1 hrow.2 (by exact_mod_cast (by decide : 1 ≤ 8))
    (by rw [show row_qqFvarTotal_as.length = 0 from rfl]; exact_mod_cast (by decide : 0 ≤ 8)) hes ?_, by simp, ?_⟩
  · exact neg_mem_of_map hinst.1 (List.forall_mem_nil _)
  · rw [ctxAfter_introFact [wx] row_qqFvarTotal_as (by rw [← Nat.cast_succ]; exact isSemiformula_qqFvarTotal_R) (fun e he ↦ (hes e he).1),
      show row_qqFvarTotal_R = row_qqFvarTotal_body from rfl, ← freeIter_one, hinst.2]

/-- Totality row `qqFuncTotal` as a step: the new eigenvariable `&0`, the context shifted. -/
lemma ok_qqFuncTotal {tbl N E Γ W : V} {wk : V} {wf : V} {wv : V} (htbl : TableOK tbl N) (hW : WalkTable tbl) (hWp : W = walkPieces)
    (hΓ : IsFormulaSet LAct Γ) (hwk : IsSemiterm LAct 0 wk) (hEwk : termLen LAct wk ≤ E) (hwf : IsSemiterm LAct 0 wf) (hEwf : termLen LAct wf ≤ E) (hwv : IsSemiterm LAct 0 wv) (hEwv : termLen LAct wv ≤ E) :
    StepOK tbl E ((8 : ℕ) : V) Γ (mkStep W 7 ?[wk, wf, wv]) ∧ sTag (mkStep W 7 ?[wk, wf, wv]) = 2 ∧
    ctxAfter Γ (mkStep W 7 ?[wk, wf, wv]) = insert (neg LAct (funcFact (^&((0 : ℕ) : V)) (termShift LAct wk) (termShift LAct wf) (termShift LAct wv))) (setShift LAct Γ) := by
  subst hWp
  have hk : ((rIdx_qqFuncTotal : ℕ) : V) = (7 : V) := by simp [rIdx_qqFuncTotal]
  have hstep := mkStep_qqFuncTotal (V := V) ?[wk, wf, wv]
  have hlen := walkTable_len hW rIdx_qqFuncTotal (by decide)
  have hrow := walkTable_qqFuncTotal hW
  rw [hk] at hstep hlen hrow
  have hes : ∀ e ∈ [wk, wf, wv], IsSemiterm LAct 0 e ∧ termLen LAct e ≤ E := List.forall_mem_cons.mpr ⟨⟨hwk, hEwk⟩, List.forall_mem_cons.mpr ⟨⟨hwf, hEwf⟩, List.forall_mem_cons.mpr ⟨⟨hwv, hEwv⟩, List.forall_mem_nil _⟩⟩⟩
  have hinst := inst_qqFuncTotal hwk hwf hwv
  rw [hstep, show (?[wk, wf, wv] : V) = vecOf [wk, wf, wv] from rfl]
  refine ⟨stepOK_introFact htbl [wk, wf, wv] row_qqFuncTotal_as hΓ hlen hrow.1 hrow.2 (by exact_mod_cast (by decide : 3 ≤ 8))
    (by rw [show row_qqFuncTotal_as.length = 0 from rfl]; exact_mod_cast (by decide : 0 ≤ 8)) hes ?_, by simp, ?_⟩
  · exact neg_mem_of_map hinst.1 (List.forall_mem_nil _)
  · rw [ctxAfter_introFact [wk, wf, wv] row_qqFuncTotal_as (by rw [← Nat.cast_succ]; exact isSemiformula_qqFuncTotal_R) (fun e he ↦ (hes e he).1),
      show row_qqFuncTotal_R = row_qqFuncTotal_body from rfl, ← freeIter_one, hinst.2]

/-- Totality row `adjoinTotal` as a step: the new eigenvariable `&0`, the context shifted. -/
lemma ok_adjoinTotal {tbl N E Γ W : V} {wt : V} {wv : V} (htbl : TableOK tbl N) (hW : WalkTable tbl) (hWp : W = walkPieces)
    (hΓ : IsFormulaSet LAct Γ) (hwt : IsSemiterm LAct 0 wt) (hEwt : termLen LAct wt ≤ E) (hwv : IsSemiterm LAct 0 wv) (hEwv : termLen LAct wv ≤ E) :
    StepOK tbl E ((8 : ℕ) : V) Γ (mkStep W 17 ?[wt, wv]) ∧ sTag (mkStep W 17 ?[wt, wv]) = 2 ∧
    ctxAfter Γ (mkStep W 17 ?[wt, wv]) = insert (neg LAct (adjFact (^&((0 : ℕ) : V)) (termShift LAct wt) (termShift LAct wv))) (setShift LAct Γ) := by
  subst hWp
  have hk : ((rIdx_adjoinTotal : ℕ) : V) = (17 : V) := by simp [rIdx_adjoinTotal]
  have hstep := mkStep_adjoinTotal (V := V) ?[wt, wv]
  have hlen := walkTable_len hW rIdx_adjoinTotal (by decide)
  have hrow := walkTable_adjoinTotal hW
  rw [hk] at hstep hlen hrow
  have hes : ∀ e ∈ [wt, wv], IsSemiterm LAct 0 e ∧ termLen LAct e ≤ E := List.forall_mem_cons.mpr ⟨⟨hwt, hEwt⟩, List.forall_mem_cons.mpr ⟨⟨hwv, hEwv⟩, List.forall_mem_nil _⟩⟩
  have hinst := inst_adjoinTotal hwt hwv
  rw [hstep, show (?[wt, wv] : V) = vecOf [wt, wv] from rfl]
  refine ⟨stepOK_introFact htbl [wt, wv] row_adjoinTotal_as hΓ hlen hrow.1 hrow.2 (by exact_mod_cast (by decide : 2 ≤ 8))
    (by rw [show row_adjoinTotal_as.length = 0 from rfl]; exact_mod_cast (by decide : 0 ≤ 8)) hes ?_, by simp, ?_⟩
  · exact neg_mem_of_map hinst.1 (List.forall_mem_nil _)
  · rw [ctxAfter_introFact [wt, wv] row_adjoinTotal_as (by rw [← Nat.cast_succ]; exact isSemiformula_adjoinTotal_R) (fun e he ↦ (hes e he).1),
      show row_adjoinTotal_R = row_adjoinTotal_body from rfl, ← freeIter_one, hinst.2]


end stepLemmas

/-! ### 3.2 Generic list lemmas, fact-code definability, iterated shifts of facts -/

section factLemmas

lemma concat_eq_appendV (S s : V) : concat S s = appendV S ?[s] := by
  induction S using adjoin_ISigma1.sigma1_succ_induction with
  | hP => definability
  | nil => simp
  | adjoin x S ih => rw [concat_adjoin, appendV_adjoin, ih]

lemma shiftsV_single (s : V) : shiftsV (?[s] : V) = if sTag s = 2 ∨ sTag s = 3 then 1 else 0 := by
  unfold shiftsV
  rw [len_adjoin, len_nil, zero_add]
  have h := shiftsAux_succ (s ∷ (0 : V)) 0
  rw [zero_add] at h
  rw [h, shiftsAux_zero, nth_adjoin_zero]
  split_ifs <;> simp

lemma finalCtx_appendV_single (Γ S s : V) : finalCtx Γ (appendV S ?[s]) = ctxAfter (finalCtx Γ S) s := by
  rw [finalCtx_appendV, finalCtx_single]

lemma cons_eq_appendV_single (s S : V) : s ∷ S = appendV ?[s] S := by simp

lemma listOK_cons {tbl E M Γ s S : V} (h : StepOK tbl E M Γ s) (hS : ListOK tbl E M (ctxAfter Γ s) S) :
    ListOK tbl E M Γ (s ∷ S) := by
  rw [cons_eq_appendV_single]; exact listOK_appendV (listOK_single h) (by rwa [finalCtx_single])

lemma finalCtx_cons (Γ s S : V) : finalCtx Γ (s ∷ S) = finalCtx (ctxAfter Γ s) S := by
  rw [cons_eq_appendV_single, finalCtx_appendV, finalCtx_single]

lemma noDrop_cons {s S : V} (h : sTag s = 0 ∨ sTag s = 1 ∨ sTag s = 2 ∨ sTag s = 3 ∨ sTag s = 4) (hS : NoDrop S) :
    NoDrop (s ∷ S) := by
  rw [cons_eq_appendV_single]; exact noDrop_appendV (noDrop_single h) hS

lemma shiftsV_cons (s S : V) : shiftsV (s ∷ S) = (if sTag s = 2 ∨ sTag s = 3 then 1 else 0) + shiftsV S := by
  rw [cons_eq_appendV_single, shiftsV_appendV, shiftsV_single]

lemma shiftsV_nil : shiftsV (0 : V) = 0 := by simp [shiftsV]

instance tPiFact_definable : 𝚺₁-Function₂ (tPiFact : V → V → V) := by
  have : (tPiFact : V → V → V) = fun a b ↦ subst LAct (a ∷ b ∷ 0) PtPi := rfl
  rw [this]; definability
instance tSigmaFact_definable : 𝚺₁-Function₂ (tSigmaFact : V → V → V) := by
  have : (tSigmaFact : V → V → V) = fun a b ↦ subst LAct (a ∷ b ∷ 0) PtSigma := rfl
  rw [this]; definability
instance tvPiFact_definable : 𝚺₁-Function₃ (tvPiFact : V → V → V → V) := by
  have : (tvPiFact : V → V → V → V) = fun a b c ↦ subst LAct (a ∷ b ∷ c ∷ 0) PtvPi := rfl
  rw [this]; definability
instance tvSigmaFact_definable : 𝚺₁-Function₃ (tvSigmaFact : V → V → V → V) := by
  have : (tvSigmaFact : V → V → V → V) = fun a b c ↦ subst LAct (a ∷ b ∷ c ∷ 0) PtvSigma := rfl
  rw [this]; definability
instance ltFact_definable : 𝚺₁-Function₂ (ltFact : V → V → V) := by
  have : (ltFact : V → V → V) = fun a b ↦ subst LAct (a ∷ b ∷ 0) Plt := rfl
  rw [this]; definability
instance bvarFact_definable : 𝚺₁-Function₂ (bvarFact : V → V → V) := by
  have : (bvarFact : V → V → V) = fun a b ↦ subst LAct (a ∷ b ∷ 0) Pbvar := rfl
  rw [this]; definability
instance fvarFact_definable : 𝚺₁-Function₂ (fvarFact : V → V → V) := by
  have : (fvarFact : V → V → V) = fun a b ↦ subst LAct (a ∷ b ∷ 0) Pfvar := rfl
  rw [this]; definability

lemma termLen_cTV_le {m E : V} (h : 2 * m + 1 ≤ E) : termLen LAct (cTV m) ≤ E := by
  rw [termLen_cTV]; exact h

lemma shiftIterV_tPiFact {a b : V} (ha : IsSemiterm LAct 0 a) (hb : IsSemiterm LAct 0 b) :
    ∀ k, shiftIterV (tPiFact a b) k = tPiFact (termShiftIterV a k) (termShiftIterV b k) := by
  intro k
  induction k using ISigma1.sigma1_succ_induction with
  | hP => definability
  | zero => simp
  | succ k ih =>
    rw [shiftIterV_succ, ih, shift_tPiFact (isSemiterm_termShiftIterV ha k) (isSemiterm_termShiftIterV hb k),
      termShiftIterV_succ, termShiftIterV_succ]

lemma shiftIterV_tvPiFact {a b c : V} (ha : IsSemiterm LAct 0 a) (hb : IsSemiterm LAct 0 b) (hc : IsSemiterm LAct 0 c) :
    ∀ k, shiftIterV (tvPiFact a b c) k = tvPiFact (termShiftIterV a k) (termShiftIterV b k) (termShiftIterV c k) := by
  intro k
  induction k using ISigma1.sigma1_succ_induction with
  | hP => definability
  | zero => simp
  | succ k ih =>
    rw [shiftIterV_succ, ih, shift_tvPiFact (isSemiterm_termShiftIterV ha k) (isSemiterm_termShiftIterV hb k)
      (isSemiterm_termShiftIterV hc k), termShiftIterV_succ, termShiftIterV_succ, termShiftIterV_succ]

lemma shiftIterV_neg {p : V} (hp : IsFormula LAct p) : ∀ k, shiftIterV (neg LAct p) k = neg LAct (shiftIterV p k) := by
  intro k
  induction k using ISigma1.sigma1_succ_induction with
  | hP => definability
  | zero => simp
  | succ k ih => rw [shiftIterV_succ, ih, shift_neg (isFormula_shiftIterV hp k), shiftIterV_succ]

lemma termShiftIterV_vRef (c j : V) : ∀ k, termShiftIterV (vRef c j) k = vRef (c + k) j := by
  intro k
  by_cases hj : j = 0
  · subst hj; rw [vRef_zero, vRef_zero, ← cTV_zero, termShiftIterV_cTV]
  · rw [vRef_of_ne hj, vRef_of_ne hj, termShiftIterV_fvar]

lemma isSemiterm_vRef (c j : V) : IsSemiterm LAct 0 (vRef c j) := by
  by_cases hj : j = 0
  · subst hj; rw [vRef_zero, ← cTV_zero]; exact cTV_semiterm_LAct 0 0
  · rw [vRef_of_ne hj]; simp

lemma termLen_vRef_le {c j E : V} (h : c + 1 ≤ E) : termLen LAct (vRef c j) ≤ E := by
  by_cases hj : j = 0
  · subst hj; rw [vRef_zero, ← cTV_zero, termLen_cTV, mul_zero, zero_add]; exact le_trans le_add_self h
  · rw [vRef_of_ne hj, termLen_fvar]; exact h

end factLemmas

/-! ### 3.3 The `z < n` chain -/

section ltChain

/-- **The `z < n` chain is applicable**: `ltAux W n z j` (`j ≤ z < n`) leaves `j < n - z + j` in
context, shifts nothing, drops nothing. -/
theorem ltAux_ok {tbl N E W n z : V} (htbl : TableOK tbl N) (hW : WalkTable tbl) (hWp : W = walkPieces)
    (hzn : z < n) (hE : 2 * n + 1 ≤ E) :
    ∀ j ≤ z, ∀ Γ, IsFormulaSet LAct Γ →
      ListOK tbl E ((8 : ℕ) : V) Γ (ltAux W n z j) ∧ NoDrop (ltAux W n z j) ∧ shiftsV (ltAux W n z j) = 0 ∧
      Γ ⊆ finalCtx Γ (ltAux W n z j) ∧
      neg LAct (ltFact (cTV j) (cTV (n - z + j))) ∈ finalCtx Γ (ltAux W n z j) := by
  intro j
  induction j using ISigma1.pi1_succ_induction with
  | hP => definability
  | zero =>
    intro _ Γ hΓ
    have hm : n - (z + 1) ≤ n := tsub_le_self
    obtain ⟨hok, htag, hctx⟩ := ok_zeroLtSucc (wy := cTV (n - (z + 1))) htbl hW hWp hΓ (cTV_semiterm_LAct 0 _)
      (termLen_cTV_le (le_trans (add_le_add (mul_le_mul_of_nonneg_left hm zero_le) le_rfl) hE))
    have h1 : n - (z + 1) + 1 = n - z := by
      rw [← tsub_tsub, tsub_add_cancel_of_le (le_tsub_of_add_le_left (lt_iff_succ_le.mp hzn))]
    have hfin : finalCtx Γ (ltAux W n z 0) = insert (neg LAct (ltFact (cTV 0) (cTV (n - z + 0)))) Γ := by
      rw [ltAux_zero, finalCtx_single, hctx, add_zero, cTV_zero, ← cTV_succ, h1]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [ltAux_zero]; exact listOK_single hok
    · rw [ltAux_zero]; exact noDrop_single (Or.inl htag)
    · rw [ltAux_zero, shiftsV_single, if_neg (by rw [htag]; norm_num)]
    · rw [hfin]; exact subset_iff.mpr fun x hx ↦ by simp [hx]
    · rw [hfin]; simp
  | succ j ih =>
    intro hj Γ hΓ
    have hj' : j ≤ z := le_trans le_self_add hj
    obtain ⟨hok, hnd, hsh, hsub, hmem⟩ := ih hj' Γ hΓ
    have hΓ' : IsFormulaSet LAct (finalCtx Γ (ltAux W n z j)) := finalCtx_isFormulaSet 8 htbl hΓ hok
    have hjn : j ≤ n := le_trans hj' (le_of_lt hzn)
    have hjn' : n - z + j ≤ n := by
      calc n - z + j ≤ n - z + z := add_le_add le_rfl hj'
        _ = n := tsub_add_cancel_of_le (le_of_lt hzn)
    obtain ⟨hok₁, htag₁, hctx₁⟩ := ok_succLtSucc (wx := cTV j) (wy := cTV (n - z + j)) htbl hW hWp hΓ'
      (cTV_semiterm_LAct 0 _) (termLen_cTV_le (le_trans (add_le_add (mul_le_mul_of_nonneg_left hjn zero_le) le_rfl) hE))
      (cTV_semiterm_LAct 0 _) (termLen_cTV_le (le_trans (add_le_add (mul_le_mul_of_nonneg_left hjn' zero_le) le_rfl) hE))
      hmem
    have hfin : finalCtx Γ (ltAux W n z (j + 1)) =
        insert (neg LAct (ltFact (cTV (j + 1)) (cTV (n - z + (j + 1))))) (finalCtx Γ (ltAux W n z j)) := by
      rw [ltAux_succ, concat_eq_appendV, finalCtx_appendV_single, hctx₁, ← add_assoc, cTV_succ, cTV_succ]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [ltAux_succ, concat_eq_appendV]; exact listOK_appendV hok (listOK_single hok₁)
    · rw [ltAux_succ, concat_eq_appendV]; exact noDrop_appendV hnd (noDrop_single (Or.inl htag₁))
    · rw [ltAux_succ, concat_eq_appendV, shiftsV_appendV, hsh, shiftsV_single, if_neg (by rw [htag₁]; norm_num)]; simp
    · rw [hfin]; exact subset_iff.mpr fun x hx ↦ by simp [subset_iff.mp hsub x hx]
    · rw [hfin]; simp

theorem ltSteps_ok {tbl N E W n z : V} (htbl : TableOK tbl N) (hW : WalkTable tbl) (hWp : W = walkPieces)
    (hzn : z < n) (hE : 2 * n + 1 ≤ E) (Γ : V) (hΓ : IsFormulaSet LAct Γ) :
    ListOK tbl E ((8 : ℕ) : V) Γ (ltSteps W n z) ∧ NoDrop (ltSteps W n z) ∧ shiftsV (ltSteps W n z) = 0 ∧
      Γ ⊆ finalCtx Γ (ltSteps W n z) ∧ neg LAct (ltFact (cTV z) (cTV n)) ∈ finalCtx Γ (ltSteps W n z) := by
  have := ltAux_ok htbl hW hWp hzn hE z le_rfl Γ hΓ
  rwa [tsub_add_cancel_of_le (le_of_lt hzn)] at this

end ltChain

/-! ### 3.4 The leaf and nil nodes are applicable -/

section nodes

lemma neg_mem_setShift {Γ p : V} (hp : IsFormula LAct p) (h : neg LAct p ∈ Γ) :
    neg LAct (shift LAct p) ∈ setShift LAct Γ := by
  rw [← shift_neg hp]; exact shift_mem_setShift h

lemma one_le_of_E {n E : V} (hE : 2 * n + 8 ≤ E) : (1 : V) ≤ E :=
  le_trans (le_trans (by norm_num) (le_add_self : (8 : V) ≤ 2 * n + 8)) hE

lemma termLen_fvar_le {i E : V} (h : i + 1 ≤ E) : termLen LAct (^&i : V) ≤ E := by
  rw [termLen_fvar]; exact h

/-- **(T#)** the bound-variable node: `z < n`, witness bound `2n + 8 ≤ E`. -/
theorem bvarNode_ok {tbl N E W n z : V} (htbl : TableOK tbl N) (hW : WalkTable tbl) (hWp : W = walkPieces)
    (hzn : z < n) (hE : 2 * n + 8 ≤ E) (Γ : V) (hΓ : IsFormulaSet LAct Γ) :
    ListOK tbl E ((8 : ℕ) : V) Γ (π₂ (bvarNode W n z)) ∧ NoDrop (π₂ (bvarNode W n z)) ∧
    shiftsV (π₂ (bvarNode W n z)) = 1 ∧
    neg LAct (tPiFact (cTV n) (^&0)) ∈ finalCtx Γ (π₂ (bvarNode W n z)) := by
  have hE1 : 2 * n + 1 ≤ E := le_trans (add_le_add le_rfl (by norm_num)) hE
  have hEn : termLen LAct (cTV n) ≤ E := termLen_cTV_le hE1
  have hEz : termLen LAct (cTV z) ≤ E :=
    termLen_cTV_le (le_trans (add_le_add (mul_le_mul_of_nonneg_left (le_of_lt hzn) zero_le) le_rfl) hE1)
  have hE0 : termLen LAct (^&0 : V) ≤ E := termLen_fvar_le (by rw [zero_add]; exact one_le_of_E hE)
  obtain ⟨hok₀, hnd₀, hsh₀, hsub₀, hmem₀⟩ := ltSteps_ok htbl hW hWp hzn hE1 Γ hΓ
  have hΓ₁ : IsFormulaSet LAct (finalCtx Γ (ltSteps W n z)) := finalCtx_isFormulaSet 8 htbl hΓ hok₀
  obtain ⟨hok₁, htag₁, hctx₁⟩ := ok_qqBvarTotal (wz := cTV z) htbl hW hWp hΓ₁ (cTV_semiterm_LAct 0 _) hEz
  rw [Nat.cast_zero, termShift_cTV] at hctx₁
  have hΓ₂ : IsFormulaSet LAct (ctxAfter (finalCtx Γ (ltSteps W n z)) (mkStep W 2 ?[cTV z])) :=
    isFormulaSet_ctxAfter 8 htbl hok₁
  have hlt₂ : neg LAct (ltFact (cTV z) (cTV n)) ∈ ctxAfter (finalCtx Γ (ltSteps W n z)) (mkStep W 2 ?[cTV z]) := by
    rw [hctx₁]
    have := neg_mem_setShift (isFormula_ltFact (cTV_semiterm_LAct 0 _) (cTV_semiterm_LAct 0 _)) hmem₀
    rw [shift_ltFact (cTV_semiterm_LAct 0 _) (cTV_semiterm_LAct 0 _), termShift_cTV, termShift_cTV] at this
    simp [this]
  have hbv₂ : neg LAct (bvarFact (^&0) (cTV z)) ∈ ctxAfter (finalCtx Γ (ltSteps W n z)) (mkStep W 2 ?[cTV z]) := by
    rw [hctx₁]; simp
  obtain ⟨hok₂, htag₂, hctx₂⟩ := ok_isSemitermBvar (wn := cTV n) (wz := cTV z) (wt := ^&0) htbl hW hWp hΓ₂
    (cTV_semiterm_LAct 0 _) hEn (cTV_semiterm_LAct 0 _) hEz (by simp) hE0 hlt₂ hbv₂
  have hΓ₃ : IsFormulaSet LAct (ctxAfter (ctxAfter (finalCtx Γ (ltSteps W n z)) (mkStep W 2 ?[cTV z]))
      (mkStep W 3 ?[cTV n, cTV z, ^&0])) := isFormulaSet_ctxAfter 8 htbl hok₂
  have hsg₃ : neg LAct (tSigmaFact (cTV n) (^&0)) ∈ ctxAfter (ctxAfter (finalCtx Γ (ltSteps W n z)) (mkStep W 2 ?[cTV z]))
      (mkStep W 3 ?[cTV n, cTV z, ^&0]) := by
    rw [hctx₂]; simp
  obtain ⟨hok₃, htag₃, hctx₃⟩ := ok_isSemitermSigmaPiLAct (wn := cTV n) (wt := ^&0) htbl hW hWp hΓ₃
    (cTV_semiterm_LAct 0 _) hEn (by simp) hE0 hsg₃
  have hS : π₂ (bvarNode W n z) = appendV (ltSteps W n z)
      ?[mkStep W 2 ?[cTV z], mkStep W 3 ?[cTV n, cTV z, ^&0], mkStep W 4 ?[cTV n, ^&0]] := by simp [bvarNode]
  rw [hS]
  refine ⟨listOK_appendV hok₀ (listOK_cons hok₁ (listOK_cons hok₂ (listOK_single hok₃))), ?_, ?_, ?_⟩
  · exact noDrop_appendV hnd₀ (noDrop_cons (Or.inr (Or.inr (Or.inl htag₁)))
      (noDrop_cons (Or.inl htag₂) (noDrop_single (Or.inl htag₃))))
  · rw [shiftsV_appendV, hsh₀, shiftsV_cons, shiftsV_cons, shiftsV_single, if_pos (Or.inl htag₁),
      if_neg (by rw [htag₂]; norm_num), if_neg (by rw [htag₃]; norm_num)]
    simp
  · rw [finalCtx_appendV, finalCtx_cons, finalCtx_cons, finalCtx_single, hctx₃]; simp

/-- **(T&)** the free-variable node: witness bound `2n + 2x + 8 ≤ E`. -/
theorem fvarNode_ok {tbl N E W n x : V} (htbl : TableOK tbl N) (hW : WalkTable tbl) (hWp : W = walkPieces)
    (hE : 2 * n + 2 * x + 8 ≤ E) (Γ : V) (hΓ : IsFormulaSet LAct Γ) :
    ListOK tbl E ((8 : ℕ) : V) Γ (π₂ (fvarNode W n x)) ∧ NoDrop (π₂ (fvarNode W n x)) ∧
    shiftsV (π₂ (fvarNode W n x)) = 1 ∧
    neg LAct (tPiFact (cTV n) (^&0)) ∈ finalCtx Γ (π₂ (fvarNode W n x)) := by
  have hE' : 2 * n + 8 ≤ E :=
    le_trans (show 2 * n + 8 ≤ 2 * n + 2 * x + 8 by rw [add_right_comm]; exact le_self_add) hE
  have hEn : termLen LAct (cTV n) ≤ E := termLen_cTV_le (le_trans (add_le_add le_rfl (by norm_num)) hE')
  have hEx : termLen LAct (cTV x) ≤ E :=
    termLen_cTV_le (le_trans (add_le_add (le_add_self : 2 * x ≤ 2 * n + 2 * x) (by norm_num)) hE)
  have hE0 : termLen LAct (^&0 : V) ≤ E := termLen_fvar_le (by rw [zero_add]; exact one_le_of_E hE')
  obtain ⟨hok₁, htag₁, hctx₁⟩ := ok_qqFvarTotal (wx := cTV x) htbl hW hWp hΓ (cTV_semiterm_LAct 0 _) hEx
  rw [Nat.cast_zero, termShift_cTV] at hctx₁
  have hΓ₂ : IsFormulaSet LAct (ctxAfter Γ (mkStep W 5 ?[cTV x])) := isFormulaSet_ctxAfter 8 htbl hok₁
  have hfv₂ : neg LAct (fvarFact (^&0) (cTV x)) ∈ ctxAfter Γ (mkStep W 5 ?[cTV x]) := by rw [hctx₁]; simp
  obtain ⟨hok₂, htag₂, hctx₂⟩ := ok_isSemitermFvar (wn := cTV n) (wx := cTV x) (wt := ^&0) htbl hW hWp hΓ₂
    (cTV_semiterm_LAct 0 _) hEn (cTV_semiterm_LAct 0 _) hEx (by simp) hE0 hfv₂
  have hΓ₃ : IsFormulaSet LAct (ctxAfter (ctxAfter Γ (mkStep W 5 ?[cTV x])) (mkStep W 6 ?[cTV n, cTV x, ^&0])) :=
    isFormulaSet_ctxAfter 8 htbl hok₂
  have hsg₃ : neg LAct (tSigmaFact (cTV n) (^&0)) ∈ ctxAfter (ctxAfter Γ (mkStep W 5 ?[cTV x])) (mkStep W 6 ?[cTV n, cTV x, ^&0]) := by
    rw [hctx₂]; simp
  obtain ⟨hok₃, htag₃, hctx₃⟩ := ok_isSemitermSigmaPiLAct (wn := cTV n) (wt := ^&0) htbl hW hWp hΓ₃
    (cTV_semiterm_LAct 0 _) hEn (by simp) hE0 hsg₃
  have hS : π₂ (fvarNode W n x) =
      ?[mkStep W 5 ?[cTV x], mkStep W 6 ?[cTV n, cTV x, ^&0], mkStep W 4 ?[cTV n, ^&0]] := by simp [fvarNode]
  rw [hS]
  refine ⟨listOK_cons hok₁ (listOK_cons hok₂ (listOK_single hok₃)), ?_, ?_, ?_⟩
  · exact noDrop_cons (Or.inr (Or.inr (Or.inl htag₁))) (noDrop_cons (Or.inl htag₂) (noDrop_single (Or.inl htag₃)))
  · rw [shiftsV_cons, shiftsV_cons, shiftsV_single, if_pos (Or.inl htag₁),
      if_neg (by rw [htag₂]; norm_num), if_neg (by rw [htag₃]; norm_num)]
    simp
  · rw [finalCtx_cons, finalCtx_cons, finalCtx_single, hctx₃]; simp

/-- **(V0)** the empty vector: witness bound `2n + 1 ≤ E`. -/
theorem nilNode_ok {tbl N E W n : V} (htbl : TableOK tbl N) (hW : WalkTable tbl) (hWp : W = walkPieces)
    (hE : 2 * n + 1 ≤ E) (Γ : V) (hΓ : IsFormulaSet LAct Γ) :
    ListOK tbl E ((8 : ℕ) : V) Γ (π₂ (nilNode W n)) ∧ NoDrop (π₂ (nilNode W n)) ∧
    shiftsV (π₂ (nilNode W n)) = 0 ∧
    neg LAct (tvPiFact (cTV 0) (cTV n) (vRef 0 0)) ∈ finalCtx Γ (π₂ (nilNode W n)) := by
  have hEn : termLen LAct (cTV n) ≤ E := termLen_cTV_le hE
  have hE0 : termLen LAct (cTV 0 : V) ≤ E := termLen_cTV_le (le_trans (add_le_add (by simp) le_rfl) hE)
  obtain ⟨hok₁, htag₁, hctx₁⟩ := ok_isSemitermVecNil (wn := cTV n) htbl hW hWp hΓ (cTV_semiterm_LAct 0 _) hEn
  have hΓ₂ : IsFormulaSet LAct (ctxAfter Γ (mkStep W 15 ?[cTV n])) := isFormulaSet_ctxAfter 8 htbl hok₁
  have hsg₂ : neg LAct (tvSigmaFact (cTV 0) (cTV n) (cTV 0)) ∈ ctxAfter Γ (mkStep W 15 ?[cTV n]) := by
    rw [hctx₁, cTV_zero]; simp
  obtain ⟨hok₂, htag₂, hctx₂⟩ := ok_isSemitermVecSigmaPiLAct (wk := cTV 0) (wn := cTV n) (wv := cTV 0) htbl hW hWp hΓ₂
    (cTV_semiterm_LAct 0 _) hE0 (cTV_semiterm_LAct 0 _) hEn (cTV_semiterm_LAct 0 _) hE0 hsg₂
  have hS : π₂ (nilNode W n) = ?[mkStep W 15 ?[cTV n], mkStep W 16 ?[cTV 0, cTV n, cTV 0]] := by simp [nilNode]
  rw [hS]
  refine ⟨listOK_cons hok₁ (listOK_single hok₂), ?_, ?_, ?_⟩
  · exact noDrop_cons (Or.inl htag₁) (noDrop_single (Or.inl htag₂))
  · rw [shiftsV_cons, shiftsV_single, if_neg (by rw [htag₁]; norm_num), if_neg (by rw [htag₂]; norm_num)]; simp
  · rw [finalCtx_cons, finalCtx_single, hctx₂, vRef_zero, ← cTV_zero]; simp

end nodes


/-! ### 3.5 The vector and function nodes are applicable -/

section vecNodes

lemma termShift_vRef (c j : V) : termShift LAct (vRef c j) = vRef (c + 1) j := by
  have h := termShiftIterV_succ (vRef c j) 0
  rw [zero_add, termShiftIterV_zero] at h
  rw [← h]; exact termShiftIterV_vRef c j 1

lemma succ_ne_zero' (j : V) : j + 1 ≠ 0 := ne_of_gt (lt_of_lt_of_le _root_.zero_lt_one le_add_self)

/-- The closed symbol row of `LAct.IsFunc k f`, by the six cases. -/
theorem funcConst_ok {tbl N E W k f Γ : V} (htbl : TableOK tbl N) (hW : WalkTable tbl) (hWp : W = walkPieces)
    (hkf : LAct.IsFunc k f) (hE : 8 ≤ E) (hΓ : IsFormulaSet LAct Γ) :
    StepOK tbl E ((8 : ℕ) : V) Γ (mkStep W (funcRow k f) 0) ∧ sTag (mkStep W (funcRow k f) 0) = 0 ∧
    ctxAfter Γ (mkStep W (funcRow k f) 0) = insert (neg LAct (isFuncFact (cTV k) (cTV f))) Γ ∧
    termLen LAct (cTV k) ≤ E ∧ termLen LAct (cTV f) ≤ E := by
  have h8 : ∀ m : V, m ≤ 3 → termLen LAct (cTV m) ≤ E := fun m hm ↦ by
    rw [termLen_cTV]
    exact le_trans (add_le_add (mul_le_mul_of_nonneg_left hm zero_le) le_rfl) (le_trans (by norm_num) hE)
  rcases isFunc_LAct_iff_V.mp hkf with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [show funcRow (0 : V) 0 = 9 by simp [funcRow]]
    obtain ⟨a, b, c⟩ := ok_isFuncConst_zero htbl hW hWp hΓ
    simp only [cT, Nat.cast_zero] at c
    exact ⟨a, b, c, h8 0 (by norm_num), h8 0 (by norm_num)⟩
  · rw [show funcRow (0 : V) 1 = 10 by simp [funcRow]]
    obtain ⟨a, b, c⟩ := ok_isFuncConst_one htbl hW hWp hΓ
    simp only [cT, Nat.cast_zero, Nat.cast_one] at c
    exact ⟨a, b, c, h8 0 (by norm_num), h8 1 (by norm_num)⟩
  · rw [show funcRow (0 : V) 2 = 13 by simp [funcRow]]
    obtain ⟨a, b, c⟩ := ok_isFuncConst_cC htbl hW hWp hΓ
    simp only [cT, Nat.cast_zero, Nat.cast_ofNat] at c
    exact ⟨a, b, c, h8 0 (by norm_num), h8 2 (by norm_num)⟩
  · rw [show funcRow (0 : V) 3 = 14 by simp [funcRow]]
    obtain ⟨a, b, c⟩ := ok_isFuncConst_cD htbl hW hWp hΓ
    simp only [cT, Nat.cast_zero, Nat.cast_ofNat] at c
    exact ⟨a, b, c, h8 0 (by norm_num), h8 3 le_rfl⟩
  · rw [show funcRow (2 : V) 0 = 11 by simp [funcRow]]
    obtain ⟨a, b, c⟩ := ok_isFuncConst_add htbl hW hWp hΓ
    simp only [cT, Nat.cast_zero, Nat.cast_ofNat] at c
    exact ⟨a, b, c, h8 2 (by norm_num), h8 0 (by norm_num)⟩
  · rw [show funcRow (2 : V) 1 = 12 by simp [funcRow]]
    obtain ⟨a, b, c⟩ := ok_isFuncConst_mul htbl hW hWp hΓ
    simp only [cT, Nat.cast_one, Nat.cast_ofNat] at c
    exact ⟨a, b, c, h8 2 (by norm_num), h8 1 (by norm_num)⟩

/-- What the walk of one term delivers (the induction hypothesis shape). -/
def TermFacts (tbl E W n p : V) : Prop :=
  ∀ Γ, IsFormulaSet LAct Γ →
    ListOK tbl E ((8 : ℕ) : V) Γ (π₂ p) ∧ NoDrop (π₂ p) ∧ shiftsV (π₂ p) = π₁ p ∧
    neg LAct (tPiFact (cTV n) (^&0)) ∈ finalCtx Γ (π₂ p)

/-- What the walk of a vector of length `j` delivers at `Γ`. -/
def VecFacts (tbl E W n j Γ q : V) : Prop :=
  ListOK tbl E ((8 : ℕ) : V) Γ (π₂ q) ∧ NoDrop (π₂ q) ∧ shiftsV (π₂ q) = π₁ q ∧
  neg LAct (tvPiFact (cTV j) (cTV n) (vRef 0 j)) ∈ finalCtx Γ (π₂ q)

/-- **(V∷)** one more entry: from the entry's facts (at every context) and the tail's facts at `Γ`. -/
theorem adjNode_ok {tbl N E W n j p ih Γ : V} (htbl : TableOK tbl N) (hW : WalkTable tbl) (hWp : W = walkPieces)
    (hE : 2 * n + 2 * j + π₁ p + 4 ≤ E) (hp : TermFacts tbl E W n p) (hΓ : IsFormulaSet LAct Γ)
    (hih : VecFacts tbl E W n j Γ ih) : VecFacts tbl E W n (j + 1) Γ (adjNode W n j p ih) := by
  obtain ⟨hok₀, hnd₀, hsh₀, hA₀⟩ := hih
  have hΓ₁ : IsFormulaSet LAct (finalCtx Γ (π₂ ih)) := finalCtx_isFormulaSet 8 htbl hΓ hok₀
  obtain ⟨hokT, hndT, hshT, hT⟩ := hp _ hΓ₁
  have hΓ₂ : IsFormulaSet LAct (finalCtx (finalCtx Γ (π₂ ih)) (π₂ p)) := finalCtx_isFormulaSet 8 htbl hΓ₁ hokT
  -- the tail's fact after the entry's `ct` shifts
  have hA₂ : neg LAct (tvPiFact (cTV j) (cTV n) (vRef (π₁ p) j)) ∈ finalCtx (finalCtx Γ (π₂ ih)) (π₂ p) := by
    have := mem_finalCtx_of_mem hndT hA₀
    rwa [hshT, shiftIterV_neg (isFormula_tvPiFact (cTV_semiterm_LAct 0 _) (cTV_semiterm_LAct 0 _) (isSemiterm_vRef 0 j)),
      shiftIterV_tvPiFact (cTV_semiterm_LAct 0 _) (cTV_semiterm_LAct 0 _) (isSemiterm_vRef 0 j),
      termShiftIterV_cTV, termShiftIterV_cTV, termShiftIterV_vRef, zero_add] at this
  -- witness bounds
  have hE' : (2 * n + 2 * j) + (π₁ p + 4) ≤ E := by rw [← add_assoc]; exact hE
  have hE4 : 4 ≤ E := le_trans (le_trans le_add_self le_add_self) hE'
  have hEn : termLen LAct (cTV n) ≤ E := termLen_cTV_le
    (le_trans (add_le_add le_self_add (le_trans (by norm_num) le_add_self)) hE')
  have hEj : termLen LAct (cTV j) ≤ E := termLen_cTV_le
    (le_trans (add_le_add le_add_self (le_trans (by norm_num) le_add_self)) hE')
  have hEj' : termLen LAct (cTV (j + 1)) ≤ E := termLen_cTV_le (by
    calc 2 * (j + 1) + 1 = 2 * j + 3 := by ring
      _ ≤ (2 * n + 2 * j) + (π₁ p + 4) := add_le_add le_add_self (le_trans (by norm_num) le_add_self)
      _ ≤ E := hE')
  have hEr : termLen LAct (vRef (π₁ p) j) ≤ E := termLen_vRef_le
    (le_trans (le_trans (add_le_add le_rfl (by norm_num)) le_add_self) hE')
  have hEr' : termLen LAct (vRef (π₁ p + 1) j) ≤ E := termLen_vRef_le (by
    calc π₁ p + 1 + 1 = π₁ p + 2 := by ring
      _ ≤ (2 * n + 2 * j) + (π₁ p + 4) := le_trans (add_le_add le_rfl (by norm_num)) le_add_self
      _ ≤ E := hE')
  have hE0 : termLen LAct (^&0 : V) ≤ E := termLen_fvar_le (by rw [zero_add]; exact le_trans (by norm_num) hE4)
  have hE1 : termLen LAct (^&1 : V) ≤ E := termLen_fvar_le (le_trans (by norm_num) hE4)
  -- step 1: adjoinTotal [&0, ⟨v'⟩]
  obtain ⟨hok₁, htag₁, hctx₁⟩ := ok_adjoinTotal (wt := ^&0) (wv := vRef (π₁ p) j) htbl hW hWp hΓ₂ (by simp) hE0
    (isSemiterm_vRef _ _) hEr
  rw [Nat.cast_zero, termShift_fvar, zero_add, termShift_vRef] at hctx₁
  set Γ₂ := finalCtx (finalCtx Γ (π₂ ih)) (π₂ p) with hΓ₂def
  set s₁ := mkStep W 17 ?[^&0, vRef (π₁ p) j] with hs₁
  have hΓ₃ : IsFormulaSet LAct (ctxAfter Γ₂ s₁) := isFormulaSet_ctxAfter 8 htbl hok₁
  have hT₃ : neg LAct (tPiFact (cTV n) (^&1)) ∈ ctxAfter Γ₂ s₁ := by
    rw [hctx₁]
    have := neg_mem_setShift (isFormula_tPiFact (cTV_semiterm_LAct 0 _) (by simp)) hT
    rw [shift_tPiFact (cTV_semiterm_LAct 0 _) (by simp), termShift_cTV, termShift_fvar, zero_add] at this
    simp [this]
  have hA₃ : neg LAct (tvPiFact (cTV j) (cTV n) (vRef (π₁ p + 1) j)) ∈ ctxAfter Γ₂ s₁ := by
    rw [hctx₁]
    have := neg_mem_setShift (isFormula_tvPiFact (cTV_semiterm_LAct 0 _) (cTV_semiterm_LAct 0 _) (isSemiterm_vRef _ _)) hA₂
    rw [shift_tvPiFact (cTV_semiterm_LAct 0 _) (cTV_semiterm_LAct 0 _) (isSemiterm_vRef _ _), termShift_cTV, termShift_cTV,
      termShift_vRef] at this
    simp [this]
  have hJ₃ : neg LAct (adjFact (^&0) (^&1) (vRef (π₁ p + 1) j)) ∈ ctxAfter Γ₂ s₁ := by rw [hctx₁]; simp
  -- step 2: isSemitermVecAdjoin [cTV j, cTV n, ⟨v'⟩', &1, &0]
  obtain ⟨hok₂, htag₂, hctx₂⟩ := ok_isSemitermVecAdjoin (wk := cTV j) (wn := cTV n) (ww := vRef (π₁ p + 1) j)
    (wt := ^&1) (wu := ^&0) htbl hW hWp hΓ₃ (cTV_semiterm_LAct 0 _) hEj (cTV_semiterm_LAct 0 _) hEn
    (isSemiterm_vRef _ _) hEr' (by simp) hE1 (by simp) hE0 hA₃ hT₃ hJ₃
  set s₂ := mkStep W 18 ?[cTV j, cTV n, vRef (π₁ p + 1) j, ^&1, ^&0] with hs₂
  have hΓ₄ : IsFormulaSet LAct (ctxAfter (ctxAfter Γ₂ s₁) s₂) := isFormulaSet_ctxAfter 8 htbl hok₂
  have hS₄ : neg LAct (tvSigmaFact (cTV (j + 1)) (cTV n) (^&0)) ∈ ctxAfter (ctxAfter Γ₂ s₁) s₂ := by
    rw [hctx₂, cTV_succ]; simp
  -- step 3: the bridge [cTV (j+1), cTV n, &0]
  obtain ⟨hok₃, htag₃, hctx₃⟩ := ok_isSemitermVecSigmaPiLAct (wk := cTV (j + 1)) (wn := cTV n) (wv := ^&0) htbl hW hWp hΓ₄
    (cTV_semiterm_LAct 0 _) hEj' (cTV_semiterm_LAct 0 _) hEn (by simp) hE0 hS₄
  set s₃ := mkStep W 16 ?[cTV (j + 1), cTV n, ^&0] with hs₃
  have hS : π₂ (adjNode W n j p ih) = appendV (π₂ ih) (appendV (π₂ p) ?[s₁, s₂, s₃]) := by
    rw [adjNode, pi₂_pair]
  have hC : π₁ (adjNode W n j p ih) = π₁ ih + π₁ p + 1 := by rw [adjNode, pi₁_pair]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hS]
    exact listOK_appendV hok₀ (listOK_appendV hokT (listOK_cons hok₁ (listOK_cons hok₂ (listOK_single hok₃))))
  · rw [hS]
    exact noDrop_appendV hnd₀ (noDrop_appendV hndT (noDrop_cons (Or.inr (Or.inr (Or.inl htag₁)))
      (noDrop_cons (Or.inl htag₂) (noDrop_single (Or.inl htag₃)))))
  · rw [hS, hC, shiftsV_appendV, shiftsV_appendV, hsh₀, hshT, shiftsV_cons, shiftsV_cons, shiftsV_single,
      if_pos (Or.inl htag₁), if_neg (by rw [htag₂]; norm_num), if_neg (by rw [htag₃]; norm_num)]
    ring
  · rw [hS, finalCtx_appendV, finalCtx_appendV, finalCtx_cons, finalCtx_cons, finalCtx_single, hctx₃,
      vRef_of_ne (succ_ne_zero' j)]
    simp

/-- **(Tf)** the function node after its vector: witness bound `2n + 8 ≤ E`. -/
theorem funcNode_ok {tbl N E W n k f d Γ : V} (htbl : TableOK tbl N) (hW : WalkTable tbl) (hWp : W = walkPieces)
    (hkf : LAct.IsFunc k f) (hE : 2 * n + 8 ≤ E) (hΓ : IsFormulaSet LAct Γ) (hd : VecFacts tbl E W n k Γ d) :
    ListOK tbl E ((8 : ℕ) : V) Γ (π₂ (funcNode W n k f d)) ∧ NoDrop (π₂ (funcNode W n k f d)) ∧
    shiftsV (π₂ (funcNode W n k f d)) = π₁ d + 1 ∧
    neg LAct (tPiFact (cTV n) (^&0)) ∈ finalCtx Γ (π₂ (funcNode W n k f d)) := by
  obtain ⟨hok₀, hnd₀, hsh₀, hA₀⟩ := hd
  have hE8 : 8 ≤ E := le_trans le_add_self hE
  have hEn : termLen LAct (cTV n) ≤ E := termLen_cTV_le (le_trans (add_le_add le_rfl (by norm_num)) hE)
  have hE0 : termLen LAct (^&0 : V) ≤ E := termLen_fvar_le (by rw [zero_add]; exact le_trans (by norm_num) hE8)
  have hEr0 : termLen LAct (vRef 0 k) ≤ E := termLen_vRef_le (by rw [zero_add]; exact le_trans (by norm_num) hE8)
  have hEr1 : termLen LAct (vRef 1 k) ≤ E := termLen_vRef_le (le_trans (by norm_num) hE8)
  set Γ₀ := finalCtx Γ (π₂ d) with hΓ₀def
  have hΓ₀ : IsFormulaSet LAct Γ₀ := finalCtx_isFormulaSet 8 htbl hΓ hok₀
  -- step 1: the closed symbol row
  obtain ⟨hok₁, htag₁, hctx₁, hEk, hEf⟩ := funcConst_ok htbl hW hWp hkf hE8 hΓ₀
  set s₁ := mkStep W (funcRow k f) 0 with hs₁
  have hΓ₁ : IsFormulaSet LAct (ctxAfter Γ₀ s₁) := isFormulaSet_ctxAfter 8 htbl hok₁
  have hF₁ : neg LAct (isFuncFact (cTV k) (cTV f)) ∈ ctxAfter Γ₀ s₁ := by rw [hctx₁]; simp
  have hA₁ : neg LAct (tvPiFact (cTV k) (cTV n) (vRef 0 k)) ∈ ctxAfter Γ₀ s₁ := by rw [hctx₁]; simp [hA₀]
  -- step 2: qqFuncTotal [cTV k, cTV f, ⟨v⟩]
  obtain ⟨hok₂, htag₂, hctx₂⟩ := ok_qqFuncTotal (wk := cTV k) (wf := cTV f) (wv := vRef 0 k) htbl hW hWp hΓ₁
    (cTV_semiterm_LAct 0 _) hEk (cTV_semiterm_LAct 0 _) hEf (isSemiterm_vRef _ _) hEr0
  rw [Nat.cast_zero, termShift_cTV, termShift_cTV, termShift_vRef, zero_add] at hctx₂
  set s₂ := mkStep W 7 ?[cTV k, cTV f, vRef 0 k] with hs₂
  have hΓ₂ : IsFormulaSet LAct (ctxAfter (ctxAfter Γ₀ s₁) s₂) := isFormulaSet_ctxAfter 8 htbl hok₂
  have hF₂ : neg LAct (isFuncFact (cTV k) (cTV f)) ∈ ctxAfter (ctxAfter Γ₀ s₁) s₂ := by
    rw [hctx₂]
    have := neg_mem_setShift (isFormula_isFuncFact (cTV_semiterm_LAct 0 _) (cTV_semiterm_LAct 0 _)) hF₁
    rw [shift_isFuncFact (cTV_semiterm_LAct 0 _) (cTV_semiterm_LAct 0 _), termShift_cTV, termShift_cTV] at this
    simp [this]
  have hA₂ : neg LAct (tvPiFact (cTV k) (cTV n) (vRef 1 k)) ∈ ctxAfter (ctxAfter Γ₀ s₁) s₂ := by
    rw [hctx₂]
    have := neg_mem_setShift (isFormula_tvPiFact (cTV_semiterm_LAct 0 _) (cTV_semiterm_LAct 0 _) (isSemiterm_vRef _ _)) hA₁
    rw [shift_tvPiFact (cTV_semiterm_LAct 0 _) (cTV_semiterm_LAct 0 _) (isSemiterm_vRef _ _), termShift_cTV, termShift_cTV,
      termShift_vRef, zero_add] at this
    simp [this]
  have hG₂ : neg LAct (funcFact (^&0) (cTV k) (cTV f) (vRef 1 k)) ∈ ctxAfter (ctxAfter Γ₀ s₁) s₂ := by
    rw [hctx₂]; simp
  -- step 3: isSemitermFunc [cTV n, cTV k, cTV f, ⟨v⟩', &0]
  obtain ⟨hok₃, htag₃, hctx₃⟩ := ok_isSemitermFunc (wn := cTV n) (wk := cTV k) (wf := cTV f) (wv := vRef 1 k) (wt := ^&0)
    htbl hW hWp hΓ₂ (cTV_semiterm_LAct 0 _) hEn (cTV_semiterm_LAct 0 _) hEk (cTV_semiterm_LAct 0 _) hEf
    (isSemiterm_vRef _ _) hEr1 (by simp) hE0 hF₂ hA₂ hG₂
  set s₃ := mkStep W 8 ?[cTV n, cTV k, cTV f, vRef 1 k, ^&0] with hs₃
  have hΓ₃ : IsFormulaSet LAct (ctxAfter (ctxAfter (ctxAfter Γ₀ s₁) s₂) s₃) := isFormulaSet_ctxAfter 8 htbl hok₃
  have hS₃ : neg LAct (tSigmaFact (cTV n) (^&0)) ∈ ctxAfter (ctxAfter (ctxAfter Γ₀ s₁) s₂) s₃ := by rw [hctx₃]; simp
  have hA₃ : neg LAct (tvPiFact (cTV k) (cTV n) (vRef 1 k)) ∈ ctxAfter (ctxAfter (ctxAfter Γ₀ s₁) s₂) s₃ := by
    rw [hctx₃]; simp [hA₂]
  -- step 4: the bridge
  obtain ⟨hok₄, htag₄, hctx₄⟩ := ok_isSemitermSigmaPiLAct (wn := cTV n) (wt := ^&0) htbl hW hWp hΓ₃
    (cTV_semiterm_LAct 0 _) hEn (by simp) hE0 hS₃
  set s₄ := mkStep W 4 ?[cTV n, ^&0] with hs₄
  have hΓ₄ : IsFormulaSet LAct (ctxAfter (ctxAfter (ctxAfter (ctxAfter Γ₀ s₁) s₂) s₃) s₄) :=
    isFormulaSet_ctxAfter 8 htbl hok₄
  have hP₄ : neg LAct (tPiFact (cTV n) (^&0)) ∈ ctxAfter (ctxAfter (ctxAfter (ctxAfter Γ₀ s₁) s₂) s₃) s₄ := by
    rw [hctx₄]; simp
  have hA₄ : neg LAct (tvPiFact (cTV k) (cTV n) (vRef 1 k)) ∈ ctxAfter (ctxAfter (ctxAfter (ctxAfter Γ₀ s₁) s₂) s₃) s₄ := by
    rw [hctx₄]; simp [hA₃]
  -- step 5: isUTermVecOfSemitermVecLAct [cTV k, cTV n, ⟨v⟩']
  obtain ⟨hok₅, htag₅, hctx₅⟩ := ok_isUTermVecOfSemitermVecLAct (wk := cTV k) (wn := cTV n) (wv := vRef 1 k) htbl hW hWp hΓ₄
    (cTV_semiterm_LAct 0 _) hEk (cTV_semiterm_LAct 0 _) hEn (isSemiterm_vRef _ _) hEr1 hA₄
  set s₅ := mkStep W 38 ?[cTV k, cTV n, vRef 1 k] with hs₅
  have hΓ₅ : IsFormulaSet LAct (ctxAfter (ctxAfter (ctxAfter (ctxAfter (ctxAfter Γ₀ s₁) s₂) s₃) s₄) s₅) :=
    isFormulaSet_ctxAfter 8 htbl hok₅
  have hU₅ : neg LAct (utvSigmaFact (cTV k) (vRef 1 k)) ∈
      ctxAfter (ctxAfter (ctxAfter (ctxAfter (ctxAfter Γ₀ s₁) s₂) s₃) s₄) s₅ := by rw [hctx₅]; simp
  have hP₅ : neg LAct (tPiFact (cTV n) (^&0)) ∈
      ctxAfter (ctxAfter (ctxAfter (ctxAfter (ctxAfter Γ₀ s₁) s₂) s₃) s₄) s₅ := by rw [hctx₅]; simp [hP₄]
  -- step 6: its bridge
  obtain ⟨hok₆, htag₆, hctx₆⟩ := ok_isUTermVecSigmaPiLAct (wk := cTV k) (wv := vRef 1 k) htbl hW hWp hΓ₅
    (cTV_semiterm_LAct 0 _) hEk (isSemiterm_vRef _ _) hEr1 hU₅
  set s₆ := mkStep W 39 ?[cTV k, vRef 1 k] with hs₆
  have hS : π₂ (funcNode W n k f d) = appendV (π₂ d) ?[s₁, s₂, s₃, s₄, s₅, s₆] := by rw [funcNode, pi₂_pair]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hS]
    exact listOK_appendV hok₀ (listOK_cons hok₁ (listOK_cons hok₂ (listOK_cons hok₃ (listOK_cons hok₄
      (listOK_cons hok₅ (listOK_single hok₆))))))
  · rw [hS]
    exact noDrop_appendV hnd₀ (noDrop_cons (Or.inl htag₁) (noDrop_cons (Or.inr (Or.inr (Or.inl htag₂)))
      (noDrop_cons (Or.inl htag₃) (noDrop_cons (Or.inl htag₄) (noDrop_cons (Or.inl htag₅)
      (noDrop_single (Or.inl htag₆)))))))
  · rw [hS, shiftsV_appendV, hsh₀, shiftsV_cons, shiftsV_cons, shiftsV_cons, shiftsV_cons, shiftsV_cons, shiftsV_single,
      if_neg (by rw [htag₁]; norm_num), if_pos (Or.inl htag₂), if_neg (by rw [htag₃]; norm_num),
      if_neg (by rw [htag₄]; norm_num), if_neg (by rw [htag₅]; norm_num), if_neg (by rw [htag₆]; norm_num)]
    ring
  · rw [hS, finalCtx_appendV, finalCtx_cons, finalCtx_cons, finalCtx_cons, finalCtx_cons, finalCtx_cons,
      finalCtx_single, hctx₆]
    simp [hP₅]

end vecNodes

/-! ### 3.6 The vector walk and the term walk (D3 for terms) -/

section termWalkOK

lemma nth_le_listSum : ∀ (a : V) (i : V), i < len a → a.[i] ≤ listSum a := by
  intro a
  induction a using adjoin_ISigma1.pi1_succ_induction with
  | hP => definability
  | nil => intro i hi; simp at hi
  | adjoin x a ih =>
    intro i hi
    rcases zero_or_succ i with rfl | ⟨i, rfl⟩
    · rw [nth_adjoin_zero, listSum_adjoin]; exact le_self_add
    · rw [nth_adjoin_succ, listSum_adjoin]
      exact le_trans (ih i (by rw [len_adjoin] at hi; exact lt_of_add_lt_add_right hi)) le_add_self

lemma arity_le_two {k f : V} (hkf : LAct.IsFunc k f) : k ≤ 2 := by
  rcases isFunc_LAct_iff_V.mp hkf with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> norm_num

/-- **The invariant of the term walk** at `(n, t)`: for every witness bound `E ≥ 2n + 2|t| + 8`,
the walk's facts at every context, and the count bound `descCountT + 1 ≤ 2|t|`. -/
def TermOK (tbl W n t : V) : Prop :=
  ∀ E, 2 * n + 2 * termLen LAct t + 8 ≤ E →
    TermFacts tbl E W n (descT W n t) ∧ descCountT W n t + 1 ≤ 2 * termLen LAct t

instance termFacts_definable : 𝚷₁-Relation₅ (TermFacts : V → V → V → V → V → Prop) := by
  unfold TermFacts; definability

instance termOK_definable : 𝚷₁-Relation₄ (TermOK : V → V → V → V → Prop) := by
  unfold TermOK TermFacts descCountT; definability

/-- **The vector walk is applicable**, tail first: after the last `j` entries of a vector of length
`k ≤ 2` whose entries satisfy the invariant. -/
theorem descVecAux_ok {tbl N W n k v : V} (htbl : TableOK tbl N) (hW : WalkTable tbl) (hWp : W = walkPieces)
    (hk : k ≤ 2) (hv : IsSemitermVec LAct k n v) (ih : ∀ i < k, TermOK tbl W n v.[i])
    {E : V} (hE : 2 * n + 2 * listSum (termLenVec LAct k v) + 8 ≤ E) :
    ∀ j ≤ k, IsUTermVec LAct j (takeLast v j) ∧
      π₁ (descVecAux W n (descTVec W n k v) j) ≤ 2 * listSum (termLenVec LAct j (takeLast v j)) ∧
      ∀ Γ, IsFormulaSet LAct Γ → VecFacts tbl E W n j Γ (descVecAux W n (descTVec W n k v) j) := by
  intro j
  induction j using ISigma1.pi1_succ_induction with
  | hP => unfold VecFacts; definability
  | zero =>
    intro _
    refine ⟨by simp, by simp [nilNode], fun Γ hΓ ↦ ?_⟩
    rw [descVecAux_zero]
    obtain ⟨a, b, c, d⟩ := nilNode_ok htbl hW hWp (E := E)
      (le_trans (add_le_add le_self_add (by norm_num)) hE) Γ hΓ
    exact ⟨a, b, by rw [c]; simp [nilNode], d⟩
  | succ j ihj =>
    intro hj
    obtain ⟨hU, hcv, hF⟩ := ihj (le_trans le_self_add hj)
    have hvlen : len v = k := hv.lh
    have hjk : j < len v := by rw [hvlen]; exact lt_of_lt_of_le (lt_add_one j) hj
    have hk0 : (0 : V) < k := lt_of_lt_of_le (lt_of_lt_of_le _root_.zero_lt_one le_add_self) hj
    have hi : k - (j + 1) < k := tsub_lt_self hk0 (lt_of_lt_of_le _root_.zero_lt_one le_add_self)
    have ht : IsSemiterm LAct n v.[k - (j + 1)] := hv.nth hi
    have hnth : nthFromEnd (descTVec W n k v) j = descT W n v.[k - (j + 1)] := by
      rw [nthFromEnd_eq (a := k - (j + 1)) (by rw [len_descTVec W n hv.isUTerm, tsub_add_cancel_of_le hj]),
        nth_descTVec W n hv.isUTerm hi]
    have hl : termLen LAct v.[k - (j + 1)] ≤ listSum (termLenVec LAct k v) := by
      rw [← nth_termLenVec hv.isUTerm hi]
      exact nth_le_listSum _ _ (by rw [len_termLenVec hv.isUTerm]; exact hi)
    have hE' : 2 * n + 2 * termLen LAct v.[k - (j + 1)] + 8 ≤ E :=
      le_trans (add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_left hl zero_le)) le_rfl) hE
    obtain ⟨hTF, hcnt⟩ := ih _ hi E hE'
    have hj1 : j ≤ 1 := by
      have := le_trans hj hk
      rw [show (2 : V) = 1 + 1 from one_add_one_eq_two.symm] at this
      exact (add_le_add_iff_right 1).mp this
    have hEadj : 2 * n + 2 * j + π₁ (descT W n v.[k - (j + 1)]) + 4 ≤ E := by
      have hct : π₁ (descT W n v.[k - (j + 1)]) + 1 ≤ 2 * termLen LAct v.[k - (j + 1)] := hcnt
      calc 2 * n + 2 * j + π₁ (descT W n v.[k - (j + 1)]) + 4
          ≤ 2 * n + 2 * 1 + π₁ (descT W n v.[k - (j + 1)]) + 4 :=
            add_le_add (add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_left hj1 zero_le)) le_rfl) le_rfl
        _ = 2 * n + (π₁ (descT W n v.[k - (j + 1)]) + 1) + 5 := by ring
        _ ≤ 2 * n + 2 * termLen LAct v.[k - (j + 1)] + 5 := add_le_add (add_le_add le_rfl hct) le_rfl
        _ ≤ 2 * n + 2 * termLen LAct v.[k - (j + 1)] + 8 := add_le_add le_rfl (by norm_num)
        _ ≤ E := hE'
    have htake : takeLast v (j + 1) = v.[k - (j + 1)] ∷ takeLast v j := by
      rw [takeLast_succ_of_lt hjk, hvlen]
    refine ⟨?_, ?_, fun Γ hΓ ↦ ?_⟩
    · rw [htake]; exact hU.adjoin ht.isUTerm
    · rw [descVecAux_succ, hnth, htake, termLenVec_cons ht.isUTerm hU, listSum_adjoin, mul_add]
      have hC : π₁ (adjNode W n j (descT W n v.[k - (j + 1)]) (descVecAux W n (descTVec W n k v) j)) =
          π₁ (descVecAux W n (descTVec W n k v) j) + π₁ (descT W n v.[k - (j + 1)]) + 1 := by simp [adjNode]
      rw [hC, add_assoc, add_comm (2 * termLen LAct v.[k - (j + 1)])]
      exact add_le_add hcv hcnt
    · rw [descVecAux_succ, hnth]
      exact adjNode_ok htbl hW hWp hEadj hTF hΓ (hF Γ hΓ)

/-- **D3 for terms — the invariant holds for every semiterm.** -/
theorem termOK_of_isSemiterm {tbl N W : V} (htbl : TableOK tbl N) (hW : WalkTable tbl) (hWp : W = walkPieces)
    (n : V) : ∀ t, IsSemiterm LAct n t → TermOK tbl W n t := by
  intro t ht
  refine IsSemiterm.induction 𝚷 ?_ ?_ ?_ ?_ t ht
  · definability
  · intro z hz E hE
    have hE' : 2 * n + 8 ≤ E := le_trans (add_le_add le_self_add le_rfl) hE
    refine ⟨?_, ?_⟩
    · intro Γ hΓ
      rw [descT_bvar]
      obtain ⟨a, b, c, d⟩ := bvarNode_ok htbl hW hWp hz hE' Γ hΓ
      exact ⟨a, b, by rw [c]; simp [bvarNode], d⟩
    · rw [descCountT_bvar, termLen_bvar, mul_add, mul_one, one_add_one_eq_two]; exact le_add_self
  · intro x E hE
    have hE' : 2 * n + 2 * x + 8 ≤ E := by
      refine le_trans ?_ hE
      rw [termLen_fvar]
      exact add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_left le_self_add zero_le)) le_rfl
    refine ⟨?_, ?_⟩
    · intro Γ hΓ
      rw [descT_fvar]
      obtain ⟨a, b, c, d⟩ := fvarNode_ok htbl hW hWp hE' Γ hΓ
      exact ⟨a, b, by rw [c]; simp [fvarNode], d⟩
    · rw [descCountT_fvar, termLen_fvar, mul_add, mul_one, one_add_one_eq_two]; exact le_add_self
  · intro k f v hkf hv ih E hE
    have hk := arity_le_two hkf
    have hlen : termLen LAct (^func k f v) = listSum (termLenVec LAct k v) + 1 := termLen_func hkf hv.isUTerm
    have hES : 2 * n + 2 * listSum (termLenVec LAct k v) + 8 ≤ E := by
      refine le_trans ?_ hE
      rw [hlen]
      exact add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_left le_self_add zero_le)) le_rfl
    have hE' : 2 * n + 8 ≤ E := le_trans (add_le_add le_self_add le_rfl) hES
    obtain ⟨_, hcnt, hF⟩ := descVecAux_ok htbl hW hWp hk hv ih hES k le_rfl
    have htl : takeLast v k = v := by rw [← hv.lh]; exact takeLast_len_self v
    rw [htl] at hcnt
    refine ⟨?_, ?_⟩
    · intro Γ hΓ
      rw [descT_func W n hkf hv.isUTerm]
      obtain ⟨a, b, c, d⟩ := funcNode_ok htbl hW hWp hkf hE' hΓ (hF Γ hΓ)
      exact ⟨a, b, by rw [c]; simp [funcNode], d⟩
    · rw [descCountT_func W n hkf hv.isUTerm, hlen, mul_add, mul_one, add_assoc, one_add_one_eq_two]
      exact add_le_add hcnt le_rfl

/-- **D3 for terms, unpacked**: the term walk from any formula-set context is applicable step by
step, drops nothing, introduces `descCountT` eigenvariables (`≤ 2|t| − 1`), and leaves
`(isSemiterm LAct).pi n &0` in the final context. -/
theorem describeT_ok {tbl N : V} (htbl : TableOK tbl N) (hW : WalkTable tbl) {n t : V} (ht : IsSemiterm LAct n t)
    {E : V} (hE : 2 * n + 2 * termLen LAct t + 8 ≤ E) {Γ : V} (hΓ : IsFormulaSet LAct Γ) :
    ListOK tbl E ((8 : ℕ) : V) Γ (describeT walkPieces n t) ∧ NoDrop (describeT walkPieces n t) ∧
    shiftsV (describeT walkPieces n t) = descCountT walkPieces n t ∧
    descCountT walkPieces n t + 1 ≤ 2 * termLen LAct t ∧
    neg LAct (tPiFact (cTV n) (^&0)) ∈ finalCtx Γ (describeT walkPieces n t) := by
  obtain ⟨hTF, hcnt⟩ := termOK_of_isSemiterm htbl hW rfl n t ht E hE
  obtain ⟨a, b, c, d⟩ := hTF Γ hΓ
  exact ⟨a, b, c, hcnt, d⟩

/-- **The term walk as a derivation**: with a continuation `d` deriving the final context, the
chain derives `Γ`. -/
theorem describeT_chain {tbl N : V} (htbl : TableOK tbl N) (hW : WalkTable tbl) {n t : V} (ht : IsSemiterm LAct n t)
    {E : V} (hE : 2 * n + 2 * termLen LAct t + 8 ≤ E) {Γ : V} (hΓ : IsFormulaSet LAct Γ) {d : V}
    (hd : DerivationOf TAct d (finalCtx Γ (describeT walkPieces n t))) :
    DerivationOf TAct (chainCode tbl Γ (describeT walkPieces n t) d) Γ :=
  chainCode_proof 8 htbl (describeT_ok htbl hW ht hE hΓ).1 hd

end termWalkOK


/-! ## Part 4 — the formula walk (D2 for formulas)

DESIGN §4.1–4.2: a `Fixpoint` on triples `⟪n, r, y⟫` (`y = ⟪count, steps⟫`) — the arity changes
under quantifiers, so no `UformulaRec1`. The node emitters take their two row indices as
arguments (`constNode W n 19 20` = ⊤, `22 23` = ⊥; `binNode … 24 25` = ∧, `26 27` = ∨;
`quantNode … 28 29` = ∀, `30 31` = ∃; `atomNode … 32 33` = rel, `34 35` = nrel) so that four
Σ₁ definitions serve the eight constructors. -/

section formulaWalk

open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic

/-- The row of the closed symbol fact `isRel 2 R` (`0` = `=`, `1` = `<`). -/
noncomputable def relRow (R : V) : V := if R = 0 then 36 else 37

def relRowDef : 𝚺₀.Semisentence 2 := .mkSigma “y R. (R = 0 → y = 36) ∧ (R ≠ 0 → y = 37)”

instance relRow_defined : 𝚺₀-Function₁ (relRow : V → V) via relRowDef := .mk fun v ↦ by
  simp [relRowDef, relRow, numeral_eq_natCast]
  by_cases h : v 1 = 0 <;> simp [h]
instance relRow_definable : 𝚺₀-Function₁ (relRow : V → V) := relRow_defined.to_definable

/-- (F⊤)/(F⊥): the totality row `i₁` (closed), the formation row `i₂` at `[cTV n, &0]`, the bridge. -/
noncomputable def constNode (W n i₁ i₂ : V) : V :=
  ⟪1, ?[mkStep W i₁ 0, mkStep W i₂ ?[cTV n, ^&0], mkStep W 21 ?[cTV n, ^&0]]⟫

noncomputable def constNodeDef : 𝚺₁.Semisentence 5 := .mkSigma
  “y W n i₁ i₂. ∃ cn, !cTVGraph cn n ∧ ∃ f0, !qqFvarDef f0 0 ∧
    ∃ s₁, !mkStepDef s₁ W i₁ 0 ∧ ∃ e₂, !mkVec₂Def e₂ cn f0 ∧ ∃ s₂, !mkStepDef s₂ W i₂ e₂ ∧
    ∃ s₃, !mkStepDef s₃ W 21 e₂ ∧
    ∃ l₃, !mkVec₁Def l₃ s₃ ∧ ∃ l₂, !adjoinDef l₂ s₂ l₃ ∧ ∃ l₁, !adjoinDef l₁ s₁ l₂ ∧ !pairDef y 1 l₁”

instance constNode_defined : 𝚺₁-Function₄ (constNode : V → V → V → V → V) via constNodeDef := .mk
  fun v ↦ by simp [constNodeDef, constNode, numeral_eq_natCast, cTV.defined.iff, mkStep_defined.iff]
instance constNode_definable : 𝚺₁-Function₄ (constNode : V → V → V → V → V) := constNode_defined.to_definable

/-- (F∧)/(F∨): after `Sp ++ Sq` (`x_p = &cq`, `x_q = &0`): the totality row `i₁` at `[&cq, &0]`, the
formation row `i₂` at `[cTV n, &(cq+1), &1, &0]`, the bridge. Count `cp + cq + 1`. -/
noncomputable def binNode (W n i₁ i₂ yp yq : V) : V :=
  ⟪π₁ yp + π₁ yq + 1, appendV (π₂ yp) (appendV (π₂ yq)
    ?[mkStep W i₁ ?[^&(π₁ yq), ^&0], mkStep W i₂ ?[cTV n, ^&(π₁ yq + 1), ^&1, ^&0], mkStep W 21 ?[cTV n, ^&0]])⟫

noncomputable def binNodeDef : 𝚺₁.Semisentence 7 := .mkSigma
  “y W n i₁ i₂ yp yq. ∃ cp, !pi₁Def cp yp ∧ ∃ Sp, !pi₂Def Sp yp ∧ ∃ cq, !pi₁Def cq yq ∧ ∃ Sq, !pi₂Def Sq yq ∧
    ∃ cn, !cTVGraph cn n ∧ ∃ f0, !qqFvarDef f0 0 ∧ ∃ f1, !qqFvarDef f1 1 ∧
    ∃ fq, !qqFvarDef fq cq ∧ ∃ fq', !qqFvarDef fq' (cq + 1) ∧
    ∃ e₁, !mkVec₂Def e₁ fq f0 ∧ ∃ s₁, !mkStepDef s₁ W i₁ e₁ ∧
    ∃ e₂₀, !mkVec₂Def e₂₀ f1 f0 ∧ ∃ e₂₁, !adjoinDef e₂₁ fq' e₂₀ ∧ ∃ e₂, !adjoinDef e₂ cn e₂₁ ∧
    ∃ s₂, !mkStepDef s₂ W i₂ e₂ ∧
    ∃ e₃, !mkVec₂Def e₃ cn f0 ∧ ∃ s₃, !mkStepDef s₃ W 21 e₃ ∧
    ∃ l₃, !mkVec₁Def l₃ s₃ ∧ ∃ l₂, !adjoinDef l₂ s₂ l₃ ∧ ∃ l₁, !adjoinDef l₁ s₁ l₂ ∧
    ∃ S₂, !appendVDef S₂ Sq l₁ ∧ ∃ S, !appendVDef S Sp S₂ ∧ !pairDef y (cp + cq + 1) S”

instance binNode_defined :
    𝚺₁.DefinedFunction (fun v : Fin 6 → V ↦ binNode (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)) binNodeDef := .mk
  fun v ↦ by simp [binNodeDef, binNode, numeral_eq_natCast, cTV.defined.iff, mkStep_defined.iff, appendV_defined.iff]
instance binNode_definable :
    𝚺₁.DefinableFunction (fun v : Fin 6 → V ↦ binNode (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)) :=
  binNode_defined.to_definable

/-- (F∀)/(F∃): after `Sp` (`x_p = &0`, at arity `n + 1`): the totality row `i₁` at `[&0]`, the
formation row `i₂` at `[cTV n, &1, &0]`, the bridge. Count `cp + 1`. -/
noncomputable def quantNode (W n i₁ i₂ yp : V) : V :=
  ⟪π₁ yp + 1, appendV (π₂ yp)
    ?[mkStep W i₁ ?[^&0], mkStep W i₂ ?[cTV n, ^&1, ^&0], mkStep W 21 ?[cTV n, ^&0]]⟫

noncomputable def quantNodeDef : 𝚺₁.Semisentence 6 := .mkSigma
  “y W n i₁ i₂ yp. ∃ cp, !pi₁Def cp yp ∧ ∃ Sp, !pi₂Def Sp yp ∧
    ∃ cn, !cTVGraph cn n ∧ ∃ f0, !qqFvarDef f0 0 ∧ ∃ f1, !qqFvarDef f1 1 ∧
    ∃ e₁, !mkVec₁Def e₁ f0 ∧ ∃ s₁, !mkStepDef s₁ W i₁ e₁ ∧
    ∃ e₂₀, !mkVec₂Def e₂₀ f1 f0 ∧ ∃ e₂, !adjoinDef e₂ cn e₂₀ ∧ ∃ s₂, !mkStepDef s₂ W i₂ e₂ ∧
    ∃ e₃, !mkVec₂Def e₃ cn f0 ∧ ∃ s₃, !mkStepDef s₃ W 21 e₃ ∧
    ∃ l₃, !mkVec₁Def l₃ s₃ ∧ ∃ l₂, !adjoinDef l₂ s₂ l₃ ∧ ∃ l₁, !adjoinDef l₁ s₁ l₂ ∧
    ∃ S, !appendVDef S Sp l₁ ∧ !pairDef y (cp + 1) S”

instance quantNode_defined : 𝚺₁-Function₅ (quantNode : V → V → V → V → V → V) via quantNodeDef := .mk
  fun v ↦ by simp [quantNodeDef, quantNode, numeral_eq_natCast, cTV.defined.iff, mkStep_defined.iff, appendV_defined.iff]
instance quantNode_definable : 𝚺₁.DefinableFunction₅ (quantNode : V → V → V → V → V → V) :=
  quantNode_defined.to_definable

/-- (Frel)/(Fnrel): after the vector (`d = ⟪cv, Sv⟫`): the closed relation row, the totality row `i₁`
at `[cTV k, cTV R, ⟨v⟩]`, the formation row `i₂` at `[cTV n, cTV k, cTV R, ⟨v⟩', &0]`, the bridge,
`isUTermVecOfSemitermVecLAct [cTV k, cTV n, ⟨v⟩']` and its bridge. Count `cv + 1`. -/
noncomputable def atomNode (W n i₁ i₂ k R d : V) : V :=
  ⟪π₁ d + 1, appendV (π₂ d)
    ?[mkStep W (relRow R) 0,
      mkStep W i₁ ?[cTV k, cTV R, vRef 0 k],
      mkStep W i₂ ?[cTV n, cTV k, cTV R, vRef 1 k, ^&0],
      mkStep W 21 ?[cTV n, ^&0],
      mkStep W 38 ?[cTV k, cTV n, vRef 1 k],
      mkStep W 39 ?[cTV k, vRef 1 k]]⟫

noncomputable def atomNodeDef : 𝚺₁.Semisentence 8 := .mkSigma
  “y W n i₁ i₂ k R d. ∃ cv, !pi₁Def cv d ∧ ∃ Sv, !pi₂Def Sv d ∧
    ∃ f0, !qqFvarDef f0 0 ∧ ∃ r0, !vRefDef r0 0 k ∧ ∃ r1, !vRefDef r1 1 k ∧
    ∃ ck, !cTVGraph ck k ∧ ∃ cR, !cTVGraph cR R ∧ ∃ cn, !cTVGraph cn n ∧
    ∃ j₁, !relRowDef j₁ R ∧ ∃ s₁, !mkStepDef s₁ W j₁ 0 ∧
    ∃ e₂₀, !mkVec₂Def e₂₀ cR r0 ∧ ∃ e₂, !adjoinDef e₂ ck e₂₀ ∧ ∃ s₂, !mkStepDef s₂ W i₁ e₂ ∧
    ∃ e₃₀, !mkVec₂Def e₃₀ r1 f0 ∧ ∃ e₃₁, !adjoinDef e₃₁ cR e₃₀ ∧ ∃ e₃₂, !adjoinDef e₃₂ ck e₃₁ ∧
    ∃ e₃, !adjoinDef e₃ cn e₃₂ ∧ ∃ s₃, !mkStepDef s₃ W i₂ e₃ ∧
    ∃ e₄, !mkVec₂Def e₄ cn f0 ∧ ∃ s₄, !mkStepDef s₄ W 21 e₄ ∧
    ∃ e₅₀, !mkVec₂Def e₅₀ cn r1 ∧ ∃ e₅, !adjoinDef e₅ ck e₅₀ ∧ ∃ s₅, !mkStepDef s₅ W 38 e₅ ∧
    ∃ e₆, !mkVec₂Def e₆ ck r1 ∧ ∃ s₆, !mkStepDef s₆ W 39 e₆ ∧
    ∃ l₆, !mkVec₁Def l₆ s₆ ∧ ∃ l₅, !adjoinDef l₅ s₅ l₆ ∧ ∃ l₄, !adjoinDef l₄ s₄ l₅ ∧
    ∃ l₃, !adjoinDef l₃ s₃ l₄ ∧ ∃ l₂, !adjoinDef l₂ s₂ l₃ ∧ ∃ l₁, !adjoinDef l₁ s₁ l₂ ∧
    ∃ S, !appendVDef S Sv l₁ ∧ !pairDef y (cv + 1) S”

instance atomNode_defined :
    𝚺₁.DefinedFunction (fun v : Fin 7 → V ↦ atomNode (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6)) atomNodeDef := .mk
  fun v ↦ by
    simp [atomNodeDef, atomNode, numeral_eq_natCast, cTV.defined.iff, mkStep_defined.iff, appendV_defined.iff,
      vRef_defined.iff, relRow_defined.iff]
instance atomNode_definable :
    𝚺₁.DefinableFunction (fun v : Fin 7 → V ↦ atomNode (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6)) :=
  atomNode_defined.to_definable

/-! ### 4.1 The fixpoint on `⟪n, r, y⟫` -/

namespace DescF

/-- The walk operator on triples `⟪n, r, y⟫`, with the bounds the blueprint carries. -/
def Phi (W : V) (C : Set V) (pr : V) : Prop :=
  ∃ n ≤ pr, ∃ q ≤ pr, pr = ⟪n, q⟫ ∧ ∃ r ≤ q, ∃ y ≤ q, q = ⟪r, y⟫ ∧
  ( (∃ k < r, ∃ R < r, ∃ v < r, r = ^rel k R v ∧
      y = atomNode W n 32 33 k R (descVecAux W n (descTVec W n k v) k)) ∨
    (∃ k < r, ∃ R < r, ∃ v < r, r = ^nrel k R v ∧
      y = atomNode W n 34 35 k R (descVecAux W n (descTVec W n k v) k)) ∨
    (r = ^⊤ ∧ y = constNode W n 19 20) ∨
    (r = ^⊥ ∧ y = constNode W n 22 23) ∨
    (∃ p < r, ∃ p' < r, r = p ^⋏ p' ∧ ∃ yp ≤ y, ∃ yq ≤ y, ⟪n, p, yp⟫ ∈ C ∧ ⟪n, p', yq⟫ ∈ C ∧
      y = binNode W n 24 25 yp yq) ∨
    (∃ p < r, ∃ p' < r, r = p ^⋎ p' ∧ ∃ yp ≤ y, ∃ yq ≤ y, ⟪n, p, yp⟫ ∈ C ∧ ⟪n, p', yq⟫ ∈ C ∧
      y = binNode W n 26 27 yp yq) ∨
    (∃ p < r, r = ^∀ p ∧ ∃ yp ≤ y, ⟪n + 1, p, yp⟫ ∈ C ∧ y = quantNode W n 28 29 yp) ∨
    (∃ p < r, r = ^∃ p ∧ ∃ yp ≤ y, ⟪n + 1, p, yp⟫ ∈ C ∧ y = quantNode W n 30 31 yp) )

noncomputable def blueprint : Fixpoint.Blueprint 1 := ⟨.mkDelta
  (.mkSigma “pr C W.
    ∃ n <⁺ pr, ∃ q <⁺ pr, !pairDef pr n q ∧ ∃ r <⁺ q, ∃ y <⁺ q, !pairDef q r y ∧
    ( (∃ k < r, ∃ R < r, ∃ v < r, !qqRelDef r k R v ∧
        ∃ w, !descTVecDef w W n k v ∧ ∃ d, !descVecAuxDef d W n w k ∧ ∃ s, !atomNodeDef s W n 32 33 k R d ∧ y = s) ∨
      (∃ k < r, ∃ R < r, ∃ v < r, !qqNRelDef r k R v ∧
        ∃ w, !descTVecDef w W n k v ∧ ∃ d, !descVecAuxDef d W n w k ∧ ∃ s, !atomNodeDef s W n 34 35 k R d ∧ y = s) ∨
      (!qqVerumDef r ∧ ∃ s, !constNodeDef s W n 19 20 ∧ y = s) ∨
      (!qqFalsumDef r ∧ ∃ s, !constNodeDef s W n 22 23 ∧ y = s) ∨
      (∃ p < r, ∃ p' < r, !qqAndDef r p p' ∧ ∃ yp <⁺ y, ∃ yq <⁺ y, :⟪n, p, yp⟫:∈ C ∧ :⟪n, p', yq⟫:∈ C ∧
        ∃ s, !binNodeDef s W n 24 25 yp yq ∧ y = s) ∨
      (∃ p < r, ∃ p' < r, !qqOrDef r p p' ∧ ∃ yp <⁺ y, ∃ yq <⁺ y, :⟪n, p, yp⟫:∈ C ∧ :⟪n, p', yq⟫:∈ C ∧
        ∃ s, !binNodeDef s W n 26 27 yp yq ∧ y = s) ∨
      (∃ p < r, !qqAllDef r p ∧ ∃ yp <⁺ y, :⟪n + 1, p, yp⟫:∈ C ∧ ∃ s, !quantNodeDef s W n 28 29 yp ∧ y = s) ∨
      (∃ p < r, !qqExsDef r p ∧ ∃ yp <⁺ y, :⟪n + 1, p, yp⟫:∈ C ∧ ∃ s, !quantNodeDef s W n 30 31 yp ∧ y = s) )”)
  (.mkPi “pr C W.
    ∃ n <⁺ pr, ∃ q <⁺ pr, !pairDef pr n q ∧ ∃ r <⁺ q, ∃ y <⁺ q, !pairDef q r y ∧
    ( (∃ k < r, ∃ R < r, ∃ v < r, !qqRelDef r k R v ∧
        ∀ w, !descTVecDef w W n k v → ∀ d, !descVecAuxDef d W n w k → ∀ s, !atomNodeDef s W n 32 33 k R d → y = s) ∨
      (∃ k < r, ∃ R < r, ∃ v < r, !qqNRelDef r k R v ∧
        ∀ w, !descTVecDef w W n k v → ∀ d, !descVecAuxDef d W n w k → ∀ s, !atomNodeDef s W n 34 35 k R d → y = s) ∨
      (!qqVerumDef r ∧ ∀ s, !constNodeDef s W n 19 20 → y = s) ∨
      (!qqFalsumDef r ∧ ∀ s, !constNodeDef s W n 22 23 → y = s) ∨
      (∃ p < r, ∃ p' < r, !qqAndDef r p p' ∧ ∃ yp <⁺ y, ∃ yq <⁺ y, :⟪n, p, yp⟫:∈ C ∧ :⟪n, p', yq⟫:∈ C ∧
        ∀ s, !binNodeDef s W n 24 25 yp yq → y = s) ∨
      (∃ p < r, ∃ p' < r, !qqOrDef r p p' ∧ ∃ yp <⁺ y, ∃ yq <⁺ y, :⟪n, p, yp⟫:∈ C ∧ :⟪n, p', yq⟫:∈ C ∧
        ∀ s, !binNodeDef s W n 26 27 yp yq → y = s) ∨
      (∃ p < r, !qqAllDef r p ∧ ∃ yp <⁺ y, :⟪n + 1, p, yp⟫:∈ C ∧ ∀ s, !quantNodeDef s W n 28 29 yp → y = s) ∨
      (∃ p < r, !qqExsDef r p ∧ ∃ yp <⁺ y, :⟪n + 1, p, yp⟫:∈ C ∧ ∀ s, !quantNodeDef s W n 30 31 yp → y = s) )”)⟩

noncomputable def construction : Fixpoint.Construction V blueprint where
  Φ := fun v ↦ Phi (v 0)
  defined := .mk <| by
    constructor
    · intro v
      simp [blueprint, descTVec_defined.iff, descVecAux_defined.iff, atomNode_defined.iff, constNode_defined.iff,
        binNode_defined.iff, quantNode_defined.iff, numeral_eq_natCast]
    · intro v
      simp [blueprint, Phi, descTVec_defined.iff, descVecAux_defined.iff, atomNode_defined.iff,
        constNode_defined.iff, binNode_defined.iff, quantNode_defined.iff, numeral_eq_natCast]
  monotone := by
    rintro C C' hC v pr ⟨n, hn, q, hq, rfl, r, hr, y, hy, rfl, h⟩
    refine ⟨n, hn, _, hq, rfl, r, hr, y, hy, rfl, ?_⟩
    rcases h with h | h | h | h | ⟨p, hp, p', hp', rfl, yp, hyp, yq, hyq, h₁, h₂, rfl⟩ |
      ⟨p, hp, p', hp', rfl, yp, hyp, yq, hyq, h₁, h₂, rfl⟩ | ⟨p, hp, rfl, yp, hyp, h₁, rfl⟩ | ⟨p, hp, rfl, yp, hyp, h₁, rfl⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, hp, p', hp', rfl, yp, hyp, yq, hyq, hC h₁, hC h₂, rfl⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, hp, p', hp', rfl, yp, hyp, yq, hyq, hC h₁, hC h₂, rfl⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, hp, rfl, yp, hyp, hC h₁, rfl⟩))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨p, hp, rfl, yp, hyp, hC h₁, rfl⟩))))))

/-- Every referenced triple `⟪n', p, yp⟫` (`p < r`, `yp ≤ y`) is below `⟪n', r, y⟫`. -/
instance : construction.Finite V where
  finite := by
    rintro C v pr ⟨n, hn, q, hq, rfl, r, hr, y, hy, rfl, h⟩
    have key : ∀ {p yp : V}, p < r → yp ≤ y → ⟪p, yp⟫ < ⟪r, y⟫ := fun hp hyp ↦
      lt_of_lt_of_le (pair_lt_pair_left hp _) (pair_le_pair_right _ hyp)
    rcases h with h | h | h | h | ⟨p, hp, p', hp', hr', yp, hyp, yq, hyq, h₁, h₂, hy'⟩ |
      ⟨p, hp, p', hp', hr', yp, hyp, yq, hyq, h₁, h₂, hy'⟩ | ⟨p, hp, hr', yp, hyp, h₁, hy'⟩ | ⟨p, hp, hr', yp, hyp, h₁, hy'⟩
    · exact ⟨0, n, hn, _, hq, rfl, r, hr, y, hy, rfl, Or.inl h⟩
    · exact ⟨0, n, hn, _, hq, rfl, r, hr, y, hy, rfl, Or.inr (Or.inl h)⟩
    · exact ⟨0, n, hn, _, hq, rfl, r, hr, y, hy, rfl, Or.inr (Or.inr (Or.inl h))⟩
    · exact ⟨0, n, hn, _, hq, rfl, r, hr, y, hy, rfl, Or.inr (Or.inr (Or.inr (Or.inl h)))⟩
    · exact ⟨⟪n, ⟪r, y⟫⟫, n, hn, _, hq, rfl, r, hr, y, hy, rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨p, hp, p', hp', hr', yp, hyp, yq, hyq, ⟨h₁, pair_lt_pair_right _ (key hp hyp)⟩,
          ⟨h₂, pair_lt_pair_right _ (key hp' hyq)⟩, hy'⟩))))⟩
    · exact ⟨⟪n, ⟪r, y⟫⟫, n, hn, _, hq, rfl, r, hr, y, hy, rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨p, hp, p', hp', hr', yp, hyp, yq, hyq, ⟨h₁, pair_lt_pair_right _ (key hp hyp)⟩,
          ⟨h₂, pair_lt_pair_right _ (key hp' hyq)⟩, hy'⟩)))))⟩
    · exact ⟨⟪n + 1, ⟪r, y⟫⟫, n, hn, _, hq, rfl, r, hr, y, hy, rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨p, hp, hr', yp, hyp, ⟨h₁, pair_lt_pair_right _ (key hp hyp)⟩, hy'⟩))))))⟩
    · exact ⟨⟪n + 1, ⟪r, y⟫⟫, n, hn, _, hq, rfl, r, hr, y, hy, rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨p, hp, hr', yp, hyp, ⟨h₁, pair_lt_pair_right _ (key hp hyp)⟩, hy'⟩))))))⟩

/-- `Phi` at a triple, the bounds discharged. -/
lemma phi_iff (W : V) (C : Set V) (n r y : V) :
    Phi W C ⟪n, r, y⟫ ↔
    ( (∃ k R v, r = ^rel k R v ∧ y = atomNode W n 32 33 k R (descVecAux W n (descTVec W n k v) k)) ∨
      (∃ k R v, r = ^nrel k R v ∧ y = atomNode W n 34 35 k R (descVecAux W n (descTVec W n k v) k)) ∨
      (r = ^⊤ ∧ y = constNode W n 19 20) ∨
      (r = ^⊥ ∧ y = constNode W n 22 23) ∨
      (∃ p p' yp yq, r = p ^⋏ p' ∧ yp ≤ y ∧ yq ≤ y ∧ ⟪n, p, yp⟫ ∈ C ∧ ⟪n, p', yq⟫ ∈ C ∧ y = binNode W n 24 25 yp yq) ∨
      (∃ p p' yp yq, r = p ^⋎ p' ∧ yp ≤ y ∧ yq ≤ y ∧ ⟪n, p, yp⟫ ∈ C ∧ ⟪n, p', yq⟫ ∈ C ∧ y = binNode W n 26 27 yp yq) ∨
      (∃ p yp, r = ^∀ p ∧ yp ≤ y ∧ ⟪n + 1, p, yp⟫ ∈ C ∧ y = quantNode W n 28 29 yp) ∨
      (∃ p yp, r = ^∃ p ∧ yp ≤ y ∧ ⟪n + 1, p, yp⟫ ∈ C ∧ y = quantNode W n 30 31 yp) ) := by
  constructor
  · rintro ⟨n', _, q, _, hpr, r', _, y', _, hq, h⟩
    obtain ⟨rfl, rfl⟩ := pair_ext_iff.mp hpr
    obtain ⟨rfl, rfl⟩ := pair_ext_iff.mp hq
    rcases h with ⟨k, _, R, _, v, _, rfl, rfl⟩ | ⟨k, _, R, _, v, _, rfl, rfl⟩ | h | h |
      ⟨p, _, p', _, rfl, yp, hyp, yq, hyq, h₁, h₂, rfl⟩ | ⟨p, _, p', _, rfl, yp, hyp, yq, hyq, h₁, h₂, rfl⟩ |
      ⟨p, _, rfl, yp, hyp, h₁, rfl⟩ | ⟨p, _, rfl, yp, hyp, h₁, rfl⟩
    · exact Or.inl ⟨k, R, v, rfl, rfl⟩
    · exact Or.inr (Or.inl ⟨k, R, v, rfl, rfl⟩)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, p', yp, yq, rfl, hyp, hyq, h₁, h₂, rfl⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, p', yp, yq, rfl, hyp, hyq, h₁, h₂, rfl⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, yp, rfl, hyp, h₁, rfl⟩))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨p, yp, rfl, hyp, h₁, rfl⟩))))))
  · intro h
    refine ⟨n, by simp, _, by simp, rfl, r, by simp, y, by simp, rfl, ?_⟩
    rcases h with ⟨k, R, v, rfl, rfl⟩ | ⟨k, R, v, rfl, rfl⟩ | h | h |
      ⟨p, p', yp, yq, rfl, hyp, hyq, h₁, h₂, rfl⟩ | ⟨p, p', yp, yq, rfl, hyp, hyq, h₁, h₂, rfl⟩ |
      ⟨p, yp, rfl, hyp, h₁, rfl⟩ | ⟨p, yp, rfl, hyp, h₁, rfl⟩
    · exact Or.inl ⟨k, by simp, R, by simp, v, by simp, rfl, rfl⟩
    · exact Or.inr (Or.inl ⟨k, by simp, R, by simp, v, by simp, rfl, rfl⟩)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, by simp, p', by simp, rfl, yp, hyp, yq, hyq, h₁, h₂, rfl⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, by simp, p', by simp, rfl, yp, hyp, yq, hyq, h₁, h₂, rfl⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, by simp, rfl, yp, hyp, h₁, rfl⟩))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨p, by simp, rfl, yp, hyp, h₁, rfl⟩))))))

end DescF

/-- **The graph of the formula walk**: `DescFGraph W n r y` — the walk of `r` at arity `n` (over
the piece table `W`) is `y = ⟪count, steps⟫`. -/
def DescFGraph (W n r y : V) : Prop := DescF.construction.Fixpoint ![W] ⟪n, r, y⟫

noncomputable def descFGraphDef : 𝚺₁.Semisentence 4 := .mkSigma
  “W n r y. ∃ q, !pairDef q r y ∧ ∃ pr, !pairDef pr n q ∧ !DescF.blueprint.fixpointDef pr W”

instance descFGraph_defined : 𝚺₁-Relation₄ (DescFGraph : V → V → V → V → Prop) via descFGraphDef := .mk
  fun v ↦ by simp [descFGraphDef, DescF.construction.eval_fixpointDef, DescFGraph]; rfl
instance descFGraph_definable : 𝚺₁-Relation₄ (DescFGraph : V → V → V → V → Prop) := descFGraph_defined.to_definable

/-! ### 4.2 Case analysis, inversion, existence and uniqueness -/

lemma DescFGraph.case_iff {W n r y : V} :
    DescFGraph W n r y ↔
    ( (∃ k R v, r = ^rel k R v ∧ y = atomNode W n 32 33 k R (descVecAux W n (descTVec W n k v) k)) ∨
      (∃ k R v, r = ^nrel k R v ∧ y = atomNode W n 34 35 k R (descVecAux W n (descTVec W n k v) k)) ∨
      (r = ^⊤ ∧ y = constNode W n 19 20) ∨
      (r = ^⊥ ∧ y = constNode W n 22 23) ∨
      (∃ p p' yp yq, r = p ^⋏ p' ∧ yp ≤ y ∧ yq ≤ y ∧ DescFGraph W n p yp ∧ DescFGraph W n p' yq ∧
        y = binNode W n 24 25 yp yq) ∨
      (∃ p p' yp yq, r = p ^⋎ p' ∧ yp ≤ y ∧ yq ≤ y ∧ DescFGraph W n p yp ∧ DescFGraph W n p' yq ∧
        y = binNode W n 26 27 yp yq) ∨
      (∃ p yp, r = ^∀ p ∧ yp ≤ y ∧ DescFGraph W (n + 1) p yp ∧ y = quantNode W n 28 29 yp) ∨
      (∃ p yp, r = ^∃ p ∧ yp ≤ y ∧ DescFGraph W (n + 1) p yp ∧ y = quantNode W n 30 31 yp) ) := by
  unfold DescFGraph
  rw [DescF.construction.case]
  exact DescF.phi_iff W _ n r y

section inversion

attribute [local simp] qqRel qqNRel qqVerum qqFalsum qqAnd qqOr qqAll qqExs

lemma DescFGraph.verum_iff {W n y : V} : DescFGraph W n ^⊤ y ↔ y = constNode W n 19 20 := by
  rw [DescFGraph.case_iff]; simp
lemma DescFGraph.falsum_iff {W n y : V} : DescFGraph W n ^⊥ y ↔ y = constNode W n 22 23 := by
  rw [DescFGraph.case_iff]; simp
lemma DescFGraph.rel_iff {W n k R v y : V} :
    DescFGraph W n (^rel k R v) y ↔ y = atomNode W n 32 33 k R (descVecAux W n (descTVec W n k v) k) := by
  rw [DescFGraph.case_iff]; simp
lemma DescFGraph.nrel_iff {W n k R v y : V} :
    DescFGraph W n (^nrel k R v) y ↔ y = atomNode W n 34 35 k R (descVecAux W n (descTVec W n k v) k) := by
  rw [DescFGraph.case_iff]; simp
lemma DescFGraph.and_iff {W n p q y : V} :
    DescFGraph W n (p ^⋏ q) y ↔
    ∃ yp yq, yp ≤ y ∧ yq ≤ y ∧ DescFGraph W n p yp ∧ DescFGraph W n q yq ∧ y = binNode W n 24 25 yp yq := by
  rw [DescFGraph.case_iff]; simp
lemma DescFGraph.or_iff {W n p q y : V} :
    DescFGraph W n (p ^⋎ q) y ↔
    ∃ yp yq, yp ≤ y ∧ yq ≤ y ∧ DescFGraph W n p yp ∧ DescFGraph W n q yq ∧ y = binNode W n 26 27 yp yq := by
  rw [DescFGraph.case_iff]; simp
lemma DescFGraph.all_iff {W n p y : V} :
    DescFGraph W n (^∀ p) y ↔ ∃ yp, yp ≤ y ∧ DescFGraph W (n + 1) p yp ∧ y = quantNode W n 28 29 yp := by
  rw [DescFGraph.case_iff]; simp
lemma DescFGraph.exs_iff {W n p y : V} :
    DescFGraph W n (^∃ p) y ↔ ∃ yp, yp ≤ y ∧ DescFGraph W (n + 1) p yp ∧ y = quantNode W n 30 31 yp := by
  rw [DescFGraph.case_iff]; simp

end inversion

/-- The step list of a node dominates the child's list (as codes): `u ≤ appendV u w`. -/
lemma le_appendV_left (u w : V) : u ≤ appendV u w := by
  induction u using adjoin_ISigma1.pi1_succ_induction with
  | hP => definability
  | nil => exact zero_le
  | adjoin x u ih => rw [appendV_adjoin]; exact adjoin_le_adjoin le_rfl ih

lemma le_adjoin_self (x v : V) : v ≤ x ∷ v := by
  rw [adjoin_def]; exact le_trans (le_pair_right x v) le_self_add

lemma le_appendV_right (u w : V) : w ≤ appendV u w := by
  induction u using adjoin_ISigma1.pi1_succ_induction with
  | hP => definability
  | nil => rw [appendV_nil]
  | adjoin x u ih => rw [appendV_adjoin]; exact le_trans ih (le_adjoin_self _ _)

lemma le_binNode_left (W n i₁ i₂ yp yq : V) : yp ≤ binNode W n i₁ i₂ yp yq := by
  unfold binNode
  calc yp = ⟪π₁ yp, π₂ yp⟫ := (pair_unpair yp).symm
    _ ≤ _ := pair_le_pair (le_trans le_self_add le_self_add) (le_appendV_left _ _)
lemma le_binNode_right (W n i₁ i₂ yp yq : V) : yq ≤ binNode W n i₁ i₂ yp yq := by
  unfold binNode
  calc yq = ⟪π₁ yq, π₂ yq⟫ := (pair_unpair yq).symm
    _ ≤ _ := pair_le_pair (le_trans le_add_self le_self_add) (le_trans (le_appendV_left _ _) (le_appendV_right _ _))
lemma le_quantNode (W n i₁ i₂ yp : V) : yp ≤ quantNode W n i₁ i₂ yp := by
  unfold quantNode
  calc yp = ⟪π₁ yp, π₂ yp⟫ := (pair_unpair yp).symm
    _ ≤ _ := pair_le_pair le_self_add (le_appendV_left _ _)

lemma descFGraph_exists (W : V) : ∀ {n r : V}, IsSemiformula LAct n r → ∃ y, DescFGraph W n r y := by
  intro n r
  apply IsSemiformula.sigma1_structural_induction (P := fun n r ↦ ∃ y, DescFGraph W n r y)
  · definability
  · intro n k R v _ _; exact ⟨_, DescFGraph.rel_iff.mpr rfl⟩
  · intro n k R v _ _; exact ⟨_, DescFGraph.nrel_iff.mpr rfl⟩
  · intro n; exact ⟨_, DescFGraph.verum_iff.mpr rfl⟩
  · intro n; exact ⟨_, DescFGraph.falsum_iff.mpr rfl⟩
  · rintro n p q _ _ ⟨yp, hp⟩ ⟨yq, hq⟩
    exact ⟨_, DescFGraph.and_iff.mpr ⟨yp, yq, le_binNode_left _ _ _ _ _ _, le_binNode_right _ _ _ _ _ _, hp, hq, rfl⟩⟩
  · rintro n p q _ _ ⟨yp, hp⟩ ⟨yq, hq⟩
    exact ⟨_, DescFGraph.or_iff.mpr ⟨yp, yq, le_binNode_left _ _ _ _ _ _, le_binNode_right _ _ _ _ _ _, hp, hq, rfl⟩⟩
  · rintro n p _ ⟨yp, hp⟩; exact ⟨_, DescFGraph.all_iff.mpr ⟨yp, le_quantNode _ _ _ _ _, hp, rfl⟩⟩
  · rintro n p _ ⟨yp, hp⟩; exact ⟨_, DescFGraph.exs_iff.mpr ⟨yp, le_quantNode _ _ _ _ _, hp, rfl⟩⟩

lemma descFGraph_unique (W : V) : ∀ {n r : V}, IsSemiformula LAct n r →
    ∀ y₁ y₂, DescFGraph W n r y₁ → DescFGraph W n r y₂ → y₁ = y₂ := by
  intro n r
  apply IsSemiformula.pi1_structural_induction
    (P := fun n r ↦ ∀ y₁ y₂, DescFGraph W n r y₁ → DescFGraph W n r y₂ → y₁ = y₂)
  · definability
  · intro n k R v _ _ y₁ y₂ h₁ h₂; rw [DescFGraph.rel_iff] at h₁ h₂; rw [h₁, h₂]
  · intro n k R v _ _ y₁ y₂ h₁ h₂; rw [DescFGraph.nrel_iff] at h₁ h₂; rw [h₁, h₂]
  · intro n y₁ y₂ h₁ h₂; rw [DescFGraph.verum_iff] at h₁ h₂; rw [h₁, h₂]
  · intro n y₁ y₂ h₁ h₂; rw [DescFGraph.falsum_iff] at h₁ h₂; rw [h₁, h₂]
  · intro n p q _ _ ihp ihq y₁ y₂ h₁ h₂
    obtain ⟨yp, yq, _, _, hp, hq, rfl⟩ := DescFGraph.and_iff.mp h₁
    obtain ⟨yp', yq', _, _, hp', hq', rfl⟩ := DescFGraph.and_iff.mp h₂
    rw [ihp yp yp' hp hp', ihq yq yq' hq hq']
  · intro n p q _ _ ihp ihq y₁ y₂ h₁ h₂
    obtain ⟨yp, yq, _, _, hp, hq, rfl⟩ := DescFGraph.or_iff.mp h₁
    obtain ⟨yp', yq', _, _, hp', hq', rfl⟩ := DescFGraph.or_iff.mp h₂
    rw [ihp yp yp' hp hp', ihq yq yq' hq hq']
  · intro n p _ ih y₁ y₂ h₁ h₂
    obtain ⟨yp, _, hp, rfl⟩ := DescFGraph.all_iff.mp h₁
    obtain ⟨yp', _, hp', rfl⟩ := DescFGraph.all_iff.mp h₂
    rw [ih yp yp' hp hp']
  · intro n p _ ih y₁ y₂ h₁ h₂
    obtain ⟨yp, _, hp, rfl⟩ := DescFGraph.exs_iff.mp h₁
    obtain ⟨yp', _, hp', rfl⟩ := DescFGraph.exs_iff.mp h₂
    rw [ih yp yp' hp hp']

lemma descFGraph_existsUnique_total (W n r : V) :
    ∃! y, (IsSemiformula LAct n r → DescFGraph W n r y) ∧ (¬IsSemiformula LAct n r → y = 0) := by
  by_cases h : IsSemiformula LAct n r
  · obtain ⟨y, hy⟩ := descFGraph_exists W h
    simpa [h] using ExistsUnique.intro y hy (fun y' hy' ↦ descFGraph_unique W h y' y hy' hy)
  · simp [h]

/-- **The formula walk**: `descFw W n r = ⟪count, steps⟫` (`0` off semiformulas). -/
noncomputable def descFw (W n r : V) : V := Classical.choose! (descFGraph_existsUnique_total W n r)

theorem descFw_graph {W n r : V} (h : IsSemiformula LAct n r) : DescFGraph W n r (descFw W n r) :=
  (Classical.choose!_spec (descFGraph_existsUnique_total W n r)).1 h

theorem descFw_of_not {W n r : V} (h : ¬IsSemiformula LAct n r) : descFw W n r = 0 :=
  (Classical.choose!_spec (descFGraph_existsUnique_total W n r)).2 h

lemma descFw_eq_of_graph {W n r y : V} (h : IsSemiformula LAct n r) (hy : DescFGraph W n r y) : descFw W n r = y :=
  descFGraph_unique W h _ _ (descFw_graph h) hy

/-- The step list of the formula walk. -/
noncomputable def describeF (W n r : V) : V := π₂ (descFw W n r)
/-- The number of eigenvariables the formula walk introduces. -/
noncomputable def descCountF (W n r : V) : V := π₁ (descFw W n r)

noncomputable def descFwDef : 𝚺₁.Semisentence 4 := .mkSigma
  “y W n r. (!(isSemiformula LAct).pi n r → !descFGraphDef W n r y) ∧ (¬!(isSemiformula LAct).sigma n r → y = 0)”

instance descFw_defined : 𝚺₁-Function₃ (descFw : V → V → V → V) via descFwDef := .mk fun v ↦ by
  simp [descFwDef, HierarchySymbol.Semiformula.val_sigma, descFGraph_defined.iff,
    (IsSemiformula.defined (L := LAct)).proper.iff', (IsSemiformula.defined (L := LAct)).df, descFw,
    Classical.choose!_eq_iff_right]
instance descFw_definable : 𝚺₁-Function₃ (descFw : V → V → V → V) := descFw_defined.to_definable

noncomputable def describeFDef : 𝚺₁.Semisentence 4 := .mkSigma “y W n r. ∃ d, !descFwDef d W n r ∧ !pi₂Def y d”
noncomputable def descCountFDef : 𝚺₁.Semisentence 4 := .mkSigma “y W n r. ∃ d, !descFwDef d W n r ∧ !pi₁Def y d”

instance describeF_defined : 𝚺₁-Function₃ (describeF : V → V → V → V) via describeFDef := .mk
  fun v ↦ by simp [describeFDef, descFw_defined.iff, describeF]
instance describeF_definable : 𝚺₁-Function₃ (describeF : V → V → V → V) := describeF_defined.to_definable
instance descCountF_defined : 𝚺₁-Function₃ (descCountF : V → V → V → V) via descCountFDef := .mk
  fun v ↦ by simp [descCountFDef, descFw_defined.iff, descCountF]
instance descCountF_definable : 𝚺₁-Function₃ (descCountF : V → V → V → V) := descCountF_defined.to_definable

/-! ### 4.3 The per-constructor equations (D2 for formulas) -/

lemma descFw_verum (W n : V) : descFw W n ^⊤ = constNode W n 19 20 :=
  descFw_eq_of_graph (by simp) (DescFGraph.verum_iff.mpr rfl)
lemma descFw_falsum (W n : V) : descFw W n ^⊥ = constNode W n 22 23 :=
  descFw_eq_of_graph (by simp) (DescFGraph.falsum_iff.mpr rfl)
lemma descFw_rel (W n : V) {k R v : V} (hR : LAct.IsRel k R) (hv : IsSemitermVec LAct k n v) :
    descFw W n (^rel k R v) = atomNode W n 32 33 k R (descVecAux W n (descTVec W n k v) k) :=
  descFw_eq_of_graph (by simp [hR, hv]) (DescFGraph.rel_iff.mpr rfl)
lemma descFw_nrel (W n : V) {k R v : V} (hR : LAct.IsRel k R) (hv : IsSemitermVec LAct k n v) :
    descFw W n (^nrel k R v) = atomNode W n 34 35 k R (descVecAux W n (descTVec W n k v) k) :=
  descFw_eq_of_graph (by simp [hR, hv]) (DescFGraph.nrel_iff.mpr rfl)
lemma descFw_and (W n : V) {p q : V} (hp : IsSemiformula LAct n p) (hq : IsSemiformula LAct n q) :
    descFw W n (p ^⋏ q) = binNode W n 24 25 (descFw W n p) (descFw W n q) :=
  descFw_eq_of_graph (by simp [hp, hq]) (DescFGraph.and_iff.mpr
    ⟨_, _, le_binNode_left _ _ _ _ _ _, le_binNode_right _ _ _ _ _ _, descFw_graph hp, descFw_graph hq, rfl⟩)
lemma descFw_or (W n : V) {p q : V} (hp : IsSemiformula LAct n p) (hq : IsSemiformula LAct n q) :
    descFw W n (p ^⋎ q) = binNode W n 26 27 (descFw W n p) (descFw W n q) :=
  descFw_eq_of_graph (by simp [hp, hq]) (DescFGraph.or_iff.mpr
    ⟨_, _, le_binNode_left _ _ _ _ _ _, le_binNode_right _ _ _ _ _ _, descFw_graph hp, descFw_graph hq, rfl⟩)
lemma descFw_all (W n : V) {p : V} (hp : IsSemiformula LAct (n + 1) p) :
    descFw W n (^∀ p) = quantNode W n 28 29 (descFw W (n + 1) p) :=
  descFw_eq_of_graph (by simp [hp]) (DescFGraph.all_iff.mpr ⟨_, le_quantNode _ _ _ _ _, descFw_graph hp, rfl⟩)
lemma descFw_exs (W n : V) {p : V} (hp : IsSemiformula LAct (n + 1) p) :
    descFw W n (^∃ p) = quantNode W n 30 31 (descFw W (n + 1) p) :=
  descFw_eq_of_graph (by simp [hp]) (DescFGraph.exs_iff.mpr ⟨_, le_quantNode _ _ _ _ _, descFw_graph hp, rfl⟩)

lemma descCountF_and (W n : V) {p q : V} (hp : IsSemiformula LAct n p) (hq : IsSemiformula LAct n q) :
    descCountF W n (p ^⋏ q) = descCountF W n p + descCountF W n q + 1 := by
  rw [descCountF, descFw_and W n hp hq, binNode, pi₁_pair]; rfl
lemma descCountF_all (W n : V) {p : V} (hp : IsSemiformula LAct (n + 1) p) :
    descCountF W n (^∀ p) = descCountF W (n + 1) p + 1 := by
  rw [descCountF, descFw_all W n hp, quantNode, pi₁_pair]; rfl
lemma descCountF_verum (W n : V) : descCountF W n ^⊤ = 1 := by
  rw [descCountF, descFw_verum, constNode, pi₁_pair]

end formulaWalk

/-! ## Part 5 — applicability of the formula walk (D3 for formulas) -/

section formulaRows
/-- Row `isSemiformulaVerum` as a step. -/
lemma ok_isSemiformulaVerum {tbl N E Γ W : V} {wn : V} {wp : V} (htbl : TableOK tbl N) (hW : WalkTable tbl) (hWp : W = walkPieces)
    (hΓ : IsFormulaSet LAct Γ) (hwn : IsSemiterm LAct 0 wn) (hEwn : termLen LAct wn ≤ E) (hwp : IsSemiterm LAct 0 wp) (hEwp : termLen LAct wp ≤ E) (hmem0 : neg LAct (verumFact wp) ∈ Γ) :
    StepOK tbl E ((8 : ℕ) : V) Γ (mkStep W 20 ?[wn, wp]) ∧ sTag (mkStep W 20 ?[wn, wp]) = 0 ∧
    ctxAfter Γ (mkStep W 20 ?[wn, wp]) = insert (neg LAct (sigmaFact wn wp)) Γ := by
  subst hWp
  have hk : ((rIdx_isSemiformulaVerum : ℕ) : V) = (20 : V) := by simp [rIdx_isSemiformulaVerum]
  have hstep := mkStep_isSemiformulaVerum (V := V) ?[wn, wp]
  have hlen := walkTable_len hW rIdx_isSemiformulaVerum (by decide)
  have hrow := walkTable_isSemiformulaVerum hW
  rw [hk] at hstep hlen hrow
  have hes : ∀ e ∈ [wn, wp], IsSemiterm LAct 0 e ∧ termLen LAct e ≤ E := List.forall_mem_cons.mpr ⟨⟨hwn, hEwn⟩, List.forall_mem_cons.mpr ⟨⟨hwp, hEwp⟩, List.forall_mem_nil _⟩⟩
  have hinst := inst_isSemiformulaVerum hwn hwp
  rw [hstep]
  rw [show (?[wn, wp] : V) = vecOf [wn, wp] from rfl]
  refine ⟨stepOK_useHorn htbl [wn, wp] row_isSemiformulaVerum_as hΓ hlen hrow.1 hrow.2 (by exact_mod_cast (by decide : 2 ≤ 8))
    (by rw [show row_isSemiformulaVerum_as.length = 1 from rfl]; exact_mod_cast (by decide : 1 ≤ 8)) hes ?_, by simp, ?_⟩
  · exact neg_mem_of_map hinst.1 (List.forall_mem_cons.mpr ⟨hmem0, List.forall_mem_nil _⟩)
  · rw [ctxAfter_useHorn [wn, wp] row_isSemiformulaVerum_as isSemiformula_isSemiformulaVerum_c (fun e he ↦ (hes e he).1), hinst.2]

/-- Row `isSemiformulaSigmaPi` as a step. -/
lemma ok_isSemiformulaSigmaPi {tbl N E Γ W : V} {wn : V} {wp : V} (htbl : TableOK tbl N) (hW : WalkTable tbl) (hWp : W = walkPieces)
    (hΓ : IsFormulaSet LAct Γ) (hwn : IsSemiterm LAct 0 wn) (hEwn : termLen LAct wn ≤ E) (hwp : IsSemiterm LAct 0 wp) (hEwp : termLen LAct wp ≤ E) (hmem0 : neg LAct (sigmaFact wn wp) ∈ Γ) :
    StepOK tbl E ((8 : ℕ) : V) Γ (mkStep W 21 ?[wn, wp]) ∧ sTag (mkStep W 21 ?[wn, wp]) = 0 ∧
    ctxAfter Γ (mkStep W 21 ?[wn, wp]) = insert (neg LAct (piFact wn wp)) Γ := by
  subst hWp
  have hk : ((rIdx_isSemiformulaSigmaPi : ℕ) : V) = (21 : V) := by simp [rIdx_isSemiformulaSigmaPi]
  have hstep := mkStep_isSemiformulaSigmaPi (V := V) ?[wn, wp]
  have hlen := walkTable_len hW rIdx_isSemiformulaSigmaPi (by decide)
  have hrow := walkTable_isSemiformulaSigmaPi hW
  rw [hk] at hstep hlen hrow
  have hes : ∀ e ∈ [wn, wp], IsSemiterm LAct 0 e ∧ termLen LAct e ≤ E := List.forall_mem_cons.mpr ⟨⟨hwn, hEwn⟩, List.forall_mem_cons.mpr ⟨⟨hwp, hEwp⟩, List.forall_mem_nil _⟩⟩
  have hinst := inst_isSemiformulaSigmaPi hwn hwp
  rw [hstep]
  rw [show (?[wn, wp] : V) = vecOf [wn, wp] from rfl]
  refine ⟨stepOK_useHorn htbl [wn, wp] row_isSemiformulaSigmaPi_as hΓ hlen hrow.1 hrow.2 (by exact_mod_cast (by decide : 2 ≤ 8))
    (by rw [show row_isSemiformulaSigmaPi_as.length = 1 from rfl]; exact_mod_cast (by decide : 1 ≤ 8)) hes ?_, by simp, ?_⟩
  · exact neg_mem_of_map hinst.1 (List.forall_mem_cons.mpr ⟨hmem0, List.forall_mem_nil _⟩)
  · rw [ctxAfter_useHorn [wn, wp] row_isSemiformulaSigmaPi_as isSemiformula_isSemiformulaSigmaPi_c (fun e he ↦ (hes e he).1), hinst.2]

/-- Row `isSemiformulaFalsum` as a step. -/
lemma ok_isSemiformulaFalsum {tbl N E Γ W : V} {wn : V} {wp : V} (htbl : TableOK tbl N) (hW : WalkTable tbl) (hWp : W = walkPieces)
    (hΓ : IsFormulaSet LAct Γ) (hwn : IsSemiterm LAct 0 wn) (hEwn : termLen LAct wn ≤ E) (hwp : IsSemiterm LAct 0 wp) (hEwp : termLen LAct wp ≤ E) (hmem0 : neg LAct (falsumFact wp) ∈ Γ) :
    StepOK tbl E ((8 : ℕ) : V) Γ (mkStep W 23 ?[wn, wp]) ∧ sTag (mkStep W 23 ?[wn, wp]) = 0 ∧
    ctxAfter Γ (mkStep W 23 ?[wn, wp]) = insert (neg LAct (sigmaFact wn wp)) Γ := by
  subst hWp
  have hk : ((rIdx_isSemiformulaFalsum : ℕ) : V) = (23 : V) := by simp [rIdx_isSemiformulaFalsum]
  have hstep := mkStep_isSemiformulaFalsum (V := V) ?[wn, wp]
  have hlen := walkTable_len hW rIdx_isSemiformulaFalsum (by decide)
  have hrow := walkTable_isSemiformulaFalsum hW
  rw [hk] at hstep hlen hrow
  have hes : ∀ e ∈ [wn, wp], IsSemiterm LAct 0 e ∧ termLen LAct e ≤ E := List.forall_mem_cons.mpr ⟨⟨hwn, hEwn⟩, List.forall_mem_cons.mpr ⟨⟨hwp, hEwp⟩, List.forall_mem_nil _⟩⟩
  have hinst := inst_isSemiformulaFalsum hwn hwp
  rw [hstep]
  rw [show (?[wn, wp] : V) = vecOf [wn, wp] from rfl]
  refine ⟨stepOK_useHorn htbl [wn, wp] row_isSemiformulaFalsum_as hΓ hlen hrow.1 hrow.2 (by exact_mod_cast (by decide : 2 ≤ 8))
    (by rw [show row_isSemiformulaFalsum_as.length = 1 from rfl]; exact_mod_cast (by decide : 1 ≤ 8)) hes ?_, by simp, ?_⟩
  · exact neg_mem_of_map hinst.1 (List.forall_mem_cons.mpr ⟨hmem0, List.forall_mem_nil _⟩)
  · rw [ctxAfter_useHorn [wn, wp] row_isSemiformulaFalsum_as isSemiformula_isSemiformulaFalsum_c (fun e he ↦ (hes e he).1), hinst.2]

/-- Row `isSemiformulaAnd` as a step. -/
lemma ok_isSemiformulaAnd {tbl N E Γ W : V} {wn : V} {wp : V} {wq : V} {wr : V} (htbl : TableOK tbl N) (hW : WalkTable tbl) (hWp : W = walkPieces)
    (hΓ : IsFormulaSet LAct Γ) (hwn : IsSemiterm LAct 0 wn) (hEwn : termLen LAct wn ≤ E) (hwp : IsSemiterm LAct 0 wp) (hEwp : termLen LAct wp ≤ E) (hwq : IsSemiterm LAct 0 wq) (hEwq : termLen LAct wq ≤ E) (hwr : IsSemiterm LAct 0 wr) (hEwr : termLen LAct wr ≤ E) (hmem0 : neg LAct (piFact wn wp) ∈ Γ) (hmem1 : neg LAct (piFact wn wq) ∈ Γ) (hmem2 : neg LAct (andFact wr wp wq) ∈ Γ) :
    StepOK tbl E ((8 : ℕ) : V) Γ (mkStep W 25 ?[wn, wp, wq, wr]) ∧ sTag (mkStep W 25 ?[wn, wp, wq, wr]) = 0 ∧
    ctxAfter Γ (mkStep W 25 ?[wn, wp, wq, wr]) = insert (neg LAct (sigmaFact wn wr)) Γ := by
  subst hWp
  have hk : ((rIdx_isSemiformulaAnd : ℕ) : V) = (25 : V) := by simp [rIdx_isSemiformulaAnd]
  have hstep := mkStep_isSemiformulaAnd (V := V) ?[wn, wp, wq, wr]
  have hlen := walkTable_len hW rIdx_isSemiformulaAnd (by decide)
  have hrow := walkTable_isSemiformulaAnd hW
  rw [hk] at hstep hlen hrow
  have hes : ∀ e ∈ [wn, wp, wq, wr], IsSemiterm LAct 0 e ∧ termLen LAct e ≤ E := List.forall_mem_cons.mpr ⟨⟨hwn, hEwn⟩, List.forall_mem_cons.mpr ⟨⟨hwp, hEwp⟩, List.forall_mem_cons.mpr ⟨⟨hwq, hEwq⟩, List.forall_mem_cons.mpr ⟨⟨hwr, hEwr⟩, List.forall_mem_nil _⟩⟩⟩⟩
  have hinst := inst_isSemiformulaAnd hwn hwp hwq hwr
  rw [hstep]
  rw [show (?[wn, wp, wq, wr] : V) = vecOf [wn, wp, wq, wr] from rfl]
  refine ⟨stepOK_useHorn htbl [wn, wp, wq, wr] row_isSemiformulaAnd_as hΓ hlen hrow.1 hrow.2 (by exact_mod_cast (by decide : 4 ≤ 8))
    (by rw [show row_isSemiformulaAnd_as.length = 3 from rfl]; exact_mod_cast (by decide : 3 ≤ 8)) hes ?_, by simp, ?_⟩
  · exact neg_mem_of_map hinst.1 (List.forall_mem_cons.mpr ⟨hmem0, List.forall_mem_cons.mpr ⟨hmem1, List.forall_mem_cons.mpr ⟨hmem2, List.forall_mem_nil _⟩⟩⟩)
  · rw [ctxAfter_useHorn [wn, wp, wq, wr] row_isSemiformulaAnd_as isSemiformula_isSemiformulaAnd_c (fun e he ↦ (hes e he).1), hinst.2]

/-- Row `isSemiformulaOr` as a step. -/
lemma ok_isSemiformulaOr {tbl N E Γ W : V} {wn : V} {wp : V} {wq : V} {wr : V} (htbl : TableOK tbl N) (hW : WalkTable tbl) (hWp : W = walkPieces)
    (hΓ : IsFormulaSet LAct Γ) (hwn : IsSemiterm LAct 0 wn) (hEwn : termLen LAct wn ≤ E) (hwp : IsSemiterm LAct 0 wp) (hEwp : termLen LAct wp ≤ E) (hwq : IsSemiterm LAct 0 wq) (hEwq : termLen LAct wq ≤ E) (hwr : IsSemiterm LAct 0 wr) (hEwr : termLen LAct wr ≤ E) (hmem0 : neg LAct (piFact wn wp) ∈ Γ) (hmem1 : neg LAct (piFact wn wq) ∈ Γ) (hmem2 : neg LAct (orFact wr wp wq) ∈ Γ) :
    StepOK tbl E ((8 : ℕ) : V) Γ (mkStep W 27 ?[wn, wp, wq, wr]) ∧ sTag (mkStep W 27 ?[wn, wp, wq, wr]) = 0 ∧
    ctxAfter Γ (mkStep W 27 ?[wn, wp, wq, wr]) = insert (neg LAct (sigmaFact wn wr)) Γ := by
  subst hWp
  have hk : ((rIdx_isSemiformulaOr : ℕ) : V) = (27 : V) := by simp [rIdx_isSemiformulaOr]
  have hstep := mkStep_isSemiformulaOr (V := V) ?[wn, wp, wq, wr]
  have hlen := walkTable_len hW rIdx_isSemiformulaOr (by decide)
  have hrow := walkTable_isSemiformulaOr hW
  rw [hk] at hstep hlen hrow
  have hes : ∀ e ∈ [wn, wp, wq, wr], IsSemiterm LAct 0 e ∧ termLen LAct e ≤ E := List.forall_mem_cons.mpr ⟨⟨hwn, hEwn⟩, List.forall_mem_cons.mpr ⟨⟨hwp, hEwp⟩, List.forall_mem_cons.mpr ⟨⟨hwq, hEwq⟩, List.forall_mem_cons.mpr ⟨⟨hwr, hEwr⟩, List.forall_mem_nil _⟩⟩⟩⟩
  have hinst := inst_isSemiformulaOr hwn hwp hwq hwr
  rw [hstep]
  rw [show (?[wn, wp, wq, wr] : V) = vecOf [wn, wp, wq, wr] from rfl]
  refine ⟨stepOK_useHorn htbl [wn, wp, wq, wr] row_isSemiformulaOr_as hΓ hlen hrow.1 hrow.2 (by exact_mod_cast (by decide : 4 ≤ 8))
    (by rw [show row_isSemiformulaOr_as.length = 3 from rfl]; exact_mod_cast (by decide : 3 ≤ 8)) hes ?_, by simp, ?_⟩
  · exact neg_mem_of_map hinst.1 (List.forall_mem_cons.mpr ⟨hmem0, List.forall_mem_cons.mpr ⟨hmem1, List.forall_mem_cons.mpr ⟨hmem2, List.forall_mem_nil _⟩⟩⟩)
  · rw [ctxAfter_useHorn [wn, wp, wq, wr] row_isSemiformulaOr_as isSemiformula_isSemiformulaOr_c (fun e he ↦ (hes e he).1), hinst.2]

/-- Row `isSemiformulaAll` as a step. -/
lemma ok_isSemiformulaAll {tbl N E Γ W : V} {wn : V} {wp : V} {wq : V} (htbl : TableOK tbl N) (hW : WalkTable tbl) (hWp : W = walkPieces)
    (hΓ : IsFormulaSet LAct Γ) (hwn : IsSemiterm LAct 0 wn) (hEwn : termLen LAct wn ≤ E) (hwp : IsSemiterm LAct 0 wp) (hEwp : termLen LAct wp ≤ E) (hwq : IsSemiterm LAct 0 wq) (hEwq : termLen LAct wq ≤ E) (hmem0 : neg LAct (piFact (wn ^+ (𝟏 : V)) wp) ∈ Γ) (hmem1 : neg LAct (allFact wq wp) ∈ Γ) :
    StepOK tbl E ((8 : ℕ) : V) Γ (mkStep W 29 ?[wn, wp, wq]) ∧ sTag (mkStep W 29 ?[wn, wp, wq]) = 0 ∧
    ctxAfter Γ (mkStep W 29 ?[wn, wp, wq]) = insert (neg LAct (sigmaFact wn wq)) Γ := by
  subst hWp
  have hk : ((rIdx_isSemiformulaAll : ℕ) : V) = (29 : V) := by simp [rIdx_isSemiformulaAll]
  have hstep := mkStep_isSemiformulaAll (V := V) ?[wn, wp, wq]
  have hlen := walkTable_len hW rIdx_isSemiformulaAll (by decide)
  have hrow := walkTable_isSemiformulaAll hW
  rw [hk] at hstep hlen hrow
  have hes : ∀ e ∈ [wn, wp, wq], IsSemiterm LAct 0 e ∧ termLen LAct e ≤ E := List.forall_mem_cons.mpr ⟨⟨hwn, hEwn⟩, List.forall_mem_cons.mpr ⟨⟨hwp, hEwp⟩, List.forall_mem_cons.mpr ⟨⟨hwq, hEwq⟩, List.forall_mem_nil _⟩⟩⟩
  have hinst := inst_isSemiformulaAll hwn hwp hwq
  rw [hstep]
  rw [show (?[wn, wp, wq] : V) = vecOf [wn, wp, wq] from rfl]
  refine ⟨stepOK_useHorn htbl [wn, wp, wq] row_isSemiformulaAll_as hΓ hlen hrow.1 hrow.2 (by exact_mod_cast (by decide : 3 ≤ 8))
    (by rw [show row_isSemiformulaAll_as.length = 2 from rfl]; exact_mod_cast (by decide : 2 ≤ 8)) hes ?_, by simp, ?_⟩
  · exact neg_mem_of_map hinst.1 (List.forall_mem_cons.mpr ⟨hmem0, List.forall_mem_cons.mpr ⟨hmem1, List.forall_mem_nil _⟩⟩)
  · rw [ctxAfter_useHorn [wn, wp, wq] row_isSemiformulaAll_as isSemiformula_isSemiformulaAll_c (fun e he ↦ (hes e he).1), hinst.2]

/-- Row `isSemiformulaExs` as a step. -/
lemma ok_isSemiformulaExs {tbl N E Γ W : V} {wn : V} {wp : V} {wq : V} (htbl : TableOK tbl N) (hW : WalkTable tbl) (hWp : W = walkPieces)
    (hΓ : IsFormulaSet LAct Γ) (hwn : IsSemiterm LAct 0 wn) (hEwn : termLen LAct wn ≤ E) (hwp : IsSemiterm LAct 0 wp) (hEwp : termLen LAct wp ≤ E) (hwq : IsSemiterm LAct 0 wq) (hEwq : termLen LAct wq ≤ E) (hmem0 : neg LAct (piFact (wn ^+ (𝟏 : V)) wp) ∈ Γ) (hmem1 : neg LAct (exsFact wq wp) ∈ Γ) :
    StepOK tbl E ((8 : ℕ) : V) Γ (mkStep W 31 ?[wn, wp, wq]) ∧ sTag (mkStep W 31 ?[wn, wp, wq]) = 0 ∧
    ctxAfter Γ (mkStep W 31 ?[wn, wp, wq]) = insert (neg LAct (sigmaFact wn wq)) Γ := by
  subst hWp
  have hk : ((rIdx_isSemiformulaExs : ℕ) : V) = (31 : V) := by simp [rIdx_isSemiformulaExs]
  have hstep := mkStep_isSemiformulaExs (V := V) ?[wn, wp, wq]
  have hlen := walkTable_len hW rIdx_isSemiformulaExs (by decide)
  have hrow := walkTable_isSemiformulaExs hW
  rw [hk] at hstep hlen hrow
  have hes : ∀ e ∈ [wn, wp, wq], IsSemiterm LAct 0 e ∧ termLen LAct e ≤ E := List.forall_mem_cons.mpr ⟨⟨hwn, hEwn⟩, List.forall_mem_cons.mpr ⟨⟨hwp, hEwp⟩, List.forall_mem_cons.mpr ⟨⟨hwq, hEwq⟩, List.forall_mem_nil _⟩⟩⟩
  have hinst := inst_isSemiformulaExs hwn hwp hwq
  rw [hstep]
  rw [show (?[wn, wp, wq] : V) = vecOf [wn, wp, wq] from rfl]
  refine ⟨stepOK_useHorn htbl [wn, wp, wq] row_isSemiformulaExs_as hΓ hlen hrow.1 hrow.2 (by exact_mod_cast (by decide : 3 ≤ 8))
    (by rw [show row_isSemiformulaExs_as.length = 2 from rfl]; exact_mod_cast (by decide : 2 ≤ 8)) hes ?_, by simp, ?_⟩
  · exact neg_mem_of_map hinst.1 (List.forall_mem_cons.mpr ⟨hmem0, List.forall_mem_cons.mpr ⟨hmem1, List.forall_mem_nil _⟩⟩)
  · rw [ctxAfter_useHorn [wn, wp, wq] row_isSemiformulaExs_as isSemiformula_isSemiformulaExs_c (fun e he ↦ (hes e he).1), hinst.2]

/-- Row `isSemiformulaRel` as a step. -/
lemma ok_isSemiformulaRel {tbl N E Γ W : V} {wn : V} {wk : V} {wR : V} {wv : V} {wp : V} (htbl : TableOK tbl N) (hW : WalkTable tbl) (hWp : W = walkPieces)
    (hΓ : IsFormulaSet LAct Γ) (hwn : IsSemiterm LAct 0 wn) (hEwn : termLen LAct wn ≤ E) (hwk : IsSemiterm LAct 0 wk) (hEwk : termLen LAct wk ≤ E) (hwR : IsSemiterm LAct 0 wR) (hEwR : termLen LAct wR ≤ E) (hwv : IsSemiterm LAct 0 wv) (hEwv : termLen LAct wv ≤ E) (hwp : IsSemiterm LAct 0 wp) (hEwp : termLen LAct wp ≤ E) (hmem0 : neg LAct (isRelFact wk wR) ∈ Γ) (hmem1 : neg LAct (tvPiFact wk wn wv) ∈ Γ) (hmem2 : neg LAct (relFact wp wk wR wv) ∈ Γ) :
    StepOK tbl E ((8 : ℕ) : V) Γ (mkStep W 33 ?[wn, wk, wR, wv, wp]) ∧ sTag (mkStep W 33 ?[wn, wk, wR, wv, wp]) = 0 ∧
    ctxAfter Γ (mkStep W 33 ?[wn, wk, wR, wv, wp]) = insert (neg LAct (sigmaFact wn wp)) Γ := by
  subst hWp
  have hk : ((rIdx_isSemiformulaRel : ℕ) : V) = (33 : V) := by simp [rIdx_isSemiformulaRel]
  have hstep := mkStep_isSemiformulaRel (V := V) ?[wn, wk, wR, wv, wp]
  have hlen := walkTable_len hW rIdx_isSemiformulaRel (by decide)
  have hrow := walkTable_isSemiformulaRel hW
  rw [hk] at hstep hlen hrow
  have hes : ∀ e ∈ [wn, wk, wR, wv, wp], IsSemiterm LAct 0 e ∧ termLen LAct e ≤ E := List.forall_mem_cons.mpr ⟨⟨hwn, hEwn⟩, List.forall_mem_cons.mpr ⟨⟨hwk, hEwk⟩, List.forall_mem_cons.mpr ⟨⟨hwR, hEwR⟩, List.forall_mem_cons.mpr ⟨⟨hwv, hEwv⟩, List.forall_mem_cons.mpr ⟨⟨hwp, hEwp⟩, List.forall_mem_nil _⟩⟩⟩⟩⟩
  have hinst := inst_isSemiformulaRel hwn hwk hwR hwv hwp
  rw [hstep]
  rw [show (?[wn, wk, wR, wv, wp] : V) = vecOf [wn, wk, wR, wv, wp] from rfl]
  refine ⟨stepOK_useHorn htbl [wn, wk, wR, wv, wp] row_isSemiformulaRel_as hΓ hlen hrow.1 hrow.2 (by exact_mod_cast (by decide : 5 ≤ 8))
    (by rw [show row_isSemiformulaRel_as.length = 3 from rfl]; exact_mod_cast (by decide : 3 ≤ 8)) hes ?_, by simp, ?_⟩
  · exact neg_mem_of_map hinst.1 (List.forall_mem_cons.mpr ⟨hmem0, List.forall_mem_cons.mpr ⟨hmem1, List.forall_mem_cons.mpr ⟨hmem2, List.forall_mem_nil _⟩⟩⟩)
  · rw [ctxAfter_useHorn [wn, wk, wR, wv, wp] row_isSemiformulaRel_as isSemiformula_isSemiformulaRel_c (fun e he ↦ (hes e he).1), hinst.2]

/-- Row `isSemiformulaNRel` as a step. -/
lemma ok_isSemiformulaNRel {tbl N E Γ W : V} {wn : V} {wk : V} {wR : V} {wv : V} {wp : V} (htbl : TableOK tbl N) (hW : WalkTable tbl) (hWp : W = walkPieces)
    (hΓ : IsFormulaSet LAct Γ) (hwn : IsSemiterm LAct 0 wn) (hEwn : termLen LAct wn ≤ E) (hwk : IsSemiterm LAct 0 wk) (hEwk : termLen LAct wk ≤ E) (hwR : IsSemiterm LAct 0 wR) (hEwR : termLen LAct wR ≤ E) (hwv : IsSemiterm LAct 0 wv) (hEwv : termLen LAct wv ≤ E) (hwp : IsSemiterm LAct 0 wp) (hEwp : termLen LAct wp ≤ E) (hmem0 : neg LAct (isRelFact wk wR) ∈ Γ) (hmem1 : neg LAct (tvPiFact wk wn wv) ∈ Γ) (hmem2 : neg LAct (nrelFact wp wk wR wv) ∈ Γ) :
    StepOK tbl E ((8 : ℕ) : V) Γ (mkStep W 35 ?[wn, wk, wR, wv, wp]) ∧ sTag (mkStep W 35 ?[wn, wk, wR, wv, wp]) = 0 ∧
    ctxAfter Γ (mkStep W 35 ?[wn, wk, wR, wv, wp]) = insert (neg LAct (sigmaFact wn wp)) Γ := by
  subst hWp
  have hk : ((rIdx_isSemiformulaNRel : ℕ) : V) = (35 : V) := by simp [rIdx_isSemiformulaNRel]
  have hstep := mkStep_isSemiformulaNRel (V := V) ?[wn, wk, wR, wv, wp]
  have hlen := walkTable_len hW rIdx_isSemiformulaNRel (by decide)
  have hrow := walkTable_isSemiformulaNRel hW
  rw [hk] at hstep hlen hrow
  have hes : ∀ e ∈ [wn, wk, wR, wv, wp], IsSemiterm LAct 0 e ∧ termLen LAct e ≤ E := List.forall_mem_cons.mpr ⟨⟨hwn, hEwn⟩, List.forall_mem_cons.mpr ⟨⟨hwk, hEwk⟩, List.forall_mem_cons.mpr ⟨⟨hwR, hEwR⟩, List.forall_mem_cons.mpr ⟨⟨hwv, hEwv⟩, List.forall_mem_cons.mpr ⟨⟨hwp, hEwp⟩, List.forall_mem_nil _⟩⟩⟩⟩⟩
  have hinst := inst_isSemiformulaNRel hwn hwk hwR hwv hwp
  rw [hstep]
  rw [show (?[wn, wk, wR, wv, wp] : V) = vecOf [wn, wk, wR, wv, wp] from rfl]
  refine ⟨stepOK_useHorn htbl [wn, wk, wR, wv, wp] row_isSemiformulaNRel_as hΓ hlen hrow.1 hrow.2 (by exact_mod_cast (by decide : 5 ≤ 8))
    (by rw [show row_isSemiformulaNRel_as.length = 3 from rfl]; exact_mod_cast (by decide : 3 ≤ 8)) hes ?_, by simp, ?_⟩
  · exact neg_mem_of_map hinst.1 (List.forall_mem_cons.mpr ⟨hmem0, List.forall_mem_cons.mpr ⟨hmem1, List.forall_mem_cons.mpr ⟨hmem2, List.forall_mem_nil _⟩⟩⟩)
  · rw [ctxAfter_useHorn [wn, wk, wR, wv, wp] row_isSemiformulaNRel_as isSemiformula_isSemiformulaNRel_c (fun e he ↦ (hes e he).1), hinst.2]

/-- Row `isRelConst_eq` as a step. -/
lemma ok_isRelConst_eq {tbl N E Γ W : V}  (htbl : TableOK tbl N) (hW : WalkTable tbl) (hWp : W = walkPieces)
    (hΓ : IsFormulaSet LAct Γ)   :
    StepOK tbl E ((8 : ℕ) : V) Γ (mkStep W 36 0) ∧ sTag (mkStep W 36 0) = 0 ∧
    ctxAfter Γ (mkStep W 36 0) = insert (neg LAct (isRelFact (cT 2) (cT 0))) Γ := by
  subst hWp
  have hk : ((rIdx_isRelConst_eq : ℕ) : V) = (36 : V) := by simp [rIdx_isRelConst_eq]
  have hstep := mkStep_isRelConst_eq (V := V) 0
  have hlen := walkTable_len hW rIdx_isRelConst_eq (by decide)
  have hrow := walkTable_isRelConst_eq hW
  rw [hk] at hstep hlen hrow
  have hes : ∀ e ∈ ([] : List V), IsSemiterm LAct 0 e ∧ termLen LAct e ≤ E := List.forall_mem_nil _
  have hinst := inst_isRelConst_eq (V := V)
  rw [hstep]
  refine ⟨stepOK_useHorn htbl ([] : List V) row_isRelConst_eq_as hΓ hlen hrow.1 hrow.2 (by exact_mod_cast (by decide : 0 ≤ 8))
    (by rw [show row_isRelConst_eq_as.length = 0 from rfl]; exact_mod_cast (by decide : 0 ≤ 8)) hes ?_, by simp, ?_⟩
  · exact neg_mem_of_map hinst.1 (List.forall_mem_nil _)
  · show ctxAfter Γ (sUseHorn 36 (vecOf ([] : List V)) (vecOf row_isRelConst_eq_as) row_isRelConst_eq_c) = _
    rw [ctxAfter_useHorn ([] : List V) row_isRelConst_eq_as isSemiformula_isRelConst_eq_c (fun e he ↦ (hes e he).1), hinst.2]

/-- Row `isRelConst_lt` as a step. -/
lemma ok_isRelConst_lt {tbl N E Γ W : V}  (htbl : TableOK tbl N) (hW : WalkTable tbl) (hWp : W = walkPieces)
    (hΓ : IsFormulaSet LAct Γ)   :
    StepOK tbl E ((8 : ℕ) : V) Γ (mkStep W 37 0) ∧ sTag (mkStep W 37 0) = 0 ∧
    ctxAfter Γ (mkStep W 37 0) = insert (neg LAct (isRelFact (cT 2) (cT 1))) Γ := by
  subst hWp
  have hk : ((rIdx_isRelConst_lt : ℕ) : V) = (37 : V) := by simp [rIdx_isRelConst_lt]
  have hstep := mkStep_isRelConst_lt (V := V) 0
  have hlen := walkTable_len hW rIdx_isRelConst_lt (by decide)
  have hrow := walkTable_isRelConst_lt hW
  rw [hk] at hstep hlen hrow
  have hes : ∀ e ∈ ([] : List V), IsSemiterm LAct 0 e ∧ termLen LAct e ≤ E := List.forall_mem_nil _
  have hinst := inst_isRelConst_lt (V := V)
  rw [hstep]
  refine ⟨stepOK_useHorn htbl ([] : List V) row_isRelConst_lt_as hΓ hlen hrow.1 hrow.2 (by exact_mod_cast (by decide : 0 ≤ 8))
    (by rw [show row_isRelConst_lt_as.length = 0 from rfl]; exact_mod_cast (by decide : 0 ≤ 8)) hes ?_, by simp, ?_⟩
  · exact neg_mem_of_map hinst.1 (List.forall_mem_nil _)
  · show ctxAfter Γ (sUseHorn 37 (vecOf ([] : List V)) (vecOf row_isRelConst_lt_as) row_isRelConst_lt_c) = _
    rw [ctxAfter_useHorn ([] : List V) row_isRelConst_lt_as isSemiformula_isRelConst_lt_c (fun e he ↦ (hes e he).1), hinst.2]

/-- Totality row `qqVerumTotal` as a step: the new eigenvariable `&0`, the context shifted. -/
lemma ok_qqVerumTotal {tbl N E Γ W : V}  (htbl : TableOK tbl N) (hW : WalkTable tbl) (hWp : W = walkPieces)
    (hΓ : IsFormulaSet LAct Γ)  :
    StepOK tbl E ((8 : ℕ) : V) Γ (mkStep W 19 0) ∧ sTag (mkStep W 19 0) = 2 ∧
    ctxAfter Γ (mkStep W 19 0) = insert (neg LAct (verumFact (^&((0 : ℕ) : V)))) (setShift LAct Γ) := by
  subst hWp
  have hk : ((rIdx_qqVerumTotal : ℕ) : V) = (19 : V) := by simp [rIdx_qqVerumTotal]
  have hstep := mkStep_qqVerumTotal (V := V) 0
  have hlen := walkTable_len hW rIdx_qqVerumTotal (by decide)
  have hrow := walkTable_qqVerumTotal hW
  rw [hk] at hstep hlen hrow
  have hes : ∀ e ∈ ([] : List V), IsSemiterm LAct 0 e ∧ termLen LAct e ≤ E := List.forall_mem_nil _
  have hinst := inst_qqVerumTotal (V := V)
  rw [hstep]
  refine ⟨stepOK_introFact htbl ([] : List V) row_qqVerumTotal_as hΓ hlen hrow.1 hrow.2 (by exact_mod_cast (by decide : 0 ≤ 8))
    (by rw [show row_qqVerumTotal_as.length = 0 from rfl]; exact_mod_cast (by decide : 0 ≤ 8)) hes ?_, by simp, ?_⟩
  · exact neg_mem_of_map hinst.1 (List.forall_mem_nil _)
  · show ctxAfter Γ (sIntroFact 19 (vecOf ([] : List V)) (vecOf row_qqVerumTotal_as) row_qqVerumTotal_R) = _
    rw [ctxAfter_introFact ([] : List V) row_qqVerumTotal_as (by rw [← Nat.cast_succ]; exact isSemiformula_qqVerumTotal_R) (fun e he ↦ (hes e he).1),
      show row_qqVerumTotal_R = row_qqVerumTotal_body from rfl, ← freeIter_one, hinst.2]

/-- Totality row `qqFalsumTotal` as a step: the new eigenvariable `&0`, the context shifted. -/
lemma ok_qqFalsumTotal {tbl N E Γ W : V}  (htbl : TableOK tbl N) (hW : WalkTable tbl) (hWp : W = walkPieces)
    (hΓ : IsFormulaSet LAct Γ)  :
    StepOK tbl E ((8 : ℕ) : V) Γ (mkStep W 22 0) ∧ sTag (mkStep W 22 0) = 2 ∧
    ctxAfter Γ (mkStep W 22 0) = insert (neg LAct (falsumFact (^&((0 : ℕ) : V)))) (setShift LAct Γ) := by
  subst hWp
  have hk : ((rIdx_qqFalsumTotal : ℕ) : V) = (22 : V) := by simp [rIdx_qqFalsumTotal]
  have hstep := mkStep_qqFalsumTotal (V := V) 0
  have hlen := walkTable_len hW rIdx_qqFalsumTotal (by decide)
  have hrow := walkTable_qqFalsumTotal hW
  rw [hk] at hstep hlen hrow
  have hes : ∀ e ∈ ([] : List V), IsSemiterm LAct 0 e ∧ termLen LAct e ≤ E := List.forall_mem_nil _
  have hinst := inst_qqFalsumTotal (V := V)
  rw [hstep]
  refine ⟨stepOK_introFact htbl ([] : List V) row_qqFalsumTotal_as hΓ hlen hrow.1 hrow.2 (by exact_mod_cast (by decide : 0 ≤ 8))
    (by rw [show row_qqFalsumTotal_as.length = 0 from rfl]; exact_mod_cast (by decide : 0 ≤ 8)) hes ?_, by simp, ?_⟩
  · exact neg_mem_of_map hinst.1 (List.forall_mem_nil _)
  · show ctxAfter Γ (sIntroFact 22 (vecOf ([] : List V)) (vecOf row_qqFalsumTotal_as) row_qqFalsumTotal_R) = _
    rw [ctxAfter_introFact ([] : List V) row_qqFalsumTotal_as (by rw [← Nat.cast_succ]; exact isSemiformula_qqFalsumTotal_R) (fun e he ↦ (hes e he).1),
      show row_qqFalsumTotal_R = row_qqFalsumTotal_body from rfl, ← freeIter_one, hinst.2]

/-- Totality row `qqAndTotal` as a step: the new eigenvariable `&0`, the context shifted. -/
lemma ok_qqAndTotal {tbl N E Γ W : V} {wp : V} {wq : V} (htbl : TableOK tbl N) (hW : WalkTable tbl) (hWp : W = walkPieces)
    (hΓ : IsFormulaSet LAct Γ) (hwp : IsSemiterm LAct 0 wp) (hEwp : termLen LAct wp ≤ E) (hwq : IsSemiterm LAct 0 wq) (hEwq : termLen LAct wq ≤ E) :
    StepOK tbl E ((8 : ℕ) : V) Γ (mkStep W 24 ?[wp, wq]) ∧ sTag (mkStep W 24 ?[wp, wq]) = 2 ∧
    ctxAfter Γ (mkStep W 24 ?[wp, wq]) = insert (neg LAct (andFact (^&((0 : ℕ) : V)) (termShift LAct wp) (termShift LAct wq))) (setShift LAct Γ) := by
  subst hWp
  have hk : ((rIdx_qqAndTotal : ℕ) : V) = (24 : V) := by simp [rIdx_qqAndTotal]
  have hstep := mkStep_qqAndTotal (V := V) ?[wp, wq]
  have hlen := walkTable_len hW rIdx_qqAndTotal (by decide)
  have hrow := walkTable_qqAndTotal hW
  rw [hk] at hstep hlen hrow
  have hes : ∀ e ∈ [wp, wq], IsSemiterm LAct 0 e ∧ termLen LAct e ≤ E := List.forall_mem_cons.mpr ⟨⟨hwp, hEwp⟩, List.forall_mem_cons.mpr ⟨⟨hwq, hEwq⟩, List.forall_mem_nil _⟩⟩
  have hinst := inst_qqAndTotal hwp hwq
  rw [hstep, show (?[wp, wq] : V) = vecOf [wp, wq] from rfl]
  refine ⟨stepOK_introFact htbl [wp, wq] row_qqAndTotal_as hΓ hlen hrow.1 hrow.2 (by exact_mod_cast (by decide : 2 ≤ 8))
    (by rw [show row_qqAndTotal_as.length = 0 from rfl]; exact_mod_cast (by decide : 0 ≤ 8)) hes ?_, by simp, ?_⟩
  · exact neg_mem_of_map hinst.1 (List.forall_mem_nil _)
  · rw [ctxAfter_introFact [wp, wq] row_qqAndTotal_as (by rw [← Nat.cast_succ]; exact isSemiformula_qqAndTotal_R) (fun e he ↦ (hes e he).1),
      show row_qqAndTotal_R = row_qqAndTotal_body from rfl, ← freeIter_one, hinst.2]

/-- Totality row `qqOrTotal` as a step: the new eigenvariable `&0`, the context shifted. -/
lemma ok_qqOrTotal {tbl N E Γ W : V} {wp : V} {wq : V} (htbl : TableOK tbl N) (hW : WalkTable tbl) (hWp : W = walkPieces)
    (hΓ : IsFormulaSet LAct Γ) (hwp : IsSemiterm LAct 0 wp) (hEwp : termLen LAct wp ≤ E) (hwq : IsSemiterm LAct 0 wq) (hEwq : termLen LAct wq ≤ E) :
    StepOK tbl E ((8 : ℕ) : V) Γ (mkStep W 26 ?[wp, wq]) ∧ sTag (mkStep W 26 ?[wp, wq]) = 2 ∧
    ctxAfter Γ (mkStep W 26 ?[wp, wq]) = insert (neg LAct (orFact (^&((0 : ℕ) : V)) (termShift LAct wp) (termShift LAct wq))) (setShift LAct Γ) := by
  subst hWp
  have hk : ((rIdx_qqOrTotal : ℕ) : V) = (26 : V) := by simp [rIdx_qqOrTotal]
  have hstep := mkStep_qqOrTotal (V := V) ?[wp, wq]
  have hlen := walkTable_len hW rIdx_qqOrTotal (by decide)
  have hrow := walkTable_qqOrTotal hW
  rw [hk] at hstep hlen hrow
  have hes : ∀ e ∈ [wp, wq], IsSemiterm LAct 0 e ∧ termLen LAct e ≤ E := List.forall_mem_cons.mpr ⟨⟨hwp, hEwp⟩, List.forall_mem_cons.mpr ⟨⟨hwq, hEwq⟩, List.forall_mem_nil _⟩⟩
  have hinst := inst_qqOrTotal hwp hwq
  rw [hstep, show (?[wp, wq] : V) = vecOf [wp, wq] from rfl]
  refine ⟨stepOK_introFact htbl [wp, wq] row_qqOrTotal_as hΓ hlen hrow.1 hrow.2 (by exact_mod_cast (by decide : 2 ≤ 8))
    (by rw [show row_qqOrTotal_as.length = 0 from rfl]; exact_mod_cast (by decide : 0 ≤ 8)) hes ?_, by simp, ?_⟩
  · exact neg_mem_of_map hinst.1 (List.forall_mem_nil _)
  · rw [ctxAfter_introFact [wp, wq] row_qqOrTotal_as (by rw [← Nat.cast_succ]; exact isSemiformula_qqOrTotal_R) (fun e he ↦ (hes e he).1),
      show row_qqOrTotal_R = row_qqOrTotal_body from rfl, ← freeIter_one, hinst.2]

/-- Totality row `qqAllTotal` as a step: the new eigenvariable `&0`, the context shifted. -/
lemma ok_qqAllTotal {tbl N E Γ W : V} {wp : V} (htbl : TableOK tbl N) (hW : WalkTable tbl) (hWp : W = walkPieces)
    (hΓ : IsFormulaSet LAct Γ) (hwp : IsSemiterm LAct 0 wp) (hEwp : termLen LAct wp ≤ E) :
    StepOK tbl E ((8 : ℕ) : V) Γ (mkStep W 28 ?[wp]) ∧ sTag (mkStep W 28 ?[wp]) = 2 ∧
    ctxAfter Γ (mkStep W 28 ?[wp]) = insert (neg LAct (allFact (^&((0 : ℕ) : V)) (termShift LAct wp))) (setShift LAct Γ) := by
  subst hWp
  have hk : ((rIdx_qqAllTotal : ℕ) : V) = (28 : V) := by simp [rIdx_qqAllTotal]
  have hstep := mkStep_qqAllTotal (V := V) ?[wp]
  have hlen := walkTable_len hW rIdx_qqAllTotal (by decide)
  have hrow := walkTable_qqAllTotal hW
  rw [hk] at hstep hlen hrow
  have hes : ∀ e ∈ [wp], IsSemiterm LAct 0 e ∧ termLen LAct e ≤ E := List.forall_mem_cons.mpr ⟨⟨hwp, hEwp⟩, List.forall_mem_nil _⟩
  have hinst := inst_qqAllTotal hwp
  rw [hstep, show (?[wp] : V) = vecOf [wp] from rfl]
  refine ⟨stepOK_introFact htbl [wp] row_qqAllTotal_as hΓ hlen hrow.1 hrow.2 (by exact_mod_cast (by decide : 1 ≤ 8))
    (by rw [show row_qqAllTotal_as.length = 0 from rfl]; exact_mod_cast (by decide : 0 ≤ 8)) hes ?_, by simp, ?_⟩
  · exact neg_mem_of_map hinst.1 (List.forall_mem_nil _)
  · rw [ctxAfter_introFact [wp] row_qqAllTotal_as (by rw [← Nat.cast_succ]; exact isSemiformula_qqAllTotal_R) (fun e he ↦ (hes e he).1),
      show row_qqAllTotal_R = row_qqAllTotal_body from rfl, ← freeIter_one, hinst.2]

/-- Totality row `qqExsTotal` as a step: the new eigenvariable `&0`, the context shifted. -/
lemma ok_qqExsTotal {tbl N E Γ W : V} {wp : V} (htbl : TableOK tbl N) (hW : WalkTable tbl) (hWp : W = walkPieces)
    (hΓ : IsFormulaSet LAct Γ) (hwp : IsSemiterm LAct 0 wp) (hEwp : termLen LAct wp ≤ E) :
    StepOK tbl E ((8 : ℕ) : V) Γ (mkStep W 30 ?[wp]) ∧ sTag (mkStep W 30 ?[wp]) = 2 ∧
    ctxAfter Γ (mkStep W 30 ?[wp]) = insert (neg LAct (exsFact (^&((0 : ℕ) : V)) (termShift LAct wp))) (setShift LAct Γ) := by
  subst hWp
  have hk : ((rIdx_qqExsTotal : ℕ) : V) = (30 : V) := by simp [rIdx_qqExsTotal]
  have hstep := mkStep_qqExsTotal (V := V) ?[wp]
  have hlen := walkTable_len hW rIdx_qqExsTotal (by decide)
  have hrow := walkTable_qqExsTotal hW
  rw [hk] at hstep hlen hrow
  have hes : ∀ e ∈ [wp], IsSemiterm LAct 0 e ∧ termLen LAct e ≤ E := List.forall_mem_cons.mpr ⟨⟨hwp, hEwp⟩, List.forall_mem_nil _⟩
  have hinst := inst_qqExsTotal hwp
  rw [hstep, show (?[wp] : V) = vecOf [wp] from rfl]
  refine ⟨stepOK_introFact htbl [wp] row_qqExsTotal_as hΓ hlen hrow.1 hrow.2 (by exact_mod_cast (by decide : 1 ≤ 8))
    (by rw [show row_qqExsTotal_as.length = 0 from rfl]; exact_mod_cast (by decide : 0 ≤ 8)) hes ?_, by simp, ?_⟩
  · exact neg_mem_of_map hinst.1 (List.forall_mem_nil _)
  · rw [ctxAfter_introFact [wp] row_qqExsTotal_as (by rw [← Nat.cast_succ]; exact isSemiformula_qqExsTotal_R) (fun e he ↦ (hes e he).1),
      show row_qqExsTotal_R = row_qqExsTotal_body from rfl, ← freeIter_one, hinst.2]

/-- Totality row `qqRelTotal` as a step: the new eigenvariable `&0`, the context shifted. -/
lemma ok_qqRelTotal {tbl N E Γ W : V} {wk : V} {wR : V} {wv : V} (htbl : TableOK tbl N) (hW : WalkTable tbl) (hWp : W = walkPieces)
    (hΓ : IsFormulaSet LAct Γ) (hwk : IsSemiterm LAct 0 wk) (hEwk : termLen LAct wk ≤ E) (hwR : IsSemiterm LAct 0 wR) (hEwR : termLen LAct wR ≤ E) (hwv : IsSemiterm LAct 0 wv) (hEwv : termLen LAct wv ≤ E) :
    StepOK tbl E ((8 : ℕ) : V) Γ (mkStep W 32 ?[wk, wR, wv]) ∧ sTag (mkStep W 32 ?[wk, wR, wv]) = 2 ∧
    ctxAfter Γ (mkStep W 32 ?[wk, wR, wv]) = insert (neg LAct (relFact (^&((0 : ℕ) : V)) (termShift LAct wk) (termShift LAct wR) (termShift LAct wv))) (setShift LAct Γ) := by
  subst hWp
  have hk : ((rIdx_qqRelTotal : ℕ) : V) = (32 : V) := by simp [rIdx_qqRelTotal]
  have hstep := mkStep_qqRelTotal (V := V) ?[wk, wR, wv]
  have hlen := walkTable_len hW rIdx_qqRelTotal (by decide)
  have hrow := walkTable_qqRelTotal hW
  rw [hk] at hstep hlen hrow
  have hes : ∀ e ∈ [wk, wR, wv], IsSemiterm LAct 0 e ∧ termLen LAct e ≤ E := List.forall_mem_cons.mpr ⟨⟨hwk, hEwk⟩, List.forall_mem_cons.mpr ⟨⟨hwR, hEwR⟩, List.forall_mem_cons.mpr ⟨⟨hwv, hEwv⟩, List.forall_mem_nil _⟩⟩⟩
  have hinst := inst_qqRelTotal hwk hwR hwv
  rw [hstep, show (?[wk, wR, wv] : V) = vecOf [wk, wR, wv] from rfl]
  refine ⟨stepOK_introFact htbl [wk, wR, wv] row_qqRelTotal_as hΓ hlen hrow.1 hrow.2 (by exact_mod_cast (by decide : 3 ≤ 8))
    (by rw [show row_qqRelTotal_as.length = 0 from rfl]; exact_mod_cast (by decide : 0 ≤ 8)) hes ?_, by simp, ?_⟩
  · exact neg_mem_of_map hinst.1 (List.forall_mem_nil _)
  · rw [ctxAfter_introFact [wk, wR, wv] row_qqRelTotal_as (by rw [← Nat.cast_succ]; exact isSemiformula_qqRelTotal_R) (fun e he ↦ (hes e he).1),
      show row_qqRelTotal_R = row_qqRelTotal_body from rfl, ← freeIter_one, hinst.2]

/-- Totality row `qqNRelTotal` as a step: the new eigenvariable `&0`, the context shifted. -/
lemma ok_qqNRelTotal {tbl N E Γ W : V} {wk : V} {wR : V} {wv : V} (htbl : TableOK tbl N) (hW : WalkTable tbl) (hWp : W = walkPieces)
    (hΓ : IsFormulaSet LAct Γ) (hwk : IsSemiterm LAct 0 wk) (hEwk : termLen LAct wk ≤ E) (hwR : IsSemiterm LAct 0 wR) (hEwR : termLen LAct wR ≤ E) (hwv : IsSemiterm LAct 0 wv) (hEwv : termLen LAct wv ≤ E) :
    StepOK tbl E ((8 : ℕ) : V) Γ (mkStep W 34 ?[wk, wR, wv]) ∧ sTag (mkStep W 34 ?[wk, wR, wv]) = 2 ∧
    ctxAfter Γ (mkStep W 34 ?[wk, wR, wv]) = insert (neg LAct (nrelFact (^&((0 : ℕ) : V)) (termShift LAct wk) (termShift LAct wR) (termShift LAct wv))) (setShift LAct Γ) := by
  subst hWp
  have hk : ((rIdx_qqNRelTotal : ℕ) : V) = (34 : V) := by simp [rIdx_qqNRelTotal]
  have hstep := mkStep_qqNRelTotal (V := V) ?[wk, wR, wv]
  have hlen := walkTable_len hW rIdx_qqNRelTotal (by decide)
  have hrow := walkTable_qqNRelTotal hW
  rw [hk] at hstep hlen hrow
  have hes : ∀ e ∈ [wk, wR, wv], IsSemiterm LAct 0 e ∧ termLen LAct e ≤ E := List.forall_mem_cons.mpr ⟨⟨hwk, hEwk⟩, List.forall_mem_cons.mpr ⟨⟨hwR, hEwR⟩, List.forall_mem_cons.mpr ⟨⟨hwv, hEwv⟩, List.forall_mem_nil _⟩⟩⟩
  have hinst := inst_qqNRelTotal hwk hwR hwv
  rw [hstep, show (?[wk, wR, wv] : V) = vecOf [wk, wR, wv] from rfl]
  refine ⟨stepOK_introFact htbl [wk, wR, wv] row_qqNRelTotal_as hΓ hlen hrow.1 hrow.2 (by exact_mod_cast (by decide : 3 ≤ 8))
    (by rw [show row_qqNRelTotal_as.length = 0 from rfl]; exact_mod_cast (by decide : 0 ≤ 8)) hes ?_, by simp, ?_⟩
  · exact neg_mem_of_map hinst.1 (List.forall_mem_nil _)
  · rw [ctxAfter_introFact [wk, wR, wv] row_qqNRelTotal_as (by rw [← Nat.cast_succ]; exact isSemiformula_qqNRelTotal_R) (fun e he ↦ (hes e he).1),
      show row_qqNRelTotal_R = row_qqNRelTotal_body from rfl, ← freeIter_one, hinst.2]

end formulaRows

/-! ### 5.2 Fact definability and iterated shifts for the formula facts -/

section formulaFacts

instance piFact_definable : 𝚺₁-Function₂ (piFact : V → V → V) := by
  have : (piFact : V → V → V) = fun a b ↦ subst LAct (a ∷ b ∷ 0) Ppi := rfl
  rw [this]; definability
instance sigmaFact_definable : 𝚺₁-Function₂ (sigmaFact : V → V → V) := by
  have : (sigmaFact : V → V → V) = fun a b ↦ subst LAct (a ∷ b ∷ 0) Psigma := rfl
  rw [this]; definability

lemma shiftIterV_piFact {a b : V} (ha : IsSemiterm LAct 0 a) (hb : IsSemiterm LAct 0 b) :
    ∀ k, shiftIterV (piFact a b) k = piFact (termShiftIterV a k) (termShiftIterV b k) := by
  intro k
  induction k using ISigma1.sigma1_succ_induction with
  | hP => definability
  | zero => simp
  | succ k ih =>
    rw [shiftIterV_succ, ih, shift_piFact (isSemiterm_termShiftIterV ha k) (isSemiterm_termShiftIterV hb k),
      termShiftIterV_succ, termShiftIterV_succ]

/-- What the walk of one formula delivers (the induction hypothesis shape). -/
def FormFacts (tbl E W n p : V) : Prop :=
  ∀ Γ, IsFormulaSet LAct Γ →
    ListOK tbl E ((8 : ℕ) : V) Γ (π₂ p) ∧ NoDrop (π₂ p) ∧ shiftsV (π₂ p) = π₁ p ∧
    neg LAct (piFact (cTV n) (^&0)) ∈ finalCtx Γ (π₂ p)

instance formFacts_definable : 𝚷₁-Relation₅ (FormFacts : V → V → V → V → V → Prop) := by
  unfold FormFacts; definability

/-- The closed relation row of `LAct.IsRel k R`, by the two cases. -/
theorem relConst_ok {tbl N E W k R Γ : V} (htbl : TableOK tbl N) (hW : WalkTable tbl) (hWp : W = walkPieces)
    (hkR : LAct.IsRel k R) (hE : 8 ≤ E) (hΓ : IsFormulaSet LAct Γ) :
    StepOK tbl E ((8 : ℕ) : V) Γ (mkStep W (relRow R) 0) ∧ sTag (mkStep W (relRow R) 0) = 0 ∧
    ctxAfter Γ (mkStep W (relRow R) 0) = insert (neg LAct (isRelFact (cTV k) (cTV R))) Γ ∧
    termLen LAct (cTV k) ≤ E ∧ termLen LAct (cTV R) ≤ E := by
  have h8 : ∀ m : V, m ≤ 3 → termLen LAct (cTV m) ≤ E := fun m hm ↦ by
    rw [termLen_cTV]
    exact le_trans (add_le_add (mul_le_mul_of_nonneg_left hm zero_le) le_rfl) (le_trans (by norm_num) hE)
  rcases isRel_LAct_iff_V.mp hkR with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [show relRow (0 : V) = 36 by simp [relRow]]
    obtain ⟨a, b, c⟩ := ok_isRelConst_eq htbl hW hWp hΓ
    simp only [cT, Nat.cast_zero, Nat.cast_ofNat] at c
    exact ⟨a, b, c, h8 2 (by norm_num), h8 0 (by norm_num)⟩
  · rw [show relRow (1 : V) = 37 by simp [relRow]]
    obtain ⟨a, b, c⟩ := ok_isRelConst_lt htbl hW hWp hΓ
    simp only [cT, Nat.cast_one, Nat.cast_ofNat] at c
    exact ⟨a, b, c, h8 2 (by norm_num), h8 1 (by norm_num)⟩

end formulaFacts

/-! ### 5.3 The formula nodes are applicable -/

section formulaNodes


/-- **(F⊤)**: witness bound `2n + 8 ≤ E`. -/
theorem constNode_ok_verum {tbl N E W n Γ : V} (htbl : TableOK tbl N) (hW : WalkTable tbl) (hWp : W = walkPieces)
    (hE : 2 * n + 8 ≤ E) (hΓ : IsFormulaSet LAct Γ) :
    ListOK tbl E ((8 : ℕ) : V) Γ (π₂ (constNode W n 19 20)) ∧ NoDrop (π₂ (constNode W n 19 20)) ∧
    shiftsV (π₂ (constNode W n 19 20)) = 1 ∧
    neg LAct (piFact (cTV n) (^&0)) ∈ finalCtx Γ (π₂ (constNode W n 19 20)) ∧
    neg LAct (verumFact (^&0)) ∈ finalCtx Γ (π₂ (constNode W n 19 20)) := by
  have hEn : termLen LAct (cTV n) ≤ E := termLen_cTV_le (le_trans (add_le_add le_rfl (by norm_num)) hE)
  have hE0 : termLen LAct (^&0 : V) ≤ E := termLen_fvar_le (by rw [zero_add]; exact one_le_of_E hE)
  obtain ⟨hok₁, htag₁, hctx₁⟩ := ok_qqVerumTotal htbl hW hWp hΓ
  rw [Nat.cast_zero] at hctx₁
  have hΓ₂ : IsFormulaSet LAct (ctxAfter Γ (mkStep W 19 0)) := isFormulaSet_ctxAfter 8 htbl hok₁
  have hV₂ : neg LAct (verumFact (^&0)) ∈ ctxAfter Γ (mkStep W 19 0) := by rw [hctx₁]; simp
  obtain ⟨hok₂, htag₂, hctx₂⟩ := ok_isSemiformulaVerum (wn := cTV n) (wp := ^&0) htbl hW hWp hΓ₂
    (cTV_semiterm_LAct 0 _) hEn (by simp) hE0 hV₂
  have hΓ₃ : IsFormulaSet LAct (ctxAfter (ctxAfter Γ (mkStep W 19 0)) (mkStep W 20 ?[cTV n, ^&0])) :=
    isFormulaSet_ctxAfter 8 htbl hok₂
  have hS₃ : neg LAct (sigmaFact (cTV n) (^&0)) ∈ ctxAfter (ctxAfter Γ (mkStep W 19 0)) (mkStep W 20 ?[cTV n, ^&0]) := by
    rw [hctx₂]; simp
  obtain ⟨hok₃, htag₃, hctx₃⟩ := ok_isSemiformulaSigmaPi (wn := cTV n) (wp := ^&0) htbl hW hWp hΓ₃
    (cTV_semiterm_LAct 0 _) hEn (by simp) hE0 hS₃
  have hS : π₂ (constNode W n 19 20) = ?[mkStep W 19 0, mkStep W 20 ?[cTV n, ^&0], mkStep W 21 ?[cTV n, ^&0]] := by
    rw [constNode, pi₂_pair]
  rw [hS]
  refine ⟨listOK_cons hok₁ (listOK_cons hok₂ (listOK_single hok₃)), ?_, ?_, ?_, ?_⟩
  · exact noDrop_cons (Or.inr (Or.inr (Or.inl htag₁))) (noDrop_cons (Or.inl htag₂) (noDrop_single (Or.inl htag₃)))
  · rw [shiftsV_cons, shiftsV_cons, shiftsV_single, if_pos (Or.inl htag₁),
      if_neg (by rw [htag₂]; norm_num), if_neg (by rw [htag₃]; norm_num)]
    simp
  · rw [finalCtx_cons, finalCtx_cons, finalCtx_single, hctx₃]; simp
  · rw [finalCtx_cons, finalCtx_cons, finalCtx_single, hctx₃, hctx₂]; simp [hV₂]


/-- **(F⊥)**: witness bound `2n + 8 ≤ E`. -/
theorem constNode_ok_falsum {tbl N E W n Γ : V} (htbl : TableOK tbl N) (hW : WalkTable tbl) (hWp : W = walkPieces)
    (hE : 2 * n + 8 ≤ E) (hΓ : IsFormulaSet LAct Γ) :
    ListOK tbl E ((8 : ℕ) : V) Γ (π₂ (constNode W n 22 23)) ∧ NoDrop (π₂ (constNode W n 22 23)) ∧
    shiftsV (π₂ (constNode W n 22 23)) = 1 ∧
    neg LAct (piFact (cTV n) (^&0)) ∈ finalCtx Γ (π₂ (constNode W n 22 23)) ∧
    neg LAct (falsumFact (^&0)) ∈ finalCtx Γ (π₂ (constNode W n 22 23)) := by
  have hEn : termLen LAct (cTV n) ≤ E := termLen_cTV_le (le_trans (add_le_add le_rfl (by norm_num)) hE)
  have hE0 : termLen LAct (^&0 : V) ≤ E := termLen_fvar_le (by rw [zero_add]; exact one_le_of_E hE)
  obtain ⟨hok₁, htag₁, hctx₁⟩ := ok_qqFalsumTotal htbl hW hWp hΓ
  rw [Nat.cast_zero] at hctx₁
  have hΓ₂ : IsFormulaSet LAct (ctxAfter Γ (mkStep W 22 0)) := isFormulaSet_ctxAfter 8 htbl hok₁
  have hV₂ : neg LAct (falsumFact (^&0)) ∈ ctxAfter Γ (mkStep W 22 0) := by rw [hctx₁]; simp
  obtain ⟨hok₂, htag₂, hctx₂⟩ := ok_isSemiformulaFalsum (wn := cTV n) (wp := ^&0) htbl hW hWp hΓ₂
    (cTV_semiterm_LAct 0 _) hEn (by simp) hE0 hV₂
  have hΓ₃ : IsFormulaSet LAct (ctxAfter (ctxAfter Γ (mkStep W 22 0)) (mkStep W 23 ?[cTV n, ^&0])) :=
    isFormulaSet_ctxAfter 8 htbl hok₂
  have hS₃ : neg LAct (sigmaFact (cTV n) (^&0)) ∈ ctxAfter (ctxAfter Γ (mkStep W 22 0)) (mkStep W 23 ?[cTV n, ^&0]) := by
    rw [hctx₂]; simp
  obtain ⟨hok₃, htag₃, hctx₃⟩ := ok_isSemiformulaSigmaPi (wn := cTV n) (wp := ^&0) htbl hW hWp hΓ₃
    (cTV_semiterm_LAct 0 _) hEn (by simp) hE0 hS₃
  have hS : π₂ (constNode W n 22 23) = ?[mkStep W 22 0, mkStep W 23 ?[cTV n, ^&0], mkStep W 21 ?[cTV n, ^&0]] := by
    rw [constNode, pi₂_pair]
  rw [hS]
  refine ⟨listOK_cons hok₁ (listOK_cons hok₂ (listOK_single hok₃)), ?_, ?_, ?_, ?_⟩
  · exact noDrop_cons (Or.inr (Or.inr (Or.inl htag₁))) (noDrop_cons (Or.inl htag₂) (noDrop_single (Or.inl htag₃)))
  · rw [shiftsV_cons, shiftsV_cons, shiftsV_single, if_pos (Or.inl htag₁),
      if_neg (by rw [htag₂]; norm_num), if_neg (by rw [htag₃]; norm_num)]
    simp
  · rw [finalCtx_cons, finalCtx_cons, finalCtx_single, hctx₃]; simp
  · rw [finalCtx_cons, finalCtx_cons, finalCtx_single, hctx₃, hctx₂]; simp [hV₂]


/-- **(F∧)**: from the two children's facts (`x_p = &cq`, `x_q = &0` after `Sp ++ Sq`); witness bound
`2n + cq + 8 ≤ E`. -/
theorem binNode_ok_and {tbl N E W n yp yq Γ : V} (htbl : TableOK tbl N) (hW : WalkTable tbl) (hWp : W = walkPieces)
    (hE : 2 * n + π₁ yq + 8 ≤ E) (hp : FormFacts tbl E W n yp) (hq : FormFacts tbl E W n yq)
    (hΓ : IsFormulaSet LAct Γ) :
    ListOK tbl E ((8 : ℕ) : V) Γ (π₂ (binNode W n 24 25 yp yq)) ∧ NoDrop (π₂ (binNode W n 24 25 yp yq)) ∧
    shiftsV (π₂ (binNode W n 24 25 yp yq)) = π₁ yp + π₁ yq + 1 ∧
    neg LAct (piFact (cTV n) (^&0)) ∈ finalCtx Γ (π₂ (binNode W n 24 25 yp yq)) ∧
    neg LAct (andFact (^&0) (^&(π₁ yq + 1)) (^&1)) ∈ finalCtx Γ (π₂ (binNode W n 24 25 yp yq)) := by
  have hE' : 2 * n + (π₁ yq + 8) ≤ E := by rw [← add_assoc]; exact hE
  have hE8 : 8 ≤ E := le_trans (le_trans le_add_self le_add_self) hE'
  have hEn : termLen LAct (cTV n) ≤ E := termLen_cTV_le (le_trans (add_le_add le_rfl (le_trans (by norm_num : (1 : V) ≤ 8) le_add_self)) hE')
  have hEq : termLen LAct (^&(π₁ yq) : V) ≤ E := termLen_fvar_le
    (le_trans (le_trans (add_le_add le_rfl (by norm_num : (1 : V) ≤ 8)) le_add_self) hE')
  have hEq' : termLen LAct (^&(π₁ yq + 1) : V) ≤ E := termLen_fvar_le (by
    calc π₁ yq + 1 + 1 = π₁ yq + 2 := by ring
      _ ≤ 2 * n + (π₁ yq + 8) := le_trans (add_le_add le_rfl (by norm_num)) le_add_self
      _ ≤ E := hE')
  have hE0 : termLen LAct (^&0 : V) ≤ E := termLen_fvar_le (by rw [zero_add]; exact le_trans (by norm_num) hE8)
  have hE1 : termLen LAct (^&1 : V) ≤ E := termLen_fvar_le (le_trans (by norm_num) hE8)
  obtain ⟨hokP, hndP, hshP, hP⟩ := hp Γ hΓ
  have hΓ₁ : IsFormulaSet LAct (finalCtx Γ (π₂ yp)) := finalCtx_isFormulaSet 8 htbl hΓ hokP
  obtain ⟨hokQ, hndQ, hshQ, hQ⟩ := hq _ hΓ₁
  set Γ₂ := finalCtx (finalCtx Γ (π₂ yp)) (π₂ yq) with hΓ₂def
  have hΓ₂ : IsFormulaSet LAct Γ₂ := finalCtx_isFormulaSet 8 htbl hΓ₁ hokQ
  have hP₂ : neg LAct (piFact (cTV n) (^&(π₁ yq))) ∈ Γ₂ := by
    have := mem_finalCtx_of_mem hndQ hP
    rwa [hshQ, shiftIterV_neg (isFormula_piFact (cTV_semiterm_LAct 0 _) (by simp)),
      shiftIterV_piFact (cTV_semiterm_LAct 0 _) (by simp), termShiftIterV_cTV, termShiftIterV_fvar, zero_add] at this
  obtain ⟨hok₁, htag₁, hctx₁⟩ := ok_qqAndTotal (wp := ^&(π₁ yq)) (wq := ^&0) htbl hW hWp hΓ₂ (by simp) hEq (by simp) hE0
  rw [Nat.cast_zero, termShift_fvar, termShift_fvar, zero_add] at hctx₁
  set s₁ := mkStep W 24 ?[^&(π₁ yq), ^&0] with hs₁
  have hΓ₃ : IsFormulaSet LAct (ctxAfter Γ₂ s₁) := isFormulaSet_ctxAfter 8 htbl hok₁
  have hP₃ : neg LAct (piFact (cTV n) (^&(π₁ yq + 1))) ∈ ctxAfter Γ₂ s₁ := by
    rw [hctx₁]
    have := neg_mem_setShift (isFormula_piFact (cTV_semiterm_LAct 0 _) (by simp)) hP₂
    rw [shift_piFact (cTV_semiterm_LAct 0 _) (by simp), termShift_cTV, termShift_fvar] at this
    simp [this]
  have hQ₃ : neg LAct (piFact (cTV n) (^&1)) ∈ ctxAfter Γ₂ s₁ := by
    rw [hctx₁]
    have := neg_mem_setShift (isFormula_piFact (cTV_semiterm_LAct 0 _) (by simp)) hQ
    rw [shift_piFact (cTV_semiterm_LAct 0 _) (by simp), termShift_cTV, termShift_fvar, zero_add] at this
    simp [this]
  have hA₃ : neg LAct (andFact (^&0) (^&(π₁ yq + 1)) (^&1)) ∈ ctxAfter Γ₂ s₁ := by rw [hctx₁]; simp
  obtain ⟨hok₂, htag₂, hctx₂⟩ := ok_isSemiformulaAnd (wn := cTV n) (wp := ^&(π₁ yq + 1)) (wq := ^&1) (wr := ^&0) htbl hW hWp hΓ₃
    (cTV_semiterm_LAct 0 _) hEn (by simp) hEq' (by simp) hE1 (by simp) hE0 hP₃ hQ₃ hA₃
  set s₂ := mkStep W 25 ?[cTV n, ^&(π₁ yq + 1), ^&1, ^&0] with hs₂
  have hΓ₄ : IsFormulaSet LAct (ctxAfter (ctxAfter Γ₂ s₁) s₂) := isFormulaSet_ctxAfter 8 htbl hok₂
  have hS₄ : neg LAct (sigmaFact (cTV n) (^&0)) ∈ ctxAfter (ctxAfter Γ₂ s₁) s₂ := by rw [hctx₂]; simp
  have hA₄ : neg LAct (andFact (^&0) (^&(π₁ yq + 1)) (^&1)) ∈ ctxAfter (ctxAfter Γ₂ s₁) s₂ := by rw [hctx₂]; simp [hA₃]
  obtain ⟨hok₃, htag₃, hctx₃⟩ := ok_isSemiformulaSigmaPi (wn := cTV n) (wp := ^&0) htbl hW hWp hΓ₄
    (cTV_semiterm_LAct 0 _) hEn (by simp) hE0 hS₄
  set s₃ := mkStep W 21 ?[cTV n, ^&0] with hs₃
  have hS : π₂ (binNode W n 24 25 yp yq) = appendV (π₂ yp) (appendV (π₂ yq) ?[s₁, s₂, s₃]) := by
    rw [binNode, pi₂_pair]
  rw [hS]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact listOK_appendV hokP (listOK_appendV hokQ (listOK_cons hok₁ (listOK_cons hok₂ (listOK_single hok₃))))
  · exact noDrop_appendV hndP (noDrop_appendV hndQ (noDrop_cons (Or.inr (Or.inr (Or.inl htag₁)))
      (noDrop_cons (Or.inl htag₂) (noDrop_single (Or.inl htag₃)))))
  · rw [shiftsV_appendV, shiftsV_appendV, hshP, hshQ, shiftsV_cons, shiftsV_cons, shiftsV_single,
      if_pos (Or.inl htag₁), if_neg (by rw [htag₂]; norm_num), if_neg (by rw [htag₃]; norm_num)]
    ring
  · rw [finalCtx_appendV, finalCtx_appendV, finalCtx_cons, finalCtx_cons, finalCtx_single, hctx₃]; simp
  · rw [finalCtx_appendV, finalCtx_appendV, finalCtx_cons, finalCtx_cons, finalCtx_single, hctx₃]; simp [hA₄]


/-- **(F∨)**: from the two children's facts (`x_p = &cq`, `x_q = &0` after `Sp ++ Sq`); witness bound
`2n + cq + 8 ≤ E`. -/
theorem binNode_ok_or {tbl N E W n yp yq Γ : V} (htbl : TableOK tbl N) (hW : WalkTable tbl) (hWp : W = walkPieces)
    (hE : 2 * n + π₁ yq + 8 ≤ E) (hp : FormFacts tbl E W n yp) (hq : FormFacts tbl E W n yq)
    (hΓ : IsFormulaSet LAct Γ) :
    ListOK tbl E ((8 : ℕ) : V) Γ (π₂ (binNode W n 26 27 yp yq)) ∧ NoDrop (π₂ (binNode W n 26 27 yp yq)) ∧
    shiftsV (π₂ (binNode W n 26 27 yp yq)) = π₁ yp + π₁ yq + 1 ∧
    neg LAct (piFact (cTV n) (^&0)) ∈ finalCtx Γ (π₂ (binNode W n 26 27 yp yq)) ∧
    neg LAct (orFact (^&0) (^&(π₁ yq + 1)) (^&1)) ∈ finalCtx Γ (π₂ (binNode W n 26 27 yp yq)) := by
  have hE' : 2 * n + (π₁ yq + 8) ≤ E := by rw [← add_assoc]; exact hE
  have hE8 : 8 ≤ E := le_trans (le_trans le_add_self le_add_self) hE'
  have hEn : termLen LAct (cTV n) ≤ E := termLen_cTV_le (le_trans (add_le_add le_rfl (le_trans (by norm_num : (1 : V) ≤ 8) le_add_self)) hE')
  have hEq : termLen LAct (^&(π₁ yq) : V) ≤ E := termLen_fvar_le
    (le_trans (le_trans (add_le_add le_rfl (by norm_num : (1 : V) ≤ 8)) le_add_self) hE')
  have hEq' : termLen LAct (^&(π₁ yq + 1) : V) ≤ E := termLen_fvar_le (by
    calc π₁ yq + 1 + 1 = π₁ yq + 2 := by ring
      _ ≤ 2 * n + (π₁ yq + 8) := le_trans (add_le_add le_rfl (by norm_num)) le_add_self
      _ ≤ E := hE')
  have hE0 : termLen LAct (^&0 : V) ≤ E := termLen_fvar_le (by rw [zero_add]; exact le_trans (by norm_num) hE8)
  have hE1 : termLen LAct (^&1 : V) ≤ E := termLen_fvar_le (le_trans (by norm_num) hE8)
  obtain ⟨hokP, hndP, hshP, hP⟩ := hp Γ hΓ
  have hΓ₁ : IsFormulaSet LAct (finalCtx Γ (π₂ yp)) := finalCtx_isFormulaSet 8 htbl hΓ hokP
  obtain ⟨hokQ, hndQ, hshQ, hQ⟩ := hq _ hΓ₁
  set Γ₂ := finalCtx (finalCtx Γ (π₂ yp)) (π₂ yq) with hΓ₂def
  have hΓ₂ : IsFormulaSet LAct Γ₂ := finalCtx_isFormulaSet 8 htbl hΓ₁ hokQ
  have hP₂ : neg LAct (piFact (cTV n) (^&(π₁ yq))) ∈ Γ₂ := by
    have := mem_finalCtx_of_mem hndQ hP
    rwa [hshQ, shiftIterV_neg (isFormula_piFact (cTV_semiterm_LAct 0 _) (by simp)),
      shiftIterV_piFact (cTV_semiterm_LAct 0 _) (by simp), termShiftIterV_cTV, termShiftIterV_fvar, zero_add] at this
  obtain ⟨hok₁, htag₁, hctx₁⟩ := ok_qqOrTotal (wp := ^&(π₁ yq)) (wq := ^&0) htbl hW hWp hΓ₂ (by simp) hEq (by simp) hE0
  rw [Nat.cast_zero, termShift_fvar, termShift_fvar, zero_add] at hctx₁
  set s₁ := mkStep W 26 ?[^&(π₁ yq), ^&0] with hs₁
  have hΓ₃ : IsFormulaSet LAct (ctxAfter Γ₂ s₁) := isFormulaSet_ctxAfter 8 htbl hok₁
  have hP₃ : neg LAct (piFact (cTV n) (^&(π₁ yq + 1))) ∈ ctxAfter Γ₂ s₁ := by
    rw [hctx₁]
    have := neg_mem_setShift (isFormula_piFact (cTV_semiterm_LAct 0 _) (by simp)) hP₂
    rw [shift_piFact (cTV_semiterm_LAct 0 _) (by simp), termShift_cTV, termShift_fvar] at this
    simp [this]
  have hQ₃ : neg LAct (piFact (cTV n) (^&1)) ∈ ctxAfter Γ₂ s₁ := by
    rw [hctx₁]
    have := neg_mem_setShift (isFormula_piFact (cTV_semiterm_LAct 0 _) (by simp)) hQ
    rw [shift_piFact (cTV_semiterm_LAct 0 _) (by simp), termShift_cTV, termShift_fvar, zero_add] at this
    simp [this]
  have hA₃ : neg LAct (orFact (^&0) (^&(π₁ yq + 1)) (^&1)) ∈ ctxAfter Γ₂ s₁ := by rw [hctx₁]; simp
  obtain ⟨hok₂, htag₂, hctx₂⟩ := ok_isSemiformulaOr (wn := cTV n) (wp := ^&(π₁ yq + 1)) (wq := ^&1) (wr := ^&0) htbl hW hWp hΓ₃
    (cTV_semiterm_LAct 0 _) hEn (by simp) hEq' (by simp) hE1 (by simp) hE0 hP₃ hQ₃ hA₃
  set s₂ := mkStep W 27 ?[cTV n, ^&(π₁ yq + 1), ^&1, ^&0] with hs₂
  have hΓ₄ : IsFormulaSet LAct (ctxAfter (ctxAfter Γ₂ s₁) s₂) := isFormulaSet_ctxAfter 8 htbl hok₂
  have hS₄ : neg LAct (sigmaFact (cTV n) (^&0)) ∈ ctxAfter (ctxAfter Γ₂ s₁) s₂ := by rw [hctx₂]; simp
  have hA₄ : neg LAct (orFact (^&0) (^&(π₁ yq + 1)) (^&1)) ∈ ctxAfter (ctxAfter Γ₂ s₁) s₂ := by rw [hctx₂]; simp [hA₃]
  obtain ⟨hok₃, htag₃, hctx₃⟩ := ok_isSemiformulaSigmaPi (wn := cTV n) (wp := ^&0) htbl hW hWp hΓ₄
    (cTV_semiterm_LAct 0 _) hEn (by simp) hE0 hS₄
  set s₃ := mkStep W 21 ?[cTV n, ^&0] with hs₃
  have hS : π₂ (binNode W n 26 27 yp yq) = appendV (π₂ yp) (appendV (π₂ yq) ?[s₁, s₂, s₃]) := by
    rw [binNode, pi₂_pair]
  rw [hS]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact listOK_appendV hokP (listOK_appendV hokQ (listOK_cons hok₁ (listOK_cons hok₂ (listOK_single hok₃))))
  · exact noDrop_appendV hndP (noDrop_appendV hndQ (noDrop_cons (Or.inr (Or.inr (Or.inl htag₁)))
      (noDrop_cons (Or.inl htag₂) (noDrop_single (Or.inl htag₃)))))
  · rw [shiftsV_appendV, shiftsV_appendV, hshP, hshQ, shiftsV_cons, shiftsV_cons, shiftsV_single,
      if_pos (Or.inl htag₁), if_neg (by rw [htag₂]; norm_num), if_neg (by rw [htag₃]; norm_num)]
    ring
  · rw [finalCtx_appendV, finalCtx_appendV, finalCtx_cons, finalCtx_cons, finalCtx_single, hctx₃]; simp
  · rw [finalCtx_appendV, finalCtx_appendV, finalCtx_cons, finalCtx_cons, finalCtx_single, hctx₃]; simp [hA₄]


/-- **(F∀)**: from the body's facts at arity `n + 1`; witness bound `2n + 8 ≤ E`. -/
theorem quantNode_ok_all {tbl N E W n yp Γ : V} (htbl : TableOK tbl N) (hW : WalkTable tbl) (hWp : W = walkPieces)
    (hE : 2 * n + 8 ≤ E) (hp : FormFacts tbl E W (n + 1) yp) (hΓ : IsFormulaSet LAct Γ) :
    ListOK tbl E ((8 : ℕ) : V) Γ (π₂ (quantNode W n 28 29 yp)) ∧ NoDrop (π₂ (quantNode W n 28 29 yp)) ∧
    shiftsV (π₂ (quantNode W n 28 29 yp)) = π₁ yp + 1 ∧
    neg LAct (piFact (cTV n) (^&0)) ∈ finalCtx Γ (π₂ (quantNode W n 28 29 yp)) ∧
    neg LAct (allFact (^&0) (^&1)) ∈ finalCtx Γ (π₂ (quantNode W n 28 29 yp)) := by
  have hE8 : 8 ≤ E := le_trans le_add_self hE
  have hEn : termLen LAct (cTV n) ≤ E := termLen_cTV_le (le_trans (add_le_add le_rfl (by norm_num)) hE)
  have hE0 : termLen LAct (^&0 : V) ≤ E := termLen_fvar_le (by rw [zero_add]; exact le_trans (by norm_num) hE8)
  have hE1 : termLen LAct (^&1 : V) ≤ E := termLen_fvar_le (le_trans (by norm_num) hE8)
  obtain ⟨hokP, hndP, hshP, hP⟩ := hp Γ hΓ
  set Γ₁ := finalCtx Γ (π₂ yp) with hΓ₁def
  have hΓ₁ : IsFormulaSet LAct Γ₁ := finalCtx_isFormulaSet 8 htbl hΓ hokP
  obtain ⟨hok₁, htag₁, hctx₁⟩ := ok_qqAllTotal (wp := ^&0) htbl hW hWp hΓ₁ (by simp) hE0
  rw [Nat.cast_zero, termShift_fvar, zero_add] at hctx₁
  set s₁ := mkStep W 28 ?[^&0] with hs₁
  have hΓ₂ : IsFormulaSet LAct (ctxAfter Γ₁ s₁) := isFormulaSet_ctxAfter 8 htbl hok₁
  have hP₂ : neg LAct (piFact (cTV n ^+ (𝟏 : V)) (^&1)) ∈ ctxAfter Γ₁ s₁ := by
    rw [hctx₁]
    have := neg_mem_setShift (isFormula_piFact (cTV_semiterm_LAct 0 _) (by simp)) hP
    rw [shift_piFact (cTV_semiterm_LAct 0 _) (by simp), termShift_cTV, termShift_fvar, zero_add, cTV_succ] at this
    simp [this]
  have hA₂ : neg LAct (allFact (^&0) (^&1)) ∈ ctxAfter Γ₁ s₁ := by rw [hctx₁]; simp
  obtain ⟨hok₂, htag₂, hctx₂⟩ := ok_isSemiformulaAll (wn := cTV n) (wp := ^&1) (wq := ^&0) htbl hW hWp hΓ₂
    (cTV_semiterm_LAct 0 _) hEn (by simp) hE1 (by simp) hE0 hP₂ hA₂
  set s₂ := mkStep W 29 ?[cTV n, ^&1, ^&0] with hs₂
  have hΓ₃ : IsFormulaSet LAct (ctxAfter (ctxAfter Γ₁ s₁) s₂) := isFormulaSet_ctxAfter 8 htbl hok₂
  have hS₃ : neg LAct (sigmaFact (cTV n) (^&0)) ∈ ctxAfter (ctxAfter Γ₁ s₁) s₂ := by rw [hctx₂]; simp
  have hA₃ : neg LAct (allFact (^&0) (^&1)) ∈ ctxAfter (ctxAfter Γ₁ s₁) s₂ := by rw [hctx₂]; simp [hA₂]
  obtain ⟨hok₃, htag₃, hctx₃⟩ := ok_isSemiformulaSigmaPi (wn := cTV n) (wp := ^&0) htbl hW hWp hΓ₃
    (cTV_semiterm_LAct 0 _) hEn (by simp) hE0 hS₃
  set s₃ := mkStep W 21 ?[cTV n, ^&0] with hs₃
  have hS : π₂ (quantNode W n 28 29 yp) = appendV (π₂ yp) ?[s₁, s₂, s₃] := by rw [quantNode, pi₂_pair]
  rw [hS]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact listOK_appendV hokP (listOK_cons hok₁ (listOK_cons hok₂ (listOK_single hok₃)))
  · exact noDrop_appendV hndP (noDrop_cons (Or.inr (Or.inr (Or.inl htag₁)))
      (noDrop_cons (Or.inl htag₂) (noDrop_single (Or.inl htag₃))))
  · rw [shiftsV_appendV, hshP, shiftsV_cons, shiftsV_cons, shiftsV_single,
      if_pos (Or.inl htag₁), if_neg (by rw [htag₂]; norm_num), if_neg (by rw [htag₃]; norm_num)]
    ring
  · rw [finalCtx_appendV, finalCtx_cons, finalCtx_cons, finalCtx_single, hctx₃]; simp
  · rw [finalCtx_appendV, finalCtx_cons, finalCtx_cons, finalCtx_single, hctx₃]; simp [hA₃]


/-- **(F∃)**: from the body's facts at arity `n + 1`; witness bound `2n + 8 ≤ E`. -/
theorem quantNode_ok_exs {tbl N E W n yp Γ : V} (htbl : TableOK tbl N) (hW : WalkTable tbl) (hWp : W = walkPieces)
    (hE : 2 * n + 8 ≤ E) (hp : FormFacts tbl E W (n + 1) yp) (hΓ : IsFormulaSet LAct Γ) :
    ListOK tbl E ((8 : ℕ) : V) Γ (π₂ (quantNode W n 30 31 yp)) ∧ NoDrop (π₂ (quantNode W n 30 31 yp)) ∧
    shiftsV (π₂ (quantNode W n 30 31 yp)) = π₁ yp + 1 ∧
    neg LAct (piFact (cTV n) (^&0)) ∈ finalCtx Γ (π₂ (quantNode W n 30 31 yp)) ∧
    neg LAct (exsFact (^&0) (^&1)) ∈ finalCtx Γ (π₂ (quantNode W n 30 31 yp)) := by
  have hE8 : 8 ≤ E := le_trans le_add_self hE
  have hEn : termLen LAct (cTV n) ≤ E := termLen_cTV_le (le_trans (add_le_add le_rfl (by norm_num)) hE)
  have hE0 : termLen LAct (^&0 : V) ≤ E := termLen_fvar_le (by rw [zero_add]; exact le_trans (by norm_num) hE8)
  have hE1 : termLen LAct (^&1 : V) ≤ E := termLen_fvar_le (le_trans (by norm_num) hE8)
  obtain ⟨hokP, hndP, hshP, hP⟩ := hp Γ hΓ
  set Γ₁ := finalCtx Γ (π₂ yp) with hΓ₁def
  have hΓ₁ : IsFormulaSet LAct Γ₁ := finalCtx_isFormulaSet 8 htbl hΓ hokP
  obtain ⟨hok₁, htag₁, hctx₁⟩ := ok_qqExsTotal (wp := ^&0) htbl hW hWp hΓ₁ (by simp) hE0
  rw [Nat.cast_zero, termShift_fvar, zero_add] at hctx₁
  set s₁ := mkStep W 30 ?[^&0] with hs₁
  have hΓ₂ : IsFormulaSet LAct (ctxAfter Γ₁ s₁) := isFormulaSet_ctxAfter 8 htbl hok₁
  have hP₂ : neg LAct (piFact (cTV n ^+ (𝟏 : V)) (^&1)) ∈ ctxAfter Γ₁ s₁ := by
    rw [hctx₁]
    have := neg_mem_setShift (isFormula_piFact (cTV_semiterm_LAct 0 _) (by simp)) hP
    rw [shift_piFact (cTV_semiterm_LAct 0 _) (by simp), termShift_cTV, termShift_fvar, zero_add, cTV_succ] at this
    simp [this]
  have hA₂ : neg LAct (exsFact (^&0) (^&1)) ∈ ctxAfter Γ₁ s₁ := by rw [hctx₁]; simp
  obtain ⟨hok₂, htag₂, hctx₂⟩ := ok_isSemiformulaExs (wn := cTV n) (wp := ^&1) (wq := ^&0) htbl hW hWp hΓ₂
    (cTV_semiterm_LAct 0 _) hEn (by simp) hE1 (by simp) hE0 hP₂ hA₂
  set s₂ := mkStep W 31 ?[cTV n, ^&1, ^&0] with hs₂
  have hΓ₃ : IsFormulaSet LAct (ctxAfter (ctxAfter Γ₁ s₁) s₂) := isFormulaSet_ctxAfter 8 htbl hok₂
  have hS₃ : neg LAct (sigmaFact (cTV n) (^&0)) ∈ ctxAfter (ctxAfter Γ₁ s₁) s₂ := by rw [hctx₂]; simp
  have hA₃ : neg LAct (exsFact (^&0) (^&1)) ∈ ctxAfter (ctxAfter Γ₁ s₁) s₂ := by rw [hctx₂]; simp [hA₂]
  obtain ⟨hok₃, htag₃, hctx₃⟩ := ok_isSemiformulaSigmaPi (wn := cTV n) (wp := ^&0) htbl hW hWp hΓ₃
    (cTV_semiterm_LAct 0 _) hEn (by simp) hE0 hS₃
  set s₃ := mkStep W 21 ?[cTV n, ^&0] with hs₃
  have hS : π₂ (quantNode W n 30 31 yp) = appendV (π₂ yp) ?[s₁, s₂, s₃] := by rw [quantNode, pi₂_pair]
  rw [hS]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact listOK_appendV hokP (listOK_cons hok₁ (listOK_cons hok₂ (listOK_single hok₃)))
  · exact noDrop_appendV hndP (noDrop_cons (Or.inr (Or.inr (Or.inl htag₁)))
      (noDrop_cons (Or.inl htag₂) (noDrop_single (Or.inl htag₃))))
  · rw [shiftsV_appendV, hshP, shiftsV_cons, shiftsV_cons, shiftsV_single,
      if_pos (Or.inl htag₁), if_neg (by rw [htag₂]; norm_num), if_neg (by rw [htag₃]; norm_num)]
    ring
  · rw [finalCtx_appendV, finalCtx_cons, finalCtx_cons, finalCtx_single, hctx₃]; simp
  · rw [finalCtx_appendV, finalCtx_cons, finalCtx_cons, finalCtx_single, hctx₃]; simp [hA₃]


/-- **(Frel)**: after the vector; witness bound `2n + 8 ≤ E`. -/
theorem atomNode_ok_rel {tbl N E W n k R d Γ : V} (htbl : TableOK tbl N) (hW : WalkTable tbl) (hWp : W = walkPieces)
    (hkR : LAct.IsRel k R) (hE : 2 * n + 8 ≤ E) (hΓ : IsFormulaSet LAct Γ) (hd : VecFacts tbl E W n k Γ d) :
    ListOK tbl E ((8 : ℕ) : V) Γ (π₂ (atomNode W n 32 33 k R d)) ∧ NoDrop (π₂ (atomNode W n 32 33 k R d)) ∧
    shiftsV (π₂ (atomNode W n 32 33 k R d)) = π₁ d + 1 ∧
    neg LAct (piFact (cTV n) (^&0)) ∈ finalCtx Γ (π₂ (atomNode W n 32 33 k R d)) ∧
    neg LAct (relFact (^&0) (cTV k) (cTV R) (vRef 1 k)) ∈ finalCtx Γ (π₂ (atomNode W n 32 33 k R d)) := by
  obtain ⟨hok₀, hnd₀, hsh₀, hA₀⟩ := hd
  have hE8 : 8 ≤ E := le_trans le_add_self hE
  have hEn : termLen LAct (cTV n) ≤ E := termLen_cTV_le (le_trans (add_le_add le_rfl (by norm_num)) hE)
  have hE0 : termLen LAct (^&0 : V) ≤ E := termLen_fvar_le (by rw [zero_add]; exact le_trans (by norm_num) hE8)
  have hEr0 : termLen LAct (vRef 0 k) ≤ E := termLen_vRef_le (by rw [zero_add]; exact le_trans (by norm_num) hE8)
  have hEr1 : termLen LAct (vRef 1 k) ≤ E := termLen_vRef_le (le_trans (by norm_num) hE8)
  set Γ₀ := finalCtx Γ (π₂ d) with hΓ₀def
  have hΓ₀ : IsFormulaSet LAct Γ₀ := finalCtx_isFormulaSet 8 htbl hΓ hok₀
  obtain ⟨hok₁, htag₁, hctx₁, hEk, hER⟩ := relConst_ok htbl hW hWp hkR hE8 hΓ₀
  set s₁ := mkStep W (relRow R) 0 with hs₁
  have hΓ₁ : IsFormulaSet LAct (ctxAfter Γ₀ s₁) := isFormulaSet_ctxAfter 8 htbl hok₁
  have hF₁ : neg LAct (isRelFact (cTV k) (cTV R)) ∈ ctxAfter Γ₀ s₁ := by rw [hctx₁]; simp
  have hA₁ : neg LAct (tvPiFact (cTV k) (cTV n) (vRef 0 k)) ∈ ctxAfter Γ₀ s₁ := by rw [hctx₁]; simp [hA₀]
  obtain ⟨hok₂, htag₂, hctx₂⟩ := ok_qqRelTotal (wk := cTV k) (wR := cTV R) (wv := vRef 0 k) htbl hW hWp hΓ₁
    (cTV_semiterm_LAct 0 _) hEk (cTV_semiterm_LAct 0 _) hER (isSemiterm_vRef _ _) hEr0
  rw [Nat.cast_zero, termShift_cTV, termShift_cTV, termShift_vRef, zero_add] at hctx₂
  set s₂ := mkStep W 32 ?[cTV k, cTV R, vRef 0 k] with hs₂
  have hΓ₂ : IsFormulaSet LAct (ctxAfter (ctxAfter Γ₀ s₁) s₂) := isFormulaSet_ctxAfter 8 htbl hok₂
  have hF₂ : neg LAct (isRelFact (cTV k) (cTV R)) ∈ ctxAfter (ctxAfter Γ₀ s₁) s₂ := by
    rw [hctx₂]
    have := neg_mem_setShift (isFormula_isRelFact (cTV_semiterm_LAct 0 _) (cTV_semiterm_LAct 0 _)) hF₁
    rw [shift_isRelFact (cTV_semiterm_LAct 0 _) (cTV_semiterm_LAct 0 _), termShift_cTV, termShift_cTV] at this
    simp [this]
  have hA₂ : neg LAct (tvPiFact (cTV k) (cTV n) (vRef 1 k)) ∈ ctxAfter (ctxAfter Γ₀ s₁) s₂ := by
    rw [hctx₂]
    have := neg_mem_setShift (isFormula_tvPiFact (cTV_semiterm_LAct 0 _) (cTV_semiterm_LAct 0 _) (isSemiterm_vRef _ _)) hA₁
    rw [shift_tvPiFact (cTV_semiterm_LAct 0 _) (cTV_semiterm_LAct 0 _) (isSemiterm_vRef _ _), termShift_cTV, termShift_cTV,
      termShift_vRef, zero_add] at this
    simp [this]
  have hG₂ : neg LAct (relFact (^&0) (cTV k) (cTV R) (vRef 1 k)) ∈ ctxAfter (ctxAfter Γ₀ s₁) s₂ := by
    rw [hctx₂]; simp
  obtain ⟨hok₃, htag₃, hctx₃⟩ := ok_isSemiformulaRel (wn := cTV n) (wk := cTV k) (wR := cTV R) (wv := vRef 1 k) (wp := ^&0)
    htbl hW hWp hΓ₂ (cTV_semiterm_LAct 0 _) hEn (cTV_semiterm_LAct 0 _) hEk (cTV_semiterm_LAct 0 _) hER
    (isSemiterm_vRef _ _) hEr1 (by simp) hE0 hF₂ hA₂ hG₂
  set s₃ := mkStep W 33 ?[cTV n, cTV k, cTV R, vRef 1 k, ^&0] with hs₃
  have hΓ₃ : IsFormulaSet LAct (ctxAfter (ctxAfter (ctxAfter Γ₀ s₁) s₂) s₃) := isFormulaSet_ctxAfter 8 htbl hok₃
  have hS₃ : neg LAct (sigmaFact (cTV n) (^&0)) ∈ ctxAfter (ctxAfter (ctxAfter Γ₀ s₁) s₂) s₃ := by rw [hctx₃]; simp
  have hA₃ : neg LAct (tvPiFact (cTV k) (cTV n) (vRef 1 k)) ∈ ctxAfter (ctxAfter (ctxAfter Γ₀ s₁) s₂) s₃ := by
    rw [hctx₃]; simp [hA₂]
  have hG₃ : neg LAct (relFact (^&0) (cTV k) (cTV R) (vRef 1 k)) ∈ ctxAfter (ctxAfter (ctxAfter Γ₀ s₁) s₂) s₃ := by
    rw [hctx₃]; simp [hG₂]
  obtain ⟨hok₄, htag₄, hctx₄⟩ := ok_isSemiformulaSigmaPi (wn := cTV n) (wp := ^&0) htbl hW hWp hΓ₃
    (cTV_semiterm_LAct 0 _) hEn (by simp) hE0 hS₃
  set s₄ := mkStep W 21 ?[cTV n, ^&0] with hs₄
  have hΓ₄ : IsFormulaSet LAct (ctxAfter (ctxAfter (ctxAfter (ctxAfter Γ₀ s₁) s₂) s₃) s₄) :=
    isFormulaSet_ctxAfter 8 htbl hok₄
  have hP₄ : neg LAct (piFact (cTV n) (^&0)) ∈ ctxAfter (ctxAfter (ctxAfter (ctxAfter Γ₀ s₁) s₂) s₃) s₄ := by
    rw [hctx₄]; simp
  have hA₄ : neg LAct (tvPiFact (cTV k) (cTV n) (vRef 1 k)) ∈ ctxAfter (ctxAfter (ctxAfter (ctxAfter Γ₀ s₁) s₂) s₃) s₄ := by
    rw [hctx₄]; simp [hA₃]
  have hG₄ : neg LAct (relFact (^&0) (cTV k) (cTV R) (vRef 1 k)) ∈
      ctxAfter (ctxAfter (ctxAfter (ctxAfter Γ₀ s₁) s₂) s₃) s₄ := by rw [hctx₄]; simp [hG₃]
  obtain ⟨hok₅, htag₅, hctx₅⟩ := ok_isUTermVecOfSemitermVecLAct (wk := cTV k) (wn := cTV n) (wv := vRef 1 k) htbl hW hWp hΓ₄
    (cTV_semiterm_LAct 0 _) hEk (cTV_semiterm_LAct 0 _) hEn (isSemiterm_vRef _ _) hEr1 hA₄
  set s₅ := mkStep W 38 ?[cTV k, cTV n, vRef 1 k] with hs₅
  have hΓ₅ : IsFormulaSet LAct (ctxAfter (ctxAfter (ctxAfter (ctxAfter (ctxAfter Γ₀ s₁) s₂) s₃) s₄) s₅) :=
    isFormulaSet_ctxAfter 8 htbl hok₅
  have hU₅ : neg LAct (utvSigmaFact (cTV k) (vRef 1 k)) ∈
      ctxAfter (ctxAfter (ctxAfter (ctxAfter (ctxAfter Γ₀ s₁) s₂) s₃) s₄) s₅ := by rw [hctx₅]; simp
  have hP₅ : neg LAct (piFact (cTV n) (^&0)) ∈
      ctxAfter (ctxAfter (ctxAfter (ctxAfter (ctxAfter Γ₀ s₁) s₂) s₃) s₄) s₅ := by rw [hctx₅]; simp [hP₄]
  have hG₅ : neg LAct (relFact (^&0) (cTV k) (cTV R) (vRef 1 k)) ∈
      ctxAfter (ctxAfter (ctxAfter (ctxAfter (ctxAfter Γ₀ s₁) s₂) s₃) s₄) s₅ := by rw [hctx₅]; simp [hG₄]
  obtain ⟨hok₆, htag₆, hctx₆⟩ := ok_isUTermVecSigmaPiLAct (wk := cTV k) (wv := vRef 1 k) htbl hW hWp hΓ₅
    (cTV_semiterm_LAct 0 _) hEk (isSemiterm_vRef _ _) hEr1 hU₅
  set s₆ := mkStep W 39 ?[cTV k, vRef 1 k] with hs₆
  have hS : π₂ (atomNode W n 32 33 k R d) = appendV (π₂ d) ?[s₁, s₂, s₃, s₄, s₅, s₆] := by rw [atomNode, pi₂_pair]
  rw [hS]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact listOK_appendV hok₀ (listOK_cons hok₁ (listOK_cons hok₂ (listOK_cons hok₃ (listOK_cons hok₄
      (listOK_cons hok₅ (listOK_single hok₆))))))
  · exact noDrop_appendV hnd₀ (noDrop_cons (Or.inl htag₁) (noDrop_cons (Or.inr (Or.inr (Or.inl htag₂)))
      (noDrop_cons (Or.inl htag₃) (noDrop_cons (Or.inl htag₄) (noDrop_cons (Or.inl htag₅)
      (noDrop_single (Or.inl htag₆)))))))
  · rw [shiftsV_appendV, hsh₀, shiftsV_cons, shiftsV_cons, shiftsV_cons, shiftsV_cons, shiftsV_cons, shiftsV_single,
      if_neg (by rw [htag₁]; norm_num), if_pos (Or.inl htag₂), if_neg (by rw [htag₃]; norm_num),
      if_neg (by rw [htag₄]; norm_num), if_neg (by rw [htag₅]; norm_num), if_neg (by rw [htag₆]; norm_num)]
    ring
  · rw [finalCtx_appendV, finalCtx_cons, finalCtx_cons, finalCtx_cons, finalCtx_cons, finalCtx_cons,
      finalCtx_single, hctx₆]
    simp [hP₅]
  · rw [finalCtx_appendV, finalCtx_cons, finalCtx_cons, finalCtx_cons, finalCtx_cons, finalCtx_cons,
      finalCtx_single, hctx₆]
    simp [hG₅]


/-- **(Fnrel)**: after the vector; witness bound `2n + 8 ≤ E`. -/
theorem atomNode_ok_nrel {tbl N E W n k R d Γ : V} (htbl : TableOK tbl N) (hW : WalkTable tbl) (hWp : W = walkPieces)
    (hkR : LAct.IsRel k R) (hE : 2 * n + 8 ≤ E) (hΓ : IsFormulaSet LAct Γ) (hd : VecFacts tbl E W n k Γ d) :
    ListOK tbl E ((8 : ℕ) : V) Γ (π₂ (atomNode W n 34 35 k R d)) ∧ NoDrop (π₂ (atomNode W n 34 35 k R d)) ∧
    shiftsV (π₂ (atomNode W n 34 35 k R d)) = π₁ d + 1 ∧
    neg LAct (piFact (cTV n) (^&0)) ∈ finalCtx Γ (π₂ (atomNode W n 34 35 k R d)) ∧
    neg LAct (nrelFact (^&0) (cTV k) (cTV R) (vRef 1 k)) ∈ finalCtx Γ (π₂ (atomNode W n 34 35 k R d)) := by
  obtain ⟨hok₀, hnd₀, hsh₀, hA₀⟩ := hd
  have hE8 : 8 ≤ E := le_trans le_add_self hE
  have hEn : termLen LAct (cTV n) ≤ E := termLen_cTV_le (le_trans (add_le_add le_rfl (by norm_num)) hE)
  have hE0 : termLen LAct (^&0 : V) ≤ E := termLen_fvar_le (by rw [zero_add]; exact le_trans (by norm_num) hE8)
  have hEr0 : termLen LAct (vRef 0 k) ≤ E := termLen_vRef_le (by rw [zero_add]; exact le_trans (by norm_num) hE8)
  have hEr1 : termLen LAct (vRef 1 k) ≤ E := termLen_vRef_le (le_trans (by norm_num) hE8)
  set Γ₀ := finalCtx Γ (π₂ d) with hΓ₀def
  have hΓ₀ : IsFormulaSet LAct Γ₀ := finalCtx_isFormulaSet 8 htbl hΓ hok₀
  obtain ⟨hok₁, htag₁, hctx₁, hEk, hER⟩ := relConst_ok htbl hW hWp hkR hE8 hΓ₀
  set s₁ := mkStep W (relRow R) 0 with hs₁
  have hΓ₁ : IsFormulaSet LAct (ctxAfter Γ₀ s₁) := isFormulaSet_ctxAfter 8 htbl hok₁
  have hF₁ : neg LAct (isRelFact (cTV k) (cTV R)) ∈ ctxAfter Γ₀ s₁ := by rw [hctx₁]; simp
  have hA₁ : neg LAct (tvPiFact (cTV k) (cTV n) (vRef 0 k)) ∈ ctxAfter Γ₀ s₁ := by rw [hctx₁]; simp [hA₀]
  obtain ⟨hok₂, htag₂, hctx₂⟩ := ok_qqNRelTotal (wk := cTV k) (wR := cTV R) (wv := vRef 0 k) htbl hW hWp hΓ₁
    (cTV_semiterm_LAct 0 _) hEk (cTV_semiterm_LAct 0 _) hER (isSemiterm_vRef _ _) hEr0
  rw [Nat.cast_zero, termShift_cTV, termShift_cTV, termShift_vRef, zero_add] at hctx₂
  set s₂ := mkStep W 34 ?[cTV k, cTV R, vRef 0 k] with hs₂
  have hΓ₂ : IsFormulaSet LAct (ctxAfter (ctxAfter Γ₀ s₁) s₂) := isFormulaSet_ctxAfter 8 htbl hok₂
  have hF₂ : neg LAct (isRelFact (cTV k) (cTV R)) ∈ ctxAfter (ctxAfter Γ₀ s₁) s₂ := by
    rw [hctx₂]
    have := neg_mem_setShift (isFormula_isRelFact (cTV_semiterm_LAct 0 _) (cTV_semiterm_LAct 0 _)) hF₁
    rw [shift_isRelFact (cTV_semiterm_LAct 0 _) (cTV_semiterm_LAct 0 _), termShift_cTV, termShift_cTV] at this
    simp [this]
  have hA₂ : neg LAct (tvPiFact (cTV k) (cTV n) (vRef 1 k)) ∈ ctxAfter (ctxAfter Γ₀ s₁) s₂ := by
    rw [hctx₂]
    have := neg_mem_setShift (isFormula_tvPiFact (cTV_semiterm_LAct 0 _) (cTV_semiterm_LAct 0 _) (isSemiterm_vRef _ _)) hA₁
    rw [shift_tvPiFact (cTV_semiterm_LAct 0 _) (cTV_semiterm_LAct 0 _) (isSemiterm_vRef _ _), termShift_cTV, termShift_cTV,
      termShift_vRef, zero_add] at this
    simp [this]
  have hG₂ : neg LAct (nrelFact (^&0) (cTV k) (cTV R) (vRef 1 k)) ∈ ctxAfter (ctxAfter Γ₀ s₁) s₂ := by
    rw [hctx₂]; simp
  obtain ⟨hok₃, htag₃, hctx₃⟩ := ok_isSemiformulaNRel (wn := cTV n) (wk := cTV k) (wR := cTV R) (wv := vRef 1 k) (wp := ^&0)
    htbl hW hWp hΓ₂ (cTV_semiterm_LAct 0 _) hEn (cTV_semiterm_LAct 0 _) hEk (cTV_semiterm_LAct 0 _) hER
    (isSemiterm_vRef _ _) hEr1 (by simp) hE0 hF₂ hA₂ hG₂
  set s₃ := mkStep W 35 ?[cTV n, cTV k, cTV R, vRef 1 k, ^&0] with hs₃
  have hΓ₃ : IsFormulaSet LAct (ctxAfter (ctxAfter (ctxAfter Γ₀ s₁) s₂) s₃) := isFormulaSet_ctxAfter 8 htbl hok₃
  have hS₃ : neg LAct (sigmaFact (cTV n) (^&0)) ∈ ctxAfter (ctxAfter (ctxAfter Γ₀ s₁) s₂) s₃ := by rw [hctx₃]; simp
  have hA₃ : neg LAct (tvPiFact (cTV k) (cTV n) (vRef 1 k)) ∈ ctxAfter (ctxAfter (ctxAfter Γ₀ s₁) s₂) s₃ := by
    rw [hctx₃]; simp [hA₂]
  have hG₃ : neg LAct (nrelFact (^&0) (cTV k) (cTV R) (vRef 1 k)) ∈ ctxAfter (ctxAfter (ctxAfter Γ₀ s₁) s₂) s₃ := by
    rw [hctx₃]; simp [hG₂]
  obtain ⟨hok₄, htag₄, hctx₄⟩ := ok_isSemiformulaSigmaPi (wn := cTV n) (wp := ^&0) htbl hW hWp hΓ₃
    (cTV_semiterm_LAct 0 _) hEn (by simp) hE0 hS₃
  set s₄ := mkStep W 21 ?[cTV n, ^&0] with hs₄
  have hΓ₄ : IsFormulaSet LAct (ctxAfter (ctxAfter (ctxAfter (ctxAfter Γ₀ s₁) s₂) s₃) s₄) :=
    isFormulaSet_ctxAfter 8 htbl hok₄
  have hP₄ : neg LAct (piFact (cTV n) (^&0)) ∈ ctxAfter (ctxAfter (ctxAfter (ctxAfter Γ₀ s₁) s₂) s₃) s₄ := by
    rw [hctx₄]; simp
  have hA₄ : neg LAct (tvPiFact (cTV k) (cTV n) (vRef 1 k)) ∈ ctxAfter (ctxAfter (ctxAfter (ctxAfter Γ₀ s₁) s₂) s₃) s₄ := by
    rw [hctx₄]; simp [hA₃]
  have hG₄ : neg LAct (nrelFact (^&0) (cTV k) (cTV R) (vRef 1 k)) ∈
      ctxAfter (ctxAfter (ctxAfter (ctxAfter Γ₀ s₁) s₂) s₃) s₄ := by rw [hctx₄]; simp [hG₃]
  obtain ⟨hok₅, htag₅, hctx₅⟩ := ok_isUTermVecOfSemitermVecLAct (wk := cTV k) (wn := cTV n) (wv := vRef 1 k) htbl hW hWp hΓ₄
    (cTV_semiterm_LAct 0 _) hEk (cTV_semiterm_LAct 0 _) hEn (isSemiterm_vRef _ _) hEr1 hA₄
  set s₅ := mkStep W 38 ?[cTV k, cTV n, vRef 1 k] with hs₅
  have hΓ₅ : IsFormulaSet LAct (ctxAfter (ctxAfter (ctxAfter (ctxAfter (ctxAfter Γ₀ s₁) s₂) s₃) s₄) s₅) :=
    isFormulaSet_ctxAfter 8 htbl hok₅
  have hU₅ : neg LAct (utvSigmaFact (cTV k) (vRef 1 k)) ∈
      ctxAfter (ctxAfter (ctxAfter (ctxAfter (ctxAfter Γ₀ s₁) s₂) s₃) s₄) s₅ := by rw [hctx₅]; simp
  have hP₅ : neg LAct (piFact (cTV n) (^&0)) ∈
      ctxAfter (ctxAfter (ctxAfter (ctxAfter (ctxAfter Γ₀ s₁) s₂) s₃) s₄) s₅ := by rw [hctx₅]; simp [hP₄]
  have hG₅ : neg LAct (nrelFact (^&0) (cTV k) (cTV R) (vRef 1 k)) ∈
      ctxAfter (ctxAfter (ctxAfter (ctxAfter (ctxAfter Γ₀ s₁) s₂) s₃) s₄) s₅ := by rw [hctx₅]; simp [hG₄]
  obtain ⟨hok₆, htag₆, hctx₆⟩ := ok_isUTermVecSigmaPiLAct (wk := cTV k) (wv := vRef 1 k) htbl hW hWp hΓ₅
    (cTV_semiterm_LAct 0 _) hEk (isSemiterm_vRef _ _) hEr1 hU₅
  set s₆ := mkStep W 39 ?[cTV k, vRef 1 k] with hs₆
  have hS : π₂ (atomNode W n 34 35 k R d) = appendV (π₂ d) ?[s₁, s₂, s₃, s₄, s₅, s₆] := by rw [atomNode, pi₂_pair]
  rw [hS]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact listOK_appendV hok₀ (listOK_cons hok₁ (listOK_cons hok₂ (listOK_cons hok₃ (listOK_cons hok₄
      (listOK_cons hok₅ (listOK_single hok₆))))))
  · exact noDrop_appendV hnd₀ (noDrop_cons (Or.inl htag₁) (noDrop_cons (Or.inr (Or.inr (Or.inl htag₂)))
      (noDrop_cons (Or.inl htag₃) (noDrop_cons (Or.inl htag₄) (noDrop_cons (Or.inl htag₅)
      (noDrop_single (Or.inl htag₆)))))))
  · rw [shiftsV_appendV, hsh₀, shiftsV_cons, shiftsV_cons, shiftsV_cons, shiftsV_cons, shiftsV_cons, shiftsV_single,
      if_neg (by rw [htag₁]; norm_num), if_pos (Or.inl htag₂), if_neg (by rw [htag₃]; norm_num),
      if_neg (by rw [htag₄]; norm_num), if_neg (by rw [htag₅]; norm_num), if_neg (by rw [htag₆]; norm_num)]
    ring
  · rw [finalCtx_appendV, finalCtx_cons, finalCtx_cons, finalCtx_cons, finalCtx_cons, finalCtx_cons,
      finalCtx_single, hctx₆]
    simp [hP₅]
  · rw [finalCtx_appendV, finalCtx_cons, finalCtx_cons, finalCtx_cons, finalCtx_cons, finalCtx_cons,
      finalCtx_single, hctx₆]
    simp [hG₅]


end formulaNodes

/-! ### 5.4 The formula walk is applicable (D3 for formulas) -/

section formulaWalkOK

lemma rel_arity_le_two {k R : V} (hkR : LAct.IsRel k R) : k ≤ 2 := by
  rcases isRel_LAct_iff_V.mp hkR with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> exact le_rfl

/-- **The invariant of the formula walk** at `(n, r)`: for every witness bound
`E ≥ 2n + 2|r| + 8`, the walk's facts at every context and the count bound `descCountF + 1 ≤ 2|r|`. -/
def FormOK (tbl W n r : V) : Prop :=
  ∀ E, 2 * n + 2 * formulaLen LAct r + 8 ≤ E →
    FormFacts tbl E W n (descFw W n r) ∧ descCountF W n r + 1 ≤ 2 * formulaLen LAct r

instance formOK_definable : 𝚷₁-Relation₄ (FormOK : V → V → V → V → Prop) := by
  unfold FormOK FormFacts descCountF; definability

/-- **D3 for formulas — the invariant holds for every semiformula.** -/
theorem formOK_of_isSemiformula {tbl N W : V} (htbl : TableOK tbl N) (hW : WalkTable tbl) (hWp : W = walkPieces) :
    ∀ {n r : V}, IsSemiformula LAct n r → FormOK tbl W n r := by
  intro n r
  apply IsSemiformula.pi1_structural_induction (P := fun n r ↦ FormOK tbl W n r)
  · definability
  · -- rel
    intro n k R v hkR hv E hE
    have hk := rel_arity_le_two hkR
    have hlen : formulaLen LAct (^rel k R v) = listSum (termLenVec LAct k v) + 1 := formulaLen_rel hkR hv.isUTerm
    have hES : 2 * n + 2 * listSum (termLenVec LAct k v) + 8 ≤ E := by
      refine le_trans ?_ hE
      rw [hlen]
      exact add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_left le_self_add zero_le)) le_rfl
    have hE' : 2 * n + 8 ≤ E := le_trans (add_le_add le_self_add le_rfl) hES
    obtain ⟨_, hcnt, hF⟩ := descVecAux_ok htbl hW hWp hk hv
      (fun i hi ↦ termOK_of_isSemiterm htbl hW hWp n _ (hv.nth hi)) hES k le_rfl
    have htl : takeLast v k = v := by rw [← hv.lh]; exact takeLast_len_self v
    rw [htl] at hcnt
    refine ⟨?_, ?_⟩
    · intro Γ hΓ
      rw [descFw_rel W n hkR hv]
      obtain ⟨a, b, c, d, _⟩ := atomNode_ok_rel htbl hW hWp hkR hE' hΓ (hF Γ hΓ)
      exact ⟨a, b, by rw [c, atomNode, pi₁_pair], d⟩
    · rw [descCountF, descFw_rel W n hkR hv, atomNode, pi₁_pair, hlen, mul_add, mul_one, add_assoc, one_add_one_eq_two]
      exact add_le_add hcnt le_rfl
  · -- nrel
    intro n k R v hkR hv E hE
    have hk := rel_arity_le_two hkR
    have hlen : formulaLen LAct (^nrel k R v) = listSum (termLenVec LAct k v) + 1 := formulaLen_nrel hkR hv.isUTerm
    have hES : 2 * n + 2 * listSum (termLenVec LAct k v) + 8 ≤ E := by
      refine le_trans ?_ hE
      rw [hlen]
      exact add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_left le_self_add zero_le)) le_rfl
    have hE' : 2 * n + 8 ≤ E := le_trans (add_le_add le_self_add le_rfl) hES
    obtain ⟨_, hcnt, hF⟩ := descVecAux_ok htbl hW hWp hk hv
      (fun i hi ↦ termOK_of_isSemiterm htbl hW hWp n _ (hv.nth hi)) hES k le_rfl
    have htl : takeLast v k = v := by rw [← hv.lh]; exact takeLast_len_self v
    rw [htl] at hcnt
    refine ⟨?_, ?_⟩
    · intro Γ hΓ
      rw [descFw_nrel W n hkR hv]
      obtain ⟨a, b, c, d, _⟩ := atomNode_ok_nrel htbl hW hWp hkR hE' hΓ (hF Γ hΓ)
      exact ⟨a, b, by rw [c, atomNode, pi₁_pair], d⟩
    · rw [descCountF, descFw_nrel W n hkR hv, atomNode, pi₁_pair, hlen, mul_add, mul_one, add_assoc, one_add_one_eq_two]
      exact add_le_add hcnt le_rfl
  · -- verum
    intro n E hE
    have hE' : 2 * n + 8 ≤ E := le_trans (add_le_add le_self_add le_rfl) hE
    refine ⟨?_, ?_⟩
    · intro Γ hΓ
      rw [descFw_verum]
      obtain ⟨a, b, c, d, _⟩ := constNode_ok_verum htbl hW hWp hE' hΓ
      exact ⟨a, b, by rw [c, constNode, pi₁_pair], d⟩
    · rw [descCountF, descFw_verum, constNode, pi₁_pair, formulaLen_verum, mul_one, one_add_one_eq_two]
  · -- falsum
    intro n E hE
    have hE' : 2 * n + 8 ≤ E := le_trans (add_le_add le_self_add le_rfl) hE
    refine ⟨?_, ?_⟩
    · intro Γ hΓ
      rw [descFw_falsum]
      obtain ⟨a, b, c, d, _⟩ := constNode_ok_falsum htbl hW hWp hE' hΓ
      exact ⟨a, b, by rw [c, constNode, pi₁_pair], d⟩
    · rw [descCountF, descFw_falsum, constNode, pi₁_pair, formulaLen_falsum, mul_one, one_add_one_eq_two]
  · -- and
    intro n p q hp hq ihp ihq E hE
    have hlen : formulaLen LAct (p ^⋏ q) = formulaLen LAct p + formulaLen LAct q + 1 :=
      formulaLen_and hp.isUFormula hq.isUFormula
    rw [hlen] at hE
    have hEp : 2 * n + 2 * formulaLen LAct p + 8 ≤ E :=
      le_trans (add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_left (le_trans le_self_add le_self_add) zero_le)) le_rfl) hE
    have hEq : 2 * n + 2 * formulaLen LAct q + 8 ≤ E :=
      le_trans (add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_left (le_trans le_add_self le_self_add) zero_le)) le_rfl) hE
    obtain ⟨hFp, hcp⟩ := ihp E hEp
    obtain ⟨hFq, hcq⟩ := ihq E hEq
    have hcq' : π₁ (descFw W n q) + 1 ≤ 2 * formulaLen LAct q := hcq
    have hEb : 2 * n + π₁ (descFw W n q) + 8 ≤ E := by
      calc 2 * n + π₁ (descFw W n q) + 8 = 2 * n + (π₁ (descFw W n q) + 1) + 7 := by ring
        _ ≤ 2 * n + 2 * formulaLen LAct q + 7 := add_le_add (add_le_add le_rfl hcq') le_rfl
        _ ≤ 2 * n + 2 * formulaLen LAct q + 8 := add_le_add le_rfl (by norm_num)
        _ ≤ E := hEq
    refine ⟨?_, ?_⟩
    · intro Γ hΓ
      rw [descFw_and W n hp hq]
      obtain ⟨a, b, c, d, _⟩ := binNode_ok_and htbl hW hWp hEb hFp hFq hΓ
      exact ⟨a, b, by rw [c, binNode, pi₁_pair], d⟩
    · rw [descCountF_and W n hp hq, hlen]
      calc descCountF W n p + descCountF W n q + 1 + 1
          = (descCountF W n p + 1) + (descCountF W n q + 1) := by ring
        _ ≤ 2 * formulaLen LAct p + 2 * formulaLen LAct q := add_le_add hcp hcq
        _ ≤ 2 * (formulaLen LAct p + formulaLen LAct q + 1) := by rw [mul_add, mul_add, mul_one]; exact le_self_add
  · -- or
    intro n p q hp hq ihp ihq E hE
    have hlen : formulaLen LAct (p ^⋎ q) = formulaLen LAct p + formulaLen LAct q + 1 :=
      formulaLen_or hp.isUFormula hq.isUFormula
    rw [hlen] at hE
    have hEp : 2 * n + 2 * formulaLen LAct p + 8 ≤ E :=
      le_trans (add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_left (le_trans le_self_add le_self_add) zero_le)) le_rfl) hE
    have hEq : 2 * n + 2 * formulaLen LAct q + 8 ≤ E :=
      le_trans (add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_left (le_trans le_add_self le_self_add) zero_le)) le_rfl) hE
    obtain ⟨hFp, hcp⟩ := ihp E hEp
    obtain ⟨hFq, hcq⟩ := ihq E hEq
    have hcq' : π₁ (descFw W n q) + 1 ≤ 2 * formulaLen LAct q := hcq
    have hEb : 2 * n + π₁ (descFw W n q) + 8 ≤ E := by
      calc 2 * n + π₁ (descFw W n q) + 8 = 2 * n + (π₁ (descFw W n q) + 1) + 7 := by ring
        _ ≤ 2 * n + 2 * formulaLen LAct q + 7 := add_le_add (add_le_add le_rfl hcq') le_rfl
        _ ≤ 2 * n + 2 * formulaLen LAct q + 8 := add_le_add le_rfl (by norm_num)
        _ ≤ E := hEq
    refine ⟨?_, ?_⟩
    · intro Γ hΓ
      rw [descFw_or W n hp hq]
      obtain ⟨a, b, c, d, _⟩ := binNode_ok_or htbl hW hWp hEb hFp hFq hΓ
      exact ⟨a, b, by rw [c, binNode, pi₁_pair], d⟩
    · rw [descCountF, descFw_or W n hp hq, binNode, pi₁_pair, hlen]
      calc π₁ (descFw W n p) + π₁ (descFw W n q) + 1 + 1
          = (π₁ (descFw W n p) + 1) + (π₁ (descFw W n q) + 1) := by ring
        _ ≤ 2 * formulaLen LAct p + 2 * formulaLen LAct q := add_le_add hcp hcq
        _ ≤ 2 * (formulaLen LAct p + formulaLen LAct q + 1) := by rw [mul_add, mul_add, mul_one]; exact le_self_add
  · -- all
    intro n p hp ih E hE
    have hlen : formulaLen LAct (^∀ p) = formulaLen LAct p + 1 := formulaLen_all hp.isUFormula
    rw [hlen] at hE
    have hEp : 2 * (n + 1) + 2 * formulaLen LAct p + 8 ≤ E := by
      refine le_trans (le_of_eq ?_) hE; ring
    have hE' : 2 * n + 8 ≤ E := le_trans (add_le_add le_self_add le_rfl) hE
    obtain ⟨hFp, hcp⟩ := ih E hEp
    refine ⟨?_, ?_⟩
    · intro Γ hΓ
      rw [descFw_all W n hp]
      obtain ⟨a, b, c, d, _⟩ := quantNode_ok_all htbl hW hWp hE' hFp hΓ
      exact ⟨a, b, by rw [c, quantNode, pi₁_pair], d⟩
    · rw [descCountF_all W n hp, hlen, mul_add, mul_one, add_assoc, one_add_one_eq_two]
      exact add_le_add (le_trans le_self_add hcp) le_rfl
  · -- exs
    intro n p hp ih E hE
    have hlen : formulaLen LAct (^∃ p) = formulaLen LAct p + 1 := formulaLen_exs hp.isUFormula
    rw [hlen] at hE
    have hEp : 2 * (n + 1) + 2 * formulaLen LAct p + 8 ≤ E := by
      refine le_trans (le_of_eq ?_) hE; ring
    have hE' : 2 * n + 8 ≤ E := le_trans (add_le_add le_self_add le_rfl) hE
    obtain ⟨hFp, hcp⟩ := ih E hEp
    refine ⟨?_, ?_⟩
    · intro Γ hΓ
      rw [descFw_exs W n hp]
      obtain ⟨a, b, c, d, _⟩ := quantNode_ok_exs htbl hW hWp hE' hFp hΓ
      exact ⟨a, b, by rw [c, quantNode, pi₁_pair], d⟩
    · rw [descCountF, descFw_exs W n hp, quantNode, pi₁_pair, hlen, mul_add, mul_one, add_assoc, one_add_one_eq_two]
      exact add_le_add (le_trans le_self_add hcp) le_rfl

/-- **D3 for formulas, unpacked**: the formula walk from any formula-set context is applicable
step by step, drops nothing, introduces `descCountF` eigenvariables (`≤ 2|r| − 1`), and leaves
`(isSemiformula LAct).pi n &0` in the final context. -/
theorem describeF_ok {tbl N : V} (htbl : TableOK tbl N) (hW : WalkTable tbl) {n r : V} (hr : IsSemiformula LAct n r)
    {E : V} (hE : 2 * n + 2 * formulaLen LAct r + 8 ≤ E) {Γ : V} (hΓ : IsFormulaSet LAct Γ) :
    ListOK tbl E ((8 : ℕ) : V) Γ (describeF walkPieces n r) ∧ NoDrop (describeF walkPieces n r) ∧
    shiftsV (describeF walkPieces n r) = descCountF walkPieces n r ∧
    descCountF walkPieces n r + 1 ≤ 2 * formulaLen LAct r ∧
    neg LAct (piFact (cTV n) (^&0)) ∈ finalCtx Γ (describeF walkPieces n r) := by
  obtain ⟨hTF, hcnt⟩ := formOK_of_isSemiformula htbl hW rfl hr E hE
  obtain ⟨a, b, c, d⟩ := hTF Γ hΓ
  exact ⟨a, b, c, hcnt, d⟩

/-- **The formula walk as a derivation**: with a continuation `d` deriving the final context, the
chain derives `Γ`. -/
theorem describeF_chain {tbl N : V} (htbl : TableOK tbl N) (hW : WalkTable tbl) {n r : V} (hr : IsSemiformula LAct n r)
    {E : V} (hE : 2 * n + 2 * formulaLen LAct r + 8 ≤ E) {Γ : V} (hΓ : IsFormulaSet LAct Γ) {d : V}
    (hd : DerivationOf TAct d (finalCtx Γ (describeF walkPieces n r))) :
    DerivationOf TAct (chainCode tbl Γ (describeF walkPieces n r) d) Γ :=
  chainCode_proof 8 htbl (describeF_ok htbl hW hr hE hΓ).1 hd

/-! ### 5.5 The final-context facts (D4): the root's shape fact, per constructor -/

theorem describeF_shape_and {tbl N : V} (htbl : TableOK tbl N) (hW : WalkTable tbl) {n p q : V}
    (hp : IsSemiformula LAct n p) (hq : IsSemiformula LAct n q)
    {E : V} (hE : 2 * n + 2 * formulaLen LAct (p ^⋏ q) + 8 ≤ E) {Γ : V} (hΓ : IsFormulaSet LAct Γ) :
    neg LAct (andFact (^&0) (^&(descCountF walkPieces n q + 1)) (^&1)) ∈ finalCtx Γ (describeF walkPieces n (p ^⋏ q)) := by
  have hlen : formulaLen LAct (p ^⋏ q) = formulaLen LAct p + formulaLen LAct q + 1 :=
    formulaLen_and hp.isUFormula hq.isUFormula
  rw [hlen] at hE
  have hEp : 2 * n + 2 * formulaLen LAct p + 8 ≤ E :=
    le_trans (add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_left (le_trans le_self_add le_self_add) zero_le)) le_rfl) hE
  have hEq : 2 * n + 2 * formulaLen LAct q + 8 ≤ E :=
    le_trans (add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_left (le_trans le_add_self le_self_add) zero_le)) le_rfl) hE
  obtain ⟨hFp, _⟩ := formOK_of_isSemiformula htbl hW rfl hp E hEp
  obtain ⟨hFq, hcq⟩ := formOK_of_isSemiformula htbl hW rfl hq E hEq
  have hcq' : π₁ (descFw walkPieces n q) + 1 ≤ 2 * formulaLen LAct q := hcq
  have hEb : 2 * n + π₁ (descFw walkPieces n q) + 8 ≤ E := by
    calc 2 * n + π₁ (descFw walkPieces n q) + 8 = 2 * n + (π₁ (descFw walkPieces n q) + 1) + 7 := by ring
      _ ≤ 2 * n + 2 * formulaLen LAct q + 7 := add_le_add (add_le_add le_rfl hcq') le_rfl
      _ ≤ 2 * n + 2 * formulaLen LAct q + 8 := add_le_add le_rfl (by norm_num)
      _ ≤ E := hEq
  rw [describeF, descFw_and _ n hp hq]
  exact (binNode_ok_and htbl hW rfl hEb hFp hFq hΓ).2.2.2.2

theorem describeF_shape_all {tbl N : V} (htbl : TableOK tbl N) (hW : WalkTable tbl) {n p : V}
    (hp : IsSemiformula LAct (n + 1) p)
    {E : V} (hE : 2 * n + 2 * formulaLen LAct (^∀ p) + 8 ≤ E) {Γ : V} (hΓ : IsFormulaSet LAct Γ) :
    neg LAct (allFact (^&0) (^&1)) ∈ finalCtx Γ (describeF walkPieces n (^∀ p)) := by
  have hlen : formulaLen LAct (^∀ p) = formulaLen LAct p + 1 := formulaLen_all hp.isUFormula
  rw [hlen] at hE
  have hEp : 2 * (n + 1) + 2 * formulaLen LAct p + 8 ≤ E := by refine le_trans (le_of_eq ?_) hE; ring
  have hE' : 2 * n + 8 ≤ E := le_trans (add_le_add le_self_add le_rfl) hE
  obtain ⟨hFp, _⟩ := formOK_of_isSemiformula htbl hW rfl hp E hEp
  rw [describeF, descFw_all _ n hp]
  exact (quantNode_ok_all htbl hW rfl hE' hFp hΓ).2.2.2.2

theorem describeF_shape_verum {tbl N : V} (htbl : TableOK tbl N) (hW : WalkTable tbl) {n : V}
    {E : V} (hE : 2 * n + 8 ≤ E) {Γ : V} (hΓ : IsFormulaSet LAct Γ) :
    neg LAct (verumFact (^&0)) ∈ finalCtx Γ (describeF walkPieces n ^⊤) := by
  rw [describeF, descFw_verum]
  exact (constNode_ok_verum htbl hW rfl hE hΓ).2.2.2.2

theorem describeF_shape_rel {tbl N : V} (htbl : TableOK tbl N) (hW : WalkTable tbl) {n k R v : V}
    (hkR : LAct.IsRel k R) (hv : IsSemitermVec LAct k n v)
    {E : V} (hE : 2 * n + 2 * formulaLen LAct (^rel k R v) + 8 ≤ E) {Γ : V} (hΓ : IsFormulaSet LAct Γ) :
    neg LAct (relFact (^&0) (cTV k) (cTV R) (vRef 1 k)) ∈ finalCtx Γ (describeF walkPieces n (^rel k R v)) := by
  have hk := rel_arity_le_two hkR
  have hlen : formulaLen LAct (^rel k R v) = listSum (termLenVec LAct k v) + 1 := formulaLen_rel hkR hv.isUTerm
  have hES : 2 * n + 2 * listSum (termLenVec LAct k v) + 8 ≤ E := by
    refine le_trans ?_ hE
    rw [hlen]
    exact add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_left le_self_add zero_le)) le_rfl
  have hE' : 2 * n + 8 ≤ E := le_trans (add_le_add le_self_add le_rfl) hES
  obtain ⟨_, _, hF⟩ := descVecAux_ok htbl hW rfl hk hv
    (fun i hi ↦ termOK_of_isSemiterm htbl hW rfl n _ (hv.nth hi)) hES k le_rfl
  rw [describeF, descFw_rel _ n hkR hv]
  exact (atomNode_ok_rel htbl hW rfl hkR hE' hΓ (hF Γ hΓ)).2.2.2.2

end formulaWalkOK

/-! ## Part 6 — the size of the walk (D5, step counts)

`len (describeT W n t) + 4 ≤ 12 · termLen t` and `len (describeF W n r) + 4 ≤ 12 · formulaLen r`
(DESIGN §4.3's `stepCount ≤ 8|r|` counts constants as one symbol; a constant `func 0 f 0` emits
8 steps, so the honest linear bound has slope 12 with slack 4). -/

section stepCount

lemma len_ltAux (W n z : V) : ∀ j, len (ltAux W n z j) = j + 1 := by
  intro j
  induction j using ISigma1.sigma1_succ_induction with
  | hP => definability
  | zero => rw [ltAux_zero, len_adjoin, len_nil]
  | succ j ih => rw [ltAux_succ, len_concat, ih]

lemma len_ltSteps (W n z : V) : len (ltSteps W n z) = z + 1 := len_ltAux W n z z

lemma len_bvarNode (W n z : V) : len (π₂ (bvarNode W n z)) = z + 4 := by
  rw [bvarNode, pi₂_pair, len_appendV, len_ltSteps]; simp; ring
lemma len_fvarNode (W n x : V) : len (π₂ (fvarNode W n x)) = 3 := by
  rw [fvarNode, pi₂_pair]; simp; norm_num
lemma len_nilNode (W n : V) : len (π₂ (nilNode W n)) = 2 := by
  rw [nilNode, pi₂_pair]; simp; norm_num
lemma len_adjNode (W n j p ih : V) : len (π₂ (adjNode W n j p ih)) = len (π₂ ih) + len (π₂ p) + 3 := by
  rw [adjNode, pi₂_pair, len_appendV, len_appendV]; simp; ring
lemma len_funcNode (W n k f d : V) : len (π₂ (funcNode W n k f d)) = len (π₂ d) + 6 := by
  rw [funcNode, pi₂_pair, len_appendV]; simp; norm_num
lemma len_constNode (W n i₁ i₂ : V) : len (π₂ (constNode W n i₁ i₂)) = 3 := by
  rw [constNode, pi₂_pair]; simp; norm_num
lemma len_binNode (W n i₁ i₂ yp yq : V) : len (π₂ (binNode W n i₁ i₂ yp yq)) = len (π₂ yp) + len (π₂ yq) + 3 := by
  rw [binNode, pi₂_pair, len_appendV, len_appendV]; simp; ring
lemma len_quantNode (W n i₁ i₂ yp : V) : len (π₂ (quantNode W n i₁ i₂ yp)) = len (π₂ yp) + 3 := by
  rw [quantNode, pi₂_pair, len_appendV]; simp; norm_num
lemma len_atomNode (W n i₁ i₂ k R d : V) : len (π₂ (atomNode W n i₁ i₂ k R d)) = len (π₂ d) + 6 := by
  rw [atomNode, pi₂_pair, len_appendV]; simp; norm_num

/-- The vector walk over the last `j` entries: `len + 2 ≤ 12 · Σ termLen + 4`. -/
lemma len_descVecAux_le {W n k v : V} (hv : IsSemitermVec LAct k n v)
    (ih : ∀ i < k, len (π₂ (descT W n v.[i])) + 4 ≤ 12 * termLen LAct v.[i]) :
    ∀ j ≤ k, IsUTermVec LAct j (takeLast v j) ∧
      len (π₂ (descVecAux W n (descTVec W n k v) j)) + 2 ≤ 12 * listSum (termLenVec LAct j (takeLast v j)) + 4 := by
  intro j
  induction j using ISigma1.pi1_succ_induction with
  | hP => definability
  | zero => intro _; refine ⟨by simp, ?_⟩; rw [descVecAux_zero, len_nilNode]; simp; norm_num
  | succ j ihj =>
    intro hj
    obtain ⟨hU, hl⟩ := ihj (le_trans le_self_add hj)
    have hvlen : len v = k := hv.lh
    have hjk : j < len v := by rw [hvlen]; exact lt_of_lt_of_le (lt_add_one j) hj
    have hk0 : (0 : V) < k := lt_of_lt_of_le (lt_of_lt_of_le _root_.zero_lt_one le_add_self) hj
    have hi : k - (j + 1) < k := tsub_lt_self hk0 (lt_of_lt_of_le _root_.zero_lt_one le_add_self)
    have ht : IsSemiterm LAct n v.[k - (j + 1)] := hv.nth hi
    have hnth : nthFromEnd (descTVec W n k v) j = descT W n v.[k - (j + 1)] := by
      rw [nthFromEnd_eq (a := k - (j + 1)) (by rw [len_descTVec W n hv.isUTerm, tsub_add_cancel_of_le hj]),
        nth_descTVec W n hv.isUTerm hi]
    have htake : takeLast v (j + 1) = v.[k - (j + 1)] ∷ takeLast v j := by
      rw [takeLast_succ_of_lt hjk, hvlen]
    refine ⟨by rw [htake]; exact hU.adjoin ht.isUTerm, ?_⟩
    rw [descVecAux_succ, hnth, len_adjNode, htake, termLenVec_cons ht.isUTerm hU, listSum_adjoin, mul_add]
    have h1 := ih _ hi
    have h2 := add_le_add hl h1
    calc len (π₂ (descVecAux W n (descTVec W n k v) j)) + len (π₂ (descT W n v.[k - (j + 1)])) + 3 + 2
        ≤ (len (π₂ (descVecAux W n (descTVec W n k v) j)) + 2) + (len (π₂ (descT W n v.[k - (j + 1)])) + 4) := by
          rw [show (len (π₂ (descVecAux W n (descTVec W n k v) j)) + 2) + (len (π₂ (descT W n v.[k - (j + 1)])) + 4)
              = len (π₂ (descVecAux W n (descTVec W n k v) j)) + len (π₂ (descT W n v.[k - (j + 1)])) + 3 + 2 + 1 by ring]
          exact le_self_add
      _ ≤ (12 * listSum (termLenVec LAct j (takeLast v j)) + 4) + 12 * termLen LAct v.[k - (j + 1)] := h2
      _ = 12 * termLen LAct v.[k - (j + 1)] + 12 * listSum (termLenVec LAct j (takeLast v j)) + 4 := by ring

/-- **The term walk has `≤ 12|t| − 4` steps.** -/
theorem len_describeT_le (W n : V) : ∀ t, IsSemiterm LAct n t → len (describeT W n t) + 4 ≤ 12 * termLen LAct t := by
  intro t ht
  refine IsSemiterm.induction 𝚷 (P := fun t ↦ len (describeT W n t) + 4 ≤ 12 * termLen LAct t) ?_ ?_ ?_ ?_ t ht
  · definability
  · intro z hz
    show len (describeT W n (^#z)) + 4 ≤ 12 * termLen LAct (^#z)
    rw [describeT, descT_bvar, len_bvarNode, termLen_bvar]
    calc z + 4 + 4 = z + 8 := by ring
      _ ≤ 12 * z + 12 := add_le_add (le_trans (le_of_eq (one_mul z).symm) (mul_le_mul_of_nonneg_right (by norm_num) zero_le)) (by norm_num)
      _ = 12 * (z + 1) := by ring
  · intro x
    show len (describeT W n (^&x)) + 4 ≤ 12 * termLen LAct (^&x)
    rw [describeT, descT_fvar, len_fvarNode, termLen_fvar]
    calc (3 : V) + 4 = 7 := by norm_num
      _ ≤ 12 := by norm_num
      _ ≤ 12 * x + 12 := le_add_self
      _ = 12 * (x + 1) := by ring
  · intro k f v hkf hv ih
    obtain ⟨_, hl⟩ := len_descVecAux_le hv (fun i hi ↦ by
      have := ih i hi; rwa [describeT] at this) k le_rfl
    have htl : takeLast v k = v := by rw [← hv.lh]; exact takeLast_len_self v
    rw [htl] at hl
    show len (describeT W n (^func k f v)) + 4 ≤ 12 * termLen LAct (^func k f v)
    rw [describeT, descT_func W n hkf hv.isUTerm, len_funcNode, termLen_func hkf hv.isUTerm]
    calc len (π₂ (descVecAux W n (descTVec W n k v) k)) + 6 + 4
        = (len (π₂ (descVecAux W n (descTVec W n k v) k)) + 2) + 8 := by ring
      _ ≤ (12 * listSum (termLenVec LAct k v) + 4) + 8 := add_le_add hl le_rfl
      _ = 12 * (listSum (termLenVec LAct k v) + 1) := by ring

/-- **The formula walk has `≤ 12|r| − 4` steps.** -/
theorem len_describeF_le (W : V) : ∀ {n r : V}, IsSemiformula LAct n r →
    len (describeF W n r) + 4 ≤ 12 * formulaLen LAct r := by
  intro n r
  apply IsSemiformula.pi1_structural_induction (P := fun n r ↦ len (describeF W n r) + 4 ≤ 12 * formulaLen LAct r)
  · definability
  · intro n k R v hkR hv
    obtain ⟨_, hl⟩ := len_descVecAux_le hv (fun i hi ↦ len_describeT_le W n _ (hv.nth hi)) k le_rfl
    have htl : takeLast v k = v := by rw [← hv.lh]; exact takeLast_len_self v
    rw [htl] at hl
    rw [describeF, descFw_rel W n hkR hv, len_atomNode, formulaLen_rel hkR hv.isUTerm]
    calc len (π₂ (descVecAux W n (descTVec W n k v) k)) + 6 + 4
        = (len (π₂ (descVecAux W n (descTVec W n k v) k)) + 2) + 8 := by ring
      _ ≤ (12 * listSum (termLenVec LAct k v) + 4) + 8 := add_le_add hl le_rfl
      _ = 12 * (listSum (termLenVec LAct k v) + 1) := by ring
  · intro n k R v hkR hv
    obtain ⟨_, hl⟩ := len_descVecAux_le hv (fun i hi ↦ len_describeT_le W n _ (hv.nth hi)) k le_rfl
    have htl : takeLast v k = v := by rw [← hv.lh]; exact takeLast_len_self v
    rw [htl] at hl
    rw [describeF, descFw_nrel W n hkR hv, len_atomNode, formulaLen_nrel hkR hv.isUTerm]
    calc len (π₂ (descVecAux W n (descTVec W n k v) k)) + 6 + 4
        = (len (π₂ (descVecAux W n (descTVec W n k v) k)) + 2) + 8 := by ring
      _ ≤ (12 * listSum (termLenVec LAct k v) + 4) + 8 := add_le_add hl le_rfl
      _ = 12 * (listSum (termLenVec LAct k v) + 1) := by ring
  · intro n; rw [describeF, descFw_verum, len_constNode, formulaLen_verum]; norm_num
  · intro n; rw [describeF, descFw_falsum, len_constNode, formulaLen_falsum]; norm_num
  · intro n p q hp hq ihp ihq
    rw [describeF, descFw_and W n hp hq, len_binNode, formulaLen_and hp.isUFormula hq.isUFormula]
    rw [describeF] at ihp ihq
    calc len (π₂ (descFw W n p)) + len (π₂ (descFw W n q)) + 3 + 4
        ≤ (len (π₂ (descFw W n p)) + 4) + (len (π₂ (descFw W n q)) + 4) := by
          rw [show (len (π₂ (descFw W n p)) + 4) + (len (π₂ (descFw W n q)) + 4)
              = len (π₂ (descFw W n p)) + len (π₂ (descFw W n q)) + 3 + 4 + 1 by ring]
          exact le_self_add
      _ ≤ 12 * formulaLen LAct p + 12 * formulaLen LAct q := add_le_add ihp ihq
      _ ≤ 12 * (formulaLen LAct p + formulaLen LAct q + 1) := by rw [mul_add, mul_add, mul_one]; exact le_self_add
  · intro n p q hp hq ihp ihq
    rw [describeF, descFw_or W n hp hq, len_binNode, formulaLen_or hp.isUFormula hq.isUFormula]
    rw [describeF] at ihp ihq
    calc len (π₂ (descFw W n p)) + len (π₂ (descFw W n q)) + 3 + 4
        ≤ (len (π₂ (descFw W n p)) + 4) + (len (π₂ (descFw W n q)) + 4) := by
          rw [show (len (π₂ (descFw W n p)) + 4) + (len (π₂ (descFw W n q)) + 4)
              = len (π₂ (descFw W n p)) + len (π₂ (descFw W n q)) + 3 + 4 + 1 by ring]
          exact le_self_add
      _ ≤ 12 * formulaLen LAct p + 12 * formulaLen LAct q := add_le_add ihp ihq
      _ ≤ 12 * (formulaLen LAct p + formulaLen LAct q + 1) := by rw [mul_add, mul_add, mul_one]; exact le_self_add
  · intro n p hp ih
    rw [describeF, descFw_all W n hp, len_quantNode, formulaLen_all hp.isUFormula]
    rw [describeF] at ih
    calc len (π₂ (descFw W (n + 1) p)) + 3 + 4 ≤ (len (π₂ (descFw W (n + 1) p)) + 4) + 12 := by
          rw [show (len (π₂ (descFw W (n + 1) p)) + 4) + 12 = len (π₂ (descFw W (n + 1) p)) + 3 + 4 + 9 by ring]
          exact le_self_add
      _ ≤ 12 * formulaLen LAct p + 12 := add_le_add ih le_rfl
      _ = 12 * (formulaLen LAct p + 1) := by ring
  · intro n p hp ih
    rw [describeF, descFw_exs W n hp, len_quantNode, formulaLen_exs hp.isUFormula]
    rw [describeF] at ih
    calc len (π₂ (descFw W (n + 1) p)) + 3 + 4 ≤ (len (π₂ (descFw W (n + 1) p)) + 4) + 12 := by
          rw [show (len (π₂ (descFw W (n + 1) p)) + 4) + 12 = len (π₂ (descFw W (n + 1) p)) + 3 + 4 + 9 by ring]
          exact le_self_add
      _ ≤ 12 * formulaLen LAct p + 12 := add_le_add ih le_rfl
      _ = 12 * (formulaLen LAct p + 1) := by ring

end stepCount

end ArithS
