import ArithS.Necessitation.Lib.Nodes

/-!
# ArithS.Necessitation.Lib.Bridge — `ℒₒᵣ`/`LAct` code bridges for the axiom recognizer

`DESIGN_inner_necessitation.md` §3.6 and the `indRec` section of `Lib/Nodes.lean`: the
induction-scheme recognizer `lib_indRec` is stated over the `ℒₒᵣ`-INDEXED graph objects
(`(isUFormula ℒₒᵣ).pi`, `(shiftGraph ℒₒᵣ)`, `(bvGraph ℒₒᵣ)`, `(substsGraph ℒₒᵣ)`,
`(isSemiformula ℒₒᵣ).pi 1`, `indBodyValGraph` — itself a chain of `substsGraph ℒₒᵣ`/`impGraph ℒₒᵣ`/
`qqAllDef`), the shape Foundation's `InductionR`/`chUniv` forces, while every other row of the
library (`Lib/Formulas.lean`, `Lib/Nodes.lean`) speaks the `LAct`-indexed vocabulary. Codes are
the same numbers — `LAct` keeps every `ℒₒᵣ` symbol code (`ArithS.LangAct`) — so on a code that
IS an `ℒₒᵣ`-formula the two readings agree. This file proves that agreement and packages it as
library rows.

**V-generic lemmas (§A).** `LAct.IsRel = (ℒₒᵣ).IsRel` (same two symbols); `(ℒₒᵣ).IsFunc k f ↔
LAct.IsFunc k f ∧ f < 2`; `IsUTerm/IsUTermVec/IsSemiterm/IsSemitermVec/IsUFormula/IsSemiformula
ℒₒᵣ → LAct`; and the LANGUAGE INVARIANCE of every `L`-indexed code operation on `ℒₒᵣ`-codes —
`termBV`, `termShift`, `termBShift`, `termSubst` (and their `Vec` forms), `qVec`, `bv`, `neg`,
`shift`, `subst`, `imp`, `substs1`, `free` — each `_LAct_eq : op LAct … = op ℒₒᵣ …`. None is
`rfl`: every one of these is `(construction L).result`, a fixpoint recursion whose atom clause
consults `L.IsFunc`/`L.IsRel` and whose term clauses recurse through the `L`-indexed term
functions; the equalities are by `IsUTerm.induction` / `IsUFormula.ISigma1.pi1_succ_induction`
with the two languages' constructor equations. (`qqAlls`, `fvarVec`, `qqAllDef`, `qqAndDef`,
`adjoinDef`, `indBodyVal` are NOT `L`-indexed — nothing to bridge.) The converse
`IsUFormula LAct p → IsUFormula ℒₒᵣ p` is FALSE (`c_C` is an `LAct`-term): `ℒₒᵣ`-ness has to be
ESTABLISHED bottom-up, which is what the `ℒₒᵣ` formation rows (§B.2) are for.

**Library rows (§B).** The `Lib` convention of `Sets`/`Formulas`/`Nodes` (body in index order,
Δ₁ hypotheses `.pi`, conclusions `.sigma`):
1. language lifts `ℒₒᵣ → LAct` (`isSemiformulaLActOfLOR`, `isUFormulaLActOfLOR`,
   `isSemitermVecLActOfLOR`, `isSemitermLActOfLOR`) and the symbol rows (`isRelLOROfLAct`,
   `isRelLActOfLOR`, `isFuncLOROfLAct`, `isFuncLActOfLOR`);
2. the FORMATION rows re-indexed at `ℒₒᵣ` (`isSemiformulaRelOR … isSemiformulaExsOR`,
   `isSemitermFuncOR/BvarOR/FvarOR`, `isSemitermVecNilOR/AdjoinOR`) — how a fragment
   propagates "`ℒₒᵣ`-only" bottom-up — with the two auxiliary-vector rows
   `fvarVecSemitermVecOR` (`fvarVec m` is an `ℒₒᵣ`-term vector) and
   `indSubstConst0VecOR`/`indSubstConst1VecOR` (the two substitution vectors inside
   `indBodyValGraph`);
3. the GRAPH bridges `LAct → ℒₒᵣ` on `ℒₒᵣ`-codes (`substsGraphOROfLAct`, `shiftGraphOROfLAct`,
   `bvGraphOROfLAct`, `negGraphOROfLAct`, `impGraphOROfLAct`, `termSubstVecGraphOROfLAct`,
   `termShiftVecGraphOROfLAct`) — how a fragment converts a walk done with the `LAct` rows of
   `Formulas.lean` into the facts `lib_indRec` wants;
4. `indBodyIntro` — `indBodyValGraph y K` from its seven constituent graph facts, all named by
   universal variables (the fragment never proves the existential itself);
5. the polarity bridges `.sigma → .pi` for `isSemiformula`/`isUFormula`/`isSemitermVec`/
   `isUTermVec` at BOTH languages (formation rows conclude `.sigma`; `lib_indRec` and the
   `Formulas` rows take `.pi`);
6. `axIsFormula : Δ₁ch TAct p → (isSemiformula LAct).sigma 0 p` — every `TAct`-axiom code is a
   formula code (item (iii) of the Nodes task).

**The chain at an `axm` leaf whose axiom is an induction instance** is spelled out at the end.
-/

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1
open LAct

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ## §A — V-generic bridges -/

/-! ### Symbols: the relation symbols coincide; the `ℒₒᵣ` function symbols are the codes `< 2` -/

section symbols

lemma isRel_LAct_iff_LOR {k R : V} : LAct.IsRel k R ↔ (ℒₒᵣ).IsRel k R := by
  rw [isRel_LAct_iff_V, isRel_LOR_iff_V]

lemma isRel_LAct_of_LOR {k R : V} (h : (ℒₒᵣ).IsRel k R) : LAct.IsRel k R :=
  isRel_LAct_iff_LOR.mpr h

end symbols

/-! ### Terms: `ℒₒᵣ`-terms are `LAct`-terms; the term operations agree on them -/

section terms

lemma IsUTermVec.LAct_of_LOR {k v : V} (hv : IsUTermVec ℒₒᵣ k v) : IsUTermVec LAct k v :=
  ⟨hv.lh, fun _ hi ↦ IsUTerm.LAct_of_LOR (hv.nth hi)⟩

lemma IsSemitermVec.LAct_of_LOR {k n v : V} (hv : IsSemitermVec ℒₒᵣ k n v) :
    IsSemitermVec LAct k n v :=
  IsSemitermVec.iff.mpr ⟨hv.lh, fun _ hi ↦ IsSemiterm.LAct_of_LOR (hv.nth hi)⟩

/-- `termBV` does not see the language on an `ℒₒᵣ`-term. -/
lemma termBV_LAct_eq {t : V} (ht : IsUTerm ℒₒᵣ t) : termBV LAct t = termBV ℒₒᵣ t := by
  apply IsUTerm.induction 𝚷 ?_ ?_ ?_ ?_ t ht
  · definability
  · intro z; simp
  · intro x; simp
  · intro k f v hf hv ih
    rw [termBV_func (isFunc_LAct_of_LOR hf) (IsUTermVec.LAct_of_LOR hv), termBV_func hf hv]
    congr 1
    apply nth_ext' k (len_termBVVec (IsUTermVec.LAct_of_LOR hv)) (len_termBVVec hv)
    intro i hi
    rw [nth_termBVVec (IsUTermVec.LAct_of_LOR hv) hi, nth_termBVVec hv hi, ih i hi]

lemma termBVVec_LAct_eq {k v : V} (hv : IsUTermVec ℒₒᵣ k v) :
    termBVVec LAct k v = termBVVec ℒₒᵣ k v :=
  nth_ext' k (len_termBVVec (IsUTermVec.LAct_of_LOR hv)) (len_termBVVec hv) fun i hi ↦ by
    rw [nth_termBVVec (IsUTermVec.LAct_of_LOR hv) hi, nth_termBVVec hv hi, termBV_LAct_eq (hv.nth hi)]

lemma termShift_LAct_eq {t : V} (ht : IsUTerm ℒₒᵣ t) : termShift LAct t = termShift ℒₒᵣ t := by
  apply IsUTerm.induction 𝚷 ?_ ?_ ?_ ?_ t ht
  · definability
  · intro z; simp
  · intro x; simp
  · intro k f v hf hv ih
    rw [termShift_func (isFunc_LAct_of_LOR hf) (IsUTermVec.LAct_of_LOR hv), termShift_func hf hv]
    congr 1
    apply nth_ext' k (len_termShiftVec (IsUTermVec.LAct_of_LOR hv)) (len_termShiftVec hv)
    intro i hi
    rw [nth_termShiftVec (IsUTermVec.LAct_of_LOR hv) hi, nth_termShiftVec hv hi, ih i hi]

lemma termShiftVec_LAct_eq {k v : V} (hv : IsUTermVec ℒₒᵣ k v) :
    termShiftVec LAct k v = termShiftVec ℒₒᵣ k v :=
  nth_ext' k (len_termShiftVec (IsUTermVec.LAct_of_LOR hv)) (len_termShiftVec hv) fun i hi ↦ by
    rw [nth_termShiftVec (IsUTermVec.LAct_of_LOR hv) hi, nth_termShiftVec hv hi,
      termShift_LAct_eq (hv.nth hi)]

lemma termBShift_LAct_eq {t : V} (ht : IsUTerm ℒₒᵣ t) : termBShift LAct t = termBShift ℒₒᵣ t := by
  apply IsUTerm.induction 𝚷 ?_ ?_ ?_ ?_ t ht
  · definability
  · intro z; simp
  · intro x; simp
  · intro k f v hf hv ih
    rw [termBShift_func (isFunc_LAct_of_LOR hf) (IsUTermVec.LAct_of_LOR hv), termBShift_func hf hv]
    congr 1
    apply nth_ext' k (len_termBShiftVec (IsUTermVec.LAct_of_LOR hv)) (len_termBShiftVec hv)
    intro i hi
    rw [nth_termBShiftVec (IsUTermVec.LAct_of_LOR hv) hi, nth_termBShiftVec hv hi, ih i hi]

lemma termBShiftVec_LAct_eq {k v : V} (hv : IsUTermVec ℒₒᵣ k v) :
    termBShiftVec LAct k v = termBShiftVec ℒₒᵣ k v :=
  nth_ext' k (len_termBShiftVec (IsUTermVec.LAct_of_LOR hv)) (len_termBShiftVec hv) fun i hi ↦ by
    rw [nth_termBShiftVec (IsUTermVec.LAct_of_LOR hv) hi, nth_termBShiftVec hv hi,
      termBShift_LAct_eq (hv.nth hi)]

/-- `termSubst` agrees on an `ℒₒᵣ`-term for EVERY substitution vector `w` (the bound-variable
clause reads `w.[z]` in both languages). -/
lemma termSubst_LAct_eq {t : V} (ht : IsUTerm ℒₒᵣ t) (w : V) :
    termSubst LAct w t = termSubst ℒₒᵣ w t := by
  revert w
  apply IsUTerm.induction 𝚷 ?_ ?_ ?_ ?_ t ht
  · definability
  · intro z w; simp
  · intro x w; simp
  · intro k f v hf hv ih w
    rw [termSubst_func (isFunc_LAct_of_LOR hf) (IsUTermVec.LAct_of_LOR hv), termSubst_func hf hv]
    congr 1
    apply nth_ext' k (len_termSubstVec (IsUTermVec.LAct_of_LOR hv)) (len_termSubstVec hv)
    intro i hi
    rw [nth_termSubstVec (IsUTermVec.LAct_of_LOR hv) hi, nth_termSubstVec hv hi, ih i hi w]

lemma termSubstVec_LAct_eq {k v : V} (hv : IsUTermVec ℒₒᵣ k v) (w : V) :
    termSubstVec LAct k w v = termSubstVec ℒₒᵣ k w v :=
  nth_ext' k (len_termSubstVec (IsUTermVec.LAct_of_LOR hv)) (len_termSubstVec hv) fun i hi ↦ by
    rw [nth_termSubstVec (IsUTermVec.LAct_of_LOR hv) hi, nth_termSubstVec hv hi,
      termSubst_LAct_eq (hv.nth hi) w]

/-- `qVec` agrees on an `ℒₒᵣ`-term VECTOR (it bumps the entries with `termBShiftVec`). -/
lemma qVec_LAct_eq {k w : V} (hw : IsUTermVec ℒₒᵣ k w) : qVec LAct w = qVec ℒₒᵣ w := by
  have hk := hw.lh
  subst hk
  unfold qVec
  rw [termBShiftVec_LAct_eq hw]

/-- The `qVec` of an `ℒₒᵣ`-term vector is one. -/
lemma IsUTermVec.qVec_LOR {k w : V} (hw : IsUTermVec ℒₒᵣ k w) :
    IsUTermVec ℒₒᵣ (k + 1) (qVec ℒₒᵣ w) :=
  (hw.isSemitermVec.qVec).isUTermVec

end terms

/-! ### Formulas: `ℒₒᵣ`-formulas are `LAct`-formulas; the formula operations agree on them -/

section formulas

lemma IsUFormula.LAct_of_LOR {p : V} (hp : IsUFormula ℒₒᵣ p) : IsUFormula LAct p := by
  apply IsUFormula.ISigma1.sigma1_succ_induction ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ p hp
  · definability
  · intro k R v hR hv
    exact IsUFormula.mk (Or.inl ⟨k, R, v, isRel_LAct_of_LOR hR, IsUTermVec.LAct_of_LOR hv, rfl⟩)
  · intro k R v hR hv
    exact IsUFormula.mk (Or.inr (Or.inl ⟨k, R, v, isRel_LAct_of_LOR hR, IsUTermVec.LAct_of_LOR hv, rfl⟩))
  · exact IsUFormula.mk (Or.inr (Or.inr (Or.inl rfl)))
  · exact IsUFormula.mk (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · intro p q _ _ ihp ihq
    exact IsUFormula.mk (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, q, ihp, ihq, rfl⟩)))))
  · intro p q _ _ ihp ihq
    exact IsUFormula.mk (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, q, ihp, ihq, rfl⟩))))))
  · intro p _ ih
    exact IsUFormula.mk (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, ih, rfl⟩)))))))
  · intro p _ ih
    exact IsUFormula.mk (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨p, ih, rfl⟩)))))))

/-- `bv` does not see the language on an `ℒₒᵣ`-formula. -/
lemma bv_LAct_eq {p : V} (hp : IsUFormula ℒₒᵣ p) : bv LAct p = bv ℒₒᵣ p := by
  apply IsUFormula.ISigma1.pi1_succ_induction ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ p hp
  · definability
  · intro k R v hR hv
    rw [bv_rel (isRel_LAct_of_LOR hR) (IsUTermVec.LAct_of_LOR hv), bv_rel hR hv, termBVVec_LAct_eq hv]
  · intro k R v hR hv
    rw [bv_nrel (isRel_LAct_of_LOR hR) (IsUTermVec.LAct_of_LOR hv), bv_nrel hR hv, termBVVec_LAct_eq hv]
  · simp
  · simp
  · intro p q hp hq ihp ihq
    rw [bv_and (IsUFormula.LAct_of_LOR hp) (IsUFormula.LAct_of_LOR hq), bv_and hp hq, ihp, ihq]
  · intro p q hp hq ihp ihq
    rw [bv_or (IsUFormula.LAct_of_LOR hp) (IsUFormula.LAct_of_LOR hq), bv_or hp hq, ihp, ihq]
  · intro p hp ih
    rw [bv_all (IsUFormula.LAct_of_LOR hp), bv_all hp, ih]
  · intro p hp ih
    rw [bv_ex (IsUFormula.LAct_of_LOR hp), bv_ex hp, ih]

lemma IsSemiformula.LAct_of_LOR {n p : V} (hp : IsSemiformula ℒₒᵣ n p) : IsSemiformula LAct n p :=
  ⟨IsUFormula.LAct_of_LOR hp.isUFormula, by rw [bv_LAct_eq hp.isUFormula]; exact hp.bv_le⟩

lemma neg_LAct_eq {p : V} (hp : IsUFormula ℒₒᵣ p) : neg LAct p = neg ℒₒᵣ p := by
  apply IsUFormula.ISigma1.pi1_succ_induction ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ p hp
  · definability
  · intro k R v hR hv
    rw [neg_rel (isRel_LAct_of_LOR hR) (IsUTermVec.LAct_of_LOR hv), neg_rel hR hv]
  · intro k R v hR hv
    rw [neg_nrel (isRel_LAct_of_LOR hR) (IsUTermVec.LAct_of_LOR hv), neg_nrel hR hv]
  · simp
  · simp
  · intro p q hp hq ihp ihq
    rw [neg_and (IsUFormula.LAct_of_LOR hp) (IsUFormula.LAct_of_LOR hq), neg_and hp hq, ihp, ihq]
  · intro p q hp hq ihp ihq
    rw [neg_or (IsUFormula.LAct_of_LOR hp) (IsUFormula.LAct_of_LOR hq), neg_or hp hq, ihp, ihq]
  · intro p hp ih
    rw [neg_all (IsUFormula.LAct_of_LOR hp), neg_all hp, ih]
  · intro p hp ih
    rw [neg_ex (IsUFormula.LAct_of_LOR hp), neg_ex hp, ih]

lemma shift_LAct_eq {p : V} (hp : IsUFormula ℒₒᵣ p) : shift LAct p = shift ℒₒᵣ p := by
  apply IsUFormula.ISigma1.pi1_succ_induction ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ p hp
  · definability
  · intro k R v hR hv
    rw [shift_rel (isRel_LAct_of_LOR hR) (IsUTermVec.LAct_of_LOR hv), shift_rel hR hv,
      termShiftVec_LAct_eq hv]
  · intro k R v hR hv
    rw [shift_nrel (isRel_LAct_of_LOR hR) (IsUTermVec.LAct_of_LOR hv), shift_nrel hR hv,
      termShiftVec_LAct_eq hv]
  · simp
  · simp
  · intro p q hp hq ihp ihq
    rw [shift_and (IsUFormula.LAct_of_LOR hp) (IsUFormula.LAct_of_LOR hq), shift_and hp hq, ihp, ihq]
  · intro p q hp hq ihp ihq
    rw [shift_or (IsUFormula.LAct_of_LOR hp) (IsUFormula.LAct_of_LOR hq), shift_or hp hq, ihp, ihq]
  · intro p hp ih
    rw [shift_all (IsUFormula.LAct_of_LOR hp), shift_all hp, ih]
  · intro p hp ih
    rw [shift_exs (IsUFormula.LAct_of_LOR hp), shift_exs hp, ih]

/-- `subst` agrees on an `ℒₒᵣ`-formula for every `ℒₒᵣ`-term VECTOR `w` (the quantifier clauses
bump `w` with `qVec`, which is where the language enters). -/
lemma subst_LAct_eq {p : V} (hp : IsUFormula ℒₒᵣ p) {k w : V} (hw : IsUTermVec ℒₒᵣ k w) :
    subst LAct w p = subst ℒₒᵣ w p := by
  revert k w
  apply IsUFormula.ISigma1.pi1_succ_induction ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ p hp
  · definability
  · intro k R v hR hv l w _
    rw [substs_rel (isRel_LAct_of_LOR hR) (IsUTermVec.LAct_of_LOR hv), substs_rel hR hv,
      termSubstVec_LAct_eq hv]
  · intro k R v hR hv l w _
    rw [substs_nrel (isRel_LAct_of_LOR hR) (IsUTermVec.LAct_of_LOR hv), substs_nrel hR hv,
      termSubstVec_LAct_eq hv]
  · intro l w _; simp
  · intro l w _; simp
  · intro p q hp hq ihp ihq l w hw
    rw [substs_and (IsUFormula.LAct_of_LOR hp) (IsUFormula.LAct_of_LOR hq), substs_and hp hq,
      ihp hw, ihq hw]
  · intro p q hp hq ihp ihq l w hw
    rw [substs_or (IsUFormula.LAct_of_LOR hp) (IsUFormula.LAct_of_LOR hq), substs_or hp hq,
      ihp hw, ihq hw]
  · intro p hp ih l w hw
    rw [substs_all (IsUFormula.LAct_of_LOR hp), substs_all hp, qVec_LAct_eq hw,
      ih (IsUTermVec.qVec_LOR hw)]
  · intro p hp ih l w hw
    rw [substs_ex (IsUFormula.LAct_of_LOR hp), substs_ex hp, qVec_LAct_eq hw,
      ih (IsUTermVec.qVec_LOR hw)]

/-- `fvarVec m = [&0, …, &(m-1)]` is an `ℒₒᵣ`-term vector of length `m` (closed, so at bound `0`). -/
lemma fvarVec_isSemitermVec_LOR (m : V) : IsSemitermVec ℒₒᵣ m 0 (fvarVec m) :=
  IsSemitermVec.iff.mpr ⟨len_fvarVec m, fun i hi ↦ by rw [nth_fvarVec m i hi]; exact IsSemiterm.fvar _ _⟩

/-- The two substitution vectors of `indBodyValGraph` (`![⌜0⌝]`, `![⌜#0 + 1⌝]`) are `ℒₒᵣ`-term
vectors. -/
lemma indSubstConst0_isSemitermVec : IsSemitermVec ℒₒᵣ 1 0 (indSubstConst0 : V) := by
  rw [val_indSubstConst0]
  simp

end formulas

/-! ## §B — library rows -/

/-! ### B.1 Language lifts `ℒₒᵣ → LAct` and the symbol rows -/

/-- `IsSemiformula ℒₒᵣ n p → IsSemiformula LAct n p`. -/
noncomputable def isSemiformulaLActOfLORB : ArithmeticSemisentence 2 :=
  “p n. !(isSemiformula ℒₒᵣ).pi n p → !(isSemiformula LAct).sigma n p”
noncomputable def isSemiformulaLActOfLOR : ArithmeticSentence := ∀¹* isSemiformulaLActOfLORB
lemma models_isSemiformulaLActOfLOR :
    V↓[ℒₒᵣ] ⊧ isSemiformulaLActOfLOR ↔ ∀ p n : V, IsSemiformula ℒₒᵣ n p → IsSemiformula LAct n p := by
  simp [isSemiformulaLActOfLOR, isSemiformulaLActOfLORB, models_iff, Matrix.vecForall_iff]
theorem pa_proves_isSemiformulaLActOfLOR : 𝗣𝗔 ⊢ isSemiformulaLActOfLOR :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_isSemiformulaLActOfLOR.mpr fun _ _ h ↦ IsSemiformula.LAct_of_LOR h
theorem lib_isSemiformulaLActOfLOR : Lib isSemiformulaLActOfLOR := Lib.of_pa pa_proves_isSemiformulaLActOfLOR

/-! ### B.2 Formation at `ℒₒᵣ` — how a fragment establishes "`ℒₒᵣ`-only" bottom-up
(the `Formulas.lean` formation rows re-indexed at `ℒₒᵣ`), plus the auxiliary vectors of the
recognizer -/

noncomputable def isSemiformulaRelORB : ArithmeticSemisentence 5 :=
  “p v R k n. !(ℒₒᵣ).isRel k R → !(isSemitermVec ℒₒᵣ).pi k n v → !qqRelDef p k R v → !(isSemiformula ℒₒᵣ).sigma n p”
noncomputable def isSemiformulaRelOR : ArithmeticSentence := ∀¹* isSemiformulaRelORB
lemma models_isSemiformulaRelOR :
    V↓[ℒₒᵣ] ⊧ isSemiformulaRelOR ↔ ∀ p v R k n : V, (ℒₒᵣ).IsRel k R → IsSemitermVec ℒₒᵣ k n v → p = ^rel k R v → IsSemiformula ℒₒᵣ n p := by
  simp [isSemiformulaRelOR, isSemiformulaRelORB, models_iff, Matrix.vecForall_iff]
theorem pa_proves_isSemiformulaRelOR : 𝗣𝗔 ⊢ isSemiformulaRelOR :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_isSemiformulaRelOR.mpr fun _ _ _ _ _ hR hv h ↦ by subst h; exact IsSemiformula.rel.mpr ⟨hR, hv⟩
theorem lib_isSemiformulaRelOR : Lib isSemiformulaRelOR := Lib.of_pa pa_proves_isSemiformulaRelOR

/-- `fvarVec m` (the parameter vector of the induction recognizer) is an `ℒₒᵣ`-term vector. -/
noncomputable def fvarVecSemitermVecORB : ArithmeticSemisentence 2 :=
  “fv m. !fvarVecDef fv m → !(isSemitermVec ℒₒᵣ).sigma m 0 fv”
noncomputable def fvarVecSemitermVecOR : ArithmeticSentence := ∀¹* fvarVecSemitermVecORB
lemma models_fvarVecSemitermVecOR :
    V↓[ℒₒᵣ] ⊧ fvarVecSemitermVecOR ↔ ∀ fv m : V, fv = fvarVec m → IsSemitermVec ℒₒᵣ m 0 fv := by
  simp [fvarVecSemitermVecOR, fvarVecSemitermVecORB, models_iff, Matrix.vecForall_iff]
theorem pa_proves_fvarVecSemitermVecOR : 𝗣𝗔 ⊢ fvarVecSemitermVecOR :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_fvarVecSemitermVecOR.mpr fun _ _ h ↦ by subst h; exact fvarVec_isSemitermVec_LOR _
theorem lib_fvarVecSemitermVecOR : Lib fvarVecSemitermVecOR := Lib.of_pa pa_proves_fvarVecSemitermVecOR

/-- The substitution vector `![⌜0⌝]` inside `indBodyValGraph` is an `ℒₒᵣ`-term vector. -/
noncomputable def indSubstConst0VecORB : ArithmeticSemisentence 1 :=
  “v. v = ↑indSubstConst0 → !(isSemitermVec ℒₒᵣ).sigma 1 0 v”
noncomputable def indSubstConst0VecOR : ArithmeticSentence := ∀¹* indSubstConst0VecORB
lemma models_indSubstConst0VecOR :
    V↓[ℒₒᵣ] ⊧ indSubstConst0VecOR ↔ ∀ v : V, v = (indSubstConst0 : V) → IsSemitermVec ℒₒᵣ 1 0 v := by
  simp [indSubstConst0VecOR, indSubstConst0VecORB, models_iff, Matrix.vecForall_iff, numeral_eq_natCast]
theorem pa_proves_indSubstConst0VecOR : 𝗣𝗔 ⊢ indSubstConst0VecOR :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_indSubstConst0VecOR.mpr fun _ h ↦ by subst h; exact indSubstConst0_isSemitermVec
theorem lib_indSubstConst0VecOR : Lib indSubstConst0VecOR := Lib.of_pa pa_proves_indSubstConst0VecOR

/-! ### B.3 Graph bridges `LAct → ℒₒᵣ` on `ℒₒᵣ`-codes — how a fragment converts a walk done
with the `LAct` rows of `Formulas.lean` into the `ℒₒᵣ`-graph facts `lib_indRec` and
`indBodyValGraph` want -/

noncomputable def substsGraphOROfLActB : ArithmeticSemisentence 4 :=
  “y w p k. !(isUFormula ℒₒᵣ).pi p → !(isUTermVec ℒₒᵣ).pi k w → !(substsGraph LAct) y w p → !(substsGraph ℒₒᵣ) y w p”
noncomputable def substsGraphOROfLAct : ArithmeticSentence := ∀¹* substsGraphOROfLActB
lemma models_substsGraphOROfLAct :
    V↓[ℒₒᵣ] ⊧ substsGraphOROfLAct ↔ ∀ y w p k : V, IsUFormula ℒₒᵣ p → IsUTermVec ℒₒᵣ k w → y = subst LAct w p → y = subst ℒₒᵣ w p := by
  simp [substsGraphOROfLAct, substsGraphOROfLActB, models_iff, Matrix.vecForall_iff, subst.defined.iff]
theorem pa_proves_substsGraphOROfLAct : 𝗣𝗔 ⊢ substsGraphOROfLAct :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_substsGraphOROfLAct.mpr fun _ _ _ _ hp hw h ↦ h.trans (subst_LAct_eq hp hw)
theorem lib_substsGraphOROfLAct : Lib substsGraphOROfLAct := Lib.of_pa pa_proves_substsGraphOROfLAct

noncomputable def bvGraphOROfLActB : ArithmeticSemisentence 2 :=
  “m p. !(isUFormula ℒₒᵣ).pi p → !(bvGraph LAct) m p → !(bvGraph ℒₒᵣ) m p”
noncomputable def bvGraphOROfLAct : ArithmeticSentence := ∀¹* bvGraphOROfLActB
lemma models_bvGraphOROfLAct :
    V↓[ℒₒᵣ] ⊧ bvGraphOROfLAct ↔ ∀ m p : V, IsUFormula ℒₒᵣ p → m = bv LAct p → m = bv ℒₒᵣ p := by
  simp [bvGraphOROfLAct, bvGraphOROfLActB, models_iff, Matrix.vecForall_iff]
theorem pa_proves_bvGraphOROfLAct : 𝗣𝗔 ⊢ bvGraphOROfLAct :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_bvGraphOROfLAct.mpr fun _ _ hp h ↦ h.trans (bv_LAct_eq hp)
theorem lib_bvGraphOROfLAct : Lib bvGraphOROfLAct := Lib.of_pa pa_proves_bvGraphOROfLAct

/-! ### B.4 `indBodyValGraph` from its constituents, every auxiliary object a universal variable -/

/-- `indBodyValGraph y K` — `y = K(0) → (∀ (K → K(#0+1))) → ∀ K` with `→` as `neg ⋎` — from the
ten constituent graph facts (`substsGraph ℒₒᵣ` at the two constant vectors, `negGraph ℒₒᵣ`,
`qqOrDef`, `qqAllDef`); the fragment names each intermediate code and never proves the
existential inside `indBodyValGraph` itself. -/
noncomputable def indBodyIntroB : ArithmeticSemisentence 11 :=
  “y K a s1 nk i1 qa1 qak nq i2 na. !(substsGraph ℒₒᵣ) a ↑indSubstConst0 K → !(substsGraph ℒₒᵣ) s1 ↑indSubstConst1 K → !(negGraph ℒₒᵣ) nk K → !qqOrDef i1 nk s1 → !qqAllDef qa1 i1 → !qqAllDef qak K → !(negGraph ℒₒᵣ) nq qa1 → !qqOrDef i2 nq qak → !(negGraph ℒₒᵣ) na a → !qqOrDef y na i2 → !indBodyValGraph y K”
noncomputable def indBodyIntro : ArithmeticSentence := ∀¹* indBodyIntroB
lemma models_indBodyIntro :
    V↓[ℒₒᵣ] ⊧ indBodyIntro ↔ ∀ y K a s1 nk i1 qa1 qak nq i2 na : V, a = subst ℒₒᵣ (indSubstConst0 : V) K → s1 = subst ℒₒᵣ (indSubstConst1 : V) K → nk = neg ℒₒᵣ K → i1 = nk ^⋎ s1 → qa1 = ^∀ i1 → qak = ^∀ K → nq = neg ℒₒᵣ qa1 → i2 = nq ^⋎ qak → na = neg ℒₒᵣ a → y = na ^⋎ i2 → y = indBodyVal K := by
  simp [indBodyIntro, indBodyIntroB, models_iff, Matrix.vecForall_iff, subst.defined.iff, numeral_eq_natCast]
theorem pa_proves_indBodyIntro : 𝗣𝗔 ⊢ indBodyIntro :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_indBodyIntro.mpr fun _ _ _ _ _ _ _ _ _ _ _ ha hs1 hnk hi1 hqa1 hqak hnq hi2 hna hy ↦ by
      subst ha hs1 hnk hi1 hqa1 hqak hnq hi2 hna hy
      unfold indBodyVal imp
      rw [val_indSubstConst0, val_indSubstConst1]
theorem lib_indBodyIntro : Lib indBodyIntro := Lib.of_pa pa_proves_indBodyIntro

/-! ### B.5 Polarity bridges `.sigma → .pi` (formation rows conclude `.sigma`; every Δ₁
hypothesis is `.pi`) at both languages -/

noncomputable def isSemiformulaSigmaPiORB : ArithmeticSemisentence 2 :=
  “p n. !(isSemiformula ℒₒᵣ).sigma n p → !(isSemiformula ℒₒᵣ).pi n p”
noncomputable def isSemiformulaSigmaPiOR : ArithmeticSentence := ∀¹* isSemiformulaSigmaPiORB
lemma models_isSemiformulaSigmaPiOR :
    V↓[ℒₒᵣ] ⊧ isSemiformulaSigmaPiOR ↔ ∀ p n : V, IsSemiformula ℒₒᵣ n p → IsSemiformula ℒₒᵣ n p := by
  simp [isSemiformulaSigmaPiOR, isSemiformulaSigmaPiORB, models_iff]
theorem pa_proves_isSemiformulaSigmaPiOR : 𝗣𝗔 ⊢ isSemiformulaSigmaPiOR :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_isSemiformulaSigmaPiOR.mpr fun _ _ h ↦ h
theorem lib_isSemiformulaSigmaPiOR : Lib isSemiformulaSigmaPiOR := Lib.of_pa pa_proves_isSemiformulaSigmaPiOR

noncomputable def isSemitermSigmaPiLActB : ArithmeticSemisentence 2 :=
  “t n. !(isSemiterm LAct).sigma n t → !(isSemiterm LAct).pi n t”
noncomputable def isSemitermSigmaPiLAct : ArithmeticSentence := ∀¹* isSemitermSigmaPiLActB
lemma models_isSemitermSigmaPiLAct :
    V↓[ℒₒᵣ] ⊧ isSemitermSigmaPiLAct ↔ ∀ t n : V, IsSemiterm LAct n t → IsSemiterm LAct n t := by
  simp [isSemitermSigmaPiLAct, isSemitermSigmaPiLActB, models_iff]
theorem pa_proves_isSemitermSigmaPiLAct : 𝗣𝗔 ⊢ isSemitermSigmaPiLAct :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_isSemitermSigmaPiLAct.mpr fun _ _ h ↦ h
theorem lib_isSemitermSigmaPiLAct : Lib isSemitermSigmaPiLAct := Lib.of_pa pa_proves_isSemitermSigmaPiLAct

noncomputable def isSemitermVecSigmaPiLActB : ArithmeticSemisentence 3 :=
  “v n k. !(isSemitermVec LAct).sigma k n v → !(isSemitermVec LAct).pi k n v”
noncomputable def isSemitermVecSigmaPiLAct : ArithmeticSentence := ∀¹* isSemitermVecSigmaPiLActB
lemma models_isSemitermVecSigmaPiLAct :
    V↓[ℒₒᵣ] ⊧ isSemitermVecSigmaPiLAct ↔ ∀ v n k : V, IsSemitermVec LAct k n v → IsSemitermVec LAct k n v := by
  simp [isSemitermVecSigmaPiLAct, isSemitermVecSigmaPiLActB, models_iff]
theorem pa_proves_isSemitermVecSigmaPiLAct : 𝗣𝗔 ⊢ isSemitermVecSigmaPiLAct :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_isSemitermVecSigmaPiLAct.mpr fun _ _ _ h ↦ h
theorem lib_isSemitermVecSigmaPiLAct : Lib isSemitermVecSigmaPiLAct := Lib.of_pa pa_proves_isSemitermVecSigmaPiLAct

noncomputable def isUTermVecSigmaPiLActB : ArithmeticSemisentence 2 :=
  “v k. !(isUTermVec LAct).sigma k v → !(isUTermVec LAct).pi k v”
noncomputable def isUTermVecSigmaPiLAct : ArithmeticSentence := ∀¹* isUTermVecSigmaPiLActB
lemma models_isUTermVecSigmaPiLAct :
    V↓[ℒₒᵣ] ⊧ isUTermVecSigmaPiLAct ↔ ∀ v k : V, IsUTermVec LAct k v → IsUTermVec LAct k v := by
  simp [isUTermVecSigmaPiLAct, isUTermVecSigmaPiLActB, models_iff]
theorem pa_proves_isUTermVecSigmaPiLAct : 𝗣𝗔 ⊢ isUTermVecSigmaPiLAct :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_isUTermVecSigmaPiLAct.mpr fun _ _ h ↦ h
theorem lib_isUTermVecSigmaPiLAct : Lib isUTermVecSigmaPiLAct := Lib.of_pa pa_proves_isUTermVecSigmaPiLAct

/-! ### B.6 Every `TAct`-axiom code is a formula code (item (iii) of the Nodes task) -/

/-- The `ch` of a singleton theory accepts exactly the code of its sentence. -/
lemma singleton_ch_iff (σ : Sentence LAct) (p : V) :
    V ⊧/![p] (Theory.Δ₁.singleton σ).ch.val ↔ p = (⌜σ⌝ : V) := by
  simp [numeral_eq_natCast, Sentence.quote_eq_encode]

/-- A code in `TAct`'s Δ₁ axiom class is an `LAct`-formula code: the embedded-`𝗣𝗔` part carries
`isFormulaOR`, the four action singletons are quoted sentences. -/
lemma isFormula_of_mem_TAct_Δ₁Class {p : V} (h : p ∈ TAct.Δ₁Class) : IsSemiformula LAct 0 p := by
  rw [mem_TAct_class_iff, tact_ch_eq] at h
  simp only [HierarchySymbol.Semiformula.val_or, HierarchySymbol.Semiformula.val_and,
    LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_and,
    LogicalConnective.Prop.or_eq, LogicalConnective.Prop.and_eq, singleton_ch_iff] at h
  rcases h with (((⟨hF, _⟩ | rfl) | rfl) | rfl) | rfl
  · exact IsSemiformula.LAct_of_LOR ((eval_isFormulaOR' p).mp hF)
  all_goals simp

/-- `Δ₁ch TAct p → IsSemiformula LAct 0 p` (the `.sigma` form of the hypothesis converts by
`lib_axSigmaPi`). -/
noncomputable def axIsFormulaB : ArithmeticSemisentence 1 :=
  “p. !(Theory.Δ₁ch TAct).pi p → !(isSemiformula LAct).sigma 0 p”
noncomputable def axIsFormula : ArithmeticSentence := ∀¹* axIsFormulaB
lemma models_axIsFormula :
    V↓[ℒₒᵣ] ⊧ axIsFormula ↔ ∀ p : V, p ∈ TAct.Δ₁Class → IsSemiformula LAct 0 p := by
  simp [axIsFormula, axIsFormulaB, models_iff, Matrix.vecForall_iff]
theorem pa_proves_axIsFormula : 𝗣𝗔 ⊢ axIsFormula :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_axIsFormula.mpr fun _ h ↦ isFormula_of_mem_TAct_Δ₁Class h
theorem lib_axIsFormula : Lib axIsFormula := Lib.of_pa pa_proves_axIsFormula

/-! ## The chain at an `axm` leaf whose axiom is an induction instance

The fragment holds, for the eigenvariables `p b m fv s K` (and every sub-syntax node of `b`, `K`),
`LAct`-vocabulary facts from the walk (`Lib/Formulas.lean` rows): `!qqAllsDef p b m`,
`!(shiftGraph LAct) b b`, `!(bvGraph LAct) m b`, `!fvarVecDef fv m`, `!(substsGraph LAct) s fv b`,
and — computing `subst fv b` through the commutation rows down to the shape
`K(0) → (∀ (K → K(#0+1))) → ∀ K` — the `LAct` graph facts of its constituents
`!(substsGraph LAct) a ↑indSubstConst0 K`, `!(substsGraph LAct) s1 ↑indSubstConst1 K`,
`!(negGraph LAct) nk K`, `!qqOrDef i1 nk s1`, `!qqAllDef qa1 i1`, `!qqAllDef qak K`,
`!(negGraph LAct) nq qa1`, `!qqOrDef i2 nq qak`, `!(negGraph LAct) na a`, `!qqOrDef s na i2`.
It chains (each step one row, `O(1)`):

1. **`ℒₒᵣ`-ness, bottom-up** over the sub-syntax of `b` and `K`: `isSemitermBvarOR/FvarOR/FuncOR`,
   `isSemitermVecNilOR/AdjoinOR`, `isSemiformulaRelOR … ExsOR` — symbol hypotheses
   `!(ℒₒᵣ).isRel k R` / `!(ℒₒᵣ).isFunc k f` are Σ₀ on literal codes (or `isRelLOROfLAct` /
   `isFuncLOROfLAct` from the `LAct` facts) — giving `(isSemiformula ℒₒᵣ).sigma m b` and
   `(isSemiformula ℒₒᵣ).sigma 1 K`; `isSemiformulaSigmaPiOR` makes them `.pi`;
   `isUFormulaOfSemiformulaOR` + `isUFormulaSigmaPiOR` gives `(isUFormula ℒₒᵣ).pi b`;
   `isSemiformulaSubstOR/NegOR/ShiftOR` (after step 3's conversions) give `ℒₒᵣ`-ness of `a`, `s1`,
   `qa1`, `i1`, … where a `negGraph` bridge needs it.
2. **The parameter vector**: `fvarVecSemitermVecOR` (`fv = fvarVec m` is an `ℒₒᵣ`-term vector) →
   `isUTermVecOfSemitermVecOR` → `isUTermVecSigmaPiOR` : `(isUTermVec ℒₒᵣ).pi m fv`; likewise
   `indSubstConst0VecOR` / `indSubstConst1VecOR` for the two constant vectors.
3. **Graph conversion `LAct → ℒₒᵣ`**: `shiftGraphOROfLAct` (`b b`), `bvGraphOROfLAct` (`m b`),
   `substsGraphOROfLAct` (`s fv b`, and `a ↑indSubstConst0 K`, `s1 ↑indSubstConst1 K`),
   `negGraphOROfLAct` (`nk K`, `nq qa1`, `na a`). `qqAllsDef`, `fvarVecDef`, `qqOrDef`, `qqAllDef`
   are not `L`-indexed — nothing to convert.
4. **`indBodyIntro`** with `y := s` packages the ten `ℒₒᵣ` constituent facts into
   `!indBodyValGraph s K`.
5. **`lib_indRec`** (`Lib/Nodes.lean`) yields `!(Theory.Δ₁ch TAct).sigma p`, the hypothesis
   `lib_introAxm` takes.

`lib_axIsFormula` is the small converse service: from `!(Theory.Δ₁ch TAct).pi p` (via
`lib_axSigmaPi` from the `.sigma` form) the fragment gets `!(isSemiformula LAct).sigma 0 p`, the
`IsFormulaSet` obligation of the `axm` node's sequent. -/

end ArithS
