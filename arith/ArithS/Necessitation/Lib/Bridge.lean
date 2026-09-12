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

lemma isRel_LOR_of_LAct {k R : V} (h : LAct.IsRel k R) : (ℒₒᵣ).IsRel k R :=
  isRel_LAct_iff_LOR.mp h

lemma isFunc_LOR_iff_LAct {k f : V} : (ℒₒᵣ).IsFunc k f ↔ LAct.IsFunc k f ∧ f < 2 := by
  constructor
  · intro h
    refine ⟨isFunc_LAct_of_LOR h, ?_⟩
    rcases isFunc_LOR_iff_V.mp h with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> norm_num
  · rintro ⟨h, hf⟩
    rw [isFunc_LOR_iff_V]
    rcases isFunc_LAct_iff_V.mp h with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · exact absurd hf (by norm_num)
    · exact absurd hf (by norm_num)
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))

lemma isFunc_LOR_of_LAct {k f : V} (h : LAct.IsFunc k f) (hf : f < 2) : (ℒₒᵣ).IsFunc k f :=
  isFunc_LOR_iff_LAct.mpr ⟨h, hf⟩

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

lemma imp_LAct_eq {p q : V} (hp : IsUFormula ℒₒᵣ p) : imp LAct p q = imp ℒₒᵣ p q := by
  unfold imp; rw [neg_LAct_eq hp]

lemma substs1_LAct_eq {p t : V} (hp : IsUFormula ℒₒᵣ p) (ht : IsUTerm ℒₒᵣ t) :
    substs1 LAct t p = substs1 ℒₒᵣ t p := by
  unfold substs1
  exact subst_LAct_eq hp (k := 1) ⟨by simp, fun i hi ↦ by
    have : i = 0 := lt_one_iff_eq_zero.mp hi
    subst this; simpa using ht⟩

lemma free_LAct_eq {p : V} (hp : IsUFormula ℒₒᵣ p) : free LAct p = free ℒₒᵣ p := by
  unfold free
  rw [shift_LAct_eq hp, substs1_LAct_eq hp.shift (by simp)]

/-- `fvarVec m = [&0, …, &(m-1)]` is an `ℒₒᵣ`-term vector of length `m` (closed, so at bound `0`). -/
lemma fvarVec_isSemitermVec_LOR (m : V) : IsSemitermVec ℒₒᵣ m 0 (fvarVec m) :=
  IsSemitermVec.iff.mpr ⟨len_fvarVec m, fun i hi ↦ by rw [nth_fvarVec m i hi]; exact IsSemiterm.fvar _ _⟩

/-- The two substitution vectors of `indBodyValGraph` (`![⌜0⌝]`, `![⌜#0 + 1⌝]`) are `ℒₒᵣ`-term
vectors. -/
lemma indSubstConst0_isSemitermVec : IsSemitermVec ℒₒᵣ 1 0 (indSubstConst0 : V) := by
  rw [val_indSubstConst0]
  simp

lemma indSubstConst1_isSemitermVec : IsSemitermVec ℒₒᵣ 1 1 (indSubstConst1 : V) := by
  rw [val_indSubstConst1]
  simpa using SemitermVec.isSemitermVec (![⌜(‘#0 + 1’ : ArithmeticSemiterm ℕ 1)⌝] : SemitermVec V ℒₒᵣ 1 1)

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

/-- `IsUFormula ℒₒᵣ p → IsUFormula LAct p`. -/
noncomputable def isUFormulaLActOfLORB : ArithmeticSemisentence 1 :=
  “p. !(isUFormula ℒₒᵣ).pi p → !(isUFormula LAct).sigma p”
noncomputable def isUFormulaLActOfLOR : ArithmeticSentence := ∀¹* isUFormulaLActOfLORB
lemma models_isUFormulaLActOfLOR :
    V↓[ℒₒᵣ] ⊧ isUFormulaLActOfLOR ↔ ∀ p : V, IsUFormula ℒₒᵣ p → IsUFormula LAct p := by
  simp [isUFormulaLActOfLOR, isUFormulaLActOfLORB, models_iff, Matrix.vecForall_iff]
theorem pa_proves_isUFormulaLActOfLOR : 𝗣𝗔 ⊢ isUFormulaLActOfLOR :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_isUFormulaLActOfLOR.mpr fun _ h ↦ IsUFormula.LAct_of_LOR h
theorem lib_isUFormulaLActOfLOR : Lib isUFormulaLActOfLOR := Lib.of_pa pa_proves_isUFormulaLActOfLOR

/-- `IsSemiterm ℒₒᵣ n t → IsSemiterm LAct n t`. -/
noncomputable def isSemitermLActOfLORB : ArithmeticSemisentence 2 :=
  “t n. !(isSemiterm ℒₒᵣ).pi n t → !(isSemiterm LAct).sigma n t”
noncomputable def isSemitermLActOfLOR : ArithmeticSentence := ∀¹* isSemitermLActOfLORB
lemma models_isSemitermLActOfLOR :
    V↓[ℒₒᵣ] ⊧ isSemitermLActOfLOR ↔ ∀ t n : V, IsSemiterm ℒₒᵣ n t → IsSemiterm LAct n t := by
  simp [isSemitermLActOfLOR, isSemitermLActOfLORB, models_iff, Matrix.vecForall_iff]
theorem pa_proves_isSemitermLActOfLOR : 𝗣𝗔 ⊢ isSemitermLActOfLOR :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_isSemitermLActOfLOR.mpr fun _ _ h ↦ IsSemiterm.LAct_of_LOR h
theorem lib_isSemitermLActOfLOR : Lib isSemitermLActOfLOR := Lib.of_pa pa_proves_isSemitermLActOfLOR

/-- `IsSemitermVec ℒₒᵣ k n v → IsSemitermVec LAct k n v`. -/
noncomputable def isSemitermVecLActOfLORB : ArithmeticSemisentence 3 :=
  “v n k. !(isSemitermVec ℒₒᵣ).pi k n v → !(isSemitermVec LAct).sigma k n v”
noncomputable def isSemitermVecLActOfLOR : ArithmeticSentence := ∀¹* isSemitermVecLActOfLORB
lemma models_isSemitermVecLActOfLOR :
    V↓[ℒₒᵣ] ⊧ isSemitermVecLActOfLOR ↔ ∀ v n k : V, IsSemitermVec ℒₒᵣ k n v → IsSemitermVec LAct k n v := by
  simp [isSemitermVecLActOfLOR, isSemitermVecLActOfLORB, models_iff, Matrix.vecForall_iff]
theorem pa_proves_isSemitermVecLActOfLOR : 𝗣𝗔 ⊢ isSemitermVecLActOfLOR :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_isSemitermVecLActOfLOR.mpr fun _ _ _ h ↦ IsSemitermVec.LAct_of_LOR h
theorem lib_isSemitermVecLActOfLOR : Lib isSemitermVecLActOfLOR := Lib.of_pa pa_proves_isSemitermVecLActOfLOR

/-- `IsUTermVec ℒₒᵣ k v → IsUTermVec LAct k v`. -/
noncomputable def isUTermVecLActOfLORB : ArithmeticSemisentence 2 :=
  “v k. !(isUTermVec ℒₒᵣ).pi k v → !(isUTermVec LAct).sigma k v”
noncomputable def isUTermVecLActOfLOR : ArithmeticSentence := ∀¹* isUTermVecLActOfLORB
lemma models_isUTermVecLActOfLOR :
    V↓[ℒₒᵣ] ⊧ isUTermVecLActOfLOR ↔ ∀ v k : V, IsUTermVec ℒₒᵣ k v → IsUTermVec LAct k v := by
  simp [isUTermVecLActOfLOR, isUTermVecLActOfLORB, models_iff, Matrix.vecForall_iff]
theorem pa_proves_isUTermVecLActOfLOR : 𝗣𝗔 ⊢ isUTermVecLActOfLOR :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_isUTermVecLActOfLOR.mpr fun _ _ h ↦ IsUTermVec.LAct_of_LOR h
theorem lib_isUTermVecLActOfLOR : Lib isUTermVecLActOfLOR := Lib.of_pa pa_proves_isUTermVecLActOfLOR

/-- The relation symbols coincide: `LAct.IsRel k R → (ℒₒᵣ).IsRel k R`. -/
noncomputable def isRelLOROfLActB : ArithmeticSemisentence 2 :=
  “R k. !LAct.isRel k R → !(ℒₒᵣ).isRel k R”
noncomputable def isRelLOROfLAct : ArithmeticSentence := ∀¹* isRelLOROfLActB
lemma models_isRelLOROfLAct :
    V↓[ℒₒᵣ] ⊧ isRelLOROfLAct ↔ ∀ R k : V, LAct.IsRel k R → (ℒₒᵣ).IsRel k R := by
  simp [isRelLOROfLAct, isRelLOROfLActB, models_iff, Matrix.vecForall_iff]
theorem pa_proves_isRelLOROfLAct : 𝗣𝗔 ⊢ isRelLOROfLAct :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_isRelLOROfLAct.mpr fun _ _ h ↦ isRel_LOR_of_LAct h
theorem lib_isRelLOROfLAct : Lib isRelLOROfLAct := Lib.of_pa pa_proves_isRelLOROfLAct

/-- `(ℒₒᵣ).IsRel k R → LAct.IsRel k R`. -/
noncomputable def isRelLActOfLORB : ArithmeticSemisentence 2 :=
  “R k. !(ℒₒᵣ).isRel k R → !LAct.isRel k R”
noncomputable def isRelLActOfLOR : ArithmeticSentence := ∀¹* isRelLActOfLORB
lemma models_isRelLActOfLOR :
    V↓[ℒₒᵣ] ⊧ isRelLActOfLOR ↔ ∀ R k : V, (ℒₒᵣ).IsRel k R → LAct.IsRel k R := by
  simp [isRelLActOfLOR, isRelLActOfLORB, models_iff, Matrix.vecForall_iff]
theorem pa_proves_isRelLActOfLOR : 𝗣𝗔 ⊢ isRelLActOfLOR :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_isRelLActOfLOR.mpr fun _ _ h ↦ isRel_LAct_of_LOR h
theorem lib_isRelLActOfLOR : Lib isRelLActOfLOR := Lib.of_pa pa_proves_isRelLActOfLOR

/-- `(ℒₒᵣ).IsFunc k f → LAct.IsFunc k f`. -/
noncomputable def isFuncLActOfLORB : ArithmeticSemisentence 2 :=
  “f k. !(ℒₒᵣ).isFunc k f → !LAct.isFunc k f”
noncomputable def isFuncLActOfLOR : ArithmeticSentence := ∀¹* isFuncLActOfLORB
lemma models_isFuncLActOfLOR :
    V↓[ℒₒᵣ] ⊧ isFuncLActOfLOR ↔ ∀ f k : V, (ℒₒᵣ).IsFunc k f → LAct.IsFunc k f := by
  simp [isFuncLActOfLOR, isFuncLActOfLORB, models_iff, Matrix.vecForall_iff]
theorem pa_proves_isFuncLActOfLOR : 𝗣𝗔 ⊢ isFuncLActOfLOR :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_isFuncLActOfLOR.mpr fun _ _ h ↦ isFunc_LAct_of_LOR h
theorem lib_isFuncLActOfLOR : Lib isFuncLActOfLOR := Lib.of_pa pa_proves_isFuncLActOfLOR

/-- An `LAct` function symbol with code `< 2` is an `ℒₒᵣ` symbol (the action constants are `2`, `3`). -/
noncomputable def isFuncLOROfLActB : ArithmeticSemisentence 2 :=
  “f k. !LAct.isFunc k f → f < 2 → !(ℒₒᵣ).isFunc k f”
noncomputable def isFuncLOROfLAct : ArithmeticSentence := ∀¹* isFuncLOROfLActB
lemma models_isFuncLOROfLAct :
    V↓[ℒₒᵣ] ⊧ isFuncLOROfLAct ↔ ∀ f k : V, LAct.IsFunc k f → f < 2 → (ℒₒᵣ).IsFunc k f := by
  simp [isFuncLOROfLAct, isFuncLOROfLActB, models_iff, Matrix.vecForall_iff]
theorem pa_proves_isFuncLOROfLAct : 𝗣𝗔 ⊢ isFuncLOROfLAct :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_isFuncLOROfLAct.mpr fun _ _ h hf ↦ isFunc_LOR_of_LAct h hf
theorem lib_isFuncLOROfLAct : Lib isFuncLOROfLAct := Lib.of_pa pa_proves_isFuncLOROfLAct

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

noncomputable def isSemiformulaNRelORB : ArithmeticSemisentence 5 :=
  “p v R k n. !(ℒₒᵣ).isRel k R → !(isSemitermVec ℒₒᵣ).pi k n v → !qqNRelDef p k R v → !(isSemiformula ℒₒᵣ).sigma n p”
noncomputable def isSemiformulaNRelOR : ArithmeticSentence := ∀¹* isSemiformulaNRelORB
lemma models_isSemiformulaNRelOR :
    V↓[ℒₒᵣ] ⊧ isSemiformulaNRelOR ↔ ∀ p v R k n : V, (ℒₒᵣ).IsRel k R → IsSemitermVec ℒₒᵣ k n v → p = ^nrel k R v → IsSemiformula ℒₒᵣ n p := by
  simp [isSemiformulaNRelOR, isSemiformulaNRelORB, models_iff, Matrix.vecForall_iff]
theorem pa_proves_isSemiformulaNRelOR : 𝗣𝗔 ⊢ isSemiformulaNRelOR :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_isSemiformulaNRelOR.mpr fun _ _ _ _ _ hR hv h ↦ by subst h; exact IsSemiformula.nrel.mpr ⟨hR, hv⟩
theorem lib_isSemiformulaNRelOR : Lib isSemiformulaNRelOR := Lib.of_pa pa_proves_isSemiformulaNRelOR

noncomputable def isSemiformulaVerumORB : ArithmeticSemisentence 2 :=
  “p n. !qqVerumDef p → !(isSemiformula ℒₒᵣ).sigma n p”
noncomputable def isSemiformulaVerumOR : ArithmeticSentence := ∀¹* isSemiformulaVerumORB
lemma models_isSemiformulaVerumOR :
    V↓[ℒₒᵣ] ⊧ isSemiformulaVerumOR ↔ ∀ p n : V, p = ^⊤ → IsSemiformula ℒₒᵣ n p := by
  simp [isSemiformulaVerumOR, isSemiformulaVerumORB, models_iff, Matrix.vecForall_iff]
theorem pa_proves_isSemiformulaVerumOR : 𝗣𝗔 ⊢ isSemiformulaVerumOR :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_isSemiformulaVerumOR.mpr fun _ _ h ↦ by subst h; simp
theorem lib_isSemiformulaVerumOR : Lib isSemiformulaVerumOR := Lib.of_pa pa_proves_isSemiformulaVerumOR

noncomputable def isSemiformulaFalsumORB : ArithmeticSemisentence 2 :=
  “p n. !qqFalsumDef p → !(isSemiformula ℒₒᵣ).sigma n p”
noncomputable def isSemiformulaFalsumOR : ArithmeticSentence := ∀¹* isSemiformulaFalsumORB
lemma models_isSemiformulaFalsumOR :
    V↓[ℒₒᵣ] ⊧ isSemiformulaFalsumOR ↔ ∀ p n : V, p = ^⊥ → IsSemiformula ℒₒᵣ n p := by
  simp [isSemiformulaFalsumOR, isSemiformulaFalsumORB, models_iff, Matrix.vecForall_iff]
theorem pa_proves_isSemiformulaFalsumOR : 𝗣𝗔 ⊢ isSemiformulaFalsumOR :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_isSemiformulaFalsumOR.mpr fun _ _ h ↦ by subst h; simp
theorem lib_isSemiformulaFalsumOR : Lib isSemiformulaFalsumOR := Lib.of_pa pa_proves_isSemiformulaFalsumOR

noncomputable def isSemiformulaAndORB : ArithmeticSemisentence 4 :=
  “r q p n. !(isSemiformula ℒₒᵣ).pi n p → !(isSemiformula ℒₒᵣ).pi n q → !qqAndDef r p q → !(isSemiformula ℒₒᵣ).sigma n r”
noncomputable def isSemiformulaAndOR : ArithmeticSentence := ∀¹* isSemiformulaAndORB
lemma models_isSemiformulaAndOR :
    V↓[ℒₒᵣ] ⊧ isSemiformulaAndOR ↔ ∀ r q p n : V, IsSemiformula ℒₒᵣ n p → IsSemiformula ℒₒᵣ n q → r = p ^⋏ q → IsSemiformula ℒₒᵣ n r := by
  simp [isSemiformulaAndOR, isSemiformulaAndORB, models_iff, Matrix.vecForall_iff]
theorem pa_proves_isSemiformulaAndOR : 𝗣𝗔 ⊢ isSemiformulaAndOR :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_isSemiformulaAndOR.mpr fun _ _ _ _ hp hq h ↦ by subst h; exact IsSemiformula.and.mpr ⟨hp, hq⟩
theorem lib_isSemiformulaAndOR : Lib isSemiformulaAndOR := Lib.of_pa pa_proves_isSemiformulaAndOR

noncomputable def isSemiformulaOrORB : ArithmeticSemisentence 4 :=
  “r q p n. !(isSemiformula ℒₒᵣ).pi n p → !(isSemiformula ℒₒᵣ).pi n q → !qqOrDef r p q → !(isSemiformula ℒₒᵣ).sigma n r”
noncomputable def isSemiformulaOrOR : ArithmeticSentence := ∀¹* isSemiformulaOrORB
lemma models_isSemiformulaOrOR :
    V↓[ℒₒᵣ] ⊧ isSemiformulaOrOR ↔ ∀ r q p n : V, IsSemiformula ℒₒᵣ n p → IsSemiformula ℒₒᵣ n q → r = p ^⋎ q → IsSemiformula ℒₒᵣ n r := by
  simp [isSemiformulaOrOR, isSemiformulaOrORB, models_iff, Matrix.vecForall_iff]
theorem pa_proves_isSemiformulaOrOR : 𝗣𝗔 ⊢ isSemiformulaOrOR :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_isSemiformulaOrOR.mpr fun _ _ _ _ hp hq h ↦ by subst h; exact IsSemiformula.or.mpr ⟨hp, hq⟩
theorem lib_isSemiformulaOrOR : Lib isSemiformulaOrOR := Lib.of_pa pa_proves_isSemiformulaOrOR

noncomputable def isSemiformulaAllORB : ArithmeticSemisentence 3 :=
  “q p n. !(isSemiformula ℒₒᵣ).pi (n + 1) p → !qqAllDef q p → !(isSemiformula ℒₒᵣ).sigma n q”
noncomputable def isSemiformulaAllOR : ArithmeticSentence := ∀¹* isSemiformulaAllORB
lemma models_isSemiformulaAllOR :
    V↓[ℒₒᵣ] ⊧ isSemiformulaAllOR ↔ ∀ q p n : V, IsSemiformula ℒₒᵣ (n + 1) p → q = ^∀ p → IsSemiformula ℒₒᵣ n q := by
  simp [isSemiformulaAllOR, isSemiformulaAllORB, models_iff, Matrix.vecForall_iff]
theorem pa_proves_isSemiformulaAllOR : 𝗣𝗔 ⊢ isSemiformulaAllOR :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_isSemiformulaAllOR.mpr fun _ _ _ hp h ↦ by subst h; exact IsSemiformula.all.mpr hp
theorem lib_isSemiformulaAllOR : Lib isSemiformulaAllOR := Lib.of_pa pa_proves_isSemiformulaAllOR

noncomputable def isSemiformulaExsORB : ArithmeticSemisentence 3 :=
  “q p n. !(isSemiformula ℒₒᵣ).pi (n + 1) p → !qqExsDef q p → !(isSemiformula ℒₒᵣ).sigma n q”
noncomputable def isSemiformulaExsOR : ArithmeticSentence := ∀¹* isSemiformulaExsORB
lemma models_isSemiformulaExsOR :
    V↓[ℒₒᵣ] ⊧ isSemiformulaExsOR ↔ ∀ q p n : V, IsSemiformula ℒₒᵣ (n + 1) p → q = ^∃ p → IsSemiformula ℒₒᵣ n q := by
  simp [isSemiformulaExsOR, isSemiformulaExsORB, models_iff, Matrix.vecForall_iff]
theorem pa_proves_isSemiformulaExsOR : 𝗣𝗔 ⊢ isSemiformulaExsOR :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_isSemiformulaExsOR.mpr fun _ _ _ hp h ↦ by subst h; exact IsSemiformula.exs.mpr hp
theorem lib_isSemiformulaExsOR : Lib isSemiformulaExsOR := Lib.of_pa pa_proves_isSemiformulaExsOR

noncomputable def isSemitermFuncORB : ArithmeticSemisentence 5 :=
  “t v f k n. !(ℒₒᵣ).isFunc k f → !(isSemitermVec ℒₒᵣ).pi k n v → !qqFuncDef t k f v → !(isSemiterm ℒₒᵣ).sigma n t”
noncomputable def isSemitermFuncOR : ArithmeticSentence := ∀¹* isSemitermFuncORB
lemma models_isSemitermFuncOR :
    V↓[ℒₒᵣ] ⊧ isSemitermFuncOR ↔ ∀ t v f k n : V, (ℒₒᵣ).IsFunc k f → IsSemitermVec ℒₒᵣ k n v → t = ^func k f v → IsSemiterm ℒₒᵣ n t := by
  simp [isSemitermFuncOR, isSemitermFuncORB, models_iff, Matrix.vecForall_iff]
theorem pa_proves_isSemitermFuncOR : 𝗣𝗔 ⊢ isSemitermFuncOR :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_isSemitermFuncOR.mpr fun _ _ _ _ _ hf hv h ↦ by subst h; exact IsSemiterm.func.mpr ⟨hf, hv⟩
theorem lib_isSemitermFuncOR : Lib isSemitermFuncOR := Lib.of_pa pa_proves_isSemitermFuncOR

noncomputable def isSemitermBvarORB : ArithmeticSemisentence 3 :=
  “t z n. z < n → !qqBvarDef t z → !(isSemiterm ℒₒᵣ).sigma n t”
noncomputable def isSemitermBvarOR : ArithmeticSentence := ∀¹* isSemitermBvarORB
lemma models_isSemitermBvarOR :
    V↓[ℒₒᵣ] ⊧ isSemitermBvarOR ↔ ∀ t z n : V, z < n → t = ^#z → IsSemiterm ℒₒᵣ n t := by
  simp [isSemitermBvarOR, isSemitermBvarORB, models_iff, Matrix.vecForall_iff]
theorem pa_proves_isSemitermBvarOR : 𝗣𝗔 ⊢ isSemitermBvarOR :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_isSemitermBvarOR.mpr fun _ _ _ hz h ↦ by subst h; exact IsSemiterm.bvar.mpr hz
theorem lib_isSemitermBvarOR : Lib isSemitermBvarOR := Lib.of_pa pa_proves_isSemitermBvarOR

noncomputable def isSemitermFvarORB : ArithmeticSemisentence 3 :=
  “t x n. !qqFvarDef t x → !(isSemiterm ℒₒᵣ).sigma n t”
noncomputable def isSemitermFvarOR : ArithmeticSentence := ∀¹* isSemitermFvarORB
lemma models_isSemitermFvarOR :
    V↓[ℒₒᵣ] ⊧ isSemitermFvarOR ↔ ∀ t x n : V, t = ^&x → IsSemiterm ℒₒᵣ n t := by
  simp [isSemitermFvarOR, isSemitermFvarORB, models_iff, Matrix.vecForall_iff]
theorem pa_proves_isSemitermFvarOR : 𝗣𝗔 ⊢ isSemitermFvarOR :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_isSemitermFvarOR.mpr fun _ x n h ↦ by subst h; exact IsSemiterm.fvar n x
theorem lib_isSemitermFvarOR : Lib isSemitermFvarOR := Lib.of_pa pa_proves_isSemitermFvarOR

noncomputable def isSemitermVecNilORB : ArithmeticSemisentence 1 :=
  “n. !(isSemitermVec ℒₒᵣ).sigma 0 n 0”
noncomputable def isSemitermVecNilOR : ArithmeticSentence := ∀¹* isSemitermVecNilORB
lemma models_isSemitermVecNilOR :
    V↓[ℒₒᵣ] ⊧ isSemitermVecNilOR ↔ ∀ n : V, IsSemitermVec ℒₒᵣ 0 n (0 : V) := by
  simp [isSemitermVecNilOR, isSemitermVecNilORB, models_iff]
theorem pa_proves_isSemitermVecNilOR : 𝗣𝗔 ⊢ isSemitermVecNilOR :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_isSemitermVecNilOR.mpr fun n ↦ IsSemitermVec.nil n
theorem lib_isSemitermVecNilOR : Lib isSemitermVecNilOR := Lib.of_pa pa_proves_isSemitermVecNilOR

noncomputable def isSemitermVecAdjoinORB : ArithmeticSemisentence 5 :=
  “u t w n k. !(isSemitermVec ℒₒᵣ).pi k n w → !(isSemiterm ℒₒᵣ).pi n t → !adjoinDef u t w → !(isSemitermVec ℒₒᵣ).sigma (k + 1) n u”
noncomputable def isSemitermVecAdjoinOR : ArithmeticSentence := ∀¹* isSemitermVecAdjoinORB
lemma models_isSemitermVecAdjoinOR :
    V↓[ℒₒᵣ] ⊧ isSemitermVecAdjoinOR ↔ ∀ u t w n k : V, IsSemitermVec ℒₒᵣ k n w → IsSemiterm ℒₒᵣ n t → u = t ∷ w → IsSemitermVec ℒₒᵣ (k + 1) n u := by
  simp [isSemitermVecAdjoinOR, isSemitermVecAdjoinORB, models_iff, Matrix.vecForall_iff]
theorem pa_proves_isSemitermVecAdjoinOR : 𝗣𝗔 ⊢ isSemitermVecAdjoinOR :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_isSemitermVecAdjoinOR.mpr fun _ _ _ _ _ hw ht h ↦ by subst h; exact IsSemitermVec.adjoin hw ht
theorem lib_isSemitermVecAdjoinOR : Lib isSemitermVecAdjoinOR := Lib.of_pa pa_proves_isSemitermVecAdjoinOR

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

/-- The substitution vector `![⌜#0 + 1⌝]` inside `indBodyValGraph` is an `ℒₒᵣ`-term vector. -/
noncomputable def indSubstConst1VecORB : ArithmeticSemisentence 1 :=
  “v. v = ↑indSubstConst1 → !(isSemitermVec ℒₒᵣ).sigma 1 1 v”
noncomputable def indSubstConst1VecOR : ArithmeticSentence := ∀¹* indSubstConst1VecORB
lemma models_indSubstConst1VecOR :
    V↓[ℒₒᵣ] ⊧ indSubstConst1VecOR ↔ ∀ v : V, v = (indSubstConst1 : V) → IsSemitermVec ℒₒᵣ 1 1 v := by
  simp [indSubstConst1VecOR, indSubstConst1VecORB, models_iff, Matrix.vecForall_iff, numeral_eq_natCast]
theorem pa_proves_indSubstConst1VecOR : 𝗣𝗔 ⊢ indSubstConst1VecOR :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_indSubstConst1VecOR.mpr fun _ h ↦ by subst h; exact indSubstConst1_isSemitermVec
theorem lib_indSubstConst1VecOR : Lib indSubstConst1VecOR := Lib.of_pa pa_proves_indSubstConst1VecOR

noncomputable def isUFormulaOfSemiformulaORB : ArithmeticSemisentence 2 :=
  “p n. !(isSemiformula ℒₒᵣ).pi n p → !(isUFormula ℒₒᵣ).sigma p”
noncomputable def isUFormulaOfSemiformulaOR : ArithmeticSentence := ∀¹* isUFormulaOfSemiformulaORB
lemma models_isUFormulaOfSemiformulaOR :
    V↓[ℒₒᵣ] ⊧ isUFormulaOfSemiformulaOR ↔ ∀ p n : V, IsSemiformula ℒₒᵣ n p → IsUFormula ℒₒᵣ p := by
  simp [isUFormulaOfSemiformulaOR, isUFormulaOfSemiformulaORB, models_iff, Matrix.vecForall_iff]
theorem pa_proves_isUFormulaOfSemiformulaOR : 𝗣𝗔 ⊢ isUFormulaOfSemiformulaOR :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_isUFormulaOfSemiformulaOR.mpr fun _ _ h ↦ h.isUFormula
theorem lib_isUFormulaOfSemiformulaOR : Lib isUFormulaOfSemiformulaOR := Lib.of_pa pa_proves_isUFormulaOfSemiformulaOR

noncomputable def isUTermVecOfSemitermVecORB : ArithmeticSemisentence 3 :=
  “v n k. !(isSemitermVec ℒₒᵣ).pi k n v → !(isUTermVec ℒₒᵣ).sigma k v”
noncomputable def isUTermVecOfSemitermVecOR : ArithmeticSentence := ∀¹* isUTermVecOfSemitermVecORB
lemma models_isUTermVecOfSemitermVecOR :
    V↓[ℒₒᵣ] ⊧ isUTermVecOfSemitermVecOR ↔ ∀ v n k : V, IsSemitermVec ℒₒᵣ k n v → IsUTermVec ℒₒᵣ k v := by
  simp [isUTermVecOfSemitermVecOR, isUTermVecOfSemitermVecORB, models_iff, Matrix.vecForall_iff]
theorem pa_proves_isUTermVecOfSemitermVecOR : 𝗣𝗔 ⊢ isUTermVecOfSemitermVecOR :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_isUTermVecOfSemitermVecOR.mpr fun _ _ _ h ↦ h.isUTermVec
theorem lib_isUTermVecOfSemitermVecOR : Lib isUTermVecOfSemitermVecOR := Lib.of_pa pa_proves_isUTermVecOfSemitermVecOR

/-- `subst`, `neg`, `shift` of an `ℒₒᵣ`-formula are `ℒₒᵣ`-formulas (the `Formulas.lean` rows at `ℒₒᵣ`). -/
noncomputable def isSemiformulaSubstORB : ArithmeticSemisentence 5 :=
  “y w p m n. !(isSemiformula ℒₒᵣ).pi n p → !(isSemitermVec ℒₒᵣ).pi n m w → !(substsGraph ℒₒᵣ) y w p → !(isSemiformula ℒₒᵣ).sigma m y”
noncomputable def isSemiformulaSubstOR : ArithmeticSentence := ∀¹* isSemiformulaSubstORB
lemma models_isSemiformulaSubstOR :
    V↓[ℒₒᵣ] ⊧ isSemiformulaSubstOR ↔ ∀ y w p m n : V, IsSemiformula ℒₒᵣ n p → IsSemitermVec ℒₒᵣ n m w → y = subst ℒₒᵣ w p → IsSemiformula ℒₒᵣ m y := by
  simp [isSemiformulaSubstOR, isSemiformulaSubstORB, models_iff, Matrix.vecForall_iff, subst.defined.iff]
theorem pa_proves_isSemiformulaSubstOR : 𝗣𝗔 ⊢ isSemiformulaSubstOR :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_isSemiformulaSubstOR.mpr fun _ _ _ _ _ hp hw h ↦ by subst h; exact IsSemiformula.subst hp hw
theorem lib_isSemiformulaSubstOR : Lib isSemiformulaSubstOR := Lib.of_pa pa_proves_isSemiformulaSubstOR

noncomputable def isSemiformulaNegORB : ArithmeticSemisentence 3 :=
  “y p n. !(isSemiformula ℒₒᵣ).pi n p → !(negGraph ℒₒᵣ) y p → !(isSemiformula ℒₒᵣ).sigma n y”
noncomputable def isSemiformulaNegOR : ArithmeticSentence := ∀¹* isSemiformulaNegORB
lemma models_isSemiformulaNegOR :
    V↓[ℒₒᵣ] ⊧ isSemiformulaNegOR ↔ ∀ y p n : V, IsSemiformula ℒₒᵣ n p → y = neg ℒₒᵣ p → IsSemiformula ℒₒᵣ n y := by
  simp [isSemiformulaNegOR, isSemiformulaNegORB, models_iff, Matrix.vecForall_iff, neg.defined.iff]
theorem pa_proves_isSemiformulaNegOR : 𝗣𝗔 ⊢ isSemiformulaNegOR :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_isSemiformulaNegOR.mpr fun _ _ _ hp h ↦ by subst h; exact IsSemiformula.neg_iff.mpr hp
theorem lib_isSemiformulaNegOR : Lib isSemiformulaNegOR := Lib.of_pa pa_proves_isSemiformulaNegOR

noncomputable def isSemiformulaShiftORB : ArithmeticSemisentence 3 :=
  “y p n. !(isSemiformula ℒₒᵣ).pi n p → !(shiftGraph ℒₒᵣ) y p → !(isSemiformula ℒₒᵣ).sigma n y”
noncomputable def isSemiformulaShiftOR : ArithmeticSentence := ∀¹* isSemiformulaShiftORB
lemma models_isSemiformulaShiftOR :
    V↓[ℒₒᵣ] ⊧ isSemiformulaShiftOR ↔ ∀ y p n : V, IsSemiformula ℒₒᵣ n p → y = shift ℒₒᵣ p → IsSemiformula ℒₒᵣ n y := by
  simp [isSemiformulaShiftOR, isSemiformulaShiftORB, models_iff, Matrix.vecForall_iff, shift.defined.iff]
theorem pa_proves_isSemiformulaShiftOR : 𝗣𝗔 ⊢ isSemiformulaShiftOR :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_isSemiformulaShiftOR.mpr fun _ _ _ hp h ↦ by subst h; exact hp.shift
theorem lib_isSemiformulaShiftOR : Lib isSemiformulaShiftOR := Lib.of_pa pa_proves_isSemiformulaShiftOR

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

noncomputable def shiftGraphOROfLActB : ArithmeticSemisentence 2 :=
  “y p. !(isUFormula ℒₒᵣ).pi p → !(shiftGraph LAct) y p → !(shiftGraph ℒₒᵣ) y p”
noncomputable def shiftGraphOROfLAct : ArithmeticSentence := ∀¹* shiftGraphOROfLActB
lemma models_shiftGraphOROfLAct :
    V↓[ℒₒᵣ] ⊧ shiftGraphOROfLAct ↔ ∀ y p : V, IsUFormula ℒₒᵣ p → y = shift LAct p → y = shift ℒₒᵣ p := by
  simp [shiftGraphOROfLAct, shiftGraphOROfLActB, models_iff, Matrix.vecForall_iff, shift.defined.iff]
theorem pa_proves_shiftGraphOROfLAct : 𝗣𝗔 ⊢ shiftGraphOROfLAct :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_shiftGraphOROfLAct.mpr fun _ _ hp h ↦ h.trans (shift_LAct_eq hp)
theorem lib_shiftGraphOROfLAct : Lib shiftGraphOROfLAct := Lib.of_pa pa_proves_shiftGraphOROfLAct

noncomputable def bvGraphOROfLActB : ArithmeticSemisentence 2 :=
  “m p. !(isUFormula ℒₒᵣ).pi p → !(bvGraph LAct) m p → !(bvGraph ℒₒᵣ) m p”
noncomputable def bvGraphOROfLAct : ArithmeticSentence := ∀¹* bvGraphOROfLActB
lemma models_bvGraphOROfLAct :
    V↓[ℒₒᵣ] ⊧ bvGraphOROfLAct ↔ ∀ m p : V, IsUFormula ℒₒᵣ p → m = bv LAct p → m = bv ℒₒᵣ p := by
  simp [bvGraphOROfLAct, bvGraphOROfLActB, models_iff, Matrix.vecForall_iff]
theorem pa_proves_bvGraphOROfLAct : 𝗣𝗔 ⊢ bvGraphOROfLAct :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_bvGraphOROfLAct.mpr fun _ _ hp h ↦ h.trans (bv_LAct_eq hp)
theorem lib_bvGraphOROfLAct : Lib bvGraphOROfLAct := Lib.of_pa pa_proves_bvGraphOROfLAct

noncomputable def negGraphOROfLActB : ArithmeticSemisentence 2 :=
  “y p. !(isUFormula ℒₒᵣ).pi p → !(negGraph LAct) y p → !(negGraph ℒₒᵣ) y p”
noncomputable def negGraphOROfLAct : ArithmeticSentence := ∀¹* negGraphOROfLActB
lemma models_negGraphOROfLAct :
    V↓[ℒₒᵣ] ⊧ negGraphOROfLAct ↔ ∀ y p : V, IsUFormula ℒₒᵣ p → y = neg LAct p → y = neg ℒₒᵣ p := by
  simp [negGraphOROfLAct, negGraphOROfLActB, models_iff, Matrix.vecForall_iff]
theorem pa_proves_negGraphOROfLAct : 𝗣𝗔 ⊢ negGraphOROfLAct :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_negGraphOROfLAct.mpr fun _ _ hp h ↦ h.trans (neg_LAct_eq hp)
theorem lib_negGraphOROfLAct : Lib negGraphOROfLAct := Lib.of_pa pa_proves_negGraphOROfLAct

noncomputable def impGraphOROfLActB : ArithmeticSemisentence 3 :=
  “y q p. !(isUFormula ℒₒᵣ).pi p → !(impGraph LAct) y p q → !(impGraph ℒₒᵣ) y p q”
noncomputable def impGraphOROfLAct : ArithmeticSentence := ∀¹* impGraphOROfLActB
lemma models_impGraphOROfLAct :
    V↓[ℒₒᵣ] ⊧ impGraphOROfLAct ↔ ∀ y q p : V, IsUFormula ℒₒᵣ p → y = imp LAct p q → y = imp ℒₒᵣ p q := by
  simp [impGraphOROfLAct, impGraphOROfLActB, models_iff, Matrix.vecForall_iff, imp.defined.iff]
theorem pa_proves_impGraphOROfLAct : 𝗣𝗔 ⊢ impGraphOROfLAct :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_impGraphOROfLAct.mpr fun _ _ _ hp h ↦ h.trans (imp_LAct_eq hp)
theorem lib_impGraphOROfLAct : Lib impGraphOROfLAct := Lib.of_pa pa_proves_impGraphOROfLAct

noncomputable def termSubstVecGraphOROfLActB : ArithmeticSemisentence 4 :=
  “u w v k. !(isUTermVec ℒₒᵣ).pi k v → !(termSubstVecGraph LAct) u k w v → !(termSubstVecGraph ℒₒᵣ) u k w v”
noncomputable def termSubstVecGraphOROfLAct : ArithmeticSentence := ∀¹* termSubstVecGraphOROfLActB
lemma models_termSubstVecGraphOROfLAct :
    V↓[ℒₒᵣ] ⊧ termSubstVecGraphOROfLAct ↔ ∀ u w v k : V, IsUTermVec ℒₒᵣ k v → u = termSubstVec LAct k w v → u = termSubstVec ℒₒᵣ k w v := by
  simp [termSubstVecGraphOROfLAct, termSubstVecGraphOROfLActB, models_iff, Matrix.vecForall_iff, termSubstVec.defined.iff]
theorem pa_proves_termSubstVecGraphOROfLAct : 𝗣𝗔 ⊢ termSubstVecGraphOROfLAct :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_termSubstVecGraphOROfLAct.mpr fun _ _ _ _ hv h ↦ h.trans (termSubstVec_LAct_eq hv _)
theorem lib_termSubstVecGraphOROfLAct : Lib termSubstVecGraphOROfLAct := Lib.of_pa pa_proves_termSubstVecGraphOROfLAct

noncomputable def termShiftVecGraphOROfLActB : ArithmeticSemisentence 3 :=
  “u v k. !(isUTermVec ℒₒᵣ).pi k v → !(termShiftVecGraph LAct) u k v → !(termShiftVecGraph ℒₒᵣ) u k v”
noncomputable def termShiftVecGraphOROfLAct : ArithmeticSentence := ∀¹* termShiftVecGraphOROfLActB
lemma models_termShiftVecGraphOROfLAct :
    V↓[ℒₒᵣ] ⊧ termShiftVecGraphOROfLAct ↔ ∀ u v k : V, IsUTermVec ℒₒᵣ k v → u = termShiftVec LAct k v → u = termShiftVec ℒₒᵣ k v := by
  simp [termShiftVecGraphOROfLAct, termShiftVecGraphOROfLActB, models_iff, Matrix.vecForall_iff, termShiftVec.defined.iff]
theorem pa_proves_termShiftVecGraphOROfLAct : 𝗣𝗔 ⊢ termShiftVecGraphOROfLAct :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_termShiftVecGraphOROfLAct.mpr fun _ _ _ hv h ↦ h.trans (termShiftVec_LAct_eq hv)
theorem lib_termShiftVecGraphOROfLAct : Lib termShiftVecGraphOROfLAct := Lib.of_pa pa_proves_termShiftVecGraphOROfLAct

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

noncomputable def isUFormulaSigmaPiORB : ArithmeticSemisentence 1 :=
  “p. !(isUFormula ℒₒᵣ).sigma p → !(isUFormula ℒₒᵣ).pi p”
noncomputable def isUFormulaSigmaPiOR : ArithmeticSentence := ∀¹* isUFormulaSigmaPiORB
lemma models_isUFormulaSigmaPiOR :
    V↓[ℒₒᵣ] ⊧ isUFormulaSigmaPiOR ↔ ∀ p : V, IsUFormula ℒₒᵣ p → IsUFormula ℒₒᵣ p := by
  simp [isUFormulaSigmaPiOR, isUFormulaSigmaPiORB, models_iff]
theorem pa_proves_isUFormulaSigmaPiOR : 𝗣𝗔 ⊢ isUFormulaSigmaPiOR :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_isUFormulaSigmaPiOR.mpr fun _ h ↦ h
theorem lib_isUFormulaSigmaPiOR : Lib isUFormulaSigmaPiOR := Lib.of_pa pa_proves_isUFormulaSigmaPiOR

noncomputable def isSemitermSigmaPiORB : ArithmeticSemisentence 2 :=
  “t n. !(isSemiterm ℒₒᵣ).sigma n t → !(isSemiterm ℒₒᵣ).pi n t”
noncomputable def isSemitermSigmaPiOR : ArithmeticSentence := ∀¹* isSemitermSigmaPiORB
lemma models_isSemitermSigmaPiOR :
    V↓[ℒₒᵣ] ⊧ isSemitermSigmaPiOR ↔ ∀ t n : V, IsSemiterm ℒₒᵣ n t → IsSemiterm ℒₒᵣ n t := by
  simp [isSemitermSigmaPiOR, isSemitermSigmaPiORB, models_iff]
theorem pa_proves_isSemitermSigmaPiOR : 𝗣𝗔 ⊢ isSemitermSigmaPiOR :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_isSemitermSigmaPiOR.mpr fun _ _ h ↦ h
theorem lib_isSemitermSigmaPiOR : Lib isSemitermSigmaPiOR := Lib.of_pa pa_proves_isSemitermSigmaPiOR

noncomputable def isSemitermVecSigmaPiORB : ArithmeticSemisentence 3 :=
  “v n k. !(isSemitermVec ℒₒᵣ).sigma k n v → !(isSemitermVec ℒₒᵣ).pi k n v”
noncomputable def isSemitermVecSigmaPiOR : ArithmeticSentence := ∀¹* isSemitermVecSigmaPiORB
lemma models_isSemitermVecSigmaPiOR :
    V↓[ℒₒᵣ] ⊧ isSemitermVecSigmaPiOR ↔ ∀ v n k : V, IsSemitermVec ℒₒᵣ k n v → IsSemitermVec ℒₒᵣ k n v := by
  simp [isSemitermVecSigmaPiOR, isSemitermVecSigmaPiORB, models_iff]
theorem pa_proves_isSemitermVecSigmaPiOR : 𝗣𝗔 ⊢ isSemitermVecSigmaPiOR :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_isSemitermVecSigmaPiOR.mpr fun _ _ _ h ↦ h
theorem lib_isSemitermVecSigmaPiOR : Lib isSemitermVecSigmaPiOR := Lib.of_pa pa_proves_isSemitermVecSigmaPiOR

noncomputable def isUTermVecSigmaPiORB : ArithmeticSemisentence 2 :=
  “v k. !(isUTermVec ℒₒᵣ).sigma k v → !(isUTermVec ℒₒᵣ).pi k v”
noncomputable def isUTermVecSigmaPiOR : ArithmeticSentence := ∀¹* isUTermVecSigmaPiORB
lemma models_isUTermVecSigmaPiOR :
    V↓[ℒₒᵣ] ⊧ isUTermVecSigmaPiOR ↔ ∀ v k : V, IsUTermVec ℒₒᵣ k v → IsUTermVec ℒₒᵣ k v := by
  simp [isUTermVecSigmaPiOR, isUTermVecSigmaPiORB, models_iff]
theorem pa_proves_isUTermVecSigmaPiOR : 𝗣𝗔 ⊢ isUTermVecSigmaPiOR :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_isUTermVecSigmaPiOR.mpr fun _ _ h ↦ h
theorem lib_isUTermVecSigmaPiOR : Lib isUTermVecSigmaPiOR := Lib.of_pa pa_proves_isUTermVecSigmaPiOR

noncomputable def isSemiformulaSigmaPiLActB : ArithmeticSemisentence 2 :=
  “p n. !(isSemiformula LAct).sigma n p → !(isSemiformula LAct).pi n p”
noncomputable def isSemiformulaSigmaPiLAct : ArithmeticSentence := ∀¹* isSemiformulaSigmaPiLActB
lemma models_isSemiformulaSigmaPiLAct :
    V↓[ℒₒᵣ] ⊧ isSemiformulaSigmaPiLAct ↔ ∀ p n : V, IsSemiformula LAct n p → IsSemiformula LAct n p := by
  simp [isSemiformulaSigmaPiLAct, isSemiformulaSigmaPiLActB, models_iff]
theorem pa_proves_isSemiformulaSigmaPiLAct : 𝗣𝗔 ⊢ isSemiformulaSigmaPiLAct :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_isSemiformulaSigmaPiLAct.mpr fun _ _ h ↦ h
theorem lib_isSemiformulaSigmaPiLAct : Lib isSemiformulaSigmaPiLAct := Lib.of_pa pa_proves_isSemiformulaSigmaPiLAct

noncomputable def isUFormulaSigmaPiLActB : ArithmeticSemisentence 1 :=
  “p. !(isUFormula LAct).sigma p → !(isUFormula LAct).pi p”
noncomputable def isUFormulaSigmaPiLAct : ArithmeticSentence := ∀¹* isUFormulaSigmaPiLActB
lemma models_isUFormulaSigmaPiLAct :
    V↓[ℒₒᵣ] ⊧ isUFormulaSigmaPiLAct ↔ ∀ p : V, IsUFormula LAct p → IsUFormula LAct p := by
  simp [isUFormulaSigmaPiLAct, isUFormulaSigmaPiLActB, models_iff]
theorem pa_proves_isUFormulaSigmaPiLAct : 𝗣𝗔 ⊢ isUFormulaSigmaPiLAct :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_isUFormulaSigmaPiLAct.mpr fun _ h ↦ h
theorem lib_isUFormulaSigmaPiLAct : Lib isUFormulaSigmaPiLAct := Lib.of_pa pa_proves_isUFormulaSigmaPiLAct

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
