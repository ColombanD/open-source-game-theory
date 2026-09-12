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

end formulas

end ArithS
