import ArithS.Agents.Guard

/-!
# ArithS.Agents.SubstTemplate — instantiating a stored guard template with the outer frame

Half of the engine's `Prog.subst` on codes (the other half, program substitution `substCode`, is
`ArithS.Agents.Subst`, which builds on this file). The engine's `.sim p q` runs `p.subst me opp`
against `q.subst me opp`, and `subst` descends into the guard of every `.search` node — so a guard
inside a simulated program refers to the OUTER players. On codes:

* **Definition.** `substTemplate me opp g` instantiates a six-variable template with the canonical
  descriptions of `me` and `opp` — it IS `guardCode g me opp` on every template
  (`IsSemiformula LAct 6 g`, `substTemplate_of_template`). The result is a SENTENCE (no free
  variables), so a later `guardCode … me' opp'` is the identity on it (`guardCode_substTemplate`):
  a search node inside a simulated program evaluates its guard against the outer players whatever
  the current frame is — the engine's semantics. On a SEVEN-variable template (the budget slot
  `#6`; `ArithS.Agents.Guard`) it fills `#0..#5` with the outer descriptions and KEEPS `#6` a
  variable (`guardCodeSlot`, `substTemplate_of_template₇`), so the node that eventually runs the
  guard fills the slot with ITS budget: `guardCodeB (substTemplate me opp g) me' opp' k =
  guardCodeB g me opp k` (`guardCodeB_substTemplate₇`). Every other code is fixed
  (`substTemplate_of_not`, hypothesis `¬IsSemiformula LAct 7 g`). The identity on non-templates is
  what makes τ-equivariance hold on EVERY code: `subst` truncates out-of-range variables to `0`
  and `revalueTemplate` fixes the resulting non-formula, so on a code with more than seven free
  variables the two do not commute — `^rel 2 R ?[c_C, #8]` is a counterexample.
* **The gate lemma** `guardCodeB_of_template`: a six-variable template never reads the budget
  slot, so every six-variable statement is literally unchanged by the seventh slot.
* **The swap equation** `revalueTemplate_substTemplate`: transposing an instantiated template is
  instantiating the transposed template in the transposed frame, on every code — from the
  code-level swap equation for descriptions (`termRelabelVec_descriptions`) and the commutation of
  `revalueTemplate` with `subst` (`revalueTemplate_subst`, by the formula recursion).

Sections: `ℒₒᵣ` term codes are `LAct` term codes · the description terms are closed · substitution
fixes untouched variables · the gate lemma · the kept slot · `substTemplate` · commutation
(Foundation plumbing) · the swap equation.
-/

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open LAct

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ### `ℒₒᵣ` term codes are `LAct` term codes (`LAct` keeps the `ℒₒᵣ` symbol codes) -/

lemma isFunc_LOR {k f : V} : (ℒₒᵣ).IsFunc k f ↔
    (k = 0 ∧ f = 0) ∨ (k = 0 ∧ f = 1) ∨ (k = 2 ∧ f = 0) ∨ (k = 2 ∧ f = 1) := by
  rw [isFunc_def (L := ℒₒᵣ), func_def_LOR]; simp

lemma isFunc_LAct_of_LOR {k f : V} (h : (ℒₒᵣ).IsFunc k f) : LAct.IsFunc k f := by
  rw [isFunc_LAct]
  rcases isFunc_LOR.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))))

lemma IsUTerm.LAct_of_LOR {t : V} (ht : IsUTerm ℒₒᵣ t) : IsUTerm LAct t := by
  apply IsUTerm.induction 𝚺 ?_ ?_ ?_ ?_ t ht
  · definability
  · intro z; simp
  · intro x; simp
  · intro k f v hf hv ih
    exact IsUTerm.func (isFunc_LAct_of_LOR hf) ⟨hv.lh, ih⟩

lemma IsSemiterm.LAct_of_LOR {n t : V} (ht : IsSemiterm ℒₒᵣ n t) : IsSemiterm LAct n t := by
  apply IsSemiterm.induction 𝚺 ?_ ?_ ?_ ?_ t ht
  · definability
  · intro z hz; simp [hz]
  · intro x; simp
  · intro k f v hf hv ih
    rw [IsSemiterm.func]
    exact ⟨isFunc_LAct_of_LOR hf, IsSemitermVec.iff.mpr ⟨hv.lh, ih⟩⟩

/-! ### The description terms are closed `LAct` terms -/

lemma isFunc_csym {a : V} (ha : IsAct a) : LAct.IsFunc 0 (2 + a) := by
  rw [isFunc_LAct]
  rcases ha with rfl | rfl
  · exact Or.inr (Or.inr (Or.inl ⟨rfl, by norm_num⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, by norm_num⟩)))

lemma csym_semiterm {n a : V} (ha : IsAct a) : IsSemiterm LAct n (csym a) := by
  rw [csym, IsSemiterm.func]
  exact ⟨isFunc_csym ha, IsSemitermVec.nil _⟩

lemma numeral_semiterm_LAct (n x : V) : IsSemiterm LAct n (numeral x) :=
  IsSemiterm.LAct_of_LOR (numeral_semiterm n x)

lemma binNumeral_semiterm_LAct (n x : V) : IsSemiterm LAct n (binNumeral x) :=
  IsSemiterm.LAct_of_LOR (binNumeral_semiterm n x)

lemma codeTerm_semiterm_LAct (n x : V) : IsSemiterm LAct n (codeTerm x) :=
  IsSemiterm.LAct_of_LOR (codeTerm_semiterm n x)

lemma revalueU_semiterm (n x : V) : IsSemiterm LAct n (revalueU x) := by
  unfold revalueU
  split_ifs
  · exact csym_semiterm isAct_zero
  · exact csym_semiterm isAct_one
  · exact numeral_semiterm_LAct n 0

lemma revalueW_semiterm (n x : V) : IsSemiterm LAct n (revalueW x) := by
  unfold revalueW
  split_ifs
  · exact csym_semiterm isAct_one
  · exact csym_semiterm isAct_zero
  · exact numeral_semiterm_LAct n 1

lemma six_eq : (6 : V) = 0 + 1 + 1 + 1 + 1 + 1 + 1 := by norm_num

/-- The description vector is a vector of six closed terms. -/
lemma descriptions_semitermVec (me opp : V) : IsSemitermVec LAct 6 0 (descriptions me opp) := by
  rw [six_eq, descriptions]
  exact ((((((IsSemitermVec.nil 0).adjoin (revalueW_semiterm 0 opp)).adjoin (revalueU_semiterm 0 opp)).adjoin
    (codeTerm_semiterm_LAct 0 _)).adjoin (revalueW_semiterm 0 me)).adjoin (revalueU_semiterm 0 me)).adjoin
    (codeTerm_semiterm_LAct 0 _)

lemma len_descriptions (me opp : V) : len (descriptions me opp) = 6 := (descriptions_semitermVec me opp).lh

lemma descriptions_utermVec (me opp : V) : IsUTermVec LAct (len (descriptions me opp)) (descriptions me opp) := by
  rw [len_descriptions]; exact (descriptions_semitermVec me opp).isUTerm

/-- Instantiating a six-variable template gives a sentence. -/
lemma isSemiformula_guardCode {g : V} (hg : IsSemiformula LAct 6 g) (me opp : V) :
    IsSemiformula LAct 0 (guardCode g me opp) :=
  hg.subst (descriptions_semitermVec me opp)

/-! ### Substitution fixes a formula whose free variables it does not touch

`subst_eq_self` of Foundation needs a substitution vector of EXACTLY `n` variables; the
description vector has six entries and the instantiated template none, so we need the
version with a longer vector: a formula with `n` free variables is fixed by any vector of
terms whose first `n` entries are the variables themselves. -/

lemma subst_eq_self_of_le {n w p : V} (hp : IsSemiformula LAct n p) :
    IsUTermVec LAct (len w) w → n ≤ len w → (∀ i < n, w.[i] = ^#i) → subst LAct w p = p := by
  revert w
  apply IsSemiformula.pi1_structural_induction ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hp
  · definability
  · intro n k R v hR hv w _ _ H
    simp only [substs_rel, qqRel_inj, true_and, hR, hv.isUTerm]
    apply nth_ext' k (by simp [hv.isUTerm]) (by simp [hv.lh])
    intro i hi
    rw [nth_termSubstVec hv.isUTerm hi, termSubst_eq_self (hv.nth hi) H]
  · intro n k R v hR hv w _ _ H
    simp only [substs_nrel, qqNRel_inj, true_and, hR, hv.isUTerm]
    apply nth_ext' k (by simp [hv.isUTerm]) (by simp [hv.lh])
    intro i hi
    rw [nth_termSubstVec hv.isUTerm hi, termSubst_eq_self (hv.nth hi) H]
  · intro n w _ _ _; simp
  · intro n w _ _ _; simp
  · intro n p q hp hq ihp ihq w hw hn H
    simp [hp.isUFormula, hq.isUFormula, ihp hw hn H, ihq hw hn H]
  · intro n p q hp hq ihp ihq w hw hn H
    simp [hp.isUFormula, hq.isUFormula, ihp hw hn H, ihq hw hn H]
  · intro n p hp ih w hw hn H
    have hw' : IsUTermVec LAct (len (qVec LAct w)) (qVec LAct w) := by
      rw [len_qVec hw]; exact hw.isSemitermVec.qVec.isUTerm
    have hn' : n + 1 ≤ len (qVec LAct w) := by rw [len_qVec hw]; exact add_le_add hn (le_refl 1)
    have H' : ∀ i < n + 1, (qVec LAct w).[i] = ^#i := by
      intro i hi
      rcases zero_or_succ i with (rfl | ⟨i, rfl⟩)
      · simp [qVec]
      · have hi : i < n := by simpa using hi
        simp only [qVec, nth_adjoin_succ]
        rw [nth_termBShiftVec hw (lt_of_lt_of_le hi hn)]
        simp [H i hi]
    simp [hp.isUFormula, ih hw' hn' H']
  · intro n p hp ih w hw hn H
    have hw' : IsUTermVec LAct (len (qVec LAct w)) (qVec LAct w) := by
      rw [len_qVec hw]; exact hw.isSemitermVec.qVec.isUTerm
    have hn' : n + 1 ≤ len (qVec LAct w) := by rw [len_qVec hw]; exact add_le_add hn (le_refl 1)
    have H' : ∀ i < n + 1, (qVec LAct w).[i] = ^#i := by
      intro i hi
      rcases zero_or_succ i with (rfl | ⟨i, rfl⟩)
      · simp [qVec]
      · have hi : i < n := by simpa using hi
        simp only [qVec, nth_adjoin_succ]
        rw [nth_termBShiftVec hw (lt_of_lt_of_le hi hn)]
        simp [H i hi]
    simp [hp.isUFormula, ih hw' hn' H']

/-- A sentence is fixed by `guardCode`. -/
lemma guardCode_of_sentence {g : V} (hg : IsSemiformula LAct 0 g) (me opp : V) :
    guardCode g me opp = g :=
  subst_eq_self_of_le hg (descriptions_utermVec me opp) (by simp) (by simp)

/-! ### The guard code with the node budget (route c): the gate lemma

`guardCodeB g me opp k` (`ArithS.Guard`) fills `#0..#5` with the frame's descriptions and `#6` with
`binNumeral k`. The GATE LEMMA of the design: a six-variable template never reads the seventh entry, so on
every existing template `guardCodeB` IS `guardCode` (`guardCodeB_of_template`) — proved through the
identity vector `idVec6` (`subst_eq_self` at `(6, 6)`, then `substs_substs` at `(6, 7)`, then the
seven-entry `termSubstVec` computed entry by entry). -/

lemma seven_eq : (7 : V) = 0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 := by norm_num

/-- The description vector with the budget is a vector of seven closed terms. -/
lemma descriptionsB_semitermVec (me opp k : V) : IsSemitermVec LAct 7 0 (descriptionsB me opp k) := by
  rw [seven_eq, descriptionsB]
  exact (((((((IsSemitermVec.nil 0).adjoin (binNumeral_semiterm_LAct 0 k)).adjoin (revalueW_semiterm 0 opp)).adjoin
    (revalueU_semiterm 0 opp)).adjoin (codeTerm_semiterm_LAct 0 (canonical opp))).adjoin (revalueW_semiterm 0 me)).adjoin
    (revalueU_semiterm 0 me)).adjoin (codeTerm_semiterm_LAct 0 (canonical me))

lemma len_descriptionsB (me opp k : V) : len (descriptionsB me opp k) = 7 := (descriptionsB_semitermVec me opp k).lh

lemma descriptionsB_utermVec (me opp k : V) :
    IsUTermVec LAct (len (descriptionsB me opp k)) (descriptionsB me opp k) := by
  rw [len_descriptionsB]; exact (descriptionsB_semitermVec me opp k).isUTerm

/-- Instantiating a seven-variable template with the budget gives a sentence. -/
lemma isSemiformula_guardCodeB {g : V} (hg : IsSemiformula LAct 7 g) (me opp k : V) :
    IsSemiformula LAct 0 (guardCodeB g me opp k) :=
  hg.subst (descriptionsB_semitermVec me opp k)

/-- A sentence is fixed by `guardCodeB`. -/
lemma guardCodeB_of_sentence {g : V} (hg : IsSemiformula LAct 0 g) (me opp k : V) :
    guardCodeB g me opp k = g :=
  subst_eq_self_of_le hg (descriptionsB_utermVec me opp k) (by simp) (by simp)

/-- The identity vector on the six frame variables. -/
noncomputable def idVec6 : V := ^#0 ∷ ^#1 ∷ ^#2 ∷ ^#3 ∷ ^#4 ∷ ^#5 ∷ 0

lemma idVec6_semitermVec {n : V} (hn : 6 ≤ n) : IsSemitermVec LAct 6 n (idVec6 : V) := by
  have h0 : IsSemiterm LAct n (^#0 : V) := IsSemiterm.bvar.mpr (lt_of_lt_of_le (by norm_num) hn)
  have h1 : IsSemiterm LAct n (^#1 : V) := IsSemiterm.bvar.mpr (lt_of_lt_of_le (by norm_num) hn)
  have h2 : IsSemiterm LAct n (^#2 : V) := IsSemiterm.bvar.mpr (lt_of_lt_of_le (by norm_num) hn)
  have h3 : IsSemiterm LAct n (^#3 : V) := IsSemiterm.bvar.mpr (lt_of_lt_of_le (by norm_num) hn)
  have h4 : IsSemiterm LAct n (^#4 : V) := IsSemiterm.bvar.mpr (lt_of_lt_of_le (by norm_num) hn)
  have h5 : IsSemiterm LAct n (^#5 : V) := IsSemiterm.bvar.mpr (lt_of_lt_of_le (by norm_num) hn)
  have := ((((((IsSemitermVec.nil n).adjoin h5).adjoin h4).adjoin h3).adjoin h2).adjoin h1).adjoin h0
  rwa [← six_eq] at this

lemma nth_idVec6 : ∀ i < (6 : V), (idVec6 : V).[i] = ^#i := by
  intro i hi
  unfold idVec6
  rcases zero_or_succ i with rfl | ⟨i, rfl⟩
  · simp
  rw [nth_adjoin_succ]
  rcases zero_or_succ i with rfl | ⟨i, rfl⟩
  · simp
  rw [nth_adjoin_succ]
  rcases zero_or_succ i with rfl | ⟨i, rfl⟩
  · simp; norm_num
  rw [nth_adjoin_succ]
  rcases zero_or_succ i with rfl | ⟨i, rfl⟩
  · simp; norm_num
  rw [nth_adjoin_succ]
  rcases zero_or_succ i with rfl | ⟨i, rfl⟩
  · simp; norm_num
  rw [nth_adjoin_succ]
  rcases zero_or_succ i with rfl | ⟨i, rfl⟩
  · simp; norm_num
  exfalso
  have e6 : i + 1 + 1 + 1 + 1 + 1 + 1 = i + 6 := by ring
  rw [e6] at hi
  exact absurd hi (not_lt.mpr le_add_self)

/-- The seven-entry substitution restricted to the six frame variables is the description vector. -/
lemma termSubstVec_descriptionsB_idVec6 (me opp k : V) :
    termSubstVec LAct 6 (descriptionsB me opp k) (idVec6 : V) = descriptions me opp := by
  have h0 : IsUTerm LAct (^#0 : V) := (IsSemiterm.bvar.mpr (by norm_num : (0 : V) < 6)).isUTerm
  have h1 : IsUTerm LAct (^#1 : V) := (IsSemiterm.bvar.mpr (by norm_num : (1 : V) < 6)).isUTerm
  have h2 : IsUTerm LAct (^#2 : V) := (IsSemiterm.bvar.mpr (by norm_num : (2 : V) < 6)).isUTerm
  have h3 : IsUTerm LAct (^#3 : V) := (IsSemiterm.bvar.mpr (by norm_num : (3 : V) < 6)).isUTerm
  have h4 : IsUTerm LAct (^#4 : V) := (IsSemiterm.bvar.mpr (by norm_num : (4 : V) < 6)).isUTerm
  have h5 : IsUTerm LAct (^#5 : V) := (IsSemiterm.bvar.mpr (by norm_num : (5 : V) < 6)).isUTerm
  have e0 : IsUTermVec LAct 0 (0 : V) := IsUTermVec.empty
  have e1 := e0.adjoin h5
  have e2 := e1.adjoin h4
  have e3 := e2.adjoin h3
  have e4 := e3.adjoin h2
  have e5 := e4.adjoin h1
  unfold idVec6 descriptionsB descriptions
  rw [six_eq, termSubstVec_cons h0 e5, termSubstVec_cons h1 e4, termSubstVec_cons h2 e3,
    termSubstVec_cons h3 e2, termSubstVec_cons h4 e1, termSubstVec_cons h5 e0, termSubstVec_nil,
    termSubst_bvar, termSubst_bvar, termSubst_bvar, termSubst_bvar, termSubst_bvar, termSubst_bvar]
  simp only [nth_adjoin_zero, nth_adjoin_one, nth_adjoin_two]
  rw [show (3 : V) = 2 + 1 by norm_num, nth_adjoin_succ, nth_adjoin_two,
    show (4 : V) = 2 + 1 + 1 by norm_num, nth_adjoin_succ, nth_adjoin_succ, nth_adjoin_two,
    show (5 : V) = 2 + 1 + 1 + 1 by norm_num, nth_adjoin_succ, nth_adjoin_succ, nth_adjoin_succ, nth_adjoin_two]
  simp only [nth_adjoin_zero, nth_adjoin_one]

/-- **The gate lemma of route (c)**: a six-variable template never reads the budget slot — on every
existing template the guard code with the node budget IS the guard code. -/
theorem guardCodeB_of_template {g : V} (hg : IsSemiformula LAct 6 g) (me opp k : V) :
    guardCodeB g me opp k = guardCode g me opp := by
  have hid6 : IsSemitermVec LAct 6 6 (idVec6 : V) := idVec6_semitermVec (le_refl _)
  have hid7 : IsSemitermVec LAct 6 7 (idVec6 : V) := idVec6_semitermVec (by norm_num)
  have e : subst LAct (idVec6 : V) g = g := subst_eq_self hg hid6 nth_idVec6
  unfold guardCodeB guardCode
  calc subst LAct (descriptionsB me opp k) g
      = subst LAct (descriptionsB me opp k) (subst LAct (idVec6 : V) g) := by rw [e]
    _ = subst LAct (termSubstVec LAct 6 (descriptionsB me opp k) (idVec6 : V)) g :=
        substs_substs hg (descriptionsB_semitermVec me opp k) hid7
    _ = subst LAct (descriptions me opp) g := by rw [termSubstVec_descriptionsB_idVec6]

/-! ### The budget slot KEPT: `guardCodeSlot` (the `.sim` debt of route c, discharged)

`guardCodeSlot g me opp := subst (descriptionsSlot me opp) g` (`ArithS.Guard`) fills `#0..#5` of a
seven-variable template with the frame's descriptions and keeps `#6` a variable. The result is a
seven-variable formula with only `#6` free, and a later `guardCodeB … me' opp' k` in ANY frame fills
that one variable with `binNumeral k` (`termSubstVec_descriptionsB_descriptionsSlot`, `guardCodeB_guardCodeSlot`):
the seven-variable twin of `guardCode_of_sentence`, with the budget the RUNNING node's. -/

lemma bvar_six_semiterm : IsSemiterm LAct 7 (^#6 : V) := IsSemiterm.bvar.mpr (by norm_num)

/-- The kept-slot vector is a vector of seven terms of arity seven (six closed, one the variable `#6`). -/
lemma descriptionsSlot_semitermVec (me opp : V) : IsSemitermVec LAct 7 7 (descriptionsSlot me opp) := by
  unfold descriptionsSlot
  have := (((((((IsSemitermVec.nil 7).adjoin bvar_six_semiterm).adjoin (revalueW_semiterm 7 opp)).adjoin
    (revalueU_semiterm 7 opp)).adjoin (codeTerm_semiterm_LAct 7 (canonical opp))).adjoin (revalueW_semiterm 7 me)).adjoin
    (revalueU_semiterm 7 me)).adjoin (codeTerm_semiterm_LAct 7 (canonical me))
  rwa [← seven_eq] at this

lemma len_descriptionsSlot (me opp : V) : len (descriptionsSlot me opp) = 7 := (descriptionsSlot_semitermVec me opp).lh

/-- Filling `#0..#5` of a seven-variable template gives a seven-variable formula (`#6` is still free). -/
lemma isSemiformula_guardCodeSlot {g : V} (hg : IsSemiformula LAct 7 g) (me opp : V) :
    IsSemiformula LAct 7 (guardCodeSlot g me opp) :=
  hg.subst (descriptionsSlot_semitermVec me opp)

private lemma termSubst_of_closed (w : V) {t : V} (ht : IsSemiterm LAct 0 t) : termSubst LAct w t = t :=
  termSubst_eq_self ht (fun i hi ↦ absurd hi (by simp))

/-- The seventh entry of `descriptionsB` is the budget numeral. -/
lemma nth_descriptionsB_budget (me opp k : V) : (descriptionsB me opp k).[6] = binNumeral k := by
  unfold descriptionsB
  rw [show (6 : V) = 2 + 1 + 1 + 1 + 1 by norm_num, nth_adjoin_succ, nth_adjoin_succ, nth_adjoin_succ,
    nth_adjoin_succ]
  simp only [nth_adjoin_zero, nth_adjoin_one, nth_adjoin_two]

/-- Substituting `descriptionsB me' opp' k` into the kept-slot vector of `(me, opp)`: the six closed
descriptions are fixed and `#6 ↦ binNumeral k` — the frame is the OUTER one, the budget the node's. -/
theorem termSubstVec_descriptionsB_descriptionsSlot (me opp me' opp' k : V) :
    termSubstVec LAct 7 (descriptionsB me' opp' k) (descriptionsSlot me opp) = descriptionsB me opp k := by
  have h6 : IsUTerm LAct (^#6 : V) := bvar_six_semiterm.isUTerm
  have e0 : IsUTermVec LAct 0 (0 : V) := IsUTermVec.empty
  have e1 := e0.adjoin h6
  have e2 := e1.adjoin (revalueW_semiterm 0 opp).isUTerm
  have e3 := e2.adjoin (revalueU_semiterm 0 opp).isUTerm
  have e4 := e3.adjoin (codeTerm_semiterm_LAct 0 (canonical opp)).isUTerm
  have e5 := e4.adjoin (revalueW_semiterm 0 me).isUTerm
  have e6 := e5.adjoin (revalueU_semiterm 0 me).isUTerm
  unfold descriptionsSlot
  rw [seven_eq, termSubstVec_cons (codeTerm_semiterm_LAct 0 (canonical me)).isUTerm e6,
    termSubstVec_cons (revalueU_semiterm 0 me).isUTerm e5, termSubstVec_cons (revalueW_semiterm 0 me).isUTerm e4,
    termSubstVec_cons (codeTerm_semiterm_LAct 0 (canonical opp)).isUTerm e3,
    termSubstVec_cons (revalueU_semiterm 0 opp).isUTerm e2, termSubstVec_cons (revalueW_semiterm 0 opp).isUTerm e1,
    termSubstVec_cons h6 e0, termSubstVec_nil, termSubst_bvar, nth_descriptionsB_budget,
    termSubst_of_closed _ (codeTerm_semiterm_LAct 0 (canonical me)), termSubst_of_closed _ (revalueU_semiterm 0 me),
    termSubst_of_closed _ (revalueW_semiterm 0 me), termSubst_of_closed _ (codeTerm_semiterm_LAct 0 (canonical opp)),
    termSubst_of_closed _ (revalueU_semiterm 0 opp), termSubst_of_closed _ (revalueW_semiterm 0 opp)]
  rfl

/-- **The seven-variable twin of `guardCode_of_sentence`**: after `guardCodeSlot` by the OUTER frame,
`guardCodeB` in ANY frame at budget `k` is the outer frame's guard code at `k`. -/
theorem guardCodeB_guardCodeSlot {g : V} (hg : IsSemiformula LAct 7 g) (me opp me' opp' k : V) :
    guardCodeB (guardCodeSlot g me opp) me' opp' k = guardCodeB g me opp k := by
  unfold guardCodeB guardCodeSlot
  rw [substs_substs hg (descriptionsB_semitermVec me' opp' k) (descriptionsSlot_semitermVec me opp),
    termSubstVec_descriptionsB_descriptionsSlot]

/-- Arity monotonicity of `IsSemiformula` (from the structure: `bv p ≤ n ≤ m`). -/
lemma isSemiformula_of_le {n m p : V} (hp : IsSemiformula LAct n p) (h : n ≤ m) : IsSemiformula LAct m p :=
  ⟨hp.isUFormula, le_trans hp.bv_le h⟩

lemma isSemiformula_seven_of_six {g : V} (hg : IsSemiformula LAct 6 g) : IsSemiformula LAct 7 g :=
  isSemiformula_of_le hg (by norm_num)

/-! ### The member slots KEPT OUT of every existing template: the gate lemma of `sysCloseTemplate`

`sysCloseTemplate d g` (`ArithS.Agents.Guard`) fills `#7..#12` of a thirteen-variable template with the closed
descriptions of the two members of `d` and keeps `#0..#6` as variables. Its gate lemma
`sysCloseTemplate_of_template₇`: a seven-variable template (so every six-variable one) never reads a member
slot and is unchanged — the twin of `guardCodeB_of_template`, by `subst_eq_self_of_le` on the vector whose
first seven entries are the variables themselves. -/

lemma thirteen_eq : (13 : V) = 0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 := by norm_num

/-- The member-slot vector is a vector of thirteen terms of arity thirteen (seven variables, six closed). -/
lemma descriptionsSys_semitermVec (d : V) : IsSemitermVec LAct 13 13 (descriptionsSys d) := by
  have h0 : IsSemiterm LAct 13 (^#0 : V) := IsSemiterm.bvar.mpr (by norm_num)
  have h1 : IsSemiterm LAct 13 (^#1 : V) := IsSemiterm.bvar.mpr (by norm_num)
  have h2 : IsSemiterm LAct 13 (^#2 : V) := IsSemiterm.bvar.mpr (by norm_num)
  have h3 : IsSemiterm LAct 13 (^#3 : V) := IsSemiterm.bvar.mpr (by norm_num)
  have h4 : IsSemiterm LAct 13 (^#4 : V) := IsSemiterm.bvar.mpr (by norm_num)
  have h5 : IsSemiterm LAct 13 (^#5 : V) := IsSemiterm.bvar.mpr (by norm_num)
  have h6 : IsSemiterm LAct 13 (^#6 : V) := IsSemiterm.bvar.mpr (by norm_num)
  unfold descriptionsSys
  have := (((((((((((((IsSemitermVec.nil 13).adjoin (revalueW_semiterm 13 (pSys d 1))).adjoin
    (revalueU_semiterm 13 (pSys d 1))).adjoin (codeTerm_semiterm_LAct 13 (canonical (pSys d 1)))).adjoin
    (revalueW_semiterm 13 (pSys d 0))).adjoin (revalueU_semiterm 13 (pSys d 0))).adjoin
    (codeTerm_semiterm_LAct 13 (canonical (pSys d 0)))).adjoin h6).adjoin h5).adjoin h4).adjoin h3).adjoin h2).adjoin
    h1).adjoin h0
  rwa [← thirteen_eq] at this

lemma len_descriptionsSys (d : V) : len (descriptionsSys d) = 13 := (descriptionsSys_semitermVec d).lh

lemma descriptionsSys_utermVec (d : V) : IsUTermVec LAct (len (descriptionsSys d)) (descriptionsSys d) := by
  rw [len_descriptionsSys]; exact (descriptionsSys_semitermVec d).isUTerm

/-- The first seven entries of the member-slot vector are the variables themselves. -/
lemma nth_descriptionsSys (d : V) : ∀ i < (7 : V), (descriptionsSys d).[i] = ^#i := by
  intro i hi
  unfold descriptionsSys
  rcases zero_or_succ i with rfl | ⟨i, rfl⟩
  · simp
  rw [nth_adjoin_succ]
  rcases zero_or_succ i with rfl | ⟨i, rfl⟩
  · simp
  rw [nth_adjoin_succ]
  rcases zero_or_succ i with rfl | ⟨i, rfl⟩
  · simp; norm_num
  rw [nth_adjoin_succ]
  rcases zero_or_succ i with rfl | ⟨i, rfl⟩
  · simp; norm_num
  rw [nth_adjoin_succ]
  rcases zero_or_succ i with rfl | ⟨i, rfl⟩
  · simp; norm_num
  rw [nth_adjoin_succ]
  rcases zero_or_succ i with rfl | ⟨i, rfl⟩
  · simp; norm_num
  rw [nth_adjoin_succ]
  rcases zero_or_succ i with rfl | ⟨i, rfl⟩
  · simp; norm_num
  exfalso
  have e7 : i + 1 + 1 + 1 + 1 + 1 + 1 + 1 = i + 7 := by ring
  rw [e7] at hi
  exact absurd hi (not_lt.mpr le_add_self)

lemma sysCloseTemplate_of_template₁₃ {g : V} (hg : IsSemiformula LAct 13 g) (d : V) :
    sysCloseTemplate d g = subst LAct (descriptionsSys d) g := by
  unfold sysCloseTemplate; rw [if_pos hg]; rfl

lemma sysCloseTemplate_of_not {g : V} (hg : ¬IsSemiformula LAct 13 g) (d : V) : sysCloseTemplate d g = g := by
  unfold sysCloseTemplate; rw [if_neg hg]

/-- **The gate lemma of the member slots**: a seven-variable template never reads a member slot, so
`sysCloseTemplate` is the identity on every template of the compiled zoo. -/
theorem sysCloseTemplate_of_template₇ {g : V} (hg : IsSemiformula LAct 7 g) (d : V) : sysCloseTemplate d g = g := by
  rw [sysCloseTemplate_of_template₁₃ (isSemiformula_of_le hg (by norm_num))]
  exact subst_eq_self_of_le hg (descriptionsSys_utermVec d) (by rw [len_descriptionsSys]; norm_num)
    (nth_descriptionsSys d)

theorem sysCloseTemplate_of_template {g : V} (hg : IsSemiformula LAct 6 g) (d : V) : sysCloseTemplate d g = g :=
  sysCloseTemplate_of_template₇ (isSemiformula_seven_of_six hg) d

/-- Filling the member slots of a thirteen-variable template gives a thirteen-variable formula (`#0..#6` free). -/
lemma isSemiformula_sysCloseTemplate {g : V} (hg : IsSemiformula LAct 13 g) (d : V) :
    IsSemiformula LAct 13 (sysCloseTemplate d g) := by
  rw [sysCloseTemplate_of_template₁₃ hg]; exact hg.subst (descriptionsSys_semitermVec d)

/-! ### The member slots at the node's budget (Phase 2d): gate lemmas and THE BRIDGE

`sysCloseTemplateAt d k g` (`ArithS.Agents.Guard`) fills the member slots with the descriptions of the members
of `d`, the node budget `k` abstracted into the slot `#6` (`codeTermAbs k ^#6`). Its gate lemmas are those of
`sysCloseTemplate`; the bridge `guardCodeB_sysCloseTemplateAt` says the sentence the evaluator CONSULTS for a
closed member is the one the verbatim closer gives — the system twin of `guardCodeB_templateCodeAt`
(`ArithS.Agents.Code`): `guardCodeB` fills `#6` with `binNumeral k`, and `codeTermAbs k (binNumeral k) = codeTerm`. -/

section slot

lemma isFunc_LAct_add : LAct.IsFunc 2 (addIndex : V) := isFunc_LAct_of_LOR LOR_func_addIndex
lemma isFunc_LAct_mul : LAct.IsFunc 2 (mulIndex : V) := isFunc_LAct_of_LOR LOR_func_mulIndex

lemma qqAdd_uterm_LAct {s t : V} (hs : IsUTerm LAct s) (ht : IsUTerm LAct t) : IsUTerm LAct (s ^+ t) := by
  unfold qqAdd; exact IsUTerm.func isFunc_LAct_add (by simp [hs, ht])
lemma qqMul_uterm_LAct {s t : V} (hs : IsUTerm LAct s) (ht : IsUTerm LAct t) : IsUTerm LAct (s ^* t) := by
  unfold qqMul; exact IsUTerm.func isFunc_LAct_mul (by simp [hs, ht])
lemma ppairTerm_uterm_LAct {s t : V} (hs : IsUTerm LAct s) (ht : IsUTerm LAct t) : IsUTerm LAct (ppairTerm s t) :=
  qqAdd_uterm_LAct (qqMul_uterm_LAct (qqAdd_uterm_LAct hs ht) (qqAdd_uterm_LAct hs ht)) ht

lemma termSubst_qqAdd (w : V) {s t : V} (hs : IsUTerm LAct s) (ht : IsUTerm LAct t) :
    termSubst LAct w (s ^+ t) = termSubst LAct w s ^+ termSubst LAct w t := by
  unfold qqAdd
  rw [termSubst_func isFunc_LAct_add (by simp [hs, ht]), termSubstVec_cons₂ hs ht]

lemma termSubst_qqMul (w : V) {s t : V} (hs : IsUTerm LAct s) (ht : IsUTerm LAct t) :
    termSubst LAct w (s ^* t) = termSubst LAct w s ^* termSubst LAct w t := by
  unfold qqMul
  rw [termSubst_func isFunc_LAct_mul (by simp [hs, ht]), termSubstVec_cons₂ hs ht]

lemma termSubst_ppairTerm (w : V) {s t : V} (hs : IsUTerm LAct s) (ht : IsUTerm LAct t) :
    termSubst LAct w (ppairTerm s t) = ppairTerm (termSubst LAct w s) (termSubst LAct w t) := by
  unfold ppairTerm
  rw [termSubst_qqAdd w (qqMul_uterm_LAct (qqAdd_uterm_LAct hs ht) (qqAdd_uterm_LAct hs ht)) ht,
    termSubst_qqMul w (qqAdd_uterm_LAct hs ht) (qqAdd_uterm_LAct hs ht), termSubst_qqAdd w hs ht]

/-- A closed term code is fixed by every substitution. -/
lemma termSubst_closed (w : V) {t : V} (ht : IsSemiterm LAct 0 t) : termSubst LAct w t = t :=
  termSubst_eq_self ht (fun i hi ↦ absurd hi (by simp))

lemma one_uterm_LAct : IsUTerm LAct (𝟏 : V) := (IsSemiterm.LAct_of_LOR (one_semiterm (n := 0))).isUTerm

/-- Substitution through the shape `ppairTerm a b ^+ 𝟏` every description clause has. -/
lemma termSubst_succ_ppairTerm (w : V) {a b : V} (ha : IsUTerm LAct a) (hb : IsUTerm LAct b) :
    termSubst LAct w (ppairTerm a b ^+ (𝟏 : V)) = ppairTerm (termSubst LAct w a) (termSubst LAct w b) ^+ (𝟏 : V) := by
  rw [termSubst_qqAdd w (ppairTerm_uterm_LAct ha hb) one_uterm_LAct, termSubst_ppairTerm w ha hb,
    termSubst_closed w (IsSemiterm.LAct_of_LOR one_semiterm)]

lemma codeTermAbs_semiterm_LAct {n k₀ s : V} (hs : IsSemiterm ℒₒᵣ n s) (x : V) :
    IsSemiterm LAct n (codeTermAbs k₀ s x) :=
  IsSemiterm.LAct_of_LOR (codeTermAbs_semiterm hs x)

lemma termSubst_budgetLeaf (w k₀ s k : V) :
    termSubst LAct w (budgetLeaf k₀ s k) = budgetLeaf k₀ (termSubst LAct w s) k := by
  unfold budgetLeaf
  split_ifs
  · rfl
  · exact termSubst_closed w (binNumeral_semiterm_LAct 0 k)

/-- **Substitution commutes with the abstracted description**: everything but the slot is closed, so a
substitution acts on the slot term only. -/
theorem termSubst_codeTermAbs (w : V) {n s : V} (hs : IsSemiterm ℒₒᵣ n s) (k₀ x : V) :
    termSubst LAct w (codeTermAbs k₀ s x) = codeTermAbs k₀ (termSubst LAct w s) x := by
  induction x using ISigma1.pi1_order_induction with
  | hP => definability
  | ind x ih =>
    have hb : ∀ a : V, IsUTerm LAct (binNumeral a) := fun a ↦ (binNumeral_semiterm_LAct 0 a).isUTerm
    have hbc : ∀ a : V, termSubst LAct w (binNumeral a) = binNumeral a :=
      fun a ↦ termSubst_closed w (binNumeral_semiterm_LAct 0 a)
    have hc : ∀ y : V, IsUTerm LAct (codeTermAbs k₀ s y) := fun y ↦ (codeTermAbs_semiterm_LAct hs y).isUTerm
    have hpp : ∀ {a c : V}, IsUTerm LAct a → IsUTerm LAct c → IsUTerm LAct (ppairTerm a c) :=
      fun ha hc ↦ ppairTerm_uterm_LAct ha hc
    by_cases hx : IsShape x
    · rcases hx with ⟨a, rfl⟩ | rfl | rfl | ⟨p, rfl⟩ | ⟨p, q, rfl⟩ | ⟨b, a, p, q, rfl⟩ | ⟨k', g, p, q, rfl⟩ |
        ⟨v, θ, p, q, rfl⟩ | ⟨d, i, rfl⟩ | ⟨j, rfl⟩ | ⟨e, r, rfl⟩
      · rw [codeTermAbs_const, codeTermAbs_const, termSubst_succ_ppairTerm w (hb _) (hb _), hbc, hbc]
      · rw [codeTermAbs_self, codeTermAbs_self, termSubst_succ_ppairTerm w (hb _) (hb _), hbc, hbc]
      · rw [codeTermAbs_opp, codeTermAbs_opp, termSubst_succ_ppairTerm w (hb _) (hb _), hbc, hbc]
      · rw [codeTermAbs_bot, codeTermAbs_bot, termSubst_succ_ppairTerm w (hb _) (hc _), hbc, ih p (by simp)]
      · rw [codeTermAbs_sim, codeTermAbs_sim, termSubst_succ_ppairTerm w (hb _) (hpp (hc _) (hc _)),
          termSubst_ppairTerm w (hc _) (hc _), hbc, ih p (by simp), ih q (by simp)]
      · rw [codeTermAbs_ite, codeTermAbs_ite,
          termSubst_succ_ppairTerm w (hb _) (hpp (hc _) (hpp (hb _) (hpp (hc _) (hc _)))),
          termSubst_ppairTerm w (hc _) (hpp (hb _) (hpp (hc _) (hc _))),
          termSubst_ppairTerm w (hb _) (hpp (hc _) (hc _)), termSubst_ppairTerm w (hc _) (hc _), hbc, hbc,
          ih b (by simp), ih p (by simp), ih q (by simp)]
      · have hl : IsUTerm LAct (budgetLeaf k₀ s k') := by
          unfold budgetLeaf; split_ifs
          · exact (IsSemiterm.LAct_of_LOR hs).isUTerm
          · exact hb _
        rw [codeTermAbs_search, codeTermAbs_search,
          termSubst_succ_ppairTerm w (hb _) (hpp hl (hpp (hb _) (hpp (hc _) (hc _)))),
          termSubst_ppairTerm w hl (hpp (hb _) (hpp (hc _) (hc _))),
          termSubst_ppairTerm w (hb _) (hpp (hc _) (hc _)), termSubst_ppairTerm w (hc _) (hc _), hbc, hbc,
          termSubst_budgetLeaf, ih p (by simp), ih q (by simp)]
      · rw [codeTermAbs_tvote, codeTermAbs_tvote,
          termSubst_succ_ppairTerm w (hb _) (hpp (hc _) (hpp (hb _) (hpp (hc _) (hc _)))),
          termSubst_ppairTerm w (hc _) (hpp (hb _) (hpp (hc _) (hc _))),
          termSubst_ppairTerm w (hb _) (hpp (hc _) (hc _)), termSubst_ppairTerm w (hc _) (hc _), hbc, hbc,
          ih v (by simp), ih p (by simp), ih q (by simp)]
      · rw [codeTermAbs_sys, codeTermAbs_sys, termSubst_succ_ppairTerm w (hb _) (hpp (hc _) (hb _)),
          termSubst_ppairTerm w (hc _) (hb _), hbc, hbc, ih d (by simp)]
      · rw [codeTermAbs_selfIdx, codeTermAbs_selfIdx, termSubst_succ_ppairTerm w (hb _) (hb _), hbc, hbc]
      · rw [codeTermAbs_cons, codeTermAbs_cons, termSubst_succ_ppairTerm w (hb _) (hpp (hc _) (hc _)),
          termSubst_ppairTerm w (hc _) (hc _), hbc, ih e (by simp), ih r (by simp)]
    · rw [codeTermAbs_of_not_shape hx, codeTermAbs_of_not_shape hx, hbc]

lemma bvar_six_semiterm_LOR {n : V} (hn : 7 ≤ n) : IsSemiterm ℒₒᵣ n (^#6 : V) :=
  IsSemiterm.bvar.mpr (lt_of_lt_of_le (by norm_num) hn)

/-- **Filling the budget slot of an abstracted member description recovers the verbatim description.** -/
theorem termSubst_descriptionsB_codeTermAbs (me opp k c : V) :
    termSubst LAct (descriptionsB me opp k) (codeTermAbs k (^#6) c) = codeTerm c := by
  rw [termSubst_codeTermAbs _ (bvar_six_semiterm_LOR (le_refl 7)), termSubst_bvar, nth_descriptionsB_budget,
    codeTermAbs_binNumeral]

/-- The member-slot vector at the node budget is a vector of thirteen terms of arity `n ≥ 7` (the variables
`#0..#6`, four closed terms, two terms in `#6`). -/
lemma descriptionsSysAt_semitermVec {n : V} (hn : 7 ≤ n) (d k : V) : IsSemitermVec LAct 13 n (descriptionsSysAt d k) := by
  have h0 : IsSemiterm LAct n (^#0 : V) := IsSemiterm.bvar.mpr (lt_of_lt_of_le (by norm_num) hn)
  have h1 : IsSemiterm LAct n (^#1 : V) := IsSemiterm.bvar.mpr (lt_of_lt_of_le (by norm_num) hn)
  have h2 : IsSemiterm LAct n (^#2 : V) := IsSemiterm.bvar.mpr (lt_of_lt_of_le (by norm_num) hn)
  have h3 : IsSemiterm LAct n (^#3 : V) := IsSemiterm.bvar.mpr (lt_of_lt_of_le (by norm_num) hn)
  have h4 : IsSemiterm LAct n (^#4 : V) := IsSemiterm.bvar.mpr (lt_of_lt_of_le (by norm_num) hn)
  have h5 : IsSemiterm LAct n (^#5 : V) := IsSemiterm.bvar.mpr (lt_of_lt_of_le (by norm_num) hn)
  have h6 : IsSemiterm LAct n (^#6 : V) := IsSemiterm.bvar.mpr (lt_of_lt_of_le (by norm_num) hn)
  have hs := bvar_six_semiterm_LOR (V := V) hn
  unfold descriptionsSysAt
  have := (((((((((((((IsSemitermVec.nil n).adjoin (revalueW_semiterm n (pSys d 1))).adjoin
    (revalueU_semiterm n (pSys d 1))).adjoin (codeTermAbs_semiterm_LAct (k₀ := k) hs (canonical (pSys d 1)))).adjoin
    (revalueW_semiterm n (pSys d 0))).adjoin (revalueU_semiterm n (pSys d 0))).adjoin
    (codeTermAbs_semiterm_LAct (k₀ := k) hs (canonical (pSys d 0)))).adjoin h6).adjoin h5).adjoin h4).adjoin h3).adjoin h2).adjoin
    h1).adjoin h0
  rwa [← thirteen_eq] at this

lemma len_descriptionsSysAt (d k : V) : len (descriptionsSysAt d k) = 13 :=
  (descriptionsSysAt_semitermVec (le_refl 7) d k).lh

lemma descriptionsSysAt_utermVec (d k : V) : IsUTermVec LAct (len (descriptionsSysAt d k)) (descriptionsSysAt d k) := by
  rw [len_descriptionsSysAt]; exact (descriptionsSysAt_semitermVec (le_refl 7) d k).isUTerm

/-- The first seven entries of the member-slot vector at the node budget are the variables themselves. -/
lemma nth_descriptionsSysAt (d k : V) : ∀ i < (7 : V), (descriptionsSysAt d k).[i] = ^#i := by
  intro i hi
  unfold descriptionsSysAt
  rcases zero_or_succ i with rfl | ⟨i, rfl⟩
  · simp
  rw [nth_adjoin_succ]
  rcases zero_or_succ i with rfl | ⟨i, rfl⟩
  · simp
  rw [nth_adjoin_succ]
  rcases zero_or_succ i with rfl | ⟨i, rfl⟩
  · simp; norm_num
  rw [nth_adjoin_succ]
  rcases zero_or_succ i with rfl | ⟨i, rfl⟩
  · simp; norm_num
  rw [nth_adjoin_succ]
  rcases zero_or_succ i with rfl | ⟨i, rfl⟩
  · simp; norm_num
  rw [nth_adjoin_succ]
  rcases zero_or_succ i with rfl | ⟨i, rfl⟩
  · simp; norm_num
  rw [nth_adjoin_succ]
  rcases zero_or_succ i with rfl | ⟨i, rfl⟩
  · simp; norm_num
  exfalso
  have e7 : i + 1 + 1 + 1 + 1 + 1 + 1 + 1 = i + 7 := by ring
  rw [e7] at hi
  exact absurd hi (not_lt.mpr le_add_self)

lemma sysCloseTemplateAt_of_template₁₃ {g : V} (hg : IsSemiformula LAct 13 g) (d k : V) :
    sysCloseTemplateAt d k g = subst LAct (descriptionsSysAt d k) g := by
  unfold sysCloseTemplateAt; rw [if_pos hg]; rfl

lemma sysCloseTemplateAt_of_not {g : V} (hg : ¬IsSemiformula LAct 13 g) (d k : V) : sysCloseTemplateAt d k g = g := by
  unfold sysCloseTemplateAt; rw [if_neg hg]

/-- **The gate lemma of the member slots, at the node budget**: a seven-variable template never reads a member
slot, so `sysCloseTemplateAt` is the identity on every template of the compiled zoo that names no pronoun. -/
theorem sysCloseTemplateAt_of_template₇ {g : V} (hg : IsSemiformula LAct 7 g) (d k : V) : sysCloseTemplateAt d k g = g := by
  rw [sysCloseTemplateAt_of_template₁₃ (isSemiformula_of_le hg (by norm_num))]
  exact subst_eq_self_of_le hg (descriptionsSysAt_utermVec d k) (by rw [len_descriptionsSysAt]; norm_num)
    (nth_descriptionsSysAt d k)

theorem sysCloseTemplateAt_of_template {g : V} (hg : IsSemiformula LAct 6 g) (d k : V) : sysCloseTemplateAt d k g = g :=
  sysCloseTemplateAt_of_template₇ (isSemiformula_seven_of_six hg) d k

/-- Filling the member slots at the node budget gives a SEVEN-variable formula (`#0..#6` free). -/
lemma isSemiformula_sysCloseTemplateAt₇ {g : V} (hg : IsSemiformula LAct 13 g) (d k : V) :
    IsSemiformula LAct 7 (sysCloseTemplateAt d k g) := by
  rw [sysCloseTemplateAt_of_template₁₃ hg]; exact hg.subst (descriptionsSysAt_semitermVec (le_refl 7) d k)

lemma isSemiformula_sysCloseTemplateAt {g : V} (hg : IsSemiformula LAct 13 g) (d k : V) :
    IsSemiformula LAct 13 (sysCloseTemplateAt d k g) :=
  isSemiformula_of_le (isSemiformula_sysCloseTemplateAt₇ hg d k) (by norm_num)

/-- The verbatim member-slot vector is also a vector of thirteen terms of arity SEVEN (the variables `#0..#6`,
six closed terms) — what `substs_substs` needs to compose it with the frame substitution. -/
lemma descriptionsSys_semitermVec₇ (d : V) : IsSemitermVec LAct 13 7 (descriptionsSys d) := by
  have h0 : IsSemiterm LAct 7 (^#0 : V) := IsSemiterm.bvar.mpr (by norm_num)
  have h1 : IsSemiterm LAct 7 (^#1 : V) := IsSemiterm.bvar.mpr (by norm_num)
  have h2 : IsSemiterm LAct 7 (^#2 : V) := IsSemiterm.bvar.mpr (by norm_num)
  have h3 : IsSemiterm LAct 7 (^#3 : V) := IsSemiterm.bvar.mpr (by norm_num)
  have h4 : IsSemiterm LAct 7 (^#4 : V) := IsSemiterm.bvar.mpr (by norm_num)
  have h5 : IsSemiterm LAct 7 (^#5 : V) := IsSemiterm.bvar.mpr (by norm_num)
  have h6 : IsSemiterm LAct 7 (^#6 : V) := IsSemiterm.bvar.mpr (by norm_num)
  unfold descriptionsSys
  have := (((((((((((((IsSemitermVec.nil 7).adjoin (revalueW_semiterm 7 (pSys d 1))).adjoin
    (revalueU_semiterm 7 (pSys d 1))).adjoin (codeTerm_semiterm_LAct 7 (canonical (pSys d 1)))).adjoin
    (revalueW_semiterm 7 (pSys d 0))).adjoin (revalueU_semiterm 7 (pSys d 0))).adjoin
    (codeTerm_semiterm_LAct 7 (canonical (pSys d 0)))).adjoin h6).adjoin h5).adjoin h4).adjoin h3).adjoin h2).adjoin
    h1).adjoin h0
  rwa [← thirteen_eq] at this

/-- **The two member-slot vectors agree once the frame fills the budget slot**: composing `descriptionsB me opp k`
with the abstracted vector at `k` is composing it with the verbatim vector. -/
theorem termSubstVec_descriptionsB_descriptionsSysAt (me opp k d : V) :
    termSubstVec LAct 13 (descriptionsB me opp k) (descriptionsSysAt d k) =
      termSubstVec LAct 13 (descriptionsB me opp k) (descriptionsSys d) := by
  have b : ∀ i : V, IsUTerm LAct (^#i : V) := fun i ↦ (IsSemiterm.bvar.mpr (lt_add_one i) : IsSemiterm LAct (i + 1) (^#i)).isUTerm
  have c : ∀ x : V, IsUTerm LAct (codeTerm x) := fun x ↦ (codeTerm_semiterm_LAct 0 x).isUTerm
  have ca : ∀ x : V, IsUTerm LAct (codeTermAbs k (^#6) x) :=
    fun x ↦ (codeTermAbs_semiterm_LAct (bvar_six_semiterm_LOR (le_refl 7)) x).isUTerm
  have ru : ∀ x : V, IsUTerm LAct (revalueU x) := fun x ↦ (revalueU_semiterm 0 x).isUTerm
  have rw' : ∀ x : V, IsUTerm LAct (revalueW x) := fun x ↦ (revalueW_semiterm 0 x).isUTerm
  have e0 : IsUTermVec LAct 0 (0 : V) := IsUTermVec.empty
  have e1 := e0.adjoin (rw' (pSys d 1))
  have e2 := e1.adjoin (ru (pSys d 1))
  have e3 := e2.adjoin (c (canonical (pSys d 1)))
  have e4 := e3.adjoin (rw' (pSys d 0))
  have e5 := e4.adjoin (ru (pSys d 0))
  have e6 := e5.adjoin (c (canonical (pSys d 0)))
  have e7 := e6.adjoin (b 6)
  have e8 := e7.adjoin (b 5)
  have e9 := e8.adjoin (b 4)
  have e10 := e9.adjoin (b 3)
  have e11 := e10.adjoin (b 2)
  have e12 := e11.adjoin (b 1)
  have a3 := e2.adjoin (ca (canonical (pSys d 1)))
  have a4 := a3.adjoin (rw' (pSys d 0))
  have a5 := a4.adjoin (ru (pSys d 0))
  have a6 := a5.adjoin (ca (canonical (pSys d 0)))
  have a7 := a6.adjoin (b 6)
  have a8 := a7.adjoin (b 5)
  have a9 := a8.adjoin (b 4)
  have a10 := a9.adjoin (b 3)
  have a11 := a10.adjoin (b 2)
  have a12 := a11.adjoin (b 1)
  unfold descriptionsSysAt descriptionsSys
  rw [thirteen_eq, termSubstVec_cons (b 0) a12, termSubstVec_cons (b 1) a11, termSubstVec_cons (b 2) a10,
    termSubstVec_cons (b 3) a9, termSubstVec_cons (b 4) a8, termSubstVec_cons (b 5) a7, termSubstVec_cons (b 6) a6,
    termSubstVec_cons (ca _) a5, termSubstVec_cons (ru _) a4, termSubstVec_cons (rw' _) a3,
    termSubstVec_cons (ca _) e2,
    termSubstVec_cons (b 0) e12, termSubstVec_cons (b 1) e11, termSubstVec_cons (b 2) e10,
    termSubstVec_cons (b 3) e9, termSubstVec_cons (b 4) e8, termSubstVec_cons (b 5) e7, termSubstVec_cons (b 6) e6,
    termSubstVec_cons (c _) e5, termSubstVec_cons (ru _) e4, termSubstVec_cons (rw' _) e3,
    termSubstVec_cons (c _) e2,
    termSubst_descriptionsB_codeTermAbs, termSubst_descriptionsB_codeTermAbs,
    termSubst_closed _ (codeTerm_semiterm_LAct 0 (canonical (pSys d 0))),
    termSubst_closed _ (codeTerm_semiterm_LAct 0 (canonical (pSys d 1)))]

/-- **THE BRIDGE (Phase 2d)**: the sentence the evaluator consults for a closed member — its stored template
closed at the node budget, then filled by the frame — is the one the verbatim closer gives. Only the stored
numerals shrink. The system twin of `guardCodeB_templateCodeAt`; unconditional (on a code that is not a
thirteen-variable template both closers are the identity). -/
theorem guardCodeB_sysCloseTemplateAt (d k g me opp : V) :
    guardCodeB (sysCloseTemplateAt d k g) me opp k = guardCodeB (sysCloseTemplate d g) me opp k := by
  by_cases hg : IsSemiformula LAct 13 g
  · rw [sysCloseTemplateAt_of_template₁₃ hg, sysCloseTemplate_of_template₁₃ hg]
    unfold guardCodeB
    rw [substs_substs hg (descriptionsB_semitermVec me opp k) (descriptionsSysAt_semitermVec (le_refl 7) d k),
      substs_substs hg (descriptionsB_semitermVec me opp k) (descriptionsSys_semitermVec₇ d),
      termSubstVec_descriptionsB_descriptionsSysAt]
  · rw [sysCloseTemplateAt_of_not hg, sysCloseTemplate_of_not hg]

end slot

/-! ### `substTemplate`: instantiate a template with the outer descriptions -/

open scoped Classical in
/-- Fill a six-variable template with the descriptions of `me` and `opp` (`guardCode`,
`substTemplate_of_template`); fill `#0..#5` of a seven-variable template with them, keeping the budget
slot `#6` free (`guardCodeSlot`, `substTemplate_of_template₇`); every other code is fixed (`substTemplate_of_not`). -/
noncomputable def substTemplate (me opp g : V) : V :=
  if IsSemiformula LAct 6 g then guardCode g me opp
  else if IsSemiformula LAct 7 g then guardCodeSlot g me opp
  else g

lemma substTemplate_of_template {g : V} (hg : IsSemiformula LAct 6 g) (me opp : V) :
    substTemplate me opp g = guardCode g me opp := by
  unfold substTemplate; rw [if_pos hg]

/-- The middle case: a seven-variable template that is not a six-variable one (it reads `#6`). -/
lemma substTemplate_of_template₇ {g : V} (h6 : ¬IsSemiformula LAct 6 g) (h7 : IsSemiformula LAct 7 g) (me opp : V) :
    substTemplate me opp g = guardCodeSlot g me opp := by
  unfold substTemplate; rw [if_neg h6, if_pos h7]

lemma substTemplate_of_not {g : V} (hg : ¬IsSemiformula LAct 7 g) (me opp : V) : substTemplate me opp g = g := by
  unfold substTemplate; rw [if_neg (fun h ↦ hg (isSemiformula_seven_of_six h)), if_neg hg]

lemma isSemiformula_substTemplate {g : V} (hg : IsSemiformula LAct 6 g) (me opp : V) :
    IsSemiformula LAct 0 (substTemplate me opp g) := by
  rw [substTemplate_of_template hg]; exact isSemiformula_guardCode hg me opp

/-- **Outer reference**: an instantiated template is a sentence, so the guard code computed by
the evaluator in ANY later frame `(me', opp')` is the instantiation by the OUTER frame. -/
theorem guardCode_substTemplate {g : V} (hg : IsSemiformula LAct 6 g) (me opp me' opp' : V) :
    guardCode (substTemplate me opp g) me' opp' = substTemplate me opp g :=
  guardCode_of_sentence (isSemiformula_substTemplate hg me opp) me' opp'

/-- The same for the guard code with the node budget: an instantiated template is a sentence. -/
theorem guardCodeB_substTemplate {g : V} (hg : IsSemiformula LAct 6 g) (me opp me' opp' k : V) :
    guardCodeB (substTemplate me opp g) me' opp' k = substTemplate me opp g :=
  guardCodeB_of_sentence (isSemiformula_substTemplate hg me opp) me' opp' k

/-- `substTemplate` of a seven-variable template is a seven-variable formula (a sentence, or `#6` free). -/
lemma isSemiformula_substTemplate₇ {g : V} (hg : IsSemiformula LAct 7 g) (me opp : V) :
    IsSemiformula LAct 7 (substTemplate me opp g) := by
  by_cases h6 : IsSemiformula LAct 6 g
  · rw [substTemplate_of_template h6]
    exact isSemiformula_of_le (isSemiformula_guardCode h6 me opp) (by norm_num)
  · rw [substTemplate_of_template₇ h6 hg]; exact isSemiformula_guardCodeSlot hg me opp

/-- **Outer reference on seven-variable templates, at the running node's budget**: a seven-variable
guard inside a simulated program is evaluated against the OUTER players, with the budget slot filled by
the node that runs it — the seven-variable twin of `guardCode_substTemplate`. (On a six-variable template the
slot is never read and both sides are `guardCode g me opp`.) -/
theorem guardCodeB_substTemplate₇ {g : V} (hg : IsSemiformula LAct 7 g) (me opp me' opp' k : V) :
    guardCodeB (substTemplate me opp g) me' opp' k = guardCodeB g me opp k := by
  by_cases h6 : IsSemiformula LAct 6 g
  · rw [substTemplate_of_template h6, guardCodeB_of_sentence (isSemiformula_guardCode h6 me opp),
      guardCodeB_of_template h6]
  · rw [substTemplate_of_template₇ h6 hg, guardCodeB_guardCodeSlot hg]

noncomputable def substTemplateGraph : 𝚺₁.Semisentence 4 := .mkSigma
  “y me opp g. (!(isSemiformula LAct).sigma 6 g ∧ !guardCodeGraph y g me opp) ∨
    (¬!(isSemiformula LAct).pi 6 g ∧ !(isSemiformula LAct).sigma 7 g ∧ !guardCodeSlotGraph y g me opp) ∨
    (¬!(isSemiformula LAct).pi 7 g ∧ y = g)”

instance substTemplate.defined : 𝚺₁-Function₃ (substTemplate : V → V → V → V) via substTemplateGraph := .mk fun v ↦ by
  simp [substTemplateGraph, HierarchySymbol.Semiformula.val_sigma,
    (IsSemiformula.defined (L := LAct) (V := V)).proper.iff',
    (IsSemiformula.defined (L := LAct) (V := V)).df, guardCode.defined.df, guardCodeSlot.defined.df,
    numeral_eq_natCast]
  by_cases h6 : IsSemiformula LAct 6 (v 3)
  · simp [h6, isSemiformula_seven_of_six h6, substTemplate]
  · by_cases h7 : IsSemiformula LAct 7 (v 3) <;> simp [h6, h7, substTemplate]

/-! ### `revalueTemplate` commutes with substitution

For `u, w ∈ {0, 1}` (the only re-valuations τ uses), re-valuing the action constants of an
instantiated template is instantiating the re-valued template with the re-valued terms —
by the term and formula recursions, exactly as Foundation's `termSubst_termSubst` and
`substs_substs`. -/

section commute

variable {u w : V}

lemma IsSemiterm.termRelabel (hu : IsAct u) (hw : IsAct w) {n t : V} (ht : IsSemiterm LAct n t) :
    IsSemiterm LAct n (termRelabel u w t) := by
  apply IsSemiterm.induction 𝚺 ?_ ?_ ?_ ?_ t ht
  · definability
  · intro z hz; simp [hz]
  · intro x; simp
  · intro k f v hkf hv ih
    rw [termRelabel_func hkf hv.isUTerm, IsSemiterm.func]
    exact ⟨isFunc_revalueSym hu hw hkf, IsSemitermVec.iff.mpr
      ⟨len_termRelabelVec hv.isUTerm, fun i hi ↦ by rw [nth_termRelabelVec hv.isUTerm hi]; exact ih i hi⟩⟩

lemma IsSemitermVec.termRelabelVec (hu : IsAct u) (hw : IsAct w) {k n v : V}
    (hv : IsSemitermVec LAct k n v) : IsSemitermVec LAct k n (termRelabelVec u w k v) :=
  IsSemitermVec.iff.mpr ⟨len_termRelabelVec hv.isUTerm, fun i hi ↦ by
    rw [nth_termRelabelVec hv.isUTerm hi]; exact IsSemiterm.termRelabel hu hw (hv.nth hi)⟩

lemma termRelabelVec_nil : termRelabelVec u w 0 (0 : V) = 0 :=
  TermRelabel.construction.resultVec_nil LAct _

lemma termRelabelVec_cons {k t ts : V} (ht : IsUTerm LAct t) (hts : IsUTermVec LAct k ts) :
    termRelabelVec u w (k + 1) (t ∷ ts) = termRelabel u w t ∷ termRelabelVec u w k ts :=
  TermRelabel.construction.resultVec_cons LAct ![u, w] hts ht

lemma termRelabel_termBShift (hu : IsAct u) (hw : IsAct w) {t : V} (ht : IsUTerm LAct t) :
    termRelabel u w (termBShift LAct t) = termBShift LAct (termRelabel u w t) := by
  apply IsUTerm.induction 𝚺 ?_ ?_ ?_ ?_ t ht
  · definability
  · intro z; simp
  · intro x; simp
  · intro k f v hkf hv ih
    rw [termBShift_func hkf hv, termRelabel_func hkf hv.isSemitermVec.termBShiftVec.isUTerm,
      termRelabel_func hkf hv,
      termBShift_func (isFunc_revalueSym hu hw hkf) (IsUTermVec.termRelabelVec hu hw hv)]
    simp only [qqFunc_inj, true_and]
    apply nth_ext' k (len_termRelabelVec hv.isSemitermVec.termBShiftVec.isUTerm)
      (len_termBShiftVec (IsUTermVec.termRelabelVec hu hw hv))
    intro i hi
    rw [nth_termRelabelVec hv.isSemitermVec.termBShiftVec.isUTerm hi,
      nth_termBShiftVec (IsUTermVec.termRelabelVec hu hw hv) hi, nth_termBShiftVec hv hi,
      nth_termRelabelVec hv hi, ih i hi]

lemma termRelabelVec_termBShiftVec (hu : IsAct u) (hw : IsAct w) {k v : V} (hv : IsUTermVec LAct k v) :
    termRelabelVec u w k (termBShiftVec LAct k v) = termBShiftVec LAct k (termRelabelVec u w k v) := by
  apply nth_ext' k (len_termRelabelVec hv.isSemitermVec.termBShiftVec.isUTerm)
    (len_termBShiftVec (IsUTermVec.termRelabelVec hu hw hv))
  intro i hi
  rw [nth_termRelabelVec hv.isSemitermVec.termBShiftVec.isUTerm hi,
    nth_termBShiftVec (IsUTermVec.termRelabelVec hu hw hv) hi, nth_termBShiftVec hv hi,
    nth_termRelabelVec hv hi, termRelabel_termBShift hu hw (hv.nth hi)]

lemma termRelabelVec_qVec (hu : IsAct u) (hw : IsAct w) {k v : V} (hv : IsUTermVec LAct k v) :
    termRelabelVec u w (k + 1) (qVec LAct v) = qVec LAct (termRelabelVec u w k v) := by
  unfold qVec
  rw [← hv.lh, len_termRelabelVec hv,
    termRelabelVec_cons (by simp) hv.isSemitermVec.termBShiftVec.isUTerm, termRelabel_bvar,
    termRelabelVec_termBShiftVec hu hw hv]

lemma termRelabel_termSubst (hu : IsAct u) (hw : IsAct w) {n t : V} (ht : IsSemiterm LAct n t)
    {m v : V} (hv : IsSemitermVec LAct n m v) :
    termRelabel u w (termSubst LAct v t) = termSubst LAct (termRelabelVec u w n v) (termRelabel u w t) := by
  apply IsSemiterm.induction 𝚺 ?_ ?_ ?_ ?_ t ht
  · definability
  · intro z hz
    rw [termSubst_bvar, termRelabel_bvar, termSubst_bvar, nth_termRelabelVec hv.isUTerm hz]
  · intro x; simp
  · intro k f ts hf hts ih
    rw [termSubst_func hf hts.isUTerm, termRelabel_func hf (hv.termSubstVec hts).isUTerm,
      termRelabel_func hf hts.isUTerm,
      termSubst_func (isFunc_revalueSym hu hw hf) (IsUTermVec.termRelabelVec hu hw hts.isUTerm)]
    simp only [qqFunc_inj, true_and]
    apply nth_ext' k (len_termRelabelVec (hv.termSubstVec hts).isUTerm)
      (len_termSubstVec (IsUTermVec.termRelabelVec hu hw hts.isUTerm))
    intro i hi
    rw [nth_termRelabelVec (hv.termSubstVec hts).isUTerm hi, nth_termSubstVec hts.isUTerm hi,
      nth_termSubstVec (IsUTermVec.termRelabelVec hu hw hts.isUTerm) hi,
      nth_termRelabelVec hts.isUTerm hi, ih i hi]

/-- **`revalueTemplate` commutes with `subst`.** -/
theorem revalueTemplate_subst (hu : IsAct u) (hw : IsAct w) {n p : V} (hp : IsSemiformula LAct n p) :
    ∀ {m v : V}, IsSemitermVec LAct n m v →
    revalueTemplate u w (subst LAct v p) = subst LAct (termRelabelVec u w n v) (revalueTemplate u w p) := by
  apply IsSemiformula.pi1_structural_induction ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hp
  · definability
  · intro n k R ts hR hts m v hv
    rw [substs_rel hR hts.isUTerm, revalueTemplate_rel hR (hv.termSubstVec hts).isUTerm,
      revalueTemplate_rel hR hts.isUTerm,
      substs_rel hR (IsUTermVec.termRelabelVec hu hw hts.isUTerm)]
    simp only [qqRel_inj, true_and]
    apply nth_ext' k (len_termRelabelVec (hv.termSubstVec hts).isUTerm)
      (len_termSubstVec (IsUTermVec.termRelabelVec hu hw hts.isUTerm))
    intro i hi
    rw [nth_termRelabelVec (hv.termSubstVec hts).isUTerm hi, nth_termSubstVec hts.isUTerm hi,
      nth_termSubstVec (IsUTermVec.termRelabelVec hu hw hts.isUTerm) hi,
      nth_termRelabelVec hts.isUTerm hi, termRelabel_termSubst hu hw (hts.nth hi) hv]
  · intro n k R ts hR hts m v hv
    rw [substs_nrel hR hts.isUTerm, revalueTemplate_nrel hR (hv.termSubstVec hts).isUTerm,
      revalueTemplate_nrel hR hts.isUTerm,
      substs_nrel hR (IsUTermVec.termRelabelVec hu hw hts.isUTerm)]
    simp only [qqNRel_inj, true_and]
    apply nth_ext' k (len_termRelabelVec (hv.termSubstVec hts).isUTerm)
      (len_termSubstVec (IsUTermVec.termRelabelVec hu hw hts.isUTerm))
    intro i hi
    rw [nth_termRelabelVec (hv.termSubstVec hts).isUTerm hi, nth_termSubstVec hts.isUTerm hi,
      nth_termSubstVec (IsUTermVec.termRelabelVec hu hw hts.isUTerm) hi,
      nth_termRelabelVec hts.isUTerm hi, termRelabel_termSubst hu hw (hts.nth hi) hv]
  · intros; simp
  · intros; simp
  · intro n p q hp hq ihp ihq m v hv
    rw [substs_and hp.isUFormula hq.isUFormula,
      revalueTemplate_and (hp.subst hv).isUFormula (hq.subst hv).isUFormula,
      revalueTemplate_and hp.isUFormula hq.isUFormula,
      substs_and (IsUFormula.revalueTemplate hu hw hp.isUFormula)
        (IsUFormula.revalueTemplate hu hw hq.isUFormula), ihp hv, ihq hv]
  · intro n p q hp hq ihp ihq m v hv
    rw [substs_or hp.isUFormula hq.isUFormula,
      revalueTemplate_or (hp.subst hv).isUFormula (hq.subst hv).isUFormula,
      revalueTemplate_or hp.isUFormula hq.isUFormula,
      substs_or (IsUFormula.revalueTemplate hu hw hp.isUFormula)
        (IsUFormula.revalueTemplate hu hw hq.isUFormula), ihp hv, ihq hv]
  · intro n p hp ih m v hv
    rw [substs_all hp.isUFormula, revalueTemplate_all (hp.subst hv.qVec).isUFormula,
      revalueTemplate_all hp.isUFormula,
      substs_all (IsUFormula.revalueTemplate hu hw hp.isUFormula), ih hv.qVec,
      termRelabelVec_qVec hu hw hv.isUTerm]
  · intro n p hp ih m v hv
    rw [substs_ex hp.isUFormula, revalueTemplate_exs (hp.subst hv.qVec).isUFormula,
      revalueTemplate_exs hp.isUFormula,
      substs_ex (IsUFormula.revalueTemplate hu hw hp.isUFormula), ih hv.qVec,
      termRelabelVec_qVec hu hw hv.isUTerm]

/-- `revalueTemplate` preserves the number of free variables. -/
lemma IsSemiformula.revalueTemplate (hu : IsAct u) (hw : IsAct w) {n p : V} (hp : IsSemiformula LAct n p) :
    IsSemiformula LAct n (revalueTemplate u w p) := by
  apply IsSemiformula.pi1_structural_induction ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hp
  · definability
  · intro n k R v hR hv
    rw [revalueTemplate_rel hR hv.isUTerm, IsSemiformula.rel]
    exact ⟨hR, IsSemitermVec.termRelabelVec hu hw hv⟩
  · intro n k R v hR hv
    rw [revalueTemplate_nrel hR hv.isUTerm, IsSemiformula.nrel]
    exact ⟨hR, IsSemitermVec.termRelabelVec hu hw hv⟩
  · intro n; simp
  · intro n; simp
  · intro n p q hp hq ihp ihq
    rw [revalueTemplate_and hp.isUFormula hq.isUFormula]; simp [ihp, ihq]
  · intro n p q hp hq ihp ihq
    rw [revalueTemplate_or hp.isUFormula hq.isUFormula]; simp [ihp, ihq]
  · intro n p hp ih
    rw [revalueTemplate_all hp.isUFormula]; simpa using ih
  · intro n p hp ih
    rw [revalueTemplate_exs hp.isUFormula]; simpa using ih

lemma isSemiformula_revalueTemplate_swap_iff {n p : V} :
    IsSemiformula LAct n (revalueTemplate 1 0 p) ↔ IsSemiformula LAct n p :=
  ⟨fun h ↦ by simpa [revalueTemplate_swap_swap] using IsSemiformula.revalueTemplate isAct_one isAct_zero h,
   IsSemiformula.revalueTemplate isAct_one isAct_zero⟩

end commute

/-! ### The swap equation for descriptions, on codes -/

section canonical

lemma canonical_of_lt {x : V} (h : x < transposeCode x) : canonical x = x := by
  unfold canonical; rw [if_pos (le_def.mpr (Or.inr h))]

lemma canonical_of_eq {x : V} (h : x = transposeCode x) : canonical x = x := by
  unfold canonical; rw [if_pos (le_def.mpr (Or.inl h))]

lemma canonical_of_gt {x : V} (h : transposeCode x < x) : canonical x = transposeCode x := by
  unfold canonical
  rw [if_neg]
  intro h'
  rcases le_def.mp h' with e | l
  · rw [← e] at h; exact _root_.lt_irrefl _ h
  · exact lt_asymm h l

lemma canonical_transposeCode (x : V) : canonical (transposeCode x) = canonical x := by
  rcases lt_trichotomy x (transposeCode x) with h | h | h
  · rw [canonical_of_lt h, canonical_of_gt (by rw [transposeCode_transposeCode]; exact h), transposeCode_transposeCode]
  · rw [← h]
  · rw [canonical_of_gt h, canonical_of_lt (by rw [transposeCode_transposeCode]; exact h)]

end canonical

/-- `termRelabel` fixes every `ℒₒᵣ` term (its symbols `0, 1, +, *` carry no action). -/
lemma termRelabel_of_LOR {u w t : V} (ht : IsUTerm ℒₒᵣ t) : termRelabel u w t = t := by
  apply IsUTerm.induction 𝚺 ?_ ?_ ?_ ?_ t ht
  · definability
  · intro z; simp
  · intro x; simp
  · intro k f v hkf hv ih
    have hv' : IsUTermVec LAct k v := ⟨hv.lh, fun i hi ↦ IsUTerm.LAct_of_LOR (hv.nth hi)⟩
    rw [termRelabel_func (isFunc_LAct_of_LOR hkf) hv']
    have hf : revalueSym f u w = f := by
      unfold revalueSym
      rcases isFunc_LOR.mp hkf with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;>
        rw [if_neg (by norm_num), if_neg (by norm_num)]
    rw [hf]
    simp only [qqFunc_inj, true_and]
    apply nth_ext' k (len_termRelabelVec hv') hv'.lh.symm
    intro i hi
    rw [nth_termRelabelVec hv' hi, ih i hi]

lemma termRelabel_binNumeral (u w n : V) : termRelabel u w (binNumeral n) = binNumeral n :=
  termRelabel_of_LOR (binNumeral_uterm n)

lemma termRelabel_codeTerm (u w x : V) : termRelabel u w (codeTerm x) = codeTerm x :=
  termRelabel_of_LOR (codeTerm_uterm x)

lemma termRelabel_numeral (u w n : V) : termRelabel u w (numeral n) = numeral n :=
  termRelabel_of_LOR (numeral_uterm n)

lemma termRelabel_csym {u w a : V} (ha : IsAct a) :
    termRelabel u w (csym a) = csym (revalueAction a u w) := by
  unfold csym
  rw [termRelabel_func (isFunc_csym ha) (by simp), termRelabelVec_nil]
  rcases ha with rfl | rfl
  · rw [show (2 : V) + 0 = 2 by norm_num, revalueSym_two]; simp [revalueAction]
  · rw [show (2 : V) + 1 = 3 by norm_num, revalueSym_three]; simp [revalueAction]

lemma termRelabel_revalueU (x : V) : termRelabel 1 0 (revalueU x) = revalueU (transposeCode x) := by
  unfold revalueU
  rw [transposeCode_transposeCode]
  generalize transposeCode x = s
  rcases lt_trichotomy x s with h | h | h
  · rw [if_pos h, if_neg (lt_asymm h), if_pos h, termRelabel_csym isAct_zero]; simp [revalueAction]
  · subst h
    rw [if_neg (_root_.lt_irrefl _), if_neg (_root_.lt_irrefl _), termRelabel_numeral]
  · rw [if_neg (lt_asymm h), if_pos h, if_pos h, termRelabel_csym isAct_one]; simp [revalueAction]

lemma termRelabel_revalueW (x : V) : termRelabel 1 0 (revalueW x) = revalueW (transposeCode x) := by
  unfold revalueW
  rw [transposeCode_transposeCode]
  generalize transposeCode x = s
  rcases lt_trichotomy x s with h | h | h
  · rw [if_pos h, if_neg (lt_asymm h), if_pos h, termRelabel_csym isAct_one]; simp [revalueAction]
  · subst h
    rw [if_neg (_root_.lt_irrefl _), if_neg (_root_.lt_irrefl _), termRelabel_numeral]
  · rw [if_neg (lt_asymm h), if_pos h, if_pos h, termRelabel_csym isAct_zero]; simp [revalueAction]

/-- **The swap equation for descriptions**: the code-level τ maps the description vector of
`(me, opp)` entrywise to that of `(transposeCode me, transposeCode opp)`. -/
theorem termRelabelVec_descriptions (me opp : V) :
    termRelabelVec 1 0 6 (descriptions me opp) = descriptions (transposeCode me) (transposeCode opp) := by
  have e0 : IsUTermVec LAct 0 (0 : V) := IsUTermVec.empty
  have h1 : IsUTermVec LAct (0 + 1) (revalueW opp ∷ (0 : V)) := e0.adjoin (revalueW_semiterm 0 opp).isUTerm
  have h2 : IsUTermVec LAct (0 + 1 + 1) (revalueU opp ∷ revalueW opp ∷ (0 : V)) := h1.adjoin (revalueU_semiterm 0 opp).isUTerm
  have h3 : IsUTermVec LAct (0 + 1 + 1 + 1) (codeTerm (canonical opp) ∷ revalueU opp ∷ revalueW opp ∷ (0 : V)) :=
    h2.adjoin (codeTerm_semiterm_LAct 0 (canonical opp)).isUTerm
  have h4 : IsUTermVec LAct (0 + 1 + 1 + 1 + 1) (revalueW me ∷ codeTerm (canonical opp) ∷ revalueU opp ∷ revalueW opp ∷ (0 : V)) :=
    h3.adjoin (revalueW_semiterm 0 me).isUTerm
  have h5 : IsUTermVec LAct (0 + 1 + 1 + 1 + 1 + 1) (revalueU me ∷ revalueW me ∷ codeTerm (canonical opp) ∷ revalueU opp ∷ revalueW opp ∷ (0 : V)) :=
    h4.adjoin (revalueU_semiterm 0 me).isUTerm
  unfold descriptions
  rw [six_eq, termRelabelVec_cons (codeTerm_semiterm_LAct 0 (canonical me)).isUTerm h5,
    termRelabelVec_cons (revalueU_semiterm 0 me).isUTerm h4, termRelabelVec_cons (revalueW_semiterm 0 me).isUTerm h3,
    termRelabelVec_cons (codeTerm_semiterm_LAct 0 (canonical opp)).isUTerm h2,
    termRelabelVec_cons (revalueU_semiterm 0 opp).isUTerm h1,
    termRelabelVec_cons (revalueW_semiterm 0 opp).isUTerm e0, termRelabelVec_nil,
    termRelabel_codeTerm, termRelabel_codeTerm, termRelabel_revalueU, termRelabel_revalueU, termRelabel_revalueW, termRelabel_revalueW,
    canonical_transposeCode, canonical_transposeCode]

/-- The code-level τ maps the kept-slot vector entrywise (the swap fixes the variable `#6`). -/
theorem termRelabelVec_descriptionsSlot (me opp : V) :
    termRelabelVec 1 0 7 (descriptionsSlot me opp) = descriptionsSlot (transposeCode me) (transposeCode opp) := by
  have h6 : IsUTerm LAct (^#6 : V) := bvar_six_semiterm.isUTerm
  have e0 : IsUTermVec LAct 0 (0 : V) := IsUTermVec.empty
  have h0 : IsUTermVec LAct (0 + 1) (^#6 ∷ (0 : V)) := e0.adjoin h6
  have h1 : IsUTermVec LAct (0 + 1 + 1) (revalueW opp ∷ ^#6 ∷ (0 : V)) := h0.adjoin (revalueW_semiterm 0 opp).isUTerm
  have h2 : IsUTermVec LAct (0 + 1 + 1 + 1) (revalueU opp ∷ revalueW opp ∷ ^#6 ∷ (0 : V)) :=
    h1.adjoin (revalueU_semiterm 0 opp).isUTerm
  have h3 : IsUTermVec LAct (0 + 1 + 1 + 1 + 1) (codeTerm (canonical opp) ∷ revalueU opp ∷ revalueW opp ∷ ^#6 ∷ (0 : V)) :=
    h2.adjoin (codeTerm_semiterm_LAct 0 (canonical opp)).isUTerm
  have h4 : IsUTermVec LAct (0 + 1 + 1 + 1 + 1 + 1)
      (revalueW me ∷ codeTerm (canonical opp) ∷ revalueU opp ∷ revalueW opp ∷ ^#6 ∷ (0 : V)) :=
    h3.adjoin (revalueW_semiterm 0 me).isUTerm
  have h5 : IsUTermVec LAct (0 + 1 + 1 + 1 + 1 + 1 + 1)
      (revalueU me ∷ revalueW me ∷ codeTerm (canonical opp) ∷ revalueU opp ∷ revalueW opp ∷ ^#6 ∷ (0 : V)) :=
    h4.adjoin (revalueU_semiterm 0 me).isUTerm
  unfold descriptionsSlot
  rw [seven_eq, termRelabelVec_cons (codeTerm_semiterm_LAct 0 (canonical me)).isUTerm h5,
    termRelabelVec_cons (revalueU_semiterm 0 me).isUTerm h4, termRelabelVec_cons (revalueW_semiterm 0 me).isUTerm h3,
    termRelabelVec_cons (codeTerm_semiterm_LAct 0 (canonical opp)).isUTerm h2,
    termRelabelVec_cons (revalueU_semiterm 0 opp).isUTerm h1,
    termRelabelVec_cons (revalueW_semiterm 0 opp).isUTerm h0,
    termRelabelVec_cons h6 e0, termRelabelVec_nil,
    termRelabel_codeTerm, termRelabel_codeTerm, termRelabel_revalueU, termRelabel_revalueU, termRelabel_revalueW, termRelabel_revalueW,
    termRelabel_bvar, canonical_transposeCode, canonical_transposeCode]

/-- **The swap equation for `substTemplate`**, on every code. -/
theorem revalueTemplate_substTemplate (me opp g : V) :
    revalueTemplate 1 0 (substTemplate me opp g) = substTemplate (transposeCode me) (transposeCode opp) (revalueTemplate 1 0 g) := by
  by_cases hg : IsSemiformula LAct 6 g
  · rw [substTemplate_of_template hg, substTemplate_of_template (isSemiformula_revalueTemplate_swap_iff.mpr hg)]
    unfold guardCode
    rw [revalueTemplate_subst isAct_one isAct_zero hg (descriptions_semitermVec me opp), termRelabelVec_descriptions]
  · by_cases h7 : IsSemiformula LAct 7 g
    · rw [substTemplate_of_template₇ hg h7,
        substTemplate_of_template₇ (fun h ↦ hg (isSemiformula_revalueTemplate_swap_iff.mp h))
          (isSemiformula_revalueTemplate_swap_iff.mpr h7)]
      unfold guardCodeSlot
      rw [revalueTemplate_subst isAct_one isAct_zero h7 (descriptionsSlot_semitermVec me opp),
        termRelabelVec_descriptionsSlot]
    · rw [substTemplate_of_not h7, substTemplate_of_not (fun h ↦ h7 (isSemiformula_revalueTemplate_swap_iff.mp h))]

/-! ### The order of `ppair` in its second argument, and the `pBot` algebra

Moved upstream on 2026-10-01 (from `Agents/Instance.lean` and `Cells/Common/Syntax.lean`, same names, same
proofs): the pronoun reading of `.selfIdx` (`Agents/Code.lean`, `Agents/SysTemplate.lean`) needs
`canonical_pBot`/`revalueU_pBot`/`revalueW_pBot` in the core tier. -/

section ppairOrder

lemma ppair_lt_ppair_right_iff (x : V) {y₁ y₂ : V} : ppair x y₁ < ppair x y₂ ↔ y₁ < y₂ := by
  constructor
  · intro h
    rcases lt_trichotomy y₁ y₂ with h' | rfl | h'
    · exact h'
    · exact absurd h (_root_.lt_irrefl _)
    · exact absurd (lt_trans h (ppair_lt_ppair_right x h')) (_root_.lt_irrefl _)
  · exact ppair_lt_ppair_right x

lemma ppair_le_ppair_right_iff (x : V) {y₁ y₂ : V} : ppair x y₁ ≤ ppair x y₂ ↔ y₁ ≤ y₂ := by
  rw [← not_lt, ← not_lt, ppair_lt_ppair_right_iff]

lemma pBot_le_pBot_iff {p q : V} : pBot p ≤ pBot q ↔ p ≤ q := by
  unfold pBot
  rw [add_le_add_iff_right, ppair_le_ppair_right_iff]

lemma pBot_lt_pBot_iff {p q : V} : pBot p < pBot q ↔ p < q := by
  rw [← not_le, ← not_le, pBot_le_pBot_iff]

lemma transposeCode_pBot (p : V) : transposeCode (pBot p) = pBot (transposeCode p) := by
  unfold transposeCode; simp

/-- The canonical numeral commutes with bot-wrapping (`pBot` is strictly monotone). -/
lemma canonical_pBot (p : V) : canonical (pBot p) = pBot (canonical p) := by
  unfold canonical
  rw [transposeCode_pBot]
  simp only [pBot_le_pBot_iff, apply_ite pBot]

lemma revalueU_pBot (p : V) : revalueU (pBot p) = revalueU p := by
  unfold revalueU
  rw [transposeCode_pBot]
  simp only [pBot_lt_pBot_iff]

lemma revalueW_pBot (p : V) : revalueW (pBot p) = revalueW p := by
  unfold revalueW
  rw [transposeCode_pBot]
  simp only [pBot_lt_pBot_iff]

end ppairOrder

/-! ### The seven-variable identity vector, and `guardCodeSlot` on a six-variable template (2026-10-01)

Route (c) made generic (`Agents/Code.lean`): the stored template of a search node may use the budget slot `#6`,
so `substCode` instantiates it through `substTemplate`'s middle case `guardCodeSlot`. On a six-variable
template `guardCodeSlot` is `guardCode` (the slot is never read), so `substTemplate` is `guardCodeSlot` on
EVERY seven-variable template (`substTemplate_eq_guardCodeSlot`) — the one case split the code equation
`templateCodeAt_subst` needs. `idVec7` serves `quote_castLE₇` (codes do not see the arity, seven to thirteen). -/

noncomputable def idVec7 : V := ^#0 ∷ ^#1 ∷ ^#2 ∷ ^#3 ∷ ^#4 ∷ ^#5 ∷ ^#6 ∷ 0

lemma idVec7_semitermVec {n : V} (hn : 7 ≤ n) : IsSemitermVec LAct 7 n (idVec7 : V) := by
  have h0 : IsSemiterm LAct n (^#0 : V) := IsSemiterm.bvar.mpr (lt_of_lt_of_le (by norm_num) hn)
  have h1 : IsSemiterm LAct n (^#1 : V) := IsSemiterm.bvar.mpr (lt_of_lt_of_le (by norm_num) hn)
  have h2 : IsSemiterm LAct n (^#2 : V) := IsSemiterm.bvar.mpr (lt_of_lt_of_le (by norm_num) hn)
  have h3 : IsSemiterm LAct n (^#3 : V) := IsSemiterm.bvar.mpr (lt_of_lt_of_le (by norm_num) hn)
  have h4 : IsSemiterm LAct n (^#4 : V) := IsSemiterm.bvar.mpr (lt_of_lt_of_le (by norm_num) hn)
  have h5 : IsSemiterm LAct n (^#5 : V) := IsSemiterm.bvar.mpr (lt_of_lt_of_le (by norm_num) hn)
  have h6 : IsSemiterm LAct n (^#6 : V) := IsSemiterm.bvar.mpr (lt_of_lt_of_le (by norm_num) hn)
  have := (((((((IsSemitermVec.nil n).adjoin h6).adjoin h5).adjoin h4).adjoin h3).adjoin h2).adjoin h1).adjoin h0
  rwa [← seven_eq] at this

lemma nth_idVec7 : ∀ i < (7 : V), (idVec7 : V).[i] = ^#i := by
  intro i hi
  unfold idVec7
  rcases zero_or_succ i with rfl | ⟨i, rfl⟩
  · simp
  rw [nth_adjoin_succ]
  rcases zero_or_succ i with rfl | ⟨i, rfl⟩
  · simp
  rw [nth_adjoin_succ]
  rcases zero_or_succ i with rfl | ⟨i, rfl⟩
  · simp; norm_num
  rw [nth_adjoin_succ]
  rcases zero_or_succ i with rfl | ⟨i, rfl⟩
  · simp; norm_num
  rw [nth_adjoin_succ]
  rcases zero_or_succ i with rfl | ⟨i, rfl⟩
  · simp; norm_num
  rw [nth_adjoin_succ]
  rcases zero_or_succ i with rfl | ⟨i, rfl⟩
  · simp; norm_num
  rw [nth_adjoin_succ]
  rcases zero_or_succ i with rfl | ⟨i, rfl⟩
  · simp; norm_num
  exfalso
  have e7 : i + 1 + 1 + 1 + 1 + 1 + 1 + 1 = i + 7 := by ring
  rw [e7] at hi
  exact absurd hi (not_lt.mpr le_add_self)

/-- The kept-slot vector restricted to the six frame variables is the description vector. -/
lemma termSubstVec_descriptionsSlot_idVec6 (me opp : V) :
    termSubstVec LAct 6 (descriptionsSlot me opp) (idVec6 : V) = descriptions me opp := by
  have h0 : IsUTerm LAct (^#0 : V) := (IsSemiterm.bvar.mpr (by norm_num : (0 : V) < 6)).isUTerm
  have h1 : IsUTerm LAct (^#1 : V) := (IsSemiterm.bvar.mpr (by norm_num : (1 : V) < 6)).isUTerm
  have h2 : IsUTerm LAct (^#2 : V) := (IsSemiterm.bvar.mpr (by norm_num : (2 : V) < 6)).isUTerm
  have h3 : IsUTerm LAct (^#3 : V) := (IsSemiterm.bvar.mpr (by norm_num : (3 : V) < 6)).isUTerm
  have h4 : IsUTerm LAct (^#4 : V) := (IsSemiterm.bvar.mpr (by norm_num : (4 : V) < 6)).isUTerm
  have h5 : IsUTerm LAct (^#5 : V) := (IsSemiterm.bvar.mpr (by norm_num : (5 : V) < 6)).isUTerm
  have e0 : IsUTermVec LAct 0 (0 : V) := IsUTermVec.empty
  have e1 := e0.adjoin h5
  have e2 := e1.adjoin h4
  have e3 := e2.adjoin h3
  have e4 := e3.adjoin h2
  have e5 := e4.adjoin h1
  unfold idVec6 descriptionsSlot descriptions
  rw [six_eq, termSubstVec_cons h0 e5, termSubstVec_cons h1 e4, termSubstVec_cons h2 e3,
    termSubstVec_cons h3 e2, termSubstVec_cons h4 e1, termSubstVec_cons h5 e0, termSubstVec_nil,
    termSubst_bvar, termSubst_bvar, termSubst_bvar, termSubst_bvar, termSubst_bvar, termSubst_bvar]
  simp only [nth_adjoin_zero, nth_adjoin_one, nth_adjoin_two]
  rw [show (3 : V) = 2 + 1 by norm_num, nth_adjoin_succ, nth_adjoin_two,
    show (4 : V) = 2 + 1 + 1 by norm_num, nth_adjoin_succ, nth_adjoin_succ, nth_adjoin_two,
    show (5 : V) = 2 + 1 + 1 + 1 by norm_num, nth_adjoin_succ, nth_adjoin_succ, nth_adjoin_succ, nth_adjoin_two]
  simp only [nth_adjoin_zero, nth_adjoin_one]

/-- A six-variable template never reads the kept slot: `guardCodeSlot` is `guardCode` on it. -/
theorem guardCodeSlot_of_template {g : V} (hg : IsSemiformula LAct 6 g) (me opp : V) :
    guardCodeSlot g me opp = guardCode g me opp := by
  have hid6 : IsSemitermVec LAct 6 6 (idVec6 : V) := idVec6_semitermVec (le_refl _)
  have hid7 : IsSemitermVec LAct 6 7 (idVec6 : V) := idVec6_semitermVec (by norm_num)
  have e : subst LAct (idVec6 : V) g = g := subst_eq_self hg hid6 nth_idVec6
  unfold guardCodeSlot guardCode
  calc subst LAct (descriptionsSlot me opp) g
      = subst LAct (descriptionsSlot me opp) (subst LAct (idVec6 : V) g) := by rw [e]
    _ = subst LAct (termSubstVec LAct 6 (descriptionsSlot me opp) (idVec6 : V)) g :=
        substs_substs hg (descriptionsSlot_semitermVec me opp) hid7
    _ = subst LAct (descriptions me opp) g := by rw [termSubstVec_descriptionsSlot_idVec6]

/-- On every seven-variable template `substTemplate` is `guardCodeSlot`. -/
theorem substTemplate_eq_guardCodeSlot {g : V} (hg : IsSemiformula LAct 7 g) (me opp : V) :
    substTemplate me opp g = guardCodeSlot g me opp := by
  by_cases h6 : IsSemiformula LAct 6 g
  · rw [substTemplate_of_template h6, guardCodeSlot_of_template h6]
  · exact substTemplate_of_template₇ h6 hg me opp

end ArithS
