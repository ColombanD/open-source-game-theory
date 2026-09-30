import ArithS.Agents.Guard

/-!
# ArithS.Subst — program substitution on codes (`substCode`), the engine's `Prog.subst`

Roadmap M3 step (b). The engine's `.sim p q` runs `p.subst me opp` against `q.subst me opp`:
`subst` is ONE-SHOT (`.self ↦ me`, `.opp ↦ opp`), `.bot` is a barrier (frozen), and it
descends into the guard of a `.search` node — so a guard inside a simulated program refers
to the OUTER players. On codes:

* `substTemplate me opp g` instantiates a six-variable template with the canonical descriptions of
  `me` and `opp` — it IS `guardCode g me opp` on every template (`IsSemiformula LAct 6 g`,
  `substTemplate_of_template`). The result is a SENTENCE
  (no free variables), so a later `guardCode … me' opp'` is the identity on it
  (`guardCode_substTemplate`): a search node inside a simulated program evaluates its guard
  against the outer players whatever the current frame is — the engine's semantics.
  On a SEVEN-variable template (route (c), the budget slot `#6`; `ArithS.Guard`) it fills
  `#0..#5` with the outer descriptions and KEEPS `#6` a variable (`guardCodeSlot`,
  `substTemplate_of_template₇`), so the node that eventually runs the guard fills the slot with ITS
  budget: `guardCodeB (substTemplate me opp g) me' opp' k = guardCodeB g me opp k`
  (`guardCodeB_substTemplate₇`, the seven-variable twin of `guardCode_substTemplate`) — the `.sim` debt of
  route (c) (`ROUTE_B_SCOPE.md` §6), discharged 2026-09-24. Every other code is fixed
  (`substTemplate_of_not`, hypothesis `¬IsSemiformula LAct 7 g`).
  (The identity on non-templates is what makes the τ-equivariance below hold on EVERY code:
  `subst` truncates out-of-range variables to `0` and `revalueTemplate` fixes the
  resulting non-formula, so on a code with more than seven free variables the two do not
  commute — `^rel 2 R ?[c_C, #8]` is a counterexample.)
* `substCode me opp p`: the Δ₁ fixpoint on pairs `⟪x, y⟫` with parameters `me opp`, exactly
  like `Revalue` (`ArithS.Prog`): `pConst a ↦ pConst a`, `pSelf ↦ me`, `pOpp ↦ opp`,
  `pBot p ↦ pBot p` (frozen), `pSim`/`pIte` structurally, `pSearch k g p q ↦
  pSearch k (substTemplate me opp g) (substCode p) (substCode q)`, non-shapes fixed. A Σ₁ function
  (`substCodeDef`), with the equations `substCode_const/self/opp/bot/sim/ite/search`.
* τ-equivariance: `transposeCode_substCode : transposeCode (substCode me opp p) = substCode (transposeCode me)
  (transposeCode opp) (transposeCode p)`, from the code-level swap equation for descriptions
  (`termRelabelVec_descriptions`: `termRelabel 1 0` maps `descriptions me opp` entrywise to
  `descriptions (transposeCode me) (transposeCode opp)`) and the commutation of `revalueTemplate` with
  `subst` (`revalueTemplate_subst`, by the formula recursion, as `substs_substs`).
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

/-! ### The budget slot KEPT: `guardCodeSlot` (the `.sim` debt of route c, discharged 2026-09-24)

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

/-! ### `substCode`: a fixpoint on pairs `⟪x, y⟫` with parameters `me opp`

The search clause instantiates the stored template through `substTemplate` (a Σ₁ function), so the
core is Δ₁ (both polarities cite `substTemplateGraph`, exactly like `Revalue` cites
`revalueTemplateGraph`); the fixpoint is StrongFinite, since the sub-results referenced are
`⟪p, p'⟫` with `p < x` and `p' < y`. -/

namespace SubstCode

/-- `Phi ![me, opp] C ⟪x, y⟫`: `y` is `x` with `pSelf ↦ me`, `pOpp ↦ opp`, `pBot` frozen and every
stored template instantiated, given the sub-results in `C`. -/
def Phi (param : Fin 2 → V) (C : Set V) (pr : V) : Prop :=
  (∃ a, pr = ⟪pConst a, pConst a⟫) ∨
  pr = ⟪pSelf, param 0⟫ ∨ pr = ⟪pOpp, param 1⟫ ∨
  (∃ p, pr = ⟪pBot p, pBot p⟫) ∨
  (∃ p q p' q', ⟪p, p'⟫ ∈ C ∧ ⟪q, q'⟫ ∈ C ∧ pr = ⟪pSim p q, pSim p' q'⟫) ∨
  (∃ b a p q b' p' q', ⟪b, b'⟫ ∈ C ∧ ⟪p, p'⟫ ∈ C ∧ ⟪q, q'⟫ ∈ C ∧
    pr = ⟪pIte b a p q, pIte b' a p' q'⟫) ∨
  (∃ k g p q p' q', ⟪p, p'⟫ ∈ C ∧ ⟪q, q'⟫ ∈ C ∧
    pr = ⟪pSearch k g p q, pSearch k (substTemplate (param 0) (param 1) g) p' q'⟫) ∨
  (∃ x, ¬IsShape x ∧ pr = ⟪x, x⟫)

noncomputable def blueprint : Fixpoint.Blueprint 2 := ⟨.mkDelta
  (.mkSigma “pr C me opp. ∃ x <⁺ pr, ∃ y <⁺ pr, !pairDef pr x y ∧
    ( (∃ a < x, !pConstGraph x a ∧ y = x) ∨
      (!pSelfGraph x ∧ y = me) ∨
      (!pOppGraph x ∧ y = opp) ∨
      (∃ p < x, !pBotGraph x p ∧ y = x) ∨
      (∃ p < x, ∃ q < x, !pSimGraph x p q ∧
        ∃ p' < y, ∃ q' < y, :⟪p, p'⟫:∈ C ∧ :⟪q, q'⟫:∈ C ∧ !pSimGraph y p' q') ∨
      (∃ b < x, ∃ a < x, ∃ p < x, ∃ q < x, !pIteGraph x b a p q ∧
        ∃ b' < y, ∃ p' < y, ∃ q' < y,
          :⟪b, b'⟫:∈ C ∧ :⟪p, p'⟫:∈ C ∧ :⟪q, q'⟫:∈ C ∧ !pIteGraph y b' a p' q') ∨
      (∃ k < x, ∃ g < x, ∃ p < x, ∃ q < x, !pSearchGraph x k g p q ∧
        ∃ g', !substTemplateGraph g' me opp g ∧ ∃ p' < y, ∃ q' < y,
          :⟪p, p'⟫:∈ C ∧ :⟪q, q'⟫:∈ C ∧ !pSearchGraph y k g' p' q') ∨
      (¬!isShape x ∧ y = x) )”)
  (.mkPi “pr C me opp. ∃ x <⁺ pr, ∃ y <⁺ pr, !pairDef pr x y ∧
    ( (∃ a < x, !pConstGraph x a ∧ y = x) ∨
      (!pSelfGraph x ∧ y = me) ∨
      (!pOppGraph x ∧ y = opp) ∨
      (∃ p < x, !pBotGraph x p ∧ y = x) ∨
      (∃ p < x, ∃ q < x, !pSimGraph x p q ∧
        ∃ p' < y, ∃ q' < y, :⟪p, p'⟫:∈ C ∧ :⟪q, q'⟫:∈ C ∧ !pSimGraph y p' q') ∨
      (∃ b < x, ∃ a < x, ∃ p < x, ∃ q < x, !pIteGraph x b a p q ∧
        ∃ b' < y, ∃ p' < y, ∃ q' < y,
          :⟪b, b'⟫:∈ C ∧ :⟪p, p'⟫:∈ C ∧ :⟪q, q'⟫:∈ C ∧ !pIteGraph y b' a p' q') ∨
      (∃ k < x, ∃ g < x, ∃ p < x, ∃ q < x, !pSearchGraph x k g p q ∧
        ∀ g', !substTemplateGraph g' me opp g → ∃ p' < y, ∃ q' < y,
          :⟪p, p'⟫:∈ C ∧ :⟪q, q'⟫:∈ C ∧ !pSearchGraph y k g' p' q') ∨
      (¬!isShape x ∧ y = x) )”)⟩

private lemma phi_iff (param : Fin 2 → V) (C pr : V) :
    Phi param {x | x ∈ C} pr ↔
    ∃ x ≤ pr, ∃ y ≤ pr, pr = ⟪x, y⟫ ∧
    ( (∃ a < x, x = pConst a ∧ y = x) ∨
      (x = pSelf ∧ y = param 0) ∨
      (x = pOpp ∧ y = param 1) ∨
      (∃ p < x, x = pBot p ∧ y = x) ∨
      (∃ p < x, ∃ q < x, x = pSim p q ∧
        ∃ p' < y, ∃ q' < y, ⟪p, p'⟫ ∈ C ∧ ⟪q, q'⟫ ∈ C ∧ y = pSim p' q') ∨
      (∃ b < x, ∃ a < x, ∃ p < x, ∃ q < x, x = pIte b a p q ∧
        ∃ b' < y, ∃ p' < y, ∃ q' < y,
          ⟪b, b'⟫ ∈ C ∧ ⟪p, p'⟫ ∈ C ∧ ⟪q, q'⟫ ∈ C ∧ y = pIte b' a p' q') ∨
      (∃ k < x, ∃ g < x, ∃ p < x, ∃ q < x, x = pSearch k g p q ∧
        ∃ p' < y, ∃ q' < y,
          ⟪p, p'⟫ ∈ C ∧ ⟪q, q'⟫ ∈ C ∧ y = pSearch k (substTemplate (param 0) (param 1) g) p' q') ∨
      (¬IsShape x ∧ y = x) ) := by
  constructor
  · rintro (⟨a, rfl⟩ | rfl | rfl | ⟨p, rfl⟩ | ⟨p, q, p', q', hp, hq, rfl⟩ |
      ⟨b, a, p, q, b', p', q', hb, hp, hq, rfl⟩ | ⟨k, g, p, q, p', q', hp, hq, rfl⟩ | ⟨x, hx, rfl⟩)
    · exact ⟨_, by simp, _, by simp, rfl, Or.inl ⟨a, by simp, rfl, rfl⟩⟩
    · exact ⟨_, by simp, _, by simp, rfl, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
    · exact ⟨_, by simp, _, by simp, rfl, Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩
    · exact ⟨_, by simp, _, by simp, rfl, Or.inr (Or.inr (Or.inr (Or.inl ⟨p, by simp, rfl, rfl⟩)))⟩
    · exact ⟨_, by simp, _, by simp, rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨p, by simp, q, by simp, rfl, p', by simp, q', by simp, hp, hq, rfl⟩))))⟩
    · exact ⟨_, by simp, _, by simp, rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨b, by simp, a, by simp, p, by simp, q, by simp, rfl, b', by simp,
          p', by simp, q', by simp, hb, hp, hq, rfl⟩)))))⟩
    · exact ⟨_, by simp, _, by simp, rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨k, by simp, g, by simp, p, by simp, q, by simp, rfl,
          p', by simp, q', by simp, hp, hq, rfl⟩))))))⟩
    · exact ⟨_, by simp, _, by simp, rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨hx, rfl⟩))))))⟩
  · rintro ⟨x, _, y, _, rfl, (⟨a, _, rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨p, _, rfl, rfl⟩ | ⟨p, _, q, _, rfl, p', _, q', _, hp, hq, rfl⟩ |
      ⟨b, _, a, _, p, _, q, _, rfl, b', _, p', _, q', _, hb, hp, hq, rfl⟩ |
      ⟨k, _, g, _, p, _, q, _, rfl, p', _, q', _, hp, hq, rfl⟩ | ⟨hx, hyx⟩)⟩
    · exact Or.inl ⟨a, rfl⟩
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨p, rfl⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, q, p', q', hp, hq, rfl⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨b, a, p, q, b', p', q', hb, hp, hq, rfl⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨k, g, p, q, p', q', hp, hq, rfl⟩))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨x, hx, by rw [hyx]⟩))))))

noncomputable def construction : Fixpoint.Construction V blueprint where
  Φ := Phi
  defined := .mk <| by
    constructor
    · intro v
      simp [blueprint, HierarchySymbol.Semiformula.val_sigma, substTemplate.defined.df]
    · intro v
      symm
      simpa [blueprint, HierarchySymbol.Semiformula.val_sigma, substTemplate.defined.df,
        pSelfGraph, pOppGraph, pSelf, pOpp, lt_and_eq_succ_iff]
        using phi_iff (fun i ↦ v i.succ.succ) (v 1) (v 0)
  monotone := by
    rintro C C' hC param pr (⟨a, rfl⟩ | rfl | rfl | ⟨p, rfl⟩ | ⟨p, q, p', q', hp, hq, rfl⟩ |
      ⟨b, a, p, q, b', p', q', hb, hp, hq, rfl⟩ | ⟨k, g, p, q, p', q', hp, hq, rfl⟩ | ⟨x, hx, rfl⟩)
    · exact Or.inl ⟨a, rfl⟩
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨p, rfl⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, q, p', q', hC hp, hC hq, rfl⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨b, a, p, q, b', p', q', hC hb, hC hp, hC hq, rfl⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨k, g, p, q, p', q', hC hp, hC hq, rfl⟩))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨x, hx, rfl⟩))))))

instance : construction.StrongFinite V where
  strong_finite := by
    rintro C param pr (⟨a, rfl⟩ | rfl | rfl | ⟨p, rfl⟩ | ⟨p, q, p', q', hp, hq, rfl⟩ |
      ⟨b, a, p, q, b', p', q', hb, hp, hq, rfl⟩ | ⟨k, g, p, q, p', q', hp, hq, rfl⟩ | ⟨x, hx, rfl⟩)
    · exact Or.inl ⟨a, rfl⟩
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨p, rfl⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, q, p', q',
        ⟨hp, pair_lt_pair (by simp) (by simp)⟩, ⟨hq, pair_lt_pair (by simp) (by simp)⟩, rfl⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨b, a, p, q, b', p', q',
        ⟨hb, pair_lt_pair (by simp) (by simp)⟩, ⟨hp, pair_lt_pair (by simp) (by simp)⟩,
        ⟨hq, pair_lt_pair (by simp) (by simp)⟩, rfl⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨k, g, p, q, p', q',
        ⟨hp, pair_lt_pair (by simp) (by simp)⟩, ⟨hq, pair_lt_pair (by simp) (by simp)⟩, rfl⟩))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨x, hx, rfl⟩))))))

end SubstCode

/-- `SubstCodeGraph me opp x y`: `y` is `x` with the frame `(me, opp)` substituted in. -/
def SubstCodeGraph (me opp x y : V) : Prop := SubstCode.construction.Fixpoint ![me, opp] ⟪x, y⟫

noncomputable def substCodeGraphDef : 𝚫₁.Semisentence 4 := .mkDelta
  (.mkSigma “me opp x y. ∃ pr <⁺ (x + y + 1)², !pairDef pr x y ∧ !SubstCode.blueprint.fixpointDefΔ₁.sigma pr me opp”)
  (.mkPi “me opp x y. ∀ pr <⁺ (x + y + 1)², !pairDef pr x y → !SubstCode.blueprint.fixpointDefΔ₁.pi pr me opp”)

private lemma substCode_param_eq (v : Fin 3 → V) : (fun i ↦ v i.succ) = ![v 1, v 2] := by
  funext i; fin_cases i <;> rfl

instance substCodeGraph_defined : 𝚫₁-Relation₄[V] SubstCodeGraph via substCodeGraphDef := .mk
  ⟨by intro v
      simp [substCodeGraphDef, HierarchySymbol.Semiformula.val_sigma,
        SubstCode.construction.fixpoint_definedΔ₁.proper.iff', SubstCode.construction.fixpoint_definedΔ₁.df]
      constructor
      · rintro h x _ rfl; simpa [substCode_param_eq] using h
      · intro h; have := h ⟪v 2, v 3⟫ (by simp) rfl; simpa [substCode_param_eq] using this,
   by intro v
      simp [substCodeGraphDef, HierarchySymbol.Semiformula.val_sigma,
        SubstCode.construction.fixpoint_definedΔ₁.df, SubstCodeGraph]⟩

instance substCodeGraph_definable : 𝚫₁-Relation₄[V] SubstCodeGraph := substCodeGraph_defined.to_definable

instance substCodeGraph_definable' : Γ-[m + 1]-Relation₄[V] SubstCodeGraph :=
  substCodeGraph_definable.of_deltaOne

lemma SubstCodeGraph.case_iff {me opp x y : V} :
    SubstCodeGraph me opp x y ↔
    (∃ a, x = pConst a ∧ y = pConst a) ∨
    (x = pSelf ∧ y = me) ∨ (x = pOpp ∧ y = opp) ∨
    (∃ p, x = pBot p ∧ y = pBot p) ∨
    (∃ p q p' q', SubstCodeGraph me opp p p' ∧ SubstCodeGraph me opp q q' ∧ x = pSim p q ∧ y = pSim p' q') ∨
    (∃ b a p q b' p' q', SubstCodeGraph me opp b b' ∧ SubstCodeGraph me opp p p' ∧ SubstCodeGraph me opp q q' ∧
      x = pIte b a p q ∧ y = pIte b' a p' q') ∨
    (∃ k g p q p' q', SubstCodeGraph me opp p p' ∧ SubstCodeGraph me opp q q' ∧
      x = pSearch k g p q ∧ y = pSearch k (substTemplate me opp g) p' q') ∨
    (¬IsShape y ∧ x = y) :=
  Iff.trans SubstCode.construction.case (by simp [SubstCode.construction, SubstCode.Phi, SubstCodeGraph])

section inversion

attribute [local simp] pConst pSelf pOpp pBot pSim pIte pSearch IsShape

lemma SubstCodeGraph.const_iff {me opp a y : V} : SubstCodeGraph me opp (pConst a) y ↔ y = pConst a := by
  rw [SubstCodeGraph.case_iff]; simp
  intro h₀ _ _ _ _ _ _ h; exact absurd h.symm (h₀ a)
lemma SubstCodeGraph.self_iff {me opp y : V} : SubstCodeGraph me opp pSelf y ↔ y = me := by
  rw [SubstCodeGraph.case_iff]; simp
  intro _ h₁ _ _ _ _ _ h; exact absurd h.symm h₁
lemma SubstCodeGraph.opp_iff {me opp y : V} : SubstCodeGraph me opp pOpp y ↔ y = opp := by
  rw [SubstCodeGraph.case_iff]; simp
  intro _ _ h₂ _ _ _ _ h; exact absurd h.symm h₂
lemma SubstCodeGraph.bot_iff {me opp p y : V} : SubstCodeGraph me opp (pBot p) y ↔ y = pBot p := by
  rw [SubstCodeGraph.case_iff]; simp
  intro _ _ _ h₃ _ _ _ h; exact absurd h.symm (h₃ p)
lemma SubstCodeGraph.sim_iff {me opp p q y : V} :
    SubstCodeGraph me opp (pSim p q) y ↔
    ∃ p' q', SubstCodeGraph me opp p p' ∧ SubstCodeGraph me opp q q' ∧ y = pSim p' q' := by
  rw [SubstCodeGraph.case_iff]; simp
  intro _ _ _ _ h₄ _ _ h; exact absurd h.symm (h₄ p q)
lemma SubstCodeGraph.ite_iff {me opp b a p q y : V} :
    SubstCodeGraph me opp (pIte b a p q) y ↔
    ∃ b' p' q', SubstCodeGraph me opp b b' ∧ SubstCodeGraph me opp p p' ∧ SubstCodeGraph me opp q q' ∧
      y = pIte b' a p' q' := by
  rw [SubstCodeGraph.case_iff]; simp
  intro _ _ _ _ _ h₅ _ h; exact absurd h.symm (h₅ b a p q)
lemma SubstCodeGraph.search_iff {me opp k g p q y : V} :
    SubstCodeGraph me opp (pSearch k g p q) y ↔
    ∃ p' q', SubstCodeGraph me opp p p' ∧ SubstCodeGraph me opp q q' ∧ y = pSearch k (substTemplate me opp g) p' q' := by
  rw [SubstCodeGraph.case_iff]; simp
  intro _ _ _ _ _ _ h₆ h; exact absurd h.symm (h₆ k g p q)
lemma SubstCodeGraph.of_not_shape {me opp x y : V} (hx : ¬IsShape x) : SubstCodeGraph me opp x y ↔ y = x := by
  rw [SubstCodeGraph.case_iff]
  constructor
  · rintro (⟨a, rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨p, rfl, _⟩ | ⟨p, q, p', q', _, _, rfl, _⟩ |
      ⟨b, a, p, q, b', p', q', _, _, _, rfl, _⟩ | ⟨k, g, p, q, p', q', _, _, rfl, _⟩ | ⟨_, h⟩)
    · exact absurd (Or.inl ⟨a, rfl⟩) hx
    · exact absurd (Or.inr (Or.inl rfl)) hx
    · exact absurd (Or.inr (Or.inr (Or.inl rfl))) hx
    · exact absurd (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, rfl⟩)))) hx
    · exact absurd (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, q, rfl⟩))))) hx
    · exact absurd (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨b, a, p, q, rfl⟩)))))) hx
    · exact absurd (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨k, g, p, q, rfl⟩)))))) hx
    · exact h.symm
  · rintro rfl
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hx, rfl⟩))))))

end inversion

/-! ### `substCode` is a total Σ₁ function -/

lemma substCodeGraph_exists (me opp x : V) : ∃ y, SubstCodeGraph me opp x y := by
  induction x using ISigma1.sigma1_order_induction with
  | hP => definability
  | ind x ih =>
    by_cases hx : IsShape x
    · rcases hx with ⟨a, rfl⟩ | rfl | rfl | ⟨p, rfl⟩ | ⟨p, q, rfl⟩ | ⟨b, a, p, q, rfl⟩ | ⟨k, g, p, q, rfl⟩
      · exact ⟨_, SubstCodeGraph.const_iff.mpr rfl⟩
      · exact ⟨_, SubstCodeGraph.self_iff.mpr rfl⟩
      · exact ⟨_, SubstCodeGraph.opp_iff.mpr rfl⟩
      · exact ⟨_, SubstCodeGraph.bot_iff.mpr rfl⟩
      · obtain ⟨p', hp⟩ := ih p (by simp); obtain ⟨q', hq⟩ := ih q (by simp)
        exact ⟨_, SubstCodeGraph.sim_iff.mpr ⟨p', q', hp, hq, rfl⟩⟩
      · obtain ⟨b', hb⟩ := ih b (by simp); obtain ⟨p', hp⟩ := ih p (by simp)
        obtain ⟨q', hq⟩ := ih q (by simp)
        exact ⟨_, SubstCodeGraph.ite_iff.mpr ⟨b', p', q', hb, hp, hq, rfl⟩⟩
      · obtain ⟨p', hp⟩ := ih p (by simp); obtain ⟨q', hq⟩ := ih q (by simp)
        exact ⟨_, SubstCodeGraph.search_iff.mpr ⟨p', q', hp, hq, rfl⟩⟩
    · exact ⟨x, (SubstCodeGraph.of_not_shape hx).mpr rfl⟩

lemma substCodeGraph_unique (me opp x : V) :
    ∀ y₁ y₂, SubstCodeGraph me opp x y₁ → SubstCodeGraph me opp x y₂ → y₁ = y₂ := by
  induction x using ISigma1.pi1_order_induction with
  | hP => definability
  | ind x ih =>
    intro y₁ y₂ h₁ h₂
    by_cases hx : IsShape x
    · rcases hx with ⟨a, rfl⟩ | rfl | rfl | ⟨p, rfl⟩ | ⟨p, q, rfl⟩ | ⟨b, a, p, q, rfl⟩ | ⟨k, g, p, q, rfl⟩
      · rw [SubstCodeGraph.const_iff] at h₁ h₂; rw [h₁, h₂]
      · rw [SubstCodeGraph.self_iff] at h₁ h₂; rw [h₁, h₂]
      · rw [SubstCodeGraph.opp_iff] at h₁ h₂; rw [h₁, h₂]
      · rw [SubstCodeGraph.bot_iff] at h₁ h₂; rw [h₁, h₂]
      · rcases SubstCodeGraph.sim_iff.mp h₁ with ⟨p₁, q₁, hp₁, hq₁, rfl⟩
        rcases SubstCodeGraph.sim_iff.mp h₂ with ⟨p₂, q₂, hp₂, hq₂, rfl⟩
        rw [ih p (by simp) _ _ hp₁ hp₂, ih q (by simp) _ _ hq₁ hq₂]
      · rcases SubstCodeGraph.ite_iff.mp h₁ with ⟨b₁, p₁, q₁, hb₁, hp₁, hq₁, rfl⟩
        rcases SubstCodeGraph.ite_iff.mp h₂ with ⟨b₂, p₂, q₂, hb₂, hp₂, hq₂, rfl⟩
        rw [ih b (by simp) _ _ hb₁ hb₂, ih p (by simp) _ _ hp₁ hp₂, ih q (by simp) _ _ hq₁ hq₂]
      · rcases SubstCodeGraph.search_iff.mp h₁ with ⟨p₁, q₁, hp₁, hq₁, rfl⟩
        rcases SubstCodeGraph.search_iff.mp h₂ with ⟨p₂, q₂, hp₂, hq₂, rfl⟩
        rw [ih p (by simp) _ _ hp₁ hp₂, ih q (by simp) _ _ hq₁ hq₂]
    · rw [SubstCodeGraph.of_not_shape hx] at h₁ h₂; rw [h₁, h₂]

lemma substCodeGraph_existsUnique (me opp x : V) : ∃! y, SubstCodeGraph me opp x y := by
  rcases substCodeGraph_exists me opp x with ⟨y, hy⟩
  exact ExistsUnique.intro y hy (fun y' h' ↦ substCodeGraph_unique me opp x y' y h' hy)

/-- **Program substitution**: `pSelf ↦ me`, `pOpp ↦ opp`, `pBot` frozen, stored templates
instantiated with the descriptions of `(me, opp)` — the engine's `Prog.subst`. -/
noncomputable def substCode (me opp x : V) : V := Classical.choose! (substCodeGraph_existsUnique me opp x)

lemma substCode_graph (me opp x : V) : SubstCodeGraph me opp x (substCode me opp x) :=
  Classical.choose!_spec (substCodeGraph_existsUnique me opp x)

lemma substCode_eq_of_graph {me opp x y : V} (h : SubstCodeGraph me opp x y) : substCode me opp x = y :=
  substCodeGraph_unique me opp x _ _ (substCode_graph me opp x) h

noncomputable def substCodeDef : 𝚺₁.Semisentence 4 := .mkSigma “y me opp x. !substCodeGraphDef.sigma me opp x y”

instance substCode_defined : 𝚺₁-Function₃ (substCode : V → V → V → V) via substCodeDef := .mk fun v ↦ by
  simp [substCodeDef, HierarchySymbol.Semiformula.val_sigma, substCodeGraph_defined.df]
  constructor
  · intro h; exact (substCode_eq_of_graph h).symm
  · intro h; rw [h]; exact substCode_graph _ _ _

instance substCode_definable : 𝚺₁-Function₃ (substCode : V → V → V → V) := substCode_defined.to_definable

instance substCode_definable' : Γ-[m + 1]-Function₃ (substCode : V → V → V → V) :=
  substCode_definable.of_sigmaOne

@[simp] lemma substCode_const (me opp a : V) : substCode me opp (pConst a) = pConst a :=
  substCode_eq_of_graph (SubstCodeGraph.const_iff.mpr rfl)
@[simp] lemma substCode_self (me opp : V) : substCode me opp (pSelf : V) = me :=
  substCode_eq_of_graph (SubstCodeGraph.self_iff.mpr rfl)
@[simp] lemma substCode_opp (me opp : V) : substCode me opp (pOpp : V) = opp :=
  substCode_eq_of_graph (SubstCodeGraph.opp_iff.mpr rfl)
@[simp] lemma substCode_bot (me opp p : V) : substCode me opp (pBot p) = pBot p :=
  substCode_eq_of_graph (SubstCodeGraph.bot_iff.mpr rfl)
@[simp] lemma substCode_sim (me opp p q : V) :
    substCode me opp (pSim p q) = pSim (substCode me opp p) (substCode me opp q) :=
  substCode_eq_of_graph (SubstCodeGraph.sim_iff.mpr ⟨_, _, substCode_graph me opp p, substCode_graph me opp q, rfl⟩)
@[simp] lemma substCode_ite (me opp b a p q : V) :
    substCode me opp (pIte b a p q) = pIte (substCode me opp b) a (substCode me opp p) (substCode me opp q) :=
  substCode_eq_of_graph (SubstCodeGraph.ite_iff.mpr
    ⟨_, _, _, substCode_graph me opp b, substCode_graph me opp p, substCode_graph me opp q, rfl⟩)
@[simp] lemma substCode_search (me opp k g p q : V) :
    substCode me opp (pSearch k g p q) = pSearch k (substTemplate me opp g) (substCode me opp p) (substCode me opp q) :=
  substCode_eq_of_graph (SubstCodeGraph.search_iff.mpr ⟨_, _, substCode_graph me opp p, substCode_graph me opp q, rfl⟩)
lemma substCode_of_not_shape {me opp x : V} (hx : ¬IsShape x) : substCode me opp x = x :=
  substCode_eq_of_graph ((SubstCodeGraph.of_not_shape hx).mpr rfl)

/-! ### τ-equivariance -/

/-- **τ commutes with substitution**: transposing a substituted program is substituting the
transposed frame into the transposed program (on every code). -/
theorem transposeCode_substCode (me opp x : V) :
    transposeCode (substCode me opp x) = substCode (transposeCode me) (transposeCode opp) (transposeCode x) := by
  induction x using ISigma1.pi1_order_induction with
  | hP => definability
  | ind x ih =>
    by_cases hx : IsShape x
    · rcases hx with ⟨a, rfl⟩ | rfl | rfl | ⟨p, rfl⟩ | ⟨p, q, rfl⟩ | ⟨b, a, p, q, rfl⟩ | ⟨k, g, p, q, rfl⟩
      · simp [transposeCode]
      · simp [transposeCode]
      · simp [transposeCode]
      · simp [transposeCode]
      · simp [transposeCode, ih p (by simp), ih q (by simp)]
      · simp [transposeCode, ih b (by simp), ih p (by simp), ih q (by simp)]
      · simp [transposeCode, ih p (by simp), ih q (by simp), revalueTemplate_substTemplate]
    · simp only [transposeCode]
      rw [substCode_of_not_shape hx, revalue_of_not_shape hx, substCode_of_not_shape hx]

end ArithS
