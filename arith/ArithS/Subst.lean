import ArithS.Guard

/-!
# ArithS.Subst — program substitution on codes (`psubst`), the engine's `Prog.subst`

Roadmap M3 step (b). The engine's `.sim p q` runs `p.subst me opp` against `q.subst me opp`:
`subst` is ONE-SHOT (`.self ↦ me`, `.opp ↦ opp`), `.bot` is a barrier (frozen), and it
descends into the guard of a `.search` node — so a guard inside a simulated program refers
to the OUTER players. On codes:

* `gsubst me opp g` instantiates a six-variable template with the canonical descriptions of
  `me` and `opp` — it IS `guardCode g me opp` on every template (`IsSemiformula LAct 6 g`,
  `gsubst_of_template`) and the identity on every other code. The result is a SENTENCE
  (no free variables), so a later `guardCode … me' opp'` is the identity on it
  (`guardCode_gsubst`): a search node inside a simulated program evaluates its guard
  against the outer players whatever the current frame is — the engine's semantics.
  (The guard on non-templates is what makes the τ-equivariance below hold on EVERY code:
  `subst` truncates out-of-range variables to `0` and `relabelTemplate` fixes the
  resulting non-formula, so on a code with more than six free variables the two do not
  commute — `^rel 2 R ?[c_C, #7]` is a counterexample.)
* `psubst me opp p`: the Δ₁ fixpoint on pairs `⟪x, y⟫` with parameters `me opp`, exactly
  like `Relabel` (`ArithS.Prog`): `pConst a ↦ pConst a`, `pSelf ↦ me`, `pOpp ↦ opp`,
  `pBot p ↦ pBot p` (frozen), `pSim`/`pIte` structurally, `pSearch k g p q ↦
  pSearch k (gsubst me opp g) (psubst p) (psubst q)`, non-shapes fixed. A Σ₁ function
  (`psubstDef`), with the equations `psubst_const/self/opp/bot/sim/ite/search`.
* τ-equivariance: `swapcode_psubst : swapcode (psubst me opp p) = psubst (swapcode me)
  (swapcode opp) (swapcode p)`, from the code-level swap equation for descriptions
  (`termRelabelVec_descVec`: `termRelabel 1 0` maps `descVec me opp` entrywise to
  `descVec (swapcode me) (swapcode opp)`) and the commutation of `relabelTemplate` with
  `subst` (`relabelTemplate_subst`, by the formula recursion, as `substs_substs`).
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

lemma bnum_semiterm_LAct (n x : V) : IsSemiterm LAct n (bnum x) :=
  IsSemiterm.LAct_of_LOR (bnum_semiterm n x)

lemma progT_semiterm_LAct (n x : V) : IsSemiterm LAct n (progT x) :=
  IsSemiterm.LAct_of_LOR (progT_semiterm n x)

lemma dU_semiterm (n x : V) : IsSemiterm LAct n (dU x) := by
  unfold dU
  split_ifs
  · exact csym_semiterm isAct_zero
  · exact csym_semiterm isAct_one
  · exact numeral_semiterm_LAct n 0

lemma dW_semiterm (n x : V) : IsSemiterm LAct n (dW x) := by
  unfold dW
  split_ifs
  · exact csym_semiterm isAct_one
  · exact csym_semiterm isAct_zero
  · exact numeral_semiterm_LAct n 1

lemma six_eq : (6 : V) = 0 + 1 + 1 + 1 + 1 + 1 + 1 := by norm_num

/-- The description vector is a vector of six closed terms. -/
lemma descVec_semitermVec (me opp : V) : IsSemitermVec LAct 6 0 (descVec me opp) := by
  rw [six_eq, descVec]
  exact ((((((IsSemitermVec.nil 0).adjoin (dW_semiterm 0 opp)).adjoin (dU_semiterm 0 opp)).adjoin
    (progT_semiterm_LAct 0 _)).adjoin (dW_semiterm 0 me)).adjoin (dU_semiterm 0 me)).adjoin
    (progT_semiterm_LAct 0 _)

lemma len_descVec (me opp : V) : len (descVec me opp) = 6 := (descVec_semitermVec me opp).lh

lemma descVec_utermVec (me opp : V) : IsUTermVec LAct (len (descVec me opp)) (descVec me opp) := by
  rw [len_descVec]; exact (descVec_semitermVec me opp).isUTerm

/-- Instantiating a six-variable template gives a sentence. -/
lemma isSemiformula_guardCode {g : V} (hg : IsSemiformula LAct 6 g) (me opp : V) :
    IsSemiformula LAct 0 (guardCode g me opp) :=
  hg.subst (descVec_semitermVec me opp)

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
  subst_eq_self_of_le hg (descVec_utermVec me opp) (by simp) (by simp)

/-! ### `gsubst`: instantiate a template with the outer descriptions -/

open scoped Classical in
/-- Fill a six-variable template with the descriptions of `me` and `opp`; every other code is
fixed. On templates this is `guardCode` (`gsubst_of_template`). -/
noncomputable def gsubst (me opp g : V) : V :=
  if IsSemiformula LAct 6 g then guardCode g me opp else g

lemma gsubst_of_template {g : V} (hg : IsSemiformula LAct 6 g) (me opp : V) :
    gsubst me opp g = guardCode g me opp := by
  unfold gsubst; rw [if_pos hg]

lemma gsubst_of_not {g : V} (hg : ¬IsSemiformula LAct 6 g) (me opp : V) : gsubst me opp g = g := by
  unfold gsubst; rw [if_neg hg]

lemma isSemiformula_gsubst {g : V} (hg : IsSemiformula LAct 6 g) (me opp : V) :
    IsSemiformula LAct 0 (gsubst me opp g) := by
  rw [gsubst_of_template hg]; exact isSemiformula_guardCode hg me opp

/-- **Outer reference**: an instantiated template is a sentence, so the guard code computed by
the evaluator in ANY later frame `(me', opp')` is the instantiation by the OUTER frame. -/
theorem guardCode_gsubst {g : V} (hg : IsSemiformula LAct 6 g) (me opp me' opp' : V) :
    guardCode (gsubst me opp g) me' opp' = gsubst me opp g :=
  guardCode_of_sentence (isSemiformula_gsubst hg me opp) me' opp'

noncomputable def gsubstGraph : 𝚺₁.Semisentence 4 := .mkSigma
  “y me opp g. (!(isSemiformula LAct).sigma 6 g ∧ !guardCodeGraph y g me opp) ∨
    (¬!(isSemiformula LAct).pi 6 g ∧ y = g)”

instance gsubst.defined : 𝚺₁-Function₃ (gsubst : V → V → V → V) via gsubstGraph := .mk fun v ↦ by
  simp [gsubstGraph, HierarchySymbol.Semiformula.val_sigma,
    (IsSemiformula.defined (L := LAct) (V := V)).proper.iff',
    (IsSemiformula.defined (L := LAct) (V := V)).df, guardCode.defined.df, numeral_eq_natCast]
  by_cases h : IsSemiformula LAct 6 (v 3) <;> simp [h, gsubst]

instance gsubst.definable : 𝚺₁-Function₃ (gsubst : V → V → V → V) := gsubst.defined.to_definable

instance gsubst.definable' : Γ-[m + 1]-Function₃ (gsubst : V → V → V → V) :=
  gsubst.definable.of_sigmaOne


/-! ### `relabelTemplate` commutes with substitution

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
    exact ⟨isFunc_relabelSym hu hw hkf, IsSemitermVec.iff.mpr
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
      termBShift_func (isFunc_relabelSym hu hw hkf) (IsUTermVec.termRelabelVec hu hw hv)]
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
      termSubst_func (isFunc_relabelSym hu hw hf) (IsUTermVec.termRelabelVec hu hw hts.isUTerm)]
    simp only [qqFunc_inj, true_and]
    apply nth_ext' k (len_termRelabelVec (hv.termSubstVec hts).isUTerm)
      (len_termSubstVec (IsUTermVec.termRelabelVec hu hw hts.isUTerm))
    intro i hi
    rw [nth_termRelabelVec (hv.termSubstVec hts).isUTerm hi, nth_termSubstVec hts.isUTerm hi,
      nth_termSubstVec (IsUTermVec.termRelabelVec hu hw hts.isUTerm) hi,
      nth_termRelabelVec hts.isUTerm hi, ih i hi]

/-- **`relabelTemplate` commutes with `subst`.** -/
theorem relabelTemplate_subst (hu : IsAct u) (hw : IsAct w) {n p : V} (hp : IsSemiformula LAct n p) :
    ∀ {m v : V}, IsSemitermVec LAct n m v →
    relabelTemplate u w (subst LAct v p) = subst LAct (termRelabelVec u w n v) (relabelTemplate u w p) := by
  apply IsSemiformula.pi1_structural_induction ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hp
  · definability
  · intro n k R ts hR hts m v hv
    rw [substs_rel hR hts.isUTerm, relabelTemplate_rel hR (hv.termSubstVec hts).isUTerm,
      relabelTemplate_rel hR hts.isUTerm,
      substs_rel hR (IsUTermVec.termRelabelVec hu hw hts.isUTerm)]
    simp only [qqRel_inj, true_and]
    apply nth_ext' k (len_termRelabelVec (hv.termSubstVec hts).isUTerm)
      (len_termSubstVec (IsUTermVec.termRelabelVec hu hw hts.isUTerm))
    intro i hi
    rw [nth_termRelabelVec (hv.termSubstVec hts).isUTerm hi, nth_termSubstVec hts.isUTerm hi,
      nth_termSubstVec (IsUTermVec.termRelabelVec hu hw hts.isUTerm) hi,
      nth_termRelabelVec hts.isUTerm hi, termRelabel_termSubst hu hw (hts.nth hi) hv]
  · intro n k R ts hR hts m v hv
    rw [substs_nrel hR hts.isUTerm, relabelTemplate_nrel hR (hv.termSubstVec hts).isUTerm,
      relabelTemplate_nrel hR hts.isUTerm,
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
      relabelTemplate_and (hp.subst hv).isUFormula (hq.subst hv).isUFormula,
      relabelTemplate_and hp.isUFormula hq.isUFormula,
      substs_and (IsUFormula.relabelTemplate hu hw hp.isUFormula)
        (IsUFormula.relabelTemplate hu hw hq.isUFormula), ihp hv, ihq hv]
  · intro n p q hp hq ihp ihq m v hv
    rw [substs_or hp.isUFormula hq.isUFormula,
      relabelTemplate_or (hp.subst hv).isUFormula (hq.subst hv).isUFormula,
      relabelTemplate_or hp.isUFormula hq.isUFormula,
      substs_or (IsUFormula.relabelTemplate hu hw hp.isUFormula)
        (IsUFormula.relabelTemplate hu hw hq.isUFormula), ihp hv, ihq hv]
  · intro n p hp ih m v hv
    rw [substs_all hp.isUFormula, relabelTemplate_all (hp.subst hv.qVec).isUFormula,
      relabelTemplate_all hp.isUFormula,
      substs_all (IsUFormula.relabelTemplate hu hw hp.isUFormula), ih hv.qVec,
      termRelabelVec_qVec hu hw hv.isUTerm]
  · intro n p hp ih m v hv
    rw [substs_ex hp.isUFormula, relabelTemplate_exs (hp.subst hv.qVec).isUFormula,
      relabelTemplate_exs hp.isUFormula,
      substs_ex (IsUFormula.relabelTemplate hu hw hp.isUFormula), ih hv.qVec,
      termRelabelVec_qVec hu hw hv.isUTerm]

/-- `relabelTemplate` preserves the number of free variables. -/
lemma IsSemiformula.relabelTemplate (hu : IsAct u) (hw : IsAct w) {n p : V} (hp : IsSemiformula LAct n p) :
    IsSemiformula LAct n (relabelTemplate u w p) := by
  apply IsSemiformula.pi1_structural_induction ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hp
  · definability
  · intro n k R v hR hv
    rw [relabelTemplate_rel hR hv.isUTerm, IsSemiformula.rel]
    exact ⟨hR, IsSemitermVec.termRelabelVec hu hw hv⟩
  · intro n k R v hR hv
    rw [relabelTemplate_nrel hR hv.isUTerm, IsSemiformula.nrel]
    exact ⟨hR, IsSemitermVec.termRelabelVec hu hw hv⟩
  · intro n; simp
  · intro n; simp
  · intro n p q hp hq ihp ihq
    rw [relabelTemplate_and hp.isUFormula hq.isUFormula]; simp [ihp, ihq]
  · intro n p q hp hq ihp ihq
    rw [relabelTemplate_or hp.isUFormula hq.isUFormula]; simp [ihp, ihq]
  · intro n p hp ih
    rw [relabelTemplate_all hp.isUFormula]; simpa using ih
  · intro n p hp ih
    rw [relabelTemplate_exs hp.isUFormula]; simpa using ih

lemma isSemiformula_relabelTemplate_swap_iff {n p : V} :
    IsSemiformula LAct n (relabelTemplate 1 0 p) ↔ IsSemiformula LAct n p :=
  ⟨fun h ↦ by simpa [relabelTemplate_swap_swap] using IsSemiformula.relabelTemplate isAct_one isAct_zero h,
   IsSemiformula.relabelTemplate isAct_one isAct_zero⟩

end commute

/-! ### The swap equation for descriptions, on codes -/

section dnum

lemma dnum_of_lt {x : V} (h : x < swapcode x) : dnum x = x := by
  unfold dnum; rw [if_pos (le_def.mpr (Or.inr h))]

lemma dnum_of_eq {x : V} (h : x = swapcode x) : dnum x = x := by
  unfold dnum; rw [if_pos (le_def.mpr (Or.inl h))]

lemma dnum_of_gt {x : V} (h : swapcode x < x) : dnum x = swapcode x := by
  unfold dnum
  rw [if_neg]
  intro h'
  rcases le_def.mp h' with e | l
  · rw [← e] at h; exact _root_.lt_irrefl _ h
  · exact lt_asymm h l

lemma dnum_swapcode (x : V) : dnum (swapcode x) = dnum x := by
  rcases lt_trichotomy x (swapcode x) with h | h | h
  · rw [dnum_of_lt h, dnum_of_gt (by rw [swapcode_swapcode]; exact h), swapcode_swapcode]
  · rw [← h]
  · rw [dnum_of_gt h, dnum_of_lt (by rw [swapcode_swapcode]; exact h)]

end dnum

/-- `termRelabel` fixes every `ℒₒᵣ` term (its symbols `0, 1, +, *` carry no action). -/
lemma termRelabel_of_LOR {u w t : V} (ht : IsUTerm ℒₒᵣ t) : termRelabel u w t = t := by
  apply IsUTerm.induction 𝚺 ?_ ?_ ?_ ?_ t ht
  · definability
  · intro z; simp
  · intro x; simp
  · intro k f v hkf hv ih
    have hv' : IsUTermVec LAct k v := ⟨hv.lh, fun i hi ↦ IsUTerm.LAct_of_LOR (hv.nth hi)⟩
    rw [termRelabel_func (isFunc_LAct_of_LOR hkf) hv']
    have hf : relabelSym f u w = f := by
      unfold relabelSym
      rcases isFunc_LOR.mp hkf with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;>
        rw [if_neg (by norm_num), if_neg (by norm_num)]
    rw [hf]
    simp only [qqFunc_inj, true_and]
    apply nth_ext' k (len_termRelabelVec hv') hv'.lh.symm
    intro i hi
    rw [nth_termRelabelVec hv' hi, ih i hi]

lemma termRelabel_bnum (u w n : V) : termRelabel u w (bnum n) = bnum n :=
  termRelabel_of_LOR (bnum_uterm n)

lemma termRelabel_progT (u w x : V) : termRelabel u w (progT x) = progT x :=
  termRelabel_of_LOR (progT_uterm x)

lemma termRelabel_numeral (u w n : V) : termRelabel u w (numeral n) = numeral n :=
  termRelabel_of_LOR (numeral_uterm n)

lemma termRelabel_csym {u w a : V} (ha : IsAct a) :
    termRelabel u w (csym a) = csym (relabelAct a u w) := by
  unfold csym
  rw [termRelabel_func (isFunc_csym ha) (by simp), termRelabelVec_nil]
  rcases ha with rfl | rfl
  · rw [show (2 : V) + 0 = 2 by norm_num, relabelSym_two]; simp [relabelAct]
  · rw [show (2 : V) + 1 = 3 by norm_num, relabelSym_three]; simp [relabelAct]

lemma termRelabel_dU (x : V) : termRelabel 1 0 (dU x) = dU (swapcode x) := by
  unfold dU
  rw [swapcode_swapcode]
  generalize swapcode x = s
  rcases lt_trichotomy x s with h | h | h
  · rw [if_pos h, if_neg (lt_asymm h), if_pos h, termRelabel_csym isAct_zero]; simp [relabelAct]
  · subst h
    rw [if_neg (_root_.lt_irrefl _), if_neg (_root_.lt_irrefl _), termRelabel_numeral]
  · rw [if_neg (lt_asymm h), if_pos h, if_pos h, termRelabel_csym isAct_one]; simp [relabelAct]

lemma termRelabel_dW (x : V) : termRelabel 1 0 (dW x) = dW (swapcode x) := by
  unfold dW
  rw [swapcode_swapcode]
  generalize swapcode x = s
  rcases lt_trichotomy x s with h | h | h
  · rw [if_pos h, if_neg (lt_asymm h), if_pos h, termRelabel_csym isAct_one]; simp [relabelAct]
  · subst h
    rw [if_neg (_root_.lt_irrefl _), if_neg (_root_.lt_irrefl _), termRelabel_numeral]
  · rw [if_neg (lt_asymm h), if_pos h, if_pos h, termRelabel_csym isAct_zero]; simp [relabelAct]

/-- **The swap equation for descriptions**: the code-level τ maps the description vector of
`(me, opp)` entrywise to that of `(swapcode me, swapcode opp)`. -/
theorem termRelabelVec_descVec (me opp : V) :
    termRelabelVec 1 0 6 (descVec me opp) = descVec (swapcode me) (swapcode opp) := by
  have e0 : IsUTermVec LAct 0 (0 : V) := IsUTermVec.empty
  have h1 : IsUTermVec LAct (0 + 1) (dW opp ∷ (0 : V)) := e0.adjoin (dW_semiterm 0 opp).isUTerm
  have h2 : IsUTermVec LAct (0 + 1 + 1) (dU opp ∷ dW opp ∷ (0 : V)) := h1.adjoin (dU_semiterm 0 opp).isUTerm
  have h3 : IsUTermVec LAct (0 + 1 + 1 + 1) (progT (dnum opp) ∷ dU opp ∷ dW opp ∷ (0 : V)) :=
    h2.adjoin (progT_semiterm_LAct 0 (dnum opp)).isUTerm
  have h4 : IsUTermVec LAct (0 + 1 + 1 + 1 + 1) (dW me ∷ progT (dnum opp) ∷ dU opp ∷ dW opp ∷ (0 : V)) :=
    h3.adjoin (dW_semiterm 0 me).isUTerm
  have h5 : IsUTermVec LAct (0 + 1 + 1 + 1 + 1 + 1) (dU me ∷ dW me ∷ progT (dnum opp) ∷ dU opp ∷ dW opp ∷ (0 : V)) :=
    h4.adjoin (dU_semiterm 0 me).isUTerm
  unfold descVec
  rw [six_eq, termRelabelVec_cons (progT_semiterm_LAct 0 (dnum me)).isUTerm h5,
    termRelabelVec_cons (dU_semiterm 0 me).isUTerm h4, termRelabelVec_cons (dW_semiterm 0 me).isUTerm h3,
    termRelabelVec_cons (progT_semiterm_LAct 0 (dnum opp)).isUTerm h2,
    termRelabelVec_cons (dU_semiterm 0 opp).isUTerm h1,
    termRelabelVec_cons (dW_semiterm 0 opp).isUTerm e0, termRelabelVec_nil,
    termRelabel_progT, termRelabel_progT, termRelabel_dU, termRelabel_dU, termRelabel_dW, termRelabel_dW,
    dnum_swapcode, dnum_swapcode]

/-- **The swap equation for `gsubst`**, on every code. -/
theorem relabelTemplate_gsubst (me opp g : V) :
    relabelTemplate 1 0 (gsubst me opp g) = gsubst (swapcode me) (swapcode opp) (relabelTemplate 1 0 g) := by
  by_cases hg : IsSemiformula LAct 6 g
  · rw [gsubst_of_template hg, gsubst_of_template (isSemiformula_relabelTemplate_swap_iff.mpr hg)]
    unfold guardCode
    rw [relabelTemplate_subst isAct_one isAct_zero hg (descVec_semitermVec me opp), termRelabelVec_descVec]
  · rw [gsubst_of_not hg, gsubst_of_not (fun h ↦ hg (isSemiformula_relabelTemplate_swap_iff.mp h))]


/-! ### `psubst`: a fixpoint on pairs `⟪x, y⟫` with parameters `me opp`

The search clause instantiates the stored template through `gsubst` (a Σ₁ function), so the
core is Δ₁ (both polarities cite `gsubstGraph`, exactly like `Relabel` cites
`relabelTemplateGraph`); the fixpoint is StrongFinite, since the sub-results referenced are
`⟪p, p'⟫` with `p < x` and `p' < y`. -/

namespace Psubst

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
    pr = ⟪pSearch k g p q, pSearch k (gsubst (param 0) (param 1) g) p' q'⟫) ∨
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
        ∃ g', !gsubstGraph g' me opp g ∧ ∃ p' < y, ∃ q' < y,
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
        ∀ g', !gsubstGraph g' me opp g → ∃ p' < y, ∃ q' < y,
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
          ⟪p, p'⟫ ∈ C ∧ ⟪q, q'⟫ ∈ C ∧ y = pSearch k (gsubst (param 0) (param 1) g) p' q') ∨
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
      simp [blueprint, HierarchySymbol.Semiformula.val_sigma, gsubst.defined.df]
    · intro v
      symm
      simpa [blueprint, HierarchySymbol.Semiformula.val_sigma, gsubst.defined.df,
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

end Psubst

/-- `PsubstGraph me opp x y`: `y` is `x` with the frame `(me, opp)` substituted in. -/
def PsubstGraph (me opp x y : V) : Prop := Psubst.construction.Fixpoint ![me, opp] ⟪x, y⟫

noncomputable def psubstGraphDef : 𝚫₁.Semisentence 4 := .mkDelta
  (.mkSigma “me opp x y. ∃ pr <⁺ (x + y + 1)², !pairDef pr x y ∧ !Psubst.blueprint.fixpointDefΔ₁.sigma pr me opp”)
  (.mkPi “me opp x y. ∀ pr <⁺ (x + y + 1)², !pairDef pr x y → !Psubst.blueprint.fixpointDefΔ₁.pi pr me opp”)

private lemma psubst_param_eq (v : Fin 3 → V) : (fun i ↦ v i.succ) = ![v 1, v 2] := by
  funext i; fin_cases i <;> rfl

instance psubstGraph_defined : 𝚫₁-Relation₄[V] PsubstGraph via psubstGraphDef := .mk
  ⟨by intro v
      simp [psubstGraphDef, HierarchySymbol.Semiformula.val_sigma,
        Psubst.construction.fixpoint_definedΔ₁.proper.iff', Psubst.construction.fixpoint_definedΔ₁.df]
      constructor
      · rintro h x _ rfl; simpa [psubst_param_eq] using h
      · intro h; have := h ⟪v 2, v 3⟫ (by simp) rfl; simpa [psubst_param_eq] using this,
   by intro v
      simp [psubstGraphDef, HierarchySymbol.Semiformula.val_sigma,
        Psubst.construction.fixpoint_definedΔ₁.df, PsubstGraph]⟩

instance psubstGraph_definable : 𝚫₁-Relation₄[V] PsubstGraph := psubstGraph_defined.to_definable

instance psubstGraph_definable' : Γ-[m + 1]-Relation₄[V] PsubstGraph :=
  psubstGraph_definable.of_deltaOne

lemma PsubstGraph.case_iff {me opp x y : V} :
    PsubstGraph me opp x y ↔
    (∃ a, x = pConst a ∧ y = pConst a) ∨
    (x = pSelf ∧ y = me) ∨ (x = pOpp ∧ y = opp) ∨
    (∃ p, x = pBot p ∧ y = pBot p) ∨
    (∃ p q p' q', PsubstGraph me opp p p' ∧ PsubstGraph me opp q q' ∧ x = pSim p q ∧ y = pSim p' q') ∨
    (∃ b a p q b' p' q', PsubstGraph me opp b b' ∧ PsubstGraph me opp p p' ∧ PsubstGraph me opp q q' ∧
      x = pIte b a p q ∧ y = pIte b' a p' q') ∨
    (∃ k g p q p' q', PsubstGraph me opp p p' ∧ PsubstGraph me opp q q' ∧
      x = pSearch k g p q ∧ y = pSearch k (gsubst me opp g) p' q') ∨
    (¬IsShape y ∧ x = y) :=
  Iff.trans Psubst.construction.case (by simp [Psubst.construction, Psubst.Phi, PsubstGraph])

section inversion

attribute [local simp] pConst pSelf pOpp pBot pSim pIte pSearch IsShape

lemma PsubstGraph.const_iff {me opp a y : V} : PsubstGraph me opp (pConst a) y ↔ y = pConst a := by
  rw [PsubstGraph.case_iff]; simp
  intro h₀ _ _ _ _ _ _ h; exact absurd h.symm (h₀ a)
lemma PsubstGraph.self_iff {me opp y : V} : PsubstGraph me opp pSelf y ↔ y = me := by
  rw [PsubstGraph.case_iff]; simp
  intro _ h₁ _ _ _ _ _ h; exact absurd h.symm h₁
lemma PsubstGraph.opp_iff {me opp y : V} : PsubstGraph me opp pOpp y ↔ y = opp := by
  rw [PsubstGraph.case_iff]; simp
  intro _ _ h₂ _ _ _ _ h; exact absurd h.symm h₂
lemma PsubstGraph.bot_iff {me opp p y : V} : PsubstGraph me opp (pBot p) y ↔ y = pBot p := by
  rw [PsubstGraph.case_iff]; simp
  intro _ _ _ h₃ _ _ _ h; exact absurd h.symm (h₃ p)
lemma PsubstGraph.sim_iff {me opp p q y : V} :
    PsubstGraph me opp (pSim p q) y ↔
    ∃ p' q', PsubstGraph me opp p p' ∧ PsubstGraph me opp q q' ∧ y = pSim p' q' := by
  rw [PsubstGraph.case_iff]; simp
  intro _ _ _ _ h₄ _ _ h; exact absurd h.symm (h₄ p q)
lemma PsubstGraph.ite_iff {me opp b a p q y : V} :
    PsubstGraph me opp (pIte b a p q) y ↔
    ∃ b' p' q', PsubstGraph me opp b b' ∧ PsubstGraph me opp p p' ∧ PsubstGraph me opp q q' ∧
      y = pIte b' a p' q' := by
  rw [PsubstGraph.case_iff]; simp
  intro _ _ _ _ _ h₅ _ h; exact absurd h.symm (h₅ b a p q)
lemma PsubstGraph.search_iff {me opp k g p q y : V} :
    PsubstGraph me opp (pSearch k g p q) y ↔
    ∃ p' q', PsubstGraph me opp p p' ∧ PsubstGraph me opp q q' ∧ y = pSearch k (gsubst me opp g) p' q' := by
  rw [PsubstGraph.case_iff]; simp
  intro _ _ _ _ _ _ h₆ h; exact absurd h.symm (h₆ k g p q)
lemma PsubstGraph.of_not_shape {me opp x y : V} (hx : ¬IsShape x) : PsubstGraph me opp x y ↔ y = x := by
  rw [PsubstGraph.case_iff]
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

/-! ### `psubst` is a total Σ₁ function -/

lemma psubstGraph_exists (me opp x : V) : ∃ y, PsubstGraph me opp x y := by
  induction x using ISigma1.sigma1_order_induction with
  | hP => definability
  | ind x ih =>
    by_cases hx : IsShape x
    · rcases hx with ⟨a, rfl⟩ | rfl | rfl | ⟨p, rfl⟩ | ⟨p, q, rfl⟩ | ⟨b, a, p, q, rfl⟩ | ⟨k, g, p, q, rfl⟩
      · exact ⟨_, PsubstGraph.const_iff.mpr rfl⟩
      · exact ⟨_, PsubstGraph.self_iff.mpr rfl⟩
      · exact ⟨_, PsubstGraph.opp_iff.mpr rfl⟩
      · exact ⟨_, PsubstGraph.bot_iff.mpr rfl⟩
      · obtain ⟨p', hp⟩ := ih p (by simp); obtain ⟨q', hq⟩ := ih q (by simp)
        exact ⟨_, PsubstGraph.sim_iff.mpr ⟨p', q', hp, hq, rfl⟩⟩
      · obtain ⟨b', hb⟩ := ih b (by simp); obtain ⟨p', hp⟩ := ih p (by simp)
        obtain ⟨q', hq⟩ := ih q (by simp)
        exact ⟨_, PsubstGraph.ite_iff.mpr ⟨b', p', q', hb, hp, hq, rfl⟩⟩
      · obtain ⟨p', hp⟩ := ih p (by simp); obtain ⟨q', hq⟩ := ih q (by simp)
        exact ⟨_, PsubstGraph.search_iff.mpr ⟨p', q', hp, hq, rfl⟩⟩
    · exact ⟨x, (PsubstGraph.of_not_shape hx).mpr rfl⟩

lemma psubstGraph_unique (me opp x : V) :
    ∀ y₁ y₂, PsubstGraph me opp x y₁ → PsubstGraph me opp x y₂ → y₁ = y₂ := by
  induction x using ISigma1.pi1_order_induction with
  | hP => definability
  | ind x ih =>
    intro y₁ y₂ h₁ h₂
    by_cases hx : IsShape x
    · rcases hx with ⟨a, rfl⟩ | rfl | rfl | ⟨p, rfl⟩ | ⟨p, q, rfl⟩ | ⟨b, a, p, q, rfl⟩ | ⟨k, g, p, q, rfl⟩
      · rw [PsubstGraph.const_iff] at h₁ h₂; rw [h₁, h₂]
      · rw [PsubstGraph.self_iff] at h₁ h₂; rw [h₁, h₂]
      · rw [PsubstGraph.opp_iff] at h₁ h₂; rw [h₁, h₂]
      · rw [PsubstGraph.bot_iff] at h₁ h₂; rw [h₁, h₂]
      · rcases PsubstGraph.sim_iff.mp h₁ with ⟨p₁, q₁, hp₁, hq₁, rfl⟩
        rcases PsubstGraph.sim_iff.mp h₂ with ⟨p₂, q₂, hp₂, hq₂, rfl⟩
        rw [ih p (by simp) _ _ hp₁ hp₂, ih q (by simp) _ _ hq₁ hq₂]
      · rcases PsubstGraph.ite_iff.mp h₁ with ⟨b₁, p₁, q₁, hb₁, hp₁, hq₁, rfl⟩
        rcases PsubstGraph.ite_iff.mp h₂ with ⟨b₂, p₂, q₂, hb₂, hp₂, hq₂, rfl⟩
        rw [ih b (by simp) _ _ hb₁ hb₂, ih p (by simp) _ _ hp₁ hp₂, ih q (by simp) _ _ hq₁ hq₂]
      · rcases PsubstGraph.search_iff.mp h₁ with ⟨p₁, q₁, hp₁, hq₁, rfl⟩
        rcases PsubstGraph.search_iff.mp h₂ with ⟨p₂, q₂, hp₂, hq₂, rfl⟩
        rw [ih p (by simp) _ _ hp₁ hp₂, ih q (by simp) _ _ hq₁ hq₂]
    · rw [PsubstGraph.of_not_shape hx] at h₁ h₂; rw [h₁, h₂]

lemma psubstGraph_existsUnique (me opp x : V) : ∃! y, PsubstGraph me opp x y := by
  rcases psubstGraph_exists me opp x with ⟨y, hy⟩
  exact ExistsUnique.intro y hy (fun y' h' ↦ psubstGraph_unique me opp x y' y h' hy)

/-- **Program substitution**: `pSelf ↦ me`, `pOpp ↦ opp`, `pBot` frozen, stored templates
instantiated with the descriptions of `(me, opp)` — the engine's `Prog.subst`. -/
noncomputable def psubst (me opp x : V) : V := Classical.choose! (psubstGraph_existsUnique me opp x)

lemma psubst_graph (me opp x : V) : PsubstGraph me opp x (psubst me opp x) :=
  Classical.choose!_spec (psubstGraph_existsUnique me opp x)

lemma psubst_eq_of_graph {me opp x y : V} (h : PsubstGraph me opp x y) : psubst me opp x = y :=
  psubstGraph_unique me opp x _ _ (psubst_graph me opp x) h

noncomputable def psubstDef : 𝚺₁.Semisentence 4 := .mkSigma “y me opp x. !psubstGraphDef.sigma me opp x y”

instance psubst_defined : 𝚺₁-Function₃ (psubst : V → V → V → V) via psubstDef := .mk fun v ↦ by
  simp [psubstDef, HierarchySymbol.Semiformula.val_sigma, psubstGraph_defined.df]
  constructor
  · intro h; exact (psubst_eq_of_graph h).symm
  · intro h; rw [h]; exact psubst_graph _ _ _

instance psubst_definable : 𝚺₁-Function₃ (psubst : V → V → V → V) := psubst_defined.to_definable

instance psubst_definable' : Γ-[m + 1]-Function₃ (psubst : V → V → V → V) :=
  psubst_definable.of_sigmaOne

@[simp] lemma psubst_const (me opp a : V) : psubst me opp (pConst a) = pConst a :=
  psubst_eq_of_graph (PsubstGraph.const_iff.mpr rfl)
@[simp] lemma psubst_self (me opp : V) : psubst me opp (pSelf : V) = me :=
  psubst_eq_of_graph (PsubstGraph.self_iff.mpr rfl)
@[simp] lemma psubst_opp (me opp : V) : psubst me opp (pOpp : V) = opp :=
  psubst_eq_of_graph (PsubstGraph.opp_iff.mpr rfl)
@[simp] lemma psubst_bot (me opp p : V) : psubst me opp (pBot p) = pBot p :=
  psubst_eq_of_graph (PsubstGraph.bot_iff.mpr rfl)
@[simp] lemma psubst_sim (me opp p q : V) :
    psubst me opp (pSim p q) = pSim (psubst me opp p) (psubst me opp q) :=
  psubst_eq_of_graph (PsubstGraph.sim_iff.mpr ⟨_, _, psubst_graph me opp p, psubst_graph me opp q, rfl⟩)
@[simp] lemma psubst_ite (me opp b a p q : V) :
    psubst me opp (pIte b a p q) = pIte (psubst me opp b) a (psubst me opp p) (psubst me opp q) :=
  psubst_eq_of_graph (PsubstGraph.ite_iff.mpr
    ⟨_, _, _, psubst_graph me opp b, psubst_graph me opp p, psubst_graph me opp q, rfl⟩)
@[simp] lemma psubst_search (me opp k g p q : V) :
    psubst me opp (pSearch k g p q) = pSearch k (gsubst me opp g) (psubst me opp p) (psubst me opp q) :=
  psubst_eq_of_graph (PsubstGraph.search_iff.mpr ⟨_, _, psubst_graph me opp p, psubst_graph me opp q, rfl⟩)
lemma psubst_of_not_shape {me opp x : V} (hx : ¬IsShape x) : psubst me opp x = x :=
  psubst_eq_of_graph ((PsubstGraph.of_not_shape hx).mpr rfl)

/-! ### τ-equivariance -/

/-- **τ commutes with substitution**: transposing a substituted program is substituting the
transposed frame into the transposed program (on every code). -/
theorem swapcode_psubst (me opp x : V) :
    swapcode (psubst me opp x) = psubst (swapcode me) (swapcode opp) (swapcode x) := by
  induction x using ISigma1.pi1_order_induction with
  | hP => definability
  | ind x ih =>
    by_cases hx : IsShape x
    · rcases hx with ⟨a, rfl⟩ | rfl | rfl | ⟨p, rfl⟩ | ⟨p, q, rfl⟩ | ⟨b, a, p, q, rfl⟩ | ⟨k, g, p, q, rfl⟩
      · simp [swapcode]
      · simp [swapcode]
      · simp [swapcode]
      · simp [swapcode]
      · simp [swapcode, ih p (by simp), ih q (by simp)]
      · simp [swapcode, ih b (by simp), ih p (by simp), ih q (by simp)]
      · simp [swapcode, ih p (by simp), ih q (by simp), relabelTemplate_gsubst]
    · simp only [swapcode]
      rw [psubst_of_not_shape hx, relabel_of_not_shape hx, psubst_of_not_shape hx]

end ArithS
