import ArithS.LangAct

/-!
# ArithS.RelabelTemplate — τ acts on template CODES

Roadmap M3 step (a): a search node stores a six-variable guard template `g` (a formula code
over `LAct`), and the code-level transposition must act on it. `relabelTemplate u w g` is the
image of `g` under the SYMBOL MAP `2 + a ↦ 2 + relabelAct a u w` on every `^func` node
(the two action constants `c_C = 2`, `c_D = 3`; the `ℒₒᵣ` symbols `0`, `1` and every other
node are unchanged), defined by Foundation's `TermRec`/`UformulaRec1` recursion schemes
exactly like `termSubst`/`subst`, hence a Σ₁ function; on a non-formula code it returns
the code itself, so that it is total and

* `relabelTemplate_zero_one : relabelTemplate 0 1 g = g`,
* `relabelTemplate_swap_swap : relabelTemplate 1 0 (relabelTemplate 1 0 g) = g`

hold for EVERY `g`. The meta link, at `V = ℕ`: `relabelTemplate 1 0 ⌜φ⌝ = ⌜lMap swap φ⌝`
(`relabelTemplate_quote`, `relabelTemplate_quote_sentence`) — the code-level τ IS the
syntactic transposition `swap` of `ArithS.LangAct`.
-/

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1
open LAct

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ### The symbol map -/

/-- The symbol code `2 ↦ 2 + u`, `3 ↦ 2 + w`, every other code fixed
(`2 + a ↦ 2 + relabelAct a u w` for the action constants). -/
noncomputable def relabelSym (f u w : V) : V := if f = 2 then 2 + u else if f = 3 then 2 + w else f

def relabelSymGraph : 𝚺₀.Semisentence 4 :=
  .mkSigma “y f u w. (f = 2 → y = 2 + u) ∧ (f = 3 → y = 2 + w) ∧ (f ≠ 2 → f ≠ 3 → y = f)”

instance relabelSym.defined : 𝚺₀-Function₃ (relabelSym : V → V → V → V) via relabelSymGraph :=
  .mk fun v ↦ by
    suffices (v 1 = 2 → v 0 = 2 + v 2) ∧ (v 1 = 3 → v 0 = 2 + v 3) ∧ (v 1 ≠ 2 → v 1 ≠ 3 → v 0 = v 1) ↔
        v 0 = relabelSym (v 1) (v 2) (v 3) by simpa [relabelSymGraph]
    unfold relabelSym
    by_cases h2 : v 1 = 2
    · simp [h2]
    · by_cases h3 : v 1 = 3
      · simp [h2, h3]
      · simp [h2, h3]

instance relabelSym.definable : 𝚺₀-Function₃ (relabelSym : V → V → V → V) :=
  relabelSym.defined.to_definable

instance relabelSym.definable' (Γ m) : Γ-[m]-Function₃ (relabelSym : V → V → V → V) :=
  HierarchySymbol.Definable.of_zero relabelSym.definable

lemma two_ne_three : (2 : V) ≠ 3 := by
  intro h
  have h' : (2 : V) + 0 = 2 + 1 := by rw [add_zero]; exact h.trans (by norm_num)
  exact _root_.zero_ne_one (add_left_cancel h')

@[simp] lemma relabelSym_zero_one (f : V) : relabelSym f 0 1 = f := by
  unfold relabelSym
  by_cases h2 : f = 2
  · simp [h2]
  · by_cases h3 : f = 3
    · subst h3
      rw [if_neg (Ne.symm two_ne_three), if_pos rfl]
      norm_num
    · simp [h2, h3]

lemma relabelSym_two (u w : V) : relabelSym 2 u w = 2 + u := by
  unfold relabelSym; rw [if_pos rfl]

lemma relabelSym_three (u w : V) : relabelSym 3 u w = 2 + w := by
  unfold relabelSym; rw [if_neg (Ne.symm two_ne_three), if_pos rfl]

@[simp] lemma relabelSym_swap_swap (f : V) : relabelSym (relabelSym f 1 0) 1 0 = f := by
  unfold relabelSym
  by_cases h2 : f = 2
  · subst h2
    simp only [if_true]
    rw [if_neg (by norm_num), if_pos (by norm_num)]
    simp
  · by_cases h3 : f = 3
    · subst h3
      rw [if_neg (Ne.symm two_ne_three), if_pos rfl, if_pos (by simp)]
      norm_num
    · simp [h2, h3]

/-! ### Terms -/

namespace TermRelabel

def blueprint : Language.TermRec.Blueprint 2 where
  bvar := .mkSigma “y z u w. !qqBvarDef y z”
  fvar := .mkSigma “y x u w. !qqFvarDef y x”
  func := .mkSigma “y k f v v' u w. ∃ f', !relabelSymGraph f' f u w ∧ !qqFuncDef y k f' v'”

noncomputable def construction : Language.TermRec.Construction V blueprint where
  bvar (_ z)            := ^#z
  fvar (_ x)            := ^&x
  func (param k f _ v') := ^func k (relabelSym f (param 0) (param 1)) v'
  bvar_defined := .mk fun v ↦ by simp [blueprint]
  fvar_defined := .mk fun v ↦ by simp [blueprint]
  func_defined := .mk fun v ↦ by simp [blueprint]

end TermRelabel

section termRelabel

open TermRelabel

/-- Re-value the action constants of a term code. -/
noncomputable def termRelabel (u w t : V) : V := construction.result LAct ![u, w] t

noncomputable def termRelabelVec (u w k v : V) : V := construction.resultVec LAct ![u, w] k v

noncomputable def termRelabelGraph : 𝚺₁.Semisentence 4 :=
  (blueprint.result LAct).rew <| Rew.subst ![#0, #3, #1, #2]

noncomputable def termRelabelVecGraph : 𝚺₁.Semisentence 5 :=
  (blueprint.resultVec LAct).rew <| Rew.subst ![#0, #3, #4, #1, #2]

variable {u w : V}

@[simp] lemma termRelabel_bvar (z : V) : termRelabel u w ^#z = ^#z := by
  simp [termRelabel, construction]

@[simp] lemma termRelabel_fvar (x : V) : termRelabel u w ^&x = ^&x := by
  simp [termRelabel, construction]

@[simp] lemma termRelabel_func {k f v : V} (hkf : LAct.IsFunc k f) (hv : IsUTermVec LAct k v) :
    termRelabel u w (^func k f v) = ^func k (relabelSym f u w) (termRelabelVec u w k v) := by
  simp [termRelabel, construction, hkf, hv]; rfl

private lemma param_eq₂ (v : Fin 4 → V) : (fun i : Fin 2 ↦ v i.succ.succ) = ![v 2, v 3] := by
  funext i; match i with | 0 => rfl | 1 => rfl

private lemma param_eq₃ (v : Fin 5 → V) : (fun i : Fin 2 ↦ v i.succ.succ.succ) = ![v 3, v 4] := by
  funext i; match i with | 0 => rfl | 1 => rfl

instance termRelabel.defined : 𝚺₁-Function₃ (termRelabel : V → V → V → V) via termRelabelGraph :=
  .mk fun v ↦ by
    have := (construction.result_defined (V := V) (L := LAct)).defined ![v 0, v 3, v 1, v 2]
    simpa [termRelabelGraph, termRelabel, Matrix.constant_eq_singleton, Matrix.comp_vecCons',
      param_eq₂] using this

instance termRelabel.definable : 𝚺₁-Function₃ (termRelabel : V → V → V → V) :=
  termRelabel.defined.to_definable

instance termRelabel.definable' : Γ-[k + 1]-Function₃ (termRelabel : V → V → V → V) :=
  termRelabel.definable.of_sigmaOne

instance termRelabelVec.defined :
    𝚺₁-Function₄ (termRelabelVec : V → V → V → V → V) via termRelabelVecGraph :=
  .mk fun v ↦ by
    have := (construction.resultVec_defined (V := V) (L := LAct)).defined ![v 0, v 3, v 4, v 1, v 2]
    have e : Semiterm.val v Empty.elim ∘ (![#0, #3, #4, #1, #2] : Fin 5 → Semiterm ℒₒᵣ Empty 5) =
        ![v 0, v 3, v 4, v 1, v 2] := by
      funext i; match i with | 0 => rfl | 1 => rfl | 2 => rfl | 3 => rfl | 4 => rfl
    have e' : (fun i ↦ Semiterm.val v Empty.elim ((![#0, #3, #4, #1, #2] : Fin 5 → Semiterm ℒₒᵣ Empty 5) i)) =
        ![v 0, v 3, v 4, v 1, v 2] := e
    simp only [termRelabelVecGraph, HierarchySymbol.Semiformula.val_rew, Semiformula.Evalb,
      Semiformula.eval_substs, e, e']
    simp only [param_eq₃, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.cons_val_succ] at this
    exact this

instance termRelabelVec.definable : 𝚺₁-Function₄ (termRelabelVec : V → V → V → V → V) :=
  termRelabelVec.defined.to_definable

instance termRelabelVec.definable' : Γ-[i + 1]-Function₄ (termRelabelVec : V → V → V → V → V) :=
  termRelabelVec.definable.of_sigmaOne

@[simp] lemma len_termRelabelVec {k ts : V} (hts : IsUTermVec LAct k ts) :
    len (termRelabelVec u w k ts) = k := construction.resultVec_lh LAct _ hts

@[simp] lemma nth_termRelabelVec {k ts i : V} (hts : IsUTermVec LAct k ts) (hi : i < k) :
    (termRelabelVec u w k ts).[i] = termRelabel u w ts.[i] :=
  construction.nth_resultVec LAct _ hts hi

end termRelabel

/-! ### Preservation of the term predicates, identity and involution (for `u, w ∈ {0, 1}`) -/

section termFacts

lemma isFunc_LAct_def : (LAct).isFunc = .mkSigma “k f. (k = 0 ∧ f = 0) ∨ (k = 0 ∧ f = 1) ∨ (k = 0 ∧ f = 2) ∨
    (k = 0 ∧ f = 3) ∨ (k = 2 ∧ f = 0) ∨ (k = 2 ∧ f = 1)” := rfl

lemma isFunc_LAct {k f : V} :
    LAct.IsFunc k f ↔
    (k = 0 ∧ f = 0) ∨ (k = 0 ∧ f = 1) ∨ (k = 0 ∧ f = 2) ∨ (k = 0 ∧ f = 3) ∨ (k = 2 ∧ f = 0) ∨ (k = 2 ∧ f = 1) := by
  rw [isFunc_def, isFunc_LAct_def]; simp

/-- An action value: `0` or `1`. -/
def IsAct (u : V) : Prop := u = 0 ∨ u = 1

lemma isAct_zero : IsAct (0 : V) := Or.inl rfl
lemma isAct_one : IsAct (1 : V) := Or.inr rfl

lemma isFunc_relabelSym {k f u w : V} (hu : IsAct u) (hw : IsAct w) (h : LAct.IsFunc k f) :
    LAct.IsFunc k (relabelSym f u w) := by
  rw [isFunc_LAct] at h ⊢
  unfold relabelSym
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · norm_num
  · norm_num
  · rcases hu with rfl | rfl <;> norm_num
  · rcases hw with rfl | rfl <;> norm_num
  · norm_num
  · norm_num

variable {u w : V}

lemma IsUTerm.termRelabel (hu : IsAct u) (hw : IsAct w) {t : V} (ht : IsUTerm LAct t) :
    IsUTerm LAct (termRelabel u w t) := by
  apply IsUTerm.induction 𝚺 ?_ ?_ ?_ ?_ t ht
  · definability
  · intro z; simp
  · intro x; simp
  · intro k f v hkf hv ih
    rw [termRelabel_func hkf hv]
    exact IsUTerm.func (isFunc_relabelSym hu hw hkf)
      ⟨(len_termRelabelVec hv).symm, fun i hi ↦ by rw [nth_termRelabelVec hv hi]; exact ih i hi⟩

lemma IsUTermVec.termRelabelVec (hu : IsAct u) (hw : IsAct w) {k v : V} (hv : IsUTermVec LAct k v) :
    IsUTermVec LAct k (termRelabelVec u w k v) :=
  ⟨(len_termRelabelVec hv).symm, fun i hi ↦ by
    rw [nth_termRelabelVec hv hi]; exact IsUTerm.termRelabel hu hw (hv.nth hi)⟩

lemma termRelabel_zero_one {t : V} (ht : IsUTerm LAct t) : termRelabel 0 1 t = t := by
  apply IsUTerm.induction 𝚺 ?_ ?_ ?_ ?_ t ht
  · definability
  · intro z; simp
  · intro x; simp
  · intro k f v hkf hv ih
    rw [termRelabel_func hkf hv, relabelSym_zero_one]
    simp only [qqFunc_inj, true_and]
    apply nth_ext' k (len_termRelabelVec hv) hv.lh.symm
    intro i hi
    rw [nth_termRelabelVec hv hi, ih i hi]

lemma termRelabelVec_zero_one {k v : V} (hv : IsUTermVec LAct k v) : termRelabelVec 0 1 k v = v := by
  apply nth_ext' k (len_termRelabelVec hv) hv.lh.symm
  intro i hi
  rw [nth_termRelabelVec hv hi, termRelabel_zero_one (hv.nth hi)]

lemma termRelabel_swap_swap {t : V} (ht : IsUTerm LAct t) : termRelabel 1 0 (termRelabel 1 0 t) = t := by
  apply IsUTerm.induction 𝚺 ?_ ?_ ?_ ?_ t ht
  · definability
  · intro z; simp
  · intro x; simp
  · intro k f v hkf hv ih
    rw [termRelabel_func hkf hv,
      termRelabel_func (isFunc_relabelSym isAct_one isAct_zero hkf) (IsUTermVec.termRelabelVec isAct_one isAct_zero hv),
      relabelSym_swap_swap]
    simp only [qqFunc_inj, true_and]
    apply nth_ext' k (len_termRelabelVec (IsUTermVec.termRelabelVec isAct_one isAct_zero hv)) hv.lh.symm
    intro i hi
    rw [nth_termRelabelVec (IsUTermVec.termRelabelVec isAct_one isAct_zero hv) hi, nth_termRelabelVec hv hi, ih i hi]

lemma termRelabelVec_swap_swap {k v : V} (hv : IsUTermVec LAct k v) :
    termRelabelVec 1 0 k (termRelabelVec 1 0 k v) = v := by
  apply nth_ext' k (len_termRelabelVec (IsUTermVec.termRelabelVec isAct_one isAct_zero hv)) hv.lh.symm
  intro i hi
  rw [nth_termRelabelVec (IsUTermVec.termRelabelVec isAct_one isAct_zero hv) hi, nth_termRelabelVec hv hi,
    termRelabel_swap_swap (hv.nth hi)]

end termFacts

/-! ### Formulas -/

namespace FRelabel

noncomputable def blueprint : UformulaRec1.Blueprint where
  rel    := .mkSigma “y param k R v. ∃ u, !pi₁Def u param ∧ ∃ w, !pi₂Def w param ∧
    ∃ v', !termRelabelVecGraph v' u w k v ∧ !qqRelDef y k R v'”
  nrel   := .mkSigma “y param k R v. ∃ u, !pi₁Def u param ∧ ∃ w, !pi₂Def w param ∧
    ∃ v', !termRelabelVecGraph v' u w k v ∧ !qqNRelDef y k R v'”
  verum  := .mkSigma “y param. !qqVerumDef y”
  falsum := .mkSigma “y param. !qqFalsumDef y”
  and    := .mkSigma “y param p₁ p₂ y₁ y₂. !qqAndDef y y₁ y₂”
  or     := .mkSigma “y param p₁ p₂ y₁ y₂. !qqOrDef y y₁ y₂”
  all    := .mkSigma “y param p₁ y₁. !qqAllDef y y₁”
  exs    := .mkSigma “y param p₁ y₁. !qqExsDef y y₁”
  allChanges := .mkSigma “param' param. param' = param”
  exsChanges := .mkSigma “param' param. param' = param”

noncomputable def construction : UformulaRec1.Construction V blueprint where
  rel param k R v  := ^rel k R (termRelabelVec (π₁ param) (π₂ param) k v)
  nrel param k R v := ^nrel k R (termRelabelVec (π₁ param) (π₂ param) k v)
  verum _  := ^⊤
  falsum _ := ^⊥
  and _    := fun _ _ y₁ y₂ ↦ y₁ ^⋏ y₂
  or _     := fun _ _ y₁ y₂ ↦ y₁ ^⋎ y₂
  all _    := fun _ y₁ ↦ ^∀ y₁
  exs _    := fun _ y₁ ↦ ^∃ y₁
  allChanges param := param
  exsChanges param := param
  rel_defined := .mk fun v ↦ by simp [blueprint]
  nrel_defined := .mk fun v ↦ by simp [blueprint]
  verum_defined := .mk fun v ↦ by simp [blueprint]
  falsum_defined := .mk fun v ↦ by simp [blueprint]
  and_defined := .mk fun v ↦ by simp [blueprint]
  or_defined := .mk fun v ↦ by simp [blueprint]
  all_defined := .mk fun v ↦ by simp [blueprint]
  exs_defined := .mk fun v ↦ by simp [blueprint]
  allChanges_defined := .mk fun v ↦ by simp [blueprint]
  exChanges_defined := .mk fun v ↦ by simp [blueprint]

end FRelabel

section relabelTemplate

open scoped Classical in
/-- **τ on template codes**: re-value the action constants of a formula code (`0 ↦ u`,
`1 ↦ w` on the symbol codes `2 + a`); a non-formula code is returned unchanged. -/
noncomputable def relabelTemplate (u w g : V) : V :=
  if IsUFormula LAct g then FRelabel.construction.result LAct ⟪u, w⟫ g else g

noncomputable def relabelTemplateGraph : 𝚺₁.Semisentence 4 := .mkSigma
  “y u w g. ∃ pr, !pairDef pr u w ∧ ∃ r, !(FRelabel.blueprint.result LAct) r pr g ∧
    ((!(isUFormula LAct).sigma g ∧ y = r) ∨ (¬!(isUFormula LAct).pi g ∧ y = g))”

instance relabelTemplate.defined :
    𝚺₁-Function₃ (relabelTemplate : V → V → V → V) via relabelTemplateGraph := .mk fun v ↦ by
  simp [relabelTemplateGraph, HierarchySymbol.Semiformula.val_sigma,
    (IsUFormula.defined (L := LAct) (V := V)).proper.iff', (IsUFormula.defined (L := LAct) (V := V)).df,
    (FRelabel.construction (V := V)).result_defined.df, relabelTemplate]
  by_cases h : IsUFormula LAct (v 3) <;> simp [h]

instance relabelTemplate.definable : 𝚺₁-Function₃ (relabelTemplate : V → V → V → V) :=
  relabelTemplate.defined.to_definable

instance relabelTemplate.definable' : Γ-[m + 1]-Function₃ (relabelTemplate : V → V → V → V) :=
  relabelTemplate.definable.of_sigmaOne

variable {u w : V}

lemma relabelTemplate_of_uformula {g : V} (hg : IsUFormula LAct g) :
    relabelTemplate u w g = FRelabel.construction.result LAct ⟪u, w⟫ g := by
  unfold relabelTemplate; rw [if_pos hg]

lemma relabelTemplate_of_not {g : V} (hg : ¬IsUFormula LAct g) : relabelTemplate u w g = g := by
  unfold relabelTemplate; rw [if_neg hg]

@[simp] lemma relabelTemplate_rel {k R v : V} (hR : LAct.IsRel k R) (hv : IsUTermVec LAct k v) :
    relabelTemplate u w (^rel k R v) = ^rel k R (termRelabelVec u w k v) := by
  rw [relabelTemplate_of_uformula (by simp [hR, hv])]
  simp [FRelabel.construction, hR, hv]

@[simp] lemma relabelTemplate_nrel {k R v : V} (hR : LAct.IsRel k R) (hv : IsUTermVec LAct k v) :
    relabelTemplate u w (^nrel k R v) = ^nrel k R (termRelabelVec u w k v) := by
  rw [relabelTemplate_of_uformula (by simp [hR, hv])]
  simp [FRelabel.construction, hR, hv]

@[simp] lemma relabelTemplate_verum : relabelTemplate u w (^⊤ : V) = ^⊤ := by
  rw [relabelTemplate_of_uformula (by simp)]
  simp [FRelabel.construction]

@[simp] lemma relabelTemplate_falsum : relabelTemplate u w (^⊥ : V) = ^⊥ := by
  rw [relabelTemplate_of_uformula (by simp)]
  simp [FRelabel.construction]

@[simp] lemma relabelTemplate_and {p q : V} (hp : IsUFormula LAct p) (hq : IsUFormula LAct q) :
    relabelTemplate u w (p ^⋏ q) = relabelTemplate u w p ^⋏ relabelTemplate u w q := by
  rw [relabelTemplate_of_uformula (by simp [hp, hq]), relabelTemplate_of_uformula hp,
    relabelTemplate_of_uformula hq]
  simp [FRelabel.construction, hp, hq]

@[simp] lemma relabelTemplate_or {p q : V} (hp : IsUFormula LAct p) (hq : IsUFormula LAct q) :
    relabelTemplate u w (p ^⋎ q) = relabelTemplate u w p ^⋎ relabelTemplate u w q := by
  rw [relabelTemplate_of_uformula (by simp [hp, hq]), relabelTemplate_of_uformula hp,
    relabelTemplate_of_uformula hq]
  simp [FRelabel.construction, hp, hq]

@[simp] lemma relabelTemplate_all {p : V} (hp : IsUFormula LAct p) :
    relabelTemplate u w (^∀ p) = ^∀ (relabelTemplate u w p) := by
  rw [relabelTemplate_of_uformula (by simp [hp]), relabelTemplate_of_uformula hp]
  simp [FRelabel.construction, hp]

@[simp] lemma relabelTemplate_exs {p : V} (hp : IsUFormula LAct p) :
    relabelTemplate u w (^∃ p) = ^∃ (relabelTemplate u w p) := by
  rw [relabelTemplate_of_uformula (by simp [hp]), relabelTemplate_of_uformula hp]
  simp [FRelabel.construction, hp]

lemma IsUFormula.relabelTemplate (hu : IsAct u) (hw : IsAct w) {p : V} :
    IsUFormula LAct p → IsUFormula LAct (relabelTemplate u w p) := by
  apply IsUFormula.ISigma1.sigma1_succ_induction
  · definability
  · intro k r v hr hv; simp [hr, hv, IsUTermVec.termRelabelVec hu hw hv]
  · intro k r v hr hv; simp [hr, hv, IsUTermVec.termRelabelVec hu hw hv]
  · simp
  · simp
  · intro p q hp hq ihp ihq; simp [hp, hq, ihp, ihq]
  · intro p q hp hq ihp ihq; simp [hp, hq, ihp, ihq]
  · intro p hp ih; simp [hp, ih]
  · intro p hp ih; simp [hp, ih]

/-- Re-valuing with `(0, 1)` is the identity on every code. -/
theorem relabelTemplate_zero_one (g : V) : relabelTemplate 0 1 g = g := by
  by_cases hg : IsUFormula LAct g
  · revert g
    apply IsUFormula.ISigma1.sigma1_succ_induction
    · definability
    · intro k r v hr hv; simp [hr, hv, termRelabelVec_zero_one hv]
    · intro k r v hr hv; simp [hr, hv, termRelabelVec_zero_one hv]
    · simp
    · simp
    · intro p q hp hq ihp ihq; simp [hp, hq, ihp, ihq]
    · intro p q hp hq ihp ihq; simp [hp, hq, ihp, ihq]
    · intro p hp ih; simp [hp, ih]
    · intro p hp ih; simp [hp, ih]
  · exact relabelTemplate_of_not hg

/-- The transposition of template codes is an involution, on every code. -/
theorem relabelTemplate_swap_swap (g : V) : relabelTemplate 1 0 (relabelTemplate 1 0 g) = g := by
  by_cases hg : IsUFormula LAct g
  · revert g
    apply IsUFormula.ISigma1.sigma1_succ_induction
    · definability
    · intro k r v hr hv
      rw [relabelTemplate_rel hr hv, relabelTemplate_rel hr (IsUTermVec.termRelabelVec isAct_one isAct_zero hv),
        termRelabelVec_swap_swap hv]
    · intro k r v hr hv
      rw [relabelTemplate_nrel hr hv, relabelTemplate_nrel hr (IsUTermVec.termRelabelVec isAct_one isAct_zero hv),
        termRelabelVec_swap_swap hv]
    · simp
    · simp
    · intro p q hp hq ihp ihq
      rw [relabelTemplate_and hp hq,
        relabelTemplate_and (IsUFormula.relabelTemplate isAct_one isAct_zero hp) (IsUFormula.relabelTemplate isAct_one isAct_zero hq),
        ihp, ihq]
    · intro p q hp hq ihp ihq
      rw [relabelTemplate_or hp hq,
        relabelTemplate_or (IsUFormula.relabelTemplate isAct_one isAct_zero hp) (IsUFormula.relabelTemplate isAct_one isAct_zero hq),
        ihp, ihq]
    · intro p hp ih
      rw [relabelTemplate_all hp, relabelTemplate_all (IsUFormula.relabelTemplate isAct_one isAct_zero hp), ih]
    · intro p hp ih
      rw [relabelTemplate_exs hp, relabelTemplate_exs (IsUFormula.relabelTemplate isAct_one isAct_zero hp), ih]
  · rw [relabelTemplate_of_not hg, relabelTemplate_of_not hg]

end relabelTemplate

/-! ### The meta link at `V = ℕ`: the code-level τ is `lMap swap` -/

section metaLink

lemma quote_relabelSym_swap {k : ℕ} (f : LAct.Func k) :
    relabelSym (⌜f⌝ : ℕ) 1 0 = ⌜swap.func f⌝ := by
  rw [quote_func_def, quote_func_def, natCast_nat, natCast_nat]
  rcases f with f | ⟨(_ | _)⟩
  · have := ORing.encode_func_lt_two f
    change relabelSym (Encodable.encode f) 1 0 = Encodable.encode f
    unfold relabelSym
    rw [if_neg (by omega), if_neg (by omega)]
  · exact (relabelSym_two (V := ℕ) 1 0).trans rfl
  · exact (relabelSym_three (V := ℕ) 1 0).trans rfl

lemma isFunc_quote_nat {k : ℕ} (f : LAct.Func k) : LAct.IsFunc (V := ℕ) k ⌜f⌝ := by
  simpa using codeIn_func_quote (V := ℕ) f

lemma isRel_quote_nat {k : ℕ} (R : LAct.Rel k) : LAct.IsRel (V := ℕ) k ⌜R⌝ := by
  simpa using codeIn_rel_quote (V := ℕ) R

lemma isUTermVec_val_nat {k n : ℕ} (v : SemitermVec ℕ LAct k n) : IsUTermVec LAct k v.val := by
  simpa using SemitermVec.isUTermVec v

lemma len_val_nat {k n : ℕ} (v : SemitermVec ℕ LAct k n) : len v.val = k := by
  simpa using SemitermVec.len_eq v

lemma val_nth_nat {k n : ℕ} (v : SemitermVec ℕ LAct k n) (i : Fin k) : v.val.[(i : ℕ)] = (v i).val := by
  simpa using SemitermVec.val_nth_eq v i

lemma termRelabel_quote {n : ℕ} (t : SyntacticSemiterm LAct n) :
    termRelabel 1 0 (⌜t⌝ : ℕ) = ⌜Semiterm.lMap swap t⌝ := by
  induction t with
  | bvar x => simp
  | fvar x => simp
  | @func k f v ih =>
    rw [Semiterm.lMap_func, Semiterm.quote_func, Semiterm.quote_func, natCast_nat]
    show termRelabel 1 0 (^func k ⌜f⌝ (SemitermVec.val fun i ↦ (⌜v i⌝ : Bootstrapping.Semiterm ℕ LAct n))) =
      ^func k ⌜swap.func f⌝ (SemitermVec.val fun i ↦ (⌜Semiterm.lMap swap (v i)⌝ : Bootstrapping.Semiterm ℕ LAct n))
    rw [termRelabel_func (isFunc_quote_nat f) (isUTermVec_val_nat _), quote_relabelSym_swap]
    congr 1
    apply nth_ext' k (len_termRelabelVec (isUTermVec_val_nat _)) (len_val_nat _)
    intro i hi
    rw [nth_termRelabelVec (isUTermVec_val_nat _) hi]
    obtain ⟨i, rfl⟩ : ∃ j : Fin k, (j : ℕ) = i := ⟨⟨i, hi⟩, rfl⟩
    rw [val_nth_nat, val_nth_nat]
    exact ih i

lemma quote_isUFormula {n : ℕ} (φ : Semiproposition LAct n) : IsUFormula LAct (⌜φ⌝ : ℕ) :=
  (Semiformula.quote_isSemiformula φ).isUFormula

/-- **The meta link**: on the code of a formula, the code-level transposition is the code of
the transposed formula. -/
theorem relabelTemplate_quote {n : ℕ} (φ : Semiproposition LAct n) :
    relabelTemplate 1 0 (⌜φ⌝ : ℕ) = ⌜Semiformula.lMap swap φ⌝ := by
  induction φ with
  | @rel n k R v =>
    rw [Semiformula.lMap_rel, Semiformula.quote_rel, Semiformula.quote_rel, natCast_nat]
    show relabelTemplate 1 0 (^rel k ⌜R⌝ (SemitermVec.val fun i ↦ (⌜v i⌝ : Bootstrapping.Semiterm ℕ LAct n))) =
      ^rel k ⌜R⌝ (SemitermVec.val fun i ↦ (⌜Semiterm.lMap swap (v i)⌝ : Bootstrapping.Semiterm ℕ LAct n))
    rw [relabelTemplate_rel (isRel_quote_nat R) (isUTermVec_val_nat _)]
    congr 1
    apply nth_ext' k (len_termRelabelVec (isUTermVec_val_nat _)) (len_val_nat _)
    intro i hi
    rw [nth_termRelabelVec (isUTermVec_val_nat _) hi]
    obtain ⟨i, rfl⟩ : ∃ j : Fin k, (j : ℕ) = i := ⟨⟨i, hi⟩, rfl⟩
    rw [val_nth_nat, val_nth_nat]
    exact termRelabel_quote (v i)
  | @nrel n k R v =>
    rw [Semiformula.lMap_nrel, Semiformula.quote_nrel, Semiformula.quote_nrel, natCast_nat]
    show relabelTemplate 1 0 (^nrel k ⌜R⌝ (SemitermVec.val fun i ↦ (⌜v i⌝ : Bootstrapping.Semiterm ℕ LAct n))) =
      ^nrel k ⌜R⌝ (SemitermVec.val fun i ↦ (⌜Semiterm.lMap swap (v i)⌝ : Bootstrapping.Semiterm ℕ LAct n))
    rw [relabelTemplate_nrel (isRel_quote_nat R) (isUTermVec_val_nat _)]
    congr 1
    apply nth_ext' k (len_termRelabelVec (isUTermVec_val_nat _)) (len_val_nat _)
    intro i hi
    rw [nth_termRelabelVec (isUTermVec_val_nat _) hi]
    obtain ⟨i, rfl⟩ : ∃ j : Fin k, (j : ℕ) = i := ⟨⟨i, hi⟩, rfl⟩
    rw [val_nth_nat, val_nth_nat]
    exact termRelabel_quote (v i)
  | verum =>
    change relabelTemplate 1 0 (⌜(⊤ : Semiproposition LAct _)⌝ : ℕ) = ⌜Semiformula.lMap swap (⊤ : Semiproposition LAct _)⌝
    rw [LogicalConnective.HomClass.map_top]; simp
  | falsum =>
    change relabelTemplate 1 0 (⌜(⊥ : Semiproposition LAct _)⌝ : ℕ) = ⌜Semiformula.lMap swap (⊥ : Semiproposition LAct _)⌝
    rw [LogicalConnective.HomClass.map_bot]; simp
  | and φ ψ ihφ ihψ =>
    change relabelTemplate 1 0 (⌜φ ⋏ ψ⌝ : ℕ) = ⌜Semiformula.lMap swap (φ ⋏ ψ)⌝
    rw [LogicalConnective.HomClass.map_and, Semiformula.quote_and, Semiformula.quote_and,
      relabelTemplate_and (quote_isUFormula φ) (quote_isUFormula ψ), ihφ, ihψ]
  | or φ ψ ihφ ihψ =>
    change relabelTemplate 1 0 (⌜φ ⋎ ψ⌝ : ℕ) = ⌜Semiformula.lMap swap (φ ⋎ ψ)⌝
    rw [LogicalConnective.HomClass.map_or, Semiformula.quote_or, Semiformula.quote_or,
      relabelTemplate_or (quote_isUFormula φ) (quote_isUFormula ψ), ihφ, ihψ]
  | all φ ih =>
    change relabelTemplate 1 0 (⌜∀¹ φ⌝ : ℕ) = ⌜Semiformula.lMap swap (∀¹ φ)⌝
    rw [Semiformula.lMap_all, Semiformula.quote_all, Semiformula.quote_all,
      relabelTemplate_all (quote_isUFormula φ), ih]
  | exs φ ih =>
    change relabelTemplate 1 0 (⌜∃¹ φ⌝ : ℕ) = ⌜Semiformula.lMap swap (∃¹ φ)⌝
    rw [Semiformula.lMap_exs, Semiformula.quote_ex, Semiformula.quote_ex,
      relabelTemplate_exs (quote_isUFormula φ), ih]

/-- The meta link for semisentences (the form the templates use). -/
theorem relabelTemplate_quote_sentence {n : ℕ} (σ : Semisentence LAct n) :
    relabelTemplate 1 0 (⌜σ⌝ : ℕ) = ⌜Semiformula.lMap swap σ⌝ := by
  rw [Sentence.quote_def, Sentence.quote_def, ← Semiformula.lMap_emb, relabelTemplate_quote]

/-- The identity re-valuation on a quoted formula (a special case of `relabelTemplate_zero_one`). -/
theorem relabelTemplate_zero_one_quote {n : ℕ} (σ : Semisentence LAct n) :
    relabelTemplate 0 1 (⌜σ⌝ : ℕ) = ⌜σ⌝ := relabelTemplate_zero_one _

end metaLink

end ArithS

