import ArithS.InstV

/-!
# ArithS.Diag — the parametric diagonal lemma over `TAct` for `LAct` formulas

M4 item U6 of `Research/Notes/M4_BOUNDED_HBL/BRIEF.md` §3. Foundation's parametric fixed point
(`Foundation/FirstOrder/Bootstrapping/FixedPoint.lean`, `parameterizedFixedpoint` /
`parameterized_diagonal₁`) is stated for theories over `ℒₒᵣ`; the Löb argument's fixed point
lives over `LAct` (its target is Dupoc's guard formula, which mentions the action constants) in
the theory `TAct`. This module transports Foundation's construction along the reduct:

* **`substNumeralParamsA φ x := subst LAct (numeral x ∷ ^#0 ∷ 0) φ`** — Foundation's
  `substNumeralParams 1` with `subst ℒₒᵣ` replaced by `subst LAct`. Foundation's function is
  `ℒₒᵣ`-SPECIFIC: `substNumeralParams k φ x := subst ℒₒᵣ (…) φ` and the internal `subst L` is
  built by `L`-indexed recursion on formula codes (`Formula/Functions.lean:436`), so on a code
  that mentions `c_C`/`c_D` (an `LAct` function symbol of code `2`/`3`, not an `ℒₒᵣ` symbol)
  `subst ℒₒᵣ` is not the substitution. The twin is defined here with its Σ₁ graph `ssnumParamsA`
  (the `instB` pattern of `ArithS.InstV`) and its code equation `substNumeralParamsA_app_quote`:
  `substNumeralParamsA ⌜σ⌝ ⌜τ⌝ = ⌜σ ⇜ ![lMap emb ⌜τ⌝, #0]⌝`, where `⌜τ⌝ : ArithmeticSemiterm Empty 1`
  is Foundation's unary Gödel numeral, embedded along `emb` — a CONSTANT of the construction whose
  length never matters (the budget `k` enters the instances as `bnum k`, below).
* **`tactDiag θ := ∀¹ (ssnumParamsA[y, x, x] 🡒 θ[y, k])`** and
  **`tactFixedpoint θ := tactDiag θ ⇜ ![lMap emb ⌜tactDiag θ⌝, #0]`** — Foundation's
  `parameterizedDiag`/`parameterizedFixedpoint` at `k = 1`, over `LAct`.
* **`tact_parametric_diagonal₁ θ : TAct ⊢ ∀¹ (tactFixedpoint θ 🡘 θ ⇜ ![lMap emb ⌜tactFixedpoint θ⌝, #0])`**
  and its existential packaging `tact_parametric_diagonal`. Proved, like Foundation's, by the
  completeness theorem: the equivalence holds in every model of `TAct`.
* **Completeness over `TAct`, model-side (`tact_complete`)**: a sentence true in every
  `LAct`-structure `S` on an `ORingStructure M` with `Structure.lMap emb S = standardModel M`,
  `M↓[ℒₒᵣ] ⊧* 𝗣𝗔` and the two action axioms is a `TAct`-theorem. This is
  `Theory.Proof.complete_on_eq_models` (equality interpreted as equality, through Foundation's
  quotient `Structure.Eq.QuotEq`), which needs **`𝗘𝗤 LAct ⪯ TAct`** — proved here
  (`eqAxiom_weakerThan_TAct`): the equality axioms for the `ℒₒᵣ` symbols are `PA` axioms
  transported along `emb`, the congruence axiom of each action constant follows from
  reflexivity (`tact_proves_eqAxiom`, each case by the plain completeness theorem). The reduct
  of such an `S` is the standard structure of the ring operations read off `S`
  (`oringOfStructure`, `lMap_emb_eq_standardModel`).
* **Instances at the binary numeral** (the code-level reading the Löb argument uses): for every
  `k : ℕ`, `tact_parametric_diagonal_inst : TAct ⊢ ψ ⇜ ![lMap emb (bnumT k)] 🡘 (θ ⇜ ![⌜ψ⌝, #0]) ⇜ ![lMap emb (bnumT k)]`
  by `∀`-elimination (`Theory.Proof.specialize`); `models_tact_parametric_diagonal_inst`, its
  truth in every model of `TAct`; `provable_code_parametric_diagonal_inst`, its internal
  provability `Provable TAct ⌜…⌝` in every model of `IΣ₁` (D1, `internalize_provability`). On
  codes, `instB ⌜ψ⌝ k = ⌜ψ ⇜ ![lMap emb (bnumT k)]⌝` (`quote_instB`, `ArithS.InstV`), so the two
  sides are the `bnum k`-instances `instB ⌜tactFixedpoint θ⌝ k` and
  `instB ⌜θ ⇜ ![lMap emb ⌜tactFixedpoint θ⌝, #0]⌝ k` — DIFFERENT codes (of different formulas)
  that `TAct` proves equivalent; `instB ⌜ψ⌝ k = instB ⌜θ ⇜ …⌝ k` is false and never needed.

Trap (`HANDOVER_ARITHMETIZED_S.md` §6): `⌜tactDiag θ⌝` contains the CLOSED code of
`ssnumParamsA`; any `simp`/`decide` that unfolds a quote of it makes the kernel build an
astronomical `Nat` literal (`LEAN_NAT_MAX_SIZE`). Every equation about such quotes is proved for a
VARIABLE sentence (`val_vec_gödel`, `quote_lMap_gödel`) and instantiated, and `tactFixedpoint` is
unfolded only through `tactFixedpoint_def`.
-/

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open LAct

/-! ### The equality axioms of `LAct` are `TAct`-theorems -/

section eq

/-- A `PA` axiom, transported along `emb`, holds in the `ℒₒᵣ`-reduct of every model of `TAct`. -/
lemma eval_reduct_of_mem_PA (s : Struc.{0} LAct) (hs : s ⊧* TAct) {σ : Sentence ℒₒᵣ} (h : σ ∈ 𝗣𝗔) :
    Semiformula.Eval (s := Structure.lMap emb s.struc) ![] Empty.elim σ :=
  (Semiformula.models_lMap (s₂ := s.struc) (Φ := emb) (σ := σ)).mp
    (hs.models_set (lMap_emb_mem_TAct h))

lemma eqAxiom_mem_PA {σ : Sentence ℒₒᵣ} (h : σ ∈ 𝗘𝗤 ℒₒᵣ) : σ ∈ 𝗣𝗔 :=
  Or.inl (PeanoMinus.equal _ h)

/-- The value of the equality operator is the equality relation of the structure. -/
lemma val_op_eq {L : Language} [L.Eq] {M : Type*} [Structure L M] (v : Fin 2 → M) :
    Semiformula.Operator.val v (op(=) : Semiformula.Operator L 2) ↔
      Structure.rel (Language.Eq.eq : L.Rel 2) ![v 0, v 1] := by
  simp only [Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq, Semiformula.eval_rel,
    Function.comp_def, Semiterm.val_bvar]
  rw [← Matrix.fun_eq_vec_two v]

/-- **`TAct` proves the equality axioms of `LAct`.** The axioms for the `ℒₒᵣ` symbols are `PA`
axioms transported along `emb` (so they hold in every model of `TAct`, by `eval_reduct_of_mem_PA`);
the congruence axiom of an action constant, `⊤ 🡒 c_a = c_a`, follows from reflexivity. Each case
is closed by the completeness theorem. -/
theorem tact_proves_eqAxiom {φ : Sentence LAct} (h : φ ∈ 𝗘𝗤 LAct) : TAct ⊢ φ := by
  rcases h with _ | _ | _ | @⟨k, f⟩ | @⟨k, r⟩
  · refine Theory.Proof.complete fun s hs₀ ↦ ?_
    have H := eval_reduct_of_mem_PA s hs₀ (eqAxiom_mem_PA Theory.eqAxiom.refl)
    change Semiformula.Eval (s := s.struc) ![] Empty.elim (Theory.Eq.refl LAct)
    simp only [Theory.Eq.refl] at H ⊢
    simp [val_op_eq] at H ⊢; exact H
  · refine Theory.Proof.complete fun s hs₀ ↦ ?_
    have H := eval_reduct_of_mem_PA s hs₀ (eqAxiom_mem_PA Theory.eqAxiom.symm)
    change Semiformula.Eval (s := s.struc) ![] Empty.elim (Theory.Eq.symm LAct)
    simp only [Theory.Eq.symm] at H ⊢
    simp [val_op_eq] at H ⊢; exact H
  · refine Theory.Proof.complete fun s hs₀ ↦ ?_
    have H := eval_reduct_of_mem_PA s hs₀ (eqAxiom_mem_PA Theory.eqAxiom.trans)
    change Semiformula.Eval (s := s.struc) ![] Empty.elim (Theory.Eq.trans LAct)
    simp only [Theory.Eq.trans] at H ⊢
    simp [val_op_eq] at H ⊢; exact H
  · cases f with
    | inl f =>
      refine Theory.Proof.complete fun s hs₀ ↦ ?_
      have H := eval_reduct_of_mem_PA s hs₀ (eqAxiom_mem_PA (Theory.eqAxiom.funcExt f))
      change Semiformula.Eval (s := s.struc) ![] Empty.elim (Theory.Eq.funcExt (Sum.inl f))
      simp only [Theory.Eq.funcExt] at H ⊢
      simp [val_op_eq, Function.comp_def] at H ⊢; exact H
    | inr c =>
      cases c with
      | const a =>
        refine Theory.Proof.complete fun s hs₀ ↦ ?_
        have H := eval_reduct_of_mem_PA s hs₀ (eqAxiom_mem_PA Theory.eqAxiom.refl)
        change Semiformula.Eval (s := s.struc) ![] Empty.elim (Theory.Eq.funcExt (const a))
        simp only [Theory.Eq.refl] at H
        simp only [Theory.Eq.funcExt]
        simp [val_op_eq, Function.comp_def] at H ⊢
        exact H _
  · cases r with
    | inl r =>
      refine Theory.Proof.complete fun s hs₀ ↦ ?_
      have H := eval_reduct_of_mem_PA s hs₀ (eqAxiom_mem_PA (Theory.eqAxiom.relExt r))
      change Semiformula.Eval (s := s.struc) ![] Empty.elim (Theory.Eq.relExt (Sum.inl r))
      simp only [Theory.Eq.relExt] at H ⊢
      simp [val_op_eq, Function.comp_def] at H ⊢; exact H
    | inr e => exact e.elim

/-- `𝗘𝗤 LAct ⪯ TAct`: the prerequisite of Foundation's completeness theorem with equality
(`Theory.Proof.complete_on_eq_models`) for `TAct`. -/
noncomputable instance eqAxiom_weakerThan_TAct : 𝗘𝗤 LAct ⪯ TAct :=
  Entailment.WeakerThan.ofAxm! fun hφ ↦ tact_proves_eqAxiom hφ

end eq

/-! ### The `ℒₒᵣ`-reduct of an `LAct`-structure with equality is a standard structure -/

section model

variable {M : Type*} [Structure LAct M] [Structure.Eq LAct M]

/-- The ring operations read off the `LAct`-structure. -/
@[instance_reducible] def oringOfStructure : ORingStructure M where
  zero := Structure.func (Language.Zero.zero : LAct.Func 0) ![]
  one := Structure.func (Language.One.one : LAct.Func 0) ![]
  add a b := Structure.func (Language.Add.add : LAct.Func 2) ![a, b]
  mul a b := Structure.func (Language.Mul.mul : LAct.Func 2) ![a, b]
  lt a b := Structure.rel (Language.LT.lt : LAct.Rel 2) ![a, b]

/-- With the operations of `oringOfStructure`, the `ℒₒᵣ`-reduct of the `LAct`-structure IS the
standard structure (`standardModel_unique'`; equality by `Structure.Eq LAct M`). -/
lemma lMap_emb_eq_standardModel :
    letI := oringOfStructure (M := M)
    Structure.lMap emb (inferInstance : Structure LAct M) = standardModel M := by
  let _ := oringOfStructure (M := M)
  let _ : Structure ℒₒᵣ M := Structure.lMap emb (inferInstance : Structure LAct M)
  refine standardModel_unique' M (Structure.lMap emb (inferInstance : Structure LAct M))
    ⟨?_⟩ ⟨?_⟩ ⟨?_⟩ ⟨?_⟩ ⟨?_⟩ ⟨?_⟩
  · simp [Semiterm.Operator.val, Semiterm.Operator.Zero.zero, Matrix.empty_eq]; rfl
  · simp [Semiterm.Operator.val, Semiterm.Operator.One.one, Matrix.empty_eq]; rfl
  · intro a b; rfl
  · intro a b; rfl
  · intro a b; exact Structure.Eq.eq (L := LAct) (M := M) a b
  · intro a b; exact Iff.rfl

end model

/-- **Completeness over `TAct`, model-side.** To prove `TAct ⊢ σ` it suffices to prove `σ` in
every `LAct`-structure `S` on a type `M` whose `ℒₒᵣ`-reduct is the standard structure of an
`ORingStructure` modelling `PA` (so every V-generic lemma of the package applies to `M`) and which
satisfies the four action axioms (`axAct`, `axAct'`, `axNe`, `axNe'`). Through
`Theory.Proof.complete_on_eq_models` (equality interpreted as equality) and
`eqAxiom_weakerThan_TAct`. `tact_complete'` below is the same with the model class resolved:
by `structure_eq_of_axAct` such an `S` is `stdActS M` or `swapActS M`. -/
theorem tact_complete (σ : Sentence LAct)
    (H : ∀ (M : Type) [ORingStructure M] (S : Structure LAct M),
      Structure.lMap emb S = standardModel M → [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] →
      Semiformula.Eval (s := S) ![] Empty.elim axAct → Semiformula.Eval (s := S) ![] Empty.elim axAct' →
      Semiformula.Eval (s := S) ![] Empty.elim axNe → Semiformula.Eval (s := S) ![] Empty.elim axNe' →
      Semiformula.Eval (s := S) ![] Empty.elim σ) :
    TAct ⊢ σ := by
  refine Theory.Proof.complete_on_eq_models σ fun M _ S _ hT ↦ ?_
  let _ : ORingStructure M := oringOfStructure (M := M)
  have hS : Structure.lMap emb S = standardModel M := lMap_emb_eq_standardModel (M := M)
  have hPA : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := by
    refine ⟨fun σ₀ hσ₀ ↦ ?_⟩
    have h : M↓[LAct] ⊧ Semiformula.lMap emb σ₀ := hT.models_set (lMap_emb_mem_TAct hσ₀)
    have h' : (Structure.lMap emb S).toStruc ⊧ σ₀ :=
      (Semiformula.models_lMap (s₂ := S) (Φ := emb) (σ := σ₀)).mp h
    rw [hS] at h'
    exact h'
  have hAct : Semiformula.Eval (s := S) ![] Empty.elim axAct := hT.models_set axAct_mem_TAct
  have hAct' : Semiformula.Eval (s := S) ![] Empty.elim axAct' := hT.models_set axAct'_mem_TAct
  have hNe : Semiformula.Eval (s := S) ![] Empty.elim axNe := hT.models_set axNe_mem_TAct
  have hNe' : Semiformula.Eval (s := S) ![] Empty.elim axNe' := hT.models_set axNe'_mem_TAct
  exact H M S hS hAct hAct' hNe hNe'

/-- **Completeness over `TAct`, the two standard readings.** The real-equality models of `TAct`
on `M` are exactly `stdActS M` (`c_C ↦ 0, c_D ↦ 1`) and `swapActS M` (`c_C ↦ 1, c_D ↦ 0`) with
`M ⊧ PA` (`structure_eq_of_axAct`, from the action axiom `axAct`): a sentence true in both, for
every such `M`, is a `TAct`-theorem. -/
theorem tact_complete' (σ : Sentence LAct)
    (H : ∀ (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔],
      Semiformula.Eval (s := stdActS M) ![] Empty.elim σ ∧
      Semiformula.Eval (s := swapActS M) ![] Empty.elim σ) :
    TAct ⊢ σ :=
  tact_complete σ fun M _ S hS _ hAct _ _ _ ↦ by
    rcases structure_eq_of_axAct S hS hAct with rfl | rfl
    · exact (H M).1
    · exact (H M).2

/-! ### Numeral substitution on `LAct` codes -/

section subst

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Foundation's `substNumeralParams 1` over `LAct`: the code `φ` (two free variables) with the
unary numeral of `x` for `#0` and `#0` for `#1` — `subst LAct (numeral x ∷ ^#0 ∷ 0) φ`. -/
noncomputable def substNumeralParamsA (φ x : V) : V := subst LAct (numeral x ∷ ^#0 ∷ 0) φ

/-- The Σ₁ graph of `substNumeralParamsA` (`y φ x`). -/
noncomputable def ssnumParamsA : 𝚺₁.Semisentence 3 := .mkSigma
  “y φ x. ∃ n, !numeralGraph n x ∧ ∃ b, !qqBvarDef b 0 ∧ ∃ v₀, !adjoinDef v₀ b 0 ∧ ∃ v, !adjoinDef v n v₀ ∧
    !(substsGraph LAct) y v φ”

instance substNumeralParamsA.defined :
    𝚺₁-Function₂ (substNumeralParamsA : V → V → V) via ssnumParamsA := .mk fun v ↦ by
  simp [ssnumParamsA, substNumeralParamsA]

instance substNumeralParamsA.definable : 𝚺₁-Function₂ (substNumeralParamsA : V → V → V) :=
  substNumeralParamsA.defined.to_definable

namespace Diag

/-- The `n`-ary form of `ArithS.term_emb_lMap_emb` (`ArithS.Template`, stated at `n = 0`). -/
lemma term_emb_lMap_emb {n : ℕ} (t : ClosedSemiterm ℒₒᵣ n) :
    (Rew.emb (Semiterm.lMap emb t) : SyntacticSemiterm LAct n) = Semiterm.lMap emb (Rew.emb t) := by
  induction t with
  | bvar x => rfl
  | fvar x => exact x.elim
  | func f v ih => simp [Rew.func, Semiterm.lMap_func, Function.comp_def, ih]

/-- The `n`-ary form of `ArithS.typed_val_emb` (`ArithS.Template`, stated at `n = 0`). -/
lemma typed_val_emb {n : ℕ} (t : ClosedSemiterm LAct n) :
    ((⌜(Rew.emb t : SyntacticSemiterm LAct n)⌝ : Bootstrapping.Semiterm V LAct n)).val = (⌜t⌝ : V) := rfl

end Diag

/-- The `LAct` code of the Gödel numeral of `τ` (embedded along `emb`) is `numeral ⌜τ⌝`. -/
lemma quote_lMap_gödel {n m : ℕ} (τ : Semisentence LAct m) :
    (⌜(Semiterm.lMap emb (⌜τ⌝ : ArithmeticSemiterm Empty n) : ClosedSemiterm LAct n)⌝ : V) =
      numeral (⌜τ⌝ : V) := by
  rw [Semiterm.empty_quote_def, Diag.term_emb_lMap_emb, quote_term_lMap_emb, rew_gödelNumber']
  exact congrArg Bootstrapping.Semiterm.val (Sentence.quote_quote_eq_numeral (V := V) (m := n) τ)

/-- **The code equation** (Foundation's `substNumeralParams_app_quote` over `LAct`):
`substNumeralParamsA ⌜σ⌝ ⌜τ⌝` is the code of `σ` with the Gödel numeral of `τ` for `#0` and `#0`
for `#1`. -/
theorem substNumeralParamsA_app_quote (σ τ : Semisentence LAct 2) :
    substNumeralParamsA (⌜σ⌝ : V) ⌜τ⌝ =
      ⌜(σ ⇜ ![Semiterm.lMap emb (⌜τ⌝ : ArithmeticSemiterm Empty 1), #0] : Semisentence LAct 1)⌝ := by
  unfold substNumeralParamsA
  conv_rhs =>
    rw [Sentence.quote_def, Semiformula.coe_subst_eq_subst_coe, Semiformula.quote_def,
      Semiformula.typed_quote_substs, Bootstrapping.Semiformula.val_substs, ← Semiformula.quote_def,
      ← Sentence.quote_def]
  congr 1
  have hv : (fun i ↦ (⌜(Rew.emb (![Semiterm.lMap emb (⌜τ⌝ : ArithmeticSemiterm Empty 1), #0] i) :
      SyntacticSemiterm LAct 1)⌝ : Bootstrapping.Semiterm V LAct 1)) =
      ![⌜(Rew.emb (Semiterm.lMap emb (⌜τ⌝ : ArithmeticSemiterm Empty 1)) : SyntacticSemiterm LAct 1)⌝,
        ⌜(Rew.emb (#0 : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝] := by
    funext i; fin_cases i <;> rfl
  rw [hv]
  simp only [SemitermVec.val_cons, SemitermVec.val_nil, Diag.typed_val_emb, quote_lMap_gödel]
  rfl

end subst

/-! ### The diagonal construction over `LAct` -/

section diag

/-- Foundation's `parameterizedDiag` at one parameter, over `LAct`:
`tactDiag θ = “x k. ∀ y, ssnumParamsA y x x → θ y k”`, i.e.
`∀¹ (ssnumParamsA ⇜ ![#0, #1, #1] 🡒 θ ⇜ ![#0, #2])` (`#0` the code slot, `#1` the parameter). -/
noncomputable def tactDiag (θ : Semisentence LAct 2) : Semisentence LAct 2 :=
  ∀¹ ((Semiformula.lMap emb (ssnumParamsA.val : Semisentence ℒₒᵣ 3)) ⇜ ![#0, #1, #1] 🡒 θ ⇜ ![#0, #2])

/-- Foundation's `parameterizedFixedpoint` over `LAct`: `tactDiag θ` with its own Gödel numeral in
the code slot. -/
noncomputable def tactFixedpoint (θ : Semisentence LAct 2) : Semisentence LAct 1 :=
  (tactDiag θ) ⇜ ![Semiterm.lMap emb (⌜tactDiag θ⌝ : ArithmeticSemiterm Empty 1), #0]

lemma tactFixedpoint_def (θ : Semisentence LAct 2) :
    tactFixedpoint θ =
      (tactDiag θ) ⇜ ![Semiterm.lMap emb (⌜tactDiag θ⌝ : ArithmeticSemiterm Empty 1), #0] := rfl

variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The graph formula, read in an `LAct`-structure whose reduct is standard. -/
lemma eval_ssnumParamsA (S : Structure LAct M) (hS : Structure.lMap emb S = standardModel M)
    (v : Fin 3 → M) :
    Semiformula.Eval (s := S) v Empty.elim (Semiformula.lMap emb (ssnumParamsA.val : Semisentence ℒₒᵣ 3)) ↔
      v 0 = substNumeralParamsA (v 1) (v 2) := by
  rw [Semiformula.eval_lMap, hS]
  exact (substNumeralParamsA.defined (V := M)).iff

/-- The embedded Gödel numeral of `σ` denotes the code `⌜σ⌝` in `M`. -/
lemma val_lMap_gödel (S : Structure LAct M) (hS : Structure.lMap emb S = standardModel M) {n m : ℕ}
    (σ : Semisentence LAct m) (b : Fin n → M) :
    Semiterm.val (s := S) b Empty.elim (Semiterm.lMap emb (⌜σ⌝ : ArithmeticSemiterm Empty n)) = (⌜σ⌝ : M) := by
  rw [Semiterm.val_lMap, hS]
  simp

/-- The valuation of the substitution vector `![⌜σ⌝, #0]` at `p` (stated for a VARIABLE `σ`, so
that no quote of a closed formula is ever unfolded). -/
lemma val_vec_gödel (S : Structure LAct M) (hS : Structure.lMap emb S = standardModel M) {m : ℕ}
    (σ : Semisentence LAct m) (p : M) :
    (Semiterm.val (s := S) (p :> ![]) Empty.elim ∘
      ![Semiterm.lMap emb (⌜σ⌝ : ArithmeticSemiterm Empty 1), #0]) = ![(⌜σ⌝ : M), p] := by
  funext i; fin_cases i
  · exact val_lMap_gödel S hS σ _
  · rfl

/-- `tactDiag θ` at `(x, p)` says `θ (substNumeralParamsA x x) p`. -/
lemma eval_tactDiag (S : Structure LAct M) (hS : Structure.lMap emb S = standardModel M)
    (θ : Semisentence LAct 2) (x p : M) :
    Semiformula.Eval (s := S) ![x, p] Empty.elim (tactDiag θ) ↔
      Semiformula.Eval (s := S) ![substNumeralParamsA x x, p] Empty.elim θ := by
  unfold tactDiag
  simp only [Semiformula.eval_all, LogicalConnective.HomClass.map_imply, LogicalConnective.Prop.arrow_eq,
    Semiformula.eval_substs, eval_ssnumParamsA S hS]
  simp

/-- **The parametric diagonal lemma over `TAct`** (Foundation's `parameterized_diagonal₁`
transported to `LAct`): `TAct ⊢ ∀ k, ψ(k) ↔ θ(⌜ψ⌝, k)` for `ψ := tactFixedpoint θ`, the numeral
`⌜ψ⌝` being Foundation's unary Gödel numeral embedded along `emb`. By `tact_complete`: in every
model, `ψ(p) ↔ tactDiag θ (⌜tactDiag θ⌝, p) ↔ θ (substNumeralParamsA ⌜tactDiag θ⌝ ⌜tactDiag θ⌝, p)`
and the code equation identifies the last argument with `⌜ψ⌝`. -/
theorem tact_parametric_diagonal₁ (θ : Semisentence LAct 2) :
    TAct ⊢ ∀¹ (tactFixedpoint θ 🡘
      θ ⇜ ![Semiterm.lMap emb (⌜tactFixedpoint θ⌝ : ArithmeticSemiterm Empty 1), #0]) := by
  refine tact_complete _ fun M _ S hS _ _ _ _ _ ↦ ?_
  have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
  have ht : substNumeralParamsA (⌜tactDiag θ⌝ : M) ⌜tactDiag θ⌝ = ⌜tactFixedpoint θ⌝ := by
    rw [tactFixedpoint_def]
    exact substNumeralParamsA_app_quote (V := M) (tactDiag θ) (tactDiag θ)
  simp only [Semiformula.eval_all, LogicalConnective.HomClass.map_iff, LogicalConnective.Prop.iff_eq]
  intro p
  have e₁ := val_vec_gödel S hS (tactDiag θ) p
  have e₂ := val_vec_gödel S hS (tactFixedpoint θ) p
  have hL : Semiformula.Eval (s := S) (p :> ![]) Empty.elim (tactFixedpoint θ) ↔
      Semiformula.Eval (s := S) ![(⌜tactDiag θ⌝ : M), p] Empty.elim (tactDiag θ) := by
    rw [tactFixedpoint_def, Semiformula.eval_substs, e₁]
  rw [hL, Semiformula.eval_substs, e₂, eval_tactDiag S hS, ht]

/-- **The parametric diagonal lemma over `TAct`, existential form**: for every
`θ : Semisentence LAct 2` there is `ψ : Semisentence LAct 1` with
`TAct ⊢ ∀¹ (ψ 🡘 θ ⇜ ![lMap emb ⌜ψ⌝, #0])`. Witness: `tactFixedpoint θ`. -/
theorem tact_parametric_diagonal (θ : Semisentence LAct 2) :
    ∃ ψ : Semisentence LAct 1,
      TAct ⊢ ∀¹ (ψ 🡘 θ ⇜ ![Semiterm.lMap emb (⌜ψ⌝ : ArithmeticSemiterm Empty 1), #0]) :=
  ⟨tactFixedpoint θ, tact_parametric_diagonal₁ θ⟩

end diag

/-! ### Instances at the binary numeral — the code-level reading -/

section inst

/-- **The fixed point at the binary numeral of `k`**: `∀`-elimination of
`tact_parametric_diagonal₁` at `lMap emb (bnumT k)`. On codes (`quote_instB`), the left sentence
is `instB ⌜tactFixedpoint θ⌝ k` and the right one `instB ⌜θ ⇜ ![lMap emb ⌜tactFixedpoint θ⌝, #0]⌝ k`. -/
theorem tact_parametric_diagonal_inst (θ : Semisentence LAct 2) (k : ℕ) :
    TAct ⊢ (tactFixedpoint θ ⇜ ![Semiterm.lMap emb (bnumT k)]) 🡘
      ((θ ⇜ ![Semiterm.lMap emb (⌜tactFixedpoint θ⌝ : ArithmeticSemiterm Empty 1), #0]) ⇜
        ![Semiterm.lMap emb (bnumT k)]) := by
  have h := Theory.Proof.specialize (T := TAct)
    (tactFixedpoint θ 🡘 θ ⇜ ![Semiterm.lMap emb (⌜tactFixedpoint θ⌝ : ArithmeticSemiterm Empty 1), #0])
    (Semiterm.lMap emb (bnumT k))
  have h' := Entailment.mdp h (tact_parametric_diagonal₁ θ)
  simpa only [LogicalConnective.HomClass.map_iff] using h'

/-- The instance holds in every model of `TAct` (soundness). -/
theorem models_tact_parametric_diagonal_inst {M : Type*} [Nonempty M] [Structure LAct M]
    [M↓[LAct] ⊧* TAct] (θ : Semisentence LAct 2) (k : ℕ) :
    M↓[LAct] ⊧ (tactFixedpoint θ ⇜ ![Semiterm.lMap emb (bnumT k)]) ↔
      M↓[LAct] ⊧ ((θ ⇜ ![Semiterm.lMap emb (⌜tactFixedpoint θ⌝ : ArithmeticSemiterm Empty 1), #0]) ⇜
        ![Semiterm.lMap emb (bnumT k)]) := by
  have := models_of_provable (M := M) inferInstance (tact_parametric_diagonal_inst θ k)
  simpa [models_iff] using this

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The instance is internally provable in every model of `IΣ₁` (D1): `TAct` proves, on codes,
that the `bnum k`-instance of the fixed point and the `bnum k`-instance of its unfolding are
equivalent. -/
theorem provable_code_parametric_diagonal_inst (θ : Semisentence LAct 2) (k : ℕ) :
    Provable TAct (⌜((tactFixedpoint θ ⇜ ![Semiterm.lMap emb (bnumT k)]) 🡘
      ((θ ⇜ ![Semiterm.lMap emb (⌜tactFixedpoint θ⌝ : ArithmeticSemiterm Empty 1), #0]) ⇜
        ![Semiterm.lMap emb (bnumT k)]) : Sentence LAct)⌝ : V) :=
  internalize_provability (V := V) (tact_parametric_diagonal_inst θ k)

end inst

end ArithS
