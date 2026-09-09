import ArithS.EvalN
import ArithS.Guard
import ArithS.Symmetry

/-!
# ArithS.Template — the guard template "opp plays `a` against me", as a sentence and as a code

The RESTRICTED template (the only one the red cell needs): `gtmpl` is the `ℒₒᵣ`-semisentence
with seven free variables

  `x₁ u₁ w₁ x₂ u₂ w₂ t ↦ ∃ n, EvalGraph n (relabel u₂ w₂ x₂) (relabel u₁ w₁ x₁) (relabel u₂ w₂ x₂) t`

("the program described by `(x₂, u₂, w₂)`, playing against the one described by `(x₁, u₁, w₁)`,
plays `t`"). Filling it with the canonical descriptions of `me`, `opp` and the action `a`
(`ArithS.Guard`) gives the meta sentence `guardSentence me opp a : Sentence LAct`, whose code
is `guardCode ⌜Gtmpl⌝ me opp a` (the code equation), which the transposition `swap` sends to
`guardSentence (swapcode me) (swapcode opp) (swapAct a)` (the swap equation), and which is
true in `ℕ` iff `∃ n, EvalGraph n opp me opp a` (the truth equation).
-/

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open LAct

/-! ### The template -/

/-- "The program described by `(x₂, u₂, w₂)` plays `t` against the one described by `(x₁, u₁, w₁)`". -/
noncomputable def gtmpl : 𝚺₁.Semisentence 7 := .mkSigma
  “x₁ u₁ w₁ x₂ u₂ w₂ t. ∃ me, !relabelDef me u₁ w₁ x₁ ∧ ∃ opp, !relabelDef opp u₂ w₂ x₂ ∧
    ∃ n, !evalGraphDef n opp me opp t”

section eval

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

lemma eval_gtmpl (v : Fin 7 → V) :
    V ⊧/v gtmpl.val ↔
    ∃ n, EvalGraph n (relabel (v 4) (v 5) (v 3)) (relabel (v 1) (v 2) (v 0)) (relabel (v 4) (v 5) (v 3)) (v 6) := by
  simp [gtmpl, HierarchySymbol.Semiformula.val_sigma, evalGraph_defined.df]

end eval

/-- The template over `LAct`. -/
noncomputable def Gtmpl : Semisentence LAct 7 := Semiformula.lMap emb gtmpl.val

lemma lMap_swap_Gtmpl : Semiformula.lMap swap Gtmpl = Gtmpl := lMap_swap_emb _

/-! ### The description terms -/

/-- The numeral `k`, as an `LAct`-term. -/
noncomputable def numT (k : ℕ) : ClosedSemiterm LAct 0 := Semiterm.lMap emb (↑k : ClosedSemiterm ℒₒᵣ 0)

/-- The canonical numeral of the orbit of `x`. -/
noncomputable def dnumT (x : ℕ) : ClosedSemiterm LAct 0 := numT (dnum x)

/-- First re-valuation term: `c_C` if `x` is canonical, `c_D` if `swapcode x` is, `0` on a tie. -/
noncomputable def dUT (x : ℕ) : ClosedSemiterm LAct 0 :=
  if x < swapcode x then cterm Act.C else if swapcode x < x then cterm Act.D else numT 0

/-- Second re-valuation term. -/
noncomputable def dWT (x : ℕ) : ClosedSemiterm LAct 0 :=
  if x < swapcode x then cterm Act.D else if swapcode x < x then cterm Act.C else numT 1

/-- The action term: `c_a` for `a ∈ {0, 1}`. -/
noncomputable def actT (a : ℕ) : ClosedSemiterm LAct 0 :=
  if a = 0 then cterm Act.C else if a = 1 then cterm Act.D else numT a

noncomputable def descTerms (me opp a : ℕ) : Fin 7 → ClosedSemiterm LAct 0 :=
  ![dnumT me, dUT me, dWT me, dnumT opp, dUT opp, dWT opp, actT a]

/-- The guard sentence: the template filled with the descriptions. -/
noncomputable def guardSentence (me opp a : ℕ) : Sentence LAct := Gtmpl ⇜ descTerms me opp a

/-! ### The swap equation -/

lemma lMap_swap_numT (k : ℕ) : Semiterm.lMap swap (numT k) = numT k := term_lMap_swap_emb _

section dnum

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

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

lemma lMap_swap_dUT (x : ℕ) : Semiterm.lMap swap (dUT x) = dUT (swapcode x) := by
  unfold dUT
  rw [swapcode_swapcode]
  generalize swapcode x = s
  rcases lt_trichotomy x s with h | h | h
  · rw [if_pos h, if_neg (lt_asymm h), if_pos h, lMap_swap_cterm_C]
  · subst h; simp [lMap_swap_numT]
  · rw [if_neg (lt_asymm h), if_pos h, if_pos h, lMap_swap_cterm_D]

lemma lMap_swap_dWT (x : ℕ) : Semiterm.lMap swap (dWT x) = dWT (swapcode x) := by
  unfold dWT
  rw [swapcode_swapcode]
  generalize swapcode x = s
  rcases lt_trichotomy x s with h | h | h
  · rw [if_pos h, if_neg (lt_asymm h), if_pos h, lMap_swap_cterm_D]
  · subst h; simp [lMap_swap_numT]
  · rw [if_neg (lt_asymm h), if_pos h, if_pos h, lMap_swap_cterm_C]

lemma lMap_swap_actT (a : ℕ) : Semiterm.lMap swap (actT a) = actT (swapAct a) := by
  unfold actT swapAct relabelAct
  by_cases h0 : a = 0
  · subst h0; simp [lMap_swap_cterm_C]
  · by_cases h1 : a = 1
    · subst h1; simp [lMap_swap_cterm_D]
    · simp [h0, h1, lMap_swap_numT]

lemma lMap_swap_dnumT (x : ℕ) : Semiterm.lMap swap (dnumT x) = dnumT (swapcode x) := by
  unfold dnumT; rw [lMap_swap_numT, dnum_swapcode]

/-- **The swap equation**: the transposition of the guard sentence is the guard sentence of the
transposed data. -/
theorem lMap_swap_guardSentence (me opp a : ℕ) :
    Semiformula.lMap swap (guardSentence me opp a) = guardSentence (swapcode me) (swapcode opp) (swapAct a) := by
  unfold guardSentence
  rw [Semiformula.lMap_subst, lMap_swap_Gtmpl]
  congr 1
  funext i
  fin_cases i <;> simp [descTerms, lMap_swap_dnumT, lMap_swap_dUT, lMap_swap_dWT, lMap_swap_actT]

/-! ### The code equation -/

section codes

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

lemma quote_Gtmpl : (⌜Gtmpl⌝ : V) = ⌜gtmpl.val⌝ := by
  unfold Gtmpl
  rw [Sentence.quote_def, Sentence.quote_def, ← Semiformula.lMap_emb, quote_lMap_emb]

lemma term_emb_lMap_emb (t : ClosedSemiterm ℒₒᵣ 0) :
    (Rew.emb (Semiterm.lMap emb t) : SyntacticSemiterm LAct 0) = Semiterm.lMap emb (Rew.emb t) := by
  induction t with
  | bvar x => rfl
  | fvar x => exact x.elim
  | func f v ih => simp [Rew.func, Semiterm.lMap_func, Function.comp_def, ih]

lemma quote_numT (k : ℕ) : (⌜numT k⌝ : V) = numeral (k : V) := by
  unfold numT
  rw [Semiterm.empty_quote_def, term_emb_lMap_emb, quote_term_lMap_emb, ← Semiterm.empty_quote_def]
  change ((⌜(↑k : ClosedSemiterm ℒₒᵣ 0)⌝ : Bootstrapping.Semiterm V ℒₒᵣ 0)).val = _
  rw [Semiterm.empty_typed_quote_numeral_eq_numeral]
  rfl

lemma encode_const_C : Encodable.encode (const Act.C) = 2 := rfl
lemma encode_const_D : Encodable.encode (const Act.D) = 3 := rfl

lemma quote_cterm_C : (⌜(cterm Act.C : ClosedSemiterm LAct 0)⌝ : V) = csym 0 := by
  rw [Semiterm.empty_quote_def]
  unfold cterm csym
  rw [Rew.func, Semiterm.quote_func, quote_func_def, SemitermVec.val_nil, encode_const_C]
  simp

lemma quote_cterm_D : (⌜(cterm Act.D : ClosedSemiterm LAct 0)⌝ : V) = csym 1 := by
  rw [Semiterm.empty_quote_def]
  unfold cterm csym
  rw [Rew.func, Semiterm.quote_func, quote_func_def, SemitermVec.val_nil, encode_const_D]
  simp
  norm_num

end codes

lemma quote_dnumT (x : ℕ) : (⌜dnumT x⌝ : ℕ) = numeral (dnum x) := by
  unfold dnumT; rw [quote_numT]; simp

lemma quote_dUT (x : ℕ) : (⌜dUT x⌝ : ℕ) = dU x := by
  unfold dUT dU
  generalize swapcode x = s
  rcases lt_trichotomy x s with h | h | h
  · rw [if_pos h, if_pos h, quote_cterm_C]
  · subst h; simp [quote_numT]
  · rw [if_neg (lt_asymm h), if_pos h, if_neg (lt_asymm h), if_pos h, quote_cterm_D]

lemma quote_dWT (x : ℕ) : (⌜dWT x⌝ : ℕ) = dW x := by
  unfold dWT dW
  generalize swapcode x = s
  rcases lt_trichotomy x s with h | h | h
  · rw [if_pos h, if_pos h, quote_cterm_D]
  · subst h; simp [quote_numT]
  · rw [if_neg (lt_asymm h), if_pos h, if_neg (lt_asymm h), if_pos h, quote_cterm_C]

lemma quote_actT (a : ℕ) : (⌜actT a⌝ : ℕ) = actTermCode a := by
  unfold actT actTermCode
  by_cases h0 : a = 0
  · subst h0; simp [quote_cterm_C]
  · by_cases h1 : a = 1
    · subst h1; simp [quote_cterm_D]
    · simp [h0, h1, quote_numT]

lemma typed_val_emb (t : ClosedSemiterm LAct 0) :
    ((⌜(Rew.emb t : SyntacticSemiterm LAct 0)⌝ : Bootstrapping.Semiterm ℕ LAct 0)).val = (⌜t⌝ : ℕ) := rfl

/-- The codes of the description terms form the description vector. -/
lemma semitermVec_val_descTerms (me opp a : ℕ) :
    SemitermVec.val (fun i ↦ (⌜(Rew.emb (descTerms me opp a i) : SyntacticSemiterm LAct 0)⌝ :
      Bootstrapping.Semiterm ℕ LAct 0)) = descVec me opp a := by
  have hv : (fun i ↦ (⌜(Rew.emb (descTerms me opp a i) : SyntacticSemiterm LAct 0)⌝ :
      Bootstrapping.Semiterm ℕ LAct 0)) =
      ![⌜(Rew.emb (dnumT me) : SyntacticSemiterm LAct 0)⌝, ⌜(Rew.emb (dUT me) : SyntacticSemiterm LAct 0)⌝,
        ⌜(Rew.emb (dWT me) : SyntacticSemiterm LAct 0)⌝, ⌜(Rew.emb (dnumT opp) : SyntacticSemiterm LAct 0)⌝,
        ⌜(Rew.emb (dUT opp) : SyntacticSemiterm LAct 0)⌝, ⌜(Rew.emb (dWT opp) : SyntacticSemiterm LAct 0)⌝,
        ⌜(Rew.emb (actT a) : SyntacticSemiterm LAct 0)⌝] := by
    funext i; fin_cases i <;> rfl
  rw [hv]
  simp only [SemitermVec.val_cons, SemitermVec.val_nil, typed_val_emb, quote_dnumT, quote_dUT, quote_dWT,
    quote_actT]
  rfl

/-- **The code equation**: the code of the guard sentence is the guard code of the template's code. -/
theorem quote_guardSentence (me opp a : ℕ) :
    (⌜guardSentence me opp a⌝ : ℕ) = guardCode (⌜Gtmpl⌝ : ℕ) me opp a := by
  unfold guardSentence guardCode
  rw [Sentence.quote_def, Semiformula.coe_subst_eq_subst_coe, Semiformula.quote_def,
    Semiformula.typed_quote_substs, Bootstrapping.Semiformula.val_substs, ← Semiformula.quote_def,
    ← Sentence.quote_def]
  congr 1
  exact semitermVec_val_descTerms me opp a

/-! ### The truth equation -/

section truth

lemma val_numT (k : ℕ) : (numT k).val (s := stdAct) ![] Empty.elim = k := by
  unfold numT
  rw [Semiterm.val_lMap, stdAct_lMap_emb]
  simp

lemma val_cterm_C : (cterm Act.C : ClosedSemiterm LAct 0).val (s := stdAct) ![] Empty.elim = 0 := rfl
lemma val_cterm_D : (cterm Act.D : ClosedSemiterm LAct 0).val (s := stdAct) ![] Empty.elim = 1 := rfl

lemma val_dnumT (x : ℕ) : (dnumT x).val (s := stdAct) ![] Empty.elim = dnum x := val_numT _

/-- The descriptions reconstruct the program. -/
lemma relabel_val_desc (x : ℕ) :
    relabel ((dUT x).val (s := stdAct) ![] Empty.elim) ((dWT x).val (s := stdAct) ![] Empty.elim) (dnum x) = x := by
  rcases lt_trichotomy x (swapcode x) with h | h | h
  · unfold dUT dWT
    rw [if_pos h, if_pos h, dnum_of_lt h, val_cterm_C, val_cterm_D, relabel_zero_one]
  · unfold dUT dWT
    have hs : swapcode x = x := h.symm
    rw [hs, if_neg (_root_.lt_irrefl _), if_neg (_root_.lt_irrefl _), if_neg (_root_.lt_irrefl _),
      if_neg (_root_.lt_irrefl _), dnum_of_eq h, val_numT, val_numT, relabel_zero_one]
  · unfold dUT dWT
    rw [if_neg (lt_asymm h), if_pos h, if_neg (lt_asymm h), if_pos h, dnum_of_gt h, val_cterm_D, val_cterm_C]
    exact swapcode_swapcode x

lemma val_actT (a : ℕ) : (actT a).val (s := stdAct) ![] Empty.elim = a := by
  unfold actT
  by_cases h0 : a = 0
  · subst h0; simp [val_cterm_C]
  · by_cases h1 : a = 1
    · subst h1; simp [val_cterm_D]
    · simp [h0, h1, val_numT]

/-- **The truth equation**: the guard sentence holds in `ℕ` iff `opp` plays `a` against `me`. -/
theorem models_guardSentence_iff (me opp a : ℕ) :
    ℕ↓[LAct] ⊧ guardSentence me opp a ↔ ∃ n, EvalGraph n opp me opp a := by
  rw [models_iff]
  unfold guardSentence Gtmpl Semiformula.Realize
  rw [Semiformula.eval_substs, Semiformula.eval_lMap, stdAct_lMap_emb]
  have h0 : (Semiterm.val (s := stdAct) ![] Empty.elim ∘ descTerms me opp a) =
      ![dnum me, (dUT me).val (s := stdAct) ![] Empty.elim, (dWT me).val (s := stdAct) ![] Empty.elim,
        dnum opp, (dUT opp).val (s := stdAct) ![] Empty.elim, (dWT opp).val (s := stdAct) ![] Empty.elim, a] := by
    funext i; fin_cases i <;> simp [descTerms, val_dnumT, val_actT]
  rw [h0]
  refine (eval_gtmpl (V := ℕ) _).trans ?_
  simp [relabel_val_desc]

end truth

end ArithS
