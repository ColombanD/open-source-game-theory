import ArithS.Eval.EvalN
import ArithS.Agents.Guard
import ArithS.Theory.Symmetry

/-!
# ArithS.Template — the guard template "opp plays `a` against me", as a sentence and as a code

The RESTRICTED template (the only one the red cell needs): `guardTemplateRaw` is the `ℒₒᵣ`-semisentence
with seven free variables

  `x₁ u₁ w₁ x₂ u₂ w₂ t ↦ ∃ n, EvalGraph n (revalue u₂ w₂ x₂) (revalue u₁ w₁ x₁) (revalue u₂ w₂ x₂) t`

("the program described by `(x₂, u₂, w₂)`, playing against the one described by `(x₁, u₁, w₁)`,
plays `t`"). Since roadmap M3 step (a) a search node stores a SIX-variable template: the two
CLOSED INSTANCES `guardTemplate a := guardTemplate7 ⇜ ![#0, …, #5, c_a]` (the action term substituted, the
six description variables kept) are the templates of the two searchers. Filling `guardTemplate a`
with the canonical descriptions of `me` and `opp` (`ArithS.Guard`; the program terms are the
structural `codeTermMeta` of `ArithS.CodeTerm`) gives the meta sentence `guardSentence a me opp : Sentence LAct`,
whose code is `guardCode ⌜guardTemplate a⌝ me opp` (the code equation), which the transposition
`swap` sends to `guardSentence (swapAction a) (transposeCode me) (transposeCode opp)` (the swap equation;
on the templates `lMap swap (guardTemplate a) = guardTemplate (swapAction a)`, hence on codes
`revalueTemplate 1 0 ⌜guardTemplate a⌝ = ⌜guardTemplate (swapAction a)⌝` by the meta link of
`ArithS.RevalueTemplate`), and which is true in `ℕ` iff `∃ n, EvalGraph n opp me opp a`
(the truth equation).
-/

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open LAct

/-! ### The template -/

/-- "The program described by `(x₂, u₂, w₂)` plays `t` against the one described by `(x₁, u₁, w₁)`". -/
noncomputable def guardTemplateRaw : 𝚺₁.Semisentence 7 := .mkSigma
  “x₁ u₁ w₁ x₂ u₂ w₂ t. ∃ me, !revalueDef me u₁ w₁ x₁ ∧ ∃ opp, !revalueDef opp u₂ w₂ x₂ ∧
    ∃ n, !evalGraphDef n opp me opp t”

section eval

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

lemma eval_guardTemplateRaw (v : Fin 7 → V) :
    V ⊧/v guardTemplateRaw.val ↔
    ∃ n, EvalGraph n (revalue (v 4) (v 5) (v 3)) (revalue (v 1) (v 2) (v 0)) (revalue (v 4) (v 5) (v 3)) (v 6) := by
  simp [guardTemplateRaw, HierarchySymbol.Semiformula.val_sigma, evalGraph_defined.df]

end eval

/-- The template over `LAct`. -/
noncomputable def guardTemplate7 : Semisentence LAct 7 := Semiformula.lMap emb guardTemplateRaw.val

lemma lMap_swap_guardTemplate7 : Semiformula.lMap swap guardTemplate7 = guardTemplate7 := lMap_swap_emb _

/-! ### The description terms -/

/-- The numeral `k`, as an `LAct`-term. -/
noncomputable def numT (k : ℕ) : ClosedSemiterm LAct 0 := Semiterm.lMap emb (↑k : ClosedSemiterm ℒₒᵣ 0)

/-- The canonical code of the orbit of `x`, as the STRUCTURAL TERM of the code (`ArithS.CodeTerm`:
`ppair`-nested binary numerals of the leaves). -/
noncomputable def canonicalMeta (x : ℕ) : ClosedSemiterm LAct 0 := Semiterm.lMap emb (codeTermMeta (canonical x))

/-- First re-valuation term: `c_C` if `x` is canonical, `c_D` if `transposeCode x` is, `0` on a tie. -/
noncomputable def revalueUMeta (x : ℕ) : ClosedSemiterm LAct 0 :=
  if x < transposeCode x then cterm Act.C else if transposeCode x < x then cterm Act.D else numT 0

/-- Second re-valuation term. -/
noncomputable def revalueWMeta (x : ℕ) : ClosedSemiterm LAct 0 :=
  if x < transposeCode x then cterm Act.D else if transposeCode x < x then cterm Act.C else numT 1

/-- The action term: `c_a` for `a ∈ {0, 1}`. -/
noncomputable def actT (a : ℕ) : ClosedSemiterm LAct 0 :=
  if a = 0 then cterm Act.C else if a = 1 then cterm Act.D else numT a

/-- The action term lifted to six bound variables (the slot of `guardTemplate`). -/
noncomputable def actT6 (a : ℕ) : Semiterm LAct Empty 6 := Rew.castLE (Nat.zero_le 6) (actT a)

/-- The closed template instance: the action term `c_a` substituted for the seventh variable,
the six description variables kept. -/
noncomputable def guardTemplate (a : ℕ) : Semisentence LAct 6 :=
  guardTemplate7 ⇜ ![#0, #1, #2, #3, #4, #5, actT6 a]

/-- The six description terms of `me` and `opp`. -/
noncomputable def descriptionTerms (me opp : ℕ) : Fin 6 → ClosedSemiterm LAct 0 :=
  ![canonicalMeta me, revalueUMeta me, revalueWMeta me, canonicalMeta opp, revalueUMeta opp, revalueWMeta opp]

/-- The guard sentence of the action `a`: the template instance filled with the descriptions. -/
noncomputable def guardSentence (a me opp : ℕ) : Sentence LAct := guardTemplate a ⇜ descriptionTerms me opp

/-! ### The swap equation -/

lemma lMap_swap_numT (k : ℕ) : Semiterm.lMap swap (numT k) = numT k := term_lMap_swap_emb _

lemma lMap_swap_revalueUMeta (x : ℕ) : Semiterm.lMap swap (revalueUMeta x) = revalueUMeta (transposeCode x) := by
  unfold revalueUMeta
  rw [transposeCode_transposeCode]
  generalize transposeCode x = s
  rcases lt_trichotomy x s with h | h | h
  · rw [if_pos h, if_neg (lt_asymm h), if_pos h, lMap_swap_cterm_C]
  · subst h; simp [lMap_swap_numT]
  · rw [if_neg (lt_asymm h), if_pos h, if_pos h, lMap_swap_cterm_D]

lemma lMap_swap_revalueWMeta (x : ℕ) : Semiterm.lMap swap (revalueWMeta x) = revalueWMeta (transposeCode x) := by
  unfold revalueWMeta
  rw [transposeCode_transposeCode]
  generalize transposeCode x = s
  rcases lt_trichotomy x s with h | h | h
  · rw [if_pos h, if_neg (lt_asymm h), if_pos h, lMap_swap_cterm_D]
  · subst h; simp [lMap_swap_numT]
  · rw [if_neg (lt_asymm h), if_pos h, if_pos h, lMap_swap_cterm_C]

lemma lMap_swap_actT (a : ℕ) : Semiterm.lMap swap (actT a) = actT (swapAction a) := by
  unfold actT swapAction revalueAction
  by_cases h0 : a = 0
  · subst h0; simp [lMap_swap_cterm_C]
  · by_cases h1 : a = 1
    · subst h1; simp [lMap_swap_cterm_D]
    · simp [h0, h1, lMap_swap_numT]

lemma lMap_swap_canonicalMeta (x : ℕ) : Semiterm.lMap swap (canonicalMeta x) = canonicalMeta (transposeCode x) := by
  unfold canonicalMeta; rw [term_lMap_swap_emb, canonical_transposeCode]

lemma lMap_swap_actT6 (a : ℕ) : Semiterm.lMap swap (actT6 a) = actT6 (swapAction a) := by
  unfold actT6
  change Semiterm.lMap swap (Rew.map (Fin.castLE (Nat.zero_le 6)) id (actT a)) =
    Rew.map (Fin.castLE (Nat.zero_le 6)) id (actT (swapAction a))
  rw [Semiterm.lMap_map, lMap_swap_actT]

/-- **The template swap**: the transposition of the instance of `a` is the instance of `swapAction a`. -/
theorem lMap_swap_GtmplA (a : ℕ) : Semiformula.lMap swap (guardTemplate a) = guardTemplate (swapAction a) := by
  unfold guardTemplate
  rw [Semiformula.lMap_subst, lMap_swap_guardTemplate7]
  congr 1
  funext i
  fin_cases i <;> simp [lMap_swap_actT6]

/-- **The swap equation**: the transposition of the guard sentence is the guard sentence of the
transposed data. -/
theorem lMap_swap_guardSentence (a me opp : ℕ) :
    Semiformula.lMap swap (guardSentence a me opp) =
    guardSentence (swapAction a) (transposeCode me) (transposeCode opp) := by
  unfold guardSentence
  rw [Semiformula.lMap_subst, lMap_swap_GtmplA]
  congr 1
  funext i
  fin_cases i <;> simp [descriptionTerms, lMap_swap_canonicalMeta, lMap_swap_revalueUMeta, lMap_swap_revalueWMeta]

/-- **The template swap on codes**: the code-level τ sends the code of `guardTemplate a` to the code of
`guardTemplate (swapAction a)`. -/
theorem revalueTemplate_quote_GtmplA (a : ℕ) :
    revalueTemplate 1 0 (⌜guardTemplate a⌝ : ℕ) = ⌜guardTemplate (swapAction a)⌝ := by
  rw [revalueTemplate_quote_sentence, lMap_swap_GtmplA]

/-! ### The code equation -/

section codes

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

lemma quote_guardTemplate7 : (⌜guardTemplate7⌝ : V) = ⌜guardTemplateRaw.val⌝ := by
  unfold guardTemplate7
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

lemma quote_canonicalMeta (x : ℕ) : (⌜canonicalMeta x⌝ : ℕ) = codeTerm (canonical x) := by
  unfold canonicalMeta
  rw [Semiterm.empty_quote_def, term_emb_lMap_emb, quote_term_lMap_emb, ← Semiterm.empty_quote_def,
    quote_codeTermMeta_nat]

lemma quote_revalueUMeta (x : ℕ) : (⌜revalueUMeta x⌝ : ℕ) = revalueU x := by
  unfold revalueUMeta revalueU
  generalize transposeCode x = s
  rcases lt_trichotomy x s with h | h | h
  · rw [if_pos h, if_pos h, quote_cterm_C]
  · subst h; simp [quote_numT]
  · rw [if_neg (lt_asymm h), if_pos h, if_neg (lt_asymm h), if_pos h, quote_cterm_D]

lemma quote_revalueWMeta (x : ℕ) : (⌜revalueWMeta x⌝ : ℕ) = revalueW x := by
  unfold revalueWMeta revalueW
  generalize transposeCode x = s
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
lemma semitermVec_val_descriptionTerms (me opp : ℕ) :
    SemitermVec.val (fun i ↦ (⌜(Rew.emb (descriptionTerms me opp i) : SyntacticSemiterm LAct 0)⌝ :
      Bootstrapping.Semiterm ℕ LAct 0)) = descriptions me opp := by
  have hv : (fun i ↦ (⌜(Rew.emb (descriptionTerms me opp i) : SyntacticSemiterm LAct 0)⌝ :
      Bootstrapping.Semiterm ℕ LAct 0)) =
      ![⌜(Rew.emb (canonicalMeta me) : SyntacticSemiterm LAct 0)⌝, ⌜(Rew.emb (revalueUMeta me) : SyntacticSemiterm LAct 0)⌝,
        ⌜(Rew.emb (revalueWMeta me) : SyntacticSemiterm LAct 0)⌝, ⌜(Rew.emb (canonicalMeta opp) : SyntacticSemiterm LAct 0)⌝,
        ⌜(Rew.emb (revalueUMeta opp) : SyntacticSemiterm LAct 0)⌝, ⌜(Rew.emb (revalueWMeta opp) : SyntacticSemiterm LAct 0)⌝] := by
    funext i; fin_cases i <;> rfl
  rw [hv]
  simp only [SemitermVec.val_cons, SemitermVec.val_nil, typed_val_emb, quote_canonicalMeta, quote_revalueUMeta, quote_revalueWMeta]
  rfl

/-- **The code equation**: the code of the guard sentence is the guard code of the template
instance's code. -/
theorem quote_guardSentence (a me opp : ℕ) :
    (⌜guardSentence a me opp⌝ : ℕ) = guardCode (⌜guardTemplate a⌝ : ℕ) me opp := by
  unfold guardSentence guardCode
  rw [Sentence.quote_def, Semiformula.coe_subst_eq_subst_coe, Semiformula.quote_def,
    Semiformula.typed_quote_substs, Bootstrapping.Semiformula.val_substs, ← Semiformula.quote_def,
    ← Sentence.quote_def]
  congr 1
  exact semitermVec_val_descriptionTerms me opp

/-! ### The truth equation -/

section truth

lemma val_numT (k : ℕ) : (numT k).val (s := stdReadingNat) ![] Empty.elim = k := by
  unfold numT
  rw [Semiterm.val_lMap, stdReadingNat_lMap_emb]
  simp

lemma val_cterm_C : (cterm Act.C : ClosedSemiterm LAct 0).val (s := stdReadingNat) ![] Empty.elim = 0 := rfl
lemma val_cterm_D : (cterm Act.D : ClosedSemiterm LAct 0).val (s := stdReadingNat) ![] Empty.elim = 1 := rfl

lemma val_canonicalMeta (x : ℕ) : (canonicalMeta x).val (s := stdReadingNat) ![] Empty.elim = canonical x := by
  unfold canonicalMeta
  rw [Semiterm.val_lMap, stdReadingNat_lMap_emb]
  exact val_codeTermMeta _

/-- The descriptions reconstruct the program. -/
lemma revalue_val_desc (x : ℕ) :
    revalue ((revalueUMeta x).val (s := stdReadingNat) ![] Empty.elim) ((revalueWMeta x).val (s := stdReadingNat) ![] Empty.elim) (canonical x) = x := by
  rcases lt_trichotomy x (transposeCode x) with h | h | h
  · unfold revalueUMeta revalueWMeta
    rw [if_pos h, if_pos h, canonical_of_lt h, val_cterm_C, val_cterm_D, revalue_zero_one]
  · unfold revalueUMeta revalueWMeta
    have hs : transposeCode x = x := h.symm
    rw [hs, if_neg (_root_.lt_irrefl _), if_neg (_root_.lt_irrefl _), if_neg (_root_.lt_irrefl _),
      if_neg (_root_.lt_irrefl _), canonical_of_eq h, val_numT, val_numT, revalue_zero_one]
  · unfold revalueUMeta revalueWMeta
    rw [if_neg (lt_asymm h), if_pos h, if_neg (lt_asymm h), if_pos h, canonical_of_gt h, val_cterm_D, val_cterm_C]
    exact transposeCode_transposeCode x

lemma val_actT (a : ℕ) : (actT a).val (s := stdReadingNat) ![] Empty.elim = a := by
  unfold actT
  by_cases h0 : a = 0
  · subst h0; simp [val_cterm_C]
  · by_cases h1 : a = 1
    · subst h1; simp [val_cterm_D]
    · simp [h0, h1, val_numT]

lemma val_actT6 (a : ℕ) (b : Fin 6 → ℕ) : (actT6 a).val (s := stdReadingNat) b Empty.elim = a := by
  unfold actT6
  rw [Semiterm.val_castLE, Subsingleton.elim (fun x : Fin 0 ↦ b (x.castLE (Nat.zero_le 6))) ![]]
  exact val_actT a

/-- **The truth equation**: the guard sentence holds in `ℕ` iff `opp` plays `a` against `me`. -/
theorem models_guardSentence_iff (a me opp : ℕ) :
    ℕ↓[LAct] ⊧ guardSentence a me opp ↔ ∃ n, EvalGraph n opp me opp a := by
  rw [models_iff]
  unfold guardSentence guardTemplate guardTemplate7 Semiformula.Realize
  rw [Semiformula.eval_substs, Semiformula.eval_substs, Semiformula.eval_lMap, stdReadingNat_lMap_emb]
  have h0 : (Semiterm.val (s := stdReadingNat) ![] Empty.elim ∘ descriptionTerms me opp) =
      ![canonical me, (revalueUMeta me).val (s := stdReadingNat) ![] Empty.elim, (revalueWMeta me).val (s := stdReadingNat) ![] Empty.elim,
        canonical opp, (revalueUMeta opp).val (s := stdReadingNat) ![] Empty.elim, (revalueWMeta opp).val (s := stdReadingNat) ![] Empty.elim] := by
    funext i; fin_cases i <;> simp [descriptionTerms, val_canonicalMeta]
  rw [h0]
  have h1 : (Semiterm.val (s := stdReadingNat)
      ![canonical me, (revalueUMeta me).val (s := stdReadingNat) ![] Empty.elim, (revalueWMeta me).val (s := stdReadingNat) ![] Empty.elim,
        canonical opp, (revalueUMeta opp).val (s := stdReadingNat) ![] Empty.elim, (revalueWMeta opp).val (s := stdReadingNat) ![] Empty.elim]
      Empty.elim ∘ ![#0, #1, #2, #3, #4, #5, actT6 a]) =
      ![canonical me, (revalueUMeta me).val (s := stdReadingNat) ![] Empty.elim, (revalueWMeta me).val (s := stdReadingNat) ![] Empty.elim,
        canonical opp, (revalueUMeta opp).val (s := stdReadingNat) ![] Empty.elim, (revalueWMeta opp).val (s := stdReadingNat) ![] Empty.elim, a] := by
    funext i; fin_cases i <;> simp [val_actT6]
  rw [h1]
  refine (eval_guardTemplateRaw (V := ℕ) _).trans ?_
  simp [revalue_val_desc]

end truth

end ArithS
