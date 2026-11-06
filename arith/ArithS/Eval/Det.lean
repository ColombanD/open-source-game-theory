import ArithS.Bridge.Inst

/-!
# ArithS.Det — PA-internal determinism of the arithmetized evaluator: the `atomNeg` leaf of T2-CORE

Closes the last non-source-reading leaf of `transfer_of_leaves` (`ArithS.Inst`): the NEGATIVE
atom. Its conclusion `∼ lMap inst (sentenceAt me' opp' (.plays me opp aN))` is `Π₁` (the negation of a
`Σ₁` sentence), so Σ₁-completeness does not apply. The route is the COMPLETENESS THEOREM
(`Arithmetic.complete`: a sentence true in every model of PA is a PA theorem): in a model
`V ⊧* 𝗣𝗔`,

1. the POSITIVE atom of the actual play `b ≠ aN` is a PA theorem (`pa_proves_sentenceAt_inst`,
   Σ₁-completeness), hence true in `V` (`models_of_provable`);
2. both atom sentences unfold in `V` to `∃ N, EvalGraph N ⌜me⌝ ⌜opp⌝ ⌜me⌝ (actCode _)` about
   `V`-elements — `models_sentenceAt_plays_V`, the truth equation of `ArithS.Agent` re-proved over
   EVERY model of `𝗜𝚺₁`: the description terms evaluate to the CASTS of their standard values
   (`val_binNumeralMeta_V`/`val_codeTermMeta_V`, `revalue_val_desc_V` — the latter through Foundation's Σ₁-absoluteness of
   the `revalue` function, `DefinedFunction.shigmaOne_absolute_func`);
3. the evaluator is deterministic INSIDE the model — `EvalGraph.unique_V'`, at every pair of
   fuels at once, by `ISigma1.pi1_order_induction` on the fuel (the statement
   `∀ n' me opp p a₁ a₂, EvalGraph n … a₁ → EvalGraph n' … a₂ → a₁ = a₂` is `Π₁` in `n`, `EvalGraph`
   being `Σ₁`; the case analysis is `EvalN.unique`'s, through the `V`-general inversion lemmas);
4. `(actCode b : V) ≠ (actCode aN : V)` by injectivity of `Nat.cast` into a model of `𝗣𝗔⁻`.

Hence `pa_proves_neg_sentenceAt_inst`, and the leaf discharges `leaf_atomNeg_sound` (under
`GuardAgree`, proper modest players) and `leaf_atomNeg_sound_searchFree` (search-free players,
NO oracle).

**What remains a hypothesis in `transfer_of_leaves` after this module: exactly the twelve
SOURCE-READING leaves** `searchBranch, simStep, botSimStep, botSearchStep, botSysSearchStep,
botSysSimStep, botSysSearchThenSearch, iteBranchSearch_t, searchThenSearch_t, searchChain,
ctxChain, searchElseChain` — their conclusions relate PA's unbounded box of the budget-erased
guard to the evaluator's length-bounded `□_k` of the realized guard (bounded D1 in both
directions, `GuardAgree` inside PA; boundary 1 of `ARITHMETIZED_S_RESULTS.md` §4). Every
other `Leaf` constructor is discharged: `atom` (`leaf_atom_sound`), `atomNeg` (here),
`atomBoxImpl` (`leaf_atomBoxImpl_sound`), `eqRefl`/`eqNeg` (`Core.leaf_eqRefl_sound`/
`leaf_eqNeg_sound`) — the first two on proper modest players.
-/

set_option linter.constructorNameAsVariable false

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1
open LAct

/-! ### Determinism inside every model of `𝗜𝚺₁` -/

section det

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- **Internal determinism, across fuels**: in every model of `𝗜𝚺₁`, two runs of the arithmetized
evaluator on the same frame and body agree, whatever their fuels. `Π₁`-order induction on the
first fuel; the second is universally quantified inside the induction predicate. -/
theorem EvalGraph.unique_V' (n : V) : ∀ n' me opp p a₁ a₂ : V,
    EvalGraph n me opp p a₁ → EvalGraph n' me opp p a₂ → a₁ = a₂ := by
  induction n using ISigma1.pi1_order_induction with
  | hP => definability
  | ind n ih =>
    intro n' me opp p a₁ a₂ h₁ h₂
    obtain ⟨m, rfl, _⟩ := EvalGraph.case_iff.mp h₁
    obtain ⟨m', rfl, _⟩ := EvalGraph.case_iff.mp h₂
    have hm : m < m + 1 := lt_add_one m
    by_cases hp : IsShape p
    · rcases hp with ⟨a, rfl⟩ | rfl | rfl | ⟨p, rfl⟩ | ⟨p, q, rfl⟩ | ⟨b, a', p, q, rfl⟩ | ⟨k, g, p, q, rfl⟩ |
        ⟨v, θ, p, q, rfl⟩ | ⟨d, i, rfl⟩ | ⟨j, rfl⟩ | ⟨e, r, rfl⟩
      · rw [EvalGraph.const_iff] at h₁ h₂; rw [h₁, h₂]
      · rw [EvalGraph.self_iff] at h₁ h₂; exact ih m hm m' _ _ _ _ _ h₁ h₂
      · rw [EvalGraph.opp_iff] at h₁ h₂; exact ih m hm m' _ _ _ _ _ h₁ h₂
      · rw [EvalGraph.bot_iff] at h₁ h₂; exact ih m hm m' _ _ _ _ _ h₁ h₂
      · rw [EvalGraph.sim_iff] at h₁ h₂; exact ih m hm m' _ _ _ _ _ h₁ h₂
      · rcases EvalGraph.ite_iff.mp h₁ with ⟨r₁, hb₁, hc₁⟩
        rcases EvalGraph.ite_iff.mp h₂ with ⟨r₂, hb₂, hc₂⟩
        have hr : r₁ = r₂ := ih m hm m' _ _ _ _ _ hb₁ hb₂
        subst hr
        rcases hc₁ with ⟨e₁, h₁'⟩ | ⟨e₁, h₁'⟩ <;> rcases hc₂ with ⟨e₂, h₂'⟩ | ⟨e₂, h₂'⟩
        · exact ih m hm m' _ _ _ _ _ h₁' h₂'
        · exact absurd e₁ e₂
        · exact absurd e₂ e₁
        · exact ih m hm m' _ _ _ _ _ h₁' h₂'
      · rcases EvalGraph.search_iff.mp h₁ with ⟨e₁, h₁'⟩ | ⟨e₁, h₁'⟩ <;>
          rcases EvalGraph.search_iff.mp h₂ with ⟨e₂, h₂'⟩ | ⟨e₂, h₂'⟩
        · exact ih m hm m' _ _ _ _ _ h₁' h₂'
        · exact absurd e₁ e₂
        · exact absurd e₂ e₁
        · exact ih m hm m' _ _ _ _ _ h₁' h₂'
      · rcases EvalGraph.tvote_iff.mp h₁ with ⟨rfl, hc₁⟩ | ⟨w, I, rest, rfl, hc₁⟩
        · rcases EvalGraph.tvote_nil_iff.mp h₂ with ⟨e₂, h₂'⟩ | ⟨e₂, h₂'⟩ <;>
            rcases hc₁ with ⟨e₁, h₁'⟩ | ⟨e₁, h₁'⟩
          · exact ih m hm m' _ _ _ _ _ h₁' h₂'
          · exact absurd e₂ e₁
          · exact absurd e₁ e₂
          · exact ih m hm m' _ _ _ _ _ h₁' h₂'
        · rcases EvalGraph.tvote_cons_iff.mp h₂ with ⟨e₂, h₂'⟩ | ⟨e₂, r₂, hI₂, hc₂⟩ <;>
            rcases hc₁ with ⟨e₁, h₁'⟩ | ⟨e₁, r₁, hI₁, hc₁⟩
          · exact ih m hm m' _ _ _ _ _ h₁' h₂'
          · exact absurd e₂ e₁
          · exact absurd e₁ e₂
          · have hr : r₁ = r₂ := ih m hm m' _ _ _ _ _ hI₁ hI₂
            subst hr
            rcases hc₁ with ⟨f₁, h₁'⟩ | ⟨f₁, h₁'⟩ <;> rcases hc₂ with ⟨f₂, h₂'⟩ | ⟨f₂, h₂'⟩
            · exact ih m hm m' _ _ _ _ _ h₁' h₂'
            · exact absurd f₁ f₂
            · exact absurd f₂ f₁
            · exact ih m hm m' _ _ _ _ _ h₁' h₂'
      · rcases EvalGraph.sys_iff.mp h₁ with ⟨m₁, hm₁, h₁'⟩
        rcases EvalGraph.sys_iff.mp h₂ with ⟨m₂, hm₂, h₂'⟩
        have hmm : m₁ = m₂ := add_right_cancel (hm₁.symm.trans hm₂)
        subst hmm
        exact ih m hm m' _ _ _ _ _ h₁' h₂'
      · exact absurd h₁ EvalGraph.selfIdx_iff
      · exact absurd h₁ EvalGraph.cons_iff
    · exfalso
      rcases EvalGraph.case_iff.mp h₁ with ⟨n', _, (h | ⟨h, _⟩ | ⟨h, _⟩ | ⟨p', h, _⟩ |
        ⟨p', q, h, _⟩ | ⟨b, a', p', q, r, h, _⟩ | ⟨k, g, p', q, h, _⟩ | ⟨θ, p', q, h, _⟩ |
        ⟨w, I, rest, θ, p', q, h, _⟩ | ⟨d, i, m, h, _⟩)⟩
      · exact hp (h ▸ IsShape.const _)
      · exact hp (h ▸ IsShape.self)
      · exact hp (h ▸ IsShape.opp)
      · exact hp (h ▸ IsShape.bot _)
      · exact hp (h ▸ IsShape.sim _ _)
      · exact hp (h ▸ IsShape.ite _ _ _ _)
      · exact hp (h ▸ IsShape.search _ _ _ _)
      · exact hp (h ▸ IsShape.tvote _ _ _ _)
      · exact hp (h ▸ IsShape.tvote _ _ _ _)
      · exact hp (h ▸ IsShape.sys _ _)


end det

/-! ### The standard `LAct`-structure on a model, and the description terms in it -/

section desc

variable (V : Type*) [ORingStructure V]

/-- `V` as an `LAct`-structure: arithmetic as `V`, `c_C ↦ 0`, `c_D ↦ 1` — the pull-back of the
standard `ℒₒᵣ`-structure along the instantiation `inst`. (At `V = ℕ` this is `stdReadingNat`,
`lMap_inst_std`.) Not an instance: `ℕ` already carries `stdReadingNat`. -/
@[instance_reducible] noncomputable def stdReadingV : Structure LAct V :=
  Structure.lMap inst (standardModel V)

lemma stdReadingV_lMap_emb : Structure.lMap emb (stdReadingV V) = standardModel V := by
  ext <;> rfl

/-- `stdReadingV V` is `stdReading V` (`ArithS.TheoryAct`): both read `c_C ↦ 0`, `c_D ↦ 1`. -/
lemma stdReadingV_eq_stdReading : stdReadingV V = stdReading V := by
  refine Structure.ext ?_ ?_
  · funext k f v
    rcases f with f | ⟨(_ | _)⟩ <;> rfl
  · funext k r v
    rcases r with r | e
    · rfl
    · exact e.elim

variable {V}

/-- Truth of an instantiated `LAct`-sentence in `V` is its truth in `stdReadingV V`. -/
lemma models_inst_V (σ : Sentence LAct) :
    V↓[ℒₒᵣ] ⊧ Semiformula.lMap inst σ ↔ Semiformula.Eval (s := stdReadingV V) ![] Empty.elim σ := by
  rw [models_iff]
  unfold Semiformula.Realize
  rw [Semiformula.eval_lMap]

lemma val_cl_V {n : ℕ} (t : ClosedSemiterm LAct 0) (b : Fin n → V) :
    (cl t : Semiterm LAct Empty n).val (s := stdReadingV V) b Empty.elim =
      t.val (s := stdReadingV V) ![] Empty.elim := by
  unfold cl
  rw [Semiterm.val_castLE, Subsingleton.elim (fun x : Fin 0 ↦ b (x.castLE (Nat.zero_le n))) ![]]

lemma stdReadingV_rel_eq (v : Fin 2 → V) :
    (stdReadingV V).rel (Language.Eq.eq : LAct.Rel 2) v ↔ v 0 = v 1 := Iff.rfl

lemma val_cterm_C_V : (cterm Act.C : ClosedSemiterm LAct 0).val (s := stdReadingV V) ![] Empty.elim = 0 := rfl
lemma val_cterm_D_V : (cterm Act.D : ClosedSemiterm LAct 0).val (s := stdReadingV V) ![] Empty.elim = 1 := rfl

variable [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

lemma val_numT_V (k : ℕ) : (numT k).val (s := stdReadingV V) ![] Empty.elim = (k : V) := by
  unfold numT
  rw [Semiterm.val_lMap, stdReadingV_lMap_emb]
  simp [numeral_eq_natCast]

lemma val_twoT_V : twoT.val (s := standardModel V) ![] Empty.elim = 2 := by
  unfold twoT; simp [one_add_one_eq_two]

/-- The binary numeral of `n` denotes the cast of `n` in every model. -/
theorem val_binNumeralMeta_V (n : ℕ) : (binNumeralMeta n).val (s := standardModel V) ![] Empty.elim = (n : V) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | _ | k
    · rw [binNumeralMeta_zero]; simp
    · rw [binNumeralMeta_one]; simp
    · by_cases he : (k + 1 + 1) % 2 = 0
      · rw [binNumeralMeta_even (by omega) he]
        simp [val_twoT_V, ih ((k + 1 + 1) / 2) (by omega)]
        have h2 : k + 1 + 1 = 2 * ((k + 1 + 1) / 2) := by omega
        have h3 : ((k : V) + 1 + 1) = ((k + 1 + 1 : ℕ) : V) := by norm_cast
        rw [h3]
        conv_rhs => rw [h2]
        push_cast
        rfl
      · rw [binNumeralMeta_odd (by omega) (by omega)]
        simp [val_twoT_V, ih ((k + 1 + 1) / 2) (by omega)]
        have h2 : k + 1 = 2 * ((k + 1 + 1) / 2) := by omega
        have h3 : ((k : V) + 1) = ((k + 1 : ℕ) : V) := by norm_cast
        rw [h3]
        conv_rhs => rw [h2]
        push_cast
        rfl

lemma val_ppairTermMeta_V (s t : ClosedSemiterm ℒₒᵣ 0) :
    (ppairTermMeta s t).val (s := standardModel V) ![] Empty.elim =
    ppair (s.val (s := standardModel V) ![] Empty.elim) (t.val (s := standardModel V) ![] Empty.elim) := by
  simp [ppairTermMeta, ppair]

lemma val_succTT_V (t : ClosedSemiterm ℒₒᵣ 0) :
    (succTT t).val (s := standardModel V) ![] Empty.elim = t.val (s := standardModel V) ![] Empty.elim + 1 := by
  simp [succTT]

/-- The structural term of `x` denotes the cast of `x` in every model. -/
theorem val_codeTermMeta_V (x : ℕ) : (codeTermMeta x).val (s := standardModel V) ![] Empty.elim = (x : V) := by
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    by_cases hx : IsShape x
    · rcases hx with ⟨a, rfl⟩ | rfl | rfl | ⟨p, rfl⟩ | ⟨p, q, rfl⟩ | ⟨b, a, p, q, rfl⟩ | ⟨k, g, p, q, rfl⟩ |
        ⟨v, θ, p, q, rfl⟩ | ⟨d, i, rfl⟩ | ⟨j, rfl⟩ | ⟨e, r, rfl⟩
      · rw [codeTermMeta_const, val_succTT_V, val_ppairTermMeta_V, val_binNumeralMeta_V, val_binNumeralMeta_V, cast_pConst]
        unfold pConst; push_cast; rfl
      · rw [codeTermMeta_self, val_succTT_V, val_ppairTermMeta_V, val_binNumeralMeta_V, val_binNumeralMeta_V, cast_pSelf]
        unfold pSelf; push_cast; rfl
      · rw [codeTermMeta_opp, val_succTT_V, val_ppairTermMeta_V, val_binNumeralMeta_V, val_binNumeralMeta_V, cast_pOpp]
        unfold pOpp; push_cast; rfl
      · rw [codeTermMeta_bot, val_succTT_V, val_ppairTermMeta_V, val_binNumeralMeta_V, ih p (by simp), cast_pBot]
        unfold pBot; push_cast; rfl
      · rw [codeTermMeta_sim, val_succTT_V, val_ppairTermMeta_V, val_ppairTermMeta_V, val_binNumeralMeta_V, ih p (by simp),
          ih q (by simp), cast_pSim]
        unfold pSim; push_cast; rfl
      · rw [codeTermMeta_ite, val_succTT_V, val_ppairTermMeta_V, val_ppairTermMeta_V, val_ppairTermMeta_V, val_ppairTermMeta_V,
          val_binNumeralMeta_V, val_binNumeralMeta_V, ih b (by simp), ih p (by simp), ih q (by simp), cast_pIte]
        unfold pIte; push_cast; rfl
      · rw [codeTermMeta_search, val_succTT_V, val_ppairTermMeta_V, val_ppairTermMeta_V, val_ppairTermMeta_V, val_ppairTermMeta_V,
          val_binNumeralMeta_V, val_binNumeralMeta_V, val_binNumeralMeta_V, ih p (by simp), ih q (by simp), cast_pSearch]
        unfold pSearch; push_cast; rfl
      · rw [codeTermMeta_tvote, val_succTT_V, val_ppairTermMeta_V, val_ppairTermMeta_V, val_ppairTermMeta_V, val_ppairTermMeta_V,
          val_binNumeralMeta_V, val_binNumeralMeta_V, ih v (by simp), ih p (by simp), ih q (by simp), cast_pTvote]
        unfold pTvote; push_cast; rfl
      · rw [codeTermMeta_sys, val_succTT_V, val_ppairTermMeta_V, val_ppairTermMeta_V, val_binNumeralMeta_V, val_binNumeralMeta_V,
          ih d (by simp), cast_pSys]
        unfold pSys; push_cast; rfl
      · rw [codeTermMeta_selfIdx, val_succTT_V, val_ppairTermMeta_V, val_binNumeralMeta_V, val_binNumeralMeta_V, cast_pSelfIdx]
        unfold pSelfIdx; push_cast; rfl
      · rw [codeTermMeta_cons, val_succTT_V, val_ppairTermMeta_V, val_ppairTermMeta_V, val_binNumeralMeta_V, ih e (by simp),
          ih r (by simp), cast_pCons]
        unfold pCons; push_cast; rfl
    · rw [codeTermMeta_of_not_shape hx, val_binNumeralMeta_V]

lemma val_canonicalMeta_V (x : ℕ) : (canonicalMeta x).val (s := stdReadingV V) ![] Empty.elim = ((canonical x : ℕ) : V) := by
  unfold canonicalMeta
  rw [Semiterm.val_lMap, stdReadingV_lMap_emb]
  exact val_codeTermMeta_V _

/-- `revalue` is absolute: its value on casts is the cast of its value (Σ₁-definable function). -/
lemma cast_revalue (u w x : ℕ) : ((revalue u w x : ℕ) : V) = revalue (u : V) (w : V) (x : V) := by
  have := DefinedFunction.shigmaOne_absolute_func V (revalue_defined (V := ℕ)) (revalue_defined (V := V))
    ![u, w, x]
  simpa [Function.comp_def] using this

/-- The descriptions reconstruct the (cast) program, in every model. -/
lemma revalue_val_desc_V (x : ℕ) :
    revalue ((revalueUMeta x).val (s := stdReadingV V) ![] Empty.elim) ((revalueWMeta x).val (s := stdReadingV V) ![] Empty.elim)
      ((canonical x : ℕ) : V) = (x : V) := by
  rcases lt_trichotomy x (transposeCode x) with h | h | h
  · unfold revalueUMeta revalueWMeta
    rw [if_pos h, if_pos h, canonical_of_lt h, val_cterm_C_V, val_cterm_D_V, revalue_zero_one]
  · unfold revalueUMeta revalueWMeta
    have hs : transposeCode x = x := h.symm
    rw [hs, if_neg (_root_.lt_irrefl _), if_neg (_root_.lt_irrefl _), if_neg (_root_.lt_irrefl _),
      if_neg (_root_.lt_irrefl _), canonical_of_eq h, val_numT_V, val_numT_V, Nat.cast_zero, Nat.cast_one,
      revalue_zero_one]
  · unfold revalueUMeta revalueWMeta
    rw [if_neg (lt_asymm h), if_pos h, if_neg (lt_asymm h), if_pos h, canonical_of_gt h, val_cterm_D_V,
      val_cterm_C_V]
    have e : ((revalue 1 0 (transposeCode x) : ℕ) : V) = revalue (1 : V) (0 : V) ((transposeCode x : ℕ) : V) := by
      have := cast_revalue (V := V) 1 0 (transposeCode x)
      rwa [Nat.cast_one, Nat.cast_zero] at this
    rw [← e]
    exact congrArg _ (transposeCode_transposeCode x)

lemma val_actT_V (a : ℕ) : (actT a).val (s := stdReadingV V) ![] Empty.elim = (a : V) := by
  unfold actT
  by_cases h0 : a = 0
  · subst h0; simp [val_cterm_C_V]
  · by_cases h1 : a = 1
    · subst h1; simp [val_cterm_D_V]
    · simp [h0, h1, val_numT_V]

/-- `relDesc` in `V` is the graph of `revalue`. -/
lemma eval_relDesc_V (v : Fin 4 → V) :
    Semiformula.Eval (s := stdReadingV V) v Empty.elim relDesc ↔ v 0 = revalue (v 1) (v 2) (v 3) := by
  unfold relDesc
  rw [Semiformula.eval_lMap, stdReadingV_lMap_emb]
  exact revalue_defined.df v

/-- `evalG` in `V` is `EvalGraph`. -/
lemma eval_evalG_V (v : Fin 5 → V) :
    Semiformula.Eval (s := stdReadingV V) v Empty.elim evalG ↔ EvalGraph (v 0) (v 1) (v 2) (v 3) (v 4) := by
  unfold evalG
  rw [Semiformula.eval_lMap, stdReadingV_lMap_emb]
  exact evalGraph_defined.df v

/-- A closed description in `V` pins the cast of the program. -/
lemma eval_closedDesc_V (c : ℕ) (b : Fin 7 → V) :
    Semiformula.Eval (s := stdReadingV V) b Empty.elim (closedDesc c) ↔ b 0 = (c : V) := by
  unfold closedDesc descF
  simp only [Semiformula.eval_ex, LogicalConnective.HomClass.map_and, LogicalConnective.Prop.and_eq,
    Semiformula.eval_rel, Semiformula.eval_substs, eval_relDesc_V, stdReadingV_rel_eq, Function.comp_def,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_succ, Matrix.vecHead, Matrix.vecTail, Semiterm.val_bvar, val_cl_V, val_canonicalMeta_V]
  constructor
  · rintro ⟨x, rfl, h⟩
    rwa [revalue_val_desc_V] at h
  · intro h
    exact ⟨_, rfl, by rw [revalue_val_desc_V]; exact h⟩


end desc

/-! ### The negative atom in every model of PA, and in PA -/


/-! ### The `atomNeg` leaf of T2-CORE -/


end ArithS

#print axioms ArithS.EvalGraph.unique_V'
