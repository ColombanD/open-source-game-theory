import ArithS.Inst

/-!
# ArithS.Det — PA-internal determinism of the arithmetized evaluator: the `atomNeg` leaf of T2-CORE

Closes the last non-source-reading leaf of `transfer_of_leaves` (`ArithS.Inst`): the NEGATIVE
atom. Its conclusion `∼ lMap inst (trAt me' opp' (.plays me opp aN))` is `Π₁` (the negation of a
`Σ₁` sentence), so Σ₁-completeness does not apply. The route is the COMPLETENESS THEOREM
(`Arithmetic.complete`: a sentence true in every model of PA is a PA theorem): in a model
`V ⊧* 𝗣𝗔`,

1. the POSITIVE atom of the actual play `b ≠ aN` is a PA theorem (`pa_proves_trAt_inst`,
   Σ₁-completeness), hence true in `V` (`models_of_provable`);
2. both atom sentences unfold in `V` to `∃ N, EvalGraph N ⌜me⌝ ⌜opp⌝ ⌜me⌝ (actCode _)` about
   `V`-elements — `models_trAt_plays_V`, the truth equation of `ArithS.Agent` re-proved over
   EVERY model of `𝗜𝚺₁`: the description terms evaluate to the CASTS of their standard values
   (`val_bnumT_V`, `relabel_val_desc_V` — the latter through Foundation's Σ₁-absoluteness of
   the `relabel` function, `DefinedFunction.shigmaOne_absolute_func`);
3. the evaluator is deterministic INSIDE the model — `EvalGraph.unique_V'`, at every pair of
   fuels at once, by `ISigma1.pi1_order_induction` on the fuel (the statement
   `∀ n' me opp p a₁ a₂, EvalGraph n … a₁ → EvalGraph n' … a₂ → a₁ = a₂` is `Π₁` in `n`, `EvalGraph`
   being `Σ₁`; the case analysis is `EvalN.unique`'s, through the `V`-general inversion lemmas);
4. `(actCode b : V) ≠ (actCode aN : V)` by injectivity of `Nat.cast` into a model of `𝗣𝗔⁻`.

Hence `pa_proves_neg_trAt_inst`, and the leaf discharges `leaf_atomNeg_sound` (under
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
    · rcases hp with ⟨a, rfl⟩ | rfl | rfl | ⟨p, rfl⟩ | ⟨p, q, rfl⟩ | ⟨b, a', p, q, rfl⟩ | ⟨k, g, p, q, rfl⟩
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
    · exfalso
      rcases EvalGraph.case_iff.mp h₁ with ⟨n', _, (h | ⟨h, _⟩ | ⟨h, _⟩ | ⟨p', h, _⟩ |
        ⟨p', q, h, _⟩ | ⟨b, a', p', q, r, h, _⟩ | ⟨k, g, p', q, h, _⟩)⟩
      · exact hp (Or.inl ⟨_, h⟩)
      · exact hp (Or.inr (Or.inl h))
      · exact hp (Or.inr (Or.inr (Or.inl h)))
      · exact hp (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, h⟩))))
      · exact hp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, h⟩)))))
      · exact hp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, _, _, h⟩))))))
      · exact hp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨_, _, _, _, h⟩))))))

/-- **Internal determinism** at one fuel. -/
theorem EvalGraph.unique_V {n me opp p a₁ a₂ : V}
    (h₁ : EvalGraph n me opp p a₁) (h₂ : EvalGraph n me opp p a₂) : a₁ = a₂ :=
  EvalGraph.unique_V' n n me opp p a₁ a₂ h₁ h₂

end det

/-! ### The standard `LAct`-structure on a model, and the description terms in it -/

section desc

variable (V : Type*) [ORingStructure V]

/-- `V` as an `LAct`-structure: arithmetic as `V`, `c_C ↦ 0`, `c_D ↦ 1` — the pull-back of the
standard `ℒₒᵣ`-structure along the instantiation `inst`. (At `V = ℕ` this is `stdAct`,
`lMap_inst_std`.) Not an instance: `ℕ` already carries `stdAct`. -/
@[instance_reducible] noncomputable def stdActV : Structure LAct V :=
  Structure.lMap inst (standardModel V)

lemma stdActV_lMap_emb : Structure.lMap emb (stdActV V) = standardModel V := by
  ext <;> rfl

variable {V}

/-- Truth of an instantiated `LAct`-sentence in `V` is its truth in `stdActV V`. -/
lemma models_inst_V (σ : Sentence LAct) :
    V↓[ℒₒᵣ] ⊧ Semiformula.lMap inst σ ↔ Semiformula.Eval (s := stdActV V) ![] Empty.elim σ := by
  rw [models_iff]
  unfold Semiformula.Realize
  rw [Semiformula.eval_lMap]

lemma val_cl_V {n : ℕ} (t : ClosedSemiterm LAct 0) (b : Fin n → V) :
    (cl t : Semiterm LAct Empty n).val (s := stdActV V) b Empty.elim =
      t.val (s := stdActV V) ![] Empty.elim := by
  unfold cl
  rw [Semiterm.val_castLE, Subsingleton.elim (fun x : Fin 0 ↦ b (x.castLE (Nat.zero_le n))) ![]]

lemma stdActV_rel_eq (v : Fin 2 → V) :
    (stdActV V).rel (Language.Eq.eq : LAct.Rel 2) v ↔ v 0 = v 1 := Iff.rfl

lemma val_cterm_C_V : (cterm Act.C : ClosedSemiterm LAct 0).val (s := stdActV V) ![] Empty.elim = 0 := rfl
lemma val_cterm_D_V : (cterm Act.D : ClosedSemiterm LAct 0).val (s := stdActV V) ![] Empty.elim = 1 := rfl

variable [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

lemma val_numT_V (k : ℕ) : (numT k).val (s := stdActV V) ![] Empty.elim = (k : V) := by
  unfold numT
  rw [Semiterm.val_lMap, stdActV_lMap_emb]
  simp [numeral_eq_natCast]

lemma val_twoT_V : twoT.val (s := standardModel V) ![] Empty.elim = 2 := by
  unfold twoT; simp [one_add_one_eq_two]

/-- The binary numeral of `n` denotes the cast of `n` in every model. -/
theorem val_bnumT_V (n : ℕ) : (bnumT n).val (s := standardModel V) ![] Empty.elim = (n : V) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | _ | k
    · rw [bnumT_zero]; simp
    · rw [bnumT_one]; simp
    · by_cases he : (k + 1 + 1) % 2 = 0
      · rw [bnumT_even (by omega) he]
        simp [val_twoT_V, ih ((k + 1 + 1) / 2) (by omega)]
        have h2 : k + 1 + 1 = 2 * ((k + 1 + 1) / 2) := by omega
        have h3 : ((k : V) + 1 + 1) = ((k + 1 + 1 : ℕ) : V) := by norm_cast
        rw [h3]
        conv_rhs => rw [h2]
        push_cast
        rfl
      · rw [bnumT_odd (by omega) (by omega)]
        simp [val_twoT_V, ih ((k + 1 + 1) / 2) (by omega)]
        have h2 : k + 1 = 2 * ((k + 1 + 1) / 2) := by omega
        have h3 : ((k : V) + 1) = ((k + 1 : ℕ) : V) := by norm_cast
        rw [h3]
        conv_rhs => rw [h2]
        push_cast
        rfl

lemma val_dnumT_V (x : ℕ) : (dnumT x).val (s := stdActV V) ![] Empty.elim = ((dnum x : ℕ) : V) := by
  unfold dnumT
  rw [Semiterm.val_lMap, stdActV_lMap_emb]
  exact val_bnumT_V _

/-- `relabel` is absolute: its value on casts is the cast of its value (Σ₁-definable function). -/
lemma cast_relabel (u w x : ℕ) : ((relabel u w x : ℕ) : V) = relabel (u : V) (w : V) (x : V) := by
  have := DefinedFunction.shigmaOne_absolute_func V (relabel_defined (V := ℕ)) (relabel_defined (V := V))
    ![u, w, x]
  simpa [Function.comp_def] using this

/-- The descriptions reconstruct the (cast) program, in every model. -/
lemma relabel_val_desc_V (x : ℕ) :
    relabel ((dUT x).val (s := stdActV V) ![] Empty.elim) ((dWT x).val (s := stdActV V) ![] Empty.elim)
      ((dnum x : ℕ) : V) = (x : V) := by
  rcases lt_trichotomy x (swapcode x) with h | h | h
  · unfold dUT dWT
    rw [if_pos h, if_pos h, dnum_of_lt h, val_cterm_C_V, val_cterm_D_V, relabel_zero_one]
  · unfold dUT dWT
    have hs : swapcode x = x := h.symm
    rw [hs, if_neg (_root_.lt_irrefl _), if_neg (_root_.lt_irrefl _), if_neg (_root_.lt_irrefl _),
      if_neg (_root_.lt_irrefl _), dnum_of_eq h, val_numT_V, val_numT_V, Nat.cast_zero, Nat.cast_one,
      relabel_zero_one]
  · unfold dUT dWT
    rw [if_neg (lt_asymm h), if_pos h, if_neg (lt_asymm h), if_pos h, dnum_of_gt h, val_cterm_D_V,
      val_cterm_C_V]
    have e : ((relabel 1 0 (swapcode x) : ℕ) : V) = relabel (1 : V) (0 : V) ((swapcode x : ℕ) : V) := by
      have := cast_relabel (V := V) 1 0 (swapcode x)
      rwa [Nat.cast_one, Nat.cast_zero] at this
    rw [← e]
    exact congrArg _ (swapcode_swapcode x)

lemma val_actT_V (a : ℕ) : (actT a).val (s := stdActV V) ![] Empty.elim = (a : V) := by
  unfold actT
  by_cases h0 : a = 0
  · subst h0; simp [val_cterm_C_V]
  · by_cases h1 : a = 1
    · subst h1; simp [val_cterm_D_V]
    · simp [h0, h1, val_numT_V]

/-- `relDesc` in `V` is the graph of `relabel`. -/
lemma eval_relDesc_V (v : Fin 4 → V) :
    Semiformula.Eval (s := stdActV V) v Empty.elim relDesc ↔ v 0 = relabel (v 1) (v 2) (v 3) := by
  unfold relDesc
  rw [Semiformula.eval_lMap, stdActV_lMap_emb]
  exact relabel_defined.df v

/-- `evalG` in `V` is `EvalGraph`. -/
lemma eval_evalG_V (v : Fin 5 → V) :
    Semiformula.Eval (s := stdActV V) v Empty.elim evalG ↔ EvalGraph (v 0) (v 1) (v 2) (v 3) (v 4) := by
  unfold evalG
  rw [Semiformula.eval_lMap, stdActV_lMap_emb]
  exact evalGraph_defined.df v

/-- A closed description in `V` pins the cast of the program. -/
lemma eval_closedDesc_V (c : ℕ) (b : Fin 7 → V) :
    Semiformula.Eval (s := stdActV V) b Empty.elim (closedDesc c) ↔ b 0 = (c : V) := by
  unfold closedDesc descF
  simp only [Semiformula.eval_ex, LogicalConnective.HomClass.map_and, LogicalConnective.Prop.and_eq,
    Semiformula.eval_rel, Semiformula.eval_substs, eval_relDesc_V, stdActV_rel_eq, Function.comp_def,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_succ, Matrix.vecHead, Matrix.vecTail, Semiterm.val_bvar, val_cl_V, val_dnumT_V]
  constructor
  · rintro ⟨x, rfl, h⟩
    rwa [relabel_val_desc_V] at h
  · intro h
    exact ⟨_, rfl, by rw [relabel_val_desc_V]; exact h⟩

/-- **The truth equation in every model of `𝗜𝚺₁`**: for PROPER programs the instantiated play-atom
holds in `V` iff the arithmetized `play` on the CAST codes yields the cast action code; the frame
`(me', opp')` is irrelevant. -/
theorem models_trAt_plays_V (me' opp' me opp : PD.Prog) (a : PD.Action)
    (hme : Proper me) (hopp : Proper opp) :
    V↓[ℒₒᵣ] ⊧ Semiformula.lMap inst (trAt me' opp' (.plays me opp a)) ↔
      ∃ N : V, EvalGraph N (pcode me : V) (pcode opp : V) (pcode me : V) (actCode a : V) := by
  rw [models_inst_V]
  unfold trAt
  rw [tmpl_plays]
  unfold progGraph
  rw [progAux_of_ne hme.1 hme.2, progAux_of_ne hopp.1 hopp.2]
  simp only [Semiformula.eval_substs, Semiformula.eval_ex, LogicalConnective.HomClass.map_and,
    LogicalConnective.Prop.and_eq, eval_closedDesc_V, eval_evalG_V, Function.comp_def,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, Matrix.cons_val_succ, Matrix.vecHead, Matrix.vecTail, Semiterm.val_bvar,
    val_cl_V, val_actT_V]
  constructor
  · rintro ⟨x, y, N, rfl, rfl, h⟩
    exact ⟨N, h⟩
  · rintro ⟨N, h⟩
    exact ⟨_, _, N, rfl, rfl, h⟩

end desc

/-! ### The negative atom in every model of PA, and in PA -/

/-- In a model of PA, a PA-provable positive atom for the play `b` refutes the atom for any
`aN ≠ b`: the positive run transfers to `V`, the negative one would be a second run, and the
evaluator is deterministic inside `V`. -/
theorem models_neg_inst_trAt_plays_V (V : Type*) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (me' opp' me opp : PD.Prog) {b aN : PD.Action} (hne : b ≠ aN)
    (hme : Proper me) (hopp : Proper opp)
    (hpos : 𝗣𝗔 ⊢ Semiformula.lMap inst (trAt me' opp' (.plays me opp b))) :
    V↓[ℒₒᵣ] ⊧ ∼ Semiformula.lMap inst (trAt me' opp' (.plays me opp aN)) := by
  have hV : V↓[ℒₒᵣ] ⊧ Semiformula.lMap inst (trAt me' opp' (.plays me opp b)) :=
    models_of_provable inferInstance hpos
  rw [models_trAt_plays_V me' opp' me opp b hme hopp] at hV
  obtain ⟨N, hN⟩ := hV
  rw [Semantics.Not.models_not, models_trAt_plays_V me' opp' me opp aN hme hopp]
  rintro ⟨N', hN'⟩
  have e : (actCode b : V) = (actCode aN : V) := EvalGraph.unique_V' N N' _ _ _ _ _ hN hN'
  exact hne (actCode_inj (nat_cast_inj.mp e))

/-- **PA refutes the wrong atom, given the right one**: from `𝗣𝗔 ⊢ atom(b)` and `b ≠ aN`,
`𝗣𝗔 ⊢ ∼ atom(aN)` — by the completeness theorem over `models_neg_inst_trAt_plays_V`. -/
theorem pa_proves_neg_trAt_inst_of_pos (me' opp' me opp : PD.Prog) {b aN : PD.Action} (hne : b ≠ aN)
    (hme : Proper me) (hopp : Proper opp)
    (hpos : 𝗣𝗔 ⊢ Semiformula.lMap inst (trAt me' opp' (.plays me opp b))) :
    𝗣𝗔 ⊢ ∼ Semiformula.lMap inst (trAt me' opp' (.plays me opp aN)) :=
  Arithmetic.complete 𝗣𝗔 _ fun (V : Type) _ _ ↦
    models_neg_inst_trAt_plays_V V me' opp' me opp hne hme hopp hpos

/-- **PA proves the negative atom sentences of modest plays**: for proper modest players, given
`GuardAgree`, an engine play `me(opp) = b` with `b ≠ aN` makes
`∼ lMap inst (trAt me' opp' (.plays me opp aN))` a theorem of PA. -/
theorem pa_proves_neg_trAt_inst (hga : GuardAgree) (me' opp' me opp : PD.Prog) {b aN : PD.Action}
    (hne : b ≠ aN) (hme : Proper me) (hopp : Proper opp) (hm : modestP me = true) (hm' : modestP opp = true)
    (h : ∃ n, PD.play n me opp = some b) :
    𝗣𝗔 ⊢ ∼ Semiformula.lMap inst (trAt me' opp' (.plays me opp aN)) :=
  pa_proves_neg_trAt_inst_of_pos me' opp' me opp hne hme hopp
    (pa_proves_trAt_inst hga me' opp' me opp b hme hopp hm hm' h)

/-- The search-free, unconditional form (no oracle): from an engine certificate of the play `b`. -/
theorem pa_proves_neg_trAt_inst_searchFree (me' opp' : PD.Prog) {k : ℕ} {me opp : PD.Prog}
    {b aN : PD.Action} (h : PD.AtomProvable k (.plays me opp b)) (hne : b ≠ aN)
    (hme : Proper me) (hopp : Proper opp) (hm : modestP me = true) (hm' : modestP opp = true)
    (hsme : me.hasSearch = false) (hsopp : opp.hasSearch = false) :
    𝗣𝗔 ⊢ ∼ Semiformula.lMap inst (trAt me' opp' (.plays me opp aN)) :=
  pa_proves_neg_trAt_inst_of_pos me' opp' me opp hne hme hopp
    (pa_proves_trAt_inst_searchFree me' opp' h hme hopp hm hm' hsme hsopp)

/-! ### The `atomNeg` leaf of T2-CORE -/

/-- **The `Leaf.atomNeg` shape of T2-CORE is discharged** on proper modest players (under
`GuardAgree`): `Core.tr Aι (.neg (.plays me opp aN))` is a PA theorem whenever `S` certifies the
play `b ≠ aN`. -/
theorem leaf_atomNeg_sound (hga : GuardAgree) {m : ℕ} {me opp : PD.Prog} {b aN : PD.Action}
    (h : PD.AtomProvable m (.plays me opp b)) (hne : b ≠ aN)
    (hme : Proper me) (hopp : Proper opp) (hm : modestP me = true) (hm' : modestP opp = true) :
    𝗣𝗔 ⊢ Core.tr Aι (.neg (.plays me opp aN)) :=
  pa_proves_neg_trAt_inst_of_pos me opp me opp hne hme hopp
    (pa_proves_trAt_inst_of_atomProvable hga me opp h hme hopp hm hm')

/-- The `Leaf.atomNeg` shape, search-free players, no oracle. -/
theorem leaf_atomNeg_sound_searchFree {m : ℕ} {me opp : PD.Prog} {b aN : PD.Action}
    (h : PD.AtomProvable m (.plays me opp b)) (hne : b ≠ aN)
    (hme : Proper me) (hopp : Proper opp) (hm : modestP me = true) (hm' : modestP opp = true)
    (hsme : me.hasSearch = false) (hsopp : opp.hasSearch = false) :
    𝗣𝗔 ⊢ Core.tr Aι (.neg (.plays me opp aN)) :=
  pa_proves_neg_trAt_inst_searchFree me opp h hne hme hopp hm hm' hsme hsopp

end ArithS

#print axioms ArithS.EvalGraph.unique_V'
#print axioms ArithS.models_trAt_plays_V
#print axioms ArithS.pa_proves_neg_trAt_inst
#print axioms ArithS.leaf_atomNeg_sound
#print axioms ArithS.leaf_atomNeg_sound_searchFree
