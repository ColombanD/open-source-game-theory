import ArithS.Tau.Watch

/-!
# ArithS.Tau.Stored — the stored (budget-abstracted) template of a guard over a closed watch (Phase 3e)

Under route (c) made generic (`Agents/CodeTermAbs.lean`, `Agents/Code.lean`), the template a `.search k φ p q`
node stores describes every closed program inside `φ` by `codeTermMetaAbs k` — its structural term with the
budget leaf `k` abstracted to the slot variable `#6`. For a guard over a closed WATCH `X_k` whose only budget is
`k` (a `W1` over a simple member, or a bot-wrapped simple searcher), that description is the watch's tower
`botT1 W.T1` (§1: the abstraction IS the tower), so the stored template is a CONSTANT above the watch's order
threshold (§4) — a `Semisentence LAct 13` in which the closed description `Dfix` carries the tower with the
budget slot in place of `k`. This module supplies:

* §1 the identification `codeTermMetaAbs K (pBot (W.code K)) = botT1 W.T1` (and for `pBot (SV g a K)`);
* §2 the denotation `absVal K c k` of the abstracted description of `c` at the budget `k` in any model, the
  evaluation of `closedDescAt (some K) c`, and the generic `.plays` shape `plAt D₁ D₂ a` of the thirteen-variable
  template with its truth equations for the three atom shapes a closed watch occurs in (`self × closed`,
  `closed × self`, `closed × closed`) and its transposition;
* §3 `qPlain` — a thirteen-variable template that never reads the member slots, filled with the frame triples
  and `#0` in the budget slot (dummy member triples) — and **its instance equation in every model**
  (`guardCodeB_plain_eq_instB`: the gate lemma `sysCloseTemplate_of_template₇` reduces it to the system case);
* §4 the constancy: `closedDescAt (some k) (pBot (W.code k)) = Dfix W` for `k ≥ W1.K`, and `absVal K (pBot (W.code K)) k
  = pBot (W.code k)` in every model — the value the watch's frame tower describes.
-/

set_option linter.constructorNameAsVariable false

namespace ArithS.Tau

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open LAct

/-! ### 1. The abstraction of a watch IS its tower -/

section identification

/-- The abstracted description of a searcher at its OWN budget is the one-variable searcher term. -/
lemma codeTermMetaAbs_search_self (K g a b : ℕ) :
    codeTermMetaAbs K (pSearch K g (pConst a) (pConst b)) = searchT1 g (pConst a) (pConst b) := by
  rw [codeTermMetaAbs_search, budgetT1_self, codeTermMetaAbs_const, codeTermMetaAbs_const, searchT1,
    bShift_ppairTermMeta, bShift_ppairTermMeta]

lemma codeTermMetaAbs_SM (s : SM) (K : ℕ) : codeTermMetaAbs K (s.code K) = s.T1 := by
  unfold SM.code SM.T1
  simp only [natCast_nat]
  exact codeTermMetaAbs_search_self K _ _ _

lemma codeTermMetaAbs_W1 (W : W1) (K : ℕ) : codeTermMetaAbs K (W.code K) = W.T1 := by
  unfold W1.code W1.T1
  simp only [natCast_nat]
  rw [codeTermMetaAbs_ite, codeTermMetaAbs_sim, codeTermMetaAbs_bot, codeTermMetaAbs_SM, codeTermMetaAbs_const,
    codeTermMetaAbs_const]
  rfl

lemma codeTermMetaAbs_botW1 (W : W1) (K : ℕ) : codeTermMetaAbs K (pBot (W.code K)) = botT1 W.T1 := by
  rw [codeTermMetaAbs_bot, codeTermMetaAbs_W1]; rfl

lemma codeTermMetaAbs_botSV (g : Semisentence LAct 6) (a : ℕ) (K : ℕ) :
    codeTermMetaAbs K (pBot (SV g a K)) = botT1 (searchT1 (⌜g⌝ : ℕ) (pConst a) (pConst (1 - a))) := by
  rw [SV_nat, codeTermMetaAbs_bot, codeTermMetaAbs_search_self]; rfl

end identification

/-! ### 2. The denotation of an abstracted description, and the `.plays` shape of the thirteen-variable template -/

section absVal

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- **The program the abstracted description of `c` (node budget `K`) denotes at the budget `k`**: the
re-valuation of the tower's value. -/
noncomputable def absVal (K c : ℕ) (k : V) : V :=
  revalue ((revalueUMeta c).val (s := stdReadingV V) ![] Empty.elim) ((revalueWMeta c).val (s := stdReadingV V) ![] Empty.elim)
    ((codeTermMetaAbs K (canonical c)).val (s := standardModel V) ![k] Empty.elim)

lemma absVal_def (K c : ℕ) (k : V) : absVal K c k =
    revalue ((revalueUMeta c).val (s := stdReadingV V) ![] Empty.elim) ((revalueWMeta c).val (s := stdReadingV V) ![] Empty.elim)
      ((codeTermMetaAbs K (canonical c)).val (s := standardModel V) ![k] Empty.elim) := rfl

omit [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
/-- The value of the abstracted description term with the budget term `t` in its slot. -/
lemma val_canonicalAbs_V {n : ℕ} (K c : ℕ) (t : Semiterm LAct Empty n) (e : Fin n → V) :
    (canonicalAbs K c t).val (s := stdReadingV V) e Empty.elim =
      (codeTermMetaAbs K (canonical c)).val (s := standardModel V) ![t.val (s := stdReadingV V) e Empty.elim] Empty.elim := by
  unfold canonicalAbs
  rw [Semiterm.val_substs, Semiterm.val_lMap, stdReadingV_lMap_emb]
  congr 1
  funext i; fin_cases i; rfl

omit [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
lemma cons_val_eight (x : V) (b : Fin 14 → V) : (x :> b) 8 = b 7 := rfl

/-- The abstracted closed description in `V` pins the denotation at the budget `b 7`. -/
lemma eval_closedDescAt_some_V (K c : ℕ) (b : Fin 14 → V) :
    Semiformula.Eval (s := stdReadingV V) b Empty.elim (closedDescAt (some K) c) ↔ b 0 = absVal K c (b 7) := by
  unfold closedDescAt descF
  rw [canonicalSlot_some]
  simp only [Semiformula.eval_ex, LogicalConnective.HomClass.map_and, LogicalConnective.Prop.and_eq,
    Semiformula.eval_rel, Semiformula.eval_substs, eval_relDesc_V, stdReadingV_rel_eq, Function.comp_def,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_succ, Matrix.vecHead, Matrix.vecTail, Semiterm.val_bvar, val_cl_V, val_canonicalAbs_V,
    cons_val_eight]
  constructor
  · rintro ⟨x, rfl, h⟩
    exact h
  · intro h
    exact ⟨_, rfl, h⟩

/-- The generic `.plays` shape of the thirteen-variable template: two descriptions `D₁ D₂` (in the fourteen-variable
frame of `closedDescAt`) and the action code `a`. -/
noncomputable def plAt (D₁ D₂ : Semisentence LAct 14) (a : ℕ) : Semisentence LAct 13 :=
  ∃¹ (∃¹ (∃¹ ((D₁ ⇜ ![#2, #3, #4, #5, #6, #7, #8, #9, #10, #11, #12, #13, #14, #15]) ⋏
    ((D₂ ⇜ ![#1, #3, #4, #5, #6, #7, #8, #9, #10, #11, #12, #13, #14, #15]) ⋏
      (evalG ⇜ ![#0, #2, #1, #2, cl (actT a)])))))

lemma templateAt_plays_eq (k₀ : Option ℕ) (p q : PD.Prog) (a : PD.Action) :
    templateAt (.plays p q a) k₀ = plAt (progGraphAt k₀ p) (progGraphAt k₀ q) (actCode a) := by
  rw [templateAt_plays]; rfl

/-- The self description, as the `D` of `plAt`. -/
noncomputable abbrev selfD : Semisentence LAct 14 := descF #1 #2 #3 #4

lemma progGraphAt_self (k₀ : Option ℕ) : progGraphAt k₀ .self = selfD := rfl

lemma progGraphAt_closed (k₀ : Option ℕ) {X : PD.Prog} (h1 : X ≠ .self) (h2 : X ≠ .opp) (h3 : pronounP X = false) :
    progGraphAt k₀ X = closedDescAt k₀ (progCode X) := by
  unfold progGraphAt; exact progAuxAt_of_ne k₀ h1 h2 h3 _

lemma lMap_swap_selfD : Semiformula.lMap swap selfD = selfD := by
  rw [lMap_swap_descF]; rfl

/-- τ on the `.plays` shape: the descriptions transposed, the action swapped. -/
theorem lMap_swap_plAt (D₁ D₂ : Semisentence LAct 14) (a : ℕ) :
    Semiformula.lMap swap (plAt D₁ D₂ a) = plAt (Semiformula.lMap swap D₁) (Semiformula.lMap swap D₂) (swapAction a) := by
  unfold plAt
  simp only [Semiformula.lMap_exs, LogicalConnective.HomClass.map_and, Semiformula.lMap_subst, lMap_swap_evalG]
  congr 4
  · congr 1; funext i; fin_cases i <;> rfl
  · congr 1
    · congr 1; funext i; fin_cases i <;> rfl
    · congr 1
      funext i
      fin_cases i
      · rfl
      · rfl
      · rfl
      · rfl
      · show Semiterm.lMap swap (cl (actT a)) = cl (actT (swapAction a))
        rw [lMap_swap_cl, lMap_swap_actT]

/-- The self description in `V`: `b 0 = revalue (b 2) (b 3) (b 1)`. -/
lemma eval_selfD_V (b : Fin 14 → V) :
    Semiformula.Eval (s := stdReadingV V) b Empty.elim selfD ↔ b 0 = revalue (b 2) (b 3) (b 1) := by
  unfold selfD descF
  simp only [Semiformula.eval_ex, LogicalConnective.HomClass.map_and, LogicalConnective.Prop.and_eq,
    Semiformula.eval_rel, Semiformula.eval_substs, eval_relDesc_V, stdReadingV_rel_eq, Function.comp_def,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_succ, Matrix.vecHead, Matrix.vecTail, Semiterm.val_bvar]
  constructor
  · rintro ⟨x, rfl, h⟩
    exact h
  · intro h
    exact ⟨_, rfl, h⟩

/-- **"Me plays `a` against the closed watch"** in every model. -/
theorem eval_plAt_self_closed (K c a : ℕ) (b : Fin 13 → V) :
    Semiformula.Eval (s := stdReadingV V) b Empty.elim (plAt selfD (closedDescAt (some K) c) a) ↔
      ∃ n, EvalGraph n (revalue (b 1) (b 2) (b 0)) (absVal K c (b 6)) (revalue (b 1) (b 2) (b 0)) (a : V) := by
  unfold plAt
  simp only [Semiformula.eval_substs, Semiformula.eval_ex, LogicalConnective.HomClass.map_and,
    LogicalConnective.Prop.and_eq, eval_selfD_V, eval_closedDescAt_some_V, eval_evalG_V, Function.comp_def,
    Matrix.cons_val, Semiterm.val_bvar, val_cl_V, val_actT_V]
  constructor
  · rintro ⟨x, y, N, rfl, rfl, h⟩
    exact ⟨N, h⟩
  · rintro ⟨N, h⟩
    exact ⟨_, _, N, rfl, rfl, h⟩

/-- **"The closed watch plays `a` against me"** in every model. -/
theorem eval_plAt_closed_self (K c a : ℕ) (b : Fin 13 → V) :
    Semiformula.Eval (s := stdReadingV V) b Empty.elim (plAt (closedDescAt (some K) c) selfD a) ↔
      ∃ n, EvalGraph n (absVal K c (b 6)) (revalue (b 1) (b 2) (b 0)) (absVal K c (b 6)) (a : V) := by
  unfold plAt
  simp only [Semiformula.eval_substs, Semiformula.eval_ex, LogicalConnective.HomClass.map_and,
    LogicalConnective.Prop.and_eq, eval_selfD_V, eval_closedDescAt_some_V, eval_evalG_V, Function.comp_def,
    Matrix.cons_val, Semiterm.val_bvar, val_cl_V, val_actT_V]
  constructor
  · rintro ⟨x, y, N, rfl, rfl, h⟩
    exact ⟨N, h⟩
  · rintro ⟨N, h⟩
    exact ⟨_, _, N, rfl, rfl, h⟩

/-- **"The closed watch plays `a` against itself"** in every model. -/
theorem eval_plAt_closed_closed (K c a : ℕ) (b : Fin 13 → V) :
    Semiformula.Eval (s := stdReadingV V) b Empty.elim (plAt (closedDescAt (some K) c) (closedDescAt (some K) c) a) ↔
      ∃ n, EvalGraph n (absVal K c (b 6)) (absVal K c (b 6)) (absVal K c (b 6)) (a : V) := by
  unfold plAt
  simp only [Semiformula.eval_substs, Semiformula.eval_ex, LogicalConnective.HomClass.map_and,
    LogicalConnective.Prop.and_eq, eval_closedDescAt_some_V, eval_evalG_V, Function.comp_def,
    Matrix.cons_val, Semiterm.val_bvar, val_cl_V, val_actT_V]
  constructor
  · rintro ⟨x, y, N, rfl, rfl, h⟩
    exact ⟨N, h⟩
  · rintro ⟨N, h⟩
    exact ⟨_, _, N, rfl, rfl, h⟩

end absVal

/-! ### 3. `qPlain`: a member-blind thirteen-variable template filled with the frame triples, and its instance equation -/

section plain

/-- A τ-fixed closed program for the dummy member slot `0` (the system of the empty list, member `0`). -/
noncomputable def P₀ : ℕ := pSys pNil 0
/-- …and for the dummy member slot `1`. -/
noncomputable def P₁ : ℕ := pSys pNil 1

lemma transposeCode_P₀ : transposeCode P₀ = P₀ := by
  unfold P₀ transposeCode; rw [revalue_sys, revalue_nil]
lemma transposeCode_P₁ : transposeCode P₁ = P₁ := by
  unfold P₁ transposeCode; rw [revalue_sys, revalue_nil]

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

lemma cast_P₀ : ((P₀ : ℕ) : V) = pSys pNil 0 := by
  unfold P₀; rw [cast_pSys]; simp [pNil]
lemma cast_P₁ : ((P₁ : ℕ) : V) = pSys pNil 1 := by
  unfold P₁; rw [cast_pSys]; simp [pNil]

/-- **A member-blind template filled with the frame triples and `#0` in the budget slot**; the member slots carry
the generic closed triples of `P₀`/`P₁` (never read). -/
noncomputable def qPlain (g : Semisentence LAct 13) (X : Semiterm LAct Empty 1) (U W : ClosedSemiterm LAct 0)
    (X' : Semiterm LAct Empty 1) (U' W' : ClosedSemiterm LAct 0) : Semisentence LAct 1 :=
  qT13 g X U W X' U' W' (cl (canonicalMeta P₀)) (revalueUMeta P₀) (revalueWMeta P₀)
    (cl (canonicalMeta P₁)) (revalueUMeta P₁) (revalueWMeta P₁)

lemma lMap_swap_qPlain (g : Semisentence LAct 13) (X : Semiterm LAct Empty 1) (U W : ClosedSemiterm LAct 0)
    (X' : Semiterm LAct Empty 1) (U' W' : ClosedSemiterm LAct 0) :
    Semiformula.lMap swap (qPlain g X U W X' U' W') =
      qPlain (Semiformula.lMap swap g) (Semiterm.lMap swap X) (Semiterm.lMap swap U) (Semiterm.lMap swap W)
        (Semiterm.lMap swap X') (Semiterm.lMap swap U') (Semiterm.lMap swap W') := by
  unfold qPlain
  rw [lMap_swap_qT13]
  simp only [lMap_swap_cl, lMap_swap_canonicalMeta', lMap_swap_revalueUMeta, lMap_swap_revalueWMeta,
    transposeCode_P₀, transposeCode_P₁]

omit [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
/-- The truth of a `qPlain` instance at `k` is the truth of the template at the frame values (the member slots
carry the dummies). -/
theorem eval_qPlain_iff (g : Semisentence LAct 13) (X : Semiterm LAct Empty 1) (U W : ClosedSemiterm LAct 0)
    (X' : Semiterm LAct Empty 1) (U' W' : ClosedSemiterm LAct 0) (k : V) :
    Semiformula.Eval (s := stdReadingV V) ![k] Empty.elim (qPlain g X U W X' U' W') ↔
      Semiformula.Eval (s := stdReadingV V)
        ![X.val (s := stdReadingV V) ![k] Empty.elim, U.val (s := stdReadingV V) ![] Empty.elim,
          W.val (s := stdReadingV V) ![] Empty.elim, X'.val (s := stdReadingV V) ![k] Empty.elim,
          U'.val (s := stdReadingV V) ![] Empty.elim, W'.val (s := stdReadingV V) ![] Empty.elim, k,
          (cl (canonicalMeta P₀) : Semiterm LAct Empty 1).val (s := stdReadingV V) ![k] Empty.elim,
          (revalueUMeta P₀).val (s := stdReadingV V) ![] Empty.elim, (revalueWMeta P₀).val (s := stdReadingV V) ![] Empty.elim,
          (cl (canonicalMeta P₁) : Semiterm LAct Empty 1).val (s := stdReadingV V) ![k] Empty.elim,
          (revalueUMeta P₁).val (s := stdReadingV V) ![] Empty.elim, (revalueWMeta P₁).val (s := stdReadingV V) ![] Empty.elim]
        Empty.elim g := by
  unfold qPlain; exact eval_qT13_iff _ _ _ _ _ _ _ _ _ _ _ _ _ k

/-- **The instance equation of a member-blind template in every model**: the code the searcher consults on the
stored template `g` in the frame `(me, opp)` at the budget `k` is the `binNumeral k`-instance of `⌜qPlain g …⌝`,
whenever the two triples describe the frame players (`sysCloseTemplate_of_template₇` + the system equation). -/
theorem guardCodeB_plain_eq_instB {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (g : Semisentence LAct 13) (hg : IsSemiformula LAct 7 ((⌜g⌝ : ℕ) : V)) (k : V)
    (X : Semiterm LAct Empty 1) (U W : ClosedSemiterm LAct 0) (X' : Semiterm LAct Empty 1) (U' W' : ClosedSemiterm LAct 0)
    {me opp : V}
    (hX : termSubst LAct (binNumeral k ∷ (0 : V)) (⌜(Rew.emb X : SyntacticSemiterm LAct 1)⌝ : V) = codeTerm (canonical me))
    (hU : (⌜U⌝ : V) = revalueU me) (hW : (⌜W⌝ : V) = revalueW me)
    (hX' : termSubst LAct (binNumeral k ∷ (0 : V)) (⌜(Rew.emb X' : SyntacticSemiterm LAct 1)⌝ : V) = codeTerm (canonical opp))
    (hU' : (⌜U'⌝ : V) = revalueU opp) (hW' : (⌜W'⌝ : V) = revalueW opp) :
    guardCodeB ((⌜g⌝ : ℕ) : V) me opp k = instB (⌜qPlain g X U W X' U' W'⌝ : V) k := by
  rw [← sysCloseTemplate_of_template₇ hg (pNil : V), coe_quote_sentence₁₃]
  unfold qPlain
  have h0 := (describes_closed P₀).hX V k
  have h0U := (describes_closed P₀).hU V k
  have h0W := (describes_closed P₀).hW V k
  have h1 := (describes_closed P₁).hX V k
  have h1U := (describes_closed P₁).hU V k
  have h1W := (describes_closed P₁).hW V k
  rw [descVal_closed, cast_P₀] at h0 h0U h0W
  rw [descVal_closed, cast_P₁] at h1 h1U h1W
  exact guardCodeB_sysClose_eq_instB g k (pNil : V) X U W X' U' W' _ _ _ _ _ _ hX hU hW hX' hU' hW' h0 h0U h0W h1 h1U h1W

end plain

/-! ### 4. The constancy of the stored description of a watch -/

section constancy

namespace W1

/-- **The fixed closed description of the watch**: the tower with the budget slot in place of the budget. -/
noncomputable def Dfix (W : W1) : Semisentence LAct 14 :=
  descF #1 (Rew.subst ![#8] (Semiterm.lMap emb (botT1 W.can.T1))) (cl W.uT) (cl W.wT)

/-- Foundation's `≤` at ℕ from `Nat.le`, in the shape the V-generic lemmas expect. -/
theorem canonical_code_nat (W : W1) {k : ℕ} (hk : W1.K ≤ k) : canonical (W.code k) = W.can.code k :=
  W1.canonical_code W (le_def.mpr (Nat.eq_or_lt_of_le (by rw [natCast_nat]; exact hk)))

theorem code_lt_tr_nat (W : W1) {k : ℕ} (hk : W1.K ≤ k) (h : W.orig) : W.code k < W.tr.code k :=
  W1.code_lt_tr W (le_def.mpr (Nat.eq_or_lt_of_le (by rw [natCast_nat]; exact hk))) h

theorem tr_lt_code_nat (W : W1) {k : ℕ} (hk : W1.K ≤ k) (h : ¬ W.orig) : W.tr.code k < W.code k :=
  W1.tr_lt_code W (le_def.mpr (Nat.eq_or_lt_of_le (by rw [natCast_nat]; exact hk))) h

theorem canonical_tr_code_nat (W : W1) {k : ℕ} (hk : W1.K ≤ k) : canonical (W.tr.code k) = W.can.code k :=
  W1.canonical_tr_code W (le_def.mpr (Nat.eq_or_lt_of_le (by rw [natCast_nat]; exact hk)))

theorem revalueUMeta_code (W : W1) {k : ℕ} (hk : W1.K ≤ k) : revalueUMeta (W.code k) = W.uT := by
  unfold revalueUMeta W1.uT
  rw [transposeCode_code]
  by_cases h : W.orig
  · rw [if_pos (code_lt_tr_nat W hk h), if_pos h]
  · rw [if_neg (lt_asymm (tr_lt_code_nat W hk h)), if_pos (tr_lt_code_nat W hk h), if_neg h]

theorem revalueWMeta_code (W : W1) {k : ℕ} (hk : W1.K ≤ k) : revalueWMeta (W.code k) = W.wT := by
  unfold revalueWMeta W1.wT
  rw [transposeCode_code]
  by_cases h : W.orig
  · rw [if_pos (code_lt_tr_nat W hk h), if_pos h]
  · rw [if_neg (lt_asymm (tr_lt_code_nat W hk h)), if_pos (tr_lt_code_nat W hk h), if_neg h]

theorem revalueUMeta_tr_code (W : W1) {k : ℕ} (hk : W1.K ≤ k) :
    revalueUMeta (W.tr.code k) = Semiterm.lMap swap W.uT := by
  have e : transposeCode (W.tr.code k) = W.code k := by rw [← transposeCode_code, transposeCode_transposeCode]
  unfold revalueUMeta W1.uT
  rw [e]
  by_cases h : W.orig
  · rw [if_neg (lt_asymm (code_lt_tr_nat W hk h)), if_pos (code_lt_tr_nat W hk h), if_pos h, lMap_swap_cterm_C]
  · rw [if_pos (tr_lt_code_nat W hk h), if_neg h, lMap_swap_cterm_D]

theorem revalueWMeta_tr_code (W : W1) {k : ℕ} (hk : W1.K ≤ k) :
    revalueWMeta (W.tr.code k) = Semiterm.lMap swap W.wT := by
  have e : transposeCode (W.tr.code k) = W.code k := by rw [← transposeCode_code, transposeCode_transposeCode]
  unfold revalueWMeta W1.wT
  rw [e]
  by_cases h : W.orig
  · rw [if_neg (lt_asymm (code_lt_tr_nat W hk h)), if_pos (code_lt_tr_nat W hk h), if_pos h, lMap_swap_cterm_D]
  · rw [if_pos (tr_lt_code_nat W hk h), if_neg h, lMap_swap_cterm_C]

/-- **The stored description of the bot-wrapped watch is constant above the threshold.** -/
theorem closedDescAt_code (W : W1) {k : ℕ} (hk : W1.K ≤ k) : closedDescAt (some k) (pBot (W.code k)) = W.Dfix := by
  unfold closedDescAt Dfix
  rw [canonicalSlot_some]
  unfold canonicalAbs
  rw [canonical_pBot, canonical_code_nat W hk, codeTermMetaAbs_botW1, revalueUMeta_pBot, revalueWMeta_pBot,
    revalueUMeta_code W hk, revalueWMeta_code W hk]

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- **The abstracted description denotes the watch at the budget `k`, in every model.** -/
theorem absVal_code (W : W1) {K : ℕ} (hK : W1.K ≤ K) (k : V) : absVal K (pBot (W.code K)) k = pBot (W.code k) := by
  rw [absVal_def, canonical_pBot, canonical_code_nat W hK, codeTermMetaAbs_botW1, revalueUMeta_pBot, revalueWMeta_pBot,
    revalueUMeta_code W hK, revalueWMeta_code W hK, val_botT1_V, W1.val_T1_V, revalue_bot, revalue_val_uT_wT]

/-- …and the abstracted description of its TRANSPOSITION denotes the transposed watch. -/
theorem absVal_tr_code (W : W1) {K : ℕ} (hK : W1.K ≤ K) (k : V) :
    absVal K (transposeCode (pBot (W.code K))) k = pBot (W.tr.code k) := by
  rw [absVal_def, transposeCode_pBot, transposeCode_code, canonical_pBot, canonical_tr_code_nat W hK,
    codeTermMetaAbs_botW1, revalueUMeta_pBot, revalueWMeta_pBot, revalueUMeta_tr_code W hK, revalueWMeta_tr_code W hK,
    val_botT1_V, W1.val_T1_V, revalue_bot, revalue_val_uT_wT_swap]

end W1

/-! #### The bot-wrapped engine searcher `pBot (SV g a k)` (τ(CupodTroll)'s instance) -/

section botSV

variable (g : Semisentence LAct 6) (a : ℕ) (ha : a = 0 ∨ a = 1)
include ha

omit ha in
lemma codeTermMetaAbs_pS (K : ℕ) : codeTermMetaAbs K (pS g a) = Rew.bShift (codeTermMeta (pS g a)) := by
  unfold pS; split_ifs <;> exact codeTermMetaAbs_const _ _
omit ha in
lemma codeTermMetaAbs_qS (K : ℕ) : codeTermMetaAbs K (qS g a) = Rew.bShift (codeTermMeta (qS g a)) := by
  unfold qS; split_ifs <;> exact codeTermMetaAbs_const _ _

omit ha in
lemma codeTermMetaAbs_search_leaves (K gg p q : ℕ) (hp : codeTermMetaAbs K p = Rew.bShift (codeTermMeta p))
    (hq : codeTermMetaAbs K q = Rew.bShift (codeTermMeta q)) :
    codeTermMetaAbs K (pSearch K gg p q) = searchT1 gg p q := by
  rw [codeTermMetaAbs_search, budgetT1_self, hp, hq, searchT1, bShift_ppairTermMeta, bShift_ppairTermMeta]

/-- The abstraction of the canonical bot-wrapped searcher is the bot tower `TBS`'s ℒₒᵣ-term. -/
theorem codeTermMetaAbs_canonical_botSV (K : ℕ) :
    codeTermMetaAbs K (canonical (pBot (SV g a K))) = botT1 (searchT1 (gS g a) (pS g a) (qS g a)) := by
  have hc : canonical (SV (V := ℕ) g a K) = pSearch K (gS g a) (pS g a) (qS g a) := by
    have := canonical_SV (V := ℕ) g a ha K
    simpa only [natCast_nat] using this
  rw [canonical_pBot, hc, codeTermMetaAbs_bot, codeTermMetaAbs_search_leaves K _ _ _ (codeTermMetaAbs_pS g a K)
    (codeTermMetaAbs_qS g a K)]
  rfl

theorem revalueUMeta_SV (K : ℕ) : revalueUMeta (SV (V := ℕ) g a K) = uS g a := by
  unfold revalueUMeta uS
  rw [transposeCode_SV g a ha]
  by_cases h1 : innerS g a < innerS (Semiformula.lMap swap g) (1 - a)
  · rw [if_pos ((SV_lt_SVT_iff g a ha K).mpr h1), if_pos h1]
  · rw [if_neg (fun h ↦ h1 ((SV_lt_SVT_iff g a ha K).mp h)), if_neg h1]
    by_cases h2 : innerS (Semiformula.lMap swap g) (1 - a) < innerS g a
    · rw [if_pos ((SVT_lt_SV_iff g a ha K).mpr h2), if_pos h2]
    · rw [if_neg (fun h ↦ h2 ((SVT_lt_SV_iff g a ha K).mp h)), if_neg h2]

theorem revalueWMeta_SV (K : ℕ) : revalueWMeta (SV (V := ℕ) g a K) = wS g a := by
  unfold revalueWMeta wS
  rw [transposeCode_SV g a ha]
  by_cases h1 : innerS g a < innerS (Semiformula.lMap swap g) (1 - a)
  · rw [if_pos ((SV_lt_SVT_iff g a ha K).mpr h1), if_pos h1]
  · rw [if_neg (fun h ↦ h1 ((SV_lt_SVT_iff g a ha K).mp h)), if_neg h1]
    by_cases h2 : innerS (Semiformula.lMap swap g) (1 - a) < innerS g a
    · rw [if_pos ((SVT_lt_SV_iff g a ha K).mpr h2), if_pos h2]
    · rw [if_neg (fun h ↦ h2 ((SVT_lt_SV_iff g a ha K).mp h)), if_neg h2]

/-- The re-valuation term of the TRANSPOSED searcher is the transposed term. -/
theorem revalueUMeta_SVT (K : ℕ) :
    revalueUMeta (SV (V := ℕ) (Semiformula.lMap swap g) (1 - a) K) = Semiterm.lMap swap (uS g a) := by
  have e : transposeCode (SV (V := ℕ) (Semiformula.lMap swap g) (1 - a) K) = SV g a K := by
    rw [← transposeCode_SV g a ha, transposeCode_transposeCode]
  unfold revalueUMeta uS
  rw [e]
  by_cases h1 : innerS g a < innerS (Semiformula.lMap swap g) (1 - a)
  · rw [if_neg (lt_asymm ((SV_lt_SVT_iff g a ha K).mpr h1)), if_pos ((SV_lt_SVT_iff g a ha K).mpr h1), if_pos h1,
      lMap_swap_cterm_C]
  · rw [if_neg h1]
    by_cases h2 : innerS (Semiformula.lMap swap g) (1 - a) < innerS g a
    · rw [if_pos ((SVT_lt_SV_iff g a ha K).mpr h2), if_pos h2, lMap_swap_cterm_D]
    · rw [if_neg (fun h ↦ h2 ((SVT_lt_SV_iff g a ha K).mp h)), if_neg (fun h ↦ h1 ((SV_lt_SVT_iff g a ha K).mp h)),
        if_neg h2, lMap_swap_numT]

theorem revalueWMeta_SVT (K : ℕ) :
    revalueWMeta (SV (V := ℕ) (Semiformula.lMap swap g) (1 - a) K) = Semiterm.lMap swap (wS g a) := by
  have e : transposeCode (SV (V := ℕ) (Semiformula.lMap swap g) (1 - a) K) = SV g a K := by
    rw [← transposeCode_SV g a ha, transposeCode_transposeCode]
  unfold revalueWMeta wS
  rw [e]
  by_cases h1 : innerS g a < innerS (Semiformula.lMap swap g) (1 - a)
  · rw [if_neg (lt_asymm ((SV_lt_SVT_iff g a ha K).mpr h1)), if_pos ((SV_lt_SVT_iff g a ha K).mpr h1), if_pos h1,
      lMap_swap_cterm_D]
  · rw [if_neg h1]
    by_cases h2 : innerS (Semiformula.lMap swap g) (1 - a) < innerS g a
    · rw [if_pos ((SVT_lt_SV_iff g a ha K).mpr h2), if_pos h2, lMap_swap_cterm_C]
    · rw [if_neg (fun h ↦ h2 ((SVT_lt_SV_iff g a ha K).mp h)), if_neg (fun h ↦ h1 ((SV_lt_SVT_iff g a ha K).mp h)),
        if_neg h2, lMap_swap_numT]

/-- The fixed closed description of the bot-wrapped searcher. -/
noncomputable def DfixSV : Semisentence LAct 14 :=
  descF #1 (Rew.subst ![#8] (Semiterm.lMap emb (botT1 (searchT1 (gS g a) (pS g a) (qS g a))))) (cl (uS g a)) (cl (wS g a))

theorem closedDescAt_botSV (k : ℕ) : closedDescAt (some k) (pBot (SV (V := ℕ) g a k)) = DfixSV g a := by
  unfold closedDescAt DfixSV
  rw [canonicalSlot_some]
  unfold canonicalAbs
  rw [codeTermMetaAbs_canonical_botSV g a ha, revalueUMeta_pBot, revalueWMeta_pBot, revalueUMeta_SV g a ha,
    revalueWMeta_SV g a ha]

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem absVal_botSV (K : ℕ) (k : V) : absVal K (pBot (SV (V := ℕ) g a K)) k = pBot (SV g a k) := by
  rw [absVal_def, codeTermMetaAbs_canonical_botSV g a ha, revalueUMeta_pBot, revalueWMeta_pBot, revalueUMeta_SV g a ha,
    revalueWMeta_SV g a ha, val_botT1_V, val_searchT1_V, revalue_bot, ← canonical_SV g a ha, revalue_val_uS_wS_V g a ha]

theorem absVal_tr_botSV (K : ℕ) (k : V) :
    absVal K (transposeCode (pBot (SV (V := ℕ) g a K))) k = pBot (SV (Semiformula.lMap swap g) (1 - a) k) := by
  have hc : canonical (pBot (SV (V := ℕ) (Semiformula.lMap swap g) (1 - a) K)) = canonical (pBot (SV g a K)) := by
    rw [← transposeCode_SV g a ha, ← transposeCode_pBot, canonical_transposeCode]
  rw [absVal_def, transposeCode_pBot, transposeCode_SV g a ha, hc, codeTermMetaAbs_canonical_botSV g a ha, revalueUMeta_pBot,
    revalueWMeta_pBot, revalueUMeta_SVT g a ha, revalueWMeta_SVT g a ha, val_botT1_V, val_searchT1_V, revalue_bot,
    ← canonical_SV g a ha, revalue_val_uST_wST_V g a ha]

end botSV

end constancy

end ArithS.Tau
