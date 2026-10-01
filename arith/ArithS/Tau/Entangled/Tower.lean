import ArithS.Tau.Entangled.Order
import ArithS.Cells.Common.Templates

/-!
# ArithS.Tau.Entangled.Tower — simple members, two-member systems, their canonical codes and description towers

The Löb families of the entangled bits live on the member slots (`SPRIME_SOURCE_OF_TRUTH.md` §2.5): the closed
member guard names the partner `.bot (.sys defs j)` by the description triple of `pSys d j` —
`(codeTerm (canonical (pSys d j)), revalueU (pSys d j), revalueW (pSys d j))` (`descriptionsSys`). For the
family formula to be the `binNumeral k`-instance of ONE fixed formula, that triple must be, uniformly in `k`
(in every model), the value of a fixed one-variable term: this module builds it for systems of two SIMPLE
members (`pSearch k ⌜g⌝ (pConst a) (pConst (1 - a))`, `g` a thirteen-variable template, `a ∈ {0, 1}` —
the shape of every Dupoc/Cupod/CIMCIC/DIMCID member).

* `SM` (a simple member) and `Sys2` (two of them): the codes in every model, their transpositions
  (`transposeCode_code`: the member list is re-valued member by member, `revalue_sys`/`revalue_cons`), the
  budget-free inner parts (`SM.inner`, never evaluated).
* **The τ-order is decided by the second member** above the threshold `Sys2.K` (`Order.lean`): `Sys2.orig`
  ("the original list is below its transposition") is a fixed Prop, and `canonical (S.code j k)` is the code of
  the canonical shapes `S.can` (`canonical_code`), the re-valuation terms the matching constants
  (`revalueU_code`, `revalueW_code`) — exactly `canonical_SV`/`revalueU_SV` with the member list in place of
  the inner triple.
* **The towers**: the one-variable ℒₒᵣ-terms `consT1`/`sysT1`/`nilT1` (`searchT1`'s shape), the member tower
  `Sys2.TM j` (the slot term) and the frame tower `Sys2.TX j` (`botT1` of it), with their values
  (`val_TM_V`, `val_TX_V`) and the substitution of the budget into their codes (`termSubst_TM`, `termSubst_TX`).
* **`Sys2.describesMem`/`Sys2.describesBot`**: `DescribesAbove S.K` for `S.code j k` and `pBot (S.code j k)` —
  the hypotheses of the instance equations (`Family.lean`).
-/

set_option linter.constructorNameAsVariable false

namespace ArithS.Tau

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open LAct

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ### 0. Quotes of thirteen-variable templates, cast and transposed -/

lemma coe_quote_sentence₁₃ (σ : Semisentence LAct 13) : ((⌜σ⌝ : ℕ) : V) = ⌜σ⌝ := by
  rw [Sentence.quote_def, Sentence.quote_def, Semiformula.coe_quote_eq_quote]

/-- The code-level τ of a quoted semisentence (any arity), on the CAST of its ℕ-code. -/
lemma revalueTemplate_cast_quote {n : ℕ} (σ : Semisentence LAct n) :
    revalueTemplate 1 0 ((⌜σ⌝ : ℕ) : V) = ((⌜Semiformula.lMap swap σ⌝ : ℕ) : V) := by
  have h := DefinedFunction.shigmaOne_absolute_func V (revalueTemplate.defined (V := ℕ))
    (revalueTemplate.defined (V := V)) ![1, 0, (⌜σ⌝ : ℕ)]
  simp only [Function.comp_def, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_succ, Matrix.vecHead, Matrix.vecTail, Nat.cast_one, Nat.cast_zero] at h
  rw [revalueTemplate_quote_sentence] at h
  exact h.symm

/-! ### 1. Simple members -/

/-- A simple member: the thirteen-variable template `g` of its raw guard and its then-action `a ∈ {0, 1}`
(the else-action is `1 - a`). -/
structure SM where
  g : Semisentence LAct 13
  a : ℕ
  ha : a = 0 ∨ a = 1

namespace SM

/-- The member's code at the budget `k`, in every model. -/
noncomputable def code (s : SM) (k : V) : V :=
  pSearch k ((⌜s.g⌝ : ℕ) : V) (pConst (s.a : V)) (pConst ((1 - s.a : ℕ) : V))

/-- The budget-free inner part (never evaluated). -/
noncomputable def inner (s : SM) : ℕ := ppair (⌜s.g⌝ : ℕ) (ppair (pConst s.a) (pConst (1 - s.a)))

lemma inner_def (s : SM) : s.inner = ppair (⌜s.g⌝ : ℕ) (ppair (pConst s.a) (pConst (1 - s.a))) := rfl

attribute [irreducible] inner

lemma cast_inner (s : SM) : ((s.inner : ℕ) : V) = ppair ((⌜s.g⌝ : ℕ) : V) (ppair (pConst (s.a : V)) (pConst ((1 - s.a : ℕ) : V))) := by
  rw [inner_def, cast_ppair, cast_ppair, cast_pConst, cast_pConst]

lemma code_eq_inner (s : SM) (k : V) : s.code k = ppair 6 (ppair k (s.inner : V)) + 1 := by
  rw [cast_inner]; rfl

/-- The transposed member: the transposed template, the actions exchanged. -/
noncomputable def tr (s : SM) : SM :=
  ⟨Semiformula.lMap swap s.g, 1 - s.a, by rcases s.ha with h | h <;> simp [h]⟩

lemma tr_g (s : SM) : s.tr.g = Semiformula.lMap swap s.g := rfl
lemma tr_a (s : SM) : s.tr.a = 1 - s.a := rfl

lemma one_sub_one_sub' (s : SM) : 1 - (1 - s.a) = s.a := by rcases s.ha with h | h <;> simp [h]

/-- τ on a member's code. -/
theorem transposeCode_code (s : SM) (k : V) : transposeCode (s.code k) = s.tr.code k := by
  unfold code transposeCode
  rw [revalue_search, revalue_const, revalue_const, revalueTemplate_cast_quote]
  show pSearch k _ (pConst (swapAction _)) (pConst (swapAction _)) = _
  rw [swapAction_cast s.a s.ha, swapAction_cast' s.a s.ha, tr_g, tr_a, one_sub_one_sub']

/-- A member is never τ-fixed: its inner part differs from the transposed one (the actions). -/
lemma inner_ne_tr (s : SM) : s.inner ≠ s.tr.inner := by
  intro h
  rw [inner_def, inner_def] at h
  obtain ⟨_, h2⟩ := ppair_inj h
  obtain ⟨h3, _⟩ := ppair_inj h2
  have := pConst_inj h3
  rcases s.ha with h0 | h0 <;> simp [tr_a, h0] at this

lemma code_lt_iff (s t : SM) (k : V) : s.code k < t.code k ↔ s.inner < t.inner := by
  rw [code_eq_inner, code_eq_inner, pSearchInner_lt_iff, Nat.cast_lt]

end SM

/-! ### 2. Two-member systems -/

/-- A two-member system of simple members: member `0` (the row's bot) and member `1` (the hypothesis). -/
structure Sys2 where
  m₀ : SM
  m₁ : SM

namespace Sys2

/-- The member list code at the budget `k`. -/
noncomputable def D (S : Sys2) (k : V) : V := pCons (S.m₀.code k) (pCons (S.m₁.code k) pNil)

/-- The code of member `j` of the system (`pSys d j`), at the budget `k`. -/
noncomputable def code (S : Sys2) (j : ℕ) (k : V) : V := pSys (S.D k) (j : V)

/-- The transposed system: both members transposed. -/
noncomputable def tr (S : Sys2) : Sys2 := ⟨S.m₀.tr, S.m₁.tr⟩

lemma tr_m₀ (S : Sys2) : S.tr.m₀ = S.m₀.tr := rfl
lemma tr_m₁ (S : Sys2) : S.tr.m₁ = S.m₁.tr := rfl

theorem transposeCode_D (S : Sys2) (k : V) : transposeCode (S.D k) = S.tr.D k := by
  unfold D transposeCode
  rw [revalue_cons, revalue_cons, revalue_nil]
  show pCons (transposeCode _) (pCons (transposeCode _) pNil) = _
  rw [SM.transposeCode_code, SM.transposeCode_code]; rfl

theorem transposeCode_code (S : Sys2) (j : ℕ) (k : V) : transposeCode (S.code j k) = S.tr.code j k := by
  unfold code transposeCode
  rw [revalue_sys]
  show pSys (transposeCode _) _ = _
  rw [transposeCode_D]

/-- **The decision**: the original list is below its transposition iff the second member's inner part is below
its transposed one (a fixed Prop, decided classically). -/
def orig (S : Sys2) : Prop := S.m₁.inner < S.m₁.tr.inner

/-- The threshold above which the τ-order is uniform: the first member's inner parts (never evaluated). -/
noncomputable def K (S : Sys2) : ℕ := S.m₀.inner + S.m₀.tr.inner + 3

lemma K_def (S : Sys2) : S.K = S.m₀.inner + S.m₀.tr.inner + 3 := rfl

attribute [irreducible] K

lemma three_le_of_K {S : Sys2} {k : V} (hk : (S.K : V) ≤ k) : 3 ≤ k := by
  rw [K_def] at hk; push_cast at hk
  exact le_trans (le_add_self) hk

lemma inner₀_le_of_K {S : Sys2} {k : V} (hk : (S.K : V) ≤ k) : (S.m₀.inner : V) ≤ k := by
  rw [K_def] at hk; push_cast at hk
  exact le_trans (le_trans le_self_add le_self_add) hk

lemma innerT₀_le_of_K {S : Sys2} {k : V} (hk : (S.K : V) ≤ k) : (S.m₀.tr.inner : V) ≤ k := by
  rw [K_def] at hk; push_cast at hk
  exact le_trans (le_trans le_add_self le_self_add) hk

/-- Above the threshold, `orig` puts the system below its transposition. -/
theorem code_lt_tr {S : Sys2} {k : V} (hk : (S.K : V) ≤ k) (h : S.orig) (j : ℕ) : S.code j k < S.tr.code j k := by
  unfold code D
  apply sys2_lt_of_member1
  · exact lt_iff_succ_le.mp ((SM.code_lt_iff _ _ k).mpr h)
  · rw [SM.code_eq_inner, SM.code_eq_inner]
    exact member1_dominates k _ _ (inner₀_le_of_K hk) (three_le_of_K hk)

/-- Above the threshold, `¬ orig` puts the transposition below the system. -/
theorem tr_lt_code {S : Sys2} {k : V} (hk : (S.K : V) ≤ k) (h : ¬ S.orig) (j : ℕ) : S.tr.code j k < S.code j k := by
  have h' : S.m₁.tr.inner < S.m₁.inner := lt_of_le_of_ne (not_lt.mp h) (Ne.symm (SM.inner_ne_tr _))
  unfold code D
  apply sys2_lt_of_member1
  · exact lt_iff_succ_le.mp ((SM.code_lt_iff _ _ k).mpr h')
  · rw [SM.code_eq_inner, SM.code_eq_inner]
    exact member1_dominates k _ _ (innerT₀_le_of_K hk) (three_le_of_K hk)

open scoped Classical in
/-- The canonical shapes: the system itself when `orig`, its transposition otherwise. -/
noncomputable def can (S : Sys2) : Sys2 := if S.orig then S else S.tr

open scoped Classical in
/-- The first re-valuation term of the canonical description (no tie: the members are never τ-fixed). -/
noncomputable def uT (S : Sys2) : ClosedSemiterm LAct 0 := if S.orig then cterm Act.C else cterm Act.D
open scoped Classical in
noncomputable def wT (S : Sys2) : ClosedSemiterm LAct 0 := if S.orig then cterm Act.D else cterm Act.C

theorem canonical_code {S : Sys2} {k : V} (hk : (S.K : V) ≤ k) (j : ℕ) :
    canonical (S.code j k) = S.can.code j k := by
  unfold can
  by_cases h : S.orig
  · rw [if_pos h, canonical_of_lt (by rw [transposeCode_code]; exact code_lt_tr hk h j)]
  · rw [if_neg h, canonical_of_gt (by rw [transposeCode_code]; exact tr_lt_code hk h j), transposeCode_code]

theorem revalueU_code {S : Sys2} {k : V} (hk : (S.K : V) ≤ k) (j : ℕ) : revalueU (S.code j k) = (⌜S.uT⌝ : V) := by
  unfold revalueU uT
  rw [transposeCode_code]
  by_cases h : S.orig
  · rw [if_pos (code_lt_tr hk h j), if_pos h, quote_cterm_C]
  · rw [if_neg (lt_asymm (tr_lt_code hk h j)), if_pos (tr_lt_code hk h j), if_neg h, quote_cterm_D]

theorem revalueW_code {S : Sys2} {k : V} (hk : (S.K : V) ≤ k) (j : ℕ) : revalueW (S.code j k) = (⌜S.wT⌝ : V) := by
  unfold revalueW wT
  rw [transposeCode_code]
  by_cases h : S.orig
  · rw [if_pos (code_lt_tr hk h j), if_pos h, quote_cterm_D]
  · rw [if_neg (lt_asymm (tr_lt_code hk h j)), if_pos (tr_lt_code hk h j), if_neg h, quote_cterm_C]

/-- The re-valuation terms reconstruct the system from its canonical code. -/
theorem revalue_val_uT_wT (S : Sys2) (k : V) (j : ℕ) :
    revalue (S.uT.val (s := stdReadingV V) ![] Empty.elim) (S.wT.val (s := stdReadingV V) ![] Empty.elim)
      (S.can.code j k) = S.code j k := by
  unfold uT wT can
  by_cases h : S.orig
  · rw [if_pos h, if_pos h, if_pos h, val_cterm_C_V, val_cterm_D_V, revalue_zero_one]
  · rw [if_neg h, if_neg h, if_neg h, val_cterm_D_V, val_cterm_C_V]
    show transposeCode (S.tr.code j k) = _
    rw [← transposeCode_code S j k, transposeCode_transposeCode]

/-- The transposed re-valuation terms reconstruct the TRANSPOSED system. -/
theorem revalue_val_uT_wT_swap (S : Sys2) (k : V) (j : ℕ) :
    revalue ((Semiterm.lMap swap S.uT).val (s := stdReadingV V) ![] Empty.elim)
      ((Semiterm.lMap swap S.wT).val (s := stdReadingV V) ![] Empty.elim) (S.can.code j k) = S.tr.code j k := by
  unfold uT wT can
  by_cases h : S.orig
  · rw [if_pos h, if_pos h, if_pos h, lMap_swap_cterm_C, lMap_swap_cterm_D, val_cterm_D_V, val_cterm_C_V]
    show transposeCode (S.code j k) = _
    rw [transposeCode_code]
  · rw [if_neg h, if_neg h, if_neg h, lMap_swap_cterm_D, lMap_swap_cterm_C, val_cterm_C_V, val_cterm_D_V,
      revalue_zero_one]

end Sys2

/-! ### 3. The towers: one-variable terms for lists and systems -/

section towers

/-- The one-variable term of the empty member list (`pNil = 0`). -/
noncomputable def nilT1 : Semiterm ℒₒᵣ Empty 1 := Rew.bShift (binNumeralMeta 0)
/-- The one-variable term of `pCons`. -/
noncomputable def consT1 (x r : Semiterm ℒₒᵣ Empty 1) : Semiterm ℒₒᵣ Empty 1 :=
  succT1 (ppairT1 (Rew.bShift (binNumeralMeta 10)) (ppairT1 x r))
/-- The one-variable term of `pSys · j`. -/
noncomputable def sysT1 (d : Semiterm ℒₒᵣ Empty 1) (j : ℕ) : Semiterm ℒₒᵣ Empty 1 :=
  succT1 (ppairT1 (Rew.bShift (binNumeralMeta 8)) (ppairT1 d (Rew.bShift (binNumeralMeta j))))

lemma val_nilT1_V (b : Fin 1 → V) : nilT1.val (s := standardModel V) b Empty.elim = pNil := by
  rw [nilT1, val_bShift₁_V, val_binNumeralMeta_V]; rfl

lemma val_consT1_V (x r : Semiterm ℒₒᵣ Empty 1) (b : Fin 1 → V) :
    (consT1 x r).val (s := standardModel V) b Empty.elim =
      pCons (x.val (s := standardModel V) b Empty.elim) (r.val (s := standardModel V) b Empty.elim) := by
  rw [consT1, val_succT1_V, val_ppairT1_V, val_ppairT1_V, val_bShift₁_V, val_binNumeralMeta_V]
  unfold pCons; push_cast; rfl

lemma val_sysT1_V (d : Semiterm ℒₒᵣ Empty 1) (j : ℕ) (b : Fin 1 → V) :
    (sysT1 d j).val (s := standardModel V) b Empty.elim = pSys (d.val (s := standardModel V) b Empty.elim) (j : V) := by
  rw [sysT1, val_succT1_V, val_ppairT1_V, val_ppairT1_V, val_bShift₁_V, val_bShift₁_V, val_binNumeralMeta_V,
    val_binNumeralMeta_V]
  unfold pSys; push_cast; rfl

lemma quote_emb_nilT1 : (⌜(Rew.emb nilT1 : SyntacticSemiterm ℒₒᵣ 1)⌝ : V) = binNumeral 0 := by
  rw [nilT1, quote_emb_bShift, ← Semiterm.empty_quote_def, quote_binNumeralMeta]; simp

lemma quote_emb_consT1 (x r : Semiterm ℒₒᵣ Empty 1) :
    (⌜(Rew.emb (consT1 x r) : SyntacticSemiterm ℒₒᵣ 1)⌝ : V) =
      ppairTerm (binNumeral 10) (ppairTerm (⌜(Rew.emb x : SyntacticSemiterm ℒₒᵣ 1)⌝ : V) ⌜(Rew.emb r : SyntacticSemiterm ℒₒᵣ 1)⌝) ^+ 𝟏 := by
  rw [consT1, quote_emb_succT1, quote_emb_ppairT1, quote_emb_ppairT1, quote_emb_bShift, ← Semiterm.empty_quote_def,
    quote_binNumeralMeta]
  push_cast; rfl

lemma quote_emb_sysT1 (d : Semiterm ℒₒᵣ Empty 1) (j : ℕ) :
    (⌜(Rew.emb (sysT1 d j) : SyntacticSemiterm ℒₒᵣ 1)⌝ : V) =
      ppairTerm (binNumeral 8) (ppairTerm (⌜(Rew.emb d : SyntacticSemiterm ℒₒᵣ 1)⌝ : V) (binNumeral (j : V))) ^+ 𝟏 := by
  rw [sysT1, quote_emb_succT1, quote_emb_ppairT1, quote_emb_ppairT1, quote_emb_bShift, quote_emb_bShift]
  simp only [← Semiterm.empty_quote_def, quote_binNumeralMeta]
  push_cast; rfl

/-- The code of an embedded ℒₒᵣ-term is an `LAct`-term code. -/
lemma uterm_quote_emb_LOR (t : Semiterm ℒₒᵣ Empty 1) : IsUTerm LAct (⌜(Rew.emb t : SyntacticSemiterm ℒₒᵣ 1)⌝ : V) := by
  rw [← quote_term_lMap_emb, ← term_emb_lMap_emb_n]
  exact (semiterm_quote_emb₁ _).isUTerm

lemma uterm_one : IsUTerm LAct (𝟏 : V) := (IsSemiterm.LAct_of_LOR (one_semiterm (n := 0))).isUTerm
lemma uterm_binNumeral (x : V) : IsUTerm LAct (binNumeral x) := (binNumeral_semiterm_LAct 0 _).isUTerm

/-- Filling the budget slot of a `pBot` layer. -/
lemma termSubst_bot_of (w : V) {t T : V} (ht : IsUTerm LAct t) (h : termSubst LAct w t = codeTerm T) :
    termSubst LAct w (ppairTerm (binNumeral 3) t ^+ 𝟏) = codeTerm (pBot T) := by
  rw [termSubst_qqAdd _ (ppairTerm_uterm_LAct (uterm_binNumeral _) ht) uterm_one,
    termSubst_ppairTerm _ (uterm_binNumeral _) ht, termSubst_closed _ (binNumeral_semiterm_LAct 0 _),
    termSubst_closed _ (IsSemiterm.LAct_of_LOR one_semiterm), h, codeTerm_bot]

/-- Filling the budget slot of a `pCons` layer. -/
lemma termSubst_cons_of (w : V) {x r X R : V} (hx : IsUTerm LAct x) (hr : IsUTerm LAct r)
    (hX : termSubst LAct w x = codeTerm X) (hR : termSubst LAct w r = codeTerm R) :
    termSubst LAct w (ppairTerm (binNumeral 10) (ppairTerm x r) ^+ 𝟏) = codeTerm (pCons X R) := by
  rw [termSubst_qqAdd _ (ppairTerm_uterm_LAct (uterm_binNumeral _) (ppairTerm_uterm_LAct hx hr)) uterm_one,
    termSubst_ppairTerm _ (uterm_binNumeral _) (ppairTerm_uterm_LAct hx hr), termSubst_ppairTerm _ hx hr,
    termSubst_closed _ (binNumeral_semiterm_LAct 0 _), termSubst_closed _ (IsSemiterm.LAct_of_LOR one_semiterm),
    hX, hR, codeTerm_cons]

/-- Filling the budget slot of a `pSys · j` layer. -/
lemma termSubst_sys_of (w : V) {d D : V} (hd : IsUTerm LAct d) (hD : termSubst LAct w d = codeTerm D) (j : V) :
    termSubst LAct w (ppairTerm (binNumeral 8) (ppairTerm d (binNumeral j)) ^+ 𝟏) = codeTerm (pSys D j) := by
  rw [termSubst_qqAdd _ (ppairTerm_uterm_LAct (uterm_binNumeral _) (ppairTerm_uterm_LAct hd (uterm_binNumeral _))) uterm_one,
    termSubst_ppairTerm _ (uterm_binNumeral _) (ppairTerm_uterm_LAct hd (uterm_binNumeral _)),
    termSubst_ppairTerm _ hd (uterm_binNumeral _),
    termSubst_closed _ (binNumeral_semiterm_LAct 0 _), termSubst_closed _ (binNumeral_semiterm_LAct 0 _),
    termSubst_closed _ (IsSemiterm.LAct_of_LOR one_semiterm), hD, codeTerm_sys]

lemma termSubst_nilT1 (w : V) : termSubst LAct w (⌜(Rew.emb nilT1 : SyntacticSemiterm ℒₒᵣ 1)⌝ : V) = codeTerm pNil := by
  rw [quote_emb_nilT1, termSubst_closed _ (binNumeral_semiterm_LAct 0 _), codeTerm_nil]

lemma termSubst_consT1 (w : V) {x r : Semiterm ℒₒᵣ Empty 1} {X R : V}
    (hX : termSubst LAct w (⌜(Rew.emb x : SyntacticSemiterm ℒₒᵣ 1)⌝ : V) = codeTerm X)
    (hR : termSubst LAct w (⌜(Rew.emb r : SyntacticSemiterm ℒₒᵣ 1)⌝ : V) = codeTerm R) :
    termSubst LAct w (⌜(Rew.emb (consT1 x r) : SyntacticSemiterm ℒₒᵣ 1)⌝ : V) = codeTerm (pCons X R) := by
  rw [quote_emb_consT1]
  exact termSubst_cons_of w (uterm_quote_emb_LOR x) (uterm_quote_emb_LOR r) hX hR

lemma termSubst_sysT1 (w : V) {d : Semiterm ℒₒᵣ Empty 1} {D : V}
    (hD : termSubst LAct w (⌜(Rew.emb d : SyntacticSemiterm ℒₒᵣ 1)⌝ : V) = codeTerm D) (j : ℕ) :
    termSubst LAct w (⌜(Rew.emb (sysT1 d j) : SyntacticSemiterm ℒₒᵣ 1)⌝ : V) = codeTerm (pSys D (j : V)) := by
  rw [quote_emb_sysT1]
  exact termSubst_sys_of w (uterm_quote_emb_LOR d) hD _

lemma termSubst_botT1 (w : V) {t : Semiterm ℒₒᵣ Empty 1} {T : V}
    (hT : termSubst LAct w (⌜(Rew.emb t : SyntacticSemiterm ℒₒᵣ 1)⌝ : V) = codeTerm T) :
    termSubst LAct w (⌜(Rew.emb (botT1 t) : SyntacticSemiterm ℒₒᵣ 1)⌝ : V) = codeTerm (pBot T) := by
  rw [quote_emb_botT1]
  exact termSubst_bot_of w (uterm_quote_emb_LOR t) hT

end towers

/-! ### 4. The member and system towers -/

namespace SM

/-- The one-variable term of a simple member. -/
noncomputable def T1 (s : SM) : Semiterm ℒₒᵣ Empty 1 := searchT1 (⌜s.g⌝ : ℕ) (pConst s.a) (pConst (1 - s.a))

lemma val_T1_V (s : SM) (k : V) : (s.T1).val (s := standardModel V) ![k] Empty.elim = s.code k := by
  rw [T1, val_searchT1_V, cast_pConst, cast_pConst]; rfl

lemma termSubst_T1 (s : SM) (k : V) :
    termSubst LAct (binNumeral k ∷ (0 : V)) (⌜(Rew.emb s.T1 : SyntacticSemiterm ℒₒᵣ 1)⌝ : V) = codeTerm (s.code k) := by
  rw [T1, quote_emb_searchT1, termSubst_tower, cast_pConst, cast_pConst]; rfl

end SM

namespace Sys2

/-- The one-variable ℒₒᵣ-term of member `j` of the system: the list tower under `pSys · j`. -/
noncomputable def T1 (S : Sys2) (j : ℕ) : Semiterm ℒₒᵣ Empty 1 := sysT1 (consT1 S.m₀.T1 (consT1 S.m₁.T1 nilT1)) j

lemma val_T1_V (S : Sys2) (j : ℕ) (k : V) : (S.T1 j).val (s := standardModel V) ![k] Empty.elim = S.code j k := by
  rw [T1, val_sysT1_V, val_consT1_V, val_consT1_V, val_nilT1_V, SM.val_T1_V, SM.val_T1_V]; rfl

lemma termSubst_T1 (S : Sys2) (j : ℕ) (k : V) :
    termSubst LAct (binNumeral k ∷ (0 : V)) (⌜(Rew.emb (S.T1 j) : SyntacticSemiterm ℒₒᵣ 1)⌝ : V) = codeTerm (S.code j k) := by
  rw [T1]
  exact termSubst_sysT1 _ (termSubst_consT1 _ (SM.termSubst_T1 _ _) (termSubst_consT1 _ (SM.termSubst_T1 _ _) (termSubst_nilT1 _))) j

/-- **The member tower** (the slot term of member `j`): the canonical shapes' list tower, over `LAct`. -/
noncomputable def TM (S : Sys2) (j : ℕ) : Semiterm LAct Empty 1 := Semiterm.lMap emb (S.can.T1 j)
/-- **The frame tower** of the bot-wrapped member `j` (`pBot (S.code j k)`, the player of a bit's frame). -/
noncomputable def TX (S : Sys2) (j : ℕ) : Semiterm LAct Empty 1 := Semiterm.lMap emb (botT1 (S.can.T1 j))

lemma lMap_swap_TM (S : Sys2) (j : ℕ) : Semiterm.lMap swap (S.TM j) = S.TM j := term_lMap_swap_emb _
lemma lMap_swap_TX (S : Sys2) (j : ℕ) : Semiterm.lMap swap (S.TX j) = S.TX j := term_lMap_swap_emb _

theorem val_TM_V {S : Sys2} {k : V} (hk : (S.K : V) ≤ k) (j : ℕ) :
    (S.TM j).val (s := stdReadingV V) ![k] Empty.elim = canonical (S.code j k) := by
  unfold TM
  rw [Semiterm.val_lMap, stdReadingV_lMap_emb, val_T1_V, canonical_code hk]

theorem val_TX_V {S : Sys2} {k : V} (hk : (S.K : V) ≤ k) (j : ℕ) :
    (S.TX j).val (s := stdReadingV V) ![k] Empty.elim = canonical (pBot (S.code j k)) := by
  unfold TX
  rw [Semiterm.val_lMap, stdReadingV_lMap_emb, val_botT1_V, val_T1_V, canonical_pBot, canonical_code hk]

theorem hX_TM {S : Sys2} {k : V} (hk : (S.K : V) ≤ k) (j : ℕ) :
    termSubst LAct (binNumeral k ∷ (0 : V)) (⌜(Rew.emb (S.TM j) : SyntacticSemiterm LAct 1)⌝ : V) =
      codeTerm (canonical (S.code j k)) := by
  unfold TM
  rw [term_emb_lMap_emb_n, quote_term_lMap_emb, termSubst_T1, canonical_code hk]

theorem hX_TX {S : Sys2} {k : V} (hk : (S.K : V) ≤ k) (j : ℕ) :
    termSubst LAct (binNumeral k ∷ (0 : V)) (⌜(Rew.emb (S.TX j) : SyntacticSemiterm LAct 1)⌝ : V) =
      codeTerm (canonical (pBot (S.code j k))) := by
  unfold TX
  rw [term_emb_lMap_emb_n, quote_term_lMap_emb, termSubst_botT1 _ (termSubst_T1 _ _ _), canonical_pBot, canonical_code hk]

/-! #### The description values -/

theorem descVal_TM {S : Sys2} {k : V} (hk : (S.K : V) ≤ k) (j : ℕ) : descVal (S.TM j) S.uT S.wT k = S.code j k := by
  rw [descVal_def, val_TM_V hk, canonical_code hk, revalue_val_uT_wT]

theorem descVal_TM_T {S : Sys2} {k : V} (hk : (S.K : V) ≤ k) (j : ℕ) :
    descVal (Semiterm.lMap swap (S.TM j)) (Semiterm.lMap swap S.uT) (Semiterm.lMap swap S.wT) k = S.tr.code j k := by
  rw [descVal_def, lMap_swap_TM, val_TM_V hk, canonical_code hk, revalue_val_uT_wT_swap]

theorem descVal_TX {S : Sys2} {k : V} (hk : (S.K : V) ≤ k) (j : ℕ) : descVal (S.TX j) S.uT S.wT k = pBot (S.code j k) := by
  rw [descVal_def, val_TX_V hk, canonical_pBot, revalue_bot, canonical_code hk, revalue_val_uT_wT]

theorem descVal_TX_T {S : Sys2} {k : V} (hk : (S.K : V) ≤ k) (j : ℕ) :
    descVal (Semiterm.lMap swap (S.TX j)) (Semiterm.lMap swap S.uT) (Semiterm.lMap swap S.wT) k = pBot (S.tr.code j k) := by
  rw [descVal_def, lMap_swap_TX, val_TX_V hk, canonical_pBot, revalue_bot, canonical_code hk, revalue_val_uT_wT_swap]

/-- **The member tower describes member `j` above the threshold.** -/
theorem describesMem (S : Sys2) (j : ℕ) : DescribesAbove S.K (S.TM j) S.uT S.wT where
  hX := fun V _ _ k hk ↦ by rw [descVal_TM hk]; exact hX_TM hk j
  hU := fun V _ _ k hk ↦ by rw [descVal_TM hk, revalueU_code hk]
  hW := fun V _ _ k hk ↦ by rw [descVal_TM hk, revalueW_code hk]
  hT := fun V _ _ k hk ↦ by rw [descVal_TM_T hk, descVal_TM hk, transposeCode_code]

/-- **The frame tower describes the bot-wrapped member `j` above the threshold.** -/
theorem describesBot (S : Sys2) (j : ℕ) : DescribesAbove S.K (S.TX j) S.uT S.wT where
  hX := fun V _ _ k hk ↦ by rw [descVal_TX hk]; exact hX_TX hk j
  hU := fun V _ _ k hk ↦ by rw [descVal_TX hk, revalueU_pBot, revalueU_code hk]
  hW := fun V _ _ k hk ↦ by rw [descVal_TX hk, revalueW_pBot, revalueW_code hk]
  hT := fun V _ _ k hk ↦ by rw [descVal_TX_T hk, descVal_TX hk, transposeCode_pBot, transposeCode_code]

end Sys2

end ArithS.Tau
