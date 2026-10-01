import ArithS.Tau.Entangled.Loeb
import ArithS.Tau.Quine

/-!
# ArithS.Tau.Watch — a bot-wrapped simple searcher and a run-stage WATCH over it, as `k̂`-towers (Phase 3e)

Route (c) made generic (Phase 2c) stores every tau template as a CONSTANT, so the compiled instance of a
self-prober at a budget-carrying hypothesis is the bot-wrapped SIMPLE searcher `pBot (pSearch k ⌜g⌝ (pConst a)
(pConst (1 - a)))` on a fixed thirteen-variable template `g` — an `SM` (`Tau/Entangled/Tower.lean`) — and the
hypothesis's instance it names is a run-stage WATCH over another simple searcher: τ(TFTSim)'s, τ(DBot)'s and
τ(OBot)'s instances at a self-prober are `pIte (pSim (pBot S) (pBot S)) t (pConst p) (pConst q)` with `S` the
self-prober's instance at a constant. Both players must be described, uniformly in `k` and in every model, by
fixed one-variable terms with the budget at `#0` (the `Describes` layer of `Cells/Common/Templates.lean`).

* §1 **a single simple member**: its canonical shape `SM.can` (the order is decided by the budget-free inner
  parts, `SM.code_lt_iff`, at EVERY budget), the re-valuation terms `SM.uT`/`SM.wT`, the frame tower `SM.TB`
  of `pBot (s.code k)` and `SM.describesBot`; the search clauses of the bot-wrapped member in every model;
* §2 **the term combinators** `constT1`/`simT1`/`iteT1` (`searchT1`'s shape) with their values and the budget
  substitution into their codes;
* §3 **the watch `W1`** `pIte (pSim (pBot S) (pBot S)) t (pConst p) (pConst q)` over a simple member: its
  transposition, **its τ-order** (decided by the inner member above a standard threshold `W1.K`: the gain of
  the quadratic pairing through the three wrappers is at least the member itself, which dominates the
  constant parts), the canonical shape, the tower `W1.TX` of `pBot (W.code k)` and `W1.describesBot`.
-/

set_option linter.constructorNameAsVariable false

namespace ArithS.Tau

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open LAct

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ### 1. A single simple member -/

namespace SM

/-- The decision: the member's inner part below its transposed one. -/
def orig (s : SM) : Prop := s.inner < s.tr.inner

open scoped Classical in
/-- The canonical shape: the member itself when `orig`, its transposition otherwise. -/
noncomputable def can (s : SM) : SM := if s.orig then s else s.tr
open scoped Classical in
noncomputable def uT (s : SM) : ClosedSemiterm LAct 0 := if s.orig then cterm Act.C else cterm Act.D
open scoped Classical in
noncomputable def wT (s : SM) : ClosedSemiterm LAct 0 := if s.orig then cterm Act.D else cterm Act.C

lemma tr_tr (s : SM) : s.tr.tr = s := by
  obtain ⟨g, a, ha⟩ := s
  unfold tr
  simp only [lMap_swap_swap]
  rcases ha with rfl | rfl <;> rfl

theorem code_lt_tr (s : SM) (k : V) (h : s.orig) : s.code k < s.tr.code k := (SM.code_lt_iff _ _ k).mpr h

theorem tr_lt_code (s : SM) (k : V) (h : ¬ s.orig) : s.tr.code k < s.code k :=
  (SM.code_lt_iff _ _ k).mpr (lt_of_le_of_ne (not_lt.mp h) (Ne.symm (inner_ne_tr s)))

theorem canonical_code (s : SM) (k : V) : canonical (s.code k) = s.can.code k := by
  unfold can
  by_cases h : s.orig
  · rw [if_pos h, canonical_of_lt (by rw [transposeCode_code]; exact code_lt_tr s k h)]
  · rw [if_neg h, canonical_of_gt (by rw [transposeCode_code]; exact tr_lt_code s k h), transposeCode_code]

theorem revalueU_code (s : SM) (k : V) : revalueU (s.code k) = (⌜s.uT⌝ : V) := by
  unfold revalueU uT
  rw [transposeCode_code]
  by_cases h : s.orig
  · rw [if_pos (code_lt_tr s k h), if_pos h, quote_cterm_C]
  · rw [if_neg (lt_asymm (tr_lt_code s k h)), if_pos (tr_lt_code s k h), if_neg h, quote_cterm_D]

theorem revalueW_code (s : SM) (k : V) : revalueW (s.code k) = (⌜s.wT⌝ : V) := by
  unfold revalueW wT
  rw [transposeCode_code]
  by_cases h : s.orig
  · rw [if_pos (code_lt_tr s k h), if_pos h, quote_cterm_D]
  · rw [if_neg (lt_asymm (tr_lt_code s k h)), if_pos (tr_lt_code s k h), if_neg h, quote_cterm_C]

theorem revalue_val_uT_wT (s : SM) (k : V) :
    revalue (s.uT.val (s := stdReadingV V) ![] Empty.elim) (s.wT.val (s := stdReadingV V) ![] Empty.elim)
      (s.can.code k) = s.code k := by
  unfold uT wT can
  by_cases h : s.orig
  · rw [if_pos h, if_pos h, if_pos h, val_cterm_C_V, val_cterm_D_V, revalue_zero_one]
  · rw [if_neg h, if_neg h, if_neg h, val_cterm_D_V, val_cterm_C_V]
    show transposeCode (s.tr.code k) = _
    rw [← transposeCode_code s k, transposeCode_transposeCode]

theorem revalue_val_uT_wT_swap (s : SM) (k : V) :
    revalue ((Semiterm.lMap swap s.uT).val (s := stdReadingV V) ![] Empty.elim)
      ((Semiterm.lMap swap s.wT).val (s := stdReadingV V) ![] Empty.elim) (s.can.code k) = s.tr.code k := by
  unfold uT wT can
  by_cases h : s.orig
  · rw [if_pos h, if_pos h, if_pos h, lMap_swap_cterm_C, lMap_swap_cterm_D, val_cterm_D_V, val_cterm_C_V]
    show transposeCode (s.code k) = _
    rw [transposeCode_code]
  · rw [if_neg h, if_neg h, if_neg h, lMap_swap_cterm_D, lMap_swap_cterm_C, val_cterm_C_V, val_cterm_D_V,
      revalue_zero_one]

theorem canonical_tr_code (s : SM) (k : V) : canonical (s.tr.code k) = s.can.code k := by
  rw [← transposeCode_code, canonical_transposeCode, canonical_code]

theorem revalueU_tr_code (s : SM) (k : V) : revalueU (s.tr.code k) = (⌜Semiterm.lMap swap s.uT⌝ : V) := by
  have e : transposeCode (s.tr.code k) = s.code k := by rw [← transposeCode_code, transposeCode_transposeCode]
  unfold revalueU uT
  rw [e]
  by_cases h : s.orig
  · rw [if_neg (lt_asymm (code_lt_tr s k h)), if_pos (code_lt_tr s k h), if_pos h, lMap_swap_cterm_C, quote_cterm_D]
  · rw [if_pos (tr_lt_code s k h), if_neg h, lMap_swap_cterm_D, quote_cterm_C]

theorem revalueW_tr_code (s : SM) (k : V) : revalueW (s.tr.code k) = (⌜Semiterm.lMap swap s.wT⌝ : V) := by
  have e : transposeCode (s.tr.code k) = s.code k := by rw [← transposeCode_code, transposeCode_transposeCode]
  unfold revalueW wT
  rw [e]
  by_cases h : s.orig
  · rw [if_neg (lt_asymm (code_lt_tr s k h)), if_pos (code_lt_tr s k h), if_pos h, lMap_swap_cterm_D, quote_cterm_C]
  · rw [if_pos (tr_lt_code s k h), if_neg h, lMap_swap_cterm_C, quote_cterm_D]

/-- **The frame tower** of the bot-wrapped member `pBot (s.code k)`. -/
noncomputable def TB (s : SM) : Semiterm LAct Empty 1 := Semiterm.lMap emb (botT1 s.can.T1)

lemma lMap_swap_TB (s : SM) : Semiterm.lMap swap s.TB = s.TB := term_lMap_swap_emb _

theorem val_TB_V (s : SM) (k : V) : s.TB.val (s := stdReadingV V) ![k] Empty.elim = canonical (pBot (s.code k)) := by
  unfold TB
  rw [Semiterm.val_lMap, stdReadingV_lMap_emb, val_botT1_V, val_T1_V, canonical_pBot, canonical_code]

theorem hX_TB (s : SM) (k : V) :
    termSubst LAct (binNumeral k ∷ (0 : V)) (⌜(Rew.emb s.TB : SyntacticSemiterm LAct 1)⌝ : V) =
      codeTerm (canonical (pBot (s.code k))) := by
  unfold TB
  rw [term_emb_lMap_emb_n, quote_term_lMap_emb, termSubst_botT1 _ (termSubst_T1 _ _), canonical_pBot, canonical_code]

theorem descVal_TB (s : SM) (k : V) : descVal s.TB s.uT s.wT k = pBot (s.code k) := by
  rw [descVal_def, val_TB_V, canonical_pBot, revalue_bot, canonical_code, revalue_val_uT_wT]

theorem descVal_TB_T (s : SM) (k : V) :
    descVal (Semiterm.lMap swap s.TB) (Semiterm.lMap swap s.uT) (Semiterm.lMap swap s.wT) k = pBot (s.tr.code k) := by
  rw [descVal_def, lMap_swap_TB, val_TB_V, canonical_pBot, revalue_bot, canonical_code, revalue_val_uT_wT_swap]

/-- **The frame tower describes the bot-wrapped member in every model.** -/
theorem describesBot (s : SM) : Describes s.TB s.uT s.wT where
  hX := fun V _ _ k ↦ by rw [descVal_TB]; exact hX_TB s k
  hU := fun V _ _ k ↦ by rw [descVal_TB, revalueU_pBot, revalueU_code]
  hW := fun V _ _ k ↦ by rw [descVal_TB, revalueW_pBot, revalueW_code]
  hT := fun V _ _ k ↦ by rw [descVal_TB_T, descVal_TB, transposeCode_pBot, transposeCode_code]

/-- The bot-wrapped member in the frame `(me, opp)`: its guard found ⇒ the then-action (fuel 3). -/
theorem bot_then_V (s : SM) (k me opp : V)
    (h : LenBox TAct k (guardCodeB ((⌜s.g⌝ : ℕ) : V) me opp k)) : EvalGraph 3 me opp (pBot (s.code k)) (s.a : V) := by
  rw [show (3 : V) = 2 + 1 from two_add_one_eq_three.symm, EvalGraph.bot_iff]
  unfold code
  rw [show (2 : V) = 1 + 1 from one_add_one_eq_two.symm, EvalGraph.search_iff]
  exact Or.inl ⟨h, by rw [show (1 : V) = 0 + 1 by simp, EvalGraph.const_iff]⟩

/-- Its guard not found ⇒ the else-action. -/
theorem bot_else_V (s : SM) (k me opp : V)
    (h : ¬ LenBox TAct k (guardCodeB ((⌜s.g⌝ : ℕ) : V) me opp k)) :
    EvalGraph 3 me opp (pBot (s.code k)) ((1 - s.a : ℕ) : V) := by
  rw [show (3 : V) = 2 + 1 from two_add_one_eq_three.symm, EvalGraph.bot_iff]
  unfold code
  rw [show (2 : V) = 1 + 1 from one_add_one_eq_two.symm, EvalGraph.search_iff]
  exact Or.inr ⟨h, by rw [show (1 : V) = 0 + 1 by simp, EvalGraph.const_iff]⟩

/-- The member's code is at least its budget. -/
lemma le_code (s : SM) (k : V) : k ≤ s.code k := by
  rw [code_eq_inner]
  exact le_trans (le_ppair_left k _) (le_trans (le_ppair_right 6 _) le_self_add)

end SM

/-! ### 2. The term combinators of a constant, a `sim` node and an `ite` node -/

section combinators

/-- The one-variable term of a frozen constant (shifted closed description). -/
noncomputable def constT1 (a : ℕ) : Semiterm ℒₒᵣ Empty 1 := Rew.bShift (codeTermMeta (pConst a))
/-- The one-variable term of `pSim`. -/
noncomputable def simT1 (x y : Semiterm ℒₒᵣ Empty 1) : Semiterm ℒₒᵣ Empty 1 :=
  succT1 (ppairT1 (Rew.bShift (binNumeralMeta 4)) (ppairT1 x y))
/-- The one-variable term of `pIte · a · ·`. -/
noncomputable def iteT1 (b : Semiterm ℒₒᵣ Empty 1) (a : ℕ) (x y : Semiterm ℒₒᵣ Empty 1) : Semiterm ℒₒᵣ Empty 1 :=
  succT1 (ppairT1 (Rew.bShift (binNumeralMeta 5)) (ppairT1 b (ppairT1 (Rew.bShift (binNumeralMeta a)) (ppairT1 x y))))

lemma val_constT1_V (a : ℕ) (b : Fin 1 → V) :
    (constT1 a).val (s := standardModel V) b Empty.elim = pConst (a : V) := by
  rw [constT1, val_bShift₁_V, val_codeTermMeta_V, cast_pConst]

lemma val_simT1_V (x y : Semiterm ℒₒᵣ Empty 1) (b : Fin 1 → V) :
    (simT1 x y).val (s := standardModel V) b Empty.elim =
      pSim (x.val (s := standardModel V) b Empty.elim) (y.val (s := standardModel V) b Empty.elim) := by
  rw [simT1, val_succT1_V, val_ppairT1_V, val_ppairT1_V, val_bShift₁_V, val_binNumeralMeta_V]
  unfold pSim; push_cast; rfl

lemma val_iteT1_V (bb : Semiterm ℒₒᵣ Empty 1) (a : ℕ) (x y : Semiterm ℒₒᵣ Empty 1) (b : Fin 1 → V) :
    (iteT1 bb a x y).val (s := standardModel V) b Empty.elim =
      pIte (bb.val (s := standardModel V) b Empty.elim) (a : V) (x.val (s := standardModel V) b Empty.elim)
        (y.val (s := standardModel V) b Empty.elim) := by
  rw [iteT1, val_succT1_V, val_ppairT1_V, val_ppairT1_V, val_ppairT1_V, val_ppairT1_V, val_bShift₁_V, val_bShift₁_V,
    val_binNumeralMeta_V, val_binNumeralMeta_V]
  unfold pIte; push_cast; rfl

lemma quote_emb_constT1 (a : ℕ) :
    (⌜(Rew.emb (constT1 a) : SyntacticSemiterm ℒₒᵣ 1)⌝ : V) = codeTerm (pConst (a : V)) := by
  rw [constT1, quote_emb_bShift, ← Semiterm.empty_quote_def, quote_codeTermMeta, cast_pConst]

lemma quote_emb_simT1 (x y : Semiterm ℒₒᵣ Empty 1) :
    (⌜(Rew.emb (simT1 x y) : SyntacticSemiterm ℒₒᵣ 1)⌝ : V) =
      ppairTerm (binNumeral 4) (ppairTerm (⌜(Rew.emb x : SyntacticSemiterm ℒₒᵣ 1)⌝ : V) ⌜(Rew.emb y : SyntacticSemiterm ℒₒᵣ 1)⌝) ^+ 𝟏 := by
  rw [simT1, quote_emb_succT1, quote_emb_ppairT1, quote_emb_ppairT1, quote_emb_bShift, ← Semiterm.empty_quote_def,
    quote_binNumeralMeta]
  push_cast; rfl

lemma quote_emb_iteT1 (bb : Semiterm ℒₒᵣ Empty 1) (a : ℕ) (x y : Semiterm ℒₒᵣ Empty 1) :
    (⌜(Rew.emb (iteT1 bb a x y) : SyntacticSemiterm ℒₒᵣ 1)⌝ : V) =
      ppairTerm (binNumeral 5) (ppairTerm (⌜(Rew.emb bb : SyntacticSemiterm ℒₒᵣ 1)⌝ : V)
        (ppairTerm (binNumeral (a : V)) (ppairTerm (⌜(Rew.emb x : SyntacticSemiterm ℒₒᵣ 1)⌝ : V)
          ⌜(Rew.emb y : SyntacticSemiterm ℒₒᵣ 1)⌝))) ^+ 𝟏 := by
  rw [iteT1, quote_emb_succT1, quote_emb_ppairT1, quote_emb_ppairT1, quote_emb_ppairT1, quote_emb_ppairT1,
    quote_emb_bShift, quote_emb_bShift]
  simp only [← Semiterm.empty_quote_def, quote_binNumeralMeta]
  push_cast; rfl

lemma termSubst_constT1 (w : V) (a : ℕ) :
    termSubst LAct w (⌜(Rew.emb (constT1 a) : SyntacticSemiterm ℒₒᵣ 1)⌝ : V) = codeTerm (pConst (a : V)) := by
  rw [quote_emb_constT1, termSubst_closed _ (codeTerm_semiterm_LAct 0 _)]

/-- Filling the budget slot of a `pSim` layer. -/
lemma termSubst_sim_of (w : V) {x y X Y : V} (hx : IsUTerm LAct x) (hy : IsUTerm LAct y)
    (hX : termSubst LAct w x = codeTerm X) (hY : termSubst LAct w y = codeTerm Y) :
    termSubst LAct w (ppairTerm (binNumeral 4) (ppairTerm x y) ^+ 𝟏) = codeTerm (pSim X Y) := by
  rw [termSubst_qqAdd _ (ppairTerm_uterm_LAct (uterm_binNumeral _) (ppairTerm_uterm_LAct hx hy)) uterm_one,
    termSubst_ppairTerm _ (uterm_binNumeral _) (ppairTerm_uterm_LAct hx hy), termSubst_ppairTerm _ hx hy,
    termSubst_closed _ (binNumeral_semiterm_LAct 0 _), termSubst_closed _ (IsSemiterm.LAct_of_LOR one_semiterm),
    hX, hY, codeTerm_sim]

/-- Filling the budget slot of a `pIte` layer. -/
lemma termSubst_ite_of (w : V) {b x y B X Y : V} (a : V) (hb : IsUTerm LAct b) (hx : IsUTerm LAct x) (hy : IsUTerm LAct y)
    (hB : termSubst LAct w b = codeTerm B) (hX : termSubst LAct w x = codeTerm X) (hY : termSubst LAct w y = codeTerm Y) :
    termSubst LAct w (ppairTerm (binNumeral 5) (ppairTerm b (ppairTerm (binNumeral a) (ppairTerm x y))) ^+ 𝟏) =
      codeTerm (pIte B a X Y) := by
  have h1 : IsUTerm LAct (ppairTerm x y) := ppairTerm_uterm_LAct hx hy
  have h2 : IsUTerm LAct (ppairTerm (binNumeral a) (ppairTerm x y)) := ppairTerm_uterm_LAct (uterm_binNumeral _) h1
  have h3 : IsUTerm LAct (ppairTerm b (ppairTerm (binNumeral a) (ppairTerm x y))) := ppairTerm_uterm_LAct hb h2
  rw [termSubst_qqAdd _ (ppairTerm_uterm_LAct (uterm_binNumeral _) h3) uterm_one,
    termSubst_ppairTerm _ (uterm_binNumeral _) h3, termSubst_ppairTerm _ hb h2,
    termSubst_ppairTerm _ (uterm_binNumeral _) h1, termSubst_ppairTerm _ hx hy,
    termSubst_closed _ (binNumeral_semiterm_LAct 0 _), termSubst_closed _ (binNumeral_semiterm_LAct 0 _),
    termSubst_closed _ (IsSemiterm.LAct_of_LOR one_semiterm), hB, hX, hY, codeTerm_ite]

lemma termSubst_simT1 (w : V) {x y : Semiterm ℒₒᵣ Empty 1} {X Y : V}
    (hX : termSubst LAct w (⌜(Rew.emb x : SyntacticSemiterm ℒₒᵣ 1)⌝ : V) = codeTerm X)
    (hY : termSubst LAct w (⌜(Rew.emb y : SyntacticSemiterm ℒₒᵣ 1)⌝ : V) = codeTerm Y) :
    termSubst LAct w (⌜(Rew.emb (simT1 x y) : SyntacticSemiterm ℒₒᵣ 1)⌝ : V) = codeTerm (pSim X Y) := by
  rw [quote_emb_simT1]
  exact termSubst_sim_of w (uterm_quote_emb_LOR x) (uterm_quote_emb_LOR y) hX hY

lemma termSubst_iteT1 (w : V) {bb x y : Semiterm ℒₒᵣ Empty 1} (a : ℕ) {B X Y : V}
    (hB : termSubst LAct w (⌜(Rew.emb bb : SyntacticSemiterm ℒₒᵣ 1)⌝ : V) = codeTerm B)
    (hX : termSubst LAct w (⌜(Rew.emb x : SyntacticSemiterm ℒₒᵣ 1)⌝ : V) = codeTerm X)
    (hY : termSubst LAct w (⌜(Rew.emb y : SyntacticSemiterm ℒₒᵣ 1)⌝ : V) = codeTerm Y) :
    termSubst LAct w (⌜(Rew.emb (iteT1 bb a x y) : SyntacticSemiterm ℒₒᵣ 1)⌝ : V) = codeTerm (pIte B (a : V) X Y) := by
  rw [quote_emb_iteT1]
  exact termSubst_ite_of w (a : V) (uterm_quote_emb_LOR bb) (uterm_quote_emb_LOR x) (uterm_quote_emb_LOR y) hB hX hY

end combinators

/-! ### 3. The watch over a simple member -/

/-- **A run-stage watch over a bot-wrapped simple member**: `pIte (pSim (pBot S) (pBot S)) t (pConst p) (pConst q)`
with `S` the member's code at the budget — τ(TFTSim)'s instance at a self-prober (`t = p = 0`, `q = 1`), τ(DBot)'s
(`t = 0`, `p = 1`, `q = 0`) and the inner watch of τ(OBot)'s (`t = p = 1`, `q = 0`). -/
structure W1 where
  s : SM
  t : ℕ
  p : ℕ
  q : ℕ
  ht : t = 0 ∨ t = 1
  hp : p = 0 ∨ p = 1
  hq : q = 0 ∨ q = 1

namespace W1

/-- The watch's code at the budget `k`, in every model. -/
noncomputable def code (W : W1) (k : V) : V :=
  pIte (pSim (pBot (W.s.code k)) (pBot (W.s.code k))) (W.t : V) (pConst (W.p : V)) (pConst (W.q : V))

/-- The transposed watch: the member transposed, the test and the branches exchanged. -/
noncomputable def tr (W : W1) : W1 :=
  ⟨W.s.tr, 1 - W.t, 1 - W.p, 1 - W.q, by rcases W.ht with h | h <;> simp [h], by rcases W.hp with h | h <;> simp [h],
    by rcases W.hq with h | h <;> simp [h]⟩

lemma tr_s (W : W1) : W.tr.s = W.s.tr := rfl

lemma tr_tr (W : W1) : W.tr.tr = W := by
  obtain ⟨s, t, p, q, ht, hp, hq⟩ := W
  unfold tr
  simp only [SM.tr_tr]
  rcases ht with rfl | rfl <;> rcases hp with rfl | rfl <;> rcases hq with rfl | rfl <;> rfl

theorem transposeCode_code (W : W1) (k : V) : transposeCode (W.code k) = W.tr.code k := by
  unfold code transposeCode
  rw [revalue_ite, revalue_sim, revalue_bot, revalue_const, revalue_const]
  show pIte (pSim (pBot (revalue 1 0 (W.s.code k))) (pBot (revalue 1 0 (W.s.code k)))) (swapAction _)
    (pConst (swapAction _)) (pConst (swapAction _)) = _
  rw [show revalue 1 0 (W.s.code k) = transposeCode (W.s.code k) from rfl, SM.transposeCode_code,
    swapAction_cast W.t W.ht, swapAction_cast W.p W.hp, swapAction_cast W.q W.hq]
  rfl

/-! #### The τ-order -/

/-- The bound on the constant part `ppair t (ppair (pConst p) (pConst q))` of a watch (never evaluated). -/
noncomputable def cB : ℕ := ppair 1 (ppair (pConst 1) (pConst 1))

lemma cB_def : cB = ppair 1 (ppair (pConst 1) (pConst 1)) := rfl

attribute [irreducible] cB

/-- The threshold above which the τ-order of a watch follows its member's. -/
noncomputable def K : ℕ := cB + 1

lemma K_def : K = cB + 1 := rfl

attribute [irreducible] K

lemma pConst_le_one {a : ℕ} (ha : a = 0 ∨ a = 1) : pConst (a : V) ≤ pConst 1 := by
  unfold pConst
  refine add_le_add (ppair_le_ppair_right 0 ?_) le_rfl
  rcases ha with rfl | rfl <;> simp

lemma cast_le_one {a : ℕ} (ha : a = 0 ∨ a = 1) : (a : V) ≤ 1 := by rcases ha with rfl | rfl <;> simp

/-- The constant part of a watch is below `cB`. -/
lemma cpart_le (W : W1) : ppair (W.t : V) (ppair (pConst (W.p : V)) (pConst (W.q : V))) ≤ (cB : V) := by
  rw [cB_def, cast_ppair, cast_ppair, cast_pConst, Nat.cast_one]
  exact ppair_le_ppair (cast_le_one W.ht) (ppair_le_ppair (pConst_le_one W.hp) (pConst_le_one W.hq))

/-- Raising the FIRST argument of `ppair` by one raises it by at least `2(x + y) + 1`. -/
lemma ppair_add_le_of_succ_le_left {x x' : V} (y : V) (h : x + 1 ≤ x') :
    ppair x y + (2 * (x + y) + 1) ≤ ppair x' y := by
  have h1 : (x + y + 1) * (x + y + 1) ≤ (x' + y) * (x' + y) :=
    mul_le_mul (by rw [add_right_comm]; exact add_le_add h le_rfl)
      (by rw [add_right_comm]; exact add_le_add h le_rfl) (by simp) (by simp)
  unfold ppair
  calc (x + y) * (x + y) + y + (2 * (x + y) + 1) = (x + y + 1) * (x + y + 1) + y := by ring
    _ ≤ (x' + y) * (x' + y) + y := add_le_add h1 le_rfl

/-- **The gain through the three wrappers**: a strictly larger member raises `pSim (pBot S) (pBot S)` by at least
`S`. -/
theorem sim_gain {S S' : V} (h : S + 1 ≤ S') : pSim (pBot S) (pBot S) + S ≤ pSim (pBot S') (pBot S') := by
  have hS : S ≤ pBot S := by unfold pBot; exact le_trans (le_ppair_right 3 S) le_self_add
  have h1 : pBot S + 1 ≤ pBot S' := by
    unfold pBot
    exact add_le_add (lt_iff_succ_le.mp (ppair_lt_ppair_right 3 (lt_iff_succ_le.mpr h))) le_rfl
  set Z := ppair (pBot S) (pBot S) with hZ
  set Z' := ppair (pBot S') (pBot S') with hZ'
  have h2 : Z + (2 * (pBot S + pBot S) + 2) ≤ ppair (pBot S) (pBot S') := ppair_add_le_of_succ_le (pBot S) h1
  have h3 : ppair (pBot S) (pBot S') ≤ Z' := ppair_le_ppair_left (le_trans le_self_add h1) _
  have hZS : Z + S + 1 ≤ Z' := by
    calc Z + S + 1 ≤ Z + (2 * (pBot S + pBot S) + 2) := by
          rw [add_assoc]
          refine add_le_add le_rfl ?_
          calc S + 1 ≤ pBot S + 1 := add_le_add hS le_rfl
            _ ≤ 2 * (pBot S + pBot S) + 2 := by
              have : pBot S ≤ 2 * (pBot S + pBot S) := by
                calc pBot S ≤ pBot S + pBot S := le_self_add
                  _ ≤ 2 * (pBot S + pBot S) := by rw [two_mul]; exact le_self_add
              exact add_le_add this (by norm_num)
      _ ≤ ppair (pBot S) (pBot S') := h2
      _ ≤ Z' := h3
  have hSZ : S ≤ Z := le_trans hS (le_ppair_left _ _)
  have h4 : ppair 4 Z + (2 * (4 + Z) + 2) ≤ ppair 4 Z' := ppair_add_le_of_succ_le 4 (le_trans (add_le_add le_self_add le_rfl) hZS)
  unfold pSim
  calc ppair 4 Z + 1 + S = ppair 4 Z + (S + 1) := by ring
    _ ≤ ppair 4 Z + (2 * (4 + Z) + 2) := by
        refine add_le_add le_rfl ?_
        calc S + 1 ≤ Z + 1 := add_le_add hSZ le_rfl
          _ ≤ 2 * (4 + Z) + 2 := by
            have : Z ≤ 2 * (4 + Z) := by
              calc Z ≤ 4 + Z := le_add_self
                _ ≤ 2 * (4 + Z) := by rw [two_mul]; exact le_self_add
            exact add_le_add this (by norm_num)
    _ ≤ ppair 4 Z' := h4
    _ ≤ ppair 4 Z' + 1 := le_self_add

/-- **The order of a watch follows its member's above the threshold.** -/
theorem code_lt_tr (W : W1) {k : V} (hk : (K : V) ≤ k) (h : W.s.orig) : W.code k < W.tr.code k := by
  unfold code
  have hS : W.s.code k + 1 ≤ W.s.tr.code k := lt_iff_succ_le.mp (SM.code_lt_tr W.s k h)
  have hg := sim_gain hS
  unfold pIte
  rw [add_lt_add_iff_right, ppair_lt_ppair_right_iff]
  apply ppair_lt_of_add_lt
  have hK : (cB : V) + 1 = (K : V) := by rw [K_def]; push_cast; rfl
  calc pSim (pBot (W.s.code k)) (pBot (W.s.code k)) + ppair (W.t : V) (ppair (pConst (W.p : V)) (pConst (W.q : V)))
      ≤ pSim (pBot (W.s.code k)) (pBot (W.s.code k)) + cB := add_le_add le_rfl (cpart_le W)
    _ < pSim (pBot (W.s.code k)) (pBot (W.s.code k)) + cB + 1 := lt_add_one _
    _ = pSim (pBot (W.s.code k)) (pBot (W.s.code k)) + (K : V) := by rw [add_assoc, hK]
    _ ≤ pSim (pBot (W.s.code k)) (pBot (W.s.code k)) + k := add_le_add le_rfl hk
    _ ≤ pSim (pBot (W.s.code k)) (pBot (W.s.code k)) + W.s.code k := add_le_add le_rfl (SM.le_code _ k)
    _ ≤ pSim (pBot (W.s.tr.code k)) (pBot (W.s.tr.code k)) := hg
    _ ≤ pSim (pBot (W.s.tr.code k)) (pBot (W.s.tr.code k)) +
          ppair ((1 - W.t : ℕ) : V) (ppair (pConst ((1 - W.p : ℕ) : V)) (pConst ((1 - W.q : ℕ) : V))) := le_self_add

lemma tr_orig_of_not {W : W1} (h : ¬ W.s.orig) : W.tr.s.orig := by
  show W.s.tr.inner < W.s.tr.tr.inner
  rw [SM.tr_tr]
  exact lt_of_le_of_ne (not_lt.mp h) (Ne.symm (SM.inner_ne_tr _))

theorem tr_lt_code (W : W1) {k : V} (hk : (K : V) ≤ k) (h : ¬ W.s.orig) : W.tr.code k < W.code k := by
  have := code_lt_tr W.tr hk (tr_orig_of_not h)
  rwa [tr_tr] at this

/-! #### The canonical shape -/

def orig (W : W1) : Prop := W.s.orig

open scoped Classical in
noncomputable def can (W : W1) : W1 := if W.orig then W else W.tr
open scoped Classical in
noncomputable def uT (W : W1) : ClosedSemiterm LAct 0 := if W.orig then cterm Act.C else cterm Act.D
open scoped Classical in
noncomputable def wT (W : W1) : ClosedSemiterm LAct 0 := if W.orig then cterm Act.D else cterm Act.C

theorem canonical_code (W : W1) {k : V} (hk : (K : V) ≤ k) : canonical (W.code k) = W.can.code k := by
  unfold can
  by_cases h : W.orig
  · rw [if_pos h, canonical_of_lt (by rw [transposeCode_code]; exact code_lt_tr W hk h)]
  · rw [if_neg h, canonical_of_gt (by rw [transposeCode_code]; exact tr_lt_code W hk h), transposeCode_code]

theorem revalueU_code (W : W1) {k : V} (hk : (K : V) ≤ k) : revalueU (W.code k) = (⌜W.uT⌝ : V) := by
  unfold revalueU uT
  rw [transposeCode_code]
  by_cases h : W.orig
  · rw [if_pos (code_lt_tr W hk h), if_pos h, quote_cterm_C]
  · rw [if_neg (lt_asymm (tr_lt_code W hk h)), if_pos (tr_lt_code W hk h), if_neg h, quote_cterm_D]

theorem revalueW_code (W : W1) {k : V} (hk : (K : V) ≤ k) : revalueW (W.code k) = (⌜W.wT⌝ : V) := by
  unfold revalueW wT
  rw [transposeCode_code]
  by_cases h : W.orig
  · rw [if_pos (code_lt_tr W hk h), if_pos h, quote_cterm_D]
  · rw [if_neg (lt_asymm (tr_lt_code W hk h)), if_pos (tr_lt_code W hk h), if_neg h, quote_cterm_C]

theorem revalue_val_uT_wT (W : W1) (k : V) :
    revalue (W.uT.val (s := stdReadingV V) ![] Empty.elim) (W.wT.val (s := stdReadingV V) ![] Empty.elim)
      (W.can.code k) = W.code k := by
  unfold uT wT can
  by_cases h : W.orig
  · rw [if_pos h, if_pos h, if_pos h, val_cterm_C_V, val_cterm_D_V, revalue_zero_one]
  · rw [if_neg h, if_neg h, if_neg h, val_cterm_D_V, val_cterm_C_V]
    show transposeCode (W.tr.code k) = _
    rw [← transposeCode_code W k, transposeCode_transposeCode]

theorem revalue_val_uT_wT_swap (W : W1) (k : V) :
    revalue ((Semiterm.lMap swap W.uT).val (s := stdReadingV V) ![] Empty.elim)
      ((Semiterm.lMap swap W.wT).val (s := stdReadingV V) ![] Empty.elim) (W.can.code k) = W.tr.code k := by
  unfold uT wT can
  by_cases h : W.orig
  · rw [if_pos h, if_pos h, if_pos h, lMap_swap_cterm_C, lMap_swap_cterm_D, val_cterm_D_V, val_cterm_C_V]
    show transposeCode (W.code k) = _
    rw [transposeCode_code]
  · rw [if_neg h, if_neg h, if_neg h, lMap_swap_cterm_D, lMap_swap_cterm_C, val_cterm_C_V, val_cterm_D_V,
      revalue_zero_one]

theorem canonical_tr_code (W : W1) {k : V} (hk : (K : V) ≤ k) : canonical (W.tr.code k) = W.can.code k := by
  rw [← transposeCode_code, canonical_transposeCode, canonical_code W hk]

theorem revalueU_tr_code (W : W1) {k : V} (hk : (K : V) ≤ k) :
    revalueU (W.tr.code k) = (⌜Semiterm.lMap swap W.uT⌝ : V) := by
  have e : transposeCode (W.tr.code k) = W.code k := by rw [← transposeCode_code, transposeCode_transposeCode]
  unfold revalueU uT
  rw [e]
  by_cases h : W.orig
  · rw [if_neg (lt_asymm (code_lt_tr W hk h)), if_pos (code_lt_tr W hk h), if_pos h, lMap_swap_cterm_C, quote_cterm_D]
  · rw [if_pos (tr_lt_code W hk h), if_neg h, lMap_swap_cterm_D, quote_cterm_C]

theorem revalueW_tr_code (W : W1) {k : V} (hk : (K : V) ≤ k) :
    revalueW (W.tr.code k) = (⌜Semiterm.lMap swap W.wT⌝ : V) := by
  have e : transposeCode (W.tr.code k) = W.code k := by rw [← transposeCode_code, transposeCode_transposeCode]
  unfold revalueW wT
  rw [e]
  by_cases h : W.orig
  · rw [if_neg (lt_asymm (code_lt_tr W hk h)), if_pos (code_lt_tr W hk h), if_pos h, lMap_swap_cterm_D, quote_cterm_C]
  · rw [if_pos (tr_lt_code W hk h), if_neg h, lMap_swap_cterm_C, quote_cterm_D]

/-! #### The towers -/

/-- The one-variable ℒₒᵣ-term of the watch. -/
noncomputable def T1 (W : W1) : Semiterm ℒₒᵣ Empty 1 :=
  iteT1 (simT1 (botT1 W.s.T1) (botT1 W.s.T1)) W.t (constT1 W.p) (constT1 W.q)

lemma val_T1_V (W : W1) (k : V) : (W.T1).val (s := standardModel V) ![k] Empty.elim = W.code k := by
  rw [T1, val_iteT1_V, val_simT1_V, val_botT1_V, SM.val_T1_V, val_constT1_V, val_constT1_V]
  rfl

lemma termSubst_T1 (W : W1) (k : V) :
    termSubst LAct (binNumeral k ∷ (0 : V)) (⌜(Rew.emb W.T1 : SyntacticSemiterm ℒₒᵣ 1)⌝ : V) = codeTerm (W.code k) := by
  rw [T1]
  exact termSubst_iteT1 _ W.t
    (termSubst_simT1 _ (termSubst_botT1 _ (SM.termSubst_T1 _ _)) (termSubst_botT1 _ (SM.termSubst_T1 _ _)))
    (termSubst_constT1 _ _) (termSubst_constT1 _ _)

/-- **The frame tower** of the bot-wrapped watch `pBot (W.code k)`. -/
noncomputable def TX (W : W1) : Semiterm LAct Empty 1 := Semiterm.lMap emb (botT1 W.can.T1)

lemma lMap_swap_TX (W : W1) : Semiterm.lMap swap W.TX = W.TX := term_lMap_swap_emb _

theorem val_TX_V (W : W1) {k : V} (hk : (K : V) ≤ k) :
    W.TX.val (s := stdReadingV V) ![k] Empty.elim = canonical (pBot (W.code k)) := by
  unfold TX
  rw [Semiterm.val_lMap, stdReadingV_lMap_emb, val_botT1_V, val_T1_V, canonical_pBot, canonical_code W hk]

theorem hX_TX (W : W1) {k : V} (hk : (K : V) ≤ k) :
    termSubst LAct (binNumeral k ∷ (0 : V)) (⌜(Rew.emb W.TX : SyntacticSemiterm LAct 1)⌝ : V) =
      codeTerm (canonical (pBot (W.code k))) := by
  unfold TX
  rw [term_emb_lMap_emb_n, quote_term_lMap_emb, termSubst_botT1 _ (termSubst_T1 _ _), canonical_pBot, canonical_code W hk]

theorem descVal_TX (W : W1) {k : V} (hk : (K : V) ≤ k) : descVal W.TX W.uT W.wT k = pBot (W.code k) := by
  rw [descVal_def, val_TX_V W hk, canonical_pBot, revalue_bot, canonical_code W hk, revalue_val_uT_wT]

theorem descVal_TX_T (W : W1) {k : V} (hk : (K : V) ≤ k) :
    descVal (Semiterm.lMap swap W.TX) (Semiterm.lMap swap W.uT) (Semiterm.lMap swap W.wT) k = pBot (W.tr.code k) := by
  rw [descVal_def, lMap_swap_TX, val_TX_V W hk, canonical_pBot, revalue_bot, canonical_code W hk, revalue_val_uT_wT_swap]

/-- **The frame tower describes the bot-wrapped watch above the threshold.** -/
theorem describesBot (W : W1) : DescribesAbove K W.TX W.uT W.wT where
  hX := fun V _ _ k hk ↦ by rw [descVal_TX W hk]; exact hX_TX W hk
  hU := fun V _ _ k hk ↦ by rw [descVal_TX W hk, revalueU_pBot, revalueU_code W hk]
  hW := fun V _ _ k hk ↦ by rw [descVal_TX W hk, revalueW_pBot, revalueW_code W hk]
  hT := fun V _ _ k hk ↦ by rw [descVal_TX_T W hk, descVal_TX W hk, transposeCode_pBot, transposeCode_code]

end W1

end ArithS.Tau
