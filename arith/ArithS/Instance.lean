import ArithS.Fit
import ArithS.Code

/-!
# ArithS.Instance — Dupoc's guard is the `k`-instance of ONE fixed formula

Roadmap M4, item U0 (`M4_BOUNDED_HBL/BRIEF.md` §2): the parametric bounded Löb argument
needs the guard sentence of `Dupoc k` to be `q(k̂)` for a FIXED one-variable formula `q` and
the binary numeral `k̂` — Critch's "source with `k` written in binary". With programs
described by the structural terms of their codes (`ArithS.ProgT`, `ArithS.Guard`) this is
now an equation:

* the canonical code `dnum (Dupoc k)` is `pSearch k G P Q` for a `k`-INDEPENDENT inner
  triple — Dupoc's own `(⌜GtmplA 0⌝, pConst 0, pConst 1)` or Cupod's — decided by ONE fixed
  inequality `innerD ≤ innerC` between two closed constants (`ppair` is strictly monotone in
  each argument, so `Dupoc k ≤ Cupod k ↔ innerD ≤ innerC` uniformly in `k`; the inequality is
  never evaluated), and likewise `dU (Dupoc k)`, `dW (Dupoc k)` are `k`-independent;
* `progTT (pSearch k G P Q) = TD ⇜ ![bnumT k]` for the fixed one-variable term
  `TD = succ (ppairT 6̂ (ppairT #0 (ppairT Ĝ (ppairT (progTT P) (progTT Q)))))`;
* hence **`exists_dupoc_instance`**: `∃ q : Semisentence LAct 1, ∀ k, guardSentenceA 0
  (Dupoc k) (Dupoc k) = q ⇜ ![lMap emb (bnumT k)]`, and its code form
  **`exists_dupoc_instance_code`**: `∃ cq, IsSemiformula LAct 1 cq ∧ ∀ k, guardCode ⌜GtmplA 0⌝
  (Dupoc k) (Dupoc k) = subst LAct (bnum k ∷ 0) cq` (through the code equation
  `quote_guardSentenceA` and the quote of a substitution instance).

Everything here is at `ℕ` (the meta level, where `Dupoc` lives); `ArithS.InstanceV` re-runs
the analysis inside every model of `𝗜𝚺₁` (`exists_dupoc_instance_code_V`, for possibly
nonstandard budgets `k : V`).
-/

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open LAct

/-! ### 1. `ppair` reflects the order in its second argument -/

section ppairOrder

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

lemma ppair_lt_ppair_right_iff (x : V) {y₁ y₂ : V} : ppair x y₁ < ppair x y₂ ↔ y₁ < y₂ := by
  constructor
  · intro h
    rcases lt_trichotomy y₁ y₂ with h' | rfl | h'
    · exact h'
    · exact absurd h (_root_.lt_irrefl _)
    · exact absurd (lt_trans h (ppair_lt_ppair_right x h')) (_root_.lt_irrefl _)
  · exact ppair_lt_ppair_right x

lemma ppair_le_ppair_right_iff (x : V) {y₁ y₂ : V} : ppair x y₁ ≤ ppair x y₂ ↔ y₁ ≤ y₂ := by
  rw [← not_lt, ← not_lt, ppair_lt_ppair_right_iff]

/-- Two searchers of the same budget compare as their budget-independent inner parts. -/
lemma pSearchInner_le_iff (k a b : V) :
    ppair 6 (ppair k a) + 1 ≤ ppair 6 (ppair k b) + 1 ↔ a ≤ b := by
  rw [add_le_add_iff_right, ppair_le_ppair_right_iff, ppair_le_ppair_right_iff]

lemma pSearchInner_lt_iff (k a b : V) :
    ppair 6 (ppair k a) + 1 < ppair 6 (ppair k b) + 1 ↔ a < b := by
  rw [← not_le, ← not_le, pSearchInner_le_iff]

end ppairOrder

/-! ### 2. The canonical description of `Dupoc k` is `k`-independent apart from the budget -/

section canonical

/-- The budget-independent inner part of Dupoc's code. -/
noncomputable def innerD : ℕ := ppair (⌜GtmplA 0⌝ : ℕ) (ppair (pConst 0) (pConst 1))

/-- The budget-independent inner part of Cupod's code. -/
noncomputable def innerC : ℕ := ppair (⌜GtmplA 1⌝ : ℕ) (ppair (pConst 1) (pConst 0))

lemma innerD_def : innerD = ppair (⌜GtmplA 0⌝ : ℕ) (ppair (pConst 0) (pConst 1)) := rfl
lemma innerC_def : innerC = ppair (⌜GtmplA 1⌝ : ℕ) (ppair (pConst 1) (pConst 0)) := rfl
lemma Dupoc_eq_inner (k : ℕ) : Dupoc k = ppair 6 (ppair k innerD) + 1 := rfl
lemma Cupod_eq_inner (k : ℕ) : Cupod k = ppair 6 (ppair k innerC) + 1 := rfl

/- Closed constants built from the giant templates: never to be evaluated. -/
attribute [irreducible] innerD innerC

lemma Dupoc_lt_Cupod_iff (k : ℕ) : Dupoc k < Cupod k ↔ innerD < innerC := by
  rw [Dupoc_eq_inner, Cupod_eq_inner]; exact pSearchInner_lt_iff k innerD innerC

lemma Cupod_lt_Dupoc_iff (k : ℕ) : Cupod k < Dupoc k ↔ innerC < innerD := by
  rw [Dupoc_eq_inner, Cupod_eq_inner]; exact pSearchInner_lt_iff k innerC innerD

/-- The stored template of the canonical searcher (`⌜GtmplA 0⌝` or `⌜GtmplA 1⌝`). -/
noncomputable def gD : ℕ := if innerD ≤ innerC then (⌜GtmplA 0⌝ : ℕ) else (⌜GtmplA 1⌝ : ℕ)
/-- Its then-branch. -/
noncomputable def pD : ℕ := if innerD ≤ innerC then pConst 0 else pConst 1
/-- Its else-branch. -/
noncomputable def qD : ℕ := if innerD ≤ innerC then pConst 1 else pConst 0
/-- The first re-valuation term of the description of `Dupoc k`. -/
noncomputable def uD : ClosedSemiterm LAct 0 :=
  if innerD < innerC then cterm Act.C else if innerC < innerD then cterm Act.D else numT 0
/-- The second re-valuation term of the description of `Dupoc k`. -/
noncomputable def wD : ClosedSemiterm LAct 0 :=
  if innerD < innerC then cterm Act.D else if innerC < innerD then cterm Act.C else numT 1

/-- **The canonical code of `Dupoc k` is a searcher with a `k`-independent inner triple.** -/
theorem dnum_Dupoc (k : ℕ) : dnum (Dupoc k) = pSearch k gD pD qD := by
  by_cases h : innerD ≤ innerC
  · simp only [gD, pD, qD, if_pos h]
    rcases Nat.lt_or_eq_of_le h with h' | h'
    · rw [dnum_of_lt (by rw [swapcode_Dupoc]; exact (Dupoc_lt_Cupod_iff k).mpr h')]; rfl
    · rw [dnum_of_eq (by rw [swapcode_Dupoc, Dupoc_eq_inner, Cupod_eq_inner, h'])]; rfl
  · simp only [gD, pD, qD, if_neg h]
    rw [dnum_of_gt (by rw [swapcode_Dupoc]; exact (Cupod_lt_Dupoc_iff k).mpr (Nat.lt_of_not_le h)),
      swapcode_Dupoc]
    rfl

theorem dUT_Dupoc (k : ℕ) : dUT (Dupoc k) = uD := by
  unfold dUT uD
  rw [swapcode_Dupoc]
  by_cases h1 : innerD < innerC
  · rw [if_pos ((Dupoc_lt_Cupod_iff k).mpr h1), if_pos h1]
  · rw [if_neg (fun h ↦ h1 ((Dupoc_lt_Cupod_iff k).mp h)), if_neg h1]
    by_cases h2 : innerC < innerD
    · rw [if_pos ((Cupod_lt_Dupoc_iff k).mpr h2), if_pos h2]
    · rw [if_neg (fun h ↦ h2 ((Cupod_lt_Dupoc_iff k).mp h)), if_neg h2]

theorem dWT_Dupoc (k : ℕ) : dWT (Dupoc k) = wD := by
  unfold dWT wD
  rw [swapcode_Dupoc]
  by_cases h1 : innerD < innerC
  · rw [if_pos ((Dupoc_lt_Cupod_iff k).mpr h1), if_pos h1]
  · rw [if_neg (fun h ↦ h1 ((Dupoc_lt_Cupod_iff k).mp h)), if_neg h1]
    by_cases h2 : innerC < innerD
    · rw [if_pos ((Cupod_lt_Dupoc_iff k).mpr h2), if_pos h2]
    · rw [if_neg (fun h ↦ h2 ((Cupod_lt_Dupoc_iff k).mp h)), if_neg h2]

end canonical

/-! ### 3. The structural term of a searcher is the `k`-instance of a one-variable term -/

section oneVariable

/-- The one-variable pairing term (bound variables allowed). -/
noncomputable def ppairT1 (s t : Semiterm ℒₒᵣ Empty 1) : Semiterm ℒₒᵣ Empty 1 :=
  Semiterm.func Language.ORing.Func.add
    ![Semiterm.func Language.ORing.Func.mul
      ![Semiterm.func Language.ORing.Func.add ![s, t], Semiterm.func Language.ORing.Func.add ![s, t]], t]

/-- The meta numeral `1` as a closed term. -/
noncomputable def oneTT : ClosedSemiterm ℒₒᵣ 0 := ‘1’

/-- The one-variable successor term. -/
noncomputable def succT1 (t : Semiterm ℒₒᵣ Empty 1) : Semiterm ℒₒᵣ Empty 1 :=
  Semiterm.func Language.ORing.Func.add ![t, Rew.bShift oneTT]

lemma ppairTT_func (s t : ClosedSemiterm ℒₒᵣ 0) :
    ppairTT s t = Semiterm.func Language.ORing.Func.add
      ![Semiterm.func Language.ORing.Func.mul
        ![Semiterm.func Language.ORing.Func.add ![s, t], Semiterm.func Language.ORing.Func.add ![s, t]], t] := rfl

lemma succTT_func (t : ClosedSemiterm ℒₒᵣ 0) :
    succTT t = Semiterm.func Language.ORing.Func.add ![t, oneTT] := rfl

lemma subst_func₂ (v : Fin 1 → ClosedSemiterm ℒₒᵣ 0) (f : (ℒₒᵣ).Func 2) (s t : Semiterm ℒₒᵣ Empty 1) :
    Rew.subst v (Semiterm.func f ![s, t]) = Semiterm.func f ![Rew.subst v s, Rew.subst v t] := by
  rw [Rew.func]; congr 1; funext i; fin_cases i <;> rfl

lemma subst_bShift₁ (u : ClosedSemiterm ℒₒᵣ 0) (t : ClosedSemiterm ℒₒᵣ 0) :
    Rew.subst ![u] (Rew.bShift t) = t := by
  rw [← Rew.comp_app, Rew.subst_comp_bShift_eq_id]; rfl

lemma subst_ppairT1 (u : ClosedSemiterm ℒₒᵣ 0) (s t : Semiterm ℒₒᵣ Empty 1) :
    Rew.subst ![u] (ppairT1 s t) = ppairTT (Rew.subst ![u] s) (Rew.subst ![u] t) := by
  rw [ppairT1, ppairTT_func, subst_func₂, subst_func₂, subst_func₂]

lemma subst_succT1 (u : ClosedSemiterm ℒₒᵣ 0) (t : Semiterm ℒₒᵣ Empty 1) :
    Rew.subst ![u] (succT1 t) = succTT (Rew.subst ![u] t) := by
  rw [succT1, succTT_func, subst_func₂, subst_bShift₁]

/-- The one-variable structural term of the searcher `pSearch · g p q`. -/
noncomputable def searchT1 (g p q : ℕ) : Semiterm ℒₒᵣ Empty 1 :=
  succT1 (ppairT1 (Rew.bShift (bnumT 6)) (ppairT1 #0
    (Rew.bShift (ppairTT (bnumT g) (ppairTT (progTT p) (progTT q))))))

/-- **The structural term of a searcher is the `k`-instance of `searchT1`.** -/
theorem progTT_search_eq_subst (k g p q : ℕ) :
    progTT (pSearch k g p q) = Rew.subst ![bnumT k] (searchT1 g p q) := by
  rw [progTT_search, searchT1, subst_succT1, subst_ppairT1, subst_ppairT1, subst_bShift₁, subst_bShift₁,
    Rew.subst_bvar]
  rfl

/-- `lMap` commutes with a one-variable substitution. -/
lemma term_lMap_subst₁ (b : ClosedSemiterm ℒₒᵣ 0) (T : Semiterm ℒₒᵣ Empty 1) :
    Semiterm.lMap emb (Rew.subst ![b] T) = Rew.subst ![Semiterm.lMap emb b] (Semiterm.lMap emb T) := by
  unfold Rew.subst
  rw [Semiterm.lMap_bind]
  have e1 : Semiterm.lMap emb ∘ ![b] = ![Semiterm.lMap emb b] := by funext i; fin_cases i; rfl
  have e2 : Semiterm.lMap emb ∘ (Semiterm.fvar : Empty → Semiterm ℒₒᵣ Empty 0) = Semiterm.fvar := by
    funext x; exact x.elim
  rw [e1, e2]

/-- The one-variable description term of `Dupoc`, over `LAct`. -/
noncomputable def TD : Semiterm LAct Empty 1 := Semiterm.lMap emb (searchT1 gD pD qD)

/-- **The description of `Dupoc k` is the `k`-instance of `TD`.** -/
theorem dnumT_Dupoc (k : ℕ) : dnumT (Dupoc k) = Rew.subst ![Semiterm.lMap emb (bnumT k)] TD := by
  unfold dnumT TD
  rw [dnum_Dupoc, progTT_search_eq_subst, term_lMap_subst₁]

end oneVariable

/-! ### 4. The instance equation -/

section instance_eq

/-- A closed term cast to zero bound variables is itself. -/
lemma cl_zero : ∀ t : ClosedSemiterm LAct 0, (cl t : Semiterm LAct Empty 0) = t
  | #x => x.elim0
  | &x => x.elim
  | .func f v => by
    show Rew.castLE _ (Semiterm.func f v) = Semiterm.func f v
    rw [Rew.func]
    congr 1
    funext i
    exact cl_zero (v i)

/-- **The fixed formula**: the template instance `GtmplA 0` filled with the one-variable
description of Dupoc (twice: `me = opp = Dupoc k`) and its `k`-independent re-valuation terms. -/
noncomputable def qDupoc : Semisentence LAct 1 :=
  GtmplA 0 ⇜ ![TD, cl uD, cl wD, TD, cl uD, cl wD]

/-- **The instance equation (meta)**: Dupoc's guard sentence against itself is the `k`-instance
of the fixed formula `qDupoc`. -/
theorem guardSentenceA_Dupoc_eq (k : ℕ) :
    guardSentenceA 0 (Dupoc k) (Dupoc k) = qDupoc ⇜ ![Semiterm.lMap emb (bnumT k)] := by
  have hv : descTerms (Dupoc k) (Dupoc k) =
      fun i ↦ Rew.subst ![Semiterm.lMap emb (bnumT k)] (![TD, cl uD, cl wD, TD, cl uD, cl wD] i) := by
    funext i
    fin_cases i <;> simp [descTerms, dnumT_Dupoc, dUT_Dupoc, dWT_Dupoc, rew_cl, cl_zero]
  unfold guardSentenceA qDupoc Rewriting.subst
  rw [← TransitiveRewriting.comp_app, comp_subst_eq, hv]

/-- **The instance equation, existentially packaged.** -/
theorem exists_dupoc_instance :
    ∃ q : Semisentence LAct 1, ∀ k : ℕ,
      guardSentenceA 0 (Dupoc k) (Dupoc k) = q ⇜ ![Semiterm.lMap emb (bnumT k)] :=
  ⟨qDupoc, guardSentenceA_Dupoc_eq⟩

/-! #### The code form -/

lemma quote_lMap_emb_bnumT (k : ℕ) : (⌜Semiterm.lMap emb (bnumT k)⌝ : ℕ) = bnum k := by
  rw [Semiterm.empty_quote_def, term_emb_lMap_emb, quote_term_lMap_emb, ← Semiterm.empty_quote_def,
    quote_bnumT_nat]

lemma semitermVec_val_single (k : ℕ) :
    SemitermVec.val (fun i ↦ (⌜(Rew.emb ((![Semiterm.lMap emb (bnumT k)] : Fin 1 → ClosedSemiterm LAct 0) i) :
      SyntacticSemiterm LAct 0)⌝ : Bootstrapping.Semiterm ℕ LAct 0)) = bnum k ∷ 0 := by
  have hv : (fun i ↦ (⌜(Rew.emb ((![Semiterm.lMap emb (bnumT k)] : Fin 1 → ClosedSemiterm LAct 0) i) :
      SyntacticSemiterm LAct 0)⌝ : Bootstrapping.Semiterm ℕ LAct 0)) =
      ![⌜(Rew.emb (Semiterm.lMap emb (bnumT k)) : SyntacticSemiterm LAct 0)⌝] := by
    funext i; fin_cases i; rfl
  rw [hv]
  simp only [SemitermVec.val_cons, SemitermVec.val_nil, typed_val_emb, quote_lMap_emb_bnumT]

/-- **The instance equation on codes**: Dupoc's guard code is the substitution of the binary
numeral of `k` into the code of `qDupoc`. -/
theorem guardCode_Dupoc_eq (k : ℕ) :
    guardCode (⌜GtmplA 0⌝ : ℕ) (Dupoc k) (Dupoc k) = subst LAct (bnum k ∷ 0) (⌜qDupoc⌝ : ℕ) := by
  rw [← quote_guardSentenceA, guardSentenceA_Dupoc_eq, Sentence.quote_def,
    Semiformula.coe_subst_eq_subst_coe, Semiformula.quote_def, Semiformula.typed_quote_substs,
    Bootstrapping.Semiformula.val_substs, ← Semiformula.quote_def, ← Sentence.quote_def]
  congr 1
  exact semitermVec_val_single k

/-- **The instance equation on codes, existentially packaged.** -/
theorem exists_dupoc_instance_code :
    ∃ cq : ℕ, IsSemiformula LAct 1 cq ∧
      ∀ k : ℕ, guardCode (⌜GtmplA 0⌝ : ℕ) (Dupoc k) (Dupoc k) = subst LAct (bnum k ∷ 0) cq :=
  ⟨⌜qDupoc⌝, by simp, guardCode_Dupoc_eq⟩

end instance_eq

end ArithS
