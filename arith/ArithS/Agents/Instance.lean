import ArithS.Agents.Fit
import ArithS.Agents.Code

/-!
# ArithS.Instance — Dupoc's guard is the `k`-instance of ONE fixed formula

Roadmap M4, item U0 (`M4_BOUNDED_HBL/BRIEF.md` §2): the parametric bounded Löb argument
needs the guard sentence of `Dupoc k` to be `q(k̂)` for a FIXED one-variable formula `q` and
the binary numeral `k̂` — Critch's "source with `k` written in binary". With programs
described by the structural terms of their codes (`ArithS.CodeTerm`, `ArithS.Guard`) this is
now an equation:

* the canonical code `canonical (Dupoc k)` is `pSearch k G P Q` for a `k`-INDEPENDENT inner
  triple — Dupoc's own `(⌜guardTemplate 0⌝, pConst 0, pConst 1)` or Cupod's — decided by ONE fixed
  inequality `innerD ≤ innerC` between two closed constants (`ppair` is strictly monotone in
  each argument, so `Dupoc k ≤ Cupod k ↔ innerD ≤ innerC` uniformly in `k`; the inequality is
  never evaluated), and likewise `revalueU (Dupoc k)`, `revalueW (Dupoc k)` are `k`-independent;
* `codeTermMeta (pSearch k G P Q) = TD ⇜ ![binNumeralMeta k]` for the fixed one-variable term
  `TD = succ (ppairTerm 6̂ (ppairTerm #0 (ppairTerm Ĝ (ppairTerm (codeTermMeta P) (codeTermMeta Q)))))`;
* hence **`exists_dupoc_instance`**: `∃ q : Semisentence LAct 1, ∀ k, guardSentence 0
  (Dupoc k) (Dupoc k) = q ⇜ ![lMap emb (binNumeralMeta k)]`, and its code form
  **`exists_dupoc_instance_code`**: `∃ cq, IsSemiformula LAct 1 cq ∧ ∀ k, guardCode ⌜guardTemplate 0⌝
  (Dupoc k) (Dupoc k) = subst LAct (binNumeral k ∷ 0) cq` (through the code equation
  `quote_guardSentence` and the quote of a substitution instance).

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

-- `ppair_lt_ppair_right_iff`/`ppair_le_ppair_right_iff` moved to `Agents/SubstTemplate.lean` (2026-10-01).

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
noncomputable def innerD : ℕ := ppair (⌜guardTemplate 0⌝ : ℕ) (ppair (pConst 0) (pConst 1))

/-- The budget-independent inner part of Cupod's code. -/
noncomputable def innerC : ℕ := ppair (⌜guardTemplate 1⌝ : ℕ) (ppair (pConst 1) (pConst 0))

lemma innerD_def : innerD = ppair (⌜guardTemplate 0⌝ : ℕ) (ppair (pConst 0) (pConst 1)) := rfl
lemma innerC_def : innerC = ppair (⌜guardTemplate 1⌝ : ℕ) (ppair (pConst 1) (pConst 0)) := rfl
lemma Dupoc_eq_inner (k : ℕ) : Dupoc k = ppair 6 (ppair k innerD) + 1 := rfl
lemma Cupod_eq_inner (k : ℕ) : Cupod k = ppair 6 (ppair k innerC) + 1 := rfl

/- Closed constants built from the giant templates: never to be evaluated. -/
attribute [irreducible] innerD innerC

lemma Dupoc_lt_Cupod_iff (k : ℕ) : Dupoc k < Cupod k ↔ innerD < innerC := by
  rw [Dupoc_eq_inner, Cupod_eq_inner]; exact pSearchInner_lt_iff k innerD innerC

lemma Cupod_lt_Dupoc_iff (k : ℕ) : Cupod k < Dupoc k ↔ innerC < innerD := by
  rw [Dupoc_eq_inner, Cupod_eq_inner]; exact pSearchInner_lt_iff k innerC innerD

/-- The stored template of the canonical searcher (`⌜guardTemplate 0⌝` or `⌜guardTemplate 1⌝`). -/
noncomputable def gD : ℕ := if innerD ≤ innerC then (⌜guardTemplate 0⌝ : ℕ) else (⌜guardTemplate 1⌝ : ℕ)
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
theorem canonical_Dupoc (k : ℕ) : canonical (Dupoc k) = pSearch k gD pD qD := by
  by_cases h : innerD ≤ innerC
  · simp only [gD, pD, qD, if_pos h]
    rcases Nat.lt_or_eq_of_le h with h' | h'
    · rw [canonical_of_lt (by rw [transposeCode_Dupoc]; exact (Dupoc_lt_Cupod_iff k).mpr h')]; rfl
    · rw [canonical_of_eq (by rw [transposeCode_Dupoc, Dupoc_eq_inner, Cupod_eq_inner, h'])]; rfl
  · simp only [gD, pD, qD, if_neg h]
    rw [canonical_of_gt (by rw [transposeCode_Dupoc]; exact (Cupod_lt_Dupoc_iff k).mpr (Nat.lt_of_not_le h)),
      transposeCode_Dupoc]
    rfl

theorem revalueUMeta_Dupoc (k : ℕ) : revalueUMeta (Dupoc k) = uD := by
  unfold revalueUMeta uD
  rw [transposeCode_Dupoc]
  by_cases h1 : innerD < innerC
  · rw [if_pos ((Dupoc_lt_Cupod_iff k).mpr h1), if_pos h1]
  · rw [if_neg (fun h ↦ h1 ((Dupoc_lt_Cupod_iff k).mp h)), if_neg h1]
    by_cases h2 : innerC < innerD
    · rw [if_pos ((Cupod_lt_Dupoc_iff k).mpr h2), if_pos h2]
    · rw [if_neg (fun h ↦ h2 ((Cupod_lt_Dupoc_iff k).mp h)), if_neg h2]

theorem revalueWMeta_Dupoc (k : ℕ) : revalueWMeta (Dupoc k) = wD := by
  unfold revalueWMeta wD
  rw [transposeCode_Dupoc]
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

lemma ppairTermMeta_func (s t : ClosedSemiterm ℒₒᵣ 0) :
    ppairTermMeta s t = Semiterm.func Language.ORing.Func.add
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
    Rew.subst ![u] (ppairT1 s t) = ppairTermMeta (Rew.subst ![u] s) (Rew.subst ![u] t) := by
  rw [ppairT1, ppairTermMeta_func, subst_func₂, subst_func₂, subst_func₂]

lemma subst_succT1 (u : ClosedSemiterm ℒₒᵣ 0) (t : Semiterm ℒₒᵣ Empty 1) :
    Rew.subst ![u] (succT1 t) = succTT (Rew.subst ![u] t) := by
  rw [succT1, succTT_func, subst_func₂, subst_bShift₁]

/-- The one-variable structural term of the searcher `pSearch · g p q`. -/
noncomputable def searchT1 (g p q : ℕ) : Semiterm ℒₒᵣ Empty 1 :=
  succT1 (ppairT1 (Rew.bShift (binNumeralMeta 6)) (ppairT1 #0
    (Rew.bShift (ppairTermMeta (binNumeralMeta g) (ppairTermMeta (codeTermMeta p) (codeTermMeta q))))))

/-- **The structural term of a searcher is the `k`-instance of `searchT1`.** -/
theorem codeTermMeta_search_eq_subst (k g p q : ℕ) :
    codeTermMeta (pSearch k g p q) = Rew.subst ![binNumeralMeta k] (searchT1 g p q) := by
  rw [codeTermMeta_search, searchT1, subst_succT1, subst_ppairT1, subst_ppairT1, subst_bShift₁, subst_bShift₁,
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
theorem canonicalMeta_Dupoc (k : ℕ) : canonicalMeta (Dupoc k) = Rew.subst ![Semiterm.lMap emb (binNumeralMeta k)] TD := by
  unfold canonicalMeta TD
  rw [canonical_Dupoc, codeTermMeta_search_eq_subst, term_lMap_subst₁]

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

/-- **The fixed formula**: the template instance `guardTemplate 0` filled with the one-variable
description of Dupoc (twice: `me = opp = Dupoc k`) and its `k`-independent re-valuation terms. -/
noncomputable def qDupoc : Semisentence LAct 1 :=
  guardTemplate 0 ⇜ ![TD, cl uD, cl wD, TD, cl uD, cl wD]

/-- **The instance equation (meta)**: Dupoc's guard sentence against itself is the `k`-instance
of the fixed formula `qDupoc`. -/
theorem guardSentence_Dupoc_eq (k : ℕ) :
    guardSentence 0 (Dupoc k) (Dupoc k) = qDupoc ⇜ ![Semiterm.lMap emb (binNumeralMeta k)] := by
  have hv : descriptionTerms (Dupoc k) (Dupoc k) =
      fun i ↦ Rew.subst ![Semiterm.lMap emb (binNumeralMeta k)] (![TD, cl uD, cl wD, TD, cl uD, cl wD] i) := by
    funext i
    fin_cases i <;> simp [descriptionTerms, canonicalMeta_Dupoc, revalueUMeta_Dupoc, revalueWMeta_Dupoc, rew_cl, cl_zero]
  unfold guardSentence qDupoc Rewriting.subst
  rw [← TransitiveRewriting.comp_app, comp_subst_eq, hv]

/-- **The instance equation, existentially packaged.** -/
theorem exists_dupoc_instance :
    ∃ q : Semisentence LAct 1, ∀ k : ℕ,
      guardSentence 0 (Dupoc k) (Dupoc k) = q ⇜ ![Semiterm.lMap emb (binNumeralMeta k)] :=
  ⟨qDupoc, guardSentence_Dupoc_eq⟩

/-! #### The code form -/

lemma quote_lMap_emb_binNumeralMeta (k : ℕ) : (⌜Semiterm.lMap emb (binNumeralMeta k)⌝ : ℕ) = binNumeral k := by
  rw [Semiterm.empty_quote_def, term_emb_lMap_emb, quote_term_lMap_emb, ← Semiterm.empty_quote_def,
    quote_binNumeralMeta_nat]

lemma semitermVec_val_single (k : ℕ) :
    SemitermVec.val (fun i ↦ (⌜(Rew.emb ((![Semiterm.lMap emb (binNumeralMeta k)] : Fin 1 → ClosedSemiterm LAct 0) i) :
      SyntacticSemiterm LAct 0)⌝ : Bootstrapping.Semiterm ℕ LAct 0)) = binNumeral k ∷ 0 := by
  have hv : (fun i ↦ (⌜(Rew.emb ((![Semiterm.lMap emb (binNumeralMeta k)] : Fin 1 → ClosedSemiterm LAct 0) i) :
      SyntacticSemiterm LAct 0)⌝ : Bootstrapping.Semiterm ℕ LAct 0)) =
      ![⌜(Rew.emb (Semiterm.lMap emb (binNumeralMeta k)) : SyntacticSemiterm LAct 0)⌝] := by
    funext i; fin_cases i; rfl
  rw [hv]
  simp only [SemitermVec.val_cons, SemitermVec.val_nil, typed_val_emb, quote_lMap_emb_binNumeralMeta]

/-- **The instance equation on codes**: Dupoc's guard code is the substitution of the binary
numeral of `k` into the code of `qDupoc`. -/
theorem guardCode_Dupoc_eq (k : ℕ) :
    guardCode (⌜guardTemplate 0⌝ : ℕ) (Dupoc k) (Dupoc k) = subst LAct (binNumeral k ∷ 0) (⌜qDupoc⌝ : ℕ) := by
  rw [← quote_guardSentence, guardSentence_Dupoc_eq, Sentence.quote_def,
    Semiformula.coe_subst_eq_subst_coe, Semiformula.quote_def, Semiformula.typed_quote_substs,
    Bootstrapping.Semiformula.val_substs, ← Semiformula.quote_def, ← Sentence.quote_def]
  congr 1
  exact semitermVec_val_single k

/-- **The instance equation on codes, existentially packaged.** -/
theorem exists_dupoc_instance_code :
    ∃ cq : ℕ, IsSemiformula LAct 1 cq ∧
      ∀ k : ℕ, guardCode (⌜guardTemplate 0⌝ : ℕ) (Dupoc k) (Dupoc k) = subst LAct (binNumeral k ∷ 0) cq :=
  ⟨⌜qDupoc⌝, by simp, guardCode_Dupoc_eq⟩

end instance_eq

end ArithS
