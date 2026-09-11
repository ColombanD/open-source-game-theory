import ArithS.Instance
import ArithS.InstV

/-!
# ArithS.InstanceV — the instance equation on codes, in EVERY model of `𝗜𝚺₁`

`ArithS.Instance` proves at `ℕ` that Dupoc's guard code is `subst (bnum k ∷ 0) cq` for one
fixed formula code `cq`. The parametric bounded Löb argument (roadmap M4, U6–U8) runs INSIDE
a model `V` with a possibly nonstandard budget `k : V`, so it needs the same equation for
`DupocV k := pSearch k ⌜GtmplA 0⌝ (pConst 0) (pConst 1)` at every `k : V`:

**`exists_dupoc_instance_code_V`**: `∃ cq : ℕ, IsSemiformula LAct 1 cq ∧ ∀ V k,
guardCode ⌜GtmplA 0⌝ (DupocV k) (DupocV k) = subst LAct (bnum k ∷ 0) (cq : V)`.

The proof re-runs the `ℕ` analysis inside `V`: the transposition `swapcode (DupocV k) =
CupodV k` (the code-level τ of the template is absolute, `relabelTemplate` being Σ₁), the
canonical code `dnum (DupocV k) = pSearch k ↑gD ↑pD ↑qD` (the deciding inequality between
the two constants is absolute: `Nat.cast_lt`), the `k`-independent re-valuation codes, and
then the internal substitution composition `substs_substs` on the code of the fixed formula
`qDupoc = GtmplA 0 ⇜ ![TD, …]`: the code of the one-variable term `TD` is a `ppairT`-tower
with the bound variable `^#0` in the budget slot, and `termSubst (bnum k ∷ 0)` fills it with
`bnum k`, giving exactly `progT (pSearch k ↑gD ↑pD ↑qD)`.
-/

universe u

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open LAct

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ### 1. The two searchers in an arbitrary model, and their transposition -/

/-- `Dupoc` in an arbitrary model (`Dupoc k` is `DupocV k` at `V = ℕ`). -/
noncomputable def DupocV (k : V) : V := pSearch k (⌜GtmplA 0⌝ : V) (pConst 0) (pConst 1)

/-- `Cupod` in an arbitrary model. -/
noncomputable def CupodV (k : V) : V := pSearch k (⌜GtmplA 1⌝ : V) (pConst 1) (pConst 0)

lemma DupocV_nat (k : ℕ) : DupocV (V := ℕ) k = Dupoc k := rfl
lemma CupodV_nat (k : ℕ) : CupodV (V := ℕ) k = Cupod k := rfl

lemma coe_quote_GtmplA (a : ℕ) : ((⌜GtmplA a⌝ : ℕ) : V) = ⌜GtmplA a⌝ := by
  rw [Sentence.quote_def, Sentence.quote_def, Semiformula.coe_quote_eq_quote]

/-- The code-level τ of the template codes, in every model (Σ₁-absoluteness of `relabelTemplate`). -/
lemma relabelTemplate_quote_GtmplA_V (a : ℕ) :
    relabelTemplate 1 0 (⌜GtmplA a⌝ : V) = ⌜GtmplA (swapAct a)⌝ := by
  have h := DefinedFunction.shigmaOne_absolute_func V (relabelTemplate.defined (V := ℕ))
    (relabelTemplate.defined (V := V)) ![1, 0, (⌜GtmplA a⌝ : ℕ)]
  simp [Function.comp_def] at h
  rw [relabelTemplate_quote_GtmplA, coe_quote_GtmplA, coe_quote_GtmplA] at h
  exact h.symm

theorem swapcode_DupocV (k : V) : swapcode (DupocV k) = CupodV k := by
  unfold DupocV CupodV swapcode
  rw [relabel_search, relabel_const, relabel_const, relabelTemplate_quote_GtmplA_V, swapAct_zero]
  simp [relabelAct]

/-! ### 2. The canonical code and the re-valuation codes are `k`-independent -/

lemma cast_innerD : ((innerD : ℕ) : V) = ppair (⌜GtmplA 0⌝ : V) (ppair (pConst 0) (pConst 1)) := by
  rw [innerD_def, cast_ppair, cast_ppair, cast_pConst, cast_pConst, coe_quote_GtmplA]
  push_cast
  rfl

lemma cast_innerC : ((innerC : ℕ) : V) = ppair (⌜GtmplA 1⌝ : V) (ppair (pConst 1) (pConst 0)) := by
  rw [innerC_def, cast_ppair, cast_ppair, cast_pConst, cast_pConst, coe_quote_GtmplA]
  push_cast
  rfl

lemma DupocV_eq_inner (k : V) : DupocV k = ppair 6 (ppair k (innerD : V)) + 1 := by
  rw [cast_innerD]; rfl
lemma CupodV_eq_inner (k : V) : CupodV k = ppair 6 (ppair k (innerC : V)) + 1 := by
  rw [cast_innerC]; rfl

lemma DupocV_lt_CupodV_iff (k : V) : DupocV k < CupodV k ↔ innerD < innerC := by
  rw [DupocV_eq_inner, CupodV_eq_inner, pSearchInner_lt_iff, Nat.cast_lt]

lemma CupodV_lt_DupocV_iff (k : V) : CupodV k < DupocV k ↔ innerC < innerD := by
  rw [DupocV_eq_inner, CupodV_eq_inner, pSearchInner_lt_iff, Nat.cast_lt]

lemma DupocV_eq_cast : DupocV (k : V) = pSearch k ((⌜GtmplA 0⌝ : ℕ) : V) ((pConst 0 : ℕ) : V) ((pConst 1 : ℕ) : V) := by
  unfold DupocV; rw [coe_quote_GtmplA, cast_pConst, cast_pConst]; push_cast; rfl

lemma CupodV_eq_cast : CupodV (k : V) = pSearch k ((⌜GtmplA 1⌝ : ℕ) : V) ((pConst 1 : ℕ) : V) ((pConst 0 : ℕ) : V) := by
  unfold CupodV; rw [coe_quote_GtmplA, cast_pConst, cast_pConst]; push_cast; rfl

/-- **The canonical code of `DupocV k` is a searcher with the (cast) `k`-independent inner triple.** -/
theorem dnum_DupocV (k : V) : dnum (DupocV k) = pSearch k (gD : V) (pD : V) (qD : V) := by
  by_cases h : innerD ≤ innerC
  · simp only [gD, pD, qD, if_pos h]
    rcases Nat.lt_or_eq_of_le h with h' | h'
    · rw [dnum_of_lt (by rw [swapcode_DupocV]; exact (DupocV_lt_CupodV_iff k).mpr h')]
      exact DupocV_eq_cast
    · rw [dnum_of_eq (by rw [swapcode_DupocV, DupocV_eq_inner, CupodV_eq_inner, h'])]
      exact DupocV_eq_cast
  · simp only [gD, pD, qD, if_neg h]
    rw [dnum_of_gt (by rw [swapcode_DupocV]; exact (CupodV_lt_DupocV_iff k).mpr (Nat.lt_of_not_le h)),
      swapcode_DupocV]
    exact CupodV_eq_cast

theorem dU_DupocV (k : V) : dU (DupocV k) = (⌜uD⌝ : V) := by
  unfold dU uD
  rw [swapcode_DupocV]
  by_cases h1 : innerD < innerC
  · rw [if_pos ((DupocV_lt_CupodV_iff k).mpr h1), if_pos h1, quote_cterm_C]
  · rw [if_neg (fun h ↦ h1 ((DupocV_lt_CupodV_iff k).mp h)), if_neg h1]
    by_cases h2 : innerC < innerD
    · rw [if_pos ((CupodV_lt_DupocV_iff k).mpr h2), if_pos h2, quote_cterm_D]
    · rw [if_neg (fun h ↦ h2 ((CupodV_lt_DupocV_iff k).mp h)), if_neg h2, quote_numT]
      simp

theorem dW_DupocV (k : V) : dW (DupocV k) = (⌜wD⌝ : V) := by
  unfold dW wD
  rw [swapcode_DupocV]
  by_cases h1 : innerD < innerC
  · rw [if_pos ((DupocV_lt_CupodV_iff k).mpr h1), if_pos h1, quote_cterm_D]
  · rw [if_neg (fun h ↦ h1 ((DupocV_lt_CupodV_iff k).mp h)), if_neg h1]
    by_cases h2 : innerC < innerD
    · rw [if_pos ((CupodV_lt_DupocV_iff k).mpr h2), if_pos h2, quote_cterm_C]
    · rw [if_neg (fun h ↦ h2 ((CupodV_lt_DupocV_iff k).mp h)), if_neg h2, quote_numT]
      simp

/-! ### 3. The code of the one-variable description term, and its internal substitution -/

section termCodes

/-- The code of `#0` (one bound variable). -/
lemma quote_emb_bvar_zero : (⌜(Rew.emb (#0 : Semiterm ℒₒᵣ Empty 1) : SyntacticSemiterm ℒₒᵣ 1)⌝ : V) = ^#0 := by
  simp [Rew.emb]

/-- The code of a shifted closed term is the code of the term. -/
lemma quote_emb_bShift {L : Language} [L.Encodable] [L.LORDefinable] :
    ∀ t : ClosedSemiterm L 0,
      (⌜(Rew.emb (Rew.bShift t) : SyntacticSemiterm L 1)⌝ : V) = ⌜(Rew.emb t : SyntacticSemiterm L 0)⌝
  | #x => x.elim0
  | &x => x.elim
  | .func f v => by
    rw [Rew.func, Rew.func, Rew.func, Semiterm.quote_func, Semiterm.quote_func]
    congr 1
    unfold SemitermVec.val
    exact matrixToVec_congr (fun i ↦ quote_emb_bShift (v i))

lemma quote_emb_add (s t : Semiterm ℒₒᵣ Empty 1) :
    (⌜(Rew.emb (Semiterm.func Language.ORing.Func.add ![s, t]) : SyntacticSemiterm ℒₒᵣ 1)⌝ : V) =
    (⌜(Rew.emb s : SyntacticSemiterm ℒₒᵣ 1)⌝ : V) ^+ ⌜(Rew.emb t : SyntacticSemiterm ℒₒᵣ 1)⌝ := by
  rw [Rew.func]
  have e : (Semiterm.func Language.ORing.Func.add (⇑Rew.emb ∘ ![s, t]) : SyntacticSemiterm ℒₒᵣ 1) =
      ‘!!(Rew.emb s : SyntacticSemiterm ℒₒᵣ 1) + !!(Rew.emb t : SyntacticSemiterm ℒₒᵣ 1)’ := by
    congr 1; funext i; fin_cases i <;> rfl
  rw [e, Semiterm.quote_def, Semiterm.typed_quote_add]; rfl

lemma quote_emb_mul (s t : Semiterm ℒₒᵣ Empty 1) :
    (⌜(Rew.emb (Semiterm.func Language.ORing.Func.mul ![s, t]) : SyntacticSemiterm ℒₒᵣ 1)⌝ : V) =
    (⌜(Rew.emb s : SyntacticSemiterm ℒₒᵣ 1)⌝ : V) ^* ⌜(Rew.emb t : SyntacticSemiterm ℒₒᵣ 1)⌝ := by
  rw [Rew.func]
  have e : (Semiterm.func Language.ORing.Func.mul (⇑Rew.emb ∘ ![s, t]) : SyntacticSemiterm ℒₒᵣ 1) =
      ‘!!(Rew.emb s : SyntacticSemiterm ℒₒᵣ 1) * !!(Rew.emb t : SyntacticSemiterm ℒₒᵣ 1)’ := by
    congr 1; funext i; fin_cases i <;> rfl
  rw [e, Semiterm.quote_def, Semiterm.typed_quote_mul]; rfl

lemma quote_emb_ppairT1 (s t : Semiterm ℒₒᵣ Empty 1) :
    (⌜(Rew.emb (ppairT1 s t) : SyntacticSemiterm ℒₒᵣ 1)⌝ : V) =
    ppairT (⌜(Rew.emb s : SyntacticSemiterm ℒₒᵣ 1)⌝ : V) ⌜(Rew.emb t : SyntacticSemiterm ℒₒᵣ 1)⌝ := by
  rw [ppairT1, quote_emb_add, quote_emb_mul, quote_emb_add]; rfl

lemma quote_emb_oneTT : (⌜(Rew.emb oneTT : SyntacticSemiterm ℒₒᵣ 0)⌝ : V) = 𝟏 := by
  rw [← Semiterm.empty_quote_def]; exact quote_closed_one

lemma quote_emb_succT1 (t : Semiterm ℒₒᵣ Empty 1) :
    (⌜(Rew.emb (succT1 t) : SyntacticSemiterm ℒₒᵣ 1)⌝ : V) =
    (⌜(Rew.emb t : SyntacticSemiterm ℒₒᵣ 1)⌝ : V) ^+ 𝟏 := by
  rw [succT1, quote_emb_add, quote_emb_bShift, quote_emb_oneTT]

/-- The code of the one-variable searcher term: the `ppairT`-tower with `^#0` in the budget slot. -/
theorem quote_emb_searchT1 (g p q : ℕ) :
    (⌜(Rew.emb (searchT1 g p q) : SyntacticSemiterm ℒₒᵣ 1)⌝ : V) =
    ppairT (bnum 6) (ppairT (^#0) (ppairT (bnum (g : V)) (ppairT (progT (p : V)) (progT (q : V))))) ^+ 𝟏 := by
  rw [searchT1, quote_emb_succT1, quote_emb_ppairT1, quote_emb_ppairT1, quote_emb_bShift, quote_emb_bShift,
    quote_emb_bvar_zero, ← Semiterm.empty_quote_def, ← Semiterm.empty_quote_def, quote_bnumT, quote_ppairTT,
    quote_ppairTT, quote_bnumT, quote_progTT, quote_progTT]
  push_cast
  rfl

/-- `Rew.emb` commutes with `lMap emb` (any bound-variable count). -/
lemma term_emb_lMap_emb_n {n : ℕ} (t : Semiterm ℒₒᵣ Empty n) :
    (Rew.emb (Semiterm.lMap emb t) : SyntacticSemiterm LAct n) = Semiterm.lMap emb (Rew.emb t) := by
  induction t with
  | bvar x => rfl
  | fvar x => exact x.elim
  | func f v ih => simp [Rew.func, Semiterm.lMap_func, Function.comp_def, ih]

/-- The code of `TD` (over `LAct`) is the `ℒₒᵣ` tower. -/
theorem quote_emb_TD :
    (⌜(Rew.emb TD : SyntacticSemiterm LAct 1)⌝ : V) =
    ppairT (bnum 6) (ppairT (^#0) (ppairT (bnum (gD : V)) (ppairT (progT (pD : V)) (progT (qD : V))))) ^+ 𝟏 := by
  unfold TD
  rw [term_emb_lMap_emb_n, quote_term_lMap_emb, quote_emb_searchT1]

/-! #### Internal substitution on the tower -/

lemma isFunc_LAct_add : LAct.IsFunc 2 (addIndex : V) := isFunc_LAct_of_LOR LOR_func_addIndex
lemma isFunc_LAct_mul : LAct.IsFunc 2 (mulIndex : V) := isFunc_LAct_of_LOR LOR_func_mulIndex

lemma qqAdd_uterm_LAct {s t : V} (hs : IsUTerm LAct s) (ht : IsUTerm LAct t) : IsUTerm LAct (s ^+ t) := by
  unfold qqAdd; exact IsUTerm.func isFunc_LAct_add (by simp [hs, ht])
lemma qqMul_uterm_LAct {s t : V} (hs : IsUTerm LAct s) (ht : IsUTerm LAct t) : IsUTerm LAct (s ^* t) := by
  unfold qqMul; exact IsUTerm.func isFunc_LAct_mul (by simp [hs, ht])
lemma ppairT_uterm_LAct {s t : V} (hs : IsUTerm LAct s) (ht : IsUTerm LAct t) : IsUTerm LAct (ppairT s t) :=
  qqAdd_uterm_LAct (qqMul_uterm_LAct (qqAdd_uterm_LAct hs ht) (qqAdd_uterm_LAct hs ht)) ht

lemma termSubst_qqAdd (w : V) {s t : V} (hs : IsUTerm LAct s) (ht : IsUTerm LAct t) :
    termSubst LAct w (s ^+ t) = termSubst LAct w s ^+ termSubst LAct w t := by
  unfold qqAdd
  rw [termSubst_func isFunc_LAct_add (by simp [hs, ht]), termSubstVec_cons₂ hs ht]

lemma termSubst_qqMul (w : V) {s t : V} (hs : IsUTerm LAct s) (ht : IsUTerm LAct t) :
    termSubst LAct w (s ^* t) = termSubst LAct w s ^* termSubst LAct w t := by
  unfold qqMul
  rw [termSubst_func isFunc_LAct_mul (by simp [hs, ht]), termSubstVec_cons₂ hs ht]

lemma termSubst_ppairT (w : V) {s t : V} (hs : IsUTerm LAct s) (ht : IsUTerm LAct t) :
    termSubst LAct w (ppairT s t) = ppairT (termSubst LAct w s) (termSubst LAct w t) := by
  unfold ppairT
  rw [termSubst_qqAdd w (qqMul_uterm_LAct (qqAdd_uterm_LAct hs ht) (qqAdd_uterm_LAct hs ht)) ht,
    termSubst_qqMul w (qqAdd_uterm_LAct hs ht) (qqAdd_uterm_LAct hs ht), termSubst_qqAdd w hs ht]

/-- A closed term code is fixed by every substitution. -/
lemma termSubst_closed (w : V) {t : V} (ht : IsSemiterm LAct 0 t) : termSubst LAct w t = t :=
  termSubst_eq_self ht (fun i hi ↦ absurd hi (by simp))

lemma bvar_zero_uterm : IsUTerm LAct (^#0 : V) := (IsSemiterm.bvar.mpr (by simp : (0 : V) < 1)).isUTerm

/-- **Filling the budget slot**: the substitution of `bnum k` into the tower is the structural
term of the searcher `pSearch k g p q`. -/
theorem termSubst_tower (k g p q : V) :
    termSubst LAct (bnum k ∷ (0 : V))
      (ppairT (bnum 6) (ppairT (^#0) (ppairT (bnum g) (ppairT (progT p) (progT q)))) ^+ 𝟏) =
    progT (pSearch k g p q) := by
  have hb6 : IsUTerm LAct (bnum (6 : V)) := (bnum_semiterm_LAct 0 _).isUTerm
  have hbg : IsUTerm LAct (bnum g) := (bnum_semiterm_LAct 0 _).isUTerm
  have hp : IsUTerm LAct (progT p) := (progT_semiterm_LAct 0 _).isUTerm
  have hq : IsUTerm LAct (progT q) := (progT_semiterm_LAct 0 _).isUTerm
  have h1 : IsUTerm LAct (ppairT (progT p) (progT q)) := ppairT_uterm_LAct hp hq
  have h2 : IsUTerm LAct (ppairT (bnum g) (ppairT (progT p) (progT q))) := ppairT_uterm_LAct hbg h1
  have h3 : IsUTerm LAct (ppairT (^#0) (ppairT (bnum g) (ppairT (progT p) (progT q)))) :=
    ppairT_uterm_LAct bvar_zero_uterm h2
  have h4 : IsUTerm LAct (ppairT (bnum 6) (ppairT (^#0) (ppairT (bnum g) (ppairT (progT p) (progT q))))) :=
    ppairT_uterm_LAct hb6 h3
  have hone : IsUTerm LAct (𝟏 : V) := (IsSemiterm.LAct_of_LOR (one_semiterm (n := 0))).isUTerm
  rw [termSubst_qqAdd _ h4 hone, termSubst_ppairT _ hb6 h3, termSubst_ppairT _ bvar_zero_uterm h2,
    termSubst_ppairT _ hbg h1, termSubst_ppairT _ hp hq, termSubst_bvar, nth_adjoin_zero,
    termSubst_closed _ (bnum_semiterm_LAct 0 _), termSubst_closed _ (bnum_semiterm_LAct 0 _),
    termSubst_closed _ (progT_semiterm_LAct 0 _), termSubst_closed _ (progT_semiterm_LAct 0 _),
    termSubst_closed _ (IsSemiterm.LAct_of_LOR one_semiterm), progT_search]

end termCodes

/-! ### 4. The instance equation on codes, in every model -/

section codes

/-- The code of a closed term cast into one bound variable is the code of the term. -/
lemma quote_emb_cl_V (t : ClosedSemiterm LAct 0) :
    (⌜(Rew.emb (cl t : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝ : V) =
    ⌜(Rew.emb t : SyntacticSemiterm LAct 0)⌝ := by
  induction t with
  | bvar x => exact x.elim0
  | fvar x => exact x.elim
  | func f v ih =>
    show (⌜(Rew.emb (Rew.castLE _ (Semiterm.func f v)) : SyntacticSemiterm LAct 1)⌝ : V) = _
    rw [Rew.func, Rew.func, Rew.func, Semiterm.quote_func, Semiterm.quote_func]
    congr 1
    unfold SemitermVec.val
    exact matrixToVec_congr (fun i ↦ ih i)

lemma semiterm_quote_emb₀ (t : ClosedSemiterm LAct 0) :
    IsSemiterm LAct 0 (⌜(Rew.emb t : SyntacticSemiterm LAct 0)⌝ : V) := by
  rw [Semiterm.quote_def]
  exact (⌜(Rew.emb t : SyntacticSemiterm LAct 0)⌝ : Bootstrapping.Semiterm V LAct 0).isSemiterm_zero

lemma semiterm_quote_emb₁ (t : Semiterm LAct Empty 1) :
    IsSemiterm LAct 1 (⌜(Rew.emb t : SyntacticSemiterm LAct 1)⌝ : V) := by
  rw [Semiterm.quote_def]
  exact (⌜(Rew.emb t : SyntacticSemiterm LAct 1)⌝ : Bootstrapping.Semiterm V LAct 1).isSemiterm_one

/-- The six codes of the substituted terms of `qDupoc`, as an internal vector. -/
noncomputable def qDupocVec : V :=
  (⌜(Rew.emb TD : SyntacticSemiterm LAct 1)⌝ : V) ∷ ⌜(Rew.emb (cl uD : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝ ∷
    ⌜(Rew.emb (cl wD : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝ ∷ ⌜(Rew.emb TD : SyntacticSemiterm LAct 1)⌝ ∷
    ⌜(Rew.emb (cl uD : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝ ∷
    ⌜(Rew.emb (cl wD : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝ ∷ 0

lemma semitermVec_val_qDupoc :
    SemitermVec.val (fun i ↦ (⌜(Rew.emb ((![TD, cl uD, cl wD, TD, cl uD, cl wD] : Fin 6 → Semiterm LAct Empty 1) i) :
      SyntacticSemiterm LAct 1)⌝ : Bootstrapping.Semiterm V LAct 1)) = qDupocVec := by
  have hv : (fun i ↦ (⌜(Rew.emb ((![TD, cl uD, cl wD, TD, cl uD, cl wD] : Fin 6 → Semiterm LAct Empty 1) i) :
      SyntacticSemiterm LAct 1)⌝ : Bootstrapping.Semiterm V LAct 1)) =
      ![⌜(Rew.emb TD : SyntacticSemiterm LAct 1)⌝, ⌜(Rew.emb (cl uD : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝,
        ⌜(Rew.emb (cl wD : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝, ⌜(Rew.emb TD : SyntacticSemiterm LAct 1)⌝,
        ⌜(Rew.emb (cl uD : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝,
        ⌜(Rew.emb (cl wD : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝] := by
    funext i; fin_cases i <;> rfl
  rw [hv]
  simp only [SemitermVec.val_cons, SemitermVec.val_nil]
  rfl

/-- The code of `qDupoc` is the internal substitution of `qDupocVec` into the template code. -/
theorem quote_qDupoc : (⌜qDupoc⌝ : V) = subst LAct qDupocVec (⌜GtmplA 0⌝ : V) := by
  unfold qDupoc
  rw [Sentence.quote_def, Semiformula.coe_subst_eq_subst_coe, Semiformula.quote_def,
    Semiformula.typed_quote_substs, Bootstrapping.Semiformula.val_substs, ← Semiformula.quote_def,
    ← Sentence.quote_def]
  congr 1

lemma qDupocVec_semitermVec : IsSemitermVec LAct 6 1 (qDupocVec : V) := by
  rw [six_eq, qDupocVec]
  exact ((((((IsSemitermVec.nil 1).adjoin (semiterm_quote_emb₁ _)).adjoin (semiterm_quote_emb₁ _)).adjoin
    (semiterm_quote_emb₁ _)).adjoin (semiterm_quote_emb₁ _)).adjoin (semiterm_quote_emb₁ _)).adjoin
    (semiterm_quote_emb₁ _)

lemma bnum_cons_semitermVec (k : V) : IsSemitermVec LAct 1 0 (bnum k ∷ (0 : V)) := by
  rw [show (1 : V) = 0 + 1 by simp]
  exact (IsSemitermVec.nil 0).adjoin (bnum_semiterm_LAct 0 k)

/-- Substituting `bnum k` into the six codes gives the description vector of `DupocV k`. -/
theorem termSubstVec_qDupocVec (k : V) :
    termSubstVec LAct 6 (bnum k ∷ (0 : V)) qDupocVec = descVec (DupocV k) (DupocV k) := by
  have hT : IsUTerm LAct (⌜(Rew.emb TD : SyntacticSemiterm LAct 1)⌝ : V) := (semiterm_quote_emb₁ _).isUTerm
  have hU : IsUTerm LAct (⌜(Rew.emb (cl uD : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝ : V) :=
    (semiterm_quote_emb₁ _).isUTerm
  have hW : IsUTerm LAct (⌜(Rew.emb (cl wD : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝ : V) :=
    (semiterm_quote_emb₁ _).isUTerm
  have e0 : IsUTermVec LAct 0 (0 : V) := IsUTermVec.empty
  have e1 := e0.adjoin hW
  have e2 := e1.adjoin hU
  have e3 := e2.adjoin hT
  have e4 := e3.adjoin hW
  have e5 := e4.adjoin hU
  have sT : termSubst LAct (bnum k ∷ 0) (⌜(Rew.emb TD : SyntacticSemiterm LAct 1)⌝ : V) =
      progT (dnum (DupocV k)) := by
    rw [quote_emb_TD, termSubst_tower, dnum_DupocV]
  have sU : termSubst LAct (bnum k ∷ 0) (⌜(Rew.emb (cl uD : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝ : V) =
      dU (DupocV k) := by
    rw [quote_emb_cl_V, termSubst_closed _ (semiterm_quote_emb₀ _), dU_DupocV, Semiterm.empty_quote_def]
  have sW : termSubst LAct (bnum k ∷ 0) (⌜(Rew.emb (cl wD : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝ : V) =
      dW (DupocV k) := by
    rw [quote_emb_cl_V, termSubst_closed _ (semiterm_quote_emb₀ _), dW_DupocV, Semiterm.empty_quote_def]
  unfold qDupocVec descVec
  rw [six_eq, termSubstVec_cons hT e5, termSubstVec_cons hU e4, termSubstVec_cons hW e3,
    termSubstVec_cons hT e2, termSubstVec_cons hU e1, termSubstVec_cons hW e0, termSubstVec_nil,
    sT, sU, sW]

/-- **The instance equation on codes, in every model**: for every `k : V`, Dupoc's guard code
against itself is the substitution of `bnum k` into the (cast) code of `qDupoc`. -/
theorem guardCode_DupocV_eq (k : V) :
    guardCode (⌜GtmplA 0⌝ : V) (DupocV k) (DupocV k) = subst LAct (bnum k ∷ (0 : V)) (⌜qDupoc⌝ : V) := by
  rw [quote_qDupoc, substs_substs (p := (⌜GtmplA 0⌝ : V)) (l := 6)
    (by simpa using Sentence.quote_isSemiformula (V := V) (GtmplA 0))
    (bnum_cons_semitermVec k) qDupocVec_semitermVec, termSubstVec_qDupocVec]
  rfl

/-- The same, in the vocabulary of the parametric box (`ArithS.InstV`): the guard code is the
`bnum`-instance `instB ⌜qDupoc⌝ k`. -/
theorem guardCode_DupocV_eq_instB (k : V) :
    guardCode (⌜GtmplA 0⌝ : V) (DupocV k) (DupocV k) = instB (⌜qDupoc⌝ : V) k :=
  guardCode_DupocV_eq k

lemma coe_quote_qDupoc : ((⌜qDupoc⌝ : ℕ) : V) = ⌜qDupoc⌝ := by
  rw [Sentence.quote_def, Sentence.quote_def, Semiformula.coe_quote_eq_quote]

end codes

/-- **The instance equation on codes, in every model of `𝗜𝚺₁`, existentially packaged.** -/
theorem exists_dupoc_instance_code_V :
    ∃ cq : ℕ, IsSemiformula LAct 1 cq ∧
      ∀ (V : Type u) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (k : V),
        guardCode (⌜GtmplA 0⌝ : V) (DupocV k) (DupocV k) = subst LAct (bnum k ∷ (0 : V)) (cq : V) :=
  ⟨⌜qDupoc⌝, by simp, fun V _ _ k ↦ by rw [coe_quote_qDupoc]; exact guardCode_DupocV_eq k⟩

end ArithS
