import ArithS.InstanceV
import ArithS.Det

/-!
# ArithS.Transparency — Dupoc's guard: truth equation and search clause in every model

Critch's "step 0" for Dupoc (roadmap M4, item U7 of `M4_BOUNDED_HBL/BRIEF.md` §3), stated
INSIDE every model `V` of `𝗜𝚺₁`, at every (possibly nonstandard) budget `k : V`, in the objects
the parametric bounded Löb argument uses (`DupocV k`, `instB ⌜qDupoc⌝ k`, `bewB`):

1. **Evaluation of the description terms in `V`.** `val_bnumT_V`/`val_progTT_V` (from
   `ArithS.Det`) extend to the ONE-VARIABLE searcher term of `ArithS.Instance`:
   `val_searchT1_V : (searchT1 g p q).val ![k] = pSearch k g p q` and hence
   `val_TD_V : TD.val ![k] = dnum (DupocV k)` — the free variable of `qDupoc` denotes the
   budget, and the description term denotes the CANONICAL code of `DupocV k` (`dnum_DupocV`'s
   case split is reused, never the constants); `relabel_val_uD_wD_V` reconstructs `DupocV k`
   from the `k`-independent re-valuation terms.
2. **The truth equation** `eval_qDupoc_iff_V : (stdActV V ⊧ qDupoc [k]) ↔ ∃ n, EvalGraph n
   (DupocV k) (DupocV k) (DupocV k) 0` — "Dupoc plays C against itself", `models_guardSentenceA_iff`
   (`ArithS.Template`, `ℕ` only) re-proved in every model along `models_trAt_plays_V`'s idiom.
3. **Transparency (the search clause)** `dupoc_search_V : LenProvableV TAct k (guardCode
   ⌜GtmplA 0⌝ (DupocV k) (DupocV k)) → EvalGraph 2 (DupocV k) (DupocV k) (DupocV k) 0` (fuel 2:
   one search step, one `pConst 0` step), its `instB` reading `dupoc_search_instB_V`
   (unconditional, through `guardCode_DupocV_eq_instB`), and the Löb premise in the box
   vocabulary `dupoc_loeb_premise_V : bewB k ⌜qDupoc⌝ k → (stdActV V ⊧ qDupoc [k])` under
   `ProperV V TAct` (the ONE place the code bound enters — `LenDerivable` has no `fbound`);
   `dupoc_loeb_premise_nat` discharges it at `ℕ` (`properV_nat_TAct`), with the `ℕ` corollaries
   in the vocabulary of `ArithS.Template` (`guardSentenceA`, `Dupoc k`).
4. **The uniform sentence** `dupocPremise : Sentence ℒₒᵣ` — "for all `k`, if the `bnum k`-instance
   of `⌜qDupoc⌝` has a `TAct`-proof of length `≤ k` (code below `fbound k`) then `qDupoc(k)`" —
   with the box written from `instBGraph` + `lenProvableV TAct` (the Δ₁ box, so NO `ProperV`
   hypothesis), the code `⌜qDupoc⌝` as a BINARY numeral, and the consequent INSTANTIATED along
   `inst : LAct →ᵥ ℒₒᵣ` (`c_C ↦ 0`, `c_D ↦ 1`): `pa_proves_dupocPremise : 𝗣𝗔 ⊢ dupocPremise`
   (completeness over item 3) and `tact_proves_dupocPremise : TAct ⊢ lMap emb dupocPremise`.

**Model class.** Every statement about truth is in the `LAct`-structure `stdActV V`
(`ArithS.Det`: the pull-back of the standard `ℒₒᵣ`-structure of `V` along `inst`, i.e. the
`LAct`-structures whose `ℒₒᵣ`-reduct is `V` and which read `c_C` as `0` and `c_D` as `1` —
`stdAct` at `V = ℕ`). This is NOT every model of `TAct`: `TAct` only asserts `c_C ≠ c_D`, and in
a model reading `c_C` as some other element the guard formula speaks about the program
RE-VALUED with that element, for which `DupocV k`'s search clause says nothing. That is why the
uniform sentence is stated over `ℒₒᵣ` with the consequent `lMap inst qDupoc` (the pattern of
`pa_proves_trAt_inst`, `ArithS.Inst`) and transported to `TAct` along `emb`, rather than as a
raw `LAct`-sentence `∀¹ (bewB … 🡒 qDupoc)` proved by the completeness theorem over all
`LAct`-models.
-/

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open LAct

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ### 1. The one-variable description term, evaluated at a free budget -/

section terms

lemma ppairT1_eq (s t : Semiterm ℒₒᵣ Empty 1) :
    ppairT1 s t = ‘(!!s + !!t) * (!!s + !!t) + !!t’ := rfl

lemma succT1_eq (t : Semiterm ℒₒᵣ Empty 1) : succT1 t = ‘!!t + !!(Rew.bShift oneTT)’ := rfl

omit [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
lemma val_ppairT1_V (s t : Semiterm ℒₒᵣ Empty 1) (b : Fin 1 → V) :
    (ppairT1 s t).val (s := standardModel V) b Empty.elim =
      ppair (s.val (s := standardModel V) b Empty.elim) (t.val (s := standardModel V) b Empty.elim) := by
  simp [ppairT1_eq, ppair]

omit [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
lemma val_bShift₁_V (t : ClosedSemiterm ℒₒᵣ 0) (b : Fin 1 → V) :
    (Rew.bShift t).val (s := standardModel V) b Empty.elim = t.val (s := standardModel V) ![] Empty.elim := by
  rw [Semiterm.val_bShift', Subsingleton.elim (fun x : Fin 0 ↦ b x.succ) ![]]

omit [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
lemma val_oneTT_V : oneTT.val (s := standardModel V) ![] Empty.elim = 1 := by
  simp [oneTT]

lemma val_succT1_V (t : Semiterm ℒₒᵣ Empty 1) (b : Fin 1 → V) :
    (succT1 t).val (s := standardModel V) b Empty.elim = t.val (s := standardModel V) b Empty.elim + 1 := by
  simp [succT1_eq, val_bShift₁_V, val_oneTT_V]

/-- **The one-variable searcher term denotes the searcher at the free budget**, in every model. -/
theorem val_searchT1_V (g p q : ℕ) (k : V) :
    (searchT1 g p q).val (s := standardModel V) ![k] Empty.elim = pSearch k (g : V) (p : V) (q : V) := by
  rw [searchT1, val_succT1_V, val_ppairT1_V, val_ppairT1_V, val_bShift₁_V, val_bShift₁_V, val_bnumT_V,
    val_ppairTT_V, val_ppairTT_V, val_bnumT_V, val_progTT_V, val_progTT_V]
  unfold pSearch
  push_cast
  rfl

/-- **`TD` at the budget `k` denotes the canonical code of `DupocV k`** (in `stdActV V`). -/
theorem val_TD_V (k : V) : TD.val (s := stdActV V) ![k] Empty.elim = dnum (DupocV k) := by
  unfold TD
  rw [Semiterm.val_lMap, stdActV_lMap_emb, val_searchT1_V, dnum_DupocV]

/-- The `k`-independent re-valuation terms reconstruct `DupocV k` from its canonical code. -/
theorem relabel_val_uD_wD_V (k : V) :
    relabel (uD.val (s := stdActV V) ![] Empty.elim) (wD.val (s := stdActV V) ![] Empty.elim)
      (dnum (DupocV k)) = DupocV k := by
  unfold uD wD
  by_cases h1 : innerD < innerC
  · rw [if_pos h1, if_pos h1, val_cterm_C_V, val_cterm_D_V,
      dnum_of_lt (by rw [swapcode_DupocV]; exact (DupocV_lt_CupodV_iff k).mpr h1), relabel_zero_one]
  · rw [if_neg h1, if_neg h1]
    by_cases h2 : innerC < innerD
    · rw [if_pos h2, if_pos h2, val_cterm_D_V, val_cterm_C_V,
        dnum_of_gt (by rw [swapcode_DupocV]; exact (CupodV_lt_DupocV_iff k).mpr h2)]
      exact swapcode_swapcode _
    · have h' : innerD = innerC := le_antisymm (not_lt.mp h2) (not_lt.mp h1)
      rw [if_neg h2, if_neg h2, val_numT_V, val_numT_V, Nat.cast_zero, Nat.cast_one,
        dnum_of_eq (by rw [swapcode_DupocV, DupocV_eq_inner, CupodV_eq_inner, h']), relabel_zero_one]

lemma val_actT6_V (a : ℕ) (b : Fin 6 → V) : (actT6 a).val (s := stdActV V) b Empty.elim = (a : V) := by
  unfold actT6
  rw [Semiterm.val_castLE, Subsingleton.elim (fun x : Fin 0 ↦ b (x.castLE (Nat.zero_le 6))) ![]]
  exact val_actT_V a

end terms

/-! ### 2. The truth equation in every model -/

/-- **The truth equation of Dupoc's guard in every model**: `qDupoc` holds at the budget `k` in
`stdActV V` iff `DupocV k` plays `C` against itself (at some fuel). -/
theorem eval_qDupoc_iff_V (k : V) :
    Semiformula.Eval (s := stdActV V) ![k] Empty.elim qDupoc ↔
      ∃ n, EvalGraph n (DupocV k) (DupocV k) (DupocV k) 0 := by
  unfold qDupoc GtmplA Gtmpl
  rw [Semiformula.eval_substs, Semiformula.eval_substs, Semiformula.eval_lMap, stdActV_lMap_emb]
  have h0 : (Semiterm.val (s := stdActV V) ![k] Empty.elim ∘ ![TD, cl uD, cl wD, TD, cl uD, cl wD]) =
      ![dnum (DupocV k), uD.val (s := stdActV V) ![] Empty.elim, wD.val (s := stdActV V) ![] Empty.elim,
        dnum (DupocV k), uD.val (s := stdActV V) ![] Empty.elim, wD.val (s := stdActV V) ![] Empty.elim] := by
    funext i; fin_cases i <;> simp [val_TD_V, val_cl_V]
  rw [h0]
  have h1 : (Semiterm.val (s := stdActV V)
      ![dnum (DupocV k), uD.val (s := stdActV V) ![] Empty.elim, wD.val (s := stdActV V) ![] Empty.elim,
        dnum (DupocV k), uD.val (s := stdActV V) ![] Empty.elim, wD.val (s := stdActV V) ![] Empty.elim]
      Empty.elim ∘ ![#0, #1, #2, #3, #4, #5, actT6 0]) =
      ![dnum (DupocV k), uD.val (s := stdActV V) ![] Empty.elim, wD.val (s := stdActV V) ![] Empty.elim,
        dnum (DupocV k), uD.val (s := stdActV V) ![] Empty.elim, wD.val (s := stdActV V) ![] Empty.elim, 0] := by
    funext i; fin_cases i <;> simp [val_actT6_V]
  rw [h1]
  refine (eval_gtmpl (V := V) _).trans ?_
  simp [relabel_val_uD_wD_V]

/-! ### 3. Transparency: the search clause -/

/-- **Dupoc's search clause in every model** (fuel `2`: the search step and the `pConst 0` step):
if the guard is provable within the budget then `DupocV k` cooperates with itself. -/
theorem dupoc_search_V (k : V) :
    LenProvableV TAct k (guardCode (⌜GtmplA 0⌝ : V) (DupocV k) (DupocV k)) →
      EvalGraph 2 (DupocV k) (DupocV k) (DupocV k) 0 := by
  intro h
  rw [show (2 : V) = 1 + 1 from one_add_one_eq_two.symm]
  show EvalGraph (1 + 1) (DupocV k) (DupocV k) (pSearch k (⌜GtmplA 0⌝ : V) (pConst 0) (pConst 1)) 0
  rw [EvalGraph.search_iff]
  left
  refine ⟨h, ?_⟩
  rw [show (1 : V) = 0 + 1 by simp, EvalGraph.const_iff]

/-- The search clause in the `instB` vocabulary, with the consequent as the truth of `qDupoc`:
UNCONDITIONAL (the Δ₁ box `LenProvableV` carries its own code bound). -/
theorem dupoc_search_instB_V (k : V) :
    LenProvableV TAct k (instB (⌜qDupoc⌝ : V) k) →
      Semiformula.Eval (s := stdActV V) ![k] Empty.elim qDupoc := by
  intro h
  rw [← guardCode_DupocV_eq_instB] at h
  exact (eval_qDupoc_iff_V k).mpr ⟨2, dupoc_search_V k h⟩

/-- **The Löb premise in the box vocabulary**: `□_k qDupoc(k̂) → qDupoc(k)` in `stdActV V`, under
properness inside `V` (`ProperV V TAct` turns `LenDerivable` into `LenProvableV`). -/
theorem dupoc_loeb_premise_V (hP : ProperV V TAct) (k : V) :
    bewB k (⌜qDupoc⌝ : V) k → Semiformula.Eval (s := stdActV V) ![k] Empty.elim qDupoc := by
  rintro ⟨d, hd, hk⟩
  exact dupoc_search_instB_V k ⟨d, hP k d _ hd hk, hd, hk⟩

/-! #### The `ℕ` instance -/

/-- The Löb premise at `V = ℕ`, unconditional (`properV_nat_TAct`). -/
theorem dupoc_loeb_premise_nat (k : ℕ) :
    bewB k (⌜qDupoc⌝ : ℕ) k → Semiformula.Eval (s := stdAct) ![k] Empty.elim qDupoc := by
  have := dupoc_loeb_premise_V (V := ℕ) properV_nat_TAct k
  rwa [show stdActV ℕ = stdAct from lMap_inst_std] at this

/-- The same in the vocabulary of `ArithS.Template`: the box of the `k`-instance yields the truth
of Dupoc's guard SENTENCE against itself. -/
theorem dupoc_loeb_premise_guardSentence (k : ℕ) :
    bewB k (⌜qDupoc⌝ : ℕ) k → ℕ↓[LAct] ⊧ guardSentenceA 0 (Dupoc k) (Dupoc k) := by
  intro h
  rw [guardSentenceA_Dupoc_eq, models_iff]
  unfold Semiformula.Realize
  rw [Semiformula.eval_substs]
  have e : (Semiterm.val (s := stdAct) ![] Empty.elim ∘ ![Semiterm.lMap emb (bnumT k)]) = ![k] := by
    funext i; fin_cases i
    show (Semiterm.lMap emb (bnumT k)).val (s := stdAct) ![] Empty.elim = k
    rw [Semiterm.val_lMap, stdAct_lMap_emb]
    exact val_bnumT k
  rw [e]
  exact dupoc_loeb_premise_nat k h

/-- And as an evaluator run: `Dupoc k` cooperates with itself. -/
theorem dupoc_loeb_premise_evalGraph (k : ℕ) :
    bewB k (⌜qDupoc⌝ : ℕ) k → ∃ n, EvalGraph n (Dupoc k) (Dupoc k) (Dupoc k) 0 := fun h ↦
  (models_guardSentenceA_iff 0 (Dupoc k) (Dupoc k)).mp (dupoc_loeb_premise_guardSentence k h)

/-! ### 4. The uniform sentence: `𝗣𝗔 ⊢ ∀ k, □_k qDupoc(k̂) → qDupoc(k)` (instantiated), and in `TAct` -/

section sentence

/-- A closed `ℒₒᵣ`-term cast into `n` bound variables. -/
noncomputable def clO {n : ℕ} (t : ClosedSemiterm ℒₒᵣ 0) : Semiterm ℒₒᵣ Empty n :=
  Rew.castLE (Nat.zero_le n) t

omit [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
lemma val_clO_V {n : ℕ} (t : ClosedSemiterm ℒₒᵣ 0) (b : Fin n → V) :
    (clO t : Semiterm ℒₒᵣ Empty n).val (s := standardModel V) b Empty.elim =
      t.val (s := standardModel V) ![] Empty.elim := by
  unfold clO
  rw [Semiterm.val_castLE, Subsingleton.elim (fun x : Fin 0 ↦ b (x.castLE (Nat.zero_le n))) ![]]

/-- The BINARY numeral of the code of `qDupoc` (never evaluated; its value is `⌜qDupoc⌝`). -/
noncomputable def cqT : ClosedSemiterm ℒₒᵣ 0 := bnumT (⌜qDupoc⌝ : ℕ)

lemma val_clO_cqT_V {n : ℕ} (b : Fin n → V) :
    (clO cqT : Semiterm ℒₒᵣ Empty n).val (s := standardModel V) b Empty.elim = (⌜qDupoc⌝ : V) := by
  rw [val_clO_V, cqT, val_bnumT_V, coe_quote_qDupoc]

/-- `qDupoc` instantiated along `inst` (`c_C ↦ 0`, `c_D ↦ 1`): an `ℒₒᵣ`-formula in the budget. -/
noncomputable def qDupocOR : Semisentence ℒₒᵣ 1 := Semiformula.lMap inst qDupoc

omit [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
lemma eval_qDupocOR_V (b : Fin 1 → V) :
    Semiformula.Eval (s := standardModel V) b Empty.elim qDupocOR ↔
      Semiformula.Eval (s := stdActV V) b Empty.elim qDupoc := by
  unfold qDupocOR
  rw [Semiformula.eval_lMap]

/-- **The uniform Löb premise as ONE `ℒₒᵣ`-sentence**: "for all `k`, if the `bnum k`-instance of
`⌜qDupoc⌝` (the guard code of `DupocV k`) has a `TAct`-proof of length `≤ k` with code below
`fbound k` — the Δ₁ box `lenProvableV`, so no properness hypothesis — then `qDupoc(k)`
(instantiated)". -/
noncomputable def dupocPremise : ArithmeticSentence :=
  “∀ k g, !instBGraph g !!(clO cqT) k → !(lenProvableV TAct).sigma k g → !qDupocOR k”

lemma models_dupocPremise :
    V↓[ℒₒᵣ] ⊧ dupocPremise ↔
    ∀ k : V, LenProvableV TAct k (instB (⌜qDupoc⌝ : V) k) →
      Semiformula.Eval (s := stdActV V) ![k] Empty.elim qDupoc := by
  simp [dupocPremise, models_iff, instB.defined.iff, val_clO_cqT_V, eval_qDupocOR_V,
    Semiformula.eval_substs]

/-- **`𝗜𝚺₁` proves the uniform Löb premise** (completeness over `dupoc_search_instB_V`). -/
theorem isigma1_proves_dupocPremise : 𝗜𝚺₁ ⊢ dupocPremise :=
  complete 𝗜𝚺₁ _ fun (_ : Type) _ _ ↦ models_dupocPremise.mpr fun k h ↦ dupoc_search_instB_V k h

/-- **`𝗣𝗔` proves the uniform Löb premise.** -/
theorem pa_proves_dupocPremise : 𝗣𝗔 ⊢ dupocPremise :=
  complete 𝗣𝗔 _ fun (V : Type) _ _ ↦
    haveI : V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    models_dupocPremise.mpr fun k h ↦ dupoc_search_instB_V k h

/-- **`TAct` proves the uniform Löb premise** (the `ℒₒᵣ`-sentence embedded along `emb`). -/
theorem tact_proves_dupocPremise : TAct ⊢ Semiformula.lMap LAct.emb dupocPremise := by
  refine Theory.Proof.complete fun (s : Struc.{0} LAct) hs ↦ ?_
  have hPA : s ⊧* Theory.lMap LAct.emb 𝗣𝗔 :=
    Semantics.ModelsSet.of_subset hs (fun x hx ↦ Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ hx))
  exact lMap_models_lMap (Theory.Proof.sound pa_proves_dupocPremise) hPA

end sentence

end ArithS

