import ArithS.Cells.JustEngine

/-!
# ArithS.Cells.CupodTrollEngine — CupodTrollBot's two twin cells on the ENGINE's `CupodTrollBot`

`Cells/KhatCells.lean` §5–§8 and `Cells/FlipCells.lean` §7 prove CupodTroll × Cupod `(D, D)` and DIMCID ×
CupodTroll `(D, C)` with CupodTroll as the hand-template twin `CupodTroll7 k` (the hand seven-variable template
`guardTemplateTroll7`, route (c) by hand) wherever a partner's guard has to DESCRIBE it. Since route (c) was made
generic (Phase 2c) the engine's own `progCode (CupodTrollBot k)` stores a constant template —
`templateCodeAt (phiT k) k`, the literal `CupodBot k` of the `.eq` guard described with its budget abstracted
into the slot `#6` (`templateAt_phiT`: `templateAt (phiT k) (some k) = gEq gCu 1` for every `k`) — so it is a
simple member (`SM`), described in every model by its own tower (`SM.describes`, `Cells/JustEngine.lean` §1).
The two cells are re-run on it; the twin-named `outcome_CupodTroll7_vs_CupodBot`, `outcome_DIMCID_vs_CupodTroll7`
are retired in favour of `outcome_CupodTrollBot_vs_CupodBot`, `outcome_DIMCID_vs_CupodTrollBot`. The twin
theorems are untouched.

1. **The stored `.eq` template** `gEq g a := eqAt oppD (closedDescAt (some 0) (SV g a 0))` — "the opponent IS
   `SV g a ·`", the searcher described at the node budget: its constancy (`closedDescAt_SV`), its truth in every
   model (`eval_gEq`: the program the opp-triple describes is `SV g a k`, `k` the budget slot), its transposition
   (`lMap_swap_gEq`).
2. **CupodTroll finds its guard against Cupod in every model above a threshold** (`troll_vs_cupod_V`): the guard
   in the frame `(CupodTroll k, Cupod k)` is the `binNumeral k`-instance of a `TAct`-theorem (the equation is
   true in both readings), so `found_of_all_V` applies — and the same for the transposed troll against Dupoc.
3. **Cupod's guard against the engine CupodTroll** (`qCuT`: "CupodTroll plays D against me") is then true above
   the threshold in both readings, found by the `k̂`-chain (`found_of_all_above`):
   **`khat_CupodBot_vs_CupodTrollBot`** — `CupodBot k` and `CupodTrollBot k` both defect, on the engine's codes.
4. **DIMCID × CupodTrollBot `(D, C)`** (a FLIP): `dimcid_vs_described` on the engine CupodTroll's description,
   and `snd_CupodTrollBot_vs_DIMCID_engine`: **`loeb_DIMCID_vs_CupodTrollBot_engine`**.

Conventions (`Research/Notes/ARITH_TRAPS.md`): every threshold EXISTENTIAL; `simp` never sees a closed quote;
`omega` is never asked about `V`; at `V = ℕ` the V-generic `≤` is bridged by `le_def`.
-/

set_option linter.constructorNameAsVariable false

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open LAct
open PD.Bots
open ArithS.Tau

/-! ### 1. The stored `.eq` template over the engine searcher -/

section eqTemplate

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The generic `.eq` shape of the thirteen-variable template: two descriptions `D₁ D₂` (in the fourteen-variable
frame of `closedDescAt`) of the same program. -/
noncomputable def eqAt (D₁ D₂ : Semisentence LAct 14) : Semisentence LAct 13 :=
  ∃¹ (∃¹ ((D₁ ⇜ ![#1, #2, #3, #4, #5, #6, #7, #8, #9, #10, #11, #12, #13, #14]) ⋏
    ((D₂ ⇜ ![#0, #2, #3, #4, #5, #6, #7, #8, #9, #10, #11, #12, #13, #14]) ⋏
      Semiformula.rel (Language.Eq.eq : LAct.Rel 2) ![#1, #0])))

lemma templateAt_eq_eqAt (k₀ : Option ℕ) (p q : PD.Prog) :
    templateAt (.eq p q) k₀ = eqAt (progGraphAt k₀ p) (closedDescAt k₀ (progCode q)) := by
  rw [templateAt_eq]; rfl

/-- τ on the `.eq` shape: the two descriptions transposed. -/
theorem lMap_swap_eqAt (D₁ D₂ : Semisentence LAct 14) :
    Semiformula.lMap swap (eqAt D₁ D₂) = eqAt (Semiformula.lMap swap D₁) (Semiformula.lMap swap D₂) := by
  unfold eqAt
  simp only [Semiformula.lMap_exs, LogicalConnective.HomClass.map_and, Semiformula.lMap_subst,
    Semiformula.lMap_rel]
  congr 3
  · congr 1; funext i; fin_cases i <;> rfl
  · congr 1
    · congr 1; funext i; fin_cases i <;> rfl
    · congr 1; funext i; fin_cases i <;> rfl

/-- **"The opponent IS the closed watch"** in every model. -/
theorem eval_eqAt_opp_closed (K c : ℕ) (b : Fin 13 → V) :
    Semiformula.Eval (s := stdReadingV V) b Empty.elim (eqAt oppD (closedDescAt (some K) c)) ↔
      revalue (b 4) (b 5) (b 3) = absVal K c (b 6) := by
  unfold eqAt
  simp only [Semiformula.eval_substs, Semiformula.eval_ex, LogicalConnective.HomClass.map_and,
    LogicalConnective.Prop.and_eq, eval_oppD_V, eval_closedDescAt_some_V, Semiformula.eval_rel, stdReadingV_rel_eq,
    Function.comp_def, Matrix.cons_val, Semiterm.val_bvar]
  constructor
  · rintro ⟨x, y, rfl, rfl, h⟩
    exact h
  · intro h
    exact ⟨_, _, rfl, rfl, h⟩

variable (g : Semisentence LAct 6) (a : ℕ) (ha : a = 0 ∨ a = 1)
include ha

/-- The abstraction of the canonical engine searcher is its one-variable tower (`codeTermMetaAbs_canonical_botSV`
without the bot). -/
theorem codeTermMetaAbs_canonical_SV (K : ℕ) :
    codeTermMetaAbs K (canonical (SV (V := ℕ) g a K)) = searchT1 (gS g a) (pS g a) (qS g a) := by
  have hc : canonical (SV (V := ℕ) g a K) = pSearch K (gS g a) (pS g a) (qS g a) := by
    have := canonical_SV (V := ℕ) g a ha K
    simpa only [natCast_nat] using this
  rw [hc, codeTermMetaAbs_search_leaves K _ _ _ (codeTermMetaAbs_pS g a K) (codeTermMetaAbs_qS g a K)]

omit ha in
/-- The fixed closed description of the engine searcher: its tower with the budget slot in place of the budget. -/
noncomputable def DfixSVu : Semisentence LAct 14 :=
  descF #1 (Rew.subst ![#8] (Semiterm.lMap emb (searchT1 (gS g a) (pS g a) (qS g a)))) (cl (uS g a)) (cl (wS g a))

/-- **The stored description of the engine searcher is the same at every budget.** -/
theorem closedDescAt_SV (k : ℕ) : closedDescAt (some k) (SV (V := ℕ) g a k) = DfixSVu g a := by
  unfold closedDescAt DfixSVu
  rw [canonicalSlot_some]
  unfold canonicalAbs
  rw [codeTermMetaAbs_canonical_SV g a ha, revalueUMeta_SV g a ha, revalueWMeta_SV g a ha]

/-- **The abstracted description denotes the searcher at the budget `k`, in every model.** -/
theorem absVal_SV (K : ℕ) (k : V) : absVal K (SV (V := ℕ) g a K) k = SV g a k := by
  rw [absVal_def, codeTermMetaAbs_canonical_SV g a ha, revalueUMeta_SV g a ha, revalueWMeta_SV g a ha, val_searchT1_V,
    ← canonical_SV g a ha, revalue_val_uS_wS_V g a ha]

omit ha in
/-- **The stored template of "the opponent IS `SV g a ·`"**: the searcher described at the node budget.
`templateAt (phiT k) (some k) = gEq gCu 1` (`templateAt_phiT`). -/
noncomputable def gEq : Semisentence LAct 13 := eqAt oppD (closedDescAt (some 0) (SV (V := ℕ) g a 0))

/-- **The truth of the `.eq` template at a frame, in every model**: the program the opp-triple describes IS
`SV g a k`, `k` the value of the budget slot. -/
theorem eval_gEq (b : Fin 13 → V) :
    Semiformula.Eval (s := stdReadingV V) b Empty.elim (gEq g a) ↔ revalue (b 4) (b 5) (b 3) = SV g a (b 6) := by
  unfold gEq
  rw [eval_eqAt_opp_closed, absVal_SV g a ha]

/-- τ on the `.eq` template: the transposed searcher. -/
theorem lMap_swap_gEq : Semiformula.lMap swap (gEq g a) = gEq (Semiformula.lMap swap g) (1 - a) := by
  unfold gEq
  rw [lMap_swap_eqAt, lMap_swap_oppD, lMap_swap_closedDescAt, transposeCode_SV g a ha]

/-- The `.eq` guard "the opponent IS `SV g a k`" in a described frame. -/
theorem eval_qF13_eq {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (me opp : DP) (k : V) :
    Semiformula.Eval (s := stdReadingV V) ![k] Empty.elim (qF13 (gEq g a) me opp) ↔ opp.val k = SV g a k := by
  unfold qF13
  rw [eval_qPlain_iff, eval_gEq g a ha]
  simp only [Matrix.cons_val]
  rfl

end eqTemplate

/-! ### 2. The engine CupodTroll as a simple member -/

section troll

lemma lMap_swap_gP_D : Semiformula.lMap swap (gP .D) = gP .C := lMap_swap_template _ rfl

/-- **CupodTroll as a simple member, in the world `c`**: the searcher on the stored `.eq` template, then-action
`c`. `progCode (CupodTrollBot k) = (sTc .D).code k` (`progCode_CupodTrollBot_sT`); `sTc .C` is its
transposition ("the opponent IS `DupocBot k`" ⇒ C). -/
noncomputable def sTc (c : PD.Action) : SM := ⟨gEq (gP c) (actCode c), actCode c, actCode_zero_or_one c⟩

/-- The transposition of CupodTroll's guard: "the opponent IS `DupocBot k`". -/
def phiTT (k : ℕ) : PD.Formula := .eq .opp (DupocBot k)

/-- **The engine's stored template of CupodTrollBot is the `.eq` template, at every budget.** -/
theorem templateAt_phiT (K : ℕ) : templateAt (phiT K) (some K) = gEq (gP .D) (actCode .D) := by
  have e1 := closedDescAt_SV (gP .D) (actCode .D) (actCode_zero_or_one .D) K
  have e0 := closedDescAt_SV (gP .D) (actCode .D) (actCode_zero_or_one .D) 0
  unfold phiT gEq
  rw [templateAt_eq_eqAt, progGraphAt_opp, progCode_CupodBot_SV]
  exact congrArg (eqAt oppD) (e1.trans e0.symm)

theorem templateAt_phiTT (K : ℕ) : templateAt (phiTT K) (some K) = gEq (gP .C) (actCode .C) := by
  have e1 := closedDescAt_SV (gP .C) (actCode .C) (actCode_zero_or_one .C) K
  have e0 := closedDescAt_SV (gP .C) (actCode .C) (actCode_zero_or_one .C) 0
  unfold phiTT gEq
  rw [templateAt_eq_eqAt, progGraphAt_opp, progCode_DupocBot_SV]
  exact congrArg (eqAt oppD) (e1.trans e0.symm)

theorem isSemiformula7_gEq_D (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] :
    IsSemiformula LAct 7 ((⌜gEq (gP .D) (actCode .D)⌝ : ℕ) : V) := by
  rw [← templateAt_phiT 0]; exact isSemiformula7_cast_templateAt _ 0 rfl V

theorem isSemiformula7_gEq_C (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] :
    IsSemiformula LAct 7 ((⌜gEq (gP .C) (actCode .C)⌝ : ℕ) : V) := by
  rw [← templateAt_phiTT 0]; exact isSemiformula7_cast_templateAt _ 0 rfl V

/-- **The engine's `CupodTrollBot k` is the simple member `sTc .D` at the budget `k`.** -/
theorem progCode_CupodTrollBot_sT (k : ℕ) : progCode (CupodTrollBot k) = (sTc .D).code (V := ℕ) k := by
  rw [progCode_CupodTrollBot]
  unfold SM.code templateCodeAt
  rw [templateAt_phiT]
  simp only [natCast_nat]
  rfl

lemma sTc_tr_code {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (k : V) : (sTc .D).tr.code k = (sTc .C).code k := by
  unfold SM.code
  rw [SM.tr_g, SM.tr_a]
  show pSearch k ((⌜Semiformula.lMap swap (gEq (gP .D) (actCode .D))⌝ : ℕ) : V) _ _ =
    pSearch k ((⌜gEq (gP .C) (actCode .C)⌝ : ℕ) : V) _ _
  rw [lMap_swap_gEq _ _ (actCode_zero_or_one .D), lMap_swap_gP_D]
  rfl

/-- The engine CupodTroll, as a described player. -/
noncomputable def dpT : DP := DP.ofSM (sTc .D)
/-- The engine Cupod, as a described player. -/
noncomputable def dpCu : DP := DP.ofSV (gP .D) (actCode .D) (actCode_zero_or_one .D)

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

lemma dpT_val (k : V) : dpT.val k = (sTc .D).code k := DP.ofSM_val _ k
lemma dpT_tr_val (k : V) : dpT.tr.val k = (sTc .C).code k := by
  rw [dpT, DP.ofSM_tr_val, sTc_tr_code]
lemma dpCu_val (k : V) : dpCu.val k = SV (gP .D) (actCode .D) k := DP.ofSV_val _ _ _ k
lemma dpCu_tr_val (k : V) : dpCu.tr.val k = SV (gP .C) (actCode .C) k := by
  rw [dpCu, DP.ofSV_tr_val, lMap_swap_gP_D]; rfl

end troll

/-! ### 3. CupodTrollBot × CupodBot `(D, D)` -/

section trollCupod

/-- **CupodTroll's guard against Cupod**: "the opponent IS `CupodBot k`", in the frame `(CupodTroll k, Cupod k)`. -/
noncomputable def qTCu : Semisentence LAct 1 := qF13 (gEq (gP .D) (actCode .D)) dpT dpCu

lemma lMap_swap_qTCu : Semiformula.lMap swap qTCu = qF13 (gEq (gP .C) (actCode .C)) dpT.tr dpCu.tr := by
  unfold qTCu
  rw [lMap_swap_qF13, lMap_swap_gEq _ _ (actCode_zero_or_one .D), lMap_swap_gP_D]
  rfl

/-- `TAct ⊢ ∀¹ qTCu`: the equation is true in both readings (the engine's `eqRefl`). -/
theorem tact_qTCu : TAct ⊢ ∀¹ qTCu := by
  refine tact_all_of_both _ (fun M _ _ x ↦ ?_) (fun M _ _ x ↦ ?_)
  · have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    exact (eval_qF13_eq _ _ (actCode_zero_or_one .D) dpT dpCu x).mpr (dpCu_val x)
  · have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    rw [eval_swappedReading, ← stdReadingV_eq_stdReading, lMap_swap_qTCu]
    exact (eval_qF13_eq _ _ (actCode_zero_or_one .C) dpT.tr dpCu.tr x).mpr (dpCu_tr_val x)

/-- The transposed equation is a `TAct`-theorem too. -/
theorem tact_qTCu_swap : TAct ⊢ ∀¹ (Semiformula.lMap swap qTCu) := by
  refine tact_all_of_both _ (fun M _ _ x ↦ ?_) (fun M _ _ x ↦ ?_)
  · have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    rw [lMap_swap_qTCu]
    exact (eval_qF13_eq _ _ (actCode_zero_or_one .C) dpT.tr dpCu.tr x).mpr (dpCu_tr_val x)
  · have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    rw [eval_swappedReading, ← stdReadingV_eq_stdReading, lMap_swap_swap]
    exact (eval_qF13_eq _ _ (actCode_zero_or_one .D) dpT dpCu x).mpr (dpCu_val x)

/-- **The engine CupodTroll finds "the opponent IS `CupodBot k`" against `CupodBot k` in every model, above a
threshold** (found ⇒ D, fuel 2). -/
theorem troll_vs_cupod_V :
    ∃ kHat : ℕ, ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (k : V), (kHat : V) ≤ k →
      EvalGraph 2 (dpT.val k) (dpCu.val k) (dpT.val k) ((actCode .D : ℕ) : V) := by
  obtain ⟨kHat, h⟩ := found_of_all_V tact_qTCu
  refine ⟨kHat, fun V _ _ k hk ↦ ?_⟩
  have hb := h V k hk
  unfold qTCu at hb
  rw [← guardCodeB_qF13 _ (isSemiformula7_gEq_D V)] at hb
  have e := SM.then_V (sTc .D) k (dpT.val k) (dpCu.val k) hb
  rw [← dpT_val] at e
  exact e

/-- The transposed troll finds "the opponent IS `DupocBot k`" against `DupocBot k` (found ⇒ C, fuel 2). -/
theorem trollT_vs_dupoc_V :
    ∃ kHat : ℕ, ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (k : V), (kHat : V) ≤ k →
      EvalGraph 2 (dpT.tr.val k) (dpCu.tr.val k) (dpT.tr.val k) ((actCode .C : ℕ) : V) := by
  obtain ⟨kHat, h⟩ := found_of_all_V tact_qTCu_swap
  refine ⟨kHat, fun V _ _ k hk ↦ ?_⟩
  have hb := h V k hk
  rw [lMap_swap_qTCu, ← guardCodeB_qF13 _ (isSemiformula7_gEq_C V)] at hb
  have e := SM.then_V (sTc .C) k (dpT.tr.val k) (dpCu.tr.val k) hb
  rw [← dpT_tr_val] at e
  exact e

/-- **Cupod's guard against the engine CupodTroll**: "CupodTroll(k) plays D against Cupod(k)". -/
noncomputable def qCuT : Semisentence LAct 1 := qF (gP .D) dpCu dpT

/-- `qCuT` is true in both readings above a standard threshold: CupodTroll's `.eq` guard is found there. -/
theorem tact_qCuT_above : ∃ kHat : ℕ, TAct ⊢ ∀¹ ((leF (↑kHat) #0 : Semisentence LAct 1) 🡒 qCuT) := by
  obtain ⟨k₁, h₁⟩ := troll_vs_cupod_V
  obtain ⟨k₂, h₂⟩ := trollT_vs_dupoc_V
  refine ⟨k₁ + k₂, tact_all_above_of_both _ _ (fun M _ _ x hx ↦ ?_) (fun M _ _ x hx ↦ ?_)⟩
  · have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    exact (eval_qF_plays .D dpCu dpT x).mpr ⟨_, h₁ M x (le_trans (by push_cast; exact le_self_add) hx)⟩
  · have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    rw [eval_swappedReading, ← stdReadingV_eq_stdReading, qCuT, lMap_swap_qF, lMap_swap_gP_D]
    exact (eval_qF_plays .C dpCu.tr dpT.tr x).mpr ⟨_, h₂ M x (le_trans (by push_cast; exact le_add_self) hx)⟩

/-- **Cupod's guard against the engine's `CupodTrollBot k` is found within the budget, for all large `k`** (the
box form, on the engine's own codes). -/
theorem khat_CupodBot_vs_CupodTrollBot_guard :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      LenBox TAct k (guardCode (templateCode phiCu) (progCode (CupodBot k)) (progCode (CupodTrollBot k))) := by
  obtain ⟨kHat, hq⟩ := tact_qCuT_above
  refine found_of_all_above kHat hq _ fun k ↦ ?_
  have e := guardCode_qF (V := ℕ) (gP .D) dpCu dpT k
  rw [dpCu_val, dpT_val, ← progCode_CupodTrollBot_sT] at e
  rw [progCode_CupodBot_SV, templateCode_eq_quote_template phiCu rfl]
  exact e

/-- **CupodBot × CupodTrollBot is `(D, D)` in PA-`S'`**, for all large `k`, unconditional, on the engine's own
codes (the twin form, on `CupodTroll7 k`, is `khat_CupodTrollBot_vs_CupodBot`; the engine's
`outcome_CupodTrollBot_vs_CupodBot`, pad 2): CupodTroll's `.eq` guard against `CupodBot k` is the reflexive
equation, found ⇒ then-branch D (`khat_CupodTrollBot_vs_CupodBot_engine`); Cupod's guard "CupodTroll defects
against me" is then TRUE above `k̂` in every model and found by the `k̂`-chain ⇒ D. -/
theorem khat_CupodBot_vs_CupodTrollBot :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 2 (progCode (CupodBot k)) (progCode (CupodTrollBot k)) (progCode (CupodBot k)) (actCode .D) ∧
      EvalGraph 2 (progCode (CupodTrollBot k)) (progCode (CupodBot k)) (progCode (CupodTrollBot k)) (actCode .D) := by
  obtain ⟨k₁, h₁⟩ := khat_CupodBot_vs_CupodTrollBot_guard
  obtain ⟨k₂, h₂⟩ := khat_CupodTrollBot_vs_CupodBot_engine
  refine ⟨k₁ + k₂, fun k hk ↦ ⟨?_, h₂ k (by omega)⟩⟩
  have hg := h₁ k (by omega)
  rw [progCode_CupodBot] at hg ⊢
  exact search_then phiCu hg (const_play _ _ _ _)

end trollCupod

/-! ### 4. DIMCID × CupodTrollBot `(D, C)` — a FLIP (the engine has `(C, C)`) -/

section dimcidTroll

/-- **DIMCID defects against the engine's `CupodTrollBot k` and FINDS its guard, for all large `k`** (the
self-fulfilling refutation against the described engine CupodTroll; the twin form is
`loeb_DIMCID_vs_CupodTroll7`). -/
theorem loeb_DIMCID_vs_CupodTrollBot_core :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 2 (progCode (DIMCID k)) (progCode (CupodTrollBot k)) (progCode (DIMCID k)) 1 ∧
      LenBox TAct k (guardCode (templateCode phiD) (progCode (DIMCID k)) (progCode (CupodTrollBot k))) := by
  obtain ⟨k₀, h⟩ := dimcid_vs_described (sTc .D).describes
  refine ⟨k₀, fun k hk ↦ ?_⟩
  have := h k hk
  rw [templateCode_eq_quote_template phiD rfl]
  rwa [SM.descVal_TU, ← progCode_CupodTrollBot_sT, ← progCode_DIMCID] at this

/-- **DIMCID × CupodTrollBot is `(D, C)` in PA-`S'`**, for all large `k`, unconditional, on the engine's own codes
(the twin form, on `CupodTroll7 k`, is `loeb_DIMCID_vs_CupodTrollBot`). The engine proves `(C, C)` by an
unreadability census (`llm_outcome_DIMCID_vs_CupodTrollBot`); in `S'` DIMCID's guard against the described
CupodTroll is self-fulfilling and found, so DIMCID defects; CupodTroll's `.eq` guard "DIMCID is `CupodBot k`" is
false, never found by soundness, so CupodTroll cooperates (`snd_CupodTrollBot_vs_DIMCID_engine`). -/
theorem loeb_DIMCID_vs_CupodTrollBot_engine :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 2 (progCode (DIMCID k)) (progCode (CupodTrollBot k)) (progCode (DIMCID k)) (actCode .D) ∧
      EvalGraph 2 (progCode (CupodTrollBot k)) (progCode (DIMCID k)) (progCode (CupodTrollBot k)) (actCode .C) := by
  obtain ⟨k₀, h⟩ := loeb_DIMCID_vs_CupodTrollBot_core
  exact ⟨k₀, fun k hk ↦ ⟨(h k hk).1, snd_CupodTrollBot_vs_DIMCID_engine k⟩⟩


end dimcidTroll

end ArithS
