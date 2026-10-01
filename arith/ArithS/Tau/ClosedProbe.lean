import ArithS.Tau.Quine

/-!
# ArithS.Tau.ClosedProbe — a TRUE closed probe of a budget-carrying searcher, FOUND (Phase 3b)

`cupod × cupodTroll`: τ(CupodTroll)'s instance at Cupod is `.search k (.eq C C) D C` — the identity is a
`TAct`-theorem, so the instance DEFECTS for all large `k` — and Cupod's guard is the closed defection probe
"that instance plays D against itself". The probe is TRUE, so Cupod plays D only if the probe is FOUND within
`k`; the probed program carries the budget, so the probe sentence is a different closed sentence at every `k`
and `closed_found` (a fixed sentence) does not apply. The uniform route (the method of `Cells/PositiveCells.lean`
and the `k̂`-chain of `Cells/Common/Khat.lean`):

1. the probe is MOVED into the opp-slots: `sentenceAt (bot I) (bot I) (probeD X) = sentenceAt Y (bot X)
   (.plays .opp .opp D)` for any proper `Y` (`sentenceAt_subst` — a `.plays .opp .opp` template, generic in the
   me-triple), so the guard code is the `binNumeral k`-instance of the FIXED formula `qCT := qT (template
   (.plays .opp .opp D)) ⟨.bot CooperateBot's triple⟩ ⟨TBS g 1, uS g 1, wS g 1⟩`, the bot tower of the
   `.eq`-searcher `pBot (SV g 1 k)` (`guardCode_qT_eq_instB`, `describes_botCB`, `describes_botSV`);
2. `qCT(k)` is TRUE in every model for `k ≥ k̂` in both readings: the bot-wrapped searcher plays its then-branch
   once its own closed guard is found, and a closed `.eq`-identity is found in every model above a standard
   threshold (`found_of_all_V` on `qInst (template (.eq a a)) n`, `tact_qInst_eq_const`);
3. `tact_all_above_of_both` + `found_of_all_above`: the instance at `binNumeral k` of the conditional theorem,
   its antecedent cut away, fits `k` for all large `k`.

The same three steps give any closed probe of a bot-wrapped ENGINE searcher (`SV`); the ite/sim watches over such
a searcher (τ(TFTSim)/τ(OBot)/τ(DBot)/τ(EBot)'s instances at a self-prober) need their own towers — the
`Rows/Dupoc.lean` TODO.
-/

set_option linter.constructorNameAsVariable false

namespace ArithS.Tau

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open LAct
open PD PD.Tau

/-! ### 1. The closed identity on a constant is a theorem in `k`, in the instance's own frame -/

/-- The `.eq (.const a) (.const a)` template holds at EVERY frame, in every model (the codes coincide). -/
theorem eval_template_eq_const_V (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (a : PD.Action) (b : Fin 6 → V) :
    Semiformula.Eval (s := stdReadingV V) b Empty.elim (template (.eq (.const a) (.const a))) := by
  rw [template_eq]
  unfold progGraph
  rw [progAux_of_ne (by simp) (by simp)]
  simp only [Semiformula.eval_substs, Semiformula.eval_ex, LogicalConnective.HomClass.map_and,
    LogicalConnective.Prop.and_eq, eval_closedDesc_V, Semiformula.eval_rel, stdReadingV_rel_eq, Function.comp_def,
    Matrix.cons_val, Semiterm.val_bvar]
  exact ⟨_, _, rfl, rfl, rfl⟩

lemma lMap_swap_template_eq_const (a : PD.Action) :
    Semiformula.lMap swap (template (.eq (.const a) (.const a))) = template (.eq (.const a.swap) (.const a.swap)) := by
  rw [lMap_swap_template _ (by cases a <;> rfl)]; cases a <;> rfl

/-- `TAct ⊢ ∀ k, qInst (template (.eq a a)) n (k)`: the identity in the bot-wrapped searcher's own frame. -/
theorem tact_qInst_eq_const (a : PD.Action) (n : ℕ) :
    TAct ⊢ ∀¹ qInst (template (.eq (.const a) (.const a))) n := by
  refine tact_all_of_both _ (fun M _ _ x ↦ ?_) (fun M _ _ x ↦ ?_)
  · have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    unfold qInst
    rw [eval_qT_iff]
    exact eval_template_eq_const_V M a _
  · have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    unfold qInst
    rw [eval_qT_swap, lMap_swap_template_eq_const, eval_qT_iff]
    exact eval_template_eq_const_V M a.swap _

/-- **A bot-wrapped searcher whose guard is a theorem in its own frame finds it in EVERY model above a standard
threshold** (`found_of_all_V` through the instance equation). -/
theorem botSV_found_V (g : Semisentence LAct 6) (n : ℕ) (hn : n = 0 ∨ n = 1) (hq : TAct ⊢ ∀¹ qInst g n) :
    ∃ kHat : ℕ, ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (k : V), (kHat : V) ≤ k →
      LenBox TAct k (guardCode (⌜g⌝ : V) (pBot (SV g n k)) (pBot (SV g n k))) := by
  obtain ⟨kHat, h⟩ := found_of_all_V hq
  exact ⟨kHat, fun V _ _ k hk ↦ by rw [guardCode_botSV_self_eq_instB_V V g n hn k]; exact h V k hk⟩

/-! ### 2. The fixed formula of the defection probe of τ(CupodTroll)'s instance at Cupod -/

/-- The `.eq`-searcher's template, and its transposition. -/
noncomputable abbrev gEqC : Semisentence LAct 6 := template (.eq (.const .C) (.const .C))
noncomputable abbrev gEqD : Semisentence LAct 6 := template (.eq (.const .D) (.const .D))

/-- The probe "`pBot (SV gEqC 1 k)` plays D against itself", with `.bot CooperateBot` in the (inert) me-slots. -/
noncomputable def qCT : Semisentence LAct 1 :=
  qT (template (.plays .opp .opp .D)) (cl TB0) (cterm Act.C) (cterm Act.D) (TBS gEqC 1) (uS gEqC 1) (wS gEqC 1)

/-- **`qCT` is a conditional `TAct`-theorem**: true in both readings for `k ≥ k̂`. -/
theorem tact_qCT_above : ∃ kHat : ℕ, TAct ⊢ ∀¹ ((leF (↑kHat) #0 : Semisentence LAct 1) 🡒 qCT) := by
  obtain ⟨k₁, h1⟩ := botSV_found_V gEqC 1 (Or.inr rfl) (tact_qInst_eq_const .C 1)
  obtain ⟨k₂, h2⟩ := botSV_found_V gEqD 0 (Or.inl rfl) (tact_qInst_eq_const .D 0)
  refine ⟨k₁ + k₂, tact_all_above_of_both qCT (k₁ + k₂) (fun M _ _ x hx ↦ ?_) (fun M _ _ x hx ↦ ?_)⟩
  · have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    have hx₁ : (k₁ : M) ≤ x := le_trans (by push_cast; exact le_self_add) hx
    unfold qCT
    rw [eval_qT_iff, eval_template_plays_opp_opp_V]
    simp only [Matrix.cons_val]
    rw [desc_botSV _ 1 (Or.inr rfl) x, actCode_D_cast]
    have e := botSV_then_V gEqC 1 x _ _ (h1 M x hx₁)
    rw [Nat.cast_one] at e
    exact ⟨3, e⟩
  · have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    have hx₂ : (k₂ : M) ≤ x := le_trans (by push_cast; exact le_add_self) hx
    unfold qCT
    have ht0 : Semiformula.lMap swap (template (.plays .opp .opp .D)) = template (.plays .opp .opp .C) :=
      lMap_swap_template _ rfl
    rw [eval_qT_swap, ht0, eval_qT_iff, eval_template_plays_opp_opp_V]
    simp only [Matrix.cons_val]
    rw [descT_botSV _ 1 (Or.inr rfl) x, actCode_C_cast, lMap_swap_template_eq_const, Nat.sub_self]
    have e := botSV_then_V gEqD 0 x _ _ (h2 M x hx₂)
    rw [Nat.cast_zero] at e
    exact ⟨3, e⟩

/-! ### 3. The guard at ℕ is the instance of `qCT`, hence found for all large `k` -/

/-- The guard Cupod's instance at CupodTroll consults, in the bit's frame, is the `binNumeral k`-instance of `qCT`:
the probe moved to the opp-slots (`sentenceAt_subst`), the probed searcher described by the bot tower. -/
theorem guardCode_cupod_cupodTroll_eq_instB (k : ℕ) :
    guardCode (templateCode (probeD (inst (tauZoo k) .cupodTroll .cupod)))
      (pBot (instCode k .cupod .cupodTroll)) (pBot (instCode k .cupod .cupodTroll)) = instB (⌜qCT⌝ : ℕ) k := by
  have e1 : guardCode (templateCode (probeD (inst (tauZoo k) .cupodTroll .cupod)))
      (pBot (instCode k .cupod .cupodTroll)) (pBot (instCode k .cupod .cupodTroll)) =
      guardCode (templateCode (.plays .opp .opp .D)) (progCode (PD.Prog.bot (.const .C)))
        (progCode (PD.Prog.bot (inst (tauZoo k) .cupodTroll .cupod))) := by
    rw [← progCode_bot_inst k .cupod .cupodTroll,
      ← quote_sentenceAt (.bot (inst (tauZoo k) .cupod .cupodTroll)) (.bot (inst (tauZoo k) .cupod .cupodTroll))
        (probeD (inst (tauZoo k) .cupodTroll .cupod)) rfl,
      ← quote_sentenceAt (.bot (.const .C)) (.bot (inst (tauZoo k) .cupodTroll .cupod)) (.plays .opp .opp .D) rfl,
      ← sentenceAt_subst (.bot (inst (tauZoo k) .cupod .cupodTroll)) (.bot (inst (tauZoo k) .cupod .cupodTroll))
        (properPlayer_bot _) (properPlayer_bot _) (.plays .opp .opp .D) rfl]
    rfl
  rw [e1, progCode_botConst, progCode_bot_inst, instCode_cupodTroll_cupod,
    templateCode_eq_quote_template (.eq (.const .C) (.const .C)) rfl, ← SV_nat,
    templateCode_eq_quote_template (.plays .opp .opp .D) rfl]
  have hX := describes_botCB.hX ℕ k
  have hU := describes_botCB.hU ℕ k
  have hW := describes_botCB.hW ℕ k
  rw [descVal_botCB] at hX hU hW
  have hX' := (describes_botSV gEqC 1 (Or.inr rfl)).hX ℕ k
  have hU' := (describes_botSV gEqC 1 (Or.inr rfl)).hU ℕ k
  have hW' := (describes_botSV gEqC 1 (Or.inr rfl)).hW ℕ k
  rw [descVal_botSV gEqC 1 (Or.inr rfl)] at hX' hU' hW'
  exact guardCode_qT_eq_instB _ k _ _ _ _ _ _ hX hU hW hX' hU' hW'

/-- **Cupod's defection probe of τ(CupodTroll)'s instance is FOUND for all large `k`** (the `k̂`-chain). -/
theorem cupod_cupodTroll_found :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      LenBox TAct k (guardCode (templateCode (probeD (inst (tauZoo k) .cupodTroll .cupod)))
        (pBot (instCode k .cupod .cupodTroll)) (pBot (instCode k .cupod .cupodTroll))) := by
  obtain ⟨kHat, hq⟩ := tact_qCT_above
  exact found_of_all_above kHat hq _ guardCode_cupod_cupodTroll_eq_instB

end ArithS.Tau
