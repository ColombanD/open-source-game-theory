import ArithS.Tau.Stored
import ArithS.Tau.ClosedProbe

/-!
# ArithS.Tau.ClosedWatch — guards over a closed budget-carrying watch, FOUND (Phase 3e)

The slots Phase 3b could not state (`Rows/CIMCIC.lean`, `Rows/DIMCID.lean`, `Rows/Dupoc.lean`): a self-prober's
instance at a hypothesis whose instance seeing it carries the budget — τ(TFTSim)'s, τ(DBot)'s, τ(CupodTroll)'s
instances at CIMCIC/DIMCID/Dupoc. Under route (c) made generic the instance is the bot-wrapped simple searcher
`pBot (pSearch k ⌜g⌝ …)` on the CONSTANT stored template `g` (`Tau/Stored.lean`), and the watch it names is
described by its own `k̂`-tower: the three families of `Cells/Common/Khat.lean` apply.

* §1 the stored template as a member-blind formula (`isSemiformula7_cast_templateAt`), the compiled searcher as
  `SV` in every model, the transposed `Describes` of the towers;
* §2 **DIMCID's self-fulfilling family on a closed watch** (`dimcid_closed_found`): the guard "if I cooperate
  with the watch, it defects against me" is found for all large `k` in the PROBE frame `(pBot I, pBot X)` —
  a box of it makes `I` defect against `X`, refuting the antecedent; `Described.lean`'s `qDiI` with the watch's
  tower in place of the constant's. Parametric in the watch's `DescribesAbove` towers and the value of its
  abstracted description (`absVal`), so one proof serves every watch shape;
* §3 **the POS-above chain** (`plain_found_above`, `tact_qCi_above`, `tact_qPr_above`): CIMCIC's "if I cooperate
  with the watch, it cooperates with me" and Dupoc's "the watch cooperates with itself" are conditional
  `TAct`-theorems once the watch's play above a standard threshold is known in both readings;
* §4 the plays of a `W1` watch in every model from its member's found guard, and the found guards of the
  self-probers' instances at the constants (`tact_qInst_implC`, the closed probe `tact_qInst_prC`);
* §5 the bits: `dimcid × {tftSim, dbot, cupodTroll}` (D), `cimcic × tftSim` (C), `dupoc/maxconfidence/minconfidence
  × tftSim` (C). τ(OBot)'s two-watch cascade is `Tau/ClosedWatch2.lean`.
-/

set_option linter.constructorNameAsVariable false

namespace ArithS.Tau

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open LAct
open PD PD.Tau

/-! ### 1. Helpers -/

section helpers

/-- The stored template of a `noSelfIdx` guard at any node budget is a seven-variable formula, in every model. -/
theorem isSemiformula7_cast_templateAt (φ : PD.Formula) (K : ℕ) (hns : noSelfIdxF φ = true) (V : Type) [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] : IsSemiformula LAct 7 ((⌜templateAt φ (some K)⌝ : ℕ) : V) := by
  rw [templateAt_eq_castLE₇ _ φ hns, quote_castLE₇, coe_quote_sentence₇]
  exact isSemiformula_quote₇ _

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The simple member of a compiled searcher IS the generic engine searcher `SV`, in every model. -/
theorem SM.code_ofSearch_eq_SV (φ : PD.Formula) (hns : noSelfIdxF φ = true) (a : PD.Action) (k : V) :
    (SM.ofSearch φ a).code k = SV (template φ) (actCode a) k := by
  unfold SM.code SV
  rw [SM.ofSearch_g, SM.ofSearch_a]
  change pSearch k ((templateCode φ : ℕ) : V) _ _ = _
  rw [templateCode_eq_quote_template φ hns, coe_quote_sentence₆]

theorem SM.tr_code_ofSearch_eq_SV (φ : PD.Formula) (hns : noSelfIdxF φ = true) (hfr : fragF φ = true) (a : PD.Action) (k : V) :
    (SM.ofSearch φ a).tr.code k = SV (template φ.transpose) (1 - actCode a) k := by
  rw [← SM.transposeCode_code, SM.code_ofSearch_eq_SV φ hns, transposeCode_SV _ _ (actCode_zero_or_one a),
    lMap_swap_template φ hfr]

/-- The bot-wrapped compiled searcher plays its then-action in any frame where its (six-variable) guard is found. -/
theorem SM.bot_then_ofSearch (φ : PD.Formula) (hns : noSelfIdxF φ = true) (a : PD.Action) (k me opp : V)
    (h : LenBox TAct k (guardCode (⌜template φ⌝ : V) me opp)) :
    EvalGraph 3 me opp (pBot ((SM.ofSearch φ a).code k)) ((actCode a : ℕ) : V) := by
  rw [SM.code_ofSearch_eq_SV φ hns]
  exact botSV_then_V (template φ) (actCode a) k me opp h

/-- The transposed description of a bot-wrapped member. -/
theorem SM.describesBotT (s : SM) :
    Describes (Semiterm.lMap swap s.TB) (Semiterm.lMap swap s.uT) (Semiterm.lMap swap s.wT) where
  hX := fun V _ _ k ↦ by
    rw [descVal_TB_T, SM.lMap_swap_TB, canonical_pBot, SM.canonical_tr_code, ← SM.canonical_code, ← canonical_pBot]
    exact SM.hX_TB s k
  hU := fun V _ _ k ↦ by rw [descVal_TB_T, revalueU_pBot, SM.revalueU_tr_code]
  hW := fun V _ _ k ↦ by rw [descVal_TB_T, revalueW_pBot, SM.revalueW_tr_code]
  hT := fun V _ _ k ↦ by
    rw [term_lMap_swap_swap, term_lMap_swap_swap, term_lMap_swap_swap, descVal_TB, descVal_TB_T, transposeCode_pBot,
      ← SM.transposeCode_code, transposeCode_transposeCode]

/-- The transposed description of a bot-wrapped watch, above the threshold. -/
theorem W1.describesBotT (W : W1) :
    DescribesAbove W1.K (Semiterm.lMap swap W.TX) (Semiterm.lMap swap W.uT) (Semiterm.lMap swap W.wT) where
  hX := fun V _ _ k hk ↦ by
    rw [W1.descVal_TX_T W hk, W1.lMap_swap_TX, canonical_pBot, W1.canonical_tr_code W hk, ← W1.canonical_code W hk,
      ← canonical_pBot]
    exact W1.hX_TX W hk
  hU := fun V _ _ k hk ↦ by rw [W1.descVal_TX_T W hk, revalueU_pBot, W1.revalueU_tr_code W hk]
  hW := fun V _ _ k hk ↦ by rw [W1.descVal_TX_T W hk, revalueW_pBot, W1.revalueW_tr_code W hk]
  hT := fun V _ _ k hk ↦ by
    rw [term_lMap_swap_swap, term_lMap_swap_swap, term_lMap_swap_swap, W1.descVal_TX W hk, W1.descVal_TX_T W hk,
      transposeCode_pBot, ← W1.transposeCode_code, transposeCode_transposeCode]

section svT

variable (g : Semisentence LAct 6) (a : ℕ) (ha : a = 0 ∨ a = 1)
include ha

theorem revalueU_SVT (k : V) :
    revalueU (SV (Semiformula.lMap swap g) (1 - a) k) = (⌜Semiterm.lMap swap (uS g a)⌝ : V) := by
  have e : transposeCode (SV (Semiformula.lMap swap g) (1 - a) k) = SV g a k := by
    rw [← transposeCode_SV g a ha, transposeCode_transposeCode]
  unfold revalueU uS
  rw [e]
  by_cases h1 : innerS g a < innerS (Semiformula.lMap swap g) (1 - a)
  · rw [if_neg (lt_asymm ((SV_lt_SVT_iff g a ha k).mpr h1)), if_pos ((SV_lt_SVT_iff g a ha k).mpr h1), if_pos h1,
      lMap_swap_cterm_C, quote_cterm_D]
  · rw [if_neg h1]
    by_cases h2 : innerS (Semiformula.lMap swap g) (1 - a) < innerS g a
    · rw [if_pos ((SVT_lt_SV_iff g a ha k).mpr h2), if_pos h2, lMap_swap_cterm_D, quote_cterm_C]
    · rw [if_neg (fun h ↦ h2 ((SVT_lt_SV_iff g a ha k).mp h)), if_neg (fun h ↦ h1 ((SV_lt_SVT_iff g a ha k).mp h)),
        if_neg h2, lMap_swap_numT, quote_numT]
      simp

theorem revalueW_SVT (k : V) :
    revalueW (SV (Semiformula.lMap swap g) (1 - a) k) = (⌜Semiterm.lMap swap (wS g a)⌝ : V) := by
  have e : transposeCode (SV (Semiformula.lMap swap g) (1 - a) k) = SV g a k := by
    rw [← transposeCode_SV g a ha, transposeCode_transposeCode]
  unfold revalueW wS
  rw [e]
  by_cases h1 : innerS g a < innerS (Semiformula.lMap swap g) (1 - a)
  · rw [if_neg (lt_asymm ((SV_lt_SVT_iff g a ha k).mpr h1)), if_pos ((SV_lt_SVT_iff g a ha k).mpr h1), if_pos h1,
      lMap_swap_cterm_D, quote_cterm_C]
  · rw [if_neg h1]
    by_cases h2 : innerS (Semiformula.lMap swap g) (1 - a) < innerS g a
    · rw [if_pos ((SVT_lt_SV_iff g a ha k).mpr h2), if_pos h2, lMap_swap_cterm_C, quote_cterm_D]
    · rw [if_neg (fun h ↦ h2 ((SVT_lt_SV_iff g a ha k).mp h)), if_neg (fun h ↦ h1 ((SV_lt_SVT_iff g a ha k).mp h)),
        if_neg h2, lMap_swap_numT, quote_numT]
      simp

end svT

/-- The transposed description of the bot-wrapped engine searcher. -/
theorem describes_botSVT (g : Semisentence LAct 6) (a : ℕ) (ha : a = 0 ∨ a = 1) :
    Describes (Semiterm.lMap swap (TBS g a)) (Semiterm.lMap swap (uS g a)) (Semiterm.lMap swap (wS g a)) where
  hX := fun V _ _ k ↦ by
    rw [descVal_botSV_T g a ha, lMap_swap_TBS]
    have hc : canonical (pBot (SV (Semiformula.lMap swap g) (1 - a) k)) = canonical (pBot (SV g a k)) := by
      rw [← transposeCode_SV g a ha, ← transposeCode_pBot, canonical_transposeCode]
    rw [hc]; exact termSubst_TBS g a ha k
  hU := fun V _ _ k ↦ by rw [descVal_botSV_T g a ha, revalueU_pBot, revalueU_SVT g a ha]
  hW := fun V _ _ k ↦ by rw [descVal_botSV_T g a ha, revalueW_pBot, revalueW_SVT g a ha]
  hT := fun V _ _ k ↦ by
    rw [term_lMap_swap_swap, term_lMap_swap_swap, term_lMap_swap_swap, descVal_botSV g a ha, descVal_botSV_T g a ha,
      transposeCode_pBot, ← transposeCode_SV g a ha, transposeCode_transposeCode]

lemma swapAction_zero' : swapAction (0 : ℕ) = 1 := by simp [revalueAction]
lemma swapAction_one' : swapAction (1 : ℕ) = 0 := by simp [revalueAction]

end helpers

/-! ### 2. DIMCID's self-fulfilling family on a closed watch -/

section dimcid

/-- DIMCID's guard over the closed program `c` (described at the node budget `K`): "if I cooperate with it, it
defects against me". -/
noncomputable def gDi (K c : ℕ) : Semisentence LAct 13 :=
  plAt selfD (closedDescAt (some K) c) 0 🡒 plAt (closedDescAt (some K) c) selfD 1

/-- DIMCID's instance as a simple member: the guard, then-action `D`. -/
noncomputable def sDi (K c : ℕ) : SM := ⟨gDi K c, 1, Or.inr rfl⟩

lemma sDi_g (K c : ℕ) : (sDi K c).g = gDi K c := rfl
lemma sDi_tr_g (K c : ℕ) : (sDi K c).tr.g = Semiformula.lMap swap (gDi K c) := rfl
lemma sDi_a (K c : ℕ) : (sDi K c).a = 1 := rfl
lemma sDi_tr_a (K c : ℕ) : (sDi K c).tr.a = 0 := rfl

/-- The family's formula: the guard in the PROBE frame `(pBot I, X)` — the instance's own bot tower on the me-side,
the watch's tower on the opp-side. -/
noncomputable def qDi (K c : ℕ) (TX : Semiterm LAct Empty 1) (uX wX : ClosedSemiterm LAct 0) : Semisentence LAct 1 :=
  qPlain (gDi K c) (sDi K c).TB (sDi K c).uT (sDi K c).wT TX uX wX

lemma lMap_swap_gDi (K c : ℕ) : Semiformula.lMap swap (gDi K c) =
    plAt selfD (closedDescAt (some K) (transposeCode c)) 1 🡒 plAt (closedDescAt (some K) (transposeCode c)) selfD 0 := by
  unfold gDi
  rw [LogicalConnective.HomClass.map_imply, lMap_swap_plAt, lMap_swap_plAt, lMap_swap_selfD, lMap_swap_closedDescAt,
    swapAction_zero', swapAction_one']

/-- `templateAt (dimG X) (some K)` IS `gDi K (progCode (.bot X))` for a closed, pronoun-free `X`. -/
theorem templateAt_dimG_eq (K : ℕ) (X : PD.Prog) (hns : noSelfIdxP (.bot X) = true) :
    templateAt (.impl (.plays .self (.bot X) .C) (.plays (.bot X) .self .D)) (some K) = gDi K (progCode (.bot X)) := by
  unfold gDi
  rw [templateAt_impl, templateAt_plays_eq, templateAt_plays_eq, progGraphAt_self,
    progGraphAt_closed _ (by simp) (by simp) (pronounP_eq_false_of_noSelfIdxP hns)]
  rfl

/-- **DIMCID's guard over a closed watch is FOUND for all large `k`, in the probe frame** (bounded Löb on the two-guard
family `pQ (qDi ⋏ qDi)`, slack `(14 + K, 16)`): a box of the guard makes the instance defect against the watch,
which falsifies the antecedent; both readings. Parametric in the watch's towers and the value of its abstracted
description. -/
theorem dimcid_closed_found (K c : ℕ) (TX : Semiterm LAct Empty 1) (uX wX : ClosedSemiterm LAct 0)
    (hD : DescribesAbove K TX uX wX)
    (hDT : DescribesAbove K (Semiterm.lMap swap TX) (Semiterm.lMap swap uX) (Semiterm.lMap swap wX))
    (habs : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (k : V), (K : V) ≤ k → absVal K c k = descVal TX uX wX k)
    (habsT : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (k : V), (K : V) ≤ k →
      absVal K (transposeCode c) k = descVal (Semiterm.lMap swap TX) (Semiterm.lMap swap uX) (Semiterm.lMap swap wX) k)
    (hg7 : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁], IsSemiformula LAct 7 ((⌜gDi K c⌝ : ℕ) : V))
    (hg7T : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁],
      IsSemiformula LAct 7 ((⌜Semiformula.lMap swap (gDi K c)⌝ : ℕ) : V)) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k → K ≤ k ∧
      LenBox TAct k (guardCodeB (⌜gDi K c⌝ : ℕ) (pBot ((sDi K c).code k)) (descVal TX uX wX k) k) := by
  -- the instance equations, in every model above the threshold
  have hinst : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (k : V), (K : V) ≤ k →
      guardCodeB ((⌜gDi K c⌝ : ℕ) : V) (pBot ((sDi K c).code k)) (descVal TX uX wX k) k =
        instB (⌜qDi K c TX uX wX⌝ : V) k := by
    intro V _ _ k hk
    unfold qDi
    refine guardCodeB_plain_eq_instB _ (hg7 V) k _ _ _ _ _ _ (SM.hX_TB _ k) ?_ ?_ (hD.hX V k hk) (hD.hU V k hk) (hD.hW V k hk)
    · rw [revalueU_pBot, SM.revalueU_code]
    · rw [revalueW_pBot, SM.revalueW_code]
  have hinstT : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (k : V), (K : V) ≤ k →
      guardCodeB ((⌜Semiformula.lMap swap (gDi K c)⌝ : ℕ) : V) (pBot ((sDi K c).tr.code k))
          (descVal (Semiterm.lMap swap TX) (Semiterm.lMap swap uX) (Semiterm.lMap swap wX) k) k =
        instB (⌜Semiformula.lMap swap (qDi K c TX uX wX)⌝ : V) k := by
    intro V _ _ k hk
    unfold qDi
    rw [lMap_swap_qPlain, SM.lMap_swap_TB]
    refine guardCodeB_plain_eq_instB _ (hg7T V) k _ _ _ _ _ _ ?_ ?_ ?_ (hDT.hX V k hk) (hDT.hU V k hk) (hDT.hW V k hk)
    · rw [canonical_pBot, SM.canonical_tr_code, ← SM.canonical_code, ← canonical_pBot]
      exact SM.hX_TB _ k
    · rw [revalueU_pBot, SM.revalueU_tr_code]
    · rw [revalueW_pBot, SM.revalueW_tr_code]
  -- the Löb premise
  have hL : LoebSound (pQ (qDi K c TX uX wX ⋏ qDi K c TX uX wX)) (14 + K) 16 := by
    refine loebSound_pQ₂_above _ _ K fun V _ _ k hk b₁ _ b₃ _ ↦ ?_
    have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    rw [← hinst V k hk] at b₁
    rw [← hinstT V k hk] at b₃
    have e1 := SM.bot_then_V (sDi K c) k _ _ b₁
    have e2 := SM.bot_then_V (sDi K c).tr k _ _ b₃
    rw [sDi_a, Nat.cast_one] at e1
    rw [sDi_tr_a, Nat.cast_zero] at e2
    rw [← stdReadingV_eq_stdReading]
    have hq : Semiformula.Eval (s := stdReadingV V) ![k] Empty.elim (qDi K c TX uX wX) := by
      unfold qDi
      rw [eval_qPlain_iff]
      unfold gDi
      simp only [LogicalConnective.HomClass.map_imply, LogicalConnective.Prop.arrow_eq]
      intro hA
      exfalso
      rw [eval_plAt_self_closed] at hA
      simp only [Matrix.cons_val] at hA
      rw [show revalue ((sDi K c).uT.val (s := stdReadingV V) ![] Empty.elim) ((sDi K c).wT.val (s := stdReadingV V) ![] Empty.elim)
        ((sDi K c).TB.val (s := stdReadingV V) ![k] Empty.elim) = descVal (sDi K c).TB (sDi K c).uT (sDi K c).wT k from rfl,
        SM.descVal_TB, habs V k hk] at hA
      obtain ⟨n, hn⟩ := hA
      have := EvalGraph.unique_V' n 3 _ _ _ _ _ hn e1
      simp at this
    have hq' : Semiformula.Eval (s := stdReadingV V) ![k] Empty.elim (Semiformula.lMap swap (qDi K c TX uX wX)) := by
      unfold qDi
      rw [lMap_swap_qPlain, eval_qPlain_iff, lMap_swap_gDi]
      simp only [LogicalConnective.HomClass.map_imply, LogicalConnective.Prop.arrow_eq]
      intro hA
      exfalso
      rw [eval_plAt_self_closed] at hA
      simp only [Matrix.cons_val] at hA
      rw [show revalue ((Semiterm.lMap swap (sDi K c).uT).val (s := stdReadingV V) ![] Empty.elim)
        ((Semiterm.lMap swap (sDi K c).wT).val (s := stdReadingV V) ![] Empty.elim)
        ((Semiterm.lMap swap (sDi K c).TB).val (s := stdReadingV V) ![k] Empty.elim) =
        descVal (Semiterm.lMap swap (sDi K c).TB) (Semiterm.lMap swap (sDi K c).uT) (Semiterm.lMap swap (sDi K c).wT) k from rfl,
        SM.descVal_TB_T, habsT V k hk] at hA
      obtain ⟨n, hn⟩ := hA
      have := EvalGraph.unique_V' n 3 _ _ _ _ _ hn e2
      simp at this
    exact ⟨hq, hq, hq', hq'⟩
  obtain ⟨k₀, hf⟩ := family_found _ boundedInnerNec_sixteen hL
  refine ⟨k₀ + K, fun k hk ↦ ?_⟩
  obtain ⟨a, ha, hbox⟩ := hf k (by omega)
  obtain ⟨b₁, -, -, -⟩ := boxes_pQ₂_nat _ _ K k a ha hbox
  refine ⟨by omega, ?_⟩
  have e := hinst ℕ k (le_def.mpr (Nat.eq_or_lt_of_le (by rw [natCast_nat]; omega)))
  rw [natCast_nat] at e
  rw [e]
  exact b₁

end dimcid

/-! ### 3. The POS-above chain for a member-blind guard -/

section posAbove

/-- **A conditional `TAct`-theorem on a member-blind guard is found in the instance's own frame for all large `k`.** -/
theorem plain_found_above (g : Semisentence LAct 13)
    (hg7 : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁], IsSemiformula LAct 7 ((⌜g⌝ : ℕ) : V))
    (a : ℕ) (ha : a = 0 ∨ a = 1) (K kHat : ℕ)
    (hq : TAct ⊢ ∀¹ ((leF (↑kHat) #0 : Semisentence LAct 1) 🡒
      qPlain g (SM.TB ⟨g, a, ha⟩) (SM.uT ⟨g, a, ha⟩) (SM.wT ⟨g, a, ha⟩) (SM.TB ⟨g, a, ha⟩) (SM.uT ⟨g, a, ha⟩) (SM.wT ⟨g, a, ha⟩))) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k → K ≤ k ∧
      LenBox TAct k (guardCodeB (⌜g⌝ : ℕ) (pBot ((⟨g, a, ha⟩ : SM).code k)) (pBot ((⟨g, a, ha⟩ : SM).code k)) k) := by
  set s : SM := ⟨g, a, ha⟩ with hs
  have hG : ∀ k : ℕ, guardCodeB (⌜g⌝ : ℕ) (pBot (s.code k)) (pBot (s.code k)) k =
      instB (⌜qPlain g s.TB s.uT s.wT s.TB s.uT s.wT⌝ : ℕ) k := by
    intro k
    have e := guardCodeB_plain_eq_instB (V := ℕ) g (hg7 ℕ) k s.TB s.uT s.wT s.TB s.uT s.wT (SM.hX_TB s k)
      (by rw [revalueU_pBot, SM.revalueU_code]) (by rw [revalueW_pBot, SM.revalueW_code]) (SM.hX_TB s k)
      (by rw [revalueU_pBot, SM.revalueU_code]) (by rw [revalueW_pBot, SM.revalueW_code])
    rw [natCast_nat] at e
    exact e
  obtain ⟨k₀, h⟩ := found_of_all_above kHat hq _ hG
  exact ⟨k₀ + K, fun k hk ↦ ⟨by omega, h k (by omega)⟩⟩

/-- CIMCIC's guard over the closed program `c`: "if I cooperate with it, it cooperates with me". -/
noncomputable def gCi (K c : ℕ) : Semisentence LAct 13 :=
  plAt selfD (closedDescAt (some K) c) 0 🡒 plAt (closedDescAt (some K) c) selfD 0

/-- Dupoc's probe of the closed program `c`: "it cooperates with itself". -/
noncomputable def gPr (K c : ℕ) : Semisentence LAct 13 := plAt (closedDescAt (some K) c) (closedDescAt (some K) c) 0

lemma lMap_swap_gCi (K c : ℕ) : Semiformula.lMap swap (gCi K c) =
    plAt selfD (closedDescAt (some K) (transposeCode c)) 1 🡒 plAt (closedDescAt (some K) (transposeCode c)) selfD 1 := by
  unfold gCi
  rw [LogicalConnective.HomClass.map_imply, lMap_swap_plAt, lMap_swap_plAt, lMap_swap_selfD, lMap_swap_closedDescAt,
    swapAction_zero']

lemma lMap_swap_gPr (K c : ℕ) : Semiformula.lMap swap (gPr K c) =
    plAt (closedDescAt (some K) (transposeCode c)) (closedDescAt (some K) (transposeCode c)) 1 := by
  unfold gPr
  rw [lMap_swap_plAt, lMap_swap_closedDescAt, swapAction_zero']

theorem templateAt_cimG_eq (K : ℕ) (X : PD.Prog) (hns : noSelfIdxP (.bot X) = true) :
    templateAt (.impl (.plays .self (.bot X) .C) (.plays (.bot X) .self .C)) (some K) = gCi K (progCode (.bot X)) := by
  unfold gCi
  rw [templateAt_impl, templateAt_plays_eq, templateAt_plays_eq, progGraphAt_self,
    progGraphAt_closed _ (by simp) (by simp) (pronounP_eq_false_of_noSelfIdxP hns)]
  rfl

theorem templateAt_probe_eq (K : ℕ) (X : PD.Prog) (hns : noSelfIdxP (.bot X) = true) :
    templateAt (.plays (.bot X) (.bot X) .C) (some K) = gPr K (progCode (.bot X)) := by
  unfold gPr
  rw [templateAt_plays_eq, progGraphAt_closed _ (by simp) (by simp) (pronounP_eq_false_of_noSelfIdxP hns)]
  rfl

/-- **CIMCIC's guard over a watch that cooperates with everyone is a conditional `TAct`-theorem** (the consequent
holds; the transposed watch defects against everyone in the swapped reading). -/
theorem tact_qCi_above (K c : ℕ) (TX : Semiterm LAct Empty 1) (uX wX : ClosedSemiterm LAct 0)
    (habs : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (k : V), (K : V) ≤ k → absVal K c k = descVal TX uX wX k)
    (habsT : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (k : V), (K : V) ≤ k →
      absVal K (transposeCode c) k = descVal (Semiterm.lMap swap TX) (Semiterm.lMap swap uX) (Semiterm.lMap swap wX) k)
    (hB : ∃ kB : ℕ, ∀ (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (x : M), (kB : M) ≤ x → ∀ me : M,
      ∃ n, EvalGraph n (descVal TX uX wX x) me (descVal TX uX wX x) ((0 : ℕ) : M))
    (hBT : ∃ kB : ℕ, ∀ (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (x : M), (kB : M) ≤ x → ∀ me : M,
      ∃ n, EvalGraph n (descVal (Semiterm.lMap swap TX) (Semiterm.lMap swap uX) (Semiterm.lMap swap wX) x) me
        (descVal (Semiterm.lMap swap TX) (Semiterm.lMap swap uX) (Semiterm.lMap swap wX) x) ((1 : ℕ) : M))
    (X : Semiterm LAct Empty 1) (U W : ClosedSemiterm LAct 0) :
    ∃ kHat : ℕ, TAct ⊢ ∀¹ ((leF (↑kHat) #0 : Semisentence LAct 1) 🡒 qPlain (gCi K c) X U W X U W) := by
  obtain ⟨kB, hB⟩ := hB
  obtain ⟨kBT, hBT⟩ := hBT
  refine ⟨kB + kBT + K, tact_all_above_of_both _ _ (fun M _ _ x hx ↦ ?_) (fun M _ _ x hx ↦ ?_)⟩
  · have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    have hK : (K : M) ≤ x := le_trans (by push_cast; exact le_add_self) hx
    have hkB : (kB : M) ≤ x := le_trans (by push_cast; exact le_trans le_self_add le_self_add) hx
    rw [eval_qPlain_iff]
    unfold gCi
    simp only [LogicalConnective.HomClass.map_imply, LogicalConnective.Prop.arrow_eq]
    intro _
    rw [eval_plAt_closed_self]
    simp only [Matrix.cons_val]
    rw [habs M x hK]
    exact hB M x hkB _
  · have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    have hK : (K : M) ≤ x := le_trans (by push_cast; exact le_add_self) hx
    have hkBT : (kBT : M) ≤ x := le_trans (by push_cast; exact le_trans le_add_self le_self_add) hx
    rw [eval_swappedReading, lMap_swap_qPlain, ← stdReadingV_eq_stdReading, eval_qPlain_iff, lMap_swap_gCi]
    simp only [LogicalConnective.HomClass.map_imply, LogicalConnective.Prop.arrow_eq]
    intro _
    rw [eval_plAt_closed_self]
    simp only [Matrix.cons_val]
    rw [habsT M x hK]
    exact hBT M x hkBT _

/-- **Dupoc's probe of a watch that cooperates with itself is a conditional `TAct`-theorem.** -/
theorem tact_qPr_above (K c : ℕ) (TX : Semiterm LAct Empty 1) (uX wX : ClosedSemiterm LAct 0)
    (habs : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (k : V), (K : V) ≤ k → absVal K c k = descVal TX uX wX k)
    (habsT : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (k : V), (K : V) ≤ k →
      absVal K (transposeCode c) k = descVal (Semiterm.lMap swap TX) (Semiterm.lMap swap uX) (Semiterm.lMap swap wX) k)
    (hB : ∃ kB : ℕ, ∀ (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (x : M), (kB : M) ≤ x →
      ∃ n, EvalGraph n (descVal TX uX wX x) (descVal TX uX wX x) (descVal TX uX wX x) ((0 : ℕ) : M))
    (hBT : ∃ kB : ℕ, ∀ (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (x : M), (kB : M) ≤ x →
      ∃ n, EvalGraph n (descVal (Semiterm.lMap swap TX) (Semiterm.lMap swap uX) (Semiterm.lMap swap wX) x)
        (descVal (Semiterm.lMap swap TX) (Semiterm.lMap swap uX) (Semiterm.lMap swap wX) x)
        (descVal (Semiterm.lMap swap TX) (Semiterm.lMap swap uX) (Semiterm.lMap swap wX) x) ((1 : ℕ) : M))
    (X : Semiterm LAct Empty 1) (U W : ClosedSemiterm LAct 0) :
    ∃ kHat : ℕ, TAct ⊢ ∀¹ ((leF (↑kHat) #0 : Semisentence LAct 1) 🡒 qPlain (gPr K c) X U W X U W) := by
  obtain ⟨kB, hB⟩ := hB
  obtain ⟨kBT, hBT⟩ := hBT
  refine ⟨kB + kBT + K, tact_all_above_of_both _ _ (fun M _ _ x hx ↦ ?_) (fun M _ _ x hx ↦ ?_)⟩
  · have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    have hK : (K : M) ≤ x := le_trans (by push_cast; exact le_add_self) hx
    have hkB : (kB : M) ≤ x := le_trans (by push_cast; exact le_trans le_self_add le_self_add) hx
    rw [eval_qPlain_iff]
    unfold gPr
    rw [eval_plAt_closed_closed]
    simp only [Matrix.cons_val]
    rw [habs M x hK]
    exact hB M x hkB
  · have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    have hK : (K : M) ≤ x := le_trans (by push_cast; exact le_add_self) hx
    have hkBT : (kBT : M) ≤ x := le_trans (by push_cast; exact le_trans le_add_self le_self_add) hx
    rw [eval_swappedReading, lMap_swap_qPlain, ← stdReadingV_eq_stdReading, eval_qPlain_iff, lMap_swap_gPr]
    rw [eval_plAt_closed_closed]
    simp only [Matrix.cons_val]
    rw [habsT M x hK]
    exact hBT M x hkBT

end posAbove

/-! ### 4. The plays of a watch in every model -/

section plays

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- A bot-wrapped watch plays its then-constant in any frame when its member's self-play hits the test. -/
theorem W1.bot_plays_then (W : W1) (x : V) {n : V}
    (hr : EvalGraph n (pBot (W.s.code x)) (pBot (W.s.code x)) (pBot (W.s.code x)) (W.t : V)) (me opp : V) :
    EvalGraph (n + 1 + 1 + 1) me opp (pBot (W.code x)) (W.p : V) := by
  unfold W1.code
  rw [EvalGraph.bot_iff, EvalGraph.ite_iff]
  refine ⟨(W.t : V), ?_, Or.inl ⟨rfl, ?_⟩⟩
  · rw [EvalGraph.sim_iff, substCode_bot]; exact hr
  · rw [EvalGraph.const_iff]

/-- …and its else-constant when the member's self-play misses the test. -/
theorem W1.bot_plays_else (W : W1) (x : V) {n r : V}
    (hr : EvalGraph n (pBot (W.s.code x)) (pBot (W.s.code x)) (pBot (W.s.code x)) r) (hne : r ≠ (W.t : V)) (me opp : V) :
    EvalGraph (n + 1 + 1 + 1) me opp (pBot (W.code x)) (W.q : V) := by
  unfold W1.code
  rw [EvalGraph.bot_iff, EvalGraph.ite_iff]
  refine ⟨r, ?_, Or.inr ⟨hne, ?_⟩⟩
  · rw [EvalGraph.sim_iff, substCode_bot]; exact hr
  · rw [EvalGraph.const_iff]

/-- **A compiled searcher whose guard is a `TAct`-theorem in its own frame plays its then-action against itself above
a standard threshold, in every model** (`botSV_found_V` on the simple member). -/
theorem ofSearch_self_plays (φ : PD.Formula) (hns : noSelfIdxF φ = true) (a : PD.Action)
    (hq : TAct ⊢ ∀¹ qInst (template φ) (actCode a)) :
    ∃ kB : ℕ, ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (x : V), (kB : V) ≤ x →
      EvalGraph 3 (pBot ((SM.ofSearch φ a).code x)) (pBot ((SM.ofSearch φ a).code x)) (pBot ((SM.ofSearch φ a).code x))
        ((actCode a : ℕ) : V) := by
  obtain ⟨kHat, h⟩ := botSV_found_V (template φ) (actCode a) (actCode_zero_or_one a) hq
  refine ⟨kHat, fun V _ _ x hx ↦ ?_⟩
  rw [SM.code_ofSearch_eq_SV φ hns]
  exact botSV_then_V (template φ) (actCode a) x _ _ (h V x hx)

/-- The transposed compiled searcher plays its then-action (the transposed one) against itself above a threshold. -/
theorem ofSearch_tr_self_plays (φ : PD.Formula) (hns : noSelfIdxF φ = true) (hfr : fragF φ = true) (a : PD.Action)
    (hq : TAct ⊢ ∀¹ qInst (template φ.transpose) (1 - actCode a)) :
    ∃ kB : ℕ, ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (x : V), (kB : V) ≤ x →
      EvalGraph 3 (pBot ((SM.ofSearch φ a).tr.code x)) (pBot ((SM.ofSearch φ a).tr.code x))
        (pBot ((SM.ofSearch φ a).tr.code x)) ((1 - actCode a : ℕ) : V) := by
  obtain ⟨kHat, h⟩ := botSV_found_V (template φ.transpose) (1 - actCode a)
    (by rcases actCode_zero_or_one a with h | h <;> simp [h]) hq
  refine ⟨kHat, fun V _ _ x hx ↦ ?_⟩
  rw [SM.tr_code_ofSearch_eq_SV φ hns hfr]
  exact botSV_then_V (template φ.transpose) (1 - actCode a) x _ _ (h V x hx)

/-- **The `.plays p p a` atom of `template` for a CLOSED `p`, in every model**: "`p` plays `a` against itself". -/
lemma eval_template_plays_closed_closed_V (p : PD.Prog) (hp1 : p ≠ .self) (hp2 : p ≠ .opp) (a : PD.Action) (b : Fin 6 → V) :
    Semiformula.Eval (s := stdReadingV V) b Empty.elim (template (.plays p p a)) ↔
      ∃ n, EvalGraph n ((progCode p : ℕ) : V) ((progCode p : ℕ) : V) ((progCode p : ℕ) : V) (actCode a : V) := by
  rw [template_plays]
  unfold progGraph
  rw [progAux_of_ne hp1 hp2]
  simp only [Semiformula.eval_substs, Semiformula.eval_ex, LogicalConnective.HomClass.map_and,
    LogicalConnective.Prop.and_eq, Semiformula.eval_rel, eval_relDesc_V, eval_evalG_V, eval_closedDesc_V,
    stdReadingV_rel_eq, Function.comp_def, Matrix.cons_val, Semiterm.val_bvar, val_cl_V, val_actT_V]
  constructor
  · rintro ⟨x, y, N, rfl, rfl, h⟩
    exact ⟨N, h⟩
  · rintro ⟨N, h⟩
    exact ⟨_, _, N, rfl, rfl, h⟩

/-- **The closed probe of a frozen constant is a `TAct`-theorem in the searcher's own frame** (both readings):
`.bot (.const a)` plays `a` against itself. -/
theorem tact_qInst_prC (a : PD.Action) (n : ℕ) : TAct ⊢ ∀¹ qInst (template (prC a a)) n := by
  refine tact_all_of_both _ (fun M _ _ x ↦ ?_) (fun M _ _ x ↦ ?_)
  · have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    unfold qInst
    rw [eval_qT_iff, eval_template_plays_closed_closed_V _ (by simp) (by simp), cast_progCode_botConst]
    exact bot_const_play_V _ _ _
  · have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    unfold qInst
    rw [eval_qT_swap, lMap_swap_template _ (by cases a <;> rfl), eval_qT_iff]
    have ht : (prC a a).transpose = prC a.swap a.swap := by cases a <;> rfl
    rw [ht, eval_template_plays_closed_closed_V _ (by simp) (by simp), cast_progCode_botConst]
    exact bot_const_play_V _ _ _

end plays

/-! ### 5. The bits -/

section bits

/-- The abstracted description of the watch at the threshold denotes the watch, as the frame tower does. -/
lemma W1.habs (W : W1) : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (k : V), (W1.K : V) ≤ k →
    absVal W1.K (pBot (W.code W1.K)) k = descVal W.TX W.uT W.wT k := fun V _ _ k hk ↦ by
  rw [W1.absVal_code W le_rfl, W1.descVal_TX W hk]

lemma W1.habsT (W : W1) : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (k : V), (W1.K : V) ≤ k →
    absVal W1.K (transposeCode (pBot (W.code W1.K))) k =
      descVal (Semiterm.lMap swap W.TX) (Semiterm.lMap swap W.uT) (Semiterm.lMap swap W.wT) k := fun V _ _ k hk ↦ by
  rw [W1.absVal_tr_code W le_rfl, W1.descVal_TX_T W hk]

/-- DIMCID's off-diagonal guard at the probed instance `X` (the `dimG` of `Rows/DIMCID.lean`). -/
abbrev dimGf (X : PD.Prog) : PD.Formula := .impl (.plays .self (.bot X) .C) (.plays (.bot X) .self .D)
/-- CIMCIC's. -/
abbrev cimGf (X : PD.Prog) : PD.Formula := .impl (.plays .self (.bot X) .C) (.plays (.bot X) .self .C)

/-- **`dimcid × T` is D whenever `T`'s instance seeing DIMCID is a `W1` watch** (the self-fulfilling family on the watch). -/
theorem dimcid_D_of_W1 (T : Tmpl) (W : W1)
    (hW : ∀ k : ℕ, pBot (W.code k) = progCode (.bot (inst (tauZoo k) T .dimcid)))
    (hI : ∀ k : ℕ, instCode k .dimcid T =
      pSearch k (templateCodeAt (dimGf (inst (tauZoo k) T .dimcid)) k) (pConst 1) (pConst 0))
    (hfr : ∀ k, fragF (dimGf (inst (tauZoo k) T .dimcid)) = true)
    (hnsF : ∀ k, noSelfIdxF (dimGf (inst (tauZoo k) T .dimcid)) = true)
    (hnsX : ∀ k, noSelfIdxP (.bot (inst (tauZoo k) T .dimcid)) = true)
    (hnsI : ∀ k, noSelfIdxP (.bot (inst (tauZoo k) .dimcid T)) = true)
    (hfrX : ∀ k, fragP (.bot (inst (tauZoo k) T .dimcid)) = true)
    (hnsXT : ∀ k, noSelfIdxP (.bot (inst (tauZoo k) T .dimcid).transpose) = true)
    (hnsT : ∀ k, noSelfIdxF (.impl (.plays .self (.bot (inst (tauZoo k) T .dimcid).transpose) .D)
      (.plays (.bot (inst (tauZoo k) T .dimcid).transpose) .self .C)) = true) :
    bitEventually .dimcid T .D := by
  set K := W1.K with hKdef
  set c : ℕ := progCode (.bot (inst (tauZoo K) T .dimcid)) with hc
  have hcW : c = pBot (W.code K) := by rw [hc, ← hW K]
  -- the stored template is constant above the threshold
  have hg : ∀ k : ℕ, K ≤ k → templateAt (dimGf (inst (tauZoo k) T .dimcid)) (some k) = gDi K c := by
    intro k hk
    rw [templateAt_dimG_eq k _ (hnsX k)]
    unfold gDi
    rw [← hW k, hcW, W1.closedDescAt_code W hk, W1.closedDescAt_code W le_rfl]
  have hg7 : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁], IsSemiformula LAct 7 ((⌜gDi K c⌝ : ℕ) : V) := by
    intro V _ _
    rw [← templateAt_dimG_eq K _ (hnsX K)]
    exact isSemiformula7_cast_templateAt _ K (hnsF K) V
  have hg7T : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁],
      IsSemiformula LAct 7 ((⌜Semiformula.lMap swap (gDi K c)⌝ : ℕ) : V) := by
    intro V _ _
    have e : Semiformula.lMap swap (gDi K c) =
        templateAt (.impl (.plays .self (.bot (inst (tauZoo K) T .dimcid).transpose) .D)
          (.plays (.bot (inst (tauZoo K) T .dimcid).transpose) .self .C)) (some K) := by
      rw [lMap_swap_gDi, templateAt_impl, templateAt_plays_eq, templateAt_plays_eq, progGraphAt_self,
        progGraphAt_closed _ (by simp) (by simp) (pronounP_eq_false_of_noSelfIdxP (hnsXT K)),
        hc, transposeCode_progCode _ (hfrX K)]
      rfl
    rw [e]
    exact isSemiformula7_cast_templateAt _ K (hnsT K) V
  obtain ⟨k₀, h⟩ := dimcid_closed_found K c W.TX W.uT W.wT W.describesBot W.describesBotT
    (by rw [hcW]; exact W1.habs W) (by rw [hcW]; exact W1.habsT W) hg7 hg7T
  refine ⟨k₀, fun k hk ↦ ?_⟩
  obtain ⟨hK, hbox⟩ := h k hk
  have e1 : (sDi K c).code k = instCode k .dimcid T := by
    rw [hI k]
    unfold SM.code
    simp only [sDi_g, sDi_a, natCast_nat]
    show pSearch k (⌜gDi K c⌝ : ℕ) (pConst 1) (pConst (1 - 1)) =
      pSearch k (⌜templateAt (dimGf (inst (tauZoo k) T .dimcid)) (some k)⌝ : ℕ) (pConst 1) (pConst 0)
    rw [hg k hK]
  have e2 : descVal W.TX W.uT W.wT k = progCode (.bot (inst (tauZoo k) T .dimcid)) := by
    rw [W1.descVal_TX W (le_def.mpr (Nat.eq_or_lt_of_le (by rw [natCast_nat]; exact hK))), hW k]
  rw [e1, e2, ← progCode_bot_inst] at hbox
  have e3 : (⌜gDi K c⌝ : ℕ) = templateCodeAt (dimGf (inst (tauZoo k) T .dimcid)) k := by
    show _ = (⌜templateAt (dimGf (inst (tauZoo k) T .dimcid)) (some k)⌝ : ℕ)
    rw [hg k hK]
  rw [e3, guardCodeB_templateCodeAt _ _ _ _ (hnsF k)] at hbox
  have hmove : guardCode (templateCode (dimGf (inst (tauZoo k) T .dimcid)))
      (progCode (.bot (inst (tauZoo k) .dimcid T))) (progCode (.bot (inst (tauZoo k) T .dimcid))) =
      guardCode (templateCode (dimGf (inst (tauZoo k) T .dimcid)))
      (progCode (.bot (inst (tauZoo k) .dimcid T))) (progCode (.bot (inst (tauZoo k) .dimcid T))) := by
    change guardOf _ _ _ = guardOf _ _ _
    rw [guardOf_eq_templateCode_subst (properPlayer_bot _) (properPlayer_bot _) _ (hfr k) (hnsI k) (hnsX k),
      guardOf_eq_templateCode_subst (properPlayer_bot _) (properPlayer_bot _) _ (hfr k) (hnsI k) (hnsI k)]
    rfl
  rw [hmove, progCode_bot_inst, hI k] at hbox
  exact bitPlays_of_eq (hI k) ⟨_, search_then_at _ hbox (const_play 0 _ _ _) (hnsF k)⟩

/-- **`dimcid × T` is D whenever `T`'s instance seeing DIMCID is the bot-wrapped engine searcher `SV g a`**
(τ(CupodTroll)'s `.eq`-searcher). -/
theorem dimcid_D_of_SV (T : Tmpl) (g : Semisentence LAct 6) (a : ℕ) (ha : a = 0 ∨ a = 1)
    (hW : ∀ k : ℕ, pBot (SV (V := ℕ) g a k) = progCode (.bot (inst (tauZoo k) T .dimcid)))
    (hI : ∀ k : ℕ, instCode k .dimcid T =
      pSearch k (templateCodeAt (dimGf (inst (tauZoo k) T .dimcid)) k) (pConst 1) (pConst 0))
    (hfr : ∀ k, fragF (dimGf (inst (tauZoo k) T .dimcid)) = true)
    (hnsF : ∀ k, noSelfIdxF (dimGf (inst (tauZoo k) T .dimcid)) = true)
    (hnsX : ∀ k, noSelfIdxP (.bot (inst (tauZoo k) T .dimcid)) = true)
    (hnsI : ∀ k, noSelfIdxP (.bot (inst (tauZoo k) .dimcid T)) = true)
    (hfrX : ∀ k, fragP (.bot (inst (tauZoo k) T .dimcid)) = true)
    (hnsXT : ∀ k, noSelfIdxP (.bot (inst (tauZoo k) T .dimcid).transpose) = true)
    (hnsT : ∀ k, noSelfIdxF (.impl (.plays .self (.bot (inst (tauZoo k) T .dimcid).transpose) .D)
      (.plays (.bot (inst (tauZoo k) T .dimcid).transpose) .self .C)) = true) :
    bitEventually .dimcid T .D := by
  set c : ℕ := progCode (.bot (inst (tauZoo 0) T .dimcid)) with hc
  have hcW : c = pBot (SV (V := ℕ) g a 0) := by rw [hc, ← hW 0]
  have hg : ∀ k : ℕ, templateAt (dimGf (inst (tauZoo k) T .dimcid)) (some k) = gDi 0 c := by
    intro k
    rw [templateAt_dimG_eq k _ (hnsX k)]
    unfold gDi
    rw [← hW k, hcW, closedDescAt_botSV g a ha k, closedDescAt_botSV g a ha 0]
  have hg7 : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁], IsSemiformula LAct 7 ((⌜gDi 0 c⌝ : ℕ) : V) := by
    intro V _ _
    rw [← templateAt_dimG_eq 0 _ (hnsX 0)]
    exact isSemiformula7_cast_templateAt _ 0 (hnsF 0) V
  have hg7T : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁],
      IsSemiformula LAct 7 ((⌜Semiformula.lMap swap (gDi 0 c)⌝ : ℕ) : V) := by
    intro V _ _
    have e : Semiformula.lMap swap (gDi 0 c) =
        templateAt (.impl (.plays .self (.bot (inst (tauZoo 0) T .dimcid).transpose) .D)
          (.plays (.bot (inst (tauZoo 0) T .dimcid).transpose) .self .C)) (some 0) := by
      rw [lMap_swap_gDi, templateAt_impl, templateAt_plays_eq, templateAt_plays_eq, progGraphAt_self,
        progGraphAt_closed _ (by simp) (by simp) (pronounP_eq_false_of_noSelfIdxP (hnsXT 0)),
        hc, transposeCode_progCode _ (hfrX 0)]
      rfl
    rw [e]
    exact isSemiformula7_cast_templateAt _ 0 (hnsT 0) V
  obtain ⟨k₀, h⟩ := dimcid_closed_found 0 c (TBS g a) (uS g a) (wS g a) (describes_botSV g a ha).above
    (describes_botSVT g a ha).above
    (fun V _ _ k _ ↦ by rw [hcW, absVal_botSV g a ha, descVal_botSV g a ha])
    (fun V _ _ k _ ↦ by rw [hcW, absVal_tr_botSV g a ha, descVal_botSV_T g a ha]) hg7 hg7T
  refine ⟨k₀, fun k hk ↦ ?_⟩
  obtain ⟨-, hbox⟩ := h k hk
  have e1 : (sDi 0 c).code k = instCode k .dimcid T := by
    rw [hI k]
    unfold SM.code
    simp only [sDi_g, sDi_a, natCast_nat]
    show pSearch k (⌜gDi 0 c⌝ : ℕ) (pConst 1) (pConst (1 - 1)) =
      pSearch k (⌜templateAt (dimGf (inst (tauZoo k) T .dimcid)) (some k)⌝ : ℕ) (pConst 1) (pConst 0)
    rw [hg k]
  have e2 : descVal (TBS g a) (uS g a) (wS g a) k = progCode (.bot (inst (tauZoo k) T .dimcid)) := by
    rw [descVal_botSV g a ha, hW k]
  rw [e1, e2, ← progCode_bot_inst] at hbox
  have e3 : (⌜gDi 0 c⌝ : ℕ) = templateCodeAt (dimGf (inst (tauZoo k) T .dimcid)) k := by
    show _ = (⌜templateAt (dimGf (inst (tauZoo k) T .dimcid)) (some k)⌝ : ℕ)
    rw [hg k]
  rw [e3, guardCodeB_templateCodeAt _ _ _ _ (hnsF k)] at hbox
  have hmove : guardCode (templateCode (dimGf (inst (tauZoo k) T .dimcid)))
      (progCode (.bot (inst (tauZoo k) .dimcid T))) (progCode (.bot (inst (tauZoo k) T .dimcid))) =
      guardCode (templateCode (dimGf (inst (tauZoo k) T .dimcid)))
      (progCode (.bot (inst (tauZoo k) .dimcid T))) (progCode (.bot (inst (tauZoo k) .dimcid T))) := by
    change guardOf _ _ _ = guardOf _ _ _
    rw [guardOf_eq_templateCode_subst (properPlayer_bot _) (properPlayer_bot _) _ (hfr k) (hnsI k) (hnsX k),
      guardOf_eq_templateCode_subst (properPlayer_bot _) (properPlayer_bot _) _ (hfr k) (hnsI k) (hnsI k)]
    rfl
  rw [hmove, progCode_bot_inst, hI k] at hbox
  exact bitPlays_of_eq (hI k) ⟨_, search_then_at _ hbox (const_play 0 _ _ _) (hnsF k)⟩

/-! #### The watches: the self-probers' instances at the constants, under τ(TFTSim)'s / τ(DBot)'s run-stage -/

/-- DIMCID's instance at the cooperator, as a simple member. -/
noncomputable def sDiCoop : SM := SM.ofSearch (implC .C .C .D) .D
/-- DIMCID's instance at the defector. -/
noncomputable def sDiDef : SM := SM.ofSearch (implC .D .C .D) .D
/-- CIMCIC's instance at the cooperator. -/
noncomputable def sCiCoop : SM := SM.ofSearch (implC .C .C .C) .C
/-- Dupoc's instance at the cooperator. -/
noncomputable def sDuCoop : SM := SM.ofSearch (prC .C .C) .C

lemma sDiCoop_code (k : ℕ) : sDiCoop.code k = instCode k .dimcid .coop := by
  rw [instCode_dimcid_coop]; unfold sDiCoop SM.code
  simp only [SM.ofSearch_g, SM.ofSearch_a, natCast_nat, actCode]; rfl
lemma sDiDef_code (k : ℕ) : sDiDef.code k = instCode k .dimcid .defect := by
  rw [instCode_dimcid_defect]; unfold sDiDef SM.code
  simp only [SM.ofSearch_g, SM.ofSearch_a, natCast_nat, actCode]; rfl
lemma sCiCoop_code (k : ℕ) : sCiCoop.code k = instCode k .cimcic .coop := by
  rw [instCode_cimcic_coop]; unfold sCiCoop SM.code
  simp only [SM.ofSearch_g, SM.ofSearch_a, natCast_nat, actCode]; rfl
lemma sDuCoop_code (k : ℕ) : sDuCoop.code k = instCode k .dupoc .coop := by
  rw [instCode_dupoc_coop]; unfold sDuCoop SM.code
  simp only [SM.ofSearch_g, SM.ofSearch_a, natCast_nat, actCode]; rfl

/-- τ(TFTSim)'s instance at DIMCID: the run-stage on DIMCID's instance at the cooperator. -/
noncomputable def WtDi : W1 := ⟨sDiCoop, 0, 0, 1, Or.inl rfl, Or.inl rfl, Or.inr rfl⟩
/-- τ(DBot)'s instance at DIMCID: the punisher on DIMCID's instance at the defector. -/
noncomputable def WdDi : W1 := ⟨sDiDef, 0, 1, 0, Or.inl rfl, Or.inr rfl, Or.inl rfl⟩
/-- τ(TFTSim)'s instance at CIMCIC. -/
noncomputable def WtCi : W1 := ⟨sCiCoop, 0, 0, 1, Or.inl rfl, Or.inl rfl, Or.inr rfl⟩
/-- τ(TFTSim)'s instance at Dupoc. -/
noncomputable def WtDu : W1 := ⟨sDuCoop, 0, 0, 1, Or.inl rfl, Or.inl rfl, Or.inr rfl⟩

lemma WtDi_code (k : ℕ) : pBot (WtDi.code k) = progCode (.bot (inst (tauZoo k) .tftSim .dimcid)) := by
  rw [progCode_bot_inst, instCode_tftSim]
  unfold W1.code
  simp only [WtDi, natCast_nat, sDiCoop_code]
lemma WdDi_code (k : ℕ) : pBot (WdDi.code k) = progCode (.bot (inst (tauZoo k) .dbot .dimcid)) := by
  rw [progCode_bot_inst, instCode_dbot]
  unfold W1.code
  simp only [WdDi, natCast_nat, sDiDef_code]
lemma WtCi_code (k : ℕ) : pBot (WtCi.code k) = progCode (.bot (inst (tauZoo k) .tftSim .cimcic)) := by
  rw [progCode_bot_inst, instCode_tftSim]
  unfold W1.code
  simp only [WtCi, natCast_nat, sCiCoop_code]
lemma WtDu_code (k : ℕ) : pBot (WtDu.code k) = progCode (.bot (inst (tauZoo k) .tftSim .dupoc)) := by
  rw [progCode_bot_inst, instCode_tftSim]
  unfold W1.code
  simp only [WtDu, natCast_nat, sDuCoop_code]

/-- τ(CupodTroll)'s instance at DIMCID: the `.eq`-searcher on the false identity. -/
noncomputable abbrev gEqCD : Semisentence LAct 6 := template (.eq (.const .C) (.const .D))

lemma SV_gEqCD_code (k : ℕ) : pBot (SV (V := ℕ) gEqCD 1 k) = progCode (.bot (inst (tauZoo k) .cupodTroll .dimcid)) := by
  rw [progCode_bot_inst, instCode_cupodTroll k .dimcid (by decide), SV_nat,
    templateCode_eq_quote_template (.eq (.const .C) (.const .D)) rfl]

/-! #### The DIMCID instances (the compiled searchers on the abstracted templates) -/

theorem instCode_dimcid_tftSim' (k : ℕ) : instCode k .dimcid .tftSim =
    pSearch k (templateCodeAt (dimGf (inst (tauZoo k) .tftSim .dimcid)) k) (pConst 1) (pConst 0) := by
  unfold instCode; rw [inst_dimcid_peel_tftSim]; simp [actCode]
theorem instCode_dimcid_dbot' (k : ℕ) : instCode k .dimcid .dbot =
    pSearch k (templateCodeAt (dimGf (inst (tauZoo k) .dbot .dimcid)) k) (pConst 1) (pConst 0) := by
  unfold instCode; rw [inst_dimcid_peel_dbot]; simp [actCode]
theorem instCode_dimcid_cupodTroll' (k : ℕ) : instCode k .dimcid .cupodTroll =
    pSearch k (templateCodeAt (dimGf (inst (tauZoo k) .cupodTroll .dimcid)) k) (pConst 1) (pConst 0) := by
  unfold instCode; rw [inst_dimcid_peel_cupodTroll]; simp [actCode]

/-- **`dimcid × tftSim` is D** — the `S'` flip of the engine's C: the self-fulfilling guard on τ(TFTSim)'s instance. -/
theorem dimcid_tftSim_D : bitEventually .dimcid .tftSim .D :=
  dimcid_D_of_W1 .tftSim WtDi WtDi_code instCode_dimcid_tftSim' (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl)
    (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl)

/-- **`dimcid × dbot` is D** (flip). -/
theorem dimcid_dbot_D : bitEventually .dimcid .dbot .D :=
  dimcid_D_of_W1 .dbot WdDi WdDi_code instCode_dimcid_dbot' (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl)
    (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl)

/-- **`dimcid × cupodTroll` is D** (flip). -/
theorem dimcid_cupodTroll_D : bitEventually .dimcid .cupodTroll .D :=
  dimcid_D_of_SV .cupodTroll gEqCD 1 (Or.inr rfl) SV_gEqCD_code instCode_dimcid_cupodTroll' (fun _ ↦ rfl) (fun _ ↦ rfl)
    (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl)

/-! #### CIMCIC and Dupoc: the POS-above chain on the watch -/

/-- **`cimcic × T` is C whenever `T`'s instance seeing CIMCIC is a `W1` watch that cooperates with everyone above a
threshold (and its transposition defects)**: the consequent of CIMCIC's guard holds in both readings. -/
theorem cimcic_C_of_W1 (T : Tmpl) (W : W1)
    (hW : ∀ k : ℕ, pBot (W.code k) = progCode (.bot (inst (tauZoo k) T .cimcic)))
    (hI : ∀ k : ℕ, instCode k .cimcic T =
      pSearch k (templateCodeAt (cimGf (inst (tauZoo k) T .cimcic)) k) (pConst 0) (pConst 1))
    (hnsF : ∀ k, noSelfIdxF (cimGf (inst (tauZoo k) T .cimcic)) = true)
    (hnsX : ∀ k, noSelfIdxP (.bot (inst (tauZoo k) T .cimcic)) = true)
    (hB : ∃ kB : ℕ, ∀ (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (x : M), (kB : M) ≤ x → ∀ me : M,
      ∃ n, EvalGraph n (pBot (W.code x)) me (pBot (W.code x)) ((0 : ℕ) : M))
    (hBT : ∃ kB : ℕ, ∀ (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (x : M), (kB : M) ≤ x → ∀ me : M,
      ∃ n, EvalGraph n (pBot (W.tr.code x)) me (pBot (W.tr.code x)) ((1 : ℕ) : M)) :
    bitEventually .cimcic T .C := by
  set K := W1.K with hKdef
  set c : ℕ := progCode (.bot (inst (tauZoo K) T .cimcic)) with hc
  have hcW : c = pBot (W.code K) := by rw [hc, ← hW K]
  have hg : ∀ k : ℕ, K ≤ k → templateAt (cimGf (inst (tauZoo k) T .cimcic)) (some k) = gCi K c := by
    intro k hk
    rw [templateAt_cimG_eq k _ (hnsX k)]
    unfold gCi
    rw [← hW k, hcW, W1.closedDescAt_code W hk, W1.closedDescAt_code W le_rfl]
  have hg7 : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁], IsSemiformula LAct 7 ((⌜gCi K c⌝ : ℕ) : V) := by
    intro V _ _
    rw [← templateAt_cimG_eq K _ (hnsX K)]
    exact isSemiformula7_cast_templateAt _ K (hnsF K) V
  obtain ⟨kB, hB⟩ := hB
  obtain ⟨kBT, hBT⟩ := hBT
  have hB' : ∃ kB : ℕ, ∀ (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (x : M), (kB : M) ≤ x → ∀ me : M,
      ∃ n, EvalGraph n (descVal W.TX W.uT W.wT x) me (descVal W.TX W.uT W.wT x) ((0 : ℕ) : M) := by
    refine ⟨kB + K, fun M _ _ x hx me ↦ ?_⟩
    have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    rw [W1.descVal_TX W (le_trans (by push_cast; exact le_add_self) hx)]
    exact hB M x (le_trans (by push_cast; exact le_self_add) hx) me
  have hBT' : ∃ kB : ℕ, ∀ (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (x : M), (kB : M) ≤ x → ∀ me : M,
      ∃ n, EvalGraph n (descVal (Semiterm.lMap swap W.TX) (Semiterm.lMap swap W.uT) (Semiterm.lMap swap W.wT) x) me
        (descVal (Semiterm.lMap swap W.TX) (Semiterm.lMap swap W.uT) (Semiterm.lMap swap W.wT) x) ((1 : ℕ) : M) := by
    refine ⟨kBT + K, fun M _ _ x hx me ↦ ?_⟩
    have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    rw [W1.descVal_TX_T W (le_trans (by push_cast; exact le_add_self) hx)]
    exact hBT M x (le_trans (by push_cast; exact le_self_add) hx) me
  set sCi : SM := ⟨gCi K c, 0, Or.inl rfl⟩ with hsCi
  obtain ⟨kHat, hq⟩ := tact_qCi_above K c W.TX W.uT W.wT (by rw [hcW]; exact W1.habs W) (by rw [hcW]; exact W1.habsT W)
    hB' hBT' sCi.TB sCi.uT sCi.wT
  obtain ⟨k₀, h⟩ := plain_found_above (gCi K c) hg7 0 (Or.inl rfl) K kHat hq
  refine ⟨k₀, fun k hk ↦ ?_⟩
  obtain ⟨hK, hbox⟩ := h k hk
  have e1 : sCi.code k = instCode k .cimcic T := by
    rw [hI k]
    unfold SM.code
    simp only [hsCi, natCast_nat]
    show pSearch k (⌜gCi K c⌝ : ℕ) (pConst 0) (pConst (1 - 0)) =
      pSearch k (⌜templateAt (cimGf (inst (tauZoo k) T .cimcic)) (some k)⌝ : ℕ) (pConst 0) (pConst 1)
    rw [hg k hK]
  have e3 : (⌜gCi K c⌝ : ℕ) = templateCodeAt (cimGf (inst (tauZoo k) T .cimcic)) k := by
    show _ = (⌜templateAt (cimGf (inst (tauZoo k) T .cimcic)) (some k)⌝ : ℕ)
    rw [hg k hK]
  rw [e1, e3, guardCodeB_templateCodeAt _ _ _ _ (hnsF k), hI k] at hbox
  exact bitPlays_of_eq (hI k) ⟨_, search_then_at _ hbox (const_play 0 _ _ _) (hnsF k)⟩

/-- **`dupoc × T` is C whenever `T`'s instance seeing Dupoc is a `W1` watch that cooperates with itself above a
threshold (and its transposition defects against itself)**: the closed probe is a conditional `TAct`-theorem. -/
theorem dupoc_C_of_W1 (T : Tmpl) (W : W1)
    (hW : ∀ k : ℕ, pBot (W.code k) = progCode (.bot (inst (tauZoo k) T .dupoc)))
    (hI : ∀ k : ℕ, instCode k .dupoc T =
      pSearch k (templateCodeAt (probe (inst (tauZoo k) T .dupoc)) k) (pConst 0) (pConst 1))
    (hnsF : ∀ k, noSelfIdxF (probe (inst (tauZoo k) T .dupoc)) = true)
    (hnsX : ∀ k, noSelfIdxP (.bot (inst (tauZoo k) T .dupoc)) = true)
    (hB : ∃ kB : ℕ, ∀ (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (x : M), (kB : M) ≤ x →
      ∃ n, EvalGraph n (pBot (W.code x)) (pBot (W.code x)) (pBot (W.code x)) ((0 : ℕ) : M))
    (hBT : ∃ kB : ℕ, ∀ (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (x : M), (kB : M) ≤ x →
      ∃ n, EvalGraph n (pBot (W.tr.code x)) (pBot (W.tr.code x)) (pBot (W.tr.code x)) ((1 : ℕ) : M)) :
    bitEventually .dupoc T .C := by
  set K := W1.K with hKdef
  set c : ℕ := progCode (.bot (inst (tauZoo K) T .dupoc)) with hc
  have hcW : c = pBot (W.code K) := by rw [hc, ← hW K]
  have hg : ∀ k : ℕ, K ≤ k → templateAt (probe (inst (tauZoo k) T .dupoc)) (some k) = gPr K c := by
    intro k hk
    show templateAt (.plays (.bot (inst (tauZoo k) T .dupoc)) (.bot (inst (tauZoo k) T .dupoc)) .C) (some k) = gPr K c
    rw [templateAt_probe_eq k _ (hnsX k)]
    unfold gPr
    rw [← hW k, hcW, W1.closedDescAt_code W hk, W1.closedDescAt_code W le_rfl]
  have hg7 : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁], IsSemiformula LAct 7 ((⌜gPr K c⌝ : ℕ) : V) := by
    intro V _ _
    rw [← templateAt_probe_eq K _ (hnsX K)]
    exact isSemiformula7_cast_templateAt _ K (hnsF K) V
  obtain ⟨kB, hB⟩ := hB
  obtain ⟨kBT, hBT⟩ := hBT
  have hB' : ∃ kB : ℕ, ∀ (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (x : M), (kB : M) ≤ x →
      ∃ n, EvalGraph n (descVal W.TX W.uT W.wT x) (descVal W.TX W.uT W.wT x) (descVal W.TX W.uT W.wT x) ((0 : ℕ) : M) := by
    refine ⟨kB + K, fun M _ _ x hx ↦ ?_⟩
    have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    rw [W1.descVal_TX W (le_trans (by push_cast; exact le_add_self) hx)]
    exact hB M x (le_trans (by push_cast; exact le_self_add) hx)
  have hBT' : ∃ kB : ℕ, ∀ (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (x : M), (kB : M) ≤ x →
      ∃ n, EvalGraph n (descVal (Semiterm.lMap swap W.TX) (Semiterm.lMap swap W.uT) (Semiterm.lMap swap W.wT) x)
        (descVal (Semiterm.lMap swap W.TX) (Semiterm.lMap swap W.uT) (Semiterm.lMap swap W.wT) x)
        (descVal (Semiterm.lMap swap W.TX) (Semiterm.lMap swap W.uT) (Semiterm.lMap swap W.wT) x) ((1 : ℕ) : M) := by
    refine ⟨kBT + K, fun M _ _ x hx ↦ ?_⟩
    have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    rw [W1.descVal_TX_T W (le_trans (by push_cast; exact le_add_self) hx)]
    exact hBT M x (le_trans (by push_cast; exact le_self_add) hx)
  set sPr : SM := ⟨gPr K c, 0, Or.inl rfl⟩ with hsPr
  obtain ⟨kHat, hq⟩ := tact_qPr_above K c W.TX W.uT W.wT (by rw [hcW]; exact W1.habs W) (by rw [hcW]; exact W1.habsT W)
    hB' hBT' sPr.TB sPr.uT sPr.wT
  obtain ⟨k₀, h⟩ := plain_found_above (gPr K c) hg7 0 (Or.inl rfl) K kHat hq
  refine ⟨k₀, fun k hk ↦ ?_⟩
  obtain ⟨hK, hbox⟩ := h k hk
  have e1 : sPr.code k = instCode k .dupoc T := by
    rw [hI k]
    unfold SM.code
    simp only [hsPr, natCast_nat]
    show pSearch k (⌜gPr K c⌝ : ℕ) (pConst 0) (pConst (1 - 0)) =
      pSearch k (⌜templateAt (probe (inst (tauZoo k) T .dupoc)) (some k)⌝ : ℕ) (pConst 0) (pConst 1)
    rw [hg k hK]
  have e3 : (⌜gPr K c⌝ : ℕ) = templateCodeAt (probe (inst (tauZoo k) T .dupoc)) k := by
    show _ = (⌜templateAt (probe (inst (tauZoo k) T .dupoc)) (some k)⌝ : ℕ)
    rw [hg k hK]
  rw [e1, e3, guardCodeB_templateCodeAt _ _ _ _ (hnsF k), hI k] at hbox
  exact bitPlays_of_eq (hI k) ⟨_, search_then_at _ hbox (const_play 0 _ _ _) (hnsF k)⟩

/-! #### The plays of τ(TFTSim)'s instances at CIMCIC and at Dupoc -/

/-- τ(TFTSim)'s instance at CIMCIC cooperates with everyone above a threshold, in every model: CIMCIC's instance at
the cooperator finds its guard (`tact_qInst_implC`) and the watch copies the C. -/
theorem WtCi_plays_C : ∃ kB : ℕ, ∀ (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (x : M), (kB : M) ≤ x → ∀ me : M,
    ∃ n, EvalGraph n (pBot (WtCi.code x)) me (pBot (WtCi.code x)) ((0 : ℕ) : M) := by
  obtain ⟨kB, h⟩ := ofSearch_self_plays (implC .C .C .C) rfl .C (tact_qInst_implC .C .C 0)
  refine ⟨kB, fun M _ _ x hx me ↦ ?_⟩
  have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
  have h' : EvalGraph 3 (pBot (WtCi.s.code x)) (pBot (WtCi.s.code x)) (pBot (WtCi.s.code x)) (WtCi.t : M) := by
    have := h M x hx
    rwa [actCode_C] at this
  exact ⟨_, W1.bot_plays_then WtCi x h' (pBot (WtCi.code x)) me⟩

/-- …and its transposition defects against everyone. -/
theorem WtCi_tr_plays_D : ∃ kB : ℕ, ∀ (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (x : M), (kB : M) ≤ x → ∀ me : M,
    ∃ n, EvalGraph n (pBot (WtCi.tr.code x)) me (pBot (WtCi.tr.code x)) ((1 : ℕ) : M) := by
  obtain ⟨kB, h⟩ := ofSearch_tr_self_plays (implC .C .C .C) rfl rfl .C (tact_qInst_implC .D .D 1)
  refine ⟨kB, fun M _ _ x hx me ↦ ?_⟩
  have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
  have h' : EvalGraph 3 (pBot (WtCi.tr.s.code x)) (pBot (WtCi.tr.s.code x)) (pBot (WtCi.tr.s.code x)) (WtCi.tr.t : M) := by
    have := h M x hx
    rwa [actCode_C] at this
  exact ⟨_, W1.bot_plays_then WtCi.tr x h' (pBot (WtCi.tr.code x)) me⟩

/-- τ(TFTSim)'s instance at Dupoc cooperates with itself above a threshold (the closed probe of the frozen cooperator
is a theorem, `tact_qInst_prC`). -/
theorem WtDu_plays_C : ∃ kB : ℕ, ∀ (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (x : M), (kB : M) ≤ x →
    ∃ n, EvalGraph n (pBot (WtDu.code x)) (pBot (WtDu.code x)) (pBot (WtDu.code x)) ((0 : ℕ) : M) := by
  obtain ⟨kB, h⟩ := ofSearch_self_plays (prC .C .C) rfl .C (tact_qInst_prC .C 0)
  refine ⟨kB, fun M _ _ x hx ↦ ?_⟩
  have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
  have h' : EvalGraph 3 (pBot (WtDu.s.code x)) (pBot (WtDu.s.code x)) (pBot (WtDu.s.code x)) (WtDu.t : M) := by
    have := h M x hx
    rwa [actCode_C] at this
  exact ⟨_, W1.bot_plays_then WtDu x h' _ _⟩

theorem WtDu_tr_plays_D : ∃ kB : ℕ, ∀ (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (x : M), (kB : M) ≤ x →
    ∃ n, EvalGraph n (pBot (WtDu.tr.code x)) (pBot (WtDu.tr.code x)) (pBot (WtDu.tr.code x)) ((1 : ℕ) : M) := by
  obtain ⟨kB, h⟩ := ofSearch_tr_self_plays (prC .C .C) rfl rfl .C (tact_qInst_prC .D 1)
  refine ⟨kB, fun M _ _ x hx ↦ ?_⟩
  have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
  have h' : EvalGraph 3 (pBot (WtDu.tr.s.code x)) (pBot (WtDu.tr.s.code x)) (pBot (WtDu.tr.s.code x)) (WtDu.tr.t : M) := by
    have := h M x hx
    rwa [actCode_C] at this
  exact ⟨_, W1.bot_plays_then WtDu.tr x h' _ _⟩

theorem instCode_cimcic_tftSim' (k : ℕ) : instCode k .cimcic .tftSim =
    pSearch k (templateCodeAt (cimGf (inst (tauZoo k) .tftSim .cimcic)) k) (pConst 0) (pConst 1) := by
  unfold instCode; rw [inst_cimcic_peel_tftSim]; simp [actCode]

theorem instCode_dupoc_tftSim' (k : ℕ) : instCode k .dupoc .tftSim =
    pSearch k (templateCodeAt (probe (inst (tauZoo k) .tftSim .dupoc)) k) (pConst 0) (pConst 1) := by
  unfold instCode; rw [inst_dupoc_peel_tftSim]; simp [actCode]

/-- **`cimcic × tftSim` is C** — the table's value, recovered under budget abstraction. -/
theorem cimcic_tftSim_C : bitEventually .cimcic .tftSim .C :=
  cimcic_C_of_W1 .tftSim WtCi WtCi_code instCode_cimcic_tftSim' (fun _ ↦ rfl) (fun _ ↦ rfl) WtCi_plays_C WtCi_tr_plays_D

/-- **`dupoc × tftSim` is C**: Dupoc's probe of τ(TFTSim)'s instance is a true closed probe of a budget-carrying watch,
found by the `k̂`-chain. -/
theorem dupoc_tftSim_C : bitEventually .dupoc .tftSim .C :=
  dupoc_C_of_W1 .tftSim WtDu WtDu_code instCode_dupoc_tftSim' (fun _ ↦ rfl) (fun _ ↦ rfl) WtDu_plays_C WtDu_tr_plays_D

/-- The natives' `tftSim` slots are Dupoc's by the bridge. -/
theorem maxconfidence_tftSim_C : bitEventually .maxconfidence .tftSim .C :=
  bitEventually.mono (fun k h ↦
    (bitPlays_congr (instCode_maxconfidence_eq k .tftSim (by decide) (by decide) (by decide)) _).mpr h) dupoc_tftSim_C

theorem minconfidence_tftSim_C : bitEventually .minconfidence .tftSim .C :=
  bitEventually.mono (fun k h ↦
    (bitPlays_congr (instCode_minconfidence_eq k .tftSim (by decide) (by decide) (by decide) (by decide)) _).mpr h)
    dupoc_tftSim_C

end bits

end ArithS.Tau
