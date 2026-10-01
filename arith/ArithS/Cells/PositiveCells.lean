import ArithS.Cells.SoundnessCells
import ArithS.Cells.CIMCIC
import ArithS.Cells.JustBot
import ArithS.Cells.PrudentMirror

/-!
# ArithS.Cells.PositiveCells — the POS class of the census in PA-`S'`, and the unreadability cells re-evaluated

`Research/Notes/ROUTE_B_SCOPE.md` §3 Phase 4, class **POS** of `ROUTE_B_CENSUS.md`: cells whose
searcher FINDS its guard without Löb (the engine's `search_t` on a search-free atom, `weakenImpl`, `atomNeg`),
unconditional in `S'` (no `BoundedInnerNec`), for all large `k`. The mechanism is `pos_Cimcic_vs_Cimcic`'s, made
generic: the guard is the `binNumeral k`-instance of a FIXED one-variable formula `q` (`guardCode_qT_eq_instB` with
the searcher's description triple), `q(k)` is true in BOTH standard readings of every model, so `TAct ⊢ ∀¹ q`
by completeness (`tact_all_of_both`), and the instance at `binNumeral k` costs `K₀ + K₁·size k ≤ k` (`found_of_all`).

1. **The constant opponents** `pConst 0`, `pConst 1`, `pBot (pConst 0)`, `pBot (pConst 1)`: canonical codes,
   re-valuation terms, closed structural terms `T0`/`TB0`, the code hypotheses `hX_const_*`/`hU_*`/`hW_*` and the
   value equations `val_desc_*`.
2. **The generic engine-searcher description layer**: `SV g a k := pSearch k ⌜g⌝ (pConst a) (pConst (1 - a))`,
   `transposeCode_SV`, the canonical triple `canonical_SV`/`revalueU_SV`/`revalueW_SV` (`Cells/CIMCIC.lean` §2 with the template and
   branch as parameters), the tower `TS`, `hX_SV`, and the reconstructions `revalue_val_uS_wS_V`/`_uST_wST_V`.
   It puts the ENGINE codes `progCode (DupocBot k)`, `progCode (CupodBot k)`, `progCode (WaryBot k)` on the same footing as
   `Cimcic k`/`Dimcid k`; the bot tower `TBS` describes the frozen snapshot `pBot (progCode (DupocBot k))`, and
   `guardCode_JustBot_eq` shows Just's consulted guard IS Dupoc's engine guard in the snapshot's frame.
3. **The closure**: `tact_all_of_both`, `found_of_all`; the generic truth of a play-atom template instance in
   both triples (`eval_qT_plays_opp_self`, `eval_qT_neg_plays_opp_self`, `eval_qT_swap`), the plays of constants
   in every model and their negations by determinism (`const_play_V`, `bot_const_play_V`, `const_not_play_V`).
4. **The cells**: `pos_DupocBot_vs_CooperateBot` `(C, C)`, `pos_CupodBot_vs_DefectBot` `(D, D)`,
   `pos_CIMCIC_vs_CooperateBot` `(C, C)`, `pos_DIMCID_vs_DefectBot` `(D, D)`, `pos_JustBot_vs_CooperateBot` `(C, C)`
   (on the engine's own code), `pos_WaryBot_vs_DefectBot` `(D, D)` (the `.neg` guard is a Π₁ truth by
   determinism — the `S'` twin of `Pf.atomNeg`), and the SND cells whose positive sub-fact is the searcher finding
   its guard against `.bot DefectBot`: `pos_CupodBot_vs_DBot`/`_EBot` and `pos_WaryBot_vs_DBot`/`_EBot`, all `(C, C)`.
5. **The unreadability cells re-evaluated** (census classes FLOOR(cenU)/OTHER, where PA reads every source):
   * CIMCIC's guard against an opponent that defects against it is SELF-REFUTING (found ⇒ CIMCIC cooperates ⇒ by
     soundness the opponent cooperates — against the fact): `cimcic_selfref_not_found`, so
     `snd_CIMCIC_vs_DefectBot` `(D, D)` at EVERY `k` and `snd_CIMCIC_vs_OBot` `(D, D)` for large `k` keep the
     engine's values by soundness instead of the unreadability census.
   * **DIMCID × CooperateBot FLIPS**: the engine's `(C, C)` becomes `(D, C)` — DIMCID's guard "I play C against
     CooperateBot ⇒ CooperateBot plays D against me" has a false consequent, so it says "I do not cooperate"; a
     proof of it makes DIMCID defect, which makes it TRUE, and bounded Löb (`family_found` on the family
     `pG (cl T0) (cterm C) (cterm D)`, `loebSound_pDi0`) finds it: `loeb_DIMCID_vs_CooperateBot`.

Conventions: every threshold EXISTENTIAL; `simp` never sees a closed quote (`innerS` is irreducible); `omega` is
never asked about `V`; `≤` at ℕ bridged by `le_def`.
-/

set_option linter.constructorNameAsVariable false

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open LAct
open PD.Bots

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ### 1. The constant opponents: `pConst 0`, `pConst 1`, `pBot (pConst 0)`, `pBot (pConst 1)` -/

section constants


end constants

/-! ### 2. The generic engine searcher `pSearch k ⌜g⌝ (pConst a) (pConst (1 - a))` and its description -/

section searcher


end searcher

/-! ### 3. From `TAct ⊢ ∀¹ q` to "found at every large `k`" -/

section closure


end closure

/-! ### 4. The truth of a play-atom template instance, generic in both triples -/

section truth


end truth

/-! ### 5. The engine searchers as `SV` instances, and the bot-wrapped snapshot -/

section instances


lemma progCode_DupocBot_SV (k : ℕ) : progCode (DupocBot k) = SV (V := ℕ) gDu 0 k := by
  rw [progCode_DupocBot_search, SV_nat, templateCode_eq_quote_template phiDu rfl]; rfl
lemma progCode_CupodBot_SV (k : ℕ) : progCode (CupodBot k) = SV (V := ℕ) gCu 1 k := by
  rw [progCode_CupodBot, SV_nat, templateCode_eq_quote_template phiCu rfl]; rfl
lemma progCode_WaryBot_SV (k : ℕ) : progCode (WaryBot k) = SV (V := ℕ) gW 1 k := by
  rw [progCode_WaryBot, SV_nat, templateCode_eq_quote_template phiW rfl]; rfl


/-- Just's consulted guard against `opp` is Dupoc's engine guard in the frame `(.bot (DupocBot k), opp)`
(both are the template code of "`opp` plays C against `.bot (DupocBot k)`"). -/
lemma guardCode_JustBot_eq (k : ℕ) {opp : PD.Prog} (hopp : ProperPlayer opp) (hopp' : noSelfIdxP opp = true := by noSelfIdx_tac) :
    guardCode (templateCode (phiJ k)) (progCode (JustBot k)) (progCode opp) =
      guardCode (templateCode phiDu) (pBot (progCode (DupocBot k))) (progCode opp) := by
  rw [← progCode_bot]
  change guardOf (phiJ k) (JustBot k) opp = guardOf phiDu (.bot (DupocBot k)) opp
  rw [guardOf_eq_templateCode_subst (properPlayer_JustBot k) hopp _ rfl, guardOf_eq_templateCode_subst (properPlayer_bot _) hopp _ rfl]
  rfl

end instances

/-! ### 6. The cells -/

section cells

lemma actCode_C_cast : ((actCode .C : ℕ) : V) = 0 := by simp [actCode]
lemma actCode_D_cast : ((actCode .D : ℕ) : V) = 1 := by simp [actCode]

/-! #### DupocBot × CooperateBot `(C, C)` -/

/-- Dupoc's guard against CooperateBot as a fixed formula: "CooperateBot plays C against Dupoc(k)". -/
noncomputable def qDu0 : Semisentence LAct 1 :=
  qT gDu (TS gDu 0) (uS gDu 0) (wS gDu 0) (cl T0) (cterm Act.C) (cterm Act.D)

theorem guardCode_Du0 (k : V) : guardCode (⌜gDu⌝ : V) (SV gDu 0 k) (pConst 0) = instB (⌜qDu0⌝ : V) k :=
  guardCode_qT_eq_instB gDu k _ _ _ _ _ _ (hX_SV gDu 0 (Or.inl rfl) k) (hU_SV gDu 0 (Or.inl rfl) k)
    (hW_SV gDu 0 (Or.inl rfl) k) (hX_const_zero k) hU_C_zero hW_D_zero

theorem tact_qDu0 : TAct ⊢ ∀¹ qDu0 := by
  refine tact_all_of_both _ (fun M _ _ x ↦ ?_) (fun M _ _ x ↦ ?_)
  · have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    rw [qDu0, eval_qT_plays_opp_self .C _ _ _ _ _ _ x (desc_SV gDu 0 (Or.inl rfl) x) (val_desc_const_zero x),
      actCode_C_cast]
    exact const_play_V _ _ _
  · have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    rw [qDu0, eval_qT_swap, lMap_swap_gDu, lMap_swap_cl, lMap_swap_T0, lMap_swap_cterm_C, lMap_swap_cterm_D,
      eval_qT_plays_opp_self .D _ _ _ _ _ _ x (descT_SV gDu 0 (Or.inl rfl) x) (val_desc_const_one x),
      actCode_D_cast]
    exact const_play_V _ _ _

/-- `DupocBot × CooperateBot = (C, C)` (engine `outcome_DupocBot_vs_CooperateBot`, pad 2), for all large `k`:
the guard "CooperateBot plays C against me" is a `TAct`-theorem in `k` (`tact_qDu0`), found within the
budget for all large `k` (`found_of_all`). -/
theorem pos_DupocBot_vs_CooperateBot :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 2 (progCode (DupocBot k)) (progCode CooperateBot) (progCode (DupocBot k)) (actCode .C) ∧
      EvalGraph 2 (progCode CooperateBot) (progCode (DupocBot k)) (progCode CooperateBot) (actCode .C) := by
  obtain ⟨k₀, h⟩ := found_of_all tact_qDu0
    (fun k ↦ guardCode (templateCode phiDu) (progCode (DupocBot k)) (progCode CooperateBot))
    (fun k ↦ by rw [progCode_CB, progCode_DupocBot_SV, templateCode_eq_quote_template phiDu rfl]; exact guardCode_Du0 (V := ℕ) k)
  refine ⟨k₀, fun k hk ↦ ⟨?_, by rw [progCode_CB]; exact const_play 1 _ _ _⟩⟩
  have hg := h k hk
  rw [progCode_DupocBot_search] at hg ⊢
  exact search_then phiDu hg (const_play _ _ _ _)

/-! #### CupodBot × DefectBot `(D, D)`, and Cupod's positive guard against `.bot DefectBot` -/

/-- Cupod's guard against DefectBot: "DefectBot plays D against Cupod(k)". -/
noncomputable def qCu1 : Semisentence LAct 1 :=
  qT gCu (TS gCu 1) (uS gCu 1) (wS gCu 1) (cl T0) (cterm Act.D) (cterm Act.C)

theorem guardCode_Cu1 (k : V) : guardCode (⌜gCu⌝ : V) (SV gCu 1 k) (pConst 1) = instB (⌜qCu1⌝ : V) k :=
  guardCode_qT_eq_instB gCu k _ _ _ _ _ _ (hX_SV gCu 1 (Or.inr rfl) k) (hU_SV gCu 1 (Or.inr rfl) k)
    (hW_SV gCu 1 (Or.inr rfl) k) (hX_const_one k) hU_D_one hW_C_one

theorem tact_qCu1 : TAct ⊢ ∀¹ qCu1 := by
  refine tact_all_of_both _ (fun M _ _ x ↦ ?_) (fun M _ _ x ↦ ?_)
  · have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    rw [qCu1, eval_qT_plays_opp_self .D _ _ _ _ _ _ x (desc_SV gCu 1 (Or.inr rfl) x) (val_desc_const_one x),
      actCode_D_cast]
    exact const_play_V _ _ _
  · have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    rw [qCu1, eval_qT_swap, lMap_swap_gCu, lMap_swap_cl, lMap_swap_T0, lMap_swap_cterm_C, lMap_swap_cterm_D,
      eval_qT_plays_opp_self .C _ _ _ _ _ _ x (descT_SV gCu 1 (Or.inr rfl) x) (val_desc_const_zero x),
      actCode_C_cast]
    exact const_play_V _ _ _

/-- `CupodBot × DefectBot = (D, D)` (engine `outcome_CupodBot_vs_DefectBot`, pad 2), for all large `k`. -/
theorem pos_CupodBot_vs_DefectBot :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 2 (progCode (CupodBot k)) (progCode DefectBot) (progCode (CupodBot k)) (actCode .D) ∧
      EvalGraph 2 (progCode DefectBot) (progCode (CupodBot k)) (progCode DefectBot) (actCode .D) := by
  obtain ⟨k₀, h⟩ := found_of_all tact_qCu1
    (fun k ↦ guardCode (templateCode phiCu) (progCode (CupodBot k)) (progCode DefectBot))
    (fun k ↦ by rw [progCode_DB, progCode_CupodBot_SV, templateCode_eq_quote_template phiCu rfl]; exact guardCode_Cu1 (V := ℕ) k)
  refine ⟨k₀, fun k hk ↦ ⟨?_, by rw [progCode_DB]; exact const_play 1 _ _ _⟩⟩
  have hg := h k hk
  rw [progCode_CupodBot] at hg ⊢
  exact search_then phiCu hg (const_play _ _ _ _)

/-- Cupod's guard against `.bot DefectBot`: "`.bot DefectBot` plays D against Cupod(k)". -/
noncomputable def qCuB1 : Semisentence LAct 1 :=
  qT gCu (TS gCu 1) (uS gCu 1) (wS gCu 1) (cl TB0) (cterm Act.D) (cterm Act.C)

theorem guardCode_CuB1 (k : V) :
    guardCode (⌜gCu⌝ : V) (SV gCu 1 k) (pBot (pConst 1)) = instB (⌜qCuB1⌝ : V) k :=
  guardCode_qT_eq_instB gCu k _ _ _ _ _ _ (hX_SV gCu 1 (Or.inr rfl) k) (hU_SV gCu 1 (Or.inr rfl) k)
    (hW_SV gCu 1 (Or.inr rfl) k) (hX_bot_one k) hU_D_bot_one hW_C_bot_one

theorem tact_qCuB1 : TAct ⊢ ∀¹ qCuB1 := by
  refine tact_all_of_both _ (fun M _ _ x ↦ ?_) (fun M _ _ x ↦ ?_)
  · have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    rw [qCuB1, eval_qT_plays_opp_self .D _ _ _ _ _ _ x (desc_SV gCu 1 (Or.inr rfl) x) (val_desc_bot_one x),
      actCode_D_cast]
    exact bot_const_play_V _ _ _
  · have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    rw [qCuB1, eval_qT_swap, lMap_swap_gCu, lMap_swap_cl, lMap_swap_TB0, lMap_swap_cterm_C, lMap_swap_cterm_D,
      eval_qT_plays_opp_self .C _ _ _ _ _ _ x (descT_SV gCu 1 (Or.inr rfl) x) (val_desc_bot_zero x),
      actCode_C_cast]
    exact bot_const_play_V _ _ _

/-- Cupod defects against `.bot DefectBot` for all large `k` (its guard is found). -/
theorem pos_CupodBot_vs_botDB :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k → EvalGraph 2 (progCode (CupodBot k)) (pBot (pConst 1)) (progCode (CupodBot k)) 1 := by
  obtain ⟨k₀, h⟩ := found_of_all tact_qCuB1
    (fun k ↦ guardCode (templateCode phiCu) (progCode (CupodBot k)) (pBot (pConst 1)))
    (fun k ↦ by rw [progCode_CupodBot_SV, templateCode_eq_quote_template phiCu rfl]; exact guardCode_CuB1 (V := ℕ) k)
  refine ⟨k₀, fun k hk ↦ ?_⟩
  have hg := h k hk
  rw [progCode_CupodBot] at hg ⊢
  exact search_then phiCu hg (const_play _ _ _ _)

/-- `CupodBot × DBot = (C, C)` (engine `outcome_CupodBot_vs_DBot`, pad 4), for all large `k`: DBot sees Cupod
defect against `.bot DefectBot` (found) and cooperates; Cupod's guard against DBot is then false. -/
theorem pos_CupodBot_vs_DBot :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 4 (progCode (CupodBot k)) (progCode DBot) (progCode (CupodBot k)) (actCode .C) ∧
      EvalGraph 4 (progCode DBot) (progCode (CupodBot k)) (progCode DBot) (actCode .C) := by
  obtain ⟨k₀, h⟩ := pos_CupodBot_vs_botDB
  refine ⟨k₀, fun k hk ↦ ?_⟩
  have hD := dbot_C_of_probe_D (h k hk)
  exact ⟨EvalGraph.mono_le (by omega) (cupod_C_of_probe k sfp_DBot.1 hD), hD⟩

/-- `CupodBot × EBot = (C, C)` (engine `outcome_CupodBot_vs_EBot`, pad 5), for all large `k`. -/
theorem pos_CupodBot_vs_EBot :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 5 (progCode (CupodBot k)) (progCode EBot) (progCode (CupodBot k)) (actCode .C) ∧
      EvalGraph 5 (progCode EBot) (progCode (CupodBot k)) (progCode EBot) (actCode .C) := by
  obtain ⟨k₀, h⟩ := pos_CupodBot_vs_botDB
  refine ⟨k₀, fun k hk ↦ ?_⟩
  have hE := ebot_C_of_probes (h k hk) (snd_CupodBot_vs_botCB k)
  exact ⟨EvalGraph.mono_le (by omega) (cupod_C_of_probe k sfp_EBot.1 hE), hE⟩

/-! #### CIMCIC × CooperateBot `(C, C)` -/

/-- CIMCIC's guard against CooperateBot: "I play C against CooperateBot ⇒ CooperateBot plays C against me". -/
noncomputable def qCi0 : Semisentence LAct 1 := qCG (cl T0) (cterm Act.C) (cterm Act.D)

theorem guardCode_Ci0 (k : V) : guardCode (⌜templateC⌝ : V) (CimcicV k) (pConst 0) = instB (⌜qCi0⌝ : V) k :=
  guardCode_CimcicV_eq_instB k (cl T0) _ _ (hX_const_zero k) hU_C_zero hW_D_zero

theorem tact_qCi0 : TAct ⊢ ∀¹ qCi0 := by
  refine tact_all_of_both _ (fun M _ _ x ↦ ?_) (fun M _ _ x ↦ ?_)
  · have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    rw [qCi0, eval_qCG_iff_V x _ _ _ (val_desc_const_zero x)]
    exact fun _ ↦ const_play_V _ _ _
  · have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    rw [qCi0, eval_qCG_swap_iff_V, lMap_swap_cl, lMap_swap_T0, lMap_swap_cterm_C, lMap_swap_cterm_D,
      eval_qCTG_iff_V x _ _ _ (val_desc_const_one x)]
    exact fun _ ↦ const_play_V _ _ _

/-- `CIMCIC × CooperateBot = (C, C)` (engine `outcome_CIMCIC_vs_CooperateBot`, pad 2), for all large `k`
(the engine's `weakenImpl`: the consequent is a closed true atom). -/
theorem pos_CIMCIC_vs_CooperateBot :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 2 (progCode (CIMCIC k)) (progCode CooperateBot) (progCode (CIMCIC k)) (actCode .C) ∧
      EvalGraph 2 (progCode CooperateBot) (progCode (CIMCIC k)) (progCode CooperateBot) (actCode .C) := by
  obtain ⟨k₀, h⟩ := found_of_all tact_qCi0
    (fun k ↦ guardCode (⌜templateC⌝ : ℕ) (Cimcic k) (pConst 0)) (fun k ↦ guardCode_Ci0 (V := ℕ) k)
  refine ⟨k₀, fun k hk ↦ ⟨?_, by rw [progCode_CB]; exact const_play 1 _ _ _⟩⟩
  rw [progCode_CIMCIC, progCode_CB]
  exact cimcic_search_V (V := ℕ) k (pConst 0) (h k hk)

/-! #### DIMCID × DefectBot `(D, D)` -/

/-- DIMCID's guard against DefectBot: "I play C against DefectBot ⇒ DefectBot plays D against me". -/
noncomputable def qDi1 : Semisentence LAct 1 := qDG (cl T0) (cterm Act.D) (cterm Act.C)

theorem guardCode_Di1 (k : V) : guardCode (⌜templateD⌝ : V) (DimcidV k) (pConst 1) = instB (⌜qDi1⌝ : V) k :=
  guardCode_DimcidV_eq_instB k (cl T0) _ _ (hX_const_one k) hU_D_one hW_C_one

theorem tact_qDi1 : TAct ⊢ ∀¹ qDi1 := by
  refine tact_all_of_both _ (fun M _ _ x ↦ ?_) (fun M _ _ x ↦ ?_)
  · have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    rw [qDi1, eval_qDG_iff_V x _ _ _ (val_desc_const_one x)]
    exact fun _ ↦ const_play_V _ _ _
  · have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    rw [qDi1, eval_qDG_swap_iff_V, lMap_swap_cl, lMap_swap_T0, lMap_swap_cterm_C, lMap_swap_cterm_D,
      eval_qTG_iff_V x _ _ _ (val_desc_const_zero x)]
    exact fun _ ↦ const_play_V _ _ _

/-- `DIMCID × DefectBot = (D, D)` (engine `outcome_DIMCID_vs_DefectBot`, pad 2), for all large `k`. -/
theorem pos_DIMCID_vs_DefectBot :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 2 (progCode (DIMCID k)) (progCode DefectBot) (progCode (DIMCID k)) (actCode .D) ∧
      EvalGraph 2 (progCode DefectBot) (progCode (DIMCID k)) (progCode DefectBot) (actCode .D) := by
  obtain ⟨k₀, h⟩ := found_of_all tact_qDi1
    (fun k ↦ guardCode (⌜templateD⌝ : ℕ) (Dimcid k) (pConst 1)) (fun k ↦ guardCode_Di1 (V := ℕ) k)
  refine ⟨k₀, fun k hk ↦ ⟨?_, by rw [progCode_DB]; exact const_play 1 _ _ _⟩⟩
  rw [progCode_DIMCID, progCode_DB]
  exact dimcid_search_V (V := ℕ) k (pConst 1) (h k hk)

/-! #### JustBot × CooperateBot `(C, C)`, on the engine's own code -/

/-- Just's guard against CooperateBot: "CooperateBot plays C against the frozen `.bot (DupocBot k)`". -/
noncomputable def qJ0 : Semisentence LAct 1 :=
  qT gDu (TBS gDu 0) (uS gDu 0) (wS gDu 0) (cl T0) (cterm Act.C) (cterm Act.D)

theorem guardCode_J0 (k : V) : guardCode (⌜gDu⌝ : V) (pBot (SV gDu 0 k)) (pConst 0) = instB (⌜qJ0⌝ : V) k :=
  guardCode_qT_eq_instB gDu k _ _ _ _ _ _ (termSubst_TBS gDu 0 (Or.inl rfl) k) (hU_botSV gDu 0 (Or.inl rfl) k)
    (hW_botSV gDu 0 (Or.inl rfl) k) (hX_const_zero k) hU_C_zero hW_D_zero

theorem tact_qJ0 : TAct ⊢ ∀¹ qJ0 := by
  refine tact_all_of_both _ (fun M _ _ x ↦ ?_) (fun M _ _ x ↦ ?_)
  · have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    rw [qJ0, eval_qT_plays_opp_self .C _ _ _ _ _ _ x (desc_botSV gDu 0 (Or.inl rfl) x) (val_desc_const_zero x),
      actCode_C_cast]
    exact const_play_V _ _ _
  · have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    rw [qJ0, eval_qT_swap, lMap_swap_gDu, lMap_swap_cl, lMap_swap_T0, lMap_swap_cterm_C, lMap_swap_cterm_D,
      eval_qT_plays_opp_self .D _ _ _ _ _ _ x (descT_botSV gDu 0 (Or.inl rfl) x) (val_desc_const_one x),
      actCode_D_cast]
    exact const_play_V _ _ _

/-- `JustBot × CooperateBot = (C, C)` (engine `outcome_JustBot_vs_CooperateBot`, pad 2), for all large `k`, on the
engine's own code `progCode (JustBot k)`: the consulted guard is Dupoc's engine guard in the frame of the frozen
snapshot (`guardCode_JustBot_eq`), the `binNumeral k`-instance of `qJ0` through the bot tower `TBS`. -/
theorem pos_JustBot_vs_CooperateBot :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 2 (progCode (JustBot k)) (progCode CooperateBot) (progCode (JustBot k)) (actCode .C) ∧
      EvalGraph 2 (progCode CooperateBot) (progCode (JustBot k)) (progCode CooperateBot) (actCode .C) := by
  obtain ⟨k₀, h⟩ := found_of_all tact_qJ0
    (fun k ↦ guardCode (templateCode (phiJ k)) (progCode (JustBot k)) (progCode CooperateBot))
    (fun k ↦ by
      rw [guardCode_JustBot_eq k sfp_CooperateBot.1, progCode_CB, progCode_DupocBot_SV, templateCode_eq_quote_template phiDu rfl]
      exact guardCode_J0 (V := ℕ) k)
  refine ⟨k₀, fun k hk ↦ ⟨?_, by rw [progCode_CB]; exact const_play 1 _ _ _⟩⟩
  have hg := h k hk
  rw [progCode_JustBot] at hg ⊢
  exact search_then_at (phiJ k) hg (const_play _ _ _ _)

/-! #### WaryBot × DefectBot `(D, D)`, and Wary's positive `.neg` guard against `.bot DefectBot` -/

/-- Wary's guard against DefectBot: "DefectBot does NOT play C against Wary(k)". -/
noncomputable def qW1 : Semisentence LAct 1 :=
  qT gW (TS gW 1) (uS gW 1) (wS gW 1) (cl T0) (cterm Act.D) (cterm Act.C)

theorem guardCode_W1 (k : V) : guardCode (⌜gW⌝ : V) (SV gW 1 k) (pConst 1) = instB (⌜qW1⌝ : V) k :=
  guardCode_qT_eq_instB gW k _ _ _ _ _ _ (hX_SV gW 1 (Or.inr rfl) k) (hU_SV gW 1 (Or.inr rfl) k)
    (hW_SV gW 1 (Or.inr rfl) k) (hX_const_one k) hU_D_one hW_C_one

theorem tact_qW1 : TAct ⊢ ∀¹ qW1 := by
  refine tact_all_of_both _ (fun M _ _ x ↦ ?_) (fun M _ _ x ↦ ?_)
  · have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    rw [qW1, eval_qT_neg_plays_opp_self .C _ _ _ _ _ _ x (desc_SV gW 1 (Or.inr rfl) x) (val_desc_const_one x),
      actCode_C_cast]
    exact const_not_play_V _ _ _root_.one_ne_zero
  · have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    rw [qW1, eval_qT_swap, lMap_swap_gW, lMap_swap_cl, lMap_swap_T0, lMap_swap_cterm_C, lMap_swap_cterm_D,
      eval_qT_neg_plays_opp_self .D _ _ _ _ _ _ x (descT_SV gW 1 (Or.inr rfl) x) (val_desc_const_zero x),
      actCode_D_cast]
    exact const_not_play_V _ _ _root_.zero_ne_one

/-- `WaryBot × DefectBot = (D, D)` (engine `outcome_WaryBot_vs_DefectBot`, pad 2), for all large `k`: the `.neg`
guard "DefectBot does not cooperate with me" is a Π₁ truth in every model (determinism), a `TAct`-theorem
in `k`, found within the budget (the `S'` twin of the engine's `Pf.atomNeg`). -/
theorem pos_WaryBot_vs_DefectBot :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 2 (progCode (WaryBot k)) (progCode DefectBot) (progCode (WaryBot k)) (actCode .D) ∧
      EvalGraph 2 (progCode DefectBot) (progCode (WaryBot k)) (progCode DefectBot) (actCode .D) := by
  obtain ⟨k₀, h⟩ := found_of_all tact_qW1
    (fun k ↦ guardCode (templateCode phiW) (progCode (WaryBot k)) (progCode DefectBot))
    (fun k ↦ by rw [progCode_DB, progCode_WaryBot_SV, templateCode_eq_quote_template phiW rfl]; exact guardCode_W1 (V := ℕ) k)
  refine ⟨k₀, fun k hk ↦ ⟨?_, by rw [progCode_DB]; exact const_play 1 _ _ _⟩⟩
  have hg := h k hk
  rw [progCode_WaryBot] at hg ⊢
  exact search_then phiW hg (const_play _ _ _ _)

/-- Wary's guard against `.bot DefectBot`: "`.bot DefectBot` does NOT play C against Wary(k)". -/
noncomputable def qWB1 : Semisentence LAct 1 :=
  qT gW (TS gW 1) (uS gW 1) (wS gW 1) (cl TB0) (cterm Act.D) (cterm Act.C)

theorem guardCode_WB1 (k : V) : guardCode (⌜gW⌝ : V) (SV gW 1 k) (pBot (pConst 1)) = instB (⌜qWB1⌝ : V) k :=
  guardCode_qT_eq_instB gW k _ _ _ _ _ _ (hX_SV gW 1 (Or.inr rfl) k) (hU_SV gW 1 (Or.inr rfl) k)
    (hW_SV gW 1 (Or.inr rfl) k) (hX_bot_one k) hU_D_bot_one hW_C_bot_one

theorem tact_qWB1 : TAct ⊢ ∀¹ qWB1 := by
  refine tact_all_of_both _ (fun M _ _ x ↦ ?_) (fun M _ _ x ↦ ?_)
  · have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    rw [qWB1, eval_qT_neg_plays_opp_self .C _ _ _ _ _ _ x (desc_SV gW 1 (Or.inr rfl) x) (val_desc_bot_one x),
      actCode_C_cast]
    exact bot_const_not_play_V _ _ _root_.one_ne_zero
  · have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    rw [qWB1, eval_qT_swap, lMap_swap_gW, lMap_swap_cl, lMap_swap_TB0, lMap_swap_cterm_C, lMap_swap_cterm_D,
      eval_qT_neg_plays_opp_self .D _ _ _ _ _ _ x (descT_SV gW 1 (Or.inr rfl) x) (val_desc_bot_zero x),
      actCode_D_cast]
    exact bot_const_not_play_V _ _ _root_.zero_ne_one

/-- Wary defects against `.bot DefectBot` for all large `k` (its `.neg` guard is found). -/
theorem pos_WaryBot_vs_botDB :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k → EvalGraph 2 (progCode (WaryBot k)) (pBot (pConst 1)) (progCode (WaryBot k)) 1 := by
  obtain ⟨k₀, h⟩ := found_of_all tact_qWB1
    (fun k ↦ guardCode (templateCode phiW) (progCode (WaryBot k)) (pBot (pConst 1)))
    (fun k ↦ by rw [progCode_WaryBot_SV, templateCode_eq_quote_template phiW rfl]; exact guardCode_WB1 (V := ℕ) k)
  refine ⟨k₀, fun k hk ↦ ?_⟩
  have hg := h k hk
  rw [progCode_WaryBot] at hg ⊢
  exact search_then phiW hg (const_play _ _ _ _)

/-- `WaryBot × DBot = (C, C)` (engine `outcome_WaryBot_vs_DBot`, pad 4), for all large `k`. -/
theorem pos_WaryBot_vs_DBot :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 4 (progCode (WaryBot k)) (progCode DBot) (progCode (WaryBot k)) (actCode .C) ∧
      EvalGraph 4 (progCode DBot) (progCode (WaryBot k)) (progCode DBot) (actCode .C) := by
  obtain ⟨k₀, h⟩ := pos_WaryBot_vs_botDB
  refine ⟨k₀, fun k hk ↦ ?_⟩
  have hD := dbot_C_of_probe_D (h k hk)
  exact ⟨EvalGraph.mono_le (by omega) (wary_C_of_probe k sfp_DBot.1 hD), hD⟩

/-- `WaryBot × EBot = (C, C)` (engine `outcome_WaryBot_vs_EBot`, pad 5), for all large `k`. -/
theorem pos_WaryBot_vs_EBot :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 5 (progCode (WaryBot k)) (progCode EBot) (progCode (WaryBot k)) (actCode .C) ∧
      EvalGraph 5 (progCode EBot) (progCode (WaryBot k)) (progCode EBot) (actCode .C) := by
  obtain ⟨k₀, h⟩ := pos_WaryBot_vs_botDB
  refine ⟨k₀, fun k hk ↦ ?_⟩
  have hE := ebot_C_of_probes (h k hk) (snd_WaryBot_vs_botCB k)
  exact ⟨EvalGraph.mono_le (by omega) (wary_C_of_probe k sfp_EBot.1 hE), hE⟩

end cells

/-! ### 7. The UNREADABILITY cells re-evaluated in `S'` (census class FLOOR(cenU)/OTHER) -/

section unreadability

lemma progCode_CIMCIC_search (k : ℕ) : progCode (CIMCIC k) = pSearch k (templateCode phiC) (pConst 0) (pConst 1) := by
  rw [CIMCIC, progCode_search_noSnap _ _ _ _ rfl]; simp [phiC, actCode]
lemma properPlayer_CIMCIC (k : ℕ) : ProperPlayer (CIMCIC k) := ⟨by simp [CIMCIC], by simp [CIMCIC]⟩

/-- **CIMCIC's guard against an opponent that defects against it is SELF-REFUTING**: a proof of
"I play C against `opp` ⇒ `opp` plays C against me" makes CIMCIC cooperate, so by soundness `opp`
cooperates — against the fact. So it is never found (the red cell's argument, one level up). -/
theorem cimcic_selfref_not_found (k : ℕ) {opp : PD.Prog} (hopp : ProperPlayer opp) {N : ℕ}
    (h : EvalGraph N (progCode opp) (progCode (CIMCIC k)) (progCode opp) 1) :
    ¬ LenBox TAct k (guardCode (templateCode phiC) (progCode (CIMCIC k)) (progCode opp)) := by
  intro hf
  have hC : EvalGraph 2 (progCode (CIMCIC k)) (progCode opp) (progCode (CIMCIC k)) 0 := by
    rw [progCode_CIMCIC_search] at hf ⊢
    exact search_then phiC hf (const_play _ _ _ _)
  have hT : ℕ↓[LAct] ⊧ sentenceAt (CIMCIC k) opp phiC :=
    models_sentenceAt_of_lenBox (φ := phiC) (me := CIMCIC k) (opp := opp) hf
  rw [← sentenceAt_subst (CIMCIC k) opp (properPlayer_CIMCIC k) hopp phiC rfl] at hT
  change ℕ↓[LAct] ⊧ sentenceAt (CIMCIC k) opp (.impl (.plays (CIMCIC k) opp .C) (.plays opp (CIMCIC k) .C)) at hT
  rw [models_sentenceAt_impl, models_sentenceAt_plays _ _ _ _ _ (properPlayer_CIMCIC k) hopp,
    models_sentenceAt_plays _ _ _ _ _ hopp (properPlayer_CIMCIC k)] at hT
  obtain ⟨N', hN'⟩ := hT ⟨2, hC⟩
  exact absurd (EvalGraph.unique' hN' h) (by decide)

/-- `CIMCIC × DefectBot = (D, D)` (engine `outcome_CIMCIC_vs_DefectBot`, pad 2) at EVERY `k`: in `S'` the
guard is true but self-refuting, hence never found — the census's unreadability argument replaced by
soundness. -/
theorem snd_CIMCIC_vs_DefectBot (k : ℕ) :
    EvalGraph 2 (progCode (CIMCIC k)) (progCode DefectBot) (progCode (CIMCIC k)) (actCode .D) ∧
    EvalGraph 2 (progCode DefectBot) (progCode (CIMCIC k)) (progCode DefectBot) (actCode .D) := by
  have hn := cimcic_selfref_not_found k sfp_DefectBot.1 (N := 1) (by rw [progCode_DB]; exact const_play 0 _ _ _)
  rw [progCode_CIMCIC_search] at hn ⊢
  exact ⟨search_else phiC hn (const_play _ _ _ _), by rw [progCode_DB]; exact const_play 1 _ _ _⟩

/-- CIMCIC defects against `.bot DefectBot` at every `k` (self-refuting guard). -/
theorem snd_CIMCIC_vs_botDB (k : ℕ) :
    EvalGraph 2 (progCode (CIMCIC k)) (pBot (pConst 1)) (progCode (CIMCIC k)) 1 := by
  have hn := cimcic_selfref_not_found k (opp := .bot DefectBot) properPlayer_botDB (N := 2)
    (by rw [progCode_botDB]; exact bot_const_play 0 _ _ _)
  rw [progCode_botDB] at hn
  rw [progCode_CIMCIC_search] at hn ⊢
  exact search_else phiC hn (const_play _ _ _ _)

/-- CIMCIC's guard against `.bot CooperateBot`: the consequent "`.bot CooperateBot` plays C against me" is
a closed truth, so the implication is a `TAct`-theorem in `k`. -/
noncomputable def qCiB0 : Semisentence LAct 1 := qCG (cl TB0) (cterm Act.C) (cterm Act.D)

theorem guardCode_CiB0 (k : V) :
    guardCode (⌜templateC⌝ : V) (CimcicV k) (pBot (pConst 0)) = instB (⌜qCiB0⌝ : V) k :=
  guardCode_CimcicV_eq_instB k (cl TB0) _ _ (hX_bot_zero k) hU_C_bot_zero hW_D_bot_zero

theorem tact_qCiB0 : TAct ⊢ ∀¹ qCiB0 := by
  refine tact_all_of_both _ (fun M _ _ x ↦ ?_) (fun M _ _ x ↦ ?_)
  · have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    rw [qCiB0, eval_qCG_iff_V x _ _ _ (val_desc_bot_zero x)]
    exact fun _ ↦ bot_const_play_V _ _ _
  · have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    rw [qCiB0, eval_qCG_swap_iff_V, lMap_swap_cl, lMap_swap_TB0, lMap_swap_cterm_C, lMap_swap_cterm_D,
      eval_qCTG_iff_V x _ _ _ (val_desc_bot_one x)]
    exact fun _ ↦ bot_const_play_V _ _ _

/-- CIMCIC cooperates with `.bot CooperateBot` for all large `k` (its guard is found). -/
theorem pos_CIMCIC_vs_botCB :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k → EvalGraph 2 (progCode (CIMCIC k)) (pBot (pConst 0)) (progCode (CIMCIC k)) 0 := by
  obtain ⟨k₀, h⟩ := found_of_all tact_qCiB0
    (fun k ↦ guardCode (⌜templateC⌝ : ℕ) (Cimcic k) (pBot (pConst 0))) (fun k ↦ guardCode_CiB0 (V := ℕ) k)
  refine ⟨k₀, fun k hk ↦ ?_⟩
  rw [progCode_CIMCIC]
  exact cimcic_search_V (V := ℕ) k (pBot (pConst 0)) (h k hk)

/-- `CIMCIC × OBot = (D, D)` (engine `outcome_CIMCIC_vs_OBot`, pad 5) for all large `k`: OBot sees CIMCIC
cooperate with `.bot CooperateBot` (found) but defect against `.bot DefectBot` (self-refuting), and defects;
CIMCIC's guard against OBot is then self-refuting too. -/
theorem snd_CIMCIC_vs_OBot :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 5 (progCode (CIMCIC k)) (progCode OBot) (progCode (CIMCIC k)) (actCode .D) ∧
      EvalGraph 5 (progCode OBot) (progCode (CIMCIC k)) (progCode OBot) (actCode .D) := by
  obtain ⟨k₀, h⟩ := pos_CIMCIC_vs_botCB
  refine ⟨k₀, fun k hk ↦ ?_⟩
  have hO := obot_D_of_probes (h k hk) (snd_CIMCIC_vs_botDB k)
  have hn := cimcic_selfref_not_found k sfp_OBot.1 hO
  refine ⟨?_, hO⟩
  rw [progCode_CIMCIC_search] at hn ⊢
  exact search_else phiC hn (const_play 3 _ _ _)

/-! #### DIMCID × CooperateBot: the value FLIPS in `S'` — a self-fulfilling refutation is Löb-provable -/

lemma progCode_DIMCID_search (k : ℕ) : progCode (DIMCID k) = pSearch k (templateCode phiD) (pConst 1) (pConst 0) := by
  rw [DIMCID, progCode_search_noSnap _ _ _ _ rfl]; simp [phiD, actCode]

/-- **The bounded Löb premise of DIMCID against CooperateBot, slack `(7, 8)`**: a box of the family makes
DIMCID defect against CooperateBot and the transposed searcher cooperate with DefectBot, so the
antecedents "I play C against CooperateBot" / "I play D against DefectBot" are false and both
implications hold, in both readings. -/
theorem loebSound_pDi0 : LoebSound (pG (cl T0) (cterm Act.C) (cterm Act.D)) 7 8 := by
  exact loebSound_pG_of describes_CB

/-- **DIMCID × CooperateBot is `(D, C)` in PA-`S'`**, for all large `k`, unconditional — the engine's cell is
`(C, C)` (`outcome_DIMCID_vs_CooperateBot`, an unreadability census). In `S'` the guard "I play C against
CooperateBot ⇒ CooperateBot plays D against me" has a false consequent, so it says "I do not cooperate":
a proof of it makes DIMCID defect, which makes it TRUE — bounded Löb (`family_found`) then finds it. -/
theorem loeb_DIMCID_vs_CooperateBot :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 2 (progCode (DIMCID k)) (progCode CooperateBot) (progCode (DIMCID k)) (actCode .D) ∧
      EvalGraph 2 (progCode CooperateBot) (progCode (DIMCID k)) (progCode CooperateBot) (actCode .C) := by
  obtain ⟨k₀, h⟩ := family_found (pG (cl T0) (cterm Act.C) (cterm Act.D)) boundedInnerNec_sixteen loebSound_pDi0
  refine ⟨k₀, fun k hk ↦ ⟨?_, by rw [progCode_CB]; exact const_play 1 _ _ _⟩⟩
  obtain ⟨a, ha, hpc⟩ := h k hk
  have ha' := le_def.mpr (pConj_slack_nat a _ _ _ k
    (formulaLen_instB_pG (V := ℕ) (cl T0) (cterm Act.C) (cterm Act.D) k) ha)
  have h1 := pG_both_V (V := ℕ) k (cl T0) (cterm Act.C) (cterm Act.D) (hX_const_zero k) hU_C_zero hW_D_zero a ha' hpc
  rw [progCode_DIMCID, progCode_CB]
  exact h1.1

end unreadability

end ArithS
