import ArithS.Cells.SoundnessCells
import ArithS.Cells.CIMCIC
import ArithS.Cells.JustBot
import ArithS.Cells.PrudentMirror

/-!
# ArithS.Cells.PositiveCells — the POS class of the census in PA-`S'`, and the unreadability cells re-evaluated

`Research/Notes/ROUTE_B_SCOPE.md` §3 Phase 4, class **POS** of `ROUTE_B_CENSUS.md` (2026-09-23): cells whose
searcher FINDS its guard without Löb (the engine's `search_t` on a search-free atom, `weakenImpl`, `atomNeg`),
unconditional in `S'` (no `BoundedInnerNec`), for all large `k`. The mechanism is `cimcic_self_coop`'s, made
generic: the guard is the `bnum k`-instance of a FIXED one-variable formula `q` (`guardCode_qT_eq_instB` with
the searcher's description triple), `q(k)` is true in BOTH standard readings of every model, so `TAct ⊢ ∀¹ q`
by completeness (`tact_all_of_both`), and the instance at `bnum k` costs `K₀ + K₁·size k ≤ k` (`found_of_all`).

1. **The constant opponents** `pConst 0`, `pConst 1`, `pBot (pConst 0)`, `pBot (pConst 1)`: canonical codes,
   re-valuation terms, closed structural terms `T0`/`TB0`, the code hypotheses `hX_const_*`/`hU_*`/`hW_*` and the
   value equations `val_desc_*`.
2. **The generic engine-searcher description layer**: `SV g a k := pSearch k ⌜g⌝ (pConst a) (pConst (1 - a))`,
   `swapcode_SV`, the canonical triple `dnum_SV`/`dU_SV`/`dW_SV` (`Cells/CIMCIC.lean` §2 with the template and
   branch as parameters), the tower `TS`, `hX_SV`, and the reconstructions `relabel_val_uS_wS_V`/`_uST_wST_V`.
   It puts the ENGINE codes `pcode (DupocBot k)`, `pcode (CupodBot k)`, `pcode (WaryBot k)` on the same footing as
   `Cimcic k`/`Dimcid k`; the bot tower `TBS` describes the frozen snapshot `pBot (pcode (DupocBot k))`, and
   `guardCode_JustBot_eq` shows Just's consulted guard IS Dupoc's engine guard in the snapshot's frame.
3. **The closure**: `tact_all_of_both`, `found_of_all`; the generic truth of a play-atom template instance in
   both triples (`eval_qT_plays_opp_self`, `eval_qT_neg_plays_opp_self`, `eval_qT_swap`), the plays of constants
   in every model and their negations by determinism (`const_play_V`, `bot_const_play_V`, `const_not_play_V`).
4. **The cells**: `pos_DupocBot_vs_CooperateBot` `(C, C)`, `pos_CupodBot_vs_DefectBot` `(D, D)`,
   `pos_CIMCIC_vs_CooperateBot` `(C, C)`, `pos_DIMCID_vs_DefectBot` `(D, D)`, `pos_JustBot_vs_CooperateBot` `(C, C)`
   (on the engine's own code), `pos_WaryBot_vs_DefectBot` `(D, D)` (the `.neg` guard is a Π₁ truth by
   determinism — the `S'` twin of `Pf.atomNeg`), and the SND cells whose positive sub-fact is the searcher finding
   its guard against `.bot DefectBot`: `snd_CupodBot_vs_DBot`/`_EBot` and `snd_WaryBot_vs_DBot`/`_EBot`, all `(C, C)`.
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

/-- **A `TAct`-theorem `∀¹ q` true in both readings, by completeness** (`tact_proves_qCC`'s shape). -/
theorem tact_all_of_both (q : Semisentence LAct 1)
    (hstd : ∀ (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (x : M),
      Semiformula.Eval (s := stdActV M) ![x] Empty.elim q)
    (hswap : ∀ (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (x : M),
      Semiformula.Eval (s := swapActS M) ![x] Empty.elim q) :
    TAct ⊢ ∀¹ q := by
  refine tact_complete' _ fun M _ _ ↦ ?_
  have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
  constructor
  · simp only [Semiformula.eval_all]
    intro x
    rw [← stdActV_eq_stdActS]
    exact hstd M x
  · simp only [Semiformula.eval_all]
    intro x
    exact hswap M x

/-- **The instance of a `TAct`-theorem `∀¹ q` at `bnum k` fits the budget `k` for all large `k`**
(`cimcic_self_finds_guard`'s body, generic in `q` and in the guard-code family `G`): the instance
costs `K₀ + K₁·size k` (`lenProvable_inst_size` + `flen_subst_bnumT_le`), below `k` eventually
(`linear_size_le_eventually`). -/
theorem found_of_all {q : Semisentence LAct 1} (hq : TAct ⊢ ∀¹ q) (G : ℕ → ℕ)
    (hG : ∀ k, G k = instB (⌜q⌝ : ℕ) k) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k → LenProvableV TAct k (G k) := by
  obtain ⟨N₃, hN₃⟩ := lenProvable_of_provable hq
  obtain ⟨kHat, hkHat⟩ :=
    linear_size_le_eventually (N₃ + 13 * flen (q : Semiproposition LAct 1) + 8 + 30 * flen (q : Semiproposition LAct 1) + 6)
  refine ⟨kHat + 1, fun k hk ↦ ?_⟩
  have h1 := lenProvable_inst_size q k hN₃
  have hqt := flen_subst_bnumT_le q k
  set fq := flen (q : Semiproposition LAct 1) with hfq
  set s := Nat.size k with hs
  have hs1 : 0 < s := Nat.lt_size.mpr (by rw [pow_zero]; omega)
  have hpoly := hkHat ℕ k (le_def.mpr (Or.inr (by rw [natCast_nat]; omega)))
  rw [natCast_nat, ← size_eq_length] at hpoly
  have hpoly' : (N₃ + 13 * fq + 8 + 30 * fq + 6) * s ≤ k := by
    rcases le_def.mp hpoly with h | h
    · exact Nat.le_of_eq h
    · exact Nat.le_of_lt h
  have hle : N₃ + 5 * flen ((q ⇜ ![Semiterm.lMap emb (bnumT k)] : Sentence LAct) : Proposition LAct)
      + 3 * fq + 6 * s + 8 ≤ k := by
    calc N₃ + 5 * flen ((q ⇜ ![Semiterm.lMap emb (bnumT k)] : Sentence LAct) : Proposition LAct)
          + 3 * fq + 6 * s + 8
        ≤ N₃ + 5 * (fq * (6 * s + 2)) + 3 * fq + 6 * s + 8 := by gcongr
      _ = (N₃ + 13 * fq + 8) + (30 * fq + 6) * s := by ring
      _ ≤ (N₃ + 13 * fq + 8) * s + (30 * fq + 6) * s := by
          gcongr; exact Nat.le_mul_of_pos_right _ hs1
      _ = (N₃ + 13 * fq + 8 + 30 * fq + 6) * s := by ring
      _ ≤ k := hpoly'
  have h2 := lenProvable_fbound_mono hle h1
  rw [← lenProvableV_nat] at h2
  have hq' : instB (⌜q⌝ : ℕ) k = ⌜(q ⇜ ![Semiterm.lMap emb (bnumT k)] : Sentence LAct)⌝ := by
    have := quote_instB (V := ℕ) q k
    rwa [natCast_nat] at this
  rw [hG, hq']
  exact h2

end closure

/-! ### 4. The truth of a play-atom template instance, generic in both triples -/

section truth


end truth

/-! ### 5. The engine searchers as `SV` instances, and the bot-wrapped snapshot -/

section instances


lemma pcode_DupocBot_SV (k : ℕ) : pcode (DupocBot k) = SV (V := ℕ) gDu 0 k := by
  rw [pcode_DupocBot', SV_nat]; rfl
lemma pcode_CupodBot_SV (k : ℕ) : pcode (CupodBot k) = SV (V := ℕ) gCu 1 k := by
  rw [pcode_CupodBot, SV_nat]; rfl
lemma pcode_WaryBot_SV (k : ℕ) : pcode (WaryBot k) = SV (V := ℕ) gW 1 k := by
  rw [pcode_WaryBot, SV_nat]; rfl


/-- Just's consulted guard against `opp` is Dupoc's engine guard in the frame `(.bot (DupocBot k), opp)`
(both are the template code of "`opp` plays C against `.bot (DupocBot k)`"). -/
lemma guardCode_JustBot_eq (k : ℕ) {opp : PD.Prog} (hopp : Proper opp) :
    guardCode (tcode (phiJ k)) (pcode (JustBot k)) (pcode opp) =
      guardCode (tcode phiDu) (pBot (pcode (DupocBot k))) (pcode opp) := by
  rw [← pcode_bot]
  change guardOf (phiJ k) (JustBot k) opp = guardOf phiDu (.bot (DupocBot k)) opp
  rw [guardOf_eq_tcode_subst (proper_JustBot k) hopp _ rfl, guardOf_eq_tcode_subst (proper_bot _) hopp _ rfl]
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
    rw [qDu0, eval_qT_plays_opp_self .C _ _ _ _ _ _ x (hme_SV gDu 0 (Or.inl rfl) x) (val_desc_const_zero x),
      actCode_C_cast]
    exact const_play_V _ _ _
  · have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    rw [qDu0, eval_qT_swap, lMap_swap_gDu, lMap_swap_cl, lMap_swap_T0, lMap_swap_cterm_C, lMap_swap_cterm_D,
      eval_qT_plays_opp_self .D _ _ _ _ _ _ x (hme_SVT gDu 0 (Or.inl rfl) x) (val_desc_const_one x),
      actCode_D_cast]
    exact const_play_V _ _ _

/-- `DupocBot × CooperateBot = (C, C)` (engine `outcome_DupocBot_vs_CooperateBot`, pad 2), for all large `k`:
the guard "CooperateBot plays C against me" is a `TAct`-theorem in `k` (`tact_qDu0`), found within the
budget for all large `k` (`found_of_all`). -/
theorem pos_DupocBot_vs_CooperateBot :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 2 (pcode (DupocBot k)) (pcode CooperateBot) (pcode (DupocBot k)) (actCode .C) ∧
      EvalGraph 2 (pcode CooperateBot) (pcode (DupocBot k)) (pcode CooperateBot) (actCode .C) := by
  obtain ⟨k₀, h⟩ := found_of_all tact_qDu0
    (fun k ↦ guardCode (tcode phiDu) (pcode (DupocBot k)) (pcode CooperateBot))
    (fun k ↦ by rw [pcode_CB, pcode_DupocBot_SV]; exact guardCode_Du0 (V := ℕ) k)
  refine ⟨k₀, fun k hk ↦ ⟨?_, by rw [pcode_CB]; exact const_play 1 _ _ _⟩⟩
  have hg := h k hk
  rw [pcode_DupocBot'] at hg ⊢
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
    rw [qCu1, eval_qT_plays_opp_self .D _ _ _ _ _ _ x (hme_SV gCu 1 (Or.inr rfl) x) (val_desc_const_one x),
      actCode_D_cast]
    exact const_play_V _ _ _
  · have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    rw [qCu1, eval_qT_swap, lMap_swap_gCu, lMap_swap_cl, lMap_swap_T0, lMap_swap_cterm_C, lMap_swap_cterm_D,
      eval_qT_plays_opp_self .C _ _ _ _ _ _ x (hme_SVT gCu 1 (Or.inr rfl) x) (val_desc_const_zero x),
      actCode_C_cast]
    exact const_play_V _ _ _

/-- `CupodBot × DefectBot = (D, D)` (engine `outcome_CupodBot_vs_DefectBot`, pad 2), for all large `k`. -/
theorem pos_CupodBot_vs_DefectBot :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 2 (pcode (CupodBot k)) (pcode DefectBot) (pcode (CupodBot k)) (actCode .D) ∧
      EvalGraph 2 (pcode DefectBot) (pcode (CupodBot k)) (pcode DefectBot) (actCode .D) := by
  obtain ⟨k₀, h⟩ := found_of_all tact_qCu1
    (fun k ↦ guardCode (tcode phiCu) (pcode (CupodBot k)) (pcode DefectBot))
    (fun k ↦ by rw [pcode_DB, pcode_CupodBot_SV]; exact guardCode_Cu1 (V := ℕ) k)
  refine ⟨k₀, fun k hk ↦ ⟨?_, by rw [pcode_DB]; exact const_play 1 _ _ _⟩⟩
  have hg := h k hk
  rw [pcode_CupodBot] at hg ⊢
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
    rw [qCuB1, eval_qT_plays_opp_self .D _ _ _ _ _ _ x (hme_SV gCu 1 (Or.inr rfl) x) (val_desc_bot_one x),
      actCode_D_cast]
    exact bot_const_play_V _ _ _
  · have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    rw [qCuB1, eval_qT_swap, lMap_swap_gCu, lMap_swap_cl, lMap_swap_TB0, lMap_swap_cterm_C, lMap_swap_cterm_D,
      eval_qT_plays_opp_self .C _ _ _ _ _ _ x (hme_SVT gCu 1 (Or.inr rfl) x) (val_desc_bot_zero x),
      actCode_C_cast]
    exact bot_const_play_V _ _ _

/-- Cupod defects against `.bot DefectBot` for all large `k` (its guard is found). -/
theorem cupod_vs_botDB_found :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k → EvalGraph 2 (pcode (CupodBot k)) (pBot (pConst 1)) (pcode (CupodBot k)) 1 := by
  obtain ⟨k₀, h⟩ := found_of_all tact_qCuB1
    (fun k ↦ guardCode (tcode phiCu) (pcode (CupodBot k)) (pBot (pConst 1)))
    (fun k ↦ by rw [pcode_CupodBot_SV]; exact guardCode_CuB1 (V := ℕ) k)
  refine ⟨k₀, fun k hk ↦ ?_⟩
  have hg := h k hk
  rw [pcode_CupodBot] at hg ⊢
  exact search_then phiCu hg (const_play _ _ _ _)

/-- `CupodBot × DBot = (C, C)` (engine `outcome_CupodBot_vs_DBot`, pad 4), for all large `k`: DBot sees Cupod
defect against `.bot DefectBot` (found) and cooperates; Cupod's guard against DBot is then false. -/
theorem snd_CupodBot_vs_DBot :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 4 (pcode (CupodBot k)) (pcode DBot) (pcode (CupodBot k)) (actCode .C) ∧
      EvalGraph 4 (pcode DBot) (pcode (CupodBot k)) (pcode DBot) (actCode .C) := by
  obtain ⟨k₀, h⟩ := cupod_vs_botDB_found
  refine ⟨k₀, fun k hk ↦ ?_⟩
  have hD := dbot_C_of_probe_D (h k hk)
  exact ⟨EvalGraph.mono_le (by omega) (cupod_C_of_probe k sfp_DBot.1 hD), hD⟩

/-- `CupodBot × EBot = (C, C)` (engine `outcome_CupodBot_vs_EBot`, pad 5), for all large `k`. -/
theorem snd_CupodBot_vs_EBot :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 5 (pcode (CupodBot k)) (pcode EBot) (pcode (CupodBot k)) (actCode .C) ∧
      EvalGraph 5 (pcode EBot) (pcode (CupodBot k)) (pcode EBot) (actCode .C) := by
  obtain ⟨k₀, h⟩ := cupod_vs_botDB_found
  refine ⟨k₀, fun k hk ↦ ?_⟩
  have hE := ebot_C_of_probes (h k hk) (cupod_vs_botCB k)
  exact ⟨EvalGraph.mono_le (by omega) (cupod_C_of_probe k sfp_EBot.1 hE), hE⟩

/-! #### CIMCIC × CooperateBot `(C, C)` -/

/-- CIMCIC's guard against CooperateBot: "I play C against CooperateBot ⇒ CooperateBot plays C against me". -/
noncomputable def qCi0 : Semisentence LAct 1 := qCG (cl T0) (cterm Act.C) (cterm Act.D)

theorem guardCode_Ci0 (k : V) : guardCode (⌜tmplC⌝ : V) (CimcicV k) (pConst 0) = instB (⌜qCi0⌝ : V) k :=
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
      EvalGraph 2 (pcode (CIMCIC k)) (pcode CooperateBot) (pcode (CIMCIC k)) (actCode .C) ∧
      EvalGraph 2 (pcode CooperateBot) (pcode (CIMCIC k)) (pcode CooperateBot) (actCode .C) := by
  obtain ⟨k₀, h⟩ := found_of_all tact_qCi0
    (fun k ↦ guardCode (⌜tmplC⌝ : ℕ) (Cimcic k) (pConst 0)) (fun k ↦ guardCode_Ci0 (V := ℕ) k)
  refine ⟨k₀, fun k hk ↦ ⟨?_, by rw [pcode_CB]; exact const_play 1 _ _ _⟩⟩
  rw [pcode_CIMCIC, pcode_CB]
  exact cimcic_search_V (V := ℕ) k (pConst 0) (h k hk)

/-! #### DIMCID × DefectBot `(D, D)` -/

/-- DIMCID's guard against DefectBot: "I play C against DefectBot ⇒ DefectBot plays D against me". -/
noncomputable def qDi1 : Semisentence LAct 1 := qDG (cl T0) (cterm Act.D) (cterm Act.C)

theorem guardCode_Di1 (k : V) : guardCode (⌜tmplD⌝ : V) (DimcidV k) (pConst 1) = instB (⌜qDi1⌝ : V) k :=
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
      EvalGraph 2 (pcode (DIMCID k)) (pcode DefectBot) (pcode (DIMCID k)) (actCode .D) ∧
      EvalGraph 2 (pcode DefectBot) (pcode (DIMCID k)) (pcode DefectBot) (actCode .D) := by
  obtain ⟨k₀, h⟩ := found_of_all tact_qDi1
    (fun k ↦ guardCode (⌜tmplD⌝ : ℕ) (Dimcid k) (pConst 1)) (fun k ↦ guardCode_Di1 (V := ℕ) k)
  refine ⟨k₀, fun k hk ↦ ⟨?_, by rw [pcode_DB]; exact const_play 1 _ _ _⟩⟩
  rw [pcode_DIMCID, pcode_DB]
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
    rw [qJ0, eval_qT_plays_opp_self .C _ _ _ _ _ _ x (hme_botSV gDu 0 (Or.inl rfl) x) (val_desc_const_zero x),
      actCode_C_cast]
    exact const_play_V _ _ _
  · have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    rw [qJ0, eval_qT_swap, lMap_swap_gDu, lMap_swap_cl, lMap_swap_T0, lMap_swap_cterm_C, lMap_swap_cterm_D,
      eval_qT_plays_opp_self .D _ _ _ _ _ _ x (hme_botSVT gDu 0 (Or.inl rfl) x) (val_desc_const_one x),
      actCode_D_cast]
    exact const_play_V _ _ _

/-- `JustBot × CooperateBot = (C, C)` (engine `outcome_JustBot_vs_CooperateBot`, pad 2), for all large `k`, on the
engine's own code `pcode (JustBot k)`: the consulted guard is Dupoc's engine guard in the frame of the frozen
snapshot (`guardCode_JustBot_eq`), the `bnum k`-instance of `qJ0` through the bot tower `TBS`. -/
theorem pos_JustBot_vs_CooperateBot :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 2 (pcode (JustBot k)) (pcode CooperateBot) (pcode (JustBot k)) (actCode .C) ∧
      EvalGraph 2 (pcode CooperateBot) (pcode (JustBot k)) (pcode CooperateBot) (actCode .C) := by
  obtain ⟨k₀, h⟩ := found_of_all tact_qJ0
    (fun k ↦ guardCode (tcode (phiJ k)) (pcode (JustBot k)) (pcode CooperateBot))
    (fun k ↦ by
      rw [guardCode_JustBot_eq k sfp_CooperateBot.1, pcode_CB, pcode_DupocBot_SV]
      exact guardCode_J0 (V := ℕ) k)
  refine ⟨k₀, fun k hk ↦ ⟨?_, by rw [pcode_CB]; exact const_play 1 _ _ _⟩⟩
  have hg := h k hk
  rw [pcode_JustBot] at hg ⊢
  exact search_then (phiJ k) hg (const_play _ _ _ _)

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
    rw [qW1, eval_qT_neg_plays_opp_self .C _ _ _ _ _ _ x (hme_SV gW 1 (Or.inr rfl) x) (val_desc_const_one x),
      actCode_C_cast]
    exact const_not_play_V _ _ _root_.one_ne_zero
  · have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    rw [qW1, eval_qT_swap, lMap_swap_gW, lMap_swap_cl, lMap_swap_T0, lMap_swap_cterm_C, lMap_swap_cterm_D,
      eval_qT_neg_plays_opp_self .D _ _ _ _ _ _ x (hme_SVT gW 1 (Or.inr rfl) x) (val_desc_const_zero x),
      actCode_D_cast]
    exact const_not_play_V _ _ _root_.zero_ne_one

/-- `WaryBot × DefectBot = (D, D)` (engine `outcome_WaryBot_vs_DefectBot`, pad 2), for all large `k`: the `.neg`
guard "DefectBot does not cooperate with me" is a Π₁ truth in every model (determinism), a `TAct`-theorem
in `k`, found within the budget (the `S'` twin of the engine's `Pf.atomNeg`). -/
theorem pos_WaryBot_vs_DefectBot :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 2 (pcode (WaryBot k)) (pcode DefectBot) (pcode (WaryBot k)) (actCode .D) ∧
      EvalGraph 2 (pcode DefectBot) (pcode (WaryBot k)) (pcode DefectBot) (actCode .D) := by
  obtain ⟨k₀, h⟩ := found_of_all tact_qW1
    (fun k ↦ guardCode (tcode phiW) (pcode (WaryBot k)) (pcode DefectBot))
    (fun k ↦ by rw [pcode_DB, pcode_WaryBot_SV]; exact guardCode_W1 (V := ℕ) k)
  refine ⟨k₀, fun k hk ↦ ⟨?_, by rw [pcode_DB]; exact const_play 1 _ _ _⟩⟩
  have hg := h k hk
  rw [pcode_WaryBot] at hg ⊢
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
    rw [qWB1, eval_qT_neg_plays_opp_self .C _ _ _ _ _ _ x (hme_SV gW 1 (Or.inr rfl) x) (val_desc_bot_one x),
      actCode_C_cast]
    exact bot_const_not_play_V _ _ _root_.one_ne_zero
  · have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    rw [qWB1, eval_qT_swap, lMap_swap_gW, lMap_swap_cl, lMap_swap_TB0, lMap_swap_cterm_C, lMap_swap_cterm_D,
      eval_qT_neg_plays_opp_self .D _ _ _ _ _ _ x (hme_SVT gW 1 (Or.inr rfl) x) (val_desc_bot_zero x),
      actCode_D_cast]
    exact bot_const_not_play_V _ _ _root_.zero_ne_one

/-- Wary defects against `.bot DefectBot` for all large `k` (its `.neg` guard is found). -/
theorem wary_vs_botDB_found :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k → EvalGraph 2 (pcode (WaryBot k)) (pBot (pConst 1)) (pcode (WaryBot k)) 1 := by
  obtain ⟨k₀, h⟩ := found_of_all tact_qWB1
    (fun k ↦ guardCode (tcode phiW) (pcode (WaryBot k)) (pBot (pConst 1)))
    (fun k ↦ by rw [pcode_WaryBot_SV]; exact guardCode_WB1 (V := ℕ) k)
  refine ⟨k₀, fun k hk ↦ ?_⟩
  have hg := h k hk
  rw [pcode_WaryBot] at hg ⊢
  exact search_then phiW hg (const_play _ _ _ _)

/-- `WaryBot × DBot = (C, C)` (engine `outcome_WaryBot_vs_DBot`, pad 4), for all large `k`. -/
theorem snd_WaryBot_vs_DBot :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 4 (pcode (WaryBot k)) (pcode DBot) (pcode (WaryBot k)) (actCode .C) ∧
      EvalGraph 4 (pcode DBot) (pcode (WaryBot k)) (pcode DBot) (actCode .C) := by
  obtain ⟨k₀, h⟩ := wary_vs_botDB_found
  refine ⟨k₀, fun k hk ↦ ?_⟩
  have hD := dbot_C_of_probe_D (h k hk)
  exact ⟨EvalGraph.mono_le (by omega) (wary_C_of_probe k sfp_DBot.1 hD), hD⟩

/-- `WaryBot × EBot = (C, C)` (engine `outcome_WaryBot_vs_EBot`, pad 5), for all large `k`. -/
theorem snd_WaryBot_vs_EBot :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 5 (pcode (WaryBot k)) (pcode EBot) (pcode (WaryBot k)) (actCode .C) ∧
      EvalGraph 5 (pcode EBot) (pcode (WaryBot k)) (pcode EBot) (actCode .C) := by
  obtain ⟨k₀, h⟩ := wary_vs_botDB_found
  refine ⟨k₀, fun k hk ↦ ?_⟩
  have hE := ebot_C_of_probes (h k hk) (wary_vs_botCB k)
  exact ⟨EvalGraph.mono_le (by omega) (wary_C_of_probe k sfp_EBot.1 hE), hE⟩

end cells

/-! ### 7. The UNREADABILITY cells re-evaluated in `S'` (census class FLOOR(cenU)/OTHER) -/

section unreadability

lemma pcode_CIMCIC' (k : ℕ) : pcode (CIMCIC k) = pSearch k (tcode phiC) (pConst 0) (pConst 1) := by
  simp [CIMCIC, phiC, actCode]
lemma proper_CIMCIC (k : ℕ) : Proper (CIMCIC k) := ⟨by simp [CIMCIC], by simp [CIMCIC]⟩

/-- **CIMCIC's guard against an opponent that defects against it is SELF-REFUTING**: a proof of
"I play C against `opp` ⇒ `opp` plays C against me" makes CIMCIC cooperate, so by soundness `opp`
cooperates — against the fact. So it is never found (the red cell's argument, one level up). -/
theorem cimcic_selfref_not_found (k : ℕ) {opp : PD.Prog} (hopp : Proper opp) {N : ℕ}
    (h : EvalGraph N (pcode opp) (pcode (CIMCIC k)) (pcode opp) 1) :
    ¬ LenProvableV TAct k (guardCode (tcode phiC) (pcode (CIMCIC k)) (pcode opp)) := by
  intro hf
  have hC : EvalGraph 2 (pcode (CIMCIC k)) (pcode opp) (pcode (CIMCIC k)) 0 := by
    rw [pcode_CIMCIC'] at hf ⊢
    exact search_then phiC hf (const_play _ _ _ _)
  have hT : ℕ↓[LAct] ⊧ trAt (CIMCIC k) opp phiC :=
    models_trAt_of_lenProvableV (φ := phiC) (me := CIMCIC k) (opp := opp) hf
  rw [← trAt_subst (CIMCIC k) opp (proper_CIMCIC k) hopp phiC rfl] at hT
  change ℕ↓[LAct] ⊧ trAt (CIMCIC k) opp (.impl (.plays (CIMCIC k) opp .C) (.plays opp (CIMCIC k) .C)) at hT
  rw [models_trAt_impl, models_trAt_plays _ _ _ _ _ (proper_CIMCIC k) hopp,
    models_trAt_plays _ _ _ _ _ hopp (proper_CIMCIC k)] at hT
  obtain ⟨N', hN'⟩ := hT ⟨2, hC⟩
  exact absurd (EvalGraph.unique' hN' h) (by decide)

/-- `CIMCIC × DefectBot = (D, D)` (engine `outcome_CIMCIC_vs_DefectBot`, pad 2) at EVERY `k`: in `S'` the
guard is true but self-refuting, hence never found — the census's unreadability argument replaced by
soundness. -/
theorem snd_CIMCIC_vs_DefectBot (k : ℕ) :
    EvalGraph 2 (pcode (CIMCIC k)) (pcode DefectBot) (pcode (CIMCIC k)) (actCode .D) ∧
    EvalGraph 2 (pcode DefectBot) (pcode (CIMCIC k)) (pcode DefectBot) (actCode .D) := by
  have hn := cimcic_selfref_not_found k sfp_DefectBot.1 (N := 1) (by rw [pcode_DB]; exact const_play 0 _ _ _)
  rw [pcode_CIMCIC'] at hn ⊢
  exact ⟨search_else phiC hn (const_play _ _ _ _), by rw [pcode_DB]; exact const_play 1 _ _ _⟩

/-- CIMCIC defects against `.bot DefectBot` at every `k` (self-refuting guard). -/
theorem cimcic_vs_botDB (k : ℕ) :
    EvalGraph 2 (pcode (CIMCIC k)) (pBot (pConst 1)) (pcode (CIMCIC k)) 1 := by
  have hn := cimcic_selfref_not_found k (opp := .bot DefectBot) proper_botDB (N := 2)
    (by rw [pcode_botDB]; exact bot_const_play 0 _ _ _)
  rw [pcode_botDB] at hn
  rw [pcode_CIMCIC'] at hn ⊢
  exact search_else phiC hn (const_play _ _ _ _)

/-- CIMCIC's guard against `.bot CooperateBot`: the consequent "`.bot CooperateBot` plays C against me" is
a closed truth, so the implication is a `TAct`-theorem in `k`. -/
noncomputable def qCiB0 : Semisentence LAct 1 := qCG (cl TB0) (cterm Act.C) (cterm Act.D)

theorem guardCode_CiB0 (k : V) :
    guardCode (⌜tmplC⌝ : V) (CimcicV k) (pBot (pConst 0)) = instB (⌜qCiB0⌝ : V) k :=
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
theorem cimcic_vs_botCB_found :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k → EvalGraph 2 (pcode (CIMCIC k)) (pBot (pConst 0)) (pcode (CIMCIC k)) 0 := by
  obtain ⟨k₀, h⟩ := found_of_all tact_qCiB0
    (fun k ↦ guardCode (⌜tmplC⌝ : ℕ) (Cimcic k) (pBot (pConst 0))) (fun k ↦ guardCode_CiB0 (V := ℕ) k)
  refine ⟨k₀, fun k hk ↦ ?_⟩
  rw [pcode_CIMCIC]
  exact cimcic_search_V (V := ℕ) k (pBot (pConst 0)) (h k hk)

/-- `CIMCIC × OBot = (D, D)` (engine `outcome_CIMCIC_vs_OBot`, pad 5) for all large `k`: OBot sees CIMCIC
cooperate with `.bot CooperateBot` (found) but defect against `.bot DefectBot` (self-refuting), and defects;
CIMCIC's guard against OBot is then self-refuting too. -/
theorem snd_CIMCIC_vs_OBot :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 5 (pcode (CIMCIC k)) (pcode OBot) (pcode (CIMCIC k)) (actCode .D) ∧
      EvalGraph 5 (pcode OBot) (pcode (CIMCIC k)) (pcode OBot) (actCode .D) := by
  obtain ⟨k₀, h⟩ := cimcic_vs_botCB_found
  refine ⟨k₀, fun k hk ↦ ?_⟩
  have hO := obot_D_of_probes (h k hk) (cimcic_vs_botDB k)
  have hn := cimcic_selfref_not_found k sfp_OBot.1 hO
  refine ⟨?_, hO⟩
  rw [pcode_CIMCIC'] at hn ⊢
  exact search_else phiC hn (const_play 3 _ _ _)

/-! #### DIMCID × CooperateBot: the value FLIPS in `S'` — a self-fulfilling refutation is Löb-provable -/

lemma pcode_DIMCID' (k : ℕ) : pcode (DIMCID k) = pSearch k (tcode phiD) (pConst 1) (pConst 0) := by
  simp [DIMCID, phiD, actCode]

/-- **The bounded Löb premise of DIMCID against CooperateBot, slack `(7, 8)`**: a box of the family makes
DIMCID defect against CooperateBot and the transposed searcher cooperate with DefectBot, so the
antecedents "I play C against CooperateBot" / "I play D against DefectBot" are false and both
implications hold, in both readings. -/
theorem loebSound_pDi0 : LoebSound (pG (cl T0) (cterm Act.C) (cterm Act.D)) 7 8 := by
  intro V _ _ k a ha h
  have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
  have ha' : a + 8 * (formulaLen LAct (instB (⌜qDG (cl T0) (cterm Act.C) (cterm Act.D)⌝ : V) k) +
      formulaLen LAct (instB (⌜qTG (Semiterm.lMap swap (cl T0 : Semiterm LAct Empty 1))
        (Semiterm.lMap swap (cterm Act.C)) (Semiterm.lMap swap (cterm Act.D))⌝ : V) k)) + 7 ≤ k :=
    le_trans (pConj_slack_le a _ _ _ (formulaLen_instB_pG (cl T0) (cterm Act.C) (cterm Act.D) k)) ha
  obtain ⟨h1, h2⟩ := pG_both_V k (cl T0) (cterm Act.C) (cterm Act.D) (hX_const_zero k) hU_C_zero hW_D_zero a ha' h
  rw [swapcode_pConst_zero] at h2
  have hopp' : relabel ((Semiterm.lMap swap (cterm Act.C : ClosedSemiterm LAct 0)).val (s := stdActV V) ![] Empty.elim)
      ((Semiterm.lMap swap (cterm Act.D : ClosedSemiterm LAct 0)).val (s := stdActV V) ![] Empty.elim)
      ((Semiterm.lMap swap (cl T0 : Semiterm LAct Empty 1)).val (s := stdActV V) ![k] Empty.elim) = pConst 1 := by
    rw [lMap_swap_cl, lMap_swap_T0, lMap_swap_cterm_C, lMap_swap_cterm_D]
    exact val_desc_const_one k
  have hA : ¬ ∃ n, EvalGraph n (DimcidV k) (pConst 0) (DimcidV k) 0 := by
    rintro ⟨n, hn⟩
    exact _root_.zero_ne_one (EvalGraph.unique_V' n 2 _ _ _ _ _ hn h1)
  have hB : ¬ ∃ n, EvalGraph n (DimcidTV k) (pConst 1) (DimcidTV k) 1 := by
    rintro ⟨n, hn⟩
    exact _root_.one_ne_zero (EvalGraph.unique_V' n 2 _ _ _ _ _ hn h2)
  exact ⟨(eval_pG_iff_stdActS k (cl T0) (cterm Act.C) (cterm Act.D) (val_desc_const_zero k) hopp').mpr
      ⟨fun h ↦ absurd h hA, fun h ↦ absurd h hB⟩,
    (eval_pG_iff_swap k (cl T0) (cterm Act.C) (cterm Act.D) (val_desc_const_zero k) hopp').mpr
      ⟨fun h ↦ absurd h hA, fun h ↦ absurd h hB⟩⟩

/-- **DIMCID × CooperateBot is `(D, C)` in PA-`S'`**, for all large `k`, unconditional — the engine's cell is
`(C, C)` (`outcome_DIMCID_vs_CooperateBot`, an unreadability census). In `S'` the guard "I play C against
CooperateBot ⇒ CooperateBot plays D against me" has a false consequent, so it says "I do not cooperate":
a proof of it makes DIMCID defect, which makes it TRUE — bounded Löb (`family_found`) then finds it. -/
theorem loeb_DIMCID_vs_CooperateBot :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 2 (pcode (DIMCID k)) (pcode CooperateBot) (pcode (DIMCID k)) (actCode .D) ∧
      EvalGraph 2 (pcode CooperateBot) (pcode (DIMCID k)) (pcode CooperateBot) (actCode .C) := by
  obtain ⟨k₀, h⟩ := family_found (pG (cl T0) (cterm Act.C) (cterm Act.D)) boundedInnerNec_sixteen loebSound_pDi0
  refine ⟨k₀, fun k hk ↦ ⟨?_, by rw [pcode_CB]; exact const_play 1 _ _ _⟩⟩
  obtain ⟨a, ha, hpc⟩ := h k hk
  have ha' := le_def.mpr (pConj_slack_nat a _ _ _ k
    (formulaLen_instB_pG (V := ℕ) (cl T0) (cterm Act.C) (cterm Act.D) k) ha)
  have h1 := pG_both_V (V := ℕ) k (cl T0) (cterm Act.C) (cterm Act.D) (hX_const_zero k) hU_C_zero hW_D_zero a ha' hpc
  rw [pcode_DIMCID, pcode_CB]
  exact h1.1

end unreadability

end ArithS
