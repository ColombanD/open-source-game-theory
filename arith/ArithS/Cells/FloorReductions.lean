import ArithS.Cells.CupodOBot

/-!
# ArithS.Cells.FloorReductions — the hinge of Dupoc × EBot is inter-reducible with bounded consistency

`Cells/FloorDichotomy` §5 ties the hinge of the simplest floor, Dupoc × DBot, to the τ-symmetrized bounded
consistency instance on `σ_k` = "`.bot DefectBot` plays C against `DupocBot k`" (Dupoc's guard against
`.bot DefectBot`, FALSE in ℕ). This module does the same for **Dupoc × EBot**, the other floor of the paper's base
zoo, on the SAME `σ_k` — so the two floors of that zoo rest on one sentence.

`EBot = ite (opp vs .bot DefectBot = C) D (ite (opp vs .bot CooperateBot = C) C (ite (opp vs .bot MirrorBot = C) C D))`.
The hinge is `A_k = □_k "EBot plays C against DupocBot k"`.

* **The reduction** (`hinge_reduces_to_bounded_consistency_DupocBot_vs_EBot`): EBot's cooperation passes its first
  rung, so Dupoc did NOT cooperate with `.bot DefectBot`, i.e. `σ_k` was not found — in every model, in both readings
  (the τ-twin in the swapped one). Hence `TAct ⊢ ∀ k, r(k) → (¬□_k σ_k ∨ ¬□_k τσ_k)` (`tact_rEB_imp_negTwin`), and a
  proof of the hinge within `k` yields a proof of `negTwin(k)` within `k + C₀ + C₁·size k`. Verbatim DBot's.
* **The converse** (`bounded_consistency_reduces_to_hinge_DupocBot_vs_EBot`): from "neither `σ_k` nor `τσ_k` is
  provable within `k`" Dupoc defects against `.bot DefectBot` (its else-branch), so EBot's first rung falls; its
  SECOND rung then needs Dupoc to cooperate with `.bot CooperateBot` — Dupoc's THEN-branch on a true atom, found in
  every model above a standard threshold (`dupoc_botCB_V`). So the uniform theorem is conditional,
  `TAct ⊢ ∀ k ≥ k̂, conjTwin(k) → r(k)` (`tact_conjTwin_imp_rEB_above`), and its instance at `k` costs
  `K₀ + K₁·size k + K₂·(size k)²` (`exists_instance_length_above`): a proof of `conjTwin(k)` within `m` yields the
  hinge within `m + C₀ + C₁·size k + C₂·(size k)²`, for `k > k̂`. The overhead is polylogarithmic in `k`, against
  DBot's logarithmic one — the price of discharging the threshold by one more cut.

As for DBot the two directions use the disjunction and the conjunction of the two twins, equivalent at ℕ
(`negTwin_true_iff`); `TAct` proves the disjunction uniformly because it cannot tell its two readings apart.

Cupod × OBot is NOT here: its hinge is found outright (`Cells/CupodOBot`), no consistency statement enters.
-/

set_option linter.constructorNameAsVariable false

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open LAct
open PD.Bots

section ebot

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ### 1. EBot in every model, its rungs and their inverses -/

/-- EBot's code in every model. -/
noncomputable def EBotV : V :=
  pIte (pSim pOpp (pBot (pConst 1))) 0 (pConst 1)
    (pIte (pSim pOpp (pBot (pConst 0))) 0 (pConst 0)
      (pIte (pSim pOpp (pBot MirrorV)) 0 (pConst 0) (pConst 1)))

/-- The transposed EBot (the Mirror probe is τ-invariant). -/
noncomputable def EBotTV : V :=
  pIte (pSim pOpp (pBot (pConst 0))) 1 (pConst 0)
    (pIte (pSim pOpp (pBot (pConst 1))) 1 (pConst 1)
      (pIte (pSim pOpp (pBot MirrorV)) 1 (pConst 1) (pConst 0)))

lemma progCode_EBot_eq :
    progCode EBot =
      pIte (pSim pOpp (pBot (pConst 1))) 0 (pConst 1)
        (pIte (pSim pOpp (pBot (pConst 0))) 0 (pConst 0)
          (pIte (pSim pOpp (pBot Mirror)) 0 (pConst 0) (pConst 1))) := by
  simp [EBot, CooperateBot, DefectBot, MirrorBot, actCode, Mirror]

lemma cast_EBot : ((progCode EBot : ℕ) : V) = EBotV := by
  rw [progCode_EBot_eq]
  simp only [cast_pIte, cast_pSim, cast_pOpp, cast_pBot, cast_pConst, cast_Mirror]
  simp [EBotV]

theorem transposeCode_EBotV : transposeCode (EBotV : V) = EBotTV := by
  unfold EBotV EBotTV MirrorV transposeCode
  simp [revalueAction]

/-- EBot cooperates with `x` when `x` defects against `.bot DefectBot` and cooperates with `.bot CooperateBot`, in
every model (the two probes at consecutive fuels: there is no fuel monotonicity off ℕ). -/
theorem ebot_C_of_probes_V {x n : V} (h1 : EvalGraph (n + 1) x (pBot (pConst 1)) x 1)
    (h0 : EvalGraph n x (pBot (pConst 0)) x 0) :
    EvalGraph (n + 1 + 1 + 1) EBotV x EBotV 0 := by
  unfold EBotV
  rw [EvalGraph.ite_iff]
  refine ⟨1, ?_, Or.inr ⟨_root_.one_ne_zero, ?_⟩⟩
  · rw [EvalGraph.sim_iff, substCode_opp, substCode_bot]
    exact h1
  · rw [EvalGraph.ite_iff]
    refine ⟨0, ?_, Or.inl ⟨rfl, EvalGraph.const_iff.mpr rfl⟩⟩
    rw [EvalGraph.sim_iff, substCode_opp, substCode_bot]
    exact h0

/-- The transposed EBot defects against `x` when `x` cooperates with `.bot CooperateBot` and defects against
`.bot DefectBot`. -/
theorem ebotT_D_of_probes_V {x n : V} (h0 : EvalGraph (n + 1) x (pBot (pConst 0)) x 0)
    (h1 : EvalGraph n x (pBot (pConst 1)) x 1) :
    EvalGraph (n + 1 + 1 + 1) EBotTV x EBotTV 1 := by
  unfold EBotTV
  rw [EvalGraph.ite_iff]
  refine ⟨0, ?_, Or.inr ⟨_root_.zero_ne_one, ?_⟩⟩
  · rw [EvalGraph.sim_iff, substCode_opp, substCode_bot]
    exact h0
  · rw [EvalGraph.ite_iff]
    refine ⟨1, ?_, Or.inl ⟨rfl, EvalGraph.const_iff.mpr rfl⟩⟩
    rw [EvalGraph.sim_iff, substCode_opp, substCode_bot]
    exact h1

/-- **The inverse**: EBot's cooperation with `x` means `x` did NOT cooperate with `.bot DefectBot` (the first
rung's then-branch is the constant D). -/
theorem probe_of_ebot_C_V {x n : V} (h : EvalGraph n EBotV x EBotV 0) :
    ∃ m r : V, EvalGraph m x (pBot (pConst 1)) x r ∧ r ≠ 0 := by
  obtain ⟨n', rfl, _⟩ := EvalGraph.case_iff.mp h
  unfold EBotV at h
  obtain ⟨r, hb, hpq⟩ := EvalGraph.ite_iff.mp h
  obtain ⟨n'', rfl, _⟩ := EvalGraph.case_iff.mp hb
  rw [EvalGraph.sim_iff, substCode_opp, substCode_bot] at hb
  refine ⟨n'', r, hb, ?_⟩
  rcases hpq with ⟨_, hc⟩ | ⟨hr, _⟩
  · exact absurd (EvalGraph.const_iff.mp hc) _root_.zero_ne_one
  · exact hr

/-- The transposed inverse: the transposed EBot's defection means `x` did NOT defect against `.bot CooperateBot`. -/
theorem probe_of_ebotT_D_V {x n : V} (h : EvalGraph n EBotTV x EBotTV 1) :
    ∃ m r : V, EvalGraph m x (pBot (pConst 0)) x r ∧ r ≠ 1 := by
  obtain ⟨n', rfl, _⟩ := EvalGraph.case_iff.mp h
  unfold EBotTV at h
  obtain ⟨r, hb, hpq⟩ := EvalGraph.ite_iff.mp h
  obtain ⟨n'', rfl, _⟩ := EvalGraph.case_iff.mp hb
  rw [EvalGraph.sim_iff, substCode_opp, substCode_bot] at hb
  refine ⟨n'', r, hb, ?_⟩
  rcases hpq with ⟨_, hc⟩ | ⟨hr, _⟩
  · exact absurd (EvalGraph.const_iff.mp hc) _root_.one_ne_zero
  · exact hr

/-! ### 2. The hinge as a fixed formula -/

/-- The hinge as a fixed formula: "EBot plays C against `DupocBot k`" (EBot by its generic closed description). -/
noncomputable def rEB : Semisentence LAct 1 :=
  qT gDu (TS gDu 0) (uS gDu 0) (wS gDu 0) (cl (canonicalMeta (progCode EBot))) (revalueUMeta (progCode EBot))
    (revalueWMeta (progCode EBot))

theorem guardCode_rEB (k : V) :
    guardCode (⌜gDu⌝ : V) (SV gDu 0 k) ((progCode EBot : ℕ) : V) = instB (⌜rEB⌝ : V) k :=
  guardCode_qT_eq_instB gDu k _ _ _ _ _ _ (hX_SV gDu 0 (Or.inl rfl) k) (hU_SV gDu 0 (Or.inl rfl) k)
    (hW_SV gDu 0 (Or.inl rfl) k)
    (by have := (describes_closed (progCode EBot)).hX V k; rwa [descVal_closed] at this)
    (by have := (describes_closed (progCode EBot)).hU V k; rwa [descVal_closed] at this)
    (by have := (describes_closed (progCode EBot)).hW V k; rwa [descVal_closed] at this)

end ebot

/-! ### 3. The two uniform theorems -/

/-- **`TAct ⊢ ∀ k, r(k) → negTwin(k)`**: in every model and both readings, EBot's cooperation with `DupocBot k`
means Dupoc did not cooperate with `.bot DefectBot`, i.e. its guard `σ_k` (standard reading) or the τ-twin (swapped
reading) was not found within `k`. -/
theorem tact_rEB_imp_negTwin : TAct ⊢ ∀¹ (rEB 🡒 negTwin) := by
  refine tact_all_of_both _ (fun M _ _ x ↦ ?_) (fun M _ _ x ↦ ?_)
  · have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    simp only [LogicalConnective.HomClass.map_imply, LogicalConnective.Prop.arrow_eq]
    intro hr
    rw [rEB, eval_qT_plays_opp_self .C _ _ _ _ _ _ x (desc_SV gDu 0 (Or.inl rfl) x) (descVal_closed (progCode EBot) x),
      actCode_C_cast, cast_EBot] at hr
    rw [eval_negTwin_iff _ (by rw [stdReadingV_eq_stdReading]; exact stdReading_lMap_emb)]
    left
    obtain ⟨n, hn⟩ := hr
    obtain ⟨m, r, hm, hr0⟩ := probe_of_ebot_C_V hn
    rw [lenBoxUnbounded_iff_lenBox, ← guardCode_DuB1]
    exact not_found_of_SV_play hm (by simpa using hr0)
  · have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    simp only [LogicalConnective.HomClass.map_imply, LogicalConnective.Prop.arrow_eq]
    intro hr
    rw [rEB, eval_qT_swap, lMap_swap_gDu, eval_qT_plays_opp_self .D _ _ _ _ _ _ x (descT_SV gDu 0 (Or.inl rfl) x)
      (descVal_closed_T (progCode EBot) x), actCode_D_cast, cast_EBot, transposeCode_EBotV, lMap_swap_gDu] at hr
    rw [eval_negTwin_iff _ swappedReading_lMap_emb]
    right
    obtain ⟨n, hn⟩ := hr
    obtain ⟨m, r, hm, hr1⟩ := probe_of_ebotT_D_V hn
    rw [lenBoxUnbounded_iff_lenBox, ← guardCode_DuB1_swap]
    exact not_found_of_SV_play hm (by simpa using hr1)

/-- **`TAct ⊢ ∀ k ≥ k̂, conjTwin(k) → r(k)`**: neither guard found ⇒ Dupoc's else-branch D against
`.bot DefectBot` ⇒ EBot's first rung falls; above the threshold Dupoc's then-branch C against `.bot CooperateBot`
⇒ the second rung fires C. (Swapped reading: Cupod's else-branch C against `.bot CooperateBot`, then-branch D
against `.bot DefectBot`.) -/
theorem tact_conjTwin_imp_rEB_above :
    ∃ kHat : ℕ, TAct ⊢ ∀¹ ((leF (↑kHat) #0 : Semisentence LAct 1) 🡒 (conjTwin 🡒 rEB)) := by
  obtain ⟨k₁, h₁⟩ := dupoc_botCB_V
  obtain ⟨k₂, h₂⟩ := cupod_botDB_V
  refine ⟨k₁ + k₂, tact_all_above_of_both _ _ (fun M _ _ x hx ↦ ?_) (fun M _ _ x hx ↦ ?_)⟩
  · have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    simp only [LogicalConnective.HomClass.map_imply, LogicalConnective.Prop.arrow_eq]
    intro h
    obtain ⟨h1, _⟩ := (eval_conjTwin_iff _ (by rw [stdReadingV_eq_stdReading]; exact stdReading_lMap_emb) x).mp h
    rw [lenBoxUnbounded_iff_lenBox, ← guardCode_DuB1] at h1
    rw [rEB, eval_qT_plays_opp_self .C _ _ _ _ _ _ x (desc_SV gDu 0 (Or.inl rfl) x) (descVal_closed (progCode EBot) x),
      actCode_C_cast, cast_EBot]
    exact ⟨_, ebot_C_of_probes_V (SV_play_succ_V gDu 0 (dupoc_else_V x _ h1))
      (h₁ M x (le_trans (by push_cast; exact le_self_add) hx))⟩
  · have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    simp only [LogicalConnective.HomClass.map_imply, LogicalConnective.Prop.arrow_eq]
    intro h
    obtain ⟨_, h2⟩ := (eval_conjTwin_iff _ swappedReading_lMap_emb x).mp h
    rw [lenBoxUnbounded_iff_lenBox, ← guardCode_DuB1_swap] at h2
    rw [rEB, eval_qT_swap, lMap_swap_gDu, eval_qT_plays_opp_self .D _ _ _ _ _ _ x (descT_SV gDu 0 (Or.inl rfl) x)
      (descVal_closed_T (progCode EBot) x), actCode_D_cast, cast_EBot, transposeCode_EBotV, lMap_swap_gDu]
    exact ⟨_, ebotT_D_of_probes_V (SV_play_succ_V gCu 1 (cupod_else_V x _ h2))
      (h₂ M x (le_trans (by push_cast; exact le_add_self) hx))⟩

/-! ### 4. At ℕ: the hinge code is the instance of `r`; the reduction and its converse -/

/-- The hinge of Dupoc × EBot, as consulted by the evaluator, is the `binNumeral k`-instance of `rEB`. -/
theorem hinge_DupocBot_vs_EBot_eq (k : ℕ) :
    guardCodeB (templateCode phiDu) (progCode (DupocBot k)) (progCode EBot) k =
      (⌜(rEB ⇜ ![Semiterm.lMap emb (binNumeralMeta k)] : Sentence LAct)⌝ : ℕ) := by
  rw [hingeB phiDu, progCode_DupocBot_SV, templateCode_eq_quote_template phiDu rfl]
  have e := guardCode_rEB (V := ℕ) k
  rw [natCast_nat] at e
  have hq : instB (⌜rEB⌝ : ℕ) k = ⌜(rEB ⇜ ![Semiterm.lMap emb (binNumeralMeta k)] : Sentence LAct)⌝ := by
    have := quote_instB (V := ℕ) rEB k
    rwa [natCast_nat] at this
  rw [← hq]
  exact e

/-- **THE REDUCTION.** If the hinge of Dupoc × EBot holds — "EBot plays C against `DupocBot k`" is `TAct`-provable
within `k` — then "`σ_k` or its τ-twin is NOT provable within `k`" (`σ_k` = Dupoc's guard against `.bot DefectBot`,
FALSE in ℕ; the SAME sentence as for Dupoc × DBot) is `TAct`-provable within `k + C₀ + C₁·size k`. -/
theorem hinge_reduces_to_bounded_consistency_DupocBot_vs_EBot :
    ∃ C₀ C₁ : ℕ, ∀ k : ℕ,
      LenBox TAct k (guardCodeB (templateCode phiDu) (progCode (DupocBot k)) (progCode EBot) k) →
      LenBox TAct (k + C₀ + C₁ * Nat.size k)
        (⌜(negTwin ⇜ ![Semiterm.lMap emb (binNumeralMeta k)] : Sentence LAct)⌝ : ℕ) := by
  obtain ⟨N₃, hN₃⟩ := lenBoxNat_of_provable tact_rEB_imp_negTwin
  refine ⟨N₃ + 13 * formulaLenMeta ((rEB 🡒 negTwin : Semisentence LAct 1) : Semiproposition LAct 1) + 8
      + 20 * formulaLenMeta (rEB : Semiproposition LAct 1) + 20 * formulaLenMeta (negTwin : Semiproposition LAct 1) + 9,
    30 * formulaLenMeta ((rEB 🡒 negTwin : Semisentence LAct 1) : Semiproposition LAct 1) + 6
      + 60 * formulaLenMeta (rEB : Semiproposition LAct 1) + 60 * formulaLenMeta (negTwin : Semiproposition LAct 1),
    fun k hA ↦ ?_⟩
  rw [hinge_DupocBot_vs_EBot_eq, lenBox_nat] at hA
  have h1 := lenBoxNat_inst_size (rEB 🡒 negTwin) k hN₃
  have hχt := formulaLenMeta_subst_binNumeralMeta_le (rEB 🡒 negTwin) k
  have hrt := formulaLenMeta_subst_binNumeralMeta_le rEB k
  have hnt := formulaLenMeta_subst_binNumeralMeta_le negTwin k
  set t : ClosedSemiterm LAct 0 := Semiterm.lMap emb (binNumeralMeta k) with ht
  set s := Nat.size k with hs
  set fχ := formulaLenMeta ((rEB 🡒 negTwin : Semisentence LAct 1) : Semiproposition LAct 1) with hfχ
  set fr := formulaLenMeta (rEB : Semiproposition LAct 1) with hfr
  set fn := formulaLenMeta (negTwin : Semiproposition LAct 1) with hfn
  have h1' : LenBoxNat (codeBound : ℕ → ℕ) (N₃ + 5 * (fχ * (6 * s + 2)) + 3 * fχ + 6 * s + 8) TAct
      (⌜((rEB 🡒 negTwin) ⇜ ![t] : Sentence LAct)⌝ : ℕ) :=
    lenBoxNat_codeBound_mono (by omega) h1
  rw [substs_imp] at h1'
  have h3 := lenBoxNat_mp h1' hA
  rw [lenBox_nat]
  refine lenBoxNat_codeBound_mono ?_ h3
  calc _ ≤ N₃ + 5 * (fχ * (6 * s + 2)) + 3 * fχ + 6 * s + 8 + k
        + 10 * (fr * (6 * s + 2) + fn * (6 * s + 2)) + 9 := by gcongr
    _ = k + (N₃ + 13 * fχ + 8 + 20 * fr + 20 * fn + 9) + (30 * fχ + 6 + 60 * fr + 60 * fn) * s := by ring

/-- **THE CONVERSE.** For `k` above a standard threshold, a `TAct`-proof within `m` of "neither `σ_k` nor its τ-twin
is provable within `k`" yields the hinge — "EBot plays C against `DupocBot k`" — within
`m + C₀ + C₁·size k + C₂·(size k)²`: the instance of the conditional uniform theorem with its threshold cut away
(`exists_instance_length_above`), then one modus ponens. -/
theorem bounded_consistency_reduces_to_hinge_DupocBot_vs_EBot :
    ∃ kHat C₀ C₁ C₂ : ℕ, ∀ k m : ℕ, kHat < k →
      LenBox TAct m (⌜(conjTwin ⇜ ![Semiterm.lMap emb (binNumeralMeta k)] : Sentence LAct)⌝ : ℕ) →
      LenBox TAct (m + C₀ + C₁ * Nat.size k + C₂ * Nat.size k * Nat.size k)
        (guardCodeB (templateCode phiDu) (progCode (DupocBot k)) (progCode EBot) k) := by
  obtain ⟨kHat, hq⟩ := tact_conjTwin_imp_rEB_above
  obtain ⟨K₀, K₁, K₂, hmeta⟩ := exists_instance_length_above (conjTwin 🡒 rEB) kHat hq
  refine ⟨kHat,
    K₀ + 20 * formulaLenMeta (conjTwin : Semiproposition LAct 1) + 20 * formulaLenMeta (rEB : Semiproposition LAct 1) + 9,
    K₁ + 60 * formulaLenMeta (conjTwin : Semiproposition LAct 1) + 60 * formulaLenMeta (rEB : Semiproposition LAct 1),
    K₂, fun k m hk hC ↦ ?_⟩
  rw [lenBox_nat] at hC
  have h1 := hmeta k hk
  have hct := formulaLenMeta_subst_binNumeralMeta_le conjTwin k
  have hrt := formulaLenMeta_subst_binNumeralMeta_le rEB k
  set t : ClosedSemiterm LAct 0 := Semiterm.lMap emb (binNumeralMeta k) with ht
  set s := Nat.size k with hs
  set fc := formulaLenMeta (conjTwin : Semiproposition LAct 1) with hfc
  set fr := formulaLenMeta (rEB : Semiproposition LAct 1) with hfr
  rw [substs_imp] at h1
  have h3 := lenBoxNat_mp h1 hC
  rw [hinge_DupocBot_vs_EBot_eq, lenBox_nat]
  refine lenBoxNat_codeBound_mono ?_ h3
  calc _ ≤ K₀ + K₁ * s + K₂ * s * s + m + 10 * (fc * (6 * s + 2) + fr * (6 * s + 2)) + 9 := by gcongr
    _ = m + (K₀ + 20 * fc + 20 * fr + 9) + (K₁ + 60 * fc + 60 * fr) * s + K₂ * s * s := by ring

end ArithS
