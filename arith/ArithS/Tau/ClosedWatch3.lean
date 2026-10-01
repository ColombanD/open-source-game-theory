import ArithS.Tau.Watch3
import ArithS.Tau.ClosedWatch2

/-!
# ArithS.Tau.ClosedWatch3 — DIMCID's guard over τ(EBot)'s three-stage watch, FOUND: `dimcid × ebot = D` (Phase 3f)

The last bit of the paper table. τ(EBot)'s instance seeing DIMCID is the three-stage cascade `W3`
(`Tau/Watch3.lean`) over DIMCID's instances at the defector, at the cooperator and at the MIRROR — the last one the
closed system `.sys [dim 1, mm 0] 0`, with the budget-`k` member `dim 1 k`. Under Phase 2c the abstraction did not
enter a system, the stored template of `inst dimcid ebot` wrote `binNumeral k`, and the guard never fitted
(`Tau/NeverFitsSys.lean`: the bit was C at every budget, the engine's value). Since Phase 2d (decision (α)) the
abstraction descends into systems: the stored description of the watch is a CONSTANT above the cascade's order
threshold (`W3.closedDescAt_code`), the watch is a `k̂`-tower (`W3.describesBot`), and DIMCID's self-fulfilling
family (`Tau/ClosedWatch.dimcid_closed_found`) applies as it does to τ(OBot)'s two-stage watch.

One step of `ClosedWatch2.dimcid_D_of_towers` does NOT transfer: it moves the found guard from the probe frame
`(pBot I, X)` to the bit's frame `(pBot I, pBot I)` through `templateCode_subst`, which needs `fragF` — and the
watch contains a `.sys`, outside `fragP`. Here the move is made on the template itself: DIMCID's guard `gDi` reads
the me-triple and the budget slot only (`gDi_subst_congr`), so the two instance formulas are the SAME sentence
(`qPlain_gDi_opp`), and the two instance equations (`guardCodeB_plain_eq_instB`, each frame) give the move. The
transposed seven-variable hypothesis comes from `isSemiformula_revalueTemplate_swap_iff` instead of `fragP`.

* §1 `gDi_subst_congr`, `qPlain_gDi_opp` — the guard does not read the opponent slots;
* §2 `dimcid_D_of_towers'` — `dimcid_D_of_towers` without the fragment hypotheses;
* §3 `WeDi`, `dimcid_ebot_D` — the bit (D, the `S'` flip of the engine's C).
-/

set_option linter.constructorNameAsVariable false

namespace ArithS.Tau

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open LAct
open PD PD.Tau

/-! ### 1. DIMCID's guard does not read the opponent slots -/

/-- The self description under a substitution: the program variable and the me-triple. -/
lemma selfD_subst {m : ℕ} (w : Fin 14 → Semiterm LAct Empty m) :
    selfD ⇜ w = descF (Rew.bShift (w 0)) (Rew.bShift (w 1)) (Rew.bShift (w 2)) (Rew.bShift (w 3)) := by
  unfold selfD Rewriting.subst
  rw [rew_descF]
  rfl

/-- "Me plays `a` against the closed watch" reads the me-triple and the budget slot only. -/
theorem plAt_self_closed_subst_congr {m : ℕ} (K c a : ℕ) (v v' : Fin 13 → Semiterm LAct Empty m)
    (h0 : v 0 = v' 0) (h1 : v 1 = v' 1) (h2 : v 2 = v' 2) (h6 : v 6 = v' 6) :
    plAt selfD (closedDescAt (some K) c) a ⇜ v = plAt selfD (closedDescAt (some K) c) a ⇜ v' := by
  unfold plAt
  simp only [Rewriting.app_exs, Rew.q_subst, LogicalConnective.HomClass.map_and, rew_subst_eq]
  congr 4
  · rw [selfD_subst, selfD_subst]
    congr 1
    · show Rew.bShift (Rew.bShift (Rew.bShift (Rew.bShift (v 0)))) = Rew.bShift (Rew.bShift (Rew.bShift (Rew.bShift (v' 0))))
      rw [h0]
    · show Rew.bShift (Rew.bShift (Rew.bShift (Rew.bShift (v 1)))) = Rew.bShift (Rew.bShift (Rew.bShift (Rew.bShift (v' 1))))
      rw [h1]
    · show Rew.bShift (Rew.bShift (Rew.bShift (Rew.bShift (v 2)))) = Rew.bShift (Rew.bShift (Rew.bShift (Rew.bShift (v' 2))))
      rw [h2]
  · congr 1
    · rw [closedDescAt_subst, closedDescAt_subst]
      congr 2
      show Rew.bShift (Rew.bShift (Rew.bShift (Rew.bShift (v 6)))) = Rew.bShift (Rew.bShift (Rew.bShift (Rew.bShift (v' 6))))
      rw [h6]
    · congr 1
      funext i
      fin_cases i
      · rfl
      · rfl
      · rfl
      · rfl
      · exact (rew_cl _ _).trans (rew_cl _ _).symm

/-- "The closed watch plays `a` against me" reads the me-triple and the budget slot only. -/
theorem plAt_closed_self_subst_congr {m : ℕ} (K c a : ℕ) (v v' : Fin 13 → Semiterm LAct Empty m)
    (h0 : v 0 = v' 0) (h1 : v 1 = v' 1) (h2 : v 2 = v' 2) (h6 : v 6 = v' 6) :
    plAt (closedDescAt (some K) c) selfD a ⇜ v = plAt (closedDescAt (some K) c) selfD a ⇜ v' := by
  unfold plAt
  simp only [Rewriting.app_exs, Rew.q_subst, LogicalConnective.HomClass.map_and, rew_subst_eq]
  congr 4
  · rw [closedDescAt_subst, closedDescAt_subst]
    congr 2
    show Rew.bShift (Rew.bShift (Rew.bShift (Rew.bShift (v 6)))) = Rew.bShift (Rew.bShift (Rew.bShift (Rew.bShift (v' 6))))
    rw [h6]
  · congr 1
    · rw [selfD_subst, selfD_subst]
      congr 1
      · show Rew.bShift (Rew.bShift (Rew.bShift (Rew.bShift (v 0)))) = Rew.bShift (Rew.bShift (Rew.bShift (Rew.bShift (v' 0))))
        rw [h0]
      · show Rew.bShift (Rew.bShift (Rew.bShift (Rew.bShift (v 1)))) = Rew.bShift (Rew.bShift (Rew.bShift (Rew.bShift (v' 1))))
        rw [h1]
      · show Rew.bShift (Rew.bShift (Rew.bShift (Rew.bShift (v 2)))) = Rew.bShift (Rew.bShift (Rew.bShift (Rew.bShift (v' 2))))
        rw [h2]
    · congr 1
      funext i
      fin_cases i
      · rfl
      · rfl
      · rfl
      · rfl
      · exact (rew_cl _ _).trans (rew_cl _ _).symm

/-- **DIMCID's guard over a closed watch reads the me-triple and the budget slot only**: two substitutions that
agree on the slots `#0 #1 #2 #6` give the same formula. -/
theorem gDi_subst_congr {m : ℕ} (K c : ℕ) (v v' : Fin 13 → Semiterm LAct Empty m)
    (h0 : v 0 = v' 0) (h1 : v 1 = v' 1) (h2 : v 2 = v' 2) (h6 : v 6 = v' 6) :
    gDi K c ⇜ v = gDi K c ⇜ v' := by
  have e1 := plAt_self_closed_subst_congr K c 0 v v' h0 h1 h2 h6
  have e2 := plAt_closed_self_subst_congr K c 1 v v' h0 h1 h2 h6
  unfold gDi
  unfold Rewriting.subst at e1 e2 ⊢
  rw [LogicalConnective.HomClass.map_imply, LogicalConnective.HomClass.map_imply, e1, e2]

/-- **The instance formula of DIMCID's guard does not depend on the opponent's towers.** -/
theorem qPlain_gDi_opp (K c : ℕ) (X : Semiterm LAct Empty 1) (U W : ClosedSemiterm LAct 0)
    (X' : Semiterm LAct Empty 1) (U' W' : ClosedSemiterm LAct 0) (X'' : Semiterm LAct Empty 1) (U'' W'' : ClosedSemiterm LAct 0) :
    qPlain (gDi K c) X U W X' U' W' = qPlain (gDi K c) X U W X'' U'' W'' := by
  unfold qPlain qT13
  exact gDi_subst_congr K c _ _ rfl rfl rfl rfl

/-! ### 2. The towers theorem without the fragment hypotheses -/

/-- **`dimcid × T` is D whenever `T`'s instance seeing DIMCID is a closed program `X k` described above a threshold
by a `k̂`-tower whose stored (budget-abstracted) description is constant** — `ClosedWatch2.dimcid_D_of_towers`
without `fragF`/`fragP` (the watch may contain a system): the found guard moves from the probe frame to the bit's
frame because the guard does not read the opponent slots (`qPlain_gDi_opp`). -/
theorem dimcid_D_of_towers' (T : Tmpl) (K : ℕ) (X : ℕ → ℕ) (TX : Semiterm LAct Empty 1) (uX wX : ClosedSemiterm LAct 0)
    (hD : DescribesAbove K TX uX wX)
    (hDT : DescribesAbove K (Semiterm.lMap swap TX) (Semiterm.lMap swap uX) (Semiterm.lMap swap wX))
    (hconst : ∀ k : ℕ, K ≤ k → closedDescAt (some k) (X k) = closedDescAt (some K) (X K))
    (habs : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (k : V), (K : V) ≤ k → absVal K (X K) k = descVal TX uX wX k)
    (habsT : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (k : V), (K : V) ≤ k →
      absVal K (transposeCode (X K)) k = descVal (Semiterm.lMap swap TX) (Semiterm.lMap swap uX) (Semiterm.lMap swap wX) k)
    (hW : ∀ k : ℕ, X k = progCode (.bot (inst (tauZoo k) T .dimcid)))
    (hI : ∀ k : ℕ, instCode k .dimcid T =
      pSearch k (templateCodeAt (dimGf (inst (tauZoo k) T .dimcid)) k) (pConst 1) (pConst 0))
    (hnsF : ∀ k, noSelfIdxF (dimGf (inst (tauZoo k) T .dimcid)) = true)
    (hnsX : ∀ k, noSelfIdxP (.bot (inst (tauZoo k) T .dimcid)) = true) :
    bitEventually .dimcid T .D := by
  set c : ℕ := progCode (.bot (inst (tauZoo K) T .dimcid)) with hc
  have hcW : c = X K := by rw [hc, ← hW K]
  -- the stored template is constant above the threshold
  have hg : ∀ k : ℕ, K ≤ k → templateAt (dimGf (inst (tauZoo k) T .dimcid)) (some k) = gDi K c := by
    intro k hk
    rw [templateAt_dimG_eq k _ (hnsX k)]
    unfold gDi
    rw [← hW k, hcW, hconst k hk]
  have hg7 : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁], IsSemiformula LAct 7 ((⌜gDi K c⌝ : ℕ) : V) := by
    intro V _ _
    rw [← templateAt_dimG_eq K _ (hnsX K)]
    exact isSemiformula7_cast_templateAt _ K (hnsF K) V
  have hg7T : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁],
      IsSemiformula LAct 7 ((⌜Semiformula.lMap swap (gDi K c)⌝ : ℕ) : V) := by
    intro V _ _
    rw [← revalueTemplate_cast_quote]
    exact isSemiformula_revalueTemplate_swap_iff.mpr (hg7 V)
  obtain ⟨k₀, h⟩ := dimcid_closed_found K c TX uX wX hD hDT
    (by rw [hcW]; exact habs) (by rw [hcW]; exact habsT) hg7 hg7T
  refine ⟨k₀, fun k hk ↦ ?_⟩
  obtain ⟨hK, hbox⟩ := h k hk
  -- the two instance equations at ℕ: the probe frame and the bit's frame
  have e := guardCodeB_plain_eq_instB (V := ℕ) (gDi K c) (hg7 ℕ) k (sDi K c).TB (sDi K c).uT (sDi K c).wT TX uX wX
    (SM.hX_TB _ k) (by rw [revalueU_pBot, SM.revalueU_code]) (by rw [revalueW_pBot, SM.revalueW_code])
    (hD.hX ℕ k (le_def.mpr (Nat.eq_or_lt_of_le (by rw [natCast_nat]; exact hK))))
    (hD.hU ℕ k (le_def.mpr (Nat.eq_or_lt_of_le (by rw [natCast_nat]; exact hK))))
    (hD.hW ℕ k (le_def.mpr (Nat.eq_or_lt_of_le (by rw [natCast_nat]; exact hK))))
  have e' := guardCodeB_plain_eq_instB (V := ℕ) (gDi K c) (hg7 ℕ) k (sDi K c).TB (sDi K c).uT (sDi K c).wT
    (sDi K c).TB (sDi K c).uT (sDi K c).wT
    (SM.hX_TB _ k) (by rw [revalueU_pBot, SM.revalueU_code]) (by rw [revalueW_pBot, SM.revalueW_code])
    (SM.hX_TB _ k) (by rw [revalueU_pBot, SM.revalueU_code]) (by rw [revalueW_pBot, SM.revalueW_code])
  rw [natCast_nat] at e e'
  rw [e, qPlain_gDi_opp K c _ _ _ TX uX wX (sDi K c).TB (sDi K c).uT (sDi K c).wT, ← e'] at hbox
  have e1 : (sDi K c).code k = instCode k .dimcid T := by
    rw [hI k]
    unfold SM.code
    simp only [sDi_g, sDi_a, natCast_nat]
    show pSearch k (⌜gDi K c⌝ : ℕ) (pConst 1) (pConst (1 - 1)) =
      pSearch k (⌜templateAt (dimGf (inst (tauZoo k) T .dimcid)) (some k)⌝ : ℕ) (pConst 1) (pConst 0)
    rw [hg k hK]
  have e3 : (⌜gDi K c⌝ : ℕ) = templateCodeAt (dimGf (inst (tauZoo k) T .dimcid)) k := by
    show _ = (⌜templateAt (dimGf (inst (tauZoo k) T .dimcid)) (some k)⌝ : ℕ)
    rw [hg k hK]
  rw [e1, e3, guardCodeB_templateCodeAt _ _ _ _ (hnsF k), hI k] at hbox
  exact bitPlays_of_eq (hI k) ⟨_, search_then_at _ hbox (const_play 0 _ _ _) (hnsF k)⟩

/-! ### 3. τ(EBot)'s instance at DIMCID -/

/-- The mirror member carries no `pSearch` node. -/
lemma noSearchAt_mm0 (K : ℕ) : NoSearchAt K (progCode (mm 0)) := noSearchAt_progCode (mm 0) rfl K

/-- τ(EBot)'s instance at DIMCID: three cooperation watches (`test = C`), on DIMCID's instances at the defector
(then `D`), at the cooperator (then `C`) and at the mirror system (then `C`, else `D`). -/
noncomputable def WeDi : W3 :=
  ⟨sDiDef, 0, 1, sDiCoop, 0, 0, SDiM, 0, 0, 1, Or.inl rfl, Or.inr rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl,
    Or.inr rfl, noSearchAt_mm0⟩

lemma SDiM_code (k : ℕ) : SDiM.code 0 k = instCode k .dimcid .mirror := by
  unfold instCode
  rw [inst_dimcid_mirror]
  exact Sys2c.code_nat (entDimG 1) .D (mm 0) transposeCode_mm0 0 k

lemma WeDi_code (k : ℕ) : pBot (WeDi.code k) = progCode (.bot (inst (tauZoo k) .ebot .dimcid)) := by
  rw [progCode_bot_inst, instCode_ebot]
  unfold W3.code W3.mid W3.inner
  simp only [WeDi, natCast_nat, sDiCoop_code, sDiDef_code, SDiM_code]

theorem instCode_dimcid_ebot' (k : ℕ) : instCode k .dimcid .ebot =
    pSearch k (templateCodeAt (dimGf (inst (tauZoo k) .ebot .dimcid)) k) (pConst 1) (pConst 0) := by
  unfold instCode; rw [inst_dimcid_peel_ebot]; simp [actCode]

/-- **`dimcid × ebot` is D** — the `S'` flip of the engine's C, the last bit of the paper table: the
self-fulfilling guard on τ(EBot)'s three-stage watch, whose third stage names the SYSTEM `inst dimcid mirror` —
described with its member's budget in the slot since Phase 2d. -/
theorem dimcid_ebot_D : bitEventually .dimcid .ebot .D :=
  dimcid_D_of_towers' .ebot WeDi.K (fun k ↦ pBot (WeDi.code k)) WeDi.TX WeDi.uT WeDi.wT WeDi.describesBot
    WeDi.describesBotT
    (fun k hk ↦ by rw [W3.closedDescAt_code WeDi hk, W3.closedDescAt_code WeDi le_rfl])
    (fun V _ _ k hk ↦ by rw [W3.absVal_code WeDi le_rfl, W3.descVal_TX WeDi hk])
    (fun V _ _ k hk ↦ by rw [W3.absVal_tr_code WeDi le_rfl, W3.descVal_TX_T WeDi hk])
    WeDi_code instCode_dimcid_ebot' (fun _ ↦ rfl) (fun _ ↦ rfl)

end ArithS.Tau
