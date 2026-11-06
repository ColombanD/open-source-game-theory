import ArithS.Tau.ClosedWatchDd

/-!
# ArithS.Tau.ClosedWatchCu — `cupod × obot = D`: Cupod's defection probe of τ(OBot)'s cascade, FOUND

The tau image of `Cells/CupodOBot.khat_CupodBot_vs_OBot` (the base cell `CupodBot × OBot = (D, D)`, a FLIP of the
engine's `(C, D)`). τ(Cupod)'s instance at τ(OBot) is `.search k (probeD X) (.const D) (.const C)` with
`X = inst obot cupod`, stored on the budget-abstracted template `templateCodeAt (probeD X) k`; `X` is the two-stage
watch `WoCu : W2` over Cupod's instances at the cooperator and at the defector (`ClosedWatch2.WoDi` with the Cupod
members). The probe "the cascade defects against itself" is TRUE in every model above a standard threshold, and not
through anyone's else-play: the SECOND stage fires because Cupod's instance at the defector finds its guard (the
closed probe `prC .D .D`, a `TAct`-theorem instance), and the FIRST stage is total (a search is decided in every
model), so whatever it sees the cascade ends in D. Hence the probe is a conditional `TAct`-theorem
(`tact_qPrD_above`, `ClosedWatch.tact_qPr_above` with the actions exchanged), found in the instance's own frame
(`plain_found_above`), then-branch D (`cupod_D_of_W2`, `ClosedWatch.dupoc_C_of_W1` one cascade level up).

Until 2026-11-05 the bit was a FLOOR bit (base `dich_CupodBot_vs_OBot`): the verdict pass read OBot's evaluation,
which runs through Cupod's else-play at the cooperator, and missed that the defection is over-determined — the
argument of `ClosedWatchDd.WoDd_plays_D` (`dimdid × obot`), which applies verbatim.
-/

set_option linter.constructorNameAsVariable false

namespace ArithS.Tau

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open LAct
open PD PD.Tau

/-! ### 1. Cupod's defection probe of a closed watch, as a thirteen-variable template -/

section guard

/-- Cupod's defection probe of the closed program `c` (described at the node budget `K`): "it defects against
itself" (`ClosedWatch.gPr` with the action `D`). -/
noncomputable def gPrDW (K c : ℕ) : Semisentence LAct 13 := plAt (closedDescAt (some K) c) (closedDescAt (some K) c) 1

lemma lMap_swap_gPrD (K c : ℕ) : Semiformula.lMap swap (gPrDW K c) =
    plAt (closedDescAt (some K) (transposeCode c)) (closedDescAt (some K) (transposeCode c)) 0 := by
  unfold gPrDW
  rw [lMap_swap_plAt, lMap_swap_closedDescAt, swapAction_one']

theorem templateAt_probeD_eq (K : ℕ) (X : PD.Prog) (hns : noSelfIdxP (.bot X) = true) :
    templateAt (.plays (.bot X) (.bot X) .D) (some K) = gPrDW K (progCode (.bot X)) := by
  unfold gPrDW
  rw [templateAt_plays_eq, progGraphAt_closed _ (by simp) (by simp) (pronounP_eq_false_of_noSelfIdxP hns)]
  rfl

/-- **Cupod's defection probe of a watch that defects against itself is a conditional `TAct`-theorem** (the
transposed watch cooperates with itself in the swapped reading). -/
theorem tact_qPrD_above (K c : ℕ) (TX : Semiterm LAct Empty 1) (uX wX : ClosedSemiterm LAct 0)
    (habs : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (k : V), (K : V) ≤ k → absVal K c k = descVal TX uX wX k)
    (habsT : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (k : V), (K : V) ≤ k →
      absVal K (transposeCode c) k = descVal (Semiterm.lMap swap TX) (Semiterm.lMap swap uX) (Semiterm.lMap swap wX) k)
    (hB : ∃ kB : ℕ, ∀ (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (x : M), (kB : M) ≤ x →
      ∃ n, EvalGraph n (descVal TX uX wX x) (descVal TX uX wX x) (descVal TX uX wX x) ((1 : ℕ) : M))
    (hBT : ∃ kB : ℕ, ∀ (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (x : M), (kB : M) ≤ x →
      ∃ n, EvalGraph n (descVal (Semiterm.lMap swap TX) (Semiterm.lMap swap uX) (Semiterm.lMap swap wX) x)
        (descVal (Semiterm.lMap swap TX) (Semiterm.lMap swap uX) (Semiterm.lMap swap wX) x)
        (descVal (Semiterm.lMap swap TX) (Semiterm.lMap swap uX) (Semiterm.lMap swap wX) x) ((0 : ℕ) : M))
    (X : Semiterm LAct Empty 1) (U W : ClosedSemiterm LAct 0) :
    ∃ kHat : ℕ, TAct ⊢ ∀¹ ((leF (↑kHat) #0 : Semisentence LAct 1) 🡒 qPlain (gPrDW K c) X U W X U W) := by
  obtain ⟨kB, hB⟩ := hB
  obtain ⟨kBT, hBT⟩ := hBT
  refine ⟨kB + kBT + K, tact_all_above_of_both _ _ (fun M _ _ x hx ↦ ?_) (fun M _ _ x hx ↦ ?_)⟩
  · have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    have hK : (K : M) ≤ x := le_trans (by push_cast; exact le_add_self) hx
    have hkB : (kB : M) ≤ x := le_trans (by push_cast; exact le_trans le_self_add le_self_add) hx
    rw [eval_qPlain_iff]
    unfold gPrDW
    rw [eval_plAt_closed_closed]
    simp only [Matrix.cons_val]
    rw [habs M x hK]
    exact hB M x hkB
  · have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    have hK : (K : M) ≤ x := le_trans (by push_cast; exact le_add_self) hx
    have hkBT : (kBT : M) ≤ x := le_trans (by push_cast; exact le_trans le_add_self le_self_add) hx
    rw [eval_swappedReading, lMap_swap_qPlain, ← stdReadingV_eq_stdReading, eval_qPlain_iff, lMap_swap_gPrD]
    rw [eval_plAt_closed_closed]
    simp only [Matrix.cons_val]
    rw [habsT M x hK]
    exact hBT M x hkBT

end guard

/-! ### 2. The bit from a two-stage watch -/

section bits

/-- **`cupod × T` is D whenever `T`'s instance seeing Cupod is a `W2` watch that defects against itself above a
threshold (and its transposition cooperates with itself)**: the closed defection probe is a conditional
`TAct`-theorem — `ClosedWatch.dupoc_C_of_W1` one cascade level up, with the actions exchanged. -/
theorem cupod_D_of_W2 (T : Tmpl) (W : W2)
    (hW : ∀ k : ℕ, pBot (W.code k) = progCode (.bot (inst (tauZoo k) T .cupod)))
    (hI : ∀ k : ℕ, instCode k .cupod T =
      pSearch k (templateCodeAt (probeD (inst (tauZoo k) T .cupod)) k) (pConst 1) (pConst 0))
    (hnsF : ∀ k, noSelfIdxF (probeD (inst (tauZoo k) T .cupod)) = true)
    (hnsX : ∀ k, noSelfIdxP (.bot (inst (tauZoo k) T .cupod)) = true)
    (hB : ∃ kB : ℕ, ∀ (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (x : M), (kB : M) ≤ x →
      ∃ n, EvalGraph n (pBot (W.code x)) (pBot (W.code x)) (pBot (W.code x)) ((1 : ℕ) : M))
    (hBT : ∃ kB : ℕ, ∀ (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (x : M), (kB : M) ≤ x →
      ∃ n, EvalGraph n (pBot (W.tr.code x)) (pBot (W.tr.code x)) (pBot (W.tr.code x)) ((0 : ℕ) : M)) :
    bitEventually .cupod T .D := by
  set K := W.K with hKdef
  set c : ℕ := progCode (.bot (inst (tauZoo K) T .cupod)) with hc
  have hcW : c = pBot (W.code K) := by rw [hc, ← hW K]
  have hg : ∀ k : ℕ, K ≤ k → templateAt (probeD (inst (tauZoo k) T .cupod)) (some k) = gPrDW K c := by
    intro k hk
    show templateAt (.plays (.bot (inst (tauZoo k) T .cupod)) (.bot (inst (tauZoo k) T .cupod)) .D) (some k) = gPrDW K c
    rw [templateAt_probeD_eq k _ (hnsX k)]
    unfold gPrDW
    rw [← hW k, hcW, W2.closedDescAt_code W hk, W2.closedDescAt_code W le_rfl]
  have hg7 : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁], IsSemiformula LAct 7 ((⌜gPrDW K c⌝ : ℕ) : V) := by
    intro V _ _
    rw [← templateAt_probeD_eq K _ (hnsX K)]
    exact isSemiformula7_cast_templateAt _ K (hnsF K) V
  obtain ⟨kB, hB⟩ := hB
  obtain ⟨kBT, hBT⟩ := hBT
  have hB' : ∃ kB : ℕ, ∀ (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (x : M), (kB : M) ≤ x →
      ∃ n, EvalGraph n (descVal W.TX W.uT W.wT x) (descVal W.TX W.uT W.wT x) (descVal W.TX W.uT W.wT x) ((1 : ℕ) : M) := by
    refine ⟨kB + K, fun M _ _ x hx ↦ ?_⟩
    have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    rw [W2.descVal_TX W (le_trans (by push_cast; exact le_add_self) hx)]
    exact hB M x (le_trans (by push_cast; exact le_self_add) hx)
  have hBT' : ∃ kB : ℕ, ∀ (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (x : M), (kB : M) ≤ x →
      ∃ n, EvalGraph n (descVal (Semiterm.lMap swap W.TX) (Semiterm.lMap swap W.uT) (Semiterm.lMap swap W.wT) x)
        (descVal (Semiterm.lMap swap W.TX) (Semiterm.lMap swap W.uT) (Semiterm.lMap swap W.wT) x)
        (descVal (Semiterm.lMap swap W.TX) (Semiterm.lMap swap W.uT) (Semiterm.lMap swap W.wT) x) ((0 : ℕ) : M) := by
    refine ⟨kBT + K, fun M _ _ x hx ↦ ?_⟩
    have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    rw [W2.descVal_TX_T W (le_trans (by push_cast; exact le_add_self) hx)]
    exact hBT M x (le_trans (by push_cast; exact le_self_add) hx)
  set sPr : SM := ⟨gPrDW K c, 1, Or.inr rfl⟩ with hsPr
  obtain ⟨kHat, hq⟩ := tact_qPrD_above K c W.TX W.uT W.wT
    (fun V _ _ k hk ↦ by rw [hcW, W2.absVal_code W le_rfl, W2.descVal_TX W hk])
    (fun V _ _ k hk ↦ by rw [hcW, W2.absVal_tr_code W le_rfl, W2.descVal_TX_T W hk])
    hB' hBT' sPr.TB sPr.uT sPr.wT
  obtain ⟨k₀, h⟩ := plain_found_above (gPrDW K c) hg7 1 (Or.inr rfl) K kHat hq
  refine ⟨k₀, fun k hk ↦ ?_⟩
  obtain ⟨hK, hbox⟩ := h k hk
  have e1 : sPr.code k = instCode k .cupod T := by
    rw [hI k]
    unfold SM.code
    simp only [hsPr, natCast_nat]
    show pSearch k (⌜gPrDW K c⌝ : ℕ) (pConst 1) (pConst (1 - 1)) =
      pSearch k (⌜templateAt (probeD (inst (tauZoo k) T .cupod)) (some k)⌝ : ℕ) (pConst 1) (pConst 0)
    rw [hg k hK]
  have e3 : (⌜gPrDW K c⌝ : ℕ) = templateCodeAt (probeD (inst (tauZoo k) T .cupod)) k := by
    show _ = (⌜templateAt (probeD (inst (tauZoo k) T .cupod)) (some k)⌝ : ℕ)
    rw [hg k hK]
  rw [e1, e3, guardCodeB_templateCodeAt _ _ _ _ (hnsF k), hI k] at hbox
  exact bitPlays_of_eq (hI k) ⟨_, search_then_at _ hbox (const_play 0 _ _ _) (hnsF k)⟩

/-! ### 3. τ(OBot)'s instance at Cupod -/

/-- Cupod's instance at the cooperator (the closed defection probe of the frozen cooperator: false). -/
noncomputable def sCuCoop : SM := SM.ofSearch (prC .C .D) .D
/-- Cupod's instance at the defector (the closed defection probe of the frozen defector: a theorem). -/
noncomputable def sCuDef : SM := SM.ofSearch (prC .D .D) .D

lemma sCuCoop_code (k : ℕ) : sCuCoop.code k = instCode k .cupod .coop := by
  rw [instCode_cupod_coop]; unfold sCuCoop SM.code
  simp only [SM.ofSearch_g, SM.ofSearch_a, natCast_nat, actCode]; rfl
lemma sCuDef_code (k : ℕ) : sCuDef.code k = instCode k .cupod .defect := by
  rw [instCode_cupod_defect]; unfold sCuDef SM.code
  simp only [SM.ofSearch_g, SM.ofSearch_a, natCast_nat, actCode]; rfl

/-- τ(OBot)'s instance at Cupod: two defection watches, on Cupod's instances at the cooperator and the defector
(`ClosedWatch2.WoDi` with the Cupod members). -/
noncomputable def WoCu : W2 :=
  ⟨sCuCoop, 1, 1, ⟨sCuDef, 1, 1, 0, Or.inr rfl, Or.inr rfl, Or.inl rfl⟩, Or.inr rfl, Or.inr rfl⟩

lemma WoCu_code (k : ℕ) : pBot (WoCu.code k) = progCode (.bot (inst (tauZoo k) .obot .cupod)) := by
  rw [progCode_bot_inst, instCode_obot]
  unfold W2.code W1.code
  simp only [WoCu, natCast_nat, sCuCoop_code, sCuDef_code]

/-- **τ(OBot)'s instance at Cupod defects against everyone above a threshold, in every model**: Cupod's instance at
the defector finds its guard (`tact_qInst_prC .D`), so the second watch fires D; the first watch is total. -/
theorem WoCu_plays_D : ∃ kB : ℕ, ∀ (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (x : M), (kB : M) ≤ x → ∀ me : M,
    ∃ n, EvalGraph n (pBot (WoCu.code x)) me (pBot (WoCu.code x)) ((1 : ℕ) : M) := by
  obtain ⟨kB, h⟩ := ofSearch_self_plays' (prC .D .D) rfl .D (tact_qInst_prC .D 1)
  refine ⟨kB, fun M _ _ x hx me ↦ ?_⟩
  have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
  obtain ⟨r, hr⟩ := SM.bot_self_total sCuCoop x (0 + 1 + 1 + 1 + 1)
  have h' : EvalGraph (0 + 1 + 1 + 1 + 1 + 1 + 1) (pBot (WoCu.w.s.code x)) (pBot (WoCu.w.s.code x))
      (pBot (WoCu.w.s.code x)) (WoCu.w.t : M) := by
    have := h M x hx (0 + 1 + 1 + 1)
    rwa [actCode_D] at this
  exact ⟨_, W2.bot_plays_of WoCu x _ me hr h' rfl⟩

/-- …and its transposition cooperates with everyone: the transposed second member is Dupoc's instance at the
cooperator (`prC .C .C`, a theorem instance), firing C. -/
theorem WoCu_tr_plays_C : ∃ kB : ℕ, ∀ (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (x : M), (kB : M) ≤ x → ∀ me : M,
    ∃ n, EvalGraph n (pBot (WoCu.tr.code x)) me (pBot (WoCu.tr.code x)) ((0 : ℕ) : M) := by
  obtain ⟨kB, h⟩ := ofSearch_tr_self_plays' (prC .D .D) rfl rfl .D (tact_qInst_prC .C 0)
  refine ⟨kB, fun M _ _ x hx me ↦ ?_⟩
  have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
  obtain ⟨r, hr⟩ := SM.bot_self_total sCuCoop.tr x (0 + 1 + 1 + 1 + 1)
  have h' : EvalGraph (0 + 1 + 1 + 1 + 1 + 1 + 1) (pBot (WoCu.tr.w.s.code x)) (pBot (WoCu.tr.w.s.code x))
      (pBot (WoCu.tr.w.s.code x)) (WoCu.tr.w.t : M) := by
    have := h M x hx (0 + 1 + 1 + 1)
    rwa [actCode_D] at this
  exact ⟨_, W2.bot_plays_of WoCu.tr x _ me hr h' rfl⟩

theorem instCode_cupod_obot' (k : ℕ) : instCode k .cupod .obot =
    pSearch k (templateCodeAt (probeD (inst (tauZoo k) .obot .cupod)) k) (pConst 1) (pConst 0) := by
  unfold instCode; rw [inst_cupod_peel_obot]; simp [actCode]

/-- **`cupod × obot` is D** — the tau image of the base flip `CupodBot × OBot = (D, D)`: Cupod's defection probe of
τ(OBot)'s cascade is a true closed probe of a budget-carrying watch, found by the `k̂`-chain. -/
theorem cupod_obot_D : bitEventually .cupod .obot .D :=
  cupod_D_of_W2 .obot WoCu WoCu_code instCode_cupod_obot' (fun _ ↦ rfl) (fun _ ↦ rfl)
    (let ⟨kB, h⟩ := WoCu_plays_D; ⟨kB, fun M _ _ x hx ↦ h M x hx _⟩)
    (let ⟨kB, h⟩ := WoCu_tr_plays_C; ⟨kB, fun M _ _ x hx ↦ h M x hx _⟩)

end bits

end ArithS.Tau
