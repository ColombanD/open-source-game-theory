import ArithS.Tau.Watch2
import ArithS.Tau.ClosedWatch

/-!
# ArithS.Tau.ClosedWatch2 — DIMCID's guard over τ(OBot)'s two-stage watch, FOUND (Phase 3e)

`dimcid × obot`: τ(OBot)'s instance seeing DIMCID is the two-stage cascade `W2` (`Tau/Watch2.lean`) over DIMCID's
instances at the cooperator and at the defector — two budget-carrying simple searchers. Under route (c) made
generic its stored description is a constant above the cascade's order threshold and the cascade is a `k̂`-tower,
so DIMCID's self-fulfilling family (`Tau/ClosedWatch.dimcid_closed_found`) applies verbatim.

* `dimcid_D_of_towers` — `Tau/ClosedWatch.dimcid_D_of_W1` with the watch abstracted to what the proof uses: a
  code family `X k`, its `DescribesAbove` towers (both orientations), the constancy of its stored description,
  the values of its abstracted description (`absVal`) and of its tower at ℕ;
* `dimcid_obot_D` — the bit (D, the `S'` flip of the engine's C).

`dimcid × ebot` is the same argument one stage deeper, in `Tau/ClosedWatch3.lean`: τ(EBot)'s instance seeing
DIMCID has a third watch over DIMCID's instance at the MIRROR, the closed system `.sys [dim 1, mm 0] 0`. Until
Phase 2d `codeTermMetaAbs` did not descend into a system and the stored template of DIMCID's instance at τ(EBot)
still wrote `binNumeral k`; it does now (`Agents/CodeTermAbs.codeTermMetaAbs_sys`), and the watch contains a
`.sys`, outside `fragP` — hence the fragment-free `dimcid_D_of_towers'` there.
-/

set_option linter.constructorNameAsVariable false

namespace ArithS.Tau

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open LAct
open PD PD.Tau

/-- **`dimcid × T` is D whenever `T`'s instance seeing DIMCID is a closed program `X k` described above a threshold
by a `k̂`-tower whose stored (budget-abstracted) description is constant** — the self-fulfilling family on the
watch (`dimcid_closed_found`), with the watch given by its interface. -/
theorem dimcid_D_of_towers (T : Tmpl) (K : ℕ) (X : ℕ → ℕ) (TX : Semiterm LAct Empty 1) (uX wX : ClosedSemiterm LAct 0)
    (hD : DescribesAbove K TX uX wX)
    (hDT : DescribesAbove K (Semiterm.lMap swap TX) (Semiterm.lMap swap uX) (Semiterm.lMap swap wX))
    (hconst : ∀ k : ℕ, K ≤ k → closedDescAt (some k) (X k) = closedDescAt (some K) (X K))
    (habs : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (k : V), (K : V) ≤ k → absVal K (X K) k = descVal TX uX wX k)
    (habsT : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (k : V), (K : V) ≤ k →
      absVal K (transposeCode (X K)) k = descVal (Semiterm.lMap swap TX) (Semiterm.lMap swap uX) (Semiterm.lMap swap wX) k)
    (hval : ∀ k : ℕ, K ≤ k → descVal TX uX wX k = X k)
    (hW : ∀ k : ℕ, X k = progCode (.bot (inst (tauZoo k) T .dimcid)))
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
    have e : Semiformula.lMap swap (gDi K c) =
        templateAt (.impl (.plays .self (.bot (inst (tauZoo K) T .dimcid).transpose) .D)
          (.plays (.bot (inst (tauZoo K) T .dimcid).transpose) .self .C)) (some K) := by
      rw [lMap_swap_gDi, templateAt_impl, templateAt_plays_eq, templateAt_plays_eq, progGraphAt_self,
        progGraphAt_closed _ (by simp) (by simp) (pronounP_eq_false_of_noSelfIdxP (hnsXT K)),
        hc, transposeCode_progCode _ (hfrX K)]
      rfl
    rw [e]
    exact isSemiformula7_cast_templateAt _ K (hnsT K) V
  obtain ⟨k₀, h⟩ := dimcid_closed_found K c TX uX wX hD hDT
    (by rw [hcW]; exact habs) (by rw [hcW]; exact habsT) hg7 hg7T
  refine ⟨k₀, fun k hk ↦ ?_⟩
  obtain ⟨hK, hbox⟩ := h k hk
  have e1 : (sDi K c).code k = instCode k .dimcid T := by
    rw [hI k]
    unfold SM.code
    simp only [sDi_g, sDi_a, natCast_nat]
    show pSearch k (⌜gDi K c⌝ : ℕ) (pConst 1) (pConst (1 - 1)) =
      pSearch k (⌜templateAt (dimGf (inst (tauZoo k) T .dimcid)) (some k)⌝ : ℕ) (pConst 1) (pConst 0)
    rw [hg k hK]
  have e2 : descVal TX uX wX k = progCode (.bot (inst (tauZoo k) T .dimcid)) := by
    rw [hval k hK, hW k]
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

/-! ### τ(OBot)'s instance at DIMCID -/

/-- τ(OBot)'s instance at DIMCID: two defection watches, on DIMCID's instances at the cooperator and the defector. -/
noncomputable def WoDi : W2 :=
  ⟨sDiCoop, 1, 1, ⟨sDiDef, 1, 1, 0, Or.inr rfl, Or.inr rfl, Or.inl rfl⟩, Or.inr rfl, Or.inr rfl⟩

lemma WoDi_code (k : ℕ) : pBot (WoDi.code k) = progCode (.bot (inst (tauZoo k) .obot .dimcid)) := by
  rw [progCode_bot_inst, instCode_obot]
  unfold W2.code W1.code
  simp only [WoDi, natCast_nat, sDiCoop_code, sDiDef_code]

theorem instCode_dimcid_obot' (k : ℕ) : instCode k .dimcid .obot =
    pSearch k (templateCodeAt (dimGf (inst (tauZoo k) .obot .dimcid)) k) (pConst 1) (pConst 0) := by
  unfold instCode; rw [inst_dimcid_peel_obot]; simp [actCode]

/-- **`dimcid × obot` is D** — the `S'` flip of the engine's C: the self-fulfilling guard on τ(OBot)'s two-stage
watch. -/
theorem dimcid_obot_D : bitEventually .dimcid .obot .D :=
  dimcid_D_of_towers .obot WoDi.K (fun k ↦ pBot (WoDi.code k)) WoDi.TX WoDi.uT WoDi.wT WoDi.describesBot
    WoDi.describesBotT
    (fun k hk ↦ by rw [W2.closedDescAt_code WoDi hk, W2.closedDescAt_code WoDi le_rfl])
    (fun V _ _ k hk ↦ by rw [W2.absVal_code WoDi le_rfl, W2.descVal_TX WoDi hk])
    (fun V _ _ k hk ↦ by rw [W2.absVal_tr_code WoDi le_rfl, W2.descVal_TX_T WoDi hk])
    (fun k hk ↦ W2.descVal_TX WoDi (le_def.mpr (Nat.eq_or_lt_of_le (by rw [natCast_nat]; exact hk))))
    WoDi_code instCode_dimcid_obot' (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl)
    (fun _ ↦ rfl) (fun _ ↦ rfl)

end ArithS.Tau
