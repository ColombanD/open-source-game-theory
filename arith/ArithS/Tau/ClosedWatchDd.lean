import ArithS.Tau.Dimdid
import ArithS.Tau.ClosedWatch2
import ArithS.Tau.ClosedWatch3
import ArithS.Tau.Entangled.Mirror
import ArithS.Tau.Entangled.DimdidSys

/-!
# ArithS.Tau.ClosedWatchDd — τ(DIMDID)'s two cascade slots: `dimdid × obot = D`, `dimdid × ebot = C` (2026-10-19)

τ(DIMDID)'s instance at a hypothesis `T` is `.search k (ddGf X) (.const D) (.const C)` with `X = inst T dimdid`
("if I defect against `X`, `X` defects against me"), stored on the budget-abstracted template
`templateCodeAt (ddGf X) k`. The two hypotheses whose instance seeing DIMDID is a run-stage CASCADE:

* **`dimdid × obot` is D** — a POS chain, no Löb (§2–§3): τ(OBot)'s instance at DIMDID is the two-stage watch
  `WoDd : W2` over DIMDID's instances at the cooperator and at the defector (`ClosedWatch2.WoDi` with the DIMDID
  members). The consequent of DIMDID's guard, "the cascade defects against me", is TRUE in every model above a
  standard threshold: the second stage fires because DIMDID's instance at the defector finds its guard
  (`implC .D .D .D`, a `TAct`-theorem instance), and the first stage is total (a search is decided in every model),
  so whatever it sees the cascade ends in D. Hence the guard is a conditional `TAct`-theorem (`tact_qDd_above`,
  the twin of `ClosedWatch.tact_qCi_above`), found in the instance's own frame (`plain_found_above`), then-branch D
  (`dimdid_D_of_W2`, the twin of `cimcic_C_of_W1` one cascade level up).
* **`dimdid × ebot` is C** — the self-defeating guard, fragment-free (§4): τ(EBot)'s instance at DIMDID cooperates
  in every frame (the exploit watch falls on `col_dimdid_defect`, the reciprocity watch fires on `col_dimdid_coop`),
  so a proof of DIMDID's guard would make the instance defect against it and, by soundness, make it defect back —
  against the fact. `Dimdid.dimdid_not_found_of_C` needs `fragF` for the frame move (bit frame `(I, I)` → probe
  frame `(I, X)`), which fails here (`X` contains the system `inst dimdid mirror`); the move is made instead on the
  SIX-variable template: `ddGf X` mentions no `.opp`, so `sentenceAt me opp (ddGf X)` does not depend on `opp`
  (`sentenceAt_ddGf_opp`, a substitution congruence in the style of `ClosedWatch3.plAt_self_closed_subst_congr`),
  and the atom truths are read through `Entangled/Base.models_plays_self_closed`/`models_plays_closed_self`.
-/

set_option linter.constructorNameAsVariable false

namespace ArithS.Tau

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open LAct
open PD PD.Tau

/-! ### 1. DIMDID's guard over a closed watch, as a thirteen-variable template -/

section guard

/-- DIMDID's guard over the closed program `c` (described at the node budget `K`): "if I defect against it, it
defects against me" (`gDi` with both actions `D`; `gCi` with both actions `C`). -/
noncomputable def gDd (K c : ℕ) : Semisentence LAct 13 :=
  plAt selfD (closedDescAt (some K) c) 1 🡒 plAt (closedDescAt (some K) c) selfD 1

/-- τ on the guard: the transposed member is CIMCIC's shape over the transposed watch. -/
lemma lMap_swap_gDd (K c : ℕ) : Semiformula.lMap swap (gDd K c) =
    plAt selfD (closedDescAt (some K) (transposeCode c)) 0 🡒 plAt (closedDescAt (some K) (transposeCode c)) selfD 0 := by
  unfold gDd
  rw [LogicalConnective.HomClass.map_imply, lMap_swap_plAt, lMap_swap_plAt, lMap_swap_selfD, lMap_swap_closedDescAt,
    swapAction_one']

/-- `templateAt (ddGf X) (some K)` IS `gDd K (progCode (.bot X))` for a closed, pronoun-free `X`. -/
theorem templateAt_ddG_eq (K : ℕ) (X : PD.Prog) (hns : noSelfIdxP (.bot X) = true) :
    templateAt (ddGf X) (some K) = gDd K (progCode (.bot X)) := by
  unfold gDd
  show templateAt (.impl (.plays .self (.bot X) .D) (.plays (.bot X) .self .D)) (some K) = _
  rw [templateAt_impl, templateAt_plays_eq, templateAt_plays_eq, progGraphAt_self,
    progGraphAt_closed _ (by simp) (by simp) (pronounP_eq_false_of_noSelfIdxP hns)]
  rfl

/-- **DIMDID's guard over a watch that defects against everyone is a conditional `TAct`-theorem** (the consequent
holds; the transposed watch cooperates with everyone in the swapped reading) — `tact_qCi_above` with the actions
exchanged. -/
theorem tact_qDd_above (K c : ℕ) (TX : Semiterm LAct Empty 1) (uX wX : ClosedSemiterm LAct 0)
    (habs : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (k : V), (K : V) ≤ k → absVal K c k = descVal TX uX wX k)
    (habsT : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (k : V), (K : V) ≤ k →
      absVal K (transposeCode c) k = descVal (Semiterm.lMap swap TX) (Semiterm.lMap swap uX) (Semiterm.lMap swap wX) k)
    (hB : ∃ kB : ℕ, ∀ (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (x : M), (kB : M) ≤ x → ∀ me : M,
      ∃ n, EvalGraph n (descVal TX uX wX x) me (descVal TX uX wX x) ((1 : ℕ) : M))
    (hBT : ∃ kB : ℕ, ∀ (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (x : M), (kB : M) ≤ x → ∀ me : M,
      ∃ n, EvalGraph n (descVal (Semiterm.lMap swap TX) (Semiterm.lMap swap uX) (Semiterm.lMap swap wX) x) me
        (descVal (Semiterm.lMap swap TX) (Semiterm.lMap swap uX) (Semiterm.lMap swap wX) x) ((0 : ℕ) : M))
    (X : Semiterm LAct Empty 1) (U W : ClosedSemiterm LAct 0) :
    ∃ kHat : ℕ, TAct ⊢ ∀¹ ((leF (↑kHat) #0 : Semisentence LAct 1) 🡒 qPlain (gDd K c) X U W X U W) := by
  obtain ⟨kB, hB⟩ := hB
  obtain ⟨kBT, hBT⟩ := hBT
  refine ⟨kB + kBT + K, tact_all_above_of_both _ _ (fun M _ _ x hx ↦ ?_) (fun M _ _ x hx ↦ ?_)⟩
  · have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    have hK : (K : M) ≤ x := le_trans (by push_cast; exact le_add_self) hx
    have hkB : (kB : M) ≤ x := le_trans (by push_cast; exact le_trans le_self_add le_self_add) hx
    rw [eval_qPlain_iff]
    unfold gDd
    simp only [LogicalConnective.HomClass.map_imply, LogicalConnective.Prop.arrow_eq]
    intro _
    rw [eval_plAt_closed_self]
    simp only [Matrix.cons_val]
    rw [habs M x hK]
    exact hB M x hkB _
  · have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    have hK : (K : M) ≤ x := le_trans (by push_cast; exact le_add_self) hx
    have hkBT : (kBT : M) ≤ x := le_trans (by push_cast; exact le_trans le_add_self le_self_add) hx
    rw [eval_swappedReading, lMap_swap_qPlain, ← stdReadingV_eq_stdReading, eval_qPlain_iff, lMap_swap_gDd]
    simp only [LogicalConnective.HomClass.map_imply, LogicalConnective.Prop.arrow_eq]
    intro _
    rw [eval_plAt_closed_self]
    simp only [Matrix.cons_val]
    rw [habsT M x hK]
    exact hBT M x hkBT _

end guard

/-! ### 2. The plays of a two-stage watch in every model, at any fuel -/

section plays

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The bot-wrapped member's then-clause at ANY fuel `n + 3` (`SM.bot_then_V` is fuel 3 exactly; there is no fuel
monotonicity in a non-standard model, so the cascade lemmas take their fuels as parameters). -/
theorem SM.bot_then_V' (s : SM) (k me opp n : V)
    (h : LenBox TAct k (guardCodeB ((⌜s.g⌝ : ℕ) : V) me opp k)) :
    EvalGraph (n + 1 + 1 + 1) me opp (pBot (s.code k)) (s.a : V) := by
  rw [EvalGraph.bot_iff]
  unfold SM.code
  rw [EvalGraph.search_iff]
  exact Or.inl ⟨h, EvalGraph.const_iff.mpr rfl⟩

theorem SM.bot_else_V' (s : SM) (k me opp n : V)
    (h : ¬ LenBox TAct k (guardCodeB ((⌜s.g⌝ : ℕ) : V) me opp k)) :
    EvalGraph (n + 1 + 1 + 1) me opp (pBot (s.code k)) ((1 - s.a : ℕ) : V) := by
  rw [EvalGraph.bot_iff]
  unfold SM.code
  rw [EvalGraph.search_iff]
  exact Or.inr ⟨h, EvalGraph.const_iff.mpr rfl⟩

/-- **A bot-wrapped member is total in its own frame, in every model**: a search is decided. -/
theorem SM.bot_self_total (s : SM) (k n : V) :
    ∃ r, EvalGraph (n + 1 + 1 + 1) (pBot (s.code k)) (pBot (s.code k)) (pBot (s.code k)) r := by
  by_cases h : LenBox TAct k (guardCodeB ((⌜s.g⌝ : ℕ) : V) (pBot (s.code k)) (pBot (s.code k)) k)
  · exact ⟨_, SM.bot_then_V' s k _ _ n h⟩
  · exact ⟨_, SM.bot_else_V' s k _ _ n h⟩

/-- The bot-wrapped generic searcher's then-clause at any fuel `n + 3` (`botSV_then_V` is fuel 3 exactly). -/
theorem botSV_then_V' (g : Semisentence LAct 6) (a : ℕ) (k me opp n : V)
    (h : LenBox TAct k (guardCode (⌜g⌝ : V) me opp)) : EvalGraph (n + 1 + 1 + 1) me opp (pBot (SV g a k)) (a : V) := by
  rw [EvalGraph.bot_iff]
  show EvalGraph (n + 1 + 1) me opp (pSearch k (⌜g⌝ : V) (pConst (a : V)) (pConst ((1 - a : ℕ) : V))) (a : V)
  rw [EvalGraph.search_iff₆ (isSemiformula_quote₆ g)]
  exact Or.inl ⟨h, EvalGraph.const_iff.mpr rfl⟩

/-- `ClosedWatch.ofSearch_self_plays` at any fuel `n + 3`. -/
theorem ofSearch_self_plays' (φ : PD.Formula) (hns : noSelfIdxF φ = true) (a : PD.Action)
    (hq : TAct ⊢ ∀¹ qInst (template φ) (actCode a)) :
    ∃ kB : ℕ, ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (x : V), (kB : V) ≤ x → ∀ n : V,
      EvalGraph (n + 1 + 1 + 1) (pBot ((SM.ofSearch φ a).code x)) (pBot ((SM.ofSearch φ a).code x))
        (pBot ((SM.ofSearch φ a).code x)) ((actCode a : ℕ) : V) := by
  obtain ⟨kHat, h⟩ := botSV_found_V (template φ) (actCode a) (actCode_zero_or_one a) hq
  refine ⟨kHat, fun V _ _ x hx n ↦ ?_⟩
  rw [SM.code_ofSearch_eq_SV φ hns]
  exact botSV_then_V' (template φ) (actCode a) x _ _ n (h V x hx)

/-- `ClosedWatch.ofSearch_tr_self_plays` at any fuel `n + 3`. -/
theorem ofSearch_tr_self_plays' (φ : PD.Formula) (hns : noSelfIdxF φ = true) (hfr : fragF φ = true) (a : PD.Action)
    (hq : TAct ⊢ ∀¹ qInst (template φ.transpose) (1 - actCode a)) :
    ∃ kB : ℕ, ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (x : V), (kB : V) ≤ x → ∀ n : V,
      EvalGraph (n + 1 + 1 + 1) (pBot ((SM.ofSearch φ a).tr.code x)) (pBot ((SM.ofSearch φ a).tr.code x))
        (pBot ((SM.ofSearch φ a).tr.code x)) ((1 - actCode a : ℕ) : V) := by
  obtain ⟨kHat, h⟩ := botSV_found_V (template φ.transpose) (1 - actCode a)
    (by rcases actCode_zero_or_one a with h | h <;> simp [h]) hq
  refine ⟨kHat, fun V _ _ x hx n ↦ ?_⟩
  rw [SM.tr_code_ofSearch_eq_SV φ hns hfr]
  exact botSV_then_V' (template φ.transpose) (1 - actCode a) x _ _ n (h V x hx)

/-- **A bot-wrapped two-stage watch whose inner watch fires plays the inner then-constant, whatever the first stage
sees**, when the first-stage then-constant is the same value: the first stage is total (`h₀`, any result `r`), the
inner member hits its test (`h₁`). -/
theorem W2.bot_plays_of (W : W2) (x : V) {n r : V} (me opp : V)
    (h₀ : EvalGraph (n + 1) (pBot (W.s₀.code x)) (pBot (W.s₀.code x)) (pBot (W.s₀.code x)) r)
    (h₁ : EvalGraph n (pBot (W.w.s.code x)) (pBot (W.w.s.code x)) (pBot (W.w.s.code x)) (W.w.t : V))
    (hp : (W.p₀ : V) = (W.w.p : V)) :
    EvalGraph (n + 1 + 1 + 1 + 1) me opp (pBot (W.code x)) (W.w.p : V) := by
  unfold W2.code
  rw [EvalGraph.bot_iff, EvalGraph.ite_iff]
  refine ⟨r, ?_, ?_⟩
  · rw [EvalGraph.sim_iff, substCode_bot]; exact h₀
  · by_cases hr : r = (W.t₀ : V)
    · refine Or.inl ⟨hr, ?_⟩
      rw [EvalGraph.const_iff]
      exact hp.symm
    · refine Or.inr ⟨hr, ?_⟩
      unfold W1.code
      rw [EvalGraph.ite_iff]
      refine ⟨(W.w.t : V), ?_, Or.inl ⟨rfl, ?_⟩⟩
      · rw [EvalGraph.sim_iff, substCode_bot]; exact h₁
      · rw [EvalGraph.const_iff]

end plays

/-! ### 3. `dimdid × obot`: the POS chain on τ(OBot)'s two-stage watch -/

section obot

/-- DIMDID's instance at the cooperator, as a simple member. -/
noncomputable def sDdCoop : SM := SM.ofSearch (implC .C .D .D) .D
/-- DIMDID's instance at the defector. -/
noncomputable def sDdDef : SM := SM.ofSearch (implC .D .D .D) .D

lemma sDdCoop_code (k : ℕ) : sDdCoop.code k = instCode k .dimdid .coop := by
  rw [instCode_dimdid_coop]; unfold sDdCoop SM.code
  simp only [SM.ofSearch_g, SM.ofSearch_a, natCast_nat, actCode]; rfl
lemma sDdDef_code (k : ℕ) : sDdDef.code k = instCode k .dimdid .defect := by
  rw [instCode_dimdid_defect]; unfold sDdDef SM.code
  simp only [SM.ofSearch_g, SM.ofSearch_a, natCast_nat, actCode]; rfl

/-- τ(OBot)'s instance at DIMDID: two defection watches, on DIMDID's instances at the cooperator and the defector
(`ClosedWatch2.WoDi` with the DIMDID members). -/
noncomputable def WoDd : W2 :=
  ⟨sDdCoop, 1, 1, ⟨sDdDef, 1, 1, 0, Or.inr rfl, Or.inr rfl, Or.inl rfl⟩, Or.inr rfl, Or.inr rfl⟩

lemma WoDd_code (k : ℕ) : pBot (WoDd.code k) = progCode (.bot (inst (tauZoo k) .obot .dimdid)) := by
  rw [progCode_bot_inst, instCode_obot]
  unfold W2.code W1.code
  simp only [WoDd, natCast_nat, sDdCoop_code, sDdDef_code]

/-- **τ(OBot)'s instance at DIMDID defects against everyone above a threshold, in every model**: DIMDID's instance at
the defector finds its guard (`tact_qInst_implC .D .D`), so the second watch fires D; the first watch is total. -/
theorem WoDd_plays_D : ∃ kB : ℕ, ∀ (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (x : M), (kB : M) ≤ x → ∀ me : M,
    ∃ n, EvalGraph n (pBot (WoDd.code x)) me (pBot (WoDd.code x)) ((1 : ℕ) : M) := by
  obtain ⟨kB, h⟩ := ofSearch_self_plays' (implC .D .D .D) rfl .D (tact_qInst_implC .D .D 1)
  refine ⟨kB, fun M _ _ x hx me ↦ ?_⟩
  have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
  obtain ⟨r, hr⟩ := SM.bot_self_total sDdCoop x (0 + 1 + 1 + 1 + 1)
  have h' : EvalGraph (0 + 1 + 1 + 1 + 1 + 1 + 1) (pBot (WoDd.w.s.code x)) (pBot (WoDd.w.s.code x))
      (pBot (WoDd.w.s.code x)) (WoDd.w.t : M) := by
    have := h M x hx (0 + 1 + 1 + 1)
    rwa [actCode_D] at this
  exact ⟨_, W2.bot_plays_of WoDd x _ me hr h' rfl⟩

/-- …and its transposition cooperates with everyone: the transposed second member is CIMCIC's instance at the
cooperator (`implC .C .C .C`, a theorem instance), firing C. -/
theorem WoDd_tr_plays_C : ∃ kB : ℕ, ∀ (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (x : M), (kB : M) ≤ x → ∀ me : M,
    ∃ n, EvalGraph n (pBot (WoDd.tr.code x)) me (pBot (WoDd.tr.code x)) ((0 : ℕ) : M) := by
  obtain ⟨kB, h⟩ := ofSearch_tr_self_plays' (implC .D .D .D) rfl rfl .D (tact_qInst_implC .C .C 0)
  refine ⟨kB, fun M _ _ x hx me ↦ ?_⟩
  have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
  obtain ⟨r, hr⟩ := SM.bot_self_total sDdCoop.tr x (0 + 1 + 1 + 1 + 1)
  have h' : EvalGraph (0 + 1 + 1 + 1 + 1 + 1 + 1) (pBot (WoDd.tr.w.s.code x)) (pBot (WoDd.tr.w.s.code x))
      (pBot (WoDd.tr.w.s.code x)) (WoDd.tr.w.t : M) := by
    have := h M x hx (0 + 1 + 1 + 1)
    rwa [actCode_D] at this
  exact ⟨_, W2.bot_plays_of WoDd.tr x _ me hr h' rfl⟩

/-- **`dimdid × T` is D whenever `T`'s instance seeing DIMDID is a `W2` watch that defects against everyone above a
threshold (and its transposition cooperates)**: the consequent of DIMDID's guard holds in both readings —
`cimcic_C_of_W1` one cascade level up, with the actions exchanged. -/
theorem dimdid_D_of_W2 (T : Tmpl) (W : W2)
    (hW : ∀ k : ℕ, pBot (W.code k) = progCode (.bot (inst (tauZoo k) T .dimdid)))
    (hI : ∀ k : ℕ, instCode k .dimdid T =
      pSearch k (templateCodeAt (ddGf (inst (tauZoo k) T .dimdid)) k) (pConst 1) (pConst 0))
    (hnsF : ∀ k, noSelfIdxF (ddGf (inst (tauZoo k) T .dimdid)) = true)
    (hnsX : ∀ k, noSelfIdxP (.bot (inst (tauZoo k) T .dimdid)) = true)
    (hB : ∃ kB : ℕ, ∀ (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (x : M), (kB : M) ≤ x → ∀ me : M,
      ∃ n, EvalGraph n (pBot (W.code x)) me (pBot (W.code x)) ((1 : ℕ) : M))
    (hBT : ∃ kB : ℕ, ∀ (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (x : M), (kB : M) ≤ x → ∀ me : M,
      ∃ n, EvalGraph n (pBot (W.tr.code x)) me (pBot (W.tr.code x)) ((0 : ℕ) : M)) :
    bitEventually .dimdid T .D := by
  set K := W.K with hKdef
  set c : ℕ := progCode (.bot (inst (tauZoo K) T .dimdid)) with hc
  have hcW : c = pBot (W.code K) := by rw [hc, ← hW K]
  have hg : ∀ k : ℕ, K ≤ k → templateAt (ddGf (inst (tauZoo k) T .dimdid)) (some k) = gDd K c := by
    intro k hk
    rw [templateAt_ddG_eq k _ (hnsX k)]
    unfold gDd
    rw [← hW k, hcW, W2.closedDescAt_code W hk, W2.closedDescAt_code W le_rfl]
  have hg7 : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁], IsSemiformula LAct 7 ((⌜gDd K c⌝ : ℕ) : V) := by
    intro V _ _
    rw [← templateAt_ddG_eq K _ (hnsX K)]
    exact isSemiformula7_cast_templateAt _ K (hnsF K) V
  obtain ⟨kB, hB⟩ := hB
  obtain ⟨kBT, hBT⟩ := hBT
  have hB' : ∃ kB : ℕ, ∀ (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (x : M), (kB : M) ≤ x → ∀ me : M,
      ∃ n, EvalGraph n (descVal W.TX W.uT W.wT x) me (descVal W.TX W.uT W.wT x) ((1 : ℕ) : M) := by
    refine ⟨kB + K, fun M _ _ x hx me ↦ ?_⟩
    have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    rw [W2.descVal_TX W (le_trans (by push_cast; exact le_add_self) hx)]
    exact hB M x (le_trans (by push_cast; exact le_self_add) hx) me
  have hBT' : ∃ kB : ℕ, ∀ (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (x : M), (kB : M) ≤ x → ∀ me : M,
      ∃ n, EvalGraph n (descVal (Semiterm.lMap swap W.TX) (Semiterm.lMap swap W.uT) (Semiterm.lMap swap W.wT) x) me
        (descVal (Semiterm.lMap swap W.TX) (Semiterm.lMap swap W.uT) (Semiterm.lMap swap W.wT) x) ((0 : ℕ) : M) := by
    refine ⟨kBT + K, fun M _ _ x hx me ↦ ?_⟩
    have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    rw [W2.descVal_TX_T W (le_trans (by push_cast; exact le_add_self) hx)]
    exact hBT M x (le_trans (by push_cast; exact le_self_add) hx) me
  set sDd : SM := ⟨gDd K c, 1, Or.inr rfl⟩ with hsDd
  obtain ⟨kHat, hq⟩ := tact_qDd_above K c W.TX W.uT W.wT
    (fun V _ _ k hk ↦ by rw [hcW, W2.absVal_code W le_rfl, W2.descVal_TX W hk])
    (fun V _ _ k hk ↦ by rw [hcW, W2.absVal_tr_code W le_rfl, W2.descVal_TX_T W hk])
    hB' hBT' sDd.TB sDd.uT sDd.wT
  obtain ⟨k₀, h⟩ := plain_found_above (gDd K c) hg7 1 (Or.inr rfl) K kHat hq
  refine ⟨k₀, fun k hk ↦ ?_⟩
  obtain ⟨hK, hbox⟩ := h k hk
  have e1 : sDd.code k = instCode k .dimdid T := by
    rw [hI k]
    unfold SM.code
    simp only [hsDd, natCast_nat]
    show pSearch k (⌜gDd K c⌝ : ℕ) (pConst 1) (pConst (1 - 1)) =
      pSearch k (⌜templateAt (ddGf (inst (tauZoo k) T .dimdid)) (some k)⌝ : ℕ) (pConst 1) (pConst 0)
    rw [hg k hK]
  have e3 : (⌜gDd K c⌝ : ℕ) = templateCodeAt (ddGf (inst (tauZoo k) T .dimdid)) k := by
    show _ = (⌜templateAt (ddGf (inst (tauZoo k) T .dimdid)) (some k)⌝ : ℕ)
    rw [hg k hK]
  rw [e1, e3, guardCodeB_templateCodeAt _ _ _ _ (hnsF k), hI k] at hbox
  exact bitPlays_of_eq (hI k) ⟨_, search_then_at _ hbox (const_play 0 _ _ _) (hnsF k)⟩

/-- **`dimdid × obot` is D**: DIMDID's guard "if I defect against τ(OBot)'s instance, it defects against me" has a
true consequent in every model — the cascade ends in D once DIMDID's instance at the defector finds its guard. -/
theorem dimdid_obot_D : bitEventually .dimdid .obot .D :=
  dimdid_D_of_W2 .obot WoDd WoDd_code instCode_dimdid_obot' (fun _ ↦ rfl) (fun _ ↦ rfl) WoDd_plays_D WoDd_tr_plays_C

end obot

/-! ### 4. `dimdid × ebot`: the self-defeating guard, fragment-free -/

section ebot

/-- `descF #1 #2 #3 #4` in the seven-variable frame under a substitution: the program variable and the me-triple. -/
lemma descF_self7_subst {m : ℕ} (w : Fin 7 → Semiterm LAct Empty m) :
    (descF #1 #2 #3 #4 : Semisentence LAct 7) ⇜ w =
      descF (Rew.bShift (w 0)) (Rew.bShift (w 1)) (Rew.bShift (w 2)) (Rew.bShift (w 3)) := by
  unfold Rewriting.subst
  rw [rew_descF]
  rfl

/-- "Me plays `a` against the closed `X`" (six-variable template) reads the me-triple only. -/
theorem template_plays_self_closed_congr {m : ℕ} (X : PD.Prog) (hX1 : X ≠ .self) (hX2 : X ≠ .opp) (a : PD.Action)
    (v v' : Fin 6 → Semiterm LAct Empty m) (h0 : v 0 = v' 0) (h1 : v 1 = v' 1) (h2 : v 2 = v' 2) :
    template (.plays .self X a) ⇜ v = template (.plays .self X a) ⇜ v' := by
  rw [template_plays]
  unfold progGraph
  rw [progAux_self, progAux_of_ne hX1 hX2]
  simp only [Rewriting.app_exs, Rew.q_subst, LogicalConnective.HomClass.map_and, rew_subst_eq]
  congr 4
  · rw [descF_self7_subst, descF_self7_subst]
    congr 1
    · show Rew.bShift (Rew.bShift (Rew.bShift (Rew.bShift (v 0)))) = Rew.bShift (Rew.bShift (Rew.bShift (Rew.bShift (v' 0))))
      rw [h0]
    · show Rew.bShift (Rew.bShift (Rew.bShift (Rew.bShift (v 1)))) = Rew.bShift (Rew.bShift (Rew.bShift (Rew.bShift (v' 1))))
      rw [h1]
    · show Rew.bShift (Rew.bShift (Rew.bShift (Rew.bShift (v 2)))) = Rew.bShift (Rew.bShift (Rew.bShift (Rew.bShift (v' 2))))
      rw [h2]
  · congr 1
    · rw [closedDesc_subst, closedDesc_subst]; rfl
    · congr 1
      funext i
      fin_cases i
      · rfl
      · rfl
      · rfl
      · rfl
      · exact (rew_cl _ _).trans (rew_cl _ _).symm

/-- "The closed `X` plays `a` against me" reads the me-triple only. -/
theorem template_plays_closed_self_congr {m : ℕ} (X : PD.Prog) (hX1 : X ≠ .self) (hX2 : X ≠ .opp) (a : PD.Action)
    (v v' : Fin 6 → Semiterm LAct Empty m) (h0 : v 0 = v' 0) (h1 : v 1 = v' 1) (h2 : v 2 = v' 2) :
    template (.plays X .self a) ⇜ v = template (.plays X .self a) ⇜ v' := by
  rw [template_plays]
  unfold progGraph
  rw [progAux_self, progAux_of_ne hX1 hX2]
  simp only [Rewriting.app_exs, Rew.q_subst, LogicalConnective.HomClass.map_and, rew_subst_eq]
  congr 4
  · rw [closedDesc_subst, closedDesc_subst]; rfl
  · congr 1
    · rw [descF_self7_subst, descF_self7_subst]
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

/-- **DIMDID's guard over a closed `X` does not read the opponent**: its realization is the same sentence in the
frames `(me, opp)` and `(me, opp')` — the fragment-free frame move (`guardOf_implConst_frame` for any closed `X`). -/
theorem sentenceAt_ddGf_opp (X me opp opp' : PD.Prog) :
    sentenceAt me opp (ddGf X) = sentenceAt me opp' (ddGf X) := by
  unfold sentenceAt
  show template (.impl (.plays .self (.bot X) .D) (.plays (.bot X) .self .D)) ⇜ _ =
    template (.impl (.plays .self (.bot X) .D) (.plays (.bot X) .self .D)) ⇜ _
  rw [template_impl]
  have e1 := template_plays_self_closed_congr (.bot X) (by simp) (by simp) .D
    (descriptionTerms (progCode me) (progCode opp)) (descriptionTerms (progCode me) (progCode opp')) rfl rfl rfl
  have e2 := template_plays_closed_self_congr (.bot X) (by simp) (by simp) .D
    (descriptionTerms (progCode me) (progCode opp)) (descriptionTerms (progCode me) (progCode opp')) rfl rfl rfl
  unfold Rewriting.subst at e1 e2 ⊢
  rw [LogicalConnective.HomClass.map_imply, LogicalConnective.HomClass.map_imply, e1, e2]

/-- **DIMDID's guard against a hypothesis whose instance cooperates with it is never found** — `Dimdid.dimdid_not_found_of_C`
without the fragment hypotheses: the frame move is `sentenceAt_ddGf_opp`, the atoms are read by
`models_plays_self_closed`/`models_plays_closed_self`. -/
theorem dimdid_not_found_of_C' {k : ℕ} {T : Tmpl}
    (hI : instCode k .dimdid T =
      pSearch k (templateCodeAt (ddGf (inst (tauZoo k) T .dimdid)) k) (pConst 1) (pConst 0))
    (hns : noSelfIdxF (ddGf (inst (tauZoo k) T .dimdid)) = true)
    (hC : ∀ me opp : PD.Prog, ∃ n, EvalGraph n (progCode me) (progCode opp) (instCode k T .dimdid) 0) :
    ¬ LenBox TAct k (guardOf (ddGf (inst (tauZoo k) T .dimdid))
      (.bot (inst (tauZoo k) .dimdid T)) (.bot (inst (tauZoo k) .dimdid T))) := by
  intro hf
  -- the same sentence in the probe frame `(me, .bot X)`: the template mentions no `.opp`
  have hf' : LenBox TAct k (guardOf (ddGf (inst (tauZoo k) T .dimdid))
      (.bot (inst (tauZoo k) .dimdid T)) (.bot (inst (tauZoo k) T .dimdid))) := by
    rw [guardOf_eq_quote_sentenceAt _ _ _ hns] at hf ⊢
    rw [sentenceAt_ddGf_opp _ _ _ (.bot (inst (tauZoo k) .dimdid T))]
    exact hf
  -- so the instance defects against `.bot X`
  have hD : EvalGraph 3 (progCode (PD.Prog.bot (inst (tauZoo k) .dimdid T)))
      (progCode (PD.Prog.bot (inst (tauZoo k) T .dimdid)))
      (progCode (PD.Prog.bot (inst (tauZoo k) .dimdid T))) (actCode .D) := by
    unfold guardOf at hf'
    rw [progCode_bot_inst, progCode_bot_inst, hI] at hf' ⊢
    show EvalGraph (2 + 1) _ _ _ _
    rw [EvalGraph.bot_iff]
    exact search_then_at _ hf' (const_play 0 _ _ _) hns
  -- by soundness the guard is true in ℕ: `.bot X` defects against the instance — against the fact
  have hT := models_sentenceAt_of_lenBox hf' hns
  change ℕ↓[LAct] ⊧ sentenceAt (.bot (inst (tauZoo k) .dimdid T)) (.bot (inst (tauZoo k) T .dimdid))
    (.impl (.plays .self (.bot (inst (tauZoo k) T .dimdid)) .D)
      (.plays (.bot (inst (tauZoo k) T .dimdid)) .self .D)) at hT
  rw [models_sentenceAt_impl,
    models_plays_self_closed (.bot (inst (tauZoo k) .dimdid T)) (.bot (inst (tauZoo k) T .dimdid))
      (.bot (inst (tauZoo k) T .dimdid)) (by simp) (by simp) .D,
    models_plays_closed_self (.bot (inst (tauZoo k) .dimdid T)) (.bot (inst (tauZoo k) T .dimdid))
      (.bot (inst (tauZoo k) T .dimdid)) (by simp) (by simp) .D] at hT
  obtain ⟨N', hN'⟩ := hT ⟨3, hD⟩
  obtain ⟨N'', rfl, _⟩ := EvalGraph.case_iff.mp hN'
  rw [progCode_bot_inst, EvalGraph.bot_iff] at hN'
  obtain ⟨n, hn⟩ := hC (.bot (inst (tauZoo k) T .dimdid)) (.bot (inst (tauZoo k) .dimdid T))
  rw [progCode_bot_inst] at hn
  exact absurd (EvalGraph.unique' hN' hn) (by decide)

/-- **`dimdid × ebot` is C**: τ(EBot)'s instance at DIMDID cooperates in every frame (the exploit watch falls on
DIMDID's D at the defector, the reciprocity watch fires on its C at the cooperator), so DIMDID's self-defeating guard
is never found and it cooperates. -/
theorem dimdid_ebot_C : bitEventually .dimdid .ebot .C := by
  refine bitEventually.mono (fun k h ↦ ?_) col_dimdid_defect
  obtain ⟨n₁, h₁⟩ := h
  obtain ⟨n₂, h₂⟩ := col_dimdid_coop k
  refine dimdid_C_of_not_found (instCode_dimdid_ebot' k) rfl
    (dimdid_not_found_of_C' (instCode_dimdid_ebot' k) rfl fun me opp ↦ ?_)
  rw [instCode_ebot]
  exact ⟨_, watch_falls' h₁ (by decide) (watch_fires' h₂ (const_play 0 _ _ _))⟩

end ebot

end ArithS.Tau
