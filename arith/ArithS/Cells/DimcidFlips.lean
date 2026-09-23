import ArithS.Cells.FlipCells

/-!
# ArithS.Cells.DimcidFlips — DIMCID's row: the seven cooperative engine cells are census artifacts

`Cells/FlipCells.lean` proved **`dimcid_vs_described`**: in PA-`S'`, DIMCID defects against EVERY
described opponent and finds its guard — the self-fulfilling Löb never uses the guard's consequent ("my
cooperating implies X" is found because its antecedent "I cooperate" is refuted by the very act of finding
it, whatever `X` is). The engine has DIMCID COOPERATING in seven more cells, every one by a census (a
floor `no_provable_tailToS_floor`, a probe-first floor, or an unreadability census) that cannot read
DIMCID's own guard. This module proves the `S'` value of each, unconditional (`∃ k₀, ∀ k > k₀, …`, three
standard axioms), with the box form, and the row summary.

1. **Every closed code is described** (`describes_closed`): the generic triple `(cl (dnumT P), dUT P,
   dWT P)` of `Template.lean` describes ANY `P : ℕ` in every model (`descVal_closed`,
   `descVal_closed_T`; the absoluteness of `swapcode`/`dnum`: `cast_swapcode`, `cast_dnum`). Hence
   **`dimcid_vs_closed`: DIMCID defects against every closed code** — DBot, EBot, OBot, the frozen probes
   `.bot DefectBot`/`.bot MirrorBot`, anything search-free — for all large `k`. No per-bot code-order
   computation is needed (contrast `describes_TFT`).
2. **A description ABOVE a threshold** (`DescribesAbove K`, `loebSound_pG_of_above`,
   `dimcid_vs_described_above`): PrudentBot's canonical description holds only for `KP ≤ k`
   (`Cells/PrudentMirror.lean` §2); the slack `S₀ = 7 + K` supplies the threshold inside `LoebSound`, as
   `loebSound_pPM` does. `Describes` is the case `K = 0`.
3. **The description instances**: `describes_botSV g a` (the bot-wrapped engine searcher `pBot (SV g a k)`,
   `PositiveCells` §5), `describes_dupocV` (the `TD` tower, `DupocV k`), `describes_botDupoc` (the `TBD`
   tower, `pBot (DupocV k)`, `JustSlot` §3), `describes_just7` (the budget-slot `Just7 k`, `TJ`),
   `describesAbove_prudent` (`TP`, `KP`).
4. **The seven cells** (engine value → `S'` value):
   * `loeb_DIMCID_vs_DBot`: `(C, C)` → **`(D, C)`** — DIMCID defects; DBot cooperates with anyone who
     defects against `.bot DefectBot`, and DIMCID does.
   * `loeb_DIMCID_vs_EBot`: `(C, C)` → **`(D, D)`** — DIMCID defects against all three of EBot's frozen
     probes, so EBot's ladder ends in D (`ebot_D_of_probes_D`).
   * `loeb_DIMCID_vs_OBot`: `(C, D)` → **`(D, D)`** — DIMCID's side flips; OBot sees a defection against
     `.bot CooperateBot` and defects.
   * `loeb_DIMCID_vs_DupocBot`: `(C, D)` at EVERY `k` in the engine (`outcome_DIMCID_vs_DupocBot`, a
     universal theorem) → **`(D, D)`** for all large `k` in `S'`: DIMCID defects against the described
     engine searcher; Dupoc's guard "DIMCID cooperates with me" is then FALSE, so by soundness it is never
     found and Dupoc defects. THE CONTRADICTION IS EXPLICIT: the engine proves `(C, D)` at every budget,
     `S'` proves `(D, D)` for all large budgets — the two proof systems disagree on this cell.
   * `loeb_DIMCID_vs_JustBot`: `(C, D)` → **`(D, D)`** — on the budget-slot `Just7 k` (the same play as the
     engine's `JustBot k` in every frame, `evalGraph_Just7_iff`; `Describes` cannot be built for the engine
     code `pcode (JustBot k)`, `ROUTE_B_SCOPE.md` §7: its stored template carries `k`); Just's guard "DIMCID
     cooperates with `.bot (Dupoc k)`" is FALSE (DIMCID defects against the described `pBot (DupocV k)`),
     never found, so Just defects (`just7_else_V` + `evalGraph_of_guard`). Just's half is ALSO stated on the
     engine's own code (`just_engine_vs_DIMCID_defects`, via `.bot (DupocBot k) = pBot (SV gDu 0 k)`).
   * `loeb_DIMCID_vs_PrudentBot`: `(C, D)` → **`(D, D)`** — DIMCID defects against the described Prudent
     (above `KP`); Prudent's outer guard "DIMCID cooperates with me" is FALSE, so Prudent defects.
   * `loeb_CIMCIC_vs_DIMCID`: `(D, C)` → **`(D, D)`** — DIMCID's side flips; CIMCIC's guard "I cooperate ⇒
     DIMCID cooperates with me" is then SELF-REFUTING (`cimcic_selfref_not_found`), so CIMCIC defects.
5. **The row** (`dimcid_flips_census`, `dimcid_vs_closed`): in `S'`, DIMCID's row is D against every
   described opponent — every closed code, every engine searcher through its `SV`/`TBS` tower, the
   budget-slot searchers, Prudent above `KP` — and the engine's seven cooperative DIMCID cells
   (DBot, EBot, OBot, DupocBot, JustBot, PrudentBot, and CIMCIC's cell against it) are census artifacts,
   exactly as the six unreadability flips of `FlipCells` were. With `loeb_DIMCID_vs_CooperateBot`,
   `_TitForTatBot`, `_CupodTrollBot` and `loeb_GuardianBot_vs_DIMCID`, DIMCID cooperates NOWHERE in `S'`.

Conventions: every threshold EXISTENTIAL; `simp` never sees a closed quote; `omega` is never asked about
`V`; `≤` at ℕ bridged by `le_def`; `V` pinned in every statement.
-/

set_option linter.constructorNameAsVariable false

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open LAct
open PD.Bots

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ### 1. Every closed code is described -/

section closed

/-- `swapcode` is absolute (it is `relabel 1 0`, a Σ₁-definable function: `cast_relabel`). -/
lemma cast_swapcode (x : ℕ) : ((swapcode x : ℕ) : V) = swapcode (x : V) := by
  have := cast_relabel (V := V) 1 0 x
  rwa [Nat.cast_one, Nat.cast_zero] at this

/-- `dnum` is absolute (a Σ₁-definable function). -/
lemma cast_dnum (x : ℕ) : ((dnum x : ℕ) : V) = dnum (x : V) := by
  have := DefinedFunction.shigmaOne_absolute_func V (dnum.defined (V := ℕ)) (dnum.defined (V := V)) ![x]
  simpa [Function.comp_def] using this

lemma lMap_swap_dnumT' (P : ℕ) : Semiterm.lMap swap (dnumT P) = dnumT P := term_lMap_swap_emb _

/-- The code of the closed structural term of the canonical code of `P`, in every model. -/
theorem quote_emb_dnumT (P : ℕ) :
    (⌜(Rew.emb (dnumT P) : SyntacticSemiterm LAct 0)⌝ : V) = progT (dnum (P : V)) := by
  unfold dnumT
  rw [term_emb_lMap_emb, quote_term_lMap_emb, ← Semiterm.empty_quote_def, quote_progTT, cast_dnum]

/-- The generic closed triple denotes `P` itself (`relabel_val_desc_V`). -/
lemma descVal_closed (P : ℕ) (k : V) : descVal (cl (dnumT P)) (dUT P) (dWT P) k = (P : V) := by
  rw [descVal_def, val_cl_V, val_dnumT_V, relabel_val_desc_V]

/-- The transposed generic triple denotes the transposed program. -/
lemma descVal_closed_T (P : ℕ) (k : V) :
    descVal (Semiterm.lMap swap (cl (dnumT P))) (Semiterm.lMap swap (dUT P)) (Semiterm.lMap swap (dWT P)) k =
      swapcode (P : V) := by
  rw [descVal_def, lMap_swap_cl, lMap_swap_dnumT', val_cl_V, val_dnumT_V]
  unfold dUT dWT
  rcases lt_trichotomy P (swapcode P) with h | h | h
  · rw [if_pos h, if_pos h, lMap_swap_cterm_C, lMap_swap_cterm_D, val_cterm_D_V, val_cterm_C_V, dnum_of_lt h]
  · have hs : swapcode P = P := h.symm
    rw [hs, if_neg (_root_.lt_irrefl _), if_neg (_root_.lt_irrefl _), if_neg (_root_.lt_irrefl _),
      if_neg (_root_.lt_irrefl _), lMap_swap_numT, lMap_swap_numT, val_numT_V, val_numT_V, Nat.cast_zero,
      Nat.cast_one, dnum_of_eq h, relabel_zero_one, ← cast_swapcode, hs]
  · rw [if_neg (lt_asymm h), if_pos h, if_neg (lt_asymm h), if_pos h, lMap_swap_cterm_D, lMap_swap_cterm_C,
      val_cterm_C_V, val_cterm_D_V, dnum_of_gt h, relabel_zero_one, cast_swapcode]

/-- **Every closed code is described in every model**: the generic triple `(cl (dnumT P), dUT P, dWT P)`. -/
theorem describes_closed (P : ℕ) : Describes (cl (dnumT P)) (dUT P) (dWT P) where
  hX := by
    intro V _ _ k
    rw [descVal_closed, quote_emb_cl_V, termSubst_closed _ (semiterm_quote_emb₀ _), quote_emb_dnumT]
  hU := by
    intro V _ _ k
    rw [descVal_closed]
    unfold dUT dU
    rcases lt_trichotomy P (swapcode P) with h | h | h
    · have h' : (P : V) < swapcode (P : V) := by rw [← cast_swapcode]; exact Nat.cast_lt.mpr h
      rw [if_pos h, if_pos h', quote_cterm_C]
    · have hs : swapcode P = P := h.symm
      have hs' : swapcode (P : V) = (P : V) := by rw [← cast_swapcode, hs]
      rw [hs, hs', if_neg (_root_.lt_irrefl _), if_neg (_root_.lt_irrefl _), if_neg (_root_.lt_irrefl _),
        if_neg (_root_.lt_irrefl _), quote_numT, Nat.cast_zero]
    · have h' : swapcode (P : V) < (P : V) := by rw [← cast_swapcode]; exact Nat.cast_lt.mpr h
      rw [if_neg (lt_asymm h), if_pos h, if_neg (lt_asymm h'), if_pos h', quote_cterm_D]
  hW := by
    intro V _ _ k
    rw [descVal_closed]
    unfold dWT dW
    rcases lt_trichotomy P (swapcode P) with h | h | h
    · have h' : (P : V) < swapcode (P : V) := by rw [← cast_swapcode]; exact Nat.cast_lt.mpr h
      rw [if_pos h, if_pos h', quote_cterm_D]
    · have hs : swapcode P = P := h.symm
      have hs' : swapcode (P : V) = (P : V) := by rw [← cast_swapcode, hs]
      rw [hs, hs', if_neg (_root_.lt_irrefl _), if_neg (_root_.lt_irrefl _), if_neg (_root_.lt_irrefl _),
        if_neg (_root_.lt_irrefl _), quote_numT, Nat.cast_one]
    · have h' : swapcode (P : V) < (P : V) := by rw [← cast_swapcode]; exact Nat.cast_lt.mpr h
      rw [if_neg (lt_asymm h), if_pos h, if_neg (lt_asymm h'), if_pos h', quote_cterm_C]
  hT := by intro V _ _ k; rw [descVal_closed_T, descVal_closed]

/-- **DIMCID defects against EVERY closed code and FINDS its guard, for all large `k`** — the row theorem
for the closed opponents (every search-free bot, every frozen `.bot` probe). -/
theorem dimcid_vs_closed (P : ℕ) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 2 (pcode (DIMCID k)) P (pcode (DIMCID k)) 1 ∧
      LenProvableV TAct k (guardCode (tcode phiD) (pcode (DIMCID k)) P) := by
  obtain ⟨k₀, h⟩ := dimcid_vs_described (describes_closed P)
  refine ⟨k₀, fun k hk ↦ ?_⟩
  have := h k hk
  rwa [descVal_closed, natCast_nat, ← pcode_DIMCID] at this

end closed

/-! ### 2. A description above a threshold -/

section above

/-- **A triple describes its value in every model ABOVE a standard threshold `K`** (`Describes` with the
hypothesis `K ≤ k` on every field): PrudentBot's canonical description (`Cells/PrudentMirror.lean` §2,
`KP ≤ k`). -/
structure DescribesAbove (K : ℕ) (X : Semiterm LAct Empty 1) (U W : ClosedSemiterm LAct 0) : Prop where
  hX : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (k : V), (K : V) ≤ k →
    termSubst LAct (bnum k ∷ (0 : V)) (⌜(Rew.emb X : SyntacticSemiterm LAct 1)⌝ : V) =
      progT (dnum (descVal X U W k))
  hU : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (k : V), (K : V) ≤ k → (⌜U⌝ : V) = dU (descVal X U W k)
  hW : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (k : V), (K : V) ≤ k → (⌜W⌝ : V) = dW (descVal X U W k)
  hT : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (k : V), (K : V) ≤ k →
    descVal (Semiterm.lMap swap X) (Semiterm.lMap swap U) (Semiterm.lMap swap W) k = swapcode (descVal X U W k)

/-- A description everywhere is a description above `0`. -/
theorem Describes.above {X : Semiterm LAct Empty 1} {U W : ClosedSemiterm LAct 0} (h : Describes X U W) :
    DescribesAbove 0 X U W where
  hX := fun V _ _ k _ ↦ h.hX V k
  hU := fun V _ _ k _ ↦ h.hU V k
  hW := fun V _ _ k _ ↦ h.hW V k
  hT := fun V _ _ k _ ↦ h.hT V k

/-- **DIMCID's Löb premise against an opponent described above `K`, slack `(7 + K, 8)`**
(`loebSound_pG_of`, with the threshold supplied by the slack as in `loebSound_pPM`). -/
theorem loebSound_pG_of_above {K : ℕ} {X : Semiterm LAct Empty 1} {U W : ClosedSemiterm LAct 0}
    (h : DescribesAbove K X U W) : LoebSound (pG X U W) (7 + K) 8 := by
  intro V _ _ k a ha hp
  have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
  have hk : (K : V) ≤ k :=
    le_trans (Nat.cast_le.mpr (Nat.le_add_left K 7)) (le_trans le_add_self (le_trans le_self_add ha))
  have h7 : ((7 : ℕ) : V) ≤ ((7 + K : ℕ) : V) := Nat.cast_le.mpr (Nat.le_add_right 7 K)
  have hb : a + ((7 : ℕ) : V) + ((8 : ℕ) : V) * formulaLen LAct (instB (⌜pG X U W⌝ : V) k) ≤
      a + ((7 + K : ℕ) : V) + ((8 : ℕ) : V) * formulaLen LAct (instB (⌜pG X U W⌝ : V) k) :=
    _root_.add_le_add_left (_root_.add_le_add_right h7 a) _
  have ha' : a + 8 * (formulaLen LAct (instB (⌜qDG X U W⌝ : V) k) +
      formulaLen LAct (instB (⌜qTG (Semiterm.lMap swap X) (Semiterm.lMap swap U) (Semiterm.lMap swap W)⌝ : V) k))
      + 7 ≤ k :=
    le_trans (pConj_slack_le a _ _ _ (formulaLen_instB_pG X U W k)) (le_trans hb ha)
  obtain ⟨h1, h2⟩ := pG_both_V k X U W (h.hX V k hk) (h.hU V k hk) (h.hW V k hk) a ha' hp
  have hA : ¬ ∃ n, EvalGraph n (DimcidV k) (descVal X U W k) (DimcidV k) 0 := by
    rintro ⟨n, hn⟩
    exact _root_.zero_ne_one (EvalGraph.unique_V' n 2 _ _ _ _ _ hn h1)
  have hB : ¬ ∃ n, EvalGraph n (DimcidTV k) (swapcode (descVal X U W k)) (DimcidTV k) 1 := by
    rintro ⟨n, hn⟩
    exact _root_.one_ne_zero (EvalGraph.unique_V' n 2 _ _ _ _ _ hn h2)
  exact ⟨(eval_pG_iff_stdActS k X U W rfl (h.hT V k hk)).mpr ⟨fun h ↦ absurd h hA, fun h ↦ absurd h hB⟩,
    (eval_pG_iff_swap k X U W rfl (h.hT V k hk)).mpr ⟨fun h ↦ absurd h hA, fun h ↦ absurd h hB⟩⟩

/-- **DIMCID defects against every opponent described above `K`, and FINDS its guard, for all large `k`**
(`dimcid_vs_described` above a threshold; the threshold `k₀ + K` keeps `K ≤ k`). -/
theorem dimcid_vs_described_above {K : ℕ} {X : Semiterm LAct Empty 1} {U W : ClosedSemiterm LAct 0}
    (h : DescribesAbove K X U W) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 2 (Dimcid k) (descVal X U W k) (Dimcid k) 1 ∧
      LenProvableV TAct k (guardCode (⌜tmplD⌝ : ℕ) (Dimcid k) (descVal X U W k)) := by
  obtain ⟨k₀, hf⟩ := family_found (pG X U W) boundedInnerNec_sixteen (loebSound_pG_of_above h)
  refine ⟨k₀ + K, fun k hk ↦ ?_⟩
  obtain ⟨a, ha, hpc⟩ := hf k (by omega)
  have hX := h.hX ℕ k (by rw [natCast_nat]; exact le_def.mpr (Nat.eq_or_lt_of_le (by omega)))
  have hU := h.hU ℕ k (by rw [natCast_nat]; exact le_def.mpr (Nat.eq_or_lt_of_le (by omega)))
  have hW := h.hW ℕ k (by rw [natCast_nat]; exact le_def.mpr (Nat.eq_or_lt_of_le (by omega)))
  have ha' := le_def.mpr (pConj_slack_nat a _ _ _ k (formulaLen_instB_pG (V := ℕ) X U W k) (by omega))
  exact ⟨(pG_both_V (V := ℕ) k X U W hX hU hW a ha' hpc).1, (pG_guards_V (V := ℕ) k X U W hX hU hW a ha' hpc).1⟩

end above

/-! ### 3. The description instances: bot-wrapped engine searchers, the Dupoc towers, `Just7`, Prudent -/

section instances

/-! #### The bot-wrapped engine searcher `pBot (SV g a k)` (`.bot (DupocBot k)`, Just's frozen snapshot) -/

lemma descVal_botSV (g : Semisentence LAct 6) (a : ℕ) (ha : a = 0 ∨ a = 1) (k : V) :
    descVal (TBS g a) (uS g a) (wS g a) k = pBot (SV g a k) := hme_botSV g a ha k

lemma descVal_botSV_T (g : Semisentence LAct 6) (a : ℕ) (ha : a = 0 ∨ a = 1) (k : V) :
    descVal (Semiterm.lMap swap (TBS g a)) (Semiterm.lMap swap (uS g a)) (Semiterm.lMap swap (wS g a)) k =
      pBot (SV (Semiformula.lMap swap g) (1 - a) k) := hme_botSVT g a ha k

/-- **The bot tower of an engine searcher describes `pBot (SV g a k)` in every model** (`PositiveCells` §5). -/
theorem describes_botSV (g : Semisentence LAct 6) (a : ℕ) (ha : a = 0 ∨ a = 1) :
    Describes (TBS g a) (uS g a) (wS g a) where
  hX := by intro V _ _ k; rw [descVal_botSV g a ha]; exact termSubst_TBS g a ha k
  hU := by intro V _ _ k; rw [descVal_botSV g a ha]; exact hU_botSV g a ha k
  hW := by intro V _ _ k; rw [descVal_botSV g a ha]; exact hW_botSV g a ha k
  hT := by intro V _ _ k; rw [descVal_botSV_T g a ha, descVal_botSV g a ha, swapcode_pBot, swapcode_SV g a ha]

/-! #### The hand-written Dupoc `DupocV k` (the `TD` tower) and its bot-wrapping (the `TBD` tower) -/

lemma descVal_dupocV (k : V) : descVal TD uD wD k = DupocV k := by
  rw [descVal_def, val_TD_V, relabel_val_uD_wD_V]

lemma descVal_dupocV_T (k : V) :
    descVal (Semiterm.lMap swap TD) (Semiterm.lMap swap uD) (Semiterm.lMap swap wD) k = CupodV k := by
  rw [descVal_def, lMap_swap_TD, val_TD_V]
  have h := relabel_val_uC_wC_V (V := V) k
  unfold uC wC at h
  exact h

/-- **The `TD` tower describes `DupocV k` in every model.** -/
theorem describes_dupocV : Describes TD uD wD where
  hX := by intro V _ _ k; rw [descVal_dupocV]; exact hX_dupoc k
  hU := by intro V _ _ k; rw [descVal_dupocV]; exact hU_dupoc k
  hW := by intro V _ _ k; rw [descVal_dupocV]; exact hW_dupoc k
  hT := by intro V _ _ k; rw [descVal_dupocV_T, descVal_dupocV, swapcode_DupocV]

lemma descVal_botDupoc (k : V) : descVal TBD uD wD k = pBot (DupocV k) := hme_bot k

lemma descVal_botDupoc_T (k : V) :
    descVal (Semiterm.lMap swap TBD) (Semiterm.lMap swap uD) (Semiterm.lMap swap wD) k = pBot (CupodV k) :=
  hme'_bot k

/-- **The `TBD` tower describes `pBot (DupocV k)` in every model** (`JustSlot` §3). -/
theorem describes_botDupoc : Describes TBD uD wD where
  hX := by intro V _ _ k; rw [descVal_botDupoc]; exact hX_bot k
  hU := by intro V _ _ k; rw [descVal_botDupoc]; exact hU_bot k
  hW := by intro V _ _ k; rw [descVal_botDupoc]; exact hW_bot k
  hT := by intro V _ _ k; rw [descVal_botDupoc_T, descVal_botDupoc, swapcode_pBot_DupocV]

/-! #### The budget-slot `Just7 k` -/

lemma descVal_just7 (k : V) : descVal TJ uJ wJ k = JustV7 k := hopp_just7 k

lemma descVal_just7_T (k : V) :
    descVal (Semiterm.lMap swap TJ) (Semiterm.lMap swap uJ) (Semiterm.lMap swap wJ) k = JustTV7 k :=
  hopp'_just7 k

/-- **The canonical triple of the budget-slot Just describes it in every model** (`JustSlot` §3). -/
theorem describes_just7 : Describes TJ uJ wJ where
  hX := by intro V _ _ k; rw [descVal_just7]; exact hX_just7 k
  hU := by intro V _ _ k; rw [descVal_just7]; exact hU_just7 k
  hW := by intro V _ _ k; rw [descVal_just7]; exact hW_just7 k
  hT := by intro V _ _ k; rw [descVal_just7_T, descVal_just7, swapcode_JustV7]

/-! #### PrudentBot, above `KP` -/

lemma descVal_prudent {k : V} (hk : (KP : V) ≤ k) : descVal TP uP wP k = PrudentV k := by
  rw [descVal_def, val_TP_V hk, relabel_val_uP_wP_V hk]

lemma descVal_prudent_T {k : V} (hk : (KP : V) ≤ k) :
    descVal (Semiterm.lMap swap TP) (Semiterm.lMap swap uP) (Semiterm.lMap swap wP) k = PrudentTV k := by
  rw [descVal_def, lMap_swap_TP, val_TP_V hk]
  have h := relabel_val_uPT_wPT_V (V := V) hk
  unfold uPT wPT at h
  exact h

/-- **Prudent's canonical triple describes `PrudentV k` in every model above `KP`** (`PrudentMirror` §2/§4). -/
theorem describesAbove_prudent : DescribesAbove KP TP uP wP where
  hX := by intro V _ _ k hk; rw [descVal_prudent hk]; exact hX_prudent hk
  hU := by intro V _ _ k hk; rw [descVal_prudent hk]; exact hU_prudent hk
  hW := by intro V _ _ k hk; rw [descVal_prudent hk]; exact hW_prudent hk
  hT := by intro V _ _ k hk; rw [descVal_prudent_T hk, descVal_prudent hk, swapcode_PrudentV]

end instances

/-! ### 4. DIMCID's defections, one per opponent -/

section defections

/-- **DIMCID defects against `.bot DefectBot` for all large `k`** (the closed code `pBot (pConst 1)`). -/
theorem dimcid_vs_botDB_defects :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 2 (pcode (DIMCID k)) (pBot (pConst 1)) (pcode (DIMCID k)) 1 ∧
      LenProvableV TAct k (guardCode (tcode phiD) (pcode (DIMCID k)) (pBot (pConst 1))) :=
  dimcid_vs_closed _

/-- **DIMCID defects against `.bot MirrorBot` for all large `k`** (EBot's third probe). -/
theorem dimcid_vs_botMirror_defects :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 2 (pcode (DIMCID k)) (pBot Mirror) (pcode (DIMCID k)) 1 ∧
      LenProvableV TAct k (guardCode (tcode phiD) (pcode (DIMCID k)) (pBot Mirror)) :=
  dimcid_vs_closed _

/-- **DIMCID defects against DBot and FINDS its guard, for all large `k`.** -/
theorem dimcid_vs_DBot_defects :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 2 (pcode (DIMCID k)) (pcode DBot) (pcode (DIMCID k)) 1 ∧
      LenProvableV TAct k (guardCode (tcode phiD) (pcode (DIMCID k)) (pcode DBot)) :=
  dimcid_vs_closed _

/-- **DIMCID defects against EBot and FINDS its guard, for all large `k`.** -/
theorem dimcid_vs_EBot_defects :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 2 (pcode (DIMCID k)) (pcode EBot) (pcode (DIMCID k)) 1 ∧
      LenProvableV TAct k (guardCode (tcode phiD) (pcode (DIMCID k)) (pcode EBot)) :=
  dimcid_vs_closed _

/-- **DIMCID defects against OBot and FINDS its guard, for all large `k`.** -/
theorem dimcid_vs_OBot_defects :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 2 (pcode (DIMCID k)) (pcode OBot) (pcode (DIMCID k)) 1 ∧
      LenProvableV TAct k (guardCode (tcode phiD) (pcode (DIMCID k)) (pcode OBot)) :=
  dimcid_vs_closed _

/-- **DIMCID defects against the engine's `DupocBot k` and FINDS its guard, for all large `k`** (the
`SV`-described engine searcher, `pcode_DupocBot_SV`). -/
theorem dimcid_vs_DupocBot_defects :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 2 (pcode (DIMCID k)) (pcode (DupocBot k)) (pcode (DIMCID k)) 1 ∧
      LenProvableV TAct k (guardCode (tcode phiD) (pcode (DIMCID k)) (pcode (DupocBot k))) := by
  obtain ⟨k₀, h⟩ := dimcid_vs_described (describes_SV gDu 0 (Or.inl rfl))
  refine ⟨k₀, fun k hk ↦ ?_⟩
  have := h k hk
  rwa [descVal_SV gDu 0 (Or.inl rfl), ← pcode_DupocBot_SV, ← pcode_DIMCID] at this

/-- **DIMCID defects against the hand-written `DupocV k` too** (the `TD` tower). -/
theorem dimcid_vs_dupocV_defects :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 2 (pcode (DIMCID k)) (Dupoc k) (pcode (DIMCID k)) 1 ∧
      LenProvableV TAct k (guardCode (tcode phiD) (pcode (DIMCID k)) (Dupoc k)) := by
  obtain ⟨k₀, h⟩ := dimcid_vs_described describes_dupocV
  refine ⟨k₀, fun k hk ↦ ?_⟩
  have := h k hk
  rwa [descVal_dupocV, DupocV_nat, ← pcode_DIMCID] at this

/-- **DIMCID defects against the frozen snapshot `.bot (DupocBot k)` and FINDS its guard, for all large
`k`** — the engine code `pBot (SV gDu 0 k)`, Just's probe. -/
theorem dimcid_vs_botDupocBot_defects :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 2 (pcode (DIMCID k)) (pBot (pcode (DupocBot k))) (pcode (DIMCID k)) 1 ∧
      LenProvableV TAct k (guardCode (tcode phiD) (pcode (DIMCID k)) (pBot (pcode (DupocBot k)))) := by
  obtain ⟨k₀, h⟩ := dimcid_vs_described (describes_botSV gDu 0 (Or.inl rfl))
  refine ⟨k₀, fun k hk ↦ ?_⟩
  have := h k hk
  rwa [descVal_botSV gDu 0 (Or.inl rfl), ← pcode_DupocBot_SV, ← pcode_DIMCID] at this

/-- **DIMCID defects against the hand-written snapshot `pBot (DupocV k)`** (the `TBD` tower, Just7's probe). -/
theorem dimcid_vs_botDupocV_defects :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 2 (pcode (DIMCID k)) (pBot (Dupoc k)) (pcode (DIMCID k)) 1 ∧
      LenProvableV TAct k (guardCode (tcode phiD) (pcode (DIMCID k)) (pBot (Dupoc k))) := by
  obtain ⟨k₀, h⟩ := dimcid_vs_described describes_botDupoc
  refine ⟨k₀, fun k hk ↦ ?_⟩
  have := h k hk
  rwa [descVal_botDupoc, DupocV_nat, ← pcode_DIMCID] at this

/-- **DIMCID defects against `Just7 k` and FINDS its guard, for all large `k`.** -/
theorem dimcid_vs_just7_defects :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 2 (pcode (DIMCID k)) (Just7 k) (pcode (DIMCID k)) 1 ∧
      LenProvableV TAct k (guardCode (tcode phiD) (pcode (DIMCID k)) (Just7 k)) := by
  obtain ⟨k₀, h⟩ := dimcid_vs_described describes_just7
  refine ⟨k₀, fun k hk ↦ ?_⟩
  have := h k hk
  rwa [descVal_just7, JustV7_nat, ← pcode_DIMCID] at this

/-- **DIMCID defects against the engine's `PrudentBot k` and FINDS its guard, for all large `k`** (the
description above `KP`; `pcode_PrudentBot`). -/
theorem dimcid_vs_PrudentBot_defects :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 2 (pcode (DIMCID k)) (pcode (PrudentBot k)) (pcode (DIMCID k)) 1 ∧
      LenProvableV TAct k (guardCode (tcode phiD) (pcode (DIMCID k)) (pcode (PrudentBot k))) := by
  obtain ⟨k₀, h⟩ := dimcid_vs_described_above describesAbove_prudent
  refine ⟨k₀ + KP, fun k hk ↦ ?_⟩
  have := h k (by omega)
  rwa [descVal_prudent (k := k) (by rw [natCast_nat]; exact le_def.mpr (Nat.eq_or_lt_of_le (by omega))),
    PrudentV_nat, ← pcode_PrudentBot, ← pcode_DIMCID] at this

lemma pcode_CIMCIC_SV (k : ℕ) : pcode (CIMCIC k) = SV (V := ℕ) tmplC 0 k := by
  rw [pcode_CIMCIC', SV_nat]; rfl

/-- **DIMCID defects against the engine's `CIMCIC k` and FINDS its guard, for all large `k`** (the
`SV`-described engine searcher). -/
theorem dimcid_vs_CIMCIC_defects :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 2 (pcode (DIMCID k)) (pcode (CIMCIC k)) (pcode (DIMCID k)) 1 ∧
      LenProvableV TAct k (guardCode (tcode phiD) (pcode (DIMCID k)) (pcode (CIMCIC k))) := by
  obtain ⟨k₀, h⟩ := dimcid_vs_described (describes_SV tmplC 0 (Or.inl rfl))
  refine ⟨k₀, fun k hk ↦ ?_⟩
  have := h k hk
  rwa [descVal_SV tmplC 0 (Or.inl rfl), ← pcode_CIMCIC_SV, ← pcode_DIMCID] at this

end defections

/-! ### 5. The opponents' replies -/

section replies

/-- `EBot` defects against `x` when `x` defects against all three frozen probes `.bot DefectBot`,
`.bot CooperateBot`, `.bot MirrorBot` (the end of its ladder). -/
theorem ebot_D_of_probes_D {x n : ℕ} (h1 : EvalGraph n x (pBot (pConst 1)) x 1)
    (h2 : EvalGraph n x (pBot (pConst 0)) x 1) (h3 : EvalGraph n x (pBot Mirror) x 1) :
    EvalGraph (n + 1 + 1 + 1 + 1) (pcode EBot) x (pcode EBot) 1 := by
  simp only [EBot, CooperateBot, DefectBot, MirrorBot, pcode_ite, pcode_sim, pcode_opp, pcode_self, pcode_bot,
    pcode_const, actCode]
  rw [EvalGraph.ite_iff]
  refine ⟨1, ?_, Or.inr ⟨by decide, ?_⟩⟩
  · rw [EvalGraph.sim_iff, psubst_opp, psubst_bot]
    exact EvalGraph.mono_le (by omega) h1
  · rw [EvalGraph.ite_iff]
    refine ⟨1, ?_, Or.inr ⟨by decide, ?_⟩⟩
    · rw [EvalGraph.sim_iff, psubst_opp, psubst_bot]
      exact EvalGraph.mono_le (by omega) h2
    · rw [EvalGraph.ite_iff]
      refine ⟨1, ?_, Or.inr ⟨by decide, const_play _ _ _ _⟩⟩
      rw [EvalGraph.sim_iff, psubst_opp, psubst_bot]
      exact h3

/-- **The else branch of the budget-slot Just in any frame** (fuel 2): the guard "`opp` plays C against
`pBot (Dupoc k)`" not found ⇒ `D`. -/
theorem just7_else_V (k me opp : V) :
    ¬ LenProvableV TAct k (guardCode (⌜GtmplA 0⌝ : V) (pBot (DupocV k)) opp) →
      EvalGraph 2 me opp (JustV7 k) 1 := by
  intro h
  rw [show (2 : V) = 1 + 1 from one_add_one_eq_two.symm]
  show EvalGraph (1 + 1) me opp (pSearch k (⌜GtmplJ7⌝ : V) (pConst 0) (pConst 1)) 1
  rw [EvalGraph.search_iff, guardCodeB_GtmplJ7]
  right
  refine ⟨h, ?_⟩
  have e : EvalGraph (0 + 1) me opp (pConst 1) 1 := EvalGraph.const_iff.mpr rfl
  rwa [zero_add] at e

/-- **`Just7 k` defects against an opponent that defects against `pBot (Dupoc k)`** (soundness of a found
guard, `evalGraph_of_guard`, against the arithmetized sub-play). -/
theorem just7_D_of_probe (k : ℕ) {opp : ℕ} {N : ℕ} (h : EvalGraph N opp (pBot (Dupoc k)) opp 1) :
    EvalGraph 2 (Just7 k) opp (Just7 k) 1 := by
  refine just7_else_V (V := ℕ) k (Just7 k) opp fun hf ↦ ?_
  obtain ⟨n, hn⟩ := evalGraph_of_guard hf
  exact absurd (EvalGraph.unique' hn h) (by decide)

end replies

/-! ### 6. The seven cells -/

section cells

/-- **DIMCID × DBot is `(D, C)` in PA-`S'`**, for all large `k`, unconditional. The engine proves `(C, C)` by
a floor census (`llm_outcome_DIMCID_vs_DBot`, `no_provable_tailToS_floor`); in `S'` DIMCID's guard against
DBot is self-fulfilling and found, so DIMCID defects; DBot punishes only those who cooperate with
`.bot DefectBot`, and DIMCID defects against that probe too (`dimcid_vs_botDB_defects`), so DBot cooperates. -/
theorem loeb_DIMCID_vs_DBot :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 2 (pcode (DIMCID k)) (pcode DBot) (pcode (DIMCID k)) (actCode .D) ∧
      EvalGraph 4 (pcode DBot) (pcode (DIMCID k)) (pcode DBot) (actCode .C) := by
  obtain ⟨k₁, h₁⟩ := dimcid_vs_DBot_defects
  obtain ⟨k₂, h₂⟩ := dimcid_vs_botDB_defects
  exact ⟨k₁ + k₂, fun k hk ↦ ⟨(h₁ k (by omega)).1, dbot_C_of_probe_D (h₂ k (by omega)).1⟩⟩

/-- **The box form**: DIMCID FINDS its guard against DBot within its budget. -/
theorem dimcid_finds_guard_vs_DBot :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k → LenProvableV TAct k (guardCode (tcode phiD) (pcode (DIMCID k)) (pcode DBot)) := by
  obtain ⟨k₀, h⟩ := dimcid_vs_DBot_defects
  exact ⟨k₀, fun k hk ↦ (h k hk).2⟩

/-- **DIMCID × EBot is `(D, D)` in PA-`S'`**, for all large `k`, unconditional. The engine proves `(C, C)` by a
floor + unreadability census (`llm_outcome_DIMCID_vs_EBot`); in `S'` DIMCID defects against EBot and against
each of EBot's three frozen probes (`.bot DefectBot`, `.bot CooperateBot`, `.bot MirrorBot` — all closed
codes, `dimcid_vs_closed`), so EBot's ladder ends in D. -/
theorem loeb_DIMCID_vs_EBot :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 2 (pcode (DIMCID k)) (pcode EBot) (pcode (DIMCID k)) (actCode .D) ∧
      EvalGraph 6 (pcode EBot) (pcode (DIMCID k)) (pcode EBot) (actCode .D) := by
  obtain ⟨k₁, h₁⟩ := dimcid_vs_EBot_defects
  obtain ⟨k₂, h₂⟩ := dimcid_vs_botDB_defects
  obtain ⟨k₃, h₃⟩ := dimcid_vs_botCB_defects
  obtain ⟨k₄, h₄⟩ := dimcid_vs_botMirror_defects
  exact ⟨k₁ + k₂ + k₃ + k₄, fun k hk ↦ ⟨(h₁ k (by omega)).1,
    ebot_D_of_probes_D (h₂ k (by omega)).1 (h₃ k (by omega)).1 (h₄ k (by omega)).1⟩⟩

/-- **The box form**: DIMCID FINDS its guard against EBot within its budget. -/
theorem dimcid_finds_guard_vs_EBot :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k → LenProvableV TAct k (guardCode (tcode phiD) (pcode (DIMCID k)) (pcode EBot)) := by
  obtain ⟨k₀, h⟩ := dimcid_vs_EBot_defects
  exact ⟨k₀, fun k hk ↦ (h k hk).2⟩

/-- **DIMCID × OBot is `(D, D)` in PA-`S'`**, for all large `k`, unconditional. The engine proves `(C, D)` by a
probe-first floor + unreadability census (`llm_outcome_DIMCID_vs_OBot`); in `S'` DIMCID's side flips to D
(self-fulfilling guard), and OBot, seeing DIMCID defect against `.bot CooperateBot`, defects as before. -/
theorem loeb_DIMCID_vs_OBot :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 2 (pcode (DIMCID k)) (pcode OBot) (pcode (DIMCID k)) (actCode .D) ∧
      EvalGraph 4 (pcode OBot) (pcode (DIMCID k)) (pcode OBot) (actCode .D) := by
  obtain ⟨k₁, h₁⟩ := dimcid_vs_OBot_defects
  obtain ⟨k₂, h₂⟩ := dimcid_vs_botCB_defects
  exact ⟨k₁ + k₂, fun k hk ↦ ⟨(h₁ k (by omega)).1, obot_D_of_probe1_D (h₂ k (by omega)).1 (by decide)⟩⟩

/-- **The box form**: DIMCID FINDS its guard against OBot within its budget. -/
theorem dimcid_finds_guard_vs_OBot :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k → LenProvableV TAct k (guardCode (tcode phiD) (pcode (DIMCID k)) (pcode OBot)) := by
  obtain ⟨k₀, h⟩ := dimcid_vs_OBot_defects
  exact ⟨k₀, fun k hk ↦ (h k hk).2⟩

/-- **DIMCID × DupocBot is `(D, D)` in PA-`S'`**, for all large `k`, unconditional, on the engine's own codes.
**The engine proves `(C, D)` at EVERY `k`** (`outcome_DIMCID_vs_DupocBot`, a universal theorem, by the two
else-play floors `no_provable_DIMCID_C_tail`/`no_provable_DupocBot_D_tail`); **`S'` proves `(D, D)` for all
large `k`**: DIMCID's guard "I play C against Dupoc ⇒ Dupoc plays D against me" is self-fulfilling and
found, so DIMCID defects (`dimcid_vs_DupocBot_defects`); Dupoc's guard "DIMCID plays C against me" is then
FALSE in ℕ, so by soundness it is never found and Dupoc defects (`dupoc_D_of_probe`). The engine's floor on
DIMCID's else-play is what `S'` cannot see — under a real proof predicate the guard is not an else-play at
all, it is FOUND. -/
theorem loeb_DIMCID_vs_DupocBot :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 2 (pcode (DIMCID k)) (pcode (DupocBot k)) (pcode (DIMCID k)) (actCode .D) ∧
      EvalGraph 2 (pcode (DupocBot k)) (pcode (DIMCID k)) (pcode (DupocBot k)) (actCode .D) := by
  obtain ⟨k₀, h⟩ := dimcid_vs_DupocBot_defects
  exact ⟨k₀, fun k hk ↦ ⟨(h k hk).1, dupoc_D_of_probe k (proper_DIMCID k) (h k hk).1⟩⟩

/-- **The box form**: DIMCID FINDS its guard against `DupocBot k` within its budget. -/
theorem dimcid_finds_guard_vs_DupocBot :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      LenProvableV TAct k (guardCode (tcode phiD) (pcode (DIMCID k)) (pcode (DupocBot k))) := by
  obtain ⟨k₀, h⟩ := dimcid_vs_DupocBot_defects
  exact ⟨k₀, fun k hk ↦ (h k hk).2⟩

/-- **Dupoc's guard against DIMCID is never found** (the SND half of the Dupoc cell, on the engine's codes). -/
theorem dupoc_guard_vs_DIMCID_not_found :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      ¬ LenProvableV TAct k (guardCode (tcode phiDu) (pcode (DupocBot k)) (pcode (DIMCID k))) := by
  obtain ⟨k₀, h⟩ := dimcid_vs_DupocBot_defects
  exact ⟨k₀, fun k hk ↦ not_found_opp_self (proper_DupocBot k) (proper_DIMCID k) .C (b := .D) (by decide)
    (h k hk).1 k⟩

/-- **The engine's `JustBot k` defects against DIMCID for all large `k`** (Just's half on the engine's own
code: its guard "DIMCID plays C against `.bot (DupocBot k)`" is FALSE — DIMCID defects against the described
snapshot `pBot (SV gDu 0 k)` — so by soundness it is never found). -/
theorem just_engine_vs_DIMCID_defects :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 2 (pcode (JustBot k)) (pcode (DIMCID k)) (pcode (JustBot k)) (actCode .D) := by
  obtain ⟨k₀, h⟩ := dimcid_vs_botDupocBot_defects
  exact ⟨k₀, fun k hk ↦ just_D_of_probe k (proper_DIMCID k) (h k hk).1⟩

/-- **DIMCID × JustBot is `(D, D)` in PA-`S'`**, for all large `k`, unconditional, on the budget-slot `Just7 k`
(the same play as the engine's `JustBot k` in every frame, `evalGraph_Just7_iff`; a `Describes` instance for
the engine code `pcode (JustBot k)` cannot be built — its stored template carries `k`, `ROUTE_B_SCOPE.md` §7 —
so DIMCID's half is stated against `Just7 k`, and Just's half both on `Just7 k` and on the engine code,
`just_engine_vs_DIMCID_defects`). The engine proves `(C, D)` by a floor census (`llm_outcome_DIMCID_vs_JustBot`);
in `S'` DIMCID's guard against the described Just is self-fulfilling and found, so DIMCID defects; Just's guard
"DIMCID plays C against `pBot (Dupoc k)`" is FALSE (DIMCID defects against the described snapshot,
`dimcid_vs_botDupocV_defects`), never found by soundness, so Just defects. -/
theorem loeb_DIMCID_vs_JustBot :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 2 (pcode (DIMCID k)) (Just7 k) (pcode (DIMCID k)) (actCode .D) ∧
      EvalGraph 2 (Just7 k) (pcode (DIMCID k)) (Just7 k) (actCode .D) := by
  obtain ⟨k₁, h₁⟩ := dimcid_vs_just7_defects
  obtain ⟨k₂, h₂⟩ := dimcid_vs_botDupocV_defects
  exact ⟨k₁ + k₂, fun k hk ↦ ⟨(h₁ k (by omega)).1, just7_D_of_probe k (h₂ k (by omega)).1⟩⟩

/-- **The box form**: DIMCID FINDS its guard against `Just7 k` within its budget. -/
theorem dimcid_finds_guard_vs_just7 :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k → LenProvableV TAct k (guardCode (tcode phiD) (pcode (DIMCID k)) (Just7 k)) := by
  obtain ⟨k₀, h⟩ := dimcid_vs_just7_defects
  exact ⟨k₀, fun k hk ↦ (h k hk).2⟩

/-- **DIMCID × PrudentBot is `(D, D)` in PA-`S'`**, for all large `k`, unconditional, on the engine's own codes.
The engine proves `(C, D)` by a floor census (`llm_outcome_DIMCID_vs_PrudentBot`); in `S'` DIMCID's guard
against the described Prudent (above `KP`) is self-fulfilling and found, so DIMCID defects; Prudent's outer
guard "DIMCID plays C against me" is then FALSE, never found by soundness, so Prudent defects
(`prudent_D_of_probe`). -/
theorem loeb_DIMCID_vs_PrudentBot :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 2 (pcode (DIMCID k)) (pcode (PrudentBot k)) (pcode (DIMCID k)) (actCode .D) ∧
      EvalGraph 2 (pcode (PrudentBot k)) (pcode (DIMCID k)) (pcode (PrudentBot k)) (actCode .D) := by
  obtain ⟨k₀, h⟩ := dimcid_vs_PrudentBot_defects
  exact ⟨k₀, fun k hk ↦ ⟨(h k hk).1, prudent_D_of_probe k (proper_DIMCID k) (h k hk).1⟩⟩

/-- **The box form**: DIMCID FINDS its guard against `PrudentBot k` within its budget. -/
theorem dimcid_finds_guard_vs_PrudentBot :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      LenProvableV TAct k (guardCode (tcode phiD) (pcode (DIMCID k)) (pcode (PrudentBot k))) := by
  obtain ⟨k₀, h⟩ := dimcid_vs_PrudentBot_defects
  exact ⟨k₀, fun k hk ↦ (h k hk).2⟩

/-- **CIMCIC × DIMCID is `(D, D)` in PA-`S'`**, for all large `k`, unconditional, on the engine's own codes.
The engine proves `(D, C)` by a floor census on both guards (`llm_outcome_CIMCIC_vs_DIMCID`); in `S'`
DIMCID's guard against the described CIMCIC is self-fulfilling and found, so DIMCID defects; CIMCIC's guard
"I play C against DIMCID ⇒ DIMCID plays C against me" is then SELF-REFUTING (finding it would make CIMCIC
cooperate, whence by soundness DIMCID would cooperate — against the fact; `cimcic_selfref_not_found`), so
CIMCIC defects. -/
theorem loeb_CIMCIC_vs_DIMCID :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 2 (pcode (CIMCIC k)) (pcode (DIMCID k)) (pcode (CIMCIC k)) (actCode .D) ∧
      EvalGraph 2 (pcode (DIMCID k)) (pcode (CIMCIC k)) (pcode (DIMCID k)) (actCode .D) := by
  obtain ⟨k₀, h⟩ := dimcid_vs_CIMCIC_defects
  refine ⟨k₀, fun k hk ↦ ⟨?_, (h k hk).1⟩⟩
  have hn := cimcic_selfref_not_found k (proper_DIMCID k) (h k hk).1
  rw [pcode_CIMCIC'] at hn ⊢
  exact search_else phiC hn (const_play _ _ _ _)

/-- **The box form**: DIMCID FINDS its guard against `CIMCIC k` within its budget. -/
theorem dimcid_finds_guard_vs_CIMCIC :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      LenProvableV TAct k (guardCode (tcode phiD) (pcode (DIMCID k)) (pcode (CIMCIC k))) := by
  obtain ⟨k₀, h⟩ := dimcid_vs_CIMCIC_defects
  exact ⟨k₀, fun k hk ↦ (h k hk).2⟩

/-- **CIMCIC's guard against DIMCID is never found** (the self-refutation, for all large `k`). -/
theorem cimcic_guard_vs_DIMCID_not_found :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      ¬ LenProvableV TAct k (guardCode (tcode phiC) (pcode (CIMCIC k)) (pcode (DIMCID k))) := by
  obtain ⟨k₀, h⟩ := dimcid_vs_CIMCIC_defects
  exact ⟨k₀, fun k hk ↦ cimcic_selfref_not_found k (proper_DIMCID k) (h k hk).1⟩

end cells

/-! ### 7. The row -/

section row

/-- **DIMCID's row in PA-`S'`: the seven cooperative engine cells, all flipped, at ONE threshold.** In `S'`
DIMCID's row is D against every described opponent (`dimcid_vs_described`, `dimcid_vs_closed`,
`dimcid_vs_described_above`); the engine's seven cooperative DIMCID cells — DBot `(C, C)`, EBot `(C, C)`,
OBot `(C, D)`, DupocBot `(C, D)` at every `k`, JustBot `(C, D)`, PrudentBot `(C, D)`, and CIMCIC × DIMCID
`(D, C)` — are census artifacts: each was closed by a floor or unreadability census that cannot read DIMCID's
own guard. -/
theorem dimcid_flips_census :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      (EvalGraph 2 (pcode (DIMCID k)) (pcode DBot) (pcode (DIMCID k)) (actCode .D) ∧
        EvalGraph 4 (pcode DBot) (pcode (DIMCID k)) (pcode DBot) (actCode .C)) ∧
      (EvalGraph 2 (pcode (DIMCID k)) (pcode EBot) (pcode (DIMCID k)) (actCode .D) ∧
        EvalGraph 6 (pcode EBot) (pcode (DIMCID k)) (pcode EBot) (actCode .D)) ∧
      (EvalGraph 2 (pcode (DIMCID k)) (pcode OBot) (pcode (DIMCID k)) (actCode .D) ∧
        EvalGraph 4 (pcode OBot) (pcode (DIMCID k)) (pcode OBot) (actCode .D)) ∧
      (EvalGraph 2 (pcode (DIMCID k)) (pcode (DupocBot k)) (pcode (DIMCID k)) (actCode .D) ∧
        EvalGraph 2 (pcode (DupocBot k)) (pcode (DIMCID k)) (pcode (DupocBot k)) (actCode .D)) ∧
      (EvalGraph 2 (pcode (DIMCID k)) (Just7 k) (pcode (DIMCID k)) (actCode .D) ∧
        EvalGraph 2 (Just7 k) (pcode (DIMCID k)) (Just7 k) (actCode .D) ∧
        EvalGraph 2 (pcode (JustBot k)) (pcode (DIMCID k)) (pcode (JustBot k)) (actCode .D)) ∧
      (EvalGraph 2 (pcode (DIMCID k)) (pcode (PrudentBot k)) (pcode (DIMCID k)) (actCode .D) ∧
        EvalGraph 2 (pcode (PrudentBot k)) (pcode (DIMCID k)) (pcode (PrudentBot k)) (actCode .D)) ∧
      (EvalGraph 2 (pcode (CIMCIC k)) (pcode (DIMCID k)) (pcode (CIMCIC k)) (actCode .D) ∧
        EvalGraph 2 (pcode (DIMCID k)) (pcode (CIMCIC k)) (pcode (DIMCID k)) (actCode .D)) := by
  obtain ⟨k₁, h₁⟩ := loeb_DIMCID_vs_DBot
  obtain ⟨k₂, h₂⟩ := loeb_DIMCID_vs_EBot
  obtain ⟨k₃, h₃⟩ := loeb_DIMCID_vs_OBot
  obtain ⟨k₄, h₄⟩ := loeb_DIMCID_vs_DupocBot
  obtain ⟨k₅, h₅⟩ := loeb_DIMCID_vs_JustBot
  obtain ⟨k₅', h₅'⟩ := just_engine_vs_DIMCID_defects
  obtain ⟨k₆, h₆⟩ := loeb_DIMCID_vs_PrudentBot
  obtain ⟨k₇, h₇⟩ := loeb_CIMCIC_vs_DIMCID
  refine ⟨k₁ + k₂ + k₃ + k₄ + k₅ + k₅' + k₆ + k₇, fun k hk ↦ ?_⟩
  exact ⟨h₁ k (by omega), h₂ k (by omega), h₃ k (by omega), h₄ k (by omega),
    ⟨(h₅ k (by omega)).1, (h₅ k (by omega)).2, h₅' k (by omega)⟩, h₆ k (by omega), h₇ k (by omega)⟩

end row

end ArithS
