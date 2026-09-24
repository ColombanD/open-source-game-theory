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
