import ArithS.Tau.Entangled.Family
import ArithS.Tau.Entangled.Base
import ArithS.Cells.Common.Khat

/-!
# ArithS.Tau.Entangled.Loeb — the Löb-family kit for two-member systems

For a system `S : Sys2` the closed member `j`, run in the frame `(pBot (S.code i k), pBot (S.code i' k))` (the
bot-wrapped members `i`, `i'` — every frame a member is ever run in by a bit or by a partner's probe), consults
the box of `S.q j i i' (k)`: `qT13` of member `j`'s template with the frame towers `S.TX i`, `S.TX i'` and the
member towers `S.TM 0`, `S.TM 1` (`guard_eq_instB`). Above the threshold `S.K`:

* **the search clauses**: a box of `S.q j i i' (k)` makes `pBot (S.code j k)` play member `j`'s then-action in
  that frame (`plays_of_box`), no box its else-action (`plays_of_not_box`);
* **the truth equations** of the two guard shapes, in the standard reading (`eval_q_partner`, `eval_q_impl`:
  "the bot-wrapped member `j'` plays `a` against itself", "if the frame player plays `a` against member `j'`,
  member `j'` plays `a'` against it") and in the swapped reading, where the same sentences speak about the
  TRANSPOSED system `S.tr` (`eval_q_partner_swap`, `eval_q_impl_swap`);
* **the conjunction families**: `pQ (q₀ ⋏ q₁)` with slack `(14 + K, 16)` (`loebSound_pQ₂_above`,
  `boxes_pQ₂_of_found`) and `pQ ((q₀ ⋏ q₁) ⋏ (q₂ ⋏ q₃))` with slack `(21 + K, 24)` — the ∧-eliminations on codes
  with ONE uniform bound per level (`boxes_of_and`), so that a family's Löb premise reduces to one semantic
  fact about its conjuncts' boxes.
-/

set_option linter.constructorNameAsVariable false

namespace ArithS.Tau

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open LAct

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ### 1. ∧-elimination with a uniform bound -/

section andElim

lemma formulaLen_instB_and (φ ψ : Semisentence LAct 1) (k : V) :
    formulaLen LAct (instB (⌜φ ⋏ ψ⌝ : V) k) = formulaLen LAct (instB (⌜φ⌝ : V) k) + formulaLen LAct (instB (⌜ψ⌝ : V) k) + 1 := by
  rw [instB_quote_and, formulaLen_and (isFormula_instB_quote _ k).isUFormula (isFormula_instB_quote _ k).isUFormula]

/-- Both conjuncts from a box of the conjunction, at the budget `a + 8 z + 7` for any `z` above the sum of the
conjuncts' lengths. -/
lemma boxes_of_and (φ ψ : Semisentence LAct 1) (k a z : V)
    (hz : formulaLen LAct (instB (⌜φ⌝ : V) k) + formulaLen LAct (instB (⌜ψ⌝ : V) k) ≤ z)
    (h : LenBoxUnbounded TAct a (instB (⌜φ ⋏ ψ⌝ : V) k)) :
    LenBoxUnbounded TAct (a + 8 * z + 7) (instB (⌜φ⌝ : V) k) ∧ LenBoxUnbounded TAct (a + 8 * z + 7) (instB (⌜ψ⌝ : V) k) := by
  rw [instB_quote_and] at h
  have hx := isFormula_instB_quote φ k
  have hy := isFormula_instB_quote ψ k
  have hle : a + 8 * (formulaLen LAct (instB (⌜φ⌝ : V) k) + formulaLen LAct (instB (⌜ψ⌝ : V) k)) + 7 ≤ a + 8 * z + 7 := by
    gcongr
  exact ⟨lenBoxUnbounded_mono_V hle (lenBoxUnbounded_andL_V hx hy h),
    lenBoxUnbounded_mono_V hle (lenBoxUnbounded_andR_V hx hy h)⟩

/-- The length of a conjunct is below the length of the conjunction. -/
lemma len_le_of_and_left (φ ψ : Semisentence LAct 1) (k : V) :
    formulaLen LAct (instB (⌜φ⌝ : V) k) + formulaLen LAct (instB (⌜ψ⌝ : V) k) ≤ formulaLen LAct (instB (⌜φ ⋏ ψ⌝ : V) k) := by
  rw [formulaLen_instB_and]; exact le_self_add

lemma lMap_swap_and (φ ψ : Semisentence LAct 1) : Semiformula.lMap swap (φ ⋏ ψ) = Semiformula.lMap swap φ ⋏ Semiformula.lMap swap ψ :=
  LogicalConnective.HomClass.map_and _ _ _

/-- **The four boxes of a `pQ (q₀ ⋏ q₁)` box**, at the budget `a + 16 z + 14` (`z` the family's length). -/
theorem boxes_pQ₂ (q₀ q₁ : Semisentence LAct 1) (k a : V)
    (h : LenBoxUnbounded TAct a (instB (⌜pQ (q₀ ⋏ q₁)⌝ : V) k)) :
    let z := formulaLen LAct (instB (⌜pQ (q₀ ⋏ q₁)⌝ : V) k)
    LenBoxUnbounded TAct (a + 8 * z + 7 + 8 * z + 7) (instB (⌜q₀⌝ : V) k) ∧
    LenBoxUnbounded TAct (a + 8 * z + 7 + 8 * z + 7) (instB (⌜q₁⌝ : V) k) ∧
    LenBoxUnbounded TAct (a + 8 * z + 7 + 8 * z + 7) (instB (⌜Semiformula.lMap swap q₀⌝ : V) k) ∧
    LenBoxUnbounded TAct (a + 8 * z + 7 + 8 * z + 7) (instB (⌜Semiformula.lMap swap q₁⌝ : V) k) := by
  intro z
  have hz₁ := len_le_of_and_left (q₀ ⋏ q₁) (Semiformula.lMap swap (q₀ ⋏ q₁)) k
  obtain ⟨h₁, h₂⟩ := boxes_of_and (q₀ ⋏ q₁) (Semiformula.lMap swap (q₀ ⋏ q₁)) k a z hz₁ h
  have hz₂ : formulaLen LAct (instB (⌜q₀⌝ : V) k) + formulaLen LAct (instB (⌜q₁⌝ : V) k) ≤ z :=
    le_trans (len_le_of_and_left q₀ q₁ k) (le_trans le_self_add hz₁)
  have hz₃ : formulaLen LAct (instB (⌜Semiformula.lMap swap q₀⌝ : V) k) +
      formulaLen LAct (instB (⌜Semiformula.lMap swap q₁⌝ : V) k) ≤ z := by
    refine le_trans (len_le_of_and_left _ _ k) (le_trans ?_ (le_trans le_add_self hz₁))
    rw [lMap_swap_and]
  rw [lMap_swap_and] at h₂
  obtain ⟨g₁, g₂⟩ := boxes_of_and q₀ q₁ k _ z hz₂ h₁
  obtain ⟨g₃, g₄⟩ := boxes_of_and _ _ k _ z hz₃ h₂
  exact ⟨g₁, g₂, g₃, g₄⟩

/-- The slack `(14, 16)` covers the two eliminations. -/
lemma slack_two (a z : V) : a + 8 * z + 7 + 8 * z + 7 ≤ a + ((14 : ℕ) : V) + ((16 : ℕ) : V) * z := by
  push_cast
  exact le_of_eq (by ring)

/-- **The Löb premise of `pQ (q₀ ⋏ q₁)` at slack `(14 + K, 16)`, from one semantic fact above `K`**: the four
instances provable within `k` make the four true in the standard reading. -/
theorem loebSound_pQ₂_above (q₀ q₁ : Semisentence LAct 1) (K : ℕ)
    (h : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (k : V), (K : V) ≤ k →
      LenBox TAct k (instB (⌜q₀⌝ : V) k) → LenBox TAct k (instB (⌜q₁⌝ : V) k) →
      LenBox TAct k (instB (⌜Semiformula.lMap swap q₀⌝ : V) k) → LenBox TAct k (instB (⌜Semiformula.lMap swap q₁⌝ : V) k) →
      Semiformula.Eval (s := stdReading V) ![k] Empty.elim q₀ ∧ Semiformula.Eval (s := stdReading V) ![k] Empty.elim q₁ ∧
      Semiformula.Eval (s := stdReading V) ![k] Empty.elim (Semiformula.lMap swap q₀) ∧
      Semiformula.Eval (s := stdReading V) ![k] Empty.elim (Semiformula.lMap swap q₁)) :
    LoebSound (pQ (q₀ ⋏ q₁)) (14 + K) 16 := by
  intro V _ _ k a ha hp
  have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
  have hk : (K : V) ≤ k :=
    le_trans (Nat.cast_le.mpr (Nat.le_add_left K 14)) (le_trans le_add_self (le_trans le_self_add ha))
  have h14 : ((14 : ℕ) : V) ≤ ((14 + K : ℕ) : V) := Nat.cast_le.mpr (Nat.le_add_right 14 K)
  have hb : a + ((14 : ℕ) : V) + ((16 : ℕ) : V) * formulaLen LAct (instB (⌜pQ (q₀ ⋏ q₁)⌝ : V) k) ≤ k :=
    le_trans (add_le_add (add_le_add le_rfl h14) le_rfl) ha
  obtain ⟨g₁, g₂, g₃, g₄⟩ := boxes_pQ₂ q₀ q₁ k a hp
  have hle := le_trans (slack_two a (formulaLen LAct (instB (⌜pQ (q₀ ⋏ q₁)⌝ : V) k))) hb
  have b₁ := (lenBoxUnbounded_iff_lenBox _ _).mp (lenBoxUnbounded_mono_V hle g₁)
  have b₂ := (lenBoxUnbounded_iff_lenBox _ _).mp (lenBoxUnbounded_mono_V hle g₂)
  have b₃ := (lenBoxUnbounded_iff_lenBox _ _).mp (lenBoxUnbounded_mono_V hle g₃)
  have b₄ := (lenBoxUnbounded_iff_lenBox _ _).mp (lenBoxUnbounded_mono_V hle g₄)
  obtain ⟨e₀, e₁, e₀', e₁'⟩ := h V k hk b₁ b₂ b₃ b₄
  constructor
  · rw [eval_pQ_std]
    simp only [LogicalConnective.HomClass.map_and, LogicalConnective.Prop.and_eq]
    exact ⟨⟨e₀, e₁⟩, e₀', e₁'⟩
  · rw [eval_pQ_swap]
    simp only [LogicalConnective.HomClass.map_and, LogicalConnective.Prop.and_eq]
    exact ⟨⟨e₀', e₁'⟩, e₀, e₁⟩

/-- **At ℕ: the four boxes from `family_found`'s witness.** -/
theorem boxes_pQ₂_nat (q₀ q₁ : Semisentence LAct 1) (K k a : ℕ)
    (ha : a + (14 + K) + 16 * formulaLen LAct (instB (⌜pQ (q₀ ⋏ q₁)⌝ : ℕ) k) ≤ k)
    (h : LenBoxUnbounded TAct a (instB (⌜pQ (q₀ ⋏ q₁)⌝ : ℕ) k)) :
    LenBox TAct k (instB (⌜q₀⌝ : ℕ) k) ∧ LenBox TAct k (instB (⌜q₁⌝ : ℕ) k) ∧
    LenBox TAct k (instB (⌜Semiformula.lMap swap q₀⌝ : ℕ) k) ∧ LenBox TAct k (instB (⌜Semiformula.lMap swap q₁⌝ : ℕ) k) := by
  obtain ⟨g₁, g₂, g₃, g₄⟩ := boxes_pQ₂ (V := ℕ) q₀ q₁ k a h
  have h' : a + 14 + 16 * formulaLen LAct (instB (⌜pQ (q₀ ⋏ q₁)⌝ : ℕ) k) ≤ k := by omega
  have hz := slack_two (V := ℕ) a (formulaLen LAct (instB (⌜pQ (q₀ ⋏ q₁)⌝ : ℕ) k))
  simp only [natCast_nat] at hz
  have hle := le_def.mpr (le_def_trans (le_def.mp hz) (Nat.eq_or_lt_of_le h'))
  exact ⟨(lenBoxUnbounded_iff_lenBox _ _).mp (lenBoxUnbounded_mono_V hle g₁),
    (lenBoxUnbounded_iff_lenBox _ _).mp (lenBoxUnbounded_mono_V hle g₂),
    (lenBoxUnbounded_iff_lenBox _ _).mp (lenBoxUnbounded_mono_V hle g₃),
    (lenBoxUnbounded_iff_lenBox _ _).mp (lenBoxUnbounded_mono_V hle g₄)⟩

end andElim

/-! ### 2. The guard formulas of a system, their instance equations and search clauses -/

namespace Sys2

/-- **Member `j`'s guard, consulted in the frame of the bot-wrapped members `(i, i')`**: `qT13` of its template
with the frame towers and the two member towers (one re-valuation pair serves all four slots: the canonical
choice is made for the whole system). -/
noncomputable def q (S : Sys2) (j i i' : ℕ) : Semisentence LAct 1 :=
  qT13 (S.mem j).g (S.TX i) S.uT S.wT (S.TX i') S.uT S.wT (S.TM 0) S.uT S.wT (S.TM 1) S.uT S.wT

lemma code_zero (S : Sys2) (k : V) : S.code 0 k = pSys (S.D k) 0 := by unfold code; rw [Nat.cast_zero]
lemma code_one (S : Sys2) (k : V) : S.code 1 k = pSys (S.D k) 1 := by unfold code; rw [Nat.cast_one]

/-- **The instance equation** above the threshold: the consulted code IS the `binNumeral k`-instance. -/
theorem guard_eq_instB {S : Sys2} {k : V} (hk : (S.K : V) ≤ k) (j i i' : ℕ) :
    guardCodeB (sysCloseTemplate (S.D k) ((⌜(S.mem j).g⌝ : ℕ) : V)) (pBot (S.code i k)) (pBot (S.code i' k)) k =
      instB (⌜S.q j i i'⌝ : V) k := by
  rw [coe_quote_sentence₁₃]
  unfold q
  have hi := describesBot S i
  have hi' := describesBot S i'
  have h0 := describesMem S 0
  have h1 := describesMem S 1
  have eX := hi.hX V k hk
  have eU := hi.hU V k hk
  have eW := hi.hW V k hk
  have eX' := hi'.hX V k hk
  have eU' := hi'.hU V k hk
  have eW' := hi'.hW V k hk
  have e0X := h0.hX V k hk
  have e0U := h0.hU V k hk
  have e0W := h0.hW V k hk
  have e1X := h1.hX V k hk
  have e1U := h1.hU V k hk
  have e1W := h1.hW V k hk
  rw [descVal_TX hk] at eX eU eW
  rw [descVal_TX hk] at eX' eU' eW'
  rw [descVal_TM hk, code_zero] at e0X e0U e0W
  rw [descVal_TM hk, code_one] at e1X e1U e1W
  exact guardCodeB_sysClose_eq_instB _ k (S.D k) _ _ _ _ _ _ _ _ _ _ _ _ eX eU eW eX' eU' eW' e0X e0U e0W e1X e1U e1W

/-- A box of `S.q j i i' (k)` makes the bot-wrapped member `j` play its then-action in the frame `(i, i')`. -/
theorem plays_of_box {S : Sys2} {k : V} (hk : (S.K : V) ≤ k) (j : ℕ) (hj : j ≤ 1) (i i' : ℕ)
    (h : LenBox TAct k (instB (⌜S.q j i i'⌝ : V) k)) :
    EvalGraph 4 (pBot (S.code i k)) (pBot (S.code i' k)) (pBot (S.code j k)) ((S.mem j).a : V) := by
  rw [← guard_eq_instB hk] at h
  exact member_then_V S j hj k _ _ h

/-- No box: the else-action. -/
theorem plays_of_not_box {S : Sys2} {k : V} (hk : (S.K : V) ≤ k) (j : ℕ) (hj : j ≤ 1) (i i' : ℕ)
    (h : ¬ LenBox TAct k (instB (⌜S.q j i i'⌝ : V) k)) :
    EvalGraph 4 (pBot (S.code i k)) (pBot (S.code i' k)) (pBot (S.code j k)) ((1 - (S.mem j).a : ℕ) : V) := by
  rw [← guard_eq_instB hk] at h
  exact member_else_V S j hj k _ _ h

/-! #### The truth equations -/

/-- The thirteen values of `S.q j i i'` at `k`. -/
noncomputable def vals (S : Sys2) (i i' : ℕ) (k : V) : Fin 13 → V :=
  ![(S.TX i).val (s := stdReadingV V) ![k] Empty.elim, S.uT.val (s := stdReadingV V) ![] Empty.elim,
    S.wT.val (s := stdReadingV V) ![] Empty.elim, (S.TX i').val (s := stdReadingV V) ![k] Empty.elim,
    S.uT.val (s := stdReadingV V) ![] Empty.elim, S.wT.val (s := stdReadingV V) ![] Empty.elim, k,
    (S.TM 0).val (s := stdReadingV V) ![k] Empty.elim, S.uT.val (s := stdReadingV V) ![] Empty.elim,
    S.wT.val (s := stdReadingV V) ![] Empty.elim, (S.TM 1).val (s := stdReadingV V) ![k] Empty.elim,
    S.uT.val (s := stdReadingV V) ![] Empty.elim, S.wT.val (s := stdReadingV V) ![] Empty.elim]

omit [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
lemma eval_q_iff_vals (S : Sys2) (j i i' : ℕ) (k : V) :
    Semiformula.Eval (s := stdReadingV V) ![k] Empty.elim (S.q j i i') ↔
      Semiformula.Eval (s := stdReadingV V) (S.vals i i' k) Empty.elim (S.mem j).g := by
  unfold q vals
  exact eval_qT13_iff _ _ _ _ _ _ _ _ _ _ _ _ _ k

lemma vals_me {S : Sys2} {k : V} (hk : (S.K : V) ≤ k) (i i' : ℕ) :
    revalue (S.vals i i' k 1) (S.vals i i' k 2) (S.vals i i' k 0) = pBot (S.code i k) := by
  have := descVal_TX hk (S := S) (k := k) i
  rw [descVal_def] at this
  exact this

lemma vals_mem {S : Sys2} {k : V} (hk : (S.K : V) ≤ k) (i i' j : ℕ) (hj : j ≤ 1) :
    memVal (S.vals i i' k) j = S.code j k := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hj with rfl | rfl
  · rw [memVal_zero]
    have := descVal_TM hk (S := S) (k := k) 0
    rw [descVal_def] at this
    exact this
  · rw [memVal_one]
    have := descVal_TM hk (S := S) (k := k) 1
    rw [descVal_def] at this
    exact this

/-- **The partner-probe guard** (`.plays (.bot (.selfIdx j')) (.bot (.selfIdx j')) a`) of member `j`, in the
standard reading: the bot-wrapped member `j'` plays `a` against itself. -/
theorem eval_q_partner {S : Sys2} {k : V} (hk : (S.K : V) ≤ k) {j j' : ℕ} (hj' : j' ≤ 1) {a : PD.Action}
    (hg : (S.mem j).g = template13 (.plays (.bot (.selfIdx j')) (.bot (.selfIdx j')) a)) (i i' : ℕ) :
    Semiformula.Eval (s := stdReadingV V) ![k] Empty.elim (S.q j i i') ↔
      ∃ n, EvalGraph n (pBot (S.code j' k)) (pBot (S.code j' k)) (pBot (S.code j' k)) (actCode a : V) := by
  rw [eval_q_iff_vals, hg, eval_template13_partner j' hj', vals_mem hk i i' j' hj']

/-- **The implication guard** (`.impl (.plays .self (.bot (.selfIdx j')) a) (.plays (.bot (.selfIdx j')) .self a')`)
of member `j`, in the standard reading, in the frame `(i, i')`: if the bot-wrapped member `i` plays `a` against
the bot-wrapped member `j'`, the latter plays `a'` against the former. -/
theorem eval_q_impl {S : Sys2} {k : V} (hk : (S.K : V) ≤ k) {j j' : ℕ} (hj' : j' ≤ 1) {a a' : PD.Action}
    (hg : (S.mem j).g = template13 (.impl (.plays .self (.bot (.selfIdx j')) a) (.plays (.bot (.selfIdx j')) .self a'))) (i i' : ℕ) :
    Semiformula.Eval (s := stdReadingV V) ![k] Empty.elim (S.q j i i') ↔
      ((∃ n, EvalGraph n (pBot (S.code i k)) (pBot (S.code j' k)) (pBot (S.code i k)) (actCode a : V)) →
        (∃ n, EvalGraph n (pBot (S.code j' k)) (pBot (S.code i k)) (pBot (S.code j' k)) (actCode a' : V))) := by
  rw [eval_q_iff_vals, hg, template13_impl]
  simp only [LogicalConnective.HomClass.map_imply, LogicalConnective.Prop.arrow_eq]
  rw [eval_template13_self_partner j' hj', eval_template13_partner_self j' hj', vals_mem hk i i' j' hj', vals_me hk]

/-! #### The swapped reading: the same sentences about the transposed system -/

/-- `lMap swap (S.q j i i')` is the transposed system's guard formula with the transposed template. -/
lemma lMap_swap_q (S : Sys2) (j i i' : ℕ) :
    Semiformula.lMap swap (S.q j i i') =
      qT13 (Semiformula.lMap swap (S.mem j).g) (S.TX i) (Semiterm.lMap swap S.uT) (Semiterm.lMap swap S.wT)
        (S.TX i') (Semiterm.lMap swap S.uT) (Semiterm.lMap swap S.wT)
        (S.TM 0) (Semiterm.lMap swap S.uT) (Semiterm.lMap swap S.wT)
        (S.TM 1) (Semiterm.lMap swap S.uT) (Semiterm.lMap swap S.wT) := by
  unfold q
  rw [lMap_swap_qT13, lMap_swap_TX, lMap_swap_TX, lMap_swap_TM, lMap_swap_TM]

/-- The thirteen values of the swapped guard formula. -/
noncomputable def valsT (S : Sys2) (i i' : ℕ) (k : V) : Fin 13 → V :=
  ![(S.TX i).val (s := stdReadingV V) ![k] Empty.elim, (Semiterm.lMap swap S.uT).val (s := stdReadingV V) ![] Empty.elim,
    (Semiterm.lMap swap S.wT).val (s := stdReadingV V) ![] Empty.elim, (S.TX i').val (s := stdReadingV V) ![k] Empty.elim,
    (Semiterm.lMap swap S.uT).val (s := stdReadingV V) ![] Empty.elim, (Semiterm.lMap swap S.wT).val (s := stdReadingV V) ![] Empty.elim, k,
    (S.TM 0).val (s := stdReadingV V) ![k] Empty.elim, (Semiterm.lMap swap S.uT).val (s := stdReadingV V) ![] Empty.elim,
    (Semiterm.lMap swap S.wT).val (s := stdReadingV V) ![] Empty.elim, (S.TM 1).val (s := stdReadingV V) ![k] Empty.elim,
    (Semiterm.lMap swap S.uT).val (s := stdReadingV V) ![] Empty.elim, (Semiterm.lMap swap S.wT).val (s := stdReadingV V) ![] Empty.elim]

omit [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
lemma eval_swap_q_iff_valsT (S : Sys2) (j i i' : ℕ) (k : V) :
    Semiformula.Eval (s := stdReadingV V) ![k] Empty.elim (Semiformula.lMap swap (S.q j i i')) ↔
      Semiformula.Eval (s := stdReadingV V) (S.valsT i i' k) Empty.elim (Semiformula.lMap swap (S.mem j).g) := by
  rw [lMap_swap_q]
  unfold valsT
  exact eval_qT13_iff _ _ _ _ _ _ _ _ _ _ _ _ _ k

lemma valsT_me {S : Sys2} {k : V} (hk : (S.K : V) ≤ k) (i i' : ℕ) :
    revalue (S.valsT i i' k 1) (S.valsT i i' k 2) (S.valsT i i' k 0) = pBot (S.tr.code i k) := by
  have := descVal_TX_T hk (S := S) (k := k) i
  rw [descVal_def, lMap_swap_TX] at this
  exact this

lemma valsT_mem {S : Sys2} {k : V} (hk : (S.K : V) ≤ k) (i i' j : ℕ) (hj : j ≤ 1) :
    memVal (S.valsT i i' k) j = S.tr.code j k := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hj with rfl | rfl
  · rw [memVal_zero]
    have := descVal_TM_T hk (S := S) (k := k) 0
    rw [descVal_def, lMap_swap_TM] at this
    exact this
  · rw [memVal_one]
    have := descVal_TM_T hk (S := S) (k := k) 1
    rw [descVal_def, lMap_swap_TM] at this
    exact this

/-- The partner-probe guard in the SWAPPED reading: the transposed system's bot-wrapped member `j'` plays
`a.swap` against itself. -/
theorem eval_q_partner_swap {S : Sys2} {k : V} (hk : (S.K : V) ≤ k) {j j' : ℕ} (hj' : j' ≤ 1) {a : PD.Action}
    (hg : (S.mem j).g = template13 (.plays (.bot (.selfIdx j')) (.bot (.selfIdx j')) a)) (i i' : ℕ) :
    Semiformula.Eval (s := stdReadingV V) ![k] Empty.elim (Semiformula.lMap swap (S.q j i i')) ↔
      ∃ n, EvalGraph n (pBot (S.tr.code j' k)) (pBot (S.tr.code j' k)) (pBot (S.tr.code j' k)) (actCode a.swap : V) := by
  rw [eval_swap_q_iff_valsT, hg, lMap_swap_template13_partner j' hj', eval_template13_partner j' hj', valsT_mem hk i i' j' hj']

/-- The implication guard in the SWAPPED reading. -/
theorem eval_q_impl_swap {S : Sys2} {k : V} (hk : (S.K : V) ≤ k) {j j' : ℕ} (hj' : j' ≤ 1) {a a' : PD.Action}
    (hg : (S.mem j).g = template13 (.impl (.plays .self (.bot (.selfIdx j')) a) (.plays (.bot (.selfIdx j')) .self a'))) (i i' : ℕ) :
    Semiformula.Eval (s := stdReadingV V) ![k] Empty.elim (Semiformula.lMap swap (S.q j i i')) ↔
      ((∃ n, EvalGraph n (pBot (S.tr.code i k)) (pBot (S.tr.code j' k)) (pBot (S.tr.code i k)) (actCode a.swap : V)) →
        (∃ n, EvalGraph n (pBot (S.tr.code j' k)) (pBot (S.tr.code i k)) (pBot (S.tr.code j' k)) (actCode a'.swap : V))) := by
  rw [eval_swap_q_iff_valsT, hg, lMap_swap_template13_impl, lMap_swap_template13_self_partner j' hj',
    lMap_swap_template13_partner_self j' hj']
  simp only [LogicalConnective.HomClass.map_imply, LogicalConnective.Prop.arrow_eq]
  rw [eval_template13_self_partner j' hj', eval_template13_partner_self j' hj', valsT_mem hk i i' j' hj', valsT_me hk]

/-! #### The transposed system's search clauses from the swapped boxes -/

lemma tr_mem (S : Sys2) (j : ℕ) (hj : j ≤ 1) : S.tr.mem j = (S.mem j).tr := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hj with rfl | rfl <;> rfl

theorem canonical_tr_code {S : Sys2} {k : V} (hk : (S.K : V) ≤ k) (j : ℕ) :
    canonical (S.tr.code j k) = S.can.code j k := by
  rw [← transposeCode_code, canonical_transposeCode, canonical_code hk]

theorem revalueU_tr_code {S : Sys2} {k : V} (hk : (S.K : V) ≤ k) (j : ℕ) :
    revalueU (S.tr.code j k) = (⌜Semiterm.lMap swap S.uT⌝ : V) := by
  have e : transposeCode (S.tr.code j k) = S.code j k := by rw [← transposeCode_code, transposeCode_transposeCode]
  unfold revalueU uT
  rw [e]
  by_cases h : S.orig
  · rw [if_neg (lt_asymm (code_lt_tr hk h j)), if_pos (code_lt_tr hk h j), if_pos h, lMap_swap_cterm_C, quote_cterm_D]
  · rw [if_pos (tr_lt_code hk h j), if_neg h, lMap_swap_cterm_D, quote_cterm_C]

theorem revalueW_tr_code {S : Sys2} {k : V} (hk : (S.K : V) ≤ k) (j : ℕ) :
    revalueW (S.tr.code j k) = (⌜Semiterm.lMap swap S.wT⌝ : V) := by
  have e : transposeCode (S.tr.code j k) = S.code j k := by rw [← transposeCode_code, transposeCode_transposeCode]
  unfold revalueW wT
  rw [e]
  by_cases h : S.orig
  · rw [if_neg (lt_asymm (code_lt_tr hk h j)), if_pos (code_lt_tr hk h j), if_pos h, lMap_swap_cterm_D, quote_cterm_C]
  · rw [if_pos (tr_lt_code hk h j), if_neg h, lMap_swap_cterm_C, quote_cterm_D]

/-- **The transposed instance equation**: the transposed system's member `j`, in the frame of ITS bot-wrapped
members `(i, i')`, consults the `binNumeral k`-instance of `lMap swap (S.q j i i')`. -/
theorem tr_guard_eq_instB {S : Sys2} {k : V} (hk : (S.K : V) ≤ k) (j : ℕ) (hj : j ≤ 1) (i i' : ℕ) :
    guardCodeB (sysCloseTemplate (S.tr.D k) ((⌜(S.tr.mem j).g⌝ : ℕ) : V)) (pBot (S.tr.code i k)) (pBot (S.tr.code i' k)) k =
      instB (⌜Semiformula.lMap swap (S.q j i i')⌝ : V) k := by
  rw [tr_mem S j hj, SM.tr_g, coe_quote_sentence₁₃, lMap_swap_q]
  refine guardCodeB_sysClose_eq_instB _ k (S.tr.D k) _ _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hX_TX hk, canonical_pBot, canonical_pBot, canonical_tr_code hk, canonical_code hk]
  · rw [revalueU_pBot, revalueU_tr_code hk]
  · rw [revalueW_pBot, revalueW_tr_code hk]
  · rw [hX_TX hk, canonical_pBot, canonical_pBot, canonical_tr_code hk, canonical_code hk]
  · rw [revalueU_pBot, revalueU_tr_code hk]
  · rw [revalueW_pBot, revalueW_tr_code hk]
  · rw [hX_TM hk, ← code_zero, canonical_tr_code hk, canonical_code hk]
  · rw [← code_zero]; exact (revalueU_tr_code hk 0).symm
  · rw [← code_zero]; exact (revalueW_tr_code hk 0).symm
  · rw [hX_TM hk, ← code_one, canonical_tr_code hk, canonical_code hk]
  · rw [← code_one]; exact (revalueU_tr_code hk 1).symm
  · rw [← code_one]; exact (revalueW_tr_code hk 1).symm

/-- A box of the swapped guard makes the TRANSPOSED system's bot-wrapped member `j` play its (transposed)
then-action in the frame of the transposed members `(i, i')`. -/
theorem tr_plays_of_box {S : Sys2} {k : V} (hk : (S.K : V) ≤ k) (j : ℕ) (hj : j ≤ 1) (i i' : ℕ)
    (h : LenBox TAct k (instB (⌜Semiformula.lMap swap (S.q j i i')⌝ : V) k)) :
    EvalGraph 4 (pBot (S.tr.code i k)) (pBot (S.tr.code i' k)) (pBot (S.tr.code j k)) ((S.tr.mem j).a : V) := by
  rw [← tr_guard_eq_instB hk j hj] at h
  exact member_then_V S.tr j hj k _ _ h

end Sys2

/-! ### 3. The bridge to the engine's compiled members, at ℕ -/

namespace SM

/-- The simple member of a compiled searcher `.search k φ (.const a) (.const a.swap)`. -/
noncomputable def ofSearch (φ : PD.Formula) (a : PD.Action) : SM :=
  ⟨template13 φ, actCode a, by cases a <;> simp [actCode]⟩

lemma ofSearch_g (φ : PD.Formula) (a : PD.Action) : (ofSearch φ a).g = template13 φ := rfl
lemma ofSearch_a (φ : PD.Formula) (a : PD.Action) : (ofSearch φ a).a = actCode a := rfl

/-- At ℕ, the member's code is the engine's code of the searcher. -/
theorem code_nat (φ : PD.Formula) (a : PD.Action) (k : ℕ) (hφ : noBudgetSnapshotF φ = true := by noSnap_tac) :
    (ofSearch φ a).code k = progCode (.search k φ (.const a) (.const a.swap)) := by
  unfold code
  rw [progCode_search, templateCodeAt_eq_templateCode φ k hφ, progCode_const, progCode_const]
  simp only [natCast_nat, ofSearch_g, ofSearch_a]
  cases a <;> rfl

end SM

namespace Sys2

/-- At ℕ, the list code of a system of two compiled searchers is the engine's list code. -/
theorem D_nat (φ₀ φ₁ : PD.Formula) (a₀ a₁ : PD.Action) (k : ℕ)
    (h₀ : noBudgetSnapshotF φ₀ = true := by noSnap_tac) (h₁ : noBudgetSnapshotF φ₁ = true := by noSnap_tac) :
    (Sys2.mk (SM.ofSearch φ₀ a₀) (SM.ofSearch φ₁ a₁)).D k =
      progListCode (sys2 (.search k φ₀ (.const a₀) (.const a₀.swap)) (.search k φ₁ (.const a₁) (.const a₁.swap))) := by
  unfold D; rw [SM.code_nat _ _ _ h₀, SM.code_nat _ _ _ h₁]; rfl

theorem code_nat (φ₀ φ₁ : PD.Formula) (a₀ a₁ : PD.Action) (j k : ℕ)
    (h₀ : noBudgetSnapshotF φ₀ = true := by noSnap_tac) (h₁ : noBudgetSnapshotF φ₁ = true := by noSnap_tac) :
    (Sys2.mk (SM.ofSearch φ₀ a₀) (SM.ofSearch φ₁ a₁)).code j k =
      progCode (.sys (sys2 (.search k φ₀ (.const a₀) (.const a₀.swap)) (.search k φ₁ (.const a₁) (.const a₁.swap))) j) := by
  unfold code; rw [D_nat _ _ _ _ _ h₀ h₁, progCode_sys, natCast_nat]

/-- **The consulted code at ℕ is the engine's guard code of the CLOSED guard** (`templateCode_sysClose`), in the
engine's frame: the bridge from a family's box to `Base.lean`'s `bit_*_then` lemmas. -/
theorem guardCodeB_sysClose_nat (φ₀ φ₁ : PD.Formula) (a₀ a₁ : PD.Action) (k : ℕ) (φ : PD.Formula) (hφ : memberGuardF φ = true)
    (hns : noSelfIdxF (φ.sysClose (sys2 (.search k φ₀ (.const a₀) (.const a₀.swap)) (.search k φ₁ (.const a₁) (.const a₁.swap)))) = true)
    (x y : ℕ)
    (h₀ : noBudgetSnapshotF φ₀ = true := by noSnap_tac) (h₁ : noBudgetSnapshotF φ₁ = true := by noSnap_tac) :
    guardCodeB (sysCloseTemplate ((Sys2.mk (SM.ofSearch φ₀ a₀) (SM.ofSearch φ₁ a₁)).D k) ((⌜template13 φ⌝ : ℕ) : ℕ)) x y k =
      guardCode (templateCode (φ.sysClose (sys2 (.search k φ₀ (.const a₀) (.const a₀.swap)) (.search k φ₁ (.const a₁) (.const a₁.swap))))) x y := by
  rw [D_nat _ _ _ _ _ h₀ h₁]
  show guardCodeB (sysCloseTemplate _ (templateCode φ)) x y k = _
  rw [templateCode_sysClose _ φ hφ, guardCodeB_of_template (isSemiformula_templateCode _ hns)]

end Sys2

end ArithS.Tau
