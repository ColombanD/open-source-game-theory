import ArithS.Tau.Entangled.Congr
import ArithS.Cells.PositiveCells

/-!
# ArithS.Tau.Entangled.Dimcid — DIMCID's self-fulfilling family on a member slot

In `S'` DIMCID defects against every closed program (`Cells/DimcidFlips.lean`, `dimcid_vs_closed`): its guard "if
I cooperate with `X`, `X` defects against me" is made true by the defection a proof of it triggers. On a system
the same argument runs on the member slot: for a system `S` whose member `i` is DIMCID probing member `j'`, a box
of its guard in the two frames it is consulted in — its own self-play `(i, i)` and the antecedent's run `(i, j')`
— makes member `i` DEFECT in both, so the antecedent "I cooperate with member `j'`" is false and both guards hold,
in both readings (`loebSound_Di`); `family_found` then delivers both boxes for all large `k` (`found_Di`).
`boxConseq_pQ₂_above` is the box-consequence twin (`Cells/Common/Khat.lean` §3) for a partner whose guard
describes DIMCID's play (Cupod's "DIMCID defects against itself").
-/

set_option linter.constructorNameAsVariable false

namespace ArithS.Tau

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1
open LAct
open PD PD.Tau

/-- Dupoc's raw member guard at the pronoun `j`. -/
abbrev entDmG (j : ℕ) : Formula := .plays (.bot (.selfIdx j)) (.bot (.selfIdx j)) .C
/-- DIMCID's raw member guard at the pronoun `j`. -/
abbrev entDimG (j : ℕ) : Formula := .impl (.plays .self (.bot (.selfIdx j)) .C) (.plays (.bot (.selfIdx j)) .self .D)
/-- CIMCIC's raw member guard at the pronoun `j`. -/
abbrev entCimG (j : ℕ) : Formula := .impl (.plays .self (.bot (.selfIdx j)) .C) (.plays (.bot (.selfIdx j)) .self .C)
/-- Cupod's raw member guard at the pronoun `j`. -/
abbrev entCmG (j : ℕ) : Formula := .plays (.bot (.selfIdx j)) (.bot (.selfIdx j)) .D

lemma dim_eq (j k : ℕ) : dim j k = .search k (entDimG j) (.const .D) (.const Action.D.swap) := rfl
lemma cim_eq (j k : ℕ) : cim j k = .search k (entCimG j) (.const .C) (.const Action.C.swap) := rfl
lemma cm_eq (j k : ℕ) : cm j k = .search k (entCmG j) (.const .D) (.const Action.D.swap) := rfl
lemma dm_eq' (j k : ℕ) : dm j k = .search k (entDmG j) (.const .C) (.const Action.C.swap) := rfl

/-- **The box-consequence twin of `loebSound_pQ₂_above`**: the four boxes of `pQ (q₀ ⋏ q₁)` make `r` true in
both readings. -/
theorem boxConseq_pQ₂_above (q₀ q₁ r : Semisentence LAct 1) (K : ℕ)
    (h : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (k : V), (K : V) ≤ k →
      LenBox TAct k (instB (⌜q₀⌝ : V) k) → LenBox TAct k (instB (⌜q₁⌝ : V) k) →
      LenBox TAct k (instB (⌜Semiformula.lMap swap q₀⌝ : V) k) → LenBox TAct k (instB (⌜Semiformula.lMap swap q₁⌝ : V) k) →
      Semiformula.Eval (s := stdReading V) ![k] Empty.elim r ∧
      Semiformula.Eval (s := stdReading V) ![k] Empty.elim (Semiformula.lMap swap r)) :
    BoxConseq (pQ (q₀ ⋏ q₁)) r (14 + K) 16 := by
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
  obtain ⟨e, e'⟩ := h V k hk b₁ b₂ b₃ b₄
  refine ⟨e, ?_⟩
  rw [eval_swappedReading]
  exact e'

namespace Sys2

/-- **DIMCID's Löb premise on the member slot**: member `i` is DIMCID (`entDimG j'`, then-action `D`); boxes of its
guard in the frames `(i, i)` and `(i, j')` make it defect in both, falsifying the antecedent of both guards —
in the transposed system the transposed member cooperates, falsifying the transposed antecedent likewise. -/
theorem loebSound_Di (S : Sys2) (i j' : ℕ) (hi : i ≤ 1) (hj' : j' ≤ 1)
    (hg : (S.mem i).g = template13 (entDimG j')) (ha : (S.mem i).a = 1) :
    LoebSound (pQ (S.q i i i ⋏ S.q i i j')) (14 + S.K) 16 := by
  refine loebSound_pQ₂_above _ _ S.K fun V _ _ k hk b₁ b₂ b₃ b₄ ↦ ?_
  have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
  rw [← stdReadingV_eq_stdReading]
  have hD := Sys2.plays_of_box hk i hi i j' b₂
  have hDT := Sys2.tr_plays_of_box hk i hi i j' b₄
  rw [ha, Nat.cast_one] at hD
  rw [tr_mem S i hi, SM.tr_a, ha] at hDT
  simp only [Nat.sub_self, Nat.cast_zero] at hDT
  have hA : ¬ ∃ n, EvalGraph n (pBot (S.code i k)) (pBot (S.code j' k)) (pBot (S.code i k)) (actCode .C : V) := by
    rintro ⟨n, hn⟩
    have := EvalGraph.unique_V' n 4 _ _ _ _ _ hn hD
    rw [actCode_C_cast] at this
    exact _root_.zero_ne_one this
  have hAT : ¬ ∃ n, EvalGraph n (pBot (S.tr.code i k)) (pBot (S.tr.code j' k)) (pBot (S.tr.code i k)) (actCode Action.C.swap : V) := by
    rintro ⟨n, hn⟩
    have := EvalGraph.unique_V' n 4 _ _ _ _ _ hn hDT
    rw [show Action.C.swap = .D from rfl, actCode_D_cast] at this
    exact _root_.one_ne_zero this
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (Sys2.eval_q_impl hk hj' hg i i).mpr fun h ↦ absurd h hA
  · exact (Sys2.eval_q_impl hk hj' hg i j').mpr fun h ↦ absurd h hA
  · exact (Sys2.eval_q_impl_swap hk hj' hg i i).mpr fun h ↦ absurd h hAT
  · exact (Sys2.eval_q_impl_swap hk hj' hg i j').mpr fun h ↦ absurd h hAT

/-- **DIMCID finds its guard in both frames for all large `k`** (with the threshold for the instance equations). -/
theorem found_Di (S : Sys2) (i j' : ℕ) (hi : i ≤ 1) (hj' : j' ≤ 1)
    (hg : (S.mem i).g = template13 (entDimG j')) (ha : (S.mem i).a = 1) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k → S.K ≤ k ∧
      LenBox TAct k (instB (⌜S.q i i i⌝ : ℕ) k) ∧ LenBox TAct k (instB (⌜S.q i i j'⌝ : ℕ) k) := by
  obtain ⟨k₀, h⟩ := family_found (pQ (S.q i i i ⋏ S.q i i j')) boundedInnerNec_sixteen (loebSound_Di S i j' hi hj' hg ha)
  refine ⟨k₀ + S.K, fun k hk ↦ ?_⟩
  obtain ⟨a, ha', hbox⟩ := h k (by omega)
  obtain ⟨b₁, b₂, -, -⟩ := boxes_pQ₂_nat _ _ S.K k a ha' hbox
  exact ⟨by omega, b₁, b₂⟩

/-- A box of `S.q j i i'` at ℕ, read on the consulted code (the instance equation at ℕ, with the threshold as
`Nat.le`), the member's template spelled out. -/
theorem box_guard_nat {S : Sys2} {k : ℕ} (hk : S.K ≤ k) (j i i' : ℕ) {φ : PD.Formula} (hg : (S.mem j).g = template13 φ)
    (h : LenBox TAct k (instB (⌜S.q j i i'⌝ : ℕ) k)) :
    LenBox TAct k (guardCodeB (sysCloseTemplate (S.D k) (⌜template13 φ⌝ : ℕ)) (pBot (S.code i k)) (pBot (S.code i' k)) k) := by
  have e := Sys2.guard_eq_instB (V := ℕ) (S := S) (k := k) (le_def.mpr (Nat.eq_or_lt_of_le (by rw [natCast_nat]; exact hk))) j i i'
  rw [natCast_nat, hg] at e
  rw [e]; exact h

theorem not_box_guard_nat {S : Sys2} {k : ℕ} (hk : S.K ≤ k) (j i i' : ℕ) {φ : PD.Formula} (hg : (S.mem j).g = template13 φ)
    (h : ¬ LenBox TAct k (instB (⌜S.q j i i'⌝ : ℕ) k)) :
    ¬ LenBox TAct k (guardCodeB (sysCloseTemplate (S.D k) (⌜template13 φ⌝ : ℕ)) (pBot (S.code i k)) (pBot (S.code i' k)) k) := by
  have e := Sys2.guard_eq_instB (V := ℕ) (S := S) (k := k) (le_def.mpr (Nat.eq_or_lt_of_le (by rw [natCast_nat]; exact hk))) j i i'
  rw [natCast_nat, hg] at e
  rw [e]; exact h

/-- The converse at ℕ: a box on the consulted code is a box of the instance. -/
theorem box_instB_of_guard_nat {S : Sys2} {k : ℕ} (hk : S.K ≤ k) (j i i' : ℕ) {φ : PD.Formula} (hg : (S.mem j).g = template13 φ)
    (h : LenBox TAct k (guardCodeB (sysCloseTemplate (S.D k) (⌜template13 φ⌝ : ℕ)) (pBot (S.code i k)) (pBot (S.code i' k)) k)) :
    LenBox TAct k (instB (⌜S.q j i i'⌝ : ℕ) k) := by
  have e := Sys2.guard_eq_instB (V := ℕ) (S := S) (k := k) (le_def.mpr (Nat.eq_or_lt_of_le (by rw [natCast_nat]; exact hk))) j i i'
  rw [natCast_nat, hg] at e
  rw [← e]; exact h

/-- The play of member `j` at ℕ from a box of its instance (`plays_of_box` at ℕ, `Nat.le` threshold). -/
theorem plays_of_box_nat {S : Sys2} {k : ℕ} (hk : S.K ≤ k) (j : ℕ) (hj : j ≤ 1) (i i' : ℕ)
    (h : LenBox TAct k (instB (⌜S.q j i i'⌝ : ℕ) k)) :
    EvalGraph 4 (pBot (S.code i k)) (pBot (S.code i' k)) (pBot (S.code j k)) (S.mem j).a := by
  have := Sys2.plays_of_box (V := ℕ) (S := S) (k := k) (le_def.mpr (Nat.eq_or_lt_of_le (by rw [natCast_nat]; exact hk))) j hj i i' h
  rwa [natCast_nat] at this

end Sys2

end ArithS.Tau
