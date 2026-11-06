import ArithS.Cells.FloorDichotomy
import ArithS.Cells.CupodTrollEngine
import ArithS.Cells.DupocTrollBot

/-!
# ArithS.Cells.TrollReduction — the hinge of Dupoc × CupodTroll is inter-reducible with bounded consistency

`Cells/FloorDichotomy` §5 and `Cells/FloorReductions` tie the hinges of Dupoc × DBot and Dupoc × EBot to the
τ-symmetrized bounded-consistency instance on Dupoc's guard against `.bot DefectBot`. This module does the same
for **Dupoc × CupodTroll**, on a DIFFERENT false sentence: the troll's own `.eq` guard.

`CupodTrollBot k = .search k (.eq .opp (CupodBot k)) (.const D) (.const C)`. The hinge is
`A_k = □_k "CupodTrollBot k plays C against DupocBot k"` (`dich_DupocBot_vs_CupodTrollBot`). The troll is ONE search
node with constant branches, so in every model it plays C against Dupoc IF AND ONLY IF its guard

  `ε_k` = "the opponent IS `CupodBot k`", in the frame `(CupodTrollBot k, DupocBot k)`

— FALSE in ℕ (`progCode_DupocBot_ne_CupodBot`) — is NOT found within `k`. There is no second route to the troll's
C (contrast OBot, `Cells/CupodOBot`), and no positive side fact is needed (contrast EBot's second rung), so the
two uniform theorems are unconditional and both overheads are logarithmic:

* **The reduction** (`hinge_reduces_to_bounded_consistency_DupocBot_vs_CupodTrollBot`):
  `TAct ⊢ ∀ k, r(k) → (¬□_k ε_k ∨ ¬□_k τε_k)` (`tact_rTr_imp_negTwinT`), so a proof of the hinge within `k` yields
  a proof of `negTwinT(k)` within `k + C₀ + C₁·size k`.
* **The converse** (`bounded_consistency_reduces_to_hinge_DupocBot_vs_CupodTrollBot`):
  `TAct ⊢ ∀ k, (¬□_k ε_k ∧ ¬□_k τε_k) → r(k)` (`tact_conjTwinT_imp_rTr`), so a proof of `conjTwinT(k)` within `m`
  yields the hinge within `m + C₀ + C₁·size k`.

The τ-twin `τε_k` is the transposed troll's guard "the opponent IS `DupocBot k`" in the frame of the transposed
pair (the transposed troll `.search k (.eq .opp (DupocBot k)) C D` facing `CupodBot k`): the swapped reading of the
same play. `TAct` proves the disjunction uniformly because it cannot tell its two readings apart; at ℕ the two
disjuncts are equivalent by the τ-symmetry of proofs, so `negTwinT(k)` SAYS "`ε_k` is not provable within `k`"
(`negTwinT_true_iff`), a true bounded-consistency-type statement whose provability within `k + c` is the question.

Vocabulary: the engine troll is the simple member `sTc .D` (`Cells/CupodTrollEngine`), described in every model by
`dpT`; Dupoc by `dpDu` (`Cells/DupocTrollBot`); the stored `.eq` template is `gEq (gP .D) (actCode .D)`; the box as
a formula is `boxK` (`Cells/FloorDichotomy` §5.3).

Conventions: `simp` never sees a closed quote; `omega` is never asked about `V`; no `sorry`, no `axiom`.
-/

set_option linter.constructorNameAsVariable false

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open LAct
open PD.Bots
open ArithS.Tau

section troll

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ### 1. A simple member's else-clause and its inverse, in every model -/

/-- A play of a simple member that differs from its then-action means its consulted guard was NOT found
(`not_found_of_SV_play` on a stored thirteen-variable template). -/
theorem sm_not_found_of_play_V (s : SM) {k me opp r n : V} (h : EvalGraph n me opp (s.code k) r)
    (hr : r ≠ (s.a : V)) : ¬ LenBox TAct k (guardCodeB ((⌜s.g⌝ : ℕ) : V) me opp k) := by
  obtain ⟨n', rfl, _⟩ := EvalGraph.case_iff.mp h
  unfold SM.code at h
  rcases EvalGraph.search_iff.mp h with ⟨_, hp⟩ | ⟨hn, _⟩
  · obtain ⟨m, rfl, _⟩ := EvalGraph.case_iff.mp hp
    exact absurd (EvalGraph.const_iff.mp hp) hr
  · exact hn

/-- A simple member's else-clause in any frame (fuel 2): guard not found ⇒ the else-action (`SM.then_V`'s twin). -/
theorem sm_else_V (s : SM) (k me opp : V)
    (h : ¬ LenBox TAct k (guardCodeB ((⌜s.g⌝ : ℕ) : V) me opp k)) :
    EvalGraph 2 me opp (s.code k) ((1 - s.a : ℕ) : V) := by
  unfold SM.code
  rw [show (2 : V) = 1 + 1 from one_add_one_eq_two.symm, EvalGraph.search_iff]
  exact Or.inr ⟨h, by rw [show (1 : V) = 0 + 1 by simp, EvalGraph.const_iff]⟩

/-! ### 2. The formulas: the hinge `r`, the false guard `ε`, the twins -/

/-- The hinge as a fixed formula: "CupodTroll(k) plays C against Dupoc(k)", in Dupoc's frame. -/
noncomputable def rTr : Semisentence LAct 1 := qF (gP .C) dpDu dpT

/-- The troll's guard against Dupoc as a fixed formula: "the opponent IS `CupodBot k`" in the frame
`(CupodTroll k, Dupoc k)` — the FALSE sentence `ε_k` whose unprovability within `k` is the troll's C. -/
noncomputable def qEps : Semisentence LAct 1 := qF13 (gEq (gP .D) (actCode .D)) dpT dpDu

/-- The τ-twin: the transposed troll's guard "the opponent IS `DupocBot k`" against the transposed Dupoc. -/
lemma lMap_swap_qEps : Semiformula.lMap swap qEps = qF13 (gEq (gP .C) (actCode .C)) dpT.tr dpDu.tr := by
  unfold qEps
  rw [lMap_swap_qF13, lMap_swap_gEq _ _ (actCode_zero_or_one .D), lMap_swap_gP_D]
  rfl

/-- "`ε_k` or its τ-twin is not provable within `k`" — the τ-symmetrized bounded-consistency instance. -/
noncomputable def negTwinT : Semisentence LAct 1 := ∼ boxK qEps ⋎ ∼ boxK (Semiformula.lMap swap qEps)

/-- "Neither `ε_k` nor its τ-twin is provable within `k`". -/
noncomputable def conjTwinT : Semisentence LAct 1 := ∼ boxK qEps ⋏ ∼ boxK (Semiformula.lMap swap qEps)

theorem eval_negTwinT_iff (S : Structure LAct V) (hS : Structure.lMap emb S = standardModel V) (k : V) :
    Semiformula.Eval (s := S) ![k] Empty.elim negTwinT ↔
      (¬ LenBoxUnbounded TAct k (instB (⌜qEps⌝ : V) k) ∨
        ¬ LenBoxUnbounded TAct k (instB (⌜Semiformula.lMap swap qEps⌝ : V) k)) := by
  unfold negTwinT
  simp only [LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_neg, LogicalConnective.Prop.or_eq,
    LogicalConnective.Prop.neg_eq]
  rw [eval_boxK_iff _ S hS, eval_boxK_iff _ S hS]

theorem eval_conjTwinT_iff (S : Structure LAct V) (hS : Structure.lMap emb S = standardModel V) (k : V) :
    Semiformula.Eval (s := S) ![k] Empty.elim conjTwinT ↔
      (¬ LenBoxUnbounded TAct k (instB (⌜qEps⌝ : V) k) ∧
        ¬ LenBoxUnbounded TAct k (instB (⌜Semiformula.lMap swap qEps⌝ : V) k)) := by
  unfold conjTwinT
  simp only [LogicalConnective.HomClass.map_and, LogicalConnective.HomClass.map_neg, LogicalConnective.Prop.and_eq,
    LogicalConnective.Prop.neg_eq]
  rw [eval_boxK_iff _ S hS, eval_boxK_iff _ S hS]

end troll

/-! ### 3. The two uniform theorems -/

/-- **`TAct ⊢ ∀ k, r(k) → negTwinT(k)`**: in every model and both readings, the troll's cooperation with
`DupocBot k` is its else-branch — its `.eq` guard `ε_k` (standard reading) or the τ-twin (swapped reading) was not
found within `k`. -/
theorem tact_rTr_imp_negTwinT : TAct ⊢ ∀¹ (rTr 🡒 negTwinT) := by
  refine tact_all_of_both _ (fun M _ _ x ↦ ?_) (fun M _ _ x ↦ ?_)
  · have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    simp only [LogicalConnective.HomClass.map_imply, LogicalConnective.Prop.arrow_eq]
    intro hr
    obtain ⟨n, hn⟩ := (eval_qF_plays .C dpDu dpT x).mp hr
    rw [eval_negTwinT_iff _ (by rw [stdReadingV_eq_stdReading]; exact stdReading_lMap_emb)]
    left
    rw [lenBoxUnbounded_iff_lenBox, qEps, ← guardCodeB_qF13 _ (isSemiformula7_gEq_D M), dpT_val]
    rw [dpT_val] at hn
    refine sm_not_found_of_play_V (sTc .D) hn ?_
    show ((actCode .C : ℕ) : M) ≠ ((actCode .D : ℕ) : M)
    rw [actCode_C_cast, actCode_D_cast]
    exact _root_.zero_ne_one
  · have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    simp only [LogicalConnective.HomClass.map_imply, LogicalConnective.Prop.arrow_eq]
    intro hr
    rw [eval_swappedReading, ← stdReadingV_eq_stdReading, rTr, lMap_swap_qF, lMap_swap_gP_C] at hr
    obtain ⟨n, hn⟩ := (eval_qF_plays .D dpDu.tr dpT.tr x).mp hr
    rw [eval_negTwinT_iff _ swappedReading_lMap_emb]
    right
    rw [lenBoxUnbounded_iff_lenBox, lMap_swap_qEps, ← guardCodeB_qF13 _ (isSemiformula7_gEq_C M), dpT_tr_val]
    rw [dpT_tr_val] at hn
    refine sm_not_found_of_play_V (sTc .C) hn ?_
    show ((actCode .D : ℕ) : M) ≠ ((actCode .C : ℕ) : M)
    rw [actCode_C_cast, actCode_D_cast]
    exact _root_.one_ne_zero

/-- **`TAct ⊢ ∀ k, conjTwinT(k) → r(k)`**: neither guard found ⇒ the troll's else-branch C against `DupocBot k`
(the transposed troll's else-branch D against `CupodBot k` in the swapped reading). -/
theorem tact_conjTwinT_imp_rTr : TAct ⊢ ∀¹ (conjTwinT 🡒 rTr) := by
  refine tact_all_of_both _ (fun M _ _ x ↦ ?_) (fun M _ _ x ↦ ?_)
  · have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    simp only [LogicalConnective.HomClass.map_imply, LogicalConnective.Prop.arrow_eq]
    intro h
    obtain ⟨h1, _⟩ := (eval_conjTwinT_iff _ (by rw [stdReadingV_eq_stdReading]; exact stdReading_lMap_emb) x).mp h
    rw [lenBoxUnbounded_iff_lenBox, qEps, ← guardCodeB_qF13 _ (isSemiformula7_gEq_D M), dpT_val] at h1
    refine (eval_qF_plays .C dpDu dpT x).mpr ⟨2, ?_⟩
    rw [dpT_val]
    exact sm_else_V (sTc .D) x _ _ h1
  · have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    simp only [LogicalConnective.HomClass.map_imply, LogicalConnective.Prop.arrow_eq]
    intro h
    obtain ⟨_, h2⟩ := (eval_conjTwinT_iff _ swappedReading_lMap_emb x).mp h
    rw [lenBoxUnbounded_iff_lenBox, lMap_swap_qEps, ← guardCodeB_qF13 _ (isSemiformula7_gEq_C M), dpT_tr_val] at h2
    rw [eval_swappedReading, ← stdReadingV_eq_stdReading, rTr, lMap_swap_qF, lMap_swap_gP_C]
    refine (eval_qF_plays .D dpDu.tr dpT.tr x).mpr ⟨2, ?_⟩
    rw [dpT_tr_val]
    exact sm_else_V (sTc .C) x _ _ h2

/-! ### 4. At ℕ: the hinge code is the instance of `r`; the reduction and its converse -/

/-- The hinge of Dupoc × CupodTroll, as consulted by the evaluator, is the `binNumeral k`-instance of `rTr`. -/
theorem hinge_DupocBot_vs_CupodTrollBot_eq (k : ℕ) :
    guardCodeB (templateCode phiDu) (progCode (DupocBot k)) (progCode (CupodTrollBot k)) k =
      (⌜(rTr ⇜ ![Semiterm.lMap emb (binNumeralMeta k)] : Sentence LAct)⌝ : ℕ) := by
  rw [hingeB phiDu]
  have e := guardCode_qF (V := ℕ) (gP .C) dpDu dpT k
  rw [dpDu_val, dpT_val, ← progCode_CupodTrollBot_sT] at e
  have hq : instB (⌜rTr⌝ : ℕ) k = ⌜(rTr ⇜ ![Semiterm.lMap emb (binNumeralMeta k)] : Sentence LAct)⌝ := by
    have := quote_instB (V := ℕ) rTr k
    rwa [natCast_nat] at this
  rw [← hq, progCode_DupocBot_SV, templateCode_eq_quote_template phiDu rfl]
  exact e

/-- **THE REDUCTION.** If the hinge of Dupoc × CupodTroll holds — "CupodTrollBot k plays C against `DupocBot k`" is
`TAct`-provable within `k` — then "`ε_k` or its τ-twin is NOT provable within `k`" (`ε_k` = the troll's `.eq` guard
against Dupoc, FALSE in ℕ; `negTwinT_true_iff`) is `TAct`-provable within `k + C₀ + C₁·size k`: one instantiation of
the uniform theorem `tact_rTr_imp_negTwinT` at `binNumeral k` and one modus ponens. -/
theorem hinge_reduces_to_bounded_consistency_DupocBot_vs_CupodTrollBot :
    ∃ C₀ C₁ : ℕ, ∀ k : ℕ,
      LenBox TAct k (guardCodeB (templateCode phiDu) (progCode (DupocBot k)) (progCode (CupodTrollBot k)) k) →
      LenBox TAct (k + C₀ + C₁ * Nat.size k)
        (⌜(negTwinT ⇜ ![Semiterm.lMap emb (binNumeralMeta k)] : Sentence LAct)⌝ : ℕ) := by
  obtain ⟨N₃, hN₃⟩ := lenBoxNat_of_provable tact_rTr_imp_negTwinT
  refine ⟨N₃ + 13 * formulaLenMeta ((rTr 🡒 negTwinT : Semisentence LAct 1) : Semiproposition LAct 1) + 8
      + 20 * formulaLenMeta (rTr : Semiproposition LAct 1) + 20 * formulaLenMeta (negTwinT : Semiproposition LAct 1) + 9,
    30 * formulaLenMeta ((rTr 🡒 negTwinT : Semisentence LAct 1) : Semiproposition LAct 1) + 6
      + 60 * formulaLenMeta (rTr : Semiproposition LAct 1) + 60 * formulaLenMeta (negTwinT : Semiproposition LAct 1),
    fun k hA ↦ ?_⟩
  rw [hinge_DupocBot_vs_CupodTrollBot_eq, lenBox_nat] at hA
  have h1 := lenBoxNat_inst_size (rTr 🡒 negTwinT) k hN₃
  have hχt := formulaLenMeta_subst_binNumeralMeta_le (rTr 🡒 negTwinT) k
  have hrt := formulaLenMeta_subst_binNumeralMeta_le rTr k
  have hnt := formulaLenMeta_subst_binNumeralMeta_le negTwinT k
  set t : ClosedSemiterm LAct 0 := Semiterm.lMap emb (binNumeralMeta k) with ht
  set s := Nat.size k with hs
  set fχ := formulaLenMeta ((rTr 🡒 negTwinT : Semisentence LAct 1) : Semiproposition LAct 1) with hfχ
  set fr := formulaLenMeta (rTr : Semiproposition LAct 1) with hfr
  set fn := formulaLenMeta (negTwinT : Semiproposition LAct 1) with hfn
  have h1' : LenBoxNat (codeBound : ℕ → ℕ) (N₃ + 5 * (fχ * (6 * s + 2)) + 3 * fχ + 6 * s + 8) TAct
      (⌜((rTr 🡒 negTwinT) ⇜ ![t] : Sentence LAct)⌝ : ℕ) :=
    lenBoxNat_codeBound_mono (by omega) h1
  rw [substs_imp] at h1'
  have h3 := lenBoxNat_mp h1' hA
  rw [lenBox_nat]
  refine lenBoxNat_codeBound_mono ?_ h3
  calc _ ≤ N₃ + 5 * (fχ * (6 * s + 2)) + 3 * fχ + 6 * s + 8 + k
        + 10 * (fr * (6 * s + 2) + fn * (6 * s + 2)) + 9 := by gcongr
    _ = k + (N₃ + 13 * fχ + 8 + 20 * fr + 20 * fn + 9) + (30 * fχ + 6 + 60 * fr + 60 * fn) * s := by ring

/-- **THE CONVERSE.** A `TAct`-proof within `m` of "neither `ε_k` nor its τ-twin is provable within `k`" yields the
hinge — "CupodTrollBot k plays C against `DupocBot k`" — within `m + C₀ + C₁·size k`, by the evaluator's determinism
inside `TAct` (`tact_conjTwinT_imp_rTr`): the conjunction, not the disjunction, because each reading needs its own
twin. No threshold: the troll's else-play needs no positive side fact. -/
theorem bounded_consistency_reduces_to_hinge_DupocBot_vs_CupodTrollBot :
    ∃ C₀ C₁ : ℕ, ∀ k m : ℕ,
      LenBox TAct m (⌜(conjTwinT ⇜ ![Semiterm.lMap emb (binNumeralMeta k)] : Sentence LAct)⌝ : ℕ) →
      LenBox TAct (m + C₀ + C₁ * Nat.size k)
        (guardCodeB (templateCode phiDu) (progCode (DupocBot k)) (progCode (CupodTrollBot k)) k) := by
  obtain ⟨N₃, hN₃⟩ := lenBoxNat_of_provable tact_conjTwinT_imp_rTr
  refine ⟨N₃ + 13 * formulaLenMeta ((conjTwinT 🡒 rTr : Semisentence LAct 1) : Semiproposition LAct 1) + 8
      + 20 * formulaLenMeta (conjTwinT : Semiproposition LAct 1) + 20 * formulaLenMeta (rTr : Semiproposition LAct 1) + 9,
    30 * formulaLenMeta ((conjTwinT 🡒 rTr : Semisentence LAct 1) : Semiproposition LAct 1) + 6
      + 60 * formulaLenMeta (conjTwinT : Semiproposition LAct 1) + 60 * formulaLenMeta (rTr : Semiproposition LAct 1),
    fun k m hC ↦ ?_⟩
  rw [lenBox_nat] at hC
  have h1 := lenBoxNat_inst_size (conjTwinT 🡒 rTr) k hN₃
  have hχt := formulaLenMeta_subst_binNumeralMeta_le (conjTwinT 🡒 rTr) k
  have hct := formulaLenMeta_subst_binNumeralMeta_le conjTwinT k
  have hrt := formulaLenMeta_subst_binNumeralMeta_le rTr k
  set t : ClosedSemiterm LAct 0 := Semiterm.lMap emb (binNumeralMeta k) with ht
  set s := Nat.size k with hs
  set fχ := formulaLenMeta ((conjTwinT 🡒 rTr : Semisentence LAct 1) : Semiproposition LAct 1) with hfχ
  set fc := formulaLenMeta (conjTwinT : Semiproposition LAct 1) with hfc
  set fr := formulaLenMeta (rTr : Semiproposition LAct 1) with hfr
  have h1' : LenBoxNat (codeBound : ℕ → ℕ) (N₃ + 5 * (fχ * (6 * s + 2)) + 3 * fχ + 6 * s + 8) TAct
      (⌜((conjTwinT 🡒 rTr) ⇜ ![t] : Sentence LAct)⌝ : ℕ) :=
    lenBoxNat_codeBound_mono (by omega) h1
  rw [substs_imp] at h1'
  have h3 := lenBoxNat_mp h1' hC
  rw [hinge_DupocBot_vs_CupodTrollBot_eq, lenBox_nat]
  refine lenBoxNat_codeBound_mono ?_ h3
  calc _ ≤ N₃ + 5 * (fχ * (6 * s + 2)) + 3 * fχ + 6 * s + 8 + m
        + 10 * (fc * (6 * s + 2) + fr * (6 * s + 2)) + 9 := by gcongr
    _ = m + (N₃ + 13 * fχ + 8 + 20 * fc + 20 * fr + 9) + (30 * fχ + 6 + 60 * fc + 60 * fr) * s := by ring

/-! ### 5. What the conclusion SAYS at ℕ -/

/-- The `binNumeral k`-instance of `qEps` IS the guard the engine's troll consults against `DupocBot k`:
"`DupocBot k` IS `CupodBot k`", `.eq .opp (CupodBot k)` in the frame `(CupodTrollBot k, DupocBot k)`. -/
theorem instB_qEps_eq (k : ℕ) :
    instB (⌜qEps⌝ : ℕ) k =
      guardCode (templateCode (phiT k)) (progCode (CupodTrollBot k)) (progCode (DupocBot k)) := by
  have e := guardCodeB_qF13 (V := ℕ) (gEq (gP .D) (actCode .D)) (isSemiformula7_gEq_D ℕ) dpT dpDu k
  rw [dpT_val, dpDu_val, ← progCode_CupodTrollBot_sT, natCast_nat] at e
  rw [qEps, ← e, ← guardCodeB_templateCodeAt (phiT k) _ _ k, progCode_DupocBot_SV]
  unfold templateCodeAt
  rw [templateAt_phiT]
  rfl

/-- **At ℕ, `negTwinT(k)` says exactly "the troll's `.eq` guard against `DupocBot k` is not provable within `k`"**:
the two disjuncts are equivalent by the τ-symmetry of `TAct`'s proofs (`lenBoxNat_swap_iff`, exact in length). The
guard is false (Dupoc is not Cupod) and `TAct` is sound, so the statement is TRUE at every `k`; the question is
only whether `TAct` PROVES it within `k + c`. -/
theorem negTwinT_true_iff (k : ℕ) :
    ℕ↓[LAct] ⊧ (negTwinT ⇜ ![Semiterm.lMap emb (binNumeralMeta k)] : Sentence LAct) ↔
      ¬ LenBox TAct k (guardCode (templateCode (phiT k)) (progCode (CupodTrollBot k)) (progCode (DupocBot k))) := by
  rw [models_iff]
  unfold Semiformula.Realize
  rw [Semiformula.eval_substs]
  have hv : (Semiterm.val (s := stdReadingNat) ![] Empty.elim ∘ ![Semiterm.lMap emb (binNumeralMeta k)]) = ![(k : ℕ)] := by
    funext i
    fin_cases i
    show Semiterm.val (s := stdReadingNat) ![] Empty.elim (Semiterm.lMap emb (binNumeralMeta k)) = k
    rw [Semiterm.val_lMap, stdReadingNat_lMap_emb]
    have := val_binNumeralMeta_V (V := ℕ) k
    rwa [natCast_nat] at this
  rw [hv, eval_negTwinT_iff stdReadingNat stdReadingNat_lMap_emb k, lenBoxUnbounded_iff_lenBox,
    lenBoxUnbounded_iff_lenBox]
  have hq1 : instB (⌜qEps⌝ : ℕ) k = ⌜(qEps ⇜ ![Semiterm.lMap emb (binNumeralMeta k)] : Sentence LAct)⌝ := by
    have := quote_instB (V := ℕ) qEps k
    rwa [natCast_nat] at this
  have hq2 : instB (⌜Semiformula.lMap swap qEps⌝ : ℕ) k =
      ⌜((Semiformula.lMap swap qEps) ⇜ ![Semiterm.lMap emb (binNumeralMeta k)] : Sentence LAct)⌝ := by
    have := quote_instB (V := ℕ) (Semiformula.lMap swap qEps) k
    rwa [natCast_nat] at this
  have hsym : LenBox TAct k (instB (⌜Semiformula.lMap swap qEps⌝ : ℕ) k) ↔
      LenBox TAct k (instB (⌜qEps⌝ : ℕ) k) := by
    rw [hq1, hq2, lenBox_nat, lenBox_nat, substs_lMap_swap_binNumeralMeta]
    exact (lenBoxNat_swap_iff k _).symm
  rw [hsym, instB_qEps_eq]
  constructor
  · rintro (h | h) <;> exact h
  · exact fun h ↦ Or.inl h

end ArithS
