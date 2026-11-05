import ArithS.Cells.FloorReductions
import ArithS.Cells.DupocTrollBot

/-!
# ArithS.Cells.ConReduction — a floor hinge found within `k` proves `Con_TAct(k − O(log k))` in about `k` symbols

`Cells/FloorDichotomy` §5 and `Cells/FloorReductions` tie the hinges of Dupoc × DBot / EBot to the unprovability of
ONE specific false sentence `σ_k`, with a τ-twin disjunction. This module gives the ONE-DIRECTION reduction to
LITERAL bounded consistency, generic in the hinge, and applies it to the CIMCIC floors, whose hinges are
implications about CIMCIC's own play and have no single false sentence behind them.

**The statement.** `conBelow C₀ C₁ (k)` is the one-variable formula "for every `j` with `j + C₀ + C₁·‖k‖ ≤ k`, `⊥`
has no `TAct`-proof of length `≤ j`", i.e. `Con_TAct(k − C₀ − C₁·‖k‖)` (`conBelow_true_iff`: at ℕ it says exactly
that, and it is true). For each hinge `A_k` below:

  `∃ k₀ C₀ C₁ D₀ D₁ D₂, ∀ k > k₀,  □_k A_k-sentence  →  □_{k + D₀ + D₁·size k + D₂·(size k)²} conBelow C₀ C₁ (k)`.

So a found hinge makes `TAct` prove its own consistency up to `k − O(log k)` with a proof of length
`k + O((log k)²)` — Pudlák's linear regime. Nothing is claimed in the other direction (from the consistency
statement back to the hinge one only gets the hinge from `Con` at a POLYNOMIALLY larger level: the two guard boxes
must first be proved as theorems, by inner necessitation).

**The generic lemma** (`tact_imp_conBelow`, `hinge_con_reduction`). Hypothesis, in every model above a threshold and
in both readings: the hinge sentence `r(x)` is true only if SOME guard `θ(x)` of a fixed finite list is NOT found
within `x`. Then `TAct ⊢ ∀ k ≥ k̂, r(k) → conBelow C₀ C₁ (k)`: a proof of `⊥` of length `≤ j` gives, in every model,
a proof of each `θ(x)` of length `≤ j + E₀ + E₁·‖x‖` (`exFalso_V`: the `binNumeral x`-instance of the `TAct`-theorem
`∀ k, ⊥ → θ(k)` and one cut, `Box/CutV.lenBoxUnbounded_cut_V_TAct`), hence within `x`. `⊥` and the box do not see the
action constants, so there is no twin disjunction; the list simply contains each guard and its τ-image.

**The semantic property, per hinge** (evaluator determinism, no proof theory):

* CIMCIC × DBot, × EBot (`rCcl_refutes_std/_swap`): the hinge "if I cooperate with `X`, `X` cooperates with me", when
  true, forbids that BOTH it and CIMCIC's guard against `.bot DefectBot` (`qCiB1`, the bounded Gödel sentence of
  CIMCIC) be found — found hinge ⇒ CIMCIC cooperates ⇒ `X` cooperates ⇒ CIMCIC did not cooperate with
  `.bot DefectBot` (`probe_of_dbot_C_V`, `probe_of_ebot_C_V`).
* CIMCIC × CupodTrollBot, × DupocTrollBot, × CupodBot (`rCi_refutes_std/_swap`, on described players `DP`): the
  opponent cooperates only through its own ELSE-branch, so found hinge ⇒ the opponent's own guard (`.eq`, resp.
  "CIMCIC plays D against me") is not found.
* Dupoc × DBot, × EBot (§6, a check of the generic lemma against the two specific reductions): the hinge true ⇒
  `σ_k` (resp. its twin) not found.

For CIMCIC × CupodBot this is the OUTER hinge of the nested dichotomy only. Conventions: every threshold
EXISTENTIAL; `simp` never sees a closed quote; no `sorry`, no `axiom`.
-/

set_option linter.constructorNameAsVariable false

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open LAct
open PD.Bots

/-! ### 1. Ex falso with length accounting, in every model -/

section exFalso

/-- `⊥` as a one-variable formula (so that it has `binNumeral k`-instances like every guard). -/
noncomputable def botF : Semisentence LAct 1 := ⊥

/-- `TAct ⊢ ∀ k, ⊥ → θ(k)`. -/
theorem tact_botF_imp (θ : Semisentence LAct 1) : TAct ⊢ ∀¹ (botF 🡒 θ) := by
  refine tact_all_of_both _ (fun M _ _ x ↦ ?_) (fun M _ _ x ↦ ?_)
  · simp [botF]
  · simp [botF]

/-- **Ex falso, in every model, with its cost**: a proof of (the `k`-instance of) `⊥` of length `≤ j` gives a proof
of `θ(k)` of length `≤ j + E₀ + E₁·‖k‖` — the instance of `∀ k, ⊥ → θ(k)` at `binNumeral k` and one cut. -/
theorem exFalso_V (θ : Semisentence LAct 1) :
    ∃ E₀ E₁ : ℕ, ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (k j : V), 1 ≤ ‖k‖ →
      LenBoxUnbounded TAct j (instB (⌜botF⌝ : V) k) →
      LenBoxUnbounded TAct (j + (E₀ : V) + (E₁ : V) * ‖k‖) (instB (⌜θ⌝ : V) k) := by
  obtain ⟨N, hN⟩ := exists_lenBoxUnbounded_V_of_proof (∀¹ (botF 🡒 θ)) (tact_botF_imp θ)
  set fχ := formulaLenMeta ((botF 🡒 θ : Semisentence LAct 1) : Semiproposition LAct 1) with hfχ
  set fb := formulaLenMeta (botF : Semiproposition LAct 1) with hfb
  set fθ := formulaLenMeta (θ : Semiproposition LAct 1) with hfθ
  refine ⟨N + 3 * fχ + 16, 35 * fχ + 7 + 70 * fb + 70 * fθ, fun V _ _ k j hs1 hj ↦ ?_⟩
  have h := hN V
  rw [quote_all_sentence] at h
  have h1 := lenBoxUnbounded_instB_V' (V := V) (k := k) (Sentence.quote_isSemiformul₁ (botF 🡒 θ)) h
  rw [formulaLen_quote_semisentence_V, ← hfχ, instB_quote_imp] at h1
  have hb0 := isSemiformula_instB (Sentence.quote_isSemiformul₁ botF) k
  have ht0 := isSemiformula_instB (Sentence.quote_isSemiformul₁ θ) k
  have h2 := lenBoxUnbounded_cut_V_TAct _ j _ _ hb0 ht0 h1 hj
  refine lenBoxUnbounded_mono_V ?_ h2
  have ht : termLen LAct (binNumeral k) ≤ 7 * ‖k‖ := termLen_binNumeral_le_V' hs1
  have hlb := formulaLen_instB_le (Sentence.quote_isSemiformul₁ botF) k
  have hlt := formulaLen_instB_le (Sentence.quote_isSemiformul₁ θ) k
  rw [formulaLen_quote_semisentence_V, ← hfb] at hlb
  rw [formulaLen_quote_semisentence_V, ← hfθ] at hlt
  have e2 : (5 : V) * ((fχ : V) * termLen LAct (binNumeral k)) ≤ 35 * fχ * ‖k‖ := by
    calc (5 : V) * ((fχ : V) * termLen LAct (binNumeral k)) ≤ 5 * ((fχ : V) * (7 * ‖k‖)) := by gcongr
      _ = 35 * fχ * ‖k‖ := by ring
  have e3 : formulaLen LAct (instB (⌜botF⌝ : V) k) ≤ 7 * fb * ‖k‖ := by
    calc formulaLen LAct (instB (⌜botF⌝ : V) k) ≤ (fb : V) * termLen LAct (binNumeral k) := hlb
      _ ≤ (fb : V) * (7 * ‖k‖) := by gcongr
      _ = 7 * fb * ‖k‖ := by ring
  have e4 : formulaLen LAct (instB (⌜θ⌝ : V) k) ≤ 7 * fθ * ‖k‖ := by
    calc formulaLen LAct (instB (⌜θ⌝ : V) k) ≤ (fθ : V) * termLen LAct (binNumeral k) := hlt
      _ ≤ (fθ : V) * (7 * ‖k‖) := by gcongr
      _ = 7 * fθ * ‖k‖ := by ring
  calc (N : V) + 5 * ((fχ : V) * termLen LAct (binNumeral k)) + 3 * (fχ : V) + termLen LAct (binNumeral k) + 7 + j
        + 10 * (formulaLen LAct (instB (⌜botF⌝ : V) k) + formulaLen LAct (instB (⌜θ⌝ : V) k)) + 9
      ≤ (N : V) + 35 * fχ * ‖k‖ + 3 * (fχ : V) + 7 * ‖k‖ + 7 + j + 10 * (7 * fb * ‖k‖ + 7 * fθ * ‖k‖) + 9 := by
        gcongr
    _ = j + ((N + 3 * fχ + 16 : ℕ) : V) + ((35 * fχ + 7 + 70 * fb + 70 * fθ : ℕ) : V) * ‖k‖ := by
        push_cast; ring

/-- Ex falso for a finite list of formulas, with ONE pair of constants. -/
theorem exFalso_list_V (θs : List (Semisentence LAct 1)) :
    ∃ E₀ E₁ : ℕ, ∀ θ ∈ θs, ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (k j : V), 1 ≤ ‖k‖ →
      LenBoxUnbounded TAct j (instB (⌜botF⌝ : V) k) →
      LenBoxUnbounded TAct (j + (E₀ : V) + (E₁ : V) * ‖k‖) (instB (⌜θ⌝ : V) k) := by
  induction θs with
  | nil => exact ⟨0, 0, fun θ h ↦ absurd h List.not_mem_nil⟩
  | cons θ₀ θs ih =>
    obtain ⟨A₀, A₁, hA⟩ := ih
    obtain ⟨B₀, B₁, hB⟩ := exFalso_V θ₀
    refine ⟨A₀ + B₀, A₁ + B₁, fun θ hθ V _ _ k j hs1 hj ↦ ?_⟩
    rcases List.mem_cons.mp hθ with rfl | hθ
    · refine lenBoxUnbounded_mono_V ?_ (hB V k j hs1 hj)
      calc j + (B₀ : V) + (B₁ : V) * ‖k‖ ≤ j + ((A₀ : V) + B₀) + ((A₁ : V) + B₁) * ‖k‖ := by
            gcongr <;> exact le_add_self
        _ = j + ((A₀ + B₀ : ℕ) : V) + ((A₁ + B₁ : ℕ) : V) * ‖k‖ := by push_cast; ring
    · refine lenBoxUnbounded_mono_V ?_ (hA θ hθ V k j hs1 hj)
      calc j + (A₀ : V) + (A₁ : V) * ‖k‖ ≤ j + ((A₀ : V) + B₀) + ((A₁ : V) + B₁) * ‖k‖ := by
            gcongr <;> exact le_self_add
        _ = j + ((A₀ + B₀ : ℕ) : V) + ((A₁ + B₁ : ℕ) : V) * ‖k‖ := by push_cast; ring

end exFalso

/-! ### 2. Bounded consistency below `k`, as one formula in `k` -/

section conBelow

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- `conCore (n, k, c, d)`: "for every `j` with `j + c + d·‖k‖ ≤ k`, the `k`-instance of the code `n` has no
`TAct`-proof of length `≤ j`". -/
noncomputable def conCore : Semisentence ℒₒᵣ 4 :=
  “n k c d. ∀ j, ∀ l, !lengthDef l k → j + c + d * l ≤ k → ¬ !bewBDef j n k”

lemma eval_conCore (n k c d : V) :
    Semiformula.Eval (s := standardModel V) ![n, k, c, d] Empty.elim conCore ↔
      ∀ j : V, j + c + d * ‖k‖ ≤ k → ¬ LenBoxUnbounded TAct j (instB n k) := by
  simp [conCore, length_defined.iff, bewB]

noncomputable def conCoreA : Semisentence LAct 4 := Semiformula.lMap emb conCore

/-- **`conBelow C₀ C₁ (k)` — bounded consistency of `TAct` below `k`**: "`⊥` has no `TAct`-proof of length `≤ j`,
for every `j` with `j + C₀ + C₁·‖k‖ ≤ k`", i.e. `Con_TAct(k − C₀ − C₁·‖k‖)`. The code of `⊥` is Foundation's Gödel
numeral (a constant, never evaluated); `C₀`, `C₁` are numerals. -/
noncomputable def conBelow (C₀ C₁ : ℕ) : Semisentence LAct 1 :=
  conCoreA ⇜ ![Semiterm.lMap emb (⌜botF⌝ : ArithmeticSemiterm Empty 1), #0,
    Semiterm.lMap emb ((C₀ : ℕ) : ArithmeticSemiterm Empty 1), Semiterm.lMap emb ((C₁ : ℕ) : ArithmeticSemiterm Empty 1)]

/-- **The semantics of `conBelow`** in every `LAct`-structure on `V` whose `ℒₒᵣ`-reduct is standard:
reading-independent (`⊥` and the box do not see the action constants). -/
theorem eval_conBelow_iff (S : Structure LAct V) (hS : Structure.lMap emb S = standardModel V) (C₀ C₁ : ℕ)
    (k : V) :
    Semiformula.Eval (s := S) ![k] Empty.elim (conBelow C₀ C₁) ↔
      ∀ j : V, j + (C₀ : V) + (C₁ : V) * ‖k‖ ≤ k → ¬ LenBoxUnbounded TAct j (instB (⌜botF⌝ : V) k) := by
  unfold conBelow
  rw [Semiformula.eval_substs]
  have hv : (Semiterm.val (s := S) ![k] Empty.elim ∘
      ![Semiterm.lMap emb (⌜botF⌝ : ArithmeticSemiterm Empty 1), #0,
        Semiterm.lMap emb ((C₀ : ℕ) : ArithmeticSemiterm Empty 1),
        Semiterm.lMap emb ((C₁ : ℕ) : ArithmeticSemiterm Empty 1)]) = ![(⌜botF⌝ : V), k, (C₀ : V), (C₁ : V)] := by
    funext i; fin_cases i
    · exact val_lMap_gödel S hS botF _
    · rfl
    · show Semiterm.val (s := S) ![k] Empty.elim (Semiterm.lMap emb ((C₀ : ℕ) : ArithmeticSemiterm Empty 1)) = (C₀ : V)
      rw [Semiterm.val_lMap, hS]
      simp [numeral_eq_natCast]
    · show Semiterm.val (s := S) ![k] Empty.elim (Semiterm.lMap emb ((C₁ : ℕ) : ArithmeticSemiterm Empty 1)) = (C₁ : V)
      rw [Semiterm.val_lMap, hS]
      simp [numeral_eq_natCast]
  rw [hv]
  unfold conCoreA
  rw [Semiformula.eval_lMap, hS]
  exact eval_conCore _ _ _ _

end conBelow

/-! ### 3. The generic reduction -/

section generic

/-- **THE GENERIC LEMMA.** Let `r(k)` be a sentence that, in every model above a threshold and in both readings,
is true only if SOME guard of a fixed finite list `θs` is NOT found within the budget (`¬ □_x θ(x)`). Then

  `TAct ⊢ ∀ k ≥ k̂', r(k) → Con_TAct(k − C₀ − C₁·‖k‖)`:

a proof of `⊥` with that much slack would, by ex falso (`exFalso_list_V`), prove every guard of the list within
the budget. No twin disjunction: `⊥` and the box are τ-invariant. -/
theorem tact_imp_conBelow (r : Semisentence LAct 1) (θs : List (Semisentence LAct 1)) (kHat : ℕ)
    (hstd : ∀ (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (x : M), (kHat : M) ≤ x →
      Semiformula.Eval (s := stdReadingV M) ![x] Empty.elim r →
      ∃ θ ∈ θs, ¬ LenBox TAct x (instB (⌜θ⌝ : M) x))
    (hswap : ∀ (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (x : M), (kHat : M) ≤ x →
      Semiformula.Eval (s := swappedReading M) ![x] Empty.elim r →
      ∃ θ ∈ θs, ¬ LenBox TAct x (instB (⌜θ⌝ : M) x)) :
    ∃ kHat' C₀ C₁ : ℕ, TAct ⊢ ∀¹ ((leF (↑kHat') #0 : Semisentence LAct 1) 🡒 (r 🡒 conBelow C₀ C₁)) := by
  obtain ⟨E₀, E₁, hE⟩ := exFalso_list_V θs
  refine ⟨kHat + 2, E₀, E₁, tact_all_above_of_both _ _ (fun M _ _ x hx ↦ ?_) (fun M _ _ x hx ↦ ?_)⟩
  · have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    have hk : (kHat : M) ≤ x := le_trans (by push_cast; exact le_self_add) hx
    have hs1 : 1 ≤ ‖x‖ := by
      have h1 : (1 : M) ≤ x := le_trans (by push_cast; exact le_add_left one_le_two) hx
      have := length_monotone h1
      rwa [length_one] at this
    simp only [LogicalConnective.HomClass.map_imply, LogicalConnective.Prop.arrow_eq]
    intro hr
    rw [eval_conBelow_iff _ (by rw [stdReadingV_eq_stdReading]; exact stdReading_lMap_emb)]
    intro j hj hbot
    obtain ⟨θ, hθ, hn⟩ := hstd M x hk hr
    exact hn ((lenBoxUnbounded_iff_lenBox _ _).mp (lenBoxUnbounded_mono_V hj (hE θ hθ M x j hs1 hbot)))
  · have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    have hk : (kHat : M) ≤ x := le_trans (by push_cast; exact le_self_add) hx
    have hs1 : 1 ≤ ‖x‖ := by
      have h1 : (1 : M) ≤ x := le_trans (by push_cast; exact le_add_left one_le_two) hx
      have := length_monotone h1
      rwa [length_one] at this
    simp only [LogicalConnective.HomClass.map_imply, LogicalConnective.Prop.arrow_eq]
    intro hr
    rw [eval_conBelow_iff _ swappedReading_lMap_emb]
    intro j hj hbot
    obtain ⟨θ, hθ, hn⟩ := hswap M x hk hr
    exact hn ((lenBoxUnbounded_iff_lenBox _ _).mp (lenBoxUnbounded_mono_V hj (hE θ hθ M x j hs1 hbot)))

/-- **The length statement at ℕ**: above the threshold, a `TAct`-proof of `r(k)` within `m` yields a `TAct`-proof
of `Con_TAct(k − C₀ − C₁·size k)` within `m + D₀ + D₁·size k + D₂·(size k)²` — the instance of the conditional
uniform theorem with its threshold cut away (`exists_instance_length_above`), then one modus ponens. -/
theorem con_reduction_of (r : Semisentence LAct 1) {kHat C₀ C₁ : ℕ}
    (hq : TAct ⊢ ∀¹ ((leF (↑kHat) #0 : Semisentence LAct 1) 🡒 (r 🡒 conBelow C₀ C₁))) :
    ∃ D₀ D₁ D₂ : ℕ, ∀ k m : ℕ, kHat < k →
      LenBox TAct m (⌜(r ⇜ ![Semiterm.lMap emb (binNumeralMeta k)] : Sentence LAct)⌝ : ℕ) →
      LenBox TAct (m + D₀ + D₁ * Nat.size k + D₂ * Nat.size k * Nat.size k)
        (⌜(conBelow C₀ C₁ ⇜ ![Semiterm.lMap emb (binNumeralMeta k)] : Sentence LAct)⌝ : ℕ) := by
  obtain ⟨K₀, K₁, K₂, hmeta⟩ := exists_instance_length_above (r 🡒 conBelow C₀ C₁) kHat hq
  refine ⟨K₀ + 20 * formulaLenMeta (r : Semiproposition LAct 1)
      + 20 * formulaLenMeta (conBelow C₀ C₁ : Semiproposition LAct 1) + 9,
    K₁ + 60 * formulaLenMeta (r : Semiproposition LAct 1) + 60 * formulaLenMeta (conBelow C₀ C₁ : Semiproposition LAct 1),
    K₂, fun k m hk hR ↦ ?_⟩
  rw [lenBox_nat] at hR
  have h1 := hmeta k hk
  have hrt := formulaLenMeta_subst_binNumeralMeta_le r k
  have hct := formulaLenMeta_subst_binNumeralMeta_le (conBelow C₀ C₁) k
  set t : ClosedSemiterm LAct 0 := Semiterm.lMap emb (binNumeralMeta k) with ht
  set s := Nat.size k with hs
  set fr := formulaLenMeta (r : Semiproposition LAct 1) with hfr
  set fc := formulaLenMeta (conBelow C₀ C₁ : Semiproposition LAct 1) with hfc
  rw [substs_imp] at h1
  have h3 := lenBoxNat_mp h1 hR
  rw [lenBox_nat]
  refine lenBoxNat_codeBound_mono ?_ h3
  calc _ ≤ K₀ + K₁ * s + K₂ * s * s + m + 10 * (fr * (6 * s + 2) + fc * (6 * s + 2)) + 9 := by gcongr
    _ = m + (K₀ + 20 * fr + 20 * fc + 9) + (K₁ + 60 * fr + 60 * fc) * s + K₂ * s * s := by ring

/-- The `binNumeral k`-instance of `⊥` is `⊥`. -/
lemma instB_botF_nat (k : ℕ) : instB (⌜botF⌝ : ℕ) k = (⌜(⊥ : Sentence LAct)⌝ : ℕ) := by
  have h := quote_instB (V := ℕ) botF k
  rw [natCast_nat] at h
  rw [h]
  rfl

/-- **At ℕ, `conBelow C₀ C₁ (k)` says exactly "`⊥` has no `TAct`-proof of length `≤ j`, for every `j` with
`j + C₀ + C₁·size k ≤ k`"** — TRUE at every `k` (`TAct` is sound); the question is only whether `TAct` PROVES it
within about `k`. -/
theorem conBelow_true_iff (C₀ C₁ k : ℕ) :
    ℕ↓[LAct] ⊧ (conBelow C₀ C₁ ⇜ ![Semiterm.lMap emb (binNumeralMeta k)] : Sentence LAct) ↔
      ∀ j : ℕ, j + C₀ + C₁ * Nat.size k ≤ k → ¬ LenBox TAct j (⌜(⊥ : Sentence LAct)⌝ : ℕ) := by
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
  rw [hv, eval_conBelow_iff stdReadingNat stdReadingNat_lMap_emb C₀ C₁ k]
  simp only [natCast_nat, ← size_eq_length, instB_botF_nat, lenBoxUnbounded_iff_lenBox]
  constructor
  · intro h j hj
    exact h j (le_def.mpr (Nat.eq_or_lt_of_le hj))
  · intro h j hj
    refine h j ?_
    rcases le_def.mp hj with e | e
    · exact Nat.le_of_eq e
    · exact Nat.le_of_lt e

/-- **The reduction for a hinge**: if the hinge code at `k` is the `binNumeral k`-instance of `r` and `r` has the
semantic property of `tact_imp_conBelow`, then for all large `k` a proof of the hinge within `k` yields a proof of
`Con_TAct(k − C₀ − C₁·size k)` within `k + D₀ + D₁·size k + D₂·(size k)²`. -/
theorem hinge_con_reduction (r : Semisentence LAct 1) (θs : List (Semisentence LAct 1)) (kHat : ℕ)
    (hstd : ∀ (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (x : M), (kHat : M) ≤ x →
      Semiformula.Eval (s := stdReadingV M) ![x] Empty.elim r →
      ∃ θ ∈ θs, ¬ LenBox TAct x (instB (⌜θ⌝ : M) x))
    (hswap : ∀ (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (x : M), (kHat : M) ≤ x →
      Semiformula.Eval (s := swappedReading M) ![x] Empty.elim r →
      ∃ θ ∈ θs, ¬ LenBox TAct x (instB (⌜θ⌝ : M) x))
    (H : ℕ → ℕ) (hH : ∀ k, H k = (⌜(r ⇜ ![Semiterm.lMap emb (binNumeralMeta k)] : Sentence LAct)⌝ : ℕ)) :
    ∃ k₀ C₀ C₁ D₀ D₁ D₂ : ℕ, ∀ k : ℕ, k₀ < k → LenBox TAct k (H k) →
      LenBox TAct (k + D₀ + D₁ * Nat.size k + D₂ * Nat.size k * Nat.size k)
        (⌜(conBelow C₀ C₁ ⇜ ![Semiterm.lMap emb (binNumeralMeta k)] : Sentence LAct)⌝ : ℕ) := by
  obtain ⟨k₀, C₀, C₁, hq⟩ := tact_imp_conBelow r θs kHat hstd hswap
  obtain ⟨D₀, D₁, D₂, h⟩ := con_reduction_of r hq
  exact ⟨k₀, C₀, C₁, D₀, D₁, D₂, fun k hk hA ↦ h k k hk (by rw [← hH]; exact hA)⟩

end generic

/-! ### 4. CIMCIC against a CLOSED opponent whose cooperation needs CIMCIC's else-play against `.bot DefectBot` -/

section cimcicClosed

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- CIMCIC's hinge against the closed program `P`, as a fixed formula: "if I cooperate with `P`, `P` cooperates with
me" (`P` by its generic closed description, `describes_closed`). -/
noncomputable def rCcl (P : ℕ) : Semisentence LAct 1 :=
  qCG (cl (canonicalMeta P)) (revalueUMeta P) (revalueWMeta P)

theorem guardCode_rCcl (P : ℕ) (k : V) :
    guardCode (⌜templateC⌝ : V) (CimcicV k) ((P : ℕ) : V) = instB (⌜rCcl P⌝ : V) k :=
  guardCode_CimcicV_eq_instB k _ _ _
    (by have := (describes_closed P).hX V k; rwa [descVal_closed] at this)
    (by have := (describes_closed P).hU V k; rwa [descVal_closed] at this)
    (by have := (describes_closed P).hW V k; rwa [descVal_closed] at this)

/-- The τ-twin: the transposed searcher's guard against the transposed `P`. -/
theorem guardCode_rCcl_swap (P : ℕ) (k : V) :
    guardCode (⌜templateCT⌝ : V) (CimcicTV k) (transposeCode ((P : ℕ) : V)) =
      instB (⌜Semiformula.lMap swap (rCcl P)⌝ : V) k := by
  unfold rCcl
  rw [lMap_swap_qCG]
  exact guardCode_CimcicTV_eq_instB k _ _ _
    (by have := (describes_closed P).hX V k; rwa [descVal_closed] at this)
    (by have := (describes_closed P).hU V k; rwa [descVal_closed] at this)
    (by have := (describes_closed P).hW V k; rwa [descVal_closed] at this)

/-- CIMCIC's guard against `.bot DefectBot`: "if I cooperate with `.bot DefectBot`, it cooperates with me" — the
bounded Gödel sentence of CIMCIC (`TAct`-equivalent to its own unprovability within `k`). -/
noncomputable def qCiB1 : Semisentence LAct 1 := qCG (cl TB0) (cterm Act.D) (cterm Act.C)

theorem guardCode_CiB1 (k : V) :
    guardCode (⌜templateC⌝ : V) (CimcicV k) (pBot (pConst 1)) = instB (⌜qCiB1⌝ : V) k :=
  guardCode_CimcicV_eq_instB k (cl TB0) _ _ (hX_bot_one k) hU_D_bot_one hW_C_bot_one

theorem guardCode_CiB1_swap (k : V) :
    guardCode (⌜templateCT⌝ : V) (CimcicTV k) (pBot (pConst 0)) = instB (⌜Semiformula.lMap swap qCiB1⌝ : V) k := by
  have h := guardCode_CimcicTV_eq_instB k (cl TB0) (cterm Act.D) (cterm Act.C) (hX_bot_one k) hU_D_bot_one hW_C_bot_one
  rw [transposeCode_pBot, transposeCode_pConst_one] at h
  unfold qCiB1
  rw [lMap_swap_qCG]
  exact h

end cimcicClosed

/-- **The semantic property, standard reading**: if `P`'s cooperation with a program means that program did NOT
cooperate with `.bot DefectBot` (`hprobe`: DBot, EBot), then CIMCIC's hinge against `P`, when TRUE, forbids that
both the hinge and CIMCIC's guard against `.bot DefectBot` be found. -/
theorem rCcl_refutes_std (P : ℕ) (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (x : M)
    (hprobe : ∀ n : M, EvalGraph n ((P : ℕ) : M) (CimcicV x) ((P : ℕ) : M) 0 →
      ∃ m r : M, EvalGraph m (CimcicV x) (pBot (pConst 1)) (CimcicV x) r ∧ r ≠ 0)
    (hr : Semiformula.Eval (s := stdReadingV M) ![x] Empty.elim (rCcl P)) :
    ∃ θ ∈ [rCcl P, qCiB1, Semiformula.lMap swap (rCcl P), Semiformula.lMap swap qCiB1],
      ¬ LenBox TAct x (instB (⌜θ⌝ : M) x) := by
  have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
  by_cases ha : LenBox TAct x (instB (⌜rCcl P⌝ : M) x)
  · by_cases hb : LenBox TAct x (instB (⌜qCiB1⌝ : M) x)
    · exfalso
      rw [← guardCode_rCcl] at ha
      rw [← guardCode_CiB1] at hb
      rw [rCcl, eval_qCG_iff_V x _ _ _ (descVal_closed P x)] at hr
      obtain ⟨n, hn⟩ := hr ⟨_, cimcic_search_V x _ ha⟩
      obtain ⟨m, r, hm, hr0⟩ := hprobe n hn
      exact hr0 (EvalGraph.unique_V' m 2 _ _ _ _ _ hm (cimcic_search_V x _ hb))
    · exact ⟨qCiB1, by simp, hb⟩
  · exact ⟨rCcl P, by simp, ha⟩

/-- **The semantic property, swapped reading**: the transposed statement, on the transposed searcher and the
transposed `P`. -/
theorem rCcl_refutes_swap (P : ℕ) (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (x : M)
    (hprobe : ∀ n : M, EvalGraph n (transposeCode ((P : ℕ) : M)) (CimcicTV x) (transposeCode ((P : ℕ) : M)) 1 →
      ∃ m r : M, EvalGraph m (CimcicTV x) (pBot (pConst 0)) (CimcicTV x) r ∧ r ≠ 1)
    (hr : Semiformula.Eval (s := swappedReading M) ![x] Empty.elim (rCcl P)) :
    ∃ θ ∈ [rCcl P, qCiB1, Semiformula.lMap swap (rCcl P), Semiformula.lMap swap qCiB1],
      ¬ LenBox TAct x (instB (⌜θ⌝ : M) x) := by
  have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
  by_cases ha : LenBox TAct x (instB (⌜Semiformula.lMap swap (rCcl P)⌝ : M) x)
  · by_cases hb : LenBox TAct x (instB (⌜Semiformula.lMap swap qCiB1⌝ : M) x)
    · exfalso
      rw [← guardCode_rCcl_swap] at ha
      rw [← guardCode_CiB1_swap] at hb
      rw [rCcl, eval_qCG_swap_iff_V, eval_qCTG_iff_V x _ _ _ (descVal_closed_T P x)] at hr
      obtain ⟨n, hn⟩ := hr ⟨_, cimcicT_search_V x _ ha⟩
      obtain ⟨m, r, hm, hr1⟩ := hprobe n hn
      exact hr1 (EvalGraph.unique_V' m 2 _ _ _ _ _ hm (cimcicT_search_V x _ hb))
    · exact ⟨Semiformula.lMap swap qCiB1, by simp, hb⟩
  · exact ⟨Semiformula.lMap swap (rCcl P), by simp, ha⟩

/-- CIMCIC's hinge against a closed engine bot, as consulted by the evaluator, is the `binNumeral k`-instance of
`rCcl`. -/
theorem hinge_CIMCIC_closed_eq (P : PD.Prog) (k : ℕ) :
    guardCodeB (templateCode phiC) (progCode (CIMCIC k)) (progCode P) k =
      (⌜(rCcl (progCode P) ⇜ ![Semiterm.lMap emb (binNumeralMeta k)] : Sentence LAct)⌝ : ℕ) := by
  rw [hingeB phiC, progCode_CIMCIC, templateCode_eq_quote_template phiC rfl]
  have e := guardCode_rCcl (V := ℕ) (progCode P) k
  rw [natCast_nat] at e
  have hq : instB (⌜rCcl (progCode P)⌝ : ℕ) k =
      ⌜(rCcl (progCode P) ⇜ ![Semiterm.lMap emb (binNumeralMeta k)] : Sentence LAct)⌝ := by
    have := quote_instB (V := ℕ) (rCcl (progCode P)) k
    rwa [natCast_nat] at this
  rw [← hq]
  exact e

/-! #### CIMCIC × DBot and CIMCIC × EBot -/

/-- **THE REDUCTION, CIMCIC × DBot.** For all large `k`: if the hinge — CIMCIC's guard "if I cooperate with DBot,
DBot cooperates with me" — is `TAct`-provable within `k`, then `TAct` proves within
`k + D₀ + D₁·size k + D₂·(size k)²` that `⊥` has no proof of length `≤ k − C₀ − C₁·size k`. -/
theorem hinge_reduces_to_bounded_consistency_CIMCIC_vs_DBot :
    ∃ k₀ C₀ C₁ D₀ D₁ D₂ : ℕ, ∀ k : ℕ, k₀ < k →
      LenBox TAct k (guardCodeB (templateCode phiC) (progCode (CIMCIC k)) (progCode DBot) k) →
      LenBox TAct (k + D₀ + D₁ * Nat.size k + D₂ * Nat.size k * Nat.size k)
        (⌜(conBelow C₀ C₁ ⇜ ![Semiterm.lMap emb (binNumeralMeta k)] : Sentence LAct)⌝ : ℕ) :=
  hinge_con_reduction (rCcl (progCode DBot)) _ 0
    (fun M _ _ x _ hr ↦ rCcl_refutes_std (progCode DBot) M x
      (fun n hn ↦ by
        have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
        rw [cast_DBot] at hn; exact probe_of_dbot_C_V hn) hr)
    (fun M _ _ x _ hr ↦ rCcl_refutes_swap (progCode DBot) M x
      (fun n hn ↦ by
        have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
        rw [cast_DBot, transposeCode_DBotV] at hn; exact probe_of_dbotT_D_V hn) hr)
    _ (hinge_CIMCIC_closed_eq DBot)

/-- **THE REDUCTION, CIMCIC × EBot** (EBot's cooperation passes its first rung, DBot's probe). -/
theorem hinge_reduces_to_bounded_consistency_CIMCIC_vs_EBot :
    ∃ k₀ C₀ C₁ D₀ D₁ D₂ : ℕ, ∀ k : ℕ, k₀ < k →
      LenBox TAct k (guardCodeB (templateCode phiC) (progCode (CIMCIC k)) (progCode EBot) k) →
      LenBox TAct (k + D₀ + D₁ * Nat.size k + D₂ * Nat.size k * Nat.size k)
        (⌜(conBelow C₀ C₁ ⇜ ![Semiterm.lMap emb (binNumeralMeta k)] : Sentence LAct)⌝ : ℕ) :=
  hinge_con_reduction (rCcl (progCode EBot)) _ 0
    (fun M _ _ x _ hr ↦ rCcl_refutes_std (progCode EBot) M x
      (fun n hn ↦ by
        have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
        rw [cast_EBot] at hn; exact probe_of_ebot_C_V hn) hr)
    (fun M _ _ x _ hr ↦ rCcl_refutes_swap (progCode EBot) M x
      (fun n hn ↦ by
        have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
        rw [cast_EBot, transposeCode_EBotV] at hn; exact probe_of_ebotT_D_V hn) hr)
    _ (hinge_CIMCIC_closed_eq EBot)

/-! ### 5. CIMCIC against a DESCRIBED searcher whose cooperation is its own else-play -/

section cimcicDescribed

/-- CIMCIC as a described player: the engine searcher `SV (gI .C) 0` (`progCode_CIMCIC_SV`). -/
noncomputable abbrev dpCi : DP := DP.ofSV (gI .C) 0 (Or.inl rfl)

/-- CIMCIC's hinge against a described opponent, as a fixed formula: "if I cooperate with it, it cooperates with
me". -/
noncomputable def rCi (opp : DP) : Semisentence LAct 1 := qF (gI .C) dpCi opp

lemma lMap_swap_rCi (opp : DP) : Semiformula.lMap swap (rCi opp) = qF (gI .D) dpCi.tr opp.tr := by
  unfold rCi
  rw [lMap_swap_qF, lMap_swap_gI_C]

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

lemma dpCi_val (k : V) : dpCi.val k = SV (gI .C) 0 k := DP.ofSV_val _ _ _ k
lemma dpCi_tr_val (k : V) : dpCi.tr.val k = SV (gI .D) 1 k := by
  rw [DP.ofSV_tr_val, lMap_swap_gI_C]

/-- A play of a simple member that differs from its then-constant means its stored guard was NOT found. -/
theorem Tau.SM.not_found_of_play (s : Tau.SM) {x me opp r n : V} (h : EvalGraph n me opp (s.code x) r)
    (hr : r ≠ (s.a : V)) : ¬ LenBox TAct x (guardCodeB ((⌜s.g⌝ : ℕ) : V) me opp x) := by
  obtain ⟨n', rfl, _⟩ := EvalGraph.case_iff.mp h
  unfold Tau.SM.code at h
  rcases EvalGraph.search_iff.mp h with ⟨_, hp⟩ | ⟨hn, _⟩
  · obtain ⟨m, rfl, _⟩ := EvalGraph.case_iff.mp hp
    exact absurd (EvalGraph.const_iff.mp hp) hr
  · exact hn

end cimcicDescribed

/-- **The semantic property, standard reading**: if the opponent's cooperation with CIMCIC means that the
opponent's own guard `e` was not found (`hE`), then CIMCIC's hinge, when TRUE, forbids that both the hinge and `e`
be found. -/
theorem rCi_refutes_std (opp : DP) (e : Semisentence LAct 1) (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (x : M)
    (hE : (∃ n : M, EvalGraph n (opp.val x) (SV (gI .C) 0 x) (opp.val x) 0) →
      ¬ LenBox TAct x (instB (⌜e⌝ : M) x))
    (hr : Semiformula.Eval (s := stdReadingV M) ![x] Empty.elim (rCi opp)) :
    ∃ θ ∈ [rCi opp, e, Semiformula.lMap swap (rCi opp), Semiformula.lMap swap e],
      ¬ LenBox TAct x (instB (⌜θ⌝ : M) x) := by
  have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
  by_cases ha : LenBox TAct x (instB (⌜rCi opp⌝ : M) x)
  · refine ⟨e, by simp, hE ?_⟩
    have hC := SV_then_qF (gI .C) 0 dpCi opp x ha
    rw [dpCi_val] at hC
    have hr' := (eval_qF_impl .C dpCi opp x).mp hr
    rw [dpCi_val] at hr'
    obtain ⟨n, hn⟩ := hr' ⟨_, by simpa [actCode] using hC⟩
    exact ⟨n, by simpa [actCode] using hn⟩
  · exact ⟨rCi opp, by simp, ha⟩

/-- **The semantic property, swapped reading.** -/
theorem rCi_refutes_swap (opp : DP) (e : Semisentence LAct 1) (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (x : M)
    (hE : (∃ n : M, EvalGraph n (opp.tr.val x) (SV (gI .D) 1 x) (opp.tr.val x) 1) →
      ¬ LenBox TAct x (instB (⌜Semiformula.lMap swap e⌝ : M) x))
    (hr : Semiformula.Eval (s := swappedReading M) ![x] Empty.elim (rCi opp)) :
    ∃ θ ∈ [rCi opp, e, Semiformula.lMap swap (rCi opp), Semiformula.lMap swap e],
      ¬ LenBox TAct x (instB (⌜θ⌝ : M) x) := by
  have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
  by_cases ha : LenBox TAct x (instB (⌜Semiformula.lMap swap (rCi opp)⌝ : M) x)
  · refine ⟨Semiformula.lMap swap e, by simp, hE ?_⟩
    rw [lMap_swap_rCi] at ha
    have hD := SV_then_qF (gI .D) 1 dpCi.tr opp.tr x ha
    rw [dpCi_tr_val] at hD
    rw [eval_swappedReading, lMap_swap_rCi, ← stdReadingV_eq_stdReading] at hr
    have hr' := (eval_qF_impl .D dpCi.tr opp.tr x).mp hr
    rw [dpCi_tr_val] at hr'
    obtain ⟨n, hn⟩ := hr' ⟨_, by simpa [actCode] using hD⟩
    exact ⟨n, by simpa [actCode] using hn⟩
  · exact ⟨Semiformula.lMap swap (rCi opp), by simp, ha⟩

/-- CIMCIC's hinge against a described opponent, as consulted by the evaluator, is the `binNumeral k`-instance of
`rCi`, given the value of the description at ℕ. -/
theorem hinge_CIMCIC_described_eq (opp : DP) (P : ℕ → PD.Prog) (hP : ∀ k : ℕ, opp.val (V := ℕ) k = progCode (P k))
    (k : ℕ) :
    guardCodeB (templateCode phiC) (progCode (CIMCIC k)) (progCode (P k)) k =
      (⌜(rCi opp ⇜ ![Semiterm.lMap emb (binNumeralMeta k)] : Sentence LAct)⌝ : ℕ) := by
  rw [hingeB phiC, progCode_CIMCIC_SV, templateCode_eq_quote_template phiC rfl, ← hP k]
  have e := guardCode_qF (V := ℕ) (gI .C) dpCi opp k
  rw [dpCi_val] at e
  have hq : instB (⌜rCi opp⌝ : ℕ) k =
      ⌜(rCi opp ⇜ ![Semiterm.lMap emb (binNumeralMeta k)] : Sentence LAct)⌝ := by
    have := quote_instB (V := ℕ) (rCi opp) k
    rwa [natCast_nat] at this
  rw [← hq]
  exact e

/-! #### The opponent is a simple member with then-action `D` (the trolls) -/

/-- **CIMCIC against a simple member `s` with then-action `D`**: `s` cooperates only through its else-branch, so
CIMCIC's hinge reduces to bounded consistency. -/
theorem hinge_con_reduction_CIMCIC_vs_SM (s : Tau.SM) (hs : s.a = 1)
    (hg : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁], IsSemiformula LAct 7 ((⌜s.g⌝ : ℕ) : V))
    (hgT : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁],
      IsSemiformula LAct 7 ((⌜Semiformula.lMap swap s.g⌝ : ℕ) : V))
    (P : ℕ → PD.Prog) (hP : ∀ k : ℕ, s.code (V := ℕ) k = progCode (P k)) :
    ∃ k₀ C₀ C₁ D₀ D₁ D₂ : ℕ, ∀ k : ℕ, k₀ < k →
      LenBox TAct k (guardCodeB (templateCode phiC) (progCode (CIMCIC k)) (progCode (P k)) k) →
      LenBox TAct (k + D₀ + D₁ * Nat.size k + D₂ * Nat.size k * Nat.size k)
        (⌜(conBelow C₀ C₁ ⇜ ![Semiterm.lMap emb (binNumeralMeta k)] : Sentence LAct)⌝ : ℕ) := by
  refine hinge_con_reduction (rCi (DP.ofSM s)) _ 0
    (fun M _ _ x _ hr ↦ rCi_refutes_std (DP.ofSM s) (qF13 s.g (DP.ofSM s) dpCi) M x ?_ hr)
    (fun M _ _ x _ hr ↦ rCi_refutes_swap (DP.ofSM s) (qF13 s.g (DP.ofSM s) dpCi) M x ?_ hr)
    _ (hinge_CIMCIC_described_eq (DP.ofSM s) P (fun k ↦ by rw [DP.ofSM_val]; exact hP k))
  · have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    rintro ⟨n, hn⟩
    rw [← guardCodeB_qF13 s.g (hg M) (DP.ofSM s) dpCi x, DP.ofSM_val, dpCi_val]
    rw [DP.ofSM_val] at hn
    exact Tau.SM.not_found_of_play s hn (by rw [hs]; simp)
  · have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    rintro ⟨n, hn⟩
    rw [lMap_swap_qF13, ← guardCodeB_qF13 (Semiformula.lMap swap s.g) (hgT M) (DP.ofSM s).tr dpCi.tr x,
      DP.ofSM_tr_val, dpCi_tr_val]
    rw [DP.ofSM_tr_val] at hn
    exact Tau.SM.not_found_of_play s.tr hn (by rw [Tau.SM.tr_a, hs]; simp)

/-- **THE REDUCTION, CIMCIC × CupodTrollBot.** -/
theorem hinge_reduces_to_bounded_consistency_CIMCIC_vs_CupodTrollBot :
    ∃ k₀ C₀ C₁ D₀ D₁ D₂ : ℕ, ∀ k : ℕ, k₀ < k →
      LenBox TAct k (guardCodeB (templateCode phiC) (progCode (CIMCIC k)) (progCode (CupodTrollBot k)) k) →
      LenBox TAct (k + D₀ + D₁ * Nat.size k + D₂ * Nat.size k * Nat.size k)
        (⌜(conBelow C₀ C₁ ⇜ ![Semiterm.lMap emb (binNumeralMeta k)] : Sentence LAct)⌝ : ℕ) :=
  hinge_con_reduction_CIMCIC_vs_SM (sTc .D) rfl isSemiformula7_gEq_D
    (fun V _ _ ↦ by
      rw [show (sTc .D).g = gEq (gP .D) (actCode .D) from rfl, lMap_swap_gEq _ _ (Tau.actCode_zero_or_one .D),
        lMap_swap_gP_D]
      exact isSemiformula7_gEq_C V)
    CupodTrollBot (fun k ↦ (progCode_CupodTrollBot_sT k).symm)

/-- **THE REDUCTION, CIMCIC × DupocTrollBot** (the `S'`-only floor `dich_DupocTrollBot_vs_CIMCIC`). -/
theorem hinge_reduces_to_bounded_consistency_CIMCIC_vs_DupocTrollBot :
    ∃ k₀ C₀ C₁ D₀ D₁ D₂ : ℕ, ∀ k : ℕ, k₀ < k →
      LenBox TAct k (guardCodeB (templateCode phiC) (progCode (CIMCIC k)) (progCode (DupocTrollBot k)) k) →
      LenBox TAct (k + D₀ + D₁ * Nat.size k + D₂ * Nat.size k * Nat.size k)
        (⌜(conBelow C₀ C₁ ⇜ ![Semiterm.lMap emb (binNumeralMeta k)] : Sentence LAct)⌝ : ℕ) :=
  hinge_con_reduction_CIMCIC_vs_SM sTd rfl isSemiformula7_gEq_C
    (fun V _ _ ↦ by
      rw [show sTd.g = gEq (gP .C) (actCode .C) from rfl, lMap_swap_gEq _ _ (Tau.actCode_zero_or_one .C),
        lMap_swap_gP_C]
      exact isSemiformula7_gEq_D V)
    DupocTrollBot (fun k ↦ (progCode_DupocTrollBot_sT k).symm)

/-! #### The opponent is `CupodBot` (the outer hinge of the nested floor) -/

/-- **THE REDUCTION, the OUTER hinge of CIMCIC × CupodBot**: Cupod cooperates only through its else-branch (its
guard "CIMCIC plays D against me" not found). -/
theorem hinge_reduces_to_bounded_consistency_CIMCIC_vs_CupodBot :
    ∃ k₀ C₀ C₁ D₀ D₁ D₂ : ℕ, ∀ k : ℕ, k₀ < k →
      LenBox TAct k (guardCodeB (templateCode phiC) (progCode (CIMCIC k)) (progCode (CupodBot k)) k) →
      LenBox TAct (k + D₀ + D₁ * Nat.size k + D₂ * Nat.size k * Nat.size k)
        (⌜(conBelow C₀ C₁ ⇜ ![Semiterm.lMap emb (binNumeralMeta k)] : Sentence LAct)⌝ : ℕ) := by
  refine hinge_con_reduction (rCi dpCu) _ 0
    (fun M _ _ x _ hr ↦ rCi_refutes_std dpCu (qF (gP .D) dpCu dpCi) M x ?_ hr)
    (fun M _ _ x _ hr ↦ rCi_refutes_swap dpCu (qF (gP .D) dpCu dpCi) M x ?_ hr)
    _ (hinge_CIMCIC_described_eq dpCu CupodBot (fun k ↦ by rw [dpCu_val, progCode_CupodBot_SV]; rfl))
  · have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    rintro ⟨n, hn⟩
    rw [← guardCode_qF, dpCu_val, dpCi_val]
    rw [dpCu_val] at hn
    exact not_found_of_SV_play hn (by simp [actCode])
  · have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    rintro ⟨n, hn⟩
    rw [lMap_swap_qF, lMap_swap_gP_D, ← guardCode_qF, dpCu_tr_val, dpCi_tr_val]
    rw [dpCu_tr_val] at hn
    exact not_found_of_SV_play hn (by simp [actCode])

/-! ### 6. Dupoc × DBot and Dupoc × EBot through the generic lemma (a check against the specific reductions) -/

/-- **Dupoc × DBot, literal form**: the hinge within `k` ⇒ `Con_TAct(k − C₀ − C₁·size k)` within
`k + D₀ + D₁·size k + D₂·(size k)²` (compare `hinge_reduces_to_bounded_consistency_DupocBot_vs_DBot`, on `σ_k`). -/
theorem hinge_reduces_to_literal_consistency_DupocBot_vs_DBot :
    ∃ k₀ C₀ C₁ D₀ D₁ D₂ : ℕ, ∀ k : ℕ, k₀ < k →
      LenBox TAct k (guardCodeB (templateCode phiDu) (progCode (DupocBot k)) (progCode DBot) k) →
      LenBox TAct (k + D₀ + D₁ * Nat.size k + D₂ * Nat.size k * Nat.size k)
        (⌜(conBelow C₀ C₁ ⇜ ![Semiterm.lMap emb (binNumeralMeta k)] : Sentence LAct)⌝ : ℕ) :=
  hinge_con_reduction rDB [qDuB1, Semiformula.lMap swap qDuB1] 0
    (fun M _ _ x _ hr ↦ by
      have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
      rw [rDB, eval_qT_plays_opp_self .C _ _ _ _ _ _ x (desc_SV gDu 0 (Or.inl rfl) x)
        (descVal_closed (progCode DBot) x), actCode_C_cast, cast_DBot] at hr
      obtain ⟨n, hn⟩ := hr
      obtain ⟨m, r, hm, hr0⟩ := probe_of_dbot_C_V hn
      refine ⟨qDuB1, by simp, ?_⟩
      rw [← guardCode_DuB1]
      exact not_found_of_SV_play hm (by simpa using hr0))
    (fun M _ _ x _ hr ↦ by
      have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
      rw [rDB, eval_qT_swap, lMap_swap_gDu, eval_qT_plays_opp_self .D _ _ _ _ _ _ x (descT_SV gDu 0 (Or.inl rfl) x)
        (descVal_closed_T (progCode DBot) x), actCode_D_cast, cast_DBot, transposeCode_DBotV, lMap_swap_gDu] at hr
      obtain ⟨n, hn⟩ := hr
      obtain ⟨m, r, hm, hr1⟩ := probe_of_dbotT_D_V hn
      refine ⟨Semiformula.lMap swap qDuB1, by simp, ?_⟩
      rw [← guardCode_DuB1_swap]
      exact not_found_of_SV_play hm (by simpa using hr1))
    _ hinge_DupocBot_vs_DBot_eq

/-- **Dupoc × EBot, literal form.** -/
theorem hinge_reduces_to_literal_consistency_DupocBot_vs_EBot :
    ∃ k₀ C₀ C₁ D₀ D₁ D₂ : ℕ, ∀ k : ℕ, k₀ < k →
      LenBox TAct k (guardCodeB (templateCode phiDu) (progCode (DupocBot k)) (progCode EBot) k) →
      LenBox TAct (k + D₀ + D₁ * Nat.size k + D₂ * Nat.size k * Nat.size k)
        (⌜(conBelow C₀ C₁ ⇜ ![Semiterm.lMap emb (binNumeralMeta k)] : Sentence LAct)⌝ : ℕ) :=
  hinge_con_reduction rEB [qDuB1, Semiformula.lMap swap qDuB1] 0
    (fun M _ _ x _ hr ↦ by
      have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
      rw [rEB, eval_qT_plays_opp_self .C _ _ _ _ _ _ x (desc_SV gDu 0 (Or.inl rfl) x)
        (descVal_closed (progCode EBot) x), actCode_C_cast, cast_EBot] at hr
      obtain ⟨n, hn⟩ := hr
      obtain ⟨m, r, hm, hr0⟩ := probe_of_ebot_C_V hn
      refine ⟨qDuB1, by simp, ?_⟩
      rw [← guardCode_DuB1]
      exact not_found_of_SV_play hm (by simpa using hr0))
    (fun M _ _ x _ hr ↦ by
      have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
      rw [rEB, eval_qT_swap, lMap_swap_gDu, eval_qT_plays_opp_self .D _ _ _ _ _ _ x (descT_SV gDu 0 (Or.inl rfl) x)
        (descVal_closed_T (progCode EBot) x), actCode_D_cast, cast_EBot, transposeCode_EBotV, lMap_swap_gDu] at hr
      obtain ⟨n, hn⟩ := hr
      obtain ⟨m, r, hm, hr1⟩ := probe_of_ebotT_D_V hn
      refine ⟨Semiformula.lMap swap qDuB1, by simp, ?_⟩
      rw [← guardCode_DuB1_swap]
      exact not_found_of_SV_play hm (by simpa using hr1))
    _ hinge_DupocBot_vs_EBot_eq

end ArithS
