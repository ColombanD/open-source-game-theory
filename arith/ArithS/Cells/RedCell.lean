import ArithS.Agents.Template
import ArithS.Box.Cut

/-!
# ArithS.RedCell — `(Dupoc, Cupod) = (D, C)` in the arithmetized `S`

`Dupoc k` searches, within proof length `k` over `TAct`, for a proof that its opponent
cooperates with it, and cooperates iff it finds one. `Cupod k` is its transposition: it
searches for a proof that its opponent defects against it, and defects iff it finds one.
The two guard sentences are transpositions of each other (the swap equation), so by the
τ-closure of `TAct` at every length (`ArithS.Symmetry`) they are provable together or not
at all. Provable together is impossible: by soundness both facts would be TRUE — Cupod
cooperates with Dupoc and Dupoc defects against Cupod — but Dupoc, finding its proof,
COOPERATES, contradicting determinism. So neither is provable, Dupoc defects and Cupod
cooperates: the outcome is `(D, C)`.

No census, no rule inspection: soundness, symmetry and determinism only, exactly as in the
engine's `outcome_DupocBot_vs_CupodBot`.
-/

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus
open LAct

/-! ### The two bots -/

/-- `Dupoc k`: cooperate iff a proof of length `≤ k` shows the opponent cooperates with me
(the template instance `guardTemplate 0`, "opp plays `C` against me"). -/
noncomputable def Dupoc (k : ℕ) : ℕ := pSearch k (⌜guardTemplate 0⌝ : ℕ) (pConst 0) (pConst 1)

/-- `Cupod k`: defect iff a proof of length `≤ k` shows the opponent defects against me
(the template instance `guardTemplate 1`, "opp plays `D` against me"). -/
noncomputable def Cupod (k : ℕ) : ℕ := pSearch k (⌜guardTemplate 1⌝ : ℕ) (pConst 1) (pConst 0)

lemma swapAction_zero : swapAction (0 : ℕ) = 1 := by simp [revalueAction]
lemma swapAction_one : swapAction (1 : ℕ) = 0 := by simp [revalueAction]

/-- `Cupod` is the transposition of `Dupoc`: τ swaps the constants in the stored template
(`revalueTemplate_quote_GtmplA`) and the two action values. -/
theorem transposeCode_Dupoc (k : ℕ) : transposeCode (Dupoc k) = Cupod k := by
  unfold Dupoc Cupod transposeCode
  rw [revalue_search, revalue_const, revalue_const, revalueTemplate_quote_GtmplA, swapAction_zero]
  simp [revalueAction]

theorem transposeCode_Cupod (k : ℕ) : transposeCode (Cupod k) = Dupoc k := by
  rw [← transposeCode_Dupoc, transposeCode_transposeCode]

/-! ### `ℕ` is a model of `TAct` -/

lemma models_constNe : ℕ↓[LAct] ⊧ constNe := by
  rw [models_iff]
  unfold constNe Semiformula.Realize
  simp [Semiformula.eval_nrel, cterm]
  change ¬((0 : ℕ) = 1)
  decide

lemma models_constNe' : ℕ↓[LAct] ⊧ constNe' := by
  rw [models_iff]
  unfold constNe' Semiformula.Realize
  simp [Semiformula.eval_nrel, cterm]
  change ¬((1 : ℕ) = 0)
  decide

instance models_TAct : ℕ↓[LAct] ⊧* TAct := by
  rw [models_theory_iff]
  intro φ hφ
  rcases hφ with rfl | rfl | rfl | rfl | ⟨σ, hσ, rfl⟩
  · exact models_actionAxiom
  · exact models_actionAxiom'
  · exact models_constNe
  · exact models_constNe'
  · rw [models_lMap_emb]
    exact Theory.models ℕ 𝗣𝗔 hσ

/-! ### From the guard predicate to the evaluator -/

/-- The internal guard predicate at a meta budget is `LenBoxNat codeBound`. -/
lemma lenBox_nat (k φ : ℕ) :
    LenBox TAct k φ ↔ LenBoxNat (codeBound : ℕ → ℕ) k TAct φ := by
  have := lenBox_numeral (V := ℕ) TAct k φ
  rwa [Nat.numeral_eq] at this

/-- Bounded D2 in rule form for the object-variable predicate `LenBox` at `ℕ`
(`ArithS.Cut.lenBoxNat_mp` through `lenBox_nat`). -/
theorem lenBox_mp_nat {k₁ k₂ : ℕ} {φ ψ : Sentence LAct}
    (h₁ : LenBox TAct k₁ (⌜φ 🡒 ψ⌝ : ℕ)) (h₂ : LenBox TAct k₂ (⌜φ⌝ : ℕ)) :
    LenBox TAct (k₁ + k₂ + 10 * (formulaLenMeta (φ : Proposition LAct) + formulaLenMeta (ψ : Proposition LAct)) + 9)
      (⌜ψ⌝ : ℕ) := by
  rw [lenBox_nat] at h₁ h₂ ⊢
  exact lenBoxNat_mp h₁ h₂

/-- **Soundness of the guard**: if the guard is found, it is true. -/
theorem evalGraph_of_guard {k me opp a : ℕ}
    (h : LenBox TAct k (guardCode (⌜guardTemplate a⌝ : ℕ) me opp)) :
    ∃ n, EvalGraph n opp me opp a := by
  rw [← quote_guardSentence, lenBox_nat] at h
  have hp : TAct ⊢ guardSentence a me opp := provable_iff_provable.mp h.provable
  exact (models_guardSentence_iff a me opp).mp (models_of_provable models_TAct hp)

/-- **Symmetry of the guards**: Dupoc's guard against Cupod is found iff Cupod's guard against
Dupoc is. -/
theorem guard_Dupoc_iff_guard_Cupod (k : ℕ) :
    LenBox TAct k (guardCode (⌜guardTemplate 0⌝ : ℕ) (Dupoc k) (Cupod k)) ↔
    LenBox TAct k (guardCode (⌜guardTemplate 1⌝ : ℕ) (Cupod k) (Dupoc k)) := by
  rw [← quote_guardSentence, ← quote_guardSentence, lenBox_nat, lenBox_nat,
    lenBoxNat_swap_iff, lMap_swap_guardSentence, transposeCode_Dupoc, transposeCode_Cupod, swapAction_zero]

/-! ### The theorem -/

/-- **The red cell**: `Dupoc k` defects against `Cupod k` and `Cupod k` cooperates with
`Dupoc k`, at every shared budget `k` (fuel `2` suffices). -/
theorem red_cell (k : ℕ) :
    EvalGraph 2 (Dupoc k) (Cupod k) (Dupoc k) 1 ∧ EvalGraph 2 (Cupod k) (Dupoc k) (Cupod k) 0 := by
  have hG : ¬LenBox TAct k (guardCode (⌜guardTemplate 0⌝ : ℕ) (Dupoc k) (Cupod k)) := by
    intro hD
    have hC := (guard_Dupoc_iff_guard_Cupod k).mp hD
    -- Cupod's guard is true: Dupoc defects against Cupod.
    obtain ⟨n, hn⟩ := evalGraph_of_guard hC
    -- But Dupoc, finding its proof, cooperates.
    have hcoop : EvalGraph 2 (Dupoc k) (Cupod k) (Dupoc k) 0 := by
      show EvalGraph (1 + 1) (Dupoc k) (Cupod k) (pSearch k (⌜guardTemplate 0⌝ : ℕ) (pConst 0) (pConst 1)) 0
      rw [EvalGraph.search_iff₆ (isSemiformula_quote₆ (guardTemplate 0))]
      exact Or.inl ⟨hD, (EvalGraph.const_iff (n := 0)).mpr rfl⟩
    exact absurd (EvalGraph.unique' hn hcoop) (by decide)
  have hG' : ¬LenBox TAct k (guardCode (⌜guardTemplate 1⌝ : ℕ) (Cupod k) (Dupoc k)) :=
    fun h ↦ hG ((guard_Dupoc_iff_guard_Cupod k).mpr h)
  constructor
  · show EvalGraph (1 + 1) (Dupoc k) (Cupod k) (pSearch k (⌜guardTemplate 0⌝ : ℕ) (pConst 0) (pConst 1)) 1
    rw [EvalGraph.search_iff₆ (isSemiformula_quote₆ (guardTemplate 0))]
    exact Or.inr ⟨hG, (EvalGraph.const_iff (n := 0)).mpr rfl⟩
  · show EvalGraph (1 + 1) (Cupod k) (Dupoc k) (pSearch k (⌜guardTemplate 1⌝ : ℕ) (pConst 1) (pConst 0)) 0
    rw [EvalGraph.search_iff₆ (isSemiformula_quote₆ (guardTemplate 1))]
    exact Or.inr ⟨hG', (EvalGraph.const_iff (n := 0)).mpr rfl⟩

/-- The outcome is the same at every fuel `≥ 2`, and no other outcome exists at any fuel. -/
theorem red_cell_unique (k n : ℕ) {a b : ℕ}
    (ha : EvalGraph n (Dupoc k) (Cupod k) (Dupoc k) a) (hb : EvalGraph n (Cupod k) (Dupoc k) (Cupod k) b) :
    a = 1 ∧ b = 0 :=
  ⟨EvalGraph.unique' ha (red_cell k).1, EvalGraph.unique' hb (red_cell k).2⟩

end ArithS
