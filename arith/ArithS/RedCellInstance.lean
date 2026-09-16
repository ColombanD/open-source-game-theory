import ArithS.RedCell
import PrisonersDilemma.Base.RedCellFramework

/-!
# ArithS.RedCellInstance — the red cell through the abstract framework, in PA-`S'`

The engine's `Base/RedCellFramework.lean` proves `(Dupoc, Cupod) = (D, C)` once, over a
hypothesis package (transposition is an involution, proofs transpose at the same length,
provable guards are true, the evaluator is a function). This file instantiates it with
the arithmetized system: sentences of `LAct`, `LenProvableV TAct k` on codes, the
language swap `lMap swap` (τ-closure of `TAct` at every proof length,
`lenProvable_fbound_swap_iff`), the evaluation graph `EvalGraph`, the two guard
sentences `guardSentenceA`, soundness `evalGraph_of_guard` and determinism
`EvalGraph.unique'`. `red_cell_via_framework` is then one application of the abstract
theorem, the same one `Theorems/DupocBot/RedCellInstance.lean` applies to `Pf`.
-/

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus
open LAct

/-- Dupoc's guard fires: a proof of `guardSentenceA 0 (Dupoc k) (Cupod k)` within `k`
makes Dupoc cooperate (fuel 2). -/
theorem dupoc_fires (k : ℕ)
    (h : LenProvableV TAct k (⌜guardSentenceA 0 (Dupoc k) (Cupod k)⌝ : ℕ)) :
    EvalGraph 2 (Dupoc k) (Cupod k) (Dupoc k) 0 := by
  rw [quote_guardSentenceA] at h
  show EvalGraph (1 + 1) (Dupoc k) (Cupod k) (pSearch k (⌜GtmplA 0⌝ : ℕ) (pConst 0) (pConst 1)) 0
  rw [EvalGraph.search_iff]
  exact Or.inl ⟨h, (EvalGraph.const_iff (n := 0)).mpr rfl⟩

/-- Dupoc's else-branch: no such proof makes Dupoc defect (fuel 2). -/
theorem dupoc_else (k : ℕ)
    (h : ¬LenProvableV TAct k (⌜guardSentenceA 0 (Dupoc k) (Cupod k)⌝ : ℕ)) :
    EvalGraph 2 (Dupoc k) (Cupod k) (Dupoc k) 1 := by
  rw [quote_guardSentenceA] at h
  show EvalGraph (1 + 1) (Dupoc k) (Cupod k) (pSearch k (⌜GtmplA 0⌝ : ℕ) (pConst 0) (pConst 1)) 1
  rw [EvalGraph.search_iff]
  exact Or.inr ⟨h, (EvalGraph.const_iff (n := 0)).mpr rfl⟩

/-- Cupod's guard fires: a proof of `guardSentenceA 1 (Cupod k) (Dupoc k)` within `k`
makes Cupod defect (fuel 2). -/
theorem cupod_fires (k : ℕ)
    (h : LenProvableV TAct k (⌜guardSentenceA 1 (Cupod k) (Dupoc k)⌝ : ℕ)) :
    EvalGraph 2 (Cupod k) (Dupoc k) (Cupod k) 1 := by
  rw [quote_guardSentenceA] at h
  show EvalGraph (1 + 1) (Cupod k) (Dupoc k) (pSearch k (⌜GtmplA 1⌝ : ℕ) (pConst 1) (pConst 0)) 1
  rw [EvalGraph.search_iff]
  exact Or.inl ⟨h, (EvalGraph.const_iff (n := 0)).mpr rfl⟩

/-- Cupod's else-branch: no such proof makes Cupod cooperate (fuel 2). -/
theorem cupod_else (k : ℕ)
    (h : ¬LenProvableV TAct k (⌜guardSentenceA 1 (Cupod k) (Dupoc k)⌝ : ℕ)) :
    EvalGraph 2 (Cupod k) (Dupoc k) (Cupod k) 0 := by
  rw [quote_guardSentenceA] at h
  show EvalGraph (1 + 1) (Cupod k) (Dupoc k) (pSearch k (⌜GtmplA 1⌝ : ℕ) (pConst 1) (pConst 0)) 0
  rw [EvalGraph.search_iff]
  exact Or.inr ⟨h, (EvalGraph.const_iff (n := 0)).mpr rfl⟩

/-- **The arithmetized instance** of the red-cell package: `LenProvableV TAct` over
`Sentence LAct` (on codes), transposed by `lMap swap`, played by `EvalGraph`. -/
noncomputable def arithRedCell : PD.RedCellFramework where
  Act := ℕ
  C := 0
  D := 1
  hCD := by decide
  Sent := Sentence LAct
  Prov := fun k φ => LenProvableV TAct k (⌜φ⌝ : ℕ)
  τ := Semiformula.lMap swap
  τ_invol := fun φ => lMap_swap_swap φ
  prov_swap := fun k φ h => by
    rw [lenProvableV_nat] at h ⊢
    exact (lenProvable_fbound_swap_iff k φ).mp h
  playA := fun k a => ∃ n, EvalGraph n (Dupoc k) (Cupod k) (Dupoc k) a
  playB := fun k b => ∃ n, EvalGraph n (Cupod k) (Dupoc k) (Cupod k) b
  ρ₁ := fun k => guardSentenceA 0 (Dupoc k) (Cupod k)
  ρ₂ := fun k => guardSentenceA 1 (Cupod k) (Dupoc k)
  mirror := fun k => by
    rw [lMap_swap_guardSentenceA, swapcode_Dupoc, swapcode_Cupod, swapAct_zero]
  fireA := fun k h => ⟨2, dupoc_fires k h⟩
  elseA := fun k h => ⟨2, dupoc_else k h⟩
  fireB := fun k h => ⟨2, cupod_fires k h⟩
  elseB := fun k h => ⟨2, cupod_else k h⟩
  sound₂ := fun k h => by
    rw [quote_guardSentenceA] at h
    exact evalGraph_of_guard h
  detA := fun _ _ _ ⟨_, hn⟩ ⟨_, hm⟩ => EvalGraph.unique' hn hm
  detB := fun _ _ _ ⟨_, hn⟩ ⟨_, hm⟩ => EvalGraph.unique' hn hm

/-- **The red cell in PA-`S'`, via the framework**: at every shared budget `k`, Dupoc
defects against Cupod and Cupod cooperates with Dupoc, at some fuel. -/
theorem red_cell_via_framework (k : ℕ) :
    (∃ n, EvalGraph n (Dupoc k) (Cupod k) (Dupoc k) 1) ∧
    (∃ n, EvalGraph n (Cupod k) (Dupoc k) (Cupod k) 0) :=
  arithRedCell.red_cell k

/-- The framework's negative half is `RedCell.lean`'s `hG`/`hG'`, on sentences. -/
example (k : ℕ) :
    ¬LenProvableV TAct k (⌜guardSentenceA 0 (Dupoc k) (Cupod k)⌝ : ℕ) ∧
    ¬LenProvableV TAct k (⌜guardSentenceA 1 (Cupod k) (Dupoc k)⌝ : ℕ) :=
  arithRedCell.guards_fail k

/-- Agreement with the direct proof `red_cell` (fuel-2 form): determinism identifies the
framework's witnesses with it. -/
example (k : ℕ) :
    ∀ n, 2 ≤ n → EvalGraph n (Dupoc k) (Cupod k) (Dupoc k) 1 ∧
      EvalGraph n (Cupod k) (Dupoc k) (Cupod k) 0 :=
  fun _ hn => ⟨EvalGraph.mono_le hn (red_cell k).1, EvalGraph.mono_le hn (red_cell k).2⟩

example (k : ℕ) {a b : ℕ}
    (ha : EvalGraph 2 (Dupoc k) (Cupod k) (Dupoc k) a) (hb : EvalGraph 2 (Cupod k) (Dupoc k) (Cupod k) b) :
    a = 1 ∧ b = 0 :=
  let ⟨⟨_, hA⟩, ⟨_, hB⟩⟩ := red_cell_via_framework k
  ⟨EvalGraph.unique' ha hA, EvalGraph.unique' hb hB⟩

end ArithS
