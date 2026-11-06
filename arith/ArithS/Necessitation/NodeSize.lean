import ArithS.Length.DerivationLength
import ArithS.Box.ProperBound

/-!
# ArithS.Necessitation.NodeSize — every node's sizes are charged in its own `proofLen`

`proofLen d = Σ_{nodes} (1 + sequentLen (sequent at the node)) + Σ_{exsIntro nodes} termLen (witness)`
(`DerivationLength.lean`). The verification recursion of `DESIGN_fragments.md` §9 needs, at every
node `d` of an internal derivation, that the quantities its prologue is linear in — the node's
sequent length, its principal formulas, the `exs` witness, the children's lengths — are all
`≤ proofLen d`, so that the per-node bounds of `Prologue.lean` §18 sum to a bound in `proofLen ρ`.

Contents (all for `Derivation T d`, any `L`, any `T.Δ₁`):

* §1 the inversions `Derivation.<tag>_inv` (the node's side conditions and the children's
  `DerivationOf`, from `Derivation.case_iff` + code injectivity);
* §2 the exact node laws `proofLen_<tag>` (`ProofLenGraph.<tag>_iff` read through `proofLen_eq_of_graph`);
* §3 the bounds: `one_le_proofLen`, `sequentLen_fstIdx_le_proofLen`, `length_sequentLen_fstIdx_le`,
  `formulaLen_le_proofLen_of_mem`, the children `proofLen_<child>_succ_le_<tag>`, the principal formulas
  (`formulaLen_p_le_proofLen_andIntro`, …, `termLen_le_proofLen_exsIntro`).

Everything is stated for the code `d` with `Derivation T d` as the hypothesis (the Δ₁ predicate
`derivation T` is its definition); `fstIdx d` is the node's sequent.
-/

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {L : Language} [L.Encodable] [L.LORDefinable]
variable {T : Theory L} [T.Δ₁]

/-! ## 1. Inversions of `Derivation` at each node code -/

section inversion

attribute [local simp] axL verumIntro andIntro orIntro allIntro exsIntro wkRule shiftRule cutRule axm

lemma Derivation.andIntro_inv {s p q dp dq : V} (h : Derivation T (andIntro s p q dp dq)) :
    p ^⋏ q ∈ s ∧ DerivationOf T dp (insert p s) ∧ DerivationOf T dq (insert q s) := by
  have := Derivation.case_iff.mp h
  simpa using this.2

lemma Derivation.orIntro_inv {s p q d : V} (h : Derivation T (orIntro s p q d)) :
    p ^⋎ q ∈ s ∧ DerivationOf T d (insert p (insert q s)) := by
  have := Derivation.case_iff.mp h
  simpa using this.2

lemma Derivation.allIntro_inv {s p d : V} (h : Derivation T (allIntro s p d)) :
    (^∀ p) ∈ s ∧ DerivationOf T d (insert (free L p) (setShift L s)) := by
  have := Derivation.case_iff.mp h
  simpa using this.2

lemma Derivation.exsIntro_inv {s p t d : V} (h : Derivation T (exsIntro s p t d)) :
    (^∃ p) ∈ s ∧ IsTerm L t ∧ DerivationOf T d (insert (substs1 L t p) s) := by
  have := Derivation.case_iff.mp h
  simpa using this.2

lemma Derivation.wkRule_inv {s d : V} (h : Derivation T (wkRule s d)) : fstIdx d ⊆ s ∧ Derivation T d := by
  have := Derivation.case_iff.mp h
  simpa using this.2

lemma Derivation.shiftRule_inv {s d : V} (h : Derivation T (shiftRule s d)) :
    s = setShift L (fstIdx d) ∧ Derivation T d := by
  have := Derivation.case_iff.mp h
  simpa using this.2

lemma Derivation.cutRule_inv {s p d₁ d₂ : V} (h : Derivation T (cutRule s p d₁ d₂)) :
    DerivationOf T d₁ (insert p s) ∧ DerivationOf T d₂ (insert (neg L p) s) := by
  have := Derivation.case_iff.mp h
  simpa using this.2

end inversion

/-! ## 2. The exact node laws of `proofLen` -/

section nodeLaws

lemma proofLen_axL {s p : V} (h : Derivation T (axL s p)) : proofLen T (axL s p) = sequentLen L s + 1 :=
  proofLen_eq_of_graph h (ProofLenGraph.axL_iff.mpr rfl)

lemma proofLen_verumIntro {s : V} (h : Derivation T (verumIntro s)) : proofLen T (verumIntro s) = sequentLen L s + 1 :=
  proofLen_eq_of_graph h (ProofLenGraph.verumIntro_iff.mpr rfl)

lemma proofLen_axm {s p : V} (h : Derivation T (axm s p)) : proofLen T (axm s p) = sequentLen L s + 1 :=
  proofLen_eq_of_graph h (ProofLenGraph.axm_iff.mpr rfl)

lemma proofLen_andIntro {s p q dp dq : V} (h : Derivation T (andIntro s p q dp dq)) :
    proofLen T (andIntro s p q dp dq) = sequentLen L s + proofLen T dp + proofLen T dq + 1 :=
  proofLen_eq_of_graph h (ProofLenGraph.andIntro_iff.mpr
    ⟨_, _, proofLen_graph (Derivation.andIntro_inv h).2.1.2, proofLen_graph (Derivation.andIntro_inv h).2.2.2, rfl⟩)

lemma proofLen_orIntro {s p q d : V} (h : Derivation T (orIntro s p q d)) :
    proofLen T (orIntro s p q d) = sequentLen L s + proofLen T d + 1 :=
  proofLen_eq_of_graph h (ProofLenGraph.orIntro_iff.mpr ⟨_, proofLen_graph (Derivation.orIntro_inv h).2.2, rfl⟩)

lemma proofLen_allIntro {s p d : V} (h : Derivation T (allIntro s p d)) :
    proofLen T (allIntro s p d) = sequentLen L s + proofLen T d + 1 :=
  proofLen_eq_of_graph h (ProofLenGraph.allIntro_iff.mpr ⟨_, proofLen_graph (Derivation.allIntro_inv h).2.2, rfl⟩)

lemma proofLen_exsIntro {s p t d : V} (h : Derivation T (exsIntro s p t d)) :
    proofLen T (exsIntro s p t d) = sequentLen L s + termLen L t + proofLen T d + 1 :=
  proofLen_eq_of_graph h (ProofLenGraph.exsIntro_iff.mpr ⟨_, proofLen_graph (Derivation.exsIntro_inv h).2.2.2, rfl⟩)

lemma proofLen_wkRule {s d : V} (h : Derivation T (wkRule s d)) :
    proofLen T (wkRule s d) = sequentLen L s + proofLen T d + 1 :=
  proofLen_eq_of_graph h (ProofLenGraph.wkRule_iff.mpr ⟨_, proofLen_graph (Derivation.wkRule_inv h).2, rfl⟩)

lemma proofLen_shiftRule {s d : V} (h : Derivation T (shiftRule s d)) :
    proofLen T (shiftRule s d) = sequentLen L s + proofLen T d + 1 :=
  proofLen_eq_of_graph h (ProofLenGraph.shiftRule_iff.mpr ⟨_, proofLen_graph (Derivation.shiftRule_inv h).2, rfl⟩)

lemma proofLen_cutRule {s p d₁ d₂ : V} (h : Derivation T (cutRule s p d₁ d₂)) :
    proofLen T (cutRule s p d₁ d₂) = sequentLen L s + proofLen T d₁ + proofLen T d₂ + 1 :=
  proofLen_eq_of_graph h (ProofLenGraph.cutRule_iff.mpr
    ⟨_, _, proofLen_graph (Derivation.cutRule_inv h).1.2, proofLen_graph (Derivation.cutRule_inv h).2.2, rfl⟩)

end nodeLaws

/-! ## 3. The bounds -/

section bounds

private lemma le_a2 (a b c : V) : a ≤ a + b + c := le_trans le_self_add le_self_add
private lemma le_a3 (a b c d : V) : a ≤ a + b + c + d := le_trans (le_a2 a b c) le_self_add

/-- Every internal derivation has positive length (the root node is charged). -/
theorem one_le_proofLen {d : V} (h : Derivation T d) : 1 ≤ proofLen T d := by
  have hg := proofLen_graph h
  rw [ProofLenGraph.case_iff] at hg
  rcases hg with ⟨s, p, _, e⟩ | ⟨s, _, e⟩ | ⟨s, p, q, dp, dq, np, nq, _, _, _, e⟩ | ⟨s, p, q, d', n', _, _, e⟩ |
    ⟨s, p, d', n', _, _, e⟩ | ⟨s, p, t, d', n', _, _, e⟩ | ⟨s, d', n', _, _, e⟩ | ⟨s, d', n', _, _, e⟩ |
    ⟨s, p, d₁, d₂, n₁, n₂, _, _, _, e⟩ | ⟨s, p, _, e⟩ <;> rw [e] <;> exact le_add_self

/-- **The node's sequent is charged in its own length**: `sequentLen (fstIdx d) ≤ proofLen d`. -/
theorem sequentLen_fstIdx_le_proofLen {d : V} (h : Derivation T d) : sequentLen L (fstIdx d) ≤ proofLen T d := by
  have hg := proofLen_graph h
  rw [ProofLenGraph.case_iff] at hg
  rcases hg with ⟨s, p, rfl, e⟩ | ⟨s, rfl, e⟩ | ⟨s, p, q, dp, dq, np, nq, _, _, rfl, e⟩ | ⟨s, p, q, d', n', _, rfl, e⟩ |
    ⟨s, p, d', n', _, rfl, e⟩ | ⟨s, p, t, d', n', _, rfl, e⟩ | ⟨s, d', n', _, rfl, e⟩ | ⟨s, d', n', _, rfl, e⟩ |
    ⟨s, p, d₁, d₂, n₁, n₂, _, _, rfl, e⟩ | ⟨s, p, rfl, e⟩ <;> rw [e] <;> simp only [fstIdx_axL, fstIdx_verumIntro,
    fstIdx_andIntro, fstIdx_orIntro, fstIdx_allIntro, fstIdx_exsIntro, fstIdx_wkRule, fstIdx_shiftRule,
    fstIdx_cutRule, fstIdx_axm]
  · exact le_self_add
  · exact le_self_add
  · exact le_a3 _ _ _ _
  · exact le_a2 _ _ _
  · exact le_a2 _ _ _
  · exact le_a3 _ _ _ _
  · exact le_a2 _ _ _
  · exact le_a2 _ _ _
  · exact le_a3 _ _ _ _
  · exact le_self_add

/-- A member of the node's sequent is no longer than the derivation. -/
theorem formulaLen_le_proofLen_of_mem {d p : V} (h : Derivation T d) (hp : p ∈ fstIdx d) :
    formulaLen L p ≤ proofLen T d :=
  le_trans (formulaLen_le_sequentLen_of_mem hp) (sequentLen_fstIdx_le_proofLen h)

/-! ### 3.1 The children -/

theorem proofLen_dp_succ_le_andIntro {s p q dp dq : V} (h : Derivation T (andIntro s p q dp dq)) :
    proofLen T dp + 1 ≤ proofLen T (andIntro s p q dp dq) := by
  rw [proofLen_andIntro h]; exact add_le_add (le_trans le_add_self le_self_add) le_rfl

theorem proofLen_dq_succ_le_andIntro {s p q dp dq : V} (h : Derivation T (andIntro s p q dp dq)) :
    proofLen T dq + 1 ≤ proofLen T (andIntro s p q dp dq) := by
  rw [proofLen_andIntro h]; exact add_le_add le_add_self le_rfl

theorem proofLen_d_succ_le_orIntro {s p q d : V} (h : Derivation T (orIntro s p q d)) :
    proofLen T d + 1 ≤ proofLen T (orIntro s p q d) := by
  rw [proofLen_orIntro h]; exact add_le_add le_add_self le_rfl

theorem proofLen_d_succ_le_allIntro {s p d : V} (h : Derivation T (allIntro s p d)) :
    proofLen T d + 1 ≤ proofLen T (allIntro s p d) := by
  rw [proofLen_allIntro h]; exact add_le_add le_add_self le_rfl

theorem proofLen_d_succ_le_exsIntro {s p t d : V} (h : Derivation T (exsIntro s p t d)) :
    proofLen T d + 1 ≤ proofLen T (exsIntro s p t d) := by
  rw [proofLen_exsIntro h]; exact add_le_add le_add_self le_rfl

theorem proofLen_d_succ_le_wkRule {s d : V} (h : Derivation T (wkRule s d)) :
    proofLen T d + 1 ≤ proofLen T (wkRule s d) := by
  rw [proofLen_wkRule h]; exact add_le_add le_add_self le_rfl

theorem proofLen_d_succ_le_shiftRule {s d : V} (h : Derivation T (shiftRule s d)) :
    proofLen T d + 1 ≤ proofLen T (shiftRule s d) := by
  rw [proofLen_shiftRule h]; exact add_le_add le_add_self le_rfl

theorem proofLen_d₁_succ_le_cutRule {s p d₁ d₂ : V} (h : Derivation T (cutRule s p d₁ d₂)) :
    proofLen T d₁ + 1 ≤ proofLen T (cutRule s p d₁ d₂) := by
  rw [proofLen_cutRule h]; exact add_le_add (le_trans le_add_self le_self_add) le_rfl

theorem proofLen_d₂_succ_le_cutRule {s p d₁ d₂ : V} (h : Derivation T (cutRule s p d₁ d₂)) :
    proofLen T d₂ + 1 ≤ proofLen T (cutRule s p d₁ d₂) := by
  rw [proofLen_cutRule h]; exact add_le_add le_add_self le_rfl

/-! ### 3.2 The principal formulas and the `exs` witness -/

theorem formulaLen_q_le_proofLen_andIntro {s p q dp dq : V} (h : Derivation T (andIntro s p q dp dq)) :
    formulaLen L q ≤ proofLen T (andIntro s p q dp dq) := by
  obtain ⟨_, _, ⟨hf, hd⟩⟩ := Derivation.andIntro_inv h
  refine le_trans (formulaLen_le_proofLen_of_mem hd (by rw [hf]; simp)) (le_trans le_self_add (proofLen_dq_succ_le_andIntro h))

theorem formulaLen_all_le_proofLen_allIntro {s p d : V} (h : Derivation T (allIntro s p d)) :
    formulaLen L (^∀ p) ≤ proofLen T (allIntro s p d) :=
  formulaLen_le_proofLen_of_mem h (by rw [fstIdx_allIntro]; exact (Derivation.allIntro_inv h).1)

/-- The witness term of an `exsIntro` node is charged explicitly. -/
theorem termLen_le_proofLen_exsIntro {s p t d : V} (h : Derivation T (exsIntro s p t d)) :
    termLen L t ≤ proofLen T (exsIntro s p t d) := by
  rw [proofLen_exsIntro h]; exact le_trans le_add_self (le_a2 _ _ _)

theorem formulaLen_substs1_le_proofLen_exsIntro {s p t d : V} (h : Derivation T (exsIntro s p t d)) :
    formulaLen L (substs1 L t p) ≤ proofLen T (exsIntro s p t d) := by
  obtain ⟨_, _, hf, hd⟩ := Derivation.exsIntro_inv h
  refine le_trans (formulaLen_le_proofLen_of_mem hd (by rw [hf]; simp)) (le_trans le_self_add (proofLen_d_succ_le_exsIntro h))

/-! ### 3.3 The children's sequents are charged in the parent's length too -/

theorem sequentLen_child_le_proofLen_andIntro_left {s p q dp dq : V} (h : Derivation T (andIntro s p q dp dq)) :
    sequentLen L (insert p s) ≤ proofLen T (andIntro s p q dp dq) := by
  obtain ⟨_, ⟨hf, hd⟩, _⟩ := Derivation.andIntro_inv h
  rw [← hf]; exact le_trans (sequentLen_fstIdx_le_proofLen hd) (le_trans le_self_add (proofLen_dp_succ_le_andIntro h))

theorem sequentLen_child_le_proofLen_andIntro_right {s p q dp dq : V} (h : Derivation T (andIntro s p q dp dq)) :
    sequentLen L (insert q s) ≤ proofLen T (andIntro s p q dp dq) := by
  obtain ⟨_, _, ⟨hf, hd⟩⟩ := Derivation.andIntro_inv h
  rw [← hf]; exact le_trans (sequentLen_fstIdx_le_proofLen hd) (le_trans le_self_add (proofLen_dq_succ_le_andIntro h))

theorem sequentLen_child_le_proofLen_orIntro {s p q d : V} (h : Derivation T (orIntro s p q d)) :
    sequentLen L (insert p (insert q s)) ≤ proofLen T (orIntro s p q d) := by
  obtain ⟨_, hf, hd⟩ := Derivation.orIntro_inv h
  rw [← hf]; exact le_trans (sequentLen_fstIdx_le_proofLen hd) (le_trans le_self_add (proofLen_d_succ_le_orIntro h))

theorem sequentLen_child_le_proofLen_allIntro {s p d : V} (h : Derivation T (allIntro s p d)) :
    sequentLen L (insert (free L p) (setShift L s)) ≤ proofLen T (allIntro s p d) := by
  obtain ⟨_, hf, hd⟩ := Derivation.allIntro_inv h
  rw [← hf]; exact le_trans (sequentLen_fstIdx_le_proofLen hd) (le_trans le_self_add (proofLen_d_succ_le_allIntro h))

theorem sequentLen_child_le_proofLen_exsIntro {s p t d : V} (h : Derivation T (exsIntro s p t d)) :
    sequentLen L (insert (substs1 L t p) s) ≤ proofLen T (exsIntro s p t d) := by
  obtain ⟨_, _, hf, hd⟩ := Derivation.exsIntro_inv h
  rw [← hf]; exact le_trans (sequentLen_fstIdx_le_proofLen hd) (le_trans le_self_add (proofLen_d_succ_le_exsIntro h))

theorem sequentLen_child_le_proofLen_wkRule {s d : V} (h : Derivation T (wkRule s d)) :
    sequentLen L (fstIdx d) ≤ proofLen T (wkRule s d) :=
  le_trans (sequentLen_fstIdx_le_proofLen (Derivation.wkRule_inv h).2) (le_trans le_self_add (proofLen_d_succ_le_wkRule h))

theorem sequentLen_child_le_proofLen_shiftRule {s d : V} (h : Derivation T (shiftRule s d)) :
    sequentLen L (fstIdx d) ≤ proofLen T (shiftRule s d) :=
  le_trans (sequentLen_fstIdx_le_proofLen (Derivation.shiftRule_inv h).2) (le_trans le_self_add (proofLen_d_succ_le_shiftRule h))

theorem sequentLen_child_le_proofLen_cutRule_left {s p d₁ d₂ : V} (h : Derivation T (cutRule s p d₁ d₂)) :
    sequentLen L (insert p s) ≤ proofLen T (cutRule s p d₁ d₂) := by
  obtain ⟨⟨hf, hd⟩, _⟩ := Derivation.cutRule_inv h
  rw [← hf]; exact le_trans (sequentLen_fstIdx_le_proofLen hd) (le_trans le_self_add (proofLen_d₁_succ_le_cutRule h))

theorem sequentLen_child_le_proofLen_cutRule_right {s p d₁ d₂ : V} (h : Derivation T (cutRule s p d₁ d₂)) :
    sequentLen L (insert (neg L p) s) ≤ proofLen T (cutRule s p d₁ d₂) := by
  obtain ⟨_, ⟨hf, hd⟩⟩ := Derivation.cutRule_inv h
  rw [← hf]; exact le_trans (sequentLen_fstIdx_le_proofLen hd) (le_trans le_self_add (proofLen_d₂_succ_le_cutRule h))

end bounds

end ArithS
