import ArithS.DerivationLength
import ArithS.ProperV

/-!
# ArithS.Necessitation.NodeSize — every node's sizes are charged in its own `dlen`

`dlen d = Σ_{nodes} (1 + setLen (sequent at the node)) + Σ_{exsIntro nodes} termLen (witness)`
(`DerivationLength.lean`). The verification recursion of `DESIGN_fragments.md` §9 needs, at every
node `d` of an internal derivation, that the quantities its prologue is linear in — the node's
sequent length, its principal formulas, the `exs` witness, the children's lengths — are all
`≤ dlen d`, so that the per-node bounds of `Prologue.lean` §18 sum to a bound in `dlen ρ`.

Contents (all for `Derivation T d`, any `L`, any `T.Δ₁`):

* §1 the inversions `Derivation.<tag>_inv` (the node's side conditions and the children's
  `DerivationOf`, from `Derivation.case_iff` + code injectivity);
* §2 the exact node laws `dlen_<tag>` (`DlenGraph.<tag>_iff` read through `dlen_eq_of_graph`);
* §3 the bounds: `one_le_dlen`, `setLen_fstIdx_le_dlen`, `length_setLen_fstIdx_le`,
  `formulaLen_le_dlen_of_mem`, the children `dlen_<child>_succ_le_<tag>`, the principal formulas
  (`formulaLen_p_le_dlen_andIntro`, …, `termLen_le_dlen_exsIntro`).

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

lemma Derivation.axL_inv {s p : V} (h : Derivation T (axL s p)) : p ∈ s ∧ neg L p ∈ s := by
  have := Derivation.case_iff.mp h
  simpa using this.2

lemma Derivation.verumIntro_inv {s : V} (h : Derivation T (verumIntro s)) : (^⊤ : V) ∈ s := by
  have := Derivation.case_iff.mp h
  simpa using this.2

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

lemma Derivation.axm_inv {s p : V} (h : Derivation T (axm s p)) : p ∈ s ∧ p ∈ T.Δ₁Class := by
  have := Derivation.case_iff.mp h
  simpa using this.2

end inversion

/-! ## 2. The exact node laws of `dlen` -/

section nodeLaws

lemma dlen_axL {s p : V} (h : Derivation T (axL s p)) : dlen T (axL s p) = setLen L s + 1 :=
  dlen_eq_of_graph h (DlenGraph.axL_iff.mpr rfl)

lemma dlen_verumIntro {s : V} (h : Derivation T (verumIntro s)) : dlen T (verumIntro s) = setLen L s + 1 :=
  dlen_eq_of_graph h (DlenGraph.verumIntro_iff.mpr rfl)

lemma dlen_axm {s p : V} (h : Derivation T (axm s p)) : dlen T (axm s p) = setLen L s + 1 :=
  dlen_eq_of_graph h (DlenGraph.axm_iff.mpr rfl)

lemma dlen_andIntro {s p q dp dq : V} (h : Derivation T (andIntro s p q dp dq)) :
    dlen T (andIntro s p q dp dq) = setLen L s + dlen T dp + dlen T dq + 1 :=
  dlen_eq_of_graph h (DlenGraph.andIntro_iff.mpr
    ⟨_, _, dlen_graph (Derivation.andIntro_inv h).2.1.2, dlen_graph (Derivation.andIntro_inv h).2.2.2, rfl⟩)

lemma dlen_orIntro {s p q d : V} (h : Derivation T (orIntro s p q d)) :
    dlen T (orIntro s p q d) = setLen L s + dlen T d + 1 :=
  dlen_eq_of_graph h (DlenGraph.orIntro_iff.mpr ⟨_, dlen_graph (Derivation.orIntro_inv h).2.2, rfl⟩)

lemma dlen_allIntro {s p d : V} (h : Derivation T (allIntro s p d)) :
    dlen T (allIntro s p d) = setLen L s + dlen T d + 1 :=
  dlen_eq_of_graph h (DlenGraph.allIntro_iff.mpr ⟨_, dlen_graph (Derivation.allIntro_inv h).2.2, rfl⟩)

lemma dlen_exsIntro {s p t d : V} (h : Derivation T (exsIntro s p t d)) :
    dlen T (exsIntro s p t d) = setLen L s + termLen L t + dlen T d + 1 :=
  dlen_eq_of_graph h (DlenGraph.exsIntro_iff.mpr ⟨_, dlen_graph (Derivation.exsIntro_inv h).2.2.2, rfl⟩)

lemma dlen_wkRule {s d : V} (h : Derivation T (wkRule s d)) :
    dlen T (wkRule s d) = setLen L s + dlen T d + 1 :=
  dlen_eq_of_graph h (DlenGraph.wkRule_iff.mpr ⟨_, dlen_graph (Derivation.wkRule_inv h).2, rfl⟩)

lemma dlen_shiftRule {s d : V} (h : Derivation T (shiftRule s d)) :
    dlen T (shiftRule s d) = setLen L s + dlen T d + 1 :=
  dlen_eq_of_graph h (DlenGraph.shiftRule_iff.mpr ⟨_, dlen_graph (Derivation.shiftRule_inv h).2, rfl⟩)

lemma dlen_cutRule {s p d₁ d₂ : V} (h : Derivation T (cutRule s p d₁ d₂)) :
    dlen T (cutRule s p d₁ d₂) = setLen L s + dlen T d₁ + dlen T d₂ + 1 :=
  dlen_eq_of_graph h (DlenGraph.cutRule_iff.mpr
    ⟨_, _, dlen_graph (Derivation.cutRule_inv h).1.2, dlen_graph (Derivation.cutRule_inv h).2.2, rfl⟩)

end nodeLaws

/-! ## 3. The bounds -/

section bounds

private lemma le_a2 (a b c : V) : a ≤ a + b + c := le_trans le_self_add le_self_add
private lemma le_a3 (a b c d : V) : a ≤ a + b + c + d := le_trans (le_a2 a b c) le_self_add

/-- Every internal derivation has positive length (the root node is charged). -/
theorem one_le_dlen {d : V} (h : Derivation T d) : 1 ≤ dlen T d := by
  have hg := dlen_graph h
  rw [DlenGraph.case_iff] at hg
  rcases hg with ⟨s, p, _, e⟩ | ⟨s, _, e⟩ | ⟨s, p, q, dp, dq, np, nq, _, _, _, e⟩ | ⟨s, p, q, d', n', _, _, e⟩ |
    ⟨s, p, d', n', _, _, e⟩ | ⟨s, p, t, d', n', _, _, e⟩ | ⟨s, d', n', _, _, e⟩ | ⟨s, d', n', _, _, e⟩ |
    ⟨s, p, d₁, d₂, n₁, n₂, _, _, _, e⟩ | ⟨s, p, _, e⟩ <;> rw [e] <;> exact le_add_self

/-- **The node's sequent is charged in its own length**: `setLen (fstIdx d) ≤ dlen d`. -/
theorem setLen_fstIdx_le_dlen {d : V} (h : Derivation T d) : setLen L (fstIdx d) ≤ dlen T d := by
  have hg := dlen_graph h
  rw [DlenGraph.case_iff] at hg
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

theorem length_setLen_fstIdx_le {d : V} (h : Derivation T d) : ‖setLen L (fstIdx d)‖ ≤ ‖dlen T d‖ :=
  length_monotone (setLen_fstIdx_le_dlen h)

/-- A member of the node's sequent is no longer than the derivation. -/
theorem formulaLen_le_dlen_of_mem {d p : V} (h : Derivation T d) (hp : p ∈ fstIdx d) :
    formulaLen L p ≤ dlen T d :=
  le_trans (formulaLen_le_setLen_of_mem hp) (setLen_fstIdx_le_dlen h)

/-! ### 3.1 The children -/

theorem dlen_dp_succ_le_andIntro {s p q dp dq : V} (h : Derivation T (andIntro s p q dp dq)) :
    dlen T dp + 1 ≤ dlen T (andIntro s p q dp dq) := by
  rw [dlen_andIntro h]; exact add_le_add (le_trans le_add_self le_self_add) le_rfl

theorem dlen_dq_succ_le_andIntro {s p q dp dq : V} (h : Derivation T (andIntro s p q dp dq)) :
    dlen T dq + 1 ≤ dlen T (andIntro s p q dp dq) := by
  rw [dlen_andIntro h]; exact add_le_add le_add_self le_rfl

theorem dlen_d_succ_le_orIntro {s p q d : V} (h : Derivation T (orIntro s p q d)) :
    dlen T d + 1 ≤ dlen T (orIntro s p q d) := by
  rw [dlen_orIntro h]; exact add_le_add le_add_self le_rfl

theorem dlen_d_succ_le_allIntro {s p d : V} (h : Derivation T (allIntro s p d)) :
    dlen T d + 1 ≤ dlen T (allIntro s p d) := by
  rw [dlen_allIntro h]; exact add_le_add le_add_self le_rfl

theorem dlen_d_succ_le_exsIntro {s p t d : V} (h : Derivation T (exsIntro s p t d)) :
    dlen T d + 1 ≤ dlen T (exsIntro s p t d) := by
  rw [dlen_exsIntro h]; exact add_le_add le_add_self le_rfl

theorem dlen_d_succ_le_wkRule {s d : V} (h : Derivation T (wkRule s d)) :
    dlen T d + 1 ≤ dlen T (wkRule s d) := by
  rw [dlen_wkRule h]; exact add_le_add le_add_self le_rfl

theorem dlen_d_succ_le_shiftRule {s d : V} (h : Derivation T (shiftRule s d)) :
    dlen T d + 1 ≤ dlen T (shiftRule s d) := by
  rw [dlen_shiftRule h]; exact add_le_add le_add_self le_rfl

theorem dlen_d₁_succ_le_cutRule {s p d₁ d₂ : V} (h : Derivation T (cutRule s p d₁ d₂)) :
    dlen T d₁ + 1 ≤ dlen T (cutRule s p d₁ d₂) := by
  rw [dlen_cutRule h]; exact add_le_add (le_trans le_add_self le_self_add) le_rfl

theorem dlen_d₂_succ_le_cutRule {s p d₁ d₂ : V} (h : Derivation T (cutRule s p d₁ d₂)) :
    dlen T d₂ + 1 ≤ dlen T (cutRule s p d₁ d₂) := by
  rw [dlen_cutRule h]; exact add_le_add le_add_self le_rfl

/-! ### 3.2 The principal formulas and the `exs` witness -/

/-- `p` and `neg p` at an `axL` leaf. -/
theorem formulaLen_p_le_dlen_axL {s p : V} (h : Derivation T (axL s p)) : formulaLen L p ≤ dlen T (axL s p) :=
  formulaLen_le_dlen_of_mem h (by rw [fstIdx_axL]; exact (Derivation.axL_inv h).1)

theorem formulaLen_negp_le_dlen_axL {s p : V} (h : Derivation T (axL s p)) :
    formulaLen L (neg L p) ≤ dlen T (axL s p) :=
  formulaLen_le_dlen_of_mem h (by rw [fstIdx_axL]; exact (Derivation.axL_inv h).2)

/-- The conjuncts of an `andIntro` node (members of the children's sequents). -/
theorem formulaLen_p_le_dlen_andIntro {s p q dp dq : V} (h : Derivation T (andIntro s p q dp dq)) :
    formulaLen L p ≤ dlen T (andIntro s p q dp dq) := by
  obtain ⟨_, ⟨hf, hd⟩, _⟩ := Derivation.andIntro_inv h
  refine le_trans (formulaLen_le_dlen_of_mem hd (by rw [hf]; simp)) (le_trans le_self_add (dlen_dp_succ_le_andIntro h))

theorem formulaLen_q_le_dlen_andIntro {s p q dp dq : V} (h : Derivation T (andIntro s p q dp dq)) :
    formulaLen L q ≤ dlen T (andIntro s p q dp dq) := by
  obtain ⟨_, _, ⟨hf, hd⟩⟩ := Derivation.andIntro_inv h
  refine le_trans (formulaLen_le_dlen_of_mem hd (by rw [hf]; simp)) (le_trans le_self_add (dlen_dq_succ_le_andIntro h))

theorem formulaLen_pq_le_dlen_andIntro {s p q dp dq : V} (h : Derivation T (andIntro s p q dp dq)) :
    formulaLen L (p ^⋏ q) ≤ dlen T (andIntro s p q dp dq) :=
  formulaLen_le_dlen_of_mem h (by rw [fstIdx_andIntro]; exact (Derivation.andIntro_inv h).1)

/-- The disjuncts of an `orIntro` node. -/
theorem formulaLen_p_le_dlen_orIntro {s p q d : V} (h : Derivation T (orIntro s p q d)) :
    formulaLen L p ≤ dlen T (orIntro s p q d) := by
  obtain ⟨_, hf, hd⟩ := Derivation.orIntro_inv h
  refine le_trans (formulaLen_le_dlen_of_mem hd (by rw [hf]; simp)) (le_trans le_self_add (dlen_d_succ_le_orIntro h))

theorem formulaLen_q_le_dlen_orIntro {s p q d : V} (h : Derivation T (orIntro s p q d)) :
    formulaLen L q ≤ dlen T (orIntro s p q d) := by
  obtain ⟨_, hf, hd⟩ := Derivation.orIntro_inv h
  refine le_trans (formulaLen_le_dlen_of_mem hd (by rw [hf]; simp)) (le_trans le_self_add (dlen_d_succ_le_orIntro h))

theorem formulaLen_pq_le_dlen_orIntro {s p q d : V} (h : Derivation T (orIntro s p q d)) :
    formulaLen L (p ^⋎ q) ≤ dlen T (orIntro s p q d) :=
  formulaLen_le_dlen_of_mem h (by rw [fstIdx_orIntro]; exact (Derivation.orIntro_inv h).1)

/-- The eigenformula `free p` of an `allIntro` node (a member of the child's sequent) and the member `∀p`. -/
theorem formulaLen_free_le_dlen_allIntro {s p d : V} (h : Derivation T (allIntro s p d)) :
    formulaLen L (free L p) ≤ dlen T (allIntro s p d) := by
  obtain ⟨_, hf, hd⟩ := Derivation.allIntro_inv h
  refine le_trans (formulaLen_le_dlen_of_mem hd (by rw [hf]; simp)) (le_trans le_self_add (dlen_d_succ_le_allIntro h))

theorem formulaLen_all_le_dlen_allIntro {s p d : V} (h : Derivation T (allIntro s p d)) :
    formulaLen L (^∀ p) ≤ dlen T (allIntro s p d) :=
  formulaLen_le_dlen_of_mem h (by rw [fstIdx_allIntro]; exact (Derivation.allIntro_inv h).1)

/-- The witness term of an `exsIntro` node is charged explicitly. -/
theorem termLen_le_dlen_exsIntro {s p t d : V} (h : Derivation T (exsIntro s p t d)) :
    termLen L t ≤ dlen T (exsIntro s p t d) := by
  rw [dlen_exsIntro h]; exact le_trans le_add_self (le_a2 _ _ _)

theorem formulaLen_substs1_le_dlen_exsIntro {s p t d : V} (h : Derivation T (exsIntro s p t d)) :
    formulaLen L (substs1 L t p) ≤ dlen T (exsIntro s p t d) := by
  obtain ⟨_, _, hf, hd⟩ := Derivation.exsIntro_inv h
  refine le_trans (formulaLen_le_dlen_of_mem hd (by rw [hf]; simp)) (le_trans le_self_add (dlen_d_succ_le_exsIntro h))

theorem formulaLen_exs_le_dlen_exsIntro {s p t d : V} (h : Derivation T (exsIntro s p t d)) :
    formulaLen L (^∃ p) ≤ dlen T (exsIntro s p t d) :=
  formulaLen_le_dlen_of_mem h (by rw [fstIdx_exsIntro]; exact (Derivation.exsIntro_inv h).1)

/-- The cut formula and its negation (members of the two children's sequents). -/
theorem formulaLen_p_le_dlen_cutRule {s p d₁ d₂ : V} (h : Derivation T (cutRule s p d₁ d₂)) :
    formulaLen L p ≤ dlen T (cutRule s p d₁ d₂) := by
  obtain ⟨⟨hf, hd⟩, _⟩ := Derivation.cutRule_inv h
  refine le_trans (formulaLen_le_dlen_of_mem hd (by rw [hf]; simp)) (le_trans le_self_add (dlen_d₁_succ_le_cutRule h))

theorem formulaLen_negp_le_dlen_cutRule {s p d₁ d₂ : V} (h : Derivation T (cutRule s p d₁ d₂)) :
    formulaLen L (neg L p) ≤ dlen T (cutRule s p d₁ d₂) := by
  obtain ⟨_, ⟨hf, hd⟩⟩ := Derivation.cutRule_inv h
  refine le_trans (formulaLen_le_dlen_of_mem hd (by rw [hf]; simp)) (le_trans le_self_add (dlen_d₂_succ_le_cutRule h))

/-- The axiom at an `axm` leaf. -/
theorem formulaLen_p_le_dlen_axm {s p : V} (h : Derivation T (axm s p)) : formulaLen L p ≤ dlen T (axm s p) :=
  formulaLen_le_dlen_of_mem h (by rw [fstIdx_axm]; exact (Derivation.axm_inv h).1)

/-! ### 3.3 The children's sequents are charged in the parent's length too -/

theorem setLen_child_le_dlen_andIntro_left {s p q dp dq : V} (h : Derivation T (andIntro s p q dp dq)) :
    setLen L (insert p s) ≤ dlen T (andIntro s p q dp dq) := by
  obtain ⟨_, ⟨hf, hd⟩, _⟩ := Derivation.andIntro_inv h
  rw [← hf]; exact le_trans (setLen_fstIdx_le_dlen hd) (le_trans le_self_add (dlen_dp_succ_le_andIntro h))

theorem setLen_child_le_dlen_andIntro_right {s p q dp dq : V} (h : Derivation T (andIntro s p q dp dq)) :
    setLen L (insert q s) ≤ dlen T (andIntro s p q dp dq) := by
  obtain ⟨_, _, ⟨hf, hd⟩⟩ := Derivation.andIntro_inv h
  rw [← hf]; exact le_trans (setLen_fstIdx_le_dlen hd) (le_trans le_self_add (dlen_dq_succ_le_andIntro h))

theorem setLen_child_le_dlen_orIntro {s p q d : V} (h : Derivation T (orIntro s p q d)) :
    setLen L (insert p (insert q s)) ≤ dlen T (orIntro s p q d) := by
  obtain ⟨_, hf, hd⟩ := Derivation.orIntro_inv h
  rw [← hf]; exact le_trans (setLen_fstIdx_le_dlen hd) (le_trans le_self_add (dlen_d_succ_le_orIntro h))

theorem setLen_child_le_dlen_allIntro {s p d : V} (h : Derivation T (allIntro s p d)) :
    setLen L (insert (free L p) (setShift L s)) ≤ dlen T (allIntro s p d) := by
  obtain ⟨_, hf, hd⟩ := Derivation.allIntro_inv h
  rw [← hf]; exact le_trans (setLen_fstIdx_le_dlen hd) (le_trans le_self_add (dlen_d_succ_le_allIntro h))

theorem setLen_child_le_dlen_exsIntro {s p t d : V} (h : Derivation T (exsIntro s p t d)) :
    setLen L (insert (substs1 L t p) s) ≤ dlen T (exsIntro s p t d) := by
  obtain ⟨_, _, hf, hd⟩ := Derivation.exsIntro_inv h
  rw [← hf]; exact le_trans (setLen_fstIdx_le_dlen hd) (le_trans le_self_add (dlen_d_succ_le_exsIntro h))

theorem setLen_child_le_dlen_wkRule {s d : V} (h : Derivation T (wkRule s d)) :
    setLen L (fstIdx d) ≤ dlen T (wkRule s d) :=
  le_trans (setLen_fstIdx_le_dlen (Derivation.wkRule_inv h).2) (le_trans le_self_add (dlen_d_succ_le_wkRule h))

theorem setLen_child_le_dlen_shiftRule {s d : V} (h : Derivation T (shiftRule s d)) :
    setLen L (fstIdx d) ≤ dlen T (shiftRule s d) :=
  le_trans (setLen_fstIdx_le_dlen (Derivation.shiftRule_inv h).2) (le_trans le_self_add (dlen_d_succ_le_shiftRule h))

theorem setLen_child_le_dlen_cutRule_left {s p d₁ d₂ : V} (h : Derivation T (cutRule s p d₁ d₂)) :
    setLen L (insert p s) ≤ dlen T (cutRule s p d₁ d₂) := by
  obtain ⟨⟨hf, hd⟩, _⟩ := Derivation.cutRule_inv h
  rw [← hf]; exact le_trans (setLen_fstIdx_le_dlen hd) (le_trans le_self_add (dlen_d₁_succ_le_cutRule h))

theorem setLen_child_le_dlen_cutRule_right {s p d₁ d₂ : V} (h : Derivation T (cutRule s p d₁ d₂)) :
    setLen L (insert (neg L p) s) ≤ dlen T (cutRule s p d₁ d₂) := by
  obtain ⟨_, ⟨hf, hd⟩⟩ := Derivation.cutRule_inv h
  rw [← hf]; exact le_trans (setLen_fstIdx_le_dlen hd) (le_trans le_self_add (dlen_d₂_succ_le_cutRule h))

end bounds

end ArithS
