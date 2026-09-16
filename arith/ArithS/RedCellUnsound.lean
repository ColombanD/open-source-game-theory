import ArithS.RedCell
import ArithS.Fit

/-!
# ArithS.RedCellUnsound — the red cell FLIPS when soundness is dropped

The "drop soundness" mutation of the red-cell audit
(`engine/PrisonersDilemma/Research/Notes/RED_CELL_AUDIT.md` §4; the paper note's
Proposition 6.1), executed as a POSITIVE theorem rather than as a scratch-copy compile
failure.

`ArithS.red_cell` says `Dupoc k` vs `Cupod k` is `(D, C) = (1, 0)` at every budget, in
PA-`S'`. Its proof uses soundness of the theory the searchers consult (`TAct`, `ℕ` is a
model), τ-symmetry and determinism — nothing else. The audit predicts that soundness is
load-bearing: make the theory INCONSISTENT and, for all large `k`, BOTH guards become
provable within budget (every sentence has a short proof from a contradiction), so both
searchers take their then-branch and the outcome flips to `(C, D) = (0, 1)`.

This file proves exactly that:

* `TBad := TAct + {c_C = c_D, c_D = c_C}` (`axEq`, `axEq'`; the swap of the axiom is added
  too, so the axiom set stays literally closed under `swap` like `TAct`'s —
  `lMap_swap_mem_TBad`). It is Δ₁-axiomatized by Foundation's `Theory.Δ₁.insert`.
* `exFalso φ : TBad ⟹₂ {φ}` — the three-node Tait derivation of ANY formula: `axm` on
  `c_C = c_D`, `axm` on `c_C ≠ c_D` (which IS `∼(c_C = c_D)`, `coe_axNe`), one `cut`. Its
  length is `≤ 3|φ| + 2|axEq| + 3` (`mlen_exFalso`); quoting it (`lenProvable_of_derivation`)
  gives `LenProvable fbound k TBad ⌜φ⌝` for every `k` at least that
  (`lenProvable_TBad_of_flen`), so `TBad` is inconsistent (`tbad_inconsistent`,
  `tbad_proves_bot`) and, more to the point, inconsistent AT SHORT LENGTH.
* `EvalGraphBad` — **a verbatim copy of `ArithS.Eval`'s `EvalGraph`** (the Σ₁ fixpoint on
  tuples, its blueprint, definability, the clause inversions of `ArithS.EvalN` and the
  determinism/monotonicity facts at `ℕ`) **with `TAct` replaced by `TBad` in the `search`
  clause and nowhere else.** The evaluator is not parametric in its theory: the theory is
  hardwired in `EvalFix.Phi` and in the blueprint's `!(lenProvableV TAct)` literal, and
  making it a parameter would touch every consumer (`RedCell`, `Template`, `Agent`,
  `Assembly/*`, `Necessitation/*`); the mutation protocol asks for a copy, so this is one —
  every `Bad`-suffixed name below is the same-named declaration of `Eval.lean`/`EvalN.lean`
  with the theory swapped. (The one hazard the notes record — a blanket `simp` over the
  multi-disjunct blueprint hangs — is avoided by copying the targeted `simp`/`simpa` calls
  exactly.)
* `guards_fit_bad`: the ex-falso proofs of BOTH guard sentences fit their budget for all
  large `k` — `guard_fits`'s argument (`exists_guard_const`, `exists_desc_const`,
  `exists_linear_size_le`) with the ex-falso constants folded in; so
  `guard_provable_bad`: `LenProvableV TBad k` of both guard codes.
* **`red_cell_flips_when_unsound`**: `∃ K, ∀ k ≥ K, Dupoc k plays 0 and Cupod k plays 1`
  under `EvalGraphBad` (fuel 2), by the then-branch of `search_iff`; `red_cell_flip` puts
  the sound and the unsound value side by side; `red_cell_flips_unique` says no other
  value exists at any fuel.

Read together with `red_cell`: the SAME two programs, the SAME evaluator clauses, the SAME
budget — only the theory consulted at the search node differs — and the cell is `(D, C)`
under the sound theory and `(C, D)` under the inconsistent one. Soundness cannot be dropped.
-/

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1
open LAct

/-! ### 1. The inconsistent theory `TBad` -/

/-- `c_C = c_D` — the contradiction of `axNe`, as the atomic equality. -/
def axEq : Sentence LAct := Semiformula.rel Language.Eq.eq ![cterm Act.C, cterm Act.D]

/-- `c_D = c_C` — its swap (added so the axiom set stays closed under the transposition). -/
def axEq' : Sentence LAct := Semiformula.rel Language.Eq.eq ![cterm Act.D, cterm Act.C]

/-- `TBad := TAct ∪ {c_C = c_D, c_D = c_C}`: `TAct` made inconsistent. -/
abbrev TBad : Theory LAct := insert axEq (insert axEq' TAct)

lemma axEq_mem_TBad : axEq ∈ TBad := Set.mem_insert _ _

lemma axEq'_mem_TBad : axEq' ∈ TBad := Set.mem_insert_of_mem _ (Set.mem_insert _ _)

lemma TAct_subset_TBad : TAct ⊆ TBad := fun _ h ↦
  Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ h)

lemma axNe_mem_TBad : axNe ∈ TBad := TAct_subset_TBad axNe_mem_TAct

lemma axNe'_mem_TBad : axNe' ∈ TBad := TAct_subset_TBad axNe'_mem_TAct

/-- Δ₁, by two `insert`s on top of `TAct`'s instance. -/
noncomputable instance : TBad.Δ₁ := inferInstance

/-- `c_C ≠ c_D` IS `∼(c_C = c_D)` (definitionally: `∼` swaps `rel`/`nrel`). -/
lemma neg_axEq : ∼axEq = axNe := rfl

lemma neg_axEq' : ∼axEq' = axNe' := rfl

/-- The same after the sentence-to-proposition coercion (`Rewriting.emb` is structural). -/
lemma coe_axNe : (axNe : Proposition LAct) = ∼(axEq : Proposition LAct) := rfl

lemma lMap_swap_axEq : Semiformula.lMap swap axEq = axEq' := by
  unfold axEq axEq'
  rw [Semiformula.lMap_rel]
  congr 1
  funext i; fin_cases i <;> simp [lMap_swap_cterm_C, lMap_swap_cterm_D]

lemma lMap_swap_axEq' : Semiformula.lMap swap axEq' = axEq := by
  unfold axEq axEq'
  rw [Semiformula.lMap_rel]
  congr 1
  funext i; fin_cases i <;> simp [lMap_swap_cterm_C, lMap_swap_cterm_D]

/-- The axiom set of `TBad` is literally closed under the transposition, like `TAct`'s. -/
theorem lMap_swap_mem_TBad {σ : Sentence LAct} (h : σ ∈ TBad) : Semiformula.lMap swap σ ∈ TBad := by
  rcases h with rfl | rfl | h
  · rw [lMap_swap_axEq]; exact axEq'_mem_TBad
  · rw [lMap_swap_axEq']; exact axEq_mem_TBad
  · exact TAct_subset_TBad (lMap_swap_mem_TAct h)

/-! ### 2. Short proofs from the contradiction -/

section exFalso

variable {L : Language} [L.DecidableEq] {T : Theory L}

lemma mlen_axm {Γ : Finset (Proposition L)} (σ : Sentence L) (hT : σ ∈ T)
    (hΓ : (σ : Proposition L) ∈ Γ) :
    mlen (Derivation2.axm (T := T) σ hT hΓ) = sqlen Γ + 1 := by simp [mlen]

end exFalso

/-- **Ex falso, as a three-node derivation**: `{φ}` from `axm` on `c_C = c_D` (sequent
`{c_C = c_D, φ}`), `axm` on `c_C ≠ c_D` (sequent `{∼(c_C = c_D), φ}`) and one `cut`. -/
noncomputable def exFalso (φ : Proposition LAct) : TBad ⟹₂ {φ} :=
  Derivation2.cut (Γ := {φ}) (φ := (axEq : Proposition LAct))
    (Derivation2.axm axEq axEq_mem_TBad (Finset.mem_insert_self _ _))
    (Derivation2.axm axNe axNe_mem_TBad (by rw [coe_axNe]; exact Finset.mem_insert_self _ _))

/-- **Its length**: `3|φ| + 2|c_C = c_D| + 3` — every node charges its whole sequent. -/
theorem mlen_exFalso (φ : Proposition LAct) :
    mlen (exFalso φ) ≤ 3 * flen φ + 2 * flen (axEq : Proposition LAct) + 3 := by
  unfold exFalso
  rw [mlen_cut, mlen_axm, mlen_axm]
  have h0 : sqlen ({φ} : Finset (Proposition LAct)) = flen φ := sqlen_singleton φ
  have h1 := sqlen_insert_le (axEq : Proposition LAct) {φ}
  have h2 := sqlen_insert_le (∼(axEq : Proposition LAct)) {φ}
  rw [flen_neg] at h2
  omega

/-- **Every sentence has a `TBad`-proof of length linear in its own**: the quoted ex-falso
derivation is a `LenProvable fbound k TBad` witness once `k ≥ 3|σ| + 2|axEq| + 3`. -/
theorem lenProvable_TBad_of_flen {σ : Sentence LAct} {k : ℕ}
    (h : 3 * flen (σ : Proposition LAct) + 2 * flen (axEq : Proposition LAct) + 3 ≤ k) :
    LenProvable (fbound : ℕ → ℕ) k TBad (⌜σ⌝ : ℕ) :=
  lenProvable_of_derivation smallCodes_LAct smallRelCodes_LAct (exFalso σ)
    (le_trans (mlen_exFalso _) h)

/-- The object-variable box at `ℕ` is `LenProvable fbound` (as `lenProvableV_nat` for `TAct`). -/
lemma lenProvableV_nat_TBad (k φ : ℕ) :
    LenProvableV TBad k φ ↔ LenProvable (fbound : ℕ → ℕ) k TBad φ := by
  have := lenProvableV_numeral (V := ℕ) TBad k φ
  rwa [Nat.numeral_eq] at this

/-- Every sentence is `LenProvableV TBad` at some budget. -/
theorem exists_lenProvableV_TBad (σ : Sentence LAct) : ∃ k : ℕ, LenProvableV TBad k (⌜σ⌝ : ℕ) :=
  ⟨3 * flen (σ : Proposition LAct) + 2 * flen (axEq : Proposition LAct) + 3,
    (lenProvableV_nat_TBad _ _).mpr (lenProvable_TBad_of_flen le_rfl)⟩

/-- `TBad` proves every sentence. -/
theorem tbad_proves (σ : Sentence LAct) : TBad ⊢ σ :=
  provable_iff_derivable2.mpr ⟨exFalso σ⟩

/-- **`TBad` is inconsistent** (for the record). -/
theorem tbad_inconsistent : Entailment.Inconsistent TBad := fun σ ↦ tbad_proves σ

theorem tbad_proves_bot : TBad ⊢ ⊥ := tbad_proves ⊥

/-! ### 3. The evaluator with the theory swapped: `EvalGraphBad`

Everything in this section is `ArithS.Eval` + `ArithS.EvalN` with `TAct ↦ TBad` (and a `Bad`
suffix on every name); see the header for why it is a copy and not a parameter. -/

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

namespace EvalFixBad

/-- The evaluation operator on tuples `⟪n, me, opp, p, a⟫`, consulting `TBad`. -/
def Phi (C : Set V) (pr : V) : Prop :=
  (∃ n me opp a, pr = ⟪n + 1, me, opp, pConst a, a⟫) ∨
  (∃ n me opp a, ⟪n, me, opp, me, a⟫ ∈ C ∧ pr = ⟪n + 1, me, opp, pSelf, a⟫) ∨
  (∃ n me opp a, ⟪n, me, opp, opp, a⟫ ∈ C ∧ pr = ⟪n + 1, me, opp, pOpp, a⟫) ∨
  (∃ n me opp p a, ⟪n, me, opp, p, a⟫ ∈ C ∧ pr = ⟪n + 1, me, opp, pBot p, a⟫) ∨
  (∃ n me opp p q a, ⟪n, psubst me opp p, psubst me opp q, psubst me opp p, a⟫ ∈ C ∧
    pr = ⟪n + 1, me, opp, pSim p q, a⟫) ∨
  (∃ n me opp b a' p q a r, ⟪n, me, opp, b, r⟫ ∈ C ∧
    ((r = a' ∧ ⟪n, me, opp, p, a⟫ ∈ C) ∨ (r ≠ a' ∧ ⟪n, me, opp, q, a⟫ ∈ C)) ∧
    pr = ⟪n + 1, me, opp, pIte b a' p q, a⟫) ∨
  (∃ n me opp k g p q a,
    ((LenProvableV TBad k (guardCode g me opp) ∧ ⟪n, me, opp, p, a⟫ ∈ C) ∨
      (¬LenProvableV TBad k (guardCode g me opp) ∧ ⟪n, me, opp, q, a⟫ ∈ C)) ∧
    pr = ⟪n + 1, me, opp, pSearch k g p q, a⟫)

noncomputable def blueprint : Fixpoint.Blueprint 0 := ⟨.mkDelta
  (.mkSigma “pr C.
    ∃ n <⁺ pr, ∃ me <⁺ pr, ∃ opp <⁺ pr, ∃ p <⁺ pr, ∃ a <⁺ pr, !pair₅Def pr (n + 1) me opp p a ∧
    ( !pConstGraph p a ∨
      (!pSelfGraph p ∧ ∃ t, !pair₅Def t n me opp me a ∧ t ∈ C) ∨
      (!pOppGraph p ∧ ∃ t, !pair₅Def t n me opp opp a ∧ t ∈ C) ∨
      (∃ p' < p, !pBotGraph p p' ∧ ∃ t, !pair₅Def t n me opp p' a ∧ t ∈ C) ∨
      (∃ p' < p, ∃ q < p, !pSimGraph p p' q ∧
        ∃ sp, !psubstDef sp me opp p' ∧ ∃ sq, !psubstDef sq me opp q ∧
          ∃ t, !pair₅Def t n sp sq sp a ∧ t ∈ C) ∨
      (∃ b < p, ∃ a' < p, ∃ p' < p, ∃ q < p, !pIteGraph p b a' p' q ∧
        ∃ r < pr + C + 1, (∃ t, !pair₅Def t n me opp b r ∧ t ∈ C) ∧
          ((r = a' ∧ ∃ t, !pair₅Def t n me opp p' a ∧ t ∈ C) ∨
           (r ≠ a' ∧ ∃ t, !pair₅Def t n me opp q a ∧ t ∈ C))) ∨
      (∃ k < p, ∃ g < p, ∃ p' < p, ∃ q < p, !pSearchGraph p k g p' q ∧
        ∃ gc, !guardCodeGraph gc g me opp ∧
          ((!(lenProvableV TBad).sigma k gc ∧ ∃ t, !pair₅Def t n me opp p' a ∧ t ∈ C) ∨
           (¬!(lenProvableV TBad).pi k gc ∧ ∃ t, !pair₅Def t n me opp q a ∧ t ∈ C))) )”)
  (.mkPi “pr C.
    ∃ n <⁺ pr, ∃ me <⁺ pr, ∃ opp <⁺ pr, ∃ p <⁺ pr, ∃ a <⁺ pr, !pair₅Def pr (n + 1) me opp p a ∧
    ( !pConstGraph p a ∨
      (!pSelfGraph p ∧ ∀ t, !pair₅Def t n me opp me a → t ∈ C) ∨
      (!pOppGraph p ∧ ∀ t, !pair₅Def t n me opp opp a → t ∈ C) ∨
      (∃ p' < p, !pBotGraph p p' ∧ ∀ t, !pair₅Def t n me opp p' a → t ∈ C) ∨
      (∃ p' < p, ∃ q < p, !pSimGraph p p' q ∧
        ∀ sp, !psubstDef sp me opp p' → ∀ sq, !psubstDef sq me opp q →
          ∀ t, !pair₅Def t n sp sq sp a → t ∈ C) ∨
      (∃ b < p, ∃ a' < p, ∃ p' < p, ∃ q < p, !pIteGraph p b a' p' q ∧
        ∃ r < pr + C + 1, (∀ t, !pair₅Def t n me opp b r → t ∈ C) ∧
          ((r = a' ∧ ∀ t, !pair₅Def t n me opp p' a → t ∈ C) ∨
           (r ≠ a' ∧ ∀ t, !pair₅Def t n me opp q a → t ∈ C))) ∨
      (∃ k < p, ∃ g < p, ∃ p' < p, ∃ q < p, !pSearchGraph p k g p' q ∧
        ∀ gc, !guardCodeGraph gc g me opp →
          ((!(lenProvableV TBad).pi k gc ∧ ∀ t, !pair₅Def t n me opp p' a → t ∈ C) ∨
           (¬!(lenProvableV TBad).sigma k gc ∧ ∀ t, !pair₅Def t n me opp q a → t ∈ C))) )”)⟩

/-- Every component of a tuple is below any set containing the tuple. -/
private lemma lt_of_tuple_mem {n me opp b r C : V} (h : ⟪n, me, opp, b, r⟫ ∈ C) : r < C :=
  lt_of_le_of_lt (le_trans (le_pair_right _ _) (le_trans (le_pair_right _ _)
    (le_trans (le_pair_right _ _) (le_pair_right _ _)))) (lt_of_mem h)

private lemma tuple_bounds (n me opp p a : V) :
    n ≤ ⟪n + 1, me, opp, p, a⟫ ∧ me ≤ ⟪n + 1, me, opp, p, a⟫ ∧ opp ≤ ⟪n + 1, me, opp, p, a⟫ ∧
    p ≤ ⟪n + 1, me, opp, p, a⟫ ∧ a ≤ ⟪n + 1, me, opp, p, a⟫ :=
  ⟨le_trans (le_of_lt (lt_add_one n)) (le_pair_left _ _),
   le_trans (le_pair_left _ _) (le_pair_right _ _),
   le_trans (le_trans (le_pair_left _ _) (le_pair_right _ _)) (le_pair_right _ _),
   le_trans (le_trans (le_trans (le_pair_left _ _) (le_pair_right _ _)) (le_pair_right _ _))
     (le_pair_right _ _),
   le_trans (le_trans (le_trans (le_pair_right _ _) (le_pair_right _ _)) (le_pair_right _ _))
     (le_pair_right _ _)⟩

private lemma phi_iff (C pr : V) :
    Phi {x | x ∈ C} pr ↔
    ∃ n ≤ pr, ∃ me ≤ pr, ∃ opp ≤ pr, ∃ p ≤ pr, ∃ a ≤ pr, pr = ⟪n + 1, me, opp, p, a⟫ ∧
    ( p = pConst a ∨
      (p = pSelf ∧ ⟪n, me, opp, me, a⟫ ∈ C) ∨
      (p = pOpp ∧ ⟪n, me, opp, opp, a⟫ ∈ C) ∨
      (∃ p' < p, p = pBot p' ∧ ⟪n, me, opp, p', a⟫ ∈ C) ∨
      (∃ p' < p, ∃ q < p, p = pSim p' q ∧
        ⟪n, psubst me opp p', psubst me opp q, psubst me opp p', a⟫ ∈ C) ∨
      (∃ b < p, ∃ a' < p, ∃ p' < p, ∃ q < p, p = pIte b a' p' q ∧
        ∃ r < pr + C + 1, ⟪n, me, opp, b, r⟫ ∈ C ∧
          ((r = a' ∧ ⟪n, me, opp, p', a⟫ ∈ C) ∨ (r ≠ a' ∧ ⟪n, me, opp, q, a⟫ ∈ C))) ∨
      (∃ k < p, ∃ g < p, ∃ p' < p, ∃ q < p, p = pSearch k g p' q ∧
        ((LenProvableV TBad k (guardCode g me opp) ∧ ⟪n, me, opp, p', a⟫ ∈ C) ∨
         (¬LenProvableV TBad k (guardCode g me opp) ∧ ⟪n, me, opp, q, a⟫ ∈ C))) ) := by
  constructor
  · rintro (⟨n, me, opp, a, rfl⟩ | ⟨n, me, opp, a, h, rfl⟩ | ⟨n, me, opp, a, h, rfl⟩ |
      ⟨n, me, opp, p, a, h, rfl⟩ | ⟨n, me, opp, p, q, a, h, rfl⟩ |
      ⟨n, me, opp, b, a', p, q, a, r, hb, hpq, rfl⟩ | ⟨n, me, opp, k, g, p, q, a, hpq, rfl⟩)
    · obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := tuple_bounds n me opp (pConst a) a
      exact ⟨n, h₁, me, h₂, opp, h₃, _, h₄, a, h₅, rfl, Or.inl rfl⟩
    · obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := tuple_bounds n me opp pSelf a
      exact ⟨n, h₁, me, h₂, opp, h₃, _, h₄, a, h₅, rfl, Or.inr (Or.inl ⟨rfl, h⟩)⟩
    · obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := tuple_bounds n me opp pOpp a
      exact ⟨n, h₁, me, h₂, opp, h₃, _, h₄, a, h₅, rfl, Or.inr (Or.inr (Or.inl ⟨rfl, h⟩))⟩
    · obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := tuple_bounds n me opp (pBot p) a
      exact ⟨n, h₁, me, h₂, opp, h₃, _, h₄, a, h₅, rfl,
        Or.inr (Or.inr (Or.inr (Or.inl ⟨p, by simp, rfl, h⟩)))⟩
    · obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := tuple_bounds n me opp (pSim p q) a
      exact ⟨n, h₁, me, h₂, opp, h₃, _, h₄, a, h₅, rfl,
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, by simp, q, by simp, rfl, h⟩))))⟩
    · obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := tuple_bounds n me opp (pIte b a' p q) a
      exact ⟨n, h₁, me, h₂, opp, h₃, _, h₄, a, h₅, rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨b, by simp, a', by simp, p, by simp, q, by simp, rfl, r,
          lt_of_lt_of_le (lt_of_tuple_mem hb) (le_trans le_add_self le_self_add), hb, hpq⟩)))))⟩
    · obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := tuple_bounds n me opp (pSearch k g p q) a
      exact ⟨n, h₁, me, h₂, opp, h₃, _, h₄, a, h₅, rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨k, by simp, g, by simp, p, by simp, q, by simp, rfl, hpq⟩)))))⟩
  · rintro ⟨n, _, me, _, opp, _, p, _, a, _, rfl, (rfl | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨p', _, rfl, h⟩ |
      ⟨p', _, q, _, rfl, h⟩ | ⟨b, _, a', _, p', _, q, _, rfl, r, _, hb, hpq⟩ |
      ⟨k, _, g, _, p', _, q, _, rfl, hpq⟩)⟩
    · exact Or.inl ⟨n, me, opp, a, rfl⟩
    · exact Or.inr (Or.inl ⟨n, me, opp, a, h, rfl⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨n, me, opp, a, h, rfl⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨n, me, opp, p', a, h, rfl⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, me, opp, p', q, a, h, rfl⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, me, opp, b, a', p', q, a, r, hb, hpq, rfl⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨n, me, opp, k, g, p', q, a, hpq, rfl⟩)))))

noncomputable def construction : Fixpoint.Construction V blueprint where
  Φ := fun _ ↦ Phi
  defined := .mk <| by
    constructor
    · intro v
      simp [blueprint, HierarchySymbol.Semiformula.val_sigma,
        (LenProvableV.defined TBad).proper.iff', psubst_defined.df]
    · intro v
      symm
      simpa [blueprint, HierarchySymbol.Semiformula.val_sigma, (LenProvableV.defined TBad).df,
        psubst_defined.df, pSelfGraph, pOppGraph, pSelf, pOpp, lt_and_eq_succ_iff]
        using phi_iff (v 1) (v 0)
  monotone := by
    rintro C C' hC _ pr (⟨n, me, opp, a, rfl⟩ | ⟨n, me, opp, a, h, rfl⟩ | ⟨n, me, opp, a, h, rfl⟩ |
      ⟨n, me, opp, p, a, h, rfl⟩ | ⟨n, me, opp, p, q, a, h, rfl⟩ |
      ⟨n, me, opp, b, a', p, q, a, r, hb, hpq, rfl⟩ | ⟨n, me, opp, k, g, p, q, a, hpq, rfl⟩)
    · exact Or.inl ⟨n, me, opp, a, rfl⟩
    · exact Or.inr (Or.inl ⟨n, me, opp, a, hC h, rfl⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨n, me, opp, a, hC h, rfl⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨n, me, opp, p, a, hC h, rfl⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, me, opp, p, q, a, hC h, rfl⟩))))
    · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨n, me, opp, b, a', p, q, a, r, hC hb, ?_, rfl⟩)))))
      rcases hpq with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨h1, hC h2⟩
      · exact Or.inr ⟨h1, hC h2⟩
    · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨n, me, opp, k, g, p, q, a, ?_, rfl⟩)))))
      rcases hpq with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨h1, hC h2⟩
      · exact Or.inr ⟨h1, hC h2⟩

instance : construction.Finite V where
  finite := by
    rintro C _ pr (⟨n, me, opp, a, rfl⟩ | ⟨n, me, opp, a, h, rfl⟩ | ⟨n, me, opp, a, h, rfl⟩ |
      ⟨n, me, opp, p, a, h, rfl⟩ | ⟨n, me, opp, p, q, a, h, rfl⟩ |
      ⟨n, me, opp, b, a', p, q, a, r, hb, hpq, rfl⟩ | ⟨n, me, opp, k, g, p, q, a, hpq, rfl⟩)
    · exact ⟨0, Or.inl ⟨n, me, opp, a, rfl⟩⟩
    · exact ⟨_ + 1, Or.inr (Or.inl ⟨n, me, opp, a, ⟨h, lt_add_one _⟩, rfl⟩)⟩
    · exact ⟨_ + 1, Or.inr (Or.inr (Or.inl ⟨n, me, opp, a, ⟨h, lt_add_one _⟩, rfl⟩))⟩
    · exact ⟨_ + 1, Or.inr (Or.inr (Or.inr (Or.inl ⟨n, me, opp, p, a, ⟨h, lt_add_one _⟩, rfl⟩)))⟩
    · exact ⟨_ + 1, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, me, opp, p, q, a, ⟨h, lt_add_one _⟩, rfl⟩))))⟩
    · refine ⟨⟪n, me, opp, b, r⟫ + ⟪n, me, opp, p, a⟫ + ⟪n, me, opp, q, a⟫ + 1,
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, me, opp, b, a', p, q, a, r, ⟨hb, by
          have := le_self_add (a := ⟪n, me, opp, b, r⟫) (b := ⟪n, me, opp, p, a⟫)
          have := le_self_add (a := ⟪n, me, opp, b, r⟫ + ⟪n, me, opp, p, a⟫) (b := ⟪n, me, opp, q, a⟫)
          exact lt_of_le_of_lt (le_trans (by assumption) (by assumption)) (lt_add_one _)⟩, ?_, rfl⟩)))))⟩
      rcases hpq with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨h1, h2, by
          have := le_add_self (a := ⟪n, me, opp, p, a⟫) (b := ⟪n, me, opp, b, r⟫)
          have := le_self_add (a := ⟪n, me, opp, b, r⟫ + ⟪n, me, opp, p, a⟫) (b := ⟪n, me, opp, q, a⟫)
          exact lt_of_le_of_lt (le_trans (by assumption) (by assumption)) (lt_add_one _)⟩
      · exact Or.inr ⟨h1, h2, lt_of_le_of_lt le_add_self (lt_add_one _)⟩
    · refine ⟨⟪n, me, opp, p, a⟫ + ⟪n, me, opp, q, a⟫ + 1,
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨n, me, opp, k, g, p, q, a, ?_, rfl⟩)))))⟩
      rcases hpq with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨h1, h2, lt_of_le_of_lt le_self_add (lt_add_one _)⟩
      · exact Or.inr ⟨h1, h2, lt_of_le_of_lt le_add_self (lt_add_one _)⟩

end EvalFixBad

/-- `EvalGraphBad n me opp p a`: `EvalGraph` with the search node consulting `TBad`. -/
def EvalGraphBad (n me opp p a : V) : Prop := EvalFixBad.construction.Fixpoint ![] ⟪n, me, opp, p, a⟫

noncomputable def evalGraphBadDef : 𝚺₁.Semisentence 5 := .mkSigma
  “n me opp p a. ∃ pr, !pair₅Def pr n me opp p a ∧ !EvalFixBad.blueprint.fixpointDef pr”

private lemma evalBad_param_eq (p : Fin 0 → V) (x : V) :
    EvalFixBad.construction.Fixpoint p x = EvalFixBad.construction.Fixpoint ![] x := by
  rw [Subsingleton.elim p ![]]

lemma evalGraphBad_defined :
    𝚺₁.Defined (fun v : Fin 5 → V ↦ EvalGraphBad (v 0) (v 1) (v 2) (v 3) (v 4)) evalGraphBadDef :=
  .mk fun v ↦ by
    simp [evalGraphBadDef, EvalFixBad.construction.fixpoint_defined.iff, EvalGraphBad]
    rw [evalBad_param_eq]

instance evalGraphBad_definable : 𝚺₁-Relation₅[V] EvalGraphBad := evalGraphBad_defined.to_definable

lemma EvalGraphBad.case_iff {n me opp p a : V} :
    EvalGraphBad n me opp p a ↔
    ∃ n', n = n' + 1 ∧
    ( p = pConst a ∨
      (p = pSelf ∧ EvalGraphBad n' me opp me a) ∨
      (p = pOpp ∧ EvalGraphBad n' me opp opp a) ∨
      (∃ p', p = pBot p' ∧ EvalGraphBad n' me opp p' a) ∨
      (∃ p' q, p = pSim p' q ∧
        EvalGraphBad n' (psubst me opp p') (psubst me opp q) (psubst me opp p') a) ∨
      (∃ b a' p' q r, p = pIte b a' p' q ∧ EvalGraphBad n' me opp b r ∧
        ((r = a' ∧ EvalGraphBad n' me opp p' a) ∨ (r ≠ a' ∧ EvalGraphBad n' me opp q a))) ∨
      (∃ k g p' q, p = pSearch k g p' q ∧
        ((LenProvableV TBad k (guardCode g me opp) ∧ EvalGraphBad n' me opp p' a) ∨
         (¬LenProvableV TBad k (guardCode g me opp) ∧ EvalGraphBad n' me opp q a))) ) := by
  rw [EvalGraphBad, EvalFixBad.construction.case]
  simp only [EvalFixBad.construction, EvalFixBad.Phi, Set.mem_setOf_eq, pair_ext_iff]
  constructor
  · rintro (⟨n₀, me₀, opp₀, a₀, h⟩ | ⟨n₀, me₀, opp₀, a₀, hc, h⟩ | ⟨n₀, me₀, opp₀, a₀, hc, h⟩ |
      ⟨n₀, me₀, opp₀, p₀, a₀, hc, h⟩ | ⟨n₀, me₀, opp₀, p', q, a₀, hc, h⟩ |
      ⟨n₀, me₀, opp₀, b, a', p', q, a₀, r, hb, hpq, h⟩ | ⟨n₀, me₀, opp₀, k, g, p', q, a₀, hpq, h⟩) <;>
      obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
    · exact ⟨n₀, rfl, Or.inl rfl⟩
    · exact ⟨n₀, rfl, Or.inr (Or.inl ⟨rfl, hc⟩)⟩
    · exact ⟨n₀, rfl, Or.inr (Or.inr (Or.inl ⟨rfl, hc⟩))⟩
    · exact ⟨n₀, rfl, Or.inr (Or.inr (Or.inr (Or.inl ⟨p₀, rfl, hc⟩)))⟩
    · exact ⟨n₀, rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p', q, rfl, hc⟩))))⟩
    · exact ⟨n₀, rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨b, a', p', q, r, rfl, hb, hpq⟩)))))⟩
    · exact ⟨n₀, rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨k, g, p', q, rfl, hpq⟩)))))⟩
  · rintro ⟨n', rfl, (rfl | ⟨rfl, hc⟩ | ⟨rfl, hc⟩ | ⟨p', rfl, hc⟩ | ⟨p', q, rfl, hc⟩ |
      ⟨b, a', p', q, r, rfl, hb, hpq⟩ | ⟨k, g, p', q, rfl, hpq⟩)⟩
    · exact Or.inl ⟨n', me, opp, a, by simp⟩
    · exact Or.inr (Or.inl ⟨n', me, opp, a, hc, by simp⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨n', me, opp, a, hc, by simp⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨n', me, opp, p', a, hc, by simp⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n', me, opp, p', q, a, hc, by simp⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n', me, opp, b, a', p', q, a, r, hb, hpq, by simp⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨n', me, opp, k, g, p', q, a, hpq, by simp⟩)))))

/-! #### Clause inversion (`ArithS.EvalN`, theory swapped) -/

section inversion

attribute [local simp] pConst pSelf pOpp pBot pSim pIte pSearch

lemma EvalGraphBad.zero_iff {me opp p a : V} : ¬EvalGraphBad 0 me opp p a := by
  rw [EvalGraphBad.case_iff]
  rintro ⟨n', h, _⟩
  exact zero_ne_add_one n' h

lemma EvalGraphBad.const_iff {n me opp a a' : V} :
    EvalGraphBad (n + 1) me opp (pConst a) a' ↔ a' = a := by
  rw [EvalGraphBad.case_iff]; simp [eq_comm]

lemma EvalGraphBad.self_iff {n me opp a : V} :
    EvalGraphBad (n + 1) me opp pSelf a ↔ EvalGraphBad n me opp me a := by
  rw [EvalGraphBad.case_iff]; simp

lemma EvalGraphBad.opp_iff {n me opp a : V} :
    EvalGraphBad (n + 1) me opp pOpp a ↔ EvalGraphBad n me opp opp a := by
  rw [EvalGraphBad.case_iff]; simp

lemma EvalGraphBad.bot_iff {n me opp p a : V} :
    EvalGraphBad (n + 1) me opp (pBot p) a ↔ EvalGraphBad n me opp p a := by
  rw [EvalGraphBad.case_iff]; simp

lemma EvalGraphBad.sim_iff {n me opp p q a : V} :
    EvalGraphBad (n + 1) me opp (pSim p q) a ↔
    EvalGraphBad n (psubst me opp p) (psubst me opp q) (psubst me opp p) a := by
  rw [EvalGraphBad.case_iff]; simp

lemma EvalGraphBad.ite_iff {n me opp b a' p q a : V} :
    EvalGraphBad (n + 1) me opp (pIte b a' p q) a ↔
    ∃ r, EvalGraphBad n me opp b r ∧
      ((r = a' ∧ EvalGraphBad n me opp p a) ∨ (r ≠ a' ∧ EvalGraphBad n me opp q a)) := by
  rw [EvalGraphBad.case_iff]; simp

lemma EvalGraphBad.search_iff {n me opp k g p q a : V} :
    EvalGraphBad (n + 1) me opp (pSearch k g p q) a ↔
    ((LenProvableV TBad k (guardCode g me opp) ∧ EvalGraphBad n me opp p a) ∨
     (¬LenProvableV TBad k (guardCode g me opp) ∧ EvalGraphBad n me opp q a)) := by
  rw [EvalGraphBad.case_iff]; simp

end inversion

/-! #### On `ℕ`: determinism and fuel monotonicity (`ArithS.EvalN`, theory swapped) -/

section nat

theorem EvalGraphBad.unique (n : ℕ) : ∀ me opp p a₁ a₂ : ℕ,
    EvalGraphBad n me opp p a₁ → EvalGraphBad n me opp p a₂ → a₁ = a₂ := by
  induction n with
  | zero => intro me opp p a₁ a₂ h; exact absurd h EvalGraphBad.zero_iff
  | succ n ih =>
    intro me opp p a₁ a₂ h₁ h₂
    by_cases hp : IsShape p
    · rcases hp with ⟨a, rfl⟩ | rfl | rfl | ⟨p, rfl⟩ | ⟨p, q, rfl⟩ | ⟨b, a', p, q, rfl⟩ | ⟨k, g, p, q, rfl⟩
      · rw [EvalGraphBad.const_iff] at h₁ h₂; rw [h₁, h₂]
      · rw [EvalGraphBad.self_iff] at h₁ h₂; exact ih _ _ _ _ _ h₁ h₂
      · rw [EvalGraphBad.opp_iff] at h₁ h₂; exact ih _ _ _ _ _ h₁ h₂
      · rw [EvalGraphBad.bot_iff] at h₁ h₂; exact ih _ _ _ _ _ h₁ h₂
      · rw [EvalGraphBad.sim_iff] at h₁ h₂; exact ih _ _ _ _ _ h₁ h₂
      · rcases EvalGraphBad.ite_iff.mp h₁ with ⟨r₁, hb₁, hc₁⟩
        rcases EvalGraphBad.ite_iff.mp h₂ with ⟨r₂, hb₂, hc₂⟩
        have hr : r₁ = r₂ := ih _ _ _ _ _ hb₁ hb₂
        subst hr
        rcases hc₁ with ⟨e₁, h₁'⟩ | ⟨e₁, h₁'⟩ <;> rcases hc₂ with ⟨e₂, h₂'⟩ | ⟨e₂, h₂'⟩
        · exact ih _ _ _ _ _ h₁' h₂'
        · exact absurd e₁ e₂
        · exact absurd e₂ e₁
        · exact ih _ _ _ _ _ h₁' h₂'
      · rcases EvalGraphBad.search_iff.mp h₁ with ⟨e₁, h₁'⟩ | ⟨e₁, h₁'⟩ <;>
          rcases EvalGraphBad.search_iff.mp h₂ with ⟨e₂, h₂'⟩ | ⟨e₂, h₂'⟩
        · exact ih _ _ _ _ _ h₁' h₂'
        · exact absurd e₁ e₂
        · exact absurd e₂ e₁
        · exact ih _ _ _ _ _ h₁' h₂'
    · exfalso
      rcases EvalGraphBad.case_iff.mp h₁ with ⟨n', _, (h | ⟨h, _⟩ | ⟨h, _⟩ | ⟨p', h, _⟩ |
        ⟨p', q, h, _⟩ | ⟨b, a', p', q, r, h, _⟩ | ⟨k, g, p', q, h, _⟩)⟩
      · exact hp (Or.inl ⟨_, h⟩)
      · exact hp (Or.inr (Or.inl h))
      · exact hp (Or.inr (Or.inr (Or.inl h)))
      · exact hp (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, h⟩))))
      · exact hp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, h⟩)))))
      · exact hp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, _, _, h⟩))))))
      · exact hp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨_, _, _, _, h⟩))))))

theorem EvalGraphBad.mono (n : ℕ) : ∀ me opp p a : ℕ,
    EvalGraphBad n me opp p a → EvalGraphBad (n + 1) me opp p a := by
  induction n with
  | zero => intro me opp p a h; exact absurd h EvalGraphBad.zero_iff
  | succ n ih =>
    intro me opp p a h
    rcases EvalGraphBad.case_iff.mp h with ⟨n', hn, H⟩
    have hn' : n' = n := by omega
    rw [hn'] at H
    rw [EvalGraphBad.case_iff]
    refine ⟨n + 1, rfl, ?_⟩
    rcases H with h | ⟨h, hc⟩ | ⟨h, hc⟩ | ⟨p', h, hc⟩ | ⟨p', q, h, hc⟩ |
      ⟨b, a', p', q, r, h, hb, hpq⟩ | ⟨k, g, p', q, h, hpq⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨h, ih _ _ _ _ hc⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨h, ih _ _ _ _ hc⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨p', h, ih _ _ _ _ hc⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p', q, h, ih _ _ _ _ hc⟩))))
    · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨b, a', p', q, r, h, ih _ _ _ _ hb, ?_⟩)))))
      rcases hpq with ⟨e, hc⟩ | ⟨e, hc⟩
      · exact Or.inl ⟨e, ih _ _ _ _ hc⟩
      · exact Or.inr ⟨e, ih _ _ _ _ hc⟩
    · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨k, g, p', q, h, ?_⟩)))))
      rcases hpq with ⟨e, hc⟩ | ⟨e, hc⟩
      · exact Or.inl ⟨e, ih _ _ _ _ hc⟩
      · exact Or.inr ⟨e, ih _ _ _ _ hc⟩

theorem EvalGraphBad.mono_le {n n' me opp p a : ℕ} (h : n ≤ n') (e : EvalGraphBad n me opp p a) :
    EvalGraphBad n' me opp p a := by
  induction h with
  | refl => exact e
  | step _ ih => exact EvalGraphBad.mono _ _ _ _ _ ih

theorem EvalGraphBad.unique' {n n' me opp p a a' : ℕ}
    (h : EvalGraphBad n me opp p a) (h' : EvalGraphBad n' me opp p a') : a = a' :=
  EvalGraphBad.unique (max n n') me opp p a a' (EvalGraphBad.mono_le (le_max_left _ _) h)
    (EvalGraphBad.mono_le (le_max_right _ _) h')

end nat

/-! ### 4. Both guards are `TBad`-provable within budget, for all large `k` -/

/-- **The ex-falso proofs of both guard sentences fit their budget** for all large `k`:
`guard_fits`'s argument with the ex-falso constants (`3·|guard| + 2·|axEq| + 3 ≤ k`). -/
theorem guards_fit_bad :
    ∃ K, ∀ k ≥ K, ∀ a ≤ 1,
      3 * flen (Rewriting.emb (guardSentenceA a (Dupoc k) (Cupod k)) : Proposition LAct) +
        2 * flen (axEq : Proposition LAct) + 3 ≤ k ∧
      3 * flen (Rewriting.emb (guardSentenceA a (Cupod k) (Dupoc k)) : Proposition LAct) +
        2 * flen (axEq : Proposition LAct) + 3 ≤ k := by
  obtain ⟨c, hc⟩ := exists_guard_const
  obtain ⟨D, hD⟩ := exists_desc_const
  obtain ⟨K, hK⟩ := exists_linear_size_le
    (3 * (c * (2 * D + 5)) + 2 * flen (axEq : Proposition LAct) + 3) (3 * (72 * c))
  refine ⟨K, fun k hk a ha ↦ ?_⟩
  obtain ⟨h1, h2⟩ := hD k
  have b1 : flen (Rewriting.emb (guardSentenceA a (Dupoc k) (Cupod k)) : Proposition LAct) ≤
      c * (2 * D + 5) + 72 * c * Nat.size k :=
    calc flen (Rewriting.emb (guardSentenceA a (Dupoc k) (Cupod k)) : Proposition LAct)
        ≤ c * (tlen (Rew.emb (dnumT (Dupoc k)) : SyntacticSemiterm LAct 0) +
            tlen (Rew.emb (dnumT (Cupod k)) : SyntacticSemiterm LAct 0) + 5) := hc _ _ a ha
      _ ≤ c * (72 * Nat.size k + 2 * D + 5) := Nat.mul_le_mul_left _ (by omega)
      _ = c * (2 * D + 5) + 72 * c * Nat.size k := by ring
  have b2 : flen (Rewriting.emb (guardSentenceA a (Cupod k) (Dupoc k)) : Proposition LAct) ≤
      c * (2 * D + 5) + 72 * c * Nat.size k :=
    calc flen (Rewriting.emb (guardSentenceA a (Cupod k) (Dupoc k)) : Proposition LAct)
        ≤ c * (tlen (Rew.emb (dnumT (Cupod k)) : SyntacticSemiterm LAct 0) +
            tlen (Rew.emb (dnumT (Dupoc k)) : SyntacticSemiterm LAct 0) + 5) := hc _ _ a ha
      _ ≤ c * (72 * Nat.size k + 2 * D + 5) := Nat.mul_le_mul_left _ (by omega)
      _ = c * (2 * D + 5) + 72 * c * Nat.size k := by ring
  have hK' : 3 * (c * (2 * D + 5) + 72 * c * Nat.size k) + 2 * flen (axEq : Proposition LAct) + 3 ≤ k :=
    calc 3 * (c * (2 * D + 5) + 72 * c * Nat.size k) + 2 * flen (axEq : Proposition LAct) + 3
        = 3 * (c * (2 * D + 5)) + 2 * flen (axEq : Proposition LAct) + 3 +
            3 * (72 * c) * Nat.size k := by ring
      _ ≤ k := hK k hk
  exact ⟨by omega, by omega⟩

/-- **Both guards are found under `TBad`**: for all large `k`, Dupoc's guard against Cupod
("Cupod plays `C` against me") and Cupod's guard against Dupoc ("Dupoc plays `D` against me")
are `LenProvableV TBad k` — from a contradiction, everything is short. -/
theorem guard_provable_bad :
    ∃ K, ∀ k ≥ K,
      LenProvableV TBad k (guardCode (⌜GtmplA 0⌝ : ℕ) (Dupoc k) (Cupod k)) ∧
      LenProvableV TBad k (guardCode (⌜GtmplA 1⌝ : ℕ) (Cupod k) (Dupoc k)) := by
  obtain ⟨K, hK⟩ := guards_fit_bad
  refine ⟨K, fun k hk ↦ ⟨?_, ?_⟩⟩
  · rw [← quote_guardSentenceA, lenProvableV_nat_TBad]
    exact lenProvable_TBad_of_flen (hK k hk 0 (by norm_num)).1
  · rw [← quote_guardSentenceA, lenProvableV_nat_TBad]
    exact lenProvable_TBad_of_flen (hK k hk 1 le_rfl).2

/-! ### 5. The flip -/

/-- **The red cell flips when soundness is dropped**: under `EvalGraphBad` — the same
evaluator consulting the inconsistent `TBad` — for all large `k`, `Dupoc k` COOPERATES with
`Cupod k` and `Cupod k` DEFECTS against `Dupoc k` (fuel 2): `(C, D) = (0, 1)`, the opposite
of `red_cell`'s `(D, C) = (1, 0)`. Both searchers find their guard and take the then-branch. -/
theorem red_cell_flips_when_unsound :
    ∃ K, ∀ k ≥ K,
      EvalGraphBad 2 (Dupoc k) (Cupod k) (Dupoc k) 0 ∧ EvalGraphBad 2 (Cupod k) (Dupoc k) (Cupod k) 1 := by
  obtain ⟨K, hK⟩ := guard_provable_bad
  refine ⟨K, fun k hk ↦ ?_⟩
  obtain ⟨hD, hC⟩ := hK k hk
  constructor
  · show EvalGraphBad (1 + 1) (Dupoc k) (Cupod k) (pSearch k (⌜GtmplA 0⌝ : ℕ) (pConst 0) (pConst 1)) 0
    rw [EvalGraphBad.search_iff]
    exact Or.inl ⟨hD, (EvalGraphBad.const_iff (n := 0)).mpr rfl⟩
  · show EvalGraphBad (1 + 1) (Cupod k) (Dupoc k) (pSearch k (⌜GtmplA 1⌝ : ℕ) (pConst 1) (pConst 0)) 1
    rw [EvalGraphBad.search_iff]
    exact Or.inl ⟨hC, (EvalGraphBad.const_iff (n := 0)).mpr rfl⟩

/-- **Sound vs unsound, side by side**: at every large `k`, the sound evaluator says `(D, C)`
and the unsound one says `(C, D)` — same programs, same clauses, same budget. -/
theorem red_cell_flip :
    ∃ K, ∀ k ≥ K,
      (EvalGraph 2 (Dupoc k) (Cupod k) (Dupoc k) 1 ∧ EvalGraph 2 (Cupod k) (Dupoc k) (Cupod k) 0) ∧
      (EvalGraphBad 2 (Dupoc k) (Cupod k) (Dupoc k) 0 ∧ EvalGraphBad 2 (Cupod k) (Dupoc k) (Cupod k) 1) := by
  obtain ⟨K, hK⟩ := red_cell_flips_when_unsound
  exact ⟨K, fun k hk ↦ ⟨red_cell k, hK k hk⟩⟩

/-- Under `TBad` the flipped outcome is the only one, at every fuel (for large `k`). -/
theorem red_cell_flips_unique :
    ∃ K, ∀ k ≥ K, ∀ (n : ℕ) {a b : ℕ},
      EvalGraphBad n (Dupoc k) (Cupod k) (Dupoc k) a → EvalGraphBad n (Cupod k) (Dupoc k) (Cupod k) b →
      a = 0 ∧ b = 1 := by
  obtain ⟨K, hK⟩ := red_cell_flips_when_unsound
  exact ⟨K, fun k hk n a b ha hb ↦
    ⟨EvalGraphBad.unique' ha (hK k hk).1, EvalGraphBad.unique' hb (hK k hk).2⟩⟩

end ArithS

#print axioms ArithS.tbad_inconsistent
#print axioms ArithS.tbad_proves_bot
#print axioms ArithS.lenProvable_TBad_of_flen
#print axioms ArithS.guard_provable_bad
#print axioms ArithS.red_cell_flips_when_unsound
#print axioms ArithS.red_cell_flip
#print axioms ArithS.red_cell_flips_unique
