import ArithS.MetaLength
import ArithS.Prog
import Mathlib.Data.Nat.Size

/-!
# ArithS.Bnum — binary numeral terms, of length `O(‖n‖)`

Critch's assumption (b) (Appendix B of `critch22`): the proof system writes a number `n` in
`O(lg n)` characters. Foundation's canonical numerals `numeral n = 1 + ⋯ + 1` are UNARY
(`tlen ↑n ~ 2n`), and under them the guard sentence of a searcher of budget `k` — which
names the searcher by its own code, `≥ k` — is longer than `k` (the retired `Vacuity.lean`,
commit 470ee43). This file provides the O(log)-length replacement used by the canonical
descriptions of `ArithS.Guard`/`ArithS.Template`:

* internally, `bnum : V → V` (V an `𝗜𝚺₁` model) is the term code with value `n` built along
  the bits of `n`: `bnum 0 = 𝟎`, `bnum 1 = 𝟏`, `bnum (2m) = 𝟐 ^* bnum m`,
  `bnum (2m + 1) = (𝟐 ^* bnum m) ^+ 𝟏` (`m ≥ 1`, `𝟐 := 𝟏 ^+ 𝟏`). It is the graph of a
  StrongFinite `Fixpoint` on pairs `⟪n, t⟫` (a Δ₁ blueprint whose core cites the Σ₁ graphs
  of `^+`/`^*` in both polarities, exactly like `DlenGraph`), so `bnum` is a Σ₁ function;
* on the meta side, `bnumT : ℕ → ClosedSemiterm ℒₒᵣ 0` is the same recursion on the syntax
  (`‘!!𝟐 * !!t’`, `‘!!𝟐 * !!t + 1’`), with the CODE equation `⌜bnumT n⌝ = bnum n` in every
  model, the TRUTH equation `val (bnumT n) = n` in `ℕ`, and the LENGTH bound
  `tlen (bnumT n) ≤ 6 · size n + 1` (`Nat.size` = bit length).

The length measure `tlen`/`termLen` is untouched: a binary numeral simply IS a short term.
-/

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ### The term code `𝟐 = 𝟏 + 𝟏` -/

/-- The term code of `1 + 1`. -/
noncomputable def qqTwo : V := (𝟏 : V) ^+ (𝟏 : V)

@[inherit_doc] notation "𝟐" => qqTwo

@[simp] lemma qqTwo_semiterm {k : V} : IsSemiterm ℒₒᵣ k (𝟐 : V) := by simp [qqTwo, qqAdd]

/-! ### The graph, as a fixpoint on pairs `⟪n, t⟫` -/

namespace Bnum

/-- `Phi C ⟪n, t⟫`: `t` is the binary numeral of `n`, given the sub-results in `C`. -/
def Phi (C : Set V) (pr : V) : Prop :=
  pr = ⟪(0 : V), (𝟎 : V)⟫ ∨ pr = ⟪(1 : V), (𝟏 : V)⟫ ∨
  (∃ m t, 1 ≤ m ∧ ⟪m, t⟫ ∈ C ∧ pr = ⟪2 * m, 𝟐 ^* t⟫) ∨
  (∃ m t, 1 ≤ m ∧ ⟪m, t⟫ ∈ C ∧ pr = ⟪2 * m + 1, (𝟐 ^* t) ^+ 𝟏⟫)

noncomputable def blueprint : Fixpoint.Blueprint 0 := ⟨.mkDelta
  (.mkSigma “pr C.
    ∃ n <⁺ pr, ∃ t <⁺ pr, !pairDef pr n t ∧
    ( (n = 0 ∧ t = ↑Arithmetic.zero) ∨
      (n = 1 ∧ t = ↑Arithmetic.one) ∨
      (∃ m < n, ∃ t' < t, 1 ≤ m ∧ :⟪m, t'⟫:∈ C ∧ n = 2 * m ∧
        ∃ two, !qqAddGraph two ↑Arithmetic.one ↑Arithmetic.one ∧ !qqMulGraph t two t') ∨
      (∃ m < n, ∃ t' < t, 1 ≤ m ∧ :⟪m, t'⟫:∈ C ∧ n = 2 * m + 1 ∧
        ∃ two, !qqAddGraph two ↑Arithmetic.one ↑Arithmetic.one ∧
        ∃ s, !qqMulGraph s two t' ∧ !qqAddGraph t s ↑Arithmetic.one) )”)
  (.mkPi “pr C.
    ∃ n <⁺ pr, ∃ t <⁺ pr, !pairDef pr n t ∧
    ( (n = 0 ∧ t = ↑Arithmetic.zero) ∨
      (n = 1 ∧ t = ↑Arithmetic.one) ∨
      (∃ m < n, ∃ t' < t, 1 ≤ m ∧ :⟪m, t'⟫:∈ C ∧ n = 2 * m ∧
        ∀ two, !qqAddGraph two ↑Arithmetic.one ↑Arithmetic.one → ∀ s, !qqMulGraph s two t' → t = s) ∨
      (∃ m < n, ∃ t' < t, 1 ≤ m ∧ :⟪m, t'⟫:∈ C ∧ n = 2 * m + 1 ∧
        ∀ two, !qqAddGraph two ↑Arithmetic.one ↑Arithmetic.one → ∀ s, !qqMulGraph s two t' →
        ∀ r, !qqAddGraph r s ↑Arithmetic.one → t = r) )”)⟩

lemma lt_two_mul {m : V} (hm : 1 ≤ m) : m < 2 * m := by
  rw [two_mul]
  exact lt_of_lt_of_le (lt_add_one m) (by rw [add_comm]; exact add_le_add_left hm m)

lemma lt_two_mul_add_one {m : V} (hm : 1 ≤ m) : m < 2 * m + 1 :=
  lt_trans (lt_two_mul hm) (lt_add_one _)

lemma lt_qqMul_qqAdd (t : V) : t < (𝟐 ^* t) ^+ 𝟏 := lt_trans (lt_qqMul_right _ _) (lt_qqAdd_left _ _)

/-- `Phi` with the bounds the blueprint carries. -/
private lemma phi_iff (C pr : V) :
    Phi {x | x ∈ C} pr ↔
    ∃ n ≤ pr, ∃ t ≤ pr, pr = ⟪n, t⟫ ∧
    ( (n = 0 ∧ t = 𝟎) ∨ (n = 1 ∧ t = 𝟏) ∨
      (∃ m < n, ∃ t' < t, 1 ≤ m ∧ ⟪m, t'⟫ ∈ C ∧ n = 2 * m ∧ t = 𝟐 ^* t') ∨
      (∃ m < n, ∃ t' < t, 1 ≤ m ∧ ⟪m, t'⟫ ∈ C ∧ n = 2 * m + 1 ∧ t = (𝟐 ^* t') ^+ 𝟏) ) := by
  constructor
  · rintro (rfl | rfl | ⟨m, t, hm, h, rfl⟩ | ⟨m, t, hm, h, rfl⟩)
    · exact ⟨_, by simp, _, by simp, rfl, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨_, by simp, _, by simp, rfl, Or.inr <| Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨_, by simp, _, by simp, rfl, Or.inr <| Or.inr <| Or.inl
        ⟨m, lt_two_mul hm, t, lt_qqMul_right _ _, hm, h, rfl, rfl⟩⟩
    · exact ⟨_, by simp, _, by simp, rfl, Or.inr <| Or.inr <| Or.inr
        ⟨m, lt_two_mul_add_one hm, t, lt_qqMul_qqAdd t, hm, h, rfl, rfl⟩⟩
  · rintro ⟨n, _, t, _, rfl, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨m, _, t', _, hm, h, rfl, rfl⟩ |
      ⟨m, _, t', _, hm, h, rfl, rfl⟩)⟩
    · exact Or.inl rfl
    · exact Or.inr <| Or.inl rfl
    · exact Or.inr <| Or.inr <| Or.inl ⟨m, t', hm, h, rfl⟩
    · exact Or.inr <| Or.inr <| Or.inr ⟨m, t', hm, h, rfl⟩

noncomputable def construction : Fixpoint.Construction V blueprint where
  Φ := fun _ ↦ Phi
  defined := .mk <| by
    constructor
    · intro v
      simp [blueprint, qqAdd_defined.iff, qqMul_defined.iff, numeral_eq_natCast]
    · intro v
      symm
      simpa [blueprint, qqAdd_defined.iff, qqMul_defined.iff, numeral_eq_natCast, qqTwo]
        using phi_iff (v 1) (v 0)
  monotone := by
    rintro C C' hC _ pr (rfl | rfl | ⟨m, t, hm, h, rfl⟩ | ⟨m, t, hm, h, rfl⟩)
    · exact Or.inl rfl
    · exact Or.inr <| Or.inl rfl
    · exact Or.inr <| Or.inr <| Or.inl ⟨m, t, hm, hC h, rfl⟩
    · exact Or.inr <| Or.inr <| Or.inr ⟨m, t, hm, hC h, rfl⟩

/-- The referenced pair `⟪m, t⟫` is below `⟪2m, 𝟐 ^* t⟫` (and below `⟪2m + 1, (𝟐 ^* t) ^+ 𝟏⟫`). -/
instance : construction.StrongFinite V where
  strong_finite := by
    rintro C _ pr (rfl | rfl | ⟨m, t, hm, h, rfl⟩ | ⟨m, t, hm, h, rfl⟩)
    · exact Or.inl rfl
    · exact Or.inr <| Or.inl rfl
    · exact Or.inr <| Or.inr <| Or.inl
        ⟨m, t, hm, ⟨h, pair_lt_pair (lt_two_mul hm) (lt_qqMul_right _ _)⟩, rfl⟩
    · exact Or.inr <| Or.inr <| Or.inr
        ⟨m, t, hm, ⟨h, pair_lt_pair (lt_two_mul_add_one hm) (lt_qqMul_qqAdd t)⟩, rfl⟩

end Bnum

/-- `BnumGraph n t`: `t` is the binary numeral term code of `n`. -/
def BnumGraph (n t : V) : Prop := Bnum.construction.Fixpoint ![] ⟪n, t⟫

noncomputable def bnumGraphDef : 𝚫₁.Semisentence 2 := .mkDelta
  (.mkSigma “n t. ∃ pr <⁺ (n + t + 1)², !pairDef pr n t ∧ !Bnum.blueprint.fixpointDefΔ₁.sigma pr”)
  (.mkPi “n t. ∀ pr <⁺ (n + t + 1)², !pairDef pr n t → !Bnum.blueprint.fixpointDefΔ₁.pi pr”)

section

private lemma fixpoint_param_eq (p : Fin 0 → V) (x : V) :
    Bnum.construction.Fixpoint p x = Bnum.construction.Fixpoint ![] x := by
  rw [Subsingleton.elim p ![]]

instance bnumGraph_defined : 𝚫₁-Relation[V] BnumGraph via bnumGraphDef := .mk
  ⟨by intro v
      simp [bnumGraphDef, HierarchySymbol.Semiformula.val_sigma,
        Bnum.construction.fixpoint_definedΔ₁.proper.iff', Bnum.construction.fixpoint_definedΔ₁.df]
      constructor
      · rintro h x _ rfl; rwa [fixpoint_param_eq] at h ⊢
      · intro h; have := h ⟪v 0, v 1⟫ (by simp) rfl; rwa [fixpoint_param_eq] at this ⊢,
   by intro v
      simp [bnumGraphDef, HierarchySymbol.Semiformula.val_sigma,
        Bnum.construction.fixpoint_definedΔ₁.df, BnumGraph]
      rw [fixpoint_param_eq]⟩

instance bnumGraph_definable : 𝚫₁-Relation[V] BnumGraph := bnumGraph_defined.to_definable

instance bnumGraph_definable' : Γ-[m + 1]-Relation[V] BnumGraph := bnumGraph_definable.of_deltaOne

end

/-! ### Case analysis and inversion -/

lemma BnumGraph.case_iff {n t : V} :
    BnumGraph n t ↔
    (n = 0 ∧ t = 𝟎) ∨ (n = 1 ∧ t = 𝟏) ∨
    (∃ m t', 1 ≤ m ∧ BnumGraph m t' ∧ n = 2 * m ∧ t = 𝟐 ^* t') ∨
    (∃ m t', 1 ≤ m ∧ BnumGraph m t' ∧ n = 2 * m + 1 ∧ t = (𝟐 ^* t') ^+ 𝟏) :=
  Iff.trans Bnum.construction.case (by simp [Bnum.construction, Bnum.Phi, BnumGraph])

section arith

lemma two_mul_ne_zero {m : V} (hm : 1 ≤ m) : 2 * m ≠ 0 := by
  intro h
  have : 0 < 2 * m := mul_pos Arithmetic.two_pos (pos_iff_one_le.mpr hm)
  rw [h] at this
  exact _root_.lt_irrefl _ this

lemma two_mul_ne_one (m : V) : 2 * m ≠ 1 := by
  intro h
  have h1 : (2 * m) % 2 = 0 := by simp
  rw [h] at h1
  simp at h1

lemma two_mul_ne_two_mul_add_one (m m' : V) : 2 * m ≠ 2 * m' + 1 := by
  intro h
  have h1 : (2 * m) % 2 = 0 := by simp
  have h2 : (2 * m' + 1) % 2 = 1 := by simp
  rw [h, h2] at h1
  exact Arithmetic.one_ne_zero h1

lemma two_mul_add_one_ne_zero (m : V) : 2 * m + 1 ≠ 0 := by
  intro h
  have : 0 < 2 * m + 1 := lt_of_le_of_lt (Arithmetic.zero_le _) (lt_add_one _)
  rw [h] at this
  exact _root_.lt_irrefl _ this

lemma two_mul_add_one_ne_one {m : V} (hm : 1 ≤ m) : 2 * m + 1 ≠ 1 := by
  intro h
  have : 2 * m = 0 := by simpa using h
  exact two_mul_ne_zero hm this

lemma two_mul_inj {m m' : V} (h : 2 * m = 2 * m') : m = m' := by
  have := congrArg (· / 2) h
  simpa using this

lemma two_mul_add_one_inj {m m' : V} (h : 2 * m + 1 = 2 * m' + 1) : m = m' :=
  two_mul_inj (by simpa using h)

end arith

lemma BnumGraph.zero_iff {t : V} : BnumGraph 0 t ↔ t = 𝟎 := by
  rw [BnumGraph.case_iff]
  constructor
  · rintro (⟨_, rfl⟩ | ⟨h, _⟩ | ⟨m, t', hm, _, h, _⟩ | ⟨m, t', hm, _, h, _⟩)
    · rfl
    · exact absurd h.symm Arithmetic.one_ne_zero
    · exact absurd h.symm (two_mul_ne_zero hm)
    · exact absurd h.symm (two_mul_add_one_ne_zero m)
  · rintro rfl; exact Or.inl ⟨rfl, rfl⟩

lemma BnumGraph.one_iff {t : V} : BnumGraph 1 t ↔ t = 𝟏 := by
  rw [BnumGraph.case_iff]
  constructor
  · rintro (⟨h, _⟩ | ⟨_, rfl⟩ | ⟨m, t', hm, _, h, _⟩ | ⟨m, t', hm, _, h, _⟩)
    · exact absurd h Arithmetic.one_ne_zero
    · rfl
    · exact absurd h.symm (two_mul_ne_one m)
    · exact absurd h.symm (two_mul_add_one_ne_one hm)
  · rintro rfl; exact Or.inr <| Or.inl ⟨rfl, rfl⟩

lemma BnumGraph.two_mul_iff {m t : V} (hm : 1 ≤ m) :
    BnumGraph (2 * m) t ↔ ∃ t', BnumGraph m t' ∧ t = 𝟐 ^* t' := by
  rw [BnumGraph.case_iff]
  constructor
  · rintro (⟨h, _⟩ | ⟨h, _⟩ | ⟨m', t', _, ht', h, rfl⟩ | ⟨m', t', _, _, h, _⟩)
    · exact absurd h (two_mul_ne_zero hm)
    · exact absurd h (two_mul_ne_one m)
    · rw [two_mul_inj h]; exact ⟨t', ht', rfl⟩
    · exact absurd h (two_mul_ne_two_mul_add_one m m')
  · rintro ⟨t', ht', rfl⟩
    exact Or.inr <| Or.inr <| Or.inl ⟨m, t', hm, ht', rfl, rfl⟩

lemma BnumGraph.two_mul_add_one_iff {m t : V} (hm : 1 ≤ m) :
    BnumGraph (2 * m + 1) t ↔ ∃ t', BnumGraph m t' ∧ t = (𝟐 ^* t') ^+ 𝟏 := by
  rw [BnumGraph.case_iff]
  constructor
  · rintro (⟨h, _⟩ | ⟨h, _⟩ | ⟨m', t', _, _, h, _⟩ | ⟨m', t', _, ht', h, rfl⟩)
    · exact absurd h (two_mul_add_one_ne_zero m)
    · exact absurd h (two_mul_add_one_ne_one hm)
    · exact absurd h.symm (two_mul_ne_two_mul_add_one m' m)
    · rw [two_mul_add_one_inj h]; exact ⟨t', ht', rfl⟩
  · rintro ⟨t', ht', rfl⟩
    exact Or.inr <| Or.inr <| Or.inr ⟨m, t', hm, ht', rfl, rfl⟩

/-! ### `bnum` is a total Σ₁ function -/

section cases

/-- Every `n ≥ 2` is `2 * (n / 2)` or `2 * (n / 2) + 1` with `1 ≤ n / 2 < n`. -/
lemma two_le_cases {n : V} (h2 : 2 ≤ n) :
    1 ≤ n / 2 ∧ n / 2 < n ∧ (n = 2 * (n / 2) ∨ n = 2 * (n / 2) + 1) :=
  ⟨by simpa using div_monotone h2 2,
   div_lt_of_pos_of_one_lt (lt_of_lt_of_le Arithmetic.two_pos h2) one_lt_two,
   even_or_odd' n⟩

/-- `n = 0`, `n = 1`, or `2 ≤ n`. -/
lemma zero_one_or_two_le (n : V) : n = 0 ∨ n = 1 ∨ 2 ≤ n := by
  rcases (Arithmetic.zero_le n).eq_or_lt with h | hpos
  · exact Or.inl h.symm
  rcases (pos_iff_one_le.mp hpos).eq_or_lt with h | h1
  · exact Or.inr (Or.inl h.symm)
  · exact Or.inr (Or.inr (one_lt_iff_two_le.mp h1))

end cases

lemma bnumGraph_exists (n : V) : ∃ t, BnumGraph n t := by
  induction n using ISigma1.sigma1_order_induction with
  | hP => definability
  | ind n ih =>
    rcases zero_one_or_two_le n with rfl | rfl | h2
    · exact ⟨_, BnumGraph.zero_iff.mpr rfl⟩
    · exact ⟨_, BnumGraph.one_iff.mpr rfl⟩
    obtain ⟨hm, hlt, he | ho⟩ := two_le_cases h2
    · obtain ⟨t', ht'⟩ := ih (n / 2) hlt
      rw [he]
      exact ⟨_, (BnumGraph.two_mul_iff hm).mpr ⟨t', ht', rfl⟩⟩
    · obtain ⟨t', ht'⟩ := ih (n / 2) hlt
      rw [ho]
      exact ⟨_, (BnumGraph.two_mul_add_one_iff hm).mpr ⟨t', ht', rfl⟩⟩

lemma bnumGraph_unique (n : V) : ∀ t₁ t₂, BnumGraph n t₁ → BnumGraph n t₂ → t₁ = t₂ := by
  induction n using ISigma1.pi1_order_induction with
  | hP => definability
  | ind n ih =>
    intro t₁ t₂ h₁ h₂
    rcases zero_one_or_two_le n with rfl | rfl | h2
    · rw [BnumGraph.zero_iff] at h₁ h₂; rw [h₁, h₂]
    · rw [BnumGraph.one_iff] at h₁ h₂; rw [h₁, h₂]
    obtain ⟨hm, hlt, he | ho⟩ := two_le_cases h2
    · rw [he] at h₁ h₂
      rcases (BnumGraph.two_mul_iff hm).mp h₁ with ⟨s₁, hs₁, rfl⟩
      rcases (BnumGraph.two_mul_iff hm).mp h₂ with ⟨s₂, hs₂, rfl⟩
      rw [ih (n / 2) hlt s₁ s₂ hs₁ hs₂]
    · rw [ho] at h₁ h₂
      rcases (BnumGraph.two_mul_add_one_iff hm).mp h₁ with ⟨s₁, hs₁, rfl⟩
      rcases (BnumGraph.two_mul_add_one_iff hm).mp h₂ with ⟨s₂, hs₂, rfl⟩
      rw [ih (n / 2) hlt s₁ s₂ hs₁ hs₂]

lemma bnumGraph_existsUnique (n : V) : ∃! t, BnumGraph n t := by
  rcases bnumGraph_exists n with ⟨t, ht⟩
  exact ExistsUnique.intro t ht (fun t' h' ↦ bnumGraph_unique n t' t h' ht)

/-- The binary numeral term code of `n`. -/
noncomputable def bnum (n : V) : V := Classical.choose! (bnumGraph_existsUnique n)

lemma bnum_graph (n : V) : BnumGraph n (bnum n) := Classical.choose!_spec (bnumGraph_existsUnique n)

lemma bnum_eq_of_graph {n t : V} (h : BnumGraph n t) : bnum n = t :=
  bnumGraph_unique n _ _ (bnum_graph n) h

noncomputable def bnumGraph : 𝚺₁.Semisentence 2 := .mkSigma “t n. !bnumGraphDef.sigma n t”

instance bnum.defined : 𝚺₁-Function₁[V] bnum via bnumGraph := .mk fun v ↦ by
  simp [bnumGraph, HierarchySymbol.Semiformula.val_sigma, bnumGraph_defined.df]
  constructor
  · intro h; exact (bnum_eq_of_graph h).symm
  · intro h; rw [h]; exact bnum_graph _

instance bnum.definable : 𝚺₁-Function₁[V] bnum := bnum.defined.to_definable

instance bnum.definable' : Γ-[m + 1]-Function₁[V] bnum := bnum.definable.of_sigmaOne

/-! ### The equations -/

@[simp] lemma bnum_zero : bnum (0 : V) = 𝟎 := bnum_eq_of_graph (BnumGraph.zero_iff.mpr rfl)

@[simp] lemma bnum_one : bnum (1 : V) = 𝟏 := bnum_eq_of_graph (BnumGraph.one_iff.mpr rfl)

lemma bnum_two_mul {m : V} (hm : 1 ≤ m) : bnum (2 * m) = 𝟐 ^* bnum m :=
  bnum_eq_of_graph ((BnumGraph.two_mul_iff hm).mpr ⟨_, bnum_graph m, rfl⟩)

lemma bnum_two_mul_add_one {m : V} (hm : 1 ≤ m) : bnum (2 * m + 1) = (𝟐 ^* bnum m) ^+ 𝟏 :=
  bnum_eq_of_graph ((BnumGraph.two_mul_add_one_iff hm).mpr ⟨_, bnum_graph m, rfl⟩)

/-- The successor forms (no hypothesis), the shapes that transfer from `ℕ` by `push_cast`. -/
lemma bnum_two_mul_succ (m : V) : bnum (2 * (m + 1)) = 𝟐 ^* bnum (m + 1) :=
  bnum_two_mul le_add_self

lemma bnum_two_mul_succ_add_one (m : V) : bnum (2 * (m + 1) + 1) = (𝟐 ^* bnum (m + 1)) ^+ 𝟏 :=
  bnum_two_mul_add_one le_add_self

/-- The even case, with Foundation's internal `/ 2` and `% 2`. -/
lemma bnum_even {n : V} (h2 : 2 ≤ n) (he : n % 2 = 0) : bnum n = 𝟐 ^* bnum (n / 2) := by
  have e : 2 * (n / 2) = n := by have := div_add_mod n 2; rwa [he, add_zero] at this
  have := bnum_two_mul (two_le_cases h2).1
  rwa [e] at this

/-- The odd case. -/
lemma bnum_odd {n : V} (h2 : 2 ≤ n) (ho : n % 2 = 1) : bnum n = (𝟐 ^* bnum (n / 2)) ^+ 𝟏 := by
  have e : 2 * (n / 2) + 1 = n := by have := div_add_mod n 2; rwa [ho] at this
  have := bnum_two_mul_add_one (two_le_cases h2).1
  rwa [e] at this

/-- `bnum n` is a closed `ℒₒᵣ`-term (at every bound-variable count). -/
lemma bnum_semiterm (k n : V) : IsSemiterm ℒₒᵣ k (bnum n) := by
  induction n using ISigma1.pi1_order_induction with
  | hP => definability
  | ind n ih =>
    rcases zero_one_or_two_le n with rfl | rfl | h2
    · simp
    · simp
    obtain ⟨hm, hlt, he | ho⟩ := two_le_cases h2
    · rw [he, bnum_two_mul hm]; simp [qqMul, ih (n / 2) hlt]
    · rw [ho, bnum_two_mul_add_one hm]; simp [qqMul, qqAdd, ih (n / 2) hlt]

lemma bnum_uterm (n : V) : IsUTerm ℒₒᵣ (bnum n) := (bnum_semiterm 0 n).isUTerm

/-! ### The meta numerals -/

section metaTerms

/-- The meta term `1 + 1`. -/
noncomputable def twoT : ClosedSemiterm ℒₒᵣ 0 := ‘1 + 1’

/-- The binary numeral term of `n`: `0`, `1`, `2 · bnumT (n / 2)`, `2 · bnumT (n / 2) + 1`. -/
noncomputable def bnumT : ℕ → ClosedSemiterm ℒₒᵣ 0
  | 0 => ‘0’
  | 1 => ‘1’
  | n + 2 =>
    if (n + 2) % 2 = 0 then ‘!!twoT * !!(bnumT ((n + 2) / 2))’
    else ‘!!twoT * !!(bnumT ((n + 2) / 2)) + 1’
  decreasing_by all_goals omega

lemma bnumT_zero : bnumT 0 = ‘0’ := by rw [bnumT]
lemma bnumT_one : bnumT 1 = ‘1’ := by rw [bnumT]

lemma bnumT_even {n : ℕ} (h2 : 2 ≤ n) (he : n % 2 = 0) :
    bnumT n = ‘!!twoT * !!(bnumT (n / 2))’ := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  rw [bnumT, if_pos he]

lemma bnumT_odd {n : ℕ} (h2 : 2 ≤ n) (ho : n % 2 = 1) :
    bnumT n = ‘!!twoT * !!(bnumT (n / 2)) + 1’ := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  rw [bnumT, if_neg (by omega)]

/-! #### The code equation -/

lemma quote_closed_add (t u : ClosedSemiterm ℒₒᵣ 0) :
    (⌜(‘!!t + !!u’ : ClosedSemiterm ℒₒᵣ 0)⌝ : V) = (⌜t⌝ : V) ^+ (⌜u⌝ : V) := by
  rw [Semiterm.empty_quote_eq, Semiterm.empty_typed_quote_add]; rfl

lemma quote_closed_mul (t u : ClosedSemiterm ℒₒᵣ 0) :
    (⌜(‘!!t * !!u’ : ClosedSemiterm ℒₒᵣ 0)⌝ : V) = (⌜t⌝ : V) ^* (⌜u⌝ : V) := by
  rw [Semiterm.empty_quote_eq, Semiterm.empty_typed_quote_mul]; rfl

lemma quote_closed_zero : (⌜(‘0’ : ClosedSemiterm ℒₒᵣ 0)⌝ : V) = 𝟎 := by
  rw [Semiterm.empty_quote_eq, Semiterm.empty_typed_quote_numeral_eq_numeral]; simp

lemma quote_closed_one : (⌜(‘1’ : ClosedSemiterm ℒₒᵣ 0)⌝ : V) = 𝟏 := by
  rw [Semiterm.empty_quote_eq, Semiterm.empty_typed_quote_numeral_eq_numeral]; simp

lemma quote_twoT : (⌜twoT⌝ : V) = 𝟐 := by
  unfold twoT
  rw [show (‘1 + 1’ : ClosedSemiterm ℒₒᵣ 0) = ‘!!(‘1’ : ClosedSemiterm ℒₒᵣ 0) + !!(‘1’ : ClosedSemiterm ℒₒᵣ 0)’ from rfl,
    quote_closed_add, quote_closed_one]
  rfl

/-- **The code equation**: the code of the meta binary numeral is the internal one, in every model. -/
theorem quote_bnumT (n : ℕ) : (⌜bnumT n⌝ : V) = bnum (n : V) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | _ | k
    · rw [bnumT_zero, quote_closed_zero]; simp
    · rw [bnumT_one, quote_closed_one]; simp
    · by_cases he : (k + 1 + 1) % 2 = 0
      · obtain ⟨m, hn⟩ : ∃ m, k + 1 + 1 = 2 * (m + 1) := ⟨(k + 1 + 1) / 2 - 1, by omega⟩
        have hm : (k + 1 + 1) / 2 = m + 1 := by omega
        rw [bnumT_even (by omega) he, quote_closed_mul, quote_twoT, hm, ih (m + 1) (by omega), hn]
        push_cast
        rw [bnum_two_mul_succ]
      · obtain ⟨m, hn⟩ : ∃ m, k + 1 + 1 = 2 * (m + 1) + 1 := ⟨(k + 1 + 1) / 2 - 1, by omega⟩
        have hm : (k + 1 + 1) / 2 = m + 1 := by omega
        rw [bnumT_odd (by omega) (by omega), quote_closed_add, quote_closed_mul, quote_twoT,
          quote_closed_one, hm, ih (m + 1) (by omega), hn]
        push_cast
        rw [bnum_two_mul_succ_add_one]

/-! #### The truth equation -/

lemma val_twoT : twoT.val (s := standardModel ℕ) ![] Empty.elim = 2 := by
  unfold twoT; simp

/-- **The truth equation**: the binary numeral of `n` denotes `n` in `ℕ`. -/
theorem val_bnumT (n : ℕ) : (bnumT n).val (s := standardModel ℕ) ![] Empty.elim = n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | _ | k
    · rw [bnumT_zero]; simp
    · rw [bnumT_one]; simp
    · by_cases he : (k + 1 + 1) % 2 = 0
      · rw [bnumT_even (by omega) he]
        simp [val_twoT, ih ((k + 1 + 1) / 2) (by omega)]
        omega
      · rw [bnumT_odd (by omega) (by omega)]
        simp [val_twoT, ih ((k + 1 + 1) / 2) (by omega)]
        omega

/-! #### The length bound -/

lemma tlen_add_operator {m : ℕ} (v : Fin 2 → SyntacticSemiterm ℒₒᵣ m) :
    tlen (Semiterm.Operator.Add.add.operator v) = tlen (v 0) + tlen (v 1) + 1 := by
  simp [Semiterm.Operator.operator, Semiterm.Operator.Add.term_eq, Fin.sum_univ_two]

lemma tlen_mul_operator {m : ℕ} (v : Fin 2 → SyntacticSemiterm ℒₒᵣ m) :
    tlen (Semiterm.Operator.Mul.mul.operator v) = tlen (v 0) + tlen (v 1) + 1 := by
  simp [Semiterm.Operator.operator, Semiterm.Operator.Mul.term_eq, Fin.sum_univ_two]

lemma tlen_zero_operator {m : ℕ} :
    tlen ((Semiterm.Operator.Zero.zero : Semiterm.Const ℒₒᵣ).operator ![] : SyntacticSemiterm ℒₒᵣ m) = 1 := by
  simp [Semiterm.Operator.operator, Semiterm.Operator.Zero.term_eq]

lemma tlen_one_operator {m : ℕ} :
    tlen ((Semiterm.Operator.One.one : Semiterm.Const ℒₒᵣ).operator ![] : SyntacticSemiterm ℒₒᵣ m) = 1 := by
  simp [Semiterm.Operator.operator, Semiterm.Operator.One.term_eq]

lemma tlen_emb_closed_zero : tlen (Rew.emb (‘0’ : ClosedSemiterm ℒₒᵣ 0) : SyntacticSemiterm ℒₒᵣ 0) = 1 := by
  have e : (Rew.emb (‘0’ : ClosedSemiterm ℒₒᵣ 0) : SyntacticSemiterm ℒₒᵣ 0) = ↑(0 : ℕ) := by simp
  rw [e]
  change tlen ((Semiterm.Operator.numeral ℒₒᵣ 0).operator ![] : SyntacticSemiterm ℒₒᵣ 0) = 1
  rw [Semiterm.Operator.numeral_zero]
  exact tlen_zero_operator

lemma tlen_emb_closed_one : tlen (Rew.emb (‘1’ : ClosedSemiterm ℒₒᵣ 0) : SyntacticSemiterm ℒₒᵣ 0) = 1 := by
  have e : (Rew.emb (‘1’ : ClosedSemiterm ℒₒᵣ 0) : SyntacticSemiterm ℒₒᵣ 0) = ↑(1 : ℕ) := by simp
  rw [e]
  change tlen ((Semiterm.Operator.numeral ℒₒᵣ 1).operator ![] : SyntacticSemiterm ℒₒᵣ 0) = 1
  rw [Semiterm.Operator.numeral_one]
  exact tlen_one_operator

lemma tlen_emb_closed_add (t u : ClosedSemiterm ℒₒᵣ 0) :
    tlen (Rew.emb (‘!!t + !!u’ : ClosedSemiterm ℒₒᵣ 0) : SyntacticSemiterm ℒₒᵣ 0) =
    tlen (Rew.emb t : SyntacticSemiterm ℒₒᵣ 0) + tlen (Rew.emb u : SyntacticSemiterm ℒₒᵣ 0) + 1 := by
  rw [show (‘!!t + !!u’ : ClosedSemiterm ℒₒᵣ 0) = Semiterm.Operator.Add.add.operator ![t, u] from rfl,
    Rew.finitary2, tlen_add_operator]
  rfl

lemma tlen_emb_closed_mul (t u : ClosedSemiterm ℒₒᵣ 0) :
    tlen (Rew.emb (‘!!t * !!u’ : ClosedSemiterm ℒₒᵣ 0) : SyntacticSemiterm ℒₒᵣ 0) =
    tlen (Rew.emb t : SyntacticSemiterm ℒₒᵣ 0) + tlen (Rew.emb u : SyntacticSemiterm ℒₒᵣ 0) + 1 := by
  rw [show (‘!!t * !!u’ : ClosedSemiterm ℒₒᵣ 0) = Semiterm.Operator.Mul.mul.operator ![t, u] from rfl,
    Rew.finitary2, tlen_mul_operator]
  rfl

lemma tlen_emb_twoT : tlen (Rew.emb twoT : SyntacticSemiterm ℒₒᵣ 0) = 3 := by
  unfold twoT
  rw [show (‘1 + 1’ : ClosedSemiterm ℒₒᵣ 0) = ‘!!(‘1’ : ClosedSemiterm ℒₒᵣ 0) + !!(‘1’ : ClosedSemiterm ℒₒᵣ 0)’ from rfl,
    tlen_emb_closed_add, tlen_emb_closed_one]

/-- `2 ^ size m ≤ 2 m` for `m ≥ 1`. -/
lemma two_pow_size_le (m : ℕ) (hm : 1 ≤ m) : 2 ^ Nat.size m ≤ 2 * m := by
  have h1 : 0 < Nat.size m := Nat.size_pos.mpr hm
  have h2 : 2 ^ (Nat.size m - 1) ≤ m := Nat.lt_size.mp (Nat.sub_lt h1 Nat.one_pos)
  calc 2 ^ Nat.size m = 2 * 2 ^ (Nat.size m - 1) := by
        rw [← Nat.pow_succ']; congr 1; omega
    _ ≤ 2 * m := Nat.mul_le_mul_left 2 h2

/-- The bit length drops under halving: `size (n / 2) < size n` for `n ≥ 2`. -/
lemma size_div_two_lt (n : ℕ) (hn : 2 ≤ n) : Nat.size (n / 2) < Nat.size n := by
  rw [Nat.lt_size]
  exact le_trans (two_pow_size_le (n / 2) (by omega)) (by omega)

/-- **The length bound**: the binary numeral of `n` has `O(size n)` symbols. -/
theorem tlen_bnumT (n : ℕ) :
    tlen (Rew.emb (bnumT n) : SyntacticSemiterm ℒₒᵣ 0) ≤ 6 * Nat.size n + 1 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | _ | k
    · rw [bnumT_zero, tlen_emb_closed_zero]; omega
    · rw [bnumT_one, tlen_emb_closed_one]; omega
    · have hs := size_div_two_lt (k + 1 + 1) (by omega)
      have ih' := ih ((k + 1 + 1) / 2) (by omega)
      by_cases he : (k + 1 + 1) % 2 = 0
      · rw [bnumT_even (by omega) he, tlen_emb_closed_mul, tlen_emb_twoT]
        omega
      · rw [bnumT_odd (by omega) (by omega), tlen_emb_closed_add, tlen_emb_closed_mul, tlen_emb_twoT,
          tlen_emb_closed_one]
        omega

end metaTerms

end ArithS
