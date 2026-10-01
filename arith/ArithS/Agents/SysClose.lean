import ArithS.Agents.Subst

/-!
# ArithS.Agents.SysClose — member lookup and the system closer, on codes

Phase 2 of `SPRIME_SOURCE_OF_TRUTH.md` (2026-09-30): the two operations the evaluator's `pSys` clause
needs, both the engine's (`Program.lean`) on codes.

* **`listGet d i`** — the engine's `ProgList.get?`: the `i`-th entry of the list code `d`, as the total
  function `m + 1` ("`some m`"), `0` ("`none`") on an empty or exhausted list and on a non-list. A
  StrongFinite Δ₁ fixpoint on triples `⟪⟪d, i⟫, m⟫` (`ListGet.Phi`); the equations `listGet_cons_zero`,
  `listGet_cons_succ`, `listGet_of_not_cons` are the definition.
* **`sysCloseCode d p`** — the engine's `Prog.sysClose defs`: `pSelfIdx j ↦ pSys d j`, transparent through
  `pBot`, `pSim`, `pIte`, the branches of `pSearch` and `pTvote` (entries frozen, as in the engine); an inner
  `pSys` is a BINDER (fixed); on `pSearch k g p q` the stored template is closed by `sysCloseTemplateAt d k g`
  (`ArithS.Agents.Guard`: the member slots `#7..#12` filled with the members' descriptions AT THE NODE'S BUDGET
  `k` — every `pSearch k` budget inside the system written as the slot `#6` —, `#0..#6` kept — the engine's
  `Formula.sysClose`; Phase 2d, 2026-10-02: the consulted sentence is the verbatim closer's,
  `guardCodeB_sysCloseTemplateAt`); a list cons and every non-shape are fixed. A Δ₁ fixpoint on pairs
  `⟪x, y⟫` with the parameter `d` (`SysClose.Phi`), exactly like `substCode`; the equations
  `sysCloseCode_*` are the definition.

**Facts.** Both are Σ₁ functions (`listGetDef`, `sysCloseCodeDef`), so the evaluator's `pSys` clause is
Δ₁ in both polarities (`ArithS.Eval.Fixpoint`).
-/

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open LAct

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ### List cons -/

/-- `d` is a list cons `pCons e r`. -/
def IsCons (d : V) : Prop := ∃ e r, d = pCons e r

def isCons : 𝚺₀.Semisentence 1 := .mkSigma “d. ∃ e < d, ∃ r < d, !pConsGraph d e r”

lemma isCons_iff (d : V) : IsCons d ↔ ∃ e < d, ∃ r < d, d = pCons e r :=
  ⟨fun ⟨e, r, h⟩ ↦ ⟨e, by rw [h]; simp, r, by rw [h]; simp, h⟩, fun ⟨e, _, r, _, h⟩ ↦ ⟨e, r, h⟩⟩

instance IsCons.defined : 𝚺₀-Predicate[V] IsCons via isCons := .mk fun v ↦ by
  simp [isCons, isCons_iff]

lemma not_isCons_zero : ¬IsCons (0 : V) := fun ⟨e, r, h⟩ ↦ pCons_ne_zero e r h.symm

lemma isCons_pCons (e r : V) : IsCons (pCons e r) := ⟨e, r, rfl⟩

/-! ### `listGet`: a fixpoint on triples `⟪⟪d, i⟫, m⟫` -/

namespace ListGet

/-- `Phi C ⟪⟪d, i⟫, m⟫`: `m` is `listGet d i` given the sub-results in `C`: `0` on a non-cons; `e + 1` at
index `0` of `pCons e r`; the value at `i` in `r` at index `i + 1`. -/
def Phi (C : Set V) (pr : V) : Prop :=
  (∃ d i, ¬IsCons d ∧ pr = ⟪⟪d, i⟫, 0⟫) ∨
  (∃ e r, pr = ⟪⟪pCons e r, 0⟫, e + 1⟫) ∨
  (∃ e r i m, ⟪⟪r, i⟫, m⟫ ∈ C ∧ pr = ⟪⟪pCons e r, i + 1⟫, m⟫)

noncomputable def blueprint : Fixpoint.Blueprint 0 := ⟨.mkDelta
  (.mkSigma “pr C. ∃ di <⁺ pr, ∃ m <⁺ pr, !pairDef pr di m ∧ ∃ d <⁺ di, ∃ i <⁺ di, !pairDef di d i ∧
    ( (¬!isCons d ∧ m = 0) ∨
      (∃ e < d, ∃ r < d, !pConsGraph d e r ∧ i = 0 ∧ m = e + 1) ∨
      (∃ e < d, ∃ r < d, !pConsGraph d e r ∧ ∃ i' < i, i = i' + 1 ∧
        ∃ t, !pairDef t r i' ∧ ∃ s, !pairDef s t m ∧ s ∈ C) )”)
  (.mkPi “pr C. ∃ di <⁺ pr, ∃ m <⁺ pr, !pairDef pr di m ∧ ∃ d <⁺ di, ∃ i <⁺ di, !pairDef di d i ∧
    ( (¬!isCons d ∧ m = 0) ∨
      (∃ e < d, ∃ r < d, !pConsGraph d e r ∧ i = 0 ∧ m = e + 1) ∨
      (∃ e < d, ∃ r < d, !pConsGraph d e r ∧ ∃ i' < i, i = i' + 1 ∧
        ∀ t, !pairDef t r i' → ∀ s, !pairDef s t m → s ∈ C) )”)⟩

private lemma phi_iff (C pr : V) :
    Phi {x | x ∈ C} pr ↔
    ∃ di ≤ pr, ∃ m ≤ pr, pr = ⟪di, m⟫ ∧ ∃ d ≤ di, ∃ i ≤ di, di = ⟪d, i⟫ ∧
    ( (¬IsCons d ∧ m = 0) ∨
      (∃ e < d, ∃ r < d, d = pCons e r ∧ i = 0 ∧ m = e + 1) ∨
      (∃ e < d, ∃ r < d, d = pCons e r ∧ ∃ i' < i, i = i' + 1 ∧ ⟪⟪r, i'⟫, m⟫ ∈ C) ) := by
  constructor
  · rintro (⟨d, i, hd, rfl⟩ | ⟨e, r, rfl⟩ | ⟨e, r, i, m, h, rfl⟩)
    · exact ⟨_, by simp, _, by simp, rfl, _, by simp, _, by simp, rfl, Or.inl ⟨hd, rfl⟩⟩
    · exact ⟨_, by simp, _, by simp, rfl, _, by simp, _, by simp, rfl,
        Or.inr (Or.inl ⟨e, by simp, r, by simp, rfl, rfl, rfl⟩)⟩
    · exact ⟨_, by simp, _, by simp, rfl, _, by simp, _, by simp, rfl,
        Or.inr (Or.inr ⟨e, by simp, r, by simp, rfl, i, lt_add_one i, rfl, h⟩)⟩
  · rintro ⟨di, _, m, _, rfl, d, _, i, _, rfl, (⟨hd, rfl⟩ | ⟨e, _, r, _, rfl, rfl, rfl⟩ |
      ⟨e, _, r, _, rfl, i', _, rfl, h⟩)⟩
    · exact Or.inl ⟨d, i, hd, rfl⟩
    · exact Or.inr (Or.inl ⟨e, r, rfl⟩)
    · exact Or.inr (Or.inr ⟨e, r, i', m, h, rfl⟩)

noncomputable def construction : Fixpoint.Construction V blueprint where
  Φ := fun _ ↦ Phi
  defined := .mk <| by
    constructor
    · intro v
      simp [blueprint, HierarchySymbol.Semiformula.val_sigma]
    · intro v
      symm
      simpa [blueprint, HierarchySymbol.Semiformula.val_sigma] using phi_iff (v 1) (v 0)
  monotone := by
    rintro C C' hC _ pr (⟨d, i, hd, rfl⟩ | ⟨e, r, rfl⟩ | ⟨e, r, i, m, h, rfl⟩)
    · exact Or.inl ⟨d, i, hd, rfl⟩
    · exact Or.inr (Or.inl ⟨e, r, rfl⟩)
    · exact Or.inr (Or.inr ⟨e, r, i, m, hC h, rfl⟩)

instance : construction.StrongFinite V where
  strong_finite := by
    rintro C _ pr (⟨d, i, hd, rfl⟩ | ⟨e, r, rfl⟩ | ⟨e, r, i, m, h, rfl⟩)
    · exact Or.inl ⟨d, i, hd, rfl⟩
    · exact Or.inr (Or.inl ⟨e, r, rfl⟩)
    · exact Or.inr (Or.inr ⟨e, r, i, m, ⟨h, pair_lt_pair_left (pair_lt_pair (by simp) (lt_add_one i)) m⟩, rfl⟩)

end ListGet

/-- `ListGetGraph d i m`: `m` is `listGet d i`. -/
def ListGetGraph (d i m : V) : Prop := ListGet.construction.Fixpoint ![] ⟪⟪d, i⟫, m⟫

noncomputable def listGetGraphDef : 𝚫₁.Semisentence 3 := .mkDelta
  (.mkSigma “d i m. ∃ di <⁺ (d + i + 1)², !pairDef di d i ∧ ∃ pr <⁺ (di + m + 1)², !pairDef pr di m ∧
    !ListGet.blueprint.fixpointDefΔ₁.sigma pr”)
  (.mkPi “d i m. ∀ di <⁺ (d + i + 1)², !pairDef di d i → ∀ pr <⁺ (di + m + 1)², !pairDef pr di m →
    !ListGet.blueprint.fixpointDefΔ₁.pi pr”)

section

private lemma listGet_fixpoint_param_eq (p : Fin 0 → V) (x : V) :
    ListGet.construction.Fixpoint p x = ListGet.construction.Fixpoint ![] x := by
  rw [Subsingleton.elim p ![]]

instance listGetGraph_defined : 𝚫₁-Relation₃[V] ListGetGraph via listGetGraphDef := .mk
  ⟨by intro v
      simp [listGetGraphDef, HierarchySymbol.Semiformula.val_sigma,
        ListGet.construction.fixpoint_definedΔ₁.proper.iff', ListGet.construction.fixpoint_definedΔ₁.df]
      constructor
      · rintro h di _ rfl pr _ rfl; rwa [listGet_fixpoint_param_eq] at h ⊢
      · intro h; have := h ⟪v 0, v 1⟫ (by simp) rfl ⟪⟪v 0, v 1⟫, v 2⟫ (by simp) rfl
        rwa [listGet_fixpoint_param_eq] at this ⊢,
   by intro v
      simp [listGetGraphDef, HierarchySymbol.Semiformula.val_sigma,
        ListGet.construction.fixpoint_definedΔ₁.df, ListGetGraph]
      rw [listGet_fixpoint_param_eq]⟩

instance listGetGraph_definable : 𝚫₁-Relation₃[V] ListGetGraph := listGetGraph_defined.to_definable

instance listGetGraph_definable' : Γ-[m + 1]-Relation₃[V] ListGetGraph := listGetGraph_definable.of_deltaOne

end

lemma ListGetGraph.case_iff {d i m : V} :
    ListGetGraph d i m ↔
    (¬IsCons d ∧ m = 0) ∨
    (∃ e r, d = pCons e r ∧ i = 0 ∧ m = e + 1) ∨
    (∃ e r i', ListGetGraph r i' m ∧ d = pCons e r ∧ i = i' + 1) := by
  rw [ListGetGraph, ListGet.construction.case]
  simp only [show ListGet.construction.Φ = fun _ ↦ ListGet.Phi from rfl, ListGet.Phi, Set.mem_setOf_eq,
    pair_ext_iff]
  constructor
  · rintro (⟨d', i', hd, ⟨rfl, rfl⟩, rfl⟩ | ⟨e, r, ⟨rfl, rfl⟩, rfl⟩ | ⟨e, r, i', m', h, ⟨rfl, rfl⟩, rfl⟩)
    · exact Or.inl ⟨hd, rfl⟩
    · exact Or.inr (Or.inl ⟨e, r, rfl, rfl, rfl⟩)
    · exact Or.inr (Or.inr ⟨e, r, i', h, rfl, rfl⟩)
  · rintro (⟨hd, rfl⟩ | ⟨e, r, rfl, rfl, rfl⟩ | ⟨e, r, i', h, rfl, rfl⟩)
    · exact Or.inl ⟨d, i, hd, ⟨rfl, rfl⟩, rfl⟩
    · exact Or.inr (Or.inl ⟨e, r, ⟨rfl, rfl⟩, rfl⟩)
    · exact Or.inr (Or.inr ⟨e, r, i', m, h, ⟨rfl, rfl⟩, rfl⟩)

section inversion

attribute [local simp] pCons

lemma ListGetGraph.of_not_cons {d i m : V} (hd : ¬IsCons d) : ListGetGraph d i m ↔ m = 0 := by
  rw [ListGetGraph.case_iff]
  constructor
  · rintro (⟨_, rfl⟩ | ⟨e, r, rfl, _, _⟩ | ⟨e, r, i', _, rfl, _⟩)
    · rfl
    · exact absurd (isCons_pCons e r) hd
    · exact absurd (isCons_pCons e r) hd
  · rintro rfl; exact Or.inl ⟨hd, rfl⟩

lemma ListGetGraph.cons_zero_iff {e r m : V} : ListGetGraph (pCons e r) 0 m ↔ m = e + 1 := by
  rw [ListGetGraph.case_iff]
  constructor
  · rintro (⟨h, _⟩ | ⟨e', r', h, _, rfl⟩ | ⟨e', r', i', _, _, h⟩)
    · exact absurd (isCons_pCons e r) h
    · obtain ⟨rfl, -⟩ := pCons_inj h; rfl
    · exact absurd h (zero_ne_add_one i')
  · rintro rfl; exact Or.inr (Or.inl ⟨e, r, rfl, rfl, rfl⟩)

lemma ListGetGraph.cons_succ_iff {e r i m : V} : ListGetGraph (pCons e r) (i + 1) m ↔ ListGetGraph r i m := by
  rw [ListGetGraph.case_iff]
  constructor
  · rintro (⟨h, _⟩ | ⟨e', r', _, h, _⟩ | ⟨e', r', i', hm, h, hi⟩)
    · exact absurd (isCons_pCons e r) h
    · exact absurd h (zero_ne_add_one i).symm
    · obtain ⟨rfl, rfl⟩ := pCons_inj h
      rwa [← add_right_cancel hi] at hm
  · intro h; exact Or.inr (Or.inr ⟨e, r, i, h, rfl, rfl⟩)

end inversion

/-! ### `listGet` is a total Σ₁ function -/

lemma listGetGraph_exists (d : V) : ∀ i, ∃ m ≤ d, ListGetGraph d i m := by
  induction d using ISigma1.pi1_order_induction with
  | hP => definability
  | ind d ih =>
    intro i
    by_cases hd : IsCons d
    · obtain ⟨e, r, rfl⟩ := hd
      rcases zero_or_succ i with rfl | ⟨i', rfl⟩
      · exact ⟨e + 1, lt_iff_succ_le.mp (by simp), ListGetGraph.cons_zero_iff.mpr rfl⟩
      · obtain ⟨m, hm, h⟩ := ih r (by simp) i'
        exact ⟨m, le_trans hm (le_of_lt (by simp)), ListGetGraph.cons_succ_iff.mpr h⟩
    · exact ⟨0, by simp, (ListGetGraph.of_not_cons hd).mpr rfl⟩

lemma listGetGraph_unique (d : V) : ∀ i m₁ m₂, ListGetGraph d i m₁ → ListGetGraph d i m₂ → m₁ = m₂ := by
  induction d using ISigma1.pi1_order_induction with
  | hP => definability
  | ind d ih =>
    intro i m₁ m₂ h₁ h₂
    by_cases hd : IsCons d
    · obtain ⟨e, r, rfl⟩ := hd
      rcases zero_or_succ i with rfl | ⟨i', rfl⟩
      · rw [ListGetGraph.cons_zero_iff] at h₁ h₂; rw [h₁, h₂]
      · rw [ListGetGraph.cons_succ_iff] at h₁ h₂
        exact ih r (by simp) i' m₁ m₂ h₁ h₂
    · rw [ListGetGraph.of_not_cons hd] at h₁ h₂; rw [h₁, h₂]

lemma listGetGraph_existsUnique (d i : V) : ∃! m, ListGetGraph d i m := by
  rcases listGetGraph_exists d i with ⟨m, _, hm⟩
  exact ExistsUnique.intro m hm (fun m' h' ↦ listGetGraph_unique d i m' m h' hm)

/-- **Member lookup**: `listGet d i = m + 1` when the `i`-th entry of `d` is `m` (the engine's `some m`),
`0` otherwise (the engine's `none`). -/
noncomputable def listGet (d i : V) : V := Classical.choose! (listGetGraph_existsUnique d i)

lemma listGet_graph (d i : V) : ListGetGraph d i (listGet d i) := Classical.choose!_spec (listGetGraph_existsUnique d i)

lemma listGet_eq_of_graph {d i m : V} (h : ListGetGraph d i m) : listGet d i = m :=
  listGetGraph_unique d i _ _ (listGet_graph d i) h

noncomputable def listGetDef : 𝚺₁.Semisentence 3 := .mkSigma “m d i. !listGetGraphDef.sigma d i m”

instance listGet_defined : 𝚺₁-Function₂ (listGet : V → V → V) via listGetDef := .mk fun v ↦ by
  simp [listGetDef, HierarchySymbol.Semiformula.val_sigma, listGetGraph_defined.df]
  constructor
  · intro h; exact (listGet_eq_of_graph h).symm
  · intro h; rw [h]; exact listGet_graph _ _

instance listGet_definable : 𝚺₁-Function₂ (listGet : V → V → V) := listGet_defined.to_definable

instance listGet_definable' : Γ-[m + 1]-Function₂ (listGet : V → V → V) := listGet_definable.of_sigmaOne

lemma listGet_of_not_cons {d : V} (hd : ¬IsCons d) (i : V) : listGet d i = 0 :=
  listGet_eq_of_graph ((ListGetGraph.of_not_cons hd).mpr rfl)
@[simp] lemma listGet_nil (i : V) : listGet (pNil : V) i = 0 := listGet_of_not_cons not_isCons_zero i
@[simp] lemma listGet_cons_zero (e r : V) : listGet (pCons e r) 0 = e + 1 :=
  listGet_eq_of_graph (ListGetGraph.cons_zero_iff.mpr rfl)
@[simp] lemma listGet_cons_succ (e r i : V) : listGet (pCons e r) (i + 1) = listGet r i :=
  listGet_eq_of_graph (ListGetGraph.cons_succ_iff.mpr (listGet_graph r i))
lemma listGet_le (d i : V) : listGet d i ≤ d := by
  obtain ⟨m, hm, h⟩ := listGetGraph_exists d i
  rw [listGet_eq_of_graph h]; exact hm

/-! ### `sysCloseCode`: a fixpoint on pairs `⟪x, y⟫` with the parameter `d` -/

namespace SysClose

/-- `Phi ![d] C ⟪x, y⟫`: `y` is `x` with every `pSelfIdx j` closed to `pSys d j` (below any inner `pSys`),
given the sub-results in `C`. -/
def Phi (param : Fin 1 → V) (C : Set V) (pr : V) : Prop :=
  (∃ a, pr = ⟪pConst a, pConst a⟫) ∨
  pr = ⟪pSelf, pSelf⟫ ∨ pr = ⟪pOpp, pOpp⟫ ∨
  (∃ p p', ⟪p, p'⟫ ∈ C ∧ pr = ⟪pBot p, pBot p'⟫) ∨
  (∃ p q p' q', ⟪p, p'⟫ ∈ C ∧ ⟪q, q'⟫ ∈ C ∧ pr = ⟪pSim p q, pSim p' q'⟫) ∨
  (∃ b a p q b' p' q', ⟪b, b'⟫ ∈ C ∧ ⟪p, p'⟫ ∈ C ∧ ⟪q, q'⟫ ∈ C ∧
    pr = ⟪pIte b a p q, pIte b' a p' q'⟫) ∨
  (∃ k g p q p' q', ⟪p, p'⟫ ∈ C ∧ ⟪q, q'⟫ ∈ C ∧
    pr = ⟪pSearch k g p q, pSearch k (sysCloseTemplateAt (param 0) k g) p' q'⟫) ∨
  (∃ v θ p q p' q', ⟪p, p'⟫ ∈ C ∧ ⟪q, q'⟫ ∈ C ∧ pr = ⟪pTvote v θ p q, pTvote v θ p' q'⟫) ∨
  (∃ d' i, pr = ⟪pSys d' i, pSys d' i⟫) ∨
  (∃ j, pr = ⟪pSelfIdx j, pSys (param 0) j⟫) ∨
  (∃ e r, pr = ⟪pCons e r, pCons e r⟫) ∨
  (∃ x, ¬IsShape x ∧ pr = ⟪x, x⟫)

noncomputable def blueprint : Fixpoint.Blueprint 1 := ⟨.mkDelta
  (.mkSigma “pr C d. ∃ x <⁺ pr, ∃ y <⁺ pr, !pairDef pr x y ∧
    ( (∃ a < x, !pConstGraph x a ∧ y = x) ∨
      (!pSelfGraph x ∧ y = x) ∨
      (!pOppGraph x ∧ y = x) ∨
      (∃ p < x, !pBotGraph x p ∧ ∃ p' < y, :⟪p, p'⟫:∈ C ∧ !pBotGraph y p') ∨
      (∃ p < x, ∃ q < x, !pSimGraph x p q ∧
        ∃ p' < y, ∃ q' < y, :⟪p, p'⟫:∈ C ∧ :⟪q, q'⟫:∈ C ∧ !pSimGraph y p' q') ∨
      (∃ b < x, ∃ a < x, ∃ p < x, ∃ q < x, !pIteGraph x b a p q ∧
        ∃ b' < y, ∃ p' < y, ∃ q' < y,
          :⟪b, b'⟫:∈ C ∧ :⟪p, p'⟫:∈ C ∧ :⟪q, q'⟫:∈ C ∧ !pIteGraph y b' a p' q') ∨
      (∃ k < x, ∃ g < x, ∃ p < x, ∃ q < x, !pSearchGraph x k g p q ∧
        ∃ g', !sysCloseTemplateAtGraph g' d k g ∧ ∃ p' < y, ∃ q' < y,
          :⟪p, p'⟫:∈ C ∧ :⟪q, q'⟫:∈ C ∧ !pSearchGraph y k g' p' q') ∨
      (∃ v < x, ∃ th < x, ∃ p < x, ∃ q < x, !pTvoteGraph x v th p q ∧
        ∃ p' < y, ∃ q' < y, :⟪p, p'⟫:∈ C ∧ :⟪q, q'⟫:∈ C ∧ !pTvoteGraph y v th p' q') ∨
      (∃ d' < x, ∃ i < x, !pSysGraph x d' i ∧ y = x) ∨
      (∃ j < x, !pSelfIdxGraph x j ∧ !pSysGraph y d j) ∨
      (∃ e < x, ∃ r < x, !pConsGraph x e r ∧ y = x) ∨
      (¬!isShape x ∧ y = x) )”)
  (.mkPi “pr C d. ∃ x <⁺ pr, ∃ y <⁺ pr, !pairDef pr x y ∧
    ( (∃ a < x, !pConstGraph x a ∧ y = x) ∨
      (!pSelfGraph x ∧ y = x) ∨
      (!pOppGraph x ∧ y = x) ∨
      (∃ p < x, !pBotGraph x p ∧ ∃ p' < y, :⟪p, p'⟫:∈ C ∧ !pBotGraph y p') ∨
      (∃ p < x, ∃ q < x, !pSimGraph x p q ∧
        ∃ p' < y, ∃ q' < y, :⟪p, p'⟫:∈ C ∧ :⟪q, q'⟫:∈ C ∧ !pSimGraph y p' q') ∨
      (∃ b < x, ∃ a < x, ∃ p < x, ∃ q < x, !pIteGraph x b a p q ∧
        ∃ b' < y, ∃ p' < y, ∃ q' < y,
          :⟪b, b'⟫:∈ C ∧ :⟪p, p'⟫:∈ C ∧ :⟪q, q'⟫:∈ C ∧ !pIteGraph y b' a p' q') ∨
      (∃ k < x, ∃ g < x, ∃ p < x, ∃ q < x, !pSearchGraph x k g p q ∧
        ∀ g', !sysCloseTemplateAtGraph g' d k g → ∃ p' < y, ∃ q' < y,
          :⟪p, p'⟫:∈ C ∧ :⟪q, q'⟫:∈ C ∧ !pSearchGraph y k g' p' q') ∨
      (∃ v < x, ∃ th < x, ∃ p < x, ∃ q < x, !pTvoteGraph x v th p q ∧
        ∃ p' < y, ∃ q' < y, :⟪p, p'⟫:∈ C ∧ :⟪q, q'⟫:∈ C ∧ !pTvoteGraph y v th p' q') ∨
      (∃ d' < x, ∃ i < x, !pSysGraph x d' i ∧ y = x) ∨
      (∃ j < x, !pSelfIdxGraph x j ∧ !pSysGraph y d j) ∨
      (∃ e < x, ∃ r < x, !pConsGraph x e r ∧ y = x) ∨
      (¬!isShape x ∧ y = x) )”)⟩

private lemma phi_iff (param : Fin 1 → V) (C pr : V) :
    Phi param {x | x ∈ C} pr ↔
    ∃ x ≤ pr, ∃ y ≤ pr, pr = ⟪x, y⟫ ∧
    ( (∃ a < x, x = pConst a ∧ y = x) ∨
      (x = pSelf ∧ y = x) ∨
      (x = pOpp ∧ y = x) ∨
      (∃ p < x, x = pBot p ∧ ∃ p' < y, ⟪p, p'⟫ ∈ C ∧ y = pBot p') ∨
      (∃ p < x, ∃ q < x, x = pSim p q ∧
        ∃ p' < y, ∃ q' < y, ⟪p, p'⟫ ∈ C ∧ ⟪q, q'⟫ ∈ C ∧ y = pSim p' q') ∨
      (∃ b < x, ∃ a < x, ∃ p < x, ∃ q < x, x = pIte b a p q ∧
        ∃ b' < y, ∃ p' < y, ∃ q' < y,
          ⟪b, b'⟫ ∈ C ∧ ⟪p, p'⟫ ∈ C ∧ ⟪q, q'⟫ ∈ C ∧ y = pIte b' a p' q') ∨
      (∃ k < x, ∃ g < x, ∃ p < x, ∃ q < x, x = pSearch k g p q ∧
        ∃ p' < y, ∃ q' < y,
          ⟪p, p'⟫ ∈ C ∧ ⟪q, q'⟫ ∈ C ∧ y = pSearch k (sysCloseTemplateAt (param 0) k g) p' q') ∨
      (∃ v < x, ∃ θ < x, ∃ p < x, ∃ q < x, x = pTvote v θ p q ∧
        ∃ p' < y, ∃ q' < y, ⟪p, p'⟫ ∈ C ∧ ⟪q, q'⟫ ∈ C ∧ y = pTvote v θ p' q') ∨
      (∃ d' < x, ∃ i < x, x = pSys d' i ∧ y = x) ∨
      (∃ j < x, x = pSelfIdx j ∧ y = pSys (param 0) j) ∨
      (∃ e < x, ∃ r < x, x = pCons e r ∧ y = x) ∨
      (¬IsShape x ∧ y = x) ) := by
  constructor
  · rintro (⟨a, rfl⟩ | rfl | rfl | ⟨p, p', h, rfl⟩ | ⟨p, q, p', q', hp, hq, rfl⟩ |
      ⟨b, a, p, q, b', p', q', hb, hp, hq, rfl⟩ | ⟨k, g, p, q, p', q', hp, hq, rfl⟩ |
      ⟨v, θ, p, q, p', q', hp, hq, rfl⟩ | ⟨d', i, rfl⟩ | ⟨j, rfl⟩ | ⟨e, r, rfl⟩ | ⟨x, hx, rfl⟩)
    · exact ⟨_, by simp, _, by simp, rfl, Or.inl ⟨a, by simp, rfl, rfl⟩⟩
    · exact ⟨_, by simp, _, by simp, rfl, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
    · exact ⟨_, by simp, _, by simp, rfl, Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩
    · exact ⟨_, by simp, _, by simp, rfl, Or.inr (Or.inr (Or.inr (Or.inl
        ⟨p, by simp, rfl, p', by simp, h, rfl⟩)))⟩
    · exact ⟨_, by simp, _, by simp, rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨p, by simp, q, by simp, rfl, p', by simp, q', by simp, hp, hq, rfl⟩))))⟩
    · exact ⟨_, by simp, _, by simp, rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨b, by simp, a, by simp, p, by simp, q, by simp, rfl, b', by simp,
          p', by simp, q', by simp, hb, hp, hq, rfl⟩)))))⟩
    · exact ⟨_, by simp, _, by simp, rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨k, by simp, g, by simp, p, by simp, q, by simp, rfl,
          p', by simp, q', by simp, hp, hq, rfl⟩))))))⟩
    · exact ⟨_, by simp, _, by simp, rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨v, by simp, θ, by simp, p, by simp, q, by simp, rfl,
          p', by simp, q', by simp, hp, hq, rfl⟩)))))))⟩
    · exact ⟨_, by simp, _, by simp, rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨d', by simp, i, by simp, rfl, rfl⟩))))))))⟩
    · exact ⟨_, by simp, _, by simp, rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨j, by simp, rfl, rfl⟩)))))))))⟩
    · exact ⟨_, by simp, _, by simp, rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨e, by simp, r, by simp, rfl, rfl⟩))))))))))⟩
    · exact ⟨_, by simp, _, by simp, rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨hx, rfl⟩))))))))))⟩
  · rintro ⟨x, _, y, _, rfl, (⟨a, _, rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨p, _, rfl, p', _, h, rfl⟩ | ⟨p, _, q, _, rfl, p', _, q', _, hp, hq, rfl⟩ |
      ⟨b, _, a, _, p, _, q, _, rfl, b', _, p', _, q', _, hb, hp, hq, rfl⟩ |
      ⟨k, _, g, _, p, _, q, _, rfl, p', _, q', _, hp, hq, rfl⟩ |
      ⟨v, _, θ, _, p, _, q, _, rfl, p', _, q', _, hp, hq, rfl⟩ |
      ⟨d', _, i, _, rfl, rfl⟩ | ⟨j, _, rfl, rfl⟩ | ⟨e, _, r, _, rfl, rfl⟩ | ⟨hx, hyx⟩)⟩
    · exact Or.inl ⟨a, rfl⟩
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨p, p', h, rfl⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, q, p', q', hp, hq, rfl⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨b, a, p, q, b', p', q', hb, hp, hq, rfl⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨k, g, p, q, p', q', hp, hq, rfl⟩))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨v, θ, p, q, p', q', hp, hq, rfl⟩)))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨d', i, rfl⟩))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨j, rfl⟩)))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨e, r, rfl⟩))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨x, hx, by rw [hyx]⟩))))))))))

noncomputable def construction : Fixpoint.Construction V blueprint where
  Φ := Phi
  defined := .mk <| by
    constructor
    · intro v
      simp [blueprint, HierarchySymbol.Semiformula.val_sigma, sysCloseTemplateAt.defined.df]
    · intro v
      symm
      simpa [blueprint, HierarchySymbol.Semiformula.val_sigma, sysCloseTemplateAt.defined.df,
        pSelfGraph, pOppGraph, pSelf, pOpp, lt_and_eq_succ_iff]
        using phi_iff (fun i ↦ v i.succ.succ) (v 1) (v 0)
  monotone := by
    rintro C C' hC param pr (⟨a, rfl⟩ | rfl | rfl | ⟨p, p', h, rfl⟩ | ⟨p, q, p', q', hp, hq, rfl⟩ |
      ⟨b, a, p, q, b', p', q', hb, hp, hq, rfl⟩ | ⟨k, g, p, q, p', q', hp, hq, rfl⟩ |
      ⟨v, θ, p, q, p', q', hp, hq, rfl⟩ | ⟨d', i, rfl⟩ | ⟨j, rfl⟩ | ⟨e, r, rfl⟩ | ⟨x, hx, rfl⟩)
    · exact Or.inl ⟨a, rfl⟩
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨p, p', hC h, rfl⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, q, p', q', hC hp, hC hq, rfl⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨b, a, p, q, b', p', q', hC hb, hC hp, hC hq, rfl⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨k, g, p, q, p', q', hC hp, hC hq, rfl⟩))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨v, θ, p, q, p', q', hC hp, hC hq, rfl⟩)))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨d', i, rfl⟩))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨j, rfl⟩)))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨e, r, rfl⟩))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨x, hx, rfl⟩))))))))))

instance : construction.StrongFinite V where
  strong_finite := by
    rintro C param pr (⟨a, rfl⟩ | rfl | rfl | ⟨p, p', h, rfl⟩ | ⟨p, q, p', q', hp, hq, rfl⟩ |
      ⟨b, a, p, q, b', p', q', hb, hp, hq, rfl⟩ | ⟨k, g, p, q, p', q', hp, hq, rfl⟩ |
      ⟨v, θ, p, q, p', q', hp, hq, rfl⟩ | ⟨d', i, rfl⟩ | ⟨j, rfl⟩ | ⟨e, r, rfl⟩ | ⟨x, hx, rfl⟩)
    · exact Or.inl ⟨a, rfl⟩
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨p, p', ⟨h, pair_lt_pair (by simp) (by simp)⟩, rfl⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, q, p', q',
        ⟨hp, pair_lt_pair (by simp) (by simp)⟩, ⟨hq, pair_lt_pair (by simp) (by simp)⟩, rfl⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨b, a, p, q, b', p', q',
        ⟨hb, pair_lt_pair (by simp) (by simp)⟩, ⟨hp, pair_lt_pair (by simp) (by simp)⟩,
        ⟨hq, pair_lt_pair (by simp) (by simp)⟩, rfl⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨k, g, p, q, p', q',
        ⟨hp, pair_lt_pair (by simp) (by simp)⟩, ⟨hq, pair_lt_pair (by simp) (by simp)⟩, rfl⟩))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨v, θ, p, q, p', q',
        ⟨hp, pair_lt_pair (by simp) (by simp)⟩, ⟨hq, pair_lt_pair (by simp) (by simp)⟩, rfl⟩)))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨d', i, rfl⟩))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨j, rfl⟩)))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨e, r, rfl⟩))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨x, hx, rfl⟩))))))))))

end SysClose

/-- `SysCloseGraph d x y`: `y` is `x` with every `pSelfIdx j` closed to `pSys d j`. -/
def SysCloseGraph (d x y : V) : Prop := SysClose.construction.Fixpoint ![d] ⟪x, y⟫

noncomputable def sysCloseGraphDef : 𝚫₁.Semisentence 3 := .mkDelta
  (.mkSigma “d x y. ∃ pr <⁺ (x + y + 1)², !pairDef pr x y ∧ !SysClose.blueprint.fixpointDefΔ₁.sigma pr d”)
  (.mkPi “d x y. ∀ pr <⁺ (x + y + 1)², !pairDef pr x y → !SysClose.blueprint.fixpointDefΔ₁.pi pr d”)

private lemma sysClose_param_eq (v : Fin 2 → V) : (fun i ↦ v i.succ) = ![v 1] := by
  funext i; fin_cases i; rfl

private lemma param1_eq (a : V) : (fun _ : Fin 1 ↦ a) = ![a] := by
  funext i; fin_cases i; rfl

instance sysCloseGraph_defined : 𝚫₁-Relation₃[V] SysCloseGraph via sysCloseGraphDef := .mk
  ⟨by intro v
      simp [sysCloseGraphDef, HierarchySymbol.Semiformula.val_sigma,
        SysClose.construction.fixpoint_definedΔ₁.proper.iff', SysClose.construction.fixpoint_definedΔ₁.df]
      constructor
      · rintro h x _ rfl; simpa [sysClose_param_eq] using h
      · intro h; have := h ⟪v 1, v 2⟫ (by simp) rfl; simpa [sysClose_param_eq] using this,
   by intro v
      simp [sysCloseGraphDef, HierarchySymbol.Semiformula.val_sigma,
        SysClose.construction.fixpoint_definedΔ₁.df, SysCloseGraph, param1_eq]⟩

instance sysCloseGraph_definable : 𝚫₁-Relation₃[V] SysCloseGraph := sysCloseGraph_defined.to_definable

instance sysCloseGraph_definable' : Γ-[m + 1]-Relation₃[V] SysCloseGraph :=
  sysCloseGraph_definable.of_deltaOne

lemma SysCloseGraph.case_iff {d x y : V} :
    SysCloseGraph d x y ↔
    (∃ a, x = pConst a ∧ y = pConst a) ∨
    (x = pSelf ∧ y = pSelf) ∨ (x = pOpp ∧ y = pOpp) ∨
    (∃ p p', SysCloseGraph d p p' ∧ x = pBot p ∧ y = pBot p') ∨
    (∃ p q p' q', SysCloseGraph d p p' ∧ SysCloseGraph d q q' ∧ x = pSim p q ∧ y = pSim p' q') ∨
    (∃ b a p q b' p' q', SysCloseGraph d b b' ∧ SysCloseGraph d p p' ∧ SysCloseGraph d q q' ∧
      x = pIte b a p q ∧ y = pIte b' a p' q') ∨
    (∃ k g p q p' q', SysCloseGraph d p p' ∧ SysCloseGraph d q q' ∧
      x = pSearch k g p q ∧ y = pSearch k (sysCloseTemplateAt d k g) p' q') ∨
    (∃ v θ p q p' q', SysCloseGraph d p p' ∧ SysCloseGraph d q q' ∧
      x = pTvote v θ p q ∧ y = pTvote v θ p' q') ∨
    (∃ d' i, x = pSys d' i ∧ y = pSys d' i) ∨
    (∃ j, x = pSelfIdx j ∧ y = pSys d j) ∨
    (∃ e r, x = pCons e r ∧ y = pCons e r) ∨
    (¬IsShape y ∧ x = y) :=
  Iff.trans SysClose.construction.case (by simp [SysClose.construction, SysClose.Phi, SysCloseGraph])

section inversion

attribute [local simp] pConst pSelf pOpp pBot pSim pIte pSearch pTvote pSys pSelfIdx pCons IsShape

lemma SysCloseGraph.const_iff {d a y : V} : SysCloseGraph d (pConst a) y ↔ y = pConst a := by
  rw [SysCloseGraph.case_iff]; simp
  intro h₀ _ _ _ _ _ _ _ _ _ _ h; exact absurd h.symm (h₀ a)
lemma SysCloseGraph.self_iff {d y : V} : SysCloseGraph d pSelf y ↔ y = pSelf := by
  rw [SysCloseGraph.case_iff]; simp
  intro _ h₁ _ _ _ _ _ _ _ _ _ h; exact absurd h.symm h₁
lemma SysCloseGraph.opp_iff {d y : V} : SysCloseGraph d pOpp y ↔ y = pOpp := by
  rw [SysCloseGraph.case_iff]; simp
  intro _ _ h₂ _ _ _ _ _ _ _ _ h; exact absurd h.symm h₂
lemma SysCloseGraph.bot_iff {d p y : V} : SysCloseGraph d (pBot p) y ↔ ∃ p', SysCloseGraph d p p' ∧ y = pBot p' := by
  rw [SysCloseGraph.case_iff]; simp
  intro _ _ _ h₃ _ _ _ _ _ _ _ h; exact absurd h.symm (h₃ p)
lemma SysCloseGraph.sim_iff {d p q y : V} :
    SysCloseGraph d (pSim p q) y ↔
    ∃ p' q', SysCloseGraph d p p' ∧ SysCloseGraph d q q' ∧ y = pSim p' q' := by
  rw [SysCloseGraph.case_iff]; simp
  intro _ _ _ _ h₄ _ _ _ _ _ _ h; exact absurd h.symm (h₄ p q)
lemma SysCloseGraph.ite_iff {d b a p q y : V} :
    SysCloseGraph d (pIte b a p q) y ↔
    ∃ b' p' q', SysCloseGraph d b b' ∧ SysCloseGraph d p p' ∧ SysCloseGraph d q q' ∧ y = pIte b' a p' q' := by
  rw [SysCloseGraph.case_iff]; simp
  intro _ _ _ _ _ h₅ _ _ _ _ _ h; exact absurd h.symm (h₅ b a p q)
lemma SysCloseGraph.search_iff {d k g p q y : V} :
    SysCloseGraph d (pSearch k g p q) y ↔
    ∃ p' q', SysCloseGraph d p p' ∧ SysCloseGraph d q q' ∧ y = pSearch k (sysCloseTemplateAt d k g) p' q' := by
  rw [SysCloseGraph.case_iff]; simp
  intro _ _ _ _ _ _ h₆ _ _ _ _ h; exact absurd h.symm (h₆ k g p q)
lemma SysCloseGraph.tvote_iff {d v θ p q y : V} :
    SysCloseGraph d (pTvote v θ p q) y ↔
    ∃ p' q', SysCloseGraph d p p' ∧ SysCloseGraph d q q' ∧ y = pTvote v θ p' q' := by
  rw [SysCloseGraph.case_iff]; simp
  intro _ _ _ _ _ _ _ h₇ _ _ _ h; exact absurd h.symm (h₇ v θ p q)
lemma SysCloseGraph.sys_iff {d d' i y : V} : SysCloseGraph d (pSys d' i) y ↔ y = pSys d' i := by
  rw [SysCloseGraph.case_iff]; simp
  intro _ _ _ _ _ _ _ _ h₈ _ _ h; exact absurd h.symm (h₈ d' i)
lemma SysCloseGraph.selfIdx_iff {d j y : V} : SysCloseGraph d (pSelfIdx j) y ↔ y = pSys d j := by
  rw [SysCloseGraph.case_iff]; simp
  intro _ _ _ _ _ _ _ _ _ h₉ _ h; exact absurd h.symm (h₉ j)
lemma SysCloseGraph.cons_iff {d e r y : V} : SysCloseGraph d (pCons e r) y ↔ y = pCons e r := by
  rw [SysCloseGraph.case_iff]; simp
  intro _ _ _ _ _ _ _ _ _ _ h₁₀ h; exact absurd h.symm (h₁₀ e r)
lemma SysCloseGraph.of_not_shape {d x y : V} (hx : ¬IsShape x) : SysCloseGraph d x y ↔ y = x := by
  rw [SysCloseGraph.case_iff]
  constructor
  · rintro (⟨a, rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨p, p', _, rfl, _⟩ | ⟨p, q, p', q', _, _, rfl, _⟩ |
      ⟨b, a, p, q, b', p', q', _, _, _, rfl, _⟩ | ⟨k, g, p, q, p', q', _, _, rfl, _⟩ |
      ⟨v, θ, p, q, p', q', _, _, rfl, _⟩ | ⟨d', i, rfl, _⟩ | ⟨j, rfl, _⟩ | ⟨e, r, rfl, _⟩ | ⟨_, h⟩)
    · exact absurd (IsShape.const a) hx
    · exact absurd IsShape.self hx
    · exact absurd IsShape.opp hx
    · exact absurd (IsShape.bot p) hx
    · exact absurd (IsShape.sim p q) hx
    · exact absurd (IsShape.ite b a p q) hx
    · exact absurd (IsShape.search k g p q) hx
    · exact absurd (IsShape.tvote v θ p q) hx
    · exact absurd (IsShape.sys d' i) hx
    · exact absurd (IsShape.selfIdx j) hx
    · exact absurd (IsShape.cons e r) hx
    · exact h.symm
  · rintro rfl
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨hx, rfl⟩))))))))))

end inversion

/-! ### `sysCloseCode` is a total Σ₁ function -/

lemma sysCloseGraph_exists (d x : V) : ∃ y, SysCloseGraph d x y := by
  induction x using ISigma1.sigma1_order_induction with
  | hP => definability
  | ind x ih =>
    by_cases hx : IsShape x
    · rcases hx with ⟨a, rfl⟩ | rfl | rfl | ⟨p, rfl⟩ | ⟨p, q, rfl⟩ | ⟨b, a, p, q, rfl⟩ | ⟨k, g, p, q, rfl⟩ |
        ⟨v, θ, p, q, rfl⟩ | ⟨d', i, rfl⟩ | ⟨j, rfl⟩ | ⟨e, r, rfl⟩
      · exact ⟨_, SysCloseGraph.const_iff.mpr rfl⟩
      · exact ⟨_, SysCloseGraph.self_iff.mpr rfl⟩
      · exact ⟨_, SysCloseGraph.opp_iff.mpr rfl⟩
      · obtain ⟨p', hp⟩ := ih p (by simp)
        exact ⟨_, SysCloseGraph.bot_iff.mpr ⟨p', hp, rfl⟩⟩
      · obtain ⟨p', hp⟩ := ih p (by simp); obtain ⟨q', hq⟩ := ih q (by simp)
        exact ⟨_, SysCloseGraph.sim_iff.mpr ⟨p', q', hp, hq, rfl⟩⟩
      · obtain ⟨b', hb⟩ := ih b (by simp); obtain ⟨p', hp⟩ := ih p (by simp)
        obtain ⟨q', hq⟩ := ih q (by simp)
        exact ⟨_, SysCloseGraph.ite_iff.mpr ⟨b', p', q', hb, hp, hq, rfl⟩⟩
      · obtain ⟨p', hp⟩ := ih p (by simp); obtain ⟨q', hq⟩ := ih q (by simp)
        exact ⟨_, SysCloseGraph.search_iff.mpr ⟨p', q', hp, hq, rfl⟩⟩
      · obtain ⟨p', hp⟩ := ih p (by simp); obtain ⟨q', hq⟩ := ih q (by simp)
        exact ⟨_, SysCloseGraph.tvote_iff.mpr ⟨p', q', hp, hq, rfl⟩⟩
      · exact ⟨_, SysCloseGraph.sys_iff.mpr rfl⟩
      · exact ⟨_, SysCloseGraph.selfIdx_iff.mpr rfl⟩
      · exact ⟨_, SysCloseGraph.cons_iff.mpr rfl⟩
    · exact ⟨x, (SysCloseGraph.of_not_shape hx).mpr rfl⟩

lemma sysCloseGraph_unique (d x : V) :
    ∀ y₁ y₂, SysCloseGraph d x y₁ → SysCloseGraph d x y₂ → y₁ = y₂ := by
  induction x using ISigma1.pi1_order_induction with
  | hP => definability
  | ind x ih =>
    intro y₁ y₂ h₁ h₂
    by_cases hx : IsShape x
    · rcases hx with ⟨a, rfl⟩ | rfl | rfl | ⟨p, rfl⟩ | ⟨p, q, rfl⟩ | ⟨b, a, p, q, rfl⟩ | ⟨k, g, p, q, rfl⟩ |
        ⟨v, θ, p, q, rfl⟩ | ⟨d', i, rfl⟩ | ⟨j, rfl⟩ | ⟨e, r, rfl⟩
      · rw [SysCloseGraph.const_iff] at h₁ h₂; rw [h₁, h₂]
      · rw [SysCloseGraph.self_iff] at h₁ h₂; rw [h₁, h₂]
      · rw [SysCloseGraph.opp_iff] at h₁ h₂; rw [h₁, h₂]
      · rcases SysCloseGraph.bot_iff.mp h₁ with ⟨p₁, hp₁, rfl⟩
        rcases SysCloseGraph.bot_iff.mp h₂ with ⟨p₂, hp₂, rfl⟩
        rw [ih p (by simp) _ _ hp₁ hp₂]
      · rcases SysCloseGraph.sim_iff.mp h₁ with ⟨p₁, q₁, hp₁, hq₁, rfl⟩
        rcases SysCloseGraph.sim_iff.mp h₂ with ⟨p₂, q₂, hp₂, hq₂, rfl⟩
        rw [ih p (by simp) _ _ hp₁ hp₂, ih q (by simp) _ _ hq₁ hq₂]
      · rcases SysCloseGraph.ite_iff.mp h₁ with ⟨b₁, p₁, q₁, hb₁, hp₁, hq₁, rfl⟩
        rcases SysCloseGraph.ite_iff.mp h₂ with ⟨b₂, p₂, q₂, hb₂, hp₂, hq₂, rfl⟩
        rw [ih b (by simp) _ _ hb₁ hb₂, ih p (by simp) _ _ hp₁ hp₂, ih q (by simp) _ _ hq₁ hq₂]
      · rcases SysCloseGraph.search_iff.mp h₁ with ⟨p₁, q₁, hp₁, hq₁, rfl⟩
        rcases SysCloseGraph.search_iff.mp h₂ with ⟨p₂, q₂, hp₂, hq₂, rfl⟩
        rw [ih p (by simp) _ _ hp₁ hp₂, ih q (by simp) _ _ hq₁ hq₂]
      · rcases SysCloseGraph.tvote_iff.mp h₁ with ⟨p₁, q₁, hp₁, hq₁, rfl⟩
        rcases SysCloseGraph.tvote_iff.mp h₂ with ⟨p₂, q₂, hp₂, hq₂, rfl⟩
        rw [ih p (by simp) _ _ hp₁ hp₂, ih q (by simp) _ _ hq₁ hq₂]
      · rw [SysCloseGraph.sys_iff] at h₁ h₂; rw [h₁, h₂]
      · rw [SysCloseGraph.selfIdx_iff] at h₁ h₂; rw [h₁, h₂]
      · rw [SysCloseGraph.cons_iff] at h₁ h₂; rw [h₁, h₂]
    · rw [SysCloseGraph.of_not_shape hx] at h₁ h₂; rw [h₁, h₂]

lemma sysCloseGraph_existsUnique (d x : V) : ∃! y, SysCloseGraph d x y := by
  rcases sysCloseGraph_exists d x with ⟨y, hy⟩
  exact ExistsUnique.intro y hy (fun y' h' ↦ sysCloseGraph_unique d x y' y h' hy)

/-- **The system closer**: `pSelfIdx j ↦ pSys d j` below every binder — the engine's `Prog.sysClose defs`. -/
noncomputable def sysCloseCode (d x : V) : V := Classical.choose! (sysCloseGraph_existsUnique d x)

lemma sysCloseCode_graph (d x : V) : SysCloseGraph d x (sysCloseCode d x) :=
  Classical.choose!_spec (sysCloseGraph_existsUnique d x)

lemma sysCloseCode_eq_of_graph {d x y : V} (h : SysCloseGraph d x y) : sysCloseCode d x = y :=
  sysCloseGraph_unique d x _ _ (sysCloseCode_graph d x) h

noncomputable def sysCloseCodeDef : 𝚺₁.Semisentence 3 := .mkSigma “y d x. !sysCloseGraphDef.sigma d x y”

instance sysCloseCode_defined : 𝚺₁-Function₂ (sysCloseCode : V → V → V) via sysCloseCodeDef := .mk fun v ↦ by
  simp [sysCloseCodeDef, HierarchySymbol.Semiformula.val_sigma, sysCloseGraph_defined.df]
  constructor
  · intro h; exact (sysCloseCode_eq_of_graph h).symm
  · intro h; rw [h]; exact sysCloseCode_graph _ _

instance sysCloseCode_definable : 𝚺₁-Function₂ (sysCloseCode : V → V → V) := sysCloseCode_defined.to_definable

instance sysCloseCode_definable' : Γ-[m + 1]-Function₂ (sysCloseCode : V → V → V) :=
  sysCloseCode_definable.of_sigmaOne

@[simp] lemma sysCloseCode_const (d a : V) : sysCloseCode d (pConst a) = pConst a :=
  sysCloseCode_eq_of_graph (SysCloseGraph.const_iff.mpr rfl)
@[simp] lemma sysCloseCode_self (d : V) : sysCloseCode d (pSelf : V) = pSelf :=
  sysCloseCode_eq_of_graph (SysCloseGraph.self_iff.mpr rfl)
@[simp] lemma sysCloseCode_opp (d : V) : sysCloseCode d (pOpp : V) = pOpp :=
  sysCloseCode_eq_of_graph (SysCloseGraph.opp_iff.mpr rfl)
/-- Transparent through `pBot` (the probes of a system's members live under `.bot`). -/
@[simp] lemma sysCloseCode_bot (d p : V) : sysCloseCode d (pBot p) = pBot (sysCloseCode d p) :=
  sysCloseCode_eq_of_graph (SysCloseGraph.bot_iff.mpr ⟨_, sysCloseCode_graph d p, rfl⟩)
@[simp] lemma sysCloseCode_sim (d p q : V) :
    sysCloseCode d (pSim p q) = pSim (sysCloseCode d p) (sysCloseCode d q) :=
  sysCloseCode_eq_of_graph (SysCloseGraph.sim_iff.mpr ⟨_, _, sysCloseCode_graph d p, sysCloseCode_graph d q, rfl⟩)
@[simp] lemma sysCloseCode_ite (d b a p q : V) :
    sysCloseCode d (pIte b a p q) = pIte (sysCloseCode d b) a (sysCloseCode d p) (sysCloseCode d q) :=
  sysCloseCode_eq_of_graph (SysCloseGraph.ite_iff.mpr
    ⟨_, _, _, sysCloseCode_graph d b, sysCloseCode_graph d p, sysCloseCode_graph d q, rfl⟩)
/-- The stored template is closed by `sysCloseTemplateAt` AT THE NODE'S OWN BUDGET `k` (the member slots filled
with the members' descriptions, the budget `k` abstracted into the slot `#6`; the identity on every
seven-variable template, `sysCloseTemplateAt_of_template₇`). The sentence the closed node consults is the one
the verbatim closer `sysCloseTemplate` gives (`guardCodeB_sysCloseTemplateAt`). -/
@[simp] lemma sysCloseCode_search (d k g p q : V) :
    sysCloseCode d (pSearch k g p q) = pSearch k (sysCloseTemplateAt d k g) (sysCloseCode d p) (sysCloseCode d q) :=
  sysCloseCode_eq_of_graph (SysCloseGraph.search_iff.mpr ⟨_, _, sysCloseCode_graph d p, sysCloseCode_graph d q, rfl⟩)
/-- The vote's entries are frozen (the engine's `sysClose` on `.tvote`). -/
@[simp] lemma sysCloseCode_tvote (d v θ p q : V) :
    sysCloseCode d (pTvote v θ p q) = pTvote v θ (sysCloseCode d p) (sysCloseCode d q) :=
  sysCloseCode_eq_of_graph (SysCloseGraph.tvote_iff.mpr ⟨_, _, sysCloseCode_graph d p, sysCloseCode_graph d q, rfl⟩)
/-- An inner system is a BINDER (shadowing). -/
@[simp] lemma sysCloseCode_sys (d d' i : V) : sysCloseCode d (pSys d' i) = pSys d' i :=
  sysCloseCode_eq_of_graph (SysCloseGraph.sys_iff.mpr rfl)
/-- The closer itself. -/
@[simp] lemma sysCloseCode_selfIdx (d j : V) : sysCloseCode d (pSelfIdx j) = pSys d j :=
  sysCloseCode_eq_of_graph (SysCloseGraph.selfIdx_iff.mpr rfl)
@[simp] lemma sysCloseCode_cons (d e r : V) : sysCloseCode d (pCons e r) = pCons e r :=
  sysCloseCode_eq_of_graph (SysCloseGraph.cons_iff.mpr rfl)
lemma sysCloseCode_of_not_shape {d x : V} (hx : ¬IsShape x) : sysCloseCode d x = x :=
  sysCloseCode_eq_of_graph ((SysCloseGraph.of_not_shape hx).mpr rfl)

end ArithS
