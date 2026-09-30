import ArithS.Agents.BinNumeral

/-!
# ArithS.CodeTerm — programs described by TERMS over the polynomial pairing

Roadmap M4, item U0 (`M4_BOUNDED_HBL/BRIEF.md` §2). A program `x` used to enter a guard
sentence as the binary numeral `binNumeral (canonical x)` of its WHOLE code; the numeral of
`pSearch k g p q` is not the numeral of `k` inside any fixed term, so a searcher's guard was
the `k`-instance of NO formula. Since the codes are built on the term-expressible pairing
`ppair x y = (x + y)² + y` (`ArithS.Prog`), a program can instead be described by the
STRUCTURAL TERM of its code, with the budget `k` and the template code `g` as binary-numeral
leaves:

* `ppairTerm s t := ((s ^+ t) ^* (s ^+ t)) ^+ t` on term codes (the term of `ppair`);
* `codeTerm : V → V` (a Σ₁ function, the graph of a StrongFinite fixpoint on pairs `⟪x, t⟫`
  exactly like `revalue`): `codeTerm (pConst a) = ppairTerm (binNumeral 0) (binNumeral a) ^+ (𝟏 : V)`, …,
  `codeTerm (pSearch k g p q) = ppairTerm (binNumeral 6) (ppairTerm (binNumeral k) (ppairTerm (binNumeral g)
  (ppairTerm (codeTerm p) (codeTerm q)))) ^+ (𝟏 : V)`, and `codeTerm x = binNumeral x` on non-shapes (total);
  `codeTerm x` is a closed `ℒₒᵣ`-term code;
* the meta twin `codeTermMeta : ℕ → ClosedSemiterm ℒₒᵣ 0` (the same recursion on the syntax, via
  the inductive graph `CodeTermMetaGraph`), with the code equation `⌜codeTermMeta x⌝ = codeTerm x` in every
  model, the truth equation `val (codeTermMeta x) = x` in `ℕ` (the term DENOTES the code — this is
  where `ppair` being a term pays off), `lMap`-invariance, and the length bounds: the exact
  `termLenMeta (ppairTermMeta s t) = 2 · termLenMeta s + 3 · termLenMeta t + 4` per pairing (upper bounds for every shape
  in terms of the leaves) and the lower bound `size x ≤ termLenMeta (codeTermMeta x)`.

**Reading guide.** Definition: the clauses `CodeTerm.Phi` and §The equations (`codeTerm_const`, …, `codeTerm_search`), plus the meta twin `codeTermMeta` with its code, truth and length equations (§The meta terms). Foundation plumbing: the blueprint, the construction and the `defined` instances — skip on first reading.
-/

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ### The pairing on term codes -/

/-- The term code of `(s + t) * (s + t) + t`. -/
noncomputable def ppairTerm (s t : V) : V := ((s ^+ t) ^* (s ^+ t)) ^+ t

def ppairTermGraph : 𝚺₁.Semisentence 3 :=
  .mkSigma “r s t. ∃ st, !qqAddGraph st s t ∧ ∃ sq, !qqMulGraph sq st st ∧ !qqAddGraph r sq t”

instance ppairTerm.defined : 𝚺₁-Function₂ (ppairTerm : V → V → V) via ppairTermGraph := .mk fun v ↦ by
  simp [ppairTermGraph, ppairTerm]

@[simp] lemma lt_ppairTerm_left (s t : V) : s < ppairTerm s t :=
  lt_trans (lt_qqAdd_left s t) (lt_trans (lt_qqMul_left _ _) (lt_qqAdd_left _ _))

@[simp] lemma lt_ppairTerm_right (s t : V) : t < ppairTerm s t := lt_qqAdd_right _ _

lemma lt_ppairTerm_succ_left (s t : V) : s < ppairTerm s t ^+ (𝟏 : V) :=
  lt_trans (lt_ppairTerm_left s t) (lt_qqAdd_left _ _)

lemma lt_ppairTerm_succ_right (s t : V) : t < ppairTerm s t ^+ (𝟏 : V) :=
  lt_trans (lt_ppairTerm_right s t) (lt_qqAdd_left _ _)

lemma ppairTerm_semiterm {k s t : V} (hs : IsSemiterm ℒₒᵣ k s) (ht : IsSemiterm ℒₒᵣ k t) :
    IsSemiterm ℒₒᵣ k (ppairTerm s t) := by
  simp [ppairTerm, qqAdd, qqMul, hs, ht]

lemma succ_semiterm {k t : V} (ht : IsSemiterm ℒₒᵣ k t) : IsSemiterm ℒₒᵣ k (t ^+ (𝟏 : V)) := by
  simp [qqAdd, ht]

/-! ### The graph, as a fixpoint on pairs `⟪x, t⟫` — the clauses `Phi`, then Foundation plumbing -/

namespace CodeTerm

/-- `Phi C ⟪x, t⟫`: `t` is the structural term of the program code `x`, given the sub-results
in `C`. -/
def Phi (C : Set V) (pr : V) : Prop :=
  (∃ a : V, pr = ⟪pConst a, ppairTerm (binNumeral 0) (binNumeral a) ^+ (𝟏 : V)⟫) ∨
  pr = ⟪(pSelf : V), ppairTerm (binNumeral 1) (binNumeral 0) ^+ (𝟏 : V)⟫ ∨
  pr = ⟪(pOpp : V), ppairTerm (binNumeral 2) (binNumeral 0) ^+ (𝟏 : V)⟫ ∨
  (∃ p tp : V, ⟪p, tp⟫ ∈ C ∧ pr = ⟪pBot p, ppairTerm (binNumeral 3) tp ^+ (𝟏 : V)⟫) ∨
  (∃ p q tp tq : V, ⟪p, tp⟫ ∈ C ∧ ⟪q, tq⟫ ∈ C ∧
    pr = ⟪pSim p q, ppairTerm (binNumeral 4) (ppairTerm tp tq) ^+ (𝟏 : V)⟫) ∨
  (∃ b a p q tb tp tq : V, ⟪b, tb⟫ ∈ C ∧ ⟪p, tp⟫ ∈ C ∧ ⟪q, tq⟫ ∈ C ∧
    pr = ⟪pIte b a p q, ppairTerm (binNumeral 5) (ppairTerm tb (ppairTerm (binNumeral a) (ppairTerm tp tq))) ^+ (𝟏 : V)⟫) ∨
  (∃ k g p q tp tq : V, ⟪p, tp⟫ ∈ C ∧ ⟪q, tq⟫ ∈ C ∧
    pr = ⟪pSearch k g p q, ppairTerm (binNumeral 6) (ppairTerm (binNumeral k) (ppairTerm (binNumeral g) (ppairTerm tp tq))) ^+ (𝟏 : V)⟫) ∨
  (∃ x : V, ¬IsShape x ∧ pr = ⟪x, binNumeral x⟫)

noncomputable def blueprint : Fixpoint.Blueprint 0 := ⟨.mkDelta
  (.mkSigma “pr C. ∃ x <⁺ pr, ∃ t <⁺ pr, !pairDef pr x t ∧
    ( (∃ a < x, !pConstGraph x a ∧
        ∃ b0, !binNumeralGraph b0 0 ∧ ∃ ba, !binNumeralGraph ba a ∧ ∃ r, !ppairTermGraph r b0 ba ∧ !qqAddGraph t r ↑Arithmetic.one) ∨
      (!pSelfGraph x ∧
        ∃ b1, !binNumeralGraph b1 1 ∧ ∃ b0, !binNumeralGraph b0 0 ∧ ∃ r, !ppairTermGraph r b1 b0 ∧ !qqAddGraph t r ↑Arithmetic.one) ∨
      (!pOppGraph x ∧
        ∃ b2, !binNumeralGraph b2 2 ∧ ∃ b0, !binNumeralGraph b0 0 ∧ ∃ r, !ppairTermGraph r b2 b0 ∧ !qqAddGraph t r ↑Arithmetic.one) ∨
      (∃ p < x, !pBotGraph x p ∧ ∃ tp < t, :⟪p, tp⟫:∈ C ∧
        ∃ b3, !binNumeralGraph b3 3 ∧ ∃ r, !ppairTermGraph r b3 tp ∧ !qqAddGraph t r ↑Arithmetic.one) ∨
      (∃ p < x, ∃ q < x, !pSimGraph x p q ∧ ∃ tp < t, ∃ tq < t, :⟪p, tp⟫:∈ C ∧ :⟪q, tq⟫:∈ C ∧
        ∃ b4, !binNumeralGraph b4 4 ∧ ∃ r1, !ppairTermGraph r1 tp tq ∧ ∃ r, !ppairTermGraph r b4 r1 ∧
        !qqAddGraph t r ↑Arithmetic.one) ∨
      (∃ b < x, ∃ a < x, ∃ p < x, ∃ q < x, !pIteGraph x b a p q ∧
        ∃ tb < t, ∃ tp < t, ∃ tq < t, :⟪b, tb⟫:∈ C ∧ :⟪p, tp⟫:∈ C ∧ :⟪q, tq⟫:∈ C ∧
        ∃ b5, !binNumeralGraph b5 5 ∧ ∃ ba, !binNumeralGraph ba a ∧ ∃ r1, !ppairTermGraph r1 tp tq ∧
        ∃ r2, !ppairTermGraph r2 ba r1 ∧ ∃ r3, !ppairTermGraph r3 tb r2 ∧ ∃ r, !ppairTermGraph r b5 r3 ∧
        !qqAddGraph t r ↑Arithmetic.one) ∨
      (∃ k < x, ∃ g < x, ∃ p < x, ∃ q < x, !pSearchGraph x k g p q ∧
        ∃ tp < t, ∃ tq < t, :⟪p, tp⟫:∈ C ∧ :⟪q, tq⟫:∈ C ∧
        ∃ b6, !binNumeralGraph b6 6 ∧ ∃ bk, !binNumeralGraph bk k ∧ ∃ bg, !binNumeralGraph bg g ∧
        ∃ r1, !ppairTermGraph r1 tp tq ∧ ∃ r2, !ppairTermGraph r2 bg r1 ∧ ∃ r3, !ppairTermGraph r3 bk r2 ∧
        ∃ r, !ppairTermGraph r b6 r3 ∧ !qqAddGraph t r ↑Arithmetic.one) ∨
      (¬!isShape x ∧ !binNumeralGraph t x) )”)
  (.mkPi “pr C. ∃ x <⁺ pr, ∃ t <⁺ pr, !pairDef pr x t ∧
    ( (∃ a < x, !pConstGraph x a ∧
        ∀ b0, !binNumeralGraph b0 0 → ∀ ba, !binNumeralGraph ba a → ∀ r, !ppairTermGraph r b0 ba → ∀ s, !qqAddGraph s r ↑Arithmetic.one → t = s) ∨
      (!pSelfGraph x ∧
        ∀ b1, !binNumeralGraph b1 1 → ∀ b0, !binNumeralGraph b0 0 → ∀ r, !ppairTermGraph r b1 b0 → ∀ s, !qqAddGraph s r ↑Arithmetic.one → t = s) ∨
      (!pOppGraph x ∧
        ∀ b2, !binNumeralGraph b2 2 → ∀ b0, !binNumeralGraph b0 0 → ∀ r, !ppairTermGraph r b2 b0 → ∀ s, !qqAddGraph s r ↑Arithmetic.one → t = s) ∨
      (∃ p < x, !pBotGraph x p ∧ ∃ tp < t, :⟪p, tp⟫:∈ C ∧
        ∀ b3, !binNumeralGraph b3 3 → ∀ r, !ppairTermGraph r b3 tp → ∀ s, !qqAddGraph s r ↑Arithmetic.one → t = s) ∨
      (∃ p < x, ∃ q < x, !pSimGraph x p q ∧ ∃ tp < t, ∃ tq < t, :⟪p, tp⟫:∈ C ∧ :⟪q, tq⟫:∈ C ∧
        ∀ b4, !binNumeralGraph b4 4 → ∀ r1, !ppairTermGraph r1 tp tq → ∀ r, !ppairTermGraph r b4 r1 →
        ∀ s, !qqAddGraph s r ↑Arithmetic.one → t = s) ∨
      (∃ b < x, ∃ a < x, ∃ p < x, ∃ q < x, !pIteGraph x b a p q ∧
        ∃ tb < t, ∃ tp < t, ∃ tq < t, :⟪b, tb⟫:∈ C ∧ :⟪p, tp⟫:∈ C ∧ :⟪q, tq⟫:∈ C ∧
        ∀ b5, !binNumeralGraph b5 5 → ∀ ba, !binNumeralGraph ba a → ∀ r1, !ppairTermGraph r1 tp tq →
        ∀ r2, !ppairTermGraph r2 ba r1 → ∀ r3, !ppairTermGraph r3 tb r2 → ∀ r, !ppairTermGraph r b5 r3 →
        ∀ s, !qqAddGraph s r ↑Arithmetic.one → t = s) ∨
      (∃ k < x, ∃ g < x, ∃ p < x, ∃ q < x, !pSearchGraph x k g p q ∧
        ∃ tp < t, ∃ tq < t, :⟪p, tp⟫:∈ C ∧ :⟪q, tq⟫:∈ C ∧
        ∀ b6, !binNumeralGraph b6 6 → ∀ bk, !binNumeralGraph bk k → ∀ bg, !binNumeralGraph bg g →
        ∀ r1, !ppairTermGraph r1 tp tq → ∀ r2, !ppairTermGraph r2 bg r1 → ∀ r3, !ppairTermGraph r3 bk r2 →
        ∀ r, !ppairTermGraph r b6 r3 → ∀ s, !qqAddGraph s r ↑Arithmetic.one → t = s) ∨
      (¬!isShape x ∧ ∀ s, !binNumeralGraph s x → t = s) )”)⟩

/-- `Phi` with the bounds the blueprint carries. -/
private lemma phi_iff (C pr : V) :
    Phi {x | x ∈ C} pr ↔
    ∃ x ≤ pr, ∃ t ≤ pr, pr = ⟪x, t⟫ ∧
    ( (∃ a < x, x = pConst a ∧ t = ppairTerm (binNumeral 0) (binNumeral a) ^+ (𝟏 : V)) ∨
      (x = pSelf ∧ t = ppairTerm (binNumeral 1) (binNumeral 0) ^+ (𝟏 : V)) ∨
      (x = pOpp ∧ t = ppairTerm (binNumeral 2) (binNumeral 0) ^+ (𝟏 : V)) ∨
      (∃ p < x, x = pBot p ∧ ∃ tp < t, ⟪p, tp⟫ ∈ C ∧ t = ppairTerm (binNumeral 3) tp ^+ (𝟏 : V)) ∨
      (∃ p < x, ∃ q < x, x = pSim p q ∧ ∃ tp < t, ∃ tq < t, ⟪p, tp⟫ ∈ C ∧ ⟪q, tq⟫ ∈ C ∧
        t = ppairTerm (binNumeral 4) (ppairTerm tp tq) ^+ (𝟏 : V)) ∨
      (∃ b < x, ∃ a < x, ∃ p < x, ∃ q < x, x = pIte b a p q ∧
        ∃ tb < t, ∃ tp < t, ∃ tq < t, ⟪b, tb⟫ ∈ C ∧ ⟪p, tp⟫ ∈ C ∧ ⟪q, tq⟫ ∈ C ∧
        t = ppairTerm (binNumeral 5) (ppairTerm tb (ppairTerm (binNumeral a) (ppairTerm tp tq))) ^+ (𝟏 : V)) ∨
      (∃ k < x, ∃ g < x, ∃ p < x, ∃ q < x, x = pSearch k g p q ∧
        ∃ tp < t, ∃ tq < t, ⟪p, tp⟫ ∈ C ∧ ⟪q, tq⟫ ∈ C ∧
        t = ppairTerm (binNumeral 6) (ppairTerm (binNumeral k) (ppairTerm (binNumeral g) (ppairTerm tp tq))) ^+ (𝟏 : V)) ∨
      (¬IsShape x ∧ t = binNumeral x) ) := by
  constructor
  · rintro (⟨a, rfl⟩ | rfl | rfl | ⟨p, tp, h, rfl⟩ | ⟨p, q, tp, tq, hp, hq, rfl⟩ |
      ⟨b, a, p, q, tb, tp, tq, hb, hp, hq, rfl⟩ | ⟨k, g, p, q, tp, tq, hp, hq, rfl⟩ | ⟨x, hx, rfl⟩)
    · exact ⟨_, by simp, _, by simp, rfl, Or.inl ⟨a, by simp, rfl, rfl⟩⟩
    · exact ⟨_, by simp, _, by simp, rfl, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
    · exact ⟨_, by simp, _, by simp, rfl, Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩
    · exact ⟨_, by simp, _, by simp, rfl, Or.inr (Or.inr (Or.inr (Or.inl
        ⟨p, by simp, rfl, tp, lt_ppairTerm_succ_right _ _, h, rfl⟩)))⟩
    · exact ⟨_, by simp, _, by simp, rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨p, by simp, q, by simp, rfl, tp, lt_trans (lt_ppairTerm_left _ _) (lt_ppairTerm_succ_right _ _),
          tq, lt_trans (lt_ppairTerm_right _ _) (lt_ppairTerm_succ_right _ _), hp, hq, rfl⟩))))⟩
    · exact ⟨_, by simp, _, by simp, rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨b, by simp, a, by simp, p, by simp, q, by simp, rfl,
          tb, lt_trans (lt_ppairTerm_left _ _) (lt_ppairTerm_succ_right _ _),
          tp, lt_trans (lt_ppairTerm_left _ _) (lt_trans (lt_ppairTerm_right _ _)
            (lt_trans (lt_ppairTerm_right _ _) (lt_ppairTerm_succ_right _ _))),
          tq, lt_trans (lt_ppairTerm_right _ _) (lt_trans (lt_ppairTerm_right _ _)
            (lt_trans (lt_ppairTerm_right _ _) (lt_ppairTerm_succ_right _ _))),
          hb, hp, hq, rfl⟩)))))⟩
    · exact ⟨_, by simp, _, by simp, rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨k, by simp, g, by simp, p, by simp, q, by simp, rfl,
          tp, lt_trans (lt_ppairTerm_left _ _) (lt_trans (lt_ppairTerm_right _ _)
            (lt_trans (lt_ppairTerm_right _ _) (lt_ppairTerm_succ_right _ _))),
          tq, lt_trans (lt_ppairTerm_right _ _) (lt_trans (lt_ppairTerm_right _ _)
            (lt_trans (lt_ppairTerm_right _ _) (lt_ppairTerm_succ_right _ _))),
          hp, hq, rfl⟩))))))⟩
    · exact ⟨_, by simp, _, by simp, rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨hx, rfl⟩))))))⟩
  · rintro ⟨x, _, t, _, rfl, (⟨a, _, rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨p, _, rfl, tp, _, h, rfl⟩ | ⟨p, _, q, _, rfl, tp, _, tq, _, hp, hq, rfl⟩ |
      ⟨b, _, a, _, p, _, q, _, rfl, tb, _, tp, _, tq, _, hb, hp, hq, rfl⟩ |
      ⟨k, _, g, _, p, _, q, _, rfl, tp, _, tq, _, hp, hq, rfl⟩ | ⟨hx, rfl⟩)⟩
    · exact Or.inl ⟨a, rfl⟩
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨p, tp, h, rfl⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, q, tp, tq, hp, hq, rfl⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨b, a, p, q, tb, tp, tq, hb, hp, hq, rfl⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨k, g, p, q, tp, tq, hp, hq, rfl⟩))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨x, hx, rfl⟩))))))

noncomputable def construction : Fixpoint.Construction V blueprint where
  Φ := fun _ ↦ Phi
  defined := .mk <| by
    constructor
    · intro v
      simp [blueprint, HierarchySymbol.Semiformula.val_sigma, binNumeral.defined.df, ppairTerm.defined.df,
        qqAdd_defined.iff, numeral_eq_natCast]
    · intro v
      symm
      simpa [blueprint, HierarchySymbol.Semiformula.val_sigma, binNumeral.defined.df, ppairTerm.defined.df,
        qqAdd_defined.iff, numeral_eq_natCast, pSelfGraph, pOppGraph, pSelf, pOpp, lt_and_eq_succ_iff]
        using phi_iff (v 1) (v 0)
  monotone := by
    rintro C C' hC _ pr (⟨a, rfl⟩ | rfl | rfl | ⟨p, tp, h, rfl⟩ | ⟨p, q, tp, tq, hp, hq, rfl⟩ |
      ⟨b, a, p, q, tb, tp, tq, hb, hp, hq, rfl⟩ | ⟨k, g, p, q, tp, tq, hp, hq, rfl⟩ | ⟨x, hx, rfl⟩)
    · exact Or.inl ⟨a, rfl⟩
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨p, tp, hC h, rfl⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, q, tp, tq, hC hp, hC hq, rfl⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨b, a, p, q, tb, tp, tq, hC hb, hC hp, hC hq, rfl⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨k, g, p, q, tp, tq, hC hp, hC hq, rfl⟩))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨x, hx, rfl⟩))))))

instance : construction.StrongFinite V where
  strong_finite := by
    rintro C _ pr (⟨a, rfl⟩ | rfl | rfl | ⟨p, tp, h, rfl⟩ | ⟨p, q, tp, tq, hp, hq, rfl⟩ |
      ⟨b, a, p, q, tb, tp, tq, hb, hp, hq, rfl⟩ | ⟨k, g, p, q, tp, tq, hp, hq, rfl⟩ | ⟨x, hx, rfl⟩)
    · exact Or.inl ⟨a, rfl⟩
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨p, tp,
        ⟨h, pair_lt_pair (by simp) (lt_ppairTerm_succ_right _ _)⟩, rfl⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, q, tp, tq,
        ⟨hp, pair_lt_pair (by simp) (lt_trans (lt_ppairTerm_left _ _) (lt_ppairTerm_succ_right _ _))⟩,
        ⟨hq, pair_lt_pair (by simp) (lt_trans (lt_ppairTerm_right _ _) (lt_ppairTerm_succ_right _ _))⟩, rfl⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨b, a, p, q, tb, tp, tq,
        ⟨hb, pair_lt_pair (by simp) (lt_trans (lt_ppairTerm_left _ _) (lt_ppairTerm_succ_right _ _))⟩,
        ⟨hp, pair_lt_pair (by simp) (lt_trans (lt_ppairTerm_left _ _) (lt_trans (lt_ppairTerm_right _ _)
            (lt_trans (lt_ppairTerm_right _ _) (lt_ppairTerm_succ_right _ _))))⟩,
        ⟨hq, pair_lt_pair (by simp) (lt_trans (lt_ppairTerm_right _ _) (lt_trans (lt_ppairTerm_right _ _)
            (lt_trans (lt_ppairTerm_right _ _) (lt_ppairTerm_succ_right _ _))))⟩, rfl⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨k, g, p, q, tp, tq,
        ⟨hp, pair_lt_pair (by simp) (lt_trans (lt_ppairTerm_left _ _) (lt_trans (lt_ppairTerm_right _ _)
            (lt_trans (lt_ppairTerm_right _ _) (lt_ppairTerm_succ_right _ _))))⟩,
        ⟨hq, pair_lt_pair (by simp) (lt_trans (lt_ppairTerm_right _ _) (lt_trans (lt_ppairTerm_right _ _)
            (lt_trans (lt_ppairTerm_right _ _) (lt_ppairTerm_succ_right _ _))))⟩, rfl⟩))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨x, hx, rfl⟩))))))

end CodeTerm

/-- `CodeTermGraph x t`: `t` is the structural term code of the program code `x`. -/
def CodeTermGraph (x t : V) : Prop := CodeTerm.construction.Fixpoint ![] ⟪x, t⟫

noncomputable def codeTermGraphDef : 𝚫₁.Semisentence 2 := .mkDelta
  (.mkSigma “x t. ∃ pr <⁺ (x + t + 1)², !pairDef pr x t ∧ !CodeTerm.blueprint.fixpointDefΔ₁.sigma pr”)
  (.mkPi “x t. ∀ pr <⁺ (x + t + 1)², !pairDef pr x t → !CodeTerm.blueprint.fixpointDefΔ₁.pi pr”)

section

private lemma fixpoint_param_eq (p : Fin 0 → V) (x : V) :
    CodeTerm.construction.Fixpoint p x = CodeTerm.construction.Fixpoint ![] x := by
  rw [Subsingleton.elim p ![]]

instance codeTermGraph_defined : 𝚫₁-Relation[V] CodeTermGraph via codeTermGraphDef := .mk
  ⟨by intro v
      simp [codeTermGraphDef, HierarchySymbol.Semiformula.val_sigma,
        CodeTerm.construction.fixpoint_definedΔ₁.proper.iff', CodeTerm.construction.fixpoint_definedΔ₁.df]
      constructor
      · rintro h x _ rfl; rwa [fixpoint_param_eq] at h ⊢
      · intro h; have := h ⟪v 0, v 1⟫ (by simp) rfl; rwa [fixpoint_param_eq] at this ⊢,
   by intro v
      simp [codeTermGraphDef, HierarchySymbol.Semiformula.val_sigma,
        CodeTerm.construction.fixpoint_definedΔ₁.df, CodeTermGraph]
      rw [fixpoint_param_eq]⟩

instance codeTermGraph_definable : 𝚫₁-Relation[V] CodeTermGraph := codeTermGraph_defined.to_definable

instance codeTermGraph_definable' : Γ-[m + 1]-Relation[V] CodeTermGraph := codeTermGraph_definable.of_deltaOne

end

/-! ### Case analysis and inversion -/

lemma CodeTermGraph.case_iff {x t : V} :
    CodeTermGraph x t ↔
    (∃ a, x = pConst a ∧ t = ppairTerm (binNumeral 0) (binNumeral a) ^+ (𝟏 : V)) ∨
    (x = pSelf ∧ t = ppairTerm (binNumeral 1) (binNumeral 0) ^+ (𝟏 : V)) ∨
    (x = pOpp ∧ t = ppairTerm (binNumeral 2) (binNumeral 0) ^+ (𝟏 : V)) ∨
    (∃ p tp, CodeTermGraph p tp ∧ x = pBot p ∧ t = ppairTerm (binNumeral 3) tp ^+ (𝟏 : V)) ∨
    (∃ p q tp tq, CodeTermGraph p tp ∧ CodeTermGraph q tq ∧ x = pSim p q ∧
      t = ppairTerm (binNumeral 4) (ppairTerm tp tq) ^+ (𝟏 : V)) ∨
    (∃ b a p q tb tp tq, CodeTermGraph b tb ∧ CodeTermGraph p tp ∧ CodeTermGraph q tq ∧ x = pIte b a p q ∧
      t = ppairTerm (binNumeral 5) (ppairTerm tb (ppairTerm (binNumeral a) (ppairTerm tp tq))) ^+ (𝟏 : V)) ∨
    (∃ k g p q tp tq, CodeTermGraph p tp ∧ CodeTermGraph q tq ∧ x = pSearch k g p q ∧
      t = ppairTerm (binNumeral 6) (ppairTerm (binNumeral k) (ppairTerm (binNumeral g) (ppairTerm tp tq))) ^+ (𝟏 : V)) ∨
    (¬IsShape x ∧ t = binNumeral x) :=
  Iff.trans CodeTerm.construction.case
    (by simp [show CodeTerm.construction.Φ = fun _ ↦ CodeTerm.Phi from rfl, CodeTerm.Phi, CodeTermGraph])

section inversion

attribute [local simp] pConst pSelf pOpp pBot pSim pIte pSearch IsShape

lemma CodeTermGraph.const_iff {a t : V} :
    CodeTermGraph (pConst a) t ↔ t = ppairTerm (binNumeral 0) (binNumeral a) ^+ (𝟏 : V) := by
  rw [CodeTermGraph.case_iff]; simp
lemma CodeTermGraph.self_iff {t : V} : CodeTermGraph pSelf t ↔ t = ppairTerm (binNumeral 1) (binNumeral 0) ^+ (𝟏 : V) := by
  rw [CodeTermGraph.case_iff]; simp
lemma CodeTermGraph.opp_iff {t : V} : CodeTermGraph pOpp t ↔ t = ppairTerm (binNumeral 2) (binNumeral 0) ^+ (𝟏 : V) := by
  rw [CodeTermGraph.case_iff]; simp
lemma CodeTermGraph.bot_iff {p t : V} :
    CodeTermGraph (pBot p) t ↔ ∃ tp, CodeTermGraph p tp ∧ t = ppairTerm (binNumeral 3) tp ^+ (𝟏 : V) := by
  rw [CodeTermGraph.case_iff]; simp
lemma CodeTermGraph.sim_iff {p q t : V} :
    CodeTermGraph (pSim p q) t ↔
    ∃ tp tq, CodeTermGraph p tp ∧ CodeTermGraph q tq ∧ t = ppairTerm (binNumeral 4) (ppairTerm tp tq) ^+ (𝟏 : V) := by
  rw [CodeTermGraph.case_iff]; simp
lemma CodeTermGraph.ite_iff {b a p q t : V} :
    CodeTermGraph (pIte b a p q) t ↔
    ∃ tb tp tq, CodeTermGraph b tb ∧ CodeTermGraph p tp ∧ CodeTermGraph q tq ∧
      t = ppairTerm (binNumeral 5) (ppairTerm tb (ppairTerm (binNumeral a) (ppairTerm tp tq))) ^+ (𝟏 : V) := by
  rw [CodeTermGraph.case_iff]; simp
lemma CodeTermGraph.search_iff {k g p q t : V} :
    CodeTermGraph (pSearch k g p q) t ↔
    ∃ tp tq, CodeTermGraph p tp ∧ CodeTermGraph q tq ∧
      t = ppairTerm (binNumeral 6) (ppairTerm (binNumeral k) (ppairTerm (binNumeral g) (ppairTerm tp tq))) ^+ (𝟏 : V) := by
  rw [CodeTermGraph.case_iff]; simp
lemma CodeTermGraph.of_not_shape {x t : V} (hx : ¬IsShape x) : CodeTermGraph x t ↔ t = binNumeral x := by
  rw [CodeTermGraph.case_iff]
  constructor
  · rintro (⟨a, rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨p, tp, _, rfl, _⟩ | ⟨p, q, tp, tq, _, _, rfl, _⟩ |
      ⟨b, a, p, q, tb, tp, tq, _, _, _, rfl, _⟩ | ⟨k, g, p, q, tp, tq, _, _, rfl, _⟩ | ⟨_, h⟩)
    · exact absurd (Or.inl ⟨a, rfl⟩) hx
    · exact absurd (Or.inr (Or.inl rfl)) hx
    · exact absurd (Or.inr (Or.inr (Or.inl rfl))) hx
    · exact absurd (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, rfl⟩)))) hx
    · exact absurd (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, q, rfl⟩))))) hx
    · exact absurd (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨b, a, p, q, rfl⟩)))))) hx
    · exact absurd (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨k, g, p, q, rfl⟩)))))) hx
    · exact h
  · rintro rfl
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hx, rfl⟩))))))

end inversion

/-! ### `codeTerm` is a total Σ₁ function -/

lemma codeTermGraph_exists (x : V) : ∃ t, CodeTermGraph x t := by
  induction x using ISigma1.sigma1_order_induction with
  | hP => definability
  | ind x ih =>
    by_cases hx : IsShape x
    · rcases hx with ⟨a, rfl⟩ | rfl | rfl | ⟨p, rfl⟩ | ⟨p, q, rfl⟩ | ⟨b, a, p, q, rfl⟩ | ⟨k, g, p, q, rfl⟩
      · exact ⟨_, CodeTermGraph.const_iff.mpr rfl⟩
      · exact ⟨_, CodeTermGraph.self_iff.mpr rfl⟩
      · exact ⟨_, CodeTermGraph.opp_iff.mpr rfl⟩
      · obtain ⟨tp, hp⟩ := ih p (by simp)
        exact ⟨_, CodeTermGraph.bot_iff.mpr ⟨tp, hp, rfl⟩⟩
      · obtain ⟨tp, hp⟩ := ih p (by simp); obtain ⟨tq, hq⟩ := ih q (by simp)
        exact ⟨_, CodeTermGraph.sim_iff.mpr ⟨tp, tq, hp, hq, rfl⟩⟩
      · obtain ⟨tb, hb⟩ := ih b (by simp); obtain ⟨tp, hp⟩ := ih p (by simp)
        obtain ⟨tq, hq⟩ := ih q (by simp)
        exact ⟨_, CodeTermGraph.ite_iff.mpr ⟨tb, tp, tq, hb, hp, hq, rfl⟩⟩
      · obtain ⟨tp, hp⟩ := ih p (by simp); obtain ⟨tq, hq⟩ := ih q (by simp)
        exact ⟨_, CodeTermGraph.search_iff.mpr ⟨tp, tq, hp, hq, rfl⟩⟩
    · exact ⟨_, (CodeTermGraph.of_not_shape hx).mpr rfl⟩

lemma codeTermGraph_unique (x : V) : ∀ t₁ t₂, CodeTermGraph x t₁ → CodeTermGraph x t₂ → t₁ = t₂ := by
  induction x using ISigma1.pi1_order_induction with
  | hP => definability
  | ind x ih =>
    intro t₁ t₂ h₁ h₂
    by_cases hx : IsShape x
    · rcases hx with ⟨a, rfl⟩ | rfl | rfl | ⟨p, rfl⟩ | ⟨p, q, rfl⟩ | ⟨b, a, p, q, rfl⟩ | ⟨k, g, p, q, rfl⟩
      · rw [CodeTermGraph.const_iff] at h₁ h₂; rw [h₁, h₂]
      · rw [CodeTermGraph.self_iff] at h₁ h₂; rw [h₁, h₂]
      · rw [CodeTermGraph.opp_iff] at h₁ h₂; rw [h₁, h₂]
      · rcases CodeTermGraph.bot_iff.mp h₁ with ⟨p₁, hp₁, rfl⟩
        rcases CodeTermGraph.bot_iff.mp h₂ with ⟨p₂, hp₂, rfl⟩
        rw [ih p (by simp) _ _ hp₁ hp₂]
      · rcases CodeTermGraph.sim_iff.mp h₁ with ⟨p₁, q₁, hp₁, hq₁, rfl⟩
        rcases CodeTermGraph.sim_iff.mp h₂ with ⟨p₂, q₂, hp₂, hq₂, rfl⟩
        rw [ih p (by simp) _ _ hp₁ hp₂, ih q (by simp) _ _ hq₁ hq₂]
      · rcases CodeTermGraph.ite_iff.mp h₁ with ⟨b₁, p₁, q₁, hb₁, hp₁, hq₁, rfl⟩
        rcases CodeTermGraph.ite_iff.mp h₂ with ⟨b₂, p₂, q₂, hb₂, hp₂, hq₂, rfl⟩
        rw [ih b (by simp) _ _ hb₁ hb₂, ih p (by simp) _ _ hp₁ hp₂, ih q (by simp) _ _ hq₁ hq₂]
      · rcases CodeTermGraph.search_iff.mp h₁ with ⟨p₁, q₁, hp₁, hq₁, rfl⟩
        rcases CodeTermGraph.search_iff.mp h₂ with ⟨p₂, q₂, hp₂, hq₂, rfl⟩
        rw [ih p (by simp) _ _ hp₁ hp₂, ih q (by simp) _ _ hq₁ hq₂]
    · rw [CodeTermGraph.of_not_shape hx] at h₁ h₂; rw [h₁, h₂]

lemma codeTermGraph_existsUnique (x : V) : ∃! t, CodeTermGraph x t := by
  rcases codeTermGraph_exists x with ⟨t, ht⟩
  exact ExistsUnique.intro t ht (fun t' h' ↦ codeTermGraph_unique x t' t h' ht)

/-- The structural term code of a program code (`binNumeral x` on non-programs). -/
noncomputable def codeTerm (x : V) : V := Classical.choose! (codeTermGraph_existsUnique x)

lemma codeTerm_graph (x : V) : CodeTermGraph x (codeTerm x) := Classical.choose!_spec (codeTermGraph_existsUnique x)

lemma codeTerm_eq_of_graph {x t : V} (h : CodeTermGraph x t) : codeTerm x = t :=
  codeTermGraph_unique x _ _ (codeTerm_graph x) h

noncomputable def codeTermGraph : 𝚺₁.Semisentence 2 := .mkSigma “t x. !codeTermGraphDef.sigma x t”

instance codeTerm.defined : 𝚺₁-Function₁[V] codeTerm via codeTermGraph := .mk fun v ↦ by
  simp [codeTermGraph, HierarchySymbol.Semiformula.val_sigma, codeTermGraph_defined.df]
  constructor
  · intro h; exact (codeTerm_eq_of_graph h).symm
  · intro h; rw [h]; exact codeTerm_graph _

instance codeTerm.definable : 𝚺₁-Function₁[V] codeTerm := codeTerm.defined.to_definable

/-! ### The equations -/

@[simp] lemma codeTerm_const (a : V) : codeTerm (pConst a) = ppairTerm (binNumeral 0) (binNumeral a) ^+ (𝟏 : V) :=
  codeTerm_eq_of_graph (CodeTermGraph.const_iff.mpr rfl)
@[simp] lemma codeTerm_self : codeTerm (pSelf : V) = ppairTerm (binNumeral 1) (binNumeral 0) ^+ (𝟏 : V) :=
  codeTerm_eq_of_graph (CodeTermGraph.self_iff.mpr rfl)
@[simp] lemma codeTerm_opp : codeTerm (pOpp : V) = ppairTerm (binNumeral 2) (binNumeral 0) ^+ (𝟏 : V) :=
  codeTerm_eq_of_graph (CodeTermGraph.opp_iff.mpr rfl)
@[simp] lemma codeTerm_bot (p : V) : codeTerm (pBot p) = ppairTerm (binNumeral 3) (codeTerm p) ^+ (𝟏 : V) :=
  codeTerm_eq_of_graph (CodeTermGraph.bot_iff.mpr ⟨_, codeTerm_graph p, rfl⟩)
@[simp] lemma codeTerm_sim (p q : V) :
    codeTerm (pSim p q) = ppairTerm (binNumeral 4) (ppairTerm (codeTerm p) (codeTerm q)) ^+ (𝟏 : V) :=
  codeTerm_eq_of_graph (CodeTermGraph.sim_iff.mpr ⟨_, _, codeTerm_graph p, codeTerm_graph q, rfl⟩)
@[simp] lemma codeTerm_ite (b a p q : V) :
    codeTerm (pIte b a p q) =
    ppairTerm (binNumeral 5) (ppairTerm (codeTerm b) (ppairTerm (binNumeral a) (ppairTerm (codeTerm p) (codeTerm q)))) ^+ (𝟏 : V) :=
  codeTerm_eq_of_graph (CodeTermGraph.ite_iff.mpr ⟨_, _, _, codeTerm_graph b, codeTerm_graph p, codeTerm_graph q, rfl⟩)
@[simp] lemma codeTerm_search (k g p q : V) :
    codeTerm (pSearch k g p q) =
    ppairTerm (binNumeral 6) (ppairTerm (binNumeral k) (ppairTerm (binNumeral g) (ppairTerm (codeTerm p) (codeTerm q)))) ^+ (𝟏 : V) :=
  codeTerm_eq_of_graph (CodeTermGraph.search_iff.mpr ⟨_, _, codeTerm_graph p, codeTerm_graph q, rfl⟩)
lemma codeTerm_of_not_shape {x : V} (hx : ¬IsShape x) : codeTerm x = binNumeral x :=
  codeTerm_eq_of_graph ((CodeTermGraph.of_not_shape hx).mpr rfl)

/-- `codeTerm x` is a closed `ℒₒᵣ`-term (at every bound-variable count). -/
lemma codeTerm_semiterm (k x : V) : IsSemiterm ℒₒᵣ k (codeTerm x) := by
  induction x using ISigma1.pi1_order_induction with
  | hP => definability
  | ind x ih =>
    by_cases hx : IsShape x
    · rcases hx with ⟨a, rfl⟩ | rfl | rfl | ⟨p, rfl⟩ | ⟨p, q, rfl⟩ | ⟨b, a, p, q, rfl⟩ | ⟨k', g, p, q, rfl⟩
      · rw [codeTerm_const]; exact succ_semiterm (ppairTerm_semiterm (binNumeral_semiterm k _) (binNumeral_semiterm k _))
      · rw [codeTerm_self]; exact succ_semiterm (ppairTerm_semiterm (binNumeral_semiterm k _) (binNumeral_semiterm k _))
      · rw [codeTerm_opp]; exact succ_semiterm (ppairTerm_semiterm (binNumeral_semiterm k _) (binNumeral_semiterm k _))
      · rw [codeTerm_bot]; exact succ_semiterm (ppairTerm_semiterm (binNumeral_semiterm k _) (ih p (by simp)))
      · rw [codeTerm_sim]
        exact succ_semiterm (ppairTerm_semiterm (binNumeral_semiterm k _)
          (ppairTerm_semiterm (ih p (by simp)) (ih q (by simp))))
      · rw [codeTerm_ite]
        exact succ_semiterm (ppairTerm_semiterm (binNumeral_semiterm k _) (ppairTerm_semiterm (ih b (by simp))
          (ppairTerm_semiterm (binNumeral_semiterm k _) (ppairTerm_semiterm (ih p (by simp)) (ih q (by simp))))))
      · rw [codeTerm_search]
        exact succ_semiterm (ppairTerm_semiterm (binNumeral_semiterm k _) (ppairTerm_semiterm (binNumeral_semiterm k _)
          (ppairTerm_semiterm (binNumeral_semiterm k _) (ppairTerm_semiterm (ih p (by simp)) (ih q (by simp))))))
    · rw [codeTerm_of_not_shape hx]; exact binNumeral_semiterm k x

lemma codeTerm_uterm (x : V) : IsUTerm ℒₒᵣ (codeTerm x) := (codeTerm_semiterm 0 x).isUTerm

/-! ### The meta terms -/

section metaTerms

/-- The meta term `(s + t) * (s + t) + t`. -/
noncomputable def ppairTermMeta (s t : ClosedSemiterm ℒₒᵣ 0) : ClosedSemiterm ℒₒᵣ 0 :=
  ‘(!!s + !!t) * (!!s + !!t) + !!t’

/-- The meta term `t + 1`. -/
noncomputable def succTT (t : ClosedSemiterm ℒₒᵣ 0) : ClosedSemiterm ℒₒᵣ 0 := ‘!!t + 1’

lemma ppairTermMeta_eq (s t : ClosedSemiterm ℒₒᵣ 0) :
    ppairTermMeta s t = ‘!!(‘!!(‘!!s + !!t’ : ClosedSemiterm ℒₒᵣ 0) * !!(‘!!s + !!t’ : ClosedSemiterm ℒₒᵣ 0)’ :
      ClosedSemiterm ℒₒᵣ 0) + !!t’ := rfl

lemma succTT_eq (t : ClosedSemiterm ℒₒᵣ 0) : succTT t = ‘!!t + !!(‘1’ : ClosedSemiterm ℒₒᵣ 0)’ := rfl

/-! #### Codes, lengths and values of the two combinators -/

lemma quote_ppairTermMeta (s t : ClosedSemiterm ℒₒᵣ 0) :
    (⌜ppairTermMeta s t⌝ : V) = ppairTerm (⌜s⌝ : V) (⌜t⌝ : V) := by
  rw [ppairTermMeta_eq, quote_closed_add, quote_closed_mul, quote_closed_add]; rfl

lemma quote_succTT (t : ClosedSemiterm ℒₒᵣ 0) : (⌜succTT t⌝ : V) = (⌜t⌝ : V) ^+ (𝟏 : V) := by
  rw [succTT_eq, quote_closed_add, quote_closed_one]

/-- `ppairTermMeta` writes `s` twice and `t` three times. -/
lemma termLenMeta_emb_ppairTermMeta (s t : ClosedSemiterm ℒₒᵣ 0) :
    termLenMeta (Rew.emb (ppairTermMeta s t) : SyntacticSemiterm ℒₒᵣ 0) =
    2 * termLenMeta (Rew.emb s : SyntacticSemiterm ℒₒᵣ 0) + 3 * termLenMeta (Rew.emb t : SyntacticSemiterm ℒₒᵣ 0) + 4 := by
  rw [ppairTermMeta_eq, termLenMeta_emb_closed_add, termLenMeta_emb_closed_mul, termLenMeta_emb_closed_add]; omega

lemma termLenMeta_emb_succTT (t : ClosedSemiterm ℒₒᵣ 0) :
    termLenMeta (Rew.emb (succTT t) : SyntacticSemiterm ℒₒᵣ 0) = termLenMeta (Rew.emb t : SyntacticSemiterm ℒₒᵣ 0) + 2 := by
  rw [succTT_eq, termLenMeta_emb_closed_add, termLenMeta_emb_closed_one]

lemma val_ppairTermMeta (s t : ClosedSemiterm ℒₒᵣ 0) :
    (ppairTermMeta s t).val (s := standardModel ℕ) ![] Empty.elim =
    ppair (s.val (s := standardModel ℕ) ![] Empty.elim) (t.val (s := standardModel ℕ) ![] Empty.elim) := by
  simp [ppairTermMeta, ppair]

lemma val_succTT (t : ClosedSemiterm ℒₒᵣ 0) :
    (succTT t).val (s := standardModel ℕ) ![] Empty.elim = t.val (s := standardModel ℕ) ![] Empty.elim + 1 := by
  simp [succTT]

/-! #### The graph of the meta recursion (inductive, with explicit equations so that `cases` works) -/

/-- `CodeTermMetaGraph x t`: `t` is the structural term of the program code `x`. -/
inductive CodeTermMetaGraph : ℕ → ClosedSemiterm ℒₒᵣ 0 → Prop
  | const (x a : ℕ) (t : ClosedSemiterm ℒₒᵣ 0) (hx : x = pConst a)
      (ht : t = succTT (ppairTermMeta (binNumeralMeta 0) (binNumeralMeta a))) : CodeTermMetaGraph x t
  | self (x : ℕ) (t : ClosedSemiterm ℒₒᵣ 0) (hx : x = pSelf)
      (ht : t = succTT (ppairTermMeta (binNumeralMeta 1) (binNumeralMeta 0))) : CodeTermMetaGraph x t
  | opp (x : ℕ) (t : ClosedSemiterm ℒₒᵣ 0) (hx : x = pOpp)
      (ht : t = succTT (ppairTermMeta (binNumeralMeta 2) (binNumeralMeta 0))) : CodeTermMetaGraph x t
  | bot (x p : ℕ) (t tp : ClosedSemiterm ℒₒᵣ 0) (hx : x = pBot p) (hp : CodeTermMetaGraph p tp)
      (ht : t = succTT (ppairTermMeta (binNumeralMeta 3) tp)) : CodeTermMetaGraph x t
  | sim (x p q : ℕ) (t tp tq : ClosedSemiterm ℒₒᵣ 0) (hx : x = pSim p q)
      (hp : CodeTermMetaGraph p tp) (hq : CodeTermMetaGraph q tq)
      (ht : t = succTT (ppairTermMeta (binNumeralMeta 4) (ppairTermMeta tp tq))) : CodeTermMetaGraph x t
  | ite (x b a p q : ℕ) (t tb tp tq : ClosedSemiterm ℒₒᵣ 0) (hx : x = pIte b a p q)
      (hb : CodeTermMetaGraph b tb) (hp : CodeTermMetaGraph p tp) (hq : CodeTermMetaGraph q tq)
      (ht : t = succTT (ppairTermMeta (binNumeralMeta 5) (ppairTermMeta tb (ppairTermMeta (binNumeralMeta a) (ppairTermMeta tp tq))))) :
      CodeTermMetaGraph x t
  | search (x k g p q : ℕ) (t tp tq : ClosedSemiterm ℒₒᵣ 0) (hx : x = pSearch k g p q)
      (hp : CodeTermMetaGraph p tp) (hq : CodeTermMetaGraph q tq)
      (ht : t = succTT (ppairTermMeta (binNumeralMeta 6) (ppairTermMeta (binNumeralMeta k) (ppairTermMeta (binNumeralMeta g) (ppairTermMeta tp tq))))) :
      CodeTermMetaGraph x t
  | other (x : ℕ) (t : ClosedSemiterm ℒₒᵣ 0) (hx : ¬IsShape x) (ht : t = binNumeralMeta x) : CodeTermMetaGraph x t

section inversion

attribute [local simp] pConst pSelf pOpp pBot pSim pIte pSearch IsShape

lemma CodeTermMetaGraph.const_iff {a : ℕ} {t : ClosedSemiterm ℒₒᵣ 0} :
    CodeTermMetaGraph (pConst a) t ↔ t = succTT (ppairTermMeta (binNumeralMeta 0) (binNumeralMeta a)) := by
  constructor
  · intro h; cases h <;> simp_all
  · rintro rfl; exact .const _ _ _ rfl rfl
lemma CodeTermMetaGraph.self_iff {t : ClosedSemiterm ℒₒᵣ 0} :
    CodeTermMetaGraph pSelf t ↔ t = succTT (ppairTermMeta (binNumeralMeta 1) (binNumeralMeta 0)) := by
  constructor
  · intro h; cases h <;> simp_all
  · rintro rfl; exact .self _ _ rfl rfl
lemma CodeTermMetaGraph.opp_iff {t : ClosedSemiterm ℒₒᵣ 0} :
    CodeTermMetaGraph pOpp t ↔ t = succTT (ppairTermMeta (binNumeralMeta 2) (binNumeralMeta 0)) := by
  constructor
  · intro h; cases h <;> simp_all
  · rintro rfl; exact .opp _ _ rfl rfl
lemma CodeTermMetaGraph.bot_iff {p : ℕ} {t : ClosedSemiterm ℒₒᵣ 0} :
    CodeTermMetaGraph (pBot p) t ↔ ∃ tp, CodeTermMetaGraph p tp ∧ t = succTT (ppairTermMeta (binNumeralMeta 3) tp) := by
  constructor
  · intro h; cases h <;> simp_all <;>
      first | exact ⟨_, ‹_›, rfl⟩ | exact ⟨_, ‹_›, _, ‹_›, rfl⟩ | exact ⟨_, ‹_›, _, ‹_›, _, ‹_›, rfl⟩
  · rintro ⟨tp, hp, rfl⟩; exact .bot _ _ _ _ rfl hp rfl
lemma CodeTermMetaGraph.sim_iff {p q : ℕ} {t : ClosedSemiterm ℒₒᵣ 0} :
    CodeTermMetaGraph (pSim p q) t ↔
    ∃ tp tq, CodeTermMetaGraph p tp ∧ CodeTermMetaGraph q tq ∧ t = succTT (ppairTermMeta (binNumeralMeta 4) (ppairTermMeta tp tq)) := by
  constructor
  · intro h; cases h <;> simp_all <;>
      first | exact ⟨_, ‹_›, rfl⟩ | exact ⟨_, ‹_›, _, ‹_›, rfl⟩ | exact ⟨_, ‹_›, _, ‹_›, _, ‹_›, rfl⟩
  · rintro ⟨tp, tq, hp, hq, rfl⟩; exact .sim _ _ _ _ _ _ rfl hp hq rfl
lemma CodeTermMetaGraph.ite_iff {b a p q : ℕ} {t : ClosedSemiterm ℒₒᵣ 0} :
    CodeTermMetaGraph (pIte b a p q) t ↔
    ∃ tb tp tq, CodeTermMetaGraph b tb ∧ CodeTermMetaGraph p tp ∧ CodeTermMetaGraph q tq ∧
      t = succTT (ppairTermMeta (binNumeralMeta 5) (ppairTermMeta tb (ppairTermMeta (binNumeralMeta a) (ppairTermMeta tp tq)))) := by
  constructor
  · intro h; cases h <;> simp_all <;>
      first | exact ⟨_, ‹_›, rfl⟩ | exact ⟨_, ‹_›, _, ‹_›, rfl⟩ | exact ⟨_, ‹_›, _, ‹_›, _, ‹_›, rfl⟩
  · rintro ⟨tb, tp, tq, hb, hp, hq, rfl⟩; exact .ite _ _ _ _ _ _ _ _ _ rfl hb hp hq rfl
lemma CodeTermMetaGraph.search_iff {k g p q : ℕ} {t : ClosedSemiterm ℒₒᵣ 0} :
    CodeTermMetaGraph (pSearch k g p q) t ↔
    ∃ tp tq, CodeTermMetaGraph p tp ∧ CodeTermMetaGraph q tq ∧
      t = succTT (ppairTermMeta (binNumeralMeta 6) (ppairTermMeta (binNumeralMeta k) (ppairTermMeta (binNumeralMeta g) (ppairTermMeta tp tq)))) := by
  constructor
  · intro h; cases h <;> simp_all <;>
      first | exact ⟨_, ‹_›, rfl⟩ | exact ⟨_, ‹_›, _, ‹_›, rfl⟩ | exact ⟨_, ‹_›, _, ‹_›, _, ‹_›, rfl⟩
  · rintro ⟨tp, tq, hp, hq, rfl⟩; exact .search _ _ _ _ _ _ _ _ rfl hp hq rfl
lemma CodeTermMetaGraph.of_not_shape {x : ℕ} {t : ClosedSemiterm ℒₒᵣ 0} (hx : ¬IsShape x) :
    CodeTermMetaGraph x t ↔ t = binNumeralMeta x := by
  constructor
  · intro h; cases h <;> simp_all
  · rintro rfl; exact .other _ _ hx rfl

end inversion

lemma codeTermMetaGraph_exists (x : ℕ) : ∃ t, CodeTermMetaGraph x t := by
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    by_cases hx : IsShape x
    · rcases hx with ⟨a, rfl⟩ | rfl | rfl | ⟨p, rfl⟩ | ⟨p, q, rfl⟩ | ⟨b, a, p, q, rfl⟩ | ⟨k, g, p, q, rfl⟩
      · exact ⟨_, CodeTermMetaGraph.const_iff.mpr rfl⟩
      · exact ⟨_, CodeTermMetaGraph.self_iff.mpr rfl⟩
      · exact ⟨_, CodeTermMetaGraph.opp_iff.mpr rfl⟩
      · obtain ⟨tp, hp⟩ := ih p (by simp)
        exact ⟨_, CodeTermMetaGraph.bot_iff.mpr ⟨tp, hp, rfl⟩⟩
      · obtain ⟨tp, hp⟩ := ih p (by simp); obtain ⟨tq, hq⟩ := ih q (by simp)
        exact ⟨_, CodeTermMetaGraph.sim_iff.mpr ⟨tp, tq, hp, hq, rfl⟩⟩
      · obtain ⟨tb, hb⟩ := ih b (by simp); obtain ⟨tp, hp⟩ := ih p (by simp)
        obtain ⟨tq, hq⟩ := ih q (by simp)
        exact ⟨_, CodeTermMetaGraph.ite_iff.mpr ⟨tb, tp, tq, hb, hp, hq, rfl⟩⟩
      · obtain ⟨tp, hp⟩ := ih p (by simp); obtain ⟨tq, hq⟩ := ih q (by simp)
        exact ⟨_, CodeTermMetaGraph.search_iff.mpr ⟨tp, tq, hp, hq, rfl⟩⟩
    · exact ⟨_, (CodeTermMetaGraph.of_not_shape hx).mpr rfl⟩

lemma codeTermMetaGraph_unique (x : ℕ) : ∀ t₁ t₂, CodeTermMetaGraph x t₁ → CodeTermMetaGraph x t₂ → t₁ = t₂ := by
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    intro t₁ t₂ h₁ h₂
    by_cases hx : IsShape x
    · rcases hx with ⟨a, rfl⟩ | rfl | rfl | ⟨p, rfl⟩ | ⟨p, q, rfl⟩ | ⟨b, a, p, q, rfl⟩ | ⟨k, g, p, q, rfl⟩
      · rw [CodeTermMetaGraph.const_iff] at h₁ h₂; rw [h₁, h₂]
      · rw [CodeTermMetaGraph.self_iff] at h₁ h₂; rw [h₁, h₂]
      · rw [CodeTermMetaGraph.opp_iff] at h₁ h₂; rw [h₁, h₂]
      · rcases CodeTermMetaGraph.bot_iff.mp h₁ with ⟨p₁, hp₁, rfl⟩
        rcases CodeTermMetaGraph.bot_iff.mp h₂ with ⟨p₂, hp₂, rfl⟩
        rw [ih p (by simp) _ _ hp₁ hp₂]
      · rcases CodeTermMetaGraph.sim_iff.mp h₁ with ⟨p₁, q₁, hp₁, hq₁, rfl⟩
        rcases CodeTermMetaGraph.sim_iff.mp h₂ with ⟨p₂, q₂, hp₂, hq₂, rfl⟩
        rw [ih p (by simp) _ _ hp₁ hp₂, ih q (by simp) _ _ hq₁ hq₂]
      · rcases CodeTermMetaGraph.ite_iff.mp h₁ with ⟨b₁, p₁, q₁, hb₁, hp₁, hq₁, rfl⟩
        rcases CodeTermMetaGraph.ite_iff.mp h₂ with ⟨b₂, p₂, q₂, hb₂, hp₂, hq₂, rfl⟩
        rw [ih b (by simp) _ _ hb₁ hb₂, ih p (by simp) _ _ hp₁ hp₂, ih q (by simp) _ _ hq₁ hq₂]
      · rcases CodeTermMetaGraph.search_iff.mp h₁ with ⟨p₁, q₁, hp₁, hq₁, rfl⟩
        rcases CodeTermMetaGraph.search_iff.mp h₂ with ⟨p₂, q₂, hp₂, hq₂, rfl⟩
        rw [ih p (by simp) _ _ hp₁ hp₂, ih q (by simp) _ _ hq₁ hq₂]
    · rw [CodeTermMetaGraph.of_not_shape hx] at h₁ h₂; rw [h₁, h₂]

lemma codeTermMetaGraph_existsUnique (x : ℕ) : ∃! t, CodeTermMetaGraph x t := by
  rcases codeTermMetaGraph_exists x with ⟨t, ht⟩
  exact ExistsUnique.intro t ht (fun t' h' ↦ codeTermMetaGraph_unique x t' t h' ht)

/-- The structural term of a program code (the binary numeral `binNumeralMeta x` on non-programs). -/
noncomputable def codeTermMeta (x : ℕ) : ClosedSemiterm ℒₒᵣ 0 := Classical.choose (codeTermMetaGraph_existsUnique x).exists

lemma codeTermMeta_graph (x : ℕ) : CodeTermMetaGraph x (codeTermMeta x) := Classical.choose_spec (codeTermMetaGraph_existsUnique x).exists

lemma codeTermMeta_eq_of_graph {x : ℕ} {t : ClosedSemiterm ℒₒᵣ 0} (h : CodeTermMetaGraph x t) : codeTermMeta x = t :=
  codeTermMetaGraph_unique x _ _ (codeTermMeta_graph x) h

/-! #### The equations -/

lemma codeTermMeta_const (a : ℕ) : codeTermMeta (pConst a) = succTT (ppairTermMeta (binNumeralMeta 0) (binNumeralMeta a)) :=
  codeTermMeta_eq_of_graph (CodeTermMetaGraph.const_iff.mpr rfl)
lemma codeTermMeta_self : codeTermMeta pSelf = succTT (ppairTermMeta (binNumeralMeta 1) (binNumeralMeta 0)) :=
  codeTermMeta_eq_of_graph (CodeTermMetaGraph.self_iff.mpr rfl)
lemma codeTermMeta_opp : codeTermMeta pOpp = succTT (ppairTermMeta (binNumeralMeta 2) (binNumeralMeta 0)) :=
  codeTermMeta_eq_of_graph (CodeTermMetaGraph.opp_iff.mpr rfl)
lemma codeTermMeta_bot (p : ℕ) : codeTermMeta (pBot p) = succTT (ppairTermMeta (binNumeralMeta 3) (codeTermMeta p)) :=
  codeTermMeta_eq_of_graph (CodeTermMetaGraph.bot_iff.mpr ⟨_, codeTermMeta_graph p, rfl⟩)
lemma codeTermMeta_sim (p q : ℕ) : codeTermMeta (pSim p q) = succTT (ppairTermMeta (binNumeralMeta 4) (ppairTermMeta (codeTermMeta p) (codeTermMeta q))) :=
  codeTermMeta_eq_of_graph (CodeTermMetaGraph.sim_iff.mpr ⟨_, _, codeTermMeta_graph p, codeTermMeta_graph q, rfl⟩)
lemma codeTermMeta_ite (b a p q : ℕ) :
    codeTermMeta (pIte b a p q) =
    succTT (ppairTermMeta (binNumeralMeta 5) (ppairTermMeta (codeTermMeta b) (ppairTermMeta (binNumeralMeta a) (ppairTermMeta (codeTermMeta p) (codeTermMeta q))))) :=
  codeTermMeta_eq_of_graph (CodeTermMetaGraph.ite_iff.mpr ⟨_, _, _, codeTermMeta_graph b, codeTermMeta_graph p, codeTermMeta_graph q, rfl⟩)
lemma codeTermMeta_search (k g p q : ℕ) :
    codeTermMeta (pSearch k g p q) =
    succTT (ppairTermMeta (binNumeralMeta 6) (ppairTermMeta (binNumeralMeta k) (ppairTermMeta (binNumeralMeta g) (ppairTermMeta (codeTermMeta p) (codeTermMeta q))))) :=
  codeTermMeta_eq_of_graph (CodeTermMetaGraph.search_iff.mpr ⟨_, _, codeTermMeta_graph p, codeTermMeta_graph q, rfl⟩)
lemma codeTermMeta_of_not_shape {x : ℕ} (hx : ¬IsShape x) : codeTermMeta x = binNumeralMeta x :=
  codeTermMeta_eq_of_graph ((CodeTermMetaGraph.of_not_shape hx).mpr rfl)

/-! #### The code equation -/

lemma quote_binNumeralMeta_nat (n : ℕ) : (⌜binNumeralMeta n⌝ : ℕ) = binNumeral n := by rw [quote_binNumeralMeta]; simp

/-- `codeTerm` is absolute: its value on a cast is the cast of its value (a Σ₁-definable function). -/
lemma cast_codeTerm (x : ℕ) : ((codeTerm x : ℕ) : V) = codeTerm (x : V) := by
  have := DefinedFunction.shigmaOne_absolute_func V (codeTerm.defined (V := ℕ)) (codeTerm.defined (V := V)) ![x]
  simpa [Function.comp_def] using this

section cast

lemma cast_ppair (x y : ℕ) : ((ppair x y : ℕ) : V) = ppair (x : V) (y : V) := by
  unfold ppair; push_cast; rfl
lemma cast_pConst (a : ℕ) : ((pConst a : ℕ) : V) = pConst (a : V) := by
  unfold pConst; push_cast [cast_ppair]; rfl
lemma cast_pSelf : ((pSelf : ℕ) : V) = pSelf := by
  unfold pSelf; push_cast [cast_ppair]; rfl
lemma cast_pOpp : ((pOpp : ℕ) : V) = pOpp := by
  unfold pOpp; push_cast [cast_ppair]; rfl
lemma cast_pBot (p : ℕ) : ((pBot p : ℕ) : V) = pBot (p : V) := by
  unfold pBot; push_cast [cast_ppair]; rfl
lemma cast_pSim (p q : ℕ) : ((pSim p q : ℕ) : V) = pSim (p : V) (q : V) := by
  unfold pSim; push_cast [cast_ppair]; rfl
lemma cast_pIte (b a p q : ℕ) : ((pIte b a p q : ℕ) : V) = pIte (b : V) (a : V) (p : V) (q : V) := by
  unfold pIte; push_cast [cast_ppair]; rfl
lemma cast_pSearch (k g p q : ℕ) : ((pSearch k g p q : ℕ) : V) = pSearch (k : V) (g : V) (p : V) (q : V) := by
  unfold pSearch; push_cast [cast_ppair]; rfl

end cast

/-- **The code equation**: the code of the structural term is the internal `codeTerm`, in every model. -/
theorem quote_codeTermMeta (x : ℕ) : (⌜codeTermMeta x⌝ : V) = codeTerm (x : V) := by
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    by_cases hx : IsShape x
    · rcases hx with ⟨a, rfl⟩ | rfl | rfl | ⟨p, rfl⟩ | ⟨p, q, rfl⟩ | ⟨b, a, p, q, rfl⟩ | ⟨k, g, p, q, rfl⟩
      · rw [codeTermMeta_const, quote_succTT, quote_ppairTermMeta, quote_binNumeralMeta, quote_binNumeralMeta, cast_pConst, codeTerm_const]
        push_cast; rfl
      · rw [codeTermMeta_self, quote_succTT, quote_ppairTermMeta, quote_binNumeralMeta, quote_binNumeralMeta, cast_pSelf, codeTerm_self]
        push_cast; rfl
      · rw [codeTermMeta_opp, quote_succTT, quote_ppairTermMeta, quote_binNumeralMeta, quote_binNumeralMeta, cast_pOpp, codeTerm_opp]
        push_cast; rfl
      · rw [codeTermMeta_bot, quote_succTT, quote_ppairTermMeta, quote_binNumeralMeta, ih p (by simp), cast_pBot, codeTerm_bot]
        push_cast; rfl
      · rw [codeTermMeta_sim, quote_succTT, quote_ppairTermMeta, quote_ppairTermMeta, quote_binNumeralMeta, ih p (by simp),
          ih q (by simp), cast_pSim, codeTerm_sim]
        push_cast; rfl
      · rw [codeTermMeta_ite, quote_succTT, quote_ppairTermMeta, quote_ppairTermMeta, quote_ppairTermMeta, quote_ppairTermMeta,
          quote_binNumeralMeta, quote_binNumeralMeta, ih b (by simp), ih p (by simp), ih q (by simp), cast_pIte, codeTerm_ite]
        push_cast; rfl
      · rw [codeTermMeta_search, quote_succTT, quote_ppairTermMeta, quote_ppairTermMeta, quote_ppairTermMeta, quote_ppairTermMeta,
          quote_binNumeralMeta, quote_binNumeralMeta, quote_binNumeralMeta, ih p (by simp), ih q (by simp), cast_pSearch, codeTerm_search]
        push_cast; rfl
    · have h1 : (⌜codeTermMeta x⌝ : V) = ((⌜codeTermMeta x⌝ : ℕ) : V) := by
        rw [Semiterm.empty_quote_def, Semiterm.empty_quote_def, Semiterm.coe_quote_eq_quote]
      rw [h1, codeTermMeta_of_not_shape hx, quote_binNumeralMeta_nat, ← codeTerm_of_not_shape hx, cast_codeTerm]

/-- The code equation in `ℕ`. -/
theorem quote_codeTermMeta_nat (x : ℕ) : (⌜codeTermMeta x⌝ : ℕ) = codeTerm x := by rw [quote_codeTermMeta]; simp

/-! #### The truth equation -/

/-- **The truth equation**: the structural term of `x` denotes `x` in `ℕ`. -/
theorem val_codeTermMeta (x : ℕ) : (codeTermMeta x).val (s := standardModel ℕ) ![] Empty.elim = x := by
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    by_cases hx : IsShape x
    · rcases hx with ⟨a, rfl⟩ | rfl | rfl | ⟨p, rfl⟩ | ⟨p, q, rfl⟩ | ⟨b, a, p, q, rfl⟩ | ⟨k, g, p, q, rfl⟩
      · rw [codeTermMeta_const, val_succTT, val_ppairTermMeta, val_binNumeralMeta, val_binNumeralMeta]; rfl
      · rw [codeTermMeta_self, val_succTT, val_ppairTermMeta, val_binNumeralMeta, val_binNumeralMeta]; rfl
      · rw [codeTermMeta_opp, val_succTT, val_ppairTermMeta, val_binNumeralMeta, val_binNumeralMeta]; rfl
      · rw [codeTermMeta_bot, val_succTT, val_ppairTermMeta, val_binNumeralMeta, ih p (by simp)]; rfl
      · rw [codeTermMeta_sim, val_succTT, val_ppairTermMeta, val_ppairTermMeta, val_binNumeralMeta, ih p (by simp), ih q (by simp)]; rfl
      · rw [codeTermMeta_ite, val_succTT, val_ppairTermMeta, val_ppairTermMeta, val_ppairTermMeta, val_ppairTermMeta, val_binNumeralMeta, val_binNumeralMeta,
          ih b (by simp), ih p (by simp), ih q (by simp)]; rfl
      · rw [codeTermMeta_search, val_succTT, val_ppairTermMeta, val_ppairTermMeta, val_ppairTermMeta, val_ppairTermMeta, val_binNumeralMeta,
          val_binNumeralMeta, val_binNumeralMeta, ih p (by simp), ih q (by simp)]; rfl
    · rw [codeTermMeta_of_not_shape hx, val_binNumeralMeta]

/-! #### The length bounds -/

/-- A closed `ℒₒᵣ`-term denotes less than `2 ^ (its length)`. -/
private lemma add_lt_mul_two {a b A B : ℕ} (ha : a < A) (hb : b < B) : a + b < A * B * 2 := by
  have h1 : A ≤ A * B := Nat.le_mul_of_pos_right _ (by omega)
  have h2 : B ≤ A * B := Nat.le_mul_of_pos_left _ (by omega)
  omega

private lemma mul_lt_mul_two {a b A B : ℕ} (ha : a < A) (hb : b < B) : a * b < A * B * 2 :=
  calc a * b ≤ a * B := Nat.mul_le_mul_left _ hb.le
    _ < A * B := Nat.mul_lt_mul_of_pos_right ha (by omega)
    _ ≤ A * B * 2 := Nat.le_mul_of_pos_right _ (by norm_num)

theorem val_lt_two_pow_termLenMeta : ∀ t : ClosedSemiterm ℒₒᵣ 0,
    t.val (s := standardModel ℕ) ![] Empty.elim < 2 ^ termLenMeta (Rew.emb t : SyntacticSemiterm ℒₒᵣ 0)
  | #x => x.elim0
  | &x => x.elim
  | .func f v => by
    have ih : ∀ i, (v i).val (s := standardModel ℕ) ![] Empty.elim < 2 ^ termLenMeta (Rew.emb (v i) : SyntacticSemiterm ℒₒᵣ 0) :=
      fun i ↦ val_lt_two_pow_termLenMeta (v i)
    rw [Rew.func, termLenMeta_func, Semiterm.val_func]
    cases f with
    | zero => show 0 < 2 ^ _; exact Nat.two_pow_pos _
    | one => show 1 < 2 ^ (_ + 1); exact Nat.one_lt_two_pow (Nat.succ_ne_zero _)
    | add =>
      show (v 0).val ![] Empty.elim + (v 1).val ![] Empty.elim < 2 ^ (_ + 1)
      rw [Fin.sum_univ_two, Nat.pow_succ, Nat.pow_add]
      exact add_lt_mul_two (ih 0) (ih 1)
    | mul =>
      show (v 0).val ![] Empty.elim * (v 1).val ![] Empty.elim < 2 ^ (_ + 1)
      rw [Fin.sum_univ_two, Nat.pow_succ, Nat.pow_add]
      exact mul_lt_mul_two (ih 0) (ih 1)

/-- **The lower bound**: the structural term of `x` has at least `size x` symbols (it denotes `x`). -/
theorem size_le_termLenMeta_codeTermMeta (x : ℕ) : Nat.size x ≤ termLenMeta (Rew.emb (codeTermMeta x) : SyntacticSemiterm ℒₒᵣ 0) := by
  rw [Nat.size_le]
  have := val_lt_two_pow_termLenMeta (codeTermMeta x)
  rwa [val_codeTermMeta] at this

/-- The upper bounds for the shapes, in terms of the leaves (`ppairTermMeta` writes `s` twice and `t`
three times, `succTT` adds two symbols). -/
lemma termLenMeta_emb_codeTermMeta_const (a : ℕ) :
    termLenMeta (Rew.emb (codeTermMeta (pConst a)) : SyntacticSemiterm ℒₒᵣ 0) =
    2 * termLenMeta (Rew.emb (binNumeralMeta 0) : SyntacticSemiterm ℒₒᵣ 0) + 3 * termLenMeta (Rew.emb (binNumeralMeta a) : SyntacticSemiterm ℒₒᵣ 0) + 6 := by
  rw [codeTermMeta_const, termLenMeta_emb_succTT, termLenMeta_emb_ppairTermMeta]

lemma termLenMeta_emb_codeTermMeta_bot (p : ℕ) :
    termLenMeta (Rew.emb (codeTermMeta (pBot p)) : SyntacticSemiterm ℒₒᵣ 0) =
    2 * termLenMeta (Rew.emb (binNumeralMeta 3) : SyntacticSemiterm ℒₒᵣ 0) + 3 * termLenMeta (Rew.emb (codeTermMeta p) : SyntacticSemiterm ℒₒᵣ 0) + 6 := by
  rw [codeTermMeta_bot, termLenMeta_emb_succTT, termLenMeta_emb_ppairTermMeta]

lemma termLenMeta_emb_codeTermMeta_sim (p q : ℕ) :
    termLenMeta (Rew.emb (codeTermMeta (pSim p q)) : SyntacticSemiterm ℒₒᵣ 0) =
    2 * termLenMeta (Rew.emb (binNumeralMeta 4) : SyntacticSemiterm ℒₒᵣ 0) +
      6 * termLenMeta (Rew.emb (codeTermMeta p) : SyntacticSemiterm ℒₒᵣ 0) + 9 * termLenMeta (Rew.emb (codeTermMeta q) : SyntacticSemiterm ℒₒᵣ 0) + 18 := by
  rw [codeTermMeta_sim, termLenMeta_emb_succTT, termLenMeta_emb_ppairTermMeta, termLenMeta_emb_ppairTermMeta]; ring

lemma termLenMeta_emb_codeTermMeta_ite (b a p q : ℕ) :
    termLenMeta (Rew.emb (codeTermMeta (pIte b a p q)) : SyntacticSemiterm ℒₒᵣ 0) =
    2 * termLenMeta (Rew.emb (binNumeralMeta 5) : SyntacticSemiterm ℒₒᵣ 0) +
      6 * termLenMeta (Rew.emb (codeTermMeta b) : SyntacticSemiterm ℒₒᵣ 0) + 18 * termLenMeta (Rew.emb (binNumeralMeta a) : SyntacticSemiterm ℒₒᵣ 0) +
      54 * termLenMeta (Rew.emb (codeTermMeta p) : SyntacticSemiterm ℒₒᵣ 0) + 81 * termLenMeta (Rew.emb (codeTermMeta q) : SyntacticSemiterm ℒₒᵣ 0) + 162 := by
  rw [codeTermMeta_ite, termLenMeta_emb_succTT, termLenMeta_emb_ppairTermMeta, termLenMeta_emb_ppairTermMeta, termLenMeta_emb_ppairTermMeta, termLenMeta_emb_ppairTermMeta]; ring

/-- The searcher's term: `2 · |binNumeralMeta 6| + 6 · |binNumeralMeta k| + 18 · |binNumeralMeta g| + 54 · |codeTermMeta p| + 81 · |codeTermMeta q| + 162`. -/
lemma termLenMeta_emb_codeTermMeta_search (k g p q : ℕ) :
    termLenMeta (Rew.emb (codeTermMeta (pSearch k g p q)) : SyntacticSemiterm ℒₒᵣ 0) =
    2 * termLenMeta (Rew.emb (binNumeralMeta 6) : SyntacticSemiterm ℒₒᵣ 0) +
      6 * termLenMeta (Rew.emb (binNumeralMeta k) : SyntacticSemiterm ℒₒᵣ 0) + 18 * termLenMeta (Rew.emb (binNumeralMeta g) : SyntacticSemiterm ℒₒᵣ 0) +
      54 * termLenMeta (Rew.emb (codeTermMeta p) : SyntacticSemiterm ℒₒᵣ 0) + 81 * termLenMeta (Rew.emb (codeTermMeta q) : SyntacticSemiterm ℒₒᵣ 0) + 162 := by
  rw [codeTermMeta_search, termLenMeta_emb_succTT, termLenMeta_emb_ppairTermMeta, termLenMeta_emb_ppairTermMeta, termLenMeta_emb_ppairTermMeta, termLenMeta_emb_ppairTermMeta]; ring

end metaTerms

end ArithS
