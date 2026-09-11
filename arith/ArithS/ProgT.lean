import ArithS.Bnum

/-!
# ArithS.ProgT — programs described by TERMS over the polynomial pairing

Roadmap M4, item U0 (`M4_BOUNDED_HBL/BRIEF.md` §2). A program `x` used to enter a guard
sentence as the binary numeral `bnum (dnum x)` of its WHOLE code; the numeral of
`pSearch k g p q` is not the numeral of `k` inside any fixed term, so a searcher's guard was
the `k`-instance of NO formula. Since the codes are built on the term-expressible pairing
`ppair x y = (x + y)² + y` (`ArithS.Prog`), a program can instead be described by the
STRUCTURAL TERM of its code, with the budget `k` and the template code `g` as binary-numeral
leaves:

* `ppairT s t := ((s ^+ t) ^* (s ^+ t)) ^+ t` on term codes (the term of `ppair`);
* `progT : V → V` (a Σ₁ function, the graph of a StrongFinite fixpoint on pairs `⟪x, t⟫`
  exactly like `relabel`): `progT (pConst a) = ppairT (bnum 0) (bnum a) ^+ (𝟏 : V)`, …,
  `progT (pSearch k g p q) = ppairT (bnum 6) (ppairT (bnum k) (ppairT (bnum g)
  (ppairT (progT p) (progT q)))) ^+ (𝟏 : V)`, and `progT x = bnum x` on non-shapes (total);
  `progT x` is a closed `ℒₒᵣ`-term code;
* the meta twin `progTT : ℕ → ClosedSemiterm ℒₒᵣ 0` (the same recursion on the syntax, via
  the inductive graph `ProgTTGraph`), with the code equation `⌜progTT x⌝ = progT x` in every
  model, the truth equation `val (progTT x) = x` in `ℕ` (the term DENOTES the code — this is
  where `ppair` being a term pays off), `lMap`-invariance, and the length bounds: the exact
  `tlen (ppairTT s t) = 2 · tlen s + 3 · tlen t + 4` per pairing (upper bounds for every shape
  in terms of the leaves) and the lower bound `size x ≤ tlen (progTT x)`.
-/

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ### The pairing on term codes -/

/-- The term code of `(s + t) * (s + t) + t`. -/
noncomputable def ppairT (s t : V) : V := ((s ^+ t) ^* (s ^+ t)) ^+ t

def ppairTGraph : 𝚺₁.Semisentence 3 :=
  .mkSigma “r s t. ∃ st, !qqAddGraph st s t ∧ ∃ sq, !qqMulGraph sq st st ∧ !qqAddGraph r sq t”

instance ppairT.defined : 𝚺₁-Function₂ (ppairT : V → V → V) via ppairTGraph := .mk fun v ↦ by
  simp [ppairTGraph, ppairT]

instance ppairT.definable : 𝚺₁-Function₂ (ppairT : V → V → V) := ppairT.defined.to_definable

instance ppairT.definable' : Γ-[m + 1]-Function₂ (ppairT : V → V → V) := ppairT.definable.of_sigmaOne

@[simp] lemma lt_ppairT_left (s t : V) : s < ppairT s t :=
  lt_trans (lt_qqAdd_left s t) (lt_trans (lt_qqMul_left _ _) (lt_qqAdd_left _ _))

@[simp] lemma lt_ppairT_right (s t : V) : t < ppairT s t := lt_qqAdd_right _ _

lemma lt_ppairT_succ_left (s t : V) : s < ppairT s t ^+ (𝟏 : V) :=
  lt_trans (lt_ppairT_left s t) (lt_qqAdd_left _ _)

lemma lt_ppairT_succ_right (s t : V) : t < ppairT s t ^+ (𝟏 : V) :=
  lt_trans (lt_ppairT_right s t) (lt_qqAdd_left _ _)

lemma ppairT_semiterm {k s t : V} (hs : IsSemiterm ℒₒᵣ k s) (ht : IsSemiterm ℒₒᵣ k t) :
    IsSemiterm ℒₒᵣ k (ppairT s t) := by
  simp [ppairT, qqAdd, qqMul, hs, ht]

lemma succ_semiterm {k t : V} (ht : IsSemiterm ℒₒᵣ k t) : IsSemiterm ℒₒᵣ k (t ^+ (𝟏 : V)) := by
  simp [qqAdd, ht]

/-! ### The graph, as a fixpoint on pairs `⟪x, t⟫` -/

namespace ProgT

/-- `Phi C ⟪x, t⟫`: `t` is the structural term of the program code `x`, given the sub-results
in `C`. -/
def Phi (C : Set V) (pr : V) : Prop :=
  (∃ a : V, pr = ⟪pConst a, ppairT (bnum 0) (bnum a) ^+ (𝟏 : V)⟫) ∨
  pr = ⟪(pSelf : V), ppairT (bnum 1) (bnum 0) ^+ (𝟏 : V)⟫ ∨
  pr = ⟪(pOpp : V), ppairT (bnum 2) (bnum 0) ^+ (𝟏 : V)⟫ ∨
  (∃ p tp : V, ⟪p, tp⟫ ∈ C ∧ pr = ⟪pBot p, ppairT (bnum 3) tp ^+ (𝟏 : V)⟫) ∨
  (∃ p q tp tq : V, ⟪p, tp⟫ ∈ C ∧ ⟪q, tq⟫ ∈ C ∧
    pr = ⟪pSim p q, ppairT (bnum 4) (ppairT tp tq) ^+ (𝟏 : V)⟫) ∨
  (∃ b a p q tb tp tq : V, ⟪b, tb⟫ ∈ C ∧ ⟪p, tp⟫ ∈ C ∧ ⟪q, tq⟫ ∈ C ∧
    pr = ⟪pIte b a p q, ppairT (bnum 5) (ppairT tb (ppairT (bnum a) (ppairT tp tq))) ^+ (𝟏 : V)⟫) ∨
  (∃ k g p q tp tq : V, ⟪p, tp⟫ ∈ C ∧ ⟪q, tq⟫ ∈ C ∧
    pr = ⟪pSearch k g p q, ppairT (bnum 6) (ppairT (bnum k) (ppairT (bnum g) (ppairT tp tq))) ^+ (𝟏 : V)⟫) ∨
  (∃ x : V, ¬IsShape x ∧ pr = ⟪x, bnum x⟫)

noncomputable def blueprint : Fixpoint.Blueprint 0 := ⟨.mkDelta
  (.mkSigma “pr C. ∃ x <⁺ pr, ∃ t <⁺ pr, !pairDef pr x t ∧
    ( (∃ a < x, !pConstGraph x a ∧
        ∃ b0, !bnumGraph b0 0 ∧ ∃ ba, !bnumGraph ba a ∧ ∃ r, !ppairTGraph r b0 ba ∧ !qqAddGraph t r ↑Arithmetic.one) ∨
      (!pSelfGraph x ∧
        ∃ b1, !bnumGraph b1 1 ∧ ∃ b0, !bnumGraph b0 0 ∧ ∃ r, !ppairTGraph r b1 b0 ∧ !qqAddGraph t r ↑Arithmetic.one) ∨
      (!pOppGraph x ∧
        ∃ b2, !bnumGraph b2 2 ∧ ∃ b0, !bnumGraph b0 0 ∧ ∃ r, !ppairTGraph r b2 b0 ∧ !qqAddGraph t r ↑Arithmetic.one) ∨
      (∃ p < x, !pBotGraph x p ∧ ∃ tp < t, :⟪p, tp⟫:∈ C ∧
        ∃ b3, !bnumGraph b3 3 ∧ ∃ r, !ppairTGraph r b3 tp ∧ !qqAddGraph t r ↑Arithmetic.one) ∨
      (∃ p < x, ∃ q < x, !pSimGraph x p q ∧ ∃ tp < t, ∃ tq < t, :⟪p, tp⟫:∈ C ∧ :⟪q, tq⟫:∈ C ∧
        ∃ b4, !bnumGraph b4 4 ∧ ∃ r1, !ppairTGraph r1 tp tq ∧ ∃ r, !ppairTGraph r b4 r1 ∧
        !qqAddGraph t r ↑Arithmetic.one) ∨
      (∃ b < x, ∃ a < x, ∃ p < x, ∃ q < x, !pIteGraph x b a p q ∧
        ∃ tb < t, ∃ tp < t, ∃ tq < t, :⟪b, tb⟫:∈ C ∧ :⟪p, tp⟫:∈ C ∧ :⟪q, tq⟫:∈ C ∧
        ∃ b5, !bnumGraph b5 5 ∧ ∃ ba, !bnumGraph ba a ∧ ∃ r1, !ppairTGraph r1 tp tq ∧
        ∃ r2, !ppairTGraph r2 ba r1 ∧ ∃ r3, !ppairTGraph r3 tb r2 ∧ ∃ r, !ppairTGraph r b5 r3 ∧
        !qqAddGraph t r ↑Arithmetic.one) ∨
      (∃ k < x, ∃ g < x, ∃ p < x, ∃ q < x, !pSearchGraph x k g p q ∧
        ∃ tp < t, ∃ tq < t, :⟪p, tp⟫:∈ C ∧ :⟪q, tq⟫:∈ C ∧
        ∃ b6, !bnumGraph b6 6 ∧ ∃ bk, !bnumGraph bk k ∧ ∃ bg, !bnumGraph bg g ∧
        ∃ r1, !ppairTGraph r1 tp tq ∧ ∃ r2, !ppairTGraph r2 bg r1 ∧ ∃ r3, !ppairTGraph r3 bk r2 ∧
        ∃ r, !ppairTGraph r b6 r3 ∧ !qqAddGraph t r ↑Arithmetic.one) ∨
      (¬!isShape x ∧ !bnumGraph t x) )”)
  (.mkPi “pr C. ∃ x <⁺ pr, ∃ t <⁺ pr, !pairDef pr x t ∧
    ( (∃ a < x, !pConstGraph x a ∧
        ∀ b0, !bnumGraph b0 0 → ∀ ba, !bnumGraph ba a → ∀ r, !ppairTGraph r b0 ba → ∀ s, !qqAddGraph s r ↑Arithmetic.one → t = s) ∨
      (!pSelfGraph x ∧
        ∀ b1, !bnumGraph b1 1 → ∀ b0, !bnumGraph b0 0 → ∀ r, !ppairTGraph r b1 b0 → ∀ s, !qqAddGraph s r ↑Arithmetic.one → t = s) ∨
      (!pOppGraph x ∧
        ∀ b2, !bnumGraph b2 2 → ∀ b0, !bnumGraph b0 0 → ∀ r, !ppairTGraph r b2 b0 → ∀ s, !qqAddGraph s r ↑Arithmetic.one → t = s) ∨
      (∃ p < x, !pBotGraph x p ∧ ∃ tp < t, :⟪p, tp⟫:∈ C ∧
        ∀ b3, !bnumGraph b3 3 → ∀ r, !ppairTGraph r b3 tp → ∀ s, !qqAddGraph s r ↑Arithmetic.one → t = s) ∨
      (∃ p < x, ∃ q < x, !pSimGraph x p q ∧ ∃ tp < t, ∃ tq < t, :⟪p, tp⟫:∈ C ∧ :⟪q, tq⟫:∈ C ∧
        ∀ b4, !bnumGraph b4 4 → ∀ r1, !ppairTGraph r1 tp tq → ∀ r, !ppairTGraph r b4 r1 →
        ∀ s, !qqAddGraph s r ↑Arithmetic.one → t = s) ∨
      (∃ b < x, ∃ a < x, ∃ p < x, ∃ q < x, !pIteGraph x b a p q ∧
        ∃ tb < t, ∃ tp < t, ∃ tq < t, :⟪b, tb⟫:∈ C ∧ :⟪p, tp⟫:∈ C ∧ :⟪q, tq⟫:∈ C ∧
        ∀ b5, !bnumGraph b5 5 → ∀ ba, !bnumGraph ba a → ∀ r1, !ppairTGraph r1 tp tq →
        ∀ r2, !ppairTGraph r2 ba r1 → ∀ r3, !ppairTGraph r3 tb r2 → ∀ r, !ppairTGraph r b5 r3 →
        ∀ s, !qqAddGraph s r ↑Arithmetic.one → t = s) ∨
      (∃ k < x, ∃ g < x, ∃ p < x, ∃ q < x, !pSearchGraph x k g p q ∧
        ∃ tp < t, ∃ tq < t, :⟪p, tp⟫:∈ C ∧ :⟪q, tq⟫:∈ C ∧
        ∀ b6, !bnumGraph b6 6 → ∀ bk, !bnumGraph bk k → ∀ bg, !bnumGraph bg g →
        ∀ r1, !ppairTGraph r1 tp tq → ∀ r2, !ppairTGraph r2 bg r1 → ∀ r3, !ppairTGraph r3 bk r2 →
        ∀ r, !ppairTGraph r b6 r3 → ∀ s, !qqAddGraph s r ↑Arithmetic.one → t = s) ∨
      (¬!isShape x ∧ ∀ s, !bnumGraph s x → t = s) )”)⟩

/-- `Phi` with the bounds the blueprint carries. -/
private lemma phi_iff (C pr : V) :
    Phi {x | x ∈ C} pr ↔
    ∃ x ≤ pr, ∃ t ≤ pr, pr = ⟪x, t⟫ ∧
    ( (∃ a < x, x = pConst a ∧ t = ppairT (bnum 0) (bnum a) ^+ (𝟏 : V)) ∨
      (x = pSelf ∧ t = ppairT (bnum 1) (bnum 0) ^+ (𝟏 : V)) ∨
      (x = pOpp ∧ t = ppairT (bnum 2) (bnum 0) ^+ (𝟏 : V)) ∨
      (∃ p < x, x = pBot p ∧ ∃ tp < t, ⟪p, tp⟫ ∈ C ∧ t = ppairT (bnum 3) tp ^+ (𝟏 : V)) ∨
      (∃ p < x, ∃ q < x, x = pSim p q ∧ ∃ tp < t, ∃ tq < t, ⟪p, tp⟫ ∈ C ∧ ⟪q, tq⟫ ∈ C ∧
        t = ppairT (bnum 4) (ppairT tp tq) ^+ (𝟏 : V)) ∨
      (∃ b < x, ∃ a < x, ∃ p < x, ∃ q < x, x = pIte b a p q ∧
        ∃ tb < t, ∃ tp < t, ∃ tq < t, ⟪b, tb⟫ ∈ C ∧ ⟪p, tp⟫ ∈ C ∧ ⟪q, tq⟫ ∈ C ∧
        t = ppairT (bnum 5) (ppairT tb (ppairT (bnum a) (ppairT tp tq))) ^+ (𝟏 : V)) ∨
      (∃ k < x, ∃ g < x, ∃ p < x, ∃ q < x, x = pSearch k g p q ∧
        ∃ tp < t, ∃ tq < t, ⟪p, tp⟫ ∈ C ∧ ⟪q, tq⟫ ∈ C ∧
        t = ppairT (bnum 6) (ppairT (bnum k) (ppairT (bnum g) (ppairT tp tq))) ^+ (𝟏 : V)) ∨
      (¬IsShape x ∧ t = bnum x) ) := by
  constructor
  · rintro (⟨a, rfl⟩ | rfl | rfl | ⟨p, tp, h, rfl⟩ | ⟨p, q, tp, tq, hp, hq, rfl⟩ |
      ⟨b, a, p, q, tb, tp, tq, hb, hp, hq, rfl⟩ | ⟨k, g, p, q, tp, tq, hp, hq, rfl⟩ | ⟨x, hx, rfl⟩)
    · exact ⟨_, by simp, _, by simp, rfl, Or.inl ⟨a, by simp, rfl, rfl⟩⟩
    · exact ⟨_, by simp, _, by simp, rfl, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
    · exact ⟨_, by simp, _, by simp, rfl, Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩
    · exact ⟨_, by simp, _, by simp, rfl, Or.inr (Or.inr (Or.inr (Or.inl
        ⟨p, by simp, rfl, tp, lt_ppairT_succ_right _ _, h, rfl⟩)))⟩
    · exact ⟨_, by simp, _, by simp, rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨p, by simp, q, by simp, rfl, tp, lt_trans (lt_ppairT_left _ _) (lt_ppairT_succ_right _ _),
          tq, lt_trans (lt_ppairT_right _ _) (lt_ppairT_succ_right _ _), hp, hq, rfl⟩))))⟩
    · exact ⟨_, by simp, _, by simp, rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨b, by simp, a, by simp, p, by simp, q, by simp, rfl,
          tb, lt_trans (lt_ppairT_left _ _) (lt_ppairT_succ_right _ _),
          tp, lt_trans (lt_ppairT_left _ _) (lt_trans (lt_ppairT_right _ _)
            (lt_trans (lt_ppairT_right _ _) (lt_ppairT_succ_right _ _))),
          tq, lt_trans (lt_ppairT_right _ _) (lt_trans (lt_ppairT_right _ _)
            (lt_trans (lt_ppairT_right _ _) (lt_ppairT_succ_right _ _))),
          hb, hp, hq, rfl⟩)))))⟩
    · exact ⟨_, by simp, _, by simp, rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨k, by simp, g, by simp, p, by simp, q, by simp, rfl,
          tp, lt_trans (lt_ppairT_left _ _) (lt_trans (lt_ppairT_right _ _)
            (lt_trans (lt_ppairT_right _ _) (lt_ppairT_succ_right _ _))),
          tq, lt_trans (lt_ppairT_right _ _) (lt_trans (lt_ppairT_right _ _)
            (lt_trans (lt_ppairT_right _ _) (lt_ppairT_succ_right _ _))),
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
      simp [blueprint, HierarchySymbol.Semiformula.val_sigma, bnum.defined.df, ppairT.defined.df,
        qqAdd_defined.iff, numeral_eq_natCast]
    · intro v
      symm
      simpa [blueprint, HierarchySymbol.Semiformula.val_sigma, bnum.defined.df, ppairT.defined.df,
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
        ⟨h, pair_lt_pair (by simp) (lt_ppairT_succ_right _ _)⟩, rfl⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, q, tp, tq,
        ⟨hp, pair_lt_pair (by simp) (lt_trans (lt_ppairT_left _ _) (lt_ppairT_succ_right _ _))⟩,
        ⟨hq, pair_lt_pair (by simp) (lt_trans (lt_ppairT_right _ _) (lt_ppairT_succ_right _ _))⟩, rfl⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨b, a, p, q, tb, tp, tq,
        ⟨hb, pair_lt_pair (by simp) (lt_trans (lt_ppairT_left _ _) (lt_ppairT_succ_right _ _))⟩,
        ⟨hp, pair_lt_pair (by simp) (lt_trans (lt_ppairT_left _ _) (lt_trans (lt_ppairT_right _ _)
            (lt_trans (lt_ppairT_right _ _) (lt_ppairT_succ_right _ _))))⟩,
        ⟨hq, pair_lt_pair (by simp) (lt_trans (lt_ppairT_right _ _) (lt_trans (lt_ppairT_right _ _)
            (lt_trans (lt_ppairT_right _ _) (lt_ppairT_succ_right _ _))))⟩, rfl⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨k, g, p, q, tp, tq,
        ⟨hp, pair_lt_pair (by simp) (lt_trans (lt_ppairT_left _ _) (lt_trans (lt_ppairT_right _ _)
            (lt_trans (lt_ppairT_right _ _) (lt_ppairT_succ_right _ _))))⟩,
        ⟨hq, pair_lt_pair (by simp) (lt_trans (lt_ppairT_right _ _) (lt_trans (lt_ppairT_right _ _)
            (lt_trans (lt_ppairT_right _ _) (lt_ppairT_succ_right _ _))))⟩, rfl⟩))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨x, hx, rfl⟩))))))

end ProgT

/-- `ProgTGraph x t`: `t` is the structural term code of the program code `x`. -/
def ProgTGraph (x t : V) : Prop := ProgT.construction.Fixpoint ![] ⟪x, t⟫

noncomputable def progTGraphDef : 𝚫₁.Semisentence 2 := .mkDelta
  (.mkSigma “x t. ∃ pr <⁺ (x + t + 1)², !pairDef pr x t ∧ !ProgT.blueprint.fixpointDefΔ₁.sigma pr”)
  (.mkPi “x t. ∀ pr <⁺ (x + t + 1)², !pairDef pr x t → !ProgT.blueprint.fixpointDefΔ₁.pi pr”)

section

private lemma fixpoint_param_eq (p : Fin 0 → V) (x : V) :
    ProgT.construction.Fixpoint p x = ProgT.construction.Fixpoint ![] x := by
  rw [Subsingleton.elim p ![]]

instance progTGraph_defined : 𝚫₁-Relation[V] ProgTGraph via progTGraphDef := .mk
  ⟨by intro v
      simp [progTGraphDef, HierarchySymbol.Semiformula.val_sigma,
        ProgT.construction.fixpoint_definedΔ₁.proper.iff', ProgT.construction.fixpoint_definedΔ₁.df]
      constructor
      · rintro h x _ rfl; rwa [fixpoint_param_eq] at h ⊢
      · intro h; have := h ⟪v 0, v 1⟫ (by simp) rfl; rwa [fixpoint_param_eq] at this ⊢,
   by intro v
      simp [progTGraphDef, HierarchySymbol.Semiformula.val_sigma,
        ProgT.construction.fixpoint_definedΔ₁.df, ProgTGraph]
      rw [fixpoint_param_eq]⟩

instance progTGraph_definable : 𝚫₁-Relation[V] ProgTGraph := progTGraph_defined.to_definable

instance progTGraph_definable' : Γ-[m + 1]-Relation[V] ProgTGraph := progTGraph_definable.of_deltaOne

end

/-! ### Case analysis and inversion -/

lemma ProgTGraph.case_iff {x t : V} :
    ProgTGraph x t ↔
    (∃ a, x = pConst a ∧ t = ppairT (bnum 0) (bnum a) ^+ (𝟏 : V)) ∨
    (x = pSelf ∧ t = ppairT (bnum 1) (bnum 0) ^+ (𝟏 : V)) ∨
    (x = pOpp ∧ t = ppairT (bnum 2) (bnum 0) ^+ (𝟏 : V)) ∨
    (∃ p tp, ProgTGraph p tp ∧ x = pBot p ∧ t = ppairT (bnum 3) tp ^+ (𝟏 : V)) ∨
    (∃ p q tp tq, ProgTGraph p tp ∧ ProgTGraph q tq ∧ x = pSim p q ∧
      t = ppairT (bnum 4) (ppairT tp tq) ^+ (𝟏 : V)) ∨
    (∃ b a p q tb tp tq, ProgTGraph b tb ∧ ProgTGraph p tp ∧ ProgTGraph q tq ∧ x = pIte b a p q ∧
      t = ppairT (bnum 5) (ppairT tb (ppairT (bnum a) (ppairT tp tq))) ^+ (𝟏 : V)) ∨
    (∃ k g p q tp tq, ProgTGraph p tp ∧ ProgTGraph q tq ∧ x = pSearch k g p q ∧
      t = ppairT (bnum 6) (ppairT (bnum k) (ppairT (bnum g) (ppairT tp tq))) ^+ (𝟏 : V)) ∨
    (¬IsShape x ∧ t = bnum x) :=
  Iff.trans ProgT.construction.case
    (by simp [show ProgT.construction.Φ = fun _ ↦ ProgT.Phi from rfl, ProgT.Phi, ProgTGraph])

section inversion

attribute [local simp] pConst pSelf pOpp pBot pSim pIte pSearch IsShape

lemma ProgTGraph.const_iff {a t : V} :
    ProgTGraph (pConst a) t ↔ t = ppairT (bnum 0) (bnum a) ^+ (𝟏 : V) := by
  rw [ProgTGraph.case_iff]; simp
lemma ProgTGraph.self_iff {t : V} : ProgTGraph pSelf t ↔ t = ppairT (bnum 1) (bnum 0) ^+ (𝟏 : V) := by
  rw [ProgTGraph.case_iff]; simp
lemma ProgTGraph.opp_iff {t : V} : ProgTGraph pOpp t ↔ t = ppairT (bnum 2) (bnum 0) ^+ (𝟏 : V) := by
  rw [ProgTGraph.case_iff]; simp
lemma ProgTGraph.bot_iff {p t : V} :
    ProgTGraph (pBot p) t ↔ ∃ tp, ProgTGraph p tp ∧ t = ppairT (bnum 3) tp ^+ (𝟏 : V) := by
  rw [ProgTGraph.case_iff]; simp
lemma ProgTGraph.sim_iff {p q t : V} :
    ProgTGraph (pSim p q) t ↔
    ∃ tp tq, ProgTGraph p tp ∧ ProgTGraph q tq ∧ t = ppairT (bnum 4) (ppairT tp tq) ^+ (𝟏 : V) := by
  rw [ProgTGraph.case_iff]; simp
lemma ProgTGraph.ite_iff {b a p q t : V} :
    ProgTGraph (pIte b a p q) t ↔
    ∃ tb tp tq, ProgTGraph b tb ∧ ProgTGraph p tp ∧ ProgTGraph q tq ∧
      t = ppairT (bnum 5) (ppairT tb (ppairT (bnum a) (ppairT tp tq))) ^+ (𝟏 : V) := by
  rw [ProgTGraph.case_iff]; simp
lemma ProgTGraph.search_iff {k g p q t : V} :
    ProgTGraph (pSearch k g p q) t ↔
    ∃ tp tq, ProgTGraph p tp ∧ ProgTGraph q tq ∧
      t = ppairT (bnum 6) (ppairT (bnum k) (ppairT (bnum g) (ppairT tp tq))) ^+ (𝟏 : V) := by
  rw [ProgTGraph.case_iff]; simp
lemma ProgTGraph.of_not_shape {x t : V} (hx : ¬IsShape x) : ProgTGraph x t ↔ t = bnum x := by
  rw [ProgTGraph.case_iff]
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

/-! ### `progT` is a total Σ₁ function -/

lemma progTGraph_exists (x : V) : ∃ t, ProgTGraph x t := by
  induction x using ISigma1.sigma1_order_induction with
  | hP => definability
  | ind x ih =>
    by_cases hx : IsShape x
    · rcases hx with ⟨a, rfl⟩ | rfl | rfl | ⟨p, rfl⟩ | ⟨p, q, rfl⟩ | ⟨b, a, p, q, rfl⟩ | ⟨k, g, p, q, rfl⟩
      · exact ⟨_, ProgTGraph.const_iff.mpr rfl⟩
      · exact ⟨_, ProgTGraph.self_iff.mpr rfl⟩
      · exact ⟨_, ProgTGraph.opp_iff.mpr rfl⟩
      · obtain ⟨tp, hp⟩ := ih p (by simp)
        exact ⟨_, ProgTGraph.bot_iff.mpr ⟨tp, hp, rfl⟩⟩
      · obtain ⟨tp, hp⟩ := ih p (by simp); obtain ⟨tq, hq⟩ := ih q (by simp)
        exact ⟨_, ProgTGraph.sim_iff.mpr ⟨tp, tq, hp, hq, rfl⟩⟩
      · obtain ⟨tb, hb⟩ := ih b (by simp); obtain ⟨tp, hp⟩ := ih p (by simp)
        obtain ⟨tq, hq⟩ := ih q (by simp)
        exact ⟨_, ProgTGraph.ite_iff.mpr ⟨tb, tp, tq, hb, hp, hq, rfl⟩⟩
      · obtain ⟨tp, hp⟩ := ih p (by simp); obtain ⟨tq, hq⟩ := ih q (by simp)
        exact ⟨_, ProgTGraph.search_iff.mpr ⟨tp, tq, hp, hq, rfl⟩⟩
    · exact ⟨_, (ProgTGraph.of_not_shape hx).mpr rfl⟩

lemma progTGraph_unique (x : V) : ∀ t₁ t₂, ProgTGraph x t₁ → ProgTGraph x t₂ → t₁ = t₂ := by
  induction x using ISigma1.pi1_order_induction with
  | hP => definability
  | ind x ih =>
    intro t₁ t₂ h₁ h₂
    by_cases hx : IsShape x
    · rcases hx with ⟨a, rfl⟩ | rfl | rfl | ⟨p, rfl⟩ | ⟨p, q, rfl⟩ | ⟨b, a, p, q, rfl⟩ | ⟨k, g, p, q, rfl⟩
      · rw [ProgTGraph.const_iff] at h₁ h₂; rw [h₁, h₂]
      · rw [ProgTGraph.self_iff] at h₁ h₂; rw [h₁, h₂]
      · rw [ProgTGraph.opp_iff] at h₁ h₂; rw [h₁, h₂]
      · rcases ProgTGraph.bot_iff.mp h₁ with ⟨p₁, hp₁, rfl⟩
        rcases ProgTGraph.bot_iff.mp h₂ with ⟨p₂, hp₂, rfl⟩
        rw [ih p (by simp) _ _ hp₁ hp₂]
      · rcases ProgTGraph.sim_iff.mp h₁ with ⟨p₁, q₁, hp₁, hq₁, rfl⟩
        rcases ProgTGraph.sim_iff.mp h₂ with ⟨p₂, q₂, hp₂, hq₂, rfl⟩
        rw [ih p (by simp) _ _ hp₁ hp₂, ih q (by simp) _ _ hq₁ hq₂]
      · rcases ProgTGraph.ite_iff.mp h₁ with ⟨b₁, p₁, q₁, hb₁, hp₁, hq₁, rfl⟩
        rcases ProgTGraph.ite_iff.mp h₂ with ⟨b₂, p₂, q₂, hb₂, hp₂, hq₂, rfl⟩
        rw [ih b (by simp) _ _ hb₁ hb₂, ih p (by simp) _ _ hp₁ hp₂, ih q (by simp) _ _ hq₁ hq₂]
      · rcases ProgTGraph.search_iff.mp h₁ with ⟨p₁, q₁, hp₁, hq₁, rfl⟩
        rcases ProgTGraph.search_iff.mp h₂ with ⟨p₂, q₂, hp₂, hq₂, rfl⟩
        rw [ih p (by simp) _ _ hp₁ hp₂, ih q (by simp) _ _ hq₁ hq₂]
    · rw [ProgTGraph.of_not_shape hx] at h₁ h₂; rw [h₁, h₂]

lemma progTGraph_existsUnique (x : V) : ∃! t, ProgTGraph x t := by
  rcases progTGraph_exists x with ⟨t, ht⟩
  exact ExistsUnique.intro t ht (fun t' h' ↦ progTGraph_unique x t' t h' ht)

/-- The structural term code of a program code (`bnum x` on non-programs). -/
noncomputable def progT (x : V) : V := Classical.choose! (progTGraph_existsUnique x)

lemma progT_graph (x : V) : ProgTGraph x (progT x) := Classical.choose!_spec (progTGraph_existsUnique x)

lemma progT_eq_of_graph {x t : V} (h : ProgTGraph x t) : progT x = t :=
  progTGraph_unique x _ _ (progT_graph x) h

noncomputable def progTGraph : 𝚺₁.Semisentence 2 := .mkSigma “t x. !progTGraphDef.sigma x t”

instance progT.defined : 𝚺₁-Function₁[V] progT via progTGraph := .mk fun v ↦ by
  simp [progTGraph, HierarchySymbol.Semiformula.val_sigma, progTGraph_defined.df]
  constructor
  · intro h; exact (progT_eq_of_graph h).symm
  · intro h; rw [h]; exact progT_graph _

instance progT.definable : 𝚺₁-Function₁[V] progT := progT.defined.to_definable

instance progT.definable' : Γ-[m + 1]-Function₁[V] progT := progT.definable.of_sigmaOne

/-! ### The equations -/

@[simp] lemma progT_const (a : V) : progT (pConst a) = ppairT (bnum 0) (bnum a) ^+ (𝟏 : V) :=
  progT_eq_of_graph (ProgTGraph.const_iff.mpr rfl)
@[simp] lemma progT_self : progT (pSelf : V) = ppairT (bnum 1) (bnum 0) ^+ (𝟏 : V) :=
  progT_eq_of_graph (ProgTGraph.self_iff.mpr rfl)
@[simp] lemma progT_opp : progT (pOpp : V) = ppairT (bnum 2) (bnum 0) ^+ (𝟏 : V) :=
  progT_eq_of_graph (ProgTGraph.opp_iff.mpr rfl)
@[simp] lemma progT_bot (p : V) : progT (pBot p) = ppairT (bnum 3) (progT p) ^+ (𝟏 : V) :=
  progT_eq_of_graph (ProgTGraph.bot_iff.mpr ⟨_, progT_graph p, rfl⟩)
@[simp] lemma progT_sim (p q : V) :
    progT (pSim p q) = ppairT (bnum 4) (ppairT (progT p) (progT q)) ^+ (𝟏 : V) :=
  progT_eq_of_graph (ProgTGraph.sim_iff.mpr ⟨_, _, progT_graph p, progT_graph q, rfl⟩)
@[simp] lemma progT_ite (b a p q : V) :
    progT (pIte b a p q) =
    ppairT (bnum 5) (ppairT (progT b) (ppairT (bnum a) (ppairT (progT p) (progT q)))) ^+ (𝟏 : V) :=
  progT_eq_of_graph (ProgTGraph.ite_iff.mpr ⟨_, _, _, progT_graph b, progT_graph p, progT_graph q, rfl⟩)
@[simp] lemma progT_search (k g p q : V) :
    progT (pSearch k g p q) =
    ppairT (bnum 6) (ppairT (bnum k) (ppairT (bnum g) (ppairT (progT p) (progT q)))) ^+ (𝟏 : V) :=
  progT_eq_of_graph (ProgTGraph.search_iff.mpr ⟨_, _, progT_graph p, progT_graph q, rfl⟩)
lemma progT_of_not_shape {x : V} (hx : ¬IsShape x) : progT x = bnum x :=
  progT_eq_of_graph ((ProgTGraph.of_not_shape hx).mpr rfl)

/-- `progT x` is a closed `ℒₒᵣ`-term (at every bound-variable count). -/
lemma progT_semiterm (k x : V) : IsSemiterm ℒₒᵣ k (progT x) := by
  induction x using ISigma1.pi1_order_induction with
  | hP => definability
  | ind x ih =>
    by_cases hx : IsShape x
    · rcases hx with ⟨a, rfl⟩ | rfl | rfl | ⟨p, rfl⟩ | ⟨p, q, rfl⟩ | ⟨b, a, p, q, rfl⟩ | ⟨k', g, p, q, rfl⟩
      · rw [progT_const]; exact succ_semiterm (ppairT_semiterm (bnum_semiterm k _) (bnum_semiterm k _))
      · rw [progT_self]; exact succ_semiterm (ppairT_semiterm (bnum_semiterm k _) (bnum_semiterm k _))
      · rw [progT_opp]; exact succ_semiterm (ppairT_semiterm (bnum_semiterm k _) (bnum_semiterm k _))
      · rw [progT_bot]; exact succ_semiterm (ppairT_semiterm (bnum_semiterm k _) (ih p (by simp)))
      · rw [progT_sim]
        exact succ_semiterm (ppairT_semiterm (bnum_semiterm k _)
          (ppairT_semiterm (ih p (by simp)) (ih q (by simp))))
      · rw [progT_ite]
        exact succ_semiterm (ppairT_semiterm (bnum_semiterm k _) (ppairT_semiterm (ih b (by simp))
          (ppairT_semiterm (bnum_semiterm k _) (ppairT_semiterm (ih p (by simp)) (ih q (by simp))))))
      · rw [progT_search]
        exact succ_semiterm (ppairT_semiterm (bnum_semiterm k _) (ppairT_semiterm (bnum_semiterm k _)
          (ppairT_semiterm (bnum_semiterm k _) (ppairT_semiterm (ih p (by simp)) (ih q (by simp))))))
    · rw [progT_of_not_shape hx]; exact bnum_semiterm k x

lemma progT_uterm (x : V) : IsUTerm ℒₒᵣ (progT x) := (progT_semiterm 0 x).isUTerm

/-! ### The meta terms -/

section metaTerms

/-- The meta term `(s + t) * (s + t) + t`. -/
noncomputable def ppairTT (s t : ClosedSemiterm ℒₒᵣ 0) : ClosedSemiterm ℒₒᵣ 0 :=
  ‘(!!s + !!t) * (!!s + !!t) + !!t’

/-- The meta term `t + 1`. -/
noncomputable def succTT (t : ClosedSemiterm ℒₒᵣ 0) : ClosedSemiterm ℒₒᵣ 0 := ‘!!t + 1’

lemma ppairTT_eq (s t : ClosedSemiterm ℒₒᵣ 0) :
    ppairTT s t = ‘!!(‘!!(‘!!s + !!t’ : ClosedSemiterm ℒₒᵣ 0) * !!(‘!!s + !!t’ : ClosedSemiterm ℒₒᵣ 0)’ :
      ClosedSemiterm ℒₒᵣ 0) + !!t’ := rfl

lemma succTT_eq (t : ClosedSemiterm ℒₒᵣ 0) : succTT t = ‘!!t + !!(‘1’ : ClosedSemiterm ℒₒᵣ 0)’ := rfl

/-! #### Codes, lengths and values of the two combinators -/

lemma quote_ppairTT (s t : ClosedSemiterm ℒₒᵣ 0) :
    (⌜ppairTT s t⌝ : V) = ppairT (⌜s⌝ : V) (⌜t⌝ : V) := by
  rw [ppairTT_eq, quote_closed_add, quote_closed_mul, quote_closed_add]; rfl

lemma quote_succTT (t : ClosedSemiterm ℒₒᵣ 0) : (⌜succTT t⌝ : V) = (⌜t⌝ : V) ^+ (𝟏 : V) := by
  rw [succTT_eq, quote_closed_add, quote_closed_one]

/-- `ppairTT` writes `s` twice and `t` three times. -/
lemma tlen_emb_ppairTT (s t : ClosedSemiterm ℒₒᵣ 0) :
    tlen (Rew.emb (ppairTT s t) : SyntacticSemiterm ℒₒᵣ 0) =
    2 * tlen (Rew.emb s : SyntacticSemiterm ℒₒᵣ 0) + 3 * tlen (Rew.emb t : SyntacticSemiterm ℒₒᵣ 0) + 4 := by
  rw [ppairTT_eq, tlen_emb_closed_add, tlen_emb_closed_mul, tlen_emb_closed_add]; omega

lemma tlen_emb_succTT (t : ClosedSemiterm ℒₒᵣ 0) :
    tlen (Rew.emb (succTT t) : SyntacticSemiterm ℒₒᵣ 0) = tlen (Rew.emb t : SyntacticSemiterm ℒₒᵣ 0) + 2 := by
  rw [succTT_eq, tlen_emb_closed_add, tlen_emb_closed_one]

lemma val_ppairTT (s t : ClosedSemiterm ℒₒᵣ 0) :
    (ppairTT s t).val (s := standardModel ℕ) ![] Empty.elim =
    ppair (s.val (s := standardModel ℕ) ![] Empty.elim) (t.val (s := standardModel ℕ) ![] Empty.elim) := by
  simp [ppairTT, ppair]

lemma val_succTT (t : ClosedSemiterm ℒₒᵣ 0) :
    (succTT t).val (s := standardModel ℕ) ![] Empty.elim = t.val (s := standardModel ℕ) ![] Empty.elim + 1 := by
  simp [succTT]

/-! #### The graph of the meta recursion (inductive, with explicit equations so that `cases` works) -/

/-- `ProgTTGraph x t`: `t` is the structural term of the program code `x`. -/
inductive ProgTTGraph : ℕ → ClosedSemiterm ℒₒᵣ 0 → Prop
  | const (x a : ℕ) (t : ClosedSemiterm ℒₒᵣ 0) (hx : x = pConst a)
      (ht : t = succTT (ppairTT (bnumT 0) (bnumT a))) : ProgTTGraph x t
  | self (x : ℕ) (t : ClosedSemiterm ℒₒᵣ 0) (hx : x = pSelf)
      (ht : t = succTT (ppairTT (bnumT 1) (bnumT 0))) : ProgTTGraph x t
  | opp (x : ℕ) (t : ClosedSemiterm ℒₒᵣ 0) (hx : x = pOpp)
      (ht : t = succTT (ppairTT (bnumT 2) (bnumT 0))) : ProgTTGraph x t
  | bot (x p : ℕ) (t tp : ClosedSemiterm ℒₒᵣ 0) (hx : x = pBot p) (hp : ProgTTGraph p tp)
      (ht : t = succTT (ppairTT (bnumT 3) tp)) : ProgTTGraph x t
  | sim (x p q : ℕ) (t tp tq : ClosedSemiterm ℒₒᵣ 0) (hx : x = pSim p q)
      (hp : ProgTTGraph p tp) (hq : ProgTTGraph q tq)
      (ht : t = succTT (ppairTT (bnumT 4) (ppairTT tp tq))) : ProgTTGraph x t
  | ite (x b a p q : ℕ) (t tb tp tq : ClosedSemiterm ℒₒᵣ 0) (hx : x = pIte b a p q)
      (hb : ProgTTGraph b tb) (hp : ProgTTGraph p tp) (hq : ProgTTGraph q tq)
      (ht : t = succTT (ppairTT (bnumT 5) (ppairTT tb (ppairTT (bnumT a) (ppairTT tp tq))))) :
      ProgTTGraph x t
  | search (x k g p q : ℕ) (t tp tq : ClosedSemiterm ℒₒᵣ 0) (hx : x = pSearch k g p q)
      (hp : ProgTTGraph p tp) (hq : ProgTTGraph q tq)
      (ht : t = succTT (ppairTT (bnumT 6) (ppairTT (bnumT k) (ppairTT (bnumT g) (ppairTT tp tq))))) :
      ProgTTGraph x t
  | other (x : ℕ) (t : ClosedSemiterm ℒₒᵣ 0) (hx : ¬IsShape x) (ht : t = bnumT x) : ProgTTGraph x t

section inversion

attribute [local simp] pConst pSelf pOpp pBot pSim pIte pSearch IsShape

lemma ProgTTGraph.const_iff {a : ℕ} {t : ClosedSemiterm ℒₒᵣ 0} :
    ProgTTGraph (pConst a) t ↔ t = succTT (ppairTT (bnumT 0) (bnumT a)) := by
  constructor
  · intro h; cases h <;> simp_all
  · rintro rfl; exact .const _ _ _ rfl rfl
lemma ProgTTGraph.self_iff {t : ClosedSemiterm ℒₒᵣ 0} :
    ProgTTGraph pSelf t ↔ t = succTT (ppairTT (bnumT 1) (bnumT 0)) := by
  constructor
  · intro h; cases h <;> simp_all
  · rintro rfl; exact .self _ _ rfl rfl
lemma ProgTTGraph.opp_iff {t : ClosedSemiterm ℒₒᵣ 0} :
    ProgTTGraph pOpp t ↔ t = succTT (ppairTT (bnumT 2) (bnumT 0)) := by
  constructor
  · intro h; cases h <;> simp_all
  · rintro rfl; exact .opp _ _ rfl rfl
lemma ProgTTGraph.bot_iff {p : ℕ} {t : ClosedSemiterm ℒₒᵣ 0} :
    ProgTTGraph (pBot p) t ↔ ∃ tp, ProgTTGraph p tp ∧ t = succTT (ppairTT (bnumT 3) tp) := by
  constructor
  · intro h; cases h <;> simp_all <;>
      first | exact ⟨_, ‹_›, rfl⟩ | exact ⟨_, ‹_›, _, ‹_›, rfl⟩ | exact ⟨_, ‹_›, _, ‹_›, _, ‹_›, rfl⟩
  · rintro ⟨tp, hp, rfl⟩; exact .bot _ _ _ _ rfl hp rfl
lemma ProgTTGraph.sim_iff {p q : ℕ} {t : ClosedSemiterm ℒₒᵣ 0} :
    ProgTTGraph (pSim p q) t ↔
    ∃ tp tq, ProgTTGraph p tp ∧ ProgTTGraph q tq ∧ t = succTT (ppairTT (bnumT 4) (ppairTT tp tq)) := by
  constructor
  · intro h; cases h <;> simp_all <;>
      first | exact ⟨_, ‹_›, rfl⟩ | exact ⟨_, ‹_›, _, ‹_›, rfl⟩ | exact ⟨_, ‹_›, _, ‹_›, _, ‹_›, rfl⟩
  · rintro ⟨tp, tq, hp, hq, rfl⟩; exact .sim _ _ _ _ _ _ rfl hp hq rfl
lemma ProgTTGraph.ite_iff {b a p q : ℕ} {t : ClosedSemiterm ℒₒᵣ 0} :
    ProgTTGraph (pIte b a p q) t ↔
    ∃ tb tp tq, ProgTTGraph b tb ∧ ProgTTGraph p tp ∧ ProgTTGraph q tq ∧
      t = succTT (ppairTT (bnumT 5) (ppairTT tb (ppairTT (bnumT a) (ppairTT tp tq)))) := by
  constructor
  · intro h; cases h <;> simp_all <;>
      first | exact ⟨_, ‹_›, rfl⟩ | exact ⟨_, ‹_›, _, ‹_›, rfl⟩ | exact ⟨_, ‹_›, _, ‹_›, _, ‹_›, rfl⟩
  · rintro ⟨tb, tp, tq, hb, hp, hq, rfl⟩; exact .ite _ _ _ _ _ _ _ _ _ rfl hb hp hq rfl
lemma ProgTTGraph.search_iff {k g p q : ℕ} {t : ClosedSemiterm ℒₒᵣ 0} :
    ProgTTGraph (pSearch k g p q) t ↔
    ∃ tp tq, ProgTTGraph p tp ∧ ProgTTGraph q tq ∧
      t = succTT (ppairTT (bnumT 6) (ppairTT (bnumT k) (ppairTT (bnumT g) (ppairTT tp tq)))) := by
  constructor
  · intro h; cases h <;> simp_all <;>
      first | exact ⟨_, ‹_›, rfl⟩ | exact ⟨_, ‹_›, _, ‹_›, rfl⟩ | exact ⟨_, ‹_›, _, ‹_›, _, ‹_›, rfl⟩
  · rintro ⟨tp, tq, hp, hq, rfl⟩; exact .search _ _ _ _ _ _ _ _ rfl hp hq rfl
lemma ProgTTGraph.of_not_shape {x : ℕ} {t : ClosedSemiterm ℒₒᵣ 0} (hx : ¬IsShape x) :
    ProgTTGraph x t ↔ t = bnumT x := by
  constructor
  · intro h; cases h <;> simp_all
  · rintro rfl; exact .other _ _ hx rfl

end inversion

lemma progTTGraph_exists (x : ℕ) : ∃ t, ProgTTGraph x t := by
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    by_cases hx : IsShape x
    · rcases hx with ⟨a, rfl⟩ | rfl | rfl | ⟨p, rfl⟩ | ⟨p, q, rfl⟩ | ⟨b, a, p, q, rfl⟩ | ⟨k, g, p, q, rfl⟩
      · exact ⟨_, ProgTTGraph.const_iff.mpr rfl⟩
      · exact ⟨_, ProgTTGraph.self_iff.mpr rfl⟩
      · exact ⟨_, ProgTTGraph.opp_iff.mpr rfl⟩
      · obtain ⟨tp, hp⟩ := ih p (by simp)
        exact ⟨_, ProgTTGraph.bot_iff.mpr ⟨tp, hp, rfl⟩⟩
      · obtain ⟨tp, hp⟩ := ih p (by simp); obtain ⟨tq, hq⟩ := ih q (by simp)
        exact ⟨_, ProgTTGraph.sim_iff.mpr ⟨tp, tq, hp, hq, rfl⟩⟩
      · obtain ⟨tb, hb⟩ := ih b (by simp); obtain ⟨tp, hp⟩ := ih p (by simp)
        obtain ⟨tq, hq⟩ := ih q (by simp)
        exact ⟨_, ProgTTGraph.ite_iff.mpr ⟨tb, tp, tq, hb, hp, hq, rfl⟩⟩
      · obtain ⟨tp, hp⟩ := ih p (by simp); obtain ⟨tq, hq⟩ := ih q (by simp)
        exact ⟨_, ProgTTGraph.search_iff.mpr ⟨tp, tq, hp, hq, rfl⟩⟩
    · exact ⟨_, (ProgTTGraph.of_not_shape hx).mpr rfl⟩

lemma progTTGraph_unique (x : ℕ) : ∀ t₁ t₂, ProgTTGraph x t₁ → ProgTTGraph x t₂ → t₁ = t₂ := by
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    intro t₁ t₂ h₁ h₂
    by_cases hx : IsShape x
    · rcases hx with ⟨a, rfl⟩ | rfl | rfl | ⟨p, rfl⟩ | ⟨p, q, rfl⟩ | ⟨b, a, p, q, rfl⟩ | ⟨k, g, p, q, rfl⟩
      · rw [ProgTTGraph.const_iff] at h₁ h₂; rw [h₁, h₂]
      · rw [ProgTTGraph.self_iff] at h₁ h₂; rw [h₁, h₂]
      · rw [ProgTTGraph.opp_iff] at h₁ h₂; rw [h₁, h₂]
      · rcases ProgTTGraph.bot_iff.mp h₁ with ⟨p₁, hp₁, rfl⟩
        rcases ProgTTGraph.bot_iff.mp h₂ with ⟨p₂, hp₂, rfl⟩
        rw [ih p (by simp) _ _ hp₁ hp₂]
      · rcases ProgTTGraph.sim_iff.mp h₁ with ⟨p₁, q₁, hp₁, hq₁, rfl⟩
        rcases ProgTTGraph.sim_iff.mp h₂ with ⟨p₂, q₂, hp₂, hq₂, rfl⟩
        rw [ih p (by simp) _ _ hp₁ hp₂, ih q (by simp) _ _ hq₁ hq₂]
      · rcases ProgTTGraph.ite_iff.mp h₁ with ⟨b₁, p₁, q₁, hb₁, hp₁, hq₁, rfl⟩
        rcases ProgTTGraph.ite_iff.mp h₂ with ⟨b₂, p₂, q₂, hb₂, hp₂, hq₂, rfl⟩
        rw [ih b (by simp) _ _ hb₁ hb₂, ih p (by simp) _ _ hp₁ hp₂, ih q (by simp) _ _ hq₁ hq₂]
      · rcases ProgTTGraph.search_iff.mp h₁ with ⟨p₁, q₁, hp₁, hq₁, rfl⟩
        rcases ProgTTGraph.search_iff.mp h₂ with ⟨p₂, q₂, hp₂, hq₂, rfl⟩
        rw [ih p (by simp) _ _ hp₁ hp₂, ih q (by simp) _ _ hq₁ hq₂]
    · rw [ProgTTGraph.of_not_shape hx] at h₁ h₂; rw [h₁, h₂]

lemma progTTGraph_existsUnique (x : ℕ) : ∃! t, ProgTTGraph x t := by
  rcases progTTGraph_exists x with ⟨t, ht⟩
  exact ExistsUnique.intro t ht (fun t' h' ↦ progTTGraph_unique x t' t h' ht)

/-- The structural term of a program code (the binary numeral `bnumT x` on non-programs). -/
noncomputable def progTT (x : ℕ) : ClosedSemiterm ℒₒᵣ 0 := Classical.choose (progTTGraph_existsUnique x).exists

lemma progTT_graph (x : ℕ) : ProgTTGraph x (progTT x) := Classical.choose_spec (progTTGraph_existsUnique x).exists

lemma progTT_eq_of_graph {x : ℕ} {t : ClosedSemiterm ℒₒᵣ 0} (h : ProgTTGraph x t) : progTT x = t :=
  progTTGraph_unique x _ _ (progTT_graph x) h

/-! #### The equations -/

lemma progTT_const (a : ℕ) : progTT (pConst a) = succTT (ppairTT (bnumT 0) (bnumT a)) :=
  progTT_eq_of_graph (ProgTTGraph.const_iff.mpr rfl)
lemma progTT_self : progTT pSelf = succTT (ppairTT (bnumT 1) (bnumT 0)) :=
  progTT_eq_of_graph (ProgTTGraph.self_iff.mpr rfl)
lemma progTT_opp : progTT pOpp = succTT (ppairTT (bnumT 2) (bnumT 0)) :=
  progTT_eq_of_graph (ProgTTGraph.opp_iff.mpr rfl)
lemma progTT_bot (p : ℕ) : progTT (pBot p) = succTT (ppairTT (bnumT 3) (progTT p)) :=
  progTT_eq_of_graph (ProgTTGraph.bot_iff.mpr ⟨_, progTT_graph p, rfl⟩)
lemma progTT_sim (p q : ℕ) : progTT (pSim p q) = succTT (ppairTT (bnumT 4) (ppairTT (progTT p) (progTT q))) :=
  progTT_eq_of_graph (ProgTTGraph.sim_iff.mpr ⟨_, _, progTT_graph p, progTT_graph q, rfl⟩)
lemma progTT_ite (b a p q : ℕ) :
    progTT (pIte b a p q) =
    succTT (ppairTT (bnumT 5) (ppairTT (progTT b) (ppairTT (bnumT a) (ppairTT (progTT p) (progTT q))))) :=
  progTT_eq_of_graph (ProgTTGraph.ite_iff.mpr ⟨_, _, _, progTT_graph b, progTT_graph p, progTT_graph q, rfl⟩)
lemma progTT_search (k g p q : ℕ) :
    progTT (pSearch k g p q) =
    succTT (ppairTT (bnumT 6) (ppairTT (bnumT k) (ppairTT (bnumT g) (ppairTT (progTT p) (progTT q))))) :=
  progTT_eq_of_graph (ProgTTGraph.search_iff.mpr ⟨_, _, progTT_graph p, progTT_graph q, rfl⟩)
lemma progTT_of_not_shape {x : ℕ} (hx : ¬IsShape x) : progTT x = bnumT x :=
  progTT_eq_of_graph ((ProgTTGraph.of_not_shape hx).mpr rfl)

/-! #### The code equation -/

lemma quote_bnumT_nat (n : ℕ) : (⌜bnumT n⌝ : ℕ) = bnum n := by rw [quote_bnumT]; simp

/-- `progT` is absolute: its value on a cast is the cast of its value (a Σ₁-definable function). -/
lemma cast_progT (x : ℕ) : ((progT x : ℕ) : V) = progT (x : V) := by
  have := DefinedFunction.shigmaOne_absolute_func V (progT.defined (V := ℕ)) (progT.defined (V := V)) ![x]
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

/-- **The code equation**: the code of the structural term is the internal `progT`, in every model. -/
theorem quote_progTT (x : ℕ) : (⌜progTT x⌝ : V) = progT (x : V) := by
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    by_cases hx : IsShape x
    · rcases hx with ⟨a, rfl⟩ | rfl | rfl | ⟨p, rfl⟩ | ⟨p, q, rfl⟩ | ⟨b, a, p, q, rfl⟩ | ⟨k, g, p, q, rfl⟩
      · rw [progTT_const, quote_succTT, quote_ppairTT, quote_bnumT, quote_bnumT, cast_pConst, progT_const]
        push_cast; rfl
      · rw [progTT_self, quote_succTT, quote_ppairTT, quote_bnumT, quote_bnumT, cast_pSelf, progT_self]
        push_cast; rfl
      · rw [progTT_opp, quote_succTT, quote_ppairTT, quote_bnumT, quote_bnumT, cast_pOpp, progT_opp]
        push_cast; rfl
      · rw [progTT_bot, quote_succTT, quote_ppairTT, quote_bnumT, ih p (by simp), cast_pBot, progT_bot]
        push_cast; rfl
      · rw [progTT_sim, quote_succTT, quote_ppairTT, quote_ppairTT, quote_bnumT, ih p (by simp),
          ih q (by simp), cast_pSim, progT_sim]
        push_cast; rfl
      · rw [progTT_ite, quote_succTT, quote_ppairTT, quote_ppairTT, quote_ppairTT, quote_ppairTT,
          quote_bnumT, quote_bnumT, ih b (by simp), ih p (by simp), ih q (by simp), cast_pIte, progT_ite]
        push_cast; rfl
      · rw [progTT_search, quote_succTT, quote_ppairTT, quote_ppairTT, quote_ppairTT, quote_ppairTT,
          quote_bnumT, quote_bnumT, quote_bnumT, ih p (by simp), ih q (by simp), cast_pSearch, progT_search]
        push_cast; rfl
    · have h1 : (⌜progTT x⌝ : V) = ((⌜progTT x⌝ : ℕ) : V) := by
        rw [Semiterm.empty_quote_def, Semiterm.empty_quote_def, Semiterm.coe_quote_eq_quote]
      rw [h1, progTT_of_not_shape hx, quote_bnumT_nat, ← progT_of_not_shape hx, cast_progT]

/-- The code equation in `ℕ`. -/
theorem quote_progTT_nat (x : ℕ) : (⌜progTT x⌝ : ℕ) = progT x := by rw [quote_progTT]; simp

/-! #### The truth equation -/

/-- **The truth equation**: the structural term of `x` denotes `x` in `ℕ`. -/
theorem val_progTT (x : ℕ) : (progTT x).val (s := standardModel ℕ) ![] Empty.elim = x := by
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    by_cases hx : IsShape x
    · rcases hx with ⟨a, rfl⟩ | rfl | rfl | ⟨p, rfl⟩ | ⟨p, q, rfl⟩ | ⟨b, a, p, q, rfl⟩ | ⟨k, g, p, q, rfl⟩
      · rw [progTT_const, val_succTT, val_ppairTT, val_bnumT, val_bnumT]; rfl
      · rw [progTT_self, val_succTT, val_ppairTT, val_bnumT, val_bnumT]; rfl
      · rw [progTT_opp, val_succTT, val_ppairTT, val_bnumT, val_bnumT]; rfl
      · rw [progTT_bot, val_succTT, val_ppairTT, val_bnumT, ih p (by simp)]; rfl
      · rw [progTT_sim, val_succTT, val_ppairTT, val_ppairTT, val_bnumT, ih p (by simp), ih q (by simp)]; rfl
      · rw [progTT_ite, val_succTT, val_ppairTT, val_ppairTT, val_ppairTT, val_ppairTT, val_bnumT, val_bnumT,
          ih b (by simp), ih p (by simp), ih q (by simp)]; rfl
      · rw [progTT_search, val_succTT, val_ppairTT, val_ppairTT, val_ppairTT, val_ppairTT, val_bnumT,
          val_bnumT, val_bnumT, ih p (by simp), ih q (by simp)]; rfl
    · rw [progTT_of_not_shape hx, val_bnumT]

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

theorem val_lt_two_pow_tlen : ∀ t : ClosedSemiterm ℒₒᵣ 0,
    t.val (s := standardModel ℕ) ![] Empty.elim < 2 ^ tlen (Rew.emb t : SyntacticSemiterm ℒₒᵣ 0)
  | #x => x.elim0
  | &x => x.elim
  | .func f v => by
    have ih : ∀ i, (v i).val (s := standardModel ℕ) ![] Empty.elim < 2 ^ tlen (Rew.emb (v i) : SyntacticSemiterm ℒₒᵣ 0) :=
      fun i ↦ val_lt_two_pow_tlen (v i)
    rw [Rew.func, tlen_func, Semiterm.val_func]
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
theorem size_le_tlen_progTT (x : ℕ) : Nat.size x ≤ tlen (Rew.emb (progTT x) : SyntacticSemiterm ℒₒᵣ 0) := by
  rw [Nat.size_le]
  have := val_lt_two_pow_tlen (progTT x)
  rwa [val_progTT] at this

/-- The upper bounds for the shapes, in terms of the leaves (`ppairTT` writes `s` twice and `t`
three times, `succTT` adds two symbols). -/
lemma tlen_emb_progTT_const (a : ℕ) :
    tlen (Rew.emb (progTT (pConst a)) : SyntacticSemiterm ℒₒᵣ 0) =
    2 * tlen (Rew.emb (bnumT 0) : SyntacticSemiterm ℒₒᵣ 0) + 3 * tlen (Rew.emb (bnumT a) : SyntacticSemiterm ℒₒᵣ 0) + 6 := by
  rw [progTT_const, tlen_emb_succTT, tlen_emb_ppairTT]

lemma tlen_emb_progTT_bot (p : ℕ) :
    tlen (Rew.emb (progTT (pBot p)) : SyntacticSemiterm ℒₒᵣ 0) =
    2 * tlen (Rew.emb (bnumT 3) : SyntacticSemiterm ℒₒᵣ 0) + 3 * tlen (Rew.emb (progTT p) : SyntacticSemiterm ℒₒᵣ 0) + 6 := by
  rw [progTT_bot, tlen_emb_succTT, tlen_emb_ppairTT]

lemma tlen_emb_progTT_sim (p q : ℕ) :
    tlen (Rew.emb (progTT (pSim p q)) : SyntacticSemiterm ℒₒᵣ 0) =
    2 * tlen (Rew.emb (bnumT 4) : SyntacticSemiterm ℒₒᵣ 0) +
      6 * tlen (Rew.emb (progTT p) : SyntacticSemiterm ℒₒᵣ 0) + 9 * tlen (Rew.emb (progTT q) : SyntacticSemiterm ℒₒᵣ 0) + 18 := by
  rw [progTT_sim, tlen_emb_succTT, tlen_emb_ppairTT, tlen_emb_ppairTT]; ring

lemma tlen_emb_progTT_ite (b a p q : ℕ) :
    tlen (Rew.emb (progTT (pIte b a p q)) : SyntacticSemiterm ℒₒᵣ 0) =
    2 * tlen (Rew.emb (bnumT 5) : SyntacticSemiterm ℒₒᵣ 0) +
      6 * tlen (Rew.emb (progTT b) : SyntacticSemiterm ℒₒᵣ 0) + 18 * tlen (Rew.emb (bnumT a) : SyntacticSemiterm ℒₒᵣ 0) +
      54 * tlen (Rew.emb (progTT p) : SyntacticSemiterm ℒₒᵣ 0) + 81 * tlen (Rew.emb (progTT q) : SyntacticSemiterm ℒₒᵣ 0) + 162 := by
  rw [progTT_ite, tlen_emb_succTT, tlen_emb_ppairTT, tlen_emb_ppairTT, tlen_emb_ppairTT, tlen_emb_ppairTT]; ring

/-- The searcher's term: `2 · |bnumT 6| + 6 · |bnumT k| + 18 · |bnumT g| + 54 · |progTT p| + 81 · |progTT q| + 162`. -/
lemma tlen_emb_progTT_search (k g p q : ℕ) :
    tlen (Rew.emb (progTT (pSearch k g p q)) : SyntacticSemiterm ℒₒᵣ 0) =
    2 * tlen (Rew.emb (bnumT 6) : SyntacticSemiterm ℒₒᵣ 0) +
      6 * tlen (Rew.emb (bnumT k) : SyntacticSemiterm ℒₒᵣ 0) + 18 * tlen (Rew.emb (bnumT g) : SyntacticSemiterm ℒₒᵣ 0) +
      54 * tlen (Rew.emb (progTT p) : SyntacticSemiterm ℒₒᵣ 0) + 81 * tlen (Rew.emb (progTT q) : SyntacticSemiterm ℒₒᵣ 0) + 162 := by
  rw [progTT_search, tlen_emb_succTT, tlen_emb_ppairTT, tlen_emb_ppairTT, tlen_emb_ppairTT, tlen_emb_ppairTT]; ring

end metaTerms

end ArithS
