import ArithS.Agents.Subst

/-!
# ArithS.Eval.Fixpoint — the Foundation plumbing behind `EvalGraph`

**Skip on first reading.** The evaluator `EvalGraph` (`ArithS.Eval.Eval`) is the least fixpoint of the
operator `EvalFix.Phi` below — one disjunct per clause of the engine's `eval` — and this file is
everything Foundation needs to build that fixpoint: the operator, its Δ₁ blueprint (the same clauses
written as a formula of arithmetic), the proof that blueprint and operator agree (`phi_iff`),
monotonicity, and finiteness (each clause cites finitely many sub-tuples). Nothing here is a
definition a reader has to accept beyond `Phi`, whose seven disjuncts are restated as the
characterization `EvalGraph.case_iff` in `Eval.lean`.
-/

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1
open LAct

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

namespace EvalFix

/-- The evaluation operator on tuples `⟪n, me, opp, p, a⟫`. -/
def Phi (C : Set V) (pr : V) : Prop :=
  (∃ n me opp a, pr = ⟪n + 1, me, opp, pConst a, a⟫) ∨
  (∃ n me opp a, ⟪n, me, opp, me, a⟫ ∈ C ∧ pr = ⟪n + 1, me, opp, pSelf, a⟫) ∨
  (∃ n me opp a, ⟪n, me, opp, opp, a⟫ ∈ C ∧ pr = ⟪n + 1, me, opp, pOpp, a⟫) ∨
  (∃ n me opp p a, ⟪n, me, opp, p, a⟫ ∈ C ∧ pr = ⟪n + 1, me, opp, pBot p, a⟫) ∨
  (∃ n me opp p q a, ⟪n, substCode me opp p, substCode me opp q, substCode me opp p, a⟫ ∈ C ∧
    pr = ⟪n + 1, me, opp, pSim p q, a⟫) ∨
  (∃ n me opp b a' p q a r, ⟪n, me, opp, b, r⟫ ∈ C ∧
    ((r = a' ∧ ⟪n, me, opp, p, a⟫ ∈ C) ∨ (r ≠ a' ∧ ⟪n, me, opp, q, a⟫ ∈ C)) ∧
    pr = ⟪n + 1, me, opp, pIte b a' p q, a⟫) ∨
  (∃ n me opp k g p q a,
    ((LenBox TAct k (guardCodeB g me opp k) ∧ ⟪n, me, opp, p, a⟫ ∈ C) ∨
      (¬LenBox TAct k (guardCodeB g me opp k) ∧ ⟪n, me, opp, q, a⟫ ∈ C)) ∧
    pr = ⟪n + 1, me, opp, pSearch k g p q, a⟫)

noncomputable def blueprint : Fixpoint.Blueprint 0 := ⟨.mkDelta
  (.mkSigma “pr C.
    ∃ n <⁺ pr, ∃ me <⁺ pr, ∃ opp <⁺ pr, ∃ p <⁺ pr, ∃ a <⁺ pr, !pair₅Def pr (n + 1) me opp p a ∧
    ( !pConstGraph p a ∨
      (!pSelfGraph p ∧ ∃ t, !pair₅Def t n me opp me a ∧ t ∈ C) ∨
      (!pOppGraph p ∧ ∃ t, !pair₅Def t n me opp opp a ∧ t ∈ C) ∨
      (∃ p' < p, !pBotGraph p p' ∧ ∃ t, !pair₅Def t n me opp p' a ∧ t ∈ C) ∨
      (∃ p' < p, ∃ q < p, !pSimGraph p p' q ∧
        ∃ sp, !substCodeDef sp me opp p' ∧ ∃ sq, !substCodeDef sq me opp q ∧
          ∃ t, !pair₅Def t n sp sq sp a ∧ t ∈ C) ∨
      (∃ b < p, ∃ a' < p, ∃ p' < p, ∃ q < p, !pIteGraph p b a' p' q ∧
        ∃ r < pr + C + 1, (∃ t, !pair₅Def t n me opp b r ∧ t ∈ C) ∧
          ((r = a' ∧ ∃ t, !pair₅Def t n me opp p' a ∧ t ∈ C) ∨
           (r ≠ a' ∧ ∃ t, !pair₅Def t n me opp q a ∧ t ∈ C))) ∨
      (∃ k < p, ∃ g < p, ∃ p' < p, ∃ q < p, !pSearchGraph p k g p' q ∧
        ∃ gc, !guardCodeBGraph gc g me opp k ∧
          ((!(lenBox TAct).sigma k gc ∧ ∃ t, !pair₅Def t n me opp p' a ∧ t ∈ C) ∨
           (¬!(lenBox TAct).pi k gc ∧ ∃ t, !pair₅Def t n me opp q a ∧ t ∈ C))) )”)
  (.mkPi “pr C.
    ∃ n <⁺ pr, ∃ me <⁺ pr, ∃ opp <⁺ pr, ∃ p <⁺ pr, ∃ a <⁺ pr, !pair₅Def pr (n + 1) me opp p a ∧
    ( !pConstGraph p a ∨
      (!pSelfGraph p ∧ ∀ t, !pair₅Def t n me opp me a → t ∈ C) ∨
      (!pOppGraph p ∧ ∀ t, !pair₅Def t n me opp opp a → t ∈ C) ∨
      (∃ p' < p, !pBotGraph p p' ∧ ∀ t, !pair₅Def t n me opp p' a → t ∈ C) ∨
      (∃ p' < p, ∃ q < p, !pSimGraph p p' q ∧
        ∀ sp, !substCodeDef sp me opp p' → ∀ sq, !substCodeDef sq me opp q →
          ∀ t, !pair₅Def t n sp sq sp a → t ∈ C) ∨
      (∃ b < p, ∃ a' < p, ∃ p' < p, ∃ q < p, !pIteGraph p b a' p' q ∧
        ∃ r < pr + C + 1, (∀ t, !pair₅Def t n me opp b r → t ∈ C) ∧
          ((r = a' ∧ ∀ t, !pair₅Def t n me opp p' a → t ∈ C) ∨
           (r ≠ a' ∧ ∀ t, !pair₅Def t n me opp q a → t ∈ C))) ∨
      (∃ k < p, ∃ g < p, ∃ p' < p, ∃ q < p, !pSearchGraph p k g p' q ∧
        ∀ gc, !guardCodeBGraph gc g me opp k →
          ((!(lenBox TAct).pi k gc ∧ ∀ t, !pair₅Def t n me opp p' a → t ∈ C) ∨
           (¬!(lenBox TAct).sigma k gc ∧ ∀ t, !pair₅Def t n me opp q a → t ∈ C))) )”)⟩

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
        ⟪n, substCode me opp p', substCode me opp q, substCode me opp p', a⟫ ∈ C) ∨
      (∃ b < p, ∃ a' < p, ∃ p' < p, ∃ q < p, p = pIte b a' p' q ∧
        ∃ r < pr + C + 1, ⟪n, me, opp, b, r⟫ ∈ C ∧
          ((r = a' ∧ ⟪n, me, opp, p', a⟫ ∈ C) ∨ (r ≠ a' ∧ ⟪n, me, opp, q, a⟫ ∈ C))) ∨
      (∃ k < p, ∃ g < p, ∃ p' < p, ∃ q < p, p = pSearch k g p' q ∧
        ((LenBox TAct k (guardCodeB g me opp k) ∧ ⟪n, me, opp, p', a⟫ ∈ C) ∨
         (¬LenBox TAct k (guardCodeB g me opp k) ∧ ⟪n, me, opp, q, a⟫ ∈ C))) ) := by
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
        (LenBox.defined TAct).proper.iff', substCode_defined.df]
    · intro v
      symm
      simpa [blueprint, HierarchySymbol.Semiformula.val_sigma, (LenBox.defined TAct).df,
        substCode_defined.df, pSelfGraph, pOppGraph, pSelf, pOpp, lt_and_eq_succ_iff]
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

end EvalFix

end ArithS
