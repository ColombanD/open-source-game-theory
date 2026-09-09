import ArithS.Guard

/-!
# ArithS.Eval — the evaluator, arithmetized

`EvalGraph n me opp p a`: with fuel `n`, in the frame `(me, opp)`, the program `p` plays `a`.
A Σ₁ fixpoint on the tuples `⟪n, me, opp, p, a⟫`, mirroring the engine's `Dynamics.eval`
clause for clause:

* `const a` plays `a`; `self` runs `me` in the same frame; `opp` runs `opp` in the same frame;
  `bot p` runs `p`; `ite b a' p q` runs `b`, then `p` if it played `a'`, else `q`;
* `search k g a' p q` runs `p` if `TAct ⊢_k guardCode g me opp a'` (the runtime guard
  sentence of `ArithS.Guard`, provability by a proof of length `≤ k`), else `q`;
* fuel `0` plays nothing; `sim p q` has NO clause yet (the engine substitutes the frame into
  `p`, `q` first, which needs a program-substitution function — deferred generalisation).

Sub-calls decrease the fuel but may grow the other components, so the fixpoint is `Finite`,
not `StrongFinite`: the graph is Σ₁-definable (`evalGraphDef`), and functionality and fuel
monotonicity are proved at `V = ℕ` by ordinary induction (`ArithS.EvalN`).
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
  (∃ n me opp b a' p q a r, ⟪n, me, opp, b, r⟫ ∈ C ∧
    ((r = a' ∧ ⟪n, me, opp, p, a⟫ ∈ C) ∨ (r ≠ a' ∧ ⟪n, me, opp, q, a⟫ ∈ C)) ∧
    pr = ⟪n + 1, me, opp, pIte b a' p q, a⟫) ∨
  (∃ n me opp k g a' p q a,
    ((LenProvableV TAct k (guardCode g me opp a') ∧ ⟪n, me, opp, p, a⟫ ∈ C) ∨
      (¬LenProvableV TAct k (guardCode g me opp a') ∧ ⟪n, me, opp, q, a⟫ ∈ C)) ∧
    pr = ⟪n + 1, me, opp, pSearch k g a' p q, a⟫)

noncomputable def blueprint : Fixpoint.Blueprint 0 := ⟨.mkDelta
  (.mkSigma “pr C.
    ∃ n <⁺ pr, ∃ me <⁺ pr, ∃ opp <⁺ pr, ∃ p <⁺ pr, ∃ a <⁺ pr, !pair₅Def pr (n + 1) me opp p a ∧
    ( !pConstGraph p a ∨
      (!pSelfGraph p ∧ ∃ t, !pair₅Def t n me opp me a ∧ t ∈ C) ∨
      (!pOppGraph p ∧ ∃ t, !pair₅Def t n me opp opp a ∧ t ∈ C) ∨
      (∃ p' < p, !pBotGraph p p' ∧ ∃ t, !pair₅Def t n me opp p' a ∧ t ∈ C) ∨
      (∃ b < p, ∃ a' < p, ∃ p' < p, ∃ q < p, !pIteGraph p b a' p' q ∧
        ∃ r < pr + C + 1, (∃ t, !pair₅Def t n me opp b r ∧ t ∈ C) ∧
          ((r = a' ∧ ∃ t, !pair₅Def t n me opp p' a ∧ t ∈ C) ∨
           (r ≠ a' ∧ ∃ t, !pair₅Def t n me opp q a ∧ t ∈ C))) ∨
      (∃ k < p, ∃ g < p, ∃ a' < p, ∃ p' < p, ∃ q < p, !pSearchGraph p k g a' p' q ∧
        ∃ gc, !guardCodeGraph gc g me opp a' ∧
          ((!(lenProvableV TAct).sigma k gc ∧ ∃ t, !pair₅Def t n me opp p' a ∧ t ∈ C) ∨
           (¬!(lenProvableV TAct).pi k gc ∧ ∃ t, !pair₅Def t n me opp q a ∧ t ∈ C))) )”)
  (.mkPi “pr C.
    ∃ n <⁺ pr, ∃ me <⁺ pr, ∃ opp <⁺ pr, ∃ p <⁺ pr, ∃ a <⁺ pr, !pair₅Def pr (n + 1) me opp p a ∧
    ( !pConstGraph p a ∨
      (!pSelfGraph p ∧ ∀ t, !pair₅Def t n me opp me a → t ∈ C) ∨
      (!pOppGraph p ∧ ∀ t, !pair₅Def t n me opp opp a → t ∈ C) ∨
      (∃ p' < p, !pBotGraph p p' ∧ ∀ t, !pair₅Def t n me opp p' a → t ∈ C) ∨
      (∃ b < p, ∃ a' < p, ∃ p' < p, ∃ q < p, !pIteGraph p b a' p' q ∧
        ∃ r < pr + C + 1, (∀ t, !pair₅Def t n me opp b r → t ∈ C) ∧
          ((r = a' ∧ ∀ t, !pair₅Def t n me opp p' a → t ∈ C) ∨
           (r ≠ a' ∧ ∀ t, !pair₅Def t n me opp q a → t ∈ C))) ∨
      (∃ k < p, ∃ g < p, ∃ a' < p, ∃ p' < p, ∃ q < p, !pSearchGraph p k g a' p' q ∧
        ∀ gc, !guardCodeGraph gc g me opp a' →
          ((!(lenProvableV TAct).pi k gc ∧ ∀ t, !pair₅Def t n me opp p' a → t ∈ C) ∨
           (¬!(lenProvableV TAct).sigma k gc ∧ ∀ t, !pair₅Def t n me opp q a → t ∈ C))) )”)⟩

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
      (∃ b < p, ∃ a' < p, ∃ p' < p, ∃ q < p, p = pIte b a' p' q ∧
        ∃ r < pr + C + 1, ⟪n, me, opp, b, r⟫ ∈ C ∧
          ((r = a' ∧ ⟪n, me, opp, p', a⟫ ∈ C) ∨ (r ≠ a' ∧ ⟪n, me, opp, q, a⟫ ∈ C))) ∨
      (∃ k < p, ∃ g < p, ∃ a' < p, ∃ p' < p, ∃ q < p, p = pSearch k g a' p' q ∧
        ((LenProvableV TAct k (guardCode g me opp a') ∧ ⟪n, me, opp, p', a⟫ ∈ C) ∨
         (¬LenProvableV TAct k (guardCode g me opp a') ∧ ⟪n, me, opp, q, a⟫ ∈ C))) ) := by
  constructor
  · rintro (⟨n, me, opp, a, rfl⟩ | ⟨n, me, opp, a, h, rfl⟩ | ⟨n, me, opp, a, h, rfl⟩ |
      ⟨n, me, opp, p, a, h, rfl⟩ | ⟨n, me, opp, b, a', p, q, a, r, hb, hpq, rfl⟩ |
      ⟨n, me, opp, k, g, a', p, q, a, hpq, rfl⟩)
    · obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := tuple_bounds n me opp (pConst a) a
      exact ⟨n, h₁, me, h₂, opp, h₃, _, h₄, a, h₅, rfl, Or.inl rfl⟩
    · obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := tuple_bounds n me opp pSelf a
      exact ⟨n, h₁, me, h₂, opp, h₃, _, h₄, a, h₅, rfl, Or.inr (Or.inl ⟨rfl, h⟩)⟩
    · obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := tuple_bounds n me opp pOpp a
      exact ⟨n, h₁, me, h₂, opp, h₃, _, h₄, a, h₅, rfl, Or.inr (Or.inr (Or.inl ⟨rfl, h⟩))⟩
    · obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := tuple_bounds n me opp (pBot p) a
      exact ⟨n, h₁, me, h₂, opp, h₃, _, h₄, a, h₅, rfl,
        Or.inr (Or.inr (Or.inr (Or.inl ⟨p, by simp, rfl, h⟩)))⟩
    · obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := tuple_bounds n me opp (pIte b a' p q) a
      exact ⟨n, h₁, me, h₂, opp, h₃, _, h₄, a, h₅, rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨b, by simp, a', by simp, p, by simp, q, by simp, rfl, r,
          lt_of_lt_of_le (lt_of_tuple_mem hb) (le_trans le_add_self le_self_add), hb, hpq⟩))))⟩
    · obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := tuple_bounds n me opp (pSearch k g a' p q) a
      exact ⟨n, h₁, me, h₂, opp, h₃, _, h₄, a, h₅, rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨k, by simp, g, by simp, a', by simp, p, by simp, q, by simp, rfl, hpq⟩))))⟩
  · rintro ⟨n, _, me, _, opp, _, p, _, a, _, rfl, (rfl | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨p', _, rfl, h⟩ |
      ⟨b, _, a', _, p', _, q, _, rfl, r, _, hb, hpq⟩ | ⟨k, _, g, _, a', _, p', _, q, _, rfl, hpq⟩)⟩
    · exact Or.inl ⟨n, me, opp, a, rfl⟩
    · exact Or.inr (Or.inl ⟨n, me, opp, a, h, rfl⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨n, me, opp, a, h, rfl⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨n, me, opp, p', a, h, rfl⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, me, opp, b, a', p', q, a, r, hb, hpq, rfl⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨n, me, opp, k, g, a', p', q, a, hpq, rfl⟩))))

noncomputable def construction : Fixpoint.Construction V blueprint where
  Φ := fun _ ↦ Phi
  defined := .mk <| by
    constructor
    · intro v
      simp [blueprint, HierarchySymbol.Semiformula.val_sigma,
        (LenProvableV.defined TAct).proper.iff']
    · intro v
      symm
      simpa [blueprint, HierarchySymbol.Semiformula.val_sigma, (LenProvableV.defined TAct).df,
        pSelfGraph, pOppGraph, pSelf, pOpp, lt_and_eq_succ_iff] using phi_iff (v 1) (v 0)
  monotone := by
    rintro C C' hC _ pr (⟨n, me, opp, a, rfl⟩ | ⟨n, me, opp, a, h, rfl⟩ | ⟨n, me, opp, a, h, rfl⟩ |
      ⟨n, me, opp, p, a, h, rfl⟩ | ⟨n, me, opp, b, a', p, q, a, r, hb, hpq, rfl⟩ |
      ⟨n, me, opp, k, g, a', p, q, a, hpq, rfl⟩)
    · exact Or.inl ⟨n, me, opp, a, rfl⟩
    · exact Or.inr (Or.inl ⟨n, me, opp, a, hC h, rfl⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨n, me, opp, a, hC h, rfl⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨n, me, opp, p, a, hC h, rfl⟩)))
    · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, me, opp, b, a', p, q, a, r, hC hb, ?_, rfl⟩))))
      rcases hpq with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨h1, hC h2⟩
      · exact Or.inr ⟨h1, hC h2⟩
    · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨n, me, opp, k, g, a', p, q, a, ?_, rfl⟩))))
      rcases hpq with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨h1, hC h2⟩
      · exact Or.inr ⟨h1, hC h2⟩

instance : construction.Finite V where
  finite := by
    rintro C _ pr (⟨n, me, opp, a, rfl⟩ | ⟨n, me, opp, a, h, rfl⟩ | ⟨n, me, opp, a, h, rfl⟩ |
      ⟨n, me, opp, p, a, h, rfl⟩ | ⟨n, me, opp, b, a', p, q, a, r, hb, hpq, rfl⟩ |
      ⟨n, me, opp, k, g, a', p, q, a, hpq, rfl⟩)
    · exact ⟨0, Or.inl ⟨n, me, opp, a, rfl⟩⟩
    · exact ⟨_ + 1, Or.inr (Or.inl ⟨n, me, opp, a, ⟨h, lt_add_one _⟩, rfl⟩)⟩
    · exact ⟨_ + 1, Or.inr (Or.inr (Or.inl ⟨n, me, opp, a, ⟨h, lt_add_one _⟩, rfl⟩))⟩
    · exact ⟨_ + 1, Or.inr (Or.inr (Or.inr (Or.inl ⟨n, me, opp, p, a, ⟨h, lt_add_one _⟩, rfl⟩)))⟩
    · refine ⟨⟪n, me, opp, b, r⟫ + ⟪n, me, opp, p, a⟫ + ⟪n, me, opp, q, a⟫ + 1,
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, me, opp, b, a', p, q, a, r, ⟨hb, by
          have := le_self_add (a := ⟪n, me, opp, b, r⟫) (b := ⟪n, me, opp, p, a⟫)
          have := le_self_add (a := ⟪n, me, opp, b, r⟫ + ⟪n, me, opp, p, a⟫) (b := ⟪n, me, opp, q, a⟫)
          exact lt_of_le_of_lt (le_trans (by assumption) (by assumption)) (lt_add_one _)⟩, ?_, rfl⟩))))⟩
      rcases hpq with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨h1, h2, by
          have := le_add_self (a := ⟪n, me, opp, p, a⟫) (b := ⟪n, me, opp, b, r⟫)
          have := le_self_add (a := ⟪n, me, opp, b, r⟫ + ⟪n, me, opp, p, a⟫) (b := ⟪n, me, opp, q, a⟫)
          exact lt_of_le_of_lt (le_trans (by assumption) (by assumption)) (lt_add_one _)⟩
      · exact Or.inr ⟨h1, h2, lt_of_le_of_lt le_add_self (lt_add_one _)⟩
    · refine ⟨⟪n, me, opp, p, a⟫ + ⟪n, me, opp, q, a⟫ + 1,
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨n, me, opp, k, g, a', p, q, a, ?_, rfl⟩))))⟩
      rcases hpq with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨h1, h2, lt_of_le_of_lt le_self_add (lt_add_one _)⟩
      · exact Or.inr ⟨h1, h2, lt_of_le_of_lt le_add_self (lt_add_one _)⟩

end EvalFix

/-- `EvalGraph n me opp p a`: with fuel `n`, in the frame `(me, opp)`, `p` plays `a`. -/
def EvalGraph (n me opp p a : V) : Prop := EvalFix.construction.Fixpoint ![] ⟪n, me, opp, p, a⟫

noncomputable def evalGraphDef : 𝚺₁.Semisentence 5 := .mkSigma
  “n me opp p a. ∃ pr, !pair₅Def pr n me opp p a ∧ !EvalFix.blueprint.fixpointDef pr”

private lemma eval_param_eq (p : Fin 0 → V) (x : V) :
    EvalFix.construction.Fixpoint p x = EvalFix.construction.Fixpoint ![] x := by
  rw [Subsingleton.elim p ![]]

lemma evalGraph_defined :
    𝚺₁.Defined (fun v : Fin 5 → V ↦ EvalGraph (v 0) (v 1) (v 2) (v 3) (v 4)) evalGraphDef := .mk fun v ↦ by
  simp [evalGraphDef, EvalFix.construction.fixpoint_defined.iff, EvalGraph]
  rw [eval_param_eq]

instance evalGraph_definable : 𝚺₁-Relation₅[V] EvalGraph := evalGraph_defined.to_definable

lemma EvalGraph.case_iff {n me opp p a : V} :
    EvalGraph n me opp p a ↔
    ∃ n', n = n' + 1 ∧
    ( p = pConst a ∨
      (p = pSelf ∧ EvalGraph n' me opp me a) ∨
      (p = pOpp ∧ EvalGraph n' me opp opp a) ∨
      (∃ p', p = pBot p' ∧ EvalGraph n' me opp p' a) ∨
      (∃ b a' p' q r, p = pIte b a' p' q ∧ EvalGraph n' me opp b r ∧
        ((r = a' ∧ EvalGraph n' me opp p' a) ∨ (r ≠ a' ∧ EvalGraph n' me opp q a))) ∨
      (∃ k g a' p' q, p = pSearch k g a' p' q ∧
        ((LenProvableV TAct k (guardCode g me opp a') ∧ EvalGraph n' me opp p' a) ∨
         (¬LenProvableV TAct k (guardCode g me opp a') ∧ EvalGraph n' me opp q a))) ) := by
  rw [EvalGraph, EvalFix.construction.case]
  simp only [EvalFix.construction, EvalFix.Phi, Set.mem_setOf_eq, pair_ext_iff]
  constructor
  · rintro (⟨n₀, me₀, opp₀, a₀, h⟩ | ⟨n₀, me₀, opp₀, a₀, hc, h⟩ | ⟨n₀, me₀, opp₀, a₀, hc, h⟩ |
      ⟨n₀, me₀, opp₀, p₀, a₀, hc, h⟩ | ⟨n₀, me₀, opp₀, b, a', p', q, a₀, r, hb, hpq, h⟩ |
      ⟨n₀, me₀, opp₀, k, g, a', p', q, a₀, hpq, h⟩) <;>
      obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
    · exact ⟨n₀, rfl, Or.inl rfl⟩
    · exact ⟨n₀, rfl, Or.inr (Or.inl ⟨rfl, hc⟩)⟩
    · exact ⟨n₀, rfl, Or.inr (Or.inr (Or.inl ⟨rfl, hc⟩))⟩
    · exact ⟨n₀, rfl, Or.inr (Or.inr (Or.inr (Or.inl ⟨p₀, rfl, hc⟩)))⟩
    · exact ⟨n₀, rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨b, a', p', q, r, rfl, hb, hpq⟩))))⟩
    · exact ⟨n₀, rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨k, g, a', p', q, rfl, hpq⟩))))⟩
  · rintro ⟨n', rfl, (rfl | ⟨rfl, hc⟩ | ⟨rfl, hc⟩ | ⟨p', rfl, hc⟩ | ⟨b, a', p', q, r, rfl, hb, hpq⟩ |
      ⟨k, g, a', p', q, rfl, hpq⟩)⟩
    · exact Or.inl ⟨n', me, opp, a, by simp⟩
    · exact Or.inr (Or.inl ⟨n', me, opp, a, hc, by simp⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨n', me, opp, a, hc, by simp⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨n', me, opp, p', a, hc, by simp⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n', me, opp, b, a', p', q, a, r, hb, hpq, by simp⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨n', me, opp, k, g, a', p', q, a, hpq, by simp⟩))))

end ArithS
