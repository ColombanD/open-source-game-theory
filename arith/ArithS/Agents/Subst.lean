import ArithS.Agents.SubstTemplate

/-!
# ArithS.Agents.Subst — program substitution on codes (`substCode`), the engine's `Prog.subst`

**Definition.** `substCode me opp p` is the engine's ONE-SHOT `Prog.subst` on codes, the Δ₁ fixpoint
on pairs `⟪x, y⟫` with parameters `me opp` (the operator `SubstCode.Phi` below, one clause per
constructor):

* `pConst a ↦ pConst a`, `pSelf ↦ me`, `pOpp ↦ opp`, `pBot p ↦ pBot p` (frozen: a `.bot` is a barrier),
* `pSim`/`pIte` structurally,
* `pSearch k g p q ↦ pSearch k (substTemplate me opp g) (substCode p) (substCode q)` — the stored
  template is instantiated with the OUTER descriptions (`ArithS.Agents.SubstTemplate`),
* non-shapes fixed (total).

The equations `substCode_const/self/opp/bot/sim/ite/search` are the definition a reader should
accept; the blueprint and construction between `SubstCode.Phi` and them are Foundation plumbing.

**Facts.** `substCode` is a Σ₁ function (`substCodeDef`); τ-equivariance `transposeCode_substCode`:
transposing a substituted program is substituting the transposed frame into the transposed program,
on every code. Agreement with the engine's `Prog.subst` on the box-free fragment is `progCode_subst`
in `ArithS.Agents.Code`. At ℕ: `progCode_subst` (`ArithS.Readings`).
-/

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open LAct

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ### `substCode`: a fixpoint on pairs `⟪x, y⟫` with parameters `me opp`

The search clause instantiates the stored template through `substTemplate` (a Σ₁ function), so the
core is Δ₁ (both polarities cite `substTemplateGraph`, exactly like `Revalue` cites
`revalueTemplateGraph`); the fixpoint is StrongFinite, since the sub-results referenced are
`⟪p, p'⟫` with `p < x` and `p' < y`. -/

namespace SubstCode

/-- `Phi ![me, opp] C ⟪x, y⟫`: `y` is `x` with `pSelf ↦ me`, `pOpp ↦ opp`, `pBot` frozen and every
stored template instantiated, given the sub-results in `C`. -/
def Phi (param : Fin 2 → V) (C : Set V) (pr : V) : Prop :=
  (∃ a, pr = ⟪pConst a, pConst a⟫) ∨
  pr = ⟪pSelf, param 0⟫ ∨ pr = ⟪pOpp, param 1⟫ ∨
  (∃ p, pr = ⟪pBot p, pBot p⟫) ∨
  (∃ p q p' q', ⟪p, p'⟫ ∈ C ∧ ⟪q, q'⟫ ∈ C ∧ pr = ⟪pSim p q, pSim p' q'⟫) ∨
  (∃ b a p q b' p' q', ⟪b, b'⟫ ∈ C ∧ ⟪p, p'⟫ ∈ C ∧ ⟪q, q'⟫ ∈ C ∧
    pr = ⟪pIte b a p q, pIte b' a p' q'⟫) ∨
  (∃ k g p q p' q', ⟪p, p'⟫ ∈ C ∧ ⟪q, q'⟫ ∈ C ∧
    pr = ⟪pSearch k g p q, pSearch k (substTemplate (param 0) (param 1) g) p' q'⟫) ∨
  (∃ x, ¬IsShape x ∧ pr = ⟪x, x⟫)

noncomputable def blueprint : Fixpoint.Blueprint 2 := ⟨.mkDelta
  (.mkSigma “pr C me opp. ∃ x <⁺ pr, ∃ y <⁺ pr, !pairDef pr x y ∧
    ( (∃ a < x, !pConstGraph x a ∧ y = x) ∨
      (!pSelfGraph x ∧ y = me) ∨
      (!pOppGraph x ∧ y = opp) ∨
      (∃ p < x, !pBotGraph x p ∧ y = x) ∨
      (∃ p < x, ∃ q < x, !pSimGraph x p q ∧
        ∃ p' < y, ∃ q' < y, :⟪p, p'⟫:∈ C ∧ :⟪q, q'⟫:∈ C ∧ !pSimGraph y p' q') ∨
      (∃ b < x, ∃ a < x, ∃ p < x, ∃ q < x, !pIteGraph x b a p q ∧
        ∃ b' < y, ∃ p' < y, ∃ q' < y,
          :⟪b, b'⟫:∈ C ∧ :⟪p, p'⟫:∈ C ∧ :⟪q, q'⟫:∈ C ∧ !pIteGraph y b' a p' q') ∨
      (∃ k < x, ∃ g < x, ∃ p < x, ∃ q < x, !pSearchGraph x k g p q ∧
        ∃ g', !substTemplateGraph g' me opp g ∧ ∃ p' < y, ∃ q' < y,
          :⟪p, p'⟫:∈ C ∧ :⟪q, q'⟫:∈ C ∧ !pSearchGraph y k g' p' q') ∨
      (¬!isShape x ∧ y = x) )”)
  (.mkPi “pr C me opp. ∃ x <⁺ pr, ∃ y <⁺ pr, !pairDef pr x y ∧
    ( (∃ a < x, !pConstGraph x a ∧ y = x) ∨
      (!pSelfGraph x ∧ y = me) ∨
      (!pOppGraph x ∧ y = opp) ∨
      (∃ p < x, !pBotGraph x p ∧ y = x) ∨
      (∃ p < x, ∃ q < x, !pSimGraph x p q ∧
        ∃ p' < y, ∃ q' < y, :⟪p, p'⟫:∈ C ∧ :⟪q, q'⟫:∈ C ∧ !pSimGraph y p' q') ∨
      (∃ b < x, ∃ a < x, ∃ p < x, ∃ q < x, !pIteGraph x b a p q ∧
        ∃ b' < y, ∃ p' < y, ∃ q' < y,
          :⟪b, b'⟫:∈ C ∧ :⟪p, p'⟫:∈ C ∧ :⟪q, q'⟫:∈ C ∧ !pIteGraph y b' a p' q') ∨
      (∃ k < x, ∃ g < x, ∃ p < x, ∃ q < x, !pSearchGraph x k g p q ∧
        ∀ g', !substTemplateGraph g' me opp g → ∃ p' < y, ∃ q' < y,
          :⟪p, p'⟫:∈ C ∧ :⟪q, q'⟫:∈ C ∧ !pSearchGraph y k g' p' q') ∨
      (¬!isShape x ∧ y = x) )”)⟩

private lemma phi_iff (param : Fin 2 → V) (C pr : V) :
    Phi param {x | x ∈ C} pr ↔
    ∃ x ≤ pr, ∃ y ≤ pr, pr = ⟪x, y⟫ ∧
    ( (∃ a < x, x = pConst a ∧ y = x) ∨
      (x = pSelf ∧ y = param 0) ∨
      (x = pOpp ∧ y = param 1) ∨
      (∃ p < x, x = pBot p ∧ y = x) ∨
      (∃ p < x, ∃ q < x, x = pSim p q ∧
        ∃ p' < y, ∃ q' < y, ⟪p, p'⟫ ∈ C ∧ ⟪q, q'⟫ ∈ C ∧ y = pSim p' q') ∨
      (∃ b < x, ∃ a < x, ∃ p < x, ∃ q < x, x = pIte b a p q ∧
        ∃ b' < y, ∃ p' < y, ∃ q' < y,
          ⟪b, b'⟫ ∈ C ∧ ⟪p, p'⟫ ∈ C ∧ ⟪q, q'⟫ ∈ C ∧ y = pIte b' a p' q') ∨
      (∃ k < x, ∃ g < x, ∃ p < x, ∃ q < x, x = pSearch k g p q ∧
        ∃ p' < y, ∃ q' < y,
          ⟪p, p'⟫ ∈ C ∧ ⟪q, q'⟫ ∈ C ∧ y = pSearch k (substTemplate (param 0) (param 1) g) p' q') ∨
      (¬IsShape x ∧ y = x) ) := by
  constructor
  · rintro (⟨a, rfl⟩ | rfl | rfl | ⟨p, rfl⟩ | ⟨p, q, p', q', hp, hq, rfl⟩ |
      ⟨b, a, p, q, b', p', q', hb, hp, hq, rfl⟩ | ⟨k, g, p, q, p', q', hp, hq, rfl⟩ | ⟨x, hx, rfl⟩)
    · exact ⟨_, by simp, _, by simp, rfl, Or.inl ⟨a, by simp, rfl, rfl⟩⟩
    · exact ⟨_, by simp, _, by simp, rfl, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
    · exact ⟨_, by simp, _, by simp, rfl, Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩
    · exact ⟨_, by simp, _, by simp, rfl, Or.inr (Or.inr (Or.inr (Or.inl ⟨p, by simp, rfl, rfl⟩)))⟩
    · exact ⟨_, by simp, _, by simp, rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨p, by simp, q, by simp, rfl, p', by simp, q', by simp, hp, hq, rfl⟩))))⟩
    · exact ⟨_, by simp, _, by simp, rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨b, by simp, a, by simp, p, by simp, q, by simp, rfl, b', by simp,
          p', by simp, q', by simp, hb, hp, hq, rfl⟩)))))⟩
    · exact ⟨_, by simp, _, by simp, rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨k, by simp, g, by simp, p, by simp, q, by simp, rfl,
          p', by simp, q', by simp, hp, hq, rfl⟩))))))⟩
    · exact ⟨_, by simp, _, by simp, rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨hx, rfl⟩))))))⟩
  · rintro ⟨x, _, y, _, rfl, (⟨a, _, rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨p, _, rfl, rfl⟩ | ⟨p, _, q, _, rfl, p', _, q', _, hp, hq, rfl⟩ |
      ⟨b, _, a, _, p, _, q, _, rfl, b', _, p', _, q', _, hb, hp, hq, rfl⟩ |
      ⟨k, _, g, _, p, _, q, _, rfl, p', _, q', _, hp, hq, rfl⟩ | ⟨hx, hyx⟩)⟩
    · exact Or.inl ⟨a, rfl⟩
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨p, rfl⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, q, p', q', hp, hq, rfl⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨b, a, p, q, b', p', q', hb, hp, hq, rfl⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨k, g, p, q, p', q', hp, hq, rfl⟩))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨x, hx, by rw [hyx]⟩))))))

noncomputable def construction : Fixpoint.Construction V blueprint where
  Φ := Phi
  defined := .mk <| by
    constructor
    · intro v
      simp [blueprint, HierarchySymbol.Semiformula.val_sigma, substTemplate.defined.df]
    · intro v
      symm
      simpa [blueprint, HierarchySymbol.Semiformula.val_sigma, substTemplate.defined.df,
        pSelfGraph, pOppGraph, pSelf, pOpp, lt_and_eq_succ_iff]
        using phi_iff (fun i ↦ v i.succ.succ) (v 1) (v 0)
  monotone := by
    rintro C C' hC param pr (⟨a, rfl⟩ | rfl | rfl | ⟨p, rfl⟩ | ⟨p, q, p', q', hp, hq, rfl⟩ |
      ⟨b, a, p, q, b', p', q', hb, hp, hq, rfl⟩ | ⟨k, g, p, q, p', q', hp, hq, rfl⟩ | ⟨x, hx, rfl⟩)
    · exact Or.inl ⟨a, rfl⟩
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨p, rfl⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, q, p', q', hC hp, hC hq, rfl⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨b, a, p, q, b', p', q', hC hb, hC hp, hC hq, rfl⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨k, g, p, q, p', q', hC hp, hC hq, rfl⟩))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨x, hx, rfl⟩))))))

instance : construction.StrongFinite V where
  strong_finite := by
    rintro C param pr (⟨a, rfl⟩ | rfl | rfl | ⟨p, rfl⟩ | ⟨p, q, p', q', hp, hq, rfl⟩ |
      ⟨b, a, p, q, b', p', q', hb, hp, hq, rfl⟩ | ⟨k, g, p, q, p', q', hp, hq, rfl⟩ | ⟨x, hx, rfl⟩)
    · exact Or.inl ⟨a, rfl⟩
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨p, rfl⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, q, p', q',
        ⟨hp, pair_lt_pair (by simp) (by simp)⟩, ⟨hq, pair_lt_pair (by simp) (by simp)⟩, rfl⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨b, a, p, q, b', p', q',
        ⟨hb, pair_lt_pair (by simp) (by simp)⟩, ⟨hp, pair_lt_pair (by simp) (by simp)⟩,
        ⟨hq, pair_lt_pair (by simp) (by simp)⟩, rfl⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨k, g, p, q, p', q',
        ⟨hp, pair_lt_pair (by simp) (by simp)⟩, ⟨hq, pair_lt_pair (by simp) (by simp)⟩, rfl⟩))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨x, hx, rfl⟩))))))

end SubstCode

/-- `SubstCodeGraph me opp x y`: `y` is `x` with the frame `(me, opp)` substituted in. -/
def SubstCodeGraph (me opp x y : V) : Prop := SubstCode.construction.Fixpoint ![me, opp] ⟪x, y⟫

noncomputable def substCodeGraphDef : 𝚫₁.Semisentence 4 := .mkDelta
  (.mkSigma “me opp x y. ∃ pr <⁺ (x + y + 1)², !pairDef pr x y ∧ !SubstCode.blueprint.fixpointDefΔ₁.sigma pr me opp”)
  (.mkPi “me opp x y. ∀ pr <⁺ (x + y + 1)², !pairDef pr x y → !SubstCode.blueprint.fixpointDefΔ₁.pi pr me opp”)

private lemma substCode_param_eq (v : Fin 3 → V) : (fun i ↦ v i.succ) = ![v 1, v 2] := by
  funext i; fin_cases i <;> rfl

instance substCodeGraph_defined : 𝚫₁-Relation₄[V] SubstCodeGraph via substCodeGraphDef := .mk
  ⟨by intro v
      simp [substCodeGraphDef, HierarchySymbol.Semiformula.val_sigma,
        SubstCode.construction.fixpoint_definedΔ₁.proper.iff', SubstCode.construction.fixpoint_definedΔ₁.df]
      constructor
      · rintro h x _ rfl; simpa [substCode_param_eq] using h
      · intro h; have := h ⟪v 2, v 3⟫ (by simp) rfl; simpa [substCode_param_eq] using this,
   by intro v
      simp [substCodeGraphDef, HierarchySymbol.Semiformula.val_sigma,
        SubstCode.construction.fixpoint_definedΔ₁.df, SubstCodeGraph]⟩

instance substCodeGraph_definable : 𝚫₁-Relation₄[V] SubstCodeGraph := substCodeGraph_defined.to_definable

instance substCodeGraph_definable' : Γ-[m + 1]-Relation₄[V] SubstCodeGraph :=
  substCodeGraph_definable.of_deltaOne

lemma SubstCodeGraph.case_iff {me opp x y : V} :
    SubstCodeGraph me opp x y ↔
    (∃ a, x = pConst a ∧ y = pConst a) ∨
    (x = pSelf ∧ y = me) ∨ (x = pOpp ∧ y = opp) ∨
    (∃ p, x = pBot p ∧ y = pBot p) ∨
    (∃ p q p' q', SubstCodeGraph me opp p p' ∧ SubstCodeGraph me opp q q' ∧ x = pSim p q ∧ y = pSim p' q') ∨
    (∃ b a p q b' p' q', SubstCodeGraph me opp b b' ∧ SubstCodeGraph me opp p p' ∧ SubstCodeGraph me opp q q' ∧
      x = pIte b a p q ∧ y = pIte b' a p' q') ∨
    (∃ k g p q p' q', SubstCodeGraph me opp p p' ∧ SubstCodeGraph me opp q q' ∧
      x = pSearch k g p q ∧ y = pSearch k (substTemplate me opp g) p' q') ∨
    (¬IsShape y ∧ x = y) :=
  Iff.trans SubstCode.construction.case (by simp [SubstCode.construction, SubstCode.Phi, SubstCodeGraph])

section inversion

attribute [local simp] pConst pSelf pOpp pBot pSim pIte pSearch IsShape

lemma SubstCodeGraph.const_iff {me opp a y : V} : SubstCodeGraph me opp (pConst a) y ↔ y = pConst a := by
  rw [SubstCodeGraph.case_iff]; simp
  intro h₀ _ _ _ _ _ _ h; exact absurd h.symm (h₀ a)
lemma SubstCodeGraph.self_iff {me opp y : V} : SubstCodeGraph me opp pSelf y ↔ y = me := by
  rw [SubstCodeGraph.case_iff]; simp
  intro _ h₁ _ _ _ _ _ h; exact absurd h.symm h₁
lemma SubstCodeGraph.opp_iff {me opp y : V} : SubstCodeGraph me opp pOpp y ↔ y = opp := by
  rw [SubstCodeGraph.case_iff]; simp
  intro _ _ h₂ _ _ _ _ h; exact absurd h.symm h₂
lemma SubstCodeGraph.bot_iff {me opp p y : V} : SubstCodeGraph me opp (pBot p) y ↔ y = pBot p := by
  rw [SubstCodeGraph.case_iff]; simp
  intro _ _ _ h₃ _ _ _ h; exact absurd h.symm (h₃ p)
lemma SubstCodeGraph.sim_iff {me opp p q y : V} :
    SubstCodeGraph me opp (pSim p q) y ↔
    ∃ p' q', SubstCodeGraph me opp p p' ∧ SubstCodeGraph me opp q q' ∧ y = pSim p' q' := by
  rw [SubstCodeGraph.case_iff]; simp
  intro _ _ _ _ h₄ _ _ h; exact absurd h.symm (h₄ p q)
lemma SubstCodeGraph.ite_iff {me opp b a p q y : V} :
    SubstCodeGraph me opp (pIte b a p q) y ↔
    ∃ b' p' q', SubstCodeGraph me opp b b' ∧ SubstCodeGraph me opp p p' ∧ SubstCodeGraph me opp q q' ∧
      y = pIte b' a p' q' := by
  rw [SubstCodeGraph.case_iff]; simp
  intro _ _ _ _ _ h₅ _ h; exact absurd h.symm (h₅ b a p q)
lemma SubstCodeGraph.search_iff {me opp k g p q y : V} :
    SubstCodeGraph me opp (pSearch k g p q) y ↔
    ∃ p' q', SubstCodeGraph me opp p p' ∧ SubstCodeGraph me opp q q' ∧ y = pSearch k (substTemplate me opp g) p' q' := by
  rw [SubstCodeGraph.case_iff]; simp
  intro _ _ _ _ _ _ h₆ h; exact absurd h.symm (h₆ k g p q)
lemma SubstCodeGraph.of_not_shape {me opp x y : V} (hx : ¬IsShape x) : SubstCodeGraph me opp x y ↔ y = x := by
  rw [SubstCodeGraph.case_iff]
  constructor
  · rintro (⟨a, rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨p, rfl, _⟩ | ⟨p, q, p', q', _, _, rfl, _⟩ |
      ⟨b, a, p, q, b', p', q', _, _, _, rfl, _⟩ | ⟨k, g, p, q, p', q', _, _, rfl, _⟩ | ⟨_, h⟩)
    · exact absurd (Or.inl ⟨a, rfl⟩) hx
    · exact absurd (Or.inr (Or.inl rfl)) hx
    · exact absurd (Or.inr (Or.inr (Or.inl rfl))) hx
    · exact absurd (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, rfl⟩)))) hx
    · exact absurd (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, q, rfl⟩))))) hx
    · exact absurd (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨b, a, p, q, rfl⟩)))))) hx
    · exact absurd (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨k, g, p, q, rfl⟩)))))) hx
    · exact h.symm
  · rintro rfl
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hx, rfl⟩))))))

end inversion

/-! ### `substCode` is a total Σ₁ function -/

lemma substCodeGraph_exists (me opp x : V) : ∃ y, SubstCodeGraph me opp x y := by
  induction x using ISigma1.sigma1_order_induction with
  | hP => definability
  | ind x ih =>
    by_cases hx : IsShape x
    · rcases hx with ⟨a, rfl⟩ | rfl | rfl | ⟨p, rfl⟩ | ⟨p, q, rfl⟩ | ⟨b, a, p, q, rfl⟩ | ⟨k, g, p, q, rfl⟩
      · exact ⟨_, SubstCodeGraph.const_iff.mpr rfl⟩
      · exact ⟨_, SubstCodeGraph.self_iff.mpr rfl⟩
      · exact ⟨_, SubstCodeGraph.opp_iff.mpr rfl⟩
      · exact ⟨_, SubstCodeGraph.bot_iff.mpr rfl⟩
      · obtain ⟨p', hp⟩ := ih p (by simp); obtain ⟨q', hq⟩ := ih q (by simp)
        exact ⟨_, SubstCodeGraph.sim_iff.mpr ⟨p', q', hp, hq, rfl⟩⟩
      · obtain ⟨b', hb⟩ := ih b (by simp); obtain ⟨p', hp⟩ := ih p (by simp)
        obtain ⟨q', hq⟩ := ih q (by simp)
        exact ⟨_, SubstCodeGraph.ite_iff.mpr ⟨b', p', q', hb, hp, hq, rfl⟩⟩
      · obtain ⟨p', hp⟩ := ih p (by simp); obtain ⟨q', hq⟩ := ih q (by simp)
        exact ⟨_, SubstCodeGraph.search_iff.mpr ⟨p', q', hp, hq, rfl⟩⟩
    · exact ⟨x, (SubstCodeGraph.of_not_shape hx).mpr rfl⟩

lemma substCodeGraph_unique (me opp x : V) :
    ∀ y₁ y₂, SubstCodeGraph me opp x y₁ → SubstCodeGraph me opp x y₂ → y₁ = y₂ := by
  induction x using ISigma1.pi1_order_induction with
  | hP => definability
  | ind x ih =>
    intro y₁ y₂ h₁ h₂
    by_cases hx : IsShape x
    · rcases hx with ⟨a, rfl⟩ | rfl | rfl | ⟨p, rfl⟩ | ⟨p, q, rfl⟩ | ⟨b, a, p, q, rfl⟩ | ⟨k, g, p, q, rfl⟩
      · rw [SubstCodeGraph.const_iff] at h₁ h₂; rw [h₁, h₂]
      · rw [SubstCodeGraph.self_iff] at h₁ h₂; rw [h₁, h₂]
      · rw [SubstCodeGraph.opp_iff] at h₁ h₂; rw [h₁, h₂]
      · rw [SubstCodeGraph.bot_iff] at h₁ h₂; rw [h₁, h₂]
      · rcases SubstCodeGraph.sim_iff.mp h₁ with ⟨p₁, q₁, hp₁, hq₁, rfl⟩
        rcases SubstCodeGraph.sim_iff.mp h₂ with ⟨p₂, q₂, hp₂, hq₂, rfl⟩
        rw [ih p (by simp) _ _ hp₁ hp₂, ih q (by simp) _ _ hq₁ hq₂]
      · rcases SubstCodeGraph.ite_iff.mp h₁ with ⟨b₁, p₁, q₁, hb₁, hp₁, hq₁, rfl⟩
        rcases SubstCodeGraph.ite_iff.mp h₂ with ⟨b₂, p₂, q₂, hb₂, hp₂, hq₂, rfl⟩
        rw [ih b (by simp) _ _ hb₁ hb₂, ih p (by simp) _ _ hp₁ hp₂, ih q (by simp) _ _ hq₁ hq₂]
      · rcases SubstCodeGraph.search_iff.mp h₁ with ⟨p₁, q₁, hp₁, hq₁, rfl⟩
        rcases SubstCodeGraph.search_iff.mp h₂ with ⟨p₂, q₂, hp₂, hq₂, rfl⟩
        rw [ih p (by simp) _ _ hp₁ hp₂, ih q (by simp) _ _ hq₁ hq₂]
    · rw [SubstCodeGraph.of_not_shape hx] at h₁ h₂; rw [h₁, h₂]

lemma substCodeGraph_existsUnique (me opp x : V) : ∃! y, SubstCodeGraph me opp x y := by
  rcases substCodeGraph_exists me opp x with ⟨y, hy⟩
  exact ExistsUnique.intro y hy (fun y' h' ↦ substCodeGraph_unique me opp x y' y h' hy)

/-- **Program substitution**: `pSelf ↦ me`, `pOpp ↦ opp`, `pBot` frozen, stored templates
instantiated with the descriptions of `(me, opp)` — the engine's `Prog.subst`. -/
noncomputable def substCode (me opp x : V) : V := Classical.choose! (substCodeGraph_existsUnique me opp x)

lemma substCode_graph (me opp x : V) : SubstCodeGraph me opp x (substCode me opp x) :=
  Classical.choose!_spec (substCodeGraph_existsUnique me opp x)

lemma substCode_eq_of_graph {me opp x y : V} (h : SubstCodeGraph me opp x y) : substCode me opp x = y :=
  substCodeGraph_unique me opp x _ _ (substCode_graph me opp x) h

noncomputable def substCodeDef : 𝚺₁.Semisentence 4 := .mkSigma “y me opp x. !substCodeGraphDef.sigma me opp x y”

instance substCode_defined : 𝚺₁-Function₃ (substCode : V → V → V → V) via substCodeDef := .mk fun v ↦ by
  simp [substCodeDef, HierarchySymbol.Semiformula.val_sigma, substCodeGraph_defined.df]
  constructor
  · intro h; exact (substCode_eq_of_graph h).symm
  · intro h; rw [h]; exact substCode_graph _ _ _

instance substCode_definable : 𝚺₁-Function₃ (substCode : V → V → V → V) := substCode_defined.to_definable

instance substCode_definable' : Γ-[m + 1]-Function₃ (substCode : V → V → V → V) :=
  substCode_definable.of_sigmaOne

@[simp] lemma substCode_const (me opp a : V) : substCode me opp (pConst a) = pConst a :=
  substCode_eq_of_graph (SubstCodeGraph.const_iff.mpr rfl)
@[simp] lemma substCode_self (me opp : V) : substCode me opp (pSelf : V) = me :=
  substCode_eq_of_graph (SubstCodeGraph.self_iff.mpr rfl)
@[simp] lemma substCode_opp (me opp : V) : substCode me opp (pOpp : V) = opp :=
  substCode_eq_of_graph (SubstCodeGraph.opp_iff.mpr rfl)
@[simp] lemma substCode_bot (me opp p : V) : substCode me opp (pBot p) = pBot p :=
  substCode_eq_of_graph (SubstCodeGraph.bot_iff.mpr rfl)
@[simp] lemma substCode_sim (me opp p q : V) :
    substCode me opp (pSim p q) = pSim (substCode me opp p) (substCode me opp q) :=
  substCode_eq_of_graph (SubstCodeGraph.sim_iff.mpr ⟨_, _, substCode_graph me opp p, substCode_graph me opp q, rfl⟩)
@[simp] lemma substCode_ite (me opp b a p q : V) :
    substCode me opp (pIte b a p q) = pIte (substCode me opp b) a (substCode me opp p) (substCode me opp q) :=
  substCode_eq_of_graph (SubstCodeGraph.ite_iff.mpr
    ⟨_, _, _, substCode_graph me opp b, substCode_graph me opp p, substCode_graph me opp q, rfl⟩)
@[simp] lemma substCode_search (me opp k g p q : V) :
    substCode me opp (pSearch k g p q) = pSearch k (substTemplate me opp g) (substCode me opp p) (substCode me opp q) :=
  substCode_eq_of_graph (SubstCodeGraph.search_iff.mpr ⟨_, _, substCode_graph me opp p, substCode_graph me opp q, rfl⟩)
lemma substCode_of_not_shape {me opp x : V} (hx : ¬IsShape x) : substCode me opp x = x :=
  substCode_eq_of_graph ((SubstCodeGraph.of_not_shape hx).mpr rfl)

/-! ### τ-equivariance -/

/-- **τ commutes with substitution**: transposing a substituted program is substituting the
transposed frame into the transposed program (on every code). -/
theorem transposeCode_substCode (me opp x : V) :
    transposeCode (substCode me opp x) = substCode (transposeCode me) (transposeCode opp) (transposeCode x) := by
  induction x using ISigma1.pi1_order_induction with
  | hP => definability
  | ind x ih =>
    by_cases hx : IsShape x
    · rcases hx with ⟨a, rfl⟩ | rfl | rfl | ⟨p, rfl⟩ | ⟨p, q, rfl⟩ | ⟨b, a, p, q, rfl⟩ | ⟨k, g, p, q, rfl⟩
      · simp [transposeCode]
      · simp [transposeCode]
      · simp [transposeCode]
      · simp [transposeCode]
      · simp [transposeCode, ih p (by simp), ih q (by simp)]
      · simp [transposeCode, ih b (by simp), ih p (by simp), ih q (by simp)]
      · simp [transposeCode, ih p (by simp), ih q (by simp), revalueTemplate_substTemplate]
    · simp only [transposeCode]
      rw [substCode_of_not_shape hx, revalue_of_not_shape hx, substCode_of_not_shape hx]

end ArithS
