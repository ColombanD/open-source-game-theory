import ArithS.Agents.CodeTerm

/-!
# ArithS.Agents.CodeTermSlot — the structural term of a program code with the node's budget in a SLOT, on codes

Phase 2d of `SPRIME_SOURCE_OF_TRUTH.md` (decision (α), 2026-10-02). `codeTerm x` (`ArithS.Agents.CodeTerm`)
describes a program code by the structural term of its code, every `pSearch` budget a binary-numeral leaf. The
system closer of a member at budget `k₀` (`sysCloseTemplateAt`, `ArithS.Agents.Guard`) must describe the members
of the system with the budget `k₀` ABSTRACTED — written as the budget slot `^#6` of the stored template, which
the evaluator fills with the node's budget — so that a closed member's stored template is a constant in `k₀`
(Critch's (b); `Tau/NeverFitsSys.lean` is what happens otherwise). That description must be computed on codes,
in every model (the member list `d` of a `pSys d i` is a variable of the evaluator's fixpoint):

* **`codeTermAbs k₀ s x`** — `codeTerm x` with every `pSearch k₀ …` budget leaf written as the term code `s`
  (`budgetLeaf k₀ s k`: `s` at `k = k₀`, `binNumeral k` otherwise). A StrongFinite Δ₁ fixpoint on pairs `⟪x, t⟫`
  with the parameters `k₀, s` — `CodeTerm.Phi` clause for clause, one leaf changed; it descends through every
  shape `codeTerm` descends through, systems and member lists included.
* The equations `codeTermAbs_const … codeTermAbs_cons`, `codeTermAbs_of_not_shape` are the definition.
* **`codeTermAbs_binNumeral`**: `codeTermAbs k₀ (binNumeral k₀) x = codeTerm x` — the slot filled with the
  node's budget recovers the verbatim description (the code-level twin of `subst_codeTermMetaAbs`).
* `codeTermAbs_semiterm`: a term code of arity `n` whenever the slot is.

The meta twin is `codeTermMetaAbs` (`ArithS.Agents.CodeTermAbs`, with the code equation
`quote_emb_codeTermMetaAbs` there); the substitution lemma `termSubst_codeTermAbs` and the bridge
`guardCodeB_sysCloseTemplateAt` are in `ArithS.Agents.SubstTemplate`.

**Reading guide.** Definition: `budgetLeaf`, the clauses `CodeTermAbs.Phi` and §The equations. Foundation
plumbing: the blueprint, the construction and the `defined` instances — skip on first reading.
-/

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ### The budget leaf -/

open scoped Classical in
/-- The budget leaf of the abstracted description: the slot term `s` at the abstracted budget `k₀`, the binary
numeral otherwise. -/
noncomputable def budgetLeaf (k₀ s k : V) : V := if k = k₀ then s else binNumeral k

lemma budgetLeaf_self (k₀ s : V) : budgetLeaf k₀ s k₀ = s := by simp [budgetLeaf]

lemma budgetLeaf_of_ne {k₀ k : V} (h : k ≠ k₀) (s : V) : budgetLeaf k₀ s k = binNumeral k := by
  simp [budgetLeaf, h]

/-- With the numeral of the abstracted budget in the slot, the leaf is the numeral. -/
lemma budgetLeaf_binNumeral (k₀ k : V) : budgetLeaf k₀ (binNumeral k₀) k = binNumeral k := by
  unfold budgetLeaf; split_ifs with h
  · rw [h]
  · rfl

noncomputable def budgetLeafGraph : 𝚺₁.Semisentence 4 := .mkSigma
  “y k0 sl k. (k = k0 ∧ y = sl) ∨ (k ≠ k0 ∧ !binNumeralGraph y k)”

instance budgetLeaf.defined : 𝚺₁-Function₃ (budgetLeaf : V → V → V → V) via budgetLeafGraph := .mk fun v ↦ by
  simp [budgetLeafGraph, binNumeral.defined.df, budgetLeaf]
  by_cases h : v 3 = v 1 <;> simp [h]

lemma budgetLeaf_semiterm {n k₀ s : V} (hs : IsSemiterm ℒₒᵣ n s) (k : V) : IsSemiterm ℒₒᵣ n (budgetLeaf k₀ s k) := by
  unfold budgetLeaf; split_ifs
  · exact hs
  · exact binNumeral_semiterm n k

/-! ### The graph, as a fixpoint on pairs `⟪x, t⟫` — the clauses `Phi`, then Foundation plumbing -/

namespace CodeTermAbs

/-- `Phi ![k₀, s] C ⟪x, t⟫`: `t` is the structural term of the program code `x` with every budget `k₀` written
as the term code `s`, given the sub-results in `C`. -/
def Phi (param : Fin 2 → V) (C : Set V) (pr : V) : Prop :=
  (∃ a : V, pr = ⟪pConst a, ppairTerm (binNumeral 0) (binNumeral a) ^+ (𝟏 : V)⟫) ∨
  pr = ⟪(pSelf : V), ppairTerm (binNumeral 1) (binNumeral 0) ^+ (𝟏 : V)⟫ ∨
  pr = ⟪(pOpp : V), ppairTerm (binNumeral 2) (binNumeral 0) ^+ (𝟏 : V)⟫ ∨
  (∃ p tp : V, ⟪p, tp⟫ ∈ C ∧ pr = ⟪pBot p, ppairTerm (binNumeral 3) tp ^+ (𝟏 : V)⟫) ∨
  (∃ p q tp tq : V, ⟪p, tp⟫ ∈ C ∧ ⟪q, tq⟫ ∈ C ∧
    pr = ⟪pSim p q, ppairTerm (binNumeral 4) (ppairTerm tp tq) ^+ (𝟏 : V)⟫) ∨
  (∃ b a p q tb tp tq : V, ⟪b, tb⟫ ∈ C ∧ ⟪p, tp⟫ ∈ C ∧ ⟪q, tq⟫ ∈ C ∧
    pr = ⟪pIte b a p q, ppairTerm (binNumeral 5) (ppairTerm tb (ppairTerm (binNumeral a) (ppairTerm tp tq))) ^+ (𝟏 : V)⟫) ∨
  (∃ k g p q tp tq : V, ⟪p, tp⟫ ∈ C ∧ ⟪q, tq⟫ ∈ C ∧
    pr = ⟪pSearch k g p q, ppairTerm (binNumeral 6) (ppairTerm (budgetLeaf (param 0) (param 1) k) (ppairTerm (binNumeral g) (ppairTerm tp tq))) ^+ (𝟏 : V)⟫) ∨
  (∃ v θ p q tv tp tq : V, ⟪v, tv⟫ ∈ C ∧ ⟪p, tp⟫ ∈ C ∧ ⟪q, tq⟫ ∈ C ∧
    pr = ⟪pTvote v θ p q, ppairTerm (binNumeral 7) (ppairTerm tv (ppairTerm (binNumeral θ) (ppairTerm tp tq))) ^+ (𝟏 : V)⟫) ∨
  (∃ d i td : V, ⟪d, td⟫ ∈ C ∧ pr = ⟪pSys d i, ppairTerm (binNumeral 8) (ppairTerm td (binNumeral i)) ^+ (𝟏 : V)⟫) ∨
  (∃ j : V, pr = ⟪pSelfIdx j, ppairTerm (binNumeral 9) (binNumeral j) ^+ (𝟏 : V)⟫) ∨
  (∃ e r te tr : V, ⟪e, te⟫ ∈ C ∧ ⟪r, tr⟫ ∈ C ∧
    pr = ⟪pCons e r, ppairTerm (binNumeral 10) (ppairTerm te tr) ^+ (𝟏 : V)⟫) ∨
  (∃ x : V, ¬IsShape x ∧ pr = ⟪x, binNumeral x⟫)

noncomputable def blueprint : Fixpoint.Blueprint 2 := ⟨.mkDelta
  (.mkSigma “pr C k0 sl. ∃ x <⁺ pr, ∃ t <⁺ pr, !pairDef pr x t ∧
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
        ∃ b6, !binNumeralGraph b6 6 ∧ ∃ bk, !budgetLeafGraph bk k0 sl k ∧ ∃ bg, !binNumeralGraph bg g ∧
        ∃ r1, !ppairTermGraph r1 tp tq ∧ ∃ r2, !ppairTermGraph r2 bg r1 ∧ ∃ r3, !ppairTermGraph r3 bk r2 ∧
        ∃ r, !ppairTermGraph r b6 r3 ∧ !qqAddGraph t r ↑Arithmetic.one) ∨
      (∃ v < x, ∃ th < x, ∃ p < x, ∃ q < x, !pTvoteGraph x v th p q ∧
        ∃ tv < t, ∃ tp < t, ∃ tq < t, :⟪v, tv⟫:∈ C ∧ :⟪p, tp⟫:∈ C ∧ :⟪q, tq⟫:∈ C ∧
        ∃ b7, !binNumeralGraph b7 7 ∧ ∃ bt, !binNumeralGraph bt th ∧ ∃ r1, !ppairTermGraph r1 tp tq ∧
        ∃ r2, !ppairTermGraph r2 bt r1 ∧ ∃ r3, !ppairTermGraph r3 tv r2 ∧ ∃ r, !ppairTermGraph r b7 r3 ∧
        !qqAddGraph t r ↑Arithmetic.one) ∨
      (∃ d < x, ∃ i < x, !pSysGraph x d i ∧ ∃ td < t, :⟪d, td⟫:∈ C ∧
        ∃ b8, !binNumeralGraph b8 8 ∧ ∃ bi, !binNumeralGraph bi i ∧ ∃ r1, !ppairTermGraph r1 td bi ∧
        ∃ r, !ppairTermGraph r b8 r1 ∧ !qqAddGraph t r ↑Arithmetic.one) ∨
      (∃ j < x, !pSelfIdxGraph x j ∧
        ∃ b9, !binNumeralGraph b9 9 ∧ ∃ bj, !binNumeralGraph bj j ∧ ∃ r, !ppairTermGraph r b9 bj ∧
        !qqAddGraph t r ↑Arithmetic.one) ∨
      (∃ e < x, ∃ rr < x, !pConsGraph x e rr ∧ ∃ te < t, ∃ tr < t, :⟪e, te⟫:∈ C ∧ :⟪rr, tr⟫:∈ C ∧
        ∃ b10, !binNumeralGraph b10 10 ∧ ∃ r1, !ppairTermGraph r1 te tr ∧ ∃ r, !ppairTermGraph r b10 r1 ∧
        !qqAddGraph t r ↑Arithmetic.one) ∨
      (¬!isShape x ∧ !binNumeralGraph t x) )”)
  (.mkPi “pr C k0 sl. ∃ x <⁺ pr, ∃ t <⁺ pr, !pairDef pr x t ∧
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
        ∀ b6, !binNumeralGraph b6 6 → ∀ bk, !budgetLeafGraph bk k0 sl k → ∀ bg, !binNumeralGraph bg g →
        ∀ r1, !ppairTermGraph r1 tp tq → ∀ r2, !ppairTermGraph r2 bg r1 → ∀ r3, !ppairTermGraph r3 bk r2 →
        ∀ r, !ppairTermGraph r b6 r3 → ∀ s, !qqAddGraph s r ↑Arithmetic.one → t = s) ∨
      (∃ v < x, ∃ th < x, ∃ p < x, ∃ q < x, !pTvoteGraph x v th p q ∧
        ∃ tv < t, ∃ tp < t, ∃ tq < t, :⟪v, tv⟫:∈ C ∧ :⟪p, tp⟫:∈ C ∧ :⟪q, tq⟫:∈ C ∧
        ∀ b7, !binNumeralGraph b7 7 → ∀ bt, !binNumeralGraph bt th → ∀ r1, !ppairTermGraph r1 tp tq →
        ∀ r2, !ppairTermGraph r2 bt r1 → ∀ r3, !ppairTermGraph r3 tv r2 → ∀ r, !ppairTermGraph r b7 r3 →
        ∀ s, !qqAddGraph s r ↑Arithmetic.one → t = s) ∨
      (∃ d < x, ∃ i < x, !pSysGraph x d i ∧ ∃ td < t, :⟪d, td⟫:∈ C ∧
        ∀ b8, !binNumeralGraph b8 8 → ∀ bi, !binNumeralGraph bi i → ∀ r1, !ppairTermGraph r1 td bi →
        ∀ r, !ppairTermGraph r b8 r1 → ∀ s, !qqAddGraph s r ↑Arithmetic.one → t = s) ∨
      (∃ j < x, !pSelfIdxGraph x j ∧
        ∀ b9, !binNumeralGraph b9 9 → ∀ bj, !binNumeralGraph bj j → ∀ r, !ppairTermGraph r b9 bj →
        ∀ s, !qqAddGraph s r ↑Arithmetic.one → t = s) ∨
      (∃ e < x, ∃ rr < x, !pConsGraph x e rr ∧ ∃ te < t, ∃ tr < t, :⟪e, te⟫:∈ C ∧ :⟪rr, tr⟫:∈ C ∧
        ∀ b10, !binNumeralGraph b10 10 → ∀ r1, !ppairTermGraph r1 te tr → ∀ r, !ppairTermGraph r b10 r1 →
        ∀ s, !qqAddGraph s r ↑Arithmetic.one → t = s) ∨
      (¬!isShape x ∧ ∀ s, !binNumeralGraph s x → t = s) )”)⟩

/-- `Phi` with the bounds the blueprint carries. -/
private lemma phi_iff (param : Fin 2 → V) (C pr : V) :
    Phi param {x | x ∈ C} pr ↔
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
        t = ppairTerm (binNumeral 6) (ppairTerm (budgetLeaf (param 0) (param 1) k) (ppairTerm (binNumeral g) (ppairTerm tp tq))) ^+ (𝟏 : V)) ∨
      (∃ v < x, ∃ θ < x, ∃ p < x, ∃ q < x, x = pTvote v θ p q ∧
        ∃ tv < t, ∃ tp < t, ∃ tq < t, ⟪v, tv⟫ ∈ C ∧ ⟪p, tp⟫ ∈ C ∧ ⟪q, tq⟫ ∈ C ∧
        t = ppairTerm (binNumeral 7) (ppairTerm tv (ppairTerm (binNumeral θ) (ppairTerm tp tq))) ^+ (𝟏 : V)) ∨
      (∃ d < x, ∃ i < x, x = pSys d i ∧ ∃ td < t, ⟪d, td⟫ ∈ C ∧
        t = ppairTerm (binNumeral 8) (ppairTerm td (binNumeral i)) ^+ (𝟏 : V)) ∨
      (∃ j < x, x = pSelfIdx j ∧ t = ppairTerm (binNumeral 9) (binNumeral j) ^+ (𝟏 : V)) ∨
      (∃ e < x, ∃ r < x, x = pCons e r ∧ ∃ te < t, ∃ tr < t, ⟪e, te⟫ ∈ C ∧ ⟪r, tr⟫ ∈ C ∧
        t = ppairTerm (binNumeral 10) (ppairTerm te tr) ^+ (𝟏 : V)) ∨
      (¬IsShape x ∧ t = binNumeral x) ) := by
  constructor
  · rintro (⟨a, rfl⟩ | rfl | rfl | ⟨p, tp, h, rfl⟩ | ⟨p, q, tp, tq, hp, hq, rfl⟩ |
      ⟨b, a, p, q, tb, tp, tq, hb, hp, hq, rfl⟩ | ⟨k, g, p, q, tp, tq, hp, hq, rfl⟩ |
      ⟨v, θ, p, q, tv, tp, tq, hv, hp, hq, rfl⟩ | ⟨d, i, td, hd, rfl⟩ | ⟨j, rfl⟩ |
      ⟨e, r, te, tr, he, hr, rfl⟩ | ⟨x, hx, rfl⟩)
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
    · exact ⟨_, by simp, _, by simp, rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨v, by simp, θ, by simp, p, by simp, q, by simp, rfl,
          tv, lt_trans (lt_ppairTerm_left _ _) (lt_ppairTerm_succ_right _ _),
          tp, lt_trans (lt_ppairTerm_left _ _) (lt_trans (lt_ppairTerm_right _ _)
            (lt_trans (lt_ppairTerm_right _ _) (lt_ppairTerm_succ_right _ _))),
          tq, lt_trans (lt_ppairTerm_right _ _) (lt_trans (lt_ppairTerm_right _ _)
            (lt_trans (lt_ppairTerm_right _ _) (lt_ppairTerm_succ_right _ _))),
          hv, hp, hq, rfl⟩)))))))⟩
    · exact ⟨_, by simp, _, by simp, rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨d, by simp, i, by simp, rfl, td, lt_trans (lt_ppairTerm_left _ _) (lt_ppairTerm_succ_right _ _),
          hd, rfl⟩))))))))⟩
    · exact ⟨_, by simp, _, by simp, rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨j, by simp, rfl, rfl⟩)))))))))⟩
    · exact ⟨_, by simp, _, by simp, rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨e, by simp, r, by simp, rfl, te, lt_trans (lt_ppairTerm_left _ _) (lt_ppairTerm_succ_right _ _),
          tr, lt_trans (lt_ppairTerm_right _ _) (lt_ppairTerm_succ_right _ _), he, hr, rfl⟩))))))))))⟩
    · exact ⟨_, by simp, _, by simp, rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨hx, rfl⟩))))))))))⟩
  · rintro ⟨x, _, t, _, rfl, (⟨a, _, rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨p, _, rfl, tp, _, h, rfl⟩ | ⟨p, _, q, _, rfl, tp, _, tq, _, hp, hq, rfl⟩ |
      ⟨b, _, a, _, p, _, q, _, rfl, tb, _, tp, _, tq, _, hb, hp, hq, rfl⟩ |
      ⟨k, _, g, _, p, _, q, _, rfl, tp, _, tq, _, hp, hq, rfl⟩ |
      ⟨v, _, θ, _, p, _, q, _, rfl, tv, _, tp, _, tq, _, hv, hp, hq, rfl⟩ |
      ⟨d, _, i, _, rfl, td, _, hd, rfl⟩ | ⟨j, _, rfl, rfl⟩ |
      ⟨e, _, r, _, rfl, te, _, tr, _, he, hr, rfl⟩ | ⟨hx, rfl⟩)⟩
    · exact Or.inl ⟨a, rfl⟩
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨p, tp, h, rfl⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, q, tp, tq, hp, hq, rfl⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨b, a, p, q, tb, tp, tq, hb, hp, hq, rfl⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨k, g, p, q, tp, tq, hp, hq, rfl⟩))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨v, θ, p, q, tv, tp, tq, hv, hp, hq, rfl⟩)))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨d, i, td, hd, rfl⟩))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨j, rfl⟩)))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨e, r, te, tr, he, hr, rfl⟩))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨x, hx, rfl⟩))))))))))

noncomputable def construction : Fixpoint.Construction V blueprint where
  Φ := Phi
  defined := .mk <| by
    constructor
    · intro v
      simp [blueprint, HierarchySymbol.Semiformula.val_sigma, binNumeral.defined.df, ppairTerm.defined.df,
        budgetLeaf.defined.df, qqAdd_defined.iff, numeral_eq_natCast]
    · intro v
      symm
      simpa [blueprint, HierarchySymbol.Semiformula.val_sigma, binNumeral.defined.df, ppairTerm.defined.df,
        budgetLeaf.defined.df, qqAdd_defined.iff, numeral_eq_natCast, pSelfGraph, pOppGraph, pSelf, pOpp, lt_and_eq_succ_iff]
        using phi_iff (fun i ↦ v i.succ.succ) (v 1) (v 0)
  monotone := by
    rintro C C' hC param pr (⟨a, rfl⟩ | rfl | rfl | ⟨p, tp, h, rfl⟩ | ⟨p, q, tp, tq, hp, hq, rfl⟩ |
      ⟨b, a, p, q, tb, tp, tq, hb, hp, hq, rfl⟩ | ⟨k, g, p, q, tp, tq, hp, hq, rfl⟩ |
      ⟨v, θ, p, q, tv, tp, tq, hv, hp, hq, rfl⟩ | ⟨d, i, td, hd, rfl⟩ | ⟨j, rfl⟩ |
      ⟨e, r, te, tr, he, hr, rfl⟩ | ⟨x, hx, rfl⟩)
    · exact Or.inl ⟨a, rfl⟩
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨p, tp, hC h, rfl⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, q, tp, tq, hC hp, hC hq, rfl⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨b, a, p, q, tb, tp, tq, hC hb, hC hp, hC hq, rfl⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨k, g, p, q, tp, tq, hC hp, hC hq, rfl⟩))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨v, θ, p, q, tv, tp, tq, hC hv, hC hp, hC hq, rfl⟩)))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨d, i, td, hC hd, rfl⟩))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨j, rfl⟩)))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨e, r, te, tr, hC he, hC hr, rfl⟩))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨x, hx, rfl⟩))))))))))

instance : construction.StrongFinite V where
  strong_finite := by
    rintro C param pr (⟨a, rfl⟩ | rfl | rfl | ⟨p, tp, h, rfl⟩ | ⟨p, q, tp, tq, hp, hq, rfl⟩ |
      ⟨b, a, p, q, tb, tp, tq, hb, hp, hq, rfl⟩ | ⟨k, g, p, q, tp, tq, hp, hq, rfl⟩ |
      ⟨v, θ, p, q, tv, tp, tq, hv, hp, hq, rfl⟩ | ⟨d, i, td, hd, rfl⟩ | ⟨j, rfl⟩ |
      ⟨e, r, te, tr, he, hr, rfl⟩ | ⟨x, hx, rfl⟩)
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
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨v, θ, p, q, tv, tp, tq,
        ⟨hv, pair_lt_pair (by simp) (lt_trans (lt_ppairTerm_left _ _) (lt_ppairTerm_succ_right _ _))⟩,
        ⟨hp, pair_lt_pair (by simp) (lt_trans (lt_ppairTerm_left _ _) (lt_trans (lt_ppairTerm_right _ _)
            (lt_trans (lt_ppairTerm_right _ _) (lt_ppairTerm_succ_right _ _))))⟩,
        ⟨hq, pair_lt_pair (by simp) (lt_trans (lt_ppairTerm_right _ _) (lt_trans (lt_ppairTerm_right _ _)
            (lt_trans (lt_ppairTerm_right _ _) (lt_ppairTerm_succ_right _ _))))⟩, rfl⟩)))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨d, i, td,
        ⟨hd, pair_lt_pair (by simp) (lt_trans (lt_ppairTerm_left _ _) (lt_ppairTerm_succ_right _ _))⟩, rfl⟩))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨j, rfl⟩)))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨e, r, te, tr,
        ⟨he, pair_lt_pair (by simp) (lt_trans (lt_ppairTerm_left _ _) (lt_ppairTerm_succ_right _ _))⟩,
        ⟨hr, pair_lt_pair (by simp) (lt_trans (lt_ppairTerm_right _ _) (lt_ppairTerm_succ_right _ _))⟩, rfl⟩))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨x, hx, rfl⟩))))))))))

end CodeTermAbs

/-- `CodeTermAbsGraph k₀ s x t`: `t` is the structural term code of the program code `x`, every budget `k₀`
written as the term code `s`. -/
def CodeTermAbsGraph (k₀ s x t : V) : Prop := CodeTermAbs.construction.Fixpoint ![k₀, s] ⟪x, t⟫

noncomputable def codeTermAbsGraphDef : 𝚫₁.Semisentence 4 := .mkDelta
  (.mkSigma “k0 sl x t. ∃ pr <⁺ (x + t + 1)², !pairDef pr x t ∧ !CodeTermAbs.blueprint.fixpointDefΔ₁.sigma pr k0 sl”)
  (.mkPi “k0 sl x t. ∀ pr <⁺ (x + t + 1)², !pairDef pr x t → !CodeTermAbs.blueprint.fixpointDefΔ₁.pi pr k0 sl”)

section

private lemma codeTermAbs_param_eq (v : Fin 3 → V) : (fun i ↦ v i.succ) = ![v 1, v 2] := by
  funext i; fin_cases i <;> rfl

instance codeTermAbsGraph_defined : 𝚫₁-Relation₄[V] CodeTermAbsGraph via codeTermAbsGraphDef := .mk
  ⟨by intro v
      simp [codeTermAbsGraphDef, HierarchySymbol.Semiformula.val_sigma,
        CodeTermAbs.construction.fixpoint_definedΔ₁.proper.iff', CodeTermAbs.construction.fixpoint_definedΔ₁.df]
      constructor
      · rintro h x _ rfl; simpa [codeTermAbs_param_eq] using h
      · intro h; have := h ⟪v 2, v 3⟫ (by simp) rfl; simpa [codeTermAbs_param_eq] using this,
   by intro v
      simp [codeTermAbsGraphDef, HierarchySymbol.Semiformula.val_sigma,
        CodeTermAbs.construction.fixpoint_definedΔ₁.df, CodeTermAbsGraph]⟩

instance codeTermAbsGraph_definable : 𝚫₁-Relation₄[V] CodeTermAbsGraph := codeTermAbsGraph_defined.to_definable

instance codeTermAbsGraph_definable' : Γ-[m + 1]-Relation₄[V] CodeTermAbsGraph :=
  codeTermAbsGraph_definable.of_deltaOne

end

/-! ### Case analysis and inversion -/

lemma CodeTermAbsGraph.case_iff {k₀ s x t : V} :
    CodeTermAbsGraph k₀ s x t ↔
    (∃ a, x = pConst a ∧ t = ppairTerm (binNumeral 0) (binNumeral a) ^+ (𝟏 : V)) ∨
    (x = pSelf ∧ t = ppairTerm (binNumeral 1) (binNumeral 0) ^+ (𝟏 : V)) ∨
    (x = pOpp ∧ t = ppairTerm (binNumeral 2) (binNumeral 0) ^+ (𝟏 : V)) ∨
    (∃ p tp, CodeTermAbsGraph k₀ s p tp ∧ x = pBot p ∧ t = ppairTerm (binNumeral 3) tp ^+ (𝟏 : V)) ∨
    (∃ p q tp tq, CodeTermAbsGraph k₀ s p tp ∧ CodeTermAbsGraph k₀ s q tq ∧ x = pSim p q ∧
      t = ppairTerm (binNumeral 4) (ppairTerm tp tq) ^+ (𝟏 : V)) ∨
    (∃ b a p q tb tp tq, CodeTermAbsGraph k₀ s b tb ∧ CodeTermAbsGraph k₀ s p tp ∧ CodeTermAbsGraph k₀ s q tq ∧ x = pIte b a p q ∧
      t = ppairTerm (binNumeral 5) (ppairTerm tb (ppairTerm (binNumeral a) (ppairTerm tp tq))) ^+ (𝟏 : V)) ∨
    (∃ k g p q tp tq, CodeTermAbsGraph k₀ s p tp ∧ CodeTermAbsGraph k₀ s q tq ∧ x = pSearch k g p q ∧
      t = ppairTerm (binNumeral 6) (ppairTerm (budgetLeaf k₀ s k) (ppairTerm (binNumeral g) (ppairTerm tp tq))) ^+ (𝟏 : V)) ∨
    (∃ v θ p q tv tp tq, CodeTermAbsGraph k₀ s v tv ∧ CodeTermAbsGraph k₀ s p tp ∧ CodeTermAbsGraph k₀ s q tq ∧ x = pTvote v θ p q ∧
      t = ppairTerm (binNumeral 7) (ppairTerm tv (ppairTerm (binNumeral θ) (ppairTerm tp tq))) ^+ (𝟏 : V)) ∨
    (∃ d i td, CodeTermAbsGraph k₀ s d td ∧ x = pSys d i ∧ t = ppairTerm (binNumeral 8) (ppairTerm td (binNumeral i)) ^+ (𝟏 : V)) ∨
    (∃ j, x = pSelfIdx j ∧ t = ppairTerm (binNumeral 9) (binNumeral j) ^+ (𝟏 : V)) ∨
    (∃ e r te tr, CodeTermAbsGraph k₀ s e te ∧ CodeTermAbsGraph k₀ s r tr ∧ x = pCons e r ∧
      t = ppairTerm (binNumeral 10) (ppairTerm te tr) ^+ (𝟏 : V)) ∨
    (¬IsShape x ∧ t = binNumeral x) :=
  Iff.trans CodeTermAbs.construction.case (by simp [CodeTermAbs.construction, CodeTermAbs.Phi, CodeTermAbsGraph])

section inversion

variable {k₀ s : V}

attribute [local simp] pConst pSelf pOpp pBot pSim pIte pSearch pTvote pSys pSelfIdx pCons IsShape

lemma CodeTermAbsGraph.const_iff {a t : V} :
    CodeTermAbsGraph k₀ s (pConst a) t ↔ t = ppairTerm (binNumeral 0) (binNumeral a) ^+ (𝟏 : V) := by
  rw [CodeTermAbsGraph.case_iff]; simp
lemma CodeTermAbsGraph.self_iff {t : V} : CodeTermAbsGraph k₀ s pSelf t ↔ t = ppairTerm (binNumeral 1) (binNumeral 0) ^+ (𝟏 : V) := by
  rw [CodeTermAbsGraph.case_iff]; simp
lemma CodeTermAbsGraph.opp_iff {t : V} : CodeTermAbsGraph k₀ s pOpp t ↔ t = ppairTerm (binNumeral 2) (binNumeral 0) ^+ (𝟏 : V) := by
  rw [CodeTermAbsGraph.case_iff]; simp
lemma CodeTermAbsGraph.bot_iff {p t : V} :
    CodeTermAbsGraph k₀ s (pBot p) t ↔ ∃ tp, CodeTermAbsGraph k₀ s p tp ∧ t = ppairTerm (binNumeral 3) tp ^+ (𝟏 : V) := by
  rw [CodeTermAbsGraph.case_iff]; simp
lemma CodeTermAbsGraph.sim_iff {p q t : V} :
    CodeTermAbsGraph k₀ s (pSim p q) t ↔
    ∃ tp tq, CodeTermAbsGraph k₀ s p tp ∧ CodeTermAbsGraph k₀ s q tq ∧ t = ppairTerm (binNumeral 4) (ppairTerm tp tq) ^+ (𝟏 : V) := by
  rw [CodeTermAbsGraph.case_iff]; simp
lemma CodeTermAbsGraph.ite_iff {b a p q t : V} :
    CodeTermAbsGraph k₀ s (pIte b a p q) t ↔
    ∃ tb tp tq, CodeTermAbsGraph k₀ s b tb ∧ CodeTermAbsGraph k₀ s p tp ∧ CodeTermAbsGraph k₀ s q tq ∧
      t = ppairTerm (binNumeral 5) (ppairTerm tb (ppairTerm (binNumeral a) (ppairTerm tp tq))) ^+ (𝟏 : V) := by
  rw [CodeTermAbsGraph.case_iff]; simp
lemma CodeTermAbsGraph.search_iff {k g p q t : V} :
    CodeTermAbsGraph k₀ s (pSearch k g p q) t ↔
    ∃ tp tq, CodeTermAbsGraph k₀ s p tp ∧ CodeTermAbsGraph k₀ s q tq ∧
      t = ppairTerm (binNumeral 6) (ppairTerm (budgetLeaf k₀ s k) (ppairTerm (binNumeral g) (ppairTerm tp tq))) ^+ (𝟏 : V) := by
  rw [CodeTermAbsGraph.case_iff]; simp
lemma CodeTermAbsGraph.tvote_iff {v θ p q t : V} :
    CodeTermAbsGraph k₀ s (pTvote v θ p q) t ↔
    ∃ tv tp tq, CodeTermAbsGraph k₀ s v tv ∧ CodeTermAbsGraph k₀ s p tp ∧ CodeTermAbsGraph k₀ s q tq ∧
      t = ppairTerm (binNumeral 7) (ppairTerm tv (ppairTerm (binNumeral θ) (ppairTerm tp tq))) ^+ (𝟏 : V) := by
  rw [CodeTermAbsGraph.case_iff]; simp
lemma CodeTermAbsGraph.sys_iff {d i t : V} :
    CodeTermAbsGraph k₀ s (pSys d i) t ↔
    ∃ td, CodeTermAbsGraph k₀ s d td ∧ t = ppairTerm (binNumeral 8) (ppairTerm td (binNumeral i)) ^+ (𝟏 : V) := by
  rw [CodeTermAbsGraph.case_iff]; simp
lemma CodeTermAbsGraph.selfIdx_iff {j t : V} :
    CodeTermAbsGraph k₀ s (pSelfIdx j) t ↔ t = ppairTerm (binNumeral 9) (binNumeral j) ^+ (𝟏 : V) := by
  rw [CodeTermAbsGraph.case_iff]; simp
lemma CodeTermAbsGraph.cons_iff {e r t : V} :
    CodeTermAbsGraph k₀ s (pCons e r) t ↔
    ∃ te tr, CodeTermAbsGraph k₀ s e te ∧ CodeTermAbsGraph k₀ s r tr ∧ t = ppairTerm (binNumeral 10) (ppairTerm te tr) ^+ (𝟏 : V) := by
  rw [CodeTermAbsGraph.case_iff]; simp
lemma CodeTermAbsGraph.of_not_shape {x t : V} (hx : ¬IsShape x) : CodeTermAbsGraph k₀ s x t ↔ t = binNumeral x := by
  rw [CodeTermAbsGraph.case_iff]
  constructor
  · rintro (⟨a, rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨p, tp, _, rfl, _⟩ | ⟨p, q, tp, tq, _, _, rfl, _⟩ |
      ⟨b, a, p, q, tb, tp, tq, _, _, _, rfl, _⟩ | ⟨k, g, p, q, tp, tq, _, _, rfl, _⟩ |
      ⟨v, θ, p, q, tv, tp, tq, _, _, _, rfl, _⟩ | ⟨d, i, td, _, rfl, _⟩ | ⟨j, rfl, _⟩ |
      ⟨e, r, te, tr, _, _, rfl, _⟩ | ⟨_, h⟩)
    · exact absurd (IsShape.const a) hx
    · exact absurd IsShape.self hx
    · exact absurd IsShape.opp hx
    · exact absurd (IsShape.bot p) hx
    · exact absurd (IsShape.sim p q) hx
    · exact absurd (IsShape.ite b a p q) hx
    · exact absurd (IsShape.search k g p q) hx
    · exact absurd (IsShape.tvote v θ p q) hx
    · exact absurd (IsShape.sys d i) hx
    · exact absurd (IsShape.selfIdx j) hx
    · exact absurd (IsShape.cons e r) hx
    · exact h
  · rintro rfl
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨hx, rfl⟩))))))))))

end inversion

/-! ### `codeTermAbs` is a total Σ₁ function -/

lemma codeTermAbsGraph_exists (k₀ s x : V) : ∃ t, CodeTermAbsGraph k₀ s x t := by
  induction x using ISigma1.sigma1_order_induction with
  | hP => definability
  | ind x ih =>
    by_cases hx : IsShape x
    · rcases hx with ⟨a, rfl⟩ | rfl | rfl | ⟨p, rfl⟩ | ⟨p, q, rfl⟩ | ⟨b, a, p, q, rfl⟩ | ⟨k, g, p, q, rfl⟩ |
        ⟨v, θ, p, q, rfl⟩ | ⟨d, i, rfl⟩ | ⟨j, rfl⟩ | ⟨e, r, rfl⟩
      · exact ⟨_, CodeTermAbsGraph.const_iff.mpr rfl⟩
      · exact ⟨_, CodeTermAbsGraph.self_iff.mpr rfl⟩
      · exact ⟨_, CodeTermAbsGraph.opp_iff.mpr rfl⟩
      · obtain ⟨tp, hp⟩ := ih p (by simp)
        exact ⟨_, CodeTermAbsGraph.bot_iff.mpr ⟨tp, hp, rfl⟩⟩
      · obtain ⟨tp, hp⟩ := ih p (by simp); obtain ⟨tq, hq⟩ := ih q (by simp)
        exact ⟨_, CodeTermAbsGraph.sim_iff.mpr ⟨tp, tq, hp, hq, rfl⟩⟩
      · obtain ⟨tb, hb⟩ := ih b (by simp); obtain ⟨tp, hp⟩ := ih p (by simp)
        obtain ⟨tq, hq⟩ := ih q (by simp)
        exact ⟨_, CodeTermAbsGraph.ite_iff.mpr ⟨tb, tp, tq, hb, hp, hq, rfl⟩⟩
      · obtain ⟨tp, hp⟩ := ih p (by simp); obtain ⟨tq, hq⟩ := ih q (by simp)
        exact ⟨_, CodeTermAbsGraph.search_iff.mpr ⟨tp, tq, hp, hq, rfl⟩⟩
      · obtain ⟨tv, hv⟩ := ih v (by simp); obtain ⟨tp, hp⟩ := ih p (by simp)
        obtain ⟨tq, hq⟩ := ih q (by simp)
        exact ⟨_, CodeTermAbsGraph.tvote_iff.mpr ⟨tv, tp, tq, hv, hp, hq, rfl⟩⟩
      · obtain ⟨td, hd⟩ := ih d (by simp)
        exact ⟨_, CodeTermAbsGraph.sys_iff.mpr ⟨td, hd, rfl⟩⟩
      · exact ⟨_, CodeTermAbsGraph.selfIdx_iff.mpr rfl⟩
      · obtain ⟨te, he⟩ := ih e (by simp); obtain ⟨tr, hr⟩ := ih r (by simp)
        exact ⟨_, CodeTermAbsGraph.cons_iff.mpr ⟨te, tr, he, hr, rfl⟩⟩
    · exact ⟨_, (CodeTermAbsGraph.of_not_shape hx).mpr rfl⟩

lemma codeTermAbsGraph_unique (k₀ s x : V) : ∀ t₁ t₂, CodeTermAbsGraph k₀ s x t₁ → CodeTermAbsGraph k₀ s x t₂ → t₁ = t₂ := by
  induction x using ISigma1.pi1_order_induction with
  | hP => definability
  | ind x ih =>
    intro t₁ t₂ h₁ h₂
    by_cases hx : IsShape x
    · rcases hx with ⟨a, rfl⟩ | rfl | rfl | ⟨p, rfl⟩ | ⟨p, q, rfl⟩ | ⟨b, a, p, q, rfl⟩ | ⟨k, g, p, q, rfl⟩ |
        ⟨v, θ, p, q, rfl⟩ | ⟨d, i, rfl⟩ | ⟨j, rfl⟩ | ⟨e, r, rfl⟩
      · rw [CodeTermAbsGraph.const_iff] at h₁ h₂; rw [h₁, h₂]
      · rw [CodeTermAbsGraph.self_iff] at h₁ h₂; rw [h₁, h₂]
      · rw [CodeTermAbsGraph.opp_iff] at h₁ h₂; rw [h₁, h₂]
      · rcases CodeTermAbsGraph.bot_iff.mp h₁ with ⟨p₁, hp₁, rfl⟩
        rcases CodeTermAbsGraph.bot_iff.mp h₂ with ⟨p₂, hp₂, rfl⟩
        rw [ih p (by simp) _ _ hp₁ hp₂]
      · rcases CodeTermAbsGraph.sim_iff.mp h₁ with ⟨p₁, q₁, hp₁, hq₁, rfl⟩
        rcases CodeTermAbsGraph.sim_iff.mp h₂ with ⟨p₂, q₂, hp₂, hq₂, rfl⟩
        rw [ih p (by simp) _ _ hp₁ hp₂, ih q (by simp) _ _ hq₁ hq₂]
      · rcases CodeTermAbsGraph.ite_iff.mp h₁ with ⟨b₁, p₁, q₁, hb₁, hp₁, hq₁, rfl⟩
        rcases CodeTermAbsGraph.ite_iff.mp h₂ with ⟨b₂, p₂, q₂, hb₂, hp₂, hq₂, rfl⟩
        rw [ih b (by simp) _ _ hb₁ hb₂, ih p (by simp) _ _ hp₁ hp₂, ih q (by simp) _ _ hq₁ hq₂]
      · rcases CodeTermAbsGraph.search_iff.mp h₁ with ⟨p₁, q₁, hp₁, hq₁, rfl⟩
        rcases CodeTermAbsGraph.search_iff.mp h₂ with ⟨p₂, q₂, hp₂, hq₂, rfl⟩
        rw [ih p (by simp) _ _ hp₁ hp₂, ih q (by simp) _ _ hq₁ hq₂]
      · rcases CodeTermAbsGraph.tvote_iff.mp h₁ with ⟨v₁, p₁, q₁, hv₁, hp₁, hq₁, rfl⟩
        rcases CodeTermAbsGraph.tvote_iff.mp h₂ with ⟨v₂, p₂, q₂, hv₂, hp₂, hq₂, rfl⟩
        rw [ih v (by simp) _ _ hv₁ hv₂, ih p (by simp) _ _ hp₁ hp₂, ih q (by simp) _ _ hq₁ hq₂]
      · rcases CodeTermAbsGraph.sys_iff.mp h₁ with ⟨d₁, hd₁, rfl⟩
        rcases CodeTermAbsGraph.sys_iff.mp h₂ with ⟨d₂, hd₂, rfl⟩
        rw [ih d (by simp) _ _ hd₁ hd₂]
      · rw [CodeTermAbsGraph.selfIdx_iff] at h₁ h₂; rw [h₁, h₂]
      · rcases CodeTermAbsGraph.cons_iff.mp h₁ with ⟨e₁, r₁, he₁, hr₁, rfl⟩
        rcases CodeTermAbsGraph.cons_iff.mp h₂ with ⟨e₂, r₂, he₂, hr₂, rfl⟩
        rw [ih e (by simp) _ _ he₁ he₂, ih r (by simp) _ _ hr₁ hr₂]
    · rw [CodeTermAbsGraph.of_not_shape hx] at h₁ h₂; rw [h₁, h₂]

lemma codeTermAbsGraph_existsUnique (k₀ s x : V) : ∃! t, CodeTermAbsGraph k₀ s x t := by
  rcases codeTermAbsGraph_exists k₀ s x with ⟨t, ht⟩
  exact ExistsUnique.intro t ht (fun t' h' ↦ codeTermAbsGraph_unique k₀ s x t' t h' ht)

/-- **The abstracted structural term code**: `codeTerm x` with every `pSearch k₀ …` budget leaf written as the
term code `s` (the slot variable `^#6` in the closer, `binNumeral k₀` to recover `codeTerm`). -/
noncomputable def codeTermAbs (k₀ s x : V) : V := Classical.choose! (codeTermAbsGraph_existsUnique k₀ s x)

lemma codeTermAbs_graph (k₀ s x : V) : CodeTermAbsGraph k₀ s x (codeTermAbs k₀ s x) :=
  Classical.choose!_spec (codeTermAbsGraph_existsUnique k₀ s x)

lemma codeTermAbs_eq_of_graph {k₀ s x t : V} (h : CodeTermAbsGraph k₀ s x t) : codeTermAbs k₀ s x = t :=
  codeTermAbsGraph_unique k₀ s x _ _ (codeTermAbs_graph k₀ s x) h

noncomputable def codeTermAbsDef : 𝚺₁.Semisentence 4 := .mkSigma “t k0 sl x. !codeTermAbsGraphDef.sigma k0 sl x t”

instance codeTermAbs_defined : 𝚺₁-Function₃ (codeTermAbs : V → V → V → V) via codeTermAbsDef := .mk fun v ↦ by
  simp [codeTermAbsDef, HierarchySymbol.Semiformula.val_sigma, codeTermAbsGraph_defined.df]
  constructor
  · intro h; exact (codeTermAbs_eq_of_graph h).symm
  · intro h; rw [h]; exact codeTermAbs_graph _ _ _

instance codeTermAbs_definable : 𝚺₁-Function₃ (codeTermAbs : V → V → V → V) := codeTermAbs_defined.to_definable

instance codeTermAbs_definable' : Γ-[m + 1]-Function₃ (codeTermAbs : V → V → V → V) :=
  codeTermAbs_definable.of_sigmaOne

/-! ### The equations -/

@[simp] lemma codeTermAbs_const (k₀ s a : V) :
    codeTermAbs k₀ s (pConst a) = ppairTerm (binNumeral 0) (binNumeral a) ^+ (𝟏 : V) :=
  codeTermAbs_eq_of_graph (CodeTermAbsGraph.const_iff.mpr rfl)
@[simp] lemma codeTermAbs_self (k₀ s : V) :
    codeTermAbs k₀ s (pSelf : V) = ppairTerm (binNumeral 1) (binNumeral 0) ^+ (𝟏 : V) :=
  codeTermAbs_eq_of_graph (CodeTermAbsGraph.self_iff.mpr rfl)
@[simp] lemma codeTermAbs_opp (k₀ s : V) :
    codeTermAbs k₀ s (pOpp : V) = ppairTerm (binNumeral 2) (binNumeral 0) ^+ (𝟏 : V) :=
  codeTermAbs_eq_of_graph (CodeTermAbsGraph.opp_iff.mpr rfl)
@[simp] lemma codeTermAbs_bot (k₀ s p : V) :
    codeTermAbs k₀ s (pBot p) = ppairTerm (binNumeral 3) (codeTermAbs k₀ s p) ^+ (𝟏 : V) :=
  codeTermAbs_eq_of_graph (CodeTermAbsGraph.bot_iff.mpr ⟨_, codeTermAbs_graph k₀ s p, rfl⟩)
@[simp] lemma codeTermAbs_sim (k₀ s p q : V) :
    codeTermAbs k₀ s (pSim p q) = ppairTerm (binNumeral 4) (ppairTerm (codeTermAbs k₀ s p) (codeTermAbs k₀ s q)) ^+ (𝟏 : V) :=
  codeTermAbs_eq_of_graph (CodeTermAbsGraph.sim_iff.mpr ⟨_, _, codeTermAbs_graph k₀ s p, codeTermAbs_graph k₀ s q, rfl⟩)
@[simp] lemma codeTermAbs_ite (k₀ s b a p q : V) :
    codeTermAbs k₀ s (pIte b a p q) =
    ppairTerm (binNumeral 5) (ppairTerm (codeTermAbs k₀ s b) (ppairTerm (binNumeral a) (ppairTerm (codeTermAbs k₀ s p) (codeTermAbs k₀ s q)))) ^+ (𝟏 : V) :=
  codeTermAbs_eq_of_graph (CodeTermAbsGraph.ite_iff.mpr
    ⟨_, _, _, codeTermAbs_graph k₀ s b, codeTermAbs_graph k₀ s p, codeTermAbs_graph k₀ s q, rfl⟩)
/-- **The one changed clause**: the budget of a searcher is the leaf `budgetLeaf k₀ s k` — the slot at `k = k₀`. -/
@[simp] lemma codeTermAbs_search (k₀ s k g p q : V) :
    codeTermAbs k₀ s (pSearch k g p q) =
    ppairTerm (binNumeral 6) (ppairTerm (budgetLeaf k₀ s k) (ppairTerm (binNumeral g) (ppairTerm (codeTermAbs k₀ s p) (codeTermAbs k₀ s q)))) ^+ (𝟏 : V) :=
  codeTermAbs_eq_of_graph (CodeTermAbsGraph.search_iff.mpr ⟨_, _, codeTermAbs_graph k₀ s p, codeTermAbs_graph k₀ s q, rfl⟩)
@[simp] lemma codeTermAbs_tvote (k₀ s v θ p q : V) :
    codeTermAbs k₀ s (pTvote v θ p q) =
    ppairTerm (binNumeral 7) (ppairTerm (codeTermAbs k₀ s v) (ppairTerm (binNumeral θ) (ppairTerm (codeTermAbs k₀ s p) (codeTermAbs k₀ s q)))) ^+ (𝟏 : V) :=
  codeTermAbs_eq_of_graph (CodeTermAbsGraph.tvote_iff.mpr
    ⟨_, _, _, codeTermAbs_graph k₀ s v, codeTermAbs_graph k₀ s p, codeTermAbs_graph k₀ s q, rfl⟩)
/-- The description of a system: the member list abstracted member by member (through `codeTermAbs_cons`), the
index a binary numeral. -/
@[simp] lemma codeTermAbs_sys (k₀ s d i : V) :
    codeTermAbs k₀ s (pSys d i) = ppairTerm (binNumeral 8) (ppairTerm (codeTermAbs k₀ s d) (binNumeral i)) ^+ (𝟏 : V) :=
  codeTermAbs_eq_of_graph (CodeTermAbsGraph.sys_iff.mpr ⟨_, codeTermAbs_graph k₀ s d, rfl⟩)
@[simp] lemma codeTermAbs_selfIdx (k₀ s j : V) :
    codeTermAbs k₀ s (pSelfIdx j) = ppairTerm (binNumeral 9) (binNumeral j) ^+ (𝟏 : V) :=
  codeTermAbs_eq_of_graph (CodeTermAbsGraph.selfIdx_iff.mpr rfl)
@[simp] lemma codeTermAbs_cons (k₀ s e r : V) :
    codeTermAbs k₀ s (pCons e r) = ppairTerm (binNumeral 10) (ppairTerm (codeTermAbs k₀ s e) (codeTermAbs k₀ s r)) ^+ (𝟏 : V) :=
  codeTermAbs_eq_of_graph (CodeTermAbsGraph.cons_iff.mpr ⟨_, _, codeTermAbs_graph k₀ s e, codeTermAbs_graph k₀ s r, rfl⟩)
lemma codeTermAbs_of_not_shape {x : V} (hx : ¬IsShape x) (k₀ s : V) : codeTermAbs k₀ s x = binNumeral x :=
  codeTermAbs_eq_of_graph ((CodeTermAbsGraph.of_not_shape hx).mpr rfl)
@[simp] lemma codeTermAbs_nil (k₀ s : V) : codeTermAbs k₀ s (pNil : V) = binNumeral 0 :=
  codeTermAbs_of_not_shape not_isShape_zero k₀ s

/-! ### Facts -/

/-- `codeTermAbs k₀ s x` is an `ℒₒᵣ`-term code of arity `n` whenever the slot term `s` is. -/
lemma codeTermAbs_semiterm {n k₀ s : V} (hs : IsSemiterm ℒₒᵣ n s) (x : V) : IsSemiterm ℒₒᵣ n (codeTermAbs k₀ s x) := by
  induction x using ISigma1.pi1_order_induction with
  | hP => definability
  | ind x ih =>
    by_cases hx : IsShape x
    · rcases hx with ⟨a, rfl⟩ | rfl | rfl | ⟨p, rfl⟩ | ⟨p, q, rfl⟩ | ⟨b, a, p, q, rfl⟩ | ⟨k', g, p, q, rfl⟩ |
        ⟨v, θ, p, q, rfl⟩ | ⟨d, i, rfl⟩ | ⟨j, rfl⟩ | ⟨e, r, rfl⟩
      · rw [codeTermAbs_const]; exact succ_semiterm (ppairTerm_semiterm (binNumeral_semiterm n _) (binNumeral_semiterm n _))
      · rw [codeTermAbs_self]; exact succ_semiterm (ppairTerm_semiterm (binNumeral_semiterm n _) (binNumeral_semiterm n _))
      · rw [codeTermAbs_opp]; exact succ_semiterm (ppairTerm_semiterm (binNumeral_semiterm n _) (binNumeral_semiterm n _))
      · rw [codeTermAbs_bot]; exact succ_semiterm (ppairTerm_semiterm (binNumeral_semiterm n _) (ih p (by simp)))
      · rw [codeTermAbs_sim]
        exact succ_semiterm (ppairTerm_semiterm (binNumeral_semiterm n _)
          (ppairTerm_semiterm (ih p (by simp)) (ih q (by simp))))
      · rw [codeTermAbs_ite]
        exact succ_semiterm (ppairTerm_semiterm (binNumeral_semiterm n _) (ppairTerm_semiterm (ih b (by simp))
          (ppairTerm_semiterm (binNumeral_semiterm n _) (ppairTerm_semiterm (ih p (by simp)) (ih q (by simp))))))
      · rw [codeTermAbs_search]
        exact succ_semiterm (ppairTerm_semiterm (binNumeral_semiterm n _) (ppairTerm_semiterm (budgetLeaf_semiterm hs _)
          (ppairTerm_semiterm (binNumeral_semiterm n _) (ppairTerm_semiterm (ih p (by simp)) (ih q (by simp))))))
      · rw [codeTermAbs_tvote]
        exact succ_semiterm (ppairTerm_semiterm (binNumeral_semiterm n _) (ppairTerm_semiterm (ih v (by simp))
          (ppairTerm_semiterm (binNumeral_semiterm n _) (ppairTerm_semiterm (ih p (by simp)) (ih q (by simp))))))
      · rw [codeTermAbs_sys]
        exact succ_semiterm (ppairTerm_semiterm (binNumeral_semiterm n _) (ppairTerm_semiterm (ih d (by simp)) (binNumeral_semiterm n _)))
      · rw [codeTermAbs_selfIdx]; exact succ_semiterm (ppairTerm_semiterm (binNumeral_semiterm n _) (binNumeral_semiterm n _))
      · rw [codeTermAbs_cons]
        exact succ_semiterm (ppairTerm_semiterm (binNumeral_semiterm n _) (ppairTerm_semiterm (ih e (by simp)) (ih r (by simp))))
    · rw [codeTermAbs_of_not_shape hx]; exact binNumeral_semiterm n x

/-- **The slot filled with the node's budget recovers the verbatim description** (the code-level twin of
`subst_codeTermMetaAbs`). -/
theorem codeTermAbs_binNumeral (k₀ x : V) : codeTermAbs k₀ (binNumeral k₀) x = codeTerm x := by
  induction x using ISigma1.pi1_order_induction with
  | hP => definability
  | ind x ih =>
    by_cases hx : IsShape x
    · rcases hx with ⟨a, rfl⟩ | rfl | rfl | ⟨p, rfl⟩ | ⟨p, q, rfl⟩ | ⟨b, a, p, q, rfl⟩ | ⟨k', g, p, q, rfl⟩ |
        ⟨v, θ, p, q, rfl⟩ | ⟨d, i, rfl⟩ | ⟨j, rfl⟩ | ⟨e, r, rfl⟩
      · rw [codeTermAbs_const, codeTerm_const]
      · rw [codeTermAbs_self, codeTerm_self]
      · rw [codeTermAbs_opp, codeTerm_opp]
      · rw [codeTermAbs_bot, codeTerm_bot, ih p (by simp)]
      · rw [codeTermAbs_sim, codeTerm_sim, ih p (by simp), ih q (by simp)]
      · rw [codeTermAbs_ite, codeTerm_ite, ih b (by simp), ih p (by simp), ih q (by simp)]
      · rw [codeTermAbs_search, codeTerm_search, budgetLeaf_binNumeral, ih p (by simp), ih q (by simp)]
      · rw [codeTermAbs_tvote, codeTerm_tvote, ih v (by simp), ih p (by simp), ih q (by simp)]
      · rw [codeTermAbs_sys, codeTerm_sys, ih d (by simp)]
      · rw [codeTermAbs_selfIdx, codeTerm_selfIdx]
      · rw [codeTermAbs_cons, codeTerm_cons, ih e (by simp), ih r (by simp)]
    · rw [codeTermAbs_of_not_shape hx, codeTerm_of_not_shape hx]

end ArithS
