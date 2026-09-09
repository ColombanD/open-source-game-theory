import ArithS.SequentLength

/-!
# ArithS.DerivationLength — symbol count of a derivation code

`dlen d = Σ_{nodes} (1 + setLen (sequent at the node)) + Σ_{exsIntro nodes} termLen (witness)`:
the length of the derivation written out as its list of sequents, plus the witness terms of
∃-introductions (charged so that the measure is PROPER — with `p` free of `#0` the witness
would otherwise be unconstrained). Defined as the graph `Graph d n` of a `Fixpoint` on pairs
`⟪d, n⟫`, exactly as Foundation defines term-recursive functions
(`Language.TermRec.Construction`, `Bootstrapping/Syntax/Term/Basic.lean`): a monotone,
finite operator; existence and uniqueness of `n` for every internal derivation by
`Derivation.induction1`; `dlen` via `Classical.choose!`.

The graph is defined on ALL codes of the right shape (no derivation-validity check inside
`Phi`) — validity is `Derivation T d`, and the two are combined only in `Bew`.
-/

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {L : Language} [L.Encodable] [L.LORDefinable]

namespace DLen

variable (L)

/-- The length operator on pairs `⟪d, n⟫`. -/
def Phi (C : Set V) (pr : V) : Prop :=
  (∃ s p, pr = ⟪axL s p, setLen L s + 1⟫) ∨
  (∃ s, pr = ⟪verumIntro s, setLen L s + 1⟫) ∨
  (∃ s p q dp dq np nq, ⟪dp, np⟫ ∈ C ∧ ⟪dq, nq⟫ ∈ C ∧
    pr = ⟪andIntro s p q dp dq, setLen L s + np + nq + 1⟫) ∨
  (∃ s p q d n', ⟪d, n'⟫ ∈ C ∧ pr = ⟪orIntro s p q d, setLen L s + n' + 1⟫) ∨
  (∃ s p d n', ⟪d, n'⟫ ∈ C ∧ pr = ⟪allIntro s p d, setLen L s + n' + 1⟫) ∨
  (∃ s p t d n', ⟪d, n'⟫ ∈ C ∧ pr = ⟪exsIntro s p t d, setLen L s + termLen L t + n' + 1⟫) ∨
  (∃ s d n', ⟪d, n'⟫ ∈ C ∧ pr = ⟪wkRule s d, setLen L s + n' + 1⟫) ∨
  (∃ s d n', ⟪d, n'⟫ ∈ C ∧ pr = ⟪shiftRule s d, setLen L s + n' + 1⟫) ∨
  (∃ s p d₁ d₂ n₁ n₂, ⟪d₁, n₁⟫ ∈ C ∧ ⟪d₂, n₂⟫ ∈ C ∧
    pr = ⟪cutRule s p d₁ d₂, setLen L s + n₁ + n₂ + 1⟫) ∨
  (∃ s p, pr = ⟪axm s p, setLen L s + 1⟫)

noncomputable def blueprint : Fixpoint.Blueprint 0 := ⟨.mkDelta
  (.mkSigma “pr C.
    ∃ d <⁺ pr, ∃ n <⁺ pr, !pairDef pr d n ∧
    ( (∃ s < d, ∃ p < d, !axLGraph d s p ∧ ∃ l, !(setLenDef L) l s ∧ n = l + 1) ∨
      (∃ s < d, !verumIntroGraph d s ∧ ∃ l, !(setLenDef L) l s ∧ n = l + 1) ∨
      (∃ s < d, ∃ p < d, ∃ q < d, ∃ dp < d, ∃ dq < d, !andIntroGraph d s p q dp dq ∧
        ∃ np <⁺ n, ∃ nq <⁺ n, :⟪dp, np⟫:∈ C ∧ :⟪dq, nq⟫:∈ C ∧
        ∃ l, !(setLenDef L) l s ∧ n = l + np + nq + 1) ∨
      (∃ s < d, ∃ p < d, ∃ q < d, ∃ d' < d, !orIntroGraph d s p q d' ∧
        ∃ n' <⁺ n, :⟪d', n'⟫:∈ C ∧ ∃ l, !(setLenDef L) l s ∧ n = l + n' + 1) ∨
      (∃ s < d, ∃ p < d, ∃ d' < d, !allIntroGraph d s p d' ∧
        ∃ n' <⁺ n, :⟪d', n'⟫:∈ C ∧ ∃ l, !(setLenDef L) l s ∧ n = l + n' + 1) ∨
      (∃ s < d, ∃ p < d, ∃ t < d, ∃ d' < d, !exsIntroGraph d s p t d' ∧
        ∃ n' <⁺ n, :⟪d', n'⟫:∈ C ∧ ∃ l, !(setLenDef L) l s ∧ ∃ lt, !(termLenGraph L) lt t ∧
        n = l + lt + n' + 1) ∨
      (∃ s < d, ∃ d' < d, !wkRuleGraph d s d' ∧
        ∃ n' <⁺ n, :⟪d', n'⟫:∈ C ∧ ∃ l, !(setLenDef L) l s ∧ n = l + n' + 1) ∨
      (∃ s < d, ∃ d' < d, !shiftRuleGraph d s d' ∧
        ∃ n' <⁺ n, :⟪d', n'⟫:∈ C ∧ ∃ l, !(setLenDef L) l s ∧ n = l + n' + 1) ∨
      (∃ s < d, ∃ p < d, ∃ d₁ < d, ∃ d₂ < d, !cutRuleGraph d s p d₁ d₂ ∧
        ∃ n₁ <⁺ n, ∃ n₂ <⁺ n, :⟪d₁, n₁⟫:∈ C ∧ :⟪d₂, n₂⟫:∈ C ∧
        ∃ l, !(setLenDef L) l s ∧ n = l + n₁ + n₂ + 1) ∨
      (∃ s < d, ∃ p < d, !axmGraph d s p ∧ ∃ l, !(setLenDef L) l s ∧ n = l + 1) )”)
  (.mkPi “pr C.
    ∃ d <⁺ pr, ∃ n <⁺ pr, !pairDef pr d n ∧
    ( (∃ s < d, ∃ p < d, !axLGraph d s p ∧ ∀ l, !(setLenDef L) l s → n = l + 1) ∨
      (∃ s < d, !verumIntroGraph d s ∧ ∀ l, !(setLenDef L) l s → n = l + 1) ∨
      (∃ s < d, ∃ p < d, ∃ q < d, ∃ dp < d, ∃ dq < d, !andIntroGraph d s p q dp dq ∧
        ∃ np <⁺ n, ∃ nq <⁺ n, :⟪dp, np⟫:∈ C ∧ :⟪dq, nq⟫:∈ C ∧
        ∀ l, !(setLenDef L) l s → n = l + np + nq + 1) ∨
      (∃ s < d, ∃ p < d, ∃ q < d, ∃ d' < d, !orIntroGraph d s p q d' ∧
        ∃ n' <⁺ n, :⟪d', n'⟫:∈ C ∧ ∀ l, !(setLenDef L) l s → n = l + n' + 1) ∨
      (∃ s < d, ∃ p < d, ∃ d' < d, !allIntroGraph d s p d' ∧
        ∃ n' <⁺ n, :⟪d', n'⟫:∈ C ∧ ∀ l, !(setLenDef L) l s → n = l + n' + 1) ∨
      (∃ s < d, ∃ p < d, ∃ t < d, ∃ d' < d, !exsIntroGraph d s p t d' ∧
        ∃ n' <⁺ n, :⟪d', n'⟫:∈ C ∧ ∀ l, !(setLenDef L) l s →
        ∀ lt, !(termLenGraph L) lt t → n = l + lt + n' + 1) ∨
      (∃ s < d, ∃ d' < d, !wkRuleGraph d s d' ∧
        ∃ n' <⁺ n, :⟪d', n'⟫:∈ C ∧ ∀ l, !(setLenDef L) l s → n = l + n' + 1) ∨
      (∃ s < d, ∃ d' < d, !shiftRuleGraph d s d' ∧
        ∃ n' <⁺ n, :⟪d', n'⟫:∈ C ∧ ∀ l, !(setLenDef L) l s → n = l + n' + 1) ∨
      (∃ s < d, ∃ p < d, ∃ d₁ < d, ∃ d₂ < d, !cutRuleGraph d s p d₁ d₂ ∧
        ∃ n₁ <⁺ n, ∃ n₂ <⁺ n, :⟪d₁, n₁⟫:∈ C ∧ :⟪d₂, n₂⟫:∈ C ∧
        ∀ l, !(setLenDef L) l s → n = l + n₁ + n₂ + 1) ∨
      (∃ s < d, ∃ p < d, !axmGraph d s p ∧ ∀ l, !(setLenDef L) l s → n = l + 1) )”)⟩

variable {L}

private lemma le_sum₀ (a b : V) : b ≤ a + b + 1 := le_trans le_add_self le_self_add
private lemma le_sum₁ (a b c : V) : b ≤ a + b + c + 1 :=
  le_trans le_add_self (le_trans le_self_add le_self_add)
private lemma le_sum₂ (a b c : V) : c ≤ a + b + c + 1 := le_trans le_add_self le_self_add

/-- `Phi` with the bounds the blueprint carries, in the shape the `defined` proof needs. -/
private lemma phi_iff (C pr : V) :
    Phi L {x | x ∈ C} pr ↔
    ∃ d ≤ pr, ∃ n ≤ pr, pr = ⟪d, n⟫ ∧
    ( (∃ s < d, ∃ p < d, d = axL s p ∧ n = setLen L s + 1) ∨
      (∃ s < d, d = verumIntro s ∧ n = setLen L s + 1) ∨
      (∃ s < d, ∃ p < d, ∃ q < d, ∃ dp < d, ∃ dq < d, d = andIntro s p q dp dq ∧
        ∃ np ≤ n, ∃ nq ≤ n, ⟪dp, np⟫ ∈ C ∧ ⟪dq, nq⟫ ∈ C ∧ n = setLen L s + np + nq + 1) ∨
      (∃ s < d, ∃ p < d, ∃ q < d, ∃ d' < d, d = orIntro s p q d' ∧
        ∃ n' ≤ n, ⟪d', n'⟫ ∈ C ∧ n = setLen L s + n' + 1) ∨
      (∃ s < d, ∃ p < d, ∃ d' < d, d = allIntro s p d' ∧
        ∃ n' ≤ n, ⟪d', n'⟫ ∈ C ∧ n = setLen L s + n' + 1) ∨
      (∃ s < d, ∃ p < d, ∃ t < d, ∃ d' < d, d = exsIntro s p t d' ∧
        ∃ n' ≤ n, ⟪d', n'⟫ ∈ C ∧ n = setLen L s + termLen L t + n' + 1) ∨
      (∃ s < d, ∃ d' < d, d = wkRule s d' ∧
        ∃ n' ≤ n, ⟪d', n'⟫ ∈ C ∧ n = setLen L s + n' + 1) ∨
      (∃ s < d, ∃ d' < d, d = shiftRule s d' ∧
        ∃ n' ≤ n, ⟪d', n'⟫ ∈ C ∧ n = setLen L s + n' + 1) ∨
      (∃ s < d, ∃ p < d, ∃ d₁ < d, ∃ d₂ < d, d = cutRule s p d₁ d₂ ∧
        ∃ n₁ ≤ n, ∃ n₂ ≤ n, ⟪d₁, n₁⟫ ∈ C ∧ ⟪d₂, n₂⟫ ∈ C ∧ n = setLen L s + n₁ + n₂ + 1) ∨
      (∃ s < d, ∃ p < d, d = axm s p ∧ n = setLen L s + 1) ) := by
  constructor
  · rintro (⟨s, p, rfl⟩ | ⟨s, rfl⟩ | ⟨s, p, q, dp, dq, np, nq, hp, hq, rfl⟩ |
      ⟨s, p, q, d', n', h, rfl⟩ | ⟨s, p, d', n', h, rfl⟩ | ⟨s, p, t, d', n', h, rfl⟩ |
      ⟨s, d', n', h, rfl⟩ | ⟨s, d', n', h, rfl⟩ | ⟨s, p, d₁, d₂, n₁, n₂, h₁, h₂, rfl⟩ | ⟨s, p, rfl⟩)
    · exact ⟨_, by simp, _, by simp, rfl, Or.inl ⟨s, by simp, p, by simp, rfl, rfl⟩⟩
    · exact ⟨_, by simp, _, by simp, rfl, Or.inr <| Or.inl ⟨s, by simp, rfl, rfl⟩⟩
    · exact ⟨_, by simp, _, by simp, rfl, Or.inr <| Or.inr <| Or.inl
        ⟨s, by simp, p, by simp, q, by simp, dp, by simp, dq, by simp, rfl,
          np, le_sum₁ _ _ _, nq, le_sum₂ _ _ _, hp, hq, rfl⟩⟩
    · exact ⟨_, by simp, _, by simp, rfl, Or.inr <| Or.inr <| Or.inr <| Or.inl
        ⟨s, by simp, p, by simp, q, by simp, d', by simp, rfl, n', le_sum₀ _ _, h, rfl⟩⟩
    · exact ⟨_, by simp, _, by simp, rfl, Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
        ⟨s, by simp, p, by simp, d', by simp, rfl, n', le_sum₀ _ _, h, rfl⟩⟩
    · exact ⟨_, by simp, _, by simp, rfl, Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
        ⟨s, by simp, p, by simp, t, by simp, d', by simp, rfl, n', le_sum₀ _ _, h, rfl⟩⟩
    · exact ⟨_, by simp, _, by simp, rfl, Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
        ⟨s, by simp, d', by simp, rfl, n', le_sum₀ _ _, h, rfl⟩⟩
    · exact ⟨_, by simp, _, by simp, rfl, Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
        ⟨s, by simp, d', by simp, rfl, n', le_sum₀ _ _, h, rfl⟩⟩
    · exact ⟨_, by simp, _, by simp, rfl, Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
        ⟨s, by simp, p, by simp, d₁, by simp, d₂, by simp, rfl, n₁, le_sum₁ _ _ _, n₂, le_sum₂ _ _ _, h₁, h₂, rfl⟩⟩
    · exact ⟨_, by simp, _, by simp, rfl, Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr
        ⟨s, by simp, p, by simp, rfl, rfl⟩⟩
  · rintro ⟨d, _, n, _, rfl, (⟨s, _, p, _, rfl, rfl⟩ | ⟨s, _, rfl, rfl⟩ |
      ⟨s, _, p, _, q, _, dp, _, dq, _, rfl, np, _, nq, _, hp, hq, rfl⟩ |
      ⟨s, _, p, _, q, _, d', _, rfl, n', _, h, rfl⟩ | ⟨s, _, p, _, d', _, rfl, n', _, h, rfl⟩ |
      ⟨s, _, p, _, t, _, d', _, rfl, n', _, h, rfl⟩ | ⟨s, _, d', _, rfl, n', _, h, rfl⟩ |
      ⟨s, _, d', _, rfl, n', _, h, rfl⟩ |
      ⟨s, _, p, _, d₁, _, d₂, _, rfl, n₁, _, n₂, _, h₁, h₂, rfl⟩ | ⟨s, _, p, _, rfl, rfl⟩)⟩
    · exact Or.inl ⟨s, p, rfl⟩
    · exact Or.inr <| Or.inl ⟨s, rfl⟩
    · exact Or.inr <| Or.inr <| Or.inl ⟨s, p, q, dp, dq, np, nq, hp, hq, rfl⟩
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨s, p, q, d', n', h, rfl⟩
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨s, p, d', n', h, rfl⟩
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨s, p, t, d', n', h, rfl⟩
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨s, d', n', h, rfl⟩
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨s, d', n', h, rfl⟩
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
        ⟨s, p, d₁, d₂, n₁, n₂, h₁, h₂, rfl⟩
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr ⟨s, p, rfl⟩

variable (L)

noncomputable def construction : Fixpoint.Construction V (blueprint L) where
  Φ := fun _ ↦ Phi L
  defined := .mk <| by
    constructor
    · intro v
      simp [blueprint, setLen_defined.iff, termLen.defined.iff]
    · intro v
      symm
      simpa [blueprint, setLen_defined.iff, termLen.defined.iff] using phi_iff _ _
  monotone := by
    rintro C C' hC _ pr (⟨s, p, rfl⟩ | ⟨s, rfl⟩ | ⟨s, p, q, dp, dq, np, nq, hp, hq, rfl⟩ |
      ⟨s, p, q, d', n', h, rfl⟩ | ⟨s, p, d', n', h, rfl⟩ | ⟨s, p, t, d', n', h, rfl⟩ |
      ⟨s, d', n', h, rfl⟩ | ⟨s, d', n', h, rfl⟩ | ⟨s, p, d₁, d₂, n₁, n₂, h₁, h₂, rfl⟩ | ⟨s, p, rfl⟩)
    · exact Or.inl ⟨s, p, rfl⟩
    · exact Or.inr <| Or.inl ⟨s, rfl⟩
    · exact Or.inr <| Or.inr <| Or.inl ⟨s, p, q, dp, dq, np, nq, hC hp, hC hq, rfl⟩
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨s, p, q, d', n', hC h, rfl⟩
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨s, p, d', n', hC h, rfl⟩
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨s, p, t, d', n', hC h, rfl⟩
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨s, d', n', hC h, rfl⟩
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨s, d', n', hC h, rfl⟩
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
        ⟨s, p, d₁, d₂, n₁, n₂, hC h₁, hC h₂, rfl⟩
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr ⟨s, p, rfl⟩

/-- Every referenced pair `⟪d', n'⟫` is below `⟪d, n⟫`: `d' < d` and `n' ≤ n`. -/
instance : (construction L).StrongFinite V where
  strong_finite := by
    rintro C _ pr (⟨s, p, rfl⟩ | ⟨s, rfl⟩ | ⟨s, p, q, dp, dq, np, nq, hp, hq, rfl⟩ |
      ⟨s, p, q, d', n', h, rfl⟩ | ⟨s, p, d', n', h, rfl⟩ | ⟨s, p, t, d', n', h, rfl⟩ |
      ⟨s, d', n', h, rfl⟩ | ⟨s, d', n', h, rfl⟩ | ⟨s, p, d₁, d₂, n₁, n₂, h₁, h₂, rfl⟩ | ⟨s, p, rfl⟩)
    · exact Or.inl ⟨s, p, rfl⟩
    · exact Or.inr <| Or.inl ⟨s, rfl⟩
    · exact Or.inr <| Or.inr <| Or.inl ⟨s, p, q, dp, dq, np, nq,
        ⟨hp, lt_of_lt_of_le (pair_lt_pair_left (by simp) _) (pair_le_pair_right _ (le_sum₁ _ _ _))⟩,
        ⟨hq, lt_of_lt_of_le (pair_lt_pair_left (by simp) _) (pair_le_pair_right _ (le_sum₂ _ _ _))⟩, rfl⟩
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨s, p, q, d', n',
        ⟨h, lt_of_lt_of_le (pair_lt_pair_left (by simp) _) (pair_le_pair_right _ (le_sum₀ _ _))⟩, rfl⟩
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨s, p, d', n',
        ⟨h, lt_of_lt_of_le (pair_lt_pair_left (by simp) _) (pair_le_pair_right _ (le_sum₀ _ _))⟩, rfl⟩
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨s, p, t, d', n',
        ⟨h, lt_of_lt_of_le (pair_lt_pair_left (by simp) _) (pair_le_pair_right _ (le_sum₀ _ _))⟩, rfl⟩
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨s, d', n',
        ⟨h, lt_of_lt_of_le (pair_lt_pair_left (by simp) _) (pair_le_pair_right _ (le_sum₀ _ _))⟩, rfl⟩
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨s, d', n',
        ⟨h, lt_of_lt_of_le (pair_lt_pair_left (by simp) _) (pair_le_pair_right _ (le_sum₀ _ _))⟩, rfl⟩
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
        ⟨s, p, d₁, d₂, n₁, n₂, ⟨h₁, lt_of_lt_of_le (pair_lt_pair_left (by simp) _) (pair_le_pair_right _ (le_sum₁ _ _ _))⟩,
          ⟨h₂, lt_of_lt_of_le (pair_lt_pair_left (by simp) _) (pair_le_pair_right _ (le_sum₂ _ _ _))⟩, rfl⟩
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr ⟨s, p, rfl⟩

end DLen

variable (L)

/-- `DlenGraph d n`: the derivation code `d` has length `n`. -/
def DlenGraph (d n : V) : Prop := (DLen.construction L).Fixpoint ![] ⟪d, n⟫

noncomputable def dlenGraphDef : 𝚫₁.Semisentence 2 := .mkDelta
  (.mkSigma “d n. ∃ pr <⁺ (d + n + 1)², !pairDef pr d n ∧ !(DLen.blueprint L).fixpointDefΔ₁.sigma pr”)
  (.mkPi “d n. ∀ pr <⁺ (d + n + 1)², !pairDef pr d n → !(DLen.blueprint L).fixpointDefΔ₁.pi pr”)

variable {L}

section

private lemma fixpoint_param_eq (p : Fin 0 → V) (x : V) :
    (DLen.construction L).Fixpoint p x = (DLen.construction L).Fixpoint ![] x := by
  rw [Subsingleton.elim p ![]]

instance dlenGraph_defined : 𝚫₁-Relation[V] DlenGraph L via dlenGraphDef L := .mk
  ⟨by intro v
      simp [dlenGraphDef, HierarchySymbol.Semiformula.val_sigma,
        (DLen.construction L).fixpoint_definedΔ₁.proper.iff', (DLen.construction L).fixpoint_definedΔ₁.df]
      constructor
      · rintro h x _ rfl; rwa [fixpoint_param_eq] at h ⊢
      · intro h; have := h ⟪v 0, v 1⟫ (by simp) rfl; rwa [fixpoint_param_eq] at this ⊢,
   by intro v
      simp [dlenGraphDef, HierarchySymbol.Semiformula.val_sigma,
        (DLen.construction L).fixpoint_definedΔ₁.df, DlenGraph]
      rw [fixpoint_param_eq]⟩

instance dlenGraph_definable : 𝚫₁-Relation[V] DlenGraph L := dlenGraph_defined.to_definable

instance dlenGraph_definable' : Γ-[m + 1]-Relation[V] DlenGraph L := dlenGraph_definable.of_deltaOne

end

/-! ### Case analysis and inversion -/

lemma DlenGraph.case_iff {d n : V} :
    DlenGraph L d n ↔
    (∃ s p, d = axL s p ∧ n = setLen L s + 1) ∨
    (∃ s, d = verumIntro s ∧ n = setLen L s + 1) ∨
    (∃ s p q dp dq np nq, DlenGraph L dp np ∧ DlenGraph L dq nq ∧
      d = andIntro s p q dp dq ∧ n = setLen L s + np + nq + 1) ∨
    (∃ s p q d' n', DlenGraph L d' n' ∧ d = orIntro s p q d' ∧ n = setLen L s + n' + 1) ∨
    (∃ s p d' n', DlenGraph L d' n' ∧ d = allIntro s p d' ∧ n = setLen L s + n' + 1) ∨
    (∃ s p t d' n', DlenGraph L d' n' ∧ d = exsIntro s p t d' ∧
      n = setLen L s + termLen L t + n' + 1) ∨
    (∃ s d' n', DlenGraph L d' n' ∧ d = wkRule s d' ∧ n = setLen L s + n' + 1) ∨
    (∃ s d' n', DlenGraph L d' n' ∧ d = shiftRule s d' ∧ n = setLen L s + n' + 1) ∨
    (∃ s p d₁ d₂ n₁ n₂, DlenGraph L d₁ n₁ ∧ DlenGraph L d₂ n₂ ∧
      d = cutRule s p d₁ d₂ ∧ n = setLen L s + n₁ + n₂ + 1) ∨
    (∃ s p, d = axm s p ∧ n = setLen L s + 1) :=
  Iff.trans (DLen.construction L).case (by simp [DLen.construction, DLen.Phi, DlenGraph])

section inversion

attribute [local simp] axL verumIntro andIntro orIntro allIntro exsIntro wkRule shiftRule cutRule axm

lemma DlenGraph.axL_iff {s p n : V} : DlenGraph L (axL s p) n ↔ n = setLen L s + 1 := by
  rw [DlenGraph.case_iff]; simp

lemma DlenGraph.verumIntro_iff {s n : V} : DlenGraph L (verumIntro s) n ↔ n = setLen L s + 1 := by
  rw [DlenGraph.case_iff]; simp

lemma DlenGraph.axm_iff {s p n : V} : DlenGraph L (axm s p) n ↔ n = setLen L s + 1 := by
  rw [DlenGraph.case_iff]; simp

lemma DlenGraph.andIntro_iff {s p q dp dq n : V} :
    DlenGraph L (andIntro s p q dp dq) n ↔
    ∃ np nq, DlenGraph L dp np ∧ DlenGraph L dq nq ∧ n = setLen L s + np + nq + 1 := by
  rw [DlenGraph.case_iff]; simp

lemma DlenGraph.orIntro_iff {s p q d' n : V} :
    DlenGraph L (orIntro s p q d') n ↔ ∃ n', DlenGraph L d' n' ∧ n = setLen L s + n' + 1 := by
  rw [DlenGraph.case_iff]; simp

lemma DlenGraph.allIntro_iff {s p d' n : V} :
    DlenGraph L (allIntro s p d') n ↔ ∃ n', DlenGraph L d' n' ∧ n = setLen L s + n' + 1 := by
  rw [DlenGraph.case_iff]; simp

lemma DlenGraph.exsIntro_iff {s p t d' n : V} :
    DlenGraph L (exsIntro s p t d') n ↔
    ∃ n', DlenGraph L d' n' ∧ n = setLen L s + termLen L t + n' + 1 := by
  rw [DlenGraph.case_iff]; simp

lemma DlenGraph.wkRule_iff {s d' n : V} :
    DlenGraph L (wkRule s d') n ↔ ∃ n', DlenGraph L d' n' ∧ n = setLen L s + n' + 1 := by
  rw [DlenGraph.case_iff]; simp

lemma DlenGraph.shiftRule_iff {s d' n : V} :
    DlenGraph L (shiftRule s d') n ↔ ∃ n', DlenGraph L d' n' ∧ n = setLen L s + n' + 1 := by
  rw [DlenGraph.case_iff]; simp

lemma DlenGraph.cutRule_iff {s p d₁ d₂ n : V} :
    DlenGraph L (cutRule s p d₁ d₂) n ↔
    ∃ n₁ n₂, DlenGraph L d₁ n₁ ∧ DlenGraph L d₂ n₂ ∧ n = setLen L s + n₁ + n₂ + 1 := by
  rw [DlenGraph.case_iff]; simp

end inversion

/-! ### Existence and uniqueness on internal derivations -/

section

variable {T : Theory L} [T.Δ₁]

lemma dlenGraph_exists {d : V} (hd : Derivation T d) : ∃ n, DlenGraph L d n := by
  apply Derivation.induction1 𝚺 (T := T) (P := fun d ↦ ∃ n, DlenGraph L d n) (by definability) hd
  · intro s _ p _ _; exact ⟨_, DlenGraph.axL_iff.mpr rfl⟩
  · intro s _ _; exact ⟨_, DlenGraph.verumIntro_iff.mpr rfl⟩
  · rintro s _ p q dp dq _ _ _ ⟨np, hp⟩ ⟨nq, hq⟩
    exact ⟨_, DlenGraph.andIntro_iff.mpr ⟨np, nq, hp, hq, rfl⟩⟩
  · rintro s _ p q d' _ _ ⟨n', h⟩; exact ⟨_, DlenGraph.orIntro_iff.mpr ⟨n', h, rfl⟩⟩
  · rintro s _ p d' _ _ ⟨n', h⟩; exact ⟨_, DlenGraph.allIntro_iff.mpr ⟨n', h, rfl⟩⟩
  · rintro s _ p t d' _ _ _ ⟨n', h⟩; exact ⟨_, DlenGraph.exsIntro_iff.mpr ⟨n', h, rfl⟩⟩
  · rintro s _ d' _ _ ⟨n', h⟩; exact ⟨_, DlenGraph.wkRule_iff.mpr ⟨n', h, rfl⟩⟩
  · rintro s _ d' _ _ ⟨n', h⟩; exact ⟨_, DlenGraph.shiftRule_iff.mpr ⟨n', h, rfl⟩⟩
  · rintro s _ p d₁ d₂ _ _ ⟨n₁, h₁⟩ ⟨n₂, h₂⟩
    exact ⟨_, DlenGraph.cutRule_iff.mpr ⟨n₁, n₂, h₁, h₂, rfl⟩⟩
  · intro s _ p _ _; exact ⟨_, DlenGraph.axm_iff.mpr rfl⟩

lemma dlenGraph_unique {d : V} (hd : Derivation T d) :
    ∀ n₁ n₂, DlenGraph L d n₁ → DlenGraph L d n₂ → n₁ = n₂ := by
  apply Derivation.induction1 𝚷 (T := T)
    (P := fun d ↦ ∀ n₁ n₂, DlenGraph L d n₁ → DlenGraph L d n₂ → n₁ = n₂) (by definability) hd
  · intro s _ p _ _ n₁ n₂ h₁ h₂
    rw [DlenGraph.axL_iff] at h₁ h₂; rw [h₁, h₂]
  · intro s _ _ n₁ n₂ h₁ h₂
    rw [DlenGraph.verumIntro_iff] at h₁ h₂; rw [h₁, h₂]
  · intro s _ p q dp dq _ _ _ ihp ihq n₁ n₂ h₁ h₂
    rcases DlenGraph.andIntro_iff.mp h₁ with ⟨np, nq, hp, hq, rfl⟩
    rcases DlenGraph.andIntro_iff.mp h₂ with ⟨np', nq', hp', hq', rfl⟩
    rw [ihp np np' hp hp', ihq nq nq' hq hq']
  · intro s _ p q d' _ _ ih n₁ n₂ h₁ h₂
    rcases DlenGraph.orIntro_iff.mp h₁ with ⟨n', h, rfl⟩
    rcases DlenGraph.orIntro_iff.mp h₂ with ⟨n'', h', rfl⟩
    rw [ih n' n'' h h']
  · intro s _ p d' _ _ ih n₁ n₂ h₁ h₂
    rcases DlenGraph.allIntro_iff.mp h₁ with ⟨n', h, rfl⟩
    rcases DlenGraph.allIntro_iff.mp h₂ with ⟨n'', h', rfl⟩
    rw [ih n' n'' h h']
  · intro s _ p t d' _ _ _ ih n₁ n₂ h₁ h₂
    rcases DlenGraph.exsIntro_iff.mp h₁ with ⟨n', h, rfl⟩
    rcases DlenGraph.exsIntro_iff.mp h₂ with ⟨n'', h', rfl⟩
    rw [ih n' n'' h h']
  · intro s _ d' _ _ ih n₁ n₂ h₁ h₂
    rcases DlenGraph.wkRule_iff.mp h₁ with ⟨n', h, rfl⟩
    rcases DlenGraph.wkRule_iff.mp h₂ with ⟨n'', h', rfl⟩
    rw [ih n' n'' h h']
  · intro s _ d' _ _ ih n₁ n₂ h₁ h₂
    rcases DlenGraph.shiftRule_iff.mp h₁ with ⟨n', h, rfl⟩
    rcases DlenGraph.shiftRule_iff.mp h₂ with ⟨n'', h', rfl⟩
    rw [ih n' n'' h h']
  · intro s _ p d₁ d₂ _ _ ih₁ ih₂ n₁ n₂ h₁ h₂
    rcases DlenGraph.cutRule_iff.mp h₁ with ⟨m₁, m₂, g₁, g₂, rfl⟩
    rcases DlenGraph.cutRule_iff.mp h₂ with ⟨m₁', m₂', g₁', g₂', rfl⟩
    rw [ih₁ m₁ m₁' g₁ g₁', ih₂ m₂ m₂' g₂ g₂']
  · intro s _ p _ _ n₁ n₂ h₁ h₂
    rw [DlenGraph.axm_iff] at h₁ h₂; rw [h₁, h₂]

lemma dlenGraph_existsUnique {d : V} (hd : Derivation T d) : ∃! n, DlenGraph L d n := by
  rcases dlenGraph_exists hd with ⟨n, hn⟩
  exact ExistsUnique.intro n hn (fun n' h' ↦ dlenGraph_unique hd n' n h' hn)

variable (T)

lemma dlenGraph_existsUnique_total (d : V) :
    ∃! n, (Derivation T d → DlenGraph L d n) ∧ (¬Derivation T d → n = 0) := by
  by_cases hd : Derivation T d
  · simpa [hd] using dlenGraph_existsUnique hd
  · simp [hd]

/-- The length of an internal derivation of `T` (`0` on non-derivations). -/
noncomputable def dlen (d : V) : V := Classical.choose! (dlenGraph_existsUnique_total (L := L) T d)

variable {T}

theorem dlen_graph {d : V} (hd : Derivation T d) : DlenGraph L d (dlen T d) :=
  Classical.choose!_spec (dlenGraph_existsUnique_total (L := L) T d) |>.1 hd

theorem dlen_of_not {d : V} (hd : ¬Derivation T d) : dlen T d = 0 :=
  Classical.choose!_spec (dlenGraph_existsUnique_total (L := L) T d) |>.2 hd

lemma dlen_eq_of_graph {d n : V} (hd : Derivation T d) (h : DlenGraph L d n) : dlen T d = n :=
  dlenGraph_unique hd _ _ (dlen_graph hd) h

variable (T)

noncomputable def dlenDef : 𝚺₁.Semisentence 2 := .mkSigma
  “n d. (!(derivation T).pi d → !(dlenGraphDef L).sigma d n) ∧ (¬!(derivation T).sigma d → n = 0)”

variable {T}

instance dlen_defined : 𝚺₁-Function₁[V] dlen (L := L) T via dlenDef T := .mk fun v ↦ by
  simp [dlenDef, HierarchySymbol.Semiformula.val_sigma, dlenGraph_defined.df,
    (Derivation.defined (T := T)).proper.iff', (Derivation.defined (T := T)).df,
    dlen, Classical.choose!_eq_iff_right]

instance dlen_definable : 𝚺₁-Function₁[V] dlen (L := L) T := dlen_defined.to_definable

instance dlen_definable' : Γ-[m + 1]-Function₁[V] dlen (L := L) T := dlen_definable.of_sigmaOne

end

end ArithS
