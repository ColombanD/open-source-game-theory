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

end ArithS
