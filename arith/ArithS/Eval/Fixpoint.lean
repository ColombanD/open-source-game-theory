import ArithS.Agents.SysClose

/-!
# ArithS.Eval.Fixpoint — the Foundation plumbing behind `EvalGraph`

**Skip on first reading.** The evaluator `EvalGraph` (`ArithS.Eval.Eval`) is the least fixpoint of the
operator `EvalFix.Phi` below — one disjunct per clause of the engine's `eval` — and this file is
everything Foundation needs to build that fixpoint: the operator, its Δ₁ blueprint (the same clauses
written as a formula of arithmetic), the proof that blueprint and operator agree (`phi_iff`),
monotonicity, and finiteness (each clause cites finitely many sub-tuples). Nothing here is a
definition a reader has to accept beyond `Phi`, whose ten disjuncts are restated as the
characterization `EvalGraph.case_iff` in `Eval.lean`.

The three tau clauses (2026-09-30, Phase 2 of `SPRIME_SOURCE_OF_TRUTH.md`) mirror `Dynamics.eval` literally:
`pTvote pNil θ p q` runs `p` iff `θ = 0`; `pTvote (pCons (ppair w I) rest) θ p q` runs `p` if `θ = 0`, else
the entry runs in ITS OWN frame `⟪n, pBot I, pBot I, I, r⟫` and the vote continues with `θ - w`
(truncated) if the entry played `0` (`C`), with `θ` otherwise; `pSys d i` looks up member `i`
(`listGet d i = m + 1`) and runs `sysCloseCode d m` in the same frame. `pSelfIdx` has no clause (a dangling
reference plays nothing — the engine's `none`), nor has a bare list cons.
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
    pr = ⟪n + 1, me, opp, pSearch k g p q, a⟫) ∨
  (∃ n me opp θ p q a,
    ((θ = 0 ∧ ⟪n, me, opp, p, a⟫ ∈ C) ∨ (θ ≠ 0 ∧ ⟪n, me, opp, q, a⟫ ∈ C)) ∧
    pr = ⟪n + 1, me, opp, pTvote pNil θ p q, a⟫) ∨
  (∃ n me opp w I rest θ p q a,
    ((θ = 0 ∧ ⟪n, me, opp, p, a⟫ ∈ C) ∨
     (θ ≠ 0 ∧ ∃ r, ⟪n, pBot I, pBot I, I, r⟫ ∈ C ∧
       ((r = 0 ∧ ⟪n, me, opp, pTvote rest (θ - w) p q, a⟫ ∈ C) ∨
        (r ≠ 0 ∧ ⟪n, me, opp, pTvote rest θ p q, a⟫ ∈ C)))) ∧
    pr = ⟪n + 1, me, opp, pTvote (pCons (ppair w I) rest) θ p q, a⟫) ∨
  (∃ n me opp d i m a, listGet d i = m + 1 ∧ ⟪n, me, opp, sysCloseCode d m, a⟫ ∈ C ∧
    pr = ⟪n + 1, me, opp, pSys d i, a⟫)

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
           (¬!(lenBox TAct).pi k gc ∧ ∃ t, !pair₅Def t n me opp q a ∧ t ∈ C))) ∨
      (∃ v < p, ∃ th < p, ∃ p' < p, ∃ q < p, !pTvoteGraph p v th p' q ∧ v = 0 ∧
        ((th = 0 ∧ ∃ t, !pair₅Def t n me opp p' a ∧ t ∈ C) ∨
         (th ≠ 0 ∧ ∃ t, !pair₅Def t n me opp q a ∧ t ∈ C))) ∨
      (∃ v < p, ∃ th < p, ∃ p' < p, ∃ q < p, !pTvoteGraph p v th p' q ∧
        ∃ e < v, ∃ rest < v, !pConsGraph v e rest ∧ ∃ w <⁺ e, ∃ I <⁺ e, !ppairDef e w I ∧
        ((th = 0 ∧ ∃ t, !pair₅Def t n me opp p' a ∧ t ∈ C) ∨
         (th ≠ 0 ∧ ∃ r < pr + C + 1,
           (∃ bI, !pBotGraph bI I ∧ ∃ t, !pair₅Def t n bI bI I r ∧ t ∈ C) ∧
           ((r = 0 ∧ ∃ th', !subDef th' th w ∧ ∃ tv, !pTvoteGraph tv rest th' p' q ∧
              ∃ t, !pair₅Def t n me opp tv a ∧ t ∈ C) ∨
            (r ≠ 0 ∧ ∃ tv, !pTvoteGraph tv rest th p' q ∧ ∃ t, !pair₅Def t n me opp tv a ∧ t ∈ C))))) ∨
      (∃ d < p, ∃ i < p, !pSysGraph p d i ∧ ∃ l, !listGetDef l d i ∧ ∃ m < l, l = m + 1 ∧
        ∃ c, !sysCloseCodeDef c d m ∧ ∃ t, !pair₅Def t n me opp c a ∧ t ∈ C) )”)
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
           (¬!(lenBox TAct).sigma k gc ∧ ∀ t, !pair₅Def t n me opp q a → t ∈ C))) ∨
      (∃ v < p, ∃ th < p, ∃ p' < p, ∃ q < p, !pTvoteGraph p v th p' q ∧ v = 0 ∧
        ((th = 0 ∧ ∀ t, !pair₅Def t n me opp p' a → t ∈ C) ∨
         (th ≠ 0 ∧ ∀ t, !pair₅Def t n me opp q a → t ∈ C))) ∨
      (∃ v < p, ∃ th < p, ∃ p' < p, ∃ q < p, !pTvoteGraph p v th p' q ∧
        ∃ e < v, ∃ rest < v, !pConsGraph v e rest ∧ ∃ w <⁺ e, ∃ I <⁺ e, !ppairDef e w I ∧
        ((th = 0 ∧ ∀ t, !pair₅Def t n me opp p' a → t ∈ C) ∨
         (th ≠ 0 ∧ ∃ r < pr + C + 1,
           (∀ bI, !pBotGraph bI I → ∀ t, !pair₅Def t n bI bI I r → t ∈ C) ∧
           ((r = 0 ∧ ∀ th', !subDef th' th w → ∀ tv, !pTvoteGraph tv rest th' p' q →
              ∀ t, !pair₅Def t n me opp tv a → t ∈ C) ∨
            (r ≠ 0 ∧ ∀ tv, !pTvoteGraph tv rest th p' q → ∀ t, !pair₅Def t n me opp tv a → t ∈ C))))) ∨
      (∃ d < p, ∃ i < p, !pSysGraph p d i ∧ ∀ l, !listGetDef l d i → ∃ m < l, l = m + 1 ∧
        ∀ c, !sysCloseCodeDef c d m → ∀ t, !pair₅Def t n me opp c a → t ∈ C) )”)⟩

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
         (¬LenBox TAct k (guardCodeB g me opp k) ∧ ⟪n, me, opp, q, a⟫ ∈ C))) ∨
      (∃ v < p, ∃ θ < p, ∃ p' < p, ∃ q < p, p = pTvote v θ p' q ∧ v = 0 ∧
        ((θ = 0 ∧ ⟪n, me, opp, p', a⟫ ∈ C) ∨ (θ ≠ 0 ∧ ⟪n, me, opp, q, a⟫ ∈ C))) ∨
      (∃ v < p, ∃ θ < p, ∃ p' < p, ∃ q < p, p = pTvote v θ p' q ∧
        ∃ e < v, ∃ rest < v, v = pCons e rest ∧ ∃ w ≤ e, ∃ I ≤ e, e = ppair w I ∧
        ((θ = 0 ∧ ⟪n, me, opp, p', a⟫ ∈ C) ∨
         (θ ≠ 0 ∧ ∃ r < pr + C + 1, ⟪n, pBot I, pBot I, I, r⟫ ∈ C ∧
           ((r = 0 ∧ ⟪n, me, opp, pTvote rest (θ - w) p' q, a⟫ ∈ C) ∨
            (r ≠ 0 ∧ ⟪n, me, opp, pTvote rest θ p' q, a⟫ ∈ C))))) ∨
      (∃ d < p, ∃ i < p, p = pSys d i ∧ ∃ m < listGet d i, listGet d i = m + 1 ∧
        ⟪n, me, opp, sysCloseCode d m, a⟫ ∈ C) ) := by
  constructor
  · rintro (⟨n, me, opp, a, rfl⟩ | ⟨n, me, opp, a, h, rfl⟩ | ⟨n, me, opp, a, h, rfl⟩ |
      ⟨n, me, opp, p, a, h, rfl⟩ | ⟨n, me, opp, p, q, a, h, rfl⟩ |
      ⟨n, me, opp, b, a', p, q, a, r, hb, hpq, rfl⟩ | ⟨n, me, opp, k, g, p, q, a, hpq, rfl⟩ |
      ⟨n, me, opp, θ, p, q, a, hpq, rfl⟩ | ⟨n, me, opp, w, I, rest, θ, p, q, a, hpq, rfl⟩ |
      ⟨n, me, opp, d, i, m, a, hm, h, rfl⟩)
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
      exact ⟨n, h₁, me, h₂, opp, h₃, _, h₄, a, h₅, rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨k, by simp, g, by simp, p, by simp, q, by simp, rfl, hpq⟩))))))⟩
    · obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := tuple_bounds n me opp (pTvote pNil θ p q) a
      exact ⟨n, h₁, me, h₂, opp, h₃, _, h₄, a, h₅, rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨pNil, by simp, θ, by simp, p, by simp, q, by simp, rfl, rfl, hpq⟩)))))))⟩
    · obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := tuple_bounds n me opp (pTvote (pCons (ppair w I) rest) θ p q) a
      refine ⟨n, h₁, me, h₂, opp, h₃, _, h₄, a, h₅, rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨_, by simp, θ, by simp, p, by simp, q, by simp, rfl, _, by simp, rest, by simp, rfl,
          w, by simp, I, by simp, rfl, ?_⟩))))))))⟩
      rcases hpq with ⟨h0, hp⟩ | ⟨h0, r, hI, hr⟩
      · exact Or.inl ⟨h0, hp⟩
      · exact Or.inr ⟨h0, r, lt_of_lt_of_le (lt_of_tuple_mem hI) (le_trans le_add_self le_self_add), hI, hr⟩
    · obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := tuple_bounds n me opp (pSys d i) a
      exact ⟨n, h₁, me, h₂, opp, h₃, _, h₄, a, h₅, rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨d, by simp, i, by simp, rfl, m, by rw [hm]; exact lt_add_one m, hm, h⟩))))))))⟩
  · rintro ⟨n, _, me, _, opp, _, p, _, a, _, rfl, (rfl | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨p', _, rfl, h⟩ |
      ⟨p', _, q, _, rfl, h⟩ | ⟨b, _, a', _, p', _, q, _, rfl, r, _, hb, hpq⟩ |
      ⟨k, _, g, _, p', _, q, _, rfl, hpq⟩ | ⟨v, _, θ, _, p', _, q, _, rfl, rfl, hpq⟩ |
      ⟨v, _, θ, _, p', _, q, _, rfl, e, _, rest, _, rfl, w, _, I, _, rfl, hpq⟩ |
      ⟨d, _, i, _, rfl, m, _, hm, h⟩)⟩
    · exact Or.inl ⟨n, me, opp, a, rfl⟩
    · exact Or.inr (Or.inl ⟨n, me, opp, a, h, rfl⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨n, me, opp, a, h, rfl⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨n, me, opp, p', a, h, rfl⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, me, opp, p', q, a, h, rfl⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, me, opp, b, a', p', q, a, r, hb, hpq, rfl⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, me, opp, k, g, p', q, a, hpq, rfl⟩))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, me, opp, θ, p', q, a, hpq, rfl⟩)))))))
    · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨n, me, opp, w, I, rest, θ, p', q, a, ?_, rfl⟩))))))))
      rcases hpq with ⟨h0, hp⟩ | ⟨h0, r, _, hI, hr⟩
      · exact Or.inl ⟨h0, hp⟩
      · exact Or.inr ⟨h0, r, hI, hr⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨n, me, opp, d, i, m, a, hm, h, rfl⟩))))))))

set_option maxHeartbeats 6400000 in
noncomputable def construction : Fixpoint.Construction V blueprint where
  Φ := fun _ ↦ Phi
  defined := .mk <| by
    constructor
    · intro v
      simp [blueprint, HierarchySymbol.Semiformula.val_sigma,
        (LenBox.defined TAct).proper.iff', substCode_defined.df, listGet_defined.df, sysCloseCode_defined.df,
        sub_defined.df]
    · intro v
      symm
      simpa [blueprint, HierarchySymbol.Semiformula.val_sigma, (LenBox.defined TAct).df,
        substCode_defined.df, listGet_defined.df, sysCloseCode_defined.df, sub_defined.df,
        pSelfGraph, pOppGraph, pSelf, pOpp, lt_and_eq_succ_iff]
        using phi_iff (v 1) (v 0)
  monotone := by
    rintro C C' hC _ pr (⟨n, me, opp, a, rfl⟩ | ⟨n, me, opp, a, h, rfl⟩ | ⟨n, me, opp, a, h, rfl⟩ |
      ⟨n, me, opp, p, a, h, rfl⟩ | ⟨n, me, opp, p, q, a, h, rfl⟩ |
      ⟨n, me, opp, b, a', p, q, a, r, hb, hpq, rfl⟩ | ⟨n, me, opp, k, g, p, q, a, hpq, rfl⟩ |
      ⟨n, me, opp, θ, p, q, a, hpq, rfl⟩ | ⟨n, me, opp, w, I, rest, θ, p, q, a, hpq, rfl⟩ |
      ⟨n, me, opp, d, i, m, a, hm, h, rfl⟩)
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
    · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, me, opp, k, g, p, q, a, ?_, rfl⟩))))))
      rcases hpq with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨h1, hC h2⟩
      · exact Or.inr ⟨h1, hC h2⟩
    · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, me, opp, θ, p, q, a, ?_, rfl⟩)))))))
      rcases hpq with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨h1, hC h2⟩
      · exact Or.inr ⟨h1, hC h2⟩
    · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨n, me, opp, w, I, rest, θ, p, q, a, ?_, rfl⟩))))))))
      rcases hpq with ⟨h1, h2⟩ | ⟨h1, r, hI, ⟨hr, h2⟩ | ⟨hr, h2⟩⟩
      · exact Or.inl ⟨h1, hC h2⟩
      · exact Or.inr ⟨h1, r, hC hI, Or.inl ⟨hr, hC h2⟩⟩
      · exact Or.inr ⟨h1, r, hC hI, Or.inr ⟨hr, hC h2⟩⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨n, me, opp, d, i, m, a, hm, hC h, rfl⟩))))))))

instance : construction.Finite V where
  finite := by
    rintro C _ pr (⟨n, me, opp, a, rfl⟩ | ⟨n, me, opp, a, h, rfl⟩ | ⟨n, me, opp, a, h, rfl⟩ |
      ⟨n, me, opp, p, a, h, rfl⟩ | ⟨n, me, opp, p, q, a, h, rfl⟩ |
      ⟨n, me, opp, b, a', p, q, a, r, hb, hpq, rfl⟩ | ⟨n, me, opp, k, g, p, q, a, hpq, rfl⟩ |
      ⟨n, me, opp, θ, p, q, a, hpq, rfl⟩ | ⟨n, me, opp, w, I, rest, θ, p, q, a, hpq, rfl⟩ |
      ⟨n, me, opp, d, i, m, a, hm, h, rfl⟩)
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
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, me, opp, k, g, p, q, a, ?_, rfl⟩))))))⟩
      rcases hpq with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨h1, h2, lt_of_le_of_lt le_self_add (lt_add_one _)⟩
      · exact Or.inr ⟨h1, h2, lt_of_le_of_lt le_add_self (lt_add_one _)⟩
    · refine ⟨⟪n, me, opp, p, a⟫ + ⟪n, me, opp, q, a⟫ + 1,
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, me, opp, θ, p, q, a, ?_, rfl⟩)))))))⟩
      rcases hpq with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨h1, h2, lt_of_le_of_lt le_self_add (lt_add_one _)⟩
      · exact Or.inr ⟨h1, h2, lt_of_le_of_lt le_add_self (lt_add_one _)⟩
    · rcases hpq with ⟨h1, h2⟩ | ⟨h1, r, hI, hr⟩
      · exact ⟨_ + 1, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          ⟨n, me, opp, w, I, rest, θ, p, q, a, Or.inl ⟨h1, h2, lt_add_one _⟩, rfl⟩))))))))⟩
      · refine ⟨⟪n, pBot I, pBot I, I, r⟫ + ⟪n, me, opp, pTvote rest (θ - w) p q, a⟫ +
          ⟪n, me, opp, pTvote rest θ p q, a⟫ + 1,
          Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          ⟨n, me, opp, w, I, rest, θ, p, q, a, Or.inr ⟨h1, r, ⟨hI, by
            have := le_self_add (a := ⟪n, pBot I, pBot I, I, r⟫) (b := ⟪n, me, opp, pTvote rest (θ - w) p q, a⟫)
            have := le_self_add (a := ⟪n, pBot I, pBot I, I, r⟫ + ⟪n, me, opp, pTvote rest (θ - w) p q, a⟫)
              (b := ⟪n, me, opp, pTvote rest θ p q, a⟫)
            exact lt_of_le_of_lt (le_trans (by assumption) (by assumption)) (lt_add_one _)⟩, ?_⟩, rfl⟩))))))))⟩
        rcases hr with ⟨hr, h2⟩ | ⟨hr, h2⟩
        · exact Or.inl ⟨hr, h2, by
            have := le_add_self (a := ⟪n, me, opp, pTvote rest (θ - w) p q, a⟫) (b := ⟪n, pBot I, pBot I, I, r⟫)
            have := le_self_add (a := ⟪n, pBot I, pBot I, I, r⟫ + ⟪n, me, opp, pTvote rest (θ - w) p q, a⟫)
              (b := ⟪n, me, opp, pTvote rest θ p q, a⟫)
            exact lt_of_le_of_lt (le_trans (by assumption) (by assumption)) (lt_add_one _)⟩
        · exact Or.inr ⟨hr, h2, lt_of_le_of_lt le_add_self (lt_add_one _)⟩
    · exact ⟨_ + 1, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨n, me, opp, d, i, m, a, hm, ⟨h, lt_add_one _⟩, rfl⟩))))))))⟩

end EvalFix

end ArithS
