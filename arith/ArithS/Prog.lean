import ArithS.Symmetry

/-!
# ArithS.Prog — program codes and the action swap on codes

Programs are HFS pair-codes with a tag, exactly like Foundation's derivation codes
(`Bootstrapping.axL`, …), mirroring the engine's `Prog` (`Program.lean`), restricted-template
version (roadmap M2 design, 2026-09-10): a search node carries a budget `k` and the action
`a` of the guard "opp plays `a` against me".

* `pConst a = ⟪0, a⟫ + 1`, `pSelf = ⟪1, 0⟫ + 1`, `pOpp = ⟪2, 0⟫ + 1`, `pBot p = ⟪3, p⟫ + 1`,
  `pSim p q = ⟪4, p, q⟫ + 1`, `pIte b a p q = ⟪5, b, a, p, q⟫ + 1`,
  `pSearch k a p q = ⟪6, k, a, p, q⟫ + 1`; action values: `0 = C`, `1 = D`.
* `swapAct` exchanges the two action values; `swapcode` applies it to every action
  occurrence of a program code (a Δ₁ function defined by a fixpoint on pairs `⟪x, y⟫`, with a
  catch-all clause `y = x` on non-program codes so that it is total). It is the code-level
  τ of `Base/Transpose`: `swapcode (swapcode x) = x`.
-/

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ### Constructors -/

noncomputable def pConst (a : V) : V := ⟪0, a⟫ + 1
noncomputable def pSelf : V := ⟪1, 0⟫ + 1
noncomputable def pOpp : V := ⟪2, 0⟫ + 1
noncomputable def pBot (p : V) : V := ⟪3, p⟫ + 1
noncomputable def pSim (p q : V) : V := ⟪4, p, q⟫ + 1
noncomputable def pIte (b a p q : V) : V := ⟪5, b, a, p, q⟫ + 1
noncomputable def pSearch (k a p q : V) : V := ⟪6, k, a, p, q⟫ + 1

section graphs

def pConstGraph : 𝚺₀.Semisentence 2 := .mkSigma “y a. ∃ y' < y, !pairDef y' 0 a ∧ y = y' + 1”
instance pConst.defined : 𝚺₀-Function₁[V] pConst via pConstGraph := .mk fun v ↦ by
  simp_all [pConstGraph, pConst]

def pSelfGraph : 𝚺₀.Semisentence 1 := .mkSigma “y. ∃ y' < y, !pairDef y' 1 0 ∧ y = y' + 1”
def pOppGraph : 𝚺₀.Semisentence 1 := .mkSigma “y. ∃ y' < y, !pairDef y' 2 0 ∧ y = y' + 1”

def pBotGraph : 𝚺₀.Semisentence 2 := .mkSigma “y p. ∃ y' < y, !pairDef y' 3 p ∧ y = y' + 1”
instance pBot.defined : 𝚺₀-Function₁[V] pBot via pBotGraph := .mk fun v ↦ by
  simp_all [pBotGraph, pBot]

def pSimGraph : 𝚺₀.Semisentence 3 := .mkSigma “y p q. ∃ y' < y, !pair₃Def y' 4 p q ∧ y = y' + 1”
instance pSim.defined : 𝚺₀-Function₂[V] pSim via pSimGraph := .mk fun v ↦ by
  simp_all [pSimGraph, pSim]

def pIteGraph : 𝚺₀.Semisentence 5 :=
  .mkSigma “y b a p q. ∃ y' < y, !pair₅Def y' 5 b a p q ∧ y = y' + 1”
instance pIte.defined : 𝚺₀-Function₄ (pIte : V → V → V → V → V) via pIteGraph := .mk fun v ↦ by
  simp_all [pIteGraph, numeral_eq_natCast, pIte]

def pSearchGraph : 𝚺₀.Semisentence 5 :=
  .mkSigma “y k a p q. ∃ y' < y, !pair₅Def y' 6 k a p q ∧ y = y' + 1”
instance pSearch.defined : 𝚺₀-Function₄ (pSearch : V → V → V → V → V) via pSearchGraph :=
  .mk fun v ↦ by simp_all [pSearchGraph, numeral_eq_natCast, pSearch]

end graphs

/-! ### Size facts (sub-programs are smaller than their parent) -/

@[simp] lemma p_lt_pBot (p : V) : p < pBot p :=
  le_iff_lt_succ.mp <| le_trans (le_pair_right _ _) (le_refl _)
@[simp] lemma p_lt_pSim (p q : V) : p < pSim p q :=
  le_iff_lt_succ.mp <| le_trans (le_pair_left _ _) (le_pair_right _ _)
@[simp] lemma q_lt_pSim (p q : V) : q < pSim p q :=
  le_iff_lt_succ.mp <| le_trans (le_pair_right _ _) (le_pair_right _ _)
@[simp] lemma b_lt_pIte (b a p q : V) : b < pIte b a p q :=
  le_iff_lt_succ.mp <| le_trans (le_pair_left _ _) (le_pair_right _ _)
@[simp] lemma p_lt_pIte (b a p q : V) : p < pIte b a p q :=
  le_iff_lt_succ.mp <| le_trans (le_trans (le_trans (le_pair_left _ _) (le_pair_right _ _))
    (le_pair_right _ _)) (le_pair_right _ _)
@[simp] lemma q_lt_pIte (b a p q : V) : q < pIte b a p q :=
  le_iff_lt_succ.mp <| le_trans (le_trans (le_trans (le_pair_right _ _) (le_pair_right _ _))
    (le_pair_right _ _)) (le_pair_right _ _)
@[simp] lemma p_lt_pSearch (k a p q : V) : p < pSearch k a p q :=
  le_iff_lt_succ.mp <| le_trans (le_trans (le_trans (le_pair_left _ _) (le_pair_right _ _))
    (le_pair_right _ _)) (le_pair_right _ _)
@[simp] lemma q_lt_pSearch (k a p q : V) : q < pSearch k a p q :=
  le_iff_lt_succ.mp <| le_trans (le_trans (le_trans (le_pair_right _ _) (le_pair_right _ _))
    (le_pair_right _ _)) (le_pair_right _ _)

/-! ### The action swap -/

/-- `0 ↦ 1`, `1 ↦ 0`, other values fixed. -/
noncomputable def swapAct (a : V) : V := if a = 0 then 1 else if a = 1 then 0 else a

def swapActGraph : 𝚺₀.Semisentence 2 :=
  .mkSigma “y a. (a = 0 → y = 1) ∧ (a = 1 → y = 0) ∧ (a ≠ 0 → a ≠ 1 → y = a)”

instance swapAct.defined : 𝚺₀-Function₁[V] swapAct via swapActGraph := .mk fun v ↦ by
  suffices (v 1 = 0 → v 0 = 1) ∧ (v 1 = 1 → v 0 = 0) ∧ (v 1 ≠ 0 → v 1 ≠ 1 → v 0 = v 1) ↔
      v 0 = swapAct (v 1) by simpa [swapActGraph]
  unfold swapAct
  by_cases h0 : v 1 = 0
  · simp [h0]
  · by_cases h1 : v 1 = 1
    · simp [h0, h1]
    · simp [h0, h1]

@[simp] lemma swapAct_swapAct (a : V) : swapAct (swapAct a) = a := by
  unfold swapAct
  by_cases h0 : a = 0
  · simp [h0]
  · by_cases h1 : a = 1
    · simp [h0, h1]
    · simp [h0, h1]

/-! ### Program shapes -/

/-- `x` is a constructor application (its immediate components are all `< x`). -/
def IsShape (x : V) : Prop :=
  (∃ a, x = pConst a) ∨ x = pSelf ∨ x = pOpp ∨ (∃ p, x = pBot p) ∨ (∃ p q, x = pSim p q) ∨
  (∃ b a p q, x = pIte b a p q) ∨ (∃ k a p q, x = pSearch k a p q)

def isShape : 𝚺₀.Semisentence 1 := .mkSigma
  “x. (∃ a < x, !pConstGraph x a) ∨ !pSelfGraph x ∨ !pOppGraph x ∨ (∃ p < x, !pBotGraph x p) ∨
    (∃ p < x, ∃ q < x, !pSimGraph x p q) ∨ (∃ b < x, ∃ a < x, ∃ p < x, ∃ q < x, !pIteGraph x b a p q) ∨
    (∃ k < x, ∃ a < x, ∃ p < x, ∃ q < x, !pSearchGraph x k a p q)”

@[simp] lemma a_lt_pConst (a : V) : a < pConst a := le_iff_lt_succ.mp (le_pair_right _ _)
@[simp] lemma a_lt_pIte (b a p q : V) : a < pIte b a p q :=
  le_iff_lt_succ.mp <| le_trans (le_trans (le_pair_left _ _) (le_pair_right _ _)) (le_pair_right _ _)
@[simp] lemma k_lt_pSearch (k a p q : V) : k < pSearch k a p q :=
  le_iff_lt_succ.mp <| le_trans (le_pair_left _ _) (le_pair_right _ _)
@[simp] lemma a_lt_pSearch (k a p q : V) : a < pSearch k a p q :=
  le_iff_lt_succ.mp <| le_trans (le_trans (le_pair_left _ _) (le_pair_right _ _)) (le_pair_right _ _)

lemma isShape_iff (x : V) :
    IsShape x ↔
    (∃ a < x, x = pConst a) ∨ x = pSelf ∨ x = pOpp ∨ (∃ p < x, x = pBot p) ∨
    (∃ p < x, ∃ q < x, x = pSim p q) ∨ (∃ b < x, ∃ a < x, ∃ p < x, ∃ q < x, x = pIte b a p q) ∨
    (∃ k < x, ∃ a < x, ∃ p < x, ∃ q < x, x = pSearch k a p q) := by
  constructor
  · rintro (⟨a, rfl⟩ | rfl | rfl | ⟨p, rfl⟩ | ⟨p, q, rfl⟩ | ⟨b, a, p, q, rfl⟩ | ⟨k, a, p, q, rfl⟩)
    · exact Or.inl ⟨a, by simp, rfl⟩
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨p, by simp, rfl⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, by simp, q, by simp, rfl⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨b, by simp, a, by simp, p, by simp, q, by simp, rfl⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨k, by simp, a, by simp, p, by simp, q, by simp, rfl⟩)))))
  · rintro (⟨a, _, rfl⟩ | rfl | rfl | ⟨p, _, rfl⟩ | ⟨p, _, q, _, rfl⟩ |
      ⟨b, _, a, _, p, _, q, _, rfl⟩ | ⟨k, _, a, _, p, _, q, _, rfl⟩)
    · exact Or.inl ⟨a, rfl⟩
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨p, rfl⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, q, rfl⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨b, a, p, q, rfl⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨k, a, p, q, rfl⟩)))))

lemma lt_and_eq_succ_iff {a y : V} : (a < y ∧ y = a + 1) ↔ y = a + 1 :=
  ⟨And.right, fun h ↦ ⟨by rw [h]; exact lt_add_one a, h⟩⟩

instance IsShape.defined : 𝚺₀-Predicate[V] IsShape via isShape := .mk fun v ↦ by
  simp [isShape, isShape_iff, pSelfGraph, pOppGraph, pSelf, pOpp, lt_and_eq_succ_iff]

instance IsShape.definable : 𝚺₀-Predicate[V] IsShape := IsShape.defined.to_definable

instance IsShape.definable' (Γ m) : Γ-[m]-Predicate[V] IsShape :=
  HierarchySymbol.Definable.of_zero IsShape.definable

/-! ### The swap on codes: a fixpoint on pairs `⟪x, y⟫` -/

lemma swapAct_le (a : V) : swapAct a ≤ a + 1 := by
  unfold swapAct
  by_cases h0 : a = 0
  · simp [h0]
  · by_cases h1 : a = 1
    · simp [h1]
    · simp [h0, h1]

namespace Swap

def Phi (C : Set V) (pr : V) : Prop :=
  (∃ a, pr = ⟪pConst a, pConst (swapAct a)⟫) ∨
  pr = ⟪pSelf, pSelf⟫ ∨ pr = ⟪pOpp, pOpp⟫ ∨
  (∃ p p', ⟪p, p'⟫ ∈ C ∧ pr = ⟪pBot p, pBot p'⟫) ∨
  (∃ p q p' q', ⟪p, p'⟫ ∈ C ∧ ⟪q, q'⟫ ∈ C ∧ pr = ⟪pSim p q, pSim p' q'⟫) ∨
  (∃ b a p q b' p' q', ⟪b, b'⟫ ∈ C ∧ ⟪p, p'⟫ ∈ C ∧ ⟪q, q'⟫ ∈ C ∧
    pr = ⟪pIte b a p q, pIte b' (swapAct a) p' q'⟫) ∨
  (∃ k a p q p' q', ⟪p, p'⟫ ∈ C ∧ ⟪q, q'⟫ ∈ C ∧
    pr = ⟪pSearch k a p q, pSearch k (swapAct a) p' q'⟫) ∨
  (∃ x, ¬IsShape x ∧ pr = ⟪x, x⟫)

def core₀ : 𝚺₀.Semisentence 2 := .mkSigma
  “pr C. ∃ x <⁺ pr, ∃ y <⁺ pr, !pairDef pr x y ∧
    ( (∃ a < x, !pConstGraph x a ∧ ∃ a' <⁺ a + 1, !swapActGraph a' a ∧ !pConstGraph y a') ∨
      (!pSelfGraph x ∧ !pSelfGraph y) ∨
      (!pOppGraph x ∧ !pOppGraph y) ∨
      (∃ p < x, !pBotGraph x p ∧ ∃ p' < y, :⟪p, p'⟫:∈ C ∧ !pBotGraph y p') ∨
      (∃ p < x, ∃ q < x, !pSimGraph x p q ∧
        ∃ p' < y, ∃ q' < y, :⟪p, p'⟫:∈ C ∧ :⟪q, q'⟫:∈ C ∧ !pSimGraph y p' q') ∨
      (∃ b < x, ∃ a < x, ∃ p < x, ∃ q < x, !pIteGraph x b a p q ∧
        ∃ b' < y, ∃ a' <⁺ a + 1, ∃ p' < y, ∃ q' < y,
          :⟪b, b'⟫:∈ C ∧ :⟪p, p'⟫:∈ C ∧ :⟪q, q'⟫:∈ C ∧ !swapActGraph a' a ∧ !pIteGraph y b' a' p' q') ∨
      (∃ k < x, ∃ a < x, ∃ p < x, ∃ q < x, !pSearchGraph x k a p q ∧
        ∃ a' <⁺ a + 1, ∃ p' < y, ∃ q' < y,
          :⟪p, p'⟫:∈ C ∧ :⟪q, q'⟫:∈ C ∧ !swapActGraph a' a ∧ !pSearchGraph y k a' p' q') ∨
      (¬!isShape x ∧ y = x) )”

noncomputable def blueprint : Fixpoint.Blueprint 0 := ⟨core₀.ofZero _⟩

private lemma phi_iff (C pr : V) :
    Phi {x | x ∈ C} pr ↔
    ∃ x ≤ pr, ∃ y ≤ pr, pr = ⟪x, y⟫ ∧
    ( (∃ a < x, x = pConst a ∧ ∃ a' ≤ a + 1, a' = swapAct a ∧ y = pConst a') ∨
      (x = pSelf ∧ y = pSelf) ∨
      (x = pOpp ∧ y = pOpp) ∨
      (∃ p < x, x = pBot p ∧ ∃ p' < y, ⟪p, p'⟫ ∈ C ∧ y = pBot p') ∨
      (∃ p < x, ∃ q < x, x = pSim p q ∧
        ∃ p' < y, ∃ q' < y, ⟪p, p'⟫ ∈ C ∧ ⟪q, q'⟫ ∈ C ∧ y = pSim p' q') ∨
      (∃ b < x, ∃ a < x, ∃ p < x, ∃ q < x, x = pIte b a p q ∧
        ∃ b' < y, ∃ a' ≤ a + 1, ∃ p' < y, ∃ q' < y,
          ⟪b, b'⟫ ∈ C ∧ ⟪p, p'⟫ ∈ C ∧ ⟪q, q'⟫ ∈ C ∧ a' = swapAct a ∧ y = pIte b' a' p' q') ∨
      (∃ k < x, ∃ a < x, ∃ p < x, ∃ q < x, x = pSearch k a p q ∧
        ∃ a' ≤ a + 1, ∃ p' < y, ∃ q' < y,
          ⟪p, p'⟫ ∈ C ∧ ⟪q, q'⟫ ∈ C ∧ a' = swapAct a ∧ y = pSearch k a' p' q') ∨
      (¬IsShape x ∧ y = x) ) := by
  constructor
  · rintro (⟨a, rfl⟩ | rfl | rfl | ⟨p, p', h, rfl⟩ | ⟨p, q, p', q', hp, hq, rfl⟩ |
      ⟨b, a, p, q, b', p', q', hb, hp, hq, rfl⟩ | ⟨k, a, p, q, p', q', hp, hq, rfl⟩ | ⟨x, hx, rfl⟩)
    · exact ⟨_, by simp, _, by simp, rfl, Or.inl ⟨a, by simp, rfl, _, swapAct_le a, rfl, rfl⟩⟩
    · exact ⟨_, by simp, _, by simp, rfl, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
    · exact ⟨_, by simp, _, by simp, rfl, Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩
    · exact ⟨_, by simp, _, by simp, rfl, Or.inr (Or.inr (Or.inr (Or.inl
        ⟨p, by simp, rfl, p', by simp, h, rfl⟩)))⟩
    · exact ⟨_, by simp, _, by simp, rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨p, by simp, q, by simp, rfl, p', by simp, q', by simp, hp, hq, rfl⟩))))⟩
    · exact ⟨_, by simp, _, by simp, rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨b, by simp, a, by simp, p, by simp, q, by simp, rfl, b', by simp, _, swapAct_le a,
          p', by simp, q', by simp, hb, hp, hq, rfl, rfl⟩)))))⟩
    · exact ⟨_, by simp, _, by simp, rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨k, by simp, a, by simp, p, by simp, q, by simp, rfl, _, swapAct_le a,
          p', by simp, q', by simp, hp, hq, rfl, rfl⟩))))))⟩
    · exact ⟨_, by simp, _, by simp, rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨hx, rfl⟩))))))⟩
  · rintro ⟨x, _, y, _, rfl, (⟨a, _, rfl, a', _, rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨p, _, rfl, p', _, h, rfl⟩ | ⟨p, _, q, _, rfl, p', _, q', _, hp, hq, rfl⟩ |
      ⟨b, _, a, _, p, _, q, _, rfl, b', _, a', _, p', _, q', _, hb, hp, hq, rfl, rfl⟩ |
      ⟨k, _, a, _, p, _, q, _, rfl, a', _, p', _, q', _, hp, hq, rfl, rfl⟩ | ⟨hx, hyx⟩)⟩
    · exact Or.inl ⟨a, rfl⟩
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨p, p', h, rfl⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, q, p', q', hp, hq, rfl⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨b, a, p, q, b', p', q', hb, hp, hq, rfl⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨k, a, p, q, p', q', hp, hq, rfl⟩))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨x, hx, by rw [hyx]⟩))))))

lemma core₀_defined : 𝚺₀.Defined (fun v : Fin 2 → V ↦ Phi {x | x ∈ v 1} (v 0)) core₀ := .mk fun v ↦ by
  symm
  simpa [core₀, pSelfGraph, pOppGraph, pSelf, pOpp, lt_and_eq_succ_iff] using phi_iff (v 1) (v 0)

noncomputable def construction : Fixpoint.Construction V blueprint where
  Φ := fun _ ↦ Phi
  defined := core₀_defined.of_zero
  monotone := by
    rintro C C' hC _ pr (⟨a, rfl⟩ | rfl | rfl | ⟨p, p', h, rfl⟩ | ⟨p, q, p', q', hp, hq, rfl⟩ |
      ⟨b, a, p, q, b', p', q', hb, hp, hq, rfl⟩ | ⟨k, a, p, q, p', q', hp, hq, rfl⟩ | ⟨x, hx, rfl⟩)
    · exact Or.inl ⟨a, rfl⟩
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨p, p', hC h, rfl⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, q, p', q', hC hp, hC hq, rfl⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨b, a, p, q, b', p', q', hC hb, hC hp, hC hq, rfl⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨k, a, p, q, p', q', hC hp, hC hq, rfl⟩))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨x, hx, rfl⟩))))))

instance : construction.StrongFinite V where
  strong_finite := by
    rintro C _ pr (⟨a, rfl⟩ | rfl | rfl | ⟨p, p', h, rfl⟩ | ⟨p, q, p', q', hp, hq, rfl⟩ |
      ⟨b, a, p, q, b', p', q', hb, hp, hq, rfl⟩ | ⟨k, a, p, q, p', q', hp, hq, rfl⟩ | ⟨x, hx, rfl⟩)
    · exact Or.inl ⟨a, rfl⟩
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨p, p', ⟨h, pair_lt_pair (by simp) (by simp)⟩, rfl⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, q, p', q',
        ⟨hp, pair_lt_pair (by simp) (by simp)⟩, ⟨hq, pair_lt_pair (by simp) (by simp)⟩, rfl⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨b, a, p, q, b', p', q',
        ⟨hb, pair_lt_pair (by simp) (by simp)⟩, ⟨hp, pair_lt_pair (by simp) (by simp)⟩,
        ⟨hq, pair_lt_pair (by simp) (by simp)⟩, rfl⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨k, a, p, q, p', q',
        ⟨hp, pair_lt_pair (by simp) (by simp)⟩, ⟨hq, pair_lt_pair (by simp) (by simp)⟩, rfl⟩))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨x, hx, rfl⟩))))))

end Swap

/-- `SwapGraph x y`: `y` is `x` with the two action values exchanged. -/
def SwapGraph (x y : V) : Prop := Swap.construction.Fixpoint ![] ⟪x, y⟫

noncomputable def swapGraphDef : 𝚫₁.Semisentence 2 := .mkDelta
  (.mkSigma “x y. ∃ pr <⁺ (x + y + 1)², !pairDef pr x y ∧ !Swap.blueprint.fixpointDefΔ₁.sigma pr”)
  (.mkPi “x y. ∀ pr <⁺ (x + y + 1)², !pairDef pr x y → !Swap.blueprint.fixpointDefΔ₁.pi pr”)

private lemma swap_fixpoint_param_eq (p : Fin 0 → V) (x : V) :
    Swap.construction.Fixpoint p x = Swap.construction.Fixpoint ![] x := by
  rw [Subsingleton.elim p ![]]

instance swapGraph_defined : 𝚫₁-Relation[V] SwapGraph via swapGraphDef := .mk
  ⟨by intro v
      simp [swapGraphDef, HierarchySymbol.Semiformula.val_sigma,
        Swap.construction.fixpoint_definedΔ₁.proper.iff', Swap.construction.fixpoint_definedΔ₁.df]
      constructor
      · rintro h x _ rfl; rwa [swap_fixpoint_param_eq] at h ⊢
      · intro h; have := h ⟪v 0, v 1⟫ (by simp) rfl; rwa [swap_fixpoint_param_eq] at this ⊢,
   by intro v
      simp [swapGraphDef, HierarchySymbol.Semiformula.val_sigma,
        Swap.construction.fixpoint_definedΔ₁.df, SwapGraph]
      rw [swap_fixpoint_param_eq]⟩

instance swapGraph_definable : 𝚫₁-Relation[V] SwapGraph := swapGraph_defined.to_definable

instance swapGraph_definable' : Γ-[m + 1]-Relation[V] SwapGraph := swapGraph_definable.of_deltaOne

lemma SwapGraph.case_iff {x y : V} :
    SwapGraph x y ↔
    (∃ a, x = pConst a ∧ y = pConst (swapAct a)) ∨
    (x = pSelf ∧ y = pSelf) ∨ (x = pOpp ∧ y = pOpp) ∨
    (∃ p p', SwapGraph p p' ∧ x = pBot p ∧ y = pBot p') ∨
    (∃ p q p' q', SwapGraph p p' ∧ SwapGraph q q' ∧ x = pSim p q ∧ y = pSim p' q') ∨
    (∃ b a p q b' p' q', SwapGraph b b' ∧ SwapGraph p p' ∧ SwapGraph q q' ∧
      x = pIte b a p q ∧ y = pIte b' (swapAct a) p' q') ∨
    (∃ k a p q p' q', SwapGraph p p' ∧ SwapGraph q q' ∧
      x = pSearch k a p q ∧ y = pSearch k (swapAct a) p' q') ∨
    (¬IsShape y ∧ x = y) :=
  Iff.trans Swap.construction.case (by simp [Swap.construction, Swap.Phi, SwapGraph])

section inversion

attribute [local simp] pConst pSelf pOpp pBot pSim pIte pSearch IsShape

lemma SwapGraph.const_iff {a y : V} : SwapGraph (pConst a) y ↔ y = pConst (swapAct a) := by
  rw [SwapGraph.case_iff]; simp
  intro h₀ _ _ _ _ _ _ h; exact absurd h.symm (h₀ a)
lemma SwapGraph.self_iff {y : V} : SwapGraph pSelf y ↔ y = pSelf := by
  rw [SwapGraph.case_iff]; simp
  intro _ h₁ _ _ _ _ _ h; exact absurd h.symm h₁
lemma SwapGraph.opp_iff {y : V} : SwapGraph pOpp y ↔ y = pOpp := by
  rw [SwapGraph.case_iff]; simp
  intro _ _ h₂ _ _ _ _ h; exact absurd h.symm h₂
lemma SwapGraph.bot_iff {p y : V} : SwapGraph (pBot p) y ↔ ∃ p', SwapGraph p p' ∧ y = pBot p' := by
  rw [SwapGraph.case_iff]; simp
  intro _ _ _ h₃ _ _ _ h; exact absurd h.symm (h₃ p)
lemma SwapGraph.sim_iff {p q y : V} :
    SwapGraph (pSim p q) y ↔ ∃ p' q', SwapGraph p p' ∧ SwapGraph q q' ∧ y = pSim p' q' := by
  rw [SwapGraph.case_iff]; simp
  intro _ _ _ _ h₄ _ _ h; exact absurd h.symm (h₄ p q)
lemma SwapGraph.ite_iff {b a p q y : V} :
    SwapGraph (pIte b a p q) y ↔
    ∃ b' p' q', SwapGraph b b' ∧ SwapGraph p p' ∧ SwapGraph q q' ∧ y = pIte b' (swapAct a) p' q' := by
  rw [SwapGraph.case_iff]; simp
  intro _ _ _ _ _ h₅ _ h; exact absurd h.symm (h₅ b a p q)
lemma SwapGraph.search_iff {k a p q y : V} :
    SwapGraph (pSearch k a p q) y ↔
    ∃ p' q', SwapGraph p p' ∧ SwapGraph q q' ∧ y = pSearch k (swapAct a) p' q' := by
  rw [SwapGraph.case_iff]; simp
  intro _ _ _ _ _ _ h₆ h; exact absurd h.symm (h₆ k a p q)
lemma SwapGraph.of_not_shape {x y : V} (hx : ¬IsShape x) : SwapGraph x y ↔ y = x := by
  rw [SwapGraph.case_iff]
  constructor
  · rintro (⟨a, rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨p, p', _, rfl, _⟩ | ⟨p, q, p', q', _, _, rfl, _⟩ |
      ⟨b, a, p, q, b', p', q', _, _, _, rfl, _⟩ | ⟨k, a, p, q, p', q', _, _, rfl, _⟩ | ⟨_, h⟩)
    · exact absurd (Or.inl ⟨a, rfl⟩) hx
    · exact absurd (Or.inr (Or.inl rfl)) hx
    · exact absurd (Or.inr (Or.inr (Or.inl rfl))) hx
    · exact absurd (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, rfl⟩)))) hx
    · exact absurd (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, q, rfl⟩))))) hx
    · exact absurd (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨b, a, p, q, rfl⟩)))))) hx
    · exact absurd (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨k, a, p, q, rfl⟩)))))) hx
    · exact h.symm
  · rintro rfl
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hx, rfl⟩))))))

end inversion

/-! ### `swapcode` is a total Σ₁ function -/

lemma swapGraph_exists (x : V) : ∃ y, SwapGraph x y := by
  induction x using ISigma1.sigma1_order_induction with
  | hP => definability
  | ind x ih =>
    by_cases hx : IsShape x
    · rcases hx with ⟨a, rfl⟩ | rfl | rfl | ⟨p, rfl⟩ | ⟨p, q, rfl⟩ | ⟨b, a, p, q, rfl⟩ | ⟨k, a, p, q, rfl⟩
      · exact ⟨_, SwapGraph.const_iff.mpr rfl⟩
      · exact ⟨_, SwapGraph.self_iff.mpr rfl⟩
      · exact ⟨_, SwapGraph.opp_iff.mpr rfl⟩
      · obtain ⟨p', hp⟩ := ih p (by simp)
        exact ⟨_, SwapGraph.bot_iff.mpr ⟨p', hp, rfl⟩⟩
      · obtain ⟨p', hp⟩ := ih p (by simp); obtain ⟨q', hq⟩ := ih q (by simp)
        exact ⟨_, SwapGraph.sim_iff.mpr ⟨p', q', hp, hq, rfl⟩⟩
      · obtain ⟨b', hb⟩ := ih b (by simp); obtain ⟨p', hp⟩ := ih p (by simp)
        obtain ⟨q', hq⟩ := ih q (by simp)
        exact ⟨_, SwapGraph.ite_iff.mpr ⟨b', p', q', hb, hp, hq, rfl⟩⟩
      · obtain ⟨p', hp⟩ := ih p (by simp); obtain ⟨q', hq⟩ := ih q (by simp)
        exact ⟨_, SwapGraph.search_iff.mpr ⟨p', q', hp, hq, rfl⟩⟩
    · exact ⟨x, (SwapGraph.of_not_shape hx).mpr rfl⟩

lemma swapGraph_unique (x : V) : ∀ y₁ y₂, SwapGraph x y₁ → SwapGraph x y₂ → y₁ = y₂ := by
  induction x using ISigma1.pi1_order_induction with
  | hP => definability
  | ind x ih =>
    intro y₁ y₂ h₁ h₂
    by_cases hx : IsShape x
    · rcases hx with ⟨a, rfl⟩ | rfl | rfl | ⟨p, rfl⟩ | ⟨p, q, rfl⟩ | ⟨b, a, p, q, rfl⟩ | ⟨k, a, p, q, rfl⟩
      · rw [SwapGraph.const_iff] at h₁ h₂; rw [h₁, h₂]
      · rw [SwapGraph.self_iff] at h₁ h₂; rw [h₁, h₂]
      · rw [SwapGraph.opp_iff] at h₁ h₂; rw [h₁, h₂]
      · rcases SwapGraph.bot_iff.mp h₁ with ⟨p₁, hp₁, rfl⟩
        rcases SwapGraph.bot_iff.mp h₂ with ⟨p₂, hp₂, rfl⟩
        rw [ih p (by simp) _ _ hp₁ hp₂]
      · rcases SwapGraph.sim_iff.mp h₁ with ⟨p₁, q₁, hp₁, hq₁, rfl⟩
        rcases SwapGraph.sim_iff.mp h₂ with ⟨p₂, q₂, hp₂, hq₂, rfl⟩
        rw [ih p (by simp) _ _ hp₁ hp₂, ih q (by simp) _ _ hq₁ hq₂]
      · rcases SwapGraph.ite_iff.mp h₁ with ⟨b₁, p₁, q₁, hb₁, hp₁, hq₁, rfl⟩
        rcases SwapGraph.ite_iff.mp h₂ with ⟨b₂, p₂, q₂, hb₂, hp₂, hq₂, rfl⟩
        rw [ih b (by simp) _ _ hb₁ hb₂, ih p (by simp) _ _ hp₁ hp₂, ih q (by simp) _ _ hq₁ hq₂]
      · rcases SwapGraph.search_iff.mp h₁ with ⟨p₁, q₁, hp₁, hq₁, rfl⟩
        rcases SwapGraph.search_iff.mp h₂ with ⟨p₂, q₂, hp₂, hq₂, rfl⟩
        rw [ih p (by simp) _ _ hp₁ hp₂, ih q (by simp) _ _ hq₁ hq₂]
    · rw [SwapGraph.of_not_shape hx] at h₁ h₂; rw [h₁, h₂]

lemma swapGraph_existsUnique (x : V) : ∃! y, SwapGraph x y := by
  rcases swapGraph_exists x with ⟨y, hy⟩
  exact ExistsUnique.intro y hy (fun y' h' ↦ swapGraph_unique x y' y h' hy)

/-- The action swap on program codes. -/
noncomputable def swapcode (x : V) : V := Classical.choose! (swapGraph_existsUnique x)

lemma swapcode_graph (x : V) : SwapGraph x (swapcode x) := Classical.choose!_spec (swapGraph_existsUnique x)

lemma swapcode_eq_of_graph {x y : V} (h : SwapGraph x y) : swapcode x = y :=
  swapGraph_unique x _ _ (swapcode_graph x) h

noncomputable def swapcodeDef : 𝚺₁.Semisentence 2 := .mkSigma “y x. !swapGraphDef.sigma x y”

instance swapcode_defined : 𝚺₁-Function₁[V] swapcode via swapcodeDef := .mk fun v ↦ by
  simp [swapcodeDef, HierarchySymbol.Semiformula.val_sigma, swapGraph_defined.df]
  constructor
  · intro h; exact (swapcode_eq_of_graph h).symm
  · intro h; rw [h]; exact swapcode_graph _

instance swapcode_definable : 𝚺₁-Function₁[V] swapcode := swapcode_defined.to_definable

instance swapcode_definable' : Γ-[m + 1]-Function₁[V] swapcode := swapcode_definable.of_sigmaOne

@[simp] lemma swapcode_const (a : V) : swapcode (pConst a) = pConst (swapAct a) :=
  swapcode_eq_of_graph (SwapGraph.const_iff.mpr rfl)
@[simp] lemma swapcode_self : swapcode (pSelf : V) = pSelf :=
  swapcode_eq_of_graph (SwapGraph.self_iff.mpr rfl)
@[simp] lemma swapcode_opp : swapcode (pOpp : V) = pOpp :=
  swapcode_eq_of_graph (SwapGraph.opp_iff.mpr rfl)
@[simp] lemma swapcode_bot (p : V) : swapcode (pBot p) = pBot (swapcode p) :=
  swapcode_eq_of_graph (SwapGraph.bot_iff.mpr ⟨_, swapcode_graph p, rfl⟩)
@[simp] lemma swapcode_sim (p q : V) : swapcode (pSim p q) = pSim (swapcode p) (swapcode q) :=
  swapcode_eq_of_graph (SwapGraph.sim_iff.mpr ⟨_, _, swapcode_graph p, swapcode_graph q, rfl⟩)
@[simp] lemma swapcode_ite (b a p q : V) :
    swapcode (pIte b a p q) = pIte (swapcode b) (swapAct a) (swapcode p) (swapcode q) :=
  swapcode_eq_of_graph (SwapGraph.ite_iff.mpr
    ⟨_, _, _, swapcode_graph b, swapcode_graph p, swapcode_graph q, rfl⟩)
@[simp] lemma swapcode_search (k a p q : V) :
    swapcode (pSearch k a p q) = pSearch k (swapAct a) (swapcode p) (swapcode q) :=
  swapcode_eq_of_graph (SwapGraph.search_iff.mpr ⟨_, _, swapcode_graph p, swapcode_graph q, rfl⟩)
lemma swapcode_of_not_shape {x : V} (hx : ¬IsShape x) : swapcode x = x :=
  swapcode_eq_of_graph ((SwapGraph.of_not_shape hx).mpr rfl)

/-- τ is an involution on codes. -/
theorem swapcode_swapcode (x : V) : swapcode (swapcode x) = x := by
  induction x using ISigma1.pi1_order_induction with
  | hP => definability
  | ind x ih =>
    by_cases hx : IsShape x
    · rcases hx with ⟨a, rfl⟩ | rfl | rfl | ⟨p, rfl⟩ | ⟨p, q, rfl⟩ | ⟨b, a, p, q, rfl⟩ | ⟨k, a, p, q, rfl⟩
      · simp
      · simp
      · simp
      · simp [ih p (by simp)]
      · simp [ih p (by simp), ih q (by simp)]
      · simp [ih b (by simp), ih p (by simp), ih q (by simp)]
      · simp [ih p (by simp), ih q (by simp)]
    · rw [swapcode_of_not_shape hx, swapcode_of_not_shape hx]

end ArithS
