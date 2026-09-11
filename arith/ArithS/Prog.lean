import ArithS.Symmetry
import ArithS.RelabelTemplate

/-!
# ArithS.Prog — program codes and the action swap on codes

Programs are tagged codes built with the POLYNOMIAL pairing `ppair x y = (x + y)² + y`
(since 2026-09-11; before that Foundation's Cantor pair `⟪x, y⟫`, an `if` no ℒₒᵣ-term
denotes — the parametric bounded Löb milestone needs a program to be describable by a TERM
built from the binary numeral of its budget). They mirror the engine's `Prog`
(`Program.lean`); since roadmap M3 step (a) (2026-09-10) a search node carries a budget `k`
and a SIX-VARIABLE guard template `g` (a formula code over `LAct` in the description triples
`x₁ u₁ w₁` of `me` and `x₂ u₂ w₂` of `opp`, see `ArithS.Guard`/`ArithS.Template`); there is
no action slot.

* `pConst a = ppair 0 a + 1`, `pSelf = ppair 1 0 + 1`, `pOpp = ppair 2 0 + 1`,
  `pBot p = ppair 3 p + 1`, `pSim p q = ppair 4 (ppair p q) + 1`,
  `pIte b a p q = ppair 5 (ppair b (ppair a (ppair p q))) + 1`,
  `pSearch k g p q = ppair 6 (ppair k (ppair g (ppair p q))) + 1` (right-nested, exactly the
  nesting of the former `⟪6, k, g, p, q⟫`); action values: `0 = C`, `1 = D`. Sub-programs are
  STRICTLY below their parent (`le_ppair_left/right` + the outer `+ 1`), constructors are
  injective and pairwise disjoint (`ppair_ext_iff` + the tag).
* `swapAct` exchanges the two action values; `swapcode` applies it to every action
  occurrence of a program code — the action VALUES of `pConst`/`pIte` and, through
  `relabelTemplate` (`ArithS.RelabelTemplate`), the action CONSTANTS of every stored
  template (a Δ₁ function defined by a fixpoint on Foundation pairs `⟪x, y⟫` of
  input/output — the fixpoint machinery keeps the Cantor pair — with a catch-all clause
  `y = x` on non-program codes so that it is total). It is the code-level τ of
  `Base/Transpose`: `swapcode (swapcode x) = x`.
-/

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ### The polynomial pairing `ppair x y = (x + y)² + y` -/

section ppair

/-- The polynomial pairing `(x + y) * (x + y) + y`: injective, monotone in each argument,
above both arguments, and — unlike Foundation's Cantor pair, defined by an `if` — denoted by
an ℒₒᵣ-TERM. -/
noncomputable def ppair (x y : V) : V := (x + y) * (x + y) + y

/-- The Δ₀ graph of `ppair`: a plain polynomial equation, no quantifier. -/
def ppairDef : 𝚺₀.Semisentence 3 := .mkSigma “z x y. z = (x + y) * (x + y) + y”

instance ppair.defined : 𝚺₀-Function₂[V] ppair via ppairDef := .mk fun v ↦ by
  simp [ppairDef, ppair]

instance ppair.definable : 𝚺₀-Function₂[V] ppair := ppair.defined.to_definable

instance ppair.definable' (Γ m) : Γ-[m]-Function₂[V] ppair :=
  HierarchySymbol.Definable.of_zero ppair.definable

@[simp] lemma le_ppair_left (x y : V) : x ≤ ppair x y :=
  le_trans le_self_add (le_trans (le_mul_self _) le_self_add)

@[simp] lemma le_ppair_right (x y : V) : y ≤ ppair x y := le_add_self

/-- `s² + y < s'² + y'` whenever `s < s'` and `y ≤ s`: `s² + y ≤ s² + s < (s + 1)² ≤ s'²`. -/
lemma sq_add_lt_sq_add {s y s' : V} (hy : y ≤ s) (h : s < s') (y' : V) :
    s * s + y < s' * s' + y' := by
  have h1 : s * s + y < (s + 1) * (s + 1) := by
    have e : (s + 1) * (s + 1) = s * s + s + (s + 1) := by ring
    rw [e]
    exact lt_of_le_of_lt (_root_.add_le_add_right hy _)
      (lt_add_of_pos_right _ (lt_of_le_of_lt (by simp) (lt_add_one s)))
  have h2 : (s + 1) * (s + 1) ≤ s' * s' :=
    mul_le_mul (lt_iff_succ_le.mp h) (lt_iff_succ_le.mp h) (by simp) (by simp)
  exact lt_of_lt_of_le h1 (le_trans h2 le_self_add)

/-- `s² + y` with `y ≤ s` determines `s`. -/
lemma sq_add_inj {s y s' y' : V} (hy : y ≤ s) (hy' : y' ≤ s')
    (h : s * s + y = s' * s' + y') : s = s' := by
  rcases lt_trichotomy s s' with hlt | heq | hgt
  · exact absurd h (ne_of_lt (sq_add_lt_sq_add hy hlt y'))
  · exact heq
  · exact absurd h.symm (ne_of_lt (sq_add_lt_sq_add hy' hgt y))

/-- `ppair` is injective. -/
lemma ppair_inj {x y x' y' : V} (h : ppair x y = ppair x' y') : x = x' ∧ y = y' := by
  have hs : x + y = x' + y' := sq_add_inj le_add_self le_add_self h
  have hy : y = y' := by
    unfold ppair at h
    rw [hs] at h
    exact add_left_cancel h
  refine ⟨?_, hy⟩
  rw [hy] at hs
  exact add_right_cancel hs

@[simp] lemma ppair_ext_iff {x y x' y' : V} : ppair x y = ppair x' y' ↔ x = x' ∧ y = y' :=
  ⟨ppair_inj, by rintro ⟨rfl, rfl⟩; rfl⟩

lemma ppair_lt_ppair_left {x₁ x₂ : V} (h : x₁ < x₂) (y : V) : ppair x₁ y < ppair x₂ y := by
  unfold ppair
  have h' : x₁ + y < x₂ + y := _root_.add_lt_add_left h y
  exact _root_.add_lt_add_left (mul_lt_mul'' h' h' (by simp) (by simp)) y

lemma ppair_lt_ppair_right (x : V) {y₁ y₂ : V} (h : y₁ < y₂) : ppair x y₁ < ppair x y₂ := by
  unfold ppair
  have h' : x + y₁ ≤ x + y₂ := _root_.add_le_add_right (le_of_lt h) x
  exact add_lt_add_of_le_of_lt (mul_le_mul h' h' (by simp) (by simp)) h

lemma ppair_le_ppair_left {x₁ x₂ : V} (h : x₁ ≤ x₂) (y : V) : ppair x₁ y ≤ ppair x₂ y := by
  rcases h with (rfl | lt)
  · exact le_refl _
  · exact le_of_lt (ppair_lt_ppair_left lt y)

lemma ppair_le_ppair_right (x : V) {y₁ y₂ : V} (h : y₁ ≤ y₂) : ppair x y₁ ≤ ppair x y₂ := by
  rcases h with (rfl | lt)
  · exact le_refl _
  · exact le_of_lt (ppair_lt_ppair_right x lt)

lemma ppair_le_ppair {x₁ x₂ y₁ y₂ : V} (hx : x₁ ≤ x₂) (hy : y₁ ≤ y₂) :
    ppair x₁ y₁ ≤ ppair x₂ y₂ :=
  le_trans (ppair_le_ppair_left hx y₁) (ppair_le_ppair_right x₂ hy)

lemma ppair_lt_ppair {x₁ x₂ y₁ y₂ : V} (hx : x₁ < x₂) (hy : y₁ < y₂) :
    ppair x₁ y₁ < ppair x₂ y₂ :=
  lt_trans (ppair_lt_ppair_left hx y₁) (ppair_lt_ppair_right x₂ hy)

/-- The polynomial bound `ppair x y ≤ (x + y + 1)²` (bit length at most doubles). -/
lemma ppair_le_sq_succ (x y : V) : ppair x y ≤ (x + y + 1) * (x + y + 1) := by
  have e : (x + y + 1) * (x + y + 1) = ppair x y + (x + (x + y) + 1) := by
    unfold ppair; ring
  rw [e]
  exact le_self_add

end ppair

/-! ### Constructors -/

noncomputable def pConst (a : V) : V := ppair 0 a + 1
noncomputable def pSelf : V := ppair 1 0 + 1
noncomputable def pOpp : V := ppair 2 0 + 1
noncomputable def pBot (p : V) : V := ppair 3 p + 1
noncomputable def pSim (p q : V) : V := ppair 4 (ppair p q) + 1
noncomputable def pIte (b a p q : V) : V := ppair 5 (ppair b (ppair a (ppair p q))) + 1
noncomputable def pSearch (k g p q : V) : V := ppair 6 (ppair k (ppair g (ppair p q))) + 1

section graphs

def pConstGraph : 𝚺₀.Semisentence 2 := .mkSigma “y a. ∃ y' < y, !ppairDef y' 0 a ∧ y = y' + 1”
instance pConst.defined : 𝚺₀-Function₁[V] pConst via pConstGraph := .mk fun v ↦ by
  simp_all [pConstGraph, pConst]

def pSelfGraph : 𝚺₀.Semisentence 1 := .mkSigma “y. ∃ y' < y, !ppairDef y' 1 0 ∧ y = y' + 1”
def pOppGraph : 𝚺₀.Semisentence 1 := .mkSigma “y. ∃ y' < y, !ppairDef y' 2 0 ∧ y = y' + 1”

def pBotGraph : 𝚺₀.Semisentence 2 := .mkSigma “y p. ∃ y' < y, !ppairDef y' 3 p ∧ y = y' + 1”
instance pBot.defined : 𝚺₀-Function₁[V] pBot via pBotGraph := .mk fun v ↦ by
  simp_all [pBotGraph, pBot]

def pSimGraph : 𝚺₀.Semisentence 3 :=
  .mkSigma “y p q. ∃ y' < y, ∃ pq <⁺ y', !ppairDef pq p q ∧ !ppairDef y' 4 pq ∧ y = y' + 1”
instance pSim.defined : 𝚺₀-Function₂[V] pSim via pSimGraph := .mk fun v ↦ by
  simp_all [pSimGraph, pSim]

def pIteGraph : 𝚺₀.Semisentence 5 :=
  .mkSigma “y b a p q. ∃ y' < y, ∃ bapq <⁺ y', ∃ apq <⁺ bapq, ∃ pq <⁺ apq,
    !ppairDef pq p q ∧ !ppairDef apq a pq ∧ !ppairDef bapq b apq ∧ !ppairDef y' 5 bapq ∧ y = y' + 1”
instance pIte.defined : 𝚺₀-Function₄ (pIte : V → V → V → V → V) via pIteGraph := .mk fun v ↦ by
  simp_all [pIteGraph, numeral_eq_natCast, pIte]

def pSearchGraph : 𝚺₀.Semisentence 5 :=
  .mkSigma “y k g p q. ∃ y' < y, ∃ kgpq <⁺ y', ∃ gpq <⁺ kgpq, ∃ pq <⁺ gpq,
    !ppairDef pq p q ∧ !ppairDef gpq g pq ∧ !ppairDef kgpq k gpq ∧ !ppairDef y' 6 kgpq ∧ y = y' + 1”
instance pSearch.defined : 𝚺₀-Function₄ (pSearch : V → V → V → V → V) via pSearchGraph :=
  .mk fun v ↦ by simp_all [pSearchGraph, numeral_eq_natCast, pSearch]

end graphs

/-! ### Size facts (sub-programs are smaller than their parent) -/

@[simp] lemma p_lt_pBot (p : V) : p < pBot p :=
  le_iff_lt_succ.mp (le_ppair_right _ _)
@[simp] lemma p_lt_pSim (p q : V) : p < pSim p q :=
  le_iff_lt_succ.mp <| le_trans (le_ppair_left _ _) (le_ppair_right _ _)
@[simp] lemma q_lt_pSim (p q : V) : q < pSim p q :=
  le_iff_lt_succ.mp <| le_trans (le_ppair_right _ _) (le_ppair_right _ _)
@[simp] lemma b_lt_pIte (b a p q : V) : b < pIte b a p q :=
  le_iff_lt_succ.mp <| le_trans (le_ppair_left _ _) (le_ppair_right _ _)
@[simp] lemma p_lt_pIte (b a p q : V) : p < pIte b a p q :=
  le_iff_lt_succ.mp <| le_trans (le_trans (le_trans (le_ppair_left _ _) (le_ppair_right _ _))
    (le_ppair_right _ _)) (le_ppair_right _ _)
@[simp] lemma q_lt_pIte (b a p q : V) : q < pIte b a p q :=
  le_iff_lt_succ.mp <| le_trans (le_trans (le_trans (le_ppair_right _ _) (le_ppair_right _ _))
    (le_ppair_right _ _)) (le_ppair_right _ _)
@[simp] lemma p_lt_pSearch (k g p q : V) : p < pSearch k g p q :=
  le_iff_lt_succ.mp <| le_trans (le_trans (le_trans (le_ppair_left _ _) (le_ppair_right _ _))
    (le_ppair_right _ _)) (le_ppair_right _ _)
@[simp] lemma q_lt_pSearch (k g p q : V) : q < pSearch k g p q :=
  le_iff_lt_succ.mp <| le_trans (le_trans (le_trans (le_ppair_right _ _) (le_ppair_right _ _))
    (le_ppair_right _ _)) (le_ppair_right _ _)

/-! ### Injectivity and disjointness of the constructors (the tag decides the shape) -/

section inj

attribute [local simp] pConst pSelf pOpp pBot pSim pIte pSearch

lemma pConst_inj {a a' : V} (h : pConst a = pConst a') : a = a' := by simpa using h
lemma pBot_inj {p p' : V} (h : pBot p = pBot p') : p = p' := by simpa using h
lemma pSim_inj {p q p' q' : V} (h : pSim p q = pSim p' q') : p = p' ∧ q = q' := by simpa using h
lemma pIte_inj {b a p q b' a' p' q' : V} (h : pIte b a p q = pIte b' a' p' q') :
    b = b' ∧ a = a' ∧ p = p' ∧ q = q' := by simpa [and_assoc] using h
lemma pSearch_inj {k g p q k' g' p' q' : V} (h : pSearch k g p q = pSearch k' g' p' q') :
    k = k' ∧ g = g' ∧ p = p' ∧ q = q' := by simpa [and_assoc] using h

end inj

/-! ### Re-valuing actions -/

/-- `0 ↦ u`, `1 ↦ w`, other values fixed. -/
noncomputable def relabelAct (a u w : V) : V := if a = 0 then u else if a = 1 then w else a

def relabelActGraph : 𝚺₀.Semisentence 4 :=
  .mkSigma “y a u w. (a = 0 → y = u) ∧ (a = 1 → y = w) ∧ (a ≠ 0 → a ≠ 1 → y = a)”

instance relabelAct.defined : 𝚺₀-Function₃ (relabelAct : V → V → V → V) via relabelActGraph :=
  .mk fun v ↦ by
    suffices (v 1 = 0 → v 0 = v 2) ∧ (v 1 = 1 → v 0 = v 3) ∧ (v 1 ≠ 0 → v 1 ≠ 1 → v 0 = v 1) ↔
        v 0 = relabelAct (v 1) (v 2) (v 3) by simpa [relabelActGraph]
    unfold relabelAct
    by_cases h0 : v 1 = 0
    · simp [h0]
    · by_cases h1 : v 1 = 1
      · simp [h0, h1]
      · simp [h0, h1]

/-- The action swap. -/
noncomputable abbrev swapAct (a : V) : V := relabelAct a 1 0

lemma relabelAct_le (a u w : V) : relabelAct a u w ≤ a + u + w := by
  unfold relabelAct
  by_cases h0 : a = 0
  · simp [h0]
  · by_cases h1 : a = 1
    · simp [h1]
    · simp [h0, h1]

@[simp] lemma relabelAct_zero_one (a : V) : relabelAct a 0 1 = a := by
  unfold relabelAct
  by_cases h0 : a = 0
  · simp [h0]
  · by_cases h1 : a = 1
    · simp [h0, h1]
    · simp [h0, h1]

@[simp] lemma swapAct_swapAct (a : V) : swapAct (swapAct a) = a := by
  unfold swapAct relabelAct
  by_cases h0 : a = 0
  · simp [h0]
  · by_cases h1 : a = 1
    · simp [h0, h1]
    · simp [h0, h1]

/-! ### Program shapes -/

/-- `x` is a constructor application (its immediate components are all `< x`). -/
def IsShape (x : V) : Prop :=
  (∃ a, x = pConst a) ∨ x = pSelf ∨ x = pOpp ∨ (∃ p, x = pBot p) ∨ (∃ p q, x = pSim p q) ∨
  (∃ b a p q, x = pIte b a p q) ∨ (∃ k g p q, x = pSearch k g p q)

def isShape : 𝚺₀.Semisentence 1 := .mkSigma
  “x. (∃ a < x, !pConstGraph x a) ∨ !pSelfGraph x ∨ !pOppGraph x ∨ (∃ p < x, !pBotGraph x p) ∨
    (∃ p < x, ∃ q < x, !pSimGraph x p q) ∨ (∃ b < x, ∃ a < x, ∃ p < x, ∃ q < x, !pIteGraph x b a p q) ∨
    (∃ k < x, ∃ g < x, ∃ p < x, ∃ q < x, !pSearchGraph x k g p q)”

@[simp] lemma a_lt_pConst (a : V) : a < pConst a := le_iff_lt_succ.mp (le_ppair_right _ _)
@[simp] lemma a_lt_pIte (b a p q : V) : a < pIte b a p q :=
  le_iff_lt_succ.mp <| le_trans (le_trans (le_ppair_left _ _) (le_ppair_right _ _)) (le_ppair_right _ _)
@[simp] lemma k_lt_pSearch (k g p q : V) : k < pSearch k g p q :=
  le_iff_lt_succ.mp <| le_trans (le_ppair_left _ _) (le_ppair_right _ _)
@[simp] lemma g_lt_pSearch (k g p q : V) : g < pSearch k g p q :=
  le_iff_lt_succ.mp <| le_trans (le_trans (le_ppair_left _ _) (le_ppair_right _ _)) (le_ppair_right _ _)

lemma isShape_iff (x : V) :
    IsShape x ↔
    (∃ a < x, x = pConst a) ∨ x = pSelf ∨ x = pOpp ∨ (∃ p < x, x = pBot p) ∨
    (∃ p < x, ∃ q < x, x = pSim p q) ∨ (∃ b < x, ∃ a < x, ∃ p < x, ∃ q < x, x = pIte b a p q) ∨
    (∃ k < x, ∃ g < x, ∃ p < x, ∃ q < x, x = pSearch k g p q) := by
  constructor
  · rintro (⟨a, rfl⟩ | rfl | rfl | ⟨p, rfl⟩ | ⟨p, q, rfl⟩ | ⟨b, a, p, q, rfl⟩ | ⟨k, g, p, q, rfl⟩)
    · exact Or.inl ⟨a, by simp, rfl⟩
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨p, by simp, rfl⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, by simp, q, by simp, rfl⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨b, by simp, a, by simp, p, by simp, q, by simp, rfl⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨k, by simp, g, by simp, p, by simp, q, by simp, rfl⟩)))))
  · rintro (⟨a, _, rfl⟩ | rfl | rfl | ⟨p, _, rfl⟩ | ⟨p, _, q, _, rfl⟩ |
      ⟨b, _, a, _, p, _, q, _, rfl⟩ | ⟨k, _, g, _, p, _, q, _, rfl⟩)
    · exact Or.inl ⟨a, rfl⟩
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨p, rfl⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, q, rfl⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨b, a, p, q, rfl⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨k, g, p, q, rfl⟩)))))

lemma lt_and_eq_succ_iff {a y : V} : (a < y ∧ y = a + 1) ↔ y = a + 1 :=
  ⟨And.right, fun h ↦ ⟨by rw [h]; exact lt_add_one a, h⟩⟩

instance IsShape.defined : 𝚺₀-Predicate[V] IsShape via isShape := .mk fun v ↦ by
  simp [isShape, isShape_iff, pSelfGraph, pOppGraph, pSelf, pOpp, lt_and_eq_succ_iff]

instance IsShape.definable : 𝚺₀-Predicate[V] IsShape := IsShape.defined.to_definable

instance IsShape.definable' (Γ m) : Γ-[m]-Predicate[V] IsShape :=
  HierarchySymbol.Definable.of_zero IsShape.definable

/-! ### Re-valuing every action of a program: a fixpoint on pairs `⟪x, y⟫` with parameters `u w`

The search clause re-values the stored template through `relabelTemplate u w` (a Σ₁
function), so the core is Δ₁ (both polarities cite `relabelTemplateGraph`, exactly like the
guard code in `ArithS.Eval`) rather than Δ₀; the fixpoint is still StrongFinite, since the
sub-results referenced are `⟪p, p'⟫` with `p < x` and `p' < y`. -/

namespace Relabel

/-- `Phi ![u, w] C ⟪x, y⟫`: `y` is `x` with actions re-valued `0 ↦ u, 1 ↦ w`, given the
sub-results in `C`. -/
def Phi (param : Fin 2 → V) (C : Set V) (pr : V) : Prop :=
  (∃ a, pr = ⟪pConst a, pConst (relabelAct a (param 0) (param 1))⟫) ∨
  pr = ⟪pSelf, pSelf⟫ ∨ pr = ⟪pOpp, pOpp⟫ ∨
  (∃ p p', ⟪p, p'⟫ ∈ C ∧ pr = ⟪pBot p, pBot p'⟫) ∨
  (∃ p q p' q', ⟪p, p'⟫ ∈ C ∧ ⟪q, q'⟫ ∈ C ∧ pr = ⟪pSim p q, pSim p' q'⟫) ∨
  (∃ b a p q b' p' q', ⟪b, b'⟫ ∈ C ∧ ⟪p, p'⟫ ∈ C ∧ ⟪q, q'⟫ ∈ C ∧
    pr = ⟪pIte b a p q, pIte b' (relabelAct a (param 0) (param 1)) p' q'⟫) ∨
  (∃ k g p q p' q', ⟪p, p'⟫ ∈ C ∧ ⟪q, q'⟫ ∈ C ∧
    pr = ⟪pSearch k g p q, pSearch k (relabelTemplate (param 0) (param 1) g) p' q'⟫) ∨
  (∃ x, ¬IsShape x ∧ pr = ⟪x, x⟫)

noncomputable def blueprint : Fixpoint.Blueprint 2 := ⟨.mkDelta
  (.mkSigma “pr C u w. ∃ x <⁺ pr, ∃ y <⁺ pr, !pairDef pr x y ∧
    ( (∃ a < x, !pConstGraph x a ∧ ∃ a' <⁺ a + u + w, !relabelActGraph a' a u w ∧ !pConstGraph y a') ∨
      (!pSelfGraph x ∧ !pSelfGraph y) ∨
      (!pOppGraph x ∧ !pOppGraph y) ∨
      (∃ p < x, !pBotGraph x p ∧ ∃ p' < y, :⟪p, p'⟫:∈ C ∧ !pBotGraph y p') ∨
      (∃ p < x, ∃ q < x, !pSimGraph x p q ∧
        ∃ p' < y, ∃ q' < y, :⟪p, p'⟫:∈ C ∧ :⟪q, q'⟫:∈ C ∧ !pSimGraph y p' q') ∨
      (∃ b < x, ∃ a < x, ∃ p < x, ∃ q < x, !pIteGraph x b a p q ∧
        ∃ b' < y, ∃ a' <⁺ a + u + w, ∃ p' < y, ∃ q' < y,
          :⟪b, b'⟫:∈ C ∧ :⟪p, p'⟫:∈ C ∧ :⟪q, q'⟫:∈ C ∧ !relabelActGraph a' a u w ∧ !pIteGraph y b' a' p' q') ∨
      (∃ k < x, ∃ g < x, ∃ p < x, ∃ q < x, !pSearchGraph x k g p q ∧
        ∃ g', !relabelTemplateGraph g' u w g ∧ ∃ p' < y, ∃ q' < y,
          :⟪p, p'⟫:∈ C ∧ :⟪q, q'⟫:∈ C ∧ !pSearchGraph y k g' p' q') ∨
      (¬!isShape x ∧ y = x) )”)
  (.mkPi “pr C u w. ∃ x <⁺ pr, ∃ y <⁺ pr, !pairDef pr x y ∧
    ( (∃ a < x, !pConstGraph x a ∧ ∃ a' <⁺ a + u + w, !relabelActGraph a' a u w ∧ !pConstGraph y a') ∨
      (!pSelfGraph x ∧ !pSelfGraph y) ∨
      (!pOppGraph x ∧ !pOppGraph y) ∨
      (∃ p < x, !pBotGraph x p ∧ ∃ p' < y, :⟪p, p'⟫:∈ C ∧ !pBotGraph y p') ∨
      (∃ p < x, ∃ q < x, !pSimGraph x p q ∧
        ∃ p' < y, ∃ q' < y, :⟪p, p'⟫:∈ C ∧ :⟪q, q'⟫:∈ C ∧ !pSimGraph y p' q') ∨
      (∃ b < x, ∃ a < x, ∃ p < x, ∃ q < x, !pIteGraph x b a p q ∧
        ∃ b' < y, ∃ a' <⁺ a + u + w, ∃ p' < y, ∃ q' < y,
          :⟪b, b'⟫:∈ C ∧ :⟪p, p'⟫:∈ C ∧ :⟪q, q'⟫:∈ C ∧ !relabelActGraph a' a u w ∧ !pIteGraph y b' a' p' q') ∨
      (∃ k < x, ∃ g < x, ∃ p < x, ∃ q < x, !pSearchGraph x k g p q ∧
        ∀ g', !relabelTemplateGraph g' u w g → ∃ p' < y, ∃ q' < y,
          :⟪p, p'⟫:∈ C ∧ :⟪q, q'⟫:∈ C ∧ !pSearchGraph y k g' p' q') ∨
      (¬!isShape x ∧ y = x) )”)⟩

private lemma phi_iff (param : Fin 2 → V) (C pr : V) :
    Phi param {x | x ∈ C} pr ↔
    ∃ x ≤ pr, ∃ y ≤ pr, pr = ⟪x, y⟫ ∧
    ( (∃ a < x, x = pConst a ∧ ∃ a' ≤ a + param 0 + param 1, a' = relabelAct a (param 0) (param 1) ∧ y = pConst a') ∨
      (x = pSelf ∧ y = pSelf) ∨
      (x = pOpp ∧ y = pOpp) ∨
      (∃ p < x, x = pBot p ∧ ∃ p' < y, ⟪p, p'⟫ ∈ C ∧ y = pBot p') ∨
      (∃ p < x, ∃ q < x, x = pSim p q ∧
        ∃ p' < y, ∃ q' < y, ⟪p, p'⟫ ∈ C ∧ ⟪q, q'⟫ ∈ C ∧ y = pSim p' q') ∨
      (∃ b < x, ∃ a < x, ∃ p < x, ∃ q < x, x = pIte b a p q ∧
        ∃ b' < y, ∃ a' ≤ a + param 0 + param 1, ∃ p' < y, ∃ q' < y,
          ⟪b, b'⟫ ∈ C ∧ ⟪p, p'⟫ ∈ C ∧ ⟪q, q'⟫ ∈ C ∧ a' = relabelAct a (param 0) (param 1) ∧
          y = pIte b' a' p' q') ∨
      (∃ k < x, ∃ g < x, ∃ p < x, ∃ q < x, x = pSearch k g p q ∧
        ∃ p' < y, ∃ q' < y,
          ⟪p, p'⟫ ∈ C ∧ ⟪q, q'⟫ ∈ C ∧ y = pSearch k (relabelTemplate (param 0) (param 1) g) p' q') ∨
      (¬IsShape x ∧ y = x) ) := by
  constructor
  · rintro (⟨a, rfl⟩ | rfl | rfl | ⟨p, p', h, rfl⟩ | ⟨p, q, p', q', hp, hq, rfl⟩ |
      ⟨b, a, p, q, b', p', q', hb, hp, hq, rfl⟩ | ⟨k, g, p, q, p', q', hp, hq, rfl⟩ | ⟨x, hx, rfl⟩)
    · exact ⟨_, by simp, _, by simp, rfl, Or.inl ⟨a, by simp, rfl, _, relabelAct_le _ _ _, rfl, rfl⟩⟩
    · exact ⟨_, by simp, _, by simp, rfl, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
    · exact ⟨_, by simp, _, by simp, rfl, Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩
    · exact ⟨_, by simp, _, by simp, rfl, Or.inr (Or.inr (Or.inr (Or.inl
        ⟨p, by simp, rfl, p', by simp, h, rfl⟩)))⟩
    · exact ⟨_, by simp, _, by simp, rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨p, by simp, q, by simp, rfl, p', by simp, q', by simp, hp, hq, rfl⟩))))⟩
    · exact ⟨_, by simp, _, by simp, rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨b, by simp, a, by simp, p, by simp, q, by simp, rfl, b', by simp, _, relabelAct_le _ _ _,
          p', by simp, q', by simp, hb, hp, hq, rfl, rfl⟩)))))⟩
    · exact ⟨_, by simp, _, by simp, rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨k, by simp, g, by simp, p, by simp, q, by simp, rfl,
          p', by simp, q', by simp, hp, hq, rfl⟩))))))⟩
    · exact ⟨_, by simp, _, by simp, rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨hx, rfl⟩))))))⟩
  · rintro ⟨x, _, y, _, rfl, (⟨a, _, rfl, a', _, rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨p, _, rfl, p', _, h, rfl⟩ | ⟨p, _, q, _, rfl, p', _, q', _, hp, hq, rfl⟩ |
      ⟨b, _, a, _, p, _, q, _, rfl, b', _, a', _, p', _, q', _, hb, hp, hq, rfl, rfl⟩ |
      ⟨k, _, g, _, p, _, q, _, rfl, p', _, q', _, hp, hq, rfl⟩ | ⟨hx, hyx⟩)⟩
    · exact Or.inl ⟨a, rfl⟩
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨p, p', h, rfl⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, q, p', q', hp, hq, rfl⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨b, a, p, q, b', p', q', hb, hp, hq, rfl⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨k, g, p, q, p', q', hp, hq, rfl⟩))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨x, hx, by rw [hyx]⟩))))))

noncomputable def construction : Fixpoint.Construction V blueprint where
  Φ := Phi
  defined := .mk <| by
    constructor
    · intro v
      simp [blueprint, HierarchySymbol.Semiformula.val_sigma, relabelTemplate.defined.df]
    · intro v
      symm
      simpa [blueprint, HierarchySymbol.Semiformula.val_sigma, relabelTemplate.defined.df,
        pSelfGraph, pOppGraph, pSelf, pOpp, lt_and_eq_succ_iff]
        using phi_iff (fun i ↦ v i.succ.succ) (v 1) (v 0)
  monotone := by
    rintro C C' hC param pr (⟨a, rfl⟩ | rfl | rfl | ⟨p, p', h, rfl⟩ | ⟨p, q, p', q', hp, hq, rfl⟩ |
      ⟨b, a, p, q, b', p', q', hb, hp, hq, rfl⟩ | ⟨k, g, p, q, p', q', hp, hq, rfl⟩ | ⟨x, hx, rfl⟩)
    · exact Or.inl ⟨a, rfl⟩
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨p, p', hC h, rfl⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, q, p', q', hC hp, hC hq, rfl⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨b, a, p, q, b', p', q', hC hb, hC hp, hC hq, rfl⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨k, g, p, q, p', q', hC hp, hC hq, rfl⟩))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨x, hx, rfl⟩))))))

instance : construction.StrongFinite V where
  strong_finite := by
    rintro C param pr (⟨a, rfl⟩ | rfl | rfl | ⟨p, p', h, rfl⟩ | ⟨p, q, p', q', hp, hq, rfl⟩ |
      ⟨b, a, p, q, b', p', q', hb, hp, hq, rfl⟩ | ⟨k, g, p, q, p', q', hp, hq, rfl⟩ | ⟨x, hx, rfl⟩)
    · exact Or.inl ⟨a, rfl⟩
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨p, p', ⟨h, pair_lt_pair (by simp) (by simp)⟩, rfl⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, q, p', q',
        ⟨hp, pair_lt_pair (by simp) (by simp)⟩, ⟨hq, pair_lt_pair (by simp) (by simp)⟩, rfl⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨b, a, p, q, b', p', q',
        ⟨hb, pair_lt_pair (by simp) (by simp)⟩, ⟨hp, pair_lt_pair (by simp) (by simp)⟩,
        ⟨hq, pair_lt_pair (by simp) (by simp)⟩, rfl⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨k, g, p, q, p', q',
        ⟨hp, pair_lt_pair (by simp) (by simp)⟩, ⟨hq, pair_lt_pair (by simp) (by simp)⟩, rfl⟩))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨x, hx, rfl⟩))))))

end Relabel

/-- `RelabelGraph u w x y`: `y` is `x` with actions re-valued `0 ↦ u, 1 ↦ w`. -/
def RelabelGraph (u w x y : V) : Prop := Relabel.construction.Fixpoint ![u, w] ⟪x, y⟫

noncomputable def relabelGraphDef : 𝚫₁.Semisentence 4 := .mkDelta
  (.mkSigma “u w x y. ∃ pr <⁺ (x + y + 1)², !pairDef pr x y ∧ !Relabel.blueprint.fixpointDefΔ₁.sigma pr u w”)
  (.mkPi “u w x y. ∀ pr <⁺ (x + y + 1)², !pairDef pr x y → !Relabel.blueprint.fixpointDefΔ₁.pi pr u w”)

private lemma relabel_param_eq (v : Fin 3 → V) : (fun i ↦ v i.succ) = ![v 1, v 2] := by
  funext i; fin_cases i <;> rfl

instance relabelGraph_defined : 𝚫₁-Relation₄[V] RelabelGraph via relabelGraphDef := .mk
  ⟨by intro v
      simp [relabelGraphDef, HierarchySymbol.Semiformula.val_sigma,
        Relabel.construction.fixpoint_definedΔ₁.proper.iff', Relabel.construction.fixpoint_definedΔ₁.df]
      constructor
      · rintro h x _ rfl; simpa [relabel_param_eq] using h
      · intro h; have := h ⟪v 2, v 3⟫ (by simp) rfl; simpa [relabel_param_eq] using this,
   by intro v
      simp [relabelGraphDef, HierarchySymbol.Semiformula.val_sigma,
        Relabel.construction.fixpoint_definedΔ₁.df, RelabelGraph]⟩

instance relabelGraph_definable : 𝚫₁-Relation₄[V] RelabelGraph := relabelGraph_defined.to_definable

instance relabelGraph_definable' : Γ-[m + 1]-Relation₄[V] RelabelGraph :=
  relabelGraph_definable.of_deltaOne

lemma RelabelGraph.case_iff {u w x y : V} :
    RelabelGraph u w x y ↔
    (∃ a, x = pConst a ∧ y = pConst (relabelAct a u w)) ∨
    (x = pSelf ∧ y = pSelf) ∨ (x = pOpp ∧ y = pOpp) ∨
    (∃ p p', RelabelGraph u w p p' ∧ x = pBot p ∧ y = pBot p') ∨
    (∃ p q p' q', RelabelGraph u w p p' ∧ RelabelGraph u w q q' ∧ x = pSim p q ∧ y = pSim p' q') ∨
    (∃ b a p q b' p' q', RelabelGraph u w b b' ∧ RelabelGraph u w p p' ∧ RelabelGraph u w q q' ∧
      x = pIte b a p q ∧ y = pIte b' (relabelAct a u w) p' q') ∨
    (∃ k g p q p' q', RelabelGraph u w p p' ∧ RelabelGraph u w q q' ∧
      x = pSearch k g p q ∧ y = pSearch k (relabelTemplate u w g) p' q') ∨
    (¬IsShape y ∧ x = y) :=
  Iff.trans Relabel.construction.case (by simp [Relabel.construction, Relabel.Phi, RelabelGraph])

section inversion

attribute [local simp] pConst pSelf pOpp pBot pSim pIte pSearch IsShape

lemma RelabelGraph.const_iff {u w a y : V} :
    RelabelGraph u w (pConst a) y ↔ y = pConst (relabelAct a u w) := by
  rw [RelabelGraph.case_iff]; simp
  intro h₀ _ _ _ _ _ _ h; exact absurd h.symm (h₀ a)
lemma RelabelGraph.self_iff {u w y : V} : RelabelGraph u w pSelf y ↔ y = pSelf := by
  rw [RelabelGraph.case_iff]; simp
  intro _ h₁ _ _ _ _ _ h; exact absurd h.symm h₁
lemma RelabelGraph.opp_iff {u w y : V} : RelabelGraph u w pOpp y ↔ y = pOpp := by
  rw [RelabelGraph.case_iff]; simp
  intro _ _ h₂ _ _ _ _ h; exact absurd h.symm h₂
lemma RelabelGraph.bot_iff {u w p y : V} :
    RelabelGraph u w (pBot p) y ↔ ∃ p', RelabelGraph u w p p' ∧ y = pBot p' := by
  rw [RelabelGraph.case_iff]; simp
  intro _ _ _ h₃ _ _ _ h; exact absurd h.symm (h₃ p)
lemma RelabelGraph.sim_iff {u w p q y : V} :
    RelabelGraph u w (pSim p q) y ↔
    ∃ p' q', RelabelGraph u w p p' ∧ RelabelGraph u w q q' ∧ y = pSim p' q' := by
  rw [RelabelGraph.case_iff]; simp
  intro _ _ _ _ h₄ _ _ h; exact absurd h.symm (h₄ p q)
lemma RelabelGraph.ite_iff {u w b a p q y : V} :
    RelabelGraph u w (pIte b a p q) y ↔
    ∃ b' p' q', RelabelGraph u w b b' ∧ RelabelGraph u w p p' ∧ RelabelGraph u w q q' ∧
      y = pIte b' (relabelAct a u w) p' q' := by
  rw [RelabelGraph.case_iff]; simp
  intro _ _ _ _ _ h₅ _ h; exact absurd h.symm (h₅ b a p q)
lemma RelabelGraph.search_iff {u w k g p q y : V} :
    RelabelGraph u w (pSearch k g p q) y ↔
    ∃ p' q', RelabelGraph u w p p' ∧ RelabelGraph u w q q' ∧ y = pSearch k (relabelTemplate u w g) p' q' := by
  rw [RelabelGraph.case_iff]; simp
  intro _ _ _ _ _ _ h₆ h; exact absurd h.symm (h₆ k g p q)
lemma RelabelGraph.of_not_shape {u w x y : V} (hx : ¬IsShape x) : RelabelGraph u w x y ↔ y = x := by
  rw [RelabelGraph.case_iff]
  constructor
  · rintro (⟨a, rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨p, p', _, rfl, _⟩ | ⟨p, q, p', q', _, _, rfl, _⟩ |
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

/-! ### `relabel` is a total Σ₁ function -/

lemma relabelGraph_exists (u w x : V) : ∃ y, RelabelGraph u w x y := by
  induction x using ISigma1.sigma1_order_induction with
  | hP => definability
  | ind x ih =>
    by_cases hx : IsShape x
    · rcases hx with ⟨a, rfl⟩ | rfl | rfl | ⟨p, rfl⟩ | ⟨p, q, rfl⟩ | ⟨b, a, p, q, rfl⟩ | ⟨k, g, p, q, rfl⟩
      · exact ⟨_, RelabelGraph.const_iff.mpr rfl⟩
      · exact ⟨_, RelabelGraph.self_iff.mpr rfl⟩
      · exact ⟨_, RelabelGraph.opp_iff.mpr rfl⟩
      · obtain ⟨p', hp⟩ := ih p (by simp)
        exact ⟨_, RelabelGraph.bot_iff.mpr ⟨p', hp, rfl⟩⟩
      · obtain ⟨p', hp⟩ := ih p (by simp); obtain ⟨q', hq⟩ := ih q (by simp)
        exact ⟨_, RelabelGraph.sim_iff.mpr ⟨p', q', hp, hq, rfl⟩⟩
      · obtain ⟨b', hb⟩ := ih b (by simp); obtain ⟨p', hp⟩ := ih p (by simp)
        obtain ⟨q', hq⟩ := ih q (by simp)
        exact ⟨_, RelabelGraph.ite_iff.mpr ⟨b', p', q', hb, hp, hq, rfl⟩⟩
      · obtain ⟨p', hp⟩ := ih p (by simp); obtain ⟨q', hq⟩ := ih q (by simp)
        exact ⟨_, RelabelGraph.search_iff.mpr ⟨p', q', hp, hq, rfl⟩⟩
    · exact ⟨x, (RelabelGraph.of_not_shape hx).mpr rfl⟩

lemma relabelGraph_unique (u w x : V) :
    ∀ y₁ y₂, RelabelGraph u w x y₁ → RelabelGraph u w x y₂ → y₁ = y₂ := by
  induction x using ISigma1.pi1_order_induction with
  | hP => definability
  | ind x ih =>
    intro y₁ y₂ h₁ h₂
    by_cases hx : IsShape x
    · rcases hx with ⟨a, rfl⟩ | rfl | rfl | ⟨p, rfl⟩ | ⟨p, q, rfl⟩ | ⟨b, a, p, q, rfl⟩ | ⟨k, g, p, q, rfl⟩
      · rw [RelabelGraph.const_iff] at h₁ h₂; rw [h₁, h₂]
      · rw [RelabelGraph.self_iff] at h₁ h₂; rw [h₁, h₂]
      · rw [RelabelGraph.opp_iff] at h₁ h₂; rw [h₁, h₂]
      · rcases RelabelGraph.bot_iff.mp h₁ with ⟨p₁, hp₁, rfl⟩
        rcases RelabelGraph.bot_iff.mp h₂ with ⟨p₂, hp₂, rfl⟩
        rw [ih p (by simp) _ _ hp₁ hp₂]
      · rcases RelabelGraph.sim_iff.mp h₁ with ⟨p₁, q₁, hp₁, hq₁, rfl⟩
        rcases RelabelGraph.sim_iff.mp h₂ with ⟨p₂, q₂, hp₂, hq₂, rfl⟩
        rw [ih p (by simp) _ _ hp₁ hp₂, ih q (by simp) _ _ hq₁ hq₂]
      · rcases RelabelGraph.ite_iff.mp h₁ with ⟨b₁, p₁, q₁, hb₁, hp₁, hq₁, rfl⟩
        rcases RelabelGraph.ite_iff.mp h₂ with ⟨b₂, p₂, q₂, hb₂, hp₂, hq₂, rfl⟩
        rw [ih b (by simp) _ _ hb₁ hb₂, ih p (by simp) _ _ hp₁ hp₂, ih q (by simp) _ _ hq₁ hq₂]
      · rcases RelabelGraph.search_iff.mp h₁ with ⟨p₁, q₁, hp₁, hq₁, rfl⟩
        rcases RelabelGraph.search_iff.mp h₂ with ⟨p₂, q₂, hp₂, hq₂, rfl⟩
        rw [ih p (by simp) _ _ hp₁ hp₂, ih q (by simp) _ _ hq₁ hq₂]
    · rw [RelabelGraph.of_not_shape hx] at h₁ h₂; rw [h₁, h₂]

lemma relabelGraph_existsUnique (u w x : V) : ∃! y, RelabelGraph u w x y := by
  rcases relabelGraph_exists u w x with ⟨y, hy⟩
  exact ExistsUnique.intro y hy (fun y' h' ↦ relabelGraph_unique u w x y' y h' hy)

/-- Re-value every action of a program: `0 ↦ u`, `1 ↦ w`. -/
noncomputable def relabel (u w x : V) : V := Classical.choose! (relabelGraph_existsUnique u w x)

lemma relabel_graph (u w x : V) : RelabelGraph u w x (relabel u w x) :=
  Classical.choose!_spec (relabelGraph_existsUnique u w x)

lemma relabel_eq_of_graph {u w x y : V} (h : RelabelGraph u w x y) : relabel u w x = y :=
  relabelGraph_unique u w x _ _ (relabel_graph u w x) h

noncomputable def relabelDef : 𝚺₁.Semisentence 4 := .mkSigma “y u w x. !relabelGraphDef.sigma u w x y”

instance relabel_defined : 𝚺₁-Function₃ (relabel : V → V → V → V) via relabelDef := .mk fun v ↦ by
  simp [relabelDef, HierarchySymbol.Semiformula.val_sigma, relabelGraph_defined.df]
  constructor
  · intro h; exact (relabel_eq_of_graph h).symm
  · intro h; rw [h]; exact relabel_graph _ _ _

instance relabel_definable : 𝚺₁-Function₃ (relabel : V → V → V → V) := relabel_defined.to_definable

instance relabel_definable' : Γ-[m + 1]-Function₃ (relabel : V → V → V → V) :=
  relabel_definable.of_sigmaOne

@[simp] lemma relabel_const (u w a : V) : relabel u w (pConst a) = pConst (relabelAct a u w) :=
  relabel_eq_of_graph (RelabelGraph.const_iff.mpr rfl)
@[simp] lemma relabel_self (u w : V) : relabel u w (pSelf : V) = pSelf :=
  relabel_eq_of_graph (RelabelGraph.self_iff.mpr rfl)
@[simp] lemma relabel_opp (u w : V) : relabel u w (pOpp : V) = pOpp :=
  relabel_eq_of_graph (RelabelGraph.opp_iff.mpr rfl)
@[simp] lemma relabel_bot (u w p : V) : relabel u w (pBot p) = pBot (relabel u w p) :=
  relabel_eq_of_graph (RelabelGraph.bot_iff.mpr ⟨_, relabel_graph u w p, rfl⟩)
@[simp] lemma relabel_sim (u w p q : V) :
    relabel u w (pSim p q) = pSim (relabel u w p) (relabel u w q) :=
  relabel_eq_of_graph (RelabelGraph.sim_iff.mpr ⟨_, _, relabel_graph u w p, relabel_graph u w q, rfl⟩)
@[simp] lemma relabel_ite (u w b a p q : V) :
    relabel u w (pIte b a p q) = pIte (relabel u w b) (relabelAct a u w) (relabel u w p) (relabel u w q) :=
  relabel_eq_of_graph (RelabelGraph.ite_iff.mpr
    ⟨_, _, _, relabel_graph u w b, relabel_graph u w p, relabel_graph u w q, rfl⟩)
@[simp] lemma relabel_search (u w k g p q : V) :
    relabel u w (pSearch k g p q) = pSearch k (relabelTemplate u w g) (relabel u w p) (relabel u w q) :=
  relabel_eq_of_graph (RelabelGraph.search_iff.mpr
    ⟨_, _, relabel_graph u w p, relabel_graph u w q, rfl⟩)
lemma relabel_of_not_shape {u w x : V} (hx : ¬IsShape x) : relabel u w x = x :=
  relabel_eq_of_graph ((RelabelGraph.of_not_shape hx).mpr rfl)

/-- Re-valuing with `(0, 1)` is the identity. -/
theorem relabel_zero_one (x : V) : relabel 0 1 x = x := by
  induction x using ISigma1.pi1_order_induction with
  | hP => definability
  | ind x ih =>
    by_cases hx : IsShape x
    · rcases hx with ⟨a, rfl⟩ | rfl | rfl | ⟨p, rfl⟩ | ⟨p, q, rfl⟩ | ⟨b, a, p, q, rfl⟩ | ⟨k, g, p, q, rfl⟩
      · simp
      · simp
      · simp
      · simp [ih p (by simp)]
      · simp [ih p (by simp), ih q (by simp)]
      · simp [ih b (by simp), ih p (by simp), ih q (by simp)]
      · simp [ih p (by simp), ih q (by simp), relabelTemplate_zero_one]
    · rw [relabel_of_not_shape hx]

/-- The action swap on program codes: re-value with `(1, 0)`. -/
noncomputable abbrev swapcode (x : V) : V := relabel 1 0 x

/-- τ is an involution on codes. -/
theorem swapcode_swapcode (x : V) : swapcode (swapcode x) = x := by
  induction x using ISigma1.pi1_order_induction with
  | hP => definability
  | ind x ih =>
    by_cases hx : IsShape x
    · rcases hx with ⟨a, rfl⟩ | rfl | rfl | ⟨p, rfl⟩ | ⟨p, q, rfl⟩ | ⟨b, a, p, q, rfl⟩ | ⟨k, g, p, q, rfl⟩
      · simp [swapcode]
      · simp [swapcode]
      · simp [swapcode]
      · simp [swapcode, ih p (by simp)]
      · simp [swapcode, ih p (by simp), ih q (by simp)]
      · simp [swapcode, ih b (by simp), ih p (by simp), ih q (by simp)]
      · simp [swapcode, ih p (by simp), ih q (by simp), relabelTemplate_swap_swap]
    · simp only [swapcode]; rw [relabel_of_not_shape hx, relabel_of_not_shape hx]

end ArithS
