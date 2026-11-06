import ArithS.Cells.PrudentMirror

/-!
# ArithS.Tau.Entangled.Order — the τ-order of a two-member system is `k`-uniform above a threshold

A system member's description (`descriptionsSys`, `Agents/Guard.lean`) is the CANONICAL code of `pSys d j`
— `min(x, transposeCode x)` — so a Löb family on the member slots needs to know, uniformly in the budget `k`
(in every model), which of the system and its transposition is the smaller. Both are
`pSys (pCons m₀ (pCons m₁ 0)) j` with members `mᵢ = ppair 6 (ppair k Iᵢ) + 1` (`Iᵢ` the budget-free inner part
of a simple searcher). The comparison is NOT lexicographic (`ppair x y = (x + y)² + y`), but it is decided
by the second member for all large `k`: raising `m₁` by one raises the list code by at least `2 m₁² + 22`
(`sys2_lt_of_member1`), and the first member is at most `72 k⁴ ≤ 2 m₁²` once `k ≥ 3` dominates its inner
part (`simple_le_bound`, `member1_dominates`). When the second member is τ-FIXED (the mirror member), the
first member decides outright (`sys2_lt_of_member0`). Pure `V`-arithmetic (`omega` is useless here; the
chains are `gcongr`/`mul_le_mul`).
-/

namespace ArithS.Tau

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1
open LAct

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ### 1. The order through the wrappers -/

lemma ppair_lt_ppair_left_iff {x₁ x₂ : V} (y : V) : ppair x₁ y < ppair x₂ y ↔ x₁ < x₂ := by
  constructor
  · intro h
    rcases lt_trichotomy x₁ x₂ with h' | rfl | h'
    · exact h'
    · exact absurd h (_root_.lt_irrefl _)
    · exact absurd (lt_trans h (ppair_lt_ppair_left h' y)) (_root_.lt_irrefl _)
  · exact fun h ↦ ppair_lt_ppair_left h y

lemma pSys_lt_pSys_iff {d d' j : V} : pSys d j < pSys d' j ↔ d < d' := by
  unfold pSys
  rw [add_lt_add_iff_right, ppair_lt_ppair_right_iff, ppair_lt_ppair_left_iff]

lemma pCons_lt_pCons_iff {x r x' r' : V} : pCons x r < pCons x' r' ↔ ppair x r < ppair x' r' := by
  unfold pCons
  rw [add_lt_add_iff_right, ppair_lt_ppair_right_iff]

lemma ppair_zero_right (m : V) : ppair m 0 = m * m := by unfold ppair; simp

/-- **The second member decides**: `m₁ + 1 ≤ m₁'` and `m₀ ≤ 2 m₁² + 21` put the system below its rival. -/
theorem sys2_lt_of_member1 {m₀ m₀' m₁ m₁' j : V} (h1 : m₁ + 1 ≤ m₁') (h0 : m₀ ≤ 2 * (m₁ * m₁) + 21) :
    pSys (pCons m₀ (pCons m₁ pNil)) j < pSys (pCons m₀' (pCons m₁' pNil)) j := by
  rw [pSys_lt_pSys_iff, pCons_lt_pCons_iff]
  apply ppair_lt_of_add_lt
  -- `R' ≥ R + 2 m₁² + 22` where `R = pCons m₁ 0 = ppair 10 (m₁²) + 1`
  have hsq : m₁ * m₁ + 1 ≤ m₁' * m₁' := by
    have h2 : (m₁ + 1) * (m₁ + 1) ≤ m₁' * m₁' := mul_le_mul h1 h1 (by simp) (by simp)
    refine le_trans ?_ h2
    calc m₁ * m₁ + 1 ≤ m₁ * m₁ + (2 * m₁ + 1) := add_le_add le_rfl le_add_self
      _ = (m₁ + 1) * (m₁ + 1) := by ring
  have hR : ppair 10 (m₁ * m₁) + (2 * (10 + m₁ * m₁) + 2) ≤ ppair 10 (m₁' * m₁') :=
    ppair_add_le_of_succ_le 10 hsq
  show m₀ + pCons m₁ pNil < m₀' + pCons m₁' pNil
  unfold pCons pNil
  rw [ppair_zero_right, ppair_zero_right]
  calc m₀ + (ppair 10 (m₁ * m₁) + 1)
      ≤ 2 * (m₁ * m₁) + 21 + (ppair 10 (m₁ * m₁) + 1) := add_le_add h0 le_rfl
    _ < 2 * (m₁ * m₁) + 21 + (ppair 10 (m₁ * m₁) + 1) + 1 := lt_add_one _
    _ = ppair 10 (m₁ * m₁) + (2 * (10 + m₁ * m₁) + 2) + 1 := by ring
    _ ≤ ppair 10 (m₁' * m₁') + 1 := add_le_add hR le_rfl
    _ ≤ m₀' + (ppair 10 (m₁' * m₁') + 1) := le_add_self

/-- **The first member decides when the second is shared** (a τ-fixed partner). -/
theorem sys2_lt_of_member0 {m₀ m₀' m₁ j : V} (h0 : m₀ < m₀') :
    pSys (pCons m₀ (pCons m₁ pNil)) j < pSys (pCons m₀' (pCons m₁ pNil)) j := by
  rw [pSys_lt_pSys_iff, pCons_lt_pCons_iff]
  exact ppair_lt_ppair_left h0 _

/-! ### 2. The bounds on a simple member `ppair 6 (ppair k I) + 1` -/

lemma sq_le_sq_of_le {a b : V} (h : a ≤ b) : a * a ≤ b * b := mul_le_mul h h (by simp) (by simp)

/-- A simple member is at least `k⁴`. -/
lemma simple_ge_k4 (k I : V) : k * k * (k * k) ≤ ppair 6 (ppair k I) + 1 := by
  have h1 : k * k ≤ ppair k I := by
    refine le_trans ?_ (le_ppair_left_sq k I)
    exact sq_le_sq_of_le le_self_add
  have h2 : ppair k I * ppair k I ≤ ppair 6 (ppair k I) := by
    unfold ppair
    refine le_trans ?_ le_self_add
    exact sq_le_sq_of_le le_add_self
  exact le_trans (le_trans (sq_le_sq_of_le h1) h2) le_self_add
where
  le_ppair_left_sq (x y : V) : (x + y) * (x + y) ≤ ppair x y := by unfold ppair; exact le_self_add

/-- A simple member whose inner part is dominated by the budget is at most `72 k⁴` (`3 ≤ k`). -/
lemma simple_le_bound (k I : V) (hI : I ≤ k) (hk : 3 ≤ k) : ppair 6 (ppair k I) + 1 ≤ 72 * (k * k * (k * k)) := by
  have hk1 : (1 : V) ≤ k := le_trans (by norm_num) hk
  have hkk : k ≤ k * k := le_mul_self k
  have h6 : (6 : V) ≤ k * k := by
    have : (3 : V) * 3 ≤ k * k := mul_le_mul hk hk (by simp) (by simp)
    exact le_trans (by norm_num) this
  -- `x = ppair k I ≤ 5 k²`
  have hx : ppair k I ≤ 5 * (k * k) := by
    unfold ppair
    calc (k + I) * (k + I) + I ≤ (k + k) * (k + k) + k :=
          add_le_add (mul_le_mul (add_le_add le_rfl hI) (add_le_add le_rfl hI) (by simp) (by simp)) hI
      _ = 4 * (k * k) + k := by ring
      _ ≤ 4 * (k * k) + k * k := add_le_add le_rfl hkk
      _ = 5 * (k * k) := by ring
  -- `ppair 6 x + 1 ≤ 2 (6 + x)²`
  have h2 : ppair 6 (ppair k I) + 1 ≤ 2 * ((6 + ppair k I) * (6 + ppair k I)) := by
    unfold ppair
    set x := (k + I) * (k + I) + I
    have hx1 : x + 1 ≤ (6 + x) * (6 + x) := by
      calc x + 1 ≤ x + 6 := add_le_add le_rfl (by norm_num)
        _ = 6 + x := add_comm _ _
        _ ≤ (6 + x) * (6 + x) := le_mul_self _
    calc (6 + x) * (6 + x) + x + 1 = (6 + x) * (6 + x) + (x + 1) := by ring
      _ ≤ (6 + x) * (6 + x) + (6 + x) * (6 + x) := add_le_add le_rfl hx1
      _ = 2 * ((6 + x) * (6 + x)) := by ring
  -- `6 + x ≤ 6 k²`
  have h3 : 6 + ppair k I ≤ 6 * (k * k) := by
    calc 6 + ppair k I ≤ k * k + 5 * (k * k) := add_le_add h6 hx
      _ = 6 * (k * k) := by ring
  calc ppair 6 (ppair k I) + 1 ≤ 2 * ((6 + ppair k I) * (6 + ppair k I)) := h2
    _ ≤ 2 * ((6 * (k * k)) * (6 * (k * k))) := by gcongr
    _ = 72 * (k * k * (k * k)) := by ring

/-- **The first member is dominated by twice the square of the (smaller) second member** above the threshold
`max(I₀, 3) ≤ k`: `m₀ ≤ 72 k⁴ ≤ 2 (k⁴)² ≤ 2 m₁²`. -/
theorem member1_dominates (k I₀ I₁ : V) (hI : I₀ ≤ k) (hk : 3 ≤ k) :
    ppair 6 (ppair k I₀) + 1 ≤ 2 * ((ppair 6 (ppair k I₁) + 1) * (ppair 6 (ppair k I₁) + 1)) + 21 := by
  have h36 : (36 : V) ≤ k * k * (k * k) := by
    have h9 : (9 : V) ≤ k * k := le_trans (by norm_num) (mul_le_mul hk hk (by simp) (by simp))
    calc (36 : V) = 4 * 9 := by norm_num
      _ ≤ 9 * 9 := by norm_num
      _ ≤ k * k * (k * k) := mul_le_mul h9 h9 (by simp) (by simp)
  have h1 := simple_ge_k4 k I₁
  calc ppair 6 (ppair k I₀) + 1 ≤ 72 * (k * k * (k * k)) := simple_le_bound k I₀ hI hk
    _ = 2 * (36 * (k * k * (k * k))) := by ring
    _ ≤ 2 * ((k * k * (k * k)) * (k * k * (k * k))) := by gcongr
    _ ≤ 2 * ((ppair 6 (ppair k I₁) + 1) * (ppair 6 (ppair k I₁) + 1)) := by gcongr
    _ ≤ _ := le_self_add

end ArithS.Tau
