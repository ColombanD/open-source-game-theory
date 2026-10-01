import ArithS.Tau.Stored

/-!
# ArithS.Tau.Watch2 — the two-stage watch (τ(OBot)'s instance at a self-prober) as a `k̂`-tower (Phase 3e)

τ(OBot)'s instance at a self-prober `A` is a cascade of TWO run-stage watches,
`pIte (pSim (pBot S₀) (pBot S₀)) t₀ (pConst p₀) (pIte (pSim (pBot S₁) (pBot S₁)) t₁ (pConst p₁) (pConst q₁))`
with `S₀`/`S₁` the simple searchers `inst A coop`/`inst A defect` — a `W1` watch (`Tau/Watch.lean`) in the
ELSE branch of a first stage over a second simple member. Both members carry the budget, so the τ-order of the
cascade is not decided by one member outright; it is decided by the INNER watch (the deepest member) above a
standard threshold, because the pairing `ppair x y = (x + y)² + y` multiplies a gain by the value at each level:

* §1 **the gain calculus** `Gain c a a' g` (`a + c + g ≤ a'`, `c ≤ g`): through the right argument of a pairing
  the gain is multiplied by the value (`Gain.ppair_right`), likewise through the left one (`Gain.ppair_left`),
  constants on the other side may move by at most the slack `c`; the base step is `pBot` (`Gain.bot`);
* §2 the gain of a `W1` watch over its transposition (`W1.gain`) and the domination of a foreign first stage by
  the watch (`W1.sim_le_code`: `pSim (pBot S₀) (pBot S₀) ≤ W.code k` once `S₀ ≤ pBot (member)`);
* §3 **the two-stage watch `W2`**: code, transposition, the τ-order above `W2.K`, the canonical shape, the
  re-valuation terms, the tower `W2.TX` and `W2.describesBot` (the `W1` development, one level up);
* §4 the stored (budget-abstracted) description of a `W2` watch is constant above the threshold, and denotes the
  watch in every model (`W2.closedDescAt_code`, `W2.absVal_code`, `W2.absVal_tr_code` — `Tau/Stored.lean` §4 for `W2`).
-/

set_option linter.constructorNameAsVariable false

namespace ArithS.Tau

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open LAct

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ### 1. The gain calculus -/

/-- `a'` exceeds `a` by the slack `c` plus a gain `g` that is at least the slack. -/
def Gain (c a a' g : V) : Prop := a + c + g ≤ a' ∧ c ≤ g

lemma le_mul_left_of_one_le {y : V} (g : V) (hy : 1 ≤ y) : g ≤ y * g := by
  calc g = 1 * g := (one_mul g).symm
    _ ≤ y * g := mul_le_mul hy le_rfl (by simp) (by simp)

lemma le_mul_right_of_one_le {g : V} (y : V) (hg : 1 ≤ g) : y ≤ y * g := by
  calc y = y * 1 := (mul_one y).symm
    _ ≤ y * g := mul_le_mul le_rfl hg (by simp) (by simp)

namespace Gain

lemma le {c a a' g : V} (h : Gain c a a' g) : a ≤ a' :=
  le_trans (le_trans le_self_add le_self_add) h.1

lemma succ {c a a' g : V} (h : Gain c a a' g) : Gain c (a + 1) (a' + 1) g :=
  ⟨by
    calc a + 1 + c + g = a + c + g + 1 := by ring
      _ ≤ a' + 1 := add_le_add h.1 le_rfl, h.2⟩

/-- **Through the right argument of a pairing the gain is multiplied by the value**; the left argument may move
down by at most the slack. -/
theorem ppair_right {c x x' y y' g : V} (hx : x ≤ x' + c) (hy : 1 ≤ y) (h : Gain c y y' g) :
    Gain c (ppair x y) (ppair x' y') (y * g) := by
  obtain ⟨h1, h2⟩ := h
  have hs : x + y + g ≤ x' + y' := by
    calc x + y + g ≤ x' + c + y + g := add_le_add (add_le_add hx le_rfl) le_rfl
      _ = x' + (y + c + g) := by ring
      _ ≤ x' + y' := add_le_add le_rfl h1
  have hsq : (x + y + g) * (x + y + g) ≤ (x' + y') * (x' + y') := mul_le_mul hs hs (by simp) (by simp)
  refine ⟨?_, le_trans h2 (le_mul_left_of_one_le g hy)⟩
  unfold ppair
  calc (x + y) * (x + y) + y + c + y * g
      = (x + y) * (x + y) + y * g + (y + c) := by ring
    _ ≤ (x + y) * (x + y) + y * g + (2 * x * g + y * g + g * g) + (y + c + g) :=
        add_le_add le_self_add le_self_add
    _ = (x + y + g) * (x + y + g) + (y + c + g) := by ring
    _ ≤ (x' + y') * (x' + y') + y' := add_le_add hsq h1

/-- **Through the left argument**; the right argument may move down by at most the slack. -/
theorem ppair_left {c x x' y y' g : V} (hy : y ≤ y' + c) (hx : 1 ≤ x) (h : Gain c x x' g) :
    Gain c (ppair x y) (ppair x' y') (x * g) := by
  obtain ⟨h1, h2⟩ := h
  have hs : x + y + g ≤ x' + y' := by
    calc x + y + g ≤ x + (y' + c) + g := add_le_add (add_le_add le_rfl hy) le_rfl
      _ = x + c + g + y' := by ring
      _ ≤ x' + y' := add_le_add h1 le_rfl
  have hsq : (x + y + g) * (x + y + g) ≤ (x' + y') * (x' + y') := mul_le_mul hs hs (by simp) (by simp)
  have hxg : c ≤ x * g := le_trans h2 (le_mul_left_of_one_le g hx)
  have hgg : c ≤ g * g := le_trans h2 (le_mul_self g)
  refine ⟨?_, hxg⟩
  unfold ppair
  calc (x + y) * (x + y) + y + c + x * g
      ≤ (x + y) * (x + y) + (y' + c) + c + x * g :=
        add_le_add (add_le_add (add_le_add le_rfl hy) le_rfl) le_rfl
    _ = (x + y) * (x + y) + y' + x * g + c + c := by ring
    _ ≤ (x + y) * (x + y) + y' + x * g + x * g + g * g := add_le_add (add_le_add le_rfl hxg) hgg
    _ ≤ (x + y) * (x + y) + y' + x * g + x * g + g * g + 2 * y * g := le_self_add
    _ = (x + y + g) * (x + y + g) + y' := by ring
    _ ≤ (x' + y') * (x' + y') + y' := add_le_add hsq le_rfl

/-- **The base step**: a member raised by one raises its bot-wrapper by the slack plus the member. -/
theorem bot {c m m' : V} (h : m + 1 ≤ m') (hc : c ≤ m) : Gain c (pBot m) (pBot m') m := by
  refine ⟨?_, hc⟩
  have h3 := ppair_add_le_of_succ_le 3 h
  unfold pBot
  calc ppair 3 m + 1 + c + m ≤ ppair 3 m + 1 + m + m := add_le_add (add_le_add le_rfl hc) le_rfl
    _ ≤ ppair 3 m + 1 + m + m + 8 := le_self_add
    _ = ppair 3 m + (2 * (3 + m) + 2) + 1 := by ring
    _ ≤ ppair 3 m' + 1 := add_le_add h3 le_rfl

end Gain

/-! ### 2. The gain of a `W1` watch, and the domination of a foreign first stage -/

lemma pBot_le_pBot {a b : V} (h : a ≤ b) : pBot a ≤ pBot b := by
  unfold pBot; exact add_le_add (ppair_le_ppair_right 3 h) le_rfl

/-- A bot-wrapper is below the self-pair of its body (`4 ≤ β`). -/
lemma pBot_le_ppair_self {β : V} (h4 : 4 ≤ β) : pBot β ≤ ppair β β := by
  have h34 : 3 + β + 1 ≤ β + β := by
    calc 3 + β + 1 = 4 + β := by ring
      _ ≤ β + β := add_le_add h4 le_rfl
  unfold pBot ppair
  calc (3 + β) * (3 + β) + β + 1 ≤ (3 + β) * (3 + β) + β + 1 + 2 * (3 + β) := le_self_add
    _ = (3 + β + 1) * (3 + β + 1) + β := by ring
    _ ≤ (β + β) * (β + β) + β := add_le_add (mul_le_mul h34 h34 (by simp) (by simp)) le_rfl

/-- A self-pair is below any pair whose left argument is its `pSim`-wrapper. -/
lemma ppair_self_le_ppair_sim (Z C : V) : ppair Z Z ≤ ppair (ppair 4 Z + 1) C := by
  have hBZ : Z + Z + 1 ≤ ppair 4 Z + 1 := by
    unfold ppair
    calc Z + Z + 1 ≤ (4 + Z) + Z + 1 := add_le_add (add_le_add le_add_self le_rfl) le_rfl
      _ ≤ (4 + Z) * (4 + Z) + Z + 1 := add_le_add (add_le_add (le_mul_self _) le_rfl) le_rfl
  set B := ppair 4 Z + 1
  show (Z + Z) * (Z + Z) + Z ≤ (B + C) * (B + C) + C
  calc (Z + Z) * (Z + Z) + Z ≤ (Z + Z) * (Z + Z) + Z + (3 * Z + 1) := le_self_add
    _ = (Z + Z + 1) * (Z + Z + 1) := by ring
    _ ≤ B * B := mul_le_mul hBZ hBZ (by simp) (by simp)
    _ ≤ (B + C) * (B + C) := mul_le_mul le_self_add le_self_add (by simp) (by simp)
    _ ≤ (B + C) * (B + C) + C := le_self_add

namespace W1

lemma cB_le_K : ((cB : ℕ) : V) ≤ ((K : ℕ) : V) := by rw [K_def]; push_cast; exact le_self_add

lemma one_le_cB : (1 : V) ≤ ((cB : ℕ) : V) := by
  rw [cB_def, cast_ppair, Nat.cast_one]; exact le_ppair_left _ _

lemma pConst_one_le_cB : pConst (1 : V) ≤ ((cB : ℕ) : V) := by
  rw [cB_def, cast_ppair, cast_ppair, cast_pConst, Nat.cast_one]
  exact le_trans (le_ppair_left _ _) (le_ppair_right _ _)

lemma one_le_code (W : W1) (k : V) : (1 : V) ≤ W.code k := by unfold code pIte; exact le_add_self

/-- **The gain of a watch over its transposition** above the threshold, when its member is below the transposed
member: the slack `cB` plus some gain. -/
theorem gain (W : W1) {k : V} (hk : ((K : ℕ) : V) ≤ k) (h : W.s.orig) :
    ∃ g, Gain ((cB : ℕ) : V) (W.code k) (W.tr.code k) g := by
  have hm : W.s.code k + 1 ≤ W.s.tr.code k := lt_iff_succ_le.mp (SM.code_lt_tr W.s k h)
  have hc : ((cB : ℕ) : V) ≤ W.s.code k := le_trans (le_trans cB_le_K hk) (SM.le_code _ k)
  have g1 : Gain ((cB : ℕ) : V) (pBot (W.s.code k)) (pBot (W.s.tr.code k)) (W.s.code k) := Gain.bot hm hc
  have hβ : (1 : V) ≤ pBot (W.s.code k) := by unfold pBot; exact le_add_self
  have g2 := Gain.ppair_right (le_trans g1.le le_self_add) hβ g1
  have hZ : (1 : V) ≤ ppair (pBot (W.s.code k)) (pBot (W.s.code k)) := le_trans hβ (le_ppair_left _ _)
  have g3 := (Gain.ppair_right (c := ((cB : ℕ) : V)) (x := 4) (x' := 4) le_self_add hZ g2).succ
  have hB : (1 : V) ≤ ppair 4 (ppair (pBot (W.s.code k)) (pBot (W.s.code k))) + 1 := le_add_self
  have g4 := Gain.ppair_left (y := ppair (W.t : V) (ppair (pConst (W.p : V)) (pConst (W.q : V))))
    (y' := ppair ((1 - W.t : ℕ) : V) (ppair (pConst ((1 - W.p : ℕ) : V)) (pConst ((1 - W.q : ℕ) : V))))
    (le_trans (cpart_le W) le_add_self) hB g3
  have hP := le_trans hB (le_ppair_left _ (ppair (W.t : V) (ppair (pConst (W.p : V)) (pConst (W.q : V)))))
  exact ⟨_, (Gain.ppair_right (c := ((cB : ℕ) : V)) (x := 5) (x' := 5) le_self_add hP g4).succ⟩

/-- **A foreign first stage is dominated by the watch**: `pSim (pBot S₀) (pBot S₀) ≤ W.code k` as soon as `S₀` is
below the watch's bot-wrapped member. -/
theorem sim_le_code (W : W1) {S₀ : V} (k : V) (h : S₀ ≤ pBot (W.s.code k)) :
    pSim (pBot S₀) (pBot S₀) ≤ W.code k := by
  have hβ4 : (4 : V) ≤ pBot (W.s.code k) := by
    unfold pBot
    calc (4 : V) = 3 + 1 := by norm_num
      _ ≤ ppair 3 (W.s.code k) + 1 := add_le_add (le_ppair_left _ _) le_rfl
  have h1 : pBot S₀ ≤ ppair (pBot (W.s.code k)) (pBot (W.s.code k)) :=
    le_trans (pBot_le_pBot h) (pBot_le_ppair_self hβ4)
  have h3 := ppair_self_le_ppair_sim (ppair (pBot (W.s.code k)) (pBot (W.s.code k)))
    (ppair (W.t : V) (ppair (pConst (W.p : V)) (pConst (W.q : V))))
  show ppair 4 (ppair (pBot S₀) (pBot S₀)) + 1 ≤
    ppair 5 (ppair (ppair 4 (ppair (pBot (W.s.code k)) (pBot (W.s.code k))) + 1)
      (ppair (W.t : V) (ppair (pConst (W.p : V)) (pConst (W.q : V))))) + 1
  refine add_le_add ?_ le_rfl
  exact le_trans (ppair_le_ppair_right 4 (le_trans (ppair_le_ppair h1 h1) h3)) (ppair_le_ppair_left (by norm_num) _)

end W1

/-! ### 3. The two-stage watch -/

/-- **A two-stage watch**: a first run-stage over the bot-wrapped simple member `s₀` (test `t₀`, then-constant
`p₀`) whose ELSE branch is a `W1` watch — τ(OBot)'s instance at a self-prober (`t₀ = p₀ = 1`, the inner watch
`⟨inst A defect, 1, 1, 0⟩`). -/
structure W2 where
  s₀ : SM
  t₀ : ℕ
  p₀ : ℕ
  w : W1
  ht : t₀ = 0 ∨ t₀ = 1
  hp : p₀ = 0 ∨ p₀ = 1

namespace W2

/-- The watch's code at the budget `k`, in every model. -/
noncomputable def code (W : W2) (k : V) : V :=
  pIte (pSim (pBot (W.s₀.code k)) (pBot (W.s₀.code k))) (W.t₀ : V) (pConst (W.p₀ : V)) (W.w.code k)

/-- The transposed watch. -/
noncomputable def tr (W : W2) : W2 :=
  ⟨W.s₀.tr, 1 - W.t₀, 1 - W.p₀, W.w.tr, by rcases W.ht with h | h <;> simp [h], by rcases W.hp with h | h <;> simp [h]⟩

lemma tr_tr (W : W2) : W.tr.tr = W := by
  obtain ⟨s, t, p, w, ht, hp⟩ := W
  unfold tr
  simp only [SM.tr_tr, W1.tr_tr]
  rcases ht with rfl | rfl <;> rcases hp with rfl | rfl <;> rfl

theorem transposeCode_code (W : W2) (k : V) : transposeCode (W.code k) = W.tr.code k := by
  unfold code transposeCode
  rw [revalue_ite, revalue_sim, revalue_bot, revalue_const]
  show pIte (pSim (pBot (revalue 1 0 (W.s₀.code k))) (pBot (revalue 1 0 (W.s₀.code k)))) (swapAction _)
    (pConst (swapAction _)) (revalue 1 0 (W.w.code k)) = _
  rw [show revalue 1 0 (W.s₀.code k) = transposeCode (W.s₀.code k) from rfl, SM.transposeCode_code,
    show revalue 1 0 (W.w.code k) = transposeCode (W.w.code k) from rfl, W1.transposeCode_code,
    swapAction_cast W.t₀ W.ht, swapAction_cast W.p₀ W.hp]
  rfl

/-! #### The τ-order -/

/-- The decision: the inner watch's member below its transposition. -/
def orig (W : W2) : Prop := W.w.s.orig

/-- The threshold above which the τ-order of the cascade follows its inner watch's (never evaluated). -/
noncomputable def K (W : W2) : ℕ := W.s₀.inner + W.s₀.tr.inner + W1.K + 3

lemma K_def (W : W2) : W.K = W.s₀.inner + W.s₀.tr.inner + W1.K + 3 := rfl

attribute [irreducible] K

lemma K_tr (W : W2) : W.tr.K = W.K := by
  rw [K_def, K_def]
  show W.s₀.tr.inner + W.s₀.tr.tr.inner + W1.K + 3 = _
  rw [SM.tr_tr]; omega

lemma three_le_of_K {W : W2} {k : V} (hk : ((W.K : ℕ) : V) ≤ k) : 3 ≤ k := by
  rw [K_def] at hk; push_cast at hk
  exact le_trans le_add_self hk

lemma w1K_le_of_K {W : W2} {k : V} (hk : ((W.K : ℕ) : V) ≤ k) : ((W1.K : ℕ) : V) ≤ k := by
  rw [K_def] at hk; push_cast at hk
  exact le_trans (le_trans le_add_self le_self_add) hk

lemma inner₀_le_of_K {W : W2} {k : V} (hk : ((W.K : ℕ) : V) ≤ k) : ((W.s₀.inner : ℕ) : V) ≤ k := by
  rw [K_def] at hk; push_cast at hk
  exact le_trans (le_trans (le_trans le_self_add le_self_add) le_self_add) hk

/-- The first-stage member is below the bot-wrapped inner member above the threshold: `S₀ ≤ 72 k⁴ ≤ k⁸ ≤ S₁² ≤
pBot S₁`. -/
lemma member_le_bot (k I₀ I₁ : V) (hI : I₀ ≤ k) (hk : 3 ≤ k) :
    ppair 6 (ppair k I₀) + 1 ≤ pBot (ppair 6 (ppair k I₁) + 1) := by
  have h9 : (9 : V) ≤ k * k := le_trans (by norm_num) (mul_le_mul hk hk (by simp) (by simp))
  have h72 : (72 : V) ≤ k * k * (k * k) := by
    calc (72 : V) ≤ 9 * 9 := by norm_num
      _ ≤ k * k * (k * k) := mul_le_mul h9 h9 (by simp) (by simp)
  have h1 := simple_ge_k4 k I₁
  calc ppair 6 (ppair k I₀) + 1 ≤ 72 * (k * k * (k * k)) := simple_le_bound k I₀ hI hk
    _ ≤ (k * k * (k * k)) * (k * k * (k * k)) := mul_le_mul h72 le_rfl (by simp) (by simp)
    _ ≤ (ppair 6 (ppair k I₁) + 1) * (ppair 6 (ppair k I₁) + 1) := mul_le_mul h1 h1 (by simp) (by simp)
    _ ≤ (3 + (ppair 6 (ppair k I₁) + 1)) * (3 + (ppair 6 (ppair k I₁) + 1)) :=
        mul_le_mul le_add_self le_add_self (by simp) (by simp)
    _ ≤ pBot (ppair 6 (ppair k I₁) + 1) := by unfold pBot ppair; exact le_trans le_self_add le_self_add

/-- **The order of the cascade follows its inner watch's above the threshold.** -/
theorem code_lt_tr (W : W2) {k : V} (hk : ((W.K : ℕ) : V) ≤ k) (h : W.orig) : W.code k < W.tr.code k := by
  obtain ⟨g, hg⟩ := W1.gain W.w (w1K_le_of_K hk) h
  have hc1 : (1 : V) ≤ ((W1.cB : ℕ) : V) := W1.one_le_cB
  have hg1 : (1 : V) ≤ g := le_trans hc1 hg.2
  have hY : (1 : V) ≤ W.w.code k := W1.one_le_code _ k
  have gQ := Gain.ppair_right (x := pConst (W.p₀ : V)) (x' := pConst ((1 - W.p₀ : ℕ) : V))
    (le_trans (le_trans (W1.pConst_le_one W.hp) W1.pConst_one_le_cB) le_add_self) hY hg
  have hQ : (1 : V) ≤ ppair (pConst (W.p₀ : V)) (W.w.code k) := le_trans hY (le_ppair_right _ _)
  have gR := Gain.ppair_right (x := (W.t₀ : V)) (x' := ((1 - W.t₀ : ℕ) : V))
    (le_trans (le_trans (W1.cast_le_one W.ht) hc1) le_add_self) hQ gQ
  have hb : pSim (pBot (W.s₀.code k)) (pBot (W.s₀.code k)) ≤ W.w.code k := by
    refine W1.sim_le_code W.w k ?_
    rw [SM.code_eq_inner, SM.code_eq_inner]
    exact member_le_bot k _ _ (inner₀_le_of_K hk) (three_le_of_K hk)
  have hYg : W.w.code k ≤
      ppair (pConst (W.p₀ : V)) (W.w.code k) * (W.w.code k * g) :=
    le_trans (le_mul_right_of_one_le _ hg1) (le_mul_left_of_one_le _ hQ)
  show pIte (pSim (pBot (W.s₀.code k)) (pBot (W.s₀.code k))) (W.t₀ : V) (pConst (W.p₀ : V)) (W.w.code k) <
    pIte (pSim (pBot (W.s₀.tr.code k)) (pBot (W.s₀.tr.code k))) ((1 - W.t₀ : ℕ) : V) (pConst ((1 - W.p₀ : ℕ) : V))
      (W.w.tr.code k)
  unfold pIte
  rw [add_lt_add_iff_right, ppair_lt_ppair_right_iff]
  apply ppair_lt_of_add_lt
  calc pSim (pBot (W.s₀.code k)) (pBot (W.s₀.code k)) + ppair (W.t₀ : V) (ppair (pConst (W.p₀ : V)) (W.w.code k))
      ≤ ppair (pConst (W.p₀ : V)) (W.w.code k) * (W.w.code k * g) +
          ppair (W.t₀ : V) (ppair (pConst (W.p₀ : V)) (W.w.code k)) := add_le_add (le_trans hb hYg) le_rfl
    _ < ppair (pConst (W.p₀ : V)) (W.w.code k) * (W.w.code k * g) +
          ppair (W.t₀ : V) (ppair (pConst (W.p₀ : V)) (W.w.code k)) + 1 := lt_add_one _
    _ ≤ ppair (pConst (W.p₀ : V)) (W.w.code k) * (W.w.code k * g) +
          ppair (W.t₀ : V) (ppair (pConst (W.p₀ : V)) (W.w.code k)) + ((W1.cB : ℕ) : V) := add_le_add le_rfl hc1
    _ = ppair (W.t₀ : V) (ppair (pConst (W.p₀ : V)) (W.w.code k)) + ((W1.cB : ℕ) : V) +
          ppair (pConst (W.p₀ : V)) (W.w.code k) * (W.w.code k * g) := by ring
    _ ≤ ppair ((1 - W.t₀ : ℕ) : V) (ppair (pConst ((1 - W.p₀ : ℕ) : V)) (W.w.tr.code k)) := gR.1
    _ ≤ pSim (pBot (W.s₀.tr.code k)) (pBot (W.s₀.tr.code k)) +
          ppair ((1 - W.t₀ : ℕ) : V) (ppair (pConst ((1 - W.p₀ : ℕ) : V)) (W.w.tr.code k)) := le_add_self

lemma tr_orig_of_not {W : W2} (h : ¬ W.orig) : W.tr.orig := W1.tr_orig_of_not (W := W.w) h

theorem tr_lt_code (W : W2) {k : V} (hk : ((W.K : ℕ) : V) ≤ k) (h : ¬ W.orig) : W.tr.code k < W.code k := by
  have := code_lt_tr W.tr (by rw [K_tr]; exact hk) (tr_orig_of_not h)
  rwa [tr_tr] at this

/-! #### The canonical shape -/

open scoped Classical in
noncomputable def can (W : W2) : W2 := if W.orig then W else W.tr
open scoped Classical in
noncomputable def uT (W : W2) : ClosedSemiterm LAct 0 := if W.orig then cterm Act.C else cterm Act.D
open scoped Classical in
noncomputable def wT (W : W2) : ClosedSemiterm LAct 0 := if W.orig then cterm Act.D else cterm Act.C

theorem canonical_code (W : W2) {k : V} (hk : ((W.K : ℕ) : V) ≤ k) : canonical (W.code k) = W.can.code k := by
  unfold can
  by_cases h : W.orig
  · rw [if_pos h, canonical_of_lt (by rw [transposeCode_code]; exact code_lt_tr W hk h)]
  · rw [if_neg h, canonical_of_gt (by rw [transposeCode_code]; exact tr_lt_code W hk h), transposeCode_code]

theorem revalueU_code (W : W2) {k : V} (hk : ((W.K : ℕ) : V) ≤ k) : revalueU (W.code k) = (⌜W.uT⌝ : V) := by
  unfold revalueU uT
  rw [transposeCode_code]
  by_cases h : W.orig
  · rw [if_pos (code_lt_tr W hk h), if_pos h, quote_cterm_C]
  · rw [if_neg (lt_asymm (tr_lt_code W hk h)), if_pos (tr_lt_code W hk h), if_neg h, quote_cterm_D]

theorem revalueW_code (W : W2) {k : V} (hk : ((W.K : ℕ) : V) ≤ k) : revalueW (W.code k) = (⌜W.wT⌝ : V) := by
  unfold revalueW wT
  rw [transposeCode_code]
  by_cases h : W.orig
  · rw [if_pos (code_lt_tr W hk h), if_pos h, quote_cterm_D]
  · rw [if_neg (lt_asymm (tr_lt_code W hk h)), if_pos (tr_lt_code W hk h), if_neg h, quote_cterm_C]

theorem revalue_val_uT_wT (W : W2) (k : V) :
    revalue (W.uT.val (s := stdReadingV V) ![] Empty.elim) (W.wT.val (s := stdReadingV V) ![] Empty.elim)
      (W.can.code k) = W.code k := by
  unfold uT wT can
  by_cases h : W.orig
  · rw [if_pos h, if_pos h, if_pos h, val_cterm_C_V, val_cterm_D_V, revalue_zero_one]
  · rw [if_neg h, if_neg h, if_neg h, val_cterm_D_V, val_cterm_C_V]
    show transposeCode (W.tr.code k) = _
    rw [← transposeCode_code W k, transposeCode_transposeCode]

theorem revalue_val_uT_wT_swap (W : W2) (k : V) :
    revalue ((Semiterm.lMap swap W.uT).val (s := stdReadingV V) ![] Empty.elim)
      ((Semiterm.lMap swap W.wT).val (s := stdReadingV V) ![] Empty.elim) (W.can.code k) = W.tr.code k := by
  unfold uT wT can
  by_cases h : W.orig
  · rw [if_pos h, if_pos h, if_pos h, lMap_swap_cterm_C, lMap_swap_cterm_D, val_cterm_D_V, val_cterm_C_V]
    show transposeCode (W.code k) = _
    rw [transposeCode_code]
  · rw [if_neg h, if_neg h, if_neg h, lMap_swap_cterm_D, lMap_swap_cterm_C, val_cterm_C_V, val_cterm_D_V,
      revalue_zero_one]

theorem canonical_tr_code (W : W2) {k : V} (hk : ((W.K : ℕ) : V) ≤ k) : canonical (W.tr.code k) = W.can.code k := by
  rw [← transposeCode_code, canonical_transposeCode, canonical_code W hk]

theorem revalueU_tr_code (W : W2) {k : V} (hk : ((W.K : ℕ) : V) ≤ k) :
    revalueU (W.tr.code k) = (⌜Semiterm.lMap swap W.uT⌝ : V) := by
  have e : transposeCode (W.tr.code k) = W.code k := by rw [← transposeCode_code, transposeCode_transposeCode]
  unfold revalueU uT
  rw [e]
  by_cases h : W.orig
  · rw [if_neg (lt_asymm (code_lt_tr W hk h)), if_pos (code_lt_tr W hk h), if_pos h, lMap_swap_cterm_C, quote_cterm_D]
  · rw [if_pos (tr_lt_code W hk h), if_neg h, lMap_swap_cterm_D, quote_cterm_C]

theorem revalueW_tr_code (W : W2) {k : V} (hk : ((W.K : ℕ) : V) ≤ k) :
    revalueW (W.tr.code k) = (⌜Semiterm.lMap swap W.wT⌝ : V) := by
  have e : transposeCode (W.tr.code k) = W.code k := by rw [← transposeCode_code, transposeCode_transposeCode]
  unfold revalueW wT
  rw [e]
  by_cases h : W.orig
  · rw [if_neg (lt_asymm (code_lt_tr W hk h)), if_pos (code_lt_tr W hk h), if_pos h, lMap_swap_cterm_D, quote_cterm_C]
  · rw [if_pos (tr_lt_code W hk h), if_neg h, lMap_swap_cterm_C, quote_cterm_D]

/-! #### The towers -/

/-- The one-variable ℒₒᵣ-term of the cascade. -/
noncomputable def T1 (W : W2) : Semiterm ℒₒᵣ Empty 1 :=
  iteT1 (simT1 (botT1 W.s₀.T1) (botT1 W.s₀.T1)) W.t₀ (constT1 W.p₀) W.w.T1

lemma val_T1_V (W : W2) (k : V) : (W.T1).val (s := standardModel V) ![k] Empty.elim = W.code k := by
  rw [T1, val_iteT1_V, val_simT1_V, val_botT1_V, SM.val_T1_V, val_constT1_V, W1.val_T1_V]
  rfl

lemma termSubst_T1 (W : W2) (k : V) :
    termSubst LAct (binNumeral k ∷ (0 : V)) (⌜(Rew.emb W.T1 : SyntacticSemiterm ℒₒᵣ 1)⌝ : V) = codeTerm (W.code k) := by
  rw [T1]
  exact termSubst_iteT1 _ W.t₀
    (termSubst_simT1 _ (termSubst_botT1 _ (SM.termSubst_T1 _ _)) (termSubst_botT1 _ (SM.termSubst_T1 _ _)))
    (termSubst_constT1 _ _) (W1.termSubst_T1 _ _)

/-- **The frame tower** of the bot-wrapped cascade `pBot (W.code k)`. -/
noncomputable def TX (W : W2) : Semiterm LAct Empty 1 := Semiterm.lMap emb (botT1 W.can.T1)

lemma lMap_swap_TX (W : W2) : Semiterm.lMap swap W.TX = W.TX := term_lMap_swap_emb _

theorem val_TX_V (W : W2) {k : V} (hk : ((W.K : ℕ) : V) ≤ k) :
    W.TX.val (s := stdReadingV V) ![k] Empty.elim = canonical (pBot (W.code k)) := by
  unfold TX
  rw [Semiterm.val_lMap, stdReadingV_lMap_emb, val_botT1_V, val_T1_V, canonical_pBot, canonical_code W hk]

theorem hX_TX (W : W2) {k : V} (hk : ((W.K : ℕ) : V) ≤ k) :
    termSubst LAct (binNumeral k ∷ (0 : V)) (⌜(Rew.emb W.TX : SyntacticSemiterm LAct 1)⌝ : V) =
      codeTerm (canonical (pBot (W.code k))) := by
  unfold TX
  rw [term_emb_lMap_emb_n, quote_term_lMap_emb, termSubst_botT1 _ (termSubst_T1 _ _), canonical_pBot, canonical_code W hk]

theorem descVal_TX (W : W2) {k : V} (hk : ((W.K : ℕ) : V) ≤ k) : descVal W.TX W.uT W.wT k = pBot (W.code k) := by
  rw [descVal_def, val_TX_V W hk, canonical_pBot, revalue_bot, canonical_code W hk, revalue_val_uT_wT]

theorem descVal_TX_T (W : W2) {k : V} (hk : ((W.K : ℕ) : V) ≤ k) :
    descVal (Semiterm.lMap swap W.TX) (Semiterm.lMap swap W.uT) (Semiterm.lMap swap W.wT) k = pBot (W.tr.code k) := by
  rw [descVal_def, lMap_swap_TX, val_TX_V W hk, canonical_pBot, revalue_bot, canonical_code W hk, revalue_val_uT_wT_swap]

/-- **The frame tower describes the bot-wrapped cascade above the threshold.** -/
theorem describesBot (W : W2) : DescribesAbove W.K W.TX W.uT W.wT where
  hX := fun V _ _ k hk ↦ by rw [descVal_TX W hk]; exact hX_TX W hk
  hU := fun V _ _ k hk ↦ by rw [descVal_TX W hk, revalueU_pBot, revalueU_code W hk]
  hW := fun V _ _ k hk ↦ by rw [descVal_TX W hk, revalueW_pBot, revalueW_code W hk]
  hT := fun V _ _ k hk ↦ by rw [descVal_TX_T W hk, descVal_TX W hk, transposeCode_pBot, transposeCode_code]

/-- The transposed description of the bot-wrapped cascade, above the threshold. -/
theorem describesBotT (W : W2) :
    DescribesAbove W.K (Semiterm.lMap swap W.TX) (Semiterm.lMap swap W.uT) (Semiterm.lMap swap W.wT) where
  hX := fun V _ _ k hk ↦ by
    rw [descVal_TX_T W hk, lMap_swap_TX, canonical_pBot, canonical_tr_code W hk, ← canonical_code W hk,
      ← canonical_pBot]
    exact hX_TX W hk
  hU := fun V _ _ k hk ↦ by rw [descVal_TX_T W hk, revalueU_pBot, revalueU_tr_code W hk]
  hW := fun V _ _ k hk ↦ by rw [descVal_TX_T W hk, revalueW_pBot, revalueW_tr_code W hk]
  hT := fun V _ _ k hk ↦ by
    rw [term_lMap_swap_swap, term_lMap_swap_swap, term_lMap_swap_swap, descVal_TX W hk, descVal_TX_T W hk,
      transposeCode_pBot, ← transposeCode_code, transposeCode_transposeCode]

end W2

/-! ### 4. The stored description of a two-stage watch -/

lemma codeTermMetaAbs_W2 (W : W2) (K : ℕ) : codeTermMetaAbs K (W.code K) = W.T1 := by
  unfold W2.code W2.T1
  simp only [natCast_nat]
  rw [codeTermMetaAbs_ite, codeTermMetaAbs_sim, codeTermMetaAbs_bot, codeTermMetaAbs_SM, codeTermMetaAbs_const,
    codeTermMetaAbs_W1]
  rfl

lemma codeTermMetaAbs_botW2 (W : W2) (K : ℕ) : codeTermMetaAbs K (pBot (W.code K)) = botT1 W.T1 := by
  rw [codeTermMetaAbs_bot, codeTermMetaAbs_W2]; rfl

namespace W2

/-- **The fixed closed description of the cascade**: the tower with the budget slot in place of the budget. -/
noncomputable def Dfix (W : W2) : Semisentence LAct 14 :=
  descF #1 (Rew.subst ![#8] (Semiterm.lMap emb (botT1 W.can.T1))) (cl W.uT) (cl W.wT)

theorem canonical_code_nat (W : W2) {k : ℕ} (hk : W.K ≤ k) : canonical (W.code k) = W.can.code k :=
  W2.canonical_code W (le_def.mpr (Nat.eq_or_lt_of_le (by rw [natCast_nat]; exact hk)))

theorem code_lt_tr_nat (W : W2) {k : ℕ} (hk : W.K ≤ k) (h : W.orig) : W.code k < W.tr.code k :=
  W2.code_lt_tr W (le_def.mpr (Nat.eq_or_lt_of_le (by rw [natCast_nat]; exact hk))) h

theorem tr_lt_code_nat (W : W2) {k : ℕ} (hk : W.K ≤ k) (h : ¬ W.orig) : W.tr.code k < W.code k :=
  W2.tr_lt_code W (le_def.mpr (Nat.eq_or_lt_of_le (by rw [natCast_nat]; exact hk))) h

theorem canonical_tr_code_nat (W : W2) {k : ℕ} (hk : W.K ≤ k) : canonical (W.tr.code k) = W.can.code k :=
  W2.canonical_tr_code W (le_def.mpr (Nat.eq_or_lt_of_le (by rw [natCast_nat]; exact hk)))

theorem revalueUMeta_code (W : W2) {k : ℕ} (hk : W.K ≤ k) : revalueUMeta (W.code k) = W.uT := by
  unfold revalueUMeta W2.uT
  rw [transposeCode_code]
  by_cases h : W.orig
  · rw [if_pos (code_lt_tr_nat W hk h), if_pos h]
  · rw [if_neg (lt_asymm (tr_lt_code_nat W hk h)), if_pos (tr_lt_code_nat W hk h), if_neg h]

theorem revalueWMeta_code (W : W2) {k : ℕ} (hk : W.K ≤ k) : revalueWMeta (W.code k) = W.wT := by
  unfold revalueWMeta W2.wT
  rw [transposeCode_code]
  by_cases h : W.orig
  · rw [if_pos (code_lt_tr_nat W hk h), if_pos h]
  · rw [if_neg (lt_asymm (tr_lt_code_nat W hk h)), if_pos (tr_lt_code_nat W hk h), if_neg h]

theorem revalueUMeta_tr_code (W : W2) {k : ℕ} (hk : W.K ≤ k) :
    revalueUMeta (W.tr.code k) = Semiterm.lMap swap W.uT := by
  have e : transposeCode (W.tr.code k) = W.code k := by rw [← transposeCode_code, transposeCode_transposeCode]
  unfold revalueUMeta W2.uT
  rw [e]
  by_cases h : W.orig
  · rw [if_neg (lt_asymm (code_lt_tr_nat W hk h)), if_pos (code_lt_tr_nat W hk h), if_pos h, lMap_swap_cterm_C]
  · rw [if_pos (tr_lt_code_nat W hk h), if_neg h, lMap_swap_cterm_D]

theorem revalueWMeta_tr_code (W : W2) {k : ℕ} (hk : W.K ≤ k) :
    revalueWMeta (W.tr.code k) = Semiterm.lMap swap W.wT := by
  have e : transposeCode (W.tr.code k) = W.code k := by rw [← transposeCode_code, transposeCode_transposeCode]
  unfold revalueWMeta W2.wT
  rw [e]
  by_cases h : W.orig
  · rw [if_neg (lt_asymm (code_lt_tr_nat W hk h)), if_pos (code_lt_tr_nat W hk h), if_pos h, lMap_swap_cterm_D]
  · rw [if_pos (tr_lt_code_nat W hk h), if_neg h, lMap_swap_cterm_C]

/-- **The stored description of the bot-wrapped cascade is constant above the threshold.** -/
theorem closedDescAt_code (W : W2) {k : ℕ} (hk : W.K ≤ k) : closedDescAt (some k) (pBot (W.code k)) = W.Dfix := by
  unfold closedDescAt Dfix
  rw [canonicalSlot_some]
  unfold canonicalAbs
  rw [canonical_pBot, canonical_code_nat W hk, codeTermMetaAbs_botW2, revalueUMeta_pBot, revalueWMeta_pBot,
    revalueUMeta_code W hk, revalueWMeta_code W hk]

/-- **The abstracted description denotes the cascade at the budget `k`, in every model.** -/
theorem absVal_code (W : W2) {K : ℕ} (hK : W.K ≤ K) (k : V) : absVal K (pBot (W.code K)) k = pBot (W.code k) := by
  rw [absVal_def, canonical_pBot, canonical_code_nat W hK, codeTermMetaAbs_botW2, revalueUMeta_pBot, revalueWMeta_pBot,
    revalueUMeta_code W hK, revalueWMeta_code W hK, val_botT1_V, W2.val_T1_V, revalue_bot, revalue_val_uT_wT]

/-- …and the abstracted description of its TRANSPOSITION denotes the transposed cascade. -/
theorem absVal_tr_code (W : W2) {K : ℕ} (hK : W.K ≤ K) (k : V) :
    absVal K (transposeCode (pBot (W.code K))) k = pBot (W.tr.code k) := by
  rw [absVal_def, transposeCode_pBot, transposeCode_code, canonical_pBot, canonical_tr_code_nat W hK,
    codeTermMetaAbs_botW2, revalueUMeta_pBot, revalueWMeta_pBot, revalueUMeta_tr_code W hK, revalueWMeta_tr_code W hK,
    val_botT1_V, W2.val_T1_V, revalue_bot, revalue_val_uT_wT_swap]

end W2

end ArithS.Tau
