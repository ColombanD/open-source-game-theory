import ArithS.Tau.Watch2
import ArithS.Tau.Entangled.Mirror

/-!
# ArithS.Tau.Watch3 — the three-stage watch over a SYSTEM (τ(EBot)'s instance at DIMCID) as a `k̂`-tower (Phase 3f)

τ(EBot)'s instance at a self-prober `A` is a cascade of THREE run-stage watches, on `A`'s instances at the
defector, at the cooperator and at the MIRROR (`Tau/Spec.instCode_ebot`); the first two members are simple
searchers (`SM`), the third is the closed SYSTEM `inst A mirror = .sys [member, mm 0] 0` — a mirror system
`Sys2c` (`Tau/Entangled/Mirror.lean`) with a `.search k` member. Under Phase 2c the abstraction did not enter
a system, so a guard naming this watch stored `binNumeral k` and never fitted (`Tau/NeverFitsSys.lean`). Since
Phase 2d (decision (α)) `codeTermMetaAbs` descends into systems, the system's tower `Sys2c.T1` IS its abstracted
description (`codeTermMetaAbs_Sys2c`), and the three-stage watch is a `k̂`-tower like `W1`/`W2`:

* §1 **the gain calculus, value level**: `Gain.lt`, `Gain.ppair_right_dom` (a left argument dominated by the gain
  may move freely), `watch_gain` (`W1.gain` for any member value), `watch_sim_le` (`W1.sim_le_code`), and
  `cascade_gain` — one more run-stage in front of a cascade that already has a gain keeps a gain, so the τ-order
  of a cascade of ANY depth follows its innermost member above a standard threshold;
* §2 **the three-stage watch `W3`**: code, transposition, the τ-order above `W3.K` (decided by the system's
  searcher member), the canonical shape, the re-valuation terms, the tower `W3.TX`, `W3.describesBot`;
* §3 the stored (budget-abstracted) description of a `W3` watch is constant above the threshold and denotes the
  watch in every model (`W3.closedDescAt_code`, `W3.absVal_code`, `W3.absVal_tr_code`).
-/

set_option linter.constructorNameAsVariable false

namespace ArithS.Tau

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open LAct

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ### 1. The gain calculus at the value level -/

namespace Gain

/-- A gain with a positive slack is a strict inequality. -/
lemma lt {c a a' g : V} (h : Gain c a a' g) (hc : 1 ≤ c) : a < a' :=
  lt_of_lt_of_le (lt_of_lt_of_le (lt_add_one a) (add_le_add le_rfl hc)) (le_trans le_self_add h.1)

/-- **Through the right argument, with a DOMINATED left argument**: when the left argument is below the gain it
may be replaced by anything. -/
theorem ppair_right_dom {c x x' y y' g : V} (hx : x ≤ g) (h : Gain c y y' g) : Gain c (ppair x y) (ppair x' y') g := by
  obtain ⟨h1, h2⟩ := h
  have hs : x + y ≤ x' + y' := by
    calc x + y ≤ g + y := add_le_add hx le_rfl
      _ = y + g := add_comm _ _
      _ ≤ y + c + g := add_le_add le_self_add le_rfl
      _ ≤ y' := h1
      _ ≤ x' + y' := le_add_self
  refine ⟨?_, h2⟩
  unfold ppair
  calc (x + y) * (x + y) + y + c + g = (x + y) * (x + y) + (y + c + g) := by ring
    _ ≤ (x' + y') * (x' + y') + y' := add_le_add (mul_le_mul hs hs (by simp) (by simp)) h1

end Gain

/-- The constant part of a run-stage is below `W1.cB`. -/
lemma cpart_le_cB {t p q : ℕ} (ht : t = 0 ∨ t = 1) (hp : p = 0 ∨ p = 1) (hq : q = 0 ∨ q = 1) :
    ppair (t : V) (ppair (pConst (p : V)) (pConst (q : V))) ≤ ((W1.cB : ℕ) : V) := by
  rw [W1.cB_def, cast_ppair, cast_ppair, cast_pConst, Nat.cast_one]
  exact ppair_le_ppair (W1.cast_le_one ht) (ppair_le_ppair (W1.pConst_le_one hp) (W1.pConst_le_one hq))

/-- **The gain of a run-stage watch over ANY member value** (`W1.gain`, with the member abstracted): a member
raised by one, above the slack, raises the watch by the slack plus a gain. -/
theorem watch_gain {m m' : V} {t p q : ℕ} (ht : t = 0 ∨ t = 1) (hp : p = 0 ∨ p = 1) (hq : q = 0 ∨ q = 1)
    (hm : m + 1 ≤ m') (hc : ((W1.cB : ℕ) : V) ≤ m) :
    ∃ g, Gain ((W1.cB : ℕ) : V)
      (pIte (pSim (pBot m) (pBot m)) (t : V) (pConst (p : V)) (pConst (q : V)))
      (pIte (pSim (pBot m') (pBot m')) ((1 - t : ℕ) : V) (pConst ((1 - p : ℕ) : V)) (pConst ((1 - q : ℕ) : V))) g := by
  have ht' : (1 - t = 0 ∨ 1 - t = 1) := by rcases ht with h | h <;> simp [h]
  have hp' : (1 - p = 0 ∨ 1 - p = 1) := by rcases hp with h | h <;> simp [h]
  have hq' : (1 - q = 0 ∨ 1 - q = 1) := by rcases hq with h | h <;> simp [h]
  have g1 : Gain ((W1.cB : ℕ) : V) (pBot m) (pBot m') m := Gain.bot hm hc
  have hβ : (1 : V) ≤ pBot m := by unfold pBot; exact le_add_self
  have g2 := Gain.ppair_right (le_trans g1.le le_self_add) hβ g1
  have hZ : (1 : V) ≤ ppair (pBot m) (pBot m) := le_trans hβ (le_ppair_left _ _)
  have g3 := (Gain.ppair_right (c := ((W1.cB : ℕ) : V)) (x := 4) (x' := 4) le_self_add hZ g2).succ
  have hB : (1 : V) ≤ ppair 4 (ppair (pBot m) (pBot m)) + 1 := le_add_self
  have g4 := Gain.ppair_left (y := ppair (t : V) (ppair (pConst (p : V)) (pConst (q : V))))
    (y' := ppair ((1 - t : ℕ) : V) (ppair (pConst ((1 - p : ℕ) : V)) (pConst ((1 - q : ℕ) : V))))
    (le_trans (cpart_le_cB ht hp hq) le_add_self) hB g3
  have hP := le_trans hB (le_ppair_left _ (ppair (t : V) (ppair (pConst (p : V)) (pConst (q : V)))))
  exact ⟨_, (Gain.ppair_right (c := ((W1.cB : ℕ) : V)) (x := 5) (x' := 5) le_self_add hP g4).succ⟩

/-- **A foreign first stage is dominated by a watch** (`W1.sim_le_code`, the member abstracted). -/
theorem watch_sim_le {m S₀ : V} (t P Q : V) (h : S₀ ≤ pBot m) :
    pSim (pBot S₀) (pBot S₀) ≤ pIte (pSim (pBot m) (pBot m)) t P Q := by
  have hβ4 : (4 : V) ≤ pBot m := by
    unfold pBot
    calc (4 : V) = 3 + 1 := by norm_num
      _ ≤ ppair 3 m + 1 := add_le_add (le_ppair_left _ _) le_rfl
  have h1 : pBot S₀ ≤ ppair (pBot m) (pBot m) := le_trans (pBot_le_pBot h) (pBot_le_ppair_self hβ4)
  have h3 := ppair_self_le_ppair_sim (ppair (pBot m) (pBot m)) (ppair t (ppair P Q))
  show ppair 4 (ppair (pBot S₀) (pBot S₀)) + 1 ≤
    ppair 5 (ppair (ppair 4 (ppair (pBot m) (pBot m)) + 1) (ppair t (ppair P Q))) + 1
  refine add_le_add ?_ le_rfl
  exact le_trans (ppair_le_ppair_right 4 (le_trans (ppair_le_ppair h1 h1) h3)) (ppair_le_ppair_left (by norm_num) _)

/-- The else-branch of a run-stage is below the stage. -/
lemma le_pIte_else (B t P Y : V) : Y ≤ pIte B t P Y := by
  unfold pIte
  exact le_trans (le_ppair_right _ _) (le_trans (le_ppair_right _ _) (le_trans (le_ppair_right _ _)
    (le_trans (le_ppair_right _ _) le_self_add)))

lemma one_le_pIte (B t P Y : V) : (1 : V) ≤ pIte B t P Y := by unfold pIte; exact le_add_self

/-- **One more run-stage keeps a gain**: a stage whose test is dominated by its else-branch `Y`, in front of a
cascade `Y` with a gain over `Y'`, has a gain over the transposed stage — whatever the transposed test `B'` is.
(The engine of `W2.code_lt_tr`, as a `Gain`, so that it iterates.) -/
theorem cascade_gain {B B' Y Y' g : V} {t p : ℕ} (ht : t = 0 ∨ t = 1) (hp : p = 0 ∨ p = 1)
    (hY : 1 ≤ Y) (hB : B ≤ Y) (hg : Gain ((W1.cB : ℕ) : V) Y Y' g) :
    ∃ g', Gain ((W1.cB : ℕ) : V) (pIte B (t : V) (pConst (p : V)) Y)
      (pIte B' ((1 - t : ℕ) : V) (pConst ((1 - p : ℕ) : V)) Y') g' := by
  have hc1 : (1 : V) ≤ ((W1.cB : ℕ) : V) := W1.one_le_cB
  have hg1 : (1 : V) ≤ g := le_trans hc1 hg.2
  have gQ := Gain.ppair_right (x := pConst (p : V)) (x' := pConst ((1 - p : ℕ) : V))
    (le_trans (le_trans (W1.pConst_le_one hp) W1.pConst_one_le_cB) le_add_self) hY hg
  have hQ : (1 : V) ≤ ppair (pConst (p : V)) Y := le_trans hY (le_ppair_right _ _)
  have gR := Gain.ppair_right (x := (t : V)) (x' := ((1 - t : ℕ) : V))
    (le_trans (le_trans (W1.cast_le_one ht) hc1) le_add_self) hQ gQ
  have hBg : B ≤ ppair (pConst (p : V)) Y * (Y * g) :=
    le_trans hB (le_trans (le_mul_right_of_one_le _ hg1) (le_mul_left_of_one_le _ hQ))
  have gP := Gain.ppair_right_dom (x' := B') hBg gR
  have hP : (1 : V) ≤ ppair B (ppair (t : V) (ppair (pConst (p : V)) Y)) :=
    le_trans hQ (le_trans (le_ppair_right _ _) (le_ppair_right _ _))
  exact ⟨_, (Gain.ppair_right (c := ((W1.cB : ℕ) : V)) (x := 5) (x' := 5) le_self_add hP gP).succ⟩

/-! #### τ on the stage shapes -/

lemma transposeCode_stage (B Y : V) (t p : ℕ) (ht : t = 0 ∨ t = 1) (hp : p = 0 ∨ p = 1) :
    transposeCode (pIte B (t : V) (pConst (p : V)) Y) =
      pIte (transposeCode B) ((1 - t : ℕ) : V) (pConst ((1 - p : ℕ) : V)) (transposeCode Y) := by
  unfold transposeCode
  rw [revalue_ite, revalue_const]
  show pIte _ (swapAction _) (pConst (swapAction _)) _ = _
  rw [swapAction_cast t ht, swapAction_cast p hp]

lemma transposeCode_simBot (m : V) :
    transposeCode (pSim (pBot m) (pBot m)) = pSim (pBot (transposeCode m)) (pBot (transposeCode m)) := by
  unfold transposeCode; rw [revalue_sim, revalue_bot]

lemma transposeCode_pConst_cast (q : ℕ) (hq : q = 0 ∨ q = 1) :
    transposeCode (pConst (q : V)) = pConst ((1 - q : ℕ) : V) := by
  unfold transposeCode; rw [revalue_const]
  show pConst (swapAction _) = _
  rw [swapAction_cast q hq]

/-! ### 2. The mirror system as a watched member -/

namespace Sys2c

lemma tr_tr (S : Sys2c) : S.tr.tr = S := by
  obtain ⟨m, P, hP⟩ := S
  unfold tr
  simp only [SM.tr_tr]

/-- The system's searcher member is below the system's code. -/
lemma member_le_code (S : Sys2c) (j : ℕ) (k : V) : S.m₀.code k ≤ S.code j k := by
  unfold code D pSys pCons
  exact le_trans (le_ppair_left _ _) (le_trans (le_ppair_right 10 _) (le_trans le_self_add
    (le_trans (le_ppair_left _ _) (le_trans (le_ppair_right 8 _) le_self_add))))

lemma tr_orig_of_not {S : Sys2c} (h : ¬ S.orig) : S.tr.orig := by
  show S.m₀.tr.inner < S.m₀.tr.tr.inner
  rw [SM.tr_tr]
  exact lt_of_le_of_ne (not_lt.mp h) (Ne.symm (SM.inner_ne_tr _))

end Sys2c

/-- **The abstracted description of a mirror system is its tower** (Phase 2d: the abstraction descends into the
member list; the closed member `P` carries no `pSearch` node). -/
lemma codeTermMetaAbs_Sys2c (S : Sys2c) (j K : ℕ) (hP : NoSearchAt K S.P) :
    codeTermMetaAbs K (S.code j K) = S.T1 j := by
  unfold Sys2c.code Sys2c.D Sys2c.T1 sysT1 consT1 nilT1 Sys2c.PT1
  simp only [natCast_nat]
  rw [codeTermMetaAbs_sys, codeTermMetaAbs_cons, codeTermMetaAbs_cons, codeTermMetaAbs_SM,
    codeTermMetaAbs_of_noSearchAt hP, codeTermMetaAbs_nil]

/-! ### 3. The three-stage watch -/

/-- **A three-stage watch**: two run-stages over the bot-wrapped simple members `s₀`, `s₁` (tests `t₀`, `t₁`,
then-constants `p₀`, `p₁`), then a run-stage over member `0` of the mirror system `S` (test `t₂`, branches
`p₂`, `q₂`) — τ(EBot)'s instance at a self-prober: `s₀ = inst A defect`, `s₁ = inst A coop`, `S = inst A mirror`. -/
structure W3 where
  s₀ : SM
  t₀ : ℕ
  p₀ : ℕ
  s₁ : SM
  t₁ : ℕ
  p₁ : ℕ
  S : Sys2c
  t₂ : ℕ
  p₂ : ℕ
  q₂ : ℕ
  ht₀ : t₀ = 0 ∨ t₀ = 1
  hp₀ : p₀ = 0 ∨ p₀ = 1
  ht₁ : t₁ = 0 ∨ t₁ = 1
  hp₁ : p₁ = 0 ∨ p₁ = 1
  ht₂ : t₂ = 0 ∨ t₂ = 1
  hp₂ : p₂ = 0 ∨ p₂ = 1
  hq₂ : q₂ = 0 ∨ q₂ = 1
  hP : ∀ K : ℕ, NoSearchAt K S.P

namespace W3

private lemma oss {a : ℕ} (h : a = 0 ∨ a = 1) : 1 - a = 0 ∨ 1 - a = 1 := by rcases h with h | h <;> simp [h]
private lemma oss' {a : ℕ} (h : a = 0 ∨ a = 1) : 1 - (1 - a) = a := by rcases h with rfl | rfl <;> rfl

/-- The innermost stage: the watch over the system's member `0`. -/
noncomputable def inner (W : W3) (k : V) : V :=
  pIte (pSim (pBot (W.S.code 0 k)) (pBot (W.S.code 0 k))) (W.t₂ : V) (pConst (W.p₂ : V)) (pConst (W.q₂ : V))

/-- The middle cascade: the stage over `s₁` in front of the inner watch. -/
noncomputable def mid (W : W3) (k : V) : V :=
  pIte (pSim (pBot (W.s₁.code k)) (pBot (W.s₁.code k))) (W.t₁ : V) (pConst (W.p₁ : V)) (W.inner k)

/-- The watch's code at the budget `k`, in every model. -/
noncomputable def code (W : W3) (k : V) : V :=
  pIte (pSim (pBot (W.s₀.code k)) (pBot (W.s₀.code k))) (W.t₀ : V) (pConst (W.p₀ : V)) (W.mid k)

/-- The transposed watch. -/
noncomputable def tr (W : W3) : W3 :=
  ⟨W.s₀.tr, 1 - W.t₀, 1 - W.p₀, W.s₁.tr, 1 - W.t₁, 1 - W.p₁, W.S.tr, 1 - W.t₂, 1 - W.p₂, 1 - W.q₂,
    oss W.ht₀, oss W.hp₀, oss W.ht₁, oss W.hp₁, oss W.ht₂, oss W.hp₂, oss W.hq₂, W.hP⟩

lemma tr_tr (W : W3) : W.tr.tr = W := by
  obtain ⟨s₀, t₀, p₀, s₁, t₁, p₁, S, t₂, p₂, q₂, ht₀, hp₀, ht₁, hp₁, ht₂, hp₂, hq₂, hP⟩ := W
  simp only [tr, W3.mk.injEq]
  exact ⟨SM.tr_tr _, oss' ht₀, oss' hp₀, SM.tr_tr _, oss' ht₁, oss' hp₁, Sys2c.tr_tr _, oss' ht₂, oss' hp₂, oss' hq₂⟩

theorem transposeCode_inner (W : W3) (k : V) : transposeCode (W.inner k) = W.tr.inner k := by
  unfold inner
  rw [transposeCode_stage _ _ _ _ W.ht₂ W.hp₂, transposeCode_simBot, Sys2c.transposeCode_code,
    transposeCode_pConst_cast _ W.hq₂]
  rfl

theorem transposeCode_mid (W : W3) (k : V) : transposeCode (W.mid k) = W.tr.mid k := by
  unfold mid
  rw [transposeCode_stage _ _ _ _ W.ht₁ W.hp₁, transposeCode_simBot, SM.transposeCode_code, transposeCode_inner]
  rfl

theorem transposeCode_code (W : W3) (k : V) : transposeCode (W.code k) = W.tr.code k := by
  unfold code
  rw [transposeCode_stage _ _ _ _ W.ht₀ W.hp₀, transposeCode_simBot, SM.transposeCode_code, transposeCode_mid]
  rfl

/-! #### The τ-order -/

/-- The decision: the system's searcher member below its transposition. -/
def orig (W : W3) : Prop := W.S.orig

/-- The threshold above which the τ-order of the watch follows the system's (never evaluated). -/
noncomputable def K (W : W3) : ℕ := W.s₀.inner + W.s₀.tr.inner + (W.s₁.inner + W.s₁.tr.inner) + W1.K + 3

lemma K_def (W : W3) : W.K = W.s₀.inner + W.s₀.tr.inner + (W.s₁.inner + W.s₁.tr.inner) + W1.K + 3 := rfl

attribute [irreducible] K

lemma K_tr (W : W3) : W.tr.K = W.K := by
  rw [K_def, K_def]
  show W.s₀.tr.inner + W.s₀.tr.tr.inner + (W.s₁.tr.inner + W.s₁.tr.tr.inner) + W1.K + 3 = _
  rw [SM.tr_tr, SM.tr_tr]; omega

lemma three_le_of_K {W : W3} {k : V} (hk : ((W.K : ℕ) : V) ≤ k) : 3 ≤ k := by
  rw [K_def] at hk; push_cast at hk
  exact le_trans le_add_self hk

lemma w1K_le_of_K {W : W3} {k : V} (hk : ((W.K : ℕ) : V) ≤ k) : ((W1.K : ℕ) : V) ≤ k := by
  rw [K_def] at hk; push_cast at hk
  exact le_trans (le_trans le_add_self le_self_add) hk

lemma inner₀_le_of_K {W : W3} {k : V} (hk : ((W.K : ℕ) : V) ≤ k) : ((W.s₀.inner : ℕ) : V) ≤ k := by
  rw [K_def] at hk; push_cast at hk
  exact le_trans (le_trans (le_trans (le_trans le_self_add le_self_add) le_self_add) le_self_add) hk

lemma inner₁_le_of_K {W : W3} {k : V} (hk : ((W.K : ℕ) : V) ≤ k) : ((W.s₁.inner : ℕ) : V) ≤ k := by
  rw [K_def] at hk; push_cast at hk
  exact le_trans (le_trans (le_trans (le_trans le_self_add le_add_self) le_self_add) le_self_add) hk

/-- A simple member is below the bot-wrapped system above the threshold. -/
lemma simple_le_bot_sys (W : W3) (s : SM) {k : V} (hs : ((s.inner : ℕ) : V) ≤ k) (hk : 3 ≤ k) :
    s.code k ≤ pBot (W.S.code 0 k) := by
  refine le_trans ?_ (pBot_le_pBot (Sys2c.member_le_code W.S 0 k))
  rw [SM.code_eq_inner, SM.code_eq_inner]
  exact W2.member_le_bot k _ _ hs hk

/-- **The order of the three-stage watch follows the system's above the threshold.** -/
theorem code_lt_tr (W : W3) {k : V} (hk : ((W.K : ℕ) : V) ≤ k) (h : W.orig) : W.code k < W.tr.code k := by
  have hm : W.S.code 0 k + 1 ≤ W.S.tr.code 0 k := lt_iff_succ_le.mp (Sys2c.code_lt_tr h 0 k)
  have hc : ((W1.cB : ℕ) : V) ≤ W.S.code 0 k :=
    le_trans (le_trans (le_trans W1.cB_le_K (w1K_le_of_K hk)) (SM.le_code _ k)) (Sys2c.member_le_code W.S 0 k)
  obtain ⟨g, hg⟩ := watch_gain W.ht₂ W.hp₂ W.hq₂ hm hc
  have hB₁ : pSim (pBot (W.s₁.code k)) (pBot (W.s₁.code k)) ≤ W.inner k :=
    watch_sim_le _ _ _ (simple_le_bot_sys W W.s₁ (inner₁_le_of_K hk) (three_le_of_K hk))
  obtain ⟨g₁, hg₁⟩ := cascade_gain (B' := pSim (pBot (W.s₁.tr.code k)) (pBot (W.s₁.tr.code k))) W.ht₁ W.hp₁
    (one_le_pIte _ _ _ _) hB₁ hg
  have hB₀ : pSim (pBot (W.s₀.code k)) (pBot (W.s₀.code k)) ≤ W.mid k :=
    le_trans (watch_sim_le _ _ _ (simple_le_bot_sys W W.s₀ (inner₀_le_of_K hk) (three_le_of_K hk)))
      (le_pIte_else _ _ _ _)
  obtain ⟨g₀, hg₀⟩ := cascade_gain (B' := pSim (pBot (W.s₀.tr.code k)) (pBot (W.s₀.tr.code k))) W.ht₀ W.hp₀
    (one_le_pIte _ _ _ _) hB₀ hg₁
  exact hg₀.lt W1.one_le_cB

lemma tr_orig_of_not {W : W3} (h : ¬ W.orig) : W.tr.orig := Sys2c.tr_orig_of_not (S := W.S) h

theorem tr_lt_code (W : W3) {k : V} (hk : ((W.K : ℕ) : V) ≤ k) (h : ¬ W.orig) : W.tr.code k < W.code k := by
  have := code_lt_tr W.tr (by rw [K_tr]; exact hk) (tr_orig_of_not h)
  rwa [tr_tr] at this

/-! #### The canonical shape -/

open scoped Classical in
noncomputable def can (W : W3) : W3 := if W.orig then W else W.tr
open scoped Classical in
noncomputable def uT (W : W3) : ClosedSemiterm LAct 0 := if W.orig then cterm Act.C else cterm Act.D
open scoped Classical in
noncomputable def wT (W : W3) : ClosedSemiterm LAct 0 := if W.orig then cterm Act.D else cterm Act.C

theorem canonical_code (W : W3) {k : V} (hk : ((W.K : ℕ) : V) ≤ k) : canonical (W.code k) = W.can.code k := by
  unfold can
  by_cases h : W.orig
  · rw [if_pos h, canonical_of_lt (by rw [transposeCode_code]; exact code_lt_tr W hk h)]
  · rw [if_neg h, canonical_of_gt (by rw [transposeCode_code]; exact tr_lt_code W hk h), transposeCode_code]

theorem revalueU_code (W : W3) {k : V} (hk : ((W.K : ℕ) : V) ≤ k) : revalueU (W.code k) = (⌜W.uT⌝ : V) := by
  unfold revalueU uT
  rw [transposeCode_code]
  by_cases h : W.orig
  · rw [if_pos (code_lt_tr W hk h), if_pos h, quote_cterm_C]
  · rw [if_neg (lt_asymm (tr_lt_code W hk h)), if_pos (tr_lt_code W hk h), if_neg h, quote_cterm_D]

theorem revalueW_code (W : W3) {k : V} (hk : ((W.K : ℕ) : V) ≤ k) : revalueW (W.code k) = (⌜W.wT⌝ : V) := by
  unfold revalueW wT
  rw [transposeCode_code]
  by_cases h : W.orig
  · rw [if_pos (code_lt_tr W hk h), if_pos h, quote_cterm_D]
  · rw [if_neg (lt_asymm (tr_lt_code W hk h)), if_pos (tr_lt_code W hk h), if_neg h, quote_cterm_C]

theorem revalue_val_uT_wT (W : W3) (k : V) :
    revalue (W.uT.val (s := stdReadingV V) ![] Empty.elim) (W.wT.val (s := stdReadingV V) ![] Empty.elim)
      (W.can.code k) = W.code k := by
  unfold uT wT can
  by_cases h : W.orig
  · rw [if_pos h, if_pos h, if_pos h, val_cterm_C_V, val_cterm_D_V, revalue_zero_one]
  · rw [if_neg h, if_neg h, if_neg h, val_cterm_D_V, val_cterm_C_V]
    show transposeCode (W.tr.code k) = _
    rw [← transposeCode_code W k, transposeCode_transposeCode]

theorem revalue_val_uT_wT_swap (W : W3) (k : V) :
    revalue ((Semiterm.lMap swap W.uT).val (s := stdReadingV V) ![] Empty.elim)
      ((Semiterm.lMap swap W.wT).val (s := stdReadingV V) ![] Empty.elim) (W.can.code k) = W.tr.code k := by
  unfold uT wT can
  by_cases h : W.orig
  · rw [if_pos h, if_pos h, if_pos h, lMap_swap_cterm_C, lMap_swap_cterm_D, val_cterm_D_V, val_cterm_C_V]
    show transposeCode (W.code k) = _
    rw [transposeCode_code]
  · rw [if_neg h, if_neg h, if_neg h, lMap_swap_cterm_D, lMap_swap_cterm_C, val_cterm_C_V, val_cterm_D_V,
      revalue_zero_one]

theorem canonical_tr_code (W : W3) {k : V} (hk : ((W.K : ℕ) : V) ≤ k) : canonical (W.tr.code k) = W.can.code k := by
  rw [← transposeCode_code, canonical_transposeCode, canonical_code W hk]

theorem revalueU_tr_code (W : W3) {k : V} (hk : ((W.K : ℕ) : V) ≤ k) :
    revalueU (W.tr.code k) = (⌜Semiterm.lMap swap W.uT⌝ : V) := by
  have e : transposeCode (W.tr.code k) = W.code k := by rw [← transposeCode_code, transposeCode_transposeCode]
  unfold revalueU uT
  rw [e]
  by_cases h : W.orig
  · rw [if_neg (lt_asymm (code_lt_tr W hk h)), if_pos (code_lt_tr W hk h), if_pos h, lMap_swap_cterm_C, quote_cterm_D]
  · rw [if_pos (tr_lt_code W hk h), if_neg h, lMap_swap_cterm_D, quote_cterm_C]

theorem revalueW_tr_code (W : W3) {k : V} (hk : ((W.K : ℕ) : V) ≤ k) :
    revalueW (W.tr.code k) = (⌜Semiterm.lMap swap W.wT⌝ : V) := by
  have e : transposeCode (W.tr.code k) = W.code k := by rw [← transposeCode_code, transposeCode_transposeCode]
  unfold revalueW wT
  rw [e]
  by_cases h : W.orig
  · rw [if_neg (lt_asymm (code_lt_tr W hk h)), if_pos (code_lt_tr W hk h), if_pos h, lMap_swap_cterm_D, quote_cterm_C]
  · rw [if_pos (tr_lt_code W hk h), if_neg h, lMap_swap_cterm_C, quote_cterm_D]

/-! #### The towers -/

/-- The one-variable ℒₒᵣ-term of the three-stage watch. -/
noncomputable def T1 (W : W3) : Semiterm ℒₒᵣ Empty 1 :=
  iteT1 (simT1 (botT1 W.s₀.T1) (botT1 W.s₀.T1)) W.t₀ (constT1 W.p₀)
    (iteT1 (simT1 (botT1 W.s₁.T1) (botT1 W.s₁.T1)) W.t₁ (constT1 W.p₁)
      (iteT1 (simT1 (botT1 (W.S.T1 0)) (botT1 (W.S.T1 0))) W.t₂ (constT1 W.p₂) (constT1 W.q₂)))

lemma val_T1_V (W : W3) (k : V) : (W.T1).val (s := standardModel V) ![k] Empty.elim = W.code k := by
  rw [T1, val_iteT1_V, val_simT1_V, val_botT1_V, SM.val_T1_V, val_constT1_V, val_iteT1_V, val_simT1_V, val_botT1_V,
    SM.val_T1_V, val_constT1_V, val_iteT1_V, val_simT1_V, val_botT1_V, Sys2c.val_T1_V, val_constT1_V, val_constT1_V]
  rfl

lemma termSubst_T1 (W : W3) (k : V) :
    termSubst LAct (binNumeral k ∷ (0 : V)) (⌜(Rew.emb W.T1 : SyntacticSemiterm ℒₒᵣ 1)⌝ : V) = codeTerm (W.code k) := by
  rw [T1]
  exact termSubst_iteT1 _ W.t₀
    (termSubst_simT1 _ (termSubst_botT1 _ (SM.termSubst_T1 _ _)) (termSubst_botT1 _ (SM.termSubst_T1 _ _)))
    (termSubst_constT1 _ _)
    (termSubst_iteT1 _ W.t₁
      (termSubst_simT1 _ (termSubst_botT1 _ (SM.termSubst_T1 _ _)) (termSubst_botT1 _ (SM.termSubst_T1 _ _)))
      (termSubst_constT1 _ _)
      (termSubst_iteT1 _ W.t₂
        (termSubst_simT1 _ (termSubst_botT1 _ (Sys2c.termSubst_T1 _ 0 _)) (termSubst_botT1 _ (Sys2c.termSubst_T1 _ 0 _)))
        (termSubst_constT1 _ _) (termSubst_constT1 _ _)))

/-- **The frame tower** of the bot-wrapped three-stage watch `pBot (W.code k)`. -/
noncomputable def TX (W : W3) : Semiterm LAct Empty 1 := Semiterm.lMap emb (botT1 W.can.T1)

lemma lMap_swap_TX (W : W3) : Semiterm.lMap swap W.TX = W.TX := term_lMap_swap_emb _

theorem val_TX_V (W : W3) {k : V} (hk : ((W.K : ℕ) : V) ≤ k) :
    W.TX.val (s := stdReadingV V) ![k] Empty.elim = canonical (pBot (W.code k)) := by
  unfold TX
  rw [Semiterm.val_lMap, stdReadingV_lMap_emb, val_botT1_V, val_T1_V, canonical_pBot, canonical_code W hk]

theorem hX_TX (W : W3) {k : V} (hk : ((W.K : ℕ) : V) ≤ k) :
    termSubst LAct (binNumeral k ∷ (0 : V)) (⌜(Rew.emb W.TX : SyntacticSemiterm LAct 1)⌝ : V) =
      codeTerm (canonical (pBot (W.code k))) := by
  unfold TX
  rw [term_emb_lMap_emb_n, quote_term_lMap_emb, termSubst_botT1 _ (termSubst_T1 _ _), canonical_pBot, canonical_code W hk]

theorem descVal_TX (W : W3) {k : V} (hk : ((W.K : ℕ) : V) ≤ k) : descVal W.TX W.uT W.wT k = pBot (W.code k) := by
  rw [descVal_def, val_TX_V W hk, canonical_pBot, revalue_bot, canonical_code W hk, revalue_val_uT_wT]

theorem descVal_TX_T (W : W3) {k : V} (hk : ((W.K : ℕ) : V) ≤ k) :
    descVal (Semiterm.lMap swap W.TX) (Semiterm.lMap swap W.uT) (Semiterm.lMap swap W.wT) k = pBot (W.tr.code k) := by
  rw [descVal_def, lMap_swap_TX, val_TX_V W hk, canonical_pBot, revalue_bot, canonical_code W hk, revalue_val_uT_wT_swap]

/-- **The frame tower describes the bot-wrapped three-stage watch above the threshold.** -/
theorem describesBot (W : W3) : DescribesAbove W.K W.TX W.uT W.wT where
  hX := fun V _ _ k hk ↦ by rw [descVal_TX W hk]; exact hX_TX W hk
  hU := fun V _ _ k hk ↦ by rw [descVal_TX W hk, revalueU_pBot, revalueU_code W hk]
  hW := fun V _ _ k hk ↦ by rw [descVal_TX W hk, revalueW_pBot, revalueW_code W hk]
  hT := fun V _ _ k hk ↦ by rw [descVal_TX_T W hk, descVal_TX W hk, transposeCode_pBot, transposeCode_code]

/-- The transposed description of the bot-wrapped three-stage watch, above the threshold. -/
theorem describesBotT (W : W3) :
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

end W3

/-! ### 4. The stored description of a three-stage watch -/

lemma codeTermMetaAbs_W3 (W : W3) (K : ℕ) : codeTermMetaAbs K (W.code K) = W.T1 := by
  unfold W3.code W3.mid W3.inner W3.T1
  simp only [natCast_nat]
  rw [codeTermMetaAbs_ite, codeTermMetaAbs_sim, codeTermMetaAbs_bot, codeTermMetaAbs_SM, codeTermMetaAbs_const,
    codeTermMetaAbs_ite, codeTermMetaAbs_sim, codeTermMetaAbs_bot, codeTermMetaAbs_SM, codeTermMetaAbs_const,
    codeTermMetaAbs_ite, codeTermMetaAbs_sim, codeTermMetaAbs_bot]
  have hS := codeTermMetaAbs_Sys2c W.S 0 K (W.hP K)
  rw [hS, codeTermMetaAbs_const, codeTermMetaAbs_const]
  rfl

lemma codeTermMetaAbs_botW3 (W : W3) (K : ℕ) : codeTermMetaAbs K (pBot (W.code K)) = botT1 W.T1 := by
  rw [codeTermMetaAbs_bot, codeTermMetaAbs_W3]; rfl

namespace W3

/-- **The fixed closed description of the three-stage watch**: the tower with the budget slot in place of the budget. -/
noncomputable def Dfix (W : W3) : Semisentence LAct 14 :=
  descF #1 (Rew.subst ![#8] (Semiterm.lMap emb (botT1 W.can.T1))) (cl W.uT) (cl W.wT)

theorem canonical_code_nat (W : W3) {k : ℕ} (hk : W.K ≤ k) : canonical (W.code k) = W.can.code k :=
  W3.canonical_code W (le_def.mpr (Nat.eq_or_lt_of_le (by rw [natCast_nat]; exact hk)))

theorem code_lt_tr_nat (W : W3) {k : ℕ} (hk : W.K ≤ k) (h : W.orig) : W.code k < W.tr.code k :=
  W3.code_lt_tr W (le_def.mpr (Nat.eq_or_lt_of_le (by rw [natCast_nat]; exact hk))) h

theorem tr_lt_code_nat (W : W3) {k : ℕ} (hk : W.K ≤ k) (h : ¬ W.orig) : W.tr.code k < W.code k :=
  W3.tr_lt_code W (le_def.mpr (Nat.eq_or_lt_of_le (by rw [natCast_nat]; exact hk))) h

theorem canonical_tr_code_nat (W : W3) {k : ℕ} (hk : W.K ≤ k) : canonical (W.tr.code k) = W.can.code k :=
  W3.canonical_tr_code W (le_def.mpr (Nat.eq_or_lt_of_le (by rw [natCast_nat]; exact hk)))

theorem revalueUMeta_code (W : W3) {k : ℕ} (hk : W.K ≤ k) : revalueUMeta (W.code k) = W.uT := by
  unfold revalueUMeta W3.uT
  rw [transposeCode_code]
  by_cases h : W.orig
  · rw [if_pos (code_lt_tr_nat W hk h), if_pos h]
  · rw [if_neg (lt_asymm (tr_lt_code_nat W hk h)), if_pos (tr_lt_code_nat W hk h), if_neg h]

theorem revalueWMeta_code (W : W3) {k : ℕ} (hk : W.K ≤ k) : revalueWMeta (W.code k) = W.wT := by
  unfold revalueWMeta W3.wT
  rw [transposeCode_code]
  by_cases h : W.orig
  · rw [if_pos (code_lt_tr_nat W hk h), if_pos h]
  · rw [if_neg (lt_asymm (tr_lt_code_nat W hk h)), if_pos (tr_lt_code_nat W hk h), if_neg h]

theorem revalueUMeta_tr_code (W : W3) {k : ℕ} (hk : W.K ≤ k) :
    revalueUMeta (W.tr.code k) = Semiterm.lMap swap W.uT := by
  have e : transposeCode (W.tr.code k) = W.code k := by rw [← transposeCode_code, transposeCode_transposeCode]
  unfold revalueUMeta W3.uT
  rw [e]
  by_cases h : W.orig
  · rw [if_neg (lt_asymm (code_lt_tr_nat W hk h)), if_pos (code_lt_tr_nat W hk h), if_pos h, lMap_swap_cterm_C]
  · rw [if_pos (tr_lt_code_nat W hk h), if_neg h, lMap_swap_cterm_D]

theorem revalueWMeta_tr_code (W : W3) {k : ℕ} (hk : W.K ≤ k) :
    revalueWMeta (W.tr.code k) = Semiterm.lMap swap W.wT := by
  have e : transposeCode (W.tr.code k) = W.code k := by rw [← transposeCode_code, transposeCode_transposeCode]
  unfold revalueWMeta W3.wT
  rw [e]
  by_cases h : W.orig
  · rw [if_neg (lt_asymm (code_lt_tr_nat W hk h)), if_pos (code_lt_tr_nat W hk h), if_pos h, lMap_swap_cterm_D]
  · rw [if_pos (tr_lt_code_nat W hk h), if_neg h, lMap_swap_cterm_C]

/-- **The stored description of the bot-wrapped three-stage watch is constant above the threshold.** -/
theorem closedDescAt_code (W : W3) {k : ℕ} (hk : W.K ≤ k) : closedDescAt (some k) (pBot (W.code k)) = W.Dfix := by
  unfold closedDescAt Dfix
  rw [canonicalSlot_some]
  unfold canonicalAbs
  rw [canonical_pBot, canonical_code_nat W hk, codeTermMetaAbs_botW3, revalueUMeta_pBot, revalueWMeta_pBot,
    revalueUMeta_code W hk, revalueWMeta_code W hk]

/-- **The abstracted description denotes the three-stage watch at the budget `k`, in every model.** -/
theorem absVal_code (W : W3) {K : ℕ} (hK : W.K ≤ K) (k : V) : absVal K (pBot (W.code K)) k = pBot (W.code k) := by
  rw [absVal_def, canonical_pBot, canonical_code_nat W hK, codeTermMetaAbs_botW3, revalueUMeta_pBot, revalueWMeta_pBot,
    revalueUMeta_code W hK, revalueWMeta_code W hK, val_botT1_V, W3.val_T1_V, revalue_bot, revalue_val_uT_wT]

/-- …and the abstracted description of its TRANSPOSITION denotes the transposed three-stage watch. -/
theorem absVal_tr_code (W : W3) {K : ℕ} (hK : W.K ≤ K) (k : V) :
    absVal K (transposeCode (pBot (W.code K))) k = pBot (W.tr.code k) := by
  rw [absVal_def, transposeCode_pBot, transposeCode_code, canonical_pBot, canonical_tr_code_nat W hK,
    codeTermMetaAbs_botW3, revalueUMeta_pBot, revalueWMeta_pBot, revalueUMeta_tr_code W hK, revalueWMeta_tr_code W hK,
    val_botT1_V, W3.val_T1_V, revalue_bot, revalue_val_uT_wT_swap]

end W3

end ArithS.Tau
