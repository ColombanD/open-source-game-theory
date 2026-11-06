import ArithS.Tau.Entangled.Loeb

/-!
# ArithS.Tau.Entangled.Congr — an `.opp`-free member guard is consulted at the SAME code in every frame

No compiled member guard mentions `.opp` (`sysGo`: the pronoun `.self` and the partner pronouns only), so the
opp-slots `#3..#5` of its thirteen-variable template do not occur, and the code a member consults in the
frame `(me, opp)` is the code it consults in `(me, opp')`. This module proves it at the level of the guard
formulas `Sys2.q`: `q_congr_opp : S.q j i i' = S.q j i i''` for an `.opp`-free `.impl`/`.plays` guard over
pronouns and pronoun-free closed programs (`progAux13_subst_congr`, index by index), so that a box found in a
member's self-play frame is a box in every frame it is probed in — the fact `Cells/Columns.lean`'s
`guardOf_implConst_frame` states on the fragment, here on the member slots.
-/

set_option linter.constructorNameAsVariable false

namespace ArithS.Tau

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1
open LAct

/-! ### 1. `progAux13` reads the opp-triple only for `.opp` -/

/-- The description of a non-`.opp` program under two substitutions agreeing off the opp slots `#4..#6`. -/
lemma progAux13_subst_congr {m : ℕ} {p : PD.Prog} (hp : p ≠ .opp) (c : ℕ) (w w' : Fin 14 → Semiterm LAct Empty m)
    (h : ∀ i : Fin 14, i ≠ 4 → i ≠ 5 → i ≠ 6 → w i = w' i) :
    progAux13 p c ⇜ w = progAux13 p c ⇜ w' := by
  have h0 := h 0 (by decide) (by decide) (by decide)
  by_cases hpr : pronounP p = true
  · rcases pronounP_cases hpr with rfl | rfl | rfl | rfl
    · rw [progAux13_selfIdx0]
      unfold Rewriting.subst
      rw [rew_descF, rew_descF]
      show descF (Rew.bShift (w 0)) (Rew.bShift (w 8)) (Rew.bShift (w 9)) (Rew.bShift (w 10)) =
        descF (Rew.bShift (w' 0)) (Rew.bShift (w' 8)) (Rew.bShift (w' 9)) (Rew.bShift (w' 10))
      rw [h0, h 8 (by decide) (by decide) (by decide), h 9 (by decide) (by decide) (by decide),
        h 10 (by decide) (by decide) (by decide)]
    · rw [progAux13_selfIdx1]
      unfold Rewriting.subst
      rw [rew_descF, rew_descF]
      show descF (Rew.bShift (w 0)) (Rew.bShift (w 11)) (Rew.bShift (w 12)) (Rew.bShift (w 13)) =
        descF (Rew.bShift (w' 0)) (Rew.bShift (w' 11)) (Rew.bShift (w' 12)) (Rew.bShift (w' 13))
      rw [h0, h 11 (by decide) (by decide) (by decide), h 12 (by decide) (by decide) (by decide),
        h 13 (by decide) (by decide) (by decide)]
    · rw [progAux13_botSelfIdx0]
      unfold Rewriting.subst
      rw [rew_descF, rew_descF, rew_pBotTerm, rew_pBotTerm]
      show descF (Rew.bShift (w 0)) (pBotTerm (Rew.bShift (w 8))) (Rew.bShift (w 9)) (Rew.bShift (w 10)) =
        descF (Rew.bShift (w' 0)) (pBotTerm (Rew.bShift (w' 8))) (Rew.bShift (w' 9)) (Rew.bShift (w' 10))
      rw [h0, h 8 (by decide) (by decide) (by decide), h 9 (by decide) (by decide) (by decide),
        h 10 (by decide) (by decide) (by decide)]
    · rw [progAux13_botSelfIdx1]
      unfold Rewriting.subst
      rw [rew_descF, rew_descF, rew_pBotTerm, rew_pBotTerm]
      show descF (Rew.bShift (w 0)) (pBotTerm (Rew.bShift (w 11))) (Rew.bShift (w 12)) (Rew.bShift (w 13)) =
        descF (Rew.bShift (w' 0)) (pBotTerm (Rew.bShift (w' 11))) (Rew.bShift (w' 12)) (Rew.bShift (w' 13))
      rw [h0, h 11 (by decide) (by decide) (by decide), h 12 (by decide) (by decide) (by decide),
        h 13 (by decide) (by decide) (by decide)]
  · by_cases h1 : p = .self
    · subst h1
      rw [progAux13_self]
      unfold Rewriting.subst
      rw [rew_descF, rew_descF]
      show descF (Rew.bShift (w 0)) (Rew.bShift (w 1)) (Rew.bShift (w 2)) (Rew.bShift (w 3)) =
        descF (Rew.bShift (w' 0)) (Rew.bShift (w' 1)) (Rew.bShift (w' 2)) (Rew.bShift (w' 3))
      rw [h0, h 1 (by decide) (by decide) (by decide), h 2 (by decide) (by decide) (by decide),
        h 3 (by decide) (by decide) (by decide)]
    · rw [progAux13_of_ne h1 hp (Bool.eq_false_iff.mpr hpr), closedDesc13_subst, closedDesc13_subst, h0]

/-! ### 2. The templates of `.opp`-free guards -/

/-- The `.plays` template of two non-`.opp` programs under two substitutions agreeing off the opp slots `#3..#5`. -/
theorem template13_plays_congr {m : ℕ} {p q : PD.Prog} (hp : p ≠ .opp) (hq : q ≠ .opp) (a : PD.Action)
    (v v' : Fin 13 → Semiterm LAct Empty m) (h : ∀ i : Fin 13, i ≠ 3 → i ≠ 4 → i ≠ 5 → v i = v' i) :
    template13 (.plays p q a) ⇜ v = template13 (.plays p q a) ⇜ v' := by
  rw [template13_plays]
  unfold progGraph13
  simp only [Rewriting.app_exs, Rew.q_subst, LogicalConnective.HomClass.map_and, rew_subst_eq]
  congr 4
  · refine progAux13_subst_congr hp _ _ _ ?_
    intro i h4 h5 h6
    fin_cases i
    · rfl
    · simp [h 0 (by decide) (by decide) (by decide)]
    · simp [h 1 (by decide) (by decide) (by decide)]
    · simp [h 2 (by decide) (by decide) (by decide)]
    · exact absurd rfl h4
    · exact absurd rfl h5
    · exact absurd rfl h6
    · simp [h 6 (by decide) (by decide) (by decide)]
    · simp [h 7 (by decide) (by decide) (by decide)]
    · simp [h 8 (by decide) (by decide) (by decide)]
    · simp [h 9 (by decide) (by decide) (by decide)]
    · simp [h 10 (by decide) (by decide) (by decide)]
    · simp [h 11 (by decide) (by decide) (by decide)]
    · simp [h 12 (by decide) (by decide) (by decide)]
  · congr 1
    · refine progAux13_subst_congr hq _ _ _ ?_
      intro i h4 h5 h6
      fin_cases i
      · rfl
      · simp [h 0 (by decide) (by decide) (by decide)]
      · simp [h 1 (by decide) (by decide) (by decide)]
      · simp [h 2 (by decide) (by decide) (by decide)]
      · exact absurd rfl h4
      · exact absurd rfl h5
      · exact absurd rfl h6
      · simp [h 6 (by decide) (by decide) (by decide)]
      · simp [h 7 (by decide) (by decide) (by decide)]
      · simp [h 8 (by decide) (by decide) (by decide)]
      · simp [h 9 (by decide) (by decide) (by decide)]
      · simp [h 10 (by decide) (by decide) (by decide)]
      · simp [h 11 (by decide) (by decide) (by decide)]
      · simp [h 12 (by decide) (by decide) (by decide)]
    · congr 1
      funext i
      fin_cases i
      · rfl
      · rfl
      · rfl
      · rfl
      · show Rew.subst _ (cl _) = Rew.subst _ (cl _)
        rw [rew_cl, rew_cl]

theorem template13_impl_congr {m : ℕ} {φ ψ : PD.Formula} (v v' : Fin 13 → Semiterm LAct Empty m)
    (hφ : template13 φ ⇜ v = template13 φ ⇜ v') (hψ : template13 ψ ⇜ v = template13 ψ ⇜ v') :
    template13 (.impl φ ψ) ⇜ v = template13 (.impl φ ψ) ⇜ v' := by
  rw [template13_impl]
  unfold Rewriting.subst
  rw [LogicalConnective.HomClass.map_imply, LogicalConnective.HomClass.map_imply]
  unfold Rewriting.subst at hφ hψ
  rw [hφ, hψ]

/-! ### 3. The guard formulas: the opp-frame is irrelevant -/

namespace Sys2

/-- **A member guard over non-`.opp` programs is the same formula in every opp-frame.** -/
theorem q_congr_opp_plays (S : Sys2) {j : ℕ} {pa pb : PD.Prog} (hpa : pa ≠ .opp) (hpb : pb ≠ .opp) {a : PD.Action}
    (hg : (S.mem j).g = template13 (.plays pa pb a)) (i i' i'' : ℕ) : S.q j i i' = S.q j i i'' := by
  unfold Sys2.q
  rw [hg]
  unfold qT13
  refine template13_plays_congr hpa hpb a _ _ ?_
  intro i h3 h4 h5
  fin_cases i
  · show S.TX i = S.TX i
    rfl
  · show (cl S.uT : Semiterm LAct Empty 1) = (cl S.uT : Semiterm LAct Empty 1)
    rfl
  · show (cl S.wT : Semiterm LAct Empty 1) = (cl S.wT : Semiterm LAct Empty 1)
    rfl
  · exact absurd rfl h3
  · show (cl S.uT : Semiterm LAct Empty 1) = (cl S.uT : Semiterm LAct Empty 1)
    rfl
  · show (cl S.wT : Semiterm LAct Empty 1) = (cl S.wT : Semiterm LAct Empty 1)
    rfl
  · show (#0 : Semiterm LAct Empty 1) = (#0 : Semiterm LAct Empty 1)
    rfl
  · show S.TM 0 = S.TM 0
    rfl
  · show (cl S.uT : Semiterm LAct Empty 1) = (cl S.uT : Semiterm LAct Empty 1)
    rfl
  · show (cl S.wT : Semiterm LAct Empty 1) = (cl S.wT : Semiterm LAct Empty 1)
    rfl
  · show S.TM 1 = S.TM 1
    rfl
  · show (cl S.uT : Semiterm LAct Empty 1) = (cl S.uT : Semiterm LAct Empty 1)
    rfl
  · show (cl S.wT : Semiterm LAct Empty 1) = (cl S.wT : Semiterm LAct Empty 1)
    rfl

theorem q_congr_opp_impl (S : Sys2) {j : ℕ} {pa pb pa' pb' : PD.Prog} (hpa : pa ≠ .opp) (hpb : pb ≠ .opp) (hpa' : pa' ≠ .opp)
    (hpb' : pb' ≠ .opp) {a a' : PD.Action}
    (hg : (S.mem j).g = template13 (.impl (.plays pa pb a) (.plays pa' pb' a'))) (i i' i'' : ℕ) : S.q j i i' = S.q j i i'' := by
  unfold Sys2.q
  rw [hg]
  unfold qT13
  have hv : ∀ i₀ : Fin 13, i₀ ≠ 3 → i₀ ≠ 4 → i₀ ≠ 5 →
      (![S.TX i, cl S.uT, cl S.wT, S.TX i', cl S.uT, cl S.wT, #0, S.TM 0, cl S.uT, cl S.wT, S.TM 1, cl S.uT, cl S.wT] :
        Fin 13 → Semiterm LAct Empty 1) i₀ =
      ![S.TX i, cl S.uT, cl S.wT, S.TX i'', cl S.uT, cl S.wT, #0, S.TM 0, cl S.uT, cl S.wT, S.TM 1, cl S.uT, cl S.wT] i₀ := by
    intro i₀ h3 h4 h5
    fin_cases i₀
    · show S.TX i = S.TX i
      rfl
    · show (cl S.uT : Semiterm LAct Empty 1) = (cl S.uT : Semiterm LAct Empty 1)
      rfl
    · show (cl S.wT : Semiterm LAct Empty 1) = (cl S.wT : Semiterm LAct Empty 1)
      rfl
    · exact absurd rfl h3
    · show (cl S.uT : Semiterm LAct Empty 1) = (cl S.uT : Semiterm LAct Empty 1)
      rfl
    · show (cl S.wT : Semiterm LAct Empty 1) = (cl S.wT : Semiterm LAct Empty 1)
      rfl
    · show (#0 : Semiterm LAct Empty 1) = (#0 : Semiterm LAct Empty 1)
      rfl
    · show S.TM 0 = S.TM 0
      rfl
    · show (cl S.uT : Semiterm LAct Empty 1) = (cl S.uT : Semiterm LAct Empty 1)
      rfl
    · show (cl S.wT : Semiterm LAct Empty 1) = (cl S.wT : Semiterm LAct Empty 1)
      rfl
    · show S.TM 1 = S.TM 1
      rfl
    · show (cl S.uT : Semiterm LAct Empty 1) = (cl S.uT : Semiterm LAct Empty 1)
      rfl
    · show (cl S.wT : Semiterm LAct Empty 1) = (cl S.wT : Semiterm LAct Empty 1)
      rfl
  exact template13_impl_congr _ _ (template13_plays_congr hpa hpb a _ _ hv) (template13_plays_congr hpa' hpb' a' _ _ hv)

end Sys2

end ArithS.Tau
