import PrisonersDilemma.Bots.LlmGenerations.JustBot
import PrisonersDilemma.Bots.DupocBot
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Axioms
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Theorems.Helpers

open PD
open PD.Axioms
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

theorem llm_outcome_JustBot_vs_DupocBot :
    ∃ k₂, ∀ k, k₂ < k →
      ∃ fuel, outcome fuel (JustBot k) (DupocBot k) = some (.C, .C) := by
  let φ : Nat → Formula :=
    fun k => Formula.plays (DupocBot k) (.bot (DupocBot k)) .C
  let f : Nat → Nat := fun k => k
  have hMono : ∀ a b : Nat, a ≤ b → f a ≤ f b := fun _ _ h => h
  have hLog : ∃ c kHat, c > 0 ∧ ∀ k, k > kHat → f k > c * Nat.log2 k := by
    refine ⟨1, 0, Nat.zero_lt_one, ?_⟩
    intro k hk
    have hlog : Nat.log2 k < k := by
      rw [Nat.log2_lt (Nat.pos_iff_ne_zero.mp hk)]
      exact Nat.lt_two_pow_self
    simpa using hlog
  have hLoeb : ∀ k, k > 0 → ∃ m, Provable m (.impl (.box (f k) (φ k)) (φ k)) := by
    intro k _
    have d1 : Derivation
        (.impl (.box k (Formula.plays (DupocBot k) (.bot (DupocBot k)) .C))
               (Formula.plays (.bot (DupocBot k)) (DupocBot k) .C)) :=
      Derivation.botSearchStep k (.plays .opp .self .C) .C .D
        (.bot (DupocBot k)) (DupocBot k) rfl
    have d3 : Derivation
        (.impl (.box k (Formula.plays (.bot (DupocBot k)) (DupocBot k) .C))
               (Formula.plays (DupocBot k) (.bot (DupocBot k)) .C)) :=
      Derivation.searchBranch k (.plays .opp .self .C) .C .D
        (DupocBot k) (.bot (DupocBot k)) rfl
    have d2 : Provable k
        (.impl (Formula.plays (.bot (DupocBot k)) (DupocBot k) .C)
               (.box k (Formula.plays (.bot (DupocBot k)) (DupocBot k) .C))) :=
      atom_box_provable_impl k (.bot (DupocBot k)) (DupocBot k) .C
    have P1 : Provable
        (Formula.impl (.box k (Formula.plays (DupocBot k) (.bot (DupocBot k)) .C))
                      (Formula.plays (.bot (DupocBot k)) (DupocBot k) .C)).size
        (.impl (.box k (Formula.plays (DupocBot k) (.bot (DupocBot k)) .C))
               (Formula.plays (.bot (DupocBot k)) (DupocBot k) .C)) :=
      Provable.struct ⟨d1, Nat.le_refl _⟩
    have P3 : Provable
        (Formula.impl (.box k (Formula.plays (.bot (DupocBot k)) (DupocBot k) .C))
                      (Formula.plays (DupocBot k) (.bot (DupocBot k)) .C)).size
        (.impl (.box k (Formula.plays (.bot (DupocBot k)) (DupocBot k) .C))
               (Formula.plays (DupocBot k) (.bot (DupocBot k)) .C)) :=
      Provable.struct ⟨d3, Nat.le_refl _⟩
    have BA : Provable
        (Formula.impl (Formula.plays (.bot (DupocBot k)) (DupocBot k) .C)
                      (Formula.plays (DupocBot k) (.bot (DupocBot k)) .C)).size
        (.impl (Formula.plays (.bot (DupocBot k)) (DupocBot k) .C)
               (Formula.plays (DupocBot k) (.bot (DupocBot k)) .C)) :=
      Provable.implTrans
        (Formula.plays (.bot (DupocBot k)) (DupocBot k) .C)
        (.box k (Formula.plays (.bot (DupocBot k)) (DupocBot k) .C))
        (Formula.plays (DupocBot k) (.bot (DupocBot k)) .C)
        k _ d2 P3 (Nat.le_refl _)
    have Final : Provable
        (Formula.impl (.box k (Formula.plays (DupocBot k) (.bot (DupocBot k)) .C))
                      (Formula.plays (DupocBot k) (.bot (DupocBot k)) .C)).size
        (.impl (.box k (Formula.plays (DupocBot k) (.bot (DupocBot k)) .C))
               (Formula.plays (DupocBot k) (.bot (DupocBot k)) .C)) :=
      Provable.implTrans
        (.box k (Formula.plays (DupocBot k) (.bot (DupocBot k)) .C))
        (Formula.plays (.bot (DupocBot k)) (DupocBot k) .C)
        (Formula.plays (DupocBot k) (.bot (DupocBot k)) .C)
        _ _ P1 BA (Nat.le_refl _)
    exact ⟨_, Final⟩
  obtain ⟨k₂, hk₂⟩ := PBLT φ f 0 hMono hLog hLoeb
  refine ⟨max k₂ (atom_cost 2), ?_⟩
  intro k hk
  have hkk2 : k₂ < k := by
    have := Nat.le_max_left k₂ (atom_cost 2); omega
  have hk2c : atom_cost 2 ≤ k := by
    have := Nat.le_max_right k₂ (atom_cost 2); omega
  obtain ⟨m, hm⟩ := hk₂ k hkk2
  have hAint : (φ k).interp := Provable_sound m _ hm
  obtain ⟨n, hplayA⟩ := hAint
  have hBtrue :
      proofSearch k (Formula.plays (.bot (DupocBot k)) (DupocBot k) .C) = true := by
    cases hps : proofSearch k (Formula.plays (.bot (DupocBot k)) (DupocBot k) .C) with
    | true => rfl
    | false =>
      exfalso
      have hgen : ∀ N, play N (DupocBot k) (.bot (DupocBot k)) = some .C → False := by
        intro N hN
        cases N with
        | zero => simp [play, eval] at hN
        | succ N0 =>
          cases N0 with
          | zero => simp [play, eval, DupocBot, Prog.subst, Formula.subst] at hN
          | succ N1 =>
            have hd : play (N1 + 2) (DupocBot k) (.bot (DupocBot k)) = some .D := by
              show eval (N1 + 2) (DupocBot k) (.bot (DupocBot k)) (DupocBot k) = some .D
              unfold DupocBot at hps ⊢
              simp [eval, Prog.subst, Formula.subst, hps]
            rw [hd] at hN; cases hN
      exact hgen n hplayA
  have hAplay2 : play 2 (DupocBot k) (.bot (DupocBot k)) = some .C := by
    show eval 2 (DupocBot k) (.bot (DupocBot k)) (DupocBot k) = some .C
    unfold DupocBot at hBtrue ⊢
    simp [eval, Prog.subst, Formula.subst, hBtrue]
  have hatomA : proofSearch (atom_cost 2)
      (Formula.plays (DupocBot k) (.bot (DupocBot k)) .C) = true :=
    (proofSearch_spec _ _).2
      (Provable.atom (atom_complete (DupocBot k) (.bot (DupocBot k)) .C 2 hAplay2))
  have hGA : proofSearch k
      (Formula.plays (DupocBot k) (.bot (DupocBot k)) .C) = true :=
    proofSearch_monotone _ _ _ hk2c hatomA
  have hJ : play 2 (JustBot k) (DupocBot k) = some .C := by
    show eval 2 (JustBot k) (DupocBot k) (JustBot k) = some .C
    unfold JustBot
    simp [eval, Prog.subst, Formula.subst, hGA]
  have hJatom : proofSearch (atom_cost 2)
      (Formula.plays (JustBot k) (DupocBot k) .C) = true :=
    (proofSearch_spec _ _).2
      (Provable.atom (atom_complete (JustBot k) (DupocBot k) .C 2 hJ))
  have hGJ : proofSearch k
      (Formula.plays (JustBot k) (DupocBot k) .C) = true :=
    proofSearch_monotone _ _ _ hk2c hJatom
  have hD : play 2 (DupocBot k) (JustBot k) = some .C := by
    show eval 2 (DupocBot k) (JustBot k) (DupocBot k) = some .C
    unfold DupocBot at hGJ ⊢
    simp [eval, Prog.subst, Formula.subst, hGJ]
  exact ⟨2, outcome_of_plays _ _ _ _ _ hJ hD⟩

end PD.Theorems
