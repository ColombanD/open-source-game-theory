import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Bots.DupocBot
import PrisonersDilemma.Bots.LlmGenerations.JustBot
import PrisonersDilemma.Theorems.DupocBot.Helpers
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Base.Asymptotics
import PrisonersDilemma.Theorems.JustBot.Helpers

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

-- DupocBot --

theorem outcome_JustBot_vs_DupocBot :
    ∃ k₂, ∀ k, k₂ < k →
      ∃ fuel, outcome fuel (JustBot k) (DupocBot k) = some (.C, .C) := by
  let φ : Nat → Formula :=
    fun k => Formula.plays (DupocBot k) (.bot (DupocBot k)) .C
-- The two transparency legs, transcript-tight; `mutual_pblt_engine_id` lowers the premise
  -- subscript internally and runs the Löb chain (the old same-subscript `mutual_loeb`
  -- factoring is underivable under transcript cost).
  have legPD : ∀ k, Pf (30 * Nat.log2 k + 300)
      (.impl (.box k (Formula.plays (DupocBot k) (.bot (DupocBot k)) .C))
             (Formula.plays (.bot (DupocBot k)) (DupocBot k) .C)) := by
    intro k
    refine Pf.botSearchStep k (.plays .opp .self .C) .C .D (.bot (DupocBot k)) (DupocBot k) rfl ?_
    simp only [Formula.subst, Prog.subst, numCost, Formula.size, Prog.size, DupocBot]
    omega
  have legDP : ∀ k, Pf (30 * Nat.log2 k + 300)
      (.impl (.box k (Formula.plays (.bot (DupocBot k)) (DupocBot k) .C))
             (Formula.plays (DupocBot k) (.bot (DupocBot k)) .C)) := by
    intro k
    refine Pf.searchBranch k (.plays .opp .self .C) .C .D (DupocBot k) (.bot (DupocBot k)) rfl ?_
    simp only [Formula.subst, Prog.subst, numCost, Formula.size, Prog.size, DupocBot]
    omega
  have hφsz : ∀ k, (φ k).size ≤ 100 * Nat.log2 k + 1000 := by
    intro k
    show (Formula.plays (DupocBot k) (.bot (DupocBot k)) .C).size ≤ _
    simp only [numCost, Formula.size, Prog.size, DupocBot]
    omega
  have hsB : ∀ k,
      (Formula.plays (.bot (DupocBot k)) (DupocBot k) .C).size ≤ 100 * Nat.log2 k + 1000 := by
    intro k
    simp only [numCost, Formula.size, Prog.size, DupocBot]
    omega
  have hpb : ∀ k, 30 * Nat.log2 k + 300 ≤ 100 * Nat.log2 k + 1000 := fun k => by omega
  obtain ⟨k₂, hk₂⟩ := mutual_pblt_engine_id φ
    (fun k => Formula.plays (.bot (DupocBot k)) (DupocBot k) .C)
    (fun k => 30 * Nat.log2 k + 300) (fun k => 30 * Nat.log2 k + 300) 0
    hφsz hsB hpb hpb (fun k _ => legPD k) (fun k _ => legDP k)
  obtain ⟨KL, hKL⟩ := linear_log2_add_le 1 3
  refine ⟨max k₂ KL, ?_⟩
  intro k hk
  have hkk2 : k₂ < k := by
    have := Nat.le_max_left k₂ KL; omega
  have hKLk : Nat.log2 k + 3 ≤ k := by
    have h1 := Nat.le_max_right k₂ KL
    have := hKL k (by omega)
    omega
  obtain ⟨m, hm⟩ := hk₂ k hkk2
  have hAint : (φ k).interp := Pf_sound m _ hm
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
  have hGA : proofSearch k
      (Formula.plays (DupocBot k) (.bot (DupocBot k)) .C) = true := by
    -- hand certificate: Dupoc's search FIRED (hBtrue) — search_t ∘ const
    refine (proofSearch_spec _ _).2 (Pf.atom
      (⟨PlaysProof.search_t ((proofSearch_spec _ _).1 hBtrue) PlaysProof.const, ?_⟩ :
        AtomProvable k (.plays (DupocBot k) (.bot (DupocBot k)) .C)))
    show c_leaf + c_guard k + c_node ≤ k
    simp only [numCost, c_leaf, c_guard, c_node]
    omega
  have hJ : play 2 (JustBot k) (DupocBot k) = some .C := by
    show eval 2 (JustBot k) (DupocBot k) (JustBot k) = some .C
    unfold JustBot
    simp [eval, Prog.subst, Formula.subst, hGA]
  have hGJ : proofSearch k
      (Formula.plays (JustBot k) (DupocBot k) .C) = true := by
    -- hand certificate: JustBot's search FIRED (hGA) — search_t ∘ const
    refine (proofSearch_spec _ _).2 (Pf.atom
      (⟨PlaysProof.search_t ((proofSearch_spec _ _).1 hGA) PlaysProof.const, ?_⟩ :
        AtomProvable k (.plays (JustBot k) (DupocBot k) .C)))
    show c_leaf + c_guard k + c_node ≤ k
    simp only [numCost, c_leaf, c_guard, c_node]
    omega
  have hD : play 2 (DupocBot k) (JustBot k) = some .C := by
    show eval 2 (DupocBot k) (JustBot k) (DupocBot k) = some .C
    unfold DupocBot at hGJ ⊢
    simp [eval, Prog.subst, Formula.subst, hGJ]
  exact ⟨2, outcome_of_plays _ _ _ _ _ hJ hD⟩
end PD.Theorems
