import PrisonersDilemma.Bots.LlmGenerations.OptimBot
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Dynamics
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Theorems.CooperateBot.Helpers
import PrisonersDilemma.Base.Helpers

open PD
open PD.Bots
open PD.BaseTheorems
namespace PD.Theorems

private def optim_rung2 (k : Nat) : Prog :=
  Prog.search k (Formula.plays Prog.opp Prog.self Action.C)
    (Prog.search k (Formula.plays Prog.self Prog.opp Action.C) (Prog.const Action.C)
      (Prog.search k (Formula.plays Prog.opp Prog.self Action.D)
        (Prog.search k (Formula.plays Prog.self Prog.opp Action.D) (Prog.const Action.D)
          (Prog.const Action.C))
        (Prog.const Action.C)))
    (Prog.search k (Formula.plays Prog.opp Prog.self Action.D)
      (Prog.search k (Formula.plays Prog.self Prog.opp Action.D) (Prog.const Action.D)
        (Prog.const Action.C))
      (Prog.const Action.C))

theorem optim_loeb_premise_D (k : Nat) (hk : 1 ≤ k) :
    Pf (300 * Nat.log2 k + 3000)
       (.impl (.box k (.plays (OptimBot k) CooperateBot Action.D))
              (.plays (OptimBot k) CooperateBot Action.D)) := by
  have hcert : AtomProvable 1 (.plays CooperateBot (OptimBot k) Action.C) :=
    ⟨(PlaysProof.const : PlaysProof CooperateBot (OptimBot k) (.const Action.C) Action.C c_leaf),
     by simp [c_leaf]⟩
  have hbox1 : Pf _ (.box 1 (.plays CooperateBot (OptimBot k) Action.C)) :=
    Pf.boxIntro 1 _ _ (Pf.atom hcert) (Nat.le_refl _)
  have hmono : Pf _ (.impl (.box 1 (.plays CooperateBot (OptimBot k) Action.C))
                           (.box k (.plays CooperateBot (OptimBot k) Action.C))) :=
    Pf.boxMono 1 k _ _ hk (Nat.le_refl _)
  have hboxk : Pf _ (.box k (.plays CooperateBot (OptimBot k) Action.C)) :=
    Pf.mp _ _ _ _ hmono hbox1 (Nat.le_refl _)
  have hchain := Pf.searchChain k (Formula.plays .opp .self Action.C)
    (optim_rung2 k)
    [(k, (Formula.plays Prog.self Prog.opp Action.D), optim_rung2 k)]
    Action.D (OptimBot k) CooperateBot rfl (Nat.le_refl _)
  simp only [searchGuards, implChain, List.foldr, Formula.subst, Prog.subst] at hchain
  have hfinal := Pf.mp _ _ _ _ hchain hboxk (Nat.le_refl _)
  refine Pf_mono hfinal ?_
  have hlog1 : Nat.log2 1 = 0 := by decide
  simp only [Formula.size, Prog.size, numCost, OptimBot, CooperateBot, hlog1]
  omega

theorem optim_D_atom_size (k : Nat) :
    (Formula.plays (OptimBot k) CooperateBot Action.D).size ≤ 20 * Nat.log2 k + 200 := by
  simp only [Formula.size, Prog.size, numCost, OptimBot, CooperateBot]
  omega

/-- Directly get `Pf k φ_D` for large `k` by running bloeb with output budget ≤ k. -/
theorem optim_D_provable_at_k :
    ∃ k₂, ∀ k, k > k₂ → proofSearch k (.plays (OptimBot k) CooperateBot Action.D) = true := by
  obtain ⟨Ksz, hKsz⟩ := linear_log2_add_le (8192 * 321) (8192 * 3208)
  refine ⟨max 1 Ksz, fun k hk => ?_⟩
  have h1 : 1 ≤ k := (lt_of_le_of_lt (Nat.le_max_left _ _) hk).le
  have hKk : k ≥ Ksz := (lt_of_le_of_lt (Nat.le_max_right _ _) hk).le
  have hb := hKsz k hKk
  have hs := optim_D_atom_size k
  set φ := Formula.plays (OptimBot k) CooperateBot Action.D with hφ
  set W := (300 * Nat.log2 k + 3000) + φ.size + Nat.log2 k + 8 with hW
  have hWk : 8192 * W ≤ k := by
    rw [hW]; omega
  have hlg : Nat.log2 (1024 * W) ≤ Nat.log2 k := log2_mono (by omega)
  have hl₁ : Nat.log2 (32 * W) ≤ Nat.log2 k := log2_mono (by omega)
  have hl₃ : Nat.log2 (2048 * W) ≤ Nat.log2 k := log2_mono (by omega)
  have hl₅ : Nat.log2 (8192 * W) ≤ Nat.log2 k := log2_mono (by omega)
  have hLoeb := optim_loeb_premise_D k h1
  -- bloeb output budget = 4096 * W ≤ k
  have hpf : Pf (4096 * W) φ := by
    refine bloeb_engine φ (300 * Nat.log2 k + 3000) k
      (1024 * W) (32 * W) (2048 * W) (2048 * W) (8192 * W)
      (16 * W) (16 * W) (64 * W) (32 * W) (128 * W) (32 * W) (16 * W)
      (256 * W) (512 * W) (16 * W) (640 * W) (704 * W) (768 * W) (2048 * W) (4096 * W)
      hLoeb ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    · (try simp only [numCost, Formula.size]); omega
  have hpfk : Pf k φ := Pf_mono hpf (by omega)
  exact (proofSearch_spec k φ).2 hpfk

theorem OptimBot_plays_D_against_CooperateBot (k fuel : Nat)
    (hOuter : proofSearch k (Formula.plays CooperateBot (OptimBot k) Action.C) = true)
    (hD : proofSearch k (Formula.plays (OptimBot k) CooperateBot Action.D) = true) :
    play (fuel + 6) (OptimBot k) CooperateBot = some .D := by
  show eval (fuel + 6) (OptimBot k) CooperateBot (OptimBot k) = some .D
  unfold OptimBot at hOuter hD ⊢
  simp [eval, Prog.subst, Formula.subst, hOuter, hD]

theorem llm_outcome_OptimBot_vs_CooperateBot :
    ∃ k₂, ∀ k, k₂ < k →
      ∃ fuel, outcome fuel (OptimBot k) CooperateBot = some (.D, .C) := by
  obtain ⟨k₂, hk₂⟩ := optim_D_provable_at_k
  refine ⟨k₂, fun k hk => ?_⟩
  have h1 : 1 ≤ k := by omega
  have hD : proofSearch k (Formula.plays (OptimBot k) CooperateBot Action.D) = true :=
    hk₂ k hk
  have hOuter : proofSearch k (Formula.plays CooperateBot (OptimBot k) Action.C) = true := by
    have hcert : AtomProvable 1 (.plays CooperateBot (OptimBot k) Action.C) :=
      ⟨(PlaysProof.const : PlaysProof CooperateBot (OptimBot k) (.const Action.C) Action.C c_leaf),
       by simp [c_leaf]⟩
    have hpf : Pf k (.plays CooperateBot (OptimBot k) Action.C) :=
      Pf_mono (Pf.atom hcert) h1
    exact (proofSearch_spec k _).2 hpf
  refine ⟨6, ?_⟩
  have hA : play 6 (OptimBot k) CooperateBot = some .D := by
    have := OptimBot_plays_D_against_CooperateBot k 0 hOuter hD
    simpa using this
  have hB : play 6 CooperateBot (OptimBot k) = some .C := by
    simpa using play_CooperateBot 5 (OptimBot k)
  exact outcome_of_plays 6 _ _ _ _ hA hB

end PD.Theorems
