import PrisonersDilemma.Bots.LlmGenerations.CIMCIC
import PrisonersDilemma.Bots.DupocBot
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Base.Asymptotics

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

/-- From CIMCIC's play C vs Dupoc, extract that CIMCIC's guard (A→B) is provable at budget k. -/
theorem cd_dupoc_guard_fired (k n : Nat)
    (h : play n (CIMCIC k) (DupocBot k) = some .C) :
    Pf k (.impl (.plays (CIMCIC k) (DupocBot k) .C) (.plays (DupocBot k) (CIMCIC k) .C)) := by
  have hguard : proofSearch k
      (.impl (.plays (CIMCIC k) (DupocBot k) .C) (.plays (DupocBot k) (CIMCIC k) .C)) = true := by
    cases hps : proofSearch k
        (.impl (.plays (CIMCIC k) (DupocBot k) .C) (.plays (DupocBot k) (CIMCIC k) .C)) with
    | true => rfl
    | false =>
      exfalso
      rcases n with _ | _ | n
      · simp [play, eval] at h
      · simp [play, eval, CIMCIC] at h
      · have hev : play (n + 2) (CIMCIC k) (DupocBot k) = some .D := by
          show (if proofSearch k
                  ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.C)).subst
                    (CIMCIC k) (DupocBot k))
                then eval (n + 1) (CIMCIC k) (DupocBot k) (.const Action.C)
                else eval (n + 1) (CIMCIC k) (DupocBot k) (.const Action.D)) = some .D
          have hsub : ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.C)).subst
                    (CIMCIC k) (DupocBot k))
                = (.impl (.plays (CIMCIC k) (DupocBot k) .C) (.plays (DupocBot k) (CIMCIC k) .C)) := by
            simp [Formula.subst, Prog.subst, CIMCIC]
          rw [hsub, hps]; simp [eval]
        rw [hev] at h; cases h
  exact (proofSearch_spec _ _).1 hguard

/-- From CIMCIC's guard provable at k, a cheap certificate makes Af provable at k. -/
theorem cd_af_provable_at_k (k : Nat) (hthr : Nat.log2 k + 3 ≤ k)
    (hBf : Pf k (.impl (.plays (CIMCIC k) (DupocBot k) .C) (.plays (DupocBot k) (CIMCIC k) .C))) :
    Pf k (.plays (CIMCIC k) (DupocBot k) .C) := by
  have hsub : ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.C)).subst
      (CIMCIC k) (DupocBot k))
      = (.impl (.plays (CIMCIC k) (DupocBot k) .C) (.plays (DupocBot k) (CIMCIC k) .C)) := by
    simp [Formula.subst, Prog.subst, CIMCIC]
  have hBf' : Pf k ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.C)).subst
      (CIMCIC k) (DupocBot k)) := by rw [hsub]; exact hBf
  refine Pf.atom (⟨PlaysProof.search_t hBf' PlaysProof.const, ?_⟩ :
    AtomProvable k (.plays (CIMCIC k) (DupocBot k) .C))
  show c_leaf + c_guard k + c_node ≤ k
  simp only [c_leaf, c_node, c_guard, numCost]; omega

/-- Dupoc plays C once its guard (Af) is provable at k. -/
theorem cd_dupoc_plays_C (k fuel : Nat)
    (hAf : Pf k (.plays (CIMCIC k) (DupocBot k) .C)) :
    play (fuel + 2) (DupocBot k) (CIMCIC k) = some .C := by
  have hguard : proofSearch k (.plays (CIMCIC k) (DupocBot k) .C) = true :=
    (proofSearch_spec _ _).2 hAf
  show eval (fuel + 2) (DupocBot k) (CIMCIC k) (DupocBot k) = some .C
  unfold DupocBot at hguard ⊢
  simp [eval, Prog.subst, Formula.subst, hguard]

/-- **CIMCIC vs DupocBot → (C, C)** for all sufficiently large `k`. CIMCIC's guard
    `(I play C → opp plays C)` and DupocBot's guard `(opp plays C)` close a mutual
    Löb fixpoint (via `mutual_pblt_engine_id` with `Bf` = CIMCIC's implication guard),
    so both cooperate. -/
theorem llm_outcome_CIMCIC_vs_DupocBot :
    ∃ k₂, ∀ k, k₂ < k →
      ∃ fuel, outcome fuel (CIMCIC k) (DupocBot k) = some (.C, .C) := by
  let Af : Nat → Formula := fun k => .plays (CIMCIC k) (DupocBot k) .C
  let Bf : Nat → Formula := fun k =>
    .impl (.plays (CIMCIC k) (DupocBot k) .C) (.plays (DupocBot k) (CIMCIC k) .C)
  let p : Nat → Nat := fun k => 100 * Nat.log2 k + 1000
  have hlog : ∀ k, Nat.log2 k ≤ k := log2_le_self
  have hsA : ∀ k, (Af k).size ≤ 100 * Nat.log2 k + 1000 := by
    intro k
    show (Formula.plays (CIMCIC k) (DupocBot k) .C).size ≤ _
    have := hlog k
    simp only [numCost, Formula.size, Prog.size, CIMCIC, DupocBot]; omega
  have hsB : ∀ k, (Bf k).size ≤ 100 * Nat.log2 k + 1000 := by
    intro k
    show (Formula.impl (.plays (CIMCIC k) (DupocBot k) .C) (.plays (DupocBot k) (CIMCIC k) .C)).size ≤ _
    have := hlog k
    simp only [numCost, Formula.size, Prog.size, CIMCIC, DupocBot]; omega
  have hp : ∀ k, p k ≤ 100 * Nat.log2 k + 1000 := fun k => le_rfl
  have hL1 : ∀ k, k > 0 → Pf (p k) (.impl (.box k (Af k)) (Bf k)) := by
    intro k _
    have hdup : Pf ((Formula.impl (.box k (Af k)) (.plays (DupocBot k) (CIMCIC k) .C)).size)
        (.impl (.box k (Af k)) (.plays (DupocBot k) (CIMCIC k) .C)) := by
      have := Pf.searchBranch k (.plays .opp .self Action.C) .C .D (DupocBot k) (CIMCIC k) rfl (Nat.le_refl _)
      simpa [DupocBot, Formula.subst, Prog.subst, Af] using this
    have hK : Pf ((Formula.impl (.plays (DupocBot k) (CIMCIC k) .C) (Bf k)).size)
        (.impl (.plays (DupocBot k) (CIMCIC k) .C) (Bf k)) :=
      Pf.implK (.plays (DupocBot k) (CIMCIC k) .C) (.plays (CIMCIC k) (DupocBot k) .C) (Nat.le_refl _)
    have htr : Pf (_ + _ + (Formula.impl (.box k (Af k)) (Bf k)).size)
        (.impl (.box k (Af k)) (Bf k)) :=
      Pf.implTrans _ _ _ _ _ hdup hK (Nat.le_refl _)
    refine Pf_mono htr ?_
    have := hlog k
    show _ ≤ 100 * Nat.log2 k + 1000
    simp only [numCost, Formula.size, Prog.size, CIMCIC, DupocBot, Af, Bf]; omega
  have hL2 : ∀ k, k > 0 → Pf (p k) (.impl (.box k (Bf k)) (Af k)) := by
    intro k _
    have hread : Pf ((Formula.impl (.box k (Bf k)) (Af k)).size)
        (.impl (.box k (Bf k)) (Af k)) := by
      have := Pf.searchBranch k (.impl (.plays .self .opp Action.C) (.plays .opp .self Action.C)) .C .D (CIMCIC k) (DupocBot k) rfl (Nat.le_refl _)
      simpa [CIMCIC, Formula.subst, Prog.subst, Af, Bf] using this
    refine Pf_mono hread ?_
    have := hlog k
    show _ ≤ 100 * Nat.log2 k + 1000
    simp only [numCost, Formula.size, Prog.size, CIMCIC, DupocBot, Af, Bf]; omega
  obtain ⟨ke, hke⟩ := mutual_pblt_engine_id Af Bf p p 0 hsA hsB hp hp hL1 hL2
  obtain ⟨kt, hkt⟩ := linear_log2_add_le 1 3
  refine ⟨max ke kt, fun k hk => ?_⟩
  have hkke : k > ke := lt_of_le_of_lt (Nat.le_max_left _ _) hk
  have hkkt : Nat.log2 k + 3 ≤ k := by
    have := hkt k (Nat.le_of_lt (lt_of_le_of_lt (Nat.le_max_right _ _) hk)); omega
  obtain ⟨m, hm⟩ := hke k hkke
  have hAint : (Af k).interp := Pf_sound m (Af k) hm
  obtain ⟨n, hnA⟩ := hAint
  have hBf : Pf k (Bf k) := cd_dupoc_guard_fired k n hnA
  have hAf : Pf k (Af k) := cd_af_provable_at_k k hkkt hBf
  have hB : play (n + 2) (DupocBot k) (CIMCIC k) = some .C := cd_dupoc_plays_C k n hAf
  have hnA' : eval n (CIMCIC k) (DupocBot k) (CIMCIC k) = some .C := hnA
  have hA : play (n + 2) (CIMCIC k) (DupocBot k) = some .C :=
    eval_mono_le hnA' (n + 2) (Nat.le_add_right _ 2)
  exact ⟨n + 2, outcome_of_plays _ _ _ _ _ hA hB⟩

end PD.Theorems

