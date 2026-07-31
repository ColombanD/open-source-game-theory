import PrisonersDilemma.Bots.LlmGenerations.CIMCIC
import PrisonersDilemma.Bots.LlmGenerations.JustBot
import PrisonersDilemma.Bots.DupocBot
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Base.Asymptotics

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

/-! # CIMCIC vs JustBot → (C, C) for all sufficiently large `k`.

JustBot's guard vs CIMCIC is "CIMCIC cooperates with `.bot (DupocBot k)`" — a
separate matchup that closes a mutual Löb fixpoint (analogous to CIMCIC vs
DupocBot). Once JustBot cooperates, CIMCIC's guard consequent (JustBot plays C) is
true with a cheap certificate, so `weakenImpl` proves CIMCIC's implication guard and
CIMCIC cooperates too. -/

/-- CIMCIC cooperates with `.bot (DupocBot k)` at large `k`, via mutual PBLT. -/
theorem cj_CIMCIC_C_vs_botDupoc :
    ∃ k₂, ∀ k, k₂ < k →
      ∃ n, play n (CIMCIC k) (.bot (DupocBot k)) = some .C := by
  let Y : Nat → Prog := fun k => .bot (DupocBot k)
  let Af : Nat → Formula := fun k => .plays (CIMCIC k) (Y k) .C
  let Bf : Nat → Formula := fun k =>
    .impl (.plays (CIMCIC k) (Y k) .C) (.plays (Y k) (CIMCIC k) .C)
  let p : Nat → Nat := fun k => 100 * Nat.log2 k + 1000
  have hlog : ∀ k, Nat.log2 k ≤ k := log2_le_self
  have hsA : ∀ k, (Af k).size ≤ 100 * Nat.log2 k + 1000 := by
    intro k
    show (Formula.plays (CIMCIC k) (Y k) .C).size ≤ _
    have := hlog k
    simp only [numCost, Formula.size, Prog.size, CIMCIC, DupocBot, Y]; omega
  have hsB : ∀ k, (Bf k).size ≤ 100 * Nat.log2 k + 1000 := by
    intro k
    show (Formula.impl (.plays (CIMCIC k) (Y k) .C) (.plays (Y k) (CIMCIC k) .C)).size ≤ _
    have := hlog k
    simp only [numCost, Formula.size, Prog.size, CIMCIC, DupocBot, Y]; omega
  have hp : ∀ k, p k ≤ 100 * Nat.log2 k + 1000 := fun k => le_rfl
  have hL2 : ∀ k, k > 0 → Pf (p k) (.impl (.box k (Bf k)) (Af k)) := by
    intro k _
    have hread : Pf ((Formula.impl (.box k (Bf k)) (Af k)).size)
        (.impl (.box k (Bf k)) (Af k)) := by
      have := Pf.searchBranch k (.impl (.plays .self .opp Action.C) (.plays .opp .self Action.C)) .C .D (CIMCIC k) (Y k) rfl (Nat.le_refl _)
      simpa [CIMCIC, Formula.subst, Prog.subst, Af, Bf, Y] using this
    refine Pf_mono hread ?_
    have := hlog k
    show _ ≤ 100 * Nat.log2 k + 1000
    simp only [numCost, Formula.size, Prog.size, CIMCIC, DupocBot, Af, Bf, Y]; omega
  have hL1 : ∀ k, k > 0 → Pf (p k) (.impl (.box k (Af k)) (Bf k)) := by
    intro k _
    have hdup : Pf ((Formula.impl (.box k (Af k)) (.plays (Y k) (CIMCIC k) .C)).size)
        (.impl (.box k (Af k)) (.plays (Y k) (CIMCIC k) .C)) := by
      have := Pf.botSearchStep k (.plays .opp .self Action.C) .C .D (Y k) (CIMCIC k) rfl (Nat.le_refl _)
      simpa [DupocBot, Formula.subst, Prog.subst, Af, Y] using this
    have hK : Pf ((Formula.impl (.plays (Y k) (CIMCIC k) .C) (Bf k)).size)
        (.impl (.plays (Y k) (CIMCIC k) .C) (Bf k)) :=
      Pf.implK (.plays (Y k) (CIMCIC k) .C) (.plays (CIMCIC k) (Y k) .C) (Nat.le_refl _)
    have htr : Pf (_ + _ + (Formula.impl (.box k (Af k)) (Bf k)).size)
        (.impl (.box k (Af k)) (Bf k)) :=
      Pf.implTrans _ _ _ _ _ hdup hK (Nat.le_refl _)
    refine Pf_mono htr ?_
    have := hlog k
    show _ ≤ 100 * Nat.log2 k + 1000
    simp only [numCost, Formula.size, Prog.size, CIMCIC, DupocBot, Af, Bf, Y]; omega
  obtain ⟨ke, hke⟩ := mutual_pblt_engine_id Af Bf p p 0 hsA hsB hp hp hL1 hL2
  refine ⟨ke, fun k hk => ?_⟩
  obtain ⟨m, hm⟩ := hke k hk
  exact Pf_sound m (Af k) hm

/-- From CIMCIC play C vs `.bot (DupocBot k)`, its guard `Bf` is provable at `k`. -/
theorem cj_cimcic_guard_fired (k n : Nat)
    (h : play n (CIMCIC k) (.bot (DupocBot k)) = some .C) :
    Pf k (.impl (.plays (CIMCIC k) (.bot (DupocBot k)) .C) (.plays (.bot (DupocBot k)) (CIMCIC k) .C)) := by
  have hguard : proofSearch k
      (.impl (.plays (CIMCIC k) (.bot (DupocBot k)) .C) (.plays (.bot (DupocBot k)) (CIMCIC k) .C)) = true := by
    cases hps : proofSearch k
        (.impl (.plays (CIMCIC k) (.bot (DupocBot k)) .C) (.plays (.bot (DupocBot k)) (CIMCIC k) .C)) with
    | true => rfl
    | false =>
      exfalso
      rcases n with _ | _ | n
      · simp [play, eval] at h
      · simp [play, eval, CIMCIC] at h
      · have hev : play (n + 2) (CIMCIC k) (.bot (DupocBot k)) = some .D := by
          show (if proofSearch k
                  ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.C)).subst
                    (CIMCIC k) (.bot (DupocBot k)))
                then eval (n + 1) (CIMCIC k) (.bot (DupocBot k)) (.const Action.C)
                else eval (n + 1) (CIMCIC k) (.bot (DupocBot k)) (.const Action.D)) = some .D
          have hsub : ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.C)).subst
                    (CIMCIC k) (.bot (DupocBot k)))
                = (.impl (.plays (CIMCIC k) (.bot (DupocBot k)) .C) (.plays (.bot (DupocBot k)) (CIMCIC k) .C)) := by
            simp [Formula.subst, Prog.subst, CIMCIC]
          rw [hsub, hps]; simp [eval]
        rw [hev] at h; cases h
  exact (proofSearch_spec _ _).1 hguard

/-- From the guard provable at `k`, a cheap `search_t` cert gives `Pf k Af`. -/
theorem cj_af_provable_at_k (k : Nat) (hthr : Nat.log2 k + 3 ≤ k)
    (hBf : Pf k (.impl (.plays (CIMCIC k) (.bot (DupocBot k)) .C) (.plays (.bot (DupocBot k)) (CIMCIC k) .C))) :
    Pf k (.plays (CIMCIC k) (.bot (DupocBot k)) .C) := by
  have hsub : ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.C)).subst
      (CIMCIC k) (.bot (DupocBot k)))
      = (.impl (.plays (CIMCIC k) (.bot (DupocBot k)) .C) (.plays (.bot (DupocBot k)) (CIMCIC k) .C)) := by
    simp [Formula.subst, Prog.subst, CIMCIC]
  have hBf' : Pf k ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.C)).subst
      (CIMCIC k) (.bot (DupocBot k))) := by rw [hsub]; exact hBf
  refine Pf.atom (⟨PlaysProof.search_t hBf' PlaysProof.const, ?_⟩ :
    AtomProvable k (.plays (CIMCIC k) (.bot (DupocBot k)) .C))
  show c_leaf + c_guard k + c_node ≤ k
  simp only [c_leaf, c_node, c_guard, numCost]; omega

/-- JustBot cooperates vs CIMCIC when its guard (= Af) fires. -/
theorem cj_JustBot_C_vs_CIMCIC (k fuel : Nat)
    (hAf : proofSearch k (.plays (CIMCIC k) (.bot (DupocBot k)) .C) = true) :
    play (fuel + 2) (JustBot k) (CIMCIC k) = some .C := by
  show (if proofSearch k
            ((Formula.plays .opp (.bot (DupocBot k)) Action.C).subst (JustBot k) (CIMCIC k))
          then eval (fuel + 1) (JustBot k) (CIMCIC k) (.const Action.C)
          else eval (fuel + 1) (JustBot k) (CIMCIC k) (.const Action.D)) = some .C
  have hsub : ((Formula.plays .opp (.bot (DupocBot k)) Action.C).subst (JustBot k) (CIMCIC k))
      = .plays (CIMCIC k) (.bot (DupocBot k)) Action.C := by
    simp [Formula.subst, Prog.subst]
  rw [hsub, hAf]; simp [eval]

/-- Cheap bounded cert: JustBot plays C vs CIMCIC, from `Pf k Af`. -/
theorem cj_JustBot_C_cert (k : Nat)
    (hAf : Pf k (.plays (CIMCIC k) (.bot (DupocBot k)) .C)) :
    AtomProvable (c_leaf + c_guard k + c_node) (.plays (JustBot k) (CIMCIC k) .C) := by
  have hsub : ((Formula.plays .opp (.bot (DupocBot k)) Action.C).subst (JustBot k) (CIMCIC k))
      = .plays (CIMCIC k) (.bot (DupocBot k)) Action.C := by
    simp [Formula.subst, Prog.subst]
  have hAf' : Pf k ((Formula.plays .opp (.bot (DupocBot k)) Action.C).subst (JustBot k) (CIMCIC k)) := by
    rw [hsub]; exact hAf
  exact ⟨PlaysProof.search_t (φ := (Formula.plays .opp (.bot (DupocBot k)) Action.C)) hAf' PlaysProof.const,
    Nat.le_refl _⟩

/-- CIMCIC's implication guard vs JustBot is provable at `k` (weakenImpl on the
    true consequent's cheap cert). -/
theorem cj_cimcic_guard_provable (k : Nat) (hthr : 10 * Nat.log2 k + 100 ≤ k)
    (hcert : AtomProvable (c_leaf + c_guard k + c_node) (.plays (JustBot k) (CIMCIC k) .C)) :
    Pf k (.impl (.plays (CIMCIC k) (JustBot k) .C) (.plays (JustBot k) (CIMCIC k) .C)) := by
  refine Pf.weakenImpl _ _ (c_leaf + c_guard k + c_node) (Pf.atom hcert) ?_
  have hl := log2_le_self k
  simp only [c_leaf, c_node, c_guard, numCost, Formula.size, Prog.size, CIMCIC, JustBot, DupocBot]
  omega

/-- CIMCIC plays C vs JustBot given the guard is provable at `k`. -/
theorem cj_CIMCIC_C_vs_JustBot (k fuel : Nat)
    (hguard : Pf k (.impl (.plays (CIMCIC k) (JustBot k) .C) (.plays (JustBot k) (CIMCIC k) .C))) :
    play (fuel + 2) (CIMCIC k) (JustBot k) = some .C := by
  have hps : proofSearch k
      ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.C)).subst
        (CIMCIC k) (JustBot k)) = true := by
    refine (proofSearch_spec _ _).2 ?_
    have hsub : ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.C)).subst
        (CIMCIC k) (JustBot k))
        = .impl (.plays (CIMCIC k) (JustBot k) .C) (.plays (JustBot k) (CIMCIC k) .C) := by
      simp [Formula.subst, Prog.subst, CIMCIC]
    rw [hsub]; exact hguard
  show (if proofSearch k
            ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.C)).subst
              (CIMCIC k) (JustBot k))
          then eval (fuel + 1) (CIMCIC k) (JustBot k) (.const Action.C)
          else eval (fuel + 1) (CIMCIC k) (JustBot k) (.const Action.D)) = some .C
  rw [hps]; simp [eval]

/-- **CIMCIC vs JustBot → (C, C)** for all sufficiently large `k`. -/
theorem llm_outcome_CIMCIC_vs_JustBot :
    ∃ k₂, ∀ k, k₂ < k →
      ∃ fuel, outcome fuel (CIMCIC k) (JustBot k) = some (.C, .C) := by
  obtain ⟨ke, hke⟩ := cj_CIMCIC_C_vs_botDupoc
  obtain ⟨kt, hkt⟩ := linear_log2_add_le 10 100
  refine ⟨max ke kt, fun k hk => ⟨2, ?_⟩⟩
  have hkke : ke < k := lt_of_le_of_lt (Nat.le_max_left _ _) hk
  have hkkt : 10 * Nat.log2 k + 100 ≤ k :=
    hkt k (Nat.le_of_lt (lt_of_le_of_lt (Nat.le_max_right _ _) hk))
  have hkkt3 : Nat.log2 k + 3 ≤ k := by omega
  obtain ⟨n, hn⟩ := hke k hkke
  have hBf := cj_cimcic_guard_fired k n hn
  have hAf : Pf k (.plays (CIMCIC k) (.bot (DupocBot k)) .C) := cj_af_provable_at_k k hkkt3 hBf
  have hAfps : proofSearch k (.plays (CIMCIC k) (.bot (DupocBot k)) .C) = true :=
    (proofSearch_spec _ _).2 hAf
  have hJC : play (0 + 2) (JustBot k) (CIMCIC k) = some .C :=
    cj_JustBot_C_vs_CIMCIC k 0 hAfps
  have hcert := cj_JustBot_C_cert k hAf
  have hguard := cj_cimcic_guard_provable k hkkt hcert
  have hCJ : play (0 + 2) (CIMCIC k) (JustBot k) = some .C :=
    cj_CIMCIC_C_vs_JustBot k 0 hguard
  exact outcome_of_plays _ _ _ _ _ hCJ hJC

end PD.Theorems
