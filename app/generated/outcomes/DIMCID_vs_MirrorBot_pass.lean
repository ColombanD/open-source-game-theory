import PrisonersDilemma.Bots.LlmGenerations.DIMCID
import PrisonersDilemma.Bots.MirrorBot
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Base.Asymptotics

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

abbrev dm7_target (k : Nat) : Formula := .plays MirrorBot (DIMCID k) Action.D
abbrev dm7_dimcid_D (k : Nat) : Formula := .plays (DIMCID k) MirrorBot Action.D
abbrev dm7_dimcid_C (k : Nat) : Formula := .plays (DIMCID k) MirrorBot Action.C
abbrev dm7_guard (k : Nat) : Formula := .impl (dm7_dimcid_C k) (dm7_target k)

theorem dm7_guard_subst (k : Nat) :
    (Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.D)).subst
      (DIMCID k) MirrorBot = dm7_guard k := by
  simp [Formula.subst, Prog.subst, MirrorBot]

theorem dm7_target_size (k : Nat) : (dm7_target k).size = Nat.log2 k + 15 := by
  show (Formula.plays MirrorBot (DIMCID k) .D).size = _
  simp only [Formula.size, DIMCID, MirrorBot, Prog.size, numCost]; omega

theorem dimcid7_mirror_loeb_premise (k b : Nat)
    (hb : b + 20 * Nat.log2 k + 300 ≤ k) :
    Pf (100 * Nat.log2 k + 100000)
       (.impl (.box b (dm7_target k)) (dm7_target k)) := by
  have legS : Pf ((Formula.impl (.box k (dm7_guard k)) (dm7_dimcid_D k)).size)
      (.impl (.box k (dm7_guard k)) (dm7_dimcid_D k)) := by
    have := Pf.searchBranch k
      (.impl (.plays .self .opp Action.C) (.plays .opp .self Action.D))
      Action.D Action.C (DIMCID k) MirrorBot rfl (Nat.le_refl _)
    simpa [DIMCID, Formula.subst, Prog.subst, MirrorBot] using this
  have legM : Pf ((Formula.impl (dm7_dimcid_D k) (dm7_target k)).size)
      (.impl (dm7_dimcid_D k) (dm7_target k)) := by
    have := Pf.simStep MirrorBot .opp .self (DIMCID k) Action.D rfl (Nat.le_refl _)
    simpa [MirrorBot, Prog.subst] using this
  have leg1 : Pf ((Formula.impl (.box k (dm7_guard k)) (dm7_dimcid_D k)).size
      + (Formula.impl (dm7_dimcid_D k) (dm7_target k)).size
      + (Formula.impl (.box k (dm7_guard k)) (dm7_target k)).size)
      (.impl (.box k (dm7_guard k)) (dm7_target k)) :=
    Pf.implTrans _ _ _ _ _ legS legM (Nat.le_refl _)
  have step1 : Pf ((Formula.impl (dm7_target k) (dm7_guard k)).size)
      (.impl (dm7_target k) (dm7_guard k)) :=
    Pf.implK (dm7_target k) (dm7_dimcid_C k) (Nat.le_refl _)
  have step2 := Pf.boxIntro _ _ _ step1 (Nat.le_refl _)
  have step3 := Pf.axK _ b k _ _ (dm7_target k) (dm7_guard k)
      step2 (by simp only [Formula.size, DIMCID, MirrorBot, Prog.size, numCost] at hb ⊢; omega) (Nat.le_refl _)
  refine Pf.implTrans _ _ _ _ _ step3 leg1 ?_
  have hlogb : Nat.log2 b ≤ Nat.log2 k := log2_mono (by omega)
  have hself : ∀ x, Nat.log2 x ≤ x := log2_le_self
  simp only [Formula.size, DIMCID, MirrorBot, Prog.size, numCost]
  have hbig := hself (1 + 1 + 1 + (Nat.log2 k + 1 + (1 + 1 + 1 + (1 + 1 + 1) + 1) + 1 + 1 + 1) + 1 +
        (Nat.log2 k + 1 + (1 + 1 + 1 + (1 + 1 + 1) + 1) + 1 + 1 + 1 + (1 + 1 + 1) + 1 +
            (1 + 1 + 1 + (Nat.log2 k + 1 + (1 + 1 + 1 + (1 + 1 + 1) + 1) + 1 + 1 + 1) + 1) +
          1) +
      1)
  omega

theorem DIMCID7_plays_D_against_MirrorBot (k fuel : Nat)
    (hk : proofSearch k (dm7_guard k) = true) :
    play (fuel + 2) (DIMCID k) MirrorBot = some .D := by
  show (if proofSearch k
            ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.D)).subst
              (DIMCID k) MirrorBot)
          then eval (fuel + 1) (DIMCID k) MirrorBot (.const Action.D)
          else eval (fuel + 1) (DIMCID k) MirrorBot (.const Action.C)) = some .D
  rw [dm7_guard_subst, hk]; simp [eval]

theorem DIMCID7_plays_C_against_MirrorBot (k fuel : Nat)
    (hk : proofSearch k (dm7_guard k) = false) :
    play (fuel + 2) (DIMCID k) MirrorBot = some .C := by
  show (if proofSearch k
            ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.D)).subst
              (DIMCID k) MirrorBot)
          then eval (fuel + 1) (DIMCID k) MirrorBot (.const Action.D)
          else eval (fuel + 1) (DIMCID k) MirrorBot (.const Action.C)) = some .C
  rw [dm7_guard_subst, hk]; simp [eval]

theorem MirrorBot7_plays_D_against_DIMCID (k fuel : Nat)
    (hk : proofSearch k (dm7_guard k) = true) :
    play (fuel + 3) MirrorBot (DIMCID k) = some .D := by
  have hD : play (fuel + 2) (DIMCID k) MirrorBot = some .D :=
    DIMCID7_plays_D_against_MirrorBot k fuel hk
  simpa [play, eval, Prog.subst, MirrorBot] using hD

theorem MirrorBot7_plays_C_against_DIMCID (k fuel : Nat)
    (hk : proofSearch k (dm7_guard k) = false) :
    play (fuel + 3) MirrorBot (DIMCID k) = some .C := by
  have hC : play (fuel + 2) (DIMCID k) MirrorBot = some .C :=
    DIMCID7_plays_C_against_MirrorBot k fuel hk
  simpa [play, eval, Prog.subst, MirrorBot] using hC

theorem proofSearch7_of_play_MirrorBot_dimcid
    (k n : Nat) (h : play n MirrorBot (DIMCID k) = some .D) :
    proofSearch k (dm7_guard k) = true := by
  cases hps : proofSearch k (dm7_guard k) with
  | true => rfl
  | false =>
    exfalso
    rcases n with _ | _ | _ | n
    · simp [play, eval] at h
    · simp [play, eval, MirrorBot] at h
    · have hev : play 2 MirrorBot (DIMCID k) = none := by
        unfold DIMCID
        simp [play, eval, Prog.subst, MirrorBot, Formula.subst]
      rw [hev] at h; cases h
    · have hev : play (n + 3) MirrorBot (DIMCID k) = some .C := by
        simpa using MirrorBot7_plays_C_against_DIMCID k n hps
      rw [hev] at h; cases h

theorem dm7_headroom (k : Nat)
    (hc : 20 * Nat.log2 k + 300 ≤ k)
    (hbig : (8192 * 102 + 20) * Nat.log2 k + (8192 * 100023 + 300) ≤ k) :
    8192 * ((100 * Nat.log2 k + 100000) + (dm7_target k).size
      + Nat.log2 (k - (20 * Nat.log2 k + 300)) + 8) ≤ k - (20 * Nat.log2 k + 300) := by
  rw [dm7_target_size]
  have hcancel : (k - (20 * Nat.log2 k + 300)) + (20 * Nat.log2 k + 300) = k :=
    Nat.sub_add_cancel hc
  have hlogf : Nat.log2 (k - (20 * Nat.log2 k + 300)) ≤ Nat.log2 k :=
    log2_mono (by omega)
  omega

theorem llm_outcome_DIMCID_vs_MirrorBot :
    ∃ k₂, ∀ k, k₂ < k →
      ∃ fuel, outcome fuel (DIMCID k) MirrorBot = some (.D, .D) := by
  let φ : Nat → Formula := fun k => dm7_target k
  let f : Nat → Nat := fun k => k - (20 * Nat.log2 k + 300)
  let pm : Nat → Nat := fun k => 100 * Nat.log2 k + 100000
  obtain ⟨Kc, hKc⟩ := linear_log2_add_le 20 300
  obtain ⟨Ksz, hKsz⟩ := linear_log2_add_le (8192 * 102 + 20) (8192 * 100023 + 300)
  have hLoeb : ∀ k, k > max Kc Ksz → Pf (pm k) (.impl (.box (f k) (φ k)) (φ k)) := by
    intro k hk
    have hc : 20 * Nat.log2 k + 300 ≤ k :=
      hKc k (Nat.le_of_lt (lt_of_le_of_lt (Nat.le_max_left _ _) hk))
    have hcancel : f k + (20 * Nat.log2 k + 300) = k := Nat.sub_add_cancel hc
    have hfb : f k + 20 * Nat.log2 k + 300 ≤ k := by omega
    exact dimcid7_mirror_loeb_premise k (f k) hfb
  have hsz : ∀ k, k > max Kc Ksz →
      8192 * (pm k + (φ k).size + Nat.log2 (f k) + 8) ≤ f k := by
    intro k hk
    have hc : 20 * Nat.log2 k + 300 ≤ k :=
      hKc k (Nat.le_of_lt (lt_of_le_of_lt (Nat.le_max_left _ _) hk))
    have hbig : (8192 * 102 + 20) * Nat.log2 k + (8192 * 100023 + 300) ≤ k :=
      hKsz k (Nat.le_of_lt (lt_of_le_of_lt (Nat.le_max_right _ _) hk))
    exact dm7_headroom k hc hbig
  obtain ⟨k₂, hk₂⟩ := pblt_engine φ f pm (max Kc Ksz) hLoeb hsz
  refine ⟨k₂, ?_⟩
  intro k hk
  obtain ⟨m, hm⟩ := hk₂ k hk
  have hInterp : (φ k).interp := Pf_sound m (φ k) hm
  obtain ⟨n, hMirror⟩ := hInterp
  have hPS : proofSearch k (dm7_guard k) = true :=
    proofSearch7_of_play_MirrorBot_dimcid k n hMirror
  refine ⟨3, ?_⟩
  have hA : play 3 (DIMCID k) MirrorBot = some .D := by
    simpa using DIMCID7_plays_D_against_MirrorBot k 1 hPS
  have hB : play 3 MirrorBot (DIMCID k) = some .D := by
    simpa using MirrorBot7_plays_D_against_DIMCID k 0 hPS
  exact outcome_of_plays _ _ _ _ _ hA hB

end PD.Theorems
