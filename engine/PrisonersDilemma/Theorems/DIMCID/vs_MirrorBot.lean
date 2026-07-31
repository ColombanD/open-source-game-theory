import PrisonersDilemma.Bots.LlmGenerations.DIMCID
import PrisonersDilemma.Bots.MirrorBot
import PrisonersDilemma.Dynamics
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Base.Asymptotics
import PrisonersDilemma.Base.Helpers

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

/-- Löb premise for DIMCID vs MirrorBot at lowered box subscript `b`. -/
theorem dm_loeb_premise (k b : Nat)
    (hb : b + 200 * Nat.log2 k + 20000 ≤ k) :
    Pf (300 * Nat.log2 k + 500000)
       (.impl (.box b (.plays (DIMCID k) MirrorBot Action.D))
              (.plays (DIMCID k) MirrorBot Action.D)) := by
  have hself : ∀ x, Nat.log2 x ≤ x := log2_le_self
  have hlogb : Nat.log2 b ≤ Nat.log2 k := log2_mono (by omega)
  have hGsz : (Formula.impl (.plays (DIMCID k) MirrorBot Action.C)
        (.plays MirrorBot (DIMCID k) Action.D)).size ≤ 3 * Nat.log2 k + 40 := by
    simp only [Formula.size, DIMCID, MirrorBot, Prog.size, numCost]; omega
  have hφsz : (Formula.plays (DIMCID k) MirrorBot Action.D).size ≤ 2 * Nat.log2 k + 30 := by
    simp only [Formula.size, DIMCID, MirrorBot, Prog.size, numCost]; omega
  have hMDsz : (Formula.plays MirrorBot (DIMCID k) Action.D).size ≤ 2 * Nat.log2 k + 30 := by
    simp only [Formula.size, DIMCID, MirrorBot, Prog.size, numCost]; omega
  have hncb : numCost b ≤ Nat.log2 k + 1 := by
    have h : numCost b = Nat.log2 b + 1 := rfl
    rw [h]; omega
  have hnck : numCost k ≤ Nat.log2 k + 1 := le_of_eq rfl
  have hnc20 : numCost (20 * Nat.log2 k + 300) ≤ 20 * Nat.log2 k + 300 + 1 := by
    have h : numCost (20 * Nat.log2 k + 300) = Nat.log2 (20 * Nat.log2 k + 300) + 1 := rfl
    rw [h]; have := hself (20 * Nat.log2 k + 300); omega
  have dφMD : (Formula.impl (.plays (DIMCID k) MirrorBot Action.D)
        (.plays MirrorBot (DIMCID k) Action.D)).size
      = (Formula.plays (DIMCID k) MirrorBot Action.D).size
        + (Formula.plays MirrorBot (DIMCID k) Action.D).size + 1 := rfl
  have dMDG : (Formula.impl (.plays MirrorBot (DIMCID k) Action.D)
        (.impl (.plays (DIMCID k) MirrorBot Action.C) (.plays MirrorBot (DIMCID k) Action.D))).size
      = (Formula.plays MirrorBot (DIMCID k) Action.D).size
        + (Formula.impl (.plays (DIMCID k) MirrorBot Action.C) (.plays MirrorBot (DIMCID k) Action.D)).size + 1 := rfl
  have dφG : (Formula.impl (.plays (DIMCID k) MirrorBot Action.D)
        (.impl (.plays (DIMCID k) MirrorBot Action.C) (.plays MirrorBot (DIMCID k) Action.D))).size
      = (Formula.plays (DIMCID k) MirrorBot Action.D).size
        + (Formula.impl (.plays (DIMCID k) MirrorBot Action.C) (.plays MirrorBot (DIMCID k) Action.D)).size + 1 := rfl
  have dBoxbφ : (Formula.box b (.plays (DIMCID k) MirrorBot Action.D)).size
      = numCost b + (Formula.plays (DIMCID k) MirrorBot Action.D).size + 1 := rfl
  have dBoxkG : (Formula.box k (.impl (.plays (DIMCID k) MirrorBot Action.C)
        (.plays MirrorBot (DIMCID k) Action.D))).size
      = numCost k + (Formula.impl (.plays (DIMCID k) MirrorBot Action.C)
          (.plays MirrorBot (DIMCID k) Action.D)).size + 1 := rfl
  have dBoxPhiG : (Formula.box (20 * Nat.log2 k + 300)
        (.impl (.plays (DIMCID k) MirrorBot Action.D)
          (.impl (.plays (DIMCID k) MirrorBot Action.C) (.plays MirrorBot (DIMCID k) Action.D)))).size
      = numCost (20 * Nat.log2 k + 300)
        + (Formula.impl (.plays (DIMCID k) MirrorBot Action.D)
            (.impl (.plays (DIMCID k) MirrorBot Action.C) (.plays MirrorBot (DIMCID k) Action.D))).size + 1 := rfl
  have dImplStep : (Formula.impl (.box b (.plays (DIMCID k) MirrorBot Action.D))
        (.box k (.impl (.plays (DIMCID k) MirrorBot Action.C) (.plays MirrorBot (DIMCID k) Action.D)))).size
      = (Formula.box b (.plays (DIMCID k) MirrorBot Action.D)).size
        + (Formula.box k (.impl (.plays (DIMCID k) MirrorBot Action.C)
            (.plays MirrorBot (DIMCID k) Action.D))).size + 1 := rfl
  have dImplFinal : (Formula.impl (.box b (.plays (DIMCID k) MirrorBot Action.D))
        (.plays (DIMCID k) MirrorBot Action.D)).size
      = (Formula.box b (.plays (DIMCID k) MirrorBot Action.D)).size
        + (Formula.plays (DIMCID k) MirrorBot Action.D).size + 1 := rfl
  have dLeg1 : (Formula.impl (.box k
        (.impl (.plays (DIMCID k) MirrorBot Action.C) (.plays MirrorBot (DIMCID k) Action.D)))
        (.plays (DIMCID k) MirrorBot Action.D)).size
      = (Formula.box k (.impl (.plays (DIMCID k) MirrorBot Action.C)
          (.plays MirrorBot (DIMCID k) Action.D))).size
        + (Formula.plays (DIMCID k) MirrorBot Action.D).size + 1 := rfl
  have leg1 : Pf ((Formula.impl (.box k
        (.impl (.plays (DIMCID k) MirrorBot Action.C) (.plays MirrorBot (DIMCID k) Action.D)))
        (.plays (DIMCID k) MirrorBot Action.D)).size)
      (.impl (.box k
        (.impl (.plays (DIMCID k) MirrorBot Action.C) (.plays MirrorBot (DIMCID k) Action.D)))
        (.plays (DIMCID k) MirrorBot Action.D)) := by
    have := Pf.searchBranch k
      (.impl (.plays .self .opp Action.C) (.plays .opp .self Action.D))
      Action.D Action.C (DIMCID k) MirrorBot rfl (Nat.le_refl _)
    simpa [DIMCID, Formula.subst, Prog.subst, MirrorBot] using this
  have hsim : Pf ((Formula.impl (.plays (DIMCID k) MirrorBot Action.D)
        (.plays MirrorBot (DIMCID k) Action.D)).size)
      (.impl (.plays (DIMCID k) MirrorBot Action.D)
        (.plays MirrorBot (DIMCID k) Action.D)) := by
    have := Pf.simStep MirrorBot .opp .self (DIMCID k) Action.D rfl (Nat.le_refl _)
    simpa [MirrorBot, Prog.subst] using this
  have hK : Pf ((Formula.impl (.plays MirrorBot (DIMCID k) Action.D)
        (.impl (.plays (DIMCID k) MirrorBot Action.C) (.plays MirrorBot (DIMCID k) Action.D))).size)
      (.impl (.plays MirrorBot (DIMCID k) Action.D)
        (.impl (.plays (DIMCID k) MirrorBot Action.C) (.plays MirrorBot (DIMCID k) Action.D))) :=
    Pf.implK (.plays MirrorBot (DIMCID k) Action.D)
      (.plays (DIMCID k) MirrorBot Action.C) (Nat.le_refl _)
  have hphi_guard : Pf (20 * Nat.log2 k + 300)
      (.impl (.plays (DIMCID k) MirrorBot Action.D)
        (.impl (.plays (DIMCID k) MirrorBot Action.C) (.plays MirrorBot (DIMCID k) Action.D))) := by
    refine Pf.implTrans _ _ _ _ _ hsim hK ?_
    rw [dφMD, dMDG, dφG]; omega
  have hbox_phi_guard : Pf (50 * Nat.log2 k + 700)
      (.box (20 * Nat.log2 k + 300)
        (.impl (.plays (DIMCID k) MirrorBot Action.D)
          (.impl (.plays (DIMCID k) MirrorBot Action.C) (.plays MirrorBot (DIMCID k) Action.D)))) := by
    refine Pf.boxIntro _ _ _ hphi_guard ?_
    rw [dBoxPhiG, dφG]; omega
  have hstep : Pf (100 * Nat.log2 k + 100000)
      (.impl (.box b (.plays (DIMCID k) MirrorBot Action.D))
        (.box k (.impl (.plays (DIMCID k) MirrorBot Action.C) (.plays MirrorBot (DIMCID k) Action.D)))) := by
    refine Pf.axK (20 * Nat.log2 k + 300) b k _ _
      (.plays (DIMCID k) MirrorBot Action.D)
      (.impl (.plays (DIMCID k) MirrorBot Action.C) (.plays MirrorBot (DIMCID k) Action.D))
      hbox_phi_guard ?_ ?_
    · omega
    · rw [dImplStep, dBoxbφ, dBoxkG]; omega
  refine Pf.implTrans _ _ _ _ _ hstep leg1 ?_
  rw [dImplFinal, dBoxbφ, dLeg1, dBoxkG]; omega

/-- The size/headroom bound feeding pblt_engine. -/
theorem dm_hsz_bound (Kc Ksz : Nat)
    (hKc : ∀ k, k ≥ Kc → 200 * Nat.log2 k + 20000 ≤ k)
    (hKsz : ∀ k, k ≥ Ksz → (8192 * 400 + 400) * Nat.log2 k + (8192 * 600000 + 40000) ≤ k)
    (k : Nat) (hk : k > max Kc Ksz) :
      8192 * ((300 * Nat.log2 k + 500000)
        + (Nat.log2 k + 15) + Nat.log2 (k - (200 * Nat.log2 k + 20000)) + 8)
        ≤ (k - (200 * Nat.log2 k + 20000)) := by
  have hc : 200 * Nat.log2 k + 20000 ≤ k :=
    hKc k (Nat.le_of_lt (lt_of_le_of_lt (Nat.le_max_left _ _) hk))
  have hlogf : Nat.log2 (k - (200 * Nat.log2 k + 20000)) ≤ Nat.log2 k :=
    log2_mono (Nat.sub_le _ _)
  have hbig := hKsz k (Nat.le_of_lt (lt_of_le_of_lt (Nat.le_max_right _ _) hk))
  have hcancel : (k - (200 * Nat.log2 k + 20000)) + (200 * Nat.log2 k + 20000) = k :=
    Nat.sub_add_cancel hc
  set a := Nat.log2 k with hadef
  set b := k - (200 * a + 20000) with hbdef
  set c := Nat.log2 (k - (200 * a + 20000)) with hcdef
  have hk2 : k = b + (200 * a + 20000) := by omega
  rw [hk2] at hbig
  omega

/-- The fb bound feeding hLoeb, stated in explicit subtraction form. -/
theorem dm_fb_bound (Kc Ksz : Nat)
    (hKc : ∀ k, k ≥ Kc → 200 * Nat.log2 k + 20000 ≤ k)
    (k : Nat) (hk : k > max Kc Ksz) :
      (k - (200 * Nat.log2 k + 20000)) + 200 * Nat.log2 k + 20000 ≤ k := by
  have hc : 200 * Nat.log2 k + 20000 ≤ k :=
    hKc k (Nat.le_of_lt (lt_of_le_of_lt (Nat.le_max_left _ _) hk))
  omega

/-- Mirror copies: play (fuel+2) MirrorBot (DIMCID k) = play (fuel+1) (DIMCID k) MirrorBot. -/
theorem dm_mirror_copies (k fuel : Nat) (a : Action)
    (h : play (fuel + 1) (DIMCID k) MirrorBot = some a) :
    play (fuel + 2) MirrorBot (DIMCID k) = some a := by
  simpa [play, eval, Prog.subst, MirrorBot] using h

/-- **DIMCID vs MirrorBot: mutual defection (D, D)** for all sufficiently large `k`. -/
theorem llm_outcome_DIMCID_vs_MirrorBot :
    ∃ k₂, ∀ k, k₂ < k →
      ∃ fuel, outcome fuel (DIMCID k) MirrorBot = some (.D, .D) := by
  let φ : Nat → Formula := fun k => .plays (DIMCID k) MirrorBot .D
  let f : Nat → Nat := fun k => k - (200 * Nat.log2 k + 20000)
  let pm : Nat → Nat := fun k => 300 * Nat.log2 k + 500000
  obtain ⟨Kc, hKc⟩ := linear_log2_add_le 200 20000
  obtain ⟨Ksz, hKsz⟩ := linear_log2_add_le (8192 * 400 + 400) (8192 * 600000 + 40000)
  have hLoeb : ∀ k, k > max Kc Ksz → Pf (pm k) (.impl (.box (f k) (φ k)) (φ k)) := by
    intro k hk
    have hfb : f k + 200 * Nat.log2 k + 20000 ≤ k := dm_fb_bound Kc Ksz hKc k hk
    exact dm_loeb_premise k (f k) hfb
  have hsz : ∀ k, k > max Kc Ksz →
      8192 * (pm k + (φ k).size + Nat.log2 (f k) + 8) ≤ f k := by
    intro k hk
    have hφsz : (φ k).size = Nat.log2 k + 15 := by
      show (Formula.plays (DIMCID k) MirrorBot .D).size = _
      simp only [Formula.size, DIMCID, MirrorBot, Prog.size, numCost]
    show 8192 * ((300 * Nat.log2 k + 500000) + (φ k).size
        + Nat.log2 (k - (200 * Nat.log2 k + 20000)) + 8) ≤ k - (200 * Nat.log2 k + 20000)
    rw [hφsz]
    exact dm_hsz_bound Kc Ksz hKc hKsz k hk
  obtain ⟨k₂, hk₂⟩ := pblt_engine φ f pm (max Kc Ksz) hLoeb hsz
  refine ⟨k₂, ?_⟩
  intro k hk
  obtain ⟨m, hm⟩ := hk₂ k hk
  have hInterp : (φ k).interp := Pf_sound m (φ k) hm
  obtain ⟨n, hn⟩ := hInterp
  have hn' : play n (DIMCID k) MirrorBot = some Action.D := hn
  have hA : play (n + 2) (DIMCID k) MirrorBot = some Action.D := by
    unfold play at hn' ⊢; exact eval_mono_le hn' (n + 2) (by omega)
  have hA1 : play (n + 1) (DIMCID k) MirrorBot = some Action.D := by
    unfold play at hn' ⊢; exact eval_mono_le hn' (n + 1) (by omega)
  have hB : play (n + 2) MirrorBot (DIMCID k) = some Action.D :=
    dm_mirror_copies k n Action.D hA1
  exact ⟨n + 2, outcome_of_plays _ _ _ _ _ hA hB⟩

end PD.Theorems
