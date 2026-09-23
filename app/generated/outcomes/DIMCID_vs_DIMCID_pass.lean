import PrisonersDilemma.Bots.LlmGenerations.DIMCID
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Base.Asymptotics

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

/-- The Löb premise for DIMCID self-play, at a lowered box subscript `b`.
    `searchBranch` reads DIMCID's `.search` body giving `□_k(C-atom → φ) → φ`
    (φ = "DIMCID plays D vs DIMCID"); `implK` gives `φ → (C-atom → φ)`, boxed via
    `axK` into `□_b φ → □_k(C-atom → φ)`; composing yields `□_b φ → φ`. -/
theorem dimcid_loeb_premise (k b : Nat)
    (hb : b + 10 * Nat.log2 k + 118 ≤ k) :
    Pf (100 * Nat.log2 k + 100000)
       (.impl (.box b (.plays (DIMCID k) (DIMCID k) Action.D))
              (.plays (DIMCID k) (DIMCID k) Action.D)) := by
  have leg1 : Pf ((Formula.impl (.box k
        (.impl (.plays (DIMCID k) (DIMCID k) Action.C) (.plays (DIMCID k) (DIMCID k) Action.D)))
        (.plays (DIMCID k) (DIMCID k) Action.D)).size)
      (.impl (.box k
        (.impl (.plays (DIMCID k) (DIMCID k) Action.C) (.plays (DIMCID k) (DIMCID k) Action.D)))
        (.plays (DIMCID k) (DIMCID k) Action.D)) := by
    have := Pf.searchBranch k
      (.impl (.plays .self .opp Action.C) (.plays .opp .self Action.D))
      Action.D Action.C (DIMCID k) (DIMCID k) rfl (Nat.le_refl _)
    simpa [DIMCID, Formula.subst, Prog.subst] using this
  have step1 : Pf ((Formula.impl (.plays (DIMCID k) (DIMCID k) Action.D)
        (.impl (.plays (DIMCID k) (DIMCID k) Action.C) (.plays (DIMCID k) (DIMCID k) Action.D))).size)
      (.impl (.plays (DIMCID k) (DIMCID k) Action.D)
        (.impl (.plays (DIMCID k) (DIMCID k) Action.C) (.plays (DIMCID k) (DIMCID k) Action.D))) :=
    Pf.implK (.plays (DIMCID k) (DIMCID k) Action.D) (.plays (DIMCID k) (DIMCID k) Action.C) (Nat.le_refl _)
  have step2 := Pf.boxIntro _ _ _ step1 (Nat.le_refl _)
  have step3 := Pf.axK _ b k _ _ (.plays (DIMCID k) (DIMCID k) Action.D)
      (.impl (.plays (DIMCID k) (DIMCID k) Action.C) (.plays (DIMCID k) (DIMCID k) Action.D))
      step2 (by simp only [Formula.size, DIMCID, Prog.size, numCost] at hb ⊢; omega) (Nat.le_refl _)
  refine Pf.implTrans _ _ _ _ _ step3 leg1 ?_
  have hlogb : Nat.log2 b ≤ Nat.log2 k := log2_mono (by omega)
  simp only [Formula.size, DIMCID, Prog.size, numCost]
  have hself : ∀ x, Nat.log2 x ≤ x := log2_le_self
  have h2 := hself (Nat.log2 k + 1 + (1 + 1 + 1 + (1 + 1 + 1) + 1) + 1 + 1 + 1 +
            (Nat.log2 k + 1 + (1 + 1 + 1 + (1 + 1 + 1) + 1) + 1 + 1 + 1) +
          1 +
        (Nat.log2 k + 1 + (1 + 1 + 1 + (1 + 1 + 1) + 1) + 1 + 1 + 1 +
                (Nat.log2 k + 1 + (1 + 1 + 1 + (1 + 1 + 1) + 1) + 1 + 1 + 1) +
              1 +
            (Nat.log2 k + 1 + (1 + 1 + 1 + (1 + 1 + 1) + 1) + 1 + 1 + 1 +
                (Nat.log2 k + 1 + (1 + 1 + 1 + (1 + 1 + 1) + 1) + 1 + 1 + 1) +
              1) +
          1) +
      1)
  omega

/-- **DIMCID vs DIMCID: mutual defection (D, D)** for all sufficiently large `k`.
    In self-play the guard "if I cooperate, opponent defects" is the Löb fixpoint on
    defection; PBLT (with box subscript `f k = k − O(log k)`) makes "DIMCID plays D"
    provable, so both bots take the defect branch. -/
theorem llm_outcome_DIMCID_vs_DIMCID :
    ∃ k₂, ∀ k, k₂ < k →
      ∃ fuel, outcome fuel (DIMCID k) (DIMCID k) = some (.D, .D) := by
  let φ : Nat → Formula := fun k => .plays (DIMCID k) (DIMCID k) .D
  let f : Nat → Nat := fun k => k - (10 * Nat.log2 k + 118)
  let pm : Nat → Nat := fun k => 100 * Nat.log2 k + 100000
  obtain ⟨Kc, hKc⟩ := linear_log2_add_le 10 118
  obtain ⟨Ksz, hKsz⟩ := linear_log2_add_le (8192 * 103 + 10) (8192 * 100031 + 118)
  have hLoeb : ∀ k, k > max Kc Ksz → Pf (pm k) (.impl (.box (f k) (φ k)) (φ k)) := by
    intro k hk
    have hc : 10 * Nat.log2 k + 118 ≤ k :=
      hKc k (Nat.le_of_lt (lt_of_le_of_lt (Nat.le_max_left _ _) hk))
    have hcancel : f k + (10 * Nat.log2 k + 118) = k := Nat.sub_add_cancel hc
    have hfb : f k + 10 * Nat.log2 k + 118 ≤ k := by omega
    exact dimcid_loeb_premise k (f k) hfb
  have hsz : ∀ k, k > max Kc Ksz →
      8192 * (pm k + (φ k).size + Nat.log2 (f k) + 8) ≤ f k := by
    intro k hk
    have hc : 10 * Nat.log2 k + 118 ≤ k :=
      hKc k (Nat.le_of_lt (lt_of_le_of_lt (Nat.le_max_left _ _) hk))
    have hcancel : f k + (10 * Nat.log2 k + 118) = k := Nat.sub_add_cancel hc
    have hlogf : Nat.log2 (f k) ≤ Nat.log2 k := log2_mono (by omega)
    have hbig := hKsz k (Nat.le_of_lt (lt_of_le_of_lt (Nat.le_max_right _ _) hk))
    have hφsz : (φ k).size = 2 * Nat.log2 k + 23 := by
      show (Formula.plays (DIMCID k) (DIMCID k) .D).size = _
      simp only [Formula.size, DIMCID, Prog.size, numCost]; omega
    have hpmval : pm k = 100 * Nat.log2 k + 100000 := rfl
    rw [hφsz, hpmval]
    omega
  obtain ⟨k₂, hk₂⟩ := pblt_engine φ f pm (max Kc Ksz) hLoeb hsz
  refine ⟨k₂, ?_⟩
  intro k hk
  obtain ⟨m, hm⟩ := hk₂ k hk
  have hInterp : (φ k).interp := Pf_sound m (φ k) hm
  obtain ⟨n, hn⟩ := hInterp
  refine ⟨n, ?_⟩
  have hn' : play n (DIMCID k) (DIMCID k) = some Action.D := hn
  simp [outcome, hn']
