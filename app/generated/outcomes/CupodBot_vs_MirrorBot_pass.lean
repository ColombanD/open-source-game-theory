import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Axioms
import PrisonersDilemma.Bots.CupodBot
import PrisonersDilemma.Bots.MirrorBot
import PrisonersDilemma.Theorems.Helpers
import PrisonersDilemma.Theorems.ProofSearch

open PD
open PD.Axioms
open PD.Bots
namespace PD.Theorems

theorem cupod_mirror_loeb_premise (k : Nat) :
    ∃ m, proofSearch m
      (.impl (.box k (.plays MirrorBot (CupodBot k) .D))
             (.plays MirrorBot (CupodBot k) .D)) = true := by
  have hSearch :
      ∃ m, proofSearch m
        (.impl (.box k (.plays MirrorBot (CupodBot k) .D))
               (.plays (CupodBot k) MirrorBot .D)) = true := by
    have h := proof_system_verifies_search_branch
                k (.plays .opp .self .D) .D .C (CupodBot k) MirrorBot rfl
    simpa [Formula.subst, Prog.subst] using h
  have hMirror :
      ∃ m, proofSearch m
        (.impl (.plays (CupodBot k) MirrorBot .D)
               (.plays MirrorBot (CupodBot k) .D)) = true := by
    have h := proof_system_verifies_sim MirrorBot .opp .self (CupodBot k) .D rfl
    simpa [Prog.subst, MirrorBot] using h
  exact proofSearch_impl_trans _ _ _ hSearch hMirror

theorem CupodBot_plays_D_against_MirrorBot (k fuel : Nat)
    (hk : proofSearch k (.plays MirrorBot (CupodBot k) .D) = true) :
    play (fuel + 2) (CupodBot k) MirrorBot = some .D := by
  show eval (fuel + 2) (CupodBot k) MirrorBot (CupodBot k) = some .D
  unfold CupodBot at hk ⊢
  simp [eval, Prog.subst, Formula.subst, hk]

theorem CupodBot_plays_C_against_MirrorBot (k fuel : Nat)
    (hk : proofSearch k (.plays MirrorBot (CupodBot k) .D) = false) :
    play (fuel + 2) (CupodBot k) MirrorBot = some .C := by
  show eval (fuel + 2) (CupodBot k) MirrorBot (CupodBot k) = some .C
  unfold CupodBot at hk ⊢
  simp [eval, Prog.subst, Formula.subst, hk]

theorem MirrorBot_plays_D_against_CupodBot (k fuel : Nat)
    (hk : proofSearch k (.plays MirrorBot (CupodBot k) .D) = true) :
    play (fuel + 3) MirrorBot (CupodBot k) = some .D := by
  have hC : play (fuel + 2) (CupodBot k) MirrorBot = some .D :=
    CupodBot_plays_D_against_MirrorBot k fuel hk
  simpa [play, eval, Prog.subst, MirrorBot] using hC

theorem MirrorBot_plays_C_against_CupodBot (k fuel : Nat)
    (hk : proofSearch k (.plays MirrorBot (CupodBot k) .D) = false) :
    play (fuel + 3) MirrorBot (CupodBot k) = some .C := by
  have hC : play (fuel + 2) (CupodBot k) MirrorBot = some .C :=
    CupodBot_plays_C_against_MirrorBot k fuel hk
  simpa [play, eval, Prog.subst, MirrorBot] using hC

theorem proofSearch_k_of_play_MirrorBot_cupod
    (k n : Nat) (h : play n MirrorBot (CupodBot k) = some .D) :
    proofSearch k (.plays MirrorBot (CupodBot k) .D) = true := by
  cases hps : proofSearch k (.plays MirrorBot (CupodBot k) .D) with
  | true  => rfl
  | false =>
    exfalso
    rcases n with _ | _ | _ | n
    · simp [play, eval] at h
    · simp [play, eval, MirrorBot] at h
    · have hev : play 2 MirrorBot (CupodBot k) = none := by
        unfold CupodBot
        simp [play, eval, Prog.subst, MirrorBot, Formula.subst]
      rw [hev] at h
      cases h
    · have hev : play (n + 3) MirrorBot (CupodBot k) = some .C := by
        simpa using MirrorBot_plays_C_against_CupodBot k n hps
      rw [hev] at h
      cases h

theorem llm_outcome_CupodBot_vs_MirrorBot :
    ∃ k₂, ∀ k, k₂ < k →
      ∃ fuel, outcome fuel (CupodBot k) MirrorBot = some (.D, .D) := by
  let φ : Nat → Formula := fun k => .plays MirrorBot (CupodBot k) .D
  have hMono : ∀ a b : Nat, a ≤ b → id a ≤ id b := fun _ _ h => h
  have hLog : ∃ c kHat, c > 0 ∧ ∀ k, k > kHat → id k > c * Nat.log2 k := by
    refine ⟨1, 0, Nat.zero_lt_one, ?_⟩
    intro k hk
    have hlog : Nat.log2 k < k := by
      rw [Nat.log2_lt (Nat.pos_iff_ne_zero.mp hk)]
      exact Nat.lt_two_pow_self
    simpa using hlog
  have hLoeb :
      ∀ k, k > 0 →
        ∃ m, proofSearch m (.impl (.box (id k) (φ k)) (φ k)) = true := by
    intro k _
    simpa using cupod_mirror_loeb_premise k
  obtain ⟨k₂, hk₂⟩ := PBLT φ id 0 hMono hLog hLoeb
  refine ⟨k₂, ?_⟩
  intro k hk
  obtain ⟨m, hm⟩ := hk₂ k hk
  have hInterp : (φ k).interp := proofSearch_sound m (φ k) hm
  obtain ⟨n, hMirror⟩ := hInterp
  have hPS : proofSearch k (.plays MirrorBot (CupodBot k) .D) = true :=
    proofSearch_k_of_play_MirrorBot_cupod k n hMirror
  refine ⟨3, ?_⟩
  have hA : play 3 (CupodBot k) MirrorBot = some .D := by
    simpa using CupodBot_plays_D_against_MirrorBot k 1 hPS
  have hB : play 3 MirrorBot (CupodBot k) = some .D := by
    simpa using MirrorBot_plays_D_against_CupodBot k 0 hPS
  exact outcome_of_plays _ _ _ _ _ hA hB

end PD.Theorems
