import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Axioms
import PrisonersDilemma.Bots.LlmGenerations.PrudentBot
import PrisonersDilemma.Bots.EBot
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Bots.MirrorBot
import PrisonersDilemma.Theorems.CooperateBot
import PrisonersDilemma.Theorems.DefectBot
import PrisonersDilemma.Theorems.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.SizeLemmas

open PD
open PD.Axioms
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

set_option linter.constructorNameAsVariable false

/-- PrudentBot defects when its outer search guard fails. -/
theorem prudent_eval_outer_false (k fuel : Nat) (q : Prog)
    (h1 : proofSearch k (.plays q (PrudentBot k) .C) = false) :
    play (fuel + 2) (PrudentBot k) q = some .D := by
  show eval (fuel + 2) (PrudentBot k) q (PrudentBot k) = some .D
  unfold PrudentBot at h1 ⊢
  simp [eval, Prog.subst, Formula.subst, h1]

/-- PrudentBot defects when outer guard holds but inner (prudence) guard fails. -/
theorem prudent_eval_inner_false (k fuel : Nat) (q : Prog)
    (h1 : proofSearch k (.plays q (PrudentBot k) .C) = true)
    (h2 : proofSearch k (.plays q (.bot DefectBot) .D) = false) :
    play (fuel + 3) (PrudentBot k) q = some .D := by
  show eval (fuel + 3) (PrudentBot k) q (PrudentBot k) = some .D
  unfold PrudentBot at h1 ⊢
  simp [eval, Prog.subst, Formula.subst, h1, h2]

/-- PrudentBot cooperates when both guards hold. -/
theorem prudent_eval_both_true (k fuel : Nat) (q : Prog)
    (h1 : proofSearch k (.plays q (PrudentBot k) .C) = true)
    (h2 : proofSearch k (.plays q (.bot DefectBot) .D) = true) :
    play (fuel + 3) (PrudentBot k) q = some .C := by
  show eval (fuel + 3) (PrudentBot k) q (PrudentBot k) = some .C
  unfold PrudentBot at h1 ⊢
  simp [eval, Prog.subst, Formula.subst, h1, h2]

/-- Inversion: if PrudentBot plays C against q, its outer guard fired. -/
theorem prudent_outer_true_of_play_C (k n : Nat) (q : Prog)
    (h : play n (PrudentBot k) q = some .C) :
    proofSearch k (.plays q (PrudentBot k) .C) = true := by
  cases hps : proofSearch k (.plays q (PrudentBot k) .C) with
  | true => rfl
  | false =>
    exfalso
    rcases n with _ | _ | n
    · simp [play, eval] at h
    · simp [play, eval, PrudentBot, Prog.subst, Formula.subst] at h
    · have hD : play (n + 2) (PrudentBot k) q = some .D :=
        prudent_eval_outer_false k n q hps
      rw [hD] at h; cases h

/-- EBot defects against `.bot DefectBot`. -/
theorem EBot_plays_D_vs_bot_DefectBot (k : Nat) :
    play (k + 6) EBot (.bot DefectBot) = some .D := by
  show eval (k + 6) EBot (.bot DefectBot) EBot = some .D
  have hOuterG : eval (k + 5) EBot (.bot DefectBot) (.sim .opp (.bot DefectBot)) = some .D := by
    simp only [eval, Prog.subst, DefectBot]
  have hInnerG : eval (k + 4) EBot (.bot DefectBot) (.sim .opp (.bot CooperateBot)) = some .D := by
    simp only [eval, Prog.subst, DefectBot]
  have hInnerInnerG : eval (k + 3) EBot (.bot DefectBot) (.sim .opp (.bot MirrorBot)) = some .D := by
    simp only [eval, Prog.subst, DefectBot]
  have hInnerInnerIte : eval (k + 4) EBot (.bot DefectBot)
      (.ite (.sim .opp (.bot MirrorBot)) .C (.const .C) (.const .D)) = some .D := by
    rw [eval_ite_from_guard _ _ _ _ _ _ _ _ hInnerInnerG]; rfl
  have hInnerIte : eval (k + 5) EBot (.bot DefectBot)
      (.ite (.sim .opp (.bot CooperateBot)) .C (.const .C)
        (.ite (.sim .opp (.bot MirrorBot)) .C (.const .C) (.const .D))) = some .D := by
    rw [eval_ite_from_guard _ _ _ _ _ _ _ _ hInnerG]
    exact hInnerInnerIte
  show eval (k + 6) EBot (.bot DefectBot)
      (.ite (.sim .opp (.bot DefectBot)) .C (.const .D)
        (.ite (.sim .opp (.bot CooperateBot)) .C (.const .C)
          (.ite (.sim .opp (.bot MirrorBot)) .C (.const .C) (.const .D)))) = some .D
  rw [eval_ite_from_guard _ _ _ _ _ _ _ _ hOuterG]
  exact hInnerIte

/-- Löb premise for PrudentBot cooperating with `.bot MirrorBot`. -/
theorem prudent_botmirror_loeb_premise :
    ∃ K₀ : Nat, ∀ k : Nat, k ≥ K₀ →
      Provable k (.impl (.box k (.plays (.bot MirrorBot) (PrudentBot k) .C))
                        (.plays (.bot MirrorBot) (PrudentBot k) .C)) := by
  obtain ⟨K₀log, hK₀log⟩ := linear_log2_add_le 5 41
  refine ⟨max K₀log (atom_cost 4), fun k hk => ?_⟩
  have hklog : k ≥ K₀log := le_trans (le_max_left _ _) hk
  have hkatom : atom_cost 4 ≤ k := le_trans (le_max_right _ _) hk
  have hbound := hK₀log k hklog
  have hd : DefectBot.size = 1 := rfl
  have hm : MirrorBot.size = 3 := rfl
  -- prudence: bot MirrorBot plays D vs bot DefectBot
  have hplayPrud : play 4 (.bot MirrorBot) (.bot DefectBot) = some .D := by
    simp [play, eval, Prog.subst, MirrorBot, DefectBot]
  have hprud : Provable k (.plays (.bot MirrorBot) (.bot DefectBot) .D) :=
    Provable.atom (atom_monotone (atom_cost 4) k _ hkatom
      (atom_complete (.bot MirrorBot) (.bot DefectBot) .D 4 hplayPrud))
  -- searchThenSearch_t
  have hA : Provable k (.impl (.box k (.plays (.bot MirrorBot) (PrudentBot k) .C))
                              (.plays (PrudentBot k) (.bot MirrorBot) .C)) := by
    refine Provable.searchThenSearch_t k k (.plays .opp .self .C)
      (.plays .opp (.bot DefectBot) .D) .C .D (.const .D) (PrudentBot k) (.bot MirrorBot)
      rfl hprud ?_
    simp only [Formula.size, Prog.size, Formula.subst, Prog.subst, PrudentBot, MirrorBot]
    omega
  have hB : Provable k (.impl (.plays (PrudentBot k) (.bot MirrorBot) .C)
                              (.plays (.bot MirrorBot) (PrudentBot k) .C)) := by
    apply Provable.struct
    refine ⟨Derivation.botSimStep (.bot MirrorBot) .opp .self (PrudentBot k) .C rfl, ?_⟩
    simp only [Derivation.size, Formula.size, Prog.size, PrudentBot, MirrorBot]
    omega
  refine Provable.implTrans (.box k (.plays (.bot MirrorBot) (PrudentBot k) .C))
    (.plays (PrudentBot k) (.bot MirrorBot) .C)
    (.plays (.bot MirrorBot) (PrudentBot k) .C) k k hA hB ?_
  simp only [Formula.size, Prog.size, PrudentBot, MirrorBot]
  omega

/-- PrudentBot's outer guard against `.bot MirrorBot` is provable for large k. -/
theorem prudent_botmirror_coop :
    ∃ k₂, ∀ k, k₂ < k →
      proofSearch k (.plays (.bot MirrorBot) (PrudentBot k) .C) = true := by
  let φ : Nat → Formula := fun k => .plays (.bot MirrorBot) (PrudentBot k) .C
  have hMono : ∀ a b : Nat, a ≤ b → id a ≤ id b := fun _ _ h => h
  have hLog : ∃ c kHat, c > 0 ∧ ∀ k, k > kHat → id k > c * Nat.log2 k := by
    refine ⟨1, 0, Nat.zero_lt_one, ?_⟩
    intro k hk
    have hlog : Nat.log2 k < k := by
      rw [Nat.log2_lt (Nat.pos_iff_ne_zero.mp hk)]
      exact Nat.lt_two_pow_self
    simpa using hlog
  obtain ⟨K₀, hK₀⟩ := prudent_botmirror_loeb_premise
  have hLoeb :
      ∀ k, k > K₀ → ∃ m, Provable m (.impl (.box (id k) (φ k)) (φ k)) := by
    intro k hk
    exact ⟨k, hK₀ k (Nat.le_of_lt hk)⟩
  obtain ⟨k₂, hk₂⟩ := PBLT φ id K₀ hMono hLog hLoeb
  refine ⟨k₂, fun k hk => ?_⟩
  obtain ⟨m, hm⟩ := hk₂ k hk
  have hInterp : (φ k).interp := Provable_sound m (φ k) hm
  obtain ⟨n, hplay⟩ := hInterp
  rcases n with _ | _ | n
  · simp [play, eval] at hplay
  · simp [play, eval] at hplay
  · have heq : play (n + 2) (.bot MirrorBot) (PrudentBot k)
             = play n (PrudentBot k) (.bot MirrorBot) := by
      simp [play, eval, Prog.subst, MirrorBot]
    rw [heq] at hplay
    exact prudent_outer_true_of_play_C k n (.bot MirrorBot) hplay

/-- The main theorem: PrudentBot and EBot mutually cooperate for large k. -/
theorem llm_outcome_PrudentBot_vs_EBot :
    ∃ k₂, ∀ k, k₂ < k →
      ∃ fuel, outcome fuel (PrudentBot k) EBot = some (.C, .C) := by
  obtain ⟨k₂c, hcoop⟩ := prudent_botmirror_coop
  refine ⟨max k₂c (atom_cost 7), fun k hk => ?_⟩
  have hk2 : k₂c < k := lt_of_le_of_lt (le_max_left _ _) hk
  have ha7 : atom_cost 7 ≤ k := le_of_lt (lt_of_le_of_lt (le_max_right _ _) hk)
  have hb2 : atom_cost 2 ≤ k := le_trans (atom_cost_mono (by omega)) ha7
  have hb4 : atom_cost 4 ≤ k := le_trans (atom_cost_mono (by omega)) ha7
  have hb6 : atom_cost 6 ≤ k := le_trans (atom_cost_mono (by omega)) ha7
  have hcoopk : proofSearch k (.plays (.bot MirrorBot) (PrudentBot k) .C) = true := hcoop k hk2
  -- probe1: PrudentBot defects vs bot DefectBot (outer guard false)
  have hf1 : proofSearch k (.plays (.bot DefectBot) (PrudentBot k) .C) = false := by
    cases h : proofSearch k (.plays (.bot DefectBot) (PrudentBot k) .C) with
    | true => exact absurd (proofSearch_sound _ _ h) (interp_bot_DefectBot_plays_C_false _)
    | false => rfl
  have p1 : play 5 (PrudentBot k) (.bot DefectBot) = some .D :=
    prudent_eval_outer_false k 3 (.bot DefectBot) hf1
  -- probe2: PrudentBot defects vs bot CooperateBot (outer true, inner false)
  have ht2 : proofSearch k (.plays (.bot CooperateBot) (PrudentBot k) .C) = true := by
    have hplay : play 2 (.bot CooperateBot) (PrudentBot k) = some .C :=
      play_bot_CooperateBot 0 (PrudentBot k)
    exact (proofSearch_spec _ _).2 (Provable.atom
      (atom_monotone (atom_cost 2) k _ hb2
        (atom_complete (.bot CooperateBot) (PrudentBot k) .C 2 hplay)))
  have hf2 : proofSearch k (.plays (.bot CooperateBot) (.bot DefectBot) .D) = false := by
    cases h : proofSearch k (.plays (.bot CooperateBot) (.bot DefectBot) .D) with
    | true => exact absurd (proofSearch_sound _ _ h) (interp_bot_CooperateBot_plays_D_false _)
    | false => rfl
  have p2 : play 4 (PrudentBot k) (.bot CooperateBot) = some .D :=
    prudent_eval_inner_false k 1 (.bot CooperateBot) ht2 hf2
  -- probe3: PrudentBot cooperates vs bot MirrorBot (both true)
  have ht3 : proofSearch k (.plays (.bot MirrorBot) (.bot DefectBot) .D) = true := by
    have hplay : play 4 (.bot MirrorBot) (.bot DefectBot) = some .D := by
      simp [play, eval, Prog.subst, MirrorBot, DefectBot]
    exact (proofSearch_spec _ _).2 (Provable.atom
      (atom_monotone (atom_cost 4) k _ hb4
        (atom_complete (.bot MirrorBot) (.bot DefectBot) .D 4 hplay)))
  have p3 : play 3 (PrudentBot k) (.bot MirrorBot) = some .C :=
    prudent_eval_both_true k 0 (.bot MirrorBot) hcoopk ht3
  -- EBot plays C vs PrudentBot
  have hg1 : eval 6 EBot (PrudentBot k) (.sim .opp (.bot DefectBot)) = some .D :=
    eval_sim_opp_bot_of_play 5 EBot (PrudentBot k) DefectBot .D p1
  have hg2 : eval 5 EBot (PrudentBot k) (.sim .opp (.bot CooperateBot)) = some .D :=
    eval_sim_opp_bot_of_play 4 EBot (PrudentBot k) CooperateBot .D p2
  have hg3 : eval 4 EBot (PrudentBot k) (.sim .opp (.bot MirrorBot)) = some .C :=
    eval_sim_opp_bot_of_play 3 EBot (PrudentBot k) MirrorBot .C p3
  have hII : eval 5 EBot (PrudentBot k)
      (.ite (.sim .opp (.bot MirrorBot)) .C (.const .C) (.const .D)) = some .C := by
    rw [eval_ite_from_guard _ _ _ _ _ _ _ _ hg3]; rfl
  have hI : eval 6 EBot (PrudentBot k)
      (.ite (.sim .opp (.bot CooperateBot)) .C (.const .C)
        (.ite (.sim .opp (.bot MirrorBot)) .C (.const .C) (.const .D))) = some .C := by
    rw [eval_ite_from_guard _ _ _ _ _ _ _ _ hg2]
    exact hII
  have hEBotC : play 7 EBot (PrudentBot k) = some .C := by
    show eval 7 EBot (PrudentBot k)
      (.ite (.sim .opp (.bot DefectBot)) .C (.const .D)
        (.ite (.sim .opp (.bot CooperateBot)) .C (.const .C)
          (.ite (.sim .opp (.bot MirrorBot)) .C (.const .C) (.const .D)))) = some .C
    rw [eval_ite_from_guard _ _ _ _ _ _ _ _ hg1]
    exact hI
  -- PrudentBot plays C vs EBot
  have hg1P : proofSearch k (.plays EBot (PrudentBot k) .C) = true :=
    (proofSearch_spec _ _).2 (Provable.atom
      (atom_monotone (atom_cost 7) k _ ha7
        (atom_complete EBot (PrudentBot k) .C 7 hEBotC)))
  have hg2P : proofSearch k (.plays EBot (.bot DefectBot) .D) = true := by
    have hplay : play 6 EBot (.bot DefectBot) = some .D := EBot_plays_D_vs_bot_DefectBot 0
    exact (proofSearch_spec _ _).2 (Provable.atom
      (atom_monotone (atom_cost 6) k _ hb6
        (atom_complete EBot (.bot DefectBot) .D 6 hplay)))
  have hPrudC : play 7 (PrudentBot k) EBot = some .C :=
    prudent_eval_both_true k 4 EBot hg1P hg2P
  exact ⟨7, outcome_of_plays 7 (PrudentBot k) EBot .C .C hPrudC hEBotC⟩

end PD.Theorems
