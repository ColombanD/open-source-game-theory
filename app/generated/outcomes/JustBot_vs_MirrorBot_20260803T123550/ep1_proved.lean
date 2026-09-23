import PrisonersDilemma.Bots.LlmGenerations.JustBot
import PrisonersDilemma.Bots.MirrorBot
import PrisonersDilemma.Bots.DupocBot
import PrisonersDilemma.Dynamics
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Base.Asymptotics
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.Theorems.JustBot.Helpers

open PD PD.Bots PD.BaseTheorems
namespace PD.Theorems

theorem jm_loeb_premise (k : Nat) :
    Pf (20 * Nat.log2 k + 200)
      (.impl (.box k (.plays MirrorBot (.bot (DupocBot k)) .C))
             (.plays MirrorBot (.bot (DupocBot k)) .C)) := by
  refine Pf.implTrans _ _ _ (5 * Nat.log2 k + 80) (5 * Nat.log2 k + 80)
    (Pf.botSearchStep k (.plays .opp .self .C) .C .D (.bot (DupocBot k)) MirrorBot rfl ?_)
    (Pf.simStep MirrorBot .opp .self (.bot (DupocBot k)) .C rfl ?_) ?_ <;>
  · simp only [Formula.subst, Prog.subst, numCost, Formula.size, Prog.size, DupocBot, MirrorBot]
    omega

theorem MirrorBot_plays_D_against_botDupoc_JM (k fuel : Nat)
    (hg : proofSearch k (.plays MirrorBot (.bot (DupocBot k)) .C) = false) :
    play (fuel + 4) MirrorBot (.bot (DupocBot k)) = some .D := by
  show eval (fuel + 4) MirrorBot (.bot (DupocBot k)) MirrorBot = some .D
  have hg' : proofSearch k
      (Formula.plays (Prog.opp.sim Prog.self)
        (Prog.search k (Formula.plays Prog.opp Prog.self Action.C) (Prog.const Action.C)
            (Prog.const Action.D)).bot Action.C) = false := hg
  simp only [MirrorBot, eval, Prog.subst, DupocBot, Formula.subst, hg',
    Bool.false_eq_true, if_false]

theorem proofSearch_of_play_MirrorBot_botDupoc (k n : Nat)
    (h : play n MirrorBot (.bot (DupocBot k)) = some .C) :
    proofSearch k (.plays MirrorBot (.bot (DupocBot k)) .C) = true := by
  cases hps : proofSearch k (.plays MirrorBot (.bot (DupocBot k)) .C) with
  | true => rfl
  | false =>
    exfalso
    rcases n with _ | _ | _ | _ | n
    · simp [play, eval] at h
    · simp [play, eval, MirrorBot] at h
    · simp [play, eval, MirrorBot, Prog.subst] at h
    · simp [play, eval, MirrorBot, Prog.subst, DupocBot, Formula.subst] at h
    · have hev : play (n + 4) MirrorBot (.bot (DupocBot k)) = some .D :=
        MirrorBot_plays_D_against_botDupoc_JM k n hps
      rw [hev] at h; cases h

theorem jm_guard_true :
    ∃ k₂, ∀ k, k₂ < k →
      proofSearch k (.plays MirrorBot (.bot (DupocBot k)) .C) = true := by
  let φ : Nat → Formula := fun k => .plays MirrorBot (.bot (DupocBot k)) .C
  have hφsz : ∀ k, (φ k).size ≤ 100 * Nat.log2 k + 1000 := by
    intro k
    show (Formula.plays MirrorBot (.bot (DupocBot k)) .C).size ≤ _
    simp only [numCost, Formula.size, Prog.size, DupocBot, MirrorBot]
    omega
  have hpm : ∀ k, 20 * Nat.log2 k + 200 ≤ 100 * Nat.log2 k + 1000 := fun k => by omega
  have hLoeb : ∀ k, k > 0 → Pf (20 * Nat.log2 k + 200) (.impl (.box k (φ k)) (φ k)) :=
    fun k _ => jm_loeb_premise k
  obtain ⟨k₂, hk₂⟩ := pblt_engine_id φ (fun k => 20 * Nat.log2 k + 200) 0 hφsz hpm hLoeb
  refine ⟨k₂, fun k hk => ?_⟩
  obtain ⟨m, hm⟩ := hk₂ k hk
  have hInterp : (φ k).interp := Pf_sound m (φ k) hm
  obtain ⟨n, hplay⟩ := hInterp
  exact proofSearch_of_play_MirrorBot_botDupoc k n hplay

theorem llm_outcome_JustBot_vs_MirrorBot :
    ∃ k₂, ∀ k, k₂ < k →
      ∃ fuel, outcome fuel (JustBot k) MirrorBot = some (.C, .C) := by
  obtain ⟨k₂, hg⟩ := jm_guard_true
  refine ⟨k₂, fun k hk => ?_⟩
  have hgk := hg k hk
  have hA : play 4 (JustBot k) MirrorBot = some .C := by
    have := JustBot_eval_step k 2 MirrorBot .C (by simpa using hgk)
    simpa using this
  have hB : play 5 MirrorBot (JustBot k) = some .C := by
    show eval 5 MirrorBot (JustBot k) MirrorBot = some .C
    simp only [MirrorBot, eval, Prog.subst]
    exact hA
  have hA' : play 5 (JustBot k) MirrorBot = some .C := by
    have := JustBot_eval_step k 3 MirrorBot .C (by simpa using hgk)
    simpa using this
  exact ⟨5, outcome_of_plays 5 (JustBot k) MirrorBot .C .C hA' hB⟩

end PD.Theorems
