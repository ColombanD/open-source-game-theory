import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Axioms
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Bots.DBot
import PrisonersDilemma.Bots.OBot
import PrisonersDilemma.Bots.TitForTatBot
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Bots.LlmGenerations.PrudentBot
import PrisonersDilemma.Theorems.CooperateBot
import PrisonersDilemma.Theorems.DefectBot
import PrisonersDilemma.Theorems.CupodTrollBot
import PrisonersDilemma.Theorems.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.SizeLemmas
import PrisonersDilemma.Bots.EBot
import PrisonersDilemma.Bots.CupodTrollBot

open PD
open PD.Axioms
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

/-- PrudentBot's head, unfolded once. The cooperation `.search` is at the root;
    the prudence (`opp defects vs DefectBot`) search is folded into its THEN
    branch. -/
theorem PrudentBot_eq (k : Nat) :
    PrudentBot k = .search k (Formula.plays .opp .self Action.C)
      (.search k (Formula.plays .opp (.bot DefectBot) Action.D)
        (.const Action.C) (.const Action.D))
      (.const Action.D) := rfl


/-- Core lemma for every matchup in which PrudentBot defects: if the opponent
    `opp` does **not** cooperate with PrudentBot (the outer cooperation search is
    false), PrudentBot lands in the root `.search`'s else-branch and defects. The
    inner prudence search is never reached. -/
theorem PrudentBot_plays_D_of_search_false (k fuel : Nat) (opponent : Prog)
    (hf : proofSearch k (Formula.plays opponent (PrudentBot k) Action.C) = false) :
    play (fuel + 2) (PrudentBot k) opponent = some .D := by
  show eval (fuel + 2) (PrudentBot k) opponent (PrudentBot k) = some .D
  rw [PrudentBot_eq]
  show (if proofSearch k ((Formula.plays .opp .self Action.C).subst (PrudentBot k) opponent)
          then eval (fuel + 1) (PrudentBot k) opponent
                (.search k (Formula.plays .opp (.bot DefectBot) Action.D)
                  (.const Action.C) (.const Action.D))
          else eval (fuel + 1) (PrudentBot k) opponent (.const Action.D)) = some .D
  rw [show (Formula.plays Prog.opp Prog.self Action.C).subst (PrudentBot k) opponent
        = Formula.plays opponent (PrudentBot k) Action.C from rfl, hf]
  rfl

-- DefectBot --

/-- The outer cooperation search "DefectBot cooperates with PrudentBot" is false:
    DefectBot never plays C. -/
theorem proofSearch_false_DefectBot_vs_PrudentBot (k : Nat) :
    proofSearch k (Formula.plays DefectBot (PrudentBot k) Action.C) = false := by
  cases h : proofSearch k (Formula.plays DefectBot (PrudentBot k) Action.C) with
  | true  => exact absurd (proofSearch_sound _ _ h) (interp_DefectBot_plays_C_false _)
  | false => rfl

/-- PrudentBot defects against DefectBot (outer cooperation search fails). -/
theorem PrudentBot_plays_D_against_DefectBot (k fuel : Nat) :
    play (fuel + 2) (PrudentBot k) DefectBot = some .D :=
  PrudentBot_plays_D_of_search_false k fuel DefectBot
    (proofSearch_false_DefectBot_vs_PrudentBot k)

/-- PrudentBot vs DefectBot: mutual defection, (D, D). -/
theorem PrudentBot_vs_DefectBot (k fuel : Nat) :
    outcome (fuel + 2) (PrudentBot k) DefectBot = some (.D, .D) := by
  have hA : play (fuel + 2) (PrudentBot k) DefectBot = some .D :=
    PrudentBot_plays_D_against_DefectBot k fuel
  have hB : play (fuel + 2) DefectBot (PrudentBot k) = some .D := by
    simpa [Nat.add_comm] using play_DefectBot (fuel + 1) (PrudentBot k)
  exact outcome_of_plays _ _ _ _ _ hA hB

-- CooperateBot --

/-- The inner prudence search "CooperateBot defects vs DefectBot" is false:
    CooperateBot cooperates against everything, so it never plays D. -/
theorem proofSearch_false_CooperateBot_prudence (k : Nat) :
    proofSearch k (Formula.plays CooperateBot (.bot DefectBot) Action.D) = false := by
  cases h : proofSearch k (Formula.plays CooperateBot (.bot DefectBot) Action.D) with
  | true  =>
    exfalso
    obtain ⟨n, hn⟩ := proofSearch_sound _ _ h
    cases n with
    | zero   => simp [play, eval] at hn
    | succ m =>
        rw [show play (m+1) CooperateBot (.bot DefectBot) = some .C from by
              simpa [Nat.add_comm] using play_CooperateBot m (.bot DefectBot)] at hn
        cases hn
  | false => rfl

/-- PrudentBot defects against CooperateBot. The outer cooperation search may
    succeed (CooperateBot does cooperate), but then the inner *prudence* search
    fails (CooperateBot is a sucker — it cooperates vs DefectBot), so PrudentBot
    defects via the inner else-branch. Either way: defect. -/
theorem PrudentBot_plays_D_against_CooperateBot (k fuel : Nat) :
    play (fuel + 3) (PrudentBot k) CooperateBot = some .D := by
  show eval (fuel + 3) (PrudentBot k) CooperateBot (PrudentBot k) = some .D
  rw [PrudentBot_eq]
  show (if proofSearch k ((Formula.plays .opp .self Action.C).subst (PrudentBot k) CooperateBot)
          then eval (fuel + 2) (PrudentBot k) CooperateBot
                (.search k (Formula.plays .opp (.bot DefectBot) Action.D)
                  (.const Action.C) (.const Action.D))
          else eval (fuel + 2) (PrudentBot k) CooperateBot (.const Action.D)) = some .D
  have hinner := proofSearch_false_CooperateBot_prudence k
  by_cases hc : proofSearch k ((Formula.plays Prog.opp Prog.self Action.C).subst (PrudentBot k) CooperateBot) = true
  · rw [if_pos hc]
    show (if proofSearch k ((Formula.plays .opp (.bot DefectBot) Action.D).subst (PrudentBot k) CooperateBot)
            then eval (fuel + 1) (PrudentBot k) CooperateBot (.const Action.C)
            else eval (fuel + 1) (PrudentBot k) CooperateBot (.const Action.D)) = some .D
    rw [show (Formula.plays Prog.opp (.bot DefectBot) Action.D).subst (PrudentBot k) CooperateBot
          = Formula.plays CooperateBot (.bot DefectBot) Action.D from rfl, hinner]
    rfl
  · rw [if_neg hc]; rfl

/-- PrudentBot vs CooperateBot: PrudentBot exploits the sucker, (D, C). -/
theorem PrudentBot_vs_CooperateBot (k fuel : Nat) :
    outcome (fuel + 3) (PrudentBot k) CooperateBot = some (.D, .C) := by
  have hA : play (fuel + 3) (PrudentBot k) CooperateBot = some .D :=
    PrudentBot_plays_D_against_CooperateBot k fuel
  have hB : play (fuel + 3) CooperateBot (PrudentBot k) = some .C := by
    simpa [Nat.add_comm] using play_CooperateBot (fuel + 2) (PrudentBot k)
  exact outcome_of_plays _ _ _ _ _ hA hB

-- Probe lemmas: how PrudentBot responds to the canonical probe bots that
-- DBot/OBot/TFT simulate it against.

/-- PrudentBot defects against `.bot DefectBot`: the outer cooperation search
    "DefectBot cooperates with PrudentBot" is false. -/
theorem PrudentBot_plays_D_vs_bot_DB (k fuel : Nat) :
    play (fuel + 2) (PrudentBot k) (.bot DefectBot) = some .D := by
  apply PrudentBot_plays_D_of_search_false
  cases h : proofSearch k (Formula.plays (.bot DefectBot) (PrudentBot k) Action.C) with
  | true  => exact absurd (proofSearch_sound _ _ h) (interp_bot_DefectBot_plays_C_false _)
  | false => rfl

/-- PrudentBot defects against `.bot CooperateBot`: outer cooperation search may
    succeed, but the inner prudence search ("CooperateBot defects vs DefectBot")
    fails, so PrudentBot defects. -/
theorem PrudentBot_plays_D_vs_bot_CB (k fuel : Nat) :
    play (fuel + 3) (PrudentBot k) (.bot CooperateBot) = some .D := by
  show eval (fuel + 3) (PrudentBot k) (.bot CooperateBot) (PrudentBot k) = some .D
  rw [PrudentBot_eq]
  show (if proofSearch k ((Formula.plays .opp .self Action.C).subst (PrudentBot k) (.bot CooperateBot))
          then eval (fuel + 2) (PrudentBot k) (.bot CooperateBot)
                (.search k (Formula.plays .opp (.bot DefectBot) Action.D)
                  (.const Action.C) (.const Action.D))
          else eval (fuel + 2) (PrudentBot k) (.bot CooperateBot) (.const Action.D)) = some .D
  have hinner : proofSearch k (Formula.plays (.bot CooperateBot) (.bot DefectBot) Action.D) = false := by
    cases h : proofSearch k (Formula.plays (.bot CooperateBot) (.bot DefectBot) Action.D) with
    | true  =>
      exfalso
      obtain ⟨n, hn⟩ := proofSearch_sound _ _ h
      cases n with
      | zero   => simp [play, eval] at hn
      | succ m =>
          cases m with
          | zero => simp [play, eval] at hn
          | succ j =>
              rw [show play (j+2) (.bot CooperateBot) (.bot DefectBot) = some .C from by
                    simp [play, eval, CooperateBot]] at hn
              cases hn
    | false => rfl
  by_cases hc : proofSearch k ((Formula.plays Prog.opp Prog.self Action.C).subst (PrudentBot k) (.bot CooperateBot)) = true
  · rw [if_pos hc]
    show (if proofSearch k ((Formula.plays .opp (.bot DefectBot) Action.D).subst (PrudentBot k) (.bot CooperateBot))
            then eval (fuel + 1) (PrudentBot k) (.bot CooperateBot) (.const Action.C)
            else eval (fuel + 1) (PrudentBot k) (.bot CooperateBot) (.const Action.D)) = some .D
    rw [show (Formula.plays Prog.opp (.bot DefectBot) Action.D).subst (PrudentBot k) (.bot CooperateBot)
          = Formula.plays (.bot CooperateBot) (.bot DefectBot) Action.D from rfl, hinner]
    rfl
  · rw [if_neg hc]; rfl

-- DBot --

/-- DBot cooperates with PrudentBot: DBot probes PrudentBot against `.bot DefectBot`,
    sees it defect (guard value D ≠ test C), and takes its else-branch (cooperate). -/
theorem DBot_plays_C_vs_PrudentBot (k fuel : Nat) :
    play (fuel + 4) DBot (PrudentBot k) = some .C := by
  have hProbe : play (fuel + 2) (PrudentBot k) (.bot DefectBot) = some .D :=
    PrudentBot_plays_D_vs_bot_DB k fuel
  have hGuard : eval (fuel + 3) DBot (PrudentBot k) (.sim .opp (.bot DefectBot)) = some .D :=
    eval_sim_opp_bot_of_play (fuel + 2) DBot (PrudentBot k) DefectBot Action.D hProbe
  have hPlay := eval_ite_from_guard
    (fuel + 3) DBot (PrudentBot k) (.sim .opp (.bot DefectBot))
    (.const Action.D) (.const Action.C)
    Action.C Action.D
    hGuard
  show eval (fuel + 4) DBot (PrudentBot k) DBot = some .C
  rw [show DBot = .ite (.sim .opp (.bot DefectBot)) Action.C (.const Action.D) (.const Action.C) from rfl] at *
  rw [hPlay]; rfl

/-- The inner prudence search "DBot defects vs DefectBot" is false: DBot probes
    DefectBot (which defects), so DBot takes its else-branch and *cooperates*
    against DefectBot. Hence it is a sucker and the prudence atom is false. -/
theorem proofSearch_false_DBot_prudence (k : Nat) :
    proofSearch k (Formula.plays DBot (.bot DefectBot) Action.D) = false := by
  cases h : proofSearch k (Formula.plays DBot (.bot DefectBot) Action.D) with
  | true  =>
    exfalso
    obtain ⟨n, hn⟩ := proofSearch_sound _ _ h
    -- DBot cooperates vs `.bot DefectBot`, so it never plays D there.
    have hC : ∀ m, play (m + 4) DBot (.bot DefectBot) = some .C := by
      intro m
      have hProbe : play (m + 2) (.bot DefectBot) (.bot DefectBot) = some .D := by
        simpa [Nat.add_comm] using play_bot_DefectBot m (.bot DefectBot)
      have hGuard : eval (m + 3) DBot (.bot DefectBot) (.sim .opp (.bot DefectBot)) = some .D :=
        eval_sim_opp_bot_of_play (m + 2) DBot (.bot DefectBot) DefectBot Action.D hProbe
      have hPlay := eval_ite_from_guard
        (m + 3) DBot (.bot DefectBot) (.sim .opp (.bot DefectBot))
        (.const Action.D) (.const Action.C) Action.C Action.D hGuard
      show eval (m + 4) DBot (.bot DefectBot) DBot = some .C
      rw [show DBot = .ite (.sim .opp (.bot DefectBot)) Action.C (.const Action.D) (.const Action.C) from rfl] at *
      rw [hPlay]; rfl
    have hmono : play (n + 4) DBot (.bot DefectBot) = some .D := by
      unfold play at hn ⊢; exact eval_mono_le hn (n + 4) (by omega)
    rw [hC n] at hmono; cases hmono
  | false => rfl

/-- PrudentBot defects against DBot. Like CooperateBot, DBot cooperates with
    PrudentBot, but DBot is a sucker against DefectBot, so the inner prudence
    search fails and PrudentBot defects. -/
theorem PrudentBot_plays_D_against_DBot (k fuel : Nat) :
    play (fuel + 3) (PrudentBot k) DBot = some .D := by
  show eval (fuel + 3) (PrudentBot k) DBot (PrudentBot k) = some .D
  rw [PrudentBot_eq]
  show (if proofSearch k ((Formula.plays .opp .self Action.C).subst (PrudentBot k) DBot)
          then eval (fuel + 2) (PrudentBot k) DBot
                (.search k (Formula.plays .opp (.bot DefectBot) Action.D)
                  (.const Action.C) (.const Action.D))
          else eval (fuel + 2) (PrudentBot k) DBot (.const Action.D)) = some .D
  have hinner := proofSearch_false_DBot_prudence k
  by_cases hc : proofSearch k ((Formula.plays Prog.opp Prog.self Action.C).subst (PrudentBot k) DBot) = true
  · rw [if_pos hc]
    show (if proofSearch k ((Formula.plays .opp (.bot DefectBot) Action.D).subst (PrudentBot k) DBot)
            then eval (fuel + 1) (PrudentBot k) DBot (.const Action.C)
            else eval (fuel + 1) (PrudentBot k) DBot (.const Action.D)) = some .D
    rw [show (Formula.plays Prog.opp (.bot DefectBot) Action.D).subst (PrudentBot k) DBot
          = Formula.plays DBot (.bot DefectBot) Action.D from rfl, hinner]
    rfl
  · rw [if_neg hc]; rfl

/-- PrudentBot vs DBot: PrudentBot exploits, (D, C). -/
theorem outcome_PrudentBot_vs_DBot :
    ∃ k₂, ∀ k, k₂ < k →
      ∃ fuel, outcome fuel (PrudentBot k) DBot = some (.D, .C) := by
  refine ⟨0, fun k _ => ⟨7, ?_⟩⟩
  have hA : play 7 (PrudentBot k) DBot = some .D := by
    simpa using PrudentBot_plays_D_against_DBot k 4
  have hB : play 7 DBot (PrudentBot k) = some .C := by
    simpa using DBot_plays_C_vs_PrudentBot k 3
  exact outcome_of_plays _ _ _ _ _ hA hB

-- TitForTatBot --

/-- TFT defects against PrudentBot: TFT probes PrudentBot against `.bot CooperateBot`,
    sees it defect (guard D ≠ test C), takes its else-branch and defects. -/
theorem TFT_plays_D_vs_PrudentBot (k fuel : Nat) :
    play (fuel + 5) TitForTatBot (PrudentBot k) = some .D := by
  have hProbe : play (fuel + 3) (PrudentBot k) (.bot CooperateBot) = some .D :=
    PrudentBot_plays_D_vs_bot_CB k fuel
  have hGuard : eval (fuel + 4) TitForTatBot (PrudentBot k)
      (.sim .opp (.bot CooperateBot)) = some .D :=
    eval_sim_opp_bot_of_play (fuel + 3) TitForTatBot (PrudentBot k) CooperateBot Action.D hProbe
  have hPlay := eval_ite_from_guard
    (fuel + 4) TitForTatBot (PrudentBot k) (.sim .opp (.bot CooperateBot))
    (.const Action.C) (.const Action.D) Action.C Action.D hGuard
  show eval (fuel + 5) TitForTatBot (PrudentBot k) TitForTatBot = some .D
  rw [show TitForTatBot = .ite (.sim .opp (.bot CooperateBot)) Action.C
        (.const Action.C) (.const Action.D) from rfl] at *
  rw [hPlay]; rfl

theorem interp_TFT_plays_C_vs_PrudentBot_false (k : Nat) :
    ¬ (Formula.plays TitForTatBot (PrudentBot k) .C).interp := by
  rintro ⟨n, hn⟩
  have hD : play (n + 6) TitForTatBot (PrudentBot k) = some .D := by
    simpa [Nat.add_assoc] using TFT_plays_D_vs_PrudentBot k (n + 1)
  have hC : play (n + 6) TitForTatBot (PrudentBot k) = some .C := by
    unfold play at hn ⊢; exact eval_mono_le hn (n + 6) (by omega)
  rw [hC] at hD; cases hD

theorem proofSearch_false_TFT_vs_PrudentBot (k : Nat) :
    proofSearch k (Formula.plays TitForTatBot (PrudentBot k) Action.C) = false := by
  cases h : proofSearch k (Formula.plays TitForTatBot (PrudentBot k) Action.C) with
  | true  => exact absurd (proofSearch_sound _ _ h) (interp_TFT_plays_C_vs_PrudentBot_false k)
  | false => rfl

theorem PrudentBot_plays_D_against_TFT (k fuel : Nat) :
    play (fuel + 2) (PrudentBot k) TitForTatBot = some .D :=
  PrudentBot_plays_D_of_search_false k fuel TitForTatBot
    (proofSearch_false_TFT_vs_PrudentBot k)

/-- PrudentBot vs TitForTatBot: mutual defection, (D, D). -/
theorem outcome_PrudentBot_vs_TitForTatBot :
    ∃ k₂, ∀ k, k₂ < k →
      ∃ fuel, outcome fuel (PrudentBot k) TitForTatBot = some (.D, .D) := by
  refine ⟨0, fun k _ => ⟨6, ?_⟩⟩
  have hA : play 6 (PrudentBot k) TitForTatBot = some .D := by
    simpa using PrudentBot_plays_D_against_TFT k 4
  have hB : play 6 TitForTatBot (PrudentBot k) = some .D := by
    simpa using TFT_plays_D_vs_PrudentBot k 1
  exact outcome_of_plays _ _ _ _ _ hA hB

-- OBot --

/-- OBot defects against PrudentBot: OBot's first probe is the opponent against
    `.bot CooperateBot`; PrudentBot defects there (D ≠ test C), so OBot takes its
    outermost else-branch and defects. -/
theorem OBot_plays_D_vs_PrudentBot (k fuel : Nat) :
    play (fuel + 5) OBot (PrudentBot k) = some .D := by
  have hProbe : play (fuel + 3) (PrudentBot k) (.bot CooperateBot) = some .D :=
    PrudentBot_plays_D_vs_bot_CB k fuel
  have hGuard : eval (fuel + 4) OBot (PrudentBot k)
      (.sim .opp (.bot CooperateBot)) = some .D :=
    eval_sim_opp_bot_of_play (fuel + 3) OBot (PrudentBot k) CooperateBot Action.D hProbe
  have hPlay := eval_ite_from_guard
    (fuel + 4) OBot (PrudentBot k) (.sim .opp (.bot CooperateBot))
    (.ite (.sim .opp (.bot DefectBot)) Action.C (.const Action.C) (.const Action.D))
    (.const Action.D) Action.C Action.D hGuard
  show eval (fuel + 5) OBot (PrudentBot k) OBot = some .D
  rw [show OBot = .ite (.sim .opp (.bot CooperateBot)) Action.C
        (.ite (.sim .opp (.bot DefectBot)) Action.C (.const Action.C) (.const Action.D))
        (.const Action.D) from rfl] at *
  rw [hPlay]; rfl

theorem interp_OBot_plays_C_vs_PrudentBot_false (k : Nat) :
    ¬ (Formula.plays OBot (PrudentBot k) .C).interp := by
  rintro ⟨n, hn⟩
  have hD : play (n + 6) OBot (PrudentBot k) = some .D := by
    simpa [Nat.add_assoc] using OBot_plays_D_vs_PrudentBot k (n + 1)
  have hC : play (n + 6) OBot (PrudentBot k) = some .C := by
    unfold play at hn ⊢; exact eval_mono_le hn (n + 6) (by omega)
  rw [hC] at hD; cases hD

theorem proofSearch_false_OBot_vs_PrudentBot (k : Nat) :
    proofSearch k (Formula.plays OBot (PrudentBot k) Action.C) = false := by
  cases h : proofSearch k (Formula.plays OBot (PrudentBot k) Action.C) with
  | true  => exact absurd (proofSearch_sound _ _ h) (interp_OBot_plays_C_vs_PrudentBot_false k)
  | false => rfl

theorem PrudentBot_plays_D_against_OBot (k fuel : Nat) :
    play (fuel + 2) (PrudentBot k) OBot = some .D :=
  PrudentBot_plays_D_of_search_false k fuel OBot
    (proofSearch_false_OBot_vs_PrudentBot k)

/-- PrudentBot vs OBot: mutual defection, (D, D). -/
theorem outcome_PrudentBot_vs_OBot :
    ∃ k₂, ∀ k, k₂ < k →
      ∃ fuel, outcome fuel (PrudentBot k) OBot = some (.D, .D) := by
  refine ⟨0, fun k _ => ⟨6, ?_⟩⟩
  have hA : play 6 (PrudentBot k) OBot = some .D := by
    simpa using PrudentBot_plays_D_against_OBot k 4
  have hB : play 6 OBot (PrudentBot k) = some .D := by
    simpa using OBot_plays_D_vs_PrudentBot k 1
  exact outcome_of_plays _ _ _ _ _ hA hB


-- MirrorBot --

/-- The prudence atom is a true Σ₁ fact: MirrorBot mirrors `.bot DefectBot`'s
    defection, so it plays `D` against it. -/
theorem MirrorBot_plays_D_vs_bot_DefectBot (fuel : Nat) :
    play (fuel + 3) MirrorBot (.bot DefectBot) = some .D := by
  show eval (fuel + 3) MirrorBot (.bot DefectBot) MirrorBot = some .D
  simp [eval, Prog.subst, MirrorBot, DefectBot]

/-- Hence the prudence atom `MirrorBot plays D vs DefectBot` is provable (for `k`
    large enough to fit the certificate). -/
theorem prudence_provable :
    Provable 27 (Formula.plays MirrorBot (.bot DefectBot) Action.D) := by
  have hPlay : play 3 MirrorBot (.bot DefectBot) = some .D := by
    simpa using MirrorBot_plays_D_vs_bot_DefectBot 0
  exact Provable.atom (atom_monotone (3 ^ 3) 27 _ (by norm_num)
    (atom_complete_searchfree MirrorBot (.bot DefectBot) Action.D 3 rfl rfl hPlay))

/-- **Löb premise for PrudentBot vs MirrorBot**, built with the new
    `searchThenSearch_t` rule. Two legs, chained by `implTrans`:
    * `searchThenSearch_t` reads PrudentBot's stacked `.search`/`.search` body and,
      *given the provable prudence atom*, yields `□_k φ → (PrudentBot plays C vs
      MirrorBot)` — the prudence box already discharged, leaving a single box;
    * `simStep` reads MirrorBot's `.sim .opp .self` swap: `(PrudentBot plays C vs
      MirrorBot) → (MirrorBot plays C vs PrudentBot)`.
    The result is the closed `□_k φ → φ` that `PBLT` consumes. -/
theorem prudent_mirror_loeb_premise (k : Nat) (hk : 27 ≤ k) :
    Provable (50 * Nat.log2 k + 500)
      (.impl (.box k (Formula.plays MirrorBot (PrudentBot k) Action.C))
             (Formula.plays MirrorBot (PrudentBot k) Action.C)) := by
  -- TRANSCRIPT-TIGHT: the whole premise costs O(log k) — searchThenSearch pays the
  -- prudence certificate (search-free, ≤ 27 chars, whence `27 ≤ k` so the inner
  -- search at budget `k` finds it) + its conclusion; the `.sim` leg is one leaf;
  -- `implTrans` pays both legs + the conclusion. No `K₀` eventuality.
  -- Leg 1: `□_k φ → (PrudentBot plays C vs Mirror)` via `searchThenSearch_t`.
  have leg1 : Provable (20 * Nat.log2 k + 200)
      (.impl (.box k (Formula.plays MirrorBot (PrudentBot k) Action.C))
             (Formula.plays (PrudentBot k) MirrorBot Action.C)) := by
    refine Provable.searchThenSearch_t k k 27
      (Formula.plays .opp .self Action.C)
      (Formula.plays .opp (.bot DefectBot) Action.D)
      Action.C Action.D (.const Action.D) (PrudentBot k) MirrorBot rfl
      prudence_provable (by omega) ?_
    simp only [Formula.subst, Prog.subst, Formula.size, Prog.size, PrudentBot, MirrorBot,
      DefectBot, c_guard]
    omega
  -- Leg 2: MirrorBot's `.sim` swap, as a Derivation → Provable (single leaf).
  have leg2 : Provable (20 * Nat.log2 k + 200)
      (.impl (Formula.plays (PrudentBot k) MirrorBot Action.C)
             (Formula.plays MirrorBot (PrudentBot k) Action.C)) := by
    refine Provable.struct ⟨Derivation.simStep MirrorBot .opp .self (PrudentBot k) Action.C rfl, ?_⟩
    simp only [Derivation.size, Formula.size, Prog.size, PrudentBot, MirrorBot, DefectBot]
    omega
  -- Chain leg1 (`□φ → A`) then leg2 (`A → φ`) into `□_k φ → φ` via `implTrans`.
  refine Provable.implTrans _ _ _ (20 * Nat.log2 k + 200) (20 * Nat.log2 k + 200) leg1 leg2 ?_
  simp only [Formula.size, Prog.size, PrudentBot, MirrorBot, DefectBot]
  omega

/-- Once `proofSearch k = true`, PrudentBot's stacked searches both fire (the inner
    prudence guard is the provable Σ₁ atom), so it cooperates with MirrorBot. -/
theorem PrudentBot_plays_C_against_MirrorBot (k fuel : Nat)
    (hCoop : proofSearch k (Formula.plays MirrorBot (PrudentBot k) Action.C) = true)
    (hPrud : proofSearch k (Formula.plays MirrorBot (.bot DefectBot) Action.D) = true) :
    play (fuel + 3) (PrudentBot k) MirrorBot = some .C := by
  show eval (fuel + 3) (PrudentBot k) MirrorBot (PrudentBot k) = some .C
  unfold PrudentBot at hCoop ⊢
  simp [eval, Prog.subst, Formula.subst, hCoop, hPrud]

/-- MirrorBot mirrors PrudentBot's cooperate via the `.sim .opp .self` swap. -/
theorem MirrorBot_plays_C_against_PrudentBot (k fuel : Nat)
    (hCoop : proofSearch k (Formula.plays MirrorBot (PrudentBot k) Action.C) = true)
    (hPrud : proofSearch k (Formula.plays MirrorBot (.bot DefectBot) Action.D) = true) :
    play (fuel + 4) MirrorBot (PrudentBot k) = some .C := by
  have hPrudent : play (fuel + 3) (PrudentBot k) MirrorBot = some .C :=
    PrudentBot_plays_C_against_MirrorBot k fuel hCoop hPrud
  simpa [play, eval, Prog.subst, MirrorBot] using hPrudent

/-- When PrudentBot's cooperation search fails, it lands in its root else-branch
    and defects against MirrorBot. -/
theorem PrudentBot_plays_D_against_MirrorBot (k fuel : Nat)
    (hf : proofSearch k (Formula.plays MirrorBot (PrudentBot k) Action.C) = false) :
    play (fuel + 2) (PrudentBot k) MirrorBot = some .D := by
  show eval (fuel + 2) (PrudentBot k) MirrorBot (PrudentBot k) = some .D
  unfold PrudentBot at hf ⊢
  simp [eval, Prog.subst, Formula.subst, hf]

/-- Inversion: a cooperation `play` on MirrorBot's leg forces PrudentBot's outer
    search to have fired at budget `k`. (If it were false, MirrorBot would mirror
    PrudentBot's defection and play `D`, contradicting the `C` witness.) -/
theorem proofSearch_k_of_play_MirrorBot_prudent
    (k n : Nat) (h : play n MirrorBot (PrudentBot k) = some .C) :
    proofSearch k (Formula.plays MirrorBot (PrudentBot k) Action.C) = true := by
  cases hps : proofSearch k (Formula.plays MirrorBot (PrudentBot k) Action.C) with
  | true  => rfl
  | false =>
    exfalso
    -- MirrorBot mirrors PrudentBot's defection: it plays D at high fuel.
    have hPrudD : ∀ f, play (f + 2) (PrudentBot k) MirrorBot = some .D :=
      fun f => PrudentBot_plays_D_against_MirrorBot k f hps
    have hMirD : play (n + 3) MirrorBot (PrudentBot k) = some .D := by
      have hP : play (n + 2) (PrudentBot k) MirrorBot = some .D := hPrudD n
      simpa [play, eval, Prog.subst, MirrorBot] using hP
    have hMonoC : play (n + 3) MirrorBot (PrudentBot k) = some .C := by
      unfold play at h ⊢
      exact eval_mono_le h (n + 3) (by omega)
    rw [hMonoC] at hMirD
    cases hMirD

/-- **PrudentBot vs MirrorBot → (C, C)** for all large enough `k`. Application of
    `PBLT` to the Löb premise: the cooperation atom `φ = MirrorBot plays C vs
    PrudentBot` is provable, so PrudentBot's outer search fires; the prudence atom
    is independently provable, so the inner search fires too — both bots cooperate.

    Contrast the *old* PrudentBot (prudence `.ite` over the search), whose Löb
    premise was unprovable: the fix was the `searchThenSearch_t` transparency rule,
    which lets S read PrudentBot's stacked-`.search` body. -/
theorem outcome_PrudentBot_vs_MirrorBot :
    ∃ k₂, ∀ k, k₂ < k →
      ∃ fuel, outcome fuel (PrudentBot k) MirrorBot = some (.C, .C) := by
  let φ : Nat → Formula := fun k => Formula.plays MirrorBot (PrudentBot k) Action.C
  have hLoeb : ∀ k, k > 27 →
      Provable (50 * Nat.log2 k + 500) (.impl (.box k (φ k)) (φ k)) := by
    intro k hk
    exact prudent_mirror_loeb_premise k (by omega)
  have hφsz : ∀ k, (φ k).size ≤ 100 * Nat.log2 k + 1000 := by
    intro k
    show (Formula.plays MirrorBot (PrudentBot k) Action.C).size ≤ _
    simp only [Formula.size, Prog.size, PrudentBot, MirrorBot, DefectBot]
    omega
  have hpm : ∀ k, 50 * Nat.log2 k + 500 ≤ 100 * Nat.log2 k + 1000 := fun k => by omega
  obtain ⟨k₂, hk₂⟩ := pblt_engine_id φ (fun k => 50 * Nat.log2 k + 500) 27 hφsz hpm hLoeb
  refine ⟨max k₂ 27, fun k hk => ?_⟩
  have hk2 : k > k₂ := lt_of_le_of_lt (le_max_left _ _) hk
  have hkP : (27 : Nat) ≤ k :=
    le_of_lt (lt_of_le_of_lt (le_max_right _ _) hk)
  -- PBLT gives `Provable m (φ k)` at *some* budget `m`; its truth yields a play
  -- witness, which the inversion lemma lifts to `proofSearch k = true` at budget `k`.
  obtain ⟨m, hm⟩ := hk₂ k hk2
  obtain ⟨n, hMir⟩ := Provable_sound m (φ k) hm
  have hCoopPS : proofSearch k (Formula.plays MirrorBot (PrudentBot k) Action.C) = true :=
    proofSearch_k_of_play_MirrorBot_prudent k n hMir
  have hPrudPS : proofSearch k (Formula.plays MirrorBot (.bot DefectBot) Action.D) = true :=
    (proofSearch_spec _ _).2 (Provable_mono prudence_provable hkP)
  refine ⟨4, ?_⟩
  have hA : play 4 (PrudentBot k) MirrorBot = some .C := by
    simpa using PrudentBot_plays_C_against_MirrorBot k 1 hCoopPS hPrudPS
  have hB : play 4 MirrorBot (PrudentBot k) = some .C := by
    simpa using MirrorBot_plays_C_against_PrudentBot k 0 hCoopPS hPrudPS
  exact outcome_of_plays _ _ _ _ _ hA hB


/-- Prudence atom for `.bot MirrorBot`: it mirrors `.bot DefectBot`'s defection. -/
theorem bot_MirrorBot_plays_D_vs_bot_DefectBot (fuel : Nat) :
    play (fuel + 4) (.bot MirrorBot) (.bot DefectBot) = some .D := by
  show eval (fuel + 4) (.bot MirrorBot) (.bot DefectBot) (.bot MirrorBot) = some .D
  simp [eval, Prog.subst, MirrorBot, DefectBot]

theorem prudence_provable_bot :
    Provable 81 (Formula.plays (.bot MirrorBot) (.bot DefectBot) Action.D) := by
  have hPlay : play 4 (.bot MirrorBot) (.bot DefectBot) = some .D := by
    simpa using bot_MirrorBot_plays_D_vs_bot_DefectBot 0
  exact Provable.atom (atom_monotone (3 ^ 4) 81 _ (by norm_num)
    (atom_complete_searchfree (.bot MirrorBot) (.bot DefectBot) Action.D 4 rfl rfl hPlay))

/-- **Löb premise for PrudentBot vs `.bot MirrorBot`.** Identical assembly to the
    bare-MirrorBot premise, but the mirror leg uses `botSimStep` (reading
    `.bot MirrorBot = .bot (.sim .opp .self)`) instead of `simStep`. -/
theorem prudent_bot_mirror_loeb_premise (k : Nat) (hk : 81 ≤ k) :
    Provable (50 * Nat.log2 k + 500)
      (.impl (.box k (Formula.plays (.bot MirrorBot) (PrudentBot k) Action.C))
             (Formula.plays (.bot MirrorBot) (PrudentBot k) Action.C)) := by
  -- TRANSCRIPT-TIGHT (see `prudent_mirror_loeb_premise`); the search-free prudence
  -- certificate costs ≤ 81 chars, whence `81 ≤ k`.
  have leg1 : Provable (20 * Nat.log2 k + 200)
      (.impl (.box k (Formula.plays (.bot MirrorBot) (PrudentBot k) Action.C))
             (Formula.plays (PrudentBot k) (.bot MirrorBot) Action.C)) := by
    refine Provable.searchThenSearch_t k k 81
      (Formula.plays .opp .self Action.C)
      (Formula.plays .opp (.bot DefectBot) Action.D)
      Action.C Action.D (.const Action.D) (PrudentBot k) (.bot MirrorBot) rfl
      prudence_provable_bot (by omega) ?_
    simp only [Formula.subst, Prog.subst, Formula.size, Prog.size, PrudentBot, MirrorBot,
      DefectBot, c_guard]
    omega
  have leg2 : Provable (20 * Nat.log2 k + 200)
      (.impl (Formula.plays (PrudentBot k) (.bot MirrorBot) Action.C)
             (Formula.plays (.bot MirrorBot) (PrudentBot k) Action.C)) := by
    refine Provable.struct
      ⟨Derivation.botSimStep (.bot MirrorBot) .opp .self (PrudentBot k) Action.C rfl, ?_⟩
    simp only [Derivation.size, Formula.size, Prog.size, PrudentBot, MirrorBot, DefectBot]
    omega
  refine Provable.implTrans _ _ _ (20 * Nat.log2 k + 200) (20 * Nat.log2 k + 200) leg1 leg2 ?_
  simp only [Formula.size, Prog.size, PrudentBot, MirrorBot, DefectBot]
  omega

/-- Once both searches fire, PrudentBot cooperates with `.bot MirrorBot`. -/
theorem PrudentBot_plays_C_against_bot_MirrorBot (k fuel : Nat)
    (hCoop : proofSearch k (Formula.plays (.bot MirrorBot) (PrudentBot k) Action.C) = true)
    (hPrud : proofSearch k (Formula.plays (.bot MirrorBot) (.bot DefectBot) Action.D) = true) :
    play (fuel + 3) (PrudentBot k) (.bot MirrorBot) = some .C := by
  show eval (fuel + 3) (PrudentBot k) (.bot MirrorBot) (PrudentBot k) = some .C
  unfold PrudentBot at hCoop ⊢
  simp [eval, Prog.subst, Formula.subst, hCoop, hPrud]

/-- When PrudentBot's cooperation search fails, it defects against `.bot MirrorBot`. -/
theorem PrudentBot_plays_D_against_bot_MirrorBot (k fuel : Nat)
    (hf : proofSearch k (Formula.plays (.bot MirrorBot) (PrudentBot k) Action.C) = false) :
    play (fuel + 2) (PrudentBot k) (.bot MirrorBot) = some .D := by
  show eval (fuel + 2) (PrudentBot k) (.bot MirrorBot) (PrudentBot k) = some .D
  unfold PrudentBot at hf ⊢
  simp [eval, Prog.subst, Formula.subst, hf]

/-- Inversion for the `.bot MirrorBot` leg. -/
theorem proofSearch_k_of_play_bot_MirrorBot_prudent
    (k n : Nat) (h : play n (.bot MirrorBot) (PrudentBot k) = some .C) :
    proofSearch k (Formula.plays (.bot MirrorBot) (PrudentBot k) Action.C) = true := by
  cases hps : proofSearch k (Formula.plays (.bot MirrorBot) (PrudentBot k) Action.C) with
  | true  => rfl
  | false =>
    exfalso
    have hPrudD : ∀ f, play (f + 2) (PrudentBot k) (.bot MirrorBot) = some .D :=
      fun f => PrudentBot_plays_D_against_bot_MirrorBot k f hps
    have hMirD : play (n + 4) (.bot MirrorBot) (PrudentBot k) = some .D := by
      have hP : play (n + 2) (PrudentBot k) (.bot MirrorBot) = some .D := hPrudD n
      show eval (n + 4) (.bot MirrorBot) (PrudentBot k) (.bot MirrorBot) = some .D
      simpa [play, eval, Prog.subst, MirrorBot] using hP
    have hMonoC : play (n + 4) (.bot MirrorBot) (PrudentBot k) = some .C := by
      unfold play at h ⊢
      exact eval_mono_le h (n + 4) (by omega)
    rw [hMonoC] at hMirD
    cases hMirD

/-- **PrudentBot cooperates with `.bot MirrorBot`**, for all large enough `k`.
    Discharges the former `PrudentBot_plays_C_vs_bot_MirrorBot` axiom. -/
theorem PrudentBot_plays_C_vs_bot_MirrorBot :
    ∃ k₂, ∀ k, k₂ < k →
      ∃ fuel, play fuel (PrudentBot k) (.bot MirrorBot) = some .C := by
  let φ : Nat → Formula := fun k => Formula.plays (.bot MirrorBot) (PrudentBot k) Action.C
  have hLoeb : ∀ k, k > 81 →
      Provable (50 * Nat.log2 k + 500) (.impl (.box k (φ k)) (φ k)) :=
    fun k hk => prudent_bot_mirror_loeb_premise k (by omega)
  have hφsz : ∀ k, (φ k).size ≤ 100 * Nat.log2 k + 1000 := by
    intro k
    show (Formula.plays (.bot MirrorBot) (PrudentBot k) Action.C).size ≤ _
    simp only [Formula.size, Prog.size, PrudentBot, MirrorBot, DefectBot]
    omega
  have hpm : ∀ k, 50 * Nat.log2 k + 500 ≤ 100 * Nat.log2 k + 1000 := fun k => by omega
  obtain ⟨k₂, hk₂⟩ := pblt_engine_id φ (fun k => 50 * Nat.log2 k + 500) 81 hφsz hpm hLoeb
  refine ⟨max k₂ 81, fun k hk => ⟨3, ?_⟩⟩
  have hk2 : k > k₂ := lt_of_le_of_lt (le_max_left _ _) hk
  have hkP : (81 : Nat) ≤ k :=
    le_of_lt (lt_of_le_of_lt (le_max_right _ _) hk)
  obtain ⟨m, hm⟩ := hk₂ k hk2
  obtain ⟨n, hMir⟩ := Provable_sound m (φ k) hm
  have hCoopPS : proofSearch k (Formula.plays (.bot MirrorBot) (PrudentBot k) Action.C) = true :=
    proofSearch_k_of_play_bot_MirrorBot_prudent k n hMir
  have hPrudPS : proofSearch k (Formula.plays (.bot MirrorBot) (.bot DefectBot) Action.D) = true :=
    (proofSearch_spec _ _).2 (Provable_mono prudence_provable_bot hkP)
  simpa using PrudentBot_plays_C_against_bot_MirrorBot k 0 hCoopPS hPrudPS

-- EBot --

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
theorem prudent_botmirror_loeb_premise (k : Nat) (hk : 81 ≤ k) :
    Provable (50 * Nat.log2 k + 500)
      (.impl (.box k (.plays (.bot MirrorBot) (PrudentBot k) .C))
             (.plays (.bot MirrorBot) (PrudentBot k) .C)) :=
  prudent_bot_mirror_loeb_premise k hk

/-- PrudentBot's outer guard against `.bot MirrorBot` is provable for large k. -/
theorem prudent_botmirror_coop :
    ∃ k₂, ∀ k, k₂ < k →
      proofSearch k (.plays (.bot MirrorBot) (PrudentBot k) .C) = true := by
  let φ : Nat → Formula := fun k => .plays (.bot MirrorBot) (PrudentBot k) .C
  have hLoeb :
      ∀ k, k > 81 → Provable (50 * Nat.log2 k + 500) (.impl (.box k (φ k)) (φ k)) := by
    intro k hk
    exact prudent_botmirror_loeb_premise k (by omega)
  have hφsz : ∀ k, (φ k).size ≤ 100 * Nat.log2 k + 1000 := by
    intro k
    show (Formula.plays (.bot MirrorBot) (PrudentBot k) Action.C).size ≤ _
    simp only [Formula.size, Prog.size, PrudentBot, MirrorBot, DefectBot]
    omega
  have hpm : ∀ k, 50 * Nat.log2 k + 500 ≤ 100 * Nat.log2 k + 1000 := fun k => by omega
  obtain ⟨k₂, hk₂⟩ := pblt_engine_id φ (fun k => 50 * Nat.log2 k + 500) 81 hφsz hpm hLoeb
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

/-! ### `outcome_PrudentBot_vs_EBot` — RETIRED (2026-07-02, the false-guard repair).

An axiom artifact: EBot's play against `PrudentBot k` crosses PrudentBot's own FAILED outer
search (the probe vs `.bot DefectBot`), so its certificate pays the `search_f` floor —
cost > k for every k — and PrudentBot's outer guard can never see "EBot plays C vs me"
within its own budget. See `DECIDABILITY_ROADMAP.md` T3.2a. -/


-- CupodTrollBot --

theorem CupodTrollBot_never_D_vs_botDefect (k : Nat) :
    ¬ ∃ n, play n (CupodTrollBot k) (.bot DefectBot) = some .D := by
  rintro ⟨n, hn⟩
  have hC : play (n + 2) (CupodTrollBot k) (.bot DefectBot) = some .C :=
    CupodTrollBot_cooperates_against_bot k n DefectBot
  have hn' : eval n (CupodTrollBot k) (.bot DefectBot) (CupodTrollBot k) = some .D := hn
  have hD : play (n + 2) (CupodTrollBot k) (.bot DefectBot) = some .D :=
    eval_mono_le hn' (n + 2) (by omega)
  rw [hC] at hD
  simp at hD

theorem PrudentBot_defects_vs_CupodTrollBot (k fuel : Nat) :
    play (fuel + 3) (PrudentBot k) (CupodTrollBot k) = some .D := by
  have hφ2 : proofSearch k (.plays (CupodTrollBot k) (.bot DefectBot) .D) = false := by
    cases hps : proofSearch k (.plays (CupodTrollBot k) (.bot DefectBot) .D) with
    | true => exact absurd (proofSearch_sound _ _ hps) (CupodTrollBot_never_D_vs_botDefect k)
    | false => rfl
  show eval (fuel + 3) (PrudentBot k) (CupodTrollBot k) (PrudentBot k) = some .D
  unfold PrudentBot
  simp [eval, Prog.subst, Formula.subst, hφ2]

theorem outcome_PrudentBot_vs_CupodTrollBot :
    ∃ k₂, ∀ k, k₂ < k →
      ∃ fuel, outcome fuel (PrudentBot k) (CupodTrollBot k) = some (.D, .C) := by
  refine ⟨0, fun k _ => ⟨3, ?_⟩⟩
  have hA : play 3 (PrudentBot k) (CupodTrollBot k) = some .D :=
    PrudentBot_defects_vs_CupodTrollBot k 0
  have hB : play 3 (CupodTrollBot k) (PrudentBot k) = some .C :=
    CupodTrollBot_cooperates_if_opp_not_CupodBot k 1 (PrudentBot k)
      (by simp [PrudentBot, CupodBot])
  exact outcome_of_plays _ _ _ _ _ hA hB


-- Dupoc --

/-!
# PrudentBot vs DupocBot → (C, C)

This matchup is a **search-vs-search modal fixed point with no unboxed `.sim`
leg**: PrudentBot reads "DupocBot cooperates with me" (`searchThenSearch_t`,
boxed) and DupocBot reads "PrudentBot cooperates with me" (`searchBranch`, boxed).
Both transparency legs are *boxed*:

* leg1 (`searchThenSearch_t` on PrudentBot, prudence atom discharged):
  `□_k (DupocBot plays C vs PrudentBot) → (PrudentBot plays C vs DupocBot)`;
* leg2 (`searchBranch` on DupocBot):
  `□_k (PrudentBot plays C vs DupocBot) → (DupocBot plays C vs PrudentBot)`.

For the MirrorBot/TFT matchups one leg is an *unboxed* `.sim` (`simStep`), and
`searchBranch` + `simStep` chain directly into the closed `□_k φ → φ` that `PBLT`
consumes. Here neither leg is a `.sim`, so that route is unavailable: composing two
*boxed* implications into `□_k φ → φ` needs to strip a box, which the source-
transparency rules cannot do.

**The closing ingredient is object-form Σ₁-completeness for play-atoms**,
`atom_box_provable_impl : ⊢ (p plays a vs q) → □_k (p plays a vs q)` (Axioms.lean).
A `.plays` atom is Σ₁, so "true ⟹ provable" is sound reflection (NOT the GL-excluded
general `φ → □φ`, which fails on Π₁ truths). Applied to the play-atom `φ_P`:
`atom_box_provable_impl ⊳ leg2` yields the *unboxed-antecedent* implication
`φ_P → φ_D` (stripping the box `searchBranch` needs), which composes with `leg1`
into `□_k φ_D → φ_D`. That is exactly the role `simStep` plays for the `.sim`
matchups, now recovered for genuine search-vs-search via Σ₁-reflection rather than
`.sim` source-transparency.

The cooperative leg is *also* independently true with no axioms at all
(`dupocShaped_self_loeb_interp` below), which is why selecting `(C, C)` — the
intended Critch fixed point — is sound: the cooperative equilibrium is consistent,
and GL-4 is what lets `S` *prove* it rather than merely admit its consistency.
-/

/-! ## The cooperative Löb premise is true (no axioms) -/

/-- **The cooperative Löb premise is true, for any Dupoc-shaped cooperator.**
    `A = .search k (.plays .opp .self c) (.const c) (.const d)` cooperates `c` iff it
    proves the opponent plays `c` with it; for any opponent `B`, the implication
    `□_k (A plays c vs B) → (A plays c vs B)` holds. Proved with no new axioms via
    `A`'s own `.search` inversion. (The `(C,C)` outcome below does not use this; it
    is recorded as the semantic justification that the cooperative equilibrium is
    consistent.) -/
theorem dupocShaped_self_loeb_interp
    (k : Nat) (c d : Action) (B : Prog)
    (A : Prog) (hA : A = .search k (.plays .opp .self c) (.const c) (.const d)) :
    (Formula.impl (.box k (Formula.plays A B c)) (Formula.plays A B c)).interp := by
  subst hA
  show (Formula.box k (Formula.plays _ B c)).interp → (Formula.plays _ B c).interp
  intro hbox
  have hps : proofSearch k (Formula.plays
      (.search k (.plays .opp .self c) (.const c) (.const d)) B c) = true :=
    (proofSearch_spec _ _).2 hbox
  obtain ⟨n, hplay⟩ := proofSearch_sound _ _ hps
  cases hg : proofSearch k (Formula.plays B
      (.search k (.plays .opp .self c) (.const c) (.const d)) c) with
  | true =>
    refine ⟨2, ?_⟩
    show eval 2 _ B _ = some c
    simp [eval, Prog.subst, Formula.subst, hg]
  | false =>
    have hD : play (n + 2)
        (.search k (.plays .opp .self c) (.const c) (.const d)) B = some d := by
      show eval (n + 2) _ B _ = some d
      simp [eval, Prog.subst, Formula.subst, hg]
    have hC : play (n + 2)
        (.search k (.plays .opp .self c) (.const c) (.const d)) B = some c := by
      unfold play at hplay ⊢; exact eval_mono_le hplay (n + 2) (by omega)
    rw [hC] at hD
    obtain rfl : c = d := by injection hD
    exact ⟨n, hplay⟩

/-! ## Supporting lemmas for the (C, C) outcome -/

abbrev φD (k : Nat) : Formula := Formula.plays (DupocBot k) (PrudentBot k) Action.C
abbrev φP (k : Nat) : Formula := Formula.plays (PrudentBot k) (DupocBot k) Action.C

/-- Prudence atom: DupocBot plays D vs `.bot DefectBot` (its cooperation search
    fails — `.bot DefectBot` never cooperates — so it defects). -/
theorem dupoc_plays_D_vs_bot_DB (k fuel : Nat) :
    play (fuel + 2) (DupocBot k) (.bot DefectBot) = some .D := by
  have hg : proofSearch k (.plays (.bot DefectBot) (DupocBot k) .C) = false := by
    cases h : proofSearch k (.plays (.bot DefectBot) (DupocBot k) .C) with
    | true  => exact absurd (proofSearch_sound _ _ h) (interp_bot_DefectBot_plays_C_false _)
    | false => rfl
  show eval (fuel + 2) (DupocBot k) (.bot DefectBot) (DupocBot k) = some .D
  unfold DupocBot at hg ⊢
  simp [eval, Prog.subst, Formula.subst, hg]

/-! ### PrudentBot × DupocBot — RETIRED at same-`k` (2026-07-02, the false-guard repair).

The former `prudence_dupoc`/`prudent_dupoc_legPD`/`prudent_dupoc_legDP`/
`outcome_PrudentBot_vs_DupocBot` (mutual cooperation at ONE shared `k`) were artifacts of
the inconsistent axiom. Honestly: PrudentBot's prudence fact "DupocBot k defects vs
`.bot DefectBot`" is an ELSE-play of Dupoc's own search, so its certificate pays the
`search_f` floor `k` — PrudentBot's inner search at the SAME `k` can never afford it.
The Critch-faithful replacement is STAGGERED budgets — `PrudentBot j` vs `DupocBot k`
with `j ≥ k + O(log k)` (the prudence certificate = `Provable.atomNeg` refutation +
`search_f`, cost `k + log2 k + O(1)`), through the two-budget `mutual_pblt` wrapper —
planned as T3.2b (`DECIDABILITY_ROADMAP.md`). Notably this rediscovers why the original
MIRI PrudentBot checks prudence in a STRONGER system (PA+1): same-strength prudence is
self-referentially impossible. -/


-- PrudentBot --

/-! ### PrudentBot × DupocBot — RECOVERED with STAGGERED budgets (T3.2b, 2026-07-03).

`PrudentBot (2k+64)` vs `DupocBot k`: the bigger bot's inner search affords the partner's
`search_f` floor (Dupoc's else-play vs `.bot DefectBot` certifies at `k + log2 k + 15`),
and the mutual Löb chain runs through the two-budget `mutual_pblt_engine_staggered`.
Critch-faithful: prudence must live in a strictly larger budget than the bot it probes —
the bounded analogue of MIRI PrudentBot's PA+1 prudence. -/

/-- Dupoc's else-play vs `.bot DefectBot`, certified at the FLOOR: `search_f` over the
    `atomNeg` refutation of Dupoc's guard ("botDefect cooperates" — refuted by botDefect's
    actual bot∘const defection certificate). -/
theorem prudence_dupoc (k : Nat) :
    Provable (k + Nat.log2 k + 15) (.plays (DupocBot k) (.bot DefectBot) .D) := by
  have hneg : Provable (Nat.log2 k + 13)
      (.neg (.plays (.bot DefectBot) (DupocBot k) .C)) := by
    refine Provable.atomNeg (.bot DefectBot) (DupocBot k) .D .C 2
      ⟨PlaysProof.bot PlaysProof.const, by decide⟩ (by decide) ?_
    simp only [Formula.size, Prog.size, DefectBot, DupocBot]
    omega
  have hcert := atom_search_f_top k (Nat.log2 k + 13) (.plays .opp .self .C) .C .D
    (.bot DefectBot) hneg
  exact Provable.atom (atom_monotone _ _ _ (by omega) hcert)

/-- Leg 1 (staggered): `□_{2k+64} φD → φP` — `PrudentBot (2k+64)`'s stacked-search read;
    the inner prudence premise `prudence_dupoc` fits its literal (`k + log2 k + 15 ≤ 2k+64`),
    and the rule CITES the inner search (`c_guard`), keeping the leg's transcript O(log k). -/
theorem prudent_dupoc_legPD (k : Nat) :
    Provable (30 * Nat.log2 k + 700)
      (.impl (.box (2*k+64) (.plays (DupocBot k) (PrudentBot (2*k+64)) .C))
             (.plays (PrudentBot (2*k+64)) (DupocBot k) .C)) := by
  have hlk := log2_le_self k
  have hlg := log2_stagger_le k
  refine Provable.searchThenSearch_t (2*k+64) (2*k+64) (k + Nat.log2 k + 15)
    (.plays .opp .self .C) (.plays .opp (.bot DefectBot) .D)
    .C .D (.const .D) (PrudentBot (2*k+64)) (DupocBot k) rfl
    (by simpa [Formula.subst, Prog.subst] using prudence_dupoc k) (by omega) ?_
  simp only [Formula.subst, Prog.subst, Formula.size, Prog.size, DupocBot, PrudentBot,
    DefectBot, c_guard]
  omega

/-- Leg 2 (staggered): `□_k φP → φD` — `DupocBot k`'s `searchBranch` leaf. -/
theorem prudent_dupoc_legDP (k : Nat) :
    Provable (30 * Nat.log2 k + 700)
      (.impl (.box k (.plays (PrudentBot (2*k+64)) (DupocBot k) .C))
             (.plays (DupocBot k) (PrudentBot (2*k+64)) .C)) := by
  have hlg := log2_stagger_le k
  apply Provable.struct
  refine ⟨Derivation.searchBranch k (.plays .opp .self .C) .C .D
    (DupocBot k) (PrudentBot (2*k+64)) rfl, ?_⟩
  simp only [Derivation.size, Formula.size, Prog.size, DupocBot, PrudentBot, DefectBot]
  omega

/-- Dupoc's staggered-opponent play lemmas (generic in the opponent). -/
theorem dupoc_C_vs_any (k fuel : Nat) (q : Prog)
    (hk : proofSearch k (.plays q (DupocBot k) .C) = true) :
    play (fuel + 2) (DupocBot k) q = some .C := by
  show eval (fuel + 2) (DupocBot k) q (DupocBot k) = some .C
  unfold DupocBot at hk ⊢
  simp [eval, Prog.subst, Formula.subst, hk]

theorem dupoc_D_vs_any (k fuel : Nat) (q : Prog)
    (hk : proofSearch k (.plays q (DupocBot k) .C) = false) :
    play (fuel + 2) (DupocBot k) q = some .D := by
  show eval (fuel + 2) (DupocBot k) q (DupocBot k) = some .D
  unfold DupocBot at hk ⊢
  simp [eval, Prog.subst, Formula.subst, hk]

theorem ps_k_of_play_dupoc_any (k n : Nat) (q : Prog)
    (h : play n (DupocBot k) q = some .C) :
    proofSearch k (.plays q (DupocBot k) .C) = true := by
  cases hps : proofSearch k (.plays q (DupocBot k) .C) with
  | true  => rfl
  | false =>
    exfalso
    have hD : play (n + 2) (DupocBot k) q = some .D := dupoc_D_vs_any k n q hps
    have hC : play (n + 2) (DupocBot k) q = some .C := by
      unfold play at h ⊢; exact eval_mono_le h (n + 2) (by omega)
    rw [hC] at hD; cases hD

/-- **PrudentBot (2k+64) vs DupocBot k → (C, C)** for all large enough `k` — the
    staggered-budget recovery of the retired same-`k` theorem. -/
theorem outcome_PrudentBot_vs_DupocBot :
    ∃ k₂, ∀ k, k₂ < k →
      ∃ fuel, outcome fuel (PrudentBot (2*k+64)) (DupocBot k) = some (.C, .C) := by
  obtain ⟨KL, hKL⟩ := linear_log2_add_le 1 3
  have hsD : ∀ k, (Formula.plays (DupocBot k) (PrudentBot (2*k+64)) .C).size
      ≤ 100 * Nat.log2 k + 1000 := by
    intro k
    have hlg := log2_stagger_le k
    simp only [Formula.size, Prog.size, PrudentBot, DupocBot, DefectBot]
    omega
  have hsP : ∀ k, (Formula.plays (PrudentBot (2*k+64)) (DupocBot k) .C).size
      ≤ 100 * Nat.log2 k + 1000 := by
    intro k
    have hlg := log2_stagger_le k
    simp only [Formula.size, Prog.size, PrudentBot, DupocBot, DefectBot]
    omega
  have hpb : ∀ k, 30 * Nat.log2 k + 700 ≤ 100 * Nat.log2 k + 1000 := fun k => by omega
  obtain ⟨k₂, hk₂⟩ := mutual_pblt_engine_staggered
    (fun k => Formula.plays (DupocBot k) (PrudentBot (2*k+64)) .C)
    (fun k => Formula.plays (PrudentBot (2*k+64)) (DupocBot k) .C)
    (fun k => 2*k+64)
    (fun k => 30 * Nat.log2 k + 700) (fun k => 30 * Nat.log2 k + 700) 0
    (fun k => by show k ≤ 2*k+64; omega) log2_stagger_le hsD hsP hpb hpb
    (fun k _ => prudent_dupoc_legPD k)
    (fun k _ => prudent_dupoc_legDP k)
  refine ⟨max k₂ KL, fun k hk => ?_⟩
  have hk2 : k > k₂ := lt_of_le_of_lt (le_max_left _ _) hk
  have hKLk : Nat.log2 k + 3 ≤ k := by
    have := hKL k (le_of_lt (lt_of_le_of_lt (le_max_right _ _) hk))
    omega
  obtain ⟨m, hm⟩ := hk₂ k hk2
  obtain ⟨n, hplayD⟩ := Provable_sound m _ hm
  -- Dupoc's guard fired (inversion from its actual cooperative play)
  have hpsP : proofSearch k (.plays (PrudentBot (2*k+64)) (DupocBot k) .C) = true :=
    ps_k_of_play_dupoc_any k n (PrudentBot (2*k+64)) hplayD
  -- Dupoc's play atom, certified through its fired search (search_t cites)
  have hpsD : proofSearch (2*k+64)
      (.plays (DupocBot k) (PrudentBot (2*k+64)) .C) = true := by
    refine (proofSearch_spec _ _).2 (Provable.atom
      (⟨PlaysProof.search_t ((proofSearch_spec _ _).1 hpsP) PlaysProof.const, ?_⟩ :
        AtomProvable (2*k+64) (.plays (DupocBot k) (PrudentBot (2*k+64)) .C)))
    show c_leaf + c_guard k + c_node ≤ 2*k+64
    have hlk := log2_le_self k
    simp only [c_leaf, c_guard, c_node]
    omega
  -- Prudent's inner prudence guard at its own (bigger) literal
  have hprud : proofSearch (2*k+64) (.plays (DupocBot k) (.bot DefectBot) .D) = true := by
    refine (proofSearch_spec _ _).2 (Provable_mono (prudence_dupoc k) ?_)
    have hlk := log2_le_self k
    omega
  refine ⟨4, ?_⟩
  have hA : play 4 (PrudentBot (2*k+64)) (DupocBot k) = some .C := by
    simpa using prudent_eval_both_true (2*k+64) 1 (DupocBot k) hpsD hprud
  have hB : play 4 (DupocBot k) (PrudentBot (2*k+64)) = some .C := by
    simpa using dupoc_C_vs_any k 2 (PrudentBot (2*k+64)) hpsP
  exact outcome_of_plays _ _ _ _ _ hA hB

/-! ### PrudentBot self-play — RETIRED at same-`k` (2026-07-02, the false-guard repair).

`prudence_self_prudent`/`prudent_self_loeb_premise`/`outcome_PrudentBot_vs_PrudentBot`:
PrudentBot's prudence about ITSELF ("I defect vs `.bot DefectBot`") is an else-play of its
OWN outer search — floor `k`, self-referentially unaffordable at any single `k`. Needs a
two-tier PrudentBot (inner prudence budget above the outer literal — exactly Critch/MIRI's
PA+1 prudence); T3.2b. -/


end PD.Theorems
