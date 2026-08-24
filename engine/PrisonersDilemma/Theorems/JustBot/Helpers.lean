import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Bots.DupocBot
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Bots.LlmGenerations.JustBot
import PrisonersDilemma.Theorems.CooperateBot.Helpers
import PrisonersDilemma.Theorems.DefectBot.Helpers
import PrisonersDilemma.Theorems.DupocBot.Helpers
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Base.Asymptotics

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

/-! # JustBot — shared play/guard lemmas used by several `vs_*` files.
Split from `LlmGenerations/JustBot.lean` (per-pair refactor, 2026-07-27). -/

/-- One evaluation step of JustBot: it consults its guard `proofSearch` and takes
    the corresponding constant branch (cooperate iff the guard fires). -/
theorem JustBot_eval_step (k fuel : Nat) (X : Prog) (a : Action)
    (hg : proofSearch k (Formula.plays X (.bot (DupocBot k)) Action.C)
            = (a == Action.C)) :
    play (fuel + 2) (JustBot k) X = some a := by
  -- The guard `proofSearch` argument is definitionally `.plays X (.bot (DupocBot k)) .C`.
  show (if proofSearch k (Formula.plays X (.bot (DupocBot k)) Action.C)
          then eval (fuel + 1) (JustBot k) X (.const Action.C)
          else eval (fuel + 1) (JustBot k) X (.const Action.D)) = some a
  rw [hg]
  cases a with
  | C => simp [eval]; rfl
  | D => simp [eval]; rfl
-- .bot DefectBot cannot play C against anything
theorem ps_false_bot_DefectBot_vs_bot_DupocBot_JB (k : Nat) :
    proofSearch k (.plays (.bot DefectBot) (.bot (DupocBot k)) .C) = false := by
  cases h : proofSearch k (.plays (.bot DefectBot) (.bot (DupocBot k)) .C) with
  | true =>
    exact absurd (proofSearch_sound _ _ h) (by
      rintro ⟨n, hn⟩
      rcases n with _ | _ | n
      · simp [play, eval] at hn
      · simp [play, eval] at hn
      · simp [play, eval, DefectBot] at hn)
  | false => rfl
-- JustBot k defects against .bot DefectBot: its guard (.plays .bot DefectBot ...) fails
theorem JustBot_plays_D_against_bot_DefectBot_JB (k fuel : Nat) :
    play (fuel + 2) (JustBot k) (.bot DefectBot) = some .D := by
  have hg := ps_false_bot_DefectBot_vs_bot_DupocBot_JB k
  show eval (fuel + 2) (JustBot k) (.bot DefectBot) (JustBot k) = some .D
  unfold JustBot
  simp [eval, Prog.subst, Formula.subst, hg]
/-- JustBot's guard against `.bot CooperateBot` is the *same* shared formula
    `.plays (.bot CooperateBot) (.bot (DupocBot k)) .C`, so JustBot cooperates
    against `.bot CooperateBot` whenever the shared guard fires. This is what makes
    TFT (which probes its opponent against `.bot CooperateBot`) cooperate with
    JustBot. -/
theorem JustBot_plays_C_against_bot_CooperateBot (k fuel : Nat)
    (hk : proofSearch k (Formula.plays (.bot CooperateBot) (.bot (DupocBot k)) Action.C) = true) :
    play (fuel + 2) (JustBot k) (.bot CooperateBot) = some .C := by
  refine JustBot_eval_step k fuel (.bot CooperateBot) .C ?_
  simpa using hk
end PD.Theorems

/-! ## JustBot's defection floor, generic in the opponent (2026-08-21)

JustBot's D is its ELSE-slot — same mechanism as CupodBot's trust floor, opposite
polarity. Predicted by the tau layer's closure of the (just, cupod) cell. -/

/-- No proof of ≤ k characters concludes any formula whose guarded spine tail is
    "JustBot plays D against O": `search_t` concludes the then-constant `.C`
    (action mismatch), `search_f` pays the floor. -/
theorem no_provable_JustBot_D_tail (k : Nat) (O : Prog) :
    ∀ K φ, Pf K φ → K ≤ k →
      TailTo (.plays (JustBot k) O .D) φ → False := by
  intro K φ hp hK ht
  refine no_provable_tailToS_floor k (· = .plays (JustBot k) O .D)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ K φ hp hK ((TailToS_singleton _ φ).2 ht)
  · rintro φ' rfl; exact ⟨_, _, _, rfl⟩
  · intro K' hK' φ' hφ'
    cases hφ'
    intro hA
    cases hA with
    | mk hpp hn =>
      unfold JustBot at hpp
      cases hpp with
      | search_t hProv hbr => cases hbr
      | search_f hneg hbr => simp only [c_node] at hn; omega
  · intro me oppo c hS g ψ b hme
    injection hS with h1 h2 h3
    subst h1; subst h3
    unfold JustBot at hme
    injection hme with e1 e2 e3 e4
    simp at e3
  · intro me oppo c hS p q hme
    injection hS with h1 h2 h3
    subst h1
    unfold JustBot at hme; simp at hme
  · intro me oppo c hS p q hme
    injection hS with h1 h2 h3
    subst h1
    unfold JustBot at hme; simp at hme
  · intro me oppo c hS g ψ b hme
    injection hS with h1 h2 h3
    subst h1
    unfold JustBot at hme; simp at hme
  · intro z a' g ψ c0 c1 q oppo hS
    injection hS with h1 h2 h3
    unfold JustBot at h1; simp at h1
  · intro me oppo c hS k₁ ψ₁ k₂ ψ₂ c1 q hme
    injection hS with h1 h2 h3
    subst h1
    unfold JustBot at hme; simp at hme
  · intro me oppo c hS L hme
    injection hS with h1 h2 h3
    subst h1; subst h3
    cases L with
    | nil => unfold JustBot at hme; simp [searchPlug] at hme
    | cons hd tl =>
        obtain ⟨g, ψ, e⟩ := hd
        unfold JustBot at hme
        simp only [searchPlug, Prog.search.injEq] at hme
        have hcontra := hme.2.2.1
        rw [searchPlug_eq_ctxPlug tl (.const .D)] at hcontra
        exact const_ne_ctxPlug (by decide) _ hcontra
  · intro me oppo c hS hd L hme
    injection hS with h1 h2 h3
    subst h1; subst h3
    exfalso
    cases hd with
    | searchL g ψ e =>
        unfold JustBot at hme
        simp only [ctxPlug, Prog.search.injEq] at hme
        have hcontra := hme.2.2.1
        exact const_ne_ctxPlug (by decide) L hcontra
    | iteL z aT other => unfold JustBot at hme; simp [ctxPlug] at hme
  · intro me oppo c hS hd L hme
    injection hS with h1 h2 h3; subst h1; subst h3
    cases hd with
    | thenL g ψ e =>
        simp only [plug2, JustBot, Prog.search.injEq] at hme
        obtain ⟨-, -, hplug, -⟩ := hme
        exfalso
        cases L with
        | nil => simp [plug2] at hplug
        | cons hd2 tl2 => cases hd2 <;> simp [plug2] at hplug
    | elseL g P' Q' c' q =>
        simp only [plug2, JustBot, Prog.search.injEq] at hme
        obtain ⟨rfl, -, -, -⟩ := hme
        simp only [layersCost, layerCost, c_node]
        omega
  · intro me oppo c hS defs i _ _ _ hme _
    injection hS with h1 h2 h3
    subst h1
    unfold JustBot at hme; simp at hme
  · -- hbotsyssim: the `.sys` RUN twin, same shape kill
    intro me oppo c hS defs i _ hme _
    injection hS with h1 h2 h3
    subst h1
    unfold JustBot at hme; simp at hme
