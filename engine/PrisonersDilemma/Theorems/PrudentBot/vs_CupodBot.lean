import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Base.Exclusion
import PrisonersDilemma.Bots.LlmGenerations.PrudentBot
import PrisonersDilemma.Bots.CupodBot
import PrisonersDilemma.Theorems.PrudentBot.Helpers
import PrisonersDilemma.Theorems.CupodBot.Helpers

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

/-! ### PrudentBot vs CupodBot — `(D, C)` at every same budget (2026-08-25)

Two else-play floors facing each other. CupodBot punishes iff it can PROVE
"PrudentBot defects against me"; PrudentBot's defection is real but is an
else-play of its own nested search (whichever guard fails), so every certificate
of it pays `search_f`'s floor and Cupod cannot convict it: Cupod trusts (C).
PrudentBot cooperates iff it can prove "CupodBot cooperates with me"; Cupod's C
is likewise its else-play (`no_provable_CupodBot_C_tail`), so Prudent's outer
probe fails and it defects (D). Neither side needs the Löb engine, and the
result holds at every `k`.

This was the last STIPULATED cell of the tau zoo (`app`'s `CUPOD_STIPULATIONS`);
the tau layer proved the same value one level up (`cupod_prudent_plays_C`,
`prudent_cupod_plays_D` in `Tau/Theorems/TauPrudent/Helpers`), and this is that
argument transplanted to the base shape. -/

/-- No proof of ≤ k characters concludes any formula whose guarded spine tail is
    "PrudentBot plays D against O": both of PrudentBot's defections are else-plays
    (outer `search_f`, or inner `search_f` behind a fired outer guard) and pay the
    floor; the only then-constant is `C`. Generic in the opponent. -/
theorem no_provable_PrudentBot_D_tail (k : Nat) (O : Prog) :
    ∀ K φ, Pf K φ → K ≤ k → TailTo (.plays (PrudentBot k) O .D) φ → False := by
  refine no_provable_tailTo_floor k (PrudentBot k) O .D ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- the atom killer: every D-transcript crosses a failed search
    intro K hK hA
    cases hA with
    | mk hpp hn =>
      unfold PrudentBot at hpp
      cases hpp with
      | search_t _ hbr =>
          cases hbr with
          | search_t _ hc => cases hc
          | search_f _ _ => simp only [c_node] at hn; omega
      | search_f _ _ => simp only [c_node] at hn; omega
  · rintro (⟨_, _, _, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, _, _, h⟩ |
      ⟨_, _, _, _, _, _, _, h⟩) <;> simp [PrudentBot] at h
  · intro defs i h; simp [PrudentBot] at h
  · -- the nested-searcher reading rule concludes the then-constant `C`, not `D`
    intro k₁ ψ₁ k₂ ψ₂ c1 q h; simp [PrudentBot] at h
  · -- not a search telescope plugging `D`: the inner then-branch is `.const .C`
    intro L h
    unfold PrudentBot at h
    cases L with
    | nil => simp [searchPlug] at h
    | cons hd tl =>
        obtain ⟨g₁, ψ₁, e₁⟩ := hd
        simp only [searchPlug, Prog.search.injEq] at h
        obtain ⟨-, -, h, -⟩ := h
        cases tl with
        | nil => simp [searchPlug] at h
        | cons hd' tl' =>
            obtain ⟨g₂, ψ₂', e₂⟩ := hd'
            simp only [searchPlug, Prog.search.injEq] at h
            obtain ⟨-, -, h, -⟩ := h
            cases tl' with
            | nil => simp [searchPlug] at h
            | cons hd'' tl'' =>
                obtain ⟨g₃, ψ₃, e₃⟩ := hd''
                simp [searchPlug] at h
  · -- nor a mixed telescope plugging `D`
    intro hd L h
    unfold PrudentBot at h
    cases hd with
    | searchL g ψ e =>
        simp only [ctxPlug, Prog.search.injEq] at h
        obtain ⟨-, -, h, -⟩ := h
        cases L with
        | nil => simp [ctxPlug] at h
        | cons hd' tl' =>
            cases hd' with
            | searchL g' ψ' e' =>
                simp only [ctxPlug, Prog.search.injEq] at h
                exact const_ne_ctxPlug (by decide) tl' h.2.2.1
            | iteL z' aT' other' => simp [ctxPlug] at h
    | iteL z aT other => simp [ctxPlug] at h
  · -- an `elseL` layer captures one of PrudentBot's own else-slots: it pays ≥ k + 1
    intro hd L hme
    unfold PrudentBot at hme
    cases hd with
    | thenL g ψ e =>
        simp only [plug2, Prog.search.injEq] at hme
        obtain ⟨rfl, rfl, hplug, rfl⟩ := hme
        cases L with
        | nil => simp [plug2] at hplug
        | cons hd2 tl2 =>
            cases hd2 with
            | thenL g2 ψ2 e2 =>
                exfalso
                simp only [plug2, Prog.search.injEq] at hplug
                obtain ⟨-, -, hplug2, -⟩ := hplug
                cases tl2 with
                | nil => simp [plug2] at hplug2
                | cons hd3 tl3 => cases hd3 <;> simp [plug2] at hplug2
            | elseL g2 P2 Q2 c2 q2 =>
                simp only [plug2, Prog.search.injEq] at hplug
                obtain ⟨rfl, -, -, -⟩ := hplug
                simp only [layersCost, layerCost, c_node]
                omega
    | elseL g P' Q' c' q =>
        simp only [plug2, Prog.search.injEq] at hme
        obtain ⟨rfl, -, -, -⟩ := hme
        simp only [layersCost, layerCost, c_node]
        omega

/-- CupodBot's punish-probe on PrudentBot fails: PrudentBot's D is floor-priced. -/
theorem proofSearch_false_PrudentBot_D_vs_CupodBot (k : Nat) :
    proofSearch k (.plays (PrudentBot k) (CupodBot k) .D) = false := by
  cases h : proofSearch k (.plays (PrudentBot k) (CupodBot k) .D) with
  | true =>
      exact absurd ((proofSearch_spec k _).mp h)
        (fun hp => no_provable_PrudentBot_D_tail k (CupodBot k) k _ hp le_rfl (by simp))
  | false => rfl

/-- PrudentBot's cooperation probe on CupodBot fails: CupodBot's C is floor-priced. -/
theorem proofSearch_false_CupodBot_C_vs_PrudentBot (k : Nat) :
    proofSearch k (.plays (CupodBot k) (PrudentBot k) .C) = false := by
  cases h : proofSearch k (.plays (CupodBot k) (PrudentBot k) .C) with
  | true =>
      exact absurd ((proofSearch_spec k _).mp h)
        (fun hp => no_provable_CupodBot_C_tail k (PrudentBot k) k _ hp le_rfl (by simp))
  | false => rfl

/-- CupodBot trusts PrudentBot: it cannot convict it. -/
theorem CupodBot_plays_C_against_PrudentBot (k fuel : Nat) :
    play (fuel + 2) (CupodBot k) (PrudentBot k) = some .C := by
  show eval (fuel + 2) (CupodBot k) (PrudentBot k) (CupodBot k) = some .C
  have h := proofSearch_false_PrudentBot_D_vs_CupodBot k
  unfold CupodBot at h ⊢
  simp [eval, Prog.subst, Formula.subst, h]

/-- PrudentBot defects on CupodBot: its outer probe fails. -/
theorem PrudentBot_plays_D_against_CupodBot (k fuel : Nat) :
    play (fuel + 2) (PrudentBot k) (CupodBot k) = some .D :=
  PrudentBot_plays_D_of_search_false k fuel (CupodBot k)
    (proofSearch_false_CupodBot_C_vs_PrudentBot k)

/-- **PrudentBot vs CupodBot = (D, C)** at every same budget: the suspicious
    cooperator trusts a floor-priced defector, and the prudent bot exploits a
    floor-priced trust. -/
theorem outcome_PrudentBot_vs_CupodBot (k fuel : Nat) :
    outcome (fuel + 2) (PrudentBot k) (CupodBot k) = some (.D, .C) :=
  outcome_of_plays _ _ _ _ _ (PrudentBot_plays_D_against_CupodBot k fuel)
    (CupodBot_plays_C_against_PrudentBot k fuel)

end PD.Theorems
