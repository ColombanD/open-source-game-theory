import PrisonersDilemmaNew.Program
import PrisonersDilemmaNew.Dynamics
import PrisonersDilemmaNew.Theorems.Axioms
import PrisonersDilemmaNew.Bots.CooperateBot
import PrisonersDilemmaNew.Bots.CupodBot
import PrisonersDilemmaNew.Theorems.CooperateBot

open PDNew
open PDNew.Axioms
open PDNew.Bots
namespace PDNew.Theorems


-- Lemma 3: therefore the oracle must return `false` on that formula.
-- This is the contrapositive of soundness, wrapped in a bool case split.
theorem guard_false (k : Nat) :
    proofSearch k (.plays CooperateBot (CupodBot k) .D) = false := by
  cases h : proofSearch k (.plays CooperateBot (CupodBot k) .D) with
  | true  => exact absurd (proofSearch_sound _ _ h)
                          (interp_CooperateBot_plays_D_false _)
  | false => rfl

-- Main theorem.
theorem CUPOD_vs_CB (k fuel : Nat) (hfuel : 2 ≤ fuel) :
    outcome fuel (CupodBot k) CooperateBot = some (.C, .C) := by
  -- Peel fuel down to at least two steps of unfolding.
  obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 2 := ⟨fuel - 2, by omega⟩
  -- Left side: CUPOD runs its `.search`; the guard is false by Lemma 3,
  -- so we fall through to `.const .C`.
  have hA : play (n + 2) (CupodBot k) CooperateBot = some .C := by
    show eval (n + 2) (CupodBot k) CooperateBot (CupodBot k) = some .C
    have hg := guard_false k
    unfold CupodBot at hg ⊢
    simp [eval, Prog.subst, Formula.subst, hg]
  -- Right side: CB always cooperates.
  have hB : play (n + 2) CooperateBot (CupodBot k) = some .C := rfl
  -- Assemble the outcome.
  simp [outcome, hA, hB]

end PDNew.Theorems
