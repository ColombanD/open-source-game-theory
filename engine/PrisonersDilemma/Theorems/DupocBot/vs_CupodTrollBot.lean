import PrisonersDilemma.Base.Exclusion
import PrisonersDilemma.Bots.DupocBot
import PrisonersDilemma.Bots.CupodTrollBot
import PrisonersDilemma.Theorems.DupocBot.Helpers
import PrisonersDilemma.Theorems.CupodTrollBot.Helpers
import PrisonersDilemma.Outcome

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

/-! ### DupocBot vs CupodTrollBot at ONE budget — `(D, C)` (2026-08-25)

The strict cell is `outcome_CupodTrollBot_vs_DupocBot` (`Theorems/CupodTrollBot/`),
a dagger cell: `(C, C)` under `hjk`, which gives DupocBot a budget above the troll's
failed identity search. At one shared budget the troll's C is its else-play, so
DupocBot's probe of it fails and it defects — the value the tau lift reads. Both
regimes are theorems; the divergence is the budget alone. -/

/-- CupodTrollBot's C is its else-play: uncitable at its own budget, any opponent. -/
theorem proofSearch_false_CupodTrollBot_C (k : Nat) (O : Prog) :
    proofSearch k (.plays (CupodTrollBot k) O .C) = false := by
  cases h : proofSearch k (.plays (CupodTrollBot k) O .C) with
  | true =>
      exact absurd ((proofSearch_spec k _).mp h)
        (fun hp => no_provable_searcherElse_tail k (.eq .opp (CupodBot k)) .D .C (by decide)
          O k _ hp le_rfl (by simp [CupodTrollBot]))
  | false => rfl

theorem DupocBot_plays_D_against_CupodTrollBot_samek (k fuel : Nat) :
    play (fuel + 2) (DupocBot k) (CupodTrollBot k) = some .D := by
  have h := proofSearch_false_CupodTrollBot_C k (DupocBot k)
  show eval (fuel + 2) (DupocBot k) (CupodTrollBot k) (DupocBot k) = some .D
  unfold DupocBot at h ⊢
  simp [eval, Prog.subst, Formula.subst, h]

theorem CupodTrollBot_plays_C_against_DupocBot_samek (k fuel : Nat) :
    play (fuel + 2) (CupodTrollBot k) (DupocBot k) = some .C :=
  CupodTrollBot_cooperates_if_opp_not_CupodBot k fuel (DupocBot k) (by simp [DupocBot, CupodBot])

/-- **THE CELL — DupocBot vs CupodTrollBot at ONE shared budget = (D, C)**: Troll's C is
    its floor-priced else-play (its `.eq` recognition fails), which Dupoc cannot certify at
    the same `k`. Cooperation needs Dupoc's budget above Troll's —
    `outcome_CupodTrollBot_vs_DupocBot_staggered` (`Theorems/CupodTrollBot/vs_DupocBot.lean`).
    (Until 2026-08-27 the staggered result filled the cell and this was `_samek`.) -/
@[outcome]
theorem outcome_DupocBot_vs_CupodTrollBot :
    OutcomeSpec .universal 2 DupocBot CupodTrollBot (some (.D, .C)) := fun k fuel =>
  outcome_of_plays _ _ _ _ _ (DupocBot_plays_D_against_CupodTrollBot_samek k fuel)
    (CupodTrollBot_plays_C_against_DupocBot_samek k fuel)

end PD.Theorems
