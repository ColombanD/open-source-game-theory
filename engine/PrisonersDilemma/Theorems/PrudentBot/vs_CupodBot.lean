import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Base.Exclusion
import PrisonersDilemma.Bots.LlmGenerations.PrudentBot
import PrisonersDilemma.Bots.CupodBot
import PrisonersDilemma.Theorems.PrudentBot.Helpers
import PrisonersDilemma.Theorems.CupodBot.Helpers
import PrisonersDilemma.Outcome

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
  -- An instance of the bare nested-searcher edition `no_provable_nestedSearcher_D_tail`
  -- (2026-08-25; formerly a 83-line hand-rolled kernel instantiation — the twin of the
  -- tau layer's `no_provable_sysNested_D_tail`, one census library for both).
  intro K φ hp hK ht
  exact no_provable_nestedSearcher_D_tail k _ _ O K φ hp hK (by simpa only [PrudentBot] using ht)

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
@[outcome]
theorem outcome_PrudentBot_vs_CupodBot :
    OutcomeSpec .universal 2
      PrudentBot CupodBot (some (.D, .C)) :=
  fun k fuel =>
  outcome_of_plays _ _ _ _ _ (PrudentBot_plays_D_against_CupodBot k fuel)
    (CupodBot_plays_C_against_PrudentBot k fuel)

end PD.Theorems
