import PrisonersDilemma.Tau.Theorems.Helpers
import PrisonersDilemma.Base.Exclusion

/-!
# Tau/Theorems/TauEBot/Helpers — the Gödelian floor pair

TauEBot's own mathematics: `inst .ebot .dupoc` REALLY cooperates (its exploit-probe
of Dupoc fails, its reciprocity-probe fires) yet that cooperation is UNPROVABLE at
any budget ≤ k — every certificate must cross the failed exploit-search and pay the
`search_f` floor (`no_provable_botSearcherElse_tail`). A true bit that reads 0: the
tau image of base `outcome_DupocBot_vs_EBot = (D, C)`, and the cell the 2026-08-11
stipulation papered over.
-/

open PD PD.BaseTheorems

namespace PD.Tau

/-! ## The Gödelian floor pair — the δ_L column's EBot cell

`inst .ebot .dupoc` is the tau image of base `outcome_DupocBot_vs_EBot = (D, C)`:
the instance REALLY COOPERATES (its exploit-probe of Dupoc fails, its
reciprocity-probe fires), yet its cooperation is UNPROVABLE at any budget ≤ k —
every certificate must cross the failed exploit-search and pay the `search_f`
floor (`no_provable_botSearcherElse_tail`). A true bit that reads 0. -/

/-- TRUE: `inst .ebot .dupoc` plays C (through the failed exploit-probe). -/
theorem interp_probe_inst_ebot_dupoc {k : Nat} (hk : 2 ≤ k)
    (hkk : c_guard k + 3 ≤ k) :
    (probe (inst (zoo6 k) .ebot .dupoc)).interp := by
  have h1 : proofSearch k (probe (inst (zoo6 k) .dupoc .defect)) = false :=
    ps_searchProbe_constD k k
  have h2 : proofSearch k (probe (inst (zoo6 k) .dupoc .coop)) = true :=
    ps_searchProbe_constC hk hkk
  refine ⟨4, ?_⟩
  -- after `refine`, the goal is the PLAY of the `.bot`-framed instance; peel one
  -- compiler level, then the two guard bits close the run
  rw [inst_ebot_peel k .dupoc]
  simp [play, eval, probe_subst, h1, h2]

/-- UNPROVABLE: the bit is 0 at every budget up to k — TauDupoc's probe honestly
    fails. -/
theorem ps_probe_inst_ebot_dupoc_false {k K : Nat} (hK : K ≤ k) :
    proofSearch K (probe (inst (zoo6 k) .ebot .dupoc)) = false := by
  cases h : proofSearch K (probe (inst (zoo6 k) .ebot .dupoc)) with
  | false => rfl
  | true =>
      exfalso
      exact no_provable_botSearcherElse_tail k k
        (probe (inst (zoo6 k) .dupoc .defect)) .D .C
        (.search k (probe (inst (zoo6 k) .dupoc .coop)) (.const .C) (.const .D))
        (by decide) (Nat.le_refl k)
        (.bot (inst (zoo6 k) .ebot .dupoc))
        K _ ((proofSearch_spec _ _).1 h) hK rfl

end PD.Tau
