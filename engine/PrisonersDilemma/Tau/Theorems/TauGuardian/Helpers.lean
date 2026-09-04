import PrisonersDilemma.Tau.Theorems.Helpers
import PrisonersDilemma.Base.Exclusion

/-!
# Tau/Theorems/TauGuardian/Helpers — the guardian floor

TauGuardian's own mathematics, and the zoo's third Gödelian phenomenon: **Guardian's
cooperation is TRUE (`⊨`) but NEVER `S`-derivable within its budget (`¬ ⊢_K`, `K ≤ k`).** Its instance at ANY hypothesis
plays C only through a FAILED punish-search (the probeD that found no defection), so
every C-certificate must cross that failed search and pay the `search_f` floor.
Parametric in the probed instance `P` — one kernel application covers Guardian's
whole row of floor cells (δ_C, δ_L, and any future column).

Consequence (proved through the columns): every PROVER in the zoo reads Guardian's
cooperation as 0 while every BEHAVIORAL reader sees it as 1 — with Guardian in the
zoo, the prover/behavioral split becomes an α-GAP, not just a budget gap.
-/

open PD PD.BaseTheorems

namespace PD.Tau

/-- Guardian's floor, parametric: the trusting else-play of a `.bot`-frozen
    punish-searcher is unprovable at every budget up to k
    (`no_provable_botSearcherElse_tail`, with the DEFECTION atom as the guard —
    the kernel is guard-generic). -/
theorem ps_probe_guardCell_false {k K : Nat} (hK : K ≤ k) (P : Prog) :
    proofSearch K (probe (.search k (.plays (.bot P) (.bot P) Action.D)
      (.const .D) (.const .C))) = false := by
  cases h : proofSearch K (probe (.search k (.plays (.bot P) (.bot P) Action.D)
      (.const .D) (.const .C))) with
  | false => rfl
  | true =>
      exfalso
      exact no_provable_botSearcherElse_tail k k
        (.plays (.bot P) (.bot P) Action.D) .D .C (.const .C)
        (by decide) (Nat.le_refl k)
        (.bot (.search k (.plays (.bot P) (.bot P) Action.D) (.const .D) (.const .C)))
        K _ ((proofSearch_spec _ _).1 h) hK rfl

end PD.Tau
