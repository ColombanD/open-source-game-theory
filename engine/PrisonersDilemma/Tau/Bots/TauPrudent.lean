import PrisonersDilemma.Tau.Roster

/-!
# τ(PrudentBot) — Critch's canonical bot, at ONE budget

Base `PrudentBot k` is two nested searches: "can I prove the opponent cooperates
with me?" and, if so, "can I prove it is not a sucker (it defects against
DefectBot)?" — cooperate only if both; defect otherwise. The tree DSL writes it
as its base source: the inner search sits in the outer's then-branch.

**Single-budget convention (2026-08-25).** Base results stagger the budgets —
`outcome_PrudentBot_vs_DupocBot` needs `PrudentBot (2k+64)` because the
prudence check on Dupoc's else-play D must pay Dupoc's `search_f` floor. The
tau zoo gives every bot the SAME `k`, so at same-`k` the inner check FAILS for
exactly those partners and τ(Prudent) defects on them; those cells diverge from
base by budget regime and are whitelisted as such. What survives at same-`k`:
cooperation with the forwarder (mirror × prudent, bounded Löb through the
binder — the base `(C, C)`), and `(D, C)` against Cupod, the value base had
only as a STIPULATION.
-/

open PD

namespace PD.Tau

/-- τ(PrudentBot)'s spec: outer self-probe, inner defect-check in its then-branch. -/
def tauPrudentSpec : Spec Tmpl :=
  .search .prove .self .C
    (.search .prove (.name .defect) .D (.const .C) (.const .D))
    (.const .D)

end PD.Tau
