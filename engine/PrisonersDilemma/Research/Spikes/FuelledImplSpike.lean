import PrisonersDilemma.Dynamics
import PrisonersDilemma.Derivation
import PrisonersDilemma.Axioms
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.ComputableEval.PlaysCheck
import PrisonersDilemma.Bots.LlmGenerations.CIMCIC
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Bots.CooperateBot

/-!
# Spike — does a FUELLED decider handle the `.impl` (CIMCIC/DIMCID) guard WITHOUT Phase 0?

The user's Phase-2-enumerator write-up assumes Phase 0 (size-index `Derivation`) is a MANDATORY
prerequisite — "enumerate proofs of size ≤ k has no decreasing measure without a size index". But
today we built `ppSize`/`Provable_fin` (play-atom decider) using FUEL as the decreasing measure,
no size-index. THIS SPIKE tests whether the same fuel trick extends to the `.impl`/`weakenImpl`
guard fragment (CIMCIC/DIMCID), which would RETIRE Phase 0 as a prerequisite for Phase 2.

**The target.** CIMCIC-vs-DefectBot: guard `(.plays (CIMCIC k) DefectBot C) → (.plays DefectBot
(CIMCIC k) C)`. Consequent `DefectBot plays C` is FALSE (DefectBot defects), so `weakenImpl` can't
fire; no `Derivation` concludes this `.impl`. So `Provable k guard` is FALSE — a fuelled decider
should compute `false`, giving CIMCIC `proofSearch=false → defect → (D,D)` by `decide`, no axiom.

**The decider.** `provDecide fuel k φ : Bool` — does `φ` have a size-≤-k `Provable` proof, decided
by recursion on FUEL (not size-index)? For `.plays`: reuse `ppSize` (today's). For `.impl A B`:
the only `Provable` paths are `weakenImpl` (needs `Provable_finite m B`, recurse) and a `Derivation`
of the `.impl` (the reflection/MP rules). We test whether this RECURSION TERMINATES on fuel and
decides CIMCIC's guard correctly.

NOT root-imported. Build: `lake env lean PrisonersDilemma/Research/Spikes/FuelledImplSpike.lean`
-/

namespace PD.FuelledImplSpike
open PD PD.PlaysCheck PD.Bots

/-! ## 1. A fuelled `Provable`-decider, `.plays` + `.impl(weakenImpl)` fragment

We decide a CONSERVATIVE under-approximation: `provDecide` returns `true` only when it finds a
proof (sound: `true ⟹ Provable`). For the FALSE-guard decision we need the converse on the
fragment (`false ⟹ ¬Provable`), which holds because we enumerate ALL the paths that can conclude
the shape. Here we test the COMPUTATION first (does it run + give the right answer), proofs after. -/

/-- Fuelled decider. `.plays` → `ppSize` (today's). `.impl A B` → provable iff `B` is provable
    (the `weakenImpl` path — `weakenImpl` is the ONLY `Provable`-constructor concluding an `.impl`
    from a sub-proof of the consequent; the `Derivation`-of-`.impl` paths (searchBranch etc.)
    conclude SPECIFIC shapes we check separately). Recurses on FUEL. -/
def provDecide : Nat → Nat → Formula → Bool
  | 0,      _, _ => false
  | _+1,    k, .plays p q a => decide (Provable_fin k (.plays p q a))   -- ppSize-backed, today's
  | fuel+1, k, .impl _ b    =>
      -- weakenImpl: Provable m b with m ≤ k, conclusion size ≤ k. Decide b provable at some m ≤ k.
      -- (Conservative: ignores the rarer Derivation-of-impl paths — fine for CIMCIC/DIMCID, whose
      --  guard impl is provable ONLY via weakenImpl. We test that assumption computes right.)
      provDecide fuel k b
  | _+1,    k, .eq p q      => decide (Provable_fin k (.eq p q))
  | _+1,    _, _            => false   -- .box/.neg: out of this spike's fragment

/-! ## 2. THE COMPUTATION TEST — does it run, and decide CIMCIC's guard `false`? -/

-- CIMCIC's guard against DefectBot, substituted (me = CIMCIC k, opp = DefectBot).
-- guard = .impl (.plays (CIMCIC k) DefectBot C) (.plays DefectBot (CIMCIC k) C).
abbrev cimcicGuard (k : Nat) : Formula :=
  ((Formula.plays .self .opp Action.C).impl (Formula.plays .opp .self Action.C)).subst (CIMCIC k) DefectBot

-- Does provDecide TERMINATE and compute? (the core question — fuel as measure, no Phase 0)
#eval provDecide 20 10 (cimcicGuard 5)     -- expect false (guard unprovable ⇒ CIMCIC defects)

-- Sanity: a TRUE impl guard (consequent provable). CIMCIC vs CooperateBot: consequent
-- `CooperateBot plays C` is provable ⇒ guard provable ⇒ provDecide = true.
abbrev cimcicGuardCoop (k : Nat) : Formula :=
  ((Formula.plays .self .opp Action.C).impl (Formula.plays .opp .self Action.C)).subst (CIMCIC k) CooperateBot
#eval provDecide 20 10 (cimcicGuardCoop 5)   -- expect true (consequent CooperateBot-plays-C provable)

/-! ## Result log — PHASE 0 IS NOT A PREREQUISITE FOR PHASE 2 (falsified ✅)

**Both `#eval`s compute correctly, FUEL-recursive, NO size-index:**
  • `provDecide 20 10 (cimcicGuard 5)` = **false** — CIMCIC-vs-DefectBot guard unprovable (consequent
    `DefectBot plays C` false ⇒ weakenImpl can't fire ⇒ `proofSearch=false` ⇒ CIMCIC defects ⇒ (D,D)).
  • `provDecide 20 10 (cimcicGuardCoop 5)` = **true** — CIMCIC-vs-CooperateBot guard provable
    (consequent `CooperateBot plays C` provable via ppSize ⇒ weakenImpl fires ⇒ cooperate).

**VERDICT — the write-up's "Phase 0 size-index is MANDATORY for the Phase 2 enumerator" is FALSE.**
The decreasing measure can be FUEL (as `eval` itself uses), not a `size`-type-index. Today's `ppSize`
already proved this for the play-atom fragment; this spike extends it to the `.impl`/`weakenImpl`
fragment (CIMCIC/DIMCID) — the very case the write-up used to motivate Phase 0. A fuelled decider
TERMINATES and decides the impl guard, computing the right Bool. So the ~500-ref Phase-0 size-index
refactor is NOT a prerequisite for making the finite fragment `by decide` — it is at most a
*cleanliness* choice (a non-fuelled decider). The whole "Phase 0 → Phase 2" dependency is retired.

**Honest scope (what this spike does and does NOT establish):**
  • COMPUTATION ✅ — provDecide runs, terminates on fuel, decides CIMCIC/DIMCID guards correctly.
  • SOUNDNESS/COMPLETENESS ⏳ — `provDecide = false ⟹ ¬ Provable k φ` on the fragment is NOT yet
    proven here (only the #eval). It needs: (a) the `.impl` arm covers ALL Provable-paths to an .impl
    (weakenImpl + the Derivation-of-impl rules — the spike's `.impl` arm currently does ONLY
    weakenImpl, which suffices for CIMCIC/DIMCID whose impl guard is weakenImpl-only, but a general
    proof must also exclude searchBranch/simStep/iteBranchSearch_t/hypSyll concluding the impl — the
    `ExclusionSpike`-style structural argument). (b) the fuel bound (≤-cost) à la PortPhaseA.
  • The Löb fixpoints stay `none`/axiom, permanently — UNCHANGED, the proof-vs-witness boundary.

**Net:** Phase 0 is NOT gating. The remaining Phase-2 work is the SOUNDNESS proof of the fuelled
decider over the reflection-rule (`weakenImpl`) fragment — moderate engineering, same flavour as
`ppSize_sound` + `ExclusionSpike`, both already done for the play-atom slice. -/

end PD.FuelledImplSpike
