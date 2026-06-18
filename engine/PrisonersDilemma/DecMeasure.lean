import PrisonersDilemma.Program

/-!
# Termination-measure investigation for deciding bounded `Provable` (route ii)

DECISIVE NEGATIVE RESULT (2026-06-18). Deciding `Provable k φ` recurses through
`PlaysProof`'s `search_t` guard `Provable kg (ψ.subst me opp)`, where `kg` is a source
literal (bounded by `2^k` but NOT < k) and `ψ` is substituted with the *players*
`me`/`opp`. The plan's candidate well-founded measure was lexicographic
`(k, search-nesting-depth-in-program)`, claiming the depth rank does not grow under
`subst` because `.bot` is a scope barrier.

**That claim is FALSE.** With `searchDepth` defined below (`.search` adds `+1`,
`.bot` blocks descent), substituting a search-bot into its OWN guard increases depth:

    meP := .search 0 (.eq .self .self) .self .self      -- searchDepth = 1
    (meP-guard).subst meP meP   has searchDepth = 2 > 1  -- the guard `.self` becomes meP

So neither `kg` (≤ 2^k, not decreasing) nor the search-depth rank decreases on the
guard recursion. This is precisely the Löb self-reference that made `eval`
noncomputable originally: a bot's `.search` guard can ask about the opponent (or
itself) at a budget/shape no smaller than the current one.

CONSEQUENCE for route (ii): there is no naive structural/lexicographic measure for a
single `decP`/`Decidable (Provable k φ)` over the guard recursion. A genuine decision
procedure must instead bound the guard recursion by an EXTERNAL fuel/depth parameter
(making `decP` fuel-indexed) and then either (a) prove that at sufficient fuel it
agrees with `Provable` — which is the same agreement obligation that sank the
`derivable` route — or (b) accept a fuel-capped *partial* decision. See
`COMPUTABLE_EVAL_NOTES.md`; this file documents why the unindexed WF measure fails.

The non-`.search` part of subst-stability below IS true and is kept as a building
block (search-depth is preserved under subst EXCEPT across `.search` substitution).
-/

namespace PD

-- Search-nesting depth reachable in the current frame (`.bot` blocks descent).
mutual
  def Prog.searchDepth : Prog → Nat
    | .const _        => 0
    | .self           => 0
    | .opp            => 0
    | .bot _          => 0
    | .sim p q        => max p.searchDepth q.searchDepth
    | .ite b _ p q    => max b.searchDepth (max p.searchDepth q.searchDepth)
    | .search _ φ p q => max φ.searchDepth (max p.searchDepth q.searchDepth) + 1
  def Formula.searchDepth : Formula → Nat
    | .plays p q _ => max p.searchDepth q.searchDepth
    | .impl φ ψ    => max φ.searchDepth ψ.searchDepth
    | .neg φ       => φ.searchDepth
    | .box _ φ     => φ.searchDepth
    | .eq p _      => p.searchDepth
end

-- The counterexample, machine-checked: substituting a search-bot into its own guard
-- raises search-depth above the substituent's. Refutes the naive WF measure.
def meP : Prog := .search 0 (.eq .self .self) .self .self

example : meP.searchDepth = 1 := by decide
example :
    ((Formula.eq Prog.self Prog.self).subst meP meP).searchDepth = 1 := by decide
example :
    ((Prog.search 0 (.eq .self .self) .self .self).subst meP meP).searchDepth = 2 := by
  decide

end PD
