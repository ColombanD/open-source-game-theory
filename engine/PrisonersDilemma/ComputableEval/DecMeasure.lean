import PrisonersDilemma.Program

/-!
# Why bounded `Provable` admits no naive well-founded decision measure

DECISIVE NEGATIVE RESULT (2026-06-18). This file is the machine-checked half of the
argument that `eval` cannot be made *totally* computable: it refutes the most natural
attempt to decide bounded provability by structural recursion.

Any decision of `Provable k φ` must recurse through `PlaysProof`'s `search_t` guard
`Provable kg (ψ.subst me opp)`, where `kg` is a source literal (bounded by `2^k` but
NOT `< k`) and `ψ` is substituted with the *players* `me`/`opp`. The obvious
well-founded measure for such a recursion is lexicographic `(k, search-nesting-depth)`,
relying on the depth rank not growing under `subst` because `.bot` is a scope barrier.

**That reliance is unfounded.** With `searchDepth` defined below (`.search` adds `+1`,
`.bot` blocks descent), substituting a search-bot into its OWN guard increases depth:

    meP := .search 0 (.eq .self .self) .self .self      -- searchDepth = 1
    (meP-guard).subst meP meP   has searchDepth = 2 > 1  -- the guard `.self` becomes meP

So neither `kg` (≤ 2^k, not decreasing) nor the search-depth rank decreases on the
guard recursion. This is precisely the Löb self-reference that makes `eval`
noncomputable: a bot's `.search` guard can ask about the opponent (or itself) at a
budget/shape no smaller than the current one, so the recursion need not bottom out.

CONSEQUENCE: no naive structural/lexicographic measure decides `Provable k φ` totally.
A terminating procedure would have to bound the guard recursion by an EXTERNAL
fuel/depth parameter and then either (a) prove it agrees with `Provable` at sufficient
fuel — an agreement that cannot hold, since the Löb-fixpoint outcomes are reflected
through `proofSearch_spec` yet have no finite proof-search witness — or (b) accept a
fuel-capped *partial* decision (which is exactly what the computable evaluator
`ComputableEval/Computable.lean` does, returning `none` at the fixpoint). This file
supplies the structural obstruction; the reflection argument supplies the rest.

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
    | .diag _ φ    => φ.searchDepth
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
