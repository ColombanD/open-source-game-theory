import PrisonersDilemma.Program

namespace PDNew

-- Fuelled evaluator, *parametric in the proof-search oracle* `ps`.
--
-- `ps : Nat → Formula → Bool` is the oracle the `.search` guard consults.
-- Taking it as an explicit parameter is what breaks the definitional cycle
-- between evaluation and the proof system: `evalWith` is defined here, before
-- any concrete oracle exists. The real oracle (`proofSearch`, defined in
-- Derivation.lean over the explicit `Derivation` system) is plugged in later
-- via the convenience abbreviation `eval := evalWith proofSearch`, at which
-- point `play` ties the knot. Downstream code uses `eval`/`play` and never
-- sees the oracle parameter.
--
-- `me`/`opponent` are the fixed source programs of the two players; `body` is
-- the subterm currently being reduced. `Option` lets runs fail when fuel is
-- exhausted, keeping `eval` finite despite the unbounded self-reference
-- available in `Prog`.
noncomputable def evalWith (ps : Nat → Formula → Bool) :
    Nat → (me opponent body : Prog) → Option Action
  | 0,   _,  _,   _    => none  -- fuel exhausted
  | n+1, me, opponent, body => match body with
    | .const a        => some a                                -- fixed action, no recursion
    | .self           => evalWith ps n me opponent me         -- resolve `.self` to my own source
    | .opp            => evalWith ps n me opponent opponent   -- resolve `.opp` to opponent's source
    | .bot p          => evalWith ps n me opponent p          -- unwrap closed bot reference
    | .sim p q        =>
        -- Enter a new context with p vs q. Close p and q against the
        -- *current* me/opponent first so their placeholders don't leak.
        let p' := p.subst me opponent
        let q' := q.subst me opponent
        evalWith ps n p' q' p'
    | .ite b a p q    => do
        -- Run guard program b; branch on whether its action equals a.
        let r ← evalWith ps n me opponent b
        if r == a then evalWith ps n me opponent p else evalWith ps n me opponent q
    | .search k φ p q =>
        -- Close the guard formula, ask the oracle with budget k, branch.
        -- Note: k (proof size) is independent of n (evaluation fuel).
        if ps k (φ.subst me opponent)
          then evalWith ps n me opponent p
          else evalWith ps n me opponent q

end PDNew
