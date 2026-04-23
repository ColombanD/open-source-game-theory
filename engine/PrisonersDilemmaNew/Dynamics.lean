import PrisonersDilemmaNew.Program

namespace PDNew


-- Abstract proof-search oracle: `proofSearch k φ = true` iff φ has a proof
-- of size ≤ k in the background logic. Declared as an axiom because we
-- reason *about* such an oracle without implementing one. The formula must
-- be closed.
noncomputable axiom proofSearch : Nat → Formula → Bool

-- Fuelled evaluator. `me`/`opponent` are the fixed source programs of the
-- two players; `body` is the subterm currently being reduced. `Option` lets
-- runs fail when fuel is exhausted, keeping `eval` finite despite the
-- unbounded self-reference available in `Prog`.
noncomputable def eval : Nat → (me opponent body : Prog) → Option Action
  | 0,   _,  _,   _    => none  -- fuel exhausted
  | n+1, me, opponent, body => match body with
    | .const a        => some a                        -- fixed action, no recursion
    | .self           => eval n me opponent me         -- resolve `.self` to my own source
    | .opp            => eval n me opponent opponent   -- resolve `.opp` to opponent's source
    | .sim p q        =>
        -- Enter a new context with p vs q. Close p and q against the
        -- *current* me/opponent first so their placeholders don't leak.
        let p' := p.subst me opponent
        let q' := q.subst me opponent
        eval n p' q' p'
    | .ite b a p q    => do
        -- Run guard program b; branch on whether its action equals a.
        let r ← eval n me opponent b
        if r == a then eval n me opponent p else eval n me opponent q
    | .search k φ p q =>
        -- Close the guard formula, ask the oracle with budget k, branch.
        -- Note: k (proof size) is independent of n (evaluation fuel).
        if proofSearch k (φ.subst me opponent)
          then eval n me opponent p
          else eval n me opponent q

-- Canonical entry point: an agent runs its own source against its opponent.
noncomputable def play (fuel : Nat) (me opponent : Prog) : Option Action :=
  eval fuel me opponent me

-- Both sides play symmetrically with the same fuel; either failing yields `none`.
noncomputable def outcome (fuel : Nat) (p q : Prog) : Option Outcome := do
  let a ← play fuel p q
  let b ← play fuel q p
  some (a, b)

-- Denotational semantics: maps a syntactic `Formula` to a Lean proposition.
-- `.plays` is fuel-existential so theorems don't have to commit to a budget.
-- Note: `interp` does not mention `proofSearch` — the oracle is operational,
-- while truth here is defined in the model.
def Formula.interp : Formula → Prop
  | .plays p q a => ∃ n, play n p q = some a
  | .impl φ ψ    => φ.interp → ψ.interp
  | .neg φ       => ¬ φ.interp
  | .box n φ     => proofSearch n φ = true

end PDNew
