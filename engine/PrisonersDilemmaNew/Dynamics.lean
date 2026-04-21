import PrisonersDilemmaNew.Program

namespace PDNew

-- The oracle now takes a closed `Formula`. The `Prog` argument in
-- your sketch is folded into the formula itself via substitution.
-- It is an axiom meaning the file assumes a boolean proof search oracle exists, but does not implement it.
noncomputable axiom proofSearch : Nat → Formula → Bool

-- Fuelled evaluator.
noncomputable def eval : Nat → (me opponent body : Prog) → Option Action
  | 0,   _,  _,   _    => none  -- out of fuel
  | n+1, me, opponent, body => match body with
    | .const a        => some a -- constant program: return the action
    | .self           => eval n me opponent me -- Evaluate the current program me
    | .opp            => eval n me opponent opponent -- Evaluate the opponent program opponent
    | .sim p q        => -- Simulate p against q, then run the resulting program.
        let p' := p.subst me opponent
        let q' := q.subst me opponent
        eval n p' q' p'
    | .ite b a p q    => do -- Evaluate the guard b; if it returns a, run p, else run q.
        let r ← eval n me opponent b
        if r == a then eval n me opponent p else eval n me opponent q
    | .search k φ p q => -- Evaluate the guard formula φ using the oracle; if it returns true, run p, else run q.
        if proofSearch k (φ.subst me opponent)
          then eval n me opponent p
          else eval n me opponent q

-- Run eval with the program as its own body, and the opponent as the opponent.
noncomputable def play (fuel : Nat) (me opponent : Prog) : Option Action :=
  eval fuel me opponent me

-- The outcome of two programs playing each other with a given fuel.
noncomputable def outcome (fuel : Nat) (p q : Prog) : Option Outcome := do
  let a ← play fuel p q
  let b ← play fuel q p
  pure (a, b)

-- Semantic interpretation. "p plays a against q" means there exists
-- some fuel under which the evaluator halts with `some a`.  This
-- fuel-existential avoids baking a specific budget into semantics.
def Formula.interp : Formula → Prop
  | .plays p q a => ∃ n, play n p q = some a  -- "p plays a against q" means there exists some fuel n under which p plays a against q
  | .impl φ ψ    => φ.interp → ψ.interp
  | .neg φ       => ¬ φ.interp

end PDNew
