import PrisonersDilemma.Program
import PrisonersDilemma.Derivation

namespace PD

/-!
# Game dynamics

The fuelled evaluator `eval`, the entry points `play`/`outcome`, and the
denotational semantics `Formula.interp`. This layer sits on top of the proof
system in `Derivation.lean`: `eval`'s `.search` guard consults `proofSearch`,
and `interp`'s box clause is `Provable`.
-/

-- The fuelled evaluator. The `.search` guard consults the oracle `proofSearch`
-- (defined in Derivation.lean, which this file imports). `me`/`opponent` are
-- the fixed players; `body` is the subterm being reduced; `Option` lets runs
-- fail when fuel is exhausted, keeping `eval` finite despite the unbounded
-- self-reference available in `Prog`.
noncomputable def eval : Nat → (me opponent body : Prog) → Option Action
  | 0,   _,  _,   _    => none
  | n+1, me, opponent, body => match body with
    | .const a        => some a
    | .self           => eval n me opponent me
    | .opp            => eval n me opponent opponent
    | .bot p          => eval n me opponent p
    | .sim p q        =>
        let p' := p.subst me opponent
        let q' := q.subst me opponent
        eval n p' q' p'
    | .ite b a p q    => do
        let r ← eval n me opponent b
        if r == a then eval n me opponent p else eval n me opponent q
    | .search k φ p q =>
        if proofSearch k (φ.subst me opponent)
          then eval n me opponent p
          else eval n me opponent q

noncomputable def play (fuel : Nat) (me opponent : Prog) : Option Action :=
  eval fuel me opponent me

noncomputable def outcome (fuel : Nat) (p q : Prog) : Option Outcome := do
  let a ← play fuel p q
  let b ← play fuel q p
  some (a, b)

-- Denotational semantics: maps a syntactic `Formula` to a Lean proposition
-- (truth). `.plays` is fuel-existential so theorems need not commit to a budget;
-- the box clause is `Provable n φ` (the proof system's provability predicate,
-- not a separate oracle).
def Formula.interp : Formula → Prop
  | .plays p q a => ∃ n, play n p q = some a
  | .impl φ ψ    => φ.interp → ψ.interp
  | .neg φ       => ¬ φ.interp
  | .box n φ     => Provable n φ

end PD
