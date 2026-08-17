import PrisonersDilemma.Program
import PrisonersDilemma.ProofSystem

namespace PD

/-!
# Game dynamics

The fuelled evaluator `eval`, the entry points `play`/`outcome`, and the
denotational semantics `Formula.interp`. This layer sits on top of the proof
system in `ProofSystem.lean`: `eval`'s `.search` guard consults `proofSearch`,
and `interp`'s box clause is `Pf` (the unified proof system `S`).
-/

-- The fuelled evaluator. The `.search` guard consults the oracle `proofSearch`
-- (defined in ProofSystem.lean, which this file imports). `me`/`opponent` are
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
    -- Weighted-threshold search: PEEL the guards in list order. A firing guard
    -- subtracts its weight from the residual threshold (truncated); residual 0
    -- commits to `p` WITHOUT consulting the remaining guards (the then
    -- short-circuit); exhausting the list with residual > 0 commits to `q`.
    -- Each peel step re-enters `eval` on a structurally smaller `.tsearch`, so fuel
    -- is charged per peel: a full consultation of the node costs `|gs| + 1` fuel
    -- before the branch runs. Guards are closed against the current frame at each
    -- consultation, exactly like `.search`. (Two arms with nested patterns — NOT an
    -- inner `match` — so per-arm equation lemmas generate and `rw [eval]` works.)
    | .tsearch _ .nil θ p q =>
        if θ = 0 then eval n me opponent p else eval n me opponent q
    | .tsearch k (.cons w φ rest) θ p q =>
        if θ = 0 then eval n me opponent p
        else if proofSearch k (φ.subst me opponent)
          then eval n me opponent (.tsearch k rest (θ - w) p q)
          else eval n me opponent (.tsearch k rest θ p q)

/-! ### `.tsearch` unfolding lemmas
The peel steps as rewrite equations. The `GuardList` match inside the `eval` arm does
not reduce syntactically under `rw [eval]` when the list is a variable, so every
consumer (fuel-monotonicity, the soundness arms, the tau-layer play lemmas) rewrites
with these four instead of unfolding `eval` directly. -/

theorem eval_tsearch_zero {me opponent : Prog} {k : Nat} {gs : GuardList} {p q : Prog}
    (n : Nat) :
    eval (n+1) me opponent (.tsearch k gs 0 p q) = eval n me opponent p := by
  cases gs with
  | nil => rw [eval, if_pos rfl]
  | cons w φ rest => rw [eval, if_pos rfl]

theorem eval_tsearch_nil {me opponent : Prog} {k θ : Nat} {p q : Prog}
    (n : Nat) (hθ : θ ≠ 0) :
    eval (n+1) me opponent (.tsearch k .nil θ p q) = eval n me opponent q := by
  rw [eval, if_neg hθ]

theorem eval_tsearch_cons_t {me opponent : Prog} {k w θ : Nat} {φ : Formula}
    {rest : GuardList} {p q : Prog} (n : Nat) (hθ : θ ≠ 0)
    (hg : proofSearch k (φ.subst me opponent) = true) :
    eval (n+1) me opponent (.tsearch k (.cons w φ rest) θ p q)
      = eval n me opponent (.tsearch k rest (θ - w) p q) := by
  rw [eval, if_neg hθ, if_pos hg]

theorem eval_tsearch_cons_f {me opponent : Prog} {k w θ : Nat} {φ : Formula}
    {rest : GuardList} {p q : Prog} (n : Nat) (hθ : θ ≠ 0)
    (hg : proofSearch k (φ.subst me opponent) = false) :
    eval (n+1) me opponent (.tsearch k (.cons w φ rest) θ p q)
      = eval n me opponent (.tsearch k rest θ p q) := by
  rw [eval, if_neg hθ, if_neg (by simp [hg])]

noncomputable def play (fuel : Nat) (me opponent : Prog) : Option Action :=
  eval fuel me opponent me

noncomputable def outcome (fuel : Nat) (p q : Prog) : Option Outcome := do
  let a ← play fuel p q
  let b ← play fuel q p
  some (a, b)

-- Denotational semantics: maps a syntactic `Formula` to a Lean proposition
-- (truth). `.plays` is fuel-existential so theorems need not commit to a budget;
-- the box clause is `Pf n φ` (the proof system's provability predicate, not a
-- separate oracle).
def Formula.interp : Formula → Prop
  | .plays p q a => ∃ n, play n p q = some a
  | .impl φ ψ    => φ.interp → ψ.interp
  | .neg φ       => ¬ φ.interp
  | .box n φ     => Pf n φ
  | .eq p q      => p = q
  | .diag g φ    => Pf g (.diag g φ) → φ.interp
  -- `.diag g φ` IS the Löb-fixpoint sentence for target `φ` at box budget `g`: its meaning is
  -- `interp (□_g (.diag g φ) → φ)` BY DEFINITION (legal: recursion descends only into `φ`; `Pf`
  -- does not recurse through `interp`). Same design pattern as `.box n φ ↦ Pf n φ`; the
  -- meta-justification is the Reflection layer's DERIVED diagonal (INTERNALIZATION_ROADMAP.md I0).

end PD
