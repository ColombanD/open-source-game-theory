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
    -- Weighted-threshold ACTION vote: PEEL the entries in list order. An entry fires
    -- iff its closed instance PLAYS `C`; firing subtracts its weight from the residual
    -- threshold (truncated); residual 0 commits to `p` WITHOUT consulting the remaining
    -- entries; exhausting the list with residual > 0 commits to `q`.
    --
    -- The entry runs in its own `.bot`-framed closed frame — literally the evaluator
    -- twin of the probe atom `.plays (.bot I) (.bot I) .C`, so a `Pf`/interp fact about
    -- `probe I` IS a fact about this entry (the `.sim` arm is the precedent for entering
    -- an inner frame inside the fuel monad; `.bot` unwraps with one fuel step, binding
    -- any `.self` inside `I` to `I` itself, which is what the quine instances need).
    -- A non-terminating entry makes the whole vote `none` — a tau player is total
    -- exactly when its entries are.
    --
    -- (Two arms with nested patterns for the LIST — NOT an inner `match gs` — so
    -- per-arm equation lemmas generate, as for `.tsearch`. The entry's RESULT, by
    -- contrast, is matched explicitly rather than bound with `do`: a `do`-bind here
    -- blocks equation-lemma generation for the arm entirely (`rw [eval]` then fails
    -- with "failed to generate equality theorems for match expression"), which is why
    -- the `.ite` arm's `do` has no unfolding lemmas either. With the explicit match,
    -- all four `eval_tvote_*` lemmas below close by a single `rw`.)
    | .tvote .nil θ p q =>
        if θ = 0 then eval n me opponent p else eval n me opponent q
    | .tvote (.cons w I rest) θ p q =>
        if θ = 0 then eval n me opponent p
        else match eval n (.bot I) (.bot I) I with
          | some Action.C => eval n me opponent (.tvote rest (θ - w) p q)
          | some Action.D => eval n me opponent (.tvote rest θ p q)
          | none          => none
    -- The mutual-fixpoint binder: LAZY unfold — close ONE level of system reference
    -- per fuel tick (`sysClose` replaces `.selfIdx j ↦ .sys defs j`), then continue
    -- in the SAME me/opponent frame. Repeated unfolding is paid by fuel exactly as
    -- `.self` re-entry is; an out-of-range index (or a dangling `.selfIdx` outside
    -- any system) fails like fuel exhaustion. A genuine semantic loop therefore
    -- yields `none` rather than diverging (Spike B's `loopSys` test).
    | .sys defs i =>
        match defs.get? i with
        | some p => eval n me opponent (p.sysClose defs)
        | none   => none
    | .selfIdx _ => none

/-! ### `.tvote` unfolding lemmas

The action-vote peel as rewrite equations. The `VoteList`
match inside the `eval` arm does not reduce syntactically when the list is a variable,
so every consumer rewrites with these rather than unfolding `eval`. -/

theorem eval_tvote_zero {me opponent : Prog} {v : VoteList} {p q : Prog} (n : Nat) :
    eval (n+1) me opponent (.tvote v 0 p q) = eval n me opponent p := by
  cases v with
  | nil => rw [eval, if_pos rfl]
  | cons w I rest => rw [eval, if_pos rfl]

theorem eval_tvote_nil {me opponent : Prog} {θ : Nat} {p q : Prog}
    (n : Nat) (hθ : θ ≠ 0) :
    eval (n+1) me opponent (.tvote .nil θ p q) = eval n me opponent q := by
  rw [eval, if_neg hθ]

/-- The entry PLAYED `C`: subtract its weight and continue. -/
theorem eval_tvote_cons_c {me opponent : Prog} {w θ : Nat} {I : Prog}
    {rest : VoteList} {p q : Prog} (n : Nat) (hθ : θ ≠ 0)
    (hI : eval n (.bot I) (.bot I) I = some Action.C) :
    eval (n+1) me opponent (.tvote (.cons w I rest) θ p q)
      = eval n me opponent (.tvote rest (θ - w) p q) := by
  rw [eval, if_neg hθ, hI]

/-- The entry PLAYED `D`: the threshold is unchanged. (`D` is the only non-`C`
    action — `Action` is binary, which is what makes the two cons lemmas exhaustive
    over terminating entries.) -/
theorem eval_tvote_cons_d {me opponent : Prog} {w θ : Nat} {I : Prog}
    {rest : VoteList} {p q : Prog} (n : Nat) (hθ : θ ≠ 0)
    (hI : eval n (.bot I) (.bot I) I = some Action.D) :
    eval (n+1) me opponent (.tvote (.cons w I rest) θ p q)
      = eval n me opponent (.tvote rest θ p q) := by
  rw [eval, if_neg hθ, hI]

/-- A non-terminating entry sinks the whole vote. -/
theorem eval_tvote_cons_none {me opponent : Prog} {w θ : Nat} {I : Prog}
    {rest : VoteList} {p q : Prog} (n : Nat) (hθ : θ ≠ 0)
    (hI : eval n (.bot I) (.bot I) I = none) :
    eval (n+1) me opponent (.tvote (.cons w I rest) θ p q) = none := by
  rw [eval, if_neg hθ, hI]

/-! ### `.sys` unfolding lemmas

Same service as the `.tvote` quintet: the `Option` match on `defs.get? i` does not
reduce under `rw [eval]` when the list is a variable, so consumers rewrite with
these. -/

theorem eval_sys_some {me opponent : Prog} {defs : ProgList} {i : Nat} {p : Prog}
    (n : Nat) (hget : defs.get? i = some p) :
    eval (n+1) me opponent (.sys defs i) = eval n me opponent (p.sysClose defs) := by
  rw [eval, hget]

theorem eval_sys_none {me opponent : Prog} {defs : ProgList} {i : Nat}
    (n : Nat) (hget : defs.get? i = none) :
    eval (n+1) me opponent (.sys defs i) = none := by
  rw [eval, hget]

theorem eval_selfIdx {me opponent : Prog} {j : Nat} (n : Nat) :
    eval (n+1) me opponent (.selfIdx j) = none := by
  rw [eval]

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
