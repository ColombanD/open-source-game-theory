/-!
# Spike B findings (2026-08-13)

**Purpose.** This is "Spike B" of the Def-5 Route-A go/no-go (see
`PrisonersDilemma/Research/Notes/DEF5_SYS_BINDER_ROADMAP.md`). The real engine has a
mutually-inductive `Prog` language and plans to add a mutual-fixpoint binder `.sys`
with system-reference `.selfIdx`. This spike tests, at toy scale, whether that design
survives Lean's equation compiler. The engine's prior extension (`.tsearch`) hit these
landmines: the equation compiler silently compiled an enlarged mutual `subst` by
well-founded recursion (killing definitional unfolding / `rfl`), an inner `match` in an
eval arm broke equation generation, and the `induction` tactic refuses
mutually-inductive members (must use `cases` or equation-style recursion).

**KILL CRITERION for Route A at this gate:** the closer `sysClose` and `eval` cannot be
kept structurally recursive with definitional unfolding.

## Findings

(a) **`sysClose` stayed structural WITHOUT any annotation.** The mutual
    `sysClose`/`sysCloseL` pair over the mutual `MProg`/`MProgList` block was compiled
    by structural recursion automatically (both `rfl` tests on `sysClose` pass, which
    requires definitional unfolding; no `termination_by` needed). The explicit
    `termination_by structural p` / `structural l` annotations below are kept as a
    guard against silent regression to well-founded recursion — they compile fine.

(b) **`eval` is structural on FUEL — but only after threading fuel through `evalL`.**
    The naive shape (`evalL n (cons p rest)` calling `eval n p` at the SAME fuel) is
    not structural (n is not a subterm of n), and the equation compiler would silently
    fall back to well-founded recursion on the lexicographic (fuel, sizeOf) measure —
    which kills `rfl`. The fix: `evalL` consumes one unit of fuel per `cons`
    (`evalL (n+1) (.cons p rest)` calls `eval n p` / `evalL n rest`), making BOTH
    functions structural on their Nat fuel argument (`termination_by structural n`
    annotations compile, and all four `rfl` tests below pass, including
    `eval 100 loopSys = none` — the kernel unfolds 100 fuel steps without trouble).
    Engine takeaway: when `.sys` lands, the guard-list evaluator must charge fuel per
    list element, exactly as `.tsearch`'s stepwise peel already does.

(c) **The inner `match` in the `sys` eval arm caused NO equation-generation problem**
    here: `match defs.get? i with | some p => eval n (sysClose defs p) | none => none`
    compiled directly, structurally, with `rfl` intact. The tsearch "inner match"
    landmine did not reproduce at this scale (the recursion is on the OUTER fuel
    argument, which the inner match does not scrutinize — likely why it is benign).
    No nested-pattern workaround was needed.

(d) **Proof style for `sysClose_closed`: a `mutual theorem` block written
    equation-style (pattern-matching on the `MProg`/`MProgList` argument, term-mode
    recursion, `termination_by structural`) worked on the first attempt.** Case
    analysis via patterns replaces the `induction` tactic (which refuses mutual
    inductives); the impossible `.selfIdx` case closes with `nomatch h` (the
    hypothesis reduces definitionally to `false = true`), and the `.cons` case splits
    `&&` with `simpa`. No manual recursor (`MProg.rec`) and no simp-with-equation-lemmas
    contortion was required.

(e) **VERDICT — equation-compiler gate: PASS.** Both `sysClose` and `eval` are
    structurally recursive with full definitional unfolding (all `rfl` tests pass),
    the shadowing convention for the inner-`.sys` binder is a one-line non-descending
    arm, and mutual proofs over the type are ergonomic in equation style. The one
    binding design constraint discovered: fuel must be threaded through the mutual
    list evaluator (finding b).
-/

namespace MiniSys

/-! ## 1. The language -/

mutual
inductive MProg where
  | act     : Bool → MProg                 -- constant play
  | flip    : MProg → MProg                -- play the negation of what p plays
  | same    : MProg → MProg                -- play what p plays
  | vote    : MProgList → MProg            -- plays true iff EVERY member plays true
  | sys     : MProgList → Nat → MProg      -- i-th component of a mutually-recursive system
  | selfIdx : Nat → MProg                  -- reference to system component j
  deriving Repr
inductive MProgList where
  | nil  : MProgList
  | cons : MProg → MProgList → MProgList
  deriving Repr
end

/-! ## 2. List lookup -/

def MProgList.get? : MProgList → Nat → Option MProg
  | .nil,         _     => none
  | .cons p _,    0     => some p
  | .cons _ rest, n + 1 => rest.get? n

/-! ## 3. The closer (mutual STRUCTURAL recursion on the program) -/

mutual
def sysClose (defs : MProgList) : MProg → MProg
  | .act b     => .act b
  | .flip p    => .flip (sysClose defs p)
  | .same p    => .same (sysClose defs p)
  | .vote l    => .vote (sysCloseL defs l)
  | .sys dl i  => .sys dl i   -- inner .sys is a BINDER: its selfIdx refs are shadowed; do NOT descend
  | .selfIdx j => .sys defs j
  termination_by structural p => p

def sysCloseL (defs : MProgList) : MProgList → MProgList
  | .nil         => .nil
  | .cons p rest => .cons (sysClose defs p) (sysCloseL defs rest)
  termination_by structural l => l
end

/-! ## 4. The fuelled evaluator (mutual, STRUCTURAL on the fuel).

`evalL` must consume fuel per `cons` — keeping the fuel constant across the list
traversal makes the mutual pair non-structural (see header finding (b)). -/

mutual
def eval : Nat → MProg → Option Bool
  | 0,     _          => none
  | _ + 1, .act b     => some b
  | n + 1, .flip p    => (eval n p).map (!·)
  | n + 1, .same p    => eval n p
  | n + 1, .vote l    => evalL n l
  | n + 1, .sys defs i =>
      match defs.get? i with
      | some p => eval n (sysClose defs p)
      | none   => none
  | _ + 1, .selfIdx _ => none   -- unbound system reference
  termination_by structural n => n

def evalL : Nat → MProgList → Option Bool
  | _,     .nil         => some true
  | 0,     .cons _ _    => none
  | n + 1, .cons p rest => do
      let b  ← eval n p
      let bs ← evalL n rest
      some (b && bs)
  termination_by structural n => n
end

/-! ## 5. Demos and the DEFEQ tests (the actual point of the spike) -/

def groundedSys : MProgList := .cons (.same (.selfIdx 1)) (.cons (.act true) .nil)
def loopSys     : MProgList := .cons (.flip (.selfIdx 1)) (.cons (.same (.selfIdx 0)) .nil)
def voteSys     : MProgList := .cons (.vote (.cons (.selfIdx 1) (.cons (.act true) .nil))) (.cons (.act true) .nil)

#eval eval 5 (.sys groundedSys 0)    -- expect: some true
#eval eval 100 (.sys loopSys 0)      -- expect: none (semantic loop, fuel-grounded)
#eval eval 6 (.sys voteSys 0)        -- expect: some true

-- THE KEY TEST: definitional unfolding of the mutual structural evaluator.
example : eval 5 (.sys groundedSys 0) = some true := rfl
example : eval 100 (.sys loopSys 0) = none := rfl
example : sysClose groundedSys (.selfIdx 1) = .sys groundedSys 1 := rfl
example : sysClose groundedSys (.sys loopSys 0) = .sys loopSys 0 := rfl  -- shadowing convention

/-! ## 6. Proof ergonomics on the mutual type -/

mutual
/-- `true` iff no `.selfIdx` occurs outside an inner `.sys` (mirror `sysClose`'s traversal). -/
def closed : MProg → Bool
  | .act _     => true
  | .flip p    => closed p
  | .same p    => closed p
  | .vote l    => closedL l
  | .sys _ _   => true      -- binder: do not descend
  | .selfIdx _ => false
  termination_by structural p => p

def closedL : MProgList → Bool
  | .nil         => true
  | .cons p rest => closed p && closedL rest
  termination_by structural l => l
end

mutual
theorem sysClose_closed (defs : MProgList) : (p : MProg) → closed p = true → sysClose defs p = p
  | .act _,     _ => rfl
  | .flip p,    h => congrArg MProg.flip (sysClose_closed defs p h)
  | .same p,    h => congrArg MProg.same (sysClose_closed defs p h)
  | .vote l,    h => congrArg MProg.vote (sysCloseL_closed defs l h)
  | .sys _ _,   _ => rfl
  | .selfIdx _, h => nomatch h
  termination_by structural p => p

theorem sysCloseL_closed (defs : MProgList) : (l : MProgList) → closedL l = true → sysCloseL defs l = l
  | .nil,         _ => rfl
  | .cons p rest, h => by
      have hh : (closed p && closedL rest) = true := h
      have h' : closed p = true ∧ closedL rest = true := by simpa using hh
      show MProgList.cons (sysClose defs p) (sysCloseL defs rest) = MProgList.cons p rest
      rw [sysClose_closed defs p h'.1, sysCloseL_closed defs rest h'.2]
  termination_by structural l => l
end

end MiniSys
