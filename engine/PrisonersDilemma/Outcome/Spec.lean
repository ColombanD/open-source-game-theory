import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics

/-!
# The canonical outcome-theorem statement

Every outcome theorem in `Theorems/<L>/vs_<R>.lean` states `OutcomeSpec …`, and the
`@[outcome]` linter (`Outcome/Lint.lean`) rejects anything else. The point is that the
matrix extractor reads an ELABORATED TYPE instead of regex-matching source text: before
this, the "proved under a side condition" (†) flag was inferred from the heuristic
"does a binder name start with `h`", which silently mis-classified at least one cell.

**This module deliberately does NOT `import Lean`** — the ~159 theorem files import it, and
none of them should pay for metaprogramming. The attribute lives in `Outcome/Attr.lean`.
-/

namespace PD

/-- How a bot's proof-search budget is quantified. Read off the elaborated type by the
    linter and exported to the app's outcome matrix.

    There is deliberately no `witness` (`∃ k`) constructor: an `∃ k` witness is always a
    COST THRESHOLD (`atom_cost 2`, a literal `0`, …) and the guard side-conditions are
    inequalities, so every such theorem generalizes to `.eventual`. -/
inductive BudgetRegime
  | /-- Both bots are closed `Prog`s — no budget parameter at all. -/
    nobudget
  | /-- Holds at EVERY budget `k`. -/
    universal
  | /-- Holds at every SUFFICIENTLY LARGE budget: `∃ k₂, ∀ k > k₂`. -/
    eventual
  deriving DecidableEq, Repr, Inhabited

/-- The fuel side of a statement. Fuel is ALWAYS cofinite (`∀ fuel, … (fuel + pad)`);
    `Theorems.outcome_mono_le` makes the `∃ fuel` form equivalent, so unlike the budget
    there is no fuel *axis* — just a `pad`.

    There is deliberately no existential-fuel template either (one existed until
    2026-08-27). `Formula.interp` reads `.plays p q a` as `∃ n, play n p q = some a`, so a
    play obtained from `Pf_sound` comes with an unbounded fuel — but that witness never
    needs bounding: fuel is consumed per program node while the budget `k` is a numeral
    inside `.search`, so every zoo match is DETERMINED at a structural pad independent of
    `k`, and fuel determinism pins the value there (`Base/Helpers.outcome_at_of_ex`,
    `play_at_of_ex`, with the totality lemmas `play_search_const_total`,
    `play_ite_total`, `play_sim_opp_self_total`). The Löbian cells carry pads 2–6 like
    every other cell. -/
abbrev OutcomeAt (pad : Nat) (L R : Prog) (r : Option Outcome) : Prop :=
  ∀ fuel, outcome (fuel + pad) L R = r

/-- As `OutcomeAt`, but each fuel is guarded by `side`.

    `side` takes BOTH the budget and the fuel because some genuine side conditions couple
    them — `atom_cost (fuel + 2) ≤ k` is satisfiable for each `k` at small fuel but false
    for large fuel, so it can be neither hoisted out of the statement (that would make it
    universally quantified and FALSE, silently rendering the theorem vacuous) nor folded
    into a `BudgetRegime`. -/
abbrev OutcomeAtIf (pad : Nat) (side : Nat → Prop) (L R : Prog) (r : Option Outcome) : Prop :=
  ∀ fuel, side fuel → outcome (fuel + pad) L R = r

/-- **THE canonical outcome-theorem statement.**

    `L`/`R` are the two bots as functions of the budget, which is what makes all three bot
    arities uniform — a closed bot is `fun _ => Bot`, a plain one is `Bot`, and a staggered
    or two-budget one is `fun k => Bot (2*k+64) k`. That last case is why the arguments are
    functions rather than `Prog`s: STAGGERING becomes a structural property of the lambda
    (a bare pass-through or not) instead of something a regex has to sniff out of source. -/
abbrev OutcomeSpec (b : BudgetRegime) (pad : Nat)
    (L R : Nat → Prog) (r : Option Outcome) : Prop :=
  match b with
  | .nobudget  => OutcomeAt pad (L 0) (R 0) r
  | .universal => ∀ k, OutcomeAt pad (L k) (R k) r
  | .eventual  => ∃ k₂, ∀ k, k₂ < k → OutcomeAt pad (L k) (R k) r

/-- **The GUARDED template** — an outcome that holds only under a side condition on the
    budget and the fuel. `side k fuel` is where a genuine caveat lives, and it is what the
    linter reads to flag the cell as daggered: a real, machine-checked reason, not the
    `h`-prefixed binder name the old extractor guessed from.

    Prefer plain `OutcomeSpec` wherever the condition is really a budget FLOOR — that is
    what `.eventual` means, and expressing it as the regime removes the dagger honestly
    (see `outcome_CupodBot_vs_OBot`). -/
abbrev OutcomeSpecIf (b : BudgetRegime) (pad : Nat) (side : Nat → Nat → Prop)
    (L R : Nat → Prog) (r : Option Outcome) : Prop :=
  match b with
  | .nobudget  => OutcomeAtIf pad (side 0) (L 0) (R 0) r
  | .universal => ∀ k, OutcomeAtIf pad (side k) (L k) (R k) r
  | .eventual  => ∃ k₂, ∀ k, k₂ < k → OutcomeAtIf pad (side k) (L k) (R k) r

end PD
