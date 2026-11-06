import ArithS.Box.BewV
import ArithS.Theory.TheoryAct

/-!
# ArithS.Notation — the paper's symbols, in Lean

One place for the notation every user-facing statement of PA-`S'` is written in, so that a cell, a
Löb statement or a floor dichotomy reads the way the paper prints it. The three layers of the paper's
Table "Proof layers", in this package:

| layer | the paper writes | here |
|---|---|---|
| 0. programs | `□_k φ` (an agent MENTIONS provability) | the sentence `□[k] φ`, i.e. `LenBox TAct k φ` — a formula of arithmetic, Δ₁ (`Box/BewV.lean`) |
| 1. `S'` | `⊢_k φ` (`φ` IS derivable at length `≤ k`) | the SAME sentence, read in ℕ: `LenBox TAct k ⌜φ⌝` |
| 2. Lean | `⊨ φ` (`φ` holds) and prose | `ℕ ⊧ₘ φ` (Foundation's `Models`), and `TAct ⊢ φ` for derivability with no length bound |

In the engine, layers 0 and 1 were two different objects (`Formula.box` and `Pf`); here they are the
internal and the external reading of one sentence — the point of an arithmetized system.

Usage: `open ArithS` (or work inside `namespace ArithS`); the notation is scoped.
-/

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping

/-- `□[k] φ`: the code `φ` has a `TAct`-proof of length `≤ k` — `LenBox TAct k φ`, the paper's `□_k φ`.
At a meta budget `k : ℕ` and a quoted sentence `⌜σ⌝` this is the paper's `⊢_k σ`. -/
scoped notation:max "□[" k "] " φ:max => LenBox TAct k φ

end ArithS
