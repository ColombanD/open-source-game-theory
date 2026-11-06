import ArithS.Audit.Theory
import ArithS.Audit.Length
import ArithS.Audit.Box
import ArithS.Audit.Agents
import ArithS.Audit.Eval
import ArithS.Audit.Loeb
import ArithS.Audit.Necessitation
import ArithS.Audit.Bridge
import ArithS.Audit.Cells
import ArithS.Audit.Outcome
import ArithS.Audit.Tau

/-!
# ArithS.Audit — the axiom census of the arithmetized layer

Every headline theorem of tiers T1 and T2, with `#print axioms`. Building this module (it is
the last import of `ArithS.lean`) prints the census; each line must read
`[propext, Classical.choice, Quot.sound]` — Lean's three standard axioms and nothing else.
The `example`s FAIL TO COMPILE if any of these theorems disappears or changes its name,
so the census is also a freshness check for the paper's claims.

Since 2026-09-28 the prints live in nine per-layer files, `ArithS/Audit/{Theory, Length, Box,
Agents, Eval, Loeb, Necessitation, Bridge, Cells, Outcome, Tau}.lean` (each with its own minimal import list; the
comment blocks moved verbatim with their prints), and this module only imports them. The three
audit-file modules `Audit/RedCellAudit`, `Audit/RedCellUnsound`, `Audit/RedCellInstance` keep their
own prints, as do `Eval/Det` and `Agents/FitBox`; the census is every `#print axioms` the build runs.
-/
