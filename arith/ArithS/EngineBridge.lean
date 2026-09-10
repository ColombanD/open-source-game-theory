import PrisonersDilemma.ProofSystem
import PrisonersDilemma.Dynamics
import ArithS.RedCell

/-!
# ArithS.EngineBridge — the engine and the arithmetized `S` in one workspace (M3)

A smoke module only: it imports the engine (`PD`, a path dependency of this package since
milestone M3) next to the arithmetized red cell and checks that the two coexist under one
toolchain and one mathlib. No theorem lives here yet — the transfer theorem
(`Research/Notes/ARITHMETIZED_S_ROADMAP.md`, M3) is the first real content.

Name clashes under `open PD` together with the ArithS opens (`FFL FFL.FirstOrder Arithmetic
Bootstrapping`): exactly ONE atomic name is declared on both sides — `Formula`
(`PD.Formula` vs `FFL.FirstOrder.Formula` / `…Arithmetic.Bootstrapping.Formula`), so it must
be written `PD.Formula` (it happens to resolve to `PD` in a bare binder only because both
Foundation versions take arguments). `Action`, `Prog`, `Pf`, `eval`, `play`, `outcome` are
unique to `PD`; `subst` unqualified is Foundation's (`Bootstrapping.subst`; the engine's are
`Prog.subst`/`Formula.subst`); `size`, `numeral`, `interp` have no top-level resolution; the
corner quotes `⌜ ⌝` are Foundation's alone.
-/

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PD

#check @PD.Pf
#check @PD.Formula.interp
#check @ArithS.red_cell

example : PD.Action := .C

/-- `Formula` is ambiguous under these opens; the qualified head with dot-notation body is
the working spelling. -/
example (φ : PD.Formula) : PD.Formula.size φ = φ.size := rfl

/-- the Foundation side still elaborates with `PD` open -/
example (k : ℕ) : Dupoc k = pSearch k (⌜GtmplA 0⌝ : ℕ) (pConst 0) (pConst 1) := rfl

end ArithS
