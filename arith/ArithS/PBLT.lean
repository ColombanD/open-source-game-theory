import ArithS.Loeb.Diag
import ArithS.Loeb.InstV
import ArithS.Loeb.NumeralFacts
import ArithS.Agents.Instance
import ArithS.Agents.InstanceV
import ArithS.Eval.Transparency
import ArithS.Assembly.Cell
import ArithS.Assembly.Family
import ArithS.Assembly.Prep
import ArithS.Assembly.Uniform
import ArithS.Necessitation.Package
import ArithS.Necessitation.ClosedNec

/-!
# ArithS.PBLT — the Löb layer: the diagonal lemma, the family-parametric bounded Löb theorem, U10 (`lake build ArithSLoeb`)

`Loeb/` (the parametric diagonal lemma, the instance operator), Dupoc's guard as the `k`-instance of one
formula and its truth equation in every model (`Agents/Instance*`, `Eval/Transparency`), `Assembly/`
(`LoebSound`, `family_found`) and the two STATEMENT files of the U10 construction (`Necessitation/Package`,
`Necessitation/ClosedNec`), which pull the ~96k-line construction in transitively. Imports the core and
frozen tiers only.
-/
