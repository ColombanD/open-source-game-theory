import ArithS.Basic
import ArithS.Notation
import ArithS.Readings
import ArithS.Cells.RedCell
import ArithS.Theory.LangAct
import ArithS.Theory.Sound
import ArithS.Theory.Symmetry
import ArithS.Theory.TheoryAct
import ArithS.Theory.Transpose
import ArithS.Length.DerivationLength
import ArithS.Length.Length
import ArithS.Length.MetaLength
import ArithS.Length.ProofLength
import ArithS.Length.Proper
import ArithS.Length.SequentLength
import ArithS.Box.Bew
import ArithS.Box.BewV
import ArithS.Box.Cut
import ArithS.Box.CutV
import ArithS.Box.ProperBound
import ArithS.Agents.BinNumeral
import ArithS.Agents.Code
import ArithS.Agents.SysTemplate
import ArithS.Agents.CodeTerm
import ArithS.Agents.CodeTermAbs
import ArithS.Agents.Guard
import ArithS.Agents.Prog
import ArithS.Agents.RevalueTemplate
import ArithS.Agents.Subst
import ArithS.Agents.SysClose
import ArithS.Agents.SubstTemplate
import ArithS.Agents.Template
import ArithS.Eval.Eval
import ArithS.Eval.EvalN
import ArithS.Eval.Fixpoint
import ArithS.Eval.SimTest
import ArithS.Eval.TauCheck

/-!
# ArithS.Core — the trusted base as ONE lake target (`lake build ArithSCore`)

The definitions a reader accepts by eye (`README.md` §2, `Tour.lean`), the theorems about them in the same
five folders, the notation, the ℕ readings, and the red cell — the one result whose proof needs nothing but
this tier. `scripts/check_tiers.py` verifies that no module here imports anything outside this list.
-/
