import ArithS.Agents.Fit
import ArithS.Agents.FitBox
import ArithS.Eval.Det
import ArithS.Bridge.Agent
import ArithS.Bridge.AgentConverse
import ArithS.Bridge.Core.Sound
import ArithS.Bridge.Core.Tr
import ArithS.Bridge.EngineBridge
import ArithS.Bridge.Inst
import ArithS.Bridge.Neg

/-!
# ArithS.Frozen — estimates and the frozen T2 bridge (`lake build ArithSFrozen`)

Numeric estimates that later tiers cite (`Agents/Fit`, `Agents/FitBox`: the guard fits its budget) and the
rule bridge `S → S'` (`Bridge/`, `Eval/Det`), frozen by decision (`MERGE_CROSSROAD.md`). Imports only the core
tier.
-/
