import ArithS.Outcome.Matrix.CIMCIC
import ArithS.Outcome.Matrix.CooperateBot
import ArithS.Outcome.Matrix.CupodBot
import ArithS.Outcome.Matrix.CupodTrollBot
import ArithS.Outcome.Matrix.DBot
import ArithS.Outcome.Matrix.DIMCID
import ArithS.Outcome.Matrix.DIMDID
import ArithS.Outcome.Matrix.DefectBot
import ArithS.Outcome.Matrix.DupocBot
import ArithS.Outcome.Matrix.DupocTrollBot
import ArithS.Outcome.Matrix.EBot
import ArithS.Outcome.Matrix.GuardianBot
import ArithS.Outcome.Matrix.JustBot
import ArithS.Outcome.Matrix.MirrorBot
import ArithS.Outcome.Matrix.OBot
import ArithS.Outcome.Matrix.PrudentBot
import ArithS.Outcome.Matrix.TitForTatBot
import ArithS.Outcome.Matrix.WaryBot
import ArithS.Outcome.Floors
import ArithS.Outcome.Lint

/-!
# ArithS.Outcome.Check — the build-time census of the PA-`S'` matrix (`lake build ArithSOutcomeCheck`)

Its own lake library root (in `defaultTargets`), not imported by `ArithS.lean`: Lean requires imports to
precede commands, and a command in the root index would break the next module appended there. `lake build`
builds this target, so the validator, the two censuses and the paper-zoo coverage run on every build.
The exporter (`Outcome/Export.lean`, `lake exe export_sprime_outcomes`) imports THIS module, so what it writes
has passed these gates. Design note: `docs/notes/SPRIME_SOURCE_OF_TRUTH.md` §1.1.
-/

-- Every declaration named like a cell under `Outcome/Matrix/` is `@[outcomeA]`-tagged and on the
-- `OutcomeSpecA` template with a name that agrees with its statement.
#check_outcomeA_theorems "ArithS/Outcome/Matrix"

-- Every `dich_<L>_vs_<R>` of `Cells/FloorDichotomy.lean` has its engine-side half `outcome_<L>_vs_<R>_floor`
-- (`Outcome/Floors.lean`), `@[floorA]`-tagged and on the `FloorSpecA` template.
#check_floorA_theorems "ArithS/Cells/FloorDichotomy.lean"
-- The `S'`-only floor of DupocTrollBot (2026-10-13) lives beside its cells, not in `FloorDichotomy.lean`.
#check_floorA_theorems "ArithS/Cells/DupocTrollBot.lean"
-- The three `S'`-only floors of DIMDID (2026-10-13) live beside its cells too.
#check_floorA_theorems "ArithS/Cells/Dimdid.lean"

-- Every unordered pair of the 12 paper base bots is a cell or a floor (§0.4 of the design note).
#check_sprime_coverage
