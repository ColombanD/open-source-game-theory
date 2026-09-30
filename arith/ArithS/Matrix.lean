import ArithS.Cells.CIMCIC
import ArithS.Cells.Common.Bots
import ArithS.Cells.Common.Families
import ArithS.Cells.Common.Khat
import ArithS.Cells.Common.Probers
import ArithS.Cells.Common.Syntax
import ArithS.Cells.Common.Templates
import ArithS.Cells.DIMCID
import ArithS.Cells.DimcidFlips
import ArithS.Cells.DupocMirror
import ArithS.Cells.DupocEngine
import ArithS.Cells.DimcidEngine
import ArithS.Cells.CimcicEngine
import ArithS.Cells.FlipCells
import ArithS.Cells.FloorDichotomy
import ArithS.Cells.FloorVerdicts
import ArithS.Cells.JustBot
import ArithS.Cells.JustSlot
import ArithS.Cells.KhatCells
import ArithS.Cells.Names
import ArithS.Cells.PositiveCells
import ArithS.Cells.PrudentLoose
import ArithS.Cells.PrudentMirror
import ArithS.Cells.RedCellEngine
import ArithS.Cells.SearchFree
import ArithS.Cells.TauMember
import ArithS.Cells.SimSlot
import ArithS.Cells.SoundnessCells
import ArithS.Outcome.Matrix.CIMCIC
import ArithS.Outcome.Matrix.CooperateBot
import ArithS.Outcome.Matrix.CupodBot
import ArithS.Outcome.Matrix.CupodTrollBot
import ArithS.Outcome.Matrix.DBot
import ArithS.Outcome.Matrix.DIMCID
import ArithS.Outcome.Matrix.DefectBot
import ArithS.Outcome.Matrix.DupocBot
import ArithS.Outcome.Matrix.EBot
import ArithS.Outcome.Matrix.GuardianBot
import ArithS.Outcome.Matrix.JustBot
import ArithS.Outcome.Matrix.MirrorBot
import ArithS.Outcome.Matrix.OBot
import ArithS.Outcome.Matrix.PrudentBot
import ArithS.Outcome.Matrix.TitForTatBot
import ArithS.Outcome.Matrix.WaryBot
import ArithS.Outcome.Spec
import ArithS.Outcome.Attr
import ArithS.Outcome.Floor
import ArithS.Outcome.Floors
import ArithS.Outcome.Lint

/-!
# ArithS.Matrix — the results: every cell of PA-`S'` (`lake build ArithSMatrix`)

`Outcome/Matrix/<L>.lean` states the cells in the engine's vocabulary; `Cells/` carries the mathematics.

**Where a proof lives (the header rule of `Cells/`).** UNIFORM methods are filed BY METHOD — `SearchFree`
(transfer at the engine's fuel), `SoundnessCells` (a false guard is never found), `PositiveCells` and
`KhatCells` (a `TAct`-theorem's instance fits the budget), `FlipCells` (where `S'` contradicts the engine),
`FloorVerdicts`/`FloorDichotomy` (the floors). LÖB cells are filed BY BOT — `DupocMirror`, `JustBot`,
`JustSlot`, `CIMCIC`, `DIMCID`, `DimcidFlips`, `PrudentMirror`, `PrudentLoose` — because each needs its own
description layer and conjunction family. `Common/` holds what several files share (bot codes, templates,
probers, families, the `k̂`-chain); `Names` the deprecated aliases. Theorem heads name the method
(`sf_`, `snd_`, `pos_`, `khat_`, `loeb_`, `floor_`, `dich_`); the cell name is the `outcome_` one.

Imports the core, frozen and Löb tiers; of `Necessitation/` only `Package` and `ClosedNec`
(`scripts/check_tiers.py`).
-/
