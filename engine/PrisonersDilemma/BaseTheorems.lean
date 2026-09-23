import PrisonersDilemma.Base.Asymptotics
import PrisonersDilemma.Base.AtomCerts
import PrisonersDilemma.Base.ValuationSoundness
import PrisonersDilemma.Base.Soundness
import PrisonersDilemma.Base.Exclusion
import PrisonersDilemma.Base.Closure
import PrisonersDilemma.Base.Loeb
import PrisonersDilemma.Base.Transpose
import PrisonersDilemma.Base.BoundedGL

/-!
# BaseTheorems — umbrella for the `Base/` meta-theorem layer

Split 2026-07-09 into `Base/Asymptotics` (log₂ arithmetic, absorbed `SizeLemmas`),
`Base/AtomCerts` (constructive atom certificates), `Base/Soundness` (`sound_upto`,
`Pf_sound`), `Base/Exclusion` (the transparency census — negative results), and
`Base/Loeb` (`bloeb_engine`, `pblt_engine`, the mutual engines).
Added 2026-08-20: `Base/Transpose` (the C/D transposition τ̂ and the same-budget
`Pf.transpose` invariance theorem — its names live in `PD`, like the syntax layer).
Added 2026-08-27: `Base/BoundedGL` (the abstract bounded-GL interface `BoundedGL`;
`pfBoundedGL` is the `Pf` model, and `mutual_loeb`/`bloeb_engine`/`pblt_engine` are its
instances by `rfl`).
All names still live in `PD.BaseTheorems` (arithmetic in `PD`); importing this module
is equivalent to the old monolith.
-/
