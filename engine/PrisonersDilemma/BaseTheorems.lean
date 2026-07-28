import PrisonersDilemma.Base.Asymptotics
import PrisonersDilemma.Base.AtomCerts
import PrisonersDilemma.Base.Soundness
import PrisonersDilemma.Base.Exclusion
import PrisonersDilemma.Base.Closure
import PrisonersDilemma.Base.Loeb

/-!
# BaseTheorems — umbrella for the `Base/` meta-theorem layer

Split 2026-07-09 into `Base/Asymptotics` (log₂ arithmetic, absorbed `SizeLemmas`),
`Base/AtomCerts` (constructive atom certificates), `Base/Soundness` (`sound_upto`,
`Pf_sound`), `Base/Exclusion` (the transparency census — negative results), and
`Base/Loeb` (`bloeb_engine`, `pblt_engine`, the mutual engines).
All names still live in `PD.BaseTheorems` (arithmetic in `PD`); importing this module
is equivalent to the old monolith.
-/
