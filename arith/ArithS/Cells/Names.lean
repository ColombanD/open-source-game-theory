import ArithS.Cells.DupocMirror
import ArithS.Cells.JustBot
import ArithS.Cells.DIMCID
import ArithS.Cells.PrudentMirror
import ArithS.Cells.CIMCIC
import ArithS.Cells.SearchFree
import ArithS.Cells.JustSlot
import ArithS.Cells.SimSlot
import ArithS.Cells.SoundnessCells
import ArithS.Cells.PositiveCells
import ArithS.Cells.KhatCells
import ArithS.Cells.FlipCells
import ArithS.Cells.DimcidFlips

/-!
# ArithS.Cells.Names — the ALIAS layer: one naming scheme over the cell theorems

Consolidation stage 7 (`Research/Notes/ROUTE_B_CELLS_MAP.md`, 2026-09-24). This module contains ONLY
`alias <new> := <old>` lines: every original name and statement stays where it is (the refactor's gate),
and every cell gets a second name under ONE scheme —

  `<method>_<L>_vs_<R>[_<suffix>]`

`method ∈ {sf, pa, snd, pos, loeb, khat}` is the PROOF METHOD (search-free transfer, PA-completeness,
soundness/else-branch, positive/found without Löb, bounded Löb, the `k̂`-chain); `L`/`R` are the exact
head symbols of the statement — the ENGINE constructor (`DIMCID`, `DupocBot`, `TitForTatBot`, …) when the
statement has `pcode (X k)`, the ARITH code name (`Dupoc`, `Cupod`, `Dimcid`, `Cimcic`, `Just`, `Just7`,
`Prudent`, `PrudentT`, `Mirror`, `botDupoc`, `CupodTroll7`) when it has the ℕ-code, `botCB`/`botDB`/
`botMirror` for the frozen `.bot` probes; `suffix ∈ {∅, _guard, _guards, _guardOf, _notFound, _engine,
_core, _of_nec, _core_of_nec}` (`_core` = the play AND the found guard in one statement, `_of_nec` = the
version still premised on `BoundedInnerNec d`, `_core_of_nec` = its core). Examples:
`dupoc_mirror_coop_unconditional` → `loeb_Dupoc_vs_Mirror`, `dupoc_mirror_coop` →
`loeb_Dupoc_vs_Mirror_of_nec`, `dimcid_cupod_find_guards_unconditional` → `loeb_Dimcid_vs_Cupod_guards`,
`cimcic_self_coop` → `pos_Cimcic_vs_Cimcic`, `snd_CupodBot_vs_DBot` → `pos_CupodBot_vs_DBot` (its proof
needs a positive sub-fact). The helper renames at the end: `hopp_*`/`hme_*` → `desc_*`/`descT_*`,
`hX_self` → `hX_dimcid`, `hX_bot` → `hX_botDupoc`, `pJJ_guard_V` → `pJJ_guards_V`, `pJD_boxes_V` →
`pJD_guards_V`, `*_find_guards*` → `*_finds_guards*`, `pcode_X'` → `pcode_X_search`, `mirror_copies_V` →
`mirror_copies2_V`. (`TFTV`/`TTFT` are handled by the `rfl` bridges of `Common/Bots`.) The old names remain
primary until the gate is relaxed; no `#print axioms` here (an alias adds no axioms).
-/

namespace ArithS

/-! ### The Löb cells on the arith codes (`Cells/DupocMirror`, `JustBot`, `DIMCID`, `CIMCIC`, `JustSlot`,
`PrudentMirror`; `dupoc_self_coop_unconditional` from `Necessitation/Package`) -/

alias loeb_Dupoc_vs_Dupoc := dupoc_self_coop_unconditional

alias loeb_Dupoc_vs_Mirror := dupoc_mirror_coop_unconditional
alias loeb_Dupoc_vs_Mirror_of_nec := dupoc_mirror_coop
alias loeb_Dupoc_vs_Mirror_core_of_nec := dupoc_mirror_cell_core
alias loeb_Dupoc_vs_Mirror_guard := dupoc_finds_guard_vs_mirror_unconditional
alias loeb_Dupoc_vs_Mirror_guard_of_nec := dupoc_finds_guard_vs_mirror
alias loeb_Cupod_vs_Mirror := cupod_mirror_defect_unconditional
alias loeb_Cupod_vs_Mirror_of_nec := cupod_mirror_defect
alias loeb_Cupod_vs_Mirror_guard := cupod_finds_guard_vs_mirror_unconditional
alias loeb_Cupod_vs_Mirror_guard_of_nec := cupod_finds_guard_vs_mirror

alias loeb_botDupoc_vs_botDupoc := botDupoc_self_coop_unconditional
alias loeb_botDupoc_vs_botDupoc_of_nec := botDupoc_self_coop
alias loeb_botDupoc_vs_botDupoc_core_of_nec := botDupoc_cell_core
alias loeb_botDupoc_vs_botDupoc_guard := botDupoc_finds_guard_unconditional
alias loeb_botDupoc_vs_botDupoc_guard_of_nec := botDupoc_finds_guard
alias loeb_botCupod_vs_botCupod := botCupod_self_defect_unconditional
alias loeb_botCupod_vs_botCupod_of_nec := botCupod_self_defect

alias loeb_Just_vs_Mirror := just_mirror_coop_unconditional
alias loeb_Just_vs_Mirror_of_nec := just_mirror_coop
alias loeb_Just_vs_Mirror_core_of_nec := just_mirror_cell_core
alias loeb_Just_vs_Mirror_guard := just_finds_guard_vs_mirror_unconditional
alias loeb_Just_vs_Mirror_guard_of_nec := just_finds_guard_vs_mirror
alias loeb_botDupoc_vs_Mirror := botDupoc_mirror_coop_unconditional
alias loeb_botDupoc_vs_Mirror_of_nec := botDupoc_mirror_coop

alias loeb_Dimcid_vs_Dimcid := dimcid_self_defect_unconditional
alias loeb_Dimcid_vs_Dimcid_of_nec := dimcid_self_defect
alias loeb_Dimcid_vs_Dimcid_core_of_nec := dimcid_self_cell_core
alias loeb_Dimcid_vs_Dimcid_guard := dimcid_finds_guard_unconditional
alias loeb_Dimcid_vs_Dimcid_guard_of_nec := dimcid_finds_guard
alias loeb_DIMCID_vs_DIMCID_guardOf := dimcid_finds_guardOf_unconditional
alias loeb_Dimcid_vs_Mirror := dimcid_mirror_defect_unconditional
alias loeb_Dimcid_vs_Mirror_of_nec := dimcid_mirror_defect
alias loeb_Dimcid_vs_Mirror_core_of_nec := dimcid_mirror_cell_core
alias loeb_Dimcid_vs_Mirror_guard := dimcid_finds_guard_vs_mirror_unconditional
alias loeb_Dimcid_vs_Mirror_guard_of_nec := dimcid_finds_guard_vs_mirror
alias loeb_Dimcid_vs_Cupod := dimcid_cupod_defect_unconditional
alias loeb_Dimcid_vs_Cupod_of_nec := dimcid_cupod_defect
alias loeb_Dimcid_vs_Cupod_core_of_nec := dimcid_cupod_cell_core
alias loeb_Dimcid_vs_Cupod_guards := dimcid_cupod_find_guards_unconditional
alias loeb_Dimcid_vs_Cupod_guards_of_nec := dimcid_cupod_find_guards

alias loeb_Cimcic_vs_Dupoc := cimcic_dupoc_coop_unconditional
alias loeb_Cimcic_vs_Dupoc_of_nec := cimcic_dupoc_coop
alias loeb_Cimcic_vs_Dupoc_core_of_nec := cimcic_dupoc_cell_core
alias loeb_Cimcic_vs_Dupoc_guards := cimcic_dupoc_find_guards_unconditional
alias loeb_Cimcic_vs_Dupoc_guards_of_nec := cimcic_dupoc_find_guards
alias loeb_Cimcic_vs_Mirror := cimcic_mirror_coop_unconditional
alias loeb_Cimcic_vs_Mirror_of_nec := cimcic_mirror_coop
alias loeb_Cimcic_vs_Mirror_core_of_nec := cimcic_mirror_cell_core
alias loeb_Cimcic_vs_Mirror_guard := cimcic_finds_guard_vs_mirror_unconditional
alias loeb_Cimcic_vs_Mirror_guard_of_nec := cimcic_finds_guard_vs_mirror
alias pos_Cimcic_vs_Cimcic := cimcic_self_coop
alias pos_Cimcic_vs_Cimcic_guard := cimcic_self_finds_guard
alias pos_CIMCIC_vs_CIMCIC_guardOf := cimcic_finds_guardOf_self

alias loeb_Just7_vs_Mirror := just7_mirror_coop_unconditional
alias loeb_Just7_vs_Just7 := just7_self_coop_unconditional
alias loeb_Just7_vs_Just7_of_nec := just7_self_coop
alias loeb_Just7_vs_Just7_core_of_nec := just7_self_cell_core
alias loeb_Just7_vs_Just7_guard := just7_finds_guard_vs_self_unconditional
alias loeb_Just7_vs_Dupoc := just7_dupoc_coop_unconditional
alias loeb_Just7_vs_Dupoc_of_nec := just7_dupoc_coop
alias loeb_Just7_vs_Dupoc_core_of_nec := just7_dupoc_cell_core
alias loeb_Just7_vs_Dupoc_guards := just7_dupoc_find_guards_unconditional
alias loeb_Cimcic_vs_Just7 := cimcic_just7_coop_unconditional
alias loeb_Cimcic_vs_Just7_of_nec := cimcic_just7_coop
alias loeb_Cimcic_vs_Just7_core_of_nec := cimcic_just7_cell_core
alias loeb_Cimcic_vs_Just7_guards := cimcic_just7_find_guards_unconditional

alias loeb_Prudent_vs_Mirror := prudent_mirror_coop_unconditional
alias loeb_Prudent_vs_Mirror_of_nec := prudent_mirror_coop
alias loeb_Prudent_vs_Mirror_core_of_nec := prudent_mirror_cell_core
alias loeb_Prudent_vs_Mirror_guards := prudent_finds_guards_vs_mirror_unconditional
alias loeb_Prudent_vs_Mirror_guards_of_nec := prudent_finds_guards_vs_mirror
alias loeb_PrudentT_vs_Mirror := prudentT_mirror_defect_unconditional
alias loeb_PrudentT_vs_Mirror_of_nec := prudentT_mirror_defect

/-! ### The flip cells on the engine codes (`Cells/FlipCells`, `Cells/DimcidFlips`): DIMCID's halves
(`_core` = defection AND found guard), the found guards, the refuted guards -/

alias loeb_DIMCID_vs_botCB := dimcid_vs_botCB_defects
alias loeb_DIMCID_vs_botDB := dimcid_vs_botDB_defects
alias loeb_DIMCID_vs_botMirror := dimcid_vs_botMirror_defects
alias loeb_DIMCID_vs_Dupoc := dimcid_vs_dupocV_defects
alias loeb_DIMCID_vs_botDupocBot := dimcid_vs_botDupocBot_defects
alias loeb_DIMCID_vs_botDupoc := dimcid_vs_botDupocV_defects
alias loeb_DIMCID_vs_Just7 := dimcid_vs_just7_defects
alias loeb_DIMCID_vs_CupodTroll7 := dimcid_vs_troll7_defects
alias loeb_DIMCID_vs_TitForTatBot_core := dimcid_vs_TFT_defects
alias loeb_DIMCID_vs_GuardianBot_core := dimcid_vs_Guardian_defects
alias loeb_DIMCID_vs_DBot_core := dimcid_vs_DBot_defects
alias loeb_DIMCID_vs_EBot_core := dimcid_vs_EBot_defects
alias loeb_DIMCID_vs_OBot_core := dimcid_vs_OBot_defects
alias loeb_DIMCID_vs_DupocBot_core := dimcid_vs_DupocBot_defects
alias loeb_DIMCID_vs_PrudentBot_core := dimcid_vs_PrudentBot_defects
alias loeb_DIMCID_vs_CIMCIC_core := dimcid_vs_CIMCIC_defects
alias loeb_DIMCID_vs_TitForTatBot_guard := dimcid_finds_guard_vs_TFT
alias loeb_DIMCID_vs_GuardianBot_guard := dimcid_finds_guard_vs_Guardian
alias loeb_DIMCID_vs_CupodTroll7_guard := dimcid_finds_guard_vs_troll7
alias loeb_DIMCID_vs_DBot_guard := dimcid_finds_guard_vs_DBot
alias loeb_DIMCID_vs_EBot_guard := dimcid_finds_guard_vs_EBot
alias loeb_DIMCID_vs_OBot_guard := dimcid_finds_guard_vs_OBot
alias loeb_DIMCID_vs_DupocBot_guard := dimcid_finds_guard_vs_DupocBot
alias loeb_DIMCID_vs_Just7_guard := dimcid_finds_guard_vs_just7
alias loeb_DIMCID_vs_PrudentBot_guard := dimcid_finds_guard_vs_PrudentBot
alias loeb_DIMCID_vs_CIMCIC_guard := dimcid_finds_guard_vs_CIMCIC
alias snd_DupocBot_vs_DIMCID_notFound := dupoc_guard_vs_DIMCID_not_found
alias snd_CIMCIC_vs_DIMCID_notFound := cimcic_guard_vs_DIMCID_not_found
alias snd_JustBot_vs_DIMCID_engine := just_engine_vs_DIMCID_defects
alias snd_CupodTroll7_vs_DIMCID := troll7_vs_DIMCID
alias loeb_WaryBot_vs_MirrorBot_core := wary_vs_mirror_core
alias loeb_WaryBot_vs_MirrorBot_guard := wary_finds_guard_vs_Mirror
alias loeb_WaryBot_vs_WaryBot_core := wary_vs_wary_core
alias loeb_WaryBot_vs_WaryBot_guard := wary_finds_guard_vs_self

/-! ### The `k̂`-chain and the probe sub-plays (`Cells/KhatCells`, `PositiveCells`, `SoundnessCells`) -/

alias khat_CupodTrollBot_vs_CupodBot_guard := troll_finds_guard_vs_cupod
alias pos_JustBot_vs_botCB := just_botCB_found
alias pos_CupodBot_vs_botDB := cupod_vs_botDB_found
alias pos_WaryBot_vs_botDB := wary_vs_botDB_found
alias pos_CIMCIC_vs_botCB := cimcic_vs_botCB_found
alias pos_GuardianBot_vs_botDB := guardian_vs_botDB_eventually
alias snd_CIMCIC_vs_botDB := cimcic_vs_botDB
alias snd_GuardianBot_vs_botCB := guardian_vs_botCB
alias snd_CupodBot_vs_botCB := cupod_vs_botCB
alias snd_DupocBot_vs_botDB := dupoc_vs_botDB
alias snd_CupodTrollBot_vs_botCB := ctb_vs_botCB
alias snd_CupodTrollBot_vs_botDB := ctb_vs_botDB
alias snd_WaryBot_vs_botCB := wary_vs_botCB
alias snd_PrudentBot_vs_botDB := prudent_vs_botDB
alias snd_PrudentBot_vs_botCB := prudent_vs_botCB
alias snd_botDupocBot_vs_botDB := botDupoc_vs_botDB

/-! ### Method prefixes that did not match the proof method (the six large-`k` SND-class cells that need
a positive sub-fact are POS) -/

alias pos_CupodBot_vs_DBot := snd_CupodBot_vs_DBot
alias pos_CupodBot_vs_EBot := snd_CupodBot_vs_EBot
alias pos_WaryBot_vs_DBot := snd_WaryBot_vs_DBot
alias pos_WaryBot_vs_EBot := snd_WaryBot_vs_EBot
alias pos_GuardianBot_vs_EBot := snd_GuardianBot_vs_EBot
alias pos_GuardianBot_vs_OBot := snd_GuardianBot_vs_OBot

/-! ### Helper renames -/

alias desc_dimcid := hopp_self
alias descT_dimcid := hopp'_self
alias desc_mirror := hopp_mirror
alias descT_mirror := hopp'_mirror
alias desc_cupod := hopp_cupod
alias descT_cupod := hopp'_cupod
alias desc_dupoc := hopp_dupoc
alias descT_dupoc := hopp'_dupoc
alias desc_cimcic := hopp_cimcic
alias descT_cimcic := hopp'_cimcic
alias desc_just7 := hopp_just7
alias descT_just7 := hopp'_just7
alias desc_troll7 := hopp_troll7
alias descT_troll7 := hopp'_troll7
alias desc_SV := hme_SV
alias descT_SV := hme_SVT
alias desc_botSV := hme_botSV
alias descT_botSV := hme_botSVT
alias desc_botDupoc := hme_bot
alias descT_botDupoc := hme'_bot
alias desc_WT := hme_WT
alias hX_dimcid := hX_self
alias hU_dimcid := hU_self
alias hW_dimcid := hW_self
alias hX_botDupoc := hX_bot
alias hU_botDupoc := hU_bot
alias hW_botDupoc := hW_bot
alias pJJ_guards_V := pJJ_guard_V
alias pJD_guards_V := pJD_boxes_V
alias dimcid_cupod_finds_guards := dimcid_cupod_find_guards
alias dimcid_cupod_finds_guards_unconditional := dimcid_cupod_find_guards_unconditional
alias cimcic_dupoc_finds_guards := cimcic_dupoc_find_guards
alias cimcic_dupoc_finds_guards_unconditional := cimcic_dupoc_find_guards_unconditional
alias just7_dupoc_finds_guards_unconditional := just7_dupoc_find_guards_unconditional
alias cimcic_just7_finds_guards_unconditional := cimcic_just7_find_guards_unconditional
alias pcode_DupocBot_search := pcode_DupocBot'
alias pcode_PrudentBot_search := pcode_PrudentBot'
alias pcode_CIMCIC_search := pcode_CIMCIC'
alias pcode_DIMCID_search := pcode_DIMCID'
alias mirror_copies2_V := mirror_copies_V

end ArithS
