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
import ArithS.Cells.FloorVerdicts
import ArithS.Cells.FloorDichotomy

/-!
# ArithS.Cells.Names — the DEPRECATION layer: the old names of the cell theorems

Consolidation stage 7 (`Research/Notes/ROUTE_B_CELLS_MAP.md`, 2026-09-24) introduced ONE naming scheme for the cell
theorems as an alias layer over the original names; on 2026-09-27 the scheme was made PRIMARY (the gate — every
original name and statement byte-identical — was relaxed): every declaration was renamed in its home file, the
statements unchanged (verified by a header diff modulo the rename map: 0 changed), and this module now contains
ONLY `@[deprecated <new> (since := "2026-09-27")] alias <old> := <new>` lines, so the old names keep working with a
warning. The scheme —

  `<method>_<L>_vs_<R>[_<suffix>]`

`method ∈ {sf, pa, snd, pos, loeb, khat, floor, dich}` is the PROOF METHOD (search-free transfer, PA-completeness,
soundness/else-branch, positive/found without Löb, bounded Löb, the `k̂`-chain, the settled floor half, the
hypothesis-free floor dichotomy); `L`/`R` are the exact head symbols of the statement — the ENGINE constructor
(`DIMCID`, `DupocBot`, `TitForTatBot`, …) when the statement has `progCode (X k)`, the ARITH code name (`Dupoc`,
`Cupod`, `Dimcid`, `Cimcic`, `Just`, `Just7`, `Prudent`, `PrudentT`, `Mirror`, `botDupoc`, `CupodTroll7`) when it
has the ℕ-code, `botCB`/`botDB`/`botMirror` for the frozen `.bot` probes; `suffix ∈ {∅, _guard, _guards, _guardOf,
_notFound, _engine, _core, _of_nec, _core_of_nec, _left, _right, _true}` (`_core` = the play AND the found guard in
one statement, `_of_nec` = the version still premised on `BoundedInnerNec d`, `_core_of_nec` = its core;
`_left`/`_right`/`_true` are `Cells/FloorVerdicts`' settled halves and true guards). Examples (old → new):
`dupoc_mirror_coop_unconditional` → `loeb_Dupoc_vs_Mirror`, `dupoc_mirror_coop` → `loeb_Dupoc_vs_Mirror_of_nec`,
`dimcid_cupod_find_guards_unconditional` → `loeb_Dimcid_vs_Cupod_guards`, `cimcic_self_coop` →
`pos_Cimcic_vs_Cimcic`, `snd_CupodBot_vs_DBot` → `pos_CupodBot_vs_DBot` (its proof needs a positive sub-fact).
The helper renames at the end: `hopp_*`/`hme_*` → `desc_*`/`descT_*`, `hX_self` → `hX_dimcid`, `hX_bot` →
`hX_botDupoc`, `pJJ_guard_V` → `pJJ_guards_V`, `pJD_boxes_V` → `pJD_guards_V`, `progCode_X'` → `progCode_X_search`,
`mirror_copies_V` → `mirror_copies2_V`; the `*_finds_guards*` spellings of the 2026-09-24 layer are kept as plain
aliases of the scheme names. (`TFTV`/`TTFT` are handled by the `rfl` bridges of `Common/Bots`.) The one name NOT
flipped: `dupoc_self_coop` (`Necessitation/Package`, the headline theorem — a Necessitation statement,
left as is; `loeb_Dupoc_vs_Dupoc` stays a plain alias of it). No `#print axioms` here (an alias adds no axioms);
`Audit.lean` prints the new names.

Since 2026-10-02 no MATRIX cell is on an arith twin code (`Cells/JustEngine.lean`, `Cells/CupodTrollEngine.lean`
re-ran the last seven on `progCode`). Three theorems named after the engine bots are still STATED on a twin —
`loeb_DIMCID_vs_JustBot` (`Just7`), `loeb_DIMCID_vs_CupodTrollBot` and `khat_CupodTrollBot_vs_CupodBot`
(`CupodTroll7`) — and keep their names; their engine-code counterparts are `loeb_DIMCID_vs_JustBot_engine`,
`loeb_DIMCID_vs_CupodTrollBot_engine` and `khat_CupodBot_vs_CupodTrollBot` (the pair in the other orientation,
with CupodTroll's half `khat_CupodTrollBot_vs_CupodBot_engine`).
-/

namespace ArithS

/-! ### The Löb cells on the arith codes (`Cells/DupocMirror`, `JustBot`, `DIMCID`, `CIMCIC`, `JustSlot`,
`PrudentMirror`; `dupoc_self_coop` from `Necessitation/Package`) -/

/-- Not flipped: the headline theorem of `Necessitation/Package` keeps its name. -/
alias loeb_Dupoc_vs_Dupoc := dupoc_self_coop

@[deprecated loeb_Dupoc_vs_Mirror (since := "2026-09-27")] alias dupoc_mirror_coop_unconditional := loeb_Dupoc_vs_Mirror
@[deprecated loeb_Dupoc_vs_Mirror_of_nec (since := "2026-09-27")] alias dupoc_mirror_coop := loeb_Dupoc_vs_Mirror_of_nec
@[deprecated loeb_Dupoc_vs_Mirror_core_of_nec (since := "2026-09-27")] alias dupoc_mirror_cell_core := loeb_Dupoc_vs_Mirror_core_of_nec
@[deprecated loeb_Dupoc_vs_Mirror_guard (since := "2026-09-27")] alias dupoc_finds_guard_vs_mirror_unconditional := loeb_Dupoc_vs_Mirror_guard
@[deprecated loeb_Dupoc_vs_Mirror_guard_of_nec (since := "2026-09-27")] alias dupoc_finds_guard_vs_mirror := loeb_Dupoc_vs_Mirror_guard_of_nec
@[deprecated loeb_Cupod_vs_Mirror (since := "2026-09-27")] alias cupod_mirror_defect_unconditional := loeb_Cupod_vs_Mirror
@[deprecated loeb_Cupod_vs_Mirror_of_nec (since := "2026-09-27")] alias cupod_mirror_defect := loeb_Cupod_vs_Mirror_of_nec
@[deprecated loeb_Cupod_vs_Mirror_guard (since := "2026-09-27")] alias cupod_finds_guard_vs_mirror_unconditional := loeb_Cupod_vs_Mirror_guard
@[deprecated loeb_Cupod_vs_Mirror_guard_of_nec (since := "2026-09-27")] alias cupod_finds_guard_vs_mirror := loeb_Cupod_vs_Mirror_guard_of_nec

@[deprecated loeb_botDupoc_vs_botDupoc (since := "2026-09-27")] alias botDupoc_self_coop_unconditional := loeb_botDupoc_vs_botDupoc
@[deprecated loeb_botDupoc_vs_botDupoc_of_nec (since := "2026-09-27")] alias botDupoc_self_coop := loeb_botDupoc_vs_botDupoc_of_nec
@[deprecated loeb_botDupoc_vs_botDupoc_core_of_nec (since := "2026-09-27")] alias botDupoc_cell_core := loeb_botDupoc_vs_botDupoc_core_of_nec
@[deprecated loeb_botDupoc_vs_botDupoc_guard (since := "2026-09-27")] alias botDupoc_finds_guard_unconditional := loeb_botDupoc_vs_botDupoc_guard
@[deprecated loeb_botDupoc_vs_botDupoc_guard_of_nec (since := "2026-09-27")] alias botDupoc_finds_guard := loeb_botDupoc_vs_botDupoc_guard_of_nec
@[deprecated loeb_botCupod_vs_botCupod (since := "2026-09-27")] alias botCupod_self_defect_unconditional := loeb_botCupod_vs_botCupod
@[deprecated loeb_botCupod_vs_botCupod_of_nec (since := "2026-09-27")] alias botCupod_self_defect := loeb_botCupod_vs_botCupod_of_nec

@[deprecated loeb_Just_vs_Mirror (since := "2026-09-27")] alias just_mirror_coop_unconditional := loeb_Just_vs_Mirror
@[deprecated loeb_Just_vs_Mirror_of_nec (since := "2026-09-27")] alias just_mirror_coop := loeb_Just_vs_Mirror_of_nec
@[deprecated loeb_Just_vs_Mirror_core_of_nec (since := "2026-09-27")] alias just_mirror_cell_core := loeb_Just_vs_Mirror_core_of_nec
@[deprecated loeb_Just_vs_Mirror_guard (since := "2026-09-27")] alias just_finds_guard_vs_mirror_unconditional := loeb_Just_vs_Mirror_guard
@[deprecated loeb_Just_vs_Mirror_guard_of_nec (since := "2026-09-27")] alias just_finds_guard_vs_mirror := loeb_Just_vs_Mirror_guard_of_nec
@[deprecated loeb_botDupoc_vs_Mirror (since := "2026-09-27")] alias botDupoc_mirror_coop_unconditional := loeb_botDupoc_vs_Mirror
@[deprecated loeb_botDupoc_vs_Mirror_of_nec (since := "2026-09-27")] alias botDupoc_mirror_coop := loeb_botDupoc_vs_Mirror_of_nec

@[deprecated loeb_Dimcid_vs_Dimcid (since := "2026-09-27")] alias dimcid_self_defect_unconditional := loeb_Dimcid_vs_Dimcid
@[deprecated loeb_Dimcid_vs_Dimcid_of_nec (since := "2026-09-27")] alias dimcid_self_defect := loeb_Dimcid_vs_Dimcid_of_nec
@[deprecated loeb_Dimcid_vs_Dimcid_core_of_nec (since := "2026-09-27")] alias dimcid_self_cell_core := loeb_Dimcid_vs_Dimcid_core_of_nec
@[deprecated loeb_Dimcid_vs_Dimcid_guard (since := "2026-09-27")] alias dimcid_finds_guard_unconditional := loeb_Dimcid_vs_Dimcid_guard
@[deprecated loeb_Dimcid_vs_Dimcid_guard_of_nec (since := "2026-09-27")] alias dimcid_finds_guard := loeb_Dimcid_vs_Dimcid_guard_of_nec
@[deprecated loeb_DIMCID_vs_DIMCID_guardOf (since := "2026-09-27")] alias dimcid_finds_guardOf_unconditional := loeb_DIMCID_vs_DIMCID_guardOf
@[deprecated loeb_Dimcid_vs_Mirror (since := "2026-09-27")] alias dimcid_mirror_defect_unconditional := loeb_Dimcid_vs_Mirror
@[deprecated loeb_Dimcid_vs_Mirror_of_nec (since := "2026-09-27")] alias dimcid_mirror_defect := loeb_Dimcid_vs_Mirror_of_nec
@[deprecated loeb_Dimcid_vs_Mirror_core_of_nec (since := "2026-09-27")] alias dimcid_mirror_cell_core := loeb_Dimcid_vs_Mirror_core_of_nec
@[deprecated loeb_Dimcid_vs_Mirror_guard (since := "2026-09-27")] alias dimcid_finds_guard_vs_mirror_unconditional := loeb_Dimcid_vs_Mirror_guard
@[deprecated loeb_Dimcid_vs_Mirror_guard_of_nec (since := "2026-09-27")] alias dimcid_finds_guard_vs_mirror := loeb_Dimcid_vs_Mirror_guard_of_nec
@[deprecated loeb_Dimcid_vs_Cupod (since := "2026-09-27")] alias dimcid_cupod_defect_unconditional := loeb_Dimcid_vs_Cupod
@[deprecated loeb_Dimcid_vs_Cupod_of_nec (since := "2026-09-27")] alias dimcid_cupod_defect := loeb_Dimcid_vs_Cupod_of_nec
@[deprecated loeb_Dimcid_vs_Cupod_core_of_nec (since := "2026-09-27")] alias dimcid_cupod_cell_core := loeb_Dimcid_vs_Cupod_core_of_nec
@[deprecated loeb_Dimcid_vs_Cupod_guards (since := "2026-09-27")] alias dimcid_cupod_find_guards_unconditional := loeb_Dimcid_vs_Cupod_guards
@[deprecated loeb_Dimcid_vs_Cupod_guards_of_nec (since := "2026-09-27")] alias dimcid_cupod_find_guards := loeb_Dimcid_vs_Cupod_guards_of_nec

@[deprecated loeb_Cimcic_vs_Dupoc (since := "2026-09-27")] alias cimcic_dupoc_coop_unconditional := loeb_Cimcic_vs_Dupoc
@[deprecated loeb_Cimcic_vs_Dupoc_of_nec (since := "2026-09-27")] alias cimcic_dupoc_coop := loeb_Cimcic_vs_Dupoc_of_nec
@[deprecated loeb_Cimcic_vs_Dupoc_core_of_nec (since := "2026-09-27")] alias cimcic_dupoc_cell_core := loeb_Cimcic_vs_Dupoc_core_of_nec
@[deprecated loeb_Cimcic_vs_Dupoc_guards (since := "2026-09-27")] alias cimcic_dupoc_find_guards_unconditional := loeb_Cimcic_vs_Dupoc_guards
@[deprecated loeb_Cimcic_vs_Dupoc_guards_of_nec (since := "2026-09-27")] alias cimcic_dupoc_find_guards := loeb_Cimcic_vs_Dupoc_guards_of_nec
@[deprecated loeb_Cimcic_vs_Mirror (since := "2026-09-27")] alias cimcic_mirror_coop_unconditional := loeb_Cimcic_vs_Mirror
@[deprecated loeb_Cimcic_vs_Mirror_of_nec (since := "2026-09-27")] alias cimcic_mirror_coop := loeb_Cimcic_vs_Mirror_of_nec
@[deprecated loeb_Cimcic_vs_Mirror_core_of_nec (since := "2026-09-27")] alias cimcic_mirror_cell_core := loeb_Cimcic_vs_Mirror_core_of_nec
@[deprecated loeb_Cimcic_vs_Mirror_guard (since := "2026-09-27")] alias cimcic_finds_guard_vs_mirror_unconditional := loeb_Cimcic_vs_Mirror_guard
@[deprecated loeb_Cimcic_vs_Mirror_guard_of_nec (since := "2026-09-27")] alias cimcic_finds_guard_vs_mirror := loeb_Cimcic_vs_Mirror_guard_of_nec
@[deprecated pos_Cimcic_vs_Cimcic (since := "2026-09-27")] alias cimcic_self_coop := pos_Cimcic_vs_Cimcic
@[deprecated pos_Cimcic_vs_Cimcic_guard (since := "2026-09-27")] alias cimcic_self_finds_guard := pos_Cimcic_vs_Cimcic_guard
@[deprecated pos_CIMCIC_vs_CIMCIC_guardOf (since := "2026-09-27")] alias cimcic_finds_guardOf_self := pos_CIMCIC_vs_CIMCIC_guardOf

@[deprecated loeb_Just7_vs_Mirror (since := "2026-09-27")] alias just7_mirror_coop_unconditional := loeb_Just7_vs_Mirror
@[deprecated loeb_Just7_vs_Just7 (since := "2026-09-27")] alias just7_self_coop_unconditional := loeb_Just7_vs_Just7
@[deprecated loeb_Just7_vs_Just7_of_nec (since := "2026-09-27")] alias just7_self_coop := loeb_Just7_vs_Just7_of_nec
@[deprecated loeb_Just7_vs_Just7_core_of_nec (since := "2026-09-27")] alias just7_self_cell_core := loeb_Just7_vs_Just7_core_of_nec
@[deprecated loeb_Just7_vs_Just7_guard (since := "2026-09-27")] alias just7_finds_guard_vs_self_unconditional := loeb_Just7_vs_Just7_guard
@[deprecated loeb_Just7_vs_Dupoc (since := "2026-09-27")] alias just7_dupoc_coop_unconditional := loeb_Just7_vs_Dupoc
@[deprecated loeb_Just7_vs_Dupoc_of_nec (since := "2026-09-27")] alias just7_dupoc_coop := loeb_Just7_vs_Dupoc_of_nec
@[deprecated loeb_Just7_vs_Dupoc_core_of_nec (since := "2026-09-27")] alias just7_dupoc_cell_core := loeb_Just7_vs_Dupoc_core_of_nec
@[deprecated loeb_Just7_vs_Dupoc_guards (since := "2026-09-27")] alias just7_dupoc_find_guards_unconditional := loeb_Just7_vs_Dupoc_guards
@[deprecated loeb_Cimcic_vs_Just7 (since := "2026-09-27")] alias cimcic_just7_coop_unconditional := loeb_Cimcic_vs_Just7
@[deprecated loeb_Cimcic_vs_Just7_of_nec (since := "2026-09-27")] alias cimcic_just7_coop := loeb_Cimcic_vs_Just7_of_nec
@[deprecated loeb_Cimcic_vs_Just7_core_of_nec (since := "2026-09-27")] alias cimcic_just7_cell_core := loeb_Cimcic_vs_Just7_core_of_nec
@[deprecated loeb_Cimcic_vs_Just7_guards (since := "2026-09-27")] alias cimcic_just7_find_guards_unconditional := loeb_Cimcic_vs_Just7_guards

@[deprecated loeb_Prudent_vs_Mirror (since := "2026-09-27")] alias prudent_mirror_coop_unconditional := loeb_Prudent_vs_Mirror
@[deprecated loeb_Prudent_vs_Mirror_of_nec (since := "2026-09-27")] alias prudent_mirror_coop := loeb_Prudent_vs_Mirror_of_nec
@[deprecated loeb_Prudent_vs_Mirror_core_of_nec (since := "2026-09-27")] alias prudent_mirror_cell_core := loeb_Prudent_vs_Mirror_core_of_nec
@[deprecated loeb_Prudent_vs_Mirror_guards (since := "2026-09-27")] alias prudent_finds_guards_vs_mirror_unconditional := loeb_Prudent_vs_Mirror_guards
@[deprecated loeb_Prudent_vs_Mirror_guards_of_nec (since := "2026-09-27")] alias prudent_finds_guards_vs_mirror := loeb_Prudent_vs_Mirror_guards_of_nec
@[deprecated loeb_PrudentT_vs_Mirror (since := "2026-09-27")] alias prudentT_mirror_defect_unconditional := loeb_PrudentT_vs_Mirror
@[deprecated loeb_PrudentT_vs_Mirror_of_nec (since := "2026-09-27")] alias prudentT_mirror_defect := loeb_PrudentT_vs_Mirror_of_nec

/-! ### The flip cells on the engine codes (`Cells/FlipCells`, `Cells/DimcidFlips`): DIMCID's halves
(`_core` = defection AND found guard), the found guards, the refuted guards -/

@[deprecated loeb_DIMCID_vs_botCB (since := "2026-09-27")] alias dimcid_vs_botCB_defects := loeb_DIMCID_vs_botCB
@[deprecated loeb_DIMCID_vs_botDB (since := "2026-09-27")] alias dimcid_vs_botDB_defects := loeb_DIMCID_vs_botDB
@[deprecated loeb_DIMCID_vs_botMirror (since := "2026-09-27")] alias dimcid_vs_botMirror_defects := loeb_DIMCID_vs_botMirror
@[deprecated loeb_DIMCID_vs_Dupoc (since := "2026-09-27")] alias dimcid_vs_dupocV_defects := loeb_DIMCID_vs_Dupoc
@[deprecated loeb_DIMCID_vs_botDupocBot (since := "2026-09-27")] alias dimcid_vs_botDupocBot_defects := loeb_DIMCID_vs_botDupocBot
@[deprecated loeb_DIMCID_vs_botDupoc (since := "2026-09-27")] alias dimcid_vs_botDupocV_defects := loeb_DIMCID_vs_botDupoc
@[deprecated loeb_DIMCID_vs_Just7 (since := "2026-09-27")] alias dimcid_vs_just7_defects := loeb_DIMCID_vs_Just7
@[deprecated loeb_DIMCID_vs_CupodTroll7 (since := "2026-09-27")] alias dimcid_vs_troll7_defects := loeb_DIMCID_vs_CupodTroll7
@[deprecated loeb_DIMCID_vs_TitForTatBot_core (since := "2026-09-27")] alias dimcid_vs_TFT_defects := loeb_DIMCID_vs_TitForTatBot_core
@[deprecated loeb_DIMCID_vs_GuardianBot_core (since := "2026-09-27")] alias dimcid_vs_Guardian_defects := loeb_DIMCID_vs_GuardianBot_core
@[deprecated loeb_DIMCID_vs_DBot_core (since := "2026-09-27")] alias dimcid_vs_DBot_defects := loeb_DIMCID_vs_DBot_core
@[deprecated loeb_DIMCID_vs_EBot_core (since := "2026-09-27")] alias dimcid_vs_EBot_defects := loeb_DIMCID_vs_EBot_core
@[deprecated loeb_DIMCID_vs_OBot_core (since := "2026-09-27")] alias dimcid_vs_OBot_defects := loeb_DIMCID_vs_OBot_core
@[deprecated loeb_DIMCID_vs_DupocBot_core (since := "2026-09-27")] alias dimcid_vs_DupocBot_defects := loeb_DIMCID_vs_DupocBot_core
@[deprecated loeb_DIMCID_vs_PrudentBot_core (since := "2026-09-27")] alias dimcid_vs_PrudentBot_defects := loeb_DIMCID_vs_PrudentBot_core
@[deprecated loeb_DIMCID_vs_CIMCIC_core (since := "2026-09-27")] alias dimcid_vs_CIMCIC_defects := loeb_DIMCID_vs_CIMCIC_core
@[deprecated loeb_DIMCID_vs_TitForTatBot_guard (since := "2026-09-27")] alias dimcid_finds_guard_vs_TFT := loeb_DIMCID_vs_TitForTatBot_guard
@[deprecated loeb_DIMCID_vs_GuardianBot_guard (since := "2026-09-27")] alias dimcid_finds_guard_vs_Guardian := loeb_DIMCID_vs_GuardianBot_guard
@[deprecated loeb_DIMCID_vs_CupodTroll7_guard (since := "2026-09-27")] alias dimcid_finds_guard_vs_troll7 := loeb_DIMCID_vs_CupodTroll7_guard
@[deprecated loeb_DIMCID_vs_DBot_guard (since := "2026-09-27")] alias dimcid_finds_guard_vs_DBot := loeb_DIMCID_vs_DBot_guard
@[deprecated loeb_DIMCID_vs_EBot_guard (since := "2026-09-27")] alias dimcid_finds_guard_vs_EBot := loeb_DIMCID_vs_EBot_guard
@[deprecated loeb_DIMCID_vs_OBot_guard (since := "2026-09-27")] alias dimcid_finds_guard_vs_OBot := loeb_DIMCID_vs_OBot_guard
@[deprecated loeb_DIMCID_vs_DupocBot_guard (since := "2026-09-27")] alias dimcid_finds_guard_vs_DupocBot := loeb_DIMCID_vs_DupocBot_guard
@[deprecated loeb_DIMCID_vs_Just7_guard (since := "2026-09-27")] alias dimcid_finds_guard_vs_just7 := loeb_DIMCID_vs_Just7_guard
@[deprecated loeb_DIMCID_vs_PrudentBot_guard (since := "2026-09-27")] alias dimcid_finds_guard_vs_PrudentBot := loeb_DIMCID_vs_PrudentBot_guard
@[deprecated loeb_DIMCID_vs_CIMCIC_guard (since := "2026-09-27")] alias dimcid_finds_guard_vs_CIMCIC := loeb_DIMCID_vs_CIMCIC_guard
@[deprecated snd_DupocBot_vs_DIMCID_notFound (since := "2026-09-27")] alias dupoc_guard_vs_DIMCID_not_found := snd_DupocBot_vs_DIMCID_notFound
@[deprecated snd_CIMCIC_vs_DIMCID_notFound (since := "2026-09-27")] alias cimcic_guard_vs_DIMCID_not_found := snd_CIMCIC_vs_DIMCID_notFound
@[deprecated snd_JustBot_vs_DIMCID_engine (since := "2026-09-27")] alias just_engine_vs_DIMCID_defects := snd_JustBot_vs_DIMCID_engine
@[deprecated snd_CupodTroll7_vs_DIMCID (since := "2026-09-27")] alias troll7_vs_DIMCID := snd_CupodTroll7_vs_DIMCID
@[deprecated loeb_WaryBot_vs_MirrorBot_core (since := "2026-09-27")] alias wary_vs_mirror_core := loeb_WaryBot_vs_MirrorBot_core
@[deprecated loeb_WaryBot_vs_MirrorBot_guard (since := "2026-09-27")] alias wary_finds_guard_vs_Mirror := loeb_WaryBot_vs_MirrorBot_guard
@[deprecated loeb_WaryBot_vs_WaryBot_core (since := "2026-09-27")] alias wary_vs_wary_core := loeb_WaryBot_vs_WaryBot_core
@[deprecated loeb_WaryBot_vs_WaryBot_guard (since := "2026-09-27")] alias wary_finds_guard_vs_self := loeb_WaryBot_vs_WaryBot_guard

/-! ### The `k̂`-chain and the probe sub-plays (`Cells/KhatCells`, `PositiveCells`, `SoundnessCells`) -/

@[deprecated khat_CupodTrollBot_vs_CupodBot_guard (since := "2026-09-27")] alias troll_finds_guard_vs_cupod := khat_CupodTrollBot_vs_CupodBot_guard
@[deprecated pos_JustBot_vs_botCB (since := "2026-09-27")] alias just_botCB_found := pos_JustBot_vs_botCB
@[deprecated pos_CupodBot_vs_botDB (since := "2026-09-27")] alias cupod_vs_botDB_found := pos_CupodBot_vs_botDB
@[deprecated pos_WaryBot_vs_botDB (since := "2026-09-27")] alias wary_vs_botDB_found := pos_WaryBot_vs_botDB
@[deprecated pos_CIMCIC_vs_botCB (since := "2026-09-27")] alias cimcic_vs_botCB_found := pos_CIMCIC_vs_botCB
@[deprecated pos_GuardianBot_vs_botDB (since := "2026-09-27")] alias guardian_vs_botDB_eventually := pos_GuardianBot_vs_botDB
@[deprecated snd_CIMCIC_vs_botDB (since := "2026-09-27")] alias cimcic_vs_botDB := snd_CIMCIC_vs_botDB
@[deprecated snd_GuardianBot_vs_botCB (since := "2026-09-27")] alias guardian_vs_botCB := snd_GuardianBot_vs_botCB
@[deprecated snd_CupodBot_vs_botCB (since := "2026-09-27")] alias cupod_vs_botCB := snd_CupodBot_vs_botCB
@[deprecated snd_DupocBot_vs_botDB (since := "2026-09-27")] alias dupoc_vs_botDB := snd_DupocBot_vs_botDB
@[deprecated snd_CupodTrollBot_vs_botCB (since := "2026-09-27")] alias ctb_vs_botCB := snd_CupodTrollBot_vs_botCB
@[deprecated snd_CupodTrollBot_vs_botDB (since := "2026-09-27")] alias ctb_vs_botDB := snd_CupodTrollBot_vs_botDB
@[deprecated snd_WaryBot_vs_botCB (since := "2026-09-27")] alias wary_vs_botCB := snd_WaryBot_vs_botCB
@[deprecated snd_PrudentBot_vs_botDB (since := "2026-09-27")] alias prudent_vs_botDB := snd_PrudentBot_vs_botDB
@[deprecated snd_PrudentBot_vs_botCB (since := "2026-09-27")] alias prudent_vs_botCB := snd_PrudentBot_vs_botCB
@[deprecated snd_botDupocBot_vs_botDB (since := "2026-09-27")] alias botDupoc_vs_botDB := snd_botDupocBot_vs_botDB

/-! ### Method prefixes that did not match the proof method (the six large-`k` SND-class cells that need
a positive sub-fact are POS) -/

@[deprecated pos_CupodBot_vs_DBot (since := "2026-09-27")] alias snd_CupodBot_vs_DBot := pos_CupodBot_vs_DBot
@[deprecated pos_CupodBot_vs_EBot (since := "2026-09-27")] alias snd_CupodBot_vs_EBot := pos_CupodBot_vs_EBot
@[deprecated pos_WaryBot_vs_DBot (since := "2026-09-27")] alias snd_WaryBot_vs_DBot := pos_WaryBot_vs_DBot
@[deprecated pos_WaryBot_vs_EBot (since := "2026-09-27")] alias snd_WaryBot_vs_EBot := pos_WaryBot_vs_EBot
@[deprecated pos_GuardianBot_vs_EBot (since := "2026-09-27")] alias snd_GuardianBot_vs_EBot := pos_GuardianBot_vs_EBot
@[deprecated pos_GuardianBot_vs_OBot (since := "2026-09-27")] alias snd_GuardianBot_vs_OBot := pos_GuardianBot_vs_OBot

/-! ### Helper renames -/

@[deprecated desc_dimcid (since := "2026-09-27")] alias hopp_self := desc_dimcid
@[deprecated descT_dimcid (since := "2026-09-27")] alias hopp'_self := descT_dimcid
@[deprecated desc_mirror (since := "2026-09-27")] alias hopp_mirror := desc_mirror
@[deprecated descT_mirror (since := "2026-09-27")] alias hopp'_mirror := descT_mirror
@[deprecated desc_cupod (since := "2026-09-27")] alias hopp_cupod := desc_cupod
@[deprecated descT_cupod (since := "2026-09-27")] alias hopp'_cupod := descT_cupod
@[deprecated desc_dupoc (since := "2026-09-27")] alias hopp_dupoc := desc_dupoc
@[deprecated descT_dupoc (since := "2026-09-27")] alias hopp'_dupoc := descT_dupoc
@[deprecated desc_cimcic (since := "2026-09-27")] alias hopp_cimcic := desc_cimcic
@[deprecated descT_cimcic (since := "2026-09-27")] alias hopp'_cimcic := descT_cimcic
@[deprecated desc_just7 (since := "2026-09-27")] alias hopp_just7 := desc_just7
@[deprecated descT_just7 (since := "2026-09-27")] alias hopp'_just7 := descT_just7
@[deprecated desc_troll7 (since := "2026-09-27")] alias hopp_troll7 := desc_troll7
@[deprecated descT_troll7 (since := "2026-09-27")] alias hopp'_troll7 := descT_troll7
@[deprecated desc_SV (since := "2026-09-27")] alias hme_SV := desc_SV
@[deprecated descT_SV (since := "2026-09-27")] alias hme_SVT := descT_SV
@[deprecated desc_botSV (since := "2026-09-27")] alias hme_botSV := desc_botSV
@[deprecated descT_botSV (since := "2026-09-27")] alias hme_botSVT := descT_botSV
@[deprecated desc_botDupoc (since := "2026-09-27")] alias hme_bot := desc_botDupoc
@[deprecated descT_botDupoc (since := "2026-09-27")] alias hme'_bot := descT_botDupoc
@[deprecated desc_WT (since := "2026-09-27")] alias hme_WT := desc_WT
@[deprecated hX_dimcid (since := "2026-09-27")] alias hX_self := hX_dimcid
@[deprecated hU_dimcid (since := "2026-09-27")] alias hU_self := hU_dimcid
@[deprecated hW_dimcid (since := "2026-09-27")] alias hW_self := hW_dimcid
@[deprecated hX_botDupoc (since := "2026-09-27")] alias hX_bot := hX_botDupoc
@[deprecated hU_botDupoc (since := "2026-09-27")] alias hU_bot := hU_botDupoc
@[deprecated hW_botDupoc (since := "2026-09-27")] alias hW_bot := hW_botDupoc
@[deprecated pJJ_guards_V (since := "2026-09-27")] alias pJJ_guard_V := pJJ_guards_V
@[deprecated pJD_guards_V (since := "2026-09-27")] alias pJD_boxes_V := pJD_guards_V
alias dimcid_cupod_finds_guards := loeb_Dimcid_vs_Cupod_guards_of_nec   -- secondary spelling of the 2026-09-24 layer
alias dimcid_cupod_finds_guards_unconditional := loeb_Dimcid_vs_Cupod_guards   -- secondary spelling of the 2026-09-24 layer
alias cimcic_dupoc_finds_guards := loeb_Cimcic_vs_Dupoc_guards_of_nec   -- secondary spelling of the 2026-09-24 layer
alias cimcic_dupoc_finds_guards_unconditional := loeb_Cimcic_vs_Dupoc_guards   -- secondary spelling of the 2026-09-24 layer
alias just7_dupoc_finds_guards_unconditional := loeb_Just7_vs_Dupoc_guards   -- secondary spelling of the 2026-09-24 layer
alias cimcic_just7_finds_guards_unconditional := loeb_Cimcic_vs_Just7_guards   -- secondary spelling of the 2026-09-24 layer
@[deprecated progCode_DupocBot_search (since := "2026-09-27")] alias progCode_DupocBot' := progCode_DupocBot_search
@[deprecated progCode_PrudentBot_search (since := "2026-09-27")] alias progCode_PrudentBot' := progCode_PrudentBot_search
@[deprecated progCode_CIMCIC_search (since := "2026-09-27")] alias progCode_CIMCIC' := progCode_CIMCIC_search
@[deprecated progCode_DIMCID_search (since := "2026-09-27")] alias progCode_DIMCID' := progCode_DIMCID_search
@[deprecated mirror_copies2_V (since := "2026-09-27")] alias mirror_copies_V := mirror_copies2_V

/-! ### The floor modules (`Cells/FloorVerdicts`, `Cells/FloorDichotomy`, written after the alias layer): the four
names that did not follow the scheme -/

@[deprecated pos_DupocBot_vs_botCB (since := "2026-09-27")] alias dupoc_vs_botCB_found := pos_DupocBot_vs_botCB
@[deprecated pos_botDupocBot_vs_botCB (since := "2026-09-27")] alias botDupoc_vs_botCB_found := pos_botDupocBot_vs_botCB
@[deprecated snd_JustBot_vs_botDB (since := "2026-09-27")] alias just_vs_botDB := snd_JustBot_vs_botDB
@[deprecated dich_CupodBot_vs_PrudentBot_core (since := "2026-09-27")] alias dich_CupodBot_PrudentBot_core := dich_CupodBot_vs_PrudentBot_core

end ArithS
