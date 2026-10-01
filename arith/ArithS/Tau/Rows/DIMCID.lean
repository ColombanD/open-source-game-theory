import ArithS.Tau.Quine
import ArithS.Tau.Entangled.DimcidDupoc
import ArithS.Tau.Entangled.DimcidCupod
import ArithS.Tau.Entangled.DimcidCimcic
import ArithS.Tau.Attr

/-!
# ArithS.Tau.Rows.DIMCID — τ(DIMCID)'s row in PA-`S'`

τ(DIMCID)'s instance at a hypothesis `T` that does not self-probe is one `proveImplD` stage: the guard
`dimG X := .impl (.plays .self (.bot X) C) (.plays (.bot X) .self D)` — "if I cooperate with `T`'s instance seeing
DIMCID, it defects against me" — fire D, else C (`Tau/Zoo.inst_dimcid_peel_*`); its diagonal is
`.impl (self plays self C) (self plays self D)`, the SAME player at opposite actions — a genuine Löb fixpoint on
DEFECTION (`inst_dimcid_quine`), closed by bounded Löb on the bot-wrapped instance (`Tau/Quine.dimcid_quine_found`:
a box of the guard makes the instance defect, refuting the antecedent). Engine twin:
`Tau/Theorems/TauDIMCID/Phase.lean`.

Slots stated here (`[coop, defect, tftSim, dupoc, ebot, obot, dbot, cupodTroll, cupod, dimcid, cimcic, maxconfidence,
minconfidence]`): `coop` D — **the `S'` FLIP** of
the engine's C (`Tau/Described.col_dimcid_coop`: the self-fulfilling refutation `dimcid_vs_closed`, on the instance),
`defect` D (POS, `col_dimcid_defect`), the diagonal D (Löb) — and **`tftSim ebot obot dbot cupodTroll`: C, the
ENGINE's values; the table's five remaining flips (`D≠`) do NOT transfer to the tau layer** — and the five ENTANGLED slots `dupoc cupod cimcic maxconfidence
minconfidence`, all D (the DIMCID member finds its self-fulfilling guard in every `.sys` system, `Tau/Entangled/
DimcidDupoc.lean`, `DimcidCupod.lean`, `DimcidCimcic.lean`; the FLIPS of the table). The base flips rest on
`dimcid_vs_closed`: DIMCID's guard is found by Löb against any closed opponent because the family is the
`binNumeral k`-instance of a fixed formula. On the tau instance the probed program is the HYPOTHESIS'S INSTANCE
SEEING DIMCID, which carries the budget `k` (`inst dimcid coop = .search k …` sits inside it, or the instance IS
`.search k (.eq C D) …`), so the instance's STORED TEMPLATE depends on `k`, the instance's own description — written
into the guard sentence by the `.self` antecedent — has a numeral of more than `k` bits, and the guard sentence is
LONGER than `k`: it is never found, at every budget (`Tau/NeverFits.dimcid_selfBot_C`), and the instance plays its
ELSE branch, C. (`coop`/`defect` flip/agree as the table says because `inst coop dimcid`/`inst defect dimcid` are the
budget-free constants.) The table and `expectedFloorBits` need no change (none of the five is a `‡` cell); §3's
"13 FLIP" count is 8 for the tau layer (+1 at `cimcic × tftSim`, see `Rows/CIMCIC.lean`).

-- UNSTATED (decision pending — `SPRIME_SOURCE_OF_TRUTH.md` §3, the budget-snapshot obstruction): slot `.prudent`
--   (`inst dimcid prudent = .sys [dim 1, pm 0 dimcid] 0`; the Prudent member's inner guard freezes
--   `inst dimcid .defect`, `k` inside — no family can be stated for either member).
-/

namespace ArithS.Tau

open PD PD.Tau

/-- τ(DIMCID)'s bit row in `S'`: the table's D everywhere (the five C's of the never-fits reading were an artefact
of the pre-2026-10-01 coding; those slots are UNSTATED until Phase 3e re-proves them). -/
def dimcidRowA : Tmpl → Action
  | .coop => .D | .defect => .D | .tftSim => .D | .dupoc => .D | .ebot => .D | .obot => .D | .dbot => .D
  | .cupodTroll => .D | .cupod => .D | .dimcid => .D | .cimcic => .D | .prudent => .D
  | .maxconfidence => .D | .minconfidence => .D
  | _ => .D

/-- DIMCID's off-diagonal guard at the probed instance `X`. -/
abbrev dimG (X : PD.Prog) : PD.Formula := .impl (.plays .self (.bot X) .C) (.plays (.bot X) .self .D)

/-! ### The compiled instances -/

-- Phase 3e: the instance equations of the five budget-carrying hypotheses (`tftSim ebot obot dbot cupodTroll`) now
-- store the ABSTRACTED template `templateCodeAt (dimG (inst T .dimcid)) k`; restated with the slots in Phase 3e.

/-- The diagonal: the Löb fixpoint on defection. -/
theorem instCode_dimcid_dimcid (k : ℕ) : instCode k .dimcid .dimcid =
    pSearch k (templateCode dimQ) (pConst 1) (pConst 0) := by
  unfold instCode; rw [inst_dimcid_quine]; rw [progCode_search_noSnap _ _ _ _ rfl]; simp [actCode]

/-! ### The slots -/

/-- **The diagonal: D by bounded Löb** (`dimcid_quine_found`). -/
theorem dimcid_quine_D : bitEventually .dimcid .dimcid .D := by
  obtain ⟨k₀, h⟩ := dimcid_quine_found
  refine ⟨k₀, fun k hk ↦ bitPlays_of_eq (instCode_dimcid_dimcid k) ?_⟩
  exact ⟨_, search_then dimQ (h k hk) (const_play 0 _ _ _)⟩

-- Phase 3e: slots `.tftSim .ebot .obot .dbot .cupodTroll` UNSTATED. Their previous proofs (`dimcid_selfBot_C`, the
-- never-fits obstruction of `Tau/NeverFits.lean`) were an artefact of the pre-2026-10-01 coding; under budget
-- abstraction the stored templates are constants and the table's D (the base flip `dimcid_vs_closed`) is expected.

/-- **τ(DIMCID)'s row in `S'`** — eight theorem slots (three non-entangled, five entangled; `tftSim ebot obot dbot
cupodTroll prudent` unstated pending Phase 3e). -/
@[tau_rowA]
theorem dimcidRowSpecA : RowSpecA .dimcid
    [.coop, .defect, .dupoc, .cupod, .dimcid, .cimcic, .maxconfidence, .minconfidence] dimcidRowA :=
  RowSpecA.cons col_dimcid_coop <|
  RowSpecA.cons col_dimcid_defect <|
  RowSpecA.cons ent_dimcid_dupoc <|
  RowSpecA.cons ent_dimcid_cupod <|
  RowSpecA.cons dimcid_quine_D <|
  RowSpecA.cons ent_dimcid_cimcic <|
  RowSpecA.cons ent_dimcid_maxconfidence <|
  RowSpecA.cons ent_dimcid_minconfidence <|
  RowSpecA.nil _ _

end ArithS.Tau
