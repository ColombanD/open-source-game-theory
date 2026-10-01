import ArithS.Tau.Quine
import ArithS.Tau.ClosedWatch
import ArithS.Tau.ClosedWatch2
import ArithS.Tau.ClosedWatch3
import ArithS.Tau.Entangled.DimcidDupoc
import ArithS.Tau.Entangled.DimcidCupod
import ArithS.Tau.Entangled.DimcidCimcic
import ArithS.Tau.Entangled.DimcidPrudent
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

Slots stated here: ALL FOURTEEN (`paperOrder`), ALL D:
* `coop` — **the `S'` FLIP** of the engine's C (`Tau/Described.col_dimcid_coop`: the self-fulfilling refutation
  `dimcid_vs_closed`, on the instance); `defect` (POS, `col_dimcid_defect`); the diagonal (Löb);
* `tftSim`, `dbot`, `cupodTroll`, `obot` (Phase 3e, FLIPS): the probed program is the hypothesis's instance seeing
  DIMCID, which carries the budget `k` — a run-stage watch over `inst dimcid coop/defect` (`W1`, `Tau/Watch.lean`;
  τ(OBot)'s two-stage cascade `W2`, `Tau/Watch2.lean`) or the `.eq`-searcher itself. Under route (c) made generic
  (Phase 2c) its stored description is a CONSTANT and the watch is a `k̂`-tower, so the base argument transfers:
  DIMCID's self-fulfilling family on the watch (`Tau/ClosedWatch.dimcid_closed_found`, `dimcid_tftSim_D`,
  `dimcid_dbot_D`, `dimcid_cupodTroll_D`; `Tau/ClosedWatch2.dimcid_obot_D`). The C's of the pre-abstraction coding
  (`Tau/NeverFits.dimcid_selfBot_C`) were an artefact of the stored template carrying the budget numeral;
* `ebot` (Phase 3f, decision (α), FLIP): τ(EBot)'s instance seeing DIMCID is a THREE-stage watch whose third stage
  names DIMCID's instance at the MIRROR, the closed SYSTEM `.sys [dim 1, mm 0] 0` with a `.search k` member. Since
  Phase 2d the budget abstraction descends into systems (`Agents/CodeTermAbs.codeTermMetaAbs_sys`; the closer takes
  the node's budget, `sysCloseTemplateAt`), so the stored template is a constant and the watch a `k̂`-tower
  (`Tau/Watch3.lean`): `Tau/ClosedWatch3.dimcid_ebot_D`. (Under Phase 2c's coding the bit was C at every budget —
  the system was described verbatim; `Tau/NeverFitsSys.lean` keeps that obstruction on the unabstracted template.);
* the ENTANGLED slots `dupoc cupod cimcic maxconfidence minconfidence` (the DIMCID member finds its self-fulfilling
  guard in every `.sys` system, `Tau/Entangled/DimcidDupoc.lean`, `DimcidCupod.lean`, `DimcidCimcic.lean`) and
  `prudent` (Phase 3e, `Tau/Entangled/DimcidPrudent.lean`: the system `[dim 1, pm 0 dimcid]` with Prudent's NESTED
  member, a `k̂`-tower now that the member's inner template is a constant) — the FLIPS of the table.
-/

namespace ArithS.Tau

open PD PD.Tau

/-- τ(DIMCID)'s bit row in `S'`: the table's D everywhere. -/
def dimcidRowA : Tmpl → Action
  | .coop => .D | .defect => .D | .tftSim => .D | .dupoc => .D | .ebot => .D | .obot => .D | .dbot => .D
  | .cupodTroll => .D | .cupod => .D | .dimcid => .D | .cimcic => .D | .prudent => .D
  | .maxconfidence => .D | .minconfidence => .D
  | _ => .D

/-- DIMCID's off-diagonal guard at the probed instance `X`. -/
abbrev dimG (X : PD.Prog) : PD.Formula := .impl (.plays .self (.bot X) .C) (.plays (.bot X) .self .D)

/-! ### The compiled instances -/

-- The instance equations of the budget-carrying hypotheses (`tftSim dbot cupodTroll obot`, the ABSTRACTED template
-- `templateCodeAt (dimG (inst T .dimcid)) k`) are `Tau/ClosedWatch.instCode_dimcid_*'` and
-- `Tau/ClosedWatch2.instCode_dimcid_obot'` (`ebot`'s: `Tau/ClosedWatch3.instCode_dimcid_ebot'`).

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

/-- **τ(DIMCID)'s row in `S'`** — fourteen theorem slots (eight non-entangled, six entangled), all D. -/
@[tau_rowA]
theorem dimcidRowSpecA : RowSpecA .dimcid
    [.coop, .defect, .tftSim, .dupoc, .ebot, .obot, .dbot, .cupodTroll, .cupod, .dimcid, .cimcic, .prudent,
      .maxconfidence, .minconfidence] dimcidRowA :=
  RowSpecA.cons col_dimcid_coop <|
  RowSpecA.cons col_dimcid_defect <|
  RowSpecA.cons dimcid_tftSim_D <|
  RowSpecA.cons ent_dimcid_dupoc <|
  RowSpecA.cons dimcid_ebot_D <|
  RowSpecA.cons dimcid_obot_D <|
  RowSpecA.cons dimcid_dbot_D <|
  RowSpecA.cons dimcid_cupodTroll_D <|
  RowSpecA.cons ent_dimcid_cupod <|
  RowSpecA.cons dimcid_quine_D <|
  RowSpecA.cons ent_dimcid_cimcic <|
  RowSpecA.cons ent_dimcid_prudent <|
  RowSpecA.cons ent_dimcid_maxconfidence <|
  RowSpecA.cons ent_dimcid_minconfidence <|
  RowSpecA.nil _ _

end ArithS.Tau
