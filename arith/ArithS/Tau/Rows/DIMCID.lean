import ArithS.Tau.Quine
import ArithS.Tau.NeverFits
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

/-- τ(DIMCID)'s bit row in `S'`: D at the budget-free hypotheses and the diagonal, C at the five budget-carrying
hypotheses (the engine's values — see the module docstring); the entangled slots keep the table's D. -/
def dimcidRowA : Tmpl → Action
  | .coop => .D | .defect => .D | .tftSim => .C | .dupoc => .D | .ebot => .C | .obot => .C | .dbot => .C
  | .cupodTroll => .C | .cupod => .D | .dimcid => .D | .cimcic => .D | .prudent => .D
  | .maxconfidence => .D | .minconfidence => .D
  | _ => .D

/-- DIMCID's off-diagonal guard at the probed instance `X`. -/
abbrev dimG (X : PD.Prog) : PD.Formula := .impl (.plays .self (.bot X) .C) (.plays (.bot X) .self .D)

/-! ### The compiled instances -/

theorem instCode_dimcid_tftSim (k : ℕ) : instCode k .dimcid .tftSim =
    pSearch k (templateCode (dimG (inst (tauZoo k) .tftSim .dimcid))) (pConst 1) (pConst 0) := by
  unfold instCode; rw [inst_dimcid_peel_tftSim]; simp [actCode]

theorem instCode_dimcid_ebot (k : ℕ) : instCode k .dimcid .ebot =
    pSearch k (templateCode (dimG (inst (tauZoo k) .ebot .dimcid))) (pConst 1) (pConst 0) := by
  unfold instCode; rw [inst_dimcid_peel_ebot]; simp [actCode]

theorem instCode_dimcid_obot (k : ℕ) : instCode k .dimcid .obot =
    pSearch k (templateCode (dimG (inst (tauZoo k) .obot .dimcid))) (pConst 1) (pConst 0) := by
  unfold instCode; rw [inst_dimcid_peel_obot]; simp [actCode]

theorem instCode_dimcid_dbot (k : ℕ) : instCode k .dimcid .dbot =
    pSearch k (templateCode (dimG (inst (tauZoo k) .dbot .dimcid))) (pConst 1) (pConst 0) := by
  unfold instCode; rw [inst_dimcid_peel_dbot]; simp [actCode]

theorem instCode_dimcid_cupodTroll (k : ℕ) : instCode k .dimcid .cupodTroll =
    pSearch k (templateCode (dimG (inst (tauZoo k) .cupodTroll .dimcid))) (pConst 1) (pConst 0) := by
  unfold instCode; rw [inst_dimcid_peel_cupodTroll]; simp [actCode]

/-- The diagonal: the Löb fixpoint on defection. -/
theorem instCode_dimcid_dimcid (k : ℕ) : instCode k .dimcid .dimcid =
    pSearch k (templateCode dimQ) (pConst 1) (pConst 0) := by
  unfold instCode; rw [inst_dimcid_quine]; simp [actCode]

/-! ### The slots -/

/-- **The diagonal: D by bounded Löb** (`dimcid_quine_found`). -/
theorem dimcid_quine_D : bitEventually .dimcid .dimcid .D := by
  obtain ⟨k₀, h⟩ := dimcid_quine_found
  refine ⟨k₀, fun k hk ↦ bitPlays_of_eq (instCode_dimcid_dimcid k) ?_⟩
  exact ⟨_, search_then dimQ (h k hk) (const_play 0 _ _ _)⟩

/-! ### The five budget-carrying hypotheses: the guard never fits — C -/

theorem hasSearch_tftSim_dimcid (k : ℕ) : HasSearchP k (inst (tauZoo k) .tftSim .dimcid) := by
  rw [inst_tftSim_peel, inst_dimcid_peel_coop]
  exact .iteB _ _ _ (.simL _ (.bot (.search _ _ _)))

theorem hasSearch_ebot_dimcid (k : ℕ) : HasSearchP k (inst (tauZoo k) .ebot .dimcid) := by
  rw [inst_ebot_peel, inst_dimcid_peel_defect]
  exact .iteB _ _ _ (.simL _ (.bot (.search _ _ _)))

theorem hasSearch_obot_dimcid (k : ℕ) : HasSearchP k (inst (tauZoo k) .obot .dimcid) := by
  rw [inst_obot_peel, inst_dimcid_peel_coop]
  exact .iteB _ _ _ (.simL _ (.bot (.search _ _ _)))

theorem hasSearch_dbot_dimcid (k : ℕ) : HasSearchP k (inst (tauZoo k) .dbot .dimcid) := by
  rw [inst_dbot_peel, inst_dimcid_peel_defect]
  exact .iteB _ _ _ (.simL _ (.bot (.search _ _ _)))

theorem hasSearch_cupodTroll_dimcid (k : ℕ) : HasSearchP k (inst (tauZoo k) .cupodTroll .dimcid) := by
  rw [inst_cupodTroll_peel k .dimcid (by decide)]
  exact .search _ _ _

theorem dimcid_tftSim_C (k : ℕ) : bitPlays k .dimcid .tftSim .C :=
  dimcid_selfBot_C (instCode_dimcid_tftSim k) (inst_dimcid_peel_tftSim k) (hasSearch_tftSim_dimcid k) rfl
theorem dimcid_ebot_C (k : ℕ) : bitPlays k .dimcid .ebot .C :=
  dimcid_selfBot_C (instCode_dimcid_ebot k) (inst_dimcid_peel_ebot k) (hasSearch_ebot_dimcid k) rfl
theorem dimcid_obot_C (k : ℕ) : bitPlays k .dimcid .obot .C :=
  dimcid_selfBot_C (instCode_dimcid_obot k) (inst_dimcid_peel_obot k) (hasSearch_obot_dimcid k) rfl
theorem dimcid_dbot_C (k : ℕ) : bitPlays k .dimcid .dbot .C :=
  dimcid_selfBot_C (instCode_dimcid_dbot k) (inst_dimcid_peel_dbot k) (hasSearch_dbot_dimcid k) rfl
theorem dimcid_cupodTroll_C (k : ℕ) : bitPlays k .dimcid .cupodTroll .C :=
  dimcid_selfBot_C (instCode_dimcid_cupodTroll k) (inst_dimcid_peel_cupodTroll k) (hasSearch_cupodTroll_dimcid k) rfl

/-- **τ(DIMCID)'s row in `S'`** — thirteen theorem slots (eight non-entangled, five entangled; `prudent` unstated). -/
@[tau_rowA]
theorem dimcidRowSpecA : RowSpecA .dimcid
    [.coop, .defect, .tftSim, .dupoc, .ebot, .obot, .dbot, .cupodTroll, .cupod, .dimcid, .cimcic,
     .maxconfidence, .minconfidence] dimcidRowA :=
  RowSpecA.cons col_dimcid_coop <|
  RowSpecA.cons col_dimcid_defect <|
  RowSpecA.cons (bitEventually.of_forall dimcid_tftSim_C) <|
  RowSpecA.cons ent_dimcid_dupoc <|
  RowSpecA.cons (bitEventually.of_forall dimcid_ebot_C) <|
  RowSpecA.cons (bitEventually.of_forall dimcid_obot_C) <|
  RowSpecA.cons (bitEventually.of_forall dimcid_dbot_C) <|
  RowSpecA.cons (bitEventually.of_forall dimcid_cupodTroll_C) <|
  RowSpecA.cons ent_dimcid_cupod <|
  RowSpecA.cons dimcid_quine_D <|
  RowSpecA.cons ent_dimcid_cimcic <|
  RowSpecA.cons ent_dimcid_maxconfidence <|
  RowSpecA.cons ent_dimcid_minconfidence <|
  RowSpecA.nil _ _

end ArithS.Tau
