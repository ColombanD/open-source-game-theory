import ArithS.Tau.Columns
import ArithS.Tau.Described
import ArithS.Tau.Attr

/-!
# ArithS.Tau.Rows.DBot — τ(DBot)'s row in PA-`S'`

τ(DBot)'s instance at `T` watches `T`'s instance at the DEFECTOR and punishes cooperation (`instCode_dbot`):
its row is the `defect` column negated (`Tau/Columns.lean` §5). Engine twin:
`Tau/Theorems/TauDBot/Phase.lean` (`dbotRowSpec`); every stated slot agrees.

**Floor bits** (`‡` in the table, four): `dupoc`, `cimcic`, `maxconfidence`, `minconfidence`. On THIS side each is
settled — the watched instance at the defector takes a sound else-branch (SND), so DBot trusts — and the hinge
is the PARTNER's question: the box of the searcher's guard about DBot's instance (`inst T .dbot`'s outer guard
in its own frame), which `S'` leaves open on the partner's bit. They are stated as `FloorBitA` for parity with
the base export, where the dichotomy `dich_DupocBot_vs_DBot` (…) carries the pair; the proofs never use the
hypothesis (`FloorBitA.of`). The `dimcid` slot rests on `Tau/Described.col_dimcid_defect` (POS on the instance's
own description). All 10 theorem slots are stated.
-/

namespace ArithS.Tau

open PD PD.Tau

/-- τ(DBot)'s bit row: D exactly at the exploitable cooperator and at itself (its own instance at the defector
trusts). -/
def dbotRowA : Tmpl → Action
  | .coop => .D | .defect => .C | .tftSim => .C | .dupoc => .C | .ebot => .C | .obot => .C | .dbot => .D
  | .cupodTroll => .D | .cupod => .C | .dimcid => .C | .cimcic => .C | .prudent => .C
  | .maxconfidence => .C | .minconfidence => .C
  | _ => .C

/-- The punisher trusts an instance that defects against the frozen defector. -/
theorem dbot_C_of_col {k : ℕ} {T : Tmpl} (h : bitPlays k T .defect .D) : bitPlays k .dbot T .C := by
  apply bitPlays_of_eq (instCode_dbot k T)
  obtain ⟨n, hn⟩ := h
  exact ⟨_, watch_falls' hn (by decide) (const_play 0 _ _ _)⟩

/-- …and punishes one that cooperates with it. -/
theorem dbot_D_of_col {k : ℕ} {T : Tmpl} (h : bitPlays k T .defect .C) : bitPlays k .dbot T .D := by
  apply bitPlays_of_eq (instCode_dbot k T)
  obtain ⟨n, hn⟩ := h
  exact ⟨_, watch_fires' hn (const_play 0 _ _ _)⟩

/-- **τ(DBot)'s row in `S'`** — the 10 theorem slots (the 4 floor bits are below). -/
@[tau_rowA]
theorem dbotRowSpecA : RowSpecA .dbot
    [.coop, .defect, .tftSim, .ebot, .obot, .dbot, .cupodTroll, .cupod, .dimcid, .prudent] dbotRowA :=
  RowSpecA.cons (bitEventually.of_forall fun k ↦ dbot_D_of_col (col_coop_defect k)) <|
  RowSpecA.cons (bitEventually.of_forall fun k ↦ dbot_C_of_col (col_defect_defect k)) <|
  RowSpecA.cons (bitEventually.of_forall fun k ↦ dbot_C_of_col (col_tftSim_defect k)) <|
  RowSpecA.cons (bitEventually.of_forall fun k ↦ dbot_C_of_col (col_ebot_defect k)) <|
  RowSpecA.cons (bitEventually.of_forall fun k ↦ dbot_C_of_col (col_obot_defect k)) <|
  RowSpecA.cons (bitEventually.of_forall fun k ↦ dbot_D_of_col (col_dbot_defect k)) <|
  RowSpecA.cons (bitEventually.of_forall fun k ↦ dbot_D_of_col (col_cupodTroll_defect k)) <|
  RowSpecA.cons (bitEventually.mono (fun _ ↦ dbot_C_of_col) col_cupod_defect) <|
  RowSpecA.cons (bitEventually.mono (fun _ ↦ dbot_C_of_col) col_dimcid_defect) <|
  RowSpecA.cons (bitEventually.of_forall fun k ↦ dbot_C_of_col (col_prudent_defect k)) <|
  RowSpecA.nil _ _

/-! ### The floor bits — settled on this side, the partner's hinge -/

/-- `dbot × dupoc` ‡ (base `dich_DupocBot_vs_DBot`): Dupoc's instance at the defector takes its sound else-branch,
DBot trusts — C. Hinge: Dupoc's probe of DBot's instance, in Dupoc's own frame (the partner's open question). -/
@[tau_floor_bitA]
theorem dbotRowSpecA_dupoc_floor : FloorBitA .dbot .dupoc
    (fun k ↦ □[k] (guardCodeB (templateCode (probe (inst (tauZoo k) .dbot .dupoc)))
      (pBot (instCode k .dupoc .dbot)) (pBot (instCode k .dupoc .dbot)) k)) .C :=
  FloorBitA.of _ (bitEventually.of_forall fun k ↦ dbot_C_of_col (col_dupoc_defect k))

/-- `dbot × cimcic` ‡ (base `dich_CIMCIC_vs_DBot`): CIMCIC's instance at the defector is self-refuting, hence
defects; DBot trusts — C. Hinge: CIMCIC's implication guard about DBot's instance, in CIMCIC's own frame. -/
@[tau_floor_bitA]
theorem dbotRowSpecA_cimcic_floor : FloorBitA .dbot .cimcic
    (fun k ↦ □[k] (guardCodeB (templateCode (.impl (.plays .self (.bot (inst (tauZoo k) .dbot .cimcic)) .C)
      (.plays (.bot (inst (tauZoo k) .dbot .cimcic)) .self .C)))
      (pBot (instCode k .cimcic .dbot)) (pBot (instCode k .cimcic .dbot)) k)) .C :=
  FloorBitA.of _ (bitEventually.of_forall fun k ↦ dbot_C_of_col (col_cimcic_defect k))

/-- `dbot × maxconfidence` ‡ (Dupoc's row by the bridge): C. -/
@[tau_floor_bitA]
theorem dbotRowSpecA_maxconfidence_floor : FloorBitA .dbot .maxconfidence
    (fun k ↦ □[k] (guardCodeB (templateCode (probe (inst (tauZoo k) .dbot .maxconfidence)))
      (pBot (instCode k .maxconfidence .dbot)) (pBot (instCode k .maxconfidence .dbot)) k)) .C :=
  FloorBitA.of _ (bitEventually.of_forall fun k ↦ dbot_C_of_col (col_maxconfidence_defect k))

/-- `dbot × minconfidence` ‡ (Dupoc's row by the bridge): C. -/
@[tau_floor_bitA]
theorem dbotRowSpecA_minconfidence_floor : FloorBitA .dbot .minconfidence
    (fun k ↦ □[k] (guardCodeB (templateCode (probe (inst (tauZoo k) .dbot .minconfidence)))
      (pBot (instCode k .minconfidence .dbot)) (pBot (instCode k .minconfidence .dbot)) k)) .C :=
  FloorBitA.of _ (bitEventually.of_forall fun k ↦ dbot_C_of_col (col_minconfidence_defect k))

end ArithS.Tau
