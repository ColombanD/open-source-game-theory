import ArithS.Tau.Columns
import ArithS.Tau.Described
import ArithS.Tau.Attr

/-!
# ArithS.Tau.Rows.TftSim — τ(TitForTatBot, behavioral)'s row in PA-`S'`

τ(TFTSim)'s instance at `T` is one run-stage copying `T`'s instance at the cooperator (`instCode_tftSim`), so
its row IS the `coop` column of the table (`Tau/Columns.lean` §4): C where `T`'s instance cooperates with the
frozen cooperator, D where it defects. Engine twin: `Tau/Theorems/TauTFTSim/Phase.lean` (`tftSimRowSpec`).

**The `dimcid` slot is an `S'` FLIP** (the engine's C becomes D): DIMCID's instance at the cooperator defects
in `S'` (`Tau/Described.col_dimcid_coop` — `Cells/DimcidFlips.dimcid_vs_closed`'s bounded Löb, on the
instance), so the copier defects. The `cimcic` slot is POS on the instance's own description
(`Tau/Described.col_cimcic_coop`). All 14 paper slots are stated.
-/

namespace ArithS.Tau

open PD PD.Tau

/-- τ(TFTSim)'s bit row: the `coop` column — the FLIP at `dimcid` recorded (`D`, the engine says `C`). -/
def tftSimRowA : Tmpl → Action
  | .coop => .C | .defect => .D | .tftSim => .C | .dupoc => .C | .ebot => .D | .obot => .C | .dbot => .D
  | .cupodTroll => .C | .cupod => .C | .dimcid => .D | .cimcic => .C | .prudent => .D
  | .maxconfidence => .C | .minconfidence => .C
  | _ => .C

/-- The copier cooperates when the watched instance cooperates with the frozen cooperator. -/
theorem tftSim_C_of_col {k : ℕ} {T : Tmpl} (h : bitPlays k T .coop .C) : bitPlays k .tftSim T .C := by
  apply bitPlays_of_eq (instCode_tftSim k T)
  obtain ⟨n, hn⟩ := h
  exact ⟨_, watch_fires' hn (const_play 0 _ _ _)⟩

/-- …and defects when it defects. -/
theorem tftSim_D_of_col {k : ℕ} {T : Tmpl} (h : bitPlays k T .coop .D) : bitPlays k .tftSim T .D := by
  apply bitPlays_of_eq (instCode_tftSim k T)
  obtain ⟨n, hn⟩ := h
  exact ⟨_, watch_falls' hn (by decide) (const_play 0 _ _ _)⟩

/-- **τ(TFTSim)'s row in `S'`** — all 14 paper slots. -/
@[tau_rowA]
theorem tftSimRowSpecA : RowSpecA .tftSim
    [.coop, .defect, .tftSim, .dupoc, .ebot, .obot, .dbot, .cupodTroll, .cupod, .dimcid, .cimcic, .prudent,
     .maxconfidence, .minconfidence] tftSimRowA :=
  RowSpecA.cons (bitEventually.of_forall fun k ↦ tftSim_C_of_col (col_coop_coop k)) <|
  RowSpecA.cons (bitEventually.of_forall fun k ↦ tftSim_D_of_col (col_defect_coop k)) <|
  RowSpecA.cons (bitEventually.of_forall fun k ↦ tftSim_C_of_col (col_tftSim_coop k)) <|
  RowSpecA.cons (bitEventually.mono (fun _ ↦ tftSim_C_of_col) col_dupoc_coop) <|
  RowSpecA.cons (bitEventually.of_forall fun k ↦ tftSim_D_of_col (col_ebot_coop k)) <|
  RowSpecA.cons (bitEventually.of_forall fun k ↦ tftSim_C_of_col (col_obot_coop k)) <|
  RowSpecA.cons (bitEventually.of_forall fun k ↦ tftSim_D_of_col (col_dbot_coop k)) <|
  RowSpecA.cons (bitEventually.of_forall fun k ↦ tftSim_C_of_col (col_cupodTroll_coop k)) <|
  RowSpecA.cons (bitEventually.of_forall fun k ↦ tftSim_C_of_col (col_cupod_coop k)) <|
  RowSpecA.cons (bitEventually.mono (fun _ ↦ tftSim_D_of_col) col_dimcid_coop) <|
  RowSpecA.cons (bitEventually.mono (fun _ ↦ tftSim_C_of_col) col_cimcic_coop) <|
  RowSpecA.cons (bitEventually.of_forall fun k ↦ tftSim_D_of_col (col_prudent_coop k)) <|
  RowSpecA.cons (bitEventually.mono (fun _ ↦ tftSim_C_of_col) col_maxconfidence_coop) <|
  RowSpecA.cons (bitEventually.mono (fun _ ↦ tftSim_C_of_col) col_minconfidence_coop) <|
  RowSpecA.nil _ _

end ArithS.Tau
