import ArithS.Tau.Columns
import ArithS.Tau.Described
import ArithS.Tau.Dimdid
import ArithS.Tau.Attr

/-!
# ArithS.Tau.Rows.OBot — τ(OBot)'s row in PA-`S'`

τ(OBot)'s instance at `T` chains two DEFECTION watches (`test = D`) over `T`'s instances at the cooperator and
at the defector, and cooperates only if both stay silent (`instCode_obot`). Engine twin:
`Tau/Theorems/TauOBot/Phase.lean` (`obotRowSpec`); every stated slot agrees.

**Floor bit** (`‡`, one): `cupod` — settled on this side (Cupod's instance at the cooperator is SND, at the
defector POS: the second watch fires, D); the hinge is Cupod's probe of OBot's instance (base
`dich_CupodBot_vs_OBot`), the partner's open question.

The `cimcic` and `dimcid` slots need no verdict on the instance at the cooperator: whatever it plays, the cascade
ends in D (`col_cimcic_coop_total` + `col_cimcic_defect`; `col_dimcid_coop_total` + `Tau/Described.col_dimcid_defect`).
All 13 theorem slots are stated.
-/

namespace ArithS.Tau

open PD PD.Tau

/-- τ(OBot)'s bit row: C only where both defection watches stay silent. -/
def obotRowA : Tmpl → Action
  | .coop => .C | .defect => .D | .tftSim => .D | .dupoc => .D | .ebot => .D | .obot => .D | .dbot => .D
  | .cupodTroll => .C | .dupocTroll => .C | .cupod => .D | .dimcid => .D | .cimcic => .D | .dimdid => .D | .prudent => .D
  | .maxconfidence => .D | .minconfidence => .D
  | _ => .D

/-- The first defection watch fires. -/
theorem obot_D_of_coop {k : ℕ} {T : Tmpl} (h : bitPlays k T .coop .D) : bitPlays k .obot T .D := by
  apply bitPlays_of_eq (instCode_obot k T)
  obtain ⟨n, hn⟩ := h
  exact ⟨_, watch_fires' hn (const_play 0 _ _ _)⟩

/-- The second defection watch fires, whatever the first saw. -/
theorem obot_D_of_defect {k : ℕ} {T : Tmpl} {r : Action} (h₁ : bitPlays k T .coop r) (h₂ : bitPlays k T .defect .D) :
    bitPlays k .obot T .D := by
  cases r with
  | D => exact obot_D_of_coop h₁
  | C =>
    apply bitPlays_of_eq (instCode_obot k T)
    obtain ⟨n₁, h₁⟩ := h₁
    obtain ⟨n₂, h₂⟩ := h₂
    exact ⟨_, watch_falls' h₁ (by decide) (watch_fires' h₂ (const_play 0 _ _ _))⟩

/-- Both watches silent: C. -/
theorem obot_C_of {k : ℕ} {T : Tmpl} (h₁ : bitPlays k T .coop .C) (h₂ : bitPlays k T .defect .C) :
    bitPlays k .obot T .C := by
  apply bitPlays_of_eq (instCode_obot k T)
  obtain ⟨n₁, h₁⟩ := h₁
  obtain ⟨n₂, h₂⟩ := h₂
  exact ⟨_, watch_falls' h₁ (by decide) (watch_falls' h₂ (by decide) (const_play 0 _ _ _))⟩

/-- **τ(OBot)'s row in `S'`** — the 13 theorem slots (the floor bit is below). -/
@[tau_rowA]
theorem obotRowSpecA : RowSpecA .obot
    [.coop, .defect, .tftSim, .dupoc, .ebot, .obot, .dbot, .cupodTroll, .dupocTroll, .dimcid, .cimcic, .dimdid, .prudent,
     .maxconfidence, .minconfidence] obotRowA :=
  RowSpecA.cons (bitEventually.of_forall fun k ↦ obot_C_of (col_coop_coop k) (col_coop_defect k)) <|
  RowSpecA.cons (bitEventually.of_forall fun k ↦ obot_D_of_coop (col_defect_coop k)) <|
  RowSpecA.cons (bitEventually.of_forall fun k ↦ obot_D_of_defect (col_tftSim_coop k) (col_tftSim_defect k)) <|
  RowSpecA.cons (bitEventually.mono₂ (fun _ h₁ h₂ ↦ obot_D_of_defect h₁ h₂) col_dupoc_coop
    (bitEventually.of_forall col_dupoc_defect)) <|
  RowSpecA.cons (bitEventually.of_forall fun k ↦ obot_D_of_coop (col_ebot_coop k)) <|
  RowSpecA.cons (bitEventually.of_forall fun k ↦ obot_D_of_defect (col_obot_coop k) (col_obot_defect k)) <|
  RowSpecA.cons (bitEventually.of_forall fun k ↦ obot_D_of_coop (col_dbot_coop k)) <|
  RowSpecA.cons (bitEventually.of_forall fun k ↦ obot_C_of (col_cupodTroll_coop k) (col_cupodTroll_defect k)) <|
  RowSpecA.cons (bitEventually.of_forall fun k ↦ obot_C_of (col_dupocTroll_coop k) (col_dupocTroll_defect k)) <|
  RowSpecA.cons (bitEventually.mono (fun k h₂ ↦
    let ⟨_, h₁⟩ := col_dimcid_coop_total k
    obot_D_of_defect h₁ h₂) col_dimcid_defect) <|
  RowSpecA.cons (bitEventually.of_forall fun k ↦
    let ⟨_, h₁⟩ := col_cimcic_coop_total k
    obot_D_of_defect h₁ (col_cimcic_defect k)) <|
  RowSpecA.cons (bitEventually.mono (fun k h₂ ↦ obot_D_of_defect (col_dimdid_coop k) h₂) col_dimdid_defect) <|
  RowSpecA.cons (bitEventually.of_forall fun k ↦ obot_D_of_coop (col_prudent_coop k)) <|
  RowSpecA.cons (bitEventually.mono₂ (fun _ h₁ h₂ ↦ obot_D_of_defect h₁ h₂) col_maxconfidence_coop
    (bitEventually.of_forall col_maxconfidence_defect)) <|
  RowSpecA.cons (bitEventually.mono₂ (fun _ h₁ h₂ ↦ obot_D_of_defect h₁ h₂) col_minconfidence_coop
    (bitEventually.of_forall col_minconfidence_defect)) <|
  RowSpecA.nil _ _

/-! ### The floor bit — settled on this side, the partner's hinge -/

/-- `obot × cupod` ‡ (base `dich_CupodBot_vs_OBot`): Cupod's instance cooperates with the cooperator (SND) and
defects against the defector (POS), so the second watch fires — D. Hinge: Cupod's probe of OBot's instance, in
Cupod's own frame. -/
@[tau_floor_bitA]
theorem obotRowSpecA_cupod_floor : FloorBitA .obot .cupod
    (fun k ↦ □[k] (guardCodeB (templateCode (probeD (inst (tauZoo k) .obot .cupod)))
      (pBot (instCode k .cupod .obot)) (pBot (instCode k .cupod .obot)) k)) .D :=
  FloorBitA.of _ (bitEventually.mono (fun k h₂ ↦ obot_D_of_defect (col_cupod_coop k) h₂) col_cupod_defect)

end ArithS.Tau
