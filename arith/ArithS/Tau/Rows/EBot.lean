import ArithS.Tau.Columns
import ArithS.Tau.Described
import ArithS.Tau.Dimdid
import ArithS.Tau.Entangled.Mirror
import ArithS.Tau.Entangled.EBotPrudent
import ArithS.Tau.Attr

/-!
# ArithS.Tau.Rows.EBot — τ(EBot)'s row in PA-`S'`

τ(EBot)'s instance at `T` is base EBot's three-stage run cascade over `T`'s instances at the defector (the
exploit watch: cooperation there ⇒ D), the cooperator (the reciprocity watch: cooperation there ⇒ C) and the
mirror (⇒ C, else D) — `instCode_ebot`. Engine twin: `Tau/Theorems/TauEBot/Phase.lean` (`ebotRowSpec`).

**Floor bits** (`‡`, five): `dupoc`, `cimcic`, `prudent`, `maxconfidence`, `minconfidence`. `dupoc`, `cimcic` and
the natives are settled on this side (the searcher's instance at the defector is SND, at the cooperator POS: the
reciprocity watch fires, C); the hinge is the partner's guard about EBot's instance (base `dich_DupocBot_vs_EBot`,
`dich_CIMCIC_vs_EBot`); `prudent` (base `dich_PrudentBot_vs_EBot`) is settled C too: the cascade reaches Prudent's
instance at the MIRROR, the system `.sys [pm 1 mirror, mm 0] 0`, whose Prudent member cooperates by the Löb family
on a closed, `k`-free third party (`Tau/Entangled/EBotPrudent.ent_ebot_prudent`, the engine's
`prudent_mirror_plays_C` transferred).

The `dimcid` slot (D, the FLIP of the engine's C) needs the cascade's third stage: DIMCID's instance at the mirror is
the system `.sys [dim 1, mm 0] 0`, whose DIMCID member defects by its self-fulfilling family, so the mirror watch
falls (`Tau/Entangled/Mirror.ent_ebot_dimcid`). All 14 paper slots are stated (9 theorem slots, 5 floor bits).
-/

namespace ArithS.Tau

open PD PD.Tau

/-- τ(EBot)'s bit row: D at the exploitable cooperator, the defector, the punisher and the troll; the FLIP at
`dimcid` recorded (`D`, the engine says `C`). -/
def ebotRowA : Tmpl → Action
  | .coop => .D | .defect => .D | .tftSim => .C | .dupoc => .C | .ebot => .C | .obot => .C | .dbot => .D
  | .cupodTroll => .D | .dupocTroll => .D | .cupod => .C | .dimcid => .D | .cimcic => .C | .dimdid => .C | .prudent => .C
  | .maxconfidence => .C | .minconfidence => .C
  | _ => .C

/-- The exploit watch fires: the watched instance cooperates with the defector — D. -/
theorem ebot_D_of_defect {k : ℕ} {T : Tmpl} (h : bitPlays k T .defect .C) : bitPlays k .ebot T .D := by
  apply bitPlays_of_eq (instCode_ebot k T)
  obtain ⟨n, hn⟩ := h
  exact ⟨_, watch_fires' hn (const_play 0 _ _ _)⟩

/-- The exploit watch falls, the reciprocity watch fires — C. -/
theorem ebot_C_of {k : ℕ} {T : Tmpl} (h₁ : bitPlays k T .defect .D) (h₂ : bitPlays k T .coop .C) :
    bitPlays k .ebot T .C := by
  apply bitPlays_of_eq (instCode_ebot k T)
  obtain ⟨n₁, h₁⟩ := h₁
  obtain ⟨n₂, h₂⟩ := h₂
  exact ⟨_, watch_falls' h₁ (by decide) (watch_fires' h₂ (const_play 0 _ _ _))⟩

/-- Both fall, the mirror watch fires — C. -/
theorem ebot_C_of_mirror {k : ℕ} {T : Tmpl} (h₁ : bitPlays k T .defect .D) (h₂ : bitPlays k T .coop .D)
    (h₃ : bitPlays k T .mirror .C) : bitPlays k .ebot T .C := by
  apply bitPlays_of_eq (instCode_ebot k T)
  obtain ⟨n₁, h₁⟩ := h₁
  obtain ⟨n₂, h₂⟩ := h₂
  obtain ⟨n₃, h₃⟩ := h₃
  exact ⟨_, watch_falls' h₁ (by decide) (watch_falls' h₂ (by decide) (watch_fires' h₃ (const_play 0 _ _ _)))⟩

/-- All three fall — D. -/
theorem ebot_D_of_all {k : ℕ} {T : Tmpl} (h₁ : bitPlays k T .defect .D) (h₂ : bitPlays k T .coop .D)
    (h₃ : bitPlays k T .mirror .D) : bitPlays k .ebot T .D := by
  apply bitPlays_of_eq (instCode_ebot k T)
  obtain ⟨n₁, h₁⟩ := h₁
  obtain ⟨n₂, h₂⟩ := h₂
  obtain ⟨n₃, h₃⟩ := h₃
  exact ⟨_, watch_falls' h₁ (by decide) (watch_falls' h₂ (by decide) (watch_falls' h₃ (by decide) (const_play 0 _ _ _)))⟩

/-- **τ(EBot)'s row in `S'`** — the 9 theorem slots (the 5 floor bits are below). -/
@[tau_rowA]
theorem ebotRowSpecA : RowSpecA .ebot
    [.coop, .defect, .tftSim, .ebot, .obot, .dbot, .cupodTroll, .dupocTroll, .cupod, .dimcid, .dimdid] ebotRowA :=
  RowSpecA.cons (bitEventually.of_forall fun k ↦ ebot_D_of_defect (col_coop_defect k)) <|
  RowSpecA.cons (bitEventually.of_forall fun k ↦
    ebot_D_of_all (col_defect_defect k) (col_defect_coop k) (col_defect_mirror k)) <|
  RowSpecA.cons (bitEventually.of_forall fun k ↦ ebot_C_of (col_tftSim_defect k) (col_tftSim_coop k)) <|
  RowSpecA.cons (bitEventually.of_forall fun k ↦
    ebot_C_of_mirror (col_ebot_defect k) (col_ebot_coop k) (col_ebot_mirror k)) <|
  RowSpecA.cons (bitEventually.of_forall fun k ↦ ebot_C_of (col_obot_defect k) (col_obot_coop k)) <|
  RowSpecA.cons (bitEventually.of_forall fun k ↦ ebot_D_of_defect (col_dbot_defect k)) <|
  RowSpecA.cons (bitEventually.of_forall fun k ↦ ebot_D_of_defect (col_cupodTroll_defect k)) <|
  RowSpecA.cons (bitEventually.of_forall fun k ↦ ebot_D_of_defect (col_dupocTroll_defect k)) <|
  RowSpecA.cons (bitEventually.mono (fun k h₁ ↦ ebot_C_of h₁ (col_cupod_coop k)) col_cupod_defect) <|
  RowSpecA.cons ent_ebot_dimcid <|
  RowSpecA.cons (bitEventually.mono (fun k h₁ ↦ ebot_C_of h₁ (col_dimdid_coop k)) col_dimdid_defect) <|
  RowSpecA.nil _ _

/-! ### The floor bits — settled on this side, the partner's hinge -/

/-- `ebot × dupoc` ‡ (base `dich_DupocBot_vs_EBot`): Dupoc's instance defects against the defector (SND) and
cooperates with the cooperator (POS): the reciprocity watch fires — C. Hinge: Dupoc's probe of EBot's instance,
in Dupoc's own frame. -/
@[tau_floor_bitA]
theorem ebotRowSpecA_dupoc_floor : FloorBitA .ebot .dupoc
    (fun k ↦ □[k] (guardCodeB (templateCode (probe (inst (tauZoo k) .ebot .dupoc)))
      (pBot (instCode k .dupoc .ebot)) (pBot (instCode k .dupoc .ebot)) k)) .C :=
  FloorBitA.of _ (bitEventually.mono (fun k h₂ ↦ ebot_C_of (col_dupoc_defect k) h₂) col_dupoc_coop)

/-- `ebot × cimcic` ‡ (base `dich_CIMCIC_vs_EBot`): CIMCIC's instance at the defector is self-refuting (D), at the
cooperator POS on its own description (C): the reciprocity watch fires — C. Hinge: CIMCIC's implication guard
about EBot's instance, in CIMCIC's own frame. -/
@[tau_floor_bitA]
theorem ebotRowSpecA_cimcic_floor : FloorBitA .ebot .cimcic
    (fun k ↦ □[k] (guardCodeB (templateCode (.impl (.plays .self (.bot (inst (tauZoo k) .ebot .cimcic)) .C)
      (.plays (.bot (inst (tauZoo k) .ebot .cimcic)) .self .C)))
      (pBot (instCode k .cimcic .ebot)) (pBot (instCode k .cimcic .ebot)) k)) .C :=
  FloorBitA.of _ (bitEventually.mono (fun k h₂ ↦ ebot_C_of (col_cimcic_defect k) h₂) col_cimcic_coop)

/-- `ebot × maxconfidence` ‡ (Dupoc's row by the bridge): C. -/
@[tau_floor_bitA]
theorem ebotRowSpecA_maxconfidence_floor : FloorBitA .ebot .maxconfidence
    (fun k ↦ □[k] (guardCodeB (templateCode (probe (inst (tauZoo k) .ebot .maxconfidence)))
      (pBot (instCode k .maxconfidence .ebot)) (pBot (instCode k .maxconfidence .ebot)) k)) .C :=
  FloorBitA.of _ (bitEventually.mono (fun k h₂ ↦ ebot_C_of (col_maxconfidence_defect k) h₂) col_maxconfidence_coop)

/-- `ebot × minconfidence` ‡ (Dupoc's row by the bridge): C. -/
@[tau_floor_bitA]
theorem ebotRowSpecA_minconfidence_floor : FloorBitA .ebot .minconfidence
    (fun k ↦ □[k] (guardCodeB (templateCode (probe (inst (tauZoo k) .ebot .minconfidence)))
      (pBot (instCode k .minconfidence .ebot)) (pBot (instCode k .minconfidence .ebot)) k)) .C :=
  FloorBitA.of _ (bitEventually.mono (fun k h₂ ↦ ebot_C_of (col_minconfidence_defect k) h₂) col_minconfidence_coop)

/-- `ebot × prudent` ‡ (base `dich_PrudentBot_vs_EBot`): settled C on this side — the exploit and reciprocity watches
fall on Prudent's instances at the defector and the cooperator (both D) and the mirror watch fires on the system
`.sys [pm 1 mirror, mm 0] 0` (`Tau/Entangled/EBotPrudent.lean`). Hinge: Prudent's outer probe of EBot's instance, in
Prudent's own frame. -/
@[tau_floor_bitA]
theorem ebotRowSpecA_prudent_floor : FloorBitA .ebot .prudent
    (fun k ↦ □[k] (guardCodeB (templateCode (probe (inst (tauZoo k) .ebot .prudent)))
      (pBot (instCode k .prudent .ebot)) (pBot (instCode k .prudent .ebot)) k)) .C :=
  entFloor_ebot_prudent

end ArithS.Tau
