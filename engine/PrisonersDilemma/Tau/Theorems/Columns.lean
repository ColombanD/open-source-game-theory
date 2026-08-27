import PrisonersDilemma.Tau.Theorems.TauDupoc.Helpers
import PrisonersDilemma.Tau.Theorems.TauEBot.Helpers
import PrisonersDilemma.Tau.Theorems.TauGuardian.Helpers
import PrisonersDilemma.Tau.Theorems.TauDBot.Helpers
import PrisonersDilemma.Tau.Theorems.TauCupodTroll.Helpers
import PrisonersDilemma.Tau.Theorems.TauCupod.Helpers
import PrisonersDilemma.Tau.Theorems.TauCIMCIC.Helpers
import PrisonersDilemma.Tau.Theorems.TauDIMCID.Helpers
import PrisonersDilemma.Tau.Theorems.TauMirror.Helpers
import PrisonersDilemma.Tau.Theorems.TauPrudent.Helpers
import PrisonersDilemma.Tau.Theorems.TauConfidence.Helpers

/-!
# Tau/Theorems/Columns — the consulted columns of the 9-template zoo

A column asks one question of EVERY zoo member; the specs consult five:

* **δ_C bits** (`ps_probe_inst_coop`) — "does T, seeing the cooperator, PROVABLY
  cooperate?": TauTFTPf's strategy, TauEBot's reciprocity stage.
* **δ_D bits** (`ps_probe_inst_defect`) — TauEBot's exploit stage.
* **δ_L bits** (`ps_probe_inst_dupoc`) — TauDupoc's self-probe AND TauJust's
  third-party probe (same objects, by name instead of by self).
* **guard bits** (`ps_probeD_inst_coop`) — "does T PROVABLY DEFECT vs the
  cooperator?": TauGuardian's punish-probe (the `test = .D` prover).
* **behavioral plays** (`inst_coop_plays`, `inst_defect_plays`) — TRUE plays of the
  δ_C / δ_D instances: TauTFTSim's copy and TauOBot's two defection watches.

The zoo's three Gödelian floors all sit in these tables, honestly as 0-bits over
TRUE cooperation: EBot's (δ_L — behind its failed exploit search) and Guardian's
two (δ_C and δ_L — behind its failed punish search). Guardian's floor is why
`coopColBit .guardian = false` while `coopColPlay .guardian = .C`: the FIRST
hypothesis on which the prover and behavioral readers disagree at large k — the
prover/behavioral split as an α-gap.
-/

open PD PD.BaseTheorems

namespace PD.Tau

/-! ## Per-cell composites the arms below need -/

/-- τ(Just)'s δ_L diagonal-adjacent cell: `inst .just .dupoc` probes THE QUINE, so
    its bit is Löb-gated — provable exactly when the quine's is. -/
theorem ps_probe_just_dupoc {k : Nat} (hkk : c_guard k + 3 ≤ k)
    (hquine : proofSearch k (probe (inst (tauZoo k) .dupoc .dupoc)) = true) :
    proofSearch k (probe (inst (tauZoo k) .just .dupoc)) = true :=
  (proofSearch_spec _ _).2 (Pf.atom
    ⟨PlaysProof.bot (PlaysProof.search_t ((proofSearch_spec _ _).1 hquine)
        PlaysProof.const),
      by
        have h1 : c_leaf = 1 := rfl
        have h2 : c_node = 1 := rfl
        have h3 : c_guard (tauZoo k).budget = c_guard k := rfl
        omega⟩)

/-- `inst .obot .dupoc` plays D: its first watch sees Dupoc-seeing-Coop cooperate
    (falls through), its second sees Dupoc-seeing-Defect defect (fires D). -/
theorem obot_dupoc_plays_D {k : Nat} (hk : 2 ≤ k) :
    ∃ N, eval N (.bot (inst (tauZoo k) .obot .dupoc)) (.bot (inst (tauZoo k) .obot .dupoc))
      (inst (tauZoo k) .obot .dupoc) = some Action.D :=
  simTestD_falls _ _
    (searchProbe_plays_C _ _ (ps_probe_constC hk))
    (simTestD_fires _ _ (searchProbe_plays_D _ _ (ps_probe_constD k)))

/-- `inst .obot .defect` plays D: its first watch sees the defector defect vs the
    cooperator — fires immediately. -/
theorem obot_defect_plays_D {k : Nat} :
    ∃ N, eval N (.bot (inst (tauZoo k) .obot .defect)) (.bot (inst (tauZoo k) .obot .defect))
      (inst (tauZoo k) .obot .defect) = some Action.D :=
  simTestD_fires _ _ ⟨1, rfl⟩

/-- `inst .guardian .defect` plays D: the punish-probe of the constant defector
    FIRES. -/
theorem guardian_defect_plays_D {k : Nat} (hk : 2 ≤ k) :
    ∃ N, eval N (.bot (inst (tauZoo k) .guardian .defect))
      (.bot (inst (tauZoo k) .guardian .defect))
      (inst (tauZoo k) .guardian .defect) = some Action.D :=
  searchProbeD_plays_D _ _ (ps_probeD_constD hk)

/-- `inst .guardian T` plays C whenever its punish-probe FAILS — here at the
    cooperator and at Dupoc (both probed instances truly cooperate, so the
    defection atom is false and unprovable). -/
theorem guardian_coop_plays_C {k : Nat} :
    ∃ N, eval N (.bot (inst (tauZoo k) .guardian .coop))
      (.bot (inst (tauZoo k) .guardian .coop))
      (inst (tauZoo k) .guardian .coop) = some Action.C :=
  searchProbeD_plays_C _ _ (ps_probeD_false_of_plays_C k ⟨1, rfl⟩)

/-- `inst .dbot .coop` plays D: its watch sees the constant cooperator cooperate
    even against a defector — the punish-fire. -/
theorem dbot_coop_plays_D {k : Nat} :
    ∃ N, eval N (.bot (inst (tauZoo k) .dbot .coop)) (.bot (inst (tauZoo k) .dbot .coop))
      (inst (tauZoo k) .dbot .coop) = some Action.D := by
  have h : ∃ N, eval N (.bot (inst (tauZoo k) .coop .defect))
      (.bot (inst (tauZoo k) .coop .defect)) (inst (tauZoo k) .coop .defect)
      = some Action.C := ⟨1, rfl⟩
  have hfire := simWatchC_fires (I := inst (tauZoo k) .coop .defect) (f := Action.D)
    (cont := .const Action.C) (.bot (inst (tauZoo k) .dbot .coop))
    (.bot (inst (tauZoo k) .dbot .coop)) h
  rw [show inst (tauZoo k) .dbot .coop
      = .ite (.sim (.bot (inst (tauZoo k) .coop .defect))
          (.bot (inst (tauZoo k) .coop .defect))) .C (.const .D) (.const .C)
      from inst_dbot_peel k .coop] at hfire ⊢
  exact hfire

/-- `inst .dbot T` plays C whenever its watch sees the probed δ_D instance DEFECT —
    the trusting default. -/
theorem dbot_plays_C_of_defect {k : Nat} (T : Tmpl)
    (h : ∃ N, eval N (.bot (inst (tauZoo k) T .defect)) (.bot (inst (tauZoo k) T .defect))
           (inst (tauZoo k) T .defect) = some Action.D) :
    ∃ N, eval N (.bot (inst (tauZoo k) .dbot T)) (.bot (inst (tauZoo k) .dbot T))
      (inst (tauZoo k) .dbot T) = some Action.C := by
  have htail : ∃ N, eval N (.bot (inst (tauZoo k) .dbot T))
      (.bot (inst (tauZoo k) .dbot T)) (.const Action.C) = some Action.C := ⟨1, rfl⟩
  have hfall := simWatchC_falls (I := inst (tauZoo k) T .defect) (f := Action.D)
    (cont := .const Action.C) (.bot (inst (tauZoo k) .dbot T))
    (.bot (inst (tauZoo k) .dbot T)) h htail
  rw [show inst (tauZoo k) .dbot T
      = .ite (.sim (.bot (inst (tauZoo k) T .defect)) (.bot (inst (tauZoo k) T .defect)))
          .C (.const .D) (.const .C) from inst_dbot_peel k T] at hfall ⊢
  exact hfall

/-- `inst .dbot .dbot` plays D — τ(DBot) PUNISHES ITSELF. Its watch runs
    `inst .dbot .defect`, which TRUSTS the defector (a defector is no pushover),
    and a cooperation-against-a-defector is exactly what the punisher fires on. -/
theorem dbot_selfWatch_fires {k : Nat} :
    ∃ N, eval N (.bot (inst (tauZoo k) .dbot .dbot)) (.bot (inst (tauZoo k) .dbot .dbot))
      (inst (tauZoo k) .dbot .dbot) = some Action.D := by
  have h : ∃ N, eval N (.bot (inst (tauZoo k) .dbot .defect))
      (.bot (inst (tauZoo k) .dbot .defect)) (inst (tauZoo k) .dbot .defect)
      = some Action.C := dbot_plays_C_of_defect .defect ⟨1, rfl⟩
  have hfire := simWatchC_fires (I := inst (tauZoo k) .dbot .defect) (f := Action.D)
    (cont := .const Action.C) (.bot (inst (tauZoo k) .dbot .dbot))
    (.bot (inst (tauZoo k) .dbot .dbot)) h
  rw [show inst (tauZoo k) .dbot .dbot
      = .ite (.sim (.bot (inst (tauZoo k) .dbot .defect))
          (.bot (inst (tauZoo k) .dbot .defect))) .C (.const .D) (.const .C)
      from inst_dbot_peel k .dbot] at hfire ⊢
  exact hfire

/-- `inst .dbot T` plays D whenever the probed δ_D instance COOPERATES — the
    punisher's fire condition. Generalizes `dbot_selfWatch_fires` (which is the
    `T = .dbot` case) to any trusting hypothesis. -/
theorem dbot_watch_fires_of_trust {k : Nat} (T : Tmpl)
    (h : ∃ N, eval N (.bot (inst (tauZoo k) T .defect)) (.bot (inst (tauZoo k) T .defect))
           (inst (tauZoo k) T .defect) = some Action.C) :
    ∃ N, eval N (.bot (inst (tauZoo k) .dbot T)) (.bot (inst (tauZoo k) .dbot T))
      (inst (tauZoo k) .dbot T) = some Action.D := by
  have hfire := simWatchC_fires (I := inst (tauZoo k) T .defect) (f := Action.D)
    (cont := .const Action.C) (.bot (inst (tauZoo k) .dbot T))
    (.bot (inst (tauZoo k) .dbot T)) h
  rw [show inst (tauZoo k) .dbot T
      = .ite (.sim (.bot (inst (tauZoo k) T .defect)) (.bot (inst (tauZoo k) T .defect)))
          .C (.const .D) (.const .C) from inst_dbot_peel k T] at hfire ⊢
  exact hfire

/-! ## The δ_C column (prover bits) -/

/-- δ_C bits. Zero rows: Defect (refutable), EBot (it EXPLOITS a cooperator), and
    GUARDIAN — the floor: its trusting C sits behind a failed punish-search. -/
def coopColBit : Tmpl → Bool
  -- τ(Mirror) COPIES the constant cooperator's C, and the copy is provable by
  -- transcript (`ps_probe_mirror_coop`) — no reading rule needed.
  | .prudent    => false
  | .mirror     => true
  | .dimcid     => false
  | .cupod      => false
  | .cupodTroll => false
  | .defect   => false
  | .ebot     => false
  | .guardian => false
  | .dbot     => false
  | _         => true

theorem ps_probe_inst_coop {k : Nat} (hk : 2 ≤ k) (hkk : c_guard k + 3 ≤ k)
    (h6 : 6 ≤ k) (h10 : 10 ≤ k) (hL : 100 * Nat.log2 k + 1000 ≤ k)
    (hcg : c_guard k + 20 ≤ k) :
    ∀ T, proofSearch k (probe (inst (tauZoo k) T .coop)) = coopColBit T
  | .coop     => ps_probe_constC hk
  | .defect   => ps_probe_constD k
  | .tftSim   => ps_simCopy_constC h6
  | .tftPf    => ps_searchProbe_constC hk hkk
  | .dupoc    => ps_searchProbe_constC hk hkk
  | .ebot     => ps_probe_false_of_plays_D k (simWatchC_fires _ _ ⟨1, rfl⟩)
  | .just     => ps_searchProbe_constC hk hkk
  | .obot     => ps_probe_obotConstC h10
  | .guardian => ps_probe_guardCell_false (le_refl k) _
  | .dbot     => ps_probe_false_of_plays_D k dbot_coop_plays_D
  | .cupod      => ps_probe_inst_cupod_coop_false (le_refl k)
  | .cupodTroll => ps_probe_inst_cupodTroll_false (le_refl k) _ (by decide)
  | .cimcic     => ps_probe_cimcic_coop hL (by omega)
  | .dimcid     => ps_probe_inst_dimcid_coop_false (le_refl k)
  | .prudent    => ps_probe_false_of_plays_D k prudent_coop_plays_D
  | .mirror     => ps_probe_mirror_coop (by omega)
  | .confidence => by rw [inst_confidence_eq_dupoc k .coop (by decide) (by decide) (by decide)]; exact ps_searchProbe_constC hk hkk

/-! ## The δ_D column (prover bits) -/

/-- δ_D bits. Only the unconditional cooperator is exploitable. -/
def defectColBit : Tmpl → Bool
  | .prudent    => false
  | .mirror     => false
  | .dimcid     => false
  | .cupod      => false
  | .cupodTroll => false
  | .coop => true
  | .dbot => true
  | _     => false

theorem ps_probe_inst_defect {k : Nat} (hk : 2 ≤ k) (hk6 : 6 ≤ k)
    (hL : 100 * Nat.log2 k + 1000 ≤ k) :
    ∀ T, proofSearch k (probe (inst (tauZoo k) T .defect)) = defectColBit T
  | .coop     => ps_probe_constC hk
  | .defect   => ps_probe_constD k
  | .tftSim   => ps_simCopy_constD k
  | .tftPf    => ps_searchProbe_constD k k
  | .dupoc    => ps_searchProbe_constD k k
  | .ebot     => ps_probe_false_of_plays_D k
      -- three watches now, all falling on the constant defector
      (simWatchC_falls _ _ ⟨1, rfl⟩ (simWatchC_falls _ _ ⟨1, rfl⟩
        (simWatchC_falls _ _ ⟨1, rfl⟩ ⟨1, rfl⟩)))
  | .just     => ps_searchProbe_constD k k
  | .obot     => ps_probe_false_of_plays_D k obot_defect_plays_D
  | .guardian => ps_probe_false_of_plays_D k (guardian_defect_plays_D hk)
  | .dbot     => (proofSearch_spec _ _).2 (pf_probe_dbotConstD hk6)
  | .cupod      => ps_probe_false_of_plays_D k (cupod_defect_plays_D hk)
  | .cupodTroll => ps_probe_inst_cupodTroll_false (le_refl k) _ (by decide)
  | .cimcic     => ps_probe_false_of_plays_D k cimcic_defect_plays_D
  | .dimcid     => ps_probe_inst_dimcid_defect_false hL
  | .prudent    => ps_probe_false_of_plays_D k prudent_defect_plays_D
  | .mirror     => ps_probe_false_of_plays_D k mirror_defect_plays_D
  | .confidence => by rw [inst_confidence_eq_dupoc k .defect (by decide) (by decide) (by decide)]; exact ps_searchProbe_constD k k

/-! ## The δ_L column (prover bits) — TauDupoc's AND TauJust's question -/

/-- δ_L bits. Zero rows: Defect; EBot and GUARDIAN (both floors); and OBot (it
    truly defects on Dupoc — the second watch sees Dupoc defect against the
    defector). The diagonal is the Löb quine, supplied as a hypothesis. -/
def dupocColBit : Tmpl → Bool
  -- the mirror×dupoc ENTANGLED cell: a mutual SIMULATION (mirror copies, dupoc
  -- proves), the tau image of base `outcome_DupocBot_vs_MirrorBot = (C, C)`.
  -- Löb-gated, so it enters as a hypothesis like every other Löb bit.
  | .prudent    => false
  | .mirror     => true
  | .dimcid     => false
  | .cupod      => false
  | .cupodTroll => false
  | .defect   => false
  | .ebot     => false
  | .obot     => false
  | .guardian => false
  | .dbot     => false
  | _         => true

theorem ps_probe_inst_dupoc {k : Nat} (hk : 2 ≤ k) (hkk : c_guard k + 3 ≤ k)
    (hk7 : c_guard k + 7 ≤ k)
    (hquine : proofSearch k (probe (inst (tauZoo k) .dupoc .dupoc)) = true)
    -- the CIMCIC×Dupoc entangled bit is LÖB-GATED (`ps_probe_inst_cimcic_dupoc`),
    -- so it enters as a hypothesis exactly like the quine bit above; the
    -- Cupod×Dupoc one is CLOSED BY THE FLOOR (a theorem, used in the `.cupod` arm)
    (hcim : proofSearch k (probe (inst (tauZoo k) .cimcic .dupoc))
      = dupocColBit .cimcic)
    -- the mirror×dupoc entangled bit (mutual simulation), Löb-gated
    (hmir : proofSearch k (probe (inst (tauZoo k) .mirror .dupoc))
      = dupocColBit .mirror)
    -- the confidence×dupoc entangled bit (two Dupoc-spec self-probers, symmetric
    -- mutual Löb — `ps_probe_inst_confidence_dupoc`), Löb-gated (2026-08-27)
    (hconf : proofSearch k (probe (inst (tauZoo k) .confidence .dupoc))
      = dupocColBit .confidence) :
    ∀ T, proofSearch k (probe (inst (tauZoo k) T .dupoc)) = dupocColBit T
  | .coop     => ps_probe_constC hk
  | .defect   => ps_probe_constD k
  | .tftSim   => (proofSearch_spec _ _).2 (pf_simCopy_searchProbeC hk hk7)
  | .tftPf    => (proofSearch_spec _ _).2 (pf_searchProbe_searchProbeC hk hkk hkk)
  | .dupoc    => hquine
  | .ebot     => ps_probe_inst_ebot_dupoc_false (le_refl k)
  | .just     => ps_probe_just_dupoc hkk hquine
  | .obot     => ps_probe_false_of_plays_D k (obot_dupoc_plays_D hk)
  | .guardian => ps_probe_guardCell_false (le_refl k) _
  | .dbot     => ps_probe_inst_dbot_dupoc_false (le_refl k)
  | .cupod      => ps_probe_inst_cupod_dupoc_false (le_refl k)
  | .cupodTroll => ps_probe_inst_cupodTroll_false (le_refl k) _ (by decide)
  | .cimcic     => hcim
  | .dimcid     => ps_probe_inst_dimcid_dupoc_false (le_refl k)
  | .prudent    => ps_probe_inst_prudent_dupoc_false
  | .mirror     => hmir
  | .confidence => hconf

/-! ## The GUARD column (probeD bits) — TauGuardian's question -/

/-- Guard bits: "does T PROVABLY DEFECT against the cooperator?" One rows: the
    constant defector, and EBot (its exploit-check FIRES on the cooperator, and the
    firing transcript is cheap — Guardian catches the exploiter red-handed). -/
def guardColBit : Tmpl → Bool
  | .prudent    => false
  | .mirror     => false
  | .dimcid     => false
  | .cupod      => false
  | .cupodTroll => false
  | .defect => true
  | .ebot   => true
  | .dbot   => true
  | _       => false

theorem ps_probeD_inst_coop {k : Nat} (hk : 2 ≤ k) (hkk : c_guard k + 3 ≤ k)
    (h6 : 6 ≤ k) (h10 : 10 ≤ k) (hL : 100 * Nat.log2 k + 1000 ≤ k) :
    ∀ T, proofSearch k (probeD (inst (tauZoo k) T .coop)) = guardColBit T
  | .coop     => ps_probeD_false_of_plays_C k ⟨1, rfl⟩
  | .defect   => ps_probeD_constD hk
  | .tftSim   => ps_probeD_false_of_plays_C k
      (entry_C_of_interp (Pf_sound _ _ (pf_simCopy_constC h6)))
  | .tftPf    => ps_probeD_false_of_plays_C k
      (entry_C_of_interp (Pf_sound _ _ (pf_searchProbe_constC hk hkk)))
  | .dupoc    => ps_probeD_false_of_plays_C k
      (entry_C_of_interp (Pf_sound _ _ (pf_searchProbe_constC hk hkk)))
  | .ebot     => ps_probeD_runCascadeConstC h6 _
  | .just     => ps_probeD_false_of_plays_C k
      (entry_C_of_interp (Pf_sound _ _ (pf_searchProbe_constC hk hkk)))
  | .obot     => ps_probeD_false_of_plays_C k
      (entry_C_of_interp (Pf_sound _ _ (pf_probe_obotConstC h10)))
  | .guardian => ps_probeD_false_of_plays_C k guardian_coop_plays_C
  | .dbot     => ps_probeD_dbotConstC h6
  | .cupod      => ps_probeD_false_of_plays_C k cupod_coop_plays_C
  | .cupodTroll => ps_probeD_inst_cupodTroll_false k _ (by decide)
  | .cimcic     => ps_probeD_false_of_plays_C k (cimcic_coop_plays_C hL)
  | .dimcid     => ps_probeD_inst_dimcid_coop_false
  | .prudent    => ps_probeD_inst_prudent_coop_false (le_refl k)
  | .mirror     => ps_probeD_false_of_plays_C k mirror_coop_plays_C
  | .confidence => by
      rw [inst_confidence_eq_dupoc k .coop (by decide) (by decide) (by decide)]
      exact ps_probeD_false_of_plays_C k (entry_C_of_interp (Pf_sound _ _ (pf_searchProbe_constC hk hkk)))

/-! ## The δ_Cu GUARD column (probeD bits) — τ(Cupod)'s question

"Does T, seeing CUPOD, provably DEFECT?" Cupod punishes exactly what it can convict.
Only ONE row besides the diagonal is `true`: the constant defector (a trivial atom).
OBot's cell is the interesting near-miss — it truly plays D (its second watch
catches Cupod punishing the defector) but the certificate must embed watch 1's
FALL, i.e. Cupod's floor-priced trust, so it is itself uncitable. The DIAGONAL is Löbian self-defection and enters as a
hypothesis, like every Löb bit; the `.dupoc` and `.just` rows are OPEN (they read
the entangled cell) and enter as hypotheses for a different reason — see
`TauCupod/Helpers`.

Note `tftPf ↦ false` over a genuine D: Cupod's trust is floor-priced, so TFTPf's
probe fails and it defects — but that defection is an ELSE-play, itself
floor-priced (`ps_probeD_searchProbe_false`). A true D that no prover can cite. -/

/-- δ_Cu guard bits. -/
def cupodColBit : Tmpl → Bool
  | .defect => true
  | .cupod  => true
  -- the ALIGNED entangled pair (2026-08-21): DIMCID wants Cupod to defect and
  -- Cupod fires D; Cupod wants DIMCID to defect and DIMCID fires D. Both
  -- guards feed each other, so mutual bounded Löb closes the cycle on MUTUAL
  -- DEFECTION — the first ALIGNED-on-D pair in the zoo (`cimcic × dupoc` is
  -- the aligned-on-C one). The bit is Löb-gated, hence a hypothesis below.
  | .dimcid => true
  -- RESTATED 2026-08-24: with `proveEq` asking about the HYPOTHESIS, the troll
  -- recognises Cupod and defects on it — base CupodTrollBot's whole point, which
  -- the old `.opp`-pronoun guard could never express.
  | .cupodTroll => true
  -- the mirror×cupod ENTANGLED cell: the D-cycle is the self-supporting one
  -- (Cupod punishes, Mirror copies the punishment), so bounded Löb closes it on
  -- MUTUAL DEFECTION — the tau image of base
  -- `outcome_CupodBot_vs_MirrorBot = (D, D)`. Löb-gated, hypothesis below.
  | .prudent    => false
  | .mirror => true
  | _       => false

theorem ps_probeD_inst_cupod {k : Nat} (hk : 2 ≤ k) (hkk : c_guard k + 3 ≤ k)
    (hquine : proofSearch k (probeD (inst (tauZoo k) .cupod .cupod)) = true)
    -- the ALIGNED dimcid×cupod pair: mutual Löb on defection, gated like every
    -- other Löb bit (see `TauDIMCID/Helpers`, "The ENTANGLED cells")
    (hdc : proofSearch k (probeD (inst (tauZoo k) .dimcid .cupod))
      = cupodColBit .dimcid)
    -- the mirror×cupod entangled bit, Löb-gated
    (hmirCu : proofSearch k (probeD (inst (tauZoo k) .mirror .cupod))
      = cupodColBit .mirror) :
    ∀ T, proofSearch k (probeD (inst (tauZoo k) T .cupod)) = cupodColBit T
  | .coop       => ps_probeD_false_of_plays_C k ⟨1, rfl⟩
  | .defect     => ps_probeD_constD hk
  | .tftSim     => ps_probeD_false_of_plays_C k (simCopy_plays _ _ cupod_coop_plays_C)
  | .tftPf      => ps_probeD_searchProbe_false (le_refl k) _
  | .dupoc      => ps_probeD_inst_dupoc_cupod_false (le_refl k)
  | .ebot       => ps_probeD_false_of_plays_C k
      (simWatchC_falls _ _ (cupod_defect_plays_D hk)
        (simWatchC_fires _ _ cupod_coop_plays_C))
  -- τ(Just)'s PLAY here is open (it probes the entangled cell), but its DEFECTION
  -- bit is false regardless: the D is an else-play, floored either way
  | .just       => ps_probeD_searchProbe_false (le_refl k) _
  -- OBot truly plays D here (its SECOND watch catches Cupod punishing the
  -- defector), but the certificate must first certify watch 1 FALLING — i.e. that
  -- Cupod trusts the cooperator — and THAT is floor-priced
  -- (`ps_probe_inst_cupod_coop_false`). An embedded floor one level up: a true D
  -- that no prover can cite at budget k.
  | .obot       => ps_probeD_obotCupod_false (le_refl k)
  | .guardian   => ps_probeD_false_of_plays_C k
      (searchProbeD_plays_C _ _ (ps_probeD_false_of_plays_C k cupod_coop_plays_C))
  | .dbot       => ps_probeD_false_of_plays_C k
      (dbot_plays_C_of_defect .cupod (cupod_defect_plays_D hk))
  -- RESTATED 2026-08-24: the identity guard now fires at `.cupod`, so the
  -- troll DEFECTS here and its defection has a cheap positive transcript
  | .cupodTroll => ps_probeD_inst_cupodTroll_cupod (by omega) hkk
  | .cupod      => hquine
  | .cimcic     => ps_probeD_inst_cimcic_cupod_false (le_refl k)
  | .dimcid     => hdc
  | .prudent    => ps_probeD_inst_prudent_cupod_false (le_refl k)
  | .mirror     => hmirCu
  | .confidence => by rw [inst_confidence_eq_dupoc k .cupod (by decide) (by decide) (by decide)]; exact ps_probeD_inst_dupoc_cupod_false (le_refl k)

/-! ## The behavioral δ_C column (true plays) — TauTFTSim's and TauOBot's read -/

/-- TRUE plays vs the cooperator. Note `.guardian ↦ .C` against
    `coopColBit .guardian = false`: the floor made visible — the behavioral reader
    sees the cooperation the prover cannot cite. -/
def coopColPlay : Tmpl → Action
  | .prudent    => .D
  | .mirror     => .C
  | .dimcid     => .C
  | .cupod      => .C
  | .cupodTroll => .C
  | .defect => .D
  | .ebot   => .D
  | .dbot   => .D
  | _       => .C

theorem inst_coop_plays {k : Nat} (hk : 2 ≤ k) (hkk : c_guard k + 3 ≤ k)
    (h6 : 6 ≤ k) (h10 : 10 ≤ k) (hL : 100 * Nat.log2 k + 1000 ≤ k) :
    ∀ T, ∃ N, eval N (.bot (inst (tauZoo k) T .coop)) (.bot (inst (tauZoo k) T .coop))
              (inst (tauZoo k) T .coop) = some (coopColPlay T)
  | .coop     => ⟨1, rfl⟩
  | .defect   => ⟨1, rfl⟩
  | .tftSim   => entry_C_of_interp (Pf_sound _ _ (pf_simCopy_constC h6))
  | .tftPf    => entry_C_of_interp (Pf_sound _ _ (pf_searchProbe_constC hk hkk))
  | .dupoc    => entry_C_of_interp (Pf_sound _ _ (pf_searchProbe_constC hk hkk))
  | .ebot     => simWatchC_fires _ _ ⟨1, rfl⟩
  | .just     => entry_C_of_interp (Pf_sound _ _ (pf_searchProbe_constC hk hkk))
  | .obot     => entry_C_of_interp (Pf_sound _ _ (pf_probe_obotConstC h10))
  | .guardian => guardian_coop_plays_C
  | .dbot     => dbot_coop_plays_D
  | .cupod      => cupod_coop_plays_C
  | .cupodTroll => cupodTroll_plays_C _ (by decide)
  | .cimcic     => cimcic_coop_plays_C hL
  | .dimcid     => dimcid_coop_plays_C
  | .prudent    => prudent_coop_plays_D
  | .mirror     => mirror_coop_plays_C
  | .confidence => by rw [inst_confidence_eq_dupoc k .coop (by decide) (by decide) (by decide)]; exact entry_C_of_interp (Pf_sound _ _ (pf_searchProbe_constC hk hkk))

/-! ## The behavioral δ_D column (true plays) — TauOBot's second watch -/

/-- TRUE plays vs the defector: only the unconditional cooperator cooperates. -/
def defectColPlay : Tmpl → Action
  | .prudent    => .D
  | .mirror     => .D
  | .dimcid     => .D
  | .cupod      => .D
  | .cupodTroll => .C
  | .coop => .C
  | .dbot => .C
  | _     => .D

theorem inst_defect_plays {k : Nat} (hk : 2 ≤ k)
    (hL : 100 * Nat.log2 k + 1000 ≤ k) :
    ∀ T, ∃ N, eval N (.bot (inst (tauZoo k) T .defect)) (.bot (inst (tauZoo k) T .defect))
              (inst (tauZoo k) T .defect) = some (defectColPlay T)
  | .coop     => ⟨1, rfl⟩
  | .defect   => ⟨1, rfl⟩
  | .tftSim   => simCopy_plays _ _ ⟨1, rfl⟩
  | .tftPf    => searchProbe_plays_D _ _ (ps_probe_constD k)
  | .dupoc    => searchProbe_plays_D _ _ (ps_probe_constD k)
  | .ebot     => simWatchC_falls _ _ ⟨1, rfl⟩ (simWatchC_falls _ _ ⟨1, rfl⟩
      (simWatchC_falls _ _ ⟨1, rfl⟩ ⟨1, rfl⟩))
  | .just     => searchProbe_plays_D _ _ (ps_probe_constD k)
  | .obot     => obot_defect_plays_D
  | .guardian => guardian_defect_plays_D hk
  | .dbot     => dbot_plays_C_of_defect .defect ⟨1, rfl⟩
  | .cupod      => cupod_defect_plays_D hk
  | .cupodTroll => cupodTroll_plays_C _ (by decide)
  | .cimcic     => cimcic_defect_plays_D
  | .dimcid     => dimcid_defect_plays_D hL
  | .prudent    => prudent_defect_plays_D
  | .mirror     => mirror_defect_plays_D
  | .confidence => by rw [inst_confidence_eq_dupoc k .defect (by decide) (by decide) (by decide)]; exact searchProbe_plays_D _ _ (ps_probe_constD k)

end PD.Tau
