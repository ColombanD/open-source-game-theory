import PrisonersDilemma.Tau.Theorems.TauDupoc.Helpers
import PrisonersDilemma.Tau.Theorems.TauEBot.Helpers
import PrisonersDilemma.Tau.Theorems.TauGuardian.Helpers

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

/-! ## The δ_C column (prover bits) -/

/-- δ_C bits. Zero rows: Defect (refutable), EBot (it EXPLOITS a cooperator), and
    GUARDIAN — the floor: its trusting C sits behind a failed punish-search. -/
def coopColBit : Tmpl → Bool
  | .defect   => false
  | .ebot     => false
  | .guardian => false
  | _         => true

theorem ps_probe_inst_coop {k : Nat} (hk : 2 ≤ k) (hkk : c_guard k + 3 ≤ k)
    (h6 : 6 ≤ k) (h10 : 10 ≤ k) :
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

/-! ## The δ_D column (prover bits) -/

/-- δ_D bits. Only the unconditional cooperator is exploitable. -/
def defectColBit : Tmpl → Bool
  | .coop => true
  | _     => false

theorem ps_probe_inst_defect {k : Nat} (hk : 2 ≤ k) :
    ∀ T, proofSearch k (probe (inst (tauZoo k) T .defect)) = defectColBit T
  | .coop     => ps_probe_constC hk
  | .defect   => ps_probe_constD k
  | .tftSim   => ps_simCopy_constD k
  | .tftPf    => ps_searchProbe_constD k k
  | .dupoc    => ps_searchProbe_constD k k
  | .ebot     => ps_probe_false_of_plays_D k
      (simWatchC_falls _ _ ⟨1, rfl⟩ (simWatchC_falls _ _ ⟨1, rfl⟩ ⟨1, rfl⟩))
  | .just     => ps_searchProbe_constD k k
  | .obot     => ps_probe_false_of_plays_D k obot_defect_plays_D
  | .guardian => ps_probe_false_of_plays_D k (guardian_defect_plays_D hk)

/-! ## The δ_L column (prover bits) — TauDupoc's AND TauJust's question -/

/-- δ_L bits. Zero rows: Defect; EBot and GUARDIAN (both floors); and OBot (it
    truly defects on Dupoc — the second watch sees Dupoc defect against the
    defector). The diagonal is the Löb quine, supplied as a hypothesis. -/
def dupocColBit : Tmpl → Bool
  | .defect   => false
  | .ebot     => false
  | .obot     => false
  | .guardian => false
  | _         => true

theorem ps_probe_inst_dupoc {k : Nat} (hk : 2 ≤ k) (hkk : c_guard k + 3 ≤ k)
    (hk7 : c_guard k + 7 ≤ k)
    (hquine : proofSearch k (probe (inst (tauZoo k) .dupoc .dupoc)) = true) :
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

/-! ## The GUARD column (probeD bits) — TauGuardian's question -/

/-- Guard bits: "does T PROVABLY DEFECT against the cooperator?" One rows: the
    constant defector, and EBot (its exploit-check FIRES on the cooperator, and the
    firing transcript is cheap — Guardian catches the exploiter red-handed). -/
def guardColBit : Tmpl → Bool
  | .defect => true
  | .ebot   => true
  | _       => false

theorem ps_probeD_inst_coop {k : Nat} (hk : 2 ≤ k) (hkk : c_guard k + 3 ≤ k)
    (h6 : 6 ≤ k) (h10 : 10 ≤ k) :
    ∀ T, proofSearch k (probeD (inst (tauZoo k) T .coop)) = guardColBit T
  | .coop     => ps_probeD_false_of_plays_C k ⟨1, rfl⟩
  | .defect   => ps_probeD_constD hk
  | .tftSim   => ps_probeD_false_of_plays_C k
      (entry_C_of_interp (Pf_sound _ _ (pf_simCopy_constC h6)))
  | .tftPf    => ps_probeD_false_of_plays_C k
      (entry_C_of_interp (Pf_sound _ _ (pf_searchProbe_constC hk hkk)))
  | .dupoc    => ps_probeD_false_of_plays_C k
      (entry_C_of_interp (Pf_sound _ _ (pf_searchProbe_constC hk hkk)))
  | .ebot     => ps_probeD_runCascadeConstC h6
  | .just     => ps_probeD_false_of_plays_C k
      (entry_C_of_interp (Pf_sound _ _ (pf_searchProbe_constC hk hkk)))
  | .obot     => ps_probeD_false_of_plays_C k
      (entry_C_of_interp (Pf_sound _ _ (pf_probe_obotConstC h10)))
  | .guardian => ps_probeD_false_of_plays_C k guardian_coop_plays_C

/-! ## The behavioral δ_C column (true plays) — TauTFTSim's and TauOBot's read -/

/-- TRUE plays vs the cooperator. Note `.guardian ↦ .C` against
    `coopColBit .guardian = false`: the floor made visible — the behavioral reader
    sees the cooperation the prover cannot cite. -/
def coopColPlay : Tmpl → Action
  | .defect => .D
  | .ebot   => .D
  | _       => .C

theorem inst_coop_plays {k : Nat} (hk : 2 ≤ k) (hkk : c_guard k + 3 ≤ k)
    (h6 : 6 ≤ k) (h10 : 10 ≤ k) :
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

/-! ## The behavioral δ_D column (true plays) — TauOBot's second watch -/

/-- TRUE plays vs the defector: only the unconditional cooperator cooperates. -/
def defectColPlay : Tmpl → Action
  | .coop => .C
  | _     => .D

theorem inst_defect_plays {k : Nat} (hk : 2 ≤ k) :
    ∀ T, ∃ N, eval N (.bot (inst (tauZoo k) T .defect)) (.bot (inst (tauZoo k) T .defect))
              (inst (tauZoo k) T .defect) = some (defectColPlay T)
  | .coop     => ⟨1, rfl⟩
  | .defect   => ⟨1, rfl⟩
  | .tftSim   => simCopy_plays _ _ ⟨1, rfl⟩
  | .tftPf    => searchProbe_plays_D _ _ (ps_probe_constD k)
  | .dupoc    => searchProbe_plays_D _ _ (ps_probe_constD k)
  | .ebot     => simWatchC_falls _ _ ⟨1, rfl⟩ (simWatchC_falls _ _ ⟨1, rfl⟩ ⟨1, rfl⟩)
  | .just     => searchProbe_plays_D _ _ (ps_probe_constD k)
  | .obot     => obot_defect_plays_D
  | .guardian => guardian_defect_plays_D hk

end PD.Tau
