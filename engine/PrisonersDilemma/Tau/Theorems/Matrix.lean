import PrisonersDilemma.Tau.Theorems.TauCooperate.Phase
import PrisonersDilemma.Tau.Theorems.TauDefect.Phase
import PrisonersDilemma.Tau.Theorems.TauTFTSim.Phase
import PrisonersDilemma.Tau.Theorems.TauTFTPf.Phase
import PrisonersDilemma.Tau.Theorems.TauDupoc.Phase
import PrisonersDilemma.Tau.Theorems.TauJust.Phase
import PrisonersDilemma.Tau.Theorems.TauEBot.Phase
import PrisonersDilemma.Tau.Theorems.TauOBot.Phase
import PrisonersDilemma.Tau.Theorems.TauGuardian.Phase
import PrisonersDilemma.Tau.Theorems.TauDBot.Phase
import PrisonersDilemma.Tau.Theorems.TauCIMCIC.Phase
import PrisonersDilemma.Tau.Theorems.TauCupod.Phase
import PrisonersDilemma.Tau.Theorems.TauCupodTroll.Phase

/-!
# Tau/Theorems/Matrix — the outcome matrix of the 9-template zoo

Every cell is two phase theorems glued by `outcome_of_ex_plays` (tau players are
`.opp`-free, so a match is two independent plays — which is why this is ONE file
while the base zoo uses per-pair files).

**The α-regime ladder** (each bot's cooperation boundary, from the phase theorems):

    obotMass = wC      dupMass ≤ pfMass ≤ simMass = guardMass
    eMass ≤ simMass    (eMass and pfMass are INCOMPARABLE since the 2026-08-19
                        run-mode EBot: they differ by wC vs wGuardian)

The headline bands the 9-zoo adds:

* **the MODALITY-SPLIT band** `pfMass < θ ≤ simMass` (nonempty iff `w .guardian > 0`):
  the behavioral TFT still cooperates while its prover twin has flipped — Guardian's
  floor-priced cooperation counts for the simulator and not for the prover, so the
  prover/behavioral split is finally an α-gap;
* **the TRUST band** `eMass < θ ≤ guardMass` (nonempty iff `w .coop > 0` —
  guardMass = eMass + wC since the run-mode EBot): the exploiter has flipped while
  the norm enforcer still trusts — `(D, C)`, Guardian pays for failing to convict.
-/

open PD PD.Tau PD.BaseTheorems

namespace PD.Theorems.Tau

/-- The constants' total mass. -/
private abbrev fullMass (w : Tmpl → Nat) : Nat :=
  w .coop + (w .defect + (w .tftSim + (w .tftPf + (w .dupoc + (w .ebot +
    (w .just + (w .obot + (w .guardian + (w .dbot + (w .cupodTroll + (w .cupod +
      (w .cimcic + (w .dimcid + w .mirror)))))))))))))

/-! ## Constants -/

theorem outcome_TauCooperate_vs_TauCooperate (k : Nat) (w : Tmpl → Nat) (θ : Nat)
    (hθ : θ ≤ fullMass w) :
    ∃ N, outcome N (TauBotZ k .coop w θ) (TauBotZ k .coop w θ) = some (.C, .C) :=
  outcome_of_ex_plays ((tauCooperate_phase k w θ _).1 hθ)
    ((tauCooperate_phase k w θ _).1 hθ)

theorem outcome_TauCooperate_vs_TauDefect (k : Nat) (w : Tmpl → Nat) (θ : Nat)
    (hθ : θ ≤ fullMass w) (hθ0 : θ ≠ 0) :
    ∃ N, outcome N (TauBotZ k .coop w θ) (TauBotZ k .defect w θ) = some (.C, .D) :=
  outcome_of_ex_plays ((tauCooperate_phase k w θ _).1 hθ)
    ((tauDefect_phase k w θ _).2 hθ0)

theorem outcome_TauDefect_vs_TauCooperate (k : Nat) (w : Tmpl → Nat) (θ : Nat)
    (hθ : θ ≤ fullMass w) (hθ0 : θ ≠ 0) :
    ∃ N, outcome N (TauBotZ k .defect w θ) (TauBotZ k .coop w θ) = some (.D, .C) :=
  outcome_of_ex_plays ((tauDefect_phase k w θ _).2 hθ0)
    ((tauCooperate_phase k w θ _).1 hθ)

theorem outcome_TauDefect_vs_TauDefect (k : Nat) (w : Tmpl → Nat) (θ : Nat)
    (hθ0 : θ ≠ 0) :
    ∃ N, outcome N (TauBotZ k .defect w θ) (TauBotZ k .defect w θ) = some (.D, .D) :=
  outcome_of_ex_plays ((tauDefect_phase k w θ _).2 hθ0)
    ((tauDefect_phase k w θ _).2 hθ0)

/-! ## The cooperators' self-plays and pairs -/

theorem outcome_TauTFTPf_vs_TauTFTPf {k : Nat} (hk : 2 ≤ k) (hkk : c_guard k + 3 ≤ k)
    (h6 : 6 ≤ k) (h10 : 10 ≤ k) (hL : 100 * Nat.log2 k + 1000 ≤ k) (hcg : c_guard k + 20 ≤ k) (θ : Nat) (w : Tmpl → Nat) (hθ : θ ≤ pfMass w) :
    ∃ N, outcome N (TauBotZ k .tftPf w θ) (TauBotZ k .tftPf w θ) = some (.C, .C) :=
  outcome_of_ex_plays ((tauTFTPf_phase hk hkk h6 h10 hL hcg θ w _).1 hθ)
    ((tauTFTPf_phase hk hkk h6 h10 hL hcg θ w _).1 hθ)

theorem outcome_TauTFTSim_vs_TauTFTSim {k : Nat} (hk : 2 ≤ k) (hkk : c_guard k + 3 ≤ k)
    (h6 : 6 ≤ k) (h10 : 10 ≤ k) (hL : 100 * Nat.log2 k + 1000 ≤ k) (hcg : c_guard k + 20 ≤ k) (θ : Nat) (w : Tmpl → Nat) (hθ : θ ≤ simMass w) :
    ∃ N, outcome N (TauBotZ k .tftSim w θ) (TauBotZ k .tftSim w θ) = some (.C, .C) :=
  outcome_of_ex_plays ((tauTFTSim_phase hk hkk h6 h10 hL hcg θ w _).1 hθ)
    ((tauTFTSim_phase hk hkk h6 h10 hL hcg θ w _).1 hθ)

theorem outcome_TauTFTPf_vs_TauTFTSim {k : Nat} (hk : 2 ≤ k) (hkk : c_guard k + 3 ≤ k)
    (h6 : 6 ≤ k) (h10 : 10 ≤ k) (hL : 100 * Nat.log2 k + 1000 ≤ k) (hcg : c_guard k + 20 ≤ k) (θ : Nat) (w : Tmpl → Nat) (hθ : θ ≤ pfMass w) :
    ∃ N, outcome N (TauBotZ k .tftPf w θ) (TauBotZ k .tftSim w θ) = some (.C, .C) :=
  outcome_of_ex_plays ((tauTFTPf_phase hk hkk h6 h10 hL hcg θ w _).1 hθ)
    ((tauTFTSim_phase hk hkk h6 h10 hL hcg θ w _).1
      (by simp only [pfMass, simMass] at *; omega))

theorem outcome_TauTFTSim_vs_TauTFTPf {k : Nat} (hk : 2 ≤ k) (hkk : c_guard k + 3 ≤ k)
    (h6 : 6 ≤ k) (h10 : 10 ≤ k) (hL : 100 * Nat.log2 k + 1000 ≤ k) (hcg : c_guard k + 20 ≤ k) (θ : Nat) (w : Tmpl → Nat) (hθ : θ ≤ pfMass w) :
    ∃ N, outcome N (TauBotZ k .tftSim w θ) (TauBotZ k .tftPf w θ) = some (.C, .C) :=
  outcome_of_ex_plays
    ((tauTFTSim_phase hk hkk h6 h10 hL hcg θ w _).1
      (by simp only [pfMass, simMass] at *; omega))
    ((tauTFTPf_phase hk hkk h6 h10 hL hcg θ w _).1 hθ)

/-! ## THE MODALITY-SPLIT BAND — `pfMass < θ ≤ simMass` (nonempty iff `w .guardian > 0`)

The same base strategy, lifted behaviorally vs by proof, DISAGREES: the simulator
still counts Guardian's true-but-floor-priced cooperation, the prover cannot. -/

theorem outcome_TauTFTSim_vs_TauTFTPf_band {k : Nat} (hk : 2 ≤ k)
    (hkk : c_guard k + 3 ≤ k) (h6 : 6 ≤ k) (h10 : 10 ≤ k)
    (hL : 100 * Nat.log2 k + 1000 ≤ k) (hcg : c_guard k + 20 ≤ k) (θ : Nat) (w : Tmpl → Nat)
    (hlo : ¬ θ ≤ pfMass w) (hhi : θ ≤ simMass w) :
    ∃ N, outcome N (TauBotZ k .tftSim w θ) (TauBotZ k .tftPf w θ) = some (.C, .D) :=
  outcome_of_ex_plays ((tauTFTSim_phase hk hkk h6 h10 hL hcg θ w _).1 hhi)
    ((tauTFTPf_phase hk hkk h6 h10 hL hcg θ w _).2 hlo)

theorem outcome_TauTFTPf_vs_TauTFTSim_band {k : Nat} (hk : 2 ≤ k)
    (hkk : c_guard k + 3 ≤ k) (h6 : 6 ≤ k) (h10 : 10 ≤ k)
    (hL : 100 * Nat.log2 k + 1000 ≤ k) (hcg : c_guard k + 20 ≤ k) (θ : Nat) (w : Tmpl → Nat)
    (hlo : ¬ θ ≤ pfMass w) (hhi : θ ≤ simMass w) :
    ∃ N, outcome N (TauBotZ k .tftPf w θ) (TauBotZ k .tftSim w θ) = some (.D, .C) :=
  outcome_of_ex_plays ((tauTFTPf_phase hk hkk h6 h10 hL hcg θ w _).2 hlo)
    ((tauTFTSim_phase hk hkk h6 h10 hL hcg θ w _).1 hhi)

/-! ## The Löb-gated cells -/

theorem outcome_TauDupoc_vs_TauDupoc :
    ∃ k₂, ∀ k, k₂ < k →
      -- the mirror×dupoc entangled cell, Löb-gated (see `TauDupoc/Phase`)
      ∀ (hmir : proofSearch k (probe (inst (tauZoo k) .mirror .dupoc))
          = dupocColBit .mirror)
        (hmirP : ∃ N, eval N (.bot (inst (tauZoo k) .dupoc .mirror))
          (.bot (inst (tauZoo k) .dupoc .mirror)) (inst (tauZoo k) .dupoc .mirror)
          = some (dupocRow .mirror)),
      ∀ θ (w : Tmpl → Nat), θ ≤ dupMass w →
      ∃ N, outcome N (TauBotZ k .dupoc w θ) (TauBotZ k .dupoc w θ) = some (.C, .C) := by
  obtain ⟨k₂, h⟩ := tauDupoc_phase
  exact ⟨k₂, fun k hk hmir hmirP θ w hθ =>
    outcome_of_ex_plays ((h k hk hmir hmirP θ w _).1 hθ)
      ((h k hk hmir hmirP θ w _).1 hθ)⟩

theorem outcome_TauJust_vs_TauJust :
    ∃ k₂, ∀ k, k₂ < k →
      ∀ (hmir : proofSearch k (probe (inst (tauZoo k) .mirror .dupoc))
          = dupocColBit .mirror),
      ∀ θ (w : Tmpl → Nat), θ ≤ dupMass w →
      ∃ N, outcome N (TauBotZ k .just w θ) (TauBotZ k .just w θ) = some (.C, .C) := by
  obtain ⟨k₂, h⟩ := tauJust_phase
  exact ⟨k₂, fun k hk hmir θ w hθ =>
    outcome_of_ex_plays ((h k hk hmir θ w _).1 hθ) ((h k hk hmir θ w _).1 hθ)⟩

/-- Self-based and norm-based reciprocity cooperate — two Löb gates, one threshold
    (the max of the two). -/
theorem outcome_TauDupoc_vs_TauJust :
    ∃ k₂, ∀ k, k₂ < k →
      ∀ (hmir : proofSearch k (probe (inst (tauZoo k) .mirror .dupoc))
          = dupocColBit .mirror)
        (hmirP : ∃ N, eval N (.bot (inst (tauZoo k) .dupoc .mirror))
          (.bot (inst (tauZoo k) .dupoc .mirror)) (inst (tauZoo k) .dupoc .mirror)
          = some (dupocRow .mirror)),
      ∀ θ (w : Tmpl → Nat), θ ≤ dupMass w →
      ∃ N, outcome N (TauBotZ k .dupoc w θ) (TauBotZ k .just w θ) = some (.C, .C) := by
  obtain ⟨kD, hD⟩ := tauDupoc_phase
  obtain ⟨kJ, hJ⟩ := tauJust_phase
  exact ⟨max kD kJ, fun k hk hmir hmirP θ w hθ =>
    outcome_of_ex_plays
      ((hD k (lt_of_le_of_lt (Nat.le_max_left _ _) hk) hmir hmirP θ w _).1 hθ)
      ((hJ k (lt_of_le_of_lt (Nat.le_max_right _ _) hk) hmir θ w _).1 hθ)⟩

theorem outcome_TauDupoc_vs_TauTFTPf :
    ∃ k₂, ∀ k, k₂ < k →
      ∀ (hmir : proofSearch k (probe (inst (tauZoo k) .mirror .dupoc))
          = dupocColBit .mirror)
        (hmirP : ∃ N, eval N (.bot (inst (tauZoo k) .dupoc .mirror))
          (.bot (inst (tauZoo k) .dupoc .mirror)) (inst (tauZoo k) .dupoc .mirror)
          = some (dupocRow .mirror)),
      2 ≤ k → c_guard k + 3 ≤ k → 6 ≤ k → 10 ≤ k →
      100 * Nat.log2 k + 1000 ≤ k → c_guard k + 20 ≤ k →
      ∀ θ (w : Tmpl → Nat), θ ≤ dupMass w →
      ∃ N, outcome N (TauBotZ k .dupoc w θ) (TauBotZ k .tftPf w θ) = some (.C, .C) := by
  obtain ⟨k₂, h⟩ := tauDupoc_phase
  exact ⟨k₂, fun k hk hmir hmirP hk2 hkk h6 h10 hL hcg θ w hθ =>
    outcome_of_ex_plays ((h k hk hmir hmirP θ w _).1 hθ)
      ((tauTFTPf_phase hk2 hkk h6 h10 hL hcg θ w _).1
        (by simp only [dupMass, pfMass] at *; omega))⟩

/-! ## τ(EBot)'s cells -/

theorem outcome_TauEBot_vs_TauEBot_coop {k : Nat} (hk : 2 ≤ k) (hkk : c_guard k + 3 ≤ k)
    (h6 : 6 ≤ k) (h10 : 10 ≤ k) (hL : 100 * Nat.log2 k + 1000 ≤ k) (hcg : c_guard k + 20 ≤ k) (θ : Nat) (w : Tmpl → Nat) (hθ : θ ≤ eMass w) :
    ∃ N, outcome N (TauBotZ k .ebot w θ) (TauBotZ k .ebot w θ) = some (.C, .C) :=
  outcome_of_ex_plays ((tauEBot_phase hk hkk h6 h10 hL hcg θ w _).1 hθ)
    ((tauEBot_phase hk hkk h6 h10 hL hcg θ w _).1 hθ)

theorem outcome_TauEBot_vs_TauEBot_high {k : Nat} (hk : 2 ≤ k) (hkk : c_guard k + 3 ≤ k)
    (h6 : 6 ≤ k) (h10 : 10 ≤ k) (hL : 100 * Nat.log2 k + 1000 ≤ k) (hcg : c_guard k + 20 ≤ k) (θ : Nat) (w : Tmpl → Nat) (hθ : ¬ θ ≤ eMass w) :
    ∃ N, outcome N (TauBotZ k .ebot w θ) (TauBotZ k .ebot w θ) = some (.D, .D) :=
  outcome_of_ex_plays ((tauEBot_phase hk hkk h6 h10 hL hcg θ w _).2 hθ)
    ((tauEBot_phase hk hkk h6 h10 hL hcg θ w _).2 hθ)

/-- The exploiter band against the prover TFT (`eMass < θ ≤ pfMass`, nonempty iff
    `w .coop > w .guardian` — the two masses differ by wC vs wGuardian since the
    run-mode EBot). -/
theorem outcome_TauTFTPf_vs_TauEBot_band {k : Nat} (hk : 2 ≤ k) (hkk : c_guard k + 3 ≤ k)
    (h6 : 6 ≤ k) (h10 : 10 ≤ k) (hL : 100 * Nat.log2 k + 1000 ≤ k) (hcg : c_guard k + 20 ≤ k) (θ : Nat) (w : Tmpl → Nat)
    (hlo : ¬ θ ≤ eMass w) (hhi : θ ≤ pfMass w) :
    ∃ N, outcome N (TauBotZ k .tftPf w θ) (TauBotZ k .ebot w θ) = some (.C, .D) :=
  outcome_of_ex_plays ((tauTFTPf_phase hk hkk h6 h10 hL hcg θ w _).1 hhi)
    ((tauEBot_phase hk hkk h6 h10 hL hcg θ w _).2 hlo)

theorem outcome_TauEBot_vs_TauTFTPf_band {k : Nat} (hk : 2 ≤ k) (hkk : c_guard k + 3 ≤ k)
    (h6 : 6 ≤ k) (h10 : 10 ≤ k) (hL : 100 * Nat.log2 k + 1000 ≤ k) (hcg : c_guard k + 20 ≤ k) (θ : Nat) (w : Tmpl → Nat)
    (hlo : ¬ θ ≤ eMass w) (hhi : θ ≤ pfMass w) :
    ∃ N, outcome N (TauBotZ k .ebot w θ) (TauBotZ k .tftPf w θ) = some (.D, .C) :=
  outcome_of_ex_plays ((tauEBot_phase hk hkk h6 h10 hL hcg θ w _).2 hlo)
    ((tauTFTPf_phase hk hkk h6 h10 hL hcg θ w _).1 hhi)

theorem outcome_TauEBot_vs_TauTFTPf_coop {k : Nat} (hk : 2 ≤ k) (hkk : c_guard k + 3 ≤ k)
    (h6 : 6 ≤ k) (h10 : 10 ≤ k) (hL : 100 * Nat.log2 k + 1000 ≤ k) (hcg : c_guard k + 20 ≤ k) (θ : Nat) (w : Tmpl → Nat) (hθ : θ ≤ eMass w)
    (hθp : θ ≤ pfMass w) :
    ∃ N, outcome N (TauBotZ k .ebot w θ) (TauBotZ k .tftPf w θ) = some (.C, .C) :=
  outcome_of_ex_plays ((tauEBot_phase hk hkk h6 h10 hL hcg θ w _).1 hθ)
    ((tauTFTPf_phase hk hkk h6 h10 hL hcg θ w _).1 hθp)

/-! ## The new bots' self-plays, and the TRUST band -/

theorem outcome_TauOBot_vs_TauOBot_coop {k : Nat} (hk : 2 ≤ k) (hkk : c_guard k + 3 ≤ k)
    (h6 : 6 ≤ k) (h10 : 10 ≤ k) (hL : 100 * Nat.log2 k + 1000 ≤ k) (hcg : c_guard k + 20 ≤ k) (θ : Nat) (w : Tmpl → Nat) (hθ : θ ≤ obotMass w) :
    ∃ N, outcome N (TauBotZ k .obot w θ) (TauBotZ k .obot w θ) = some (.C, .C) :=
  outcome_of_ex_plays ((tauOBot_phase hk hkk h6 h10 hL hcg θ w _).1 hθ)
    ((tauOBot_phase hk hkk h6 h10 hL hcg θ w _).1 hθ)

theorem outcome_TauGuardian_vs_TauGuardian {k : Nat} (hk : 2 ≤ k)
    (hkk : c_guard k + 3 ≤ k) (h6 : 6 ≤ k) (h10 : 10 ≤ k)
    (hL : 100 * Nat.log2 k + 1000 ≤ k) (hcg : c_guard k + 20 ≤ k) (θ : Nat) (w : Tmpl → Nat)
    (hθ : θ ≤ guardMass w) :
    ∃ N, outcome N (TauBotZ k .guardian w θ) (TauBotZ k .guardian w θ) = some (.C, .C) :=
  outcome_of_ex_plays ((tauGuardian_phase hk hkk h6 h10 hL hcg θ w _).1 hθ)
    ((tauGuardian_phase hk hkk h6 h10 hL hcg θ w _).1 hθ)

/-- **THE TRUST BAND** `eMass < θ ≤ guardMass`: the exploiter has flipped to
    defection while the norm enforcer — unable to CONVICT the exploiter's own
    signal-mass of bullying — still trusts. `(D, C)`: trust without proof is paid
    for. -/
theorem outcome_TauEBot_vs_TauGuardian_band {k : Nat} (hk : 2 ≤ k)
    (hkk : c_guard k + 3 ≤ k) (h6 : 6 ≤ k) (h10 : 10 ≤ k)
    (hL : 100 * Nat.log2 k + 1000 ≤ k) (hcg : c_guard k + 20 ≤ k) (θ : Nat) (w : Tmpl → Nat)
    (hlo : ¬ θ ≤ eMass w) (hhi : θ ≤ guardMass w) :
    ∃ N, outcome N (TauBotZ k .ebot w θ) (TauBotZ k .guardian w θ) = some (.D, .C) :=
  outcome_of_ex_plays ((tauEBot_phase hk hkk h6 h10 hL hcg θ w _).2 hlo)
    ((tauGuardian_phase hk hkk h6 h10 hL hcg θ w _).1 hhi)

/-! ## τ(DBot)'s cells — the self-punishing detector (2026-08-19)

`dbotMass` excludes `w .coop` (the pushover it punishes) AND `w .dbot` (itself:
its own instance TRUSTS a defector, which is exactly what its watch fires on).
The self-play cell is the behavioral analogue of single-tier PrudentBot's
`(D, D)` — a detector whose test cannot exempt its own reasoning. -/

theorem outcome_TauDBot_vs_TauDBot_coop {k : Nat} (hk : 2 ≤ k)
    (hL : 100 * Nat.log2 k + 1000 ≤ k) (θ : Nat)
    (w : Tmpl → Nat) (hθ : θ ≤ dbotMass w) :
    ∃ N, outcome N (TauBotZ k .dbot w θ) (TauBotZ k .dbot w θ) = some (.C, .C) :=
  outcome_of_ex_plays ((tauDBot_phase hk hL θ w _).1 hθ) ((tauDBot_phase hk hL θ w _).1 hθ)

theorem outcome_TauDBot_vs_TauDBot_high {k : Nat} (hk : 2 ≤ k)
    (hL : 100 * Nat.log2 k + 1000 ≤ k) (θ : Nat)
    (w : Tmpl → Nat) (hθ : ¬ θ ≤ dbotMass w) :
    ∃ N, outcome N (TauBotZ k .dbot w θ) (TauBotZ k .dbot w θ) = some (.D, .D) :=
  outcome_of_ex_plays ((tauDBot_phase hk hL θ w _).2 hθ) ((tauDBot_phase hk hL θ w _).2 hθ)

/-- **THE PUSHOVER CELL**: the unconditional cooperator is the one hypothesis the
    punisher fires on, so at any θ where both are in their cooperating regimes the
    cooperator is exploited — `(C, D)`. -/
theorem outcome_TauCooperate_vs_TauDBot {k : Nat} (hk : 2 ≤ k)
    (hL : 100 * Nat.log2 k + 1000 ≤ k) (θ : Nat)
    (w : Tmpl → Nat) (hθc : θ ≤ fullMass w) (hθd : ¬ θ ≤ dbotMass w) :
    ∃ N, outcome N (TauBotZ k .coop w θ) (TauBotZ k .dbot w θ) = some (.C, .D) :=
  outcome_of_ex_plays ((tauCooperate_phase k w θ _).1 hθc)
    ((tauDBot_phase hk hL θ w _).2 hθd)

/-- τ(DBot) and the norm enforcer punish each other: Guardian convicts DBot of
    bullying the cooperator (`guardColBit .dbot = true`), and DBot fires on
    Guardian's trust of the defector. Mutual conviction between the two
    punishers. -/
theorem outcome_TauDBot_vs_TauGuardian_high {k : Nat} (hk : 2 ≤ k)
    (hkk : c_guard k + 3 ≤ k) (h6 : 6 ≤ k) (h10 : 10 ≤ k)
    (hL : 100 * Nat.log2 k + 1000 ≤ k) (hcg : c_guard k + 20 ≤ k) (θ : Nat) (w : Tmpl → Nat)
    (hlo : ¬ θ ≤ dbotMass w) (hhi : ¬ θ ≤ guardMass w) :
    ∃ N, outcome N (TauBotZ k .dbot w θ) (TauBotZ k .guardian w θ) = some (.D, .D) :=
  outcome_of_ex_plays ((tauDBot_phase hk hL θ w _).2 hlo)
    ((tauGuardian_phase hk hkk h6 h10 hL hcg θ w _).2 hhi)

/-! ## τ(CIMCIC)'s cells — the conditional cooperator (2026-08-21)

The headline: the CIMCIC×Dupoc ENTANGLED pair cooperates — the first `.sys` cell
closed by mutual bounded Löb, matching the base `llm_outcome_CIMCIC_vs_DupocBot`
`(C, C)`. Against Cupod the floor closes the pair the other way: the suspicious
cooperator trusts, the conditional cooperator cannot certify that trust — `(D, C)`,
the same shape as the red cell. -/

theorem outcome_TauCIMCIC_vs_TauCIMCIC :
    ∃ k₂, ∀ k, k₂ < k →
      ∀ (hmirP : ∃ N, eval N (.bot (inst (tauZoo k) .cimcic .mirror))
          (.bot (inst (tauZoo k) .cimcic .mirror)) (inst (tauZoo k) .cimcic .mirror)
          = some (cimcicRow .mirror)),
      ∀ θ (w : Tmpl → Nat), θ ≤ cimcicMass w →
      ∃ N, outcome N (TauBotZ k .cimcic w θ) (TauBotZ k .cimcic w θ) = some (.C, .C) := by
  obtain ⟨k₂, h⟩ := tauCIMCIC_phase
  exact ⟨k₂, fun k hk hmirP θ w hθ =>
    outcome_of_ex_plays ((h k hk hmirP θ w _).1 hθ) ((h k hk hmirP θ w _).1 hθ)⟩

/-- **The entangled pair, cooperatively**: within both cooperation regimes the
    conditional cooperator and the Löbian cooperator settle on `(C, C)` — the tau
    image of base CIMCIC-vs-DupocBot, THROUGH the binder. -/
theorem outcome_TauCIMCIC_vs_TauDupoc :
    ∃ k₂, ∀ k, k₂ < k →
      ∀ (hmirC : ∃ N, eval N (.bot (inst (tauZoo k) .cimcic .mirror))
          (.bot (inst (tauZoo k) .cimcic .mirror)) (inst (tauZoo k) .cimcic .mirror)
          = some (cimcicRow .mirror))
        (hmir : proofSearch k (probe (inst (tauZoo k) .mirror .dupoc))
          = dupocColBit .mirror)
        (hmirP : ∃ N, eval N (.bot (inst (tauZoo k) .dupoc .mirror))
          (.bot (inst (tauZoo k) .dupoc .mirror)) (inst (tauZoo k) .dupoc .mirror)
          = some (dupocRow .mirror)),
      ∀ θ (w : Tmpl → Nat), θ ≤ cimcicMass w → θ ≤ dupMass w →
      ∃ N, outcome N (TauBotZ k .cimcic w θ) (TauBotZ k .dupoc w θ) = some (.C, .C) := by
  obtain ⟨kM, hM⟩ := tauCIMCIC_phase
  obtain ⟨kD, hD⟩ := tauDupoc_phase
  exact ⟨max kM kD, fun k hk hmirC hmir hmirP θ w hθm hθd =>
    outcome_of_ex_plays
      ((hM k (lt_of_le_of_lt (Nat.le_max_left _ _) hk) hmirC θ w _).1 hθm)
      ((hD k (lt_of_le_of_lt (Nat.le_max_right _ _) hk) hmir hmirP θ w _).1 hθd)⟩

/-- **The CIMCIC×Cupod band** `cimcicMass < θ ≤ cupodMass`: the conditional
    cooperator has flipped (it cannot certify the suspicious cooperator's
    floor-priced trust) while Cupod — unable to convict IT — still trusts.
    `(D, C)`: the red-cell shape, one tier up. -/
theorem outcome_TauCIMCIC_vs_TauCupod_band :
    ∃ k₂, ∀ k, k₂ < k →
      -- Cupod's row is gated on the ALIGNED dimcid pair and the mirror pair
      ∀ (hmirC : ∃ N, eval N (.bot (inst (tauZoo k) .cimcic .mirror))
          (.bot (inst (tauZoo k) .cimcic .mirror)) (inst (tauZoo k) .cimcic .mirror)
          = some (cimcicRow .mirror))
        (hmirCu : proofSearch k (probeD (inst (tauZoo k) .mirror .cupod))
          = cupodColBit .mirror)
        (hmirCuP : ∃ N, eval N (.bot (inst (tauZoo k) .cupod .mirror))
          (.bot (inst (tauZoo k) .cupod .mirror)) (inst (tauZoo k) .cupod .mirror)
          = some (cupodRow .mirror))
        (hdc : proofSearch k (probeD (inst (tauZoo k) .dimcid .cupod))
          = cupodColBit .dimcid)
        (hdcP : ∃ N, eval N (.bot (inst (tauZoo k) .cupod .dimcid))
          (.bot (inst (tauZoo k) .cupod .dimcid)) (inst (tauZoo k) .cupod .dimcid)
          = some Action.D),
      ∀ θ (w : Tmpl → Nat), ¬ θ ≤ cimcicMass w → θ ≤ cupodMass w →
      ∃ N, outcome N (TauBotZ k .cimcic w θ) (TauBotZ k .cupod w θ) = some (.D, .C) := by
  obtain ⟨kM, hM⟩ := tauCIMCIC_phase
  obtain ⟨kC, hC⟩ := tauCupod_phase
  exact ⟨max kM kC, fun k hk hmirC hmirCu hmirCuP hdc hdcP θ w hθm hθc =>
    outcome_of_ex_plays
      ((hM k (lt_of_le_of_lt (Nat.le_max_left _ _) hk) hmirC θ w _).2 hθm)
      ((hC k (lt_of_le_of_lt (Nat.le_max_right _ _) hk) hmirCu hmirCuP hdc hdcP
        θ w _).1 hθc)⟩

end PD.Theorems.Tau
