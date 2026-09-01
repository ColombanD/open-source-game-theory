import PrisonersDilemma.Tau.Theorems.Columns
import PrisonersDilemma.Tau.Theorems.TauMirror.Helpers
import PrisonersDilemma.Tau.RowSpec
import PrisonersDilemma.Outcome.Attr
import PrisonersDilemma.Tau.Theorems.TauPrudent.Helpers

/-!
# τ(EBot)'s phase — the ONE-SIDED boundary `θ ≤ eMass`.

Excludes `w .coop` (the weight it exploits). Since the 2026-08-19 modality fix
(run stages — base EBot's own sim cascade) `eMass` INCLUDES `w .guardian`: the
behavioral read sees Guardian's floor-priced true cooperation, exactly as base
`EBot vs GuardianBot = (C, C)ish` does — the coincidence cell the certification
flagged under the old prove-stages.
-/

open PD PD.BaseTheorems

namespace PD.Tau

/-- τ(EBot)'s bit ROW: the exploit/reciprocity RUN cascade over the δ_D and δ_C
    behavioral columns. D exactly at the exploitable cooperator, the defector,
    and itself (the Mirror-truncation cell). -/
def eRow : Tmpl → Action
  | .coop     => .D
  | .defect   => .D
  | .tftSim   => .C
  | .tftPf    => .C
  | .dupoc    => .C
  | .ebot     => .C
  | .just     => .C
  | .obot     => .C
  | .guardian => .C
  | .dbot     => .D
  | .cupod      => .C
  | .cupodTroll => .D
  | .cimcic     => .C
  | .dimcid     => .C
  | .prudent    => .C
  | .maxconfidence => .C
  | .minconfidence => .C
  | .mirror     => .C

/-- The row's witness: each entry is the two-stage run cascade fed the δ_D
    (exploit-watch) and δ_C (reciprocity-watch) behavioral columns. -/
theorem eRow_plays {k : Nat} (hk : 2 ≤ k) (hkk : c_guard k + 3 ≤ k) (h6 : 6 ≤ k)
    (h10 : 10 ≤ k) (hL : 100 * Nat.log2 k + 1000 ≤ k) (hcg : c_guard k + 20 ≤ k)
    (hpm : ∃ N, eval N (.bot (inst (tauZoo k) .prudent .mirror))
      (.bot (inst (tauZoo k) .prudent .mirror)) (inst (tauZoo k) .prudent .mirror)
      = some Action.C) :
    ∀ T, ∃ N, eval N (.bot (inst (tauZoo k) .ebot T)) (.bot (inst (tauZoo k) .ebot T))
              (inst (tauZoo k) .ebot T) = some (eRow T) :=
  let pD := inst_defect_plays (k := k) hk hL
  let pC := inst_coop_plays hk hkk h6 h10 hL
  fun T => match T with
  | .coop     => simWatchC_fires _ _ (pD .coop)
  | .defect   => simWatchC_falls _ _ (pD .defect)
      (simWatchC_falls _ _ (pC .defect)
        (simWatchC_falls _ _ ⟨1, rfl⟩ ⟨1, rfl⟩))
  | .tftSim   => simWatchC_falls _ _ (pD .tftSim) (simWatchC_fires _ _ (pC .tftSim))
  | .tftPf    => simWatchC_falls _ _ (pD .tftPf) (simWatchC_fires _ _ (pC .tftPf))
  | .dupoc    => simWatchC_falls _ _ (pD .dupoc) (simWatchC_fires _ _ (pC .dupoc))
  -- THE SELF CELL: w1 and w2 fall, and the THIRD watch — restored with the
  -- `.mirror` template — FIRES, so E cooperates with itself. This is the bit the
  -- `(TauEBot, TauEBot)` whitelist entry existed for: base EBot-vs-EBot is
  -- (C, C), and the truncated two-stage lift read D.
  | .ebot     => simWatchC_falls _ _ (pD .ebot)
      (simWatchC_falls _ _ (pC .ebot) (simWatchC_fires _ _ (ebot_mirror_plays_C rfl)))
  | .just     => simWatchC_falls _ _ (pD .just) (simWatchC_fires _ _ (pC .just))
  | .obot     => simWatchC_falls _ _ (pD .obot) (simWatchC_fires _ _ (pC .obot))
  | .guardian => simWatchC_falls _ _ (pD .guardian)
      (simWatchC_fires _ _ (pC .guardian))
  | .dbot     => simWatchC_fires _ _ (pD .dbot)
  | .cupod      => simWatchC_falls _ _ (pD .cupod) (simWatchC_fires _ _ (pC .cupod))
  | .cupodTroll => simWatchC_fires _ _ (pD .cupodTroll)
  | .cimcic     => simWatchC_falls _ _ (pD .cimcic) (simWatchC_fires _ _ (pC .cimcic))
  | .dimcid     => simWatchC_falls _ _ (pD .dimcid) (simWatchC_fires _ _ (pC .dimcid))
  | .prudent    => -- w1, w2 fall (Prudent defects on both constants); w3 FIRES: it
                   -- cooperates with the mirror (Löb-gated, hence the hypothesis)
      simWatchC_falls _ _ (pD .prudent) (simWatchC_falls _ _ (pC .prudent) (simWatchC_fires _ _ hpm))
  | .mirror     => simWatchC_falls _ _ mirror_defect_plays_D
      (simWatchC_fires _ _ mirror_coop_plays_C)
  | .maxconfidence => simWatchC_falls _ _ (pD .maxconfidence) (simWatchC_fires _ _ (pC .maxconfidence))
  | .minconfidence => simWatchC_falls _ _ (pD .minconfidence) (simWatchC_fires _ _ (pC .minconfidence))

/-- **τ(EBot)'s row** — the matrix-facing statement (`@[tau_row]`: validated by
    `Tau/Lint.lean`, exported to the app): unconditional at large `k`, the floors and
    Löb gates discharged inside. The former literal `VoteBits` list is `RowSpec.bits`. -/
@[tau_row]
theorem ebotRowSpec : RowSpec .ebot tauOrder eRow := by
  obtain ⟨K, hK⟩ := linear_log2_add_le 100 1000
  obtain ⟨kP, hP⟩ := prudent_mirror_plays_C
  refine ⟨max (K + 10) kP, fun k hk T _ => ?_⟩
  have hL : 100 * Nat.log2 k + 1000 ≤ k := hK k (by omega)
  have := Nat.log2_le_self k
  exact eRow_plays (by omega) (by simp only [c_guard, numCost]; omega) (by omega) (by omega) hL
    (by simp only [c_guard, numCost]; omega) (hP k (by omega)) T

/-- **τ(EBot)** — one-sided boundary `θ ≤ eMass`, no window. -/
theorem tauEBot_phase {k : Nat} (hk : 2 ≤ k) (hkk : c_guard k + 3 ≤ k) (h6 : 6 ≤ k)
    (h10 : 10 ≤ k) (hL : 100 * Nat.log2 k + 1000 ≤ k) (hcg : c_guard k + 20 ≤ k)
    (hpm : ∃ N, eval N (.bot (inst (tauZoo k) .prudent .mirror))
      (.bot (inst (tauZoo k) .prudent .mirror)) (inst (tauZoo k) .prudent .mirror)
      = some Action.C) (θ : Nat) (w : Tmpl → Nat) (opponent : Prog) :
    (θ ≤ eMass w → ∃ N, play N (TauBotZ k .ebot w θ) opponent = some .C)
    ∧ (¬ θ ≤ eMass w → ∃ N, play N (TauBotZ k .ebot w θ) opponent = some .D) := by
  have h := phase_of_bits (tauZoo k) .ebot w eRow tauOrder θ opponent
    (fun T _ => eRow_plays hk hkk h6 h10 hL hcg hpm T)
  simp only [bitMass, tauOrder, List.map, eRow, massOf, massOf_ifC, massOf_ifD,
    TauBotZ] at h ⊢
  simpa [eMass] using h

end PD.Tau
