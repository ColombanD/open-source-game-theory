import PrisonersDilemma.Tau.Theorems.Columns

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
  | .ebot     => .D
  | .just     => .C
  | .obot     => .C
  | .guardian => .C
  | .dbot     => .D
  | .cupod      => .C
  | .cupodTroll => .D
  | .cimcic     => .C

/-- The row's witness: each entry is the two-stage run cascade fed the δ_D
    (exploit-watch) and δ_C (reciprocity-watch) behavioral columns. -/
theorem eRow_plays {k : Nat} (hk : 2 ≤ k) (hkk : c_guard k + 3 ≤ k) (h6 : 6 ≤ k)
    (h10 : 10 ≤ k) (hL : 100 * Nat.log2 k + 1000 ≤ k) (hcg : c_guard k + 20 ≤ k) :
    ∀ T, ∃ N, eval N (.bot (inst (tauZoo k) .ebot T)) (.bot (inst (tauZoo k) .ebot T))
              (inst (tauZoo k) .ebot T) = some (eRow T) :=
  let pD := inst_defect_plays (k := k) hk
  let pC := inst_coop_plays hk hkk h6 h10 hL
  fun T => match T with
  | .coop     => simWatchC_fires _ _ (pD .coop)
  | .defect   => simWatchC_falls _ _ (pD .defect)
      (simWatchC_falls _ _ (pC .defect) ⟨1, rfl⟩)
  | .tftSim   => simWatchC_falls _ _ (pD .tftSim) (simWatchC_fires _ _ (pC .tftSim))
  | .tftPf    => simWatchC_falls _ _ (pD .tftPf) (simWatchC_fires _ _ (pC .tftPf))
  | .dupoc    => simWatchC_falls _ _ (pD .dupoc) (simWatchC_fires _ _ (pC .dupoc))
  | .ebot     => simWatchC_falls _ _ (pD .ebot)
      (simWatchC_falls _ _ (pC .ebot) ⟨1, rfl⟩)
  | .just     => simWatchC_falls _ _ (pD .just) (simWatchC_fires _ _ (pC .just))
  | .obot     => simWatchC_falls _ _ (pD .obot) (simWatchC_fires _ _ (pC .obot))
  | .guardian => simWatchC_falls _ _ (pD .guardian)
      (simWatchC_fires _ _ (pC .guardian))
  | .dbot     => simWatchC_fires _ _ (pD .dbot)
  | .cupod      => simWatchC_falls _ _ (pD .cupod) (simWatchC_fires _ _ (pC .cupod))
  | .cupodTroll => simWatchC_fires _ _ (pD .cupodTroll)
  | .cimcic     => simWatchC_falls _ _ (pD .cimcic) (simWatchC_fires _ _ (pC .cimcic))

/-- The scanner-facing bit row (read by `app`'s `def4_theorems.py` — keep the
    literal list): `vecOf_bits`' mapped row, by defeq on the concrete zoo. -/
theorem eBits {k : Nat} (hk : 2 ≤ k) (hkk : c_guard k + 3 ≤ k) (h6 : 6 ≤ k)
    (h10 : 10 ≤ k) (hL : 100 * Nat.log2 k + 1000 ≤ k) (hcg : c_guard k + 20 ≤ k) (w : Tmpl → Nat) :
    VoteBits (vecOf (tauZoo k) .ebot w tauOrder)
      [(w .coop, .D), (w .defect, .D), (w .tftSim, .C), (w .tftPf, .C),
       (w .dupoc, .C), (w .ebot, .D), (w .just, .C), (w .obot, .C),
       (w .guardian, .C), (w .dbot, .D), (w .cupodTroll, .D), (w .cupod, .C), (w .cimcic, .C)] :=
  vecOf_bits (tauZoo k) .ebot w eRow tauOrder fun T _ => eRow_plays hk hkk h6 h10 hL hcg T

/-- **τ(EBot)** — one-sided boundary `θ ≤ eMass`, no window. -/
theorem tauEBot_phase {k : Nat} (hk : 2 ≤ k) (hkk : c_guard k + 3 ≤ k) (h6 : 6 ≤ k)
    (h10 : 10 ≤ k) (hL : 100 * Nat.log2 k + 1000 ≤ k) (hcg : c_guard k + 20 ≤ k) (θ : Nat) (w : Tmpl → Nat) (opponent : Prog) :
    (θ ≤ eMass w → ∃ N, play N (TauBotZ k .ebot w θ) opponent = some .C)
    ∧ (¬ θ ≤ eMass w → ∃ N, play N (TauBotZ k .ebot w θ) opponent = some .D) := by
  have h := phase_of_bits (tauZoo k) .ebot w eRow tauOrder θ opponent
    (fun T _ => eRow_plays hk hkk h6 h10 hL hcg T)
  simp only [bitMass, tauOrder, List.map, eRow, massOf, massOf_ifC, massOf_ifD,
    TauBotZ] at h ⊢
  simpa [eMass] using h

end PD.Tau
