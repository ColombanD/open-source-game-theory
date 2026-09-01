import PrisonersDilemma.Tau.Theorems.Columns
import PrisonersDilemma.Tau.RowSpec
import PrisonersDilemma.Outcome.Attr

/-!
# τ(OBot)'s phase — the zoo's NARROWEST boundary, `θ ≤ obotMass`.

Both defection watches must stay silent. Two hypotheses pass: the unconditional
cooperator, and (since 2026-08-20) τ(CupodTroll), whose identity check never fires
so it too cooperates with everyone. The behavioral
defection-detector cooperates with almost nobody — but what it sees, it sees truly
(floor-blind).
-/

open PD PD.BaseTheorems

namespace PD.Tau

/-- τ(OBot)'s bit ROW: C only where BOTH defection watches stay silent — the
    unconditional cooperator. -/
def obotRow : Tmpl → Action
  | .coop     => .C
  | .defect   => .D
  | .tftSim   => .D
  | .tftPf    => .D
  | .dupoc    => .D
  | .ebot     => .D
  | .just     => .D
  | .obot     => .D
  | .guardian => .D
  | .dbot     => .D
  | .cupod      => .D
  | .cupodTroll => .C
  | .cimcic     => .D
  | .dimcid     => .D
  | .prudent    => .D
  | .maxconfidence => .D
  | .minconfidence => .D
  | .mirror     => .D

/-- The row's witness: two chained run-stage defection watches over the δ_C and
    δ_D behavioral columns. -/
theorem obotRow_plays {k : Nat} (hk : 2 ≤ k) (hkk : c_guard k + 3 ≤ k) (h6 : 6 ≤ k)
    (h10 : 10 ≤ k) (hL : 100 * Nat.log2 k + 1000 ≤ k) (hcg : c_guard k + 20 ≤ k) :
    ∀ T, ∃ N, eval N (.bot (inst (tauZoo k) .obot T)) (.bot (inst (tauZoo k) .obot T))
              (inst (tauZoo k) .obot T) = some (obotRow T) :=
  let pC := inst_coop_plays hk hkk h6 h10 hL
  let pD := inst_defect_plays (k := k) hk hL
  fun T => match T with
  | .coop     => simTestD_falls _ _ (pC .coop) (simTestD_falls _ _ (pD .coop) ⟨1, rfl⟩)
  | .defect   => simTestD_fires _ _ (pC .defect)
  | .tftSim   => simTestD_falls _ _ (pC .tftSim) (simTestD_fires _ _ (pD .tftSim))
  | .tftPf    => simTestD_falls _ _ (pC .tftPf) (simTestD_fires _ _ (pD .tftPf))
  | .dupoc    => simTestD_falls _ _ (pC .dupoc) (simTestD_fires _ _ (pD .dupoc))
  | .ebot     => simTestD_fires _ _ (pC .ebot)
  | .just     => simTestD_falls _ _ (pC .just) (simTestD_fires _ _ (pD .just))
  | .obot     => simTestD_falls _ _ (pC .obot) (simTestD_fires _ _ (pD .obot))
  | .guardian => simTestD_falls _ _ (pC .guardian) (simTestD_fires _ _ (pD .guardian))
  | .dbot     => simTestD_fires _ _ (pC .dbot)
  | .cupod      => simTestD_falls _ _ (pC .cupod) (simTestD_fires _ _ (pD .cupod))
  | .cupodTroll => simTestD_falls _ _ (pC .cupodTroll)
      (simTestD_falls _ _ (pD .cupodTroll) ⟨1, rfl⟩)
  | .cimcic     => simTestD_falls _ _ (pC .cimcic) (simTestD_fires _ _ (pD .cimcic))
  | .dimcid     => simTestD_falls _ _ (pC .dimcid) (simTestD_fires _ _ (pD .dimcid))
  | .prudent    => simTestD_fires _ _ (pC .prudent)
  | .mirror     => simTestD_falls _ _ (pC .mirror) (simTestD_fires _ _ (pD .mirror))
  | .maxconfidence => simTestD_falls _ _ (pC .maxconfidence) (simTestD_fires _ _ (pD .maxconfidence))
  | .minconfidence => simTestD_falls _ _ (pC .minconfidence) (simTestD_fires _ _ (pD .minconfidence))

/-- **τ(OBot)'s row** — the matrix-facing statement (`@[tau_row]`: validated by
    `Tau/Lint.lean`, exported to the app): unconditional at large `k`, the floors and
    Löb gates discharged inside. The former literal `VoteBits` list is `RowSpec.bits`. -/
@[tau_row]
theorem obotRowSpec : RowSpec .obot tauOrder obotRow := by
  obtain ⟨K, hK⟩ := linear_log2_add_le 100 1000
  refine ⟨K + 10, fun k hk T _ => ?_⟩
  have hL : 100 * Nat.log2 k + 1000 ≤ k := hK k (by omega)
  have := Nat.log2_le_self k
  exact obotRow_plays (by omega) (by simp only [c_guard, numCost]; omega) (by omega) (by omega) hL
    (by simp only [c_guard, numCost]; omega) T

/-- **τ(OBot)** — boundary `θ ≤ obotMass`. -/
theorem tauOBot_phase {k : Nat} (hk : 2 ≤ k) (hkk : c_guard k + 3 ≤ k) (h6 : 6 ≤ k)
    (h10 : 10 ≤ k) (hL : 100 * Nat.log2 k + 1000 ≤ k) (hcg : c_guard k + 20 ≤ k) (θ : Nat) (w : Tmpl → Nat) (opponent : Prog) :
    (θ ≤ obotMass w → ∃ N, play N (TauBotZ k .obot w θ) opponent = some .C)
    ∧ (¬ θ ≤ obotMass w → ∃ N, play N (TauBotZ k .obot w θ) opponent = some .D) := by
  have h := phase_of_bits (tauZoo k) .obot w obotRow tauOrder θ opponent
    (fun T _ => obotRow_plays hk hkk h6 h10 hL hcg T)
  simp only [bitMass, tauOrder, List.map, obotRow, massOf, massOf_ifC, massOf_ifD,
    TauBotZ] at h ⊢
  simpa [obotMass] using h

end PD.Tau
