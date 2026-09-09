import PrisonersDilemma.Tau.Theorems.TauPrudent.Helpers
import PrisonersDilemma.Tau.RowSpec
import PrisonersDilemma.Outcome.Attr

/-!
# τ(Prudent)'s phase (2026-08-25)

`D` at every hypothesis but the forwarder: at a SINGLE shared budget the inner
"provably defects on the defector" check fails on every partner whose defection is
an else-play, and the outer "provably cooperates with me" probe fails on the rest —
except τ(Mirror), whose cooperation is Prudent's own, closed by bounded Löb. Base
PrudentBot recovers (C, C) against DupocBot/JustBot only at the STAGGERED budget
`2k+64`; those two cells are the port's whitelisted budget divergences.
-/

open PD PD.BaseTheorems

namespace PD.Tau

def prudentRow : Tmpl → Action
  | .mirror => .C
  | _       => .D

/-- The display form of the C-mass: the forwarder's weight alone. -/
def prudentMass (w : Tmpl → Nat) : Nat := w .mirror

theorem prudentRow_plays :
    ∃ k₂, ∀ k, k₂ < k → ∀ T,
      ∃ N, eval N (.bot (inst (tauZoo k) .prudent T)) (.bot (inst (tauZoo k) .prudent T))
        (inst (tauZoo k) .prudent T) = some (prudentRow T) := by
  obtain ⟨kA, hkA⟩ := linear_log2_add_le 100 1000
  obtain ⟨k1, h1⟩ := prudent_mirror_plays_C
  refine ⟨max kA k1, fun k hk T => ?_⟩
  have hL : 100 * Nat.log2 k + 1000 ≤ k := hkA k (by omega)
  have hlog := Nat.log2_le_self k
  have hk2 : 2 ≤ k := by omega
  have hk3 : 3 ≤ k := by omega
  cases T with
  | coop => exact prudent_coop_plays_D
  | defect => exact prudent_defect_plays_D
  | tftSim => exact prudent_tftSim_plays_D
  | tftPf => exact prudent_tftPf_plays_D
  | dupoc => exact prudent_dupoc_plays_D
  | ebot => exact prudent_ebot_plays_D
  | just => exact prudent_just_plays_D
  | obot => exact prudent_obot_plays_D
  | guardian => exact prudent_guardian_plays_D
  | dbot => exact prudent_dbot_plays_D hk2 hL
  | cupodTroll => exact prudent_cupodTroll_plays_D hk3
  | cupod => exact prudent_cupod_plays_D
  | cimcic => exact prudent_cimcic_plays_D
  | dimcid => exact prudent_dimcid_plays_D
  | prudent => exact prudent_quine_plays_D
  | maxconfidence =>
      rw [inst_at_maxconfidence_eq_dupoc k .prudent (by decide) (by decide) (by decide)]
      exact prudent_dupoc_plays_D
  | minconfidence =>
      rw [inst_at_minconfidence_eq_dupoc k .prudent (by decide) (by decide) (by decide)]
      exact prudent_dupoc_plays_D
  | mirror => exact h1 k (by omega)

/-- **τ(Prudent)'s row** — the matrix-facing statement (`@[tau_row]`: validated by
    `Tau/Lint.lean`, exported to the app): unconditional at large `k`, the floors and
    Löb gates discharged inside. The former literal `VoteBits` list is `RowSpec.bits`. -/
@[tau_row]
theorem prudentRowSpec : RowSpec .prudent tauOrder prudentRow := by
  obtain ⟨k₂, h⟩ := prudentRow_plays
  exact ⟨k₂, fun k hk T _ => h k hk T⟩

/-- **τ(Prudent)'s phase** — boundary `θ ≤ prudentMass`. Unconditional. -/
theorem tauPrudent_phase :
    ∃ k₂, ∀ k, k₂ < k →
      ∀ θ (w : Tmpl → Nat) (opponent : Prog),
      (θ ≤ prudentMass w → ∃ N, play N (TauBotZ k .prudent w θ) opponent = some .C)
      ∧ (¬ θ ≤ prudentMass w → ∃ N, play N (TauBotZ k .prudent w θ) opponent = some .D) := by
  obtain ⟨k₂, hrow⟩ := prudentRow_plays
  refine ⟨k₂, fun k hk θ w opponent => ?_⟩
  have h := phase_of_bits (tauZoo k) .prudent w prudentRow tauOrder θ opponent
    (fun T _ => hrow k hk T)
  simp only [bitMass, tauOrder, List.map, prudentRow, massOf, massOf_ifC, massOf_ifD] at h
  exact ⟨fun hθ => h.1 (by simpa [prudentMass] using hθ),
         fun hθ => h.2 (by simpa [prudentMass] using hθ)⟩

end PD.Tau
