import PrisonersDilemma.Tau.Theorems.Columns

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

/-- The scanner-facing bit row (read by `app`'s `def4_theorems.py` — keep the
    literal list): `vecOf_bits`' mapped row, by defeq on the concrete zoo. -/
theorem obotBits {k : Nat} (hk : 2 ≤ k) (hkk : c_guard k + 3 ≤ k) (h6 : 6 ≤ k)
    (h10 : 10 ≤ k) (hL : 100 * Nat.log2 k + 1000 ≤ k) (hcg : c_guard k + 20 ≤ k) (w : Tmpl → Nat) :
    VoteBits (vecOf (tauZoo k) .obot w tauOrder)
      [(w .coop, .C), (w .defect, .D), (w .tftSim, .D), (w .tftPf, .D),
       (w .dupoc, .D), (w .ebot, .D), (w .just, .D), (w .obot, .D),
       (w .guardian, .D), (w .dbot, .D), (w .cupodTroll, .C), (w .cupod, .D), (w .cimcic, .D), (w .dimcid, .D)] :=
  vecOf_bits (tauZoo k) .obot w obotRow tauOrder
    fun T _ => obotRow_plays hk hkk h6 h10 hL hcg T

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
