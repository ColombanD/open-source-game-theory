import PrisonersDilemma.Tau.Theorems.Columns

/-!
# τ(EBot)'s phase — the ONE-SIDED boundary `θ ≤ eMass`.

Excludes `w .coop` (the weight it exploits) and now also `w .guardian`: EBot's
reciprocity probe cannot cite Guardian's floor-priced cooperation, so the exploiter
DEFECTS on the norm enforcer — mutual illegibility between the two prover
specialists.
-/

open PD PD.BaseTheorems

namespace PD.Tau

/-- τ(EBot)'s bit ROW: the exploit/reciprocity cascade over the δ_D and δ_C prover
    columns. -/
def eRow : Tmpl → Action
  | .coop     => .D
  | .defect   => .D
  | .tftSim   => .C
  | .tftPf    => .C
  | .dupoc    => .C
  | .ebot     => .D
  | .just     => .C
  | .obot     => .C
  | .guardian => .D

/-- The row's witness: each entry is the two-stage cascade fed the δ_D
    (exploit) and δ_C (reciprocity) column bits. -/
theorem eRow_plays {k : Nat} (hk : 2 ≤ k) (hkk : c_guard k + 3 ≤ k) (h6 : 6 ≤ k)
    (h10 : 10 ≤ k) :
    ∀ T, ∃ N, eval N (.bot (inst (tauZoo k) .ebot T)) (.bot (inst (tauZoo k) .ebot T))
              (inst (tauZoo k) .ebot T) = some (eRow T) :=
  let bD := ps_probe_inst_defect (k := k) hk
  let bC := ps_probe_inst_coop hk hkk h6 h10
  fun T => match T with
  | .coop     => cascade_plays_D_of_exploit _ _ (bD .coop)
  | .defect   => cascade_plays_D_of_both_false _ _ (bD .defect) (bC .defect)
  | .tftSim   => cascade_plays_C _ _ (bD .tftSim) (bC .tftSim)
  | .tftPf    => cascade_plays_C _ _ (bD .tftPf) (bC .tftPf)
  | .dupoc    => cascade_plays_C _ _ (bD .dupoc) (bC .dupoc)
  | .ebot     => cascade_plays_D_of_both_false _ _ (bD .ebot) (bC .ebot)
  | .just     => cascade_plays_C _ _ (bD .just) (bC .just)
  | .obot     => cascade_plays_C _ _ (bD .obot) (bC .obot)
  | .guardian => cascade_plays_D_of_both_false _ _ (bD .guardian) (bC .guardian)

/-- The scanner-facing bit row (read by `app`'s `def4_theorems.py` — keep the
    literal list): `vecOf_bits`' mapped row, by defeq on the concrete zoo. -/
theorem eBits {k : Nat} (hk : 2 ≤ k) (hkk : c_guard k + 3 ≤ k) (h6 : 6 ≤ k)
    (h10 : 10 ≤ k) (w : Tmpl → Nat) :
    VoteBits (vecOf (tauZoo k) .ebot w tauOrder)
      [(w .coop, .D), (w .defect, .D), (w .tftSim, .C), (w .tftPf, .C),
       (w .dupoc, .C), (w .ebot, .D), (w .just, .C), (w .obot, .C),
       (w .guardian, .D)] :=
  vecOf_bits (tauZoo k) .ebot w eRow tauOrder fun T _ => eRow_plays hk hkk h6 h10 T

/-- **τ(EBot)** — one-sided boundary `θ ≤ eMass`, no window. -/
theorem tauEBot_phase {k : Nat} (hk : 2 ≤ k) (hkk : c_guard k + 3 ≤ k) (h6 : 6 ≤ k)
    (h10 : 10 ≤ k) (θ : Nat) (w : Tmpl → Nat) (opponent : Prog) :
    (θ ≤ eMass w → ∃ N, play N (TauBotZ k .ebot w θ) opponent = some .C)
    ∧ (¬ θ ≤ eMass w → ∃ N, play N (TauBotZ k .ebot w θ) opponent = some .D) := by
  have h := phase_of_bits (tauZoo k) .ebot w eRow tauOrder θ opponent
    (fun T _ => eRow_plays hk hkk h6 h10 T)
  simp only [bitMass, tauOrder, List.map, eRow, massOf, massOf_ifC, massOf_ifD,
    TauBotZ] at h ⊢
  simpa [eMass] using h

end PD.Tau
