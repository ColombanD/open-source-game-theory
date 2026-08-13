import PrisonersDilemma.Tau.SysCerts
import PrisonersDilemma.Tau.PeelLemmas

/-!
# Theorems/Tau/SysMatrix — the Def-5 (σ-probing) outcome theorems, milestone 1

The first Route-A outcomes: the top-level TauDupocSys player over the σ-zoo
mutual system (`Tau/SysDefs`), in the instance regime `dC + dT < θ₂ ≤ dC + dL`
(the member-level threshold is decided by the Löbian quine bit) and the player
regimes `θ ≤ wC + wL` (cooperate) / `wC + wL + wT < θ` (defect). All corollaries
of `tauDupocSys_phase` — the players are `.opp`-free, hence extensionally
constant, and each cell is one `outcome_of_ex_plays`.

Unlike Def 4, the budget threshold `k₂` depends on the WEIGHTS (the honest
price of the binder: a `.sys` probe carries the whole system, so sizes grow
with the weight numerals). The band `wC + wL < θ ≤ wC + wL + wT` is the honest
OPEN region — the behavioral T-bit is Gödelian (regime-dependent divergence,
see `Tau/SysDefs`).
-/

open PD PD.Tau

namespace PD.Theorems.Tau

/-- **Löbian self-cooperation under COMMON-KNOWLEDGE blur** — the Def-5 headline:
    TauDupocSys vs itself is `(C, C)` in the cooperative regime. The quine bit
    fires by bounded Löb through the mutual system (`ps_probe_sysQuine`), and the
    C-bit and Löb bit alone carry the top-level vote. -/
theorem outcome_TauDupocSys_vs_TauDupocSys
    (θ₂ θ₃ θ₄ θ₅ dC dD dL dT cC cD cL cT : Nat)
    (hreg₁ : dC + dT < θ₂) (hreg₂ : θ₂ ≤ dC + dL) :
    ∃ k₂, ∀ k, k₂ < k → ∀ (wC wD wL wT θ : Nat), θ ≤ wC + wL →
      ∃ N, outcome N
        (TauDupocSys (sigmaZoo k θ₂ θ₃ θ₄ θ₅ dC dD dL dT cC cD cL cT) k wC wD wL wT θ)
        (TauDupocSys (sigmaZoo k θ₂ θ₃ θ₄ θ₅ dC dD dL dT cC cD cL cT) k wC wD wL wT θ)
        = some (.C, .C) := by
  obtain ⟨k₂, h⟩ := tauDupocSys_phase θ₂ θ₃ θ₄ θ₅ dC dD dL dT cC cD cL cT hreg₁ hreg₂
  exact ⟨k₂, fun k hk wC wD wL wT θ hθ =>
    outcome_of_ex_plays ((h k hk wC wD wL wT θ _).1 hθ) ((h k hk wC wD wL wT θ _).1 hθ)⟩

/-- The α-flip: in the defect regime (`θ` beyond even the behavioral mass) the
    self-play is `(D, D)`. -/
theorem outcome_TauDupocSys_vs_TauDupocSys_highθ
    (θ₂ θ₃ θ₄ θ₅ dC dD dL dT cC cD cL cT : Nat)
    (hreg₁ : dC + dT < θ₂) (hreg₂ : θ₂ ≤ dC + dL) :
    ∃ k₂, ∀ k, k₂ < k → ∀ (wC wD wL wT θ : Nat), wC + wL + wT < θ →
      ∃ N, outcome N
        (TauDupocSys (sigmaZoo k θ₂ θ₃ θ₄ θ₅ dC dD dL dT cC cD cL cT) k wC wD wL wT θ)
        (TauDupocSys (sigmaZoo k θ₂ θ₃ θ₄ θ₅ dC dD dL dT cC cD cL cT) k wC wD wL wT θ)
        = some (.D, .D) := by
  obtain ⟨k₂, h⟩ := tauDupocSys_phase θ₂ θ₃ θ₄ θ₅ dC dD dL dT cC cD cL cT hreg₁ hreg₂
  exact ⟨k₂, fun k hk wC wD wL wT θ hθ =>
    outcome_of_ex_plays ((h k hk wC wD wL wT θ _).2 hθ) ((h k hk wC wD wL wT θ _).2 hθ)⟩

end PD.Theorems.Tau
