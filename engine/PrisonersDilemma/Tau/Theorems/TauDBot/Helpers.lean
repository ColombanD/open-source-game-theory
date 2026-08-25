import PrisonersDilemma.Tau.Theorems.Helpers
import PrisonersDilemma.Base.Exclusion

/-!
# Tau/Theorems/TauDBot/Helpers — the single-stage embedded-floor census

TauDBot's own mathematics, and the reason it was the last non-`.sys` bot to land:
`inst .dbot .dupoc` REALLY cooperates (its watch sees `inst .dupoc .defect` defect
and falls through to the trusting default) yet that cooperation is UNPROVABLE at
any budget ≤ k. The floor is EMBEDDED — DBot's own stage has no search — it sits
one level down, in the WATCHED instance: certifying the fall means certifying that
a budget-`k` searcher plays its else-action, and that subproof pays `search_f`.

`no_provable_botRunStage_C` is the single-stage twin of TauEBot's
`no_provable_botRunCascade_C`: same spine walk (`bot → ite_t` fire-mismatch /
`ite_f → sim → bot → search_t` const-mismatch / `search_f` floor), one layer
shorter because the fall lands on a constant instead of a second stage. Proving it
is what the roster's DBot exclusion note was waiting for.
-/

open PD PD.BaseTheorems

namespace PD.Tau

-- `no_provable_botRunStage_C` moved to `Base/Exclusion.lean` (2026-08-25): a shape-general census
-- with no tau content — one census library for base and tau.

/-! ## The Gödelian floor pair — the δ_L column's DBot cell -/

/-- TRUE: `inst .dbot .dupoc` plays C (the watch sees Dupoc-seeing-Defect defect
    and falls through to the trusting default). **Intentionally unconsumed**: the
    spec-level record that the 0-bit below sits over REAL cooperation. -/
theorem interp_probe_inst_dbot_dupoc {k : Nat} :
    (probe (inst (tauZoo k) .dbot .dupoc)).interp := by
  have h1 : ∃ N, eval N (.bot (inst (tauZoo k) .dupoc .defect))
      (.bot (inst (tauZoo k) .dupoc .defect)) (inst (tauZoo k) .dupoc .defect)
      = some Action.D :=
    searchProbe_plays_D _ _ (ps_probe_constD k)
  have htail : ∃ N, eval N (.bot (inst (tauZoo k) .dbot .dupoc))
      (.bot (inst (tauZoo k) .dbot .dupoc)) (.const Action.C) = some Action.C :=
    ⟨1, rfl⟩
  obtain ⟨N, hN⟩ :=
    simWatchC_falls (.bot (inst (tauZoo k) .dbot .dupoc))
      (.bot (inst (tauZoo k) .dbot .dupoc)) h1 htail
  exact ⟨N + 2, by
    rw [play, eval]
    exact eval_mono_le hN _ (by omega)⟩

/-- UNPROVABLE: the bit is 0 at every budget up to k — the prover columns honestly
    read DBot's trust as 0. -/
theorem ps_probe_inst_dbot_dupoc_false {k K : Nat} (hK : K ≤ k) :
    proofSearch K (probe (inst (tauZoo k) .dbot .dupoc)) = false := by
  cases h : proofSearch K (probe (inst (tauZoo k) .dbot .dupoc)) with
  | false => rfl
  | true =>
      exfalso
      exact no_provable_botRunStage_C k k (Nat.le_refl k)
        (probe (inst (tauZoo k) .defect .dupoc)) (.const .D)
        (.bot (inst (tauZoo k) .dbot .dupoc))
        K _ ((proofSearch_spec _ _).1 h) hK rfl

end PD.Tau
