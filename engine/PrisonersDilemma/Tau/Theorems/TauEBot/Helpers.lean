import PrisonersDilemma.Tau.Theorems.Helpers
import PrisonersDilemma.Base.Exclusion

/-!
# Tau/Theorems/TauEBot/Helpers — the EMBEDDED-floor census

TauEBot's own mathematics, run-mode edition (the 2026-08-19 modality fix — base
EBot's cascade is `.sim` watches, and the lift now says so): `inst .ebot .dupoc`
REALLY cooperates (its exploit-watch sees Dupoc defect on the defector and falls
through; its reciprocity-watch sees Dupoc cooperate with the cooperator and fires),
yet that cooperation is UNPROVABLE at any budget ≤ k — not because of a floor at
EBot's own stage (run-stages have no searches) but ONE LEVEL DOWN: any certificate
must certify the exploit-watch FALLING, i.e. that the watched
`inst .dupoc .defect` — a budget-k searcher — plays its ELSE action, and that
subproof pays the `search_f` floor `k`. The floor moved from the prover's own
stage into the WATCHED instance, and the census below walks the extra
`ite_f → sim → bot` spine to reach it.

This is the "frozen player sim-embedding a floor-priced searcher" kernel the
roadmap deferred at the DBot lift — delivered here for the two-stage run cascade
(a DBot lift can reuse the same walk with a shorter spine).

A true bit that reads 0: the tau image of base `outcome_DupocBot_vs_EBot = (D, C)`.
-/

open PD PD.BaseTheorems

namespace PD.Tau

-- `no_provable_botRunCascade_C` moved to `Base/Exclusion.lean` (2026-08-25): a shape-general census
-- with no tau content — one census library for base and tau.

/-! ## The Gödelian floor pair — the δ_L column's EBot cell -/

/-- TRUE: `inst .ebot .dupoc` plays C (the exploit-watch falls, the
    reciprocity-watch fires). **Intentionally unconsumed**: the spec-level record
    that the 0-bit below sits over REAL cooperation — the honest-divergence half of
    the pair, consumed by the design review and the thesis. -/
theorem interp_probe_inst_ebot_dupoc {k : Nat} (hk : 2 ≤ k) :
    (probe (inst (tauZoo k) .ebot .dupoc)).interp := by
  have h1 : ∃ N, eval N (.bot (inst (tauZoo k) .dupoc .defect))
      (.bot (inst (tauZoo k) .dupoc .defect)) (inst (tauZoo k) .dupoc .defect)
      = some Action.D :=
    searchProbe_plays_D _ _ (ps_probe_constD k)
  have h2 : ∃ N, eval N (.bot (inst (tauZoo k) .dupoc .coop))
      (.bot (inst (tauZoo k) .dupoc .coop)) (inst (tauZoo k) .dupoc .coop)
      = some Action.C :=
    searchProbe_plays_C _ _ (ps_probe_constC hk)
  obtain ⟨N, hN⟩ :=
    simWatchC_falls (.bot (inst (tauZoo k) .ebot .dupoc))
      (.bot (inst (tauZoo k) .ebot .dupoc)) h1
      (simWatchC_fires _ _ h2)
  exact ⟨N + 2, by
    rw [play, eval]
    exact eval_mono_le hN _ (by omega)⟩

/-- UNPROVABLE: the bit is 0 at every budget up to k — TauDupoc's probe honestly
    fails, on the EMBEDDED floor. -/
theorem ps_probe_inst_ebot_dupoc_false {k K : Nat} (hK : K ≤ k) :
    proofSearch K (probe (inst (tauZoo k) .ebot .dupoc)) = false := by
  cases h : proofSearch K (probe (inst (tauZoo k) .ebot .dupoc)) with
  | false => rfl
  | true =>
      exfalso
      exact no_provable_botRunCascade_C k k (Nat.le_refl k)
        (probe (inst (tauZoo k) .defect .dupoc)) (.const .D)
        -- the continuation now carries EBot's THIRD stage (the mirror watch,
        -- restored 2026-08-24); the census is `cont`-generic, so only this
        -- argument changes
        (.ite (.sim (.bot (inst (tauZoo k) .dupoc .coop))
          (.bot (inst (tauZoo k) .dupoc .coop))) .C (.const .C)
          (.ite (.sim (.bot (inst (tauZoo k) .dupoc .mirror))
            (.bot (inst (tauZoo k) .dupoc .mirror))) .C (.const .C) (.const .D)))
        (.bot (inst (tauZoo k) .ebot .dupoc))
        K _ ((proofSearch_spec _ _).1 h) hK rfl

end PD.Tau
