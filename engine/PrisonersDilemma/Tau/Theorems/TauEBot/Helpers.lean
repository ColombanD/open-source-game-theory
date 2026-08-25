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

/-- **The embedded-floor census.** No proof of ≤ k characters concludes any formula
    whose spine tail says a `.bot`-frozen RUN CASCADE (first stage: watch a frozen
    budget-`kb` searcher with then-action `.C`, test `.C`, fire `.D`) plays `.C`:

    * cooperation cannot come from stage 1 firing (`ite_t` concludes the fire
      constant `.D` — action mismatch);
    * so it comes from stage 1 FALLING (`ite_f`), whose guard premise says the
      watched searcher plays something other than `.C` — impossible through
      `search_t` (the then-branch is `.const .C`) and floor-priced through
      `search_f` (the summand `kb ≥ k` blows the budget).

    No hypothesis about the inner guard `g` is needed: true, false, or undecided,
    its firing route cannot produce the target action. -/
theorem no_provable_botRunCascade_C (k kb : Nat) (hk : k ≤ kb) (g : Formula)
    (pE cont : Prog) (O : Prog) :
    ∀ K φ, Pf K φ → K ≤ k →
      TailTo (.plays (.bot (.ite
        (.sim (.bot (.search kb g (.const .C) pE)) (.bot (.search kb g (.const .C) pE)))
        .C (.const .D) cont)) O .C) φ → False := by
  intro K φ hp hK htail
  refine no_provable_tailToS_floor k
    (· = .plays (.bot (.ite
      (.sim (.bot (.search kb g (.const .C) pE)) (.bot (.search kb g (.const .C) pE)))
      .C (.const .D) cont)) O .C)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ K φ hp hK ((TailToS_singleton _ φ).2 htail)
  · rintro φ' rfl; exact ⟨_, _, _, rfl⟩
  · -- the atom killer: bot → ite_t (fire-action mismatch) / ite_f → sim → bot →
    -- search_t (then-const mismatch with the fall) / search_f (the floor `kb`)
    rintro K' hK' φ' rfl hA
    cases hA with
    | mk hpp hn =>
      cases hpp with
      | bot hin =>
        cases hin with
        | ite_t hg hbeq hbr => cases hbr
        | ite_f hg hbeq hbr =>
            cases hg with
            | sim hin2 =>
                cases hin2 with
                | bot hin3 =>
                    cases hin3 with
                    | search_t hProv hbr2 =>
                        cases hbr2
                        exact absurd hbeq (by decide)
                    | search_f hneg hbr2 =>
                        simp only [c_node] at hn
                        omega
  · intro me oppo c hS g' ψ b hme
    injection hS with h1 h2 h3
    subst h1; simp at hme
  · intro me oppo c hS p' q' hme
    injection hS with h1 h2 h3
    subst h1; simp at hme
  · intro me oppo c hS p' q' hme
    injection hS with h1 h2 h3
    subst h1
    simp only [Prog.bot.injEq] at hme
    simp at hme
  · intro me oppo c hS g' ψ b hme
    injection hS with h1 h2 h3
    subst h1
    simp only [Prog.bot.injEq] at hme
    simp at hme
  · intro z a' g' ψ c0 c1 q' oppo hS
    injection hS with h1 h2 h3
    simp at h1
  · intro me oppo c hS k₁ ψ₁ k₂ ψ₂ c1 q' hme
    injection hS with h1 h2 h3
    subst h1; simp at hme
  · intro me oppo c hS L hme
    injection hS with h1 h2 h3
    subst h1
    cases L with
    | nil => simp [searchPlug] at hme
    | cons hd tl => obtain ⟨g', ψ, e⟩ := hd; simp [searchPlug] at hme
  · intro me oppo c hS hd L hme
    injection hS with h1 h2 h3
    subst h1
    cases hd with
    | searchL g' ψ' e' => simp [ctxPlug] at hme
    | iteL z' aT' other' => simp [ctxPlug] at hme
  · intro me oppo c hS hd L hme
    injection hS with h1 h2 h3
    subst h1
    cases hd <;> simp [plug2] at hme
  · -- hbotsys: the target is not a `.bot`-wrapped system reference
    intro me oppo c hS defs i _ _ _ hme _
    injection hS with h1 h2 h3
    subst h1; simp at hme
  · -- hbotsyssim: the `.sys` RUN twin, killed by the same shape argument
    intro me oppo c hS defs i _ hme _
    injection hS with h1 h2 h3
    subst h1; simp at hme
  · -- hbotsyssts: the `.sys` NESTED twin, same shape kill
    intro me oppo c hS defs i _ _ _ _ _ _ hme _ _ _ _
    injection hS with h1 h2 h3
    subst h1; simp at hme

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
