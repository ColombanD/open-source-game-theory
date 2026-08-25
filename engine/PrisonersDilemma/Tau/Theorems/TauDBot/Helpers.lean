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

/-- **The single-stage embedded-floor census.** No proof of ≤ k characters
    concludes any formula whose spine tail says a `.bot`-frozen RUN STAGE (watch a
    frozen budget-`kb` searcher with then-action `.C`, test `.C`, fire `.D`,
    trusting tail `.const .C`) plays `.C`:

    * the fire route (`ite_t`) concludes `.D` — action mismatch;
    * the fall route (`ite_f`) needs the watched searcher to play something other
      than `.C`, impossible through `search_t` (its then-branch is `.const .C`)
      and floor-priced through `search_f` (the summand `kb ≥ k`).

    No hypothesis on the inner guard `g` is needed. -/
theorem no_provable_botRunStage_C (k kb : Nat) (hk : k ≤ kb) (g : Formula)
    (pE : Prog) (O : Prog) :
    ∀ K φ, Pf K φ → K ≤ k →
      TailTo (.plays (.bot (.ite
        (.sim (.bot (.search kb g (.const .C) pE)) (.bot (.search kb g (.const .C) pE)))
        .C (.const .D) (.const .C))) O .C) φ → False := by
  intro K φ hp hK htail
  refine no_provable_tailToS_floor k
    (· = .plays (.bot (.ite
      (.sim (.bot (.search kb g (.const .C) pE)) (.bot (.search kb g (.const .C) pE)))
      .C (.const .D) (.const .C))) O .C)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ K φ hp hK ((TailToS_singleton _ φ).2 htail)
  · rintro φ' rfl; exact ⟨_, _, _, rfl⟩
  · rintro K' hK' φ' rfl hA
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
